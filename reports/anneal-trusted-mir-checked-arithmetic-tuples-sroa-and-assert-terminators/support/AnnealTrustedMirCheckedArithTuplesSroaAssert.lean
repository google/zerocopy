-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirAst
import Trusted.MirSemantics

namespace VrustcFormal.F1_11

open Trusted.MirAst Trusted.MirSemantics

/-!
# Checked Arithmetic, Flat Tuples, Certified `SROA`, & `Assert` Lowering (`VrustcFormal.F1_11`)

This module extends Anneal's unmodified `Trusted.MirAst` and
`Trusted.MirSemantics` conservatively (`M_tupleAssert`) to model the exact
checked-arithmetic, flat-tuple, field-projection, and `Assert`-terminator
surface emitted by `rustc` for safe Rust integer arithmetic (`a + b`, `a - b`,
`a * b`, `Rvalue.aggregateTuple`, `ProjectionElem.field`,
`BinOp.{addWithOverflow, subWithOverflow, mulWithOverflow}`, and
`TerminatorKind.assert`), and formalizes certified Scalar Replacement of
Aggregates (`SROA`), constant-true `Assert` folding, and `Assert`-to-
`SwitchInt`+`Unreachable` lowering directly back into Anneal's unmodified
`Trusted.MirSemantics`:

1. **Part I — Conservative Extension `M_tupleAssert` Over Unmodified
   `Trusted.MirAst` & `Trusted.MirSemantics`:**
   - Extends `LocalSlot` to `LocalSlotExt` (`dead`, `liveBase`, `liveTuple`),
     supporting flat non-empty tuples `.tuple fieldTys` (every field in
     `Trusted.MirSemantics.isSupportedScalarOrUnitTy`) with field-granular
     initialization, inhabited ZST field preservation (`liveUninitFieldVal`),
     and field-granular `Operand.move` deinitialization
     (`deinitMovedPlace = true`).
   - Separates defined Rust panics (`TerminalOutExt.panic msg`) from normal
     returns (`TerminalOutExt.ret out`), modeled Rust UB (`.fault .undefined`),
     and unmodeled constructs (`.fault .unsupported`).
   - Evaluates `Rvalue.aggregateTuple` sequentially left-to-right in place
     (failing closed with `.fault .unsupported` on self-aliasing destinations
     where any operand mentions `dst.localId`, matching
     `rustc_const_eval/src/interpret/step.rs::write_aggregate` and
     `Miri.Interpreter.Aggregate.writeAggregate`), fails closed with `.fault
     .unsupported` on whole-tuple self-copy/self-move (`_t = copy _t` /
     `_t = move _t`, preventing masking of `copyRangesOverlap` UB), evaluates
     `ProjectionElem.field` reads and writes, `BinOp.{addWithOverflow,
     subWithOverflow, mulWithOverflow}` across all six integer widths
     (`i8`..`i128`, `isize`) in both signed and unsigned modes using unmodified
     `Trusted.MirSemantics.truncateScalar` plus exact 128-bit host-range
     overflow detection, and `TerminatorKind.assert` (validating
     `isSupportedAssertKind msg`, mapping `.continue_ | .terminate` to defined
     panic `.done (.panic msg)`, mapping `.unreachable` to modeled UB `.fault
     .undefined` per `Miri.Interpreter.ControlFlow.unwindToBlock`, and failing
     closed with `.fault .unsupported` on `.cleanup _`,
     `AssertKind.unsupported`, or non-overflowing `AssertKind.overflow op`).
   - Defines `evalTupleAssertFuel`, `ReachesResultTupleAssert`,
     `WellFormedTupleAssert`, `NoPanicAndWellFormedTupleAssert`,
     `BehaviorTupleAssert`, constructive `DivergesTupleAssert`,
     `SatisfiesPostNoPanicTupleAssert`, `BodyVerifiedNoPanicTupleAssert`,
     `ProgramVerifiedNoPanicTupleAssert`, `CrateTheoremNoPanicTupleAssert`,
     `UnitTheoremNoPanicTupleAssert`, `FullSemanticEquivTupleAssert`, and
     `NoPanicSemanticEquivTupleAssert`.

2. **Part II — Certified Tuple/WithOverflow `SROA`, Constant-True `Assert`
   Folding, & `Assert` Lowering Directly Over `Trusted.MirAst`:**
   - `SroaTuplePlan` / `SroaTrace` / `applyMirSroaTuple` / `checkMirSroaTuple`
     / `checkMirSroaTrace`: flattens non-escaping flat-tuple locals
     (`tupLocal > body.argumentCount`, zero references in `Rvalue.ref` /
     `Rvalue.addressOf`, whole-tuple `Copy`/`Move`, or self-aliasing
     `Rvalue.aggregateTuple`) into fresh trailing scalar locals `base .. base +
     k - 1`, tombstones `locals[tupLocal]` to `.unit` to preserve all other
     local indices, lowers `StorageLive` / `StorageDead` across all `k` fields
     (preserving `hasStorageAnnotation`), lowers non-aliasing
     `Rvalue.aggregateTuple` directly to left-to-right scalar field assignments
     (matching in-place field-0 `DeadLocal` and `Operand.move` ordering
     bit-for-bit without scratch temps), uses fresh scratch temporaries
     (`ovfTmpBase`) for unsigned `BinOp.{addWithOverflow, subWithOverflow}` to
     preserve exact single-time left-to-right operand evaluation,
     `Operand.move` deinitialization, self-referencing carry semantics, and
     write-time `DeadLocal` fault ordering, and rewrites every `Place
     ⟨tupLocal, [.field idx _]⟩` to `Place ⟨base + idx, []⟩`.
   - `applyMirAssertConstFold` / `checkMirAssertConstFold`: folds statically
     canonical constant-true `TerminatorKind.assert` terminators (`bits == 1`
     when `expected = true`, `bits == 0` when `expected = false`) to
     `.goto target`, rejecting invalid boolean bit patterns (`bits ≥ 2`).
   - `lowerAssertsToSwitchUnreachable` / `checkMirAssertLower`: lowers every
     statically boolean, non-cleanup, `isSupportedAssertKind`-admitted
     `TerminatorKind.assert` to `.switchInt cond { branches := [(if expected
     then 1 else 0, target)], otherwise := unreachBb }` targeting a fresh
     `.unreachable` block, reducing panic-freedom + UB-freedom directly to
     unmodified `Trusted.MirSemantics.WellFormed`.

3. **Part III — Five Core Target Theorems (`sorry` placeholders frozen for
   Stage 3 proof):**
   - `tupleAssert_conservative_extension_exact`
   - `mirSroaTuple_sound_bidirectional_iff`
   - `mirAssertConstFold_sound_bidirectional_iff`
   - `mirSroaAndAssertLower_noPanic_reduces_to_trusted_mir`
   - `mirSroaAssert_then_optPipeline_vc_transport`

4. **Part IV — Deterministic Adequacy, Ten Sharpness Counterexamples
   (`CE1`--`CE10`), and End-to-End `checked_add_pair` Witness (`0` `sorry`,
   strictly `[propext]` / `[]`):**
   - Proves bounded-fuel adequacy for both unmodified `Trusted.MirSemantics`
     and `M_tupleAssert`, ten constructive counterexamples (`CE1`--`CE10`)
     covering `u32::MAX + 1` overflow, `0_u32 - 1_u32` underflow,
     field-granular `Move` deinitialization, escaping `Rvalue.ref` rejection,
     `StorageDead` + `StorageLive` tuple reset, `Assert` polarity /
     constant-fold sharpness, self-aliasing `Rvalue.aggregateTuple` rejection
     and dead-destination field-0 `DeadLocal` ordering, failing `Assert` unwind
     (`.unreachable` -> `.undefined`, `.cleanup` -> `.unsupported`) and
     `AssertKind` fail-closed rejection, whole-tuple self-copy/self-move
     rejection, and 128-bit `i128`/`u128` overflow boundaries, plus a concrete
     `checked_add_pair(a, b)` witness lowered by `checkMirSroaTrace` +
     `checkMirAssertLower` directly into unmodified `Trusted.MirSemantics`.
-/

/-! ## Part I: Conservative Extension `M_tupleAssert` Over Unmodified `Trusted.MirAst` & `Trusted.MirSemantics` -/

/-! ### Structural Equality Predicates Over `Trusted.MirAst` -/

/-- Pairwise boolean relation over two lists of equal length. -/
noncomputable def listRel {α β : Type} (r : α → β → Bool) :
    List α → List β → Bool
  | [], [] => true
  | x :: xs, y :: ys => r x y && listRel r xs ys
  | _, _ => false

/-- Structural equality on `ProjectionElem`. -/
noncomputable def projElemEq : ProjectionElem → ProjectionElem → Bool
  | .deref, .deref => true
  | .field idx₁ ty₁, .field idx₂ ty₂ => Nat.beq idx₁ idx₂ && MirTy.beq ty₁ ty₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `Place`. -/
noncomputable def placeEq (p₁ p₂ : Place) : Bool :=
  Nat.beq p₁.localId p₂.localId && listRel projElemEq p₁.projection p₂.projection

/-- Structural equality on `ConstLit`. -/
noncomputable def constLitEq : ConstLit → ConstLit → Bool
  | .scalar b₁, .scalar b₂ => b₁ == b₂
  | .zeroSized, .zeroSized => true
  | _, _ => false

/-- Structural equality on `ConstOperand`. -/
noncomputable def constOpEq (c₁ c₂ : ConstOperand) : Bool :=
  MirTy.beq c₁.ty c₂.ty && constLitEq c₁.lit c₂.lit

/-- Structural equality on `BinOp`. -/
noncomputable def binOpEq : BinOp → BinOp → Bool
  | .add, .add | .addUnchecked, .addUnchecked | .addWithOverflow, .addWithOverflow
  | .sub, .sub | .subUnchecked, .subUnchecked | .subWithOverflow, .subWithOverflow
  | .mul, .mul | .mulUnchecked, .mulUnchecked | .mulWithOverflow, .mulWithOverflow
  | .div, .div | .rem, .rem
  | .bitXor, .bitXor | .bitAnd, .bitAnd | .bitOr, .bitOr
  | .shl, .shl | .shlUnchecked, .shlUnchecked
  | .shr, .shr | .shrUnchecked, .shrUnchecked
  | .eq, .eq | .lt, .lt | .le, .le | .ne, .ne | .ge, .ge | .gt, .gt
  | .offset, .offset => true
  | _, _ => false

/-- Structural equality on `UnOp`. -/
noncomputable def unOpEq : UnOp → UnOp → Bool
  | .not, .not | .neg, .neg | .ptrMetadata, .ptrMetadata => true
  | _, _ => false

/-- Structural equality on `Operand`. -/
noncomputable def operandEq : Operand → Operand → Bool
  | .copy p₁, .copy p₂ => placeEq p₁ p₂
  | .move p₁, .move p₂ => placeEq p₁ p₂
  | .constant c₁, .constant c₂ => constOpEq c₁ c₂
  | _, _ => false

/-- Structural equality on `Rvalue`. -/
noncomputable def rvalueEq : Rvalue → Rvalue → Bool
  | .use o₁, .use o₂ => operandEq o₁ o₂
  | .binaryOp op₁ l₁ r₁, .binaryOp op₂ l₂ r₂ =>
    binOpEq op₁ op₂ && operandEq l₁ l₂ && operandEq r₁ r₂
  | .unaryOp op₁ o₁, .unaryOp op₂ o₂ => unOpEq op₁ op₂ && operandEq o₁ o₂
  | .discriminant p₁, .discriminant p₂ => placeEq p₁ p₂
  | .ref m₁ p₁, .ref m₂ p₂ => Mutability.beq m₁ m₂ && placeEq p₁ p₂
  | .addressOf m₁ p₁, .addressOf m₂ p₂ => Mutability.beq m₁ m₂ && placeEq p₁ p₂
  | .aggregateTuple fs₁, .aggregateTuple fs₂ => listRel operandEq fs₁ fs₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `StatementKind`. -/
noncomputable def stmtEq : StatementKind → StatementKind → Bool
  | .assign d₁ rv₁, .assign d₂ rv₂ => placeEq d₁ d₂ && rvalueEq rv₁ rv₂
  | .storageLive i₁, .storageLive i₂ => Nat.beq i₁ i₂
  | .storageDead i₁, .storageDead i₂ => Nat.beq i₁ i₂
  | .nop, .nop => true
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `SwitchTargets`. -/
noncomputable def switchTargetsEq (t₁ t₂ : SwitchTargets) : Bool :=
  Nat.beq t₁.otherwise t₂.otherwise &&
    listRel (fun a b => (a.1 == b.1) && Nat.beq a.2 b.2) t₁.branches t₂.branches

/-- Structural equality on `UnwindAction`. -/
noncomputable def unwindActionEq : UnwindAction → UnwindAction → Bool
  | .continue_, .continue_ | .unreachable, .unreachable
  | .terminate, .terminate => true
  | .cleanup b₁, .cleanup b₂ => Nat.beq b₁ b₂
  | _, _ => false

/-- Structural equality on `AssertKind`. -/
noncomputable def assertKindEq : AssertKind → AssertKind → Bool
  | .overflow o₁, .overflow o₂ => binOpEq o₁ o₂
  | .overflowNeg, .overflowNeg | .divByZero, .divByZero | .remByZero, .remByZero
  | .boundsCheck, .boundsCheck | .misalignedPtrDeref, .misalignedPtrDeref
  | .nullPtrDeref, .nullPtrDeref | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `Option BasicBlockId`. -/
noncomputable def optBlockEq : Option BasicBlockId → Option BasicBlockId → Bool
  | none, none => true
  | some b₁, some b₂ => Nat.beq b₁ b₂
  | _, _ => false

/-- Structural equality on `TerminatorKind`. -/
noncomputable def terminatorEq : TerminatorKind → TerminatorKind → Bool
  | .goto t₁, .goto t₂ => Nat.beq t₁ t₂
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ =>
    operandEq d₁ d₂ && switchTargetsEq ts₁ ts₂
  | .return_, .return_ => true
  | .unreachable, .unreachable => true
  | .unwindResume, .unwindResume => true
  | .assert c₁ e₁ m₁ t₁ u₁, .assert c₂ e₂ m₂ t₂ u₂ =>
    operandEq c₁ c₂ && (e₁ == e₂) && assertKindEq m₁ m₂ &&
      Nat.beq t₁ t₂ && unwindActionEq u₁ u₂
  | .call f₁ as₁ d₁ t₁ u₁, .call f₂ as₂ d₂ t₂ u₂ =>
    Nat.beq f₁ f₂ && listRel operandEq as₁ as₂ && placeEq d₁ d₂ &&
      optBlockEq t₁ t₂ && unwindActionEq u₁ u₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `BasicBlock`. -/
noncomputable def blockEq (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel stmtEq b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

/-- Structural equality on `VerificationScope`. -/
noncomputable def scopeEq : VerificationScope → VerificationScope → Bool
  | .unit, .unit | .crate, .crate => true
  | _, _ => false

/-- Shared body-metadata equality (`argumentCount`, `locals`, `isUnsafe`,
`identity`). -/
noncomputable def bodyHeaderEq (b₁ b₂ : Body) : Bool :=
  Nat.beq b₁.argumentCount b₂.argumentCount &&
    MirTy.beqList b₁.locals b₂.locals &&
    (b₁.isUnsafe == b₂.isUnsafe) &&
    stringBeq b₁.identity b₂.identity

/-- Structural equality on `Body`. -/
noncomputable def bodyEq (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ && listRel blockEq b₁.basicBlocks b₂.basicBlocks

/-- Shared program-header equality (`pointerWidthBits`, `mirProfileVersion`,
`entryDefId`, `scope`). -/
noncomputable def programHeaderEq (p₁ p₂ : Program) : Bool :=
  Nat.beq p₁.pointerWidthBits p₂.pointerWidthBits &&
    Nat.beq p₁.mirProfileVersion p₂.mirProfileVersion &&
    Nat.beq p₁.entryDefId p₂.entryDefId &&
    scopeEq p₁.scope p₂.scope

/-- Structural equality on `Program`. -/
noncomputable def programEq (p₁ p₂ : Program) : Bool :=
  programHeaderEq p₁ p₂ && listRel bodyEq p₁.bodies p₂.bodies

/-- Metadata compatibility between two programs sharing the same crate/unit
packaging (`pointerWidthBits`, `mirProfileVersion`, `entryDefId`, `scope`,
body count, and per-body `identity` strings), preserved by every certified MIR
optimization pass (`F1-5`--`F1-10`). -/
noncomputable def ProgramMetadataCompat (p₁ p₂ : Program) : Bool :=
  programHeaderEq p₁ p₂ &&
    listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) p₁.bodies p₂.bodies

/-! ### Extended Machine State (`LocalSlotExt`, `StateExt`, `TerminalOutExt`) -/

/-- Whether `ty` is a non-empty flat tuple `.tuple fieldTys` whose every field
belongs to `Trusted.MirSemantics.isSupportedScalarOrUnitTy`. -/
noncomputable def isFlatTupleTy : MirTy → Bool
  | .tuple fieldTys =>
    !fieldTys.isEmpty && fieldTys.all isSupportedScalarOrUnitTy
  | _ => false

/-- Supported local-variable type fragment for `M_tupleAssert`: every type
admitted by `Trusted.MirSemantics.isSupportedScalarOrUnitTy` plus non-empty
flat tuples (`isFlatTupleTy`). -/
noncomputable def isSupportedTupleOrScalarTy (ty : MirTy) : Bool :=
  isSupportedScalarOrUnitTy ty || isFlatTupleTy ty

/-- Extended local slot state supporting field-granular initialization and
`Operand.move` deinitialization on flat tuples while remaining isomorphic to
`Trusted.MirSemantics.LocalSlot` on all non-tuple types. -/
inductive LocalSlotExt where
  | dead
  | liveBase (val : Option Val)
  | liveTuple (fields : List (Option Val))

/-- Extended active execution frame over `LocalSlotExt`. -/
structure FrameStateExt where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List LocalSlotExt

/-- Extended running machine state over `FrameStateExt` and unmodified
`Trusted.MirSemantics.CallerMemory`. -/
structure StateExt where
  frames : List FrameStateExt
  callerMem : CallerMemory := ⟨[]⟩

/-- Observable terminal outcomes of `M_tupleAssert`, separating normal function
returns (`.ret out`) from defined Rust assertion panics (`.panic kind`), while
modeled Rust UB (`.fault .undefined`) and unmodeled constructs
(`.fault .unsupported`) remain distinct fault poles. -/
inductive TerminalOutExt where
  | ret (out : Out)
  | panic (kind : AssertKind)

/-- Exact embedding of `Trusted.MirSemantics.LocalSlot` into `LocalSlotExt`. -/
noncomputable def embedLocalSlot : LocalSlot → LocalSlotExt
  | .dead => .dead
  | .live optVal => .liveBase optVal

/-- Exact embedding of `Trusted.MirSemantics.FrameState` into `FrameStateExt`. -/
noncomputable def embedFrame (f : FrameState) : FrameStateExt :=
  {
    defId := f.defId
    blockIdx := f.blockIdx
    stmtIdx := f.stmtIdx
    locals := f.locals.map embedLocalSlot
  }

/-- Exact embedding of `Trusted.MirSemantics.State` into `StateExt`. -/
noncomputable def embedState (s : State) : StateExt :=
  { frames := s.frames.map embedFrame, callerMem := s.callerMem }

/-- Lift a `Trusted.MirSemantics.StepResult` into `M_tupleAssert`'s
`StepResult StateExt TerminalOutExt`. -/
noncomputable def liftStepResult :
    StepResult State TerminalOut → StepResult StateExt TerminalOutExt
  | .step s' => .step (embedState s')
  | .done (.returned out) => .done (.ret out)
  | .done (.unwound _) => .fault .unsupported
  | .fault k => .fault k

/-- Initial field value of a newly live scalar/unit/enum slot (matching
`Trusted.MirSemantics.liveUninitSlot`): inhabited ZSTs (`.unit` and admitted
1-variant `.zeroSized` enums) remain inhabited; all other types start
uninitialized (`none`). -/
noncomputable def liveUninitFieldVal : MirTy → Option Val
  | .unit => some .unit
  | .enum ety => if isZstEnumTy ety then some (.enumVal ety 0) else none
  | _ => none

/-- Initial state of a newly live `LocalSlotExt` of type `ty`. -/
noncomputable def liveUninitSlotExt : MirTy → LocalSlotExt
  | .tuple fieldTys =>
    if isFlatTupleTy (.tuple fieldTys) then
      .liveTuple (fieldTys.map liveUninitFieldVal)
    else
      .liveBase none
  | ty => .liveBase (liveUninitFieldVal ty)

/-- Extended runtime value type check admitting `Val.tuple` on flat tuple
types and delegating all non-tuple types to `Trusted.MirSemantics.checkVal`. -/
noncomputable def checkValExt (v : Val) (ty : MirTy) : Bool :=
  match ty with
  | .tuple fieldTys =>
    if isFlatTupleTy (.tuple fieldTys) then
      match v with
      | .tuple vs => checkArgsMatch vs fieldTys
      | _ => false
    else
      false
  | _ => checkVal v ty

/-- Check that entry argument list `vs` matches parameter type list `tys` under
`checkValExt`. -/
noncomputable def checkArgsMatchExt : List Val → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys => checkValExt v ty && checkArgsMatchExt vs tys
  | _, _ => false

/-- Construct an initialized entry-argument `LocalSlotExt` for `(ty, v)`. -/
noncomputable def initArgSlotExt (ty : MirTy) (v : Val) : LocalSlotExt :=
  match ty, v with
  | .tuple _, .tuple vs => .liveTuple (vs.map some)
  | _, _ => .liveBase (some v)

/-- Initialize local slots of `body` at function entry in `M_tupleAssert`,
mirroring `Trusted.MirSemantics.initLocalsLoop`. -/
noncomputable def initLocalsExtLoop (body : Body) (args : List Val) :
    Nat → List MirTy → List LocalSlotExt
  | _, [] => []
  | idx, ty :: rest =>
    let slot : LocalSlotExt :=
      if Nat.beq idx 0 then
        liveUninitSlotExt ty
      else if Nat.ble idx body.argumentCount then
        match Trusted.MirSemantics.getElem? args (idx - 1) with
        | some v => initArgSlotExt ty v
        | none => .dead
      else if hasStorageAnnotation body idx then
        .dead
      else
        liveUninitSlotExt ty
    slot :: initLocalsExtLoop body args (idx + 1) rest

/-- Entry initialization for `M_tupleAssert`, mirroring
`Trusted.MirSemantics.initState` with `isSupportedTupleOrScalarTy` and
`checkArgsMatchExt`. -/
noncomputable def initStateTupleAssert (p : Program) (q : Query) :
    Except FaultKind StateExt :=
  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1 then
    .error .unsupported
  else if !q.callerMem.allocations.isEmpty then
    .error .unsupported
  else
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | none => .error .unsupported
    | some body =>
      if body.basicBlocks.isEmpty then
        .error .unsupported
      else if !Nat.blt body.argumentCount body.locals.length then
        .error .unsupported
      else if !storageAnnotationsInBounds body then
        .error .unsupported
      else if !body.locals.all isSupportedTupleOrScalarTy then
        .error .unsupported
      else
        let paramTys := (body.locals.drop 1).take body.argumentCount
        if !checkArgsMatchExt q.args paramTys then
          .error .unsupported
        else
          let locals := initLocalsExtLoop body q.args 0 body.locals
          let frame : FrameStateExt := {
            defId := p.entryDefId
            blockIdx := 0
            stmtIdx := 0
            locals := locals
          }
          .ok { frames := [frame], callerMem := q.callerMem }

/-! ### Operational Step Semantics `evalStepTupleAssert` -/

/-- Extract all initialized field values from a flat tuple slot, returning
`none` if any field is uninitialized (`none`). -/
noncomputable def extractAllInitFields : List (Option Val) → Option (List Val)
  | [] => some []
  | none :: _ => none
  | some v :: rest =>
    match extractAllInitFields rest with
    | some vs => some (v :: vs)
    | none => none

/-- Stage 1 of operand evaluation in `M_tupleAssert`: supports unprojected
scalar/unit/enum/tuple locals as well as single-step `ProjectionElem.field`
reads and field-granular `Operand.move` deinitialization on flat tuple locals
(preserving inhabited ZST fields via `liveUninitFieldVal`). -/
noncomputable def evalOperandToSlotExt (bodyLocals : List MirTy)
    (locals : List LocalSlotExt) :
    Operand → Except FaultKind (MirTy × Option Val × List LocalSlotExt)
  | .copy place =>
    match place.projection with
    | [] =>
      match Trusted.MirSemantics.getElem? bodyLocals place.localId,
          Trusted.MirSemantics.getElem? locals place.localId with
      | some ty, some (.liveBase optVal) =>
        if isFlatTupleTy ty then
          .error .unsupported
        else
          .ok (ty, optVal, locals)
      | some (.tuple fieldTys), some (.liveTuple fields) =>
        if isFlatTupleTy (.tuple fieldTys) &&
            Nat.beq fields.length fieldTys.length then
          let optVal :=
            match extractAllInitFields fields with
            | some vs => some (.tuple vs)
            | none => none
          .ok (.tuple fieldTys, optVal, locals)
        else
          .error .unsupported
      | some _, some .dead => .error .undefined
      | _, _ => .error .unsupported
    | [.field idx fieldTy] =>
      match Trusted.MirSemantics.getElem? bodyLocals place.localId,
          Trusted.MirSemantics.getElem? locals place.localId with
      | some (.tuple fieldTys), some slot =>
        if !isFlatTupleTy (.tuple fieldTys) then
          .error .unsupported
        else
          match Trusted.MirSemantics.getElem? fieldTys idx with
          | none => .error .unsupported
          | some declFieldTy =>
            if !MirTy.beq fieldTy declFieldTy then
              .error .unsupported
            else
              match slot with
              | .dead => .error .undefined
              | .liveTuple fields =>
                match Trusted.MirSemantics.getElem? fields idx with
                | some optVal => .ok (declFieldTy, optVal, locals)
                | none => .error .unsupported
              | .liveBase _ => .error .unsupported
      | _, _ => .error .unsupported
    | _ => .error .unsupported
  | .move place =>
    match place.projection with
    | [] =>
      match Trusted.MirSemantics.getElem? bodyLocals place.localId,
          Trusted.MirSemantics.getElem? locals place.localId with
      | some ty, some (.liveBase optVal) =>
        if isFlatTupleTy ty then
          .error .unsupported
        else
          match setElem? locals place.localId
              (.liveBase (liveUninitFieldVal ty)) with
          | some locals' => .ok (ty, optVal, locals')
          | none => .error .unsupported
      | some (.tuple fieldTys), some (.liveTuple fields) =>
        if isFlatTupleTy (.tuple fieldTys) &&
            Nat.beq fields.length fieldTys.length then
          let optVal :=
            match extractAllInitFields fields with
            | some vs => some (.tuple vs)
            | none => none
          match setElem? locals place.localId
              (liveUninitSlotExt (.tuple fieldTys)) with
          | some locals' => .ok (.tuple fieldTys, optVal, locals')
          | none => .error .unsupported
        else
          .error .unsupported
      | some _, some .dead => .error .undefined
      | _, _ => .error .unsupported
    | [.field idx fieldTy] =>
      match Trusted.MirSemantics.getElem? bodyLocals place.localId,
          Trusted.MirSemantics.getElem? locals place.localId with
      | some (.tuple fieldTys), some slot =>
        if !isFlatTupleTy (.tuple fieldTys) then
          .error .unsupported
        else
          match Trusted.MirSemantics.getElem? fieldTys idx with
          | none => .error .unsupported
          | some declFieldTy =>
            if !MirTy.beq fieldTy declFieldTy then
              .error .unsupported
            else
              match slot with
              | .dead => .error .undefined
              | .liveTuple fields =>
                match Trusted.MirSemantics.getElem? fields idx with
                | none => .error .unsupported
                | some optVal =>
                  match setElem? fields idx
                      (liveUninitFieldVal declFieldTy) with
                  | none => .error .unsupported
                  | some fields' =>
                    match setElem? locals place.localId
                        (.liveTuple fields') with
                    | some locals' => .ok (declFieldTy, optVal, locals')
                    | none => .error .unsupported
              | .liveBase _ => .error .unsupported
      | _, _ => .error .unsupported
    | _ => .error .unsupported
  | .constant c =>
    match evalConstLit c.ty c.lit with
    | .ok v => .ok (c.ty, some v, locals)
    | .error k => .error k

/-- Stage 2 of operand evaluation in `M_tupleAssert`, mirroring
`Trusted.MirSemantics.evalPrimitiveOperand`. -/
noncomputable def evalPrimitiveOperandExt (bodyLocals : List MirTy)
    (locals : List LocalSlotExt) (opnd : Operand) :
    Except FaultKind (Val × List LocalSlotExt) :=
  match evalOperandToSlotExt bodyLocals locals opnd with
  | .error k => .error k
  | .ok (ty, optVal, locals') =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match optVal with
      | some v => .ok (v, locals')
      | none => .error .undefined

/-- Whether `op` is a checked overflowing binary arithmetic operator
(`.addWithOverflow`, `.subWithOverflow`, or `.mulWithOverflow`). -/
noncomputable def isWithOverflowBinOp : BinOp → Bool
  | .addWithOverflow | .subWithOverflow | .mulWithOverflow => true
  | _ => false

/-- Evaluate `BinOp.{addWithOverflow, subWithOverflow, mulWithOverflow}` over
two equal-type scalar values using unmodified
`Trusted.MirSemantics.truncateScalar` plus exact 128-bit host-range overflow
detection (matching `Trusted.MirSemantics.evalArithOp` and upstream
`rustc_const_eval::interpret::operator.rs`), returning the exact
`(wrappedScalar, overflowed)` pair across all 6 integer widths (`i8`..`i128`,
`isize`) in both signed and unsigned modes. -/
noncomputable def evalWithOverflowOp (op : BinOp) (lhs rhs : Val) :
    Except FaultKind (ScalarVal × Bool) :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then
      .error .unsupported
    else
      let w := l.width
      let s := l.signed
      let lInt := decodeScalar l
      let rInt := decodeScalar r
      let res? : Option Int := match op with
        | .addWithOverflow => some (lInt + rInt)
        | .subWithOverflow => some (lInt - rInt)
        | .mulWithOverflow => some (lInt * rInt)
        | _ => none
      match res? with
      | none => .error .unsupported
      | some result =>
        let hostOverflow : Bool :=
          if s then
            decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (result ≥ HPow.hPow (2 : Int) 127)
          else
            decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
        match truncateScalar w s result with
        | .error k => .error k
        | .ok (val, lossy) =>
          .ok (val, hostOverflow || lossy)
  | _, _ => .error .unsupported

/-- Whether `opnd` references local `id` (unprojected or via any projection). -/
noncomputable def operandMentionsLocal (id : LocalId) : Operand → Bool
  | .copy p | .move p => Nat.beq p.localId id
  | .constant _ => false

/-- Whether `rvalue` is a whole-local copy or move of `dstLocalId`
(`_t = copy _t` or `_t = move _t`), which on non-immediate or padded tuple
locals triggers `copyRangesOverlap` UB in `rustc` / `vendor/lean-miri`
(`Miri/Interpreter/Place.lean::copyRuntimePlaceNoValidate`). -/
noncomputable def isWholeLocalSelfUse (dstLocalId : LocalId) : Rvalue → Bool
  | .use (.copy p) | .use (.move p) =>
    p.projection.isEmpty && Nat.beq p.localId dstLocalId
  | _ => false

/-- Evaluate an `Rvalue` in `M_tupleAssert`, extending
`Trusted.MirSemantics.evalRvalue` with `BinOp.{addWithOverflow,
subWithOverflow, mulWithOverflow}` (while `Rvalue.aggregateTuple` is evaluated
sequentially in place by `evalStatementExt` via `evalAggregateInPlaceExt`). -/
noncomputable def evalRvalueExt (bodyLocals : List MirTy)
    (locals : List LocalSlotExt) (dstTy : MirTy) :
    Rvalue → Except FaultKind (Val × List LocalSlotExt)
  | .use opnd =>
    match evalOperandToSlotExt bodyLocals locals opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals₁) =>
      if !(MirTy.beq srcTy dstTy) then
        .error .unsupported
      else
        match optVal with
        | some v => .ok (v, locals₁)
        | none => .error .undefined
  | .binaryOp op lhs rhs =>
    match evalPrimitiveOperandExt bodyLocals locals lhs with
    | .error k => .error k
    | .ok (lVal, locals₁) =>
      match evalPrimitiveOperandExt bodyLocals locals₁ rhs with
      | .error k => .error k
      | .ok (rVal, locals₂) =>
        if isWithOverflowBinOp op then
          match evalWithOverflowOp op lVal rVal with
          | .error k => .error k
          | .ok (resScalar, ovf) =>
            .ok (.tuple [.scalar resScalar, .bool ovf], locals₂)
        else
          match evalBinOp op lVal rVal with
          | .error k => .error k
          | .ok res => .ok (res, locals₂)
  | .unaryOp op opnd =>
    match evalPrimitiveOperandExt bodyLocals locals opnd with
    | .error k => .error k
    | .ok (v, locals₁) =>
      match evalUnOp op v with
      | .error k => .error k
      | .ok res => .ok (res, locals₁)
  | .discriminant place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match Trusted.MirSemantics.getElem? bodyLocals place.localId,
          Trusted.MirSemantics.getElem? locals place.localId with
      | some (.enum ety), some slot =>
        if !enumAdmitted ety then
          .error .unsupported
        else
          match ety.tagRepr, slot with
          | _, .dead => .error .undefined
          | _, .liveTuple _ => .error .unsupported
          | .zeroSized, .liveBase none =>
            match Trusted.MirSemantics.getElem? ety.discriminants 0 with
            | some disc =>
              .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
            | none => .error .unsupported
          | .zeroSized, .liveBase (some (.enumVal ety' v)) =>
            if EnumTy.beq ety ety' && Nat.beq v 0 then
              match Trusted.MirSemantics.getElem? ety.discriminants 0 with
              | some disc =>
                .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
              | none => .error .unsupported
            else
              .error .unsupported
          | .zeroSized, .liveBase (some _) => .error .unsupported
          | .scalar _ _, .liveBase none => .error .undefined
          | .scalar _ _, .liveBase (some (.enumVal ety' v)) =>
            if EnumTy.beq ety ety' && Nat.blt v ety.discriminants.length then
              match Trusted.MirSemantics.getElem? ety.discriminants v with
              | some disc =>
                .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
              | none => .error .unsupported
            else
              .error .unsupported
          | .scalar _ _, .liveBase (some _) => .error .unsupported
      | _, _ => .error .unsupported
  | .aggregateTuple _ | .ref _ _ | .addressOf _ _ | .unsupported =>
    .error .unsupported

/-- Write `val` into unprojected `dstLocalId` of type `dstTy` in `locals`:
checks `checkValExt val dstTy` first, then checks liveness (`DeadLocal` ->
`.error .undefined`). -/
noncomputable def writePlaceExt (locals : List LocalSlotExt)
    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlotExt) :=
  if !checkValExt val dstTy then
    .error .unsupported
  else
    match dstTy, val with
    | .tuple _, .tuple vs =>
      match Trusted.MirSemantics.getElem? locals dstLocalId with
      | none => .error .unsupported
      | some .dead => .error .undefined
      | some (.liveTuple _) =>
        match setElem? locals dstLocalId (.liveTuple (vs.map some)) with
        | some locals' => .ok locals'
        | none => .error .unsupported
      | some (.liveBase _) => .error .unsupported
    | _, _ =>
      match Trusted.MirSemantics.getElem? locals dstLocalId with
      | none => .error .unsupported
      | some .dead => .error .undefined
      | some (.liveBase _) =>
        match setElem? locals dstLocalId (.liveBase (some val)) with
        | some locals' => .ok locals'
        | none => .error .unsupported
      | some (.liveTuple _) => .error .unsupported

/-- Write `val` into field `idx` of a flat-tuple local `dstLocalId` of field
type `fieldTy` in `locals`. -/
noncomputable def writeTupleFieldExt (locals : List LocalSlotExt)
    (dstLocalId : LocalId) (idx : FieldIdx) (fieldTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlotExt) :=
  if !checkVal val fieldTy then
    .error .unsupported
  else
    match Trusted.MirSemantics.getElem? locals dstLocalId with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.liveTuple fields) =>
      match setElem? fields idx (some val) with
      | none => .error .unsupported
      | some fields' =>
        match setElem? locals dstLocalId (.liveTuple fields') with
        | some locals' => .ok locals'
        | none => .error .unsupported
    | some (.liveBase _) => .error .unsupported

/-- Evaluate and write `Rvalue.aggregateTuple` fields sequentially
left-to-right in place into flat tuple `dstLocalId`, mirroring
`rustc_const_eval/src/interpret/step.rs::write_aggregate` and
`vendor/lean-miri/Miri/Interpreter/Aggregate.lean`: each field `idx` evaluates
`op_idx`, validates static type equality, initialization, and value
well-formedness, and writes `dstLocalId.idx` via `writeTupleFieldExt` (so
`DeadLocal` fires on field `0` before evaluating operand `1`, and
`Operand.move` deinitialization from earlier operands is visible to later
operands). -/
noncomputable def evalAggregateInPlaceExt (bodyLocals : List MirTy)
    (locals : List LocalSlotExt) (dstLocalId : LocalId) :
    Nat → List Operand → List MirTy →
      Except FaultKind (List LocalSlotExt)
  | _, [], [] => .ok locals
  | idx, opnd :: restOps, fieldTy :: restTys =>
    match evalOperandToSlotExt bodyLocals locals opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals₁) =>
      if !MirTy.beq srcTy fieldTy then
        .error .unsupported
      else
        match optVal with
        | none => .error .undefined
        | some v =>
          match writeTupleFieldExt locals₁ dstLocalId idx fieldTy v with
          | .error k => .error k
          | .ok locals₂ =>
            evalAggregateInPlaceExt bodyLocals locals₂ dstLocalId
              (idx + 1) restOps restTys
  | _, _, _ => .error .unsupported

/-- Evaluate a single `StatementKind` in `M_tupleAssert`:
- Unprojected `.assign dst (.aggregateTuple ops)` into a flat tuple local
  fails closed with `.fault .unsupported` on any arity mismatch or
  self-aliasing destination (`ops.any (operandMentionsLocal dst.localId)`),
  and otherwise evaluates and writes fields sequentially left-to-right via
  `evalAggregateInPlaceExt`.
- Unprojected whole-tuple self-copy / self-move (`_t = copy _t` or
  `_t = move _t` when `dstTy` is `.tuple _`) fails closed with `.fault
  .unsupported` rather than masking `copyRangesOverlap` UB on non-immediate
  or padded tuples. -/
noncomputable def evalStatementExt (body : Body) (frame : FrameStateExt)
    (callerMem : CallerMemory) (stmt : StatementKind) :
    StepResult StateExt TerminalOutExt :=
  match stmt with
  | .nop =>
    .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }], callerMem }
  | .storageLive localId =>
    match Trusted.MirSemantics.getElem? body.locals localId with
    | none => .fault .unsupported
    | some localTy =>
      match setElem? frame.locals localId (liveUninitSlotExt localTy) with
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
    match dst.projection with
    | [] =>
      match Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
        match rvalue with
        | .aggregateTuple ops =>
          match dstTy with
          | .tuple fieldTys =>
            if !isFlatTupleTy (.tuple fieldTys) ||
                !Nat.beq ops.length fieldTys.length ||
                ops.any (operandMentionsLocal dst.localId) then
              .fault .unsupported
            else
              match evalAggregateInPlaceExt body.locals frame.locals
                  dst.localId 0 ops fieldTys with
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
          | _ => .fault .unsupported
        | _ =>
          let isTupleDst : Bool :=
            match dstTy with
            | .tuple _ => true
            | _ => false
          if isTupleDst && isWholeLocalSelfUse dst.localId rvalue then
            .fault .unsupported
          else
            match evalRvalueExt body.locals frame.locals dstTy rvalue with
            | .error k => .fault k
            | .ok (val, localsAfterRval) =>
              match writePlaceExt localsAfterRval dst.localId dstTy val with
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
    | [.field idx fieldTy] =>
      match Trusted.MirSemantics.getElem? body.locals dst.localId with
      | some (.tuple fieldTys) =>
        if !isFlatTupleTy (.tuple fieldTys) then
          .fault .unsupported
        else
          match Trusted.MirSemantics.getElem? fieldTys idx with
          | none => .fault .unsupported
          | some declFieldTy =>
            if !MirTy.beq fieldTy declFieldTy then
              .fault .unsupported
            else
              match evalRvalueExt body.locals frame.locals declFieldTy rvalue with
              | .error k => .fault k
              | .ok (val, localsAfterRval) =>
                match writeTupleFieldExt localsAfterRval dst.localId idx
                    declFieldTy val with
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
      | _ => .fault .unsupported
    | _ => .fault .unsupported
  | .unsupported => .fault .unsupported

/-- Jump to `(target, 0)` in `M_tupleAssert`. -/
noncomputable def jumpToBlockExt (frame : FrameStateExt)
    (callerMem : CallerMemory) (target : BasicBlockId) :
    StepResult StateExt TerminalOutExt :=
  .step {
    frames := [{ frame with blockIdx := target, stmtIdx := 0 }]
    callerMem
  }

/-- Whether `msg : AssertKind` is a modeled, valid `AssertMessage` (matching
`Miri.Interpreter.Panic.assertLangItem` in
`vendor/lean-miri/Miri/Interpreter/Panic.lean`), rejecting
`AssertKind.unsupported` and non-overflowing `BinOp`s inside
`AssertKind.overflow`. -/
noncomputable def isSupportedAssertKind : AssertKind → Bool
  | .overflow op =>
    match op with
    | .add | .sub | .mul | .div | .rem | .shl | .shr => true
    | _ => false
  | .overflowNeg | .divByZero | .remByZero
  | .boundsCheck | .misalignedPtrDeref | .nullPtrDeref => true
  | .unsupported => false

/-- Whether `unwind` is a non-cleanup `Assert` unwind action admitted by
`AssertLower` (`.continue_`, `.terminate`, or `.unreachable`). Failing
assertions with `.continue_` or `.terminate` produce a defined panic
(`TerminalOutExt.panic msg`); failing assertions with `.unreachable` produce
modeled UB (`.fault .undefined`, matching
`Miri.Interpreter.ControlFlow.unwindToBlock`); and `.cleanup _` fails closed
with `.fault .unsupported`. -/
noncomputable def isSupportedAssertUnwind : UnwindAction → Bool
  | .continue_ | .terminate | .unreachable => true
  | .cleanup _ => false

/-- Evaluate a basic block's `TerminatorKind` in `M_tupleAssert`, extending
`Trusted.MirSemantics.evalTerminator` with `TerminatorKind.assert` and flat
tuple return places.

On a failing `TerminatorKind.assert` (`b != expected`):
- Invalid or unmodeled messages (`!isSupportedAssertKind msg`, i.e.,
  `AssertKind.unsupported` or non-overflowing `AssertKind.overflow op`) fail
  closed with `.fault .unsupported` (matching
  `Miri.Interpreter.Panic.assertLangItem`).
- `UnwindAction.continue_` and `UnwindAction.terminate` terminate as a defined
  panic (`.done (.panic msg)`).
- `UnwindAction.unreachable` faults as modeled UB (`.fault .undefined`,
  matching `Miri.Interpreter.ControlFlow.unwindToBlock`).
- `UnwindAction.cleanup _` fails closed with `.fault .unsupported`.

Known `Trusted.MirAst` boundary: in `rustc` and
`vendor/lean-miri/Miri/Interpreter/Panic.lean` (`assertPanic`), failing
`BoundsCheck { len, index }` and `MisalignedPointerDereference { required,
found }` assertions evaluate their diagnostic operands before panicking
(raising UB if uninitialized or dead). Because `Trusted.MirAst.AssertKind`
erases those diagnostic operands, `M_tupleAssert` cannot evaluate them on the
failing path; this has zero soundness impact on
`NoPanicAndWellFormedTupleAssert`, where failing assertions are excluded. -/
noncomputable def evalTerminatorExt (body : Body) (bb : BasicBlock)
    (frame : FrameStateExt) (callerMem : CallerMemory) :
    StepResult StateExt TerminalOutExt :=
  match bb.terminator with
  | .goto target => jumpToBlockExt frame callerMem target
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    else
      match Trusted.MirSemantics.getElem? frame.locals 0 with
      | some (.liveBase (some retVal)) =>
        .done (.ret ⟨retVal, callerMem⟩)
      | some (.liveBase none) | some .dead => .fault .undefined
      | some (.liveTuple fields) =>
        match Trusted.MirSemantics.getElem? body.locals 0 with
        | some (.tuple fieldTys) =>
          if isFlatTupleTy (.tuple fieldTys) &&
              Nat.beq fields.length fieldTys.length then
            match extractAllInitFields fields with
            | some vs => .done (.ret ⟨.tuple vs, callerMem⟩)
            | none => .fault .undefined
          else
            .fault .unsupported
        | _ => .fault .unsupported
      | none => .fault .unsupported
  | .unreachable =>
    .fault .undefined
  | .switchInt discr targets =>
    match evalPrimitiveOperandExt body.locals frame.locals discr with
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
        jumpToBlockExt { frame with locals := localsAfterDiscr }
          callerMem target
  | .assert cond expected msg target unwind =>
    match evalPrimitiveOperandExt body.locals frame.locals cond with
    | .error k => .fault k
    | .ok (condVal, localsAfterCond) =>
      match condVal with
      | .bool b =>
        if b == expected then
          jumpToBlockExt { frame with locals := localsAfterCond }
            callerMem target
        else if !isSupportedAssertKind msg then
          .fault .unsupported
        else
          match unwind with
          | .continue_ | .terminate => .done (.panic msg)
          | .unreachable => .fault .undefined
          | .cleanup _ => .fault .unsupported
      | _ => .fault .unsupported
  | .unwindResume | .call _ _ _ _ _ | .unsupported =>
    .fault .unsupported

/-- Total single-step evaluator of `M_tupleAssert` directly over unmodified
`Trusted.MirAst.Program`. -/
noncomputable def evalStepTupleAssert (p : Program) (_c : Choice)
    (s : StateExt) : StepResult StateExt TerminalOutExt :=
  match s.frames with
  | [frame] =>
    match Trusted.MirSemantics.getElem? p.bodies frame.defId with
    | none => .fault .unsupported
    | some body =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some stmt => evalStatementExt body frame s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminatorExt body bb frame s.callerMem
          else
            .fault .unsupported
  | _ => .fault .unsupported

/-- Fuel-indexed deterministic evaluator for `M_tupleAssert`. -/
noncomputable def evalTupleAssertFuel (p : Program) :
    Nat → StateExt → StepResult StateExt TerminalOutExt
  | 0, s => .step s
  | fuel + 1, s =>
    match evalStepTupleAssert p 0 s with
    | .step s' => evalTupleAssertFuel p fuel s'
    | .done out => .done out
    | .fault k => .fault k

/-! ### Reachability, Well-Formedness, Panic-Freedom, Divergence, & Equivalence Judgments -/

/-- Admissible demonic choice predicate for `M_tupleAssert`. -/
noncomputable def ValidChoiceTupleAssert (_p : Program) (_s : StateExt)
    (c : Choice) : Prop :=
  c = 0

/-- Relational small-step transition in `M_tupleAssert`. -/
noncomputable def StepTupleAssert (p : Program) (s : StateExt)
    (res : StepResult StateExt TerminalOutExt) : Prop :=
  ∃ c : Choice, ValidChoiceTupleAssert p s c ∧ evalStepTupleAssert p c s = res

/-- Finite-step state reachability in `M_tupleAssert`. -/
inductive ReachesTupleAssert (p : Program) :
    StateExt → StateExt → Prop where
  | refl (s : StateExt) : ReachesTupleAssert p s s
  | tail {s₁ s₂ s₃ : StateExt} :
      ReachesTupleAssert p s₁ s₂ →
      StepTupleAssert p s₂ (.step s₃) →
      ReachesTupleAssert p s₁ s₃

/-- Outcome `res` is reached from `(p, q)` under `M_tupleAssert`. -/
noncomputable def ReachesResultTupleAssert (p : Program) (q : Query)
    (res : StepResult StateExt TerminalOutExt) : Prop :=
  match initStateTupleAssert p q with
  | .error k => res = .fault k
  | .ok s₀ =>
    ∃ s : StateExt, ReachesTupleAssert p s₀ s ∧ StepTupleAssert p s res

/-- All-prefix UB- and unsupported-freedom in `M_tupleAssert` (defined Rust
panics `.done (.panic _)` remain permitted under `WellFormedTupleAssert` and
are excluded separately by `NoPanicAndWellFormedTupleAssert`). -/
noncomputable def WellFormedTupleAssert (p : Program) (q : Query) : Prop :=
  (∃ s₀ : StateExt, initStateTupleAssert p q = .ok s₀ ∧
    ∀ s : StateExt, ReachesTupleAssert p s₀ s →
      ∃ c : Choice, ValidChoiceTupleAssert p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResultTupleAssert p q (.fault k))

/-- Observable terminal behavior (`.ret out` or `.panic kind`) of `(p, q)` in
`M_tupleAssert`. -/
noncomputable def BehaviorTupleAssert (p : Program) (q : Query)
    (out : TerminalOutExt) : Prop :=
  ReachesResultTupleAssert p q (.done out)

/-- Panic-free AND UB/unsupported-free execution judgment in `M_tupleAssert`:
`(p, q)` never faults (`.fault .undefined` or `.fault .unsupported`) AND never
triggers a failing `TerminatorKind.assert` (`.done (.panic _)`). -/
noncomputable def NoPanicAndWellFormedTupleAssert (p : Program) (q : Query) :
    Prop :=
  WellFormedTupleAssert p q ∧
  (∀ msg : AssertKind, ¬ BehaviorTupleAssert p q (.panic msg))

/-- Constructive divergence in `M_tupleAssert`: from `initStateTupleAssert p q
= .ok s₀`, every finite fuel step `n : Nat` remains in `.step s'`. -/
noncomputable def DivergesTupleAssert (p : Program) (q : Query) : Prop :=
  ∃ s₀ : StateExt,
    initStateTupleAssert p q = .ok s₀ ∧
    ∀ n : Nat, ∃ s' : StateExt, evalTupleAssertFuel p n s₀ = .step s'

/-- No-panic partial-correctness contract satisfaction in `M_tupleAssert`. -/
noncomputable def SatisfiesPostNoPanicTupleAssert (p : Program) (q : Query)
    (post : Out → Prop) : Prop :=
  NoPanicAndWellFormedTupleAssert p q ∧
  ∀ out : Out, BehaviorTupleAssert p q (.ret out) → post out

/-- Static body admission predicate for `M_tupleAssert`, extending
`Trusted.MirSemantics.BodyStaticAdmitted` to flat tuples. -/
noncomputable def BodyStaticAdmittedTupleAssert (p : Program) (body : Body) :
    Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    !stringBeq body.identity "" &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    body.locals.all isSupportedTupleOrScalarTy

/-- Entry argument well-typedness predicate for `M_tupleAssert`. -/
noncomputable def ValidEntryArgsTupleAssert (body : Body)
    (args : List Val) : Prop :=
  checkArgsMatchExt args ((body.locals.drop 1).take body.argumentCount) = true

/-- Per-body panic-free and UB-free verification judgment in `M_tupleAssert`,
mirroring `Trusted.MirSemantics.BodyVerified`. -/
noncomputable def BodyVerifiedNoPanicTupleAssert (p : Program) (defId : DefId)
    (body : Body) (safetyPre : List Val → Prop) : Prop :=
  Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
  BodyStaticAdmittedTupleAssert p body = true ∧
  ∀ args : List Val,
    ValidEntryArgsTupleAssert body args →
    (body.isUnsafe = true → safetyPre args) →
    NoPanicAndWellFormedTupleAssert (entryProgForBody p defId) { args := args }

/-- Program-wide panic-free and UB-free verification judgment in
`M_tupleAssert`, mirroring `Trusted.MirSemantics.ProgramVerified`. -/
noncomputable def ProgramVerifiedNoPanicTupleAssert (p : Program)
    (specs : Specs) : Prop :=
  Nat.beq p.pointerWidthBits 64 = true ∧
  Nat.beq p.mirProfileVersion 1 = true ∧
  !p.bodies.isEmpty = true ∧
  Nat.blt p.entryDefId p.bodies.length = true ∧
  bodiesHaveUniqueIdentities p.bodies = true ∧
  (∀ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body →
    BodyVerifiedNoPanicTupleAssert p defId body (specs.safety body.identity)) ∧
  specs.property p

/-- Whole-crate panic-free and UB-free verification obligation in
`M_tupleAssert`, mirroring `Trusted.MirSemantics.CrateTheorem`. -/
noncomputable def CrateTheoremNoPanicTupleAssert (c : Crate) : Prop :=
  c.program.scope = .crate ∧
  ProgramVerifiedNoPanicTupleAssert c.program c.specs

/-- Proof-unit panic-free and UB-free verification obligation in
`M_tupleAssert`, mirroring `Trusted.MirSemantics.UnitTheorem`. -/
noncomputable def UnitTheoremNoPanicTupleAssert (c : Crate) : Prop :=
  c.program.scope = .unit ∧
  ProgramVerifiedNoPanicTupleAssert c.program c.specs

/-- Bundled intraprocedural bidirectional semantic equivalence on unmodified
`Trusted.MirSemantics` (matching `F1_9.FullSemanticEquiv` /
`F1_10.FullSemanticEquiv` for vertical composition with post-lowering
optimization pipelines). -/
noncomputable def FullSemanticEquiv (pSrc pTgt : Program) : Prop :=
  (∀ q : Query,
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q)) ∧
  (∀ (q : Query) (post : TerminalOut → Prop),
    SatisfiesPost pTgt q post ↔ SatisfiesPost pSrc q post) ∧
  (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
    Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
    Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
    (BodyVerified pTgt defId bTgt safetyPre ↔
      BodyVerified pSrc defId bSrc safetyPre))

/-- Bundled exact bidirectional semantic equivalence in `M_tupleAssert`
(preserving well-formedness, panic-freedom, exact return and panic outcomes,
exact fault kinds, divergence, postconditions, and per-body verification). -/
noncomputable def FullSemanticEquivTupleAssert (pSrc pTgt : Program) : Prop :=
  (∀ q : Query,
    (WellFormedTupleAssert pTgt q ↔ WellFormedTupleAssert pSrc q) ∧
    (NoPanicAndWellFormedTupleAssert pTgt q ↔
      NoPanicAndWellFormedTupleAssert pSrc q) ∧
    (∀ out : TerminalOutExt,
      BehaviorTupleAssert pTgt q out ↔ BehaviorTupleAssert pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResultTupleAssert pTgt q (.fault k) ↔
        ReachesResultTupleAssert pSrc q (.fault k)) ∧
    (DivergesTupleAssert pTgt q ↔ DivergesTupleAssert pSrc q)) ∧
  (∀ (q : Query) (post : Out → Prop),
    SatisfiesPostNoPanicTupleAssert pTgt q post ↔
      SatisfiesPostNoPanicTupleAssert pSrc q post) ∧
  (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
    Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
    Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
    (BodyVerifiedNoPanicTupleAssert pTgt defId bTgt safetyPre ↔
      BodyVerifiedNoPanicTupleAssert pSrc defId bSrc safetyPre))

/-- No-panic observable equivalence in `M_tupleAssert`, preserved across
`SROA`, `AssertConstFold`, `AssertLower` (which turns defined panics into
`.fault .undefined` while preserving all non-panicking executions identically),
and post-lowering `FullSemanticEquiv` passes. -/
noncomputable def NoPanicSemanticEquivTupleAssert (pSrc pTgt : Program) :
    Prop :=
  (∀ q : Query,
    (NoPanicAndWellFormedTupleAssert pTgt q ↔
      NoPanicAndWellFormedTupleAssert pSrc q) ∧
    (∀ out : Out,
      BehaviorTupleAssert pTgt q (.ret out) ↔
        BehaviorTupleAssert pSrc q (.ret out)) ∧
    (DivergesTupleAssert pTgt q ↔ DivergesTupleAssert pSrc q)) ∧
  (∀ (q : Query) (post : Out → Prop),
    SatisfiesPostNoPanicTupleAssert pTgt q post ↔
      SatisfiesPostNoPanicTupleAssert pSrc q post) ∧
  (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
    Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
    Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
    (BodyVerifiedNoPanicTupleAssert pTgt defId bTgt safetyPre ↔
      BodyVerifiedNoPanicTupleAssert pSrc defId bSrc safetyPre))

/-- Select body `u` of `p` as a `.unit`-scoped proof-unit subject. -/
noncomputable def unitProgForDef (p : Program) (u : DefId) : Program :=
  { p with entryDefId := u, scope := .unit }

/-- Semantic invariance of `specs.property` across
`NoPanicSemanticEquivTupleAssert`-equivalent programs, automatically satisfied
by `property := fun _ => True` and by any behavioral contract stated over
`M_tupleAssert`'s `NoPanicAndWellFormedTupleAssert`, return
`BehaviorTupleAssert (.ret out)`, or `DivergesTupleAssert` (which by Theorem 1
coincide with unmodified `Trusted.MirSemantics.{WellFormed, Behavior,
Diverges}` on flat assert-free programs). -/
noncomputable def SpecsPropertyNoPanicInvariant (specs : Specs) : Prop :=
  ∀ p₁ p₂ : Program, NoPanicSemanticEquivTupleAssert p₁ p₂ →
    (specs.property p₁ ↔ specs.property p₂)

/-- Whether terminator `t` is `TerminatorKind.assert`. -/
noncomputable def isAssertTerminator : TerminatorKind → Bool
  | .assert _ _ _ _ _ => true
  | _ => false

/-- Whether `body` contains any `TerminatorKind.assert` terminator. -/
noncomputable def bodyHasAssert (body : Body) : Bool :=
  body.basicBlocks.any (fun bb => isAssertTerminator bb.terminator)

/-- Whether `body` uses only `Trusted.MirSemantics`-native local types
(`isSupportedScalarOrUnitTy`) and contains no `TerminatorKind.assert`. -/
noncomputable def isFlatAssertFreeBody (body : Body) : Bool :=
  body.locals.all isSupportedScalarOrUnitTy && !bodyHasAssert body

/-- Whether every body in `p.bodies` is flat and assert-free. -/
noncomputable def isFlatAssertFreeProgram (p : Program) : Bool :=
  p.bodies.all isFlatAssertFreeBody

/-- Whether the active body of a `Trusted.MirSemantics.State` in `p` (if in
bounds) is flat and assert-free. -/
noncomputable def stepIsFlatAssertFree (p : Program) (s : State) : Bool :=
  match s.frames with
  | [frame] =>
    match Trusted.MirSemantics.getElem? p.bodies frame.defId with
    | none => true
    | some body => isFlatAssertFreeBody body
  | _ => true

/-! ## Part II: Certified Tuple/WithOverflow `SROA`, `Assert` Const-Fold, & `Assert` Lowering -/

/-! ### Static Local/Block Bounds & Place/Operand Typing Helpers -/

/-- Check that every `LocalId` referenced by `opnd` is `< bound`. -/
noncomputable def operandLocalsLt (bound : Nat) : Operand → Bool
  | .copy p | .move p => Nat.blt p.localId bound
  | .constant _ => true

/-- Check that every `LocalId` referenced by `rv` is `< bound`. -/
noncomputable def rvalueLocalsLt (bound : Nat) : Rvalue → Bool
  | .use o | .unaryOp _ o => operandLocalsLt bound o
  | .binaryOp _ l r => operandLocalsLt bound l && operandLocalsLt bound r
  | .discriminant p | .ref _ p | .addressOf _ p => Nat.blt p.localId bound
  | .aggregateTuple fs => fs.all (operandLocalsLt bound)
  | .unsupported => true

/-- Check that every `LocalId` referenced by `stmt` is `< bound`. -/
noncomputable def stmtLocalsLt (bound : Nat) : StatementKind → Bool
  | .assign dst rv => Nat.blt dst.localId bound && rvalueLocalsLt bound rv
  | .storageLive id | .storageDead id => Nat.blt id bound
  | .nop | .unsupported => true

/-- Check that every `LocalId` referenced by `term` is `< bound`. -/
noncomputable def terminatorLocalsLt (bound : Nat) : TerminatorKind → Bool
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .switchInt d _ => operandLocalsLt bound d
  | .assert c _ _ _ _ => operandLocalsLt bound c
  | .call _ args dst _ _ =>
    args.all (operandLocalsLt bound) && Nat.blt dst.localId bound

/-- Check that every `LocalId` referenced in `b` is strictly `<
b.locals.length` (preventing out-of-bounds locals from aliasing fresh SROA
scalar or scratch locals). -/
noncomputable def bodyAllLocalsInBounds (b : Body) : Bool :=
  let bound := b.locals.length
  b.basicBlocks.all (fun bb =>
    bb.statements.all (stmtLocalsLt bound) &&
      terminatorLocalsLt bound bb.terminator)

/-- Check that any cleanup target in `u` is `< bound`. -/
noncomputable def unwindBlocksLt (bound : Nat) : UnwindAction → Bool
  | .continue_ | .unreachable | .terminate => true
  | .cleanup b => Nat.blt b bound

/-- Check that every `BasicBlockId` referenced by `term` is `< bound`. -/
noncomputable def terminatorBlocksLt (bound : Nat) : TerminatorKind → Bool
  | .goto t => Nat.blt t bound
  | .switchInt _ ts =>
    Nat.blt ts.otherwise bound &&
      ts.branches.all (fun br => Nat.blt br.2 bound)
  | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .assert _ _ _ t u => Nat.blt t bound && unwindBlocksLt bound u
  | .call _ _ _ tgt u =>
    (match tgt with | none => true | some b => Nat.blt b bound) &&
      unwindBlocksLt bound u

/-- Check that every basic-block target in `b` is strictly `<
b.basicBlocks.length` (preventing out-of-bounds jumps from aliasing a freshly
appended `.unreachable` block during `Assert` lowering). -/
noncomputable def bodyAllBlocksInBounds (b : Body) : Bool :=
  let bound := b.basicBlocks.length
  b.basicBlocks.all (fun bb => terminatorBlocksLt bound bb.terminator)

/-- Resolve the static `MirTy` of an unprojected place or a single-step
`ProjectionElem.field` on a flat tuple local. -/
noncomputable def placeStaticTy? (bodyLocals : List MirTy) (p : Place) :
    Option MirTy :=
  match Trusted.MirSemantics.getElem? bodyLocals p.localId with
  | none => none
  | some baseTy =>
    match p.projection with
    | [] => some baseTy
    | [.field idx ty] =>
      match baseTy with
      | .tuple fieldTys =>
        if isFlatTupleTy (.tuple fieldTys) then
          match Trusted.MirSemantics.getElem? fieldTys idx with
          | some fty => if MirTy.beq ty fty then some fty else none
          | none => none
        else
          none
      | _ => none
    | _ => none

/-- Resolve the static `MirTy` of an `Operand`. -/
noncomputable def operandStaticTy? (bodyLocals : List MirTy) :
    Operand → Option MirTy
  | .copy p | .move p => placeStaticTy? bodyLocals p
  | .constant c => some c.ty

/-- Check that `optTy` equals `some ty` under `MirTy.beq`. -/
noncomputable def optMirTyEq (optTy : Option MirTy) (ty : MirTy) : Bool :=
  match optTy with
  | some t => MirTy.beq t ty
  | none => false

/-! ### Certified Tuple & Unsigned `*WithOverflow` `SROA` (`SroaTuplePlan` & `SroaTrace`) -/

/-- Descriptor targeting one non-escaping flat-tuple local `tupLocal` inside
body `defId` for Scalar Replacement of Aggregates (`SROA`). -/
structure SroaTuplePlan where
  defId : DefId
  tupLocal : LocalId

/-- Arbitrary finite sequence of `SroaTuplePlan` steps. -/
abbrev SroaTrace := List SroaTuplePlan

/-- Check that `p` is a valid single-field projection
`⟨tupLocal, [.field idx ty]⟩` into flat-tuple `tupLocal` of field types
`fieldTys`. -/
noncomputable def isValidTupleFieldPlace (tupLocal : LocalId)
    (fieldTys : List MirTy) (p : Place) : Bool :=
  Nat.beq p.localId tupLocal &&
    match p.projection with
    | [.field idx ty] =>
      match Trusted.MirSemantics.getElem? fieldTys idx with
      | some fty => MirTy.beq ty fty
      | none => false
    | _ => false

/-- Check that `opnd` references `tupLocal` ONLY through valid single-field
projections (never whole-tuple `.copy`/`.move`). -/
noncomputable def operandTupleValid (tupLocal : LocalId)
    (fieldTys : List MirTy) : Operand → Bool
  | .copy p | .move p =>
    if Nat.beq p.localId tupLocal then
      isValidTupleFieldPlace tupLocal fieldTys p
    else
      true
  | .constant _ => true

/-- Check that `rv` references `tupLocal` ONLY through valid single-field
operands (rejecting escaping `Rvalue.ref` / `Rvalue.addressOf`, whole-tuple
`Copy`/`Move`, and `Rvalue.discriminant` on `tupLocal`). -/
noncomputable def rvalueTupleValid (tupLocal : LocalId)
    (fieldTys : List MirTy) : Rvalue → Bool
  | .use o | .unaryOp _ o => operandTupleValid tupLocal fieldTys o
  | .binaryOp _ l r =>
    operandTupleValid tupLocal fieldTys l &&
      operandTupleValid tupLocal fieldTys r
  | .discriminant p | .ref _ p | .addressOf _ p => !Nat.beq p.localId tupLocal
  | .aggregateTuple ops => ops.all (operandTupleValid tupLocal fieldTys)
  | .unsupported => true

/-- Whether `op` is a SROA-lowerable unsigned overflowing arithmetic operator
(`.addWithOverflow` or `.subWithOverflow`). -/
noncomputable def isSroaLowerableOvfBinOp : BinOp → Bool
  | .addWithOverflow | .subWithOverflow => true
  | _ => false

/-- Extract the unsigned integer width `w` when `fieldTys` is the 2-tuple
`[.int w false, .bool]` produced by unsigned checked addition/subtraction. -/
noncomputable def unsignedOvfTupleWidth? : List MirTy → Option IntWidth
  | [.int w false, .bool] => some w
  | _ => none

/-- Check that statement `stmt` uses `tupLocal` strictly within the certified
non-escaping SROA fragment. -/
noncomputable def stmtTupleValid (bodyLocals : List MirTy) (tupLocal : LocalId)
    (fieldTys : List MirTy) : StatementKind → Bool
  | .storageLive _ | .storageDead _ | .nop | .unsupported => true
  | .assign dst rv =>
    if Nat.beq dst.localId tupLocal then
      match dst.projection with
      | [] =>
        match rv with
        | .aggregateTuple ops =>
          ops.all (fun o => !operandMentionsLocal tupLocal o) &&
            listRel (fun op ty => optMirTyEq (operandStaticTy? bodyLocals op) ty)
              ops fieldTys
        | .binaryOp op lhs rhs =>
          if isSroaLowerableOvfBinOp op then
            match unsignedOvfTupleWidth? fieldTys with
            | some w =>
              let uTy : MirTy := .int w false
              operandTupleValid tupLocal fieldTys lhs &&
                operandTupleValid tupLocal fieldTys rhs &&
                optMirTyEq (operandStaticTy? bodyLocals lhs) uTy &&
                optMirTyEq (operandStaticTy? bodyLocals rhs) uTy
            | none => false
          else
            false
        | _ => false
      | [.field _ _] =>
        isValidTupleFieldPlace tupLocal fieldTys dst &&
          rvalueTupleValid tupLocal fieldTys rv
      | _ => false
    else
      rvalueTupleValid tupLocal fieldTys rv

/-- Check that terminator `term` uses `tupLocal` strictly within the certified
non-escaping SROA fragment. -/
noncomputable def terminatorTupleValid (tupLocal : LocalId)
    (fieldTys : List MirTy) : TerminatorKind → Bool
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .switchInt d _ => operandTupleValid tupLocal fieldTys d
  | .assert c _ _ _ _ => operandTupleValid tupLocal fieldTys c
  | .call _ args dst _ _ =>
    args.all (operandTupleValid tupLocal fieldTys) &&
      !Nat.beq dst.localId tupLocal

/-- Check that every statement and terminator in `body` respects the certified
non-escaping SROA fragment for `tupLocal`. -/
noncomputable def bodyTupleUsesValid (body : Body) (tupLocal : LocalId)
    (fieldTys : List MirTy) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (stmtTupleValid body.locals tupLocal fieldTys) &&
      terminatorTupleValid tupLocal fieldTys bb.terminator)

/-- Whether `body` contains any whole-tuple `.addWithOverflow` /
`.subWithOverflow` assignment into `tupLocal`. -/
noncomputable def bodyHasTupleOvfAssign (body : Body) (tupLocal : LocalId) :
    Bool :=
  body.basicBlocks.any (fun bb =>
    bb.statements.any (fun stmt =>
      match stmt with
      | .assign dst (.binaryOp op _ _) =>
        Nat.beq dst.localId tupLocal && dst.projection.isEmpty &&
          isSroaLowerableOvfBinOp op
      | _ => false))

/-- Rewrite `Place ⟨tupLocal, [.field idx _]⟩` to `Place ⟨base + idx, []⟩`. -/
noncomputable def rewriteTuplePlace (tupLocal base : Nat) (p : Place) :
    Place :=
  if Nat.beq p.localId tupLocal then
    match p.projection with
    | [.field idx _] => ⟨base + idx, []⟩
    | _ => p
  else
    p

/-- Rewrite field projections of `tupLocal` inside an `Operand`. -/
noncomputable def rewriteTupleOperand (tupLocal base : Nat) :
    Operand → Operand
  | .copy p => .copy (rewriteTuplePlace tupLocal base p)
  | .move p => .move (rewriteTuplePlace tupLocal base p)
  | .constant c => .constant c

/-- Rewrite field projections of `tupLocal` inside an `Rvalue`. -/
noncomputable def rewriteTupleRvalue (tupLocal base : Nat) : Rvalue → Rvalue
  | .use o => .use (rewriteTupleOperand tupLocal base o)
  | .binaryOp op l r =>
    .binaryOp op (rewriteTupleOperand tupLocal base l)
      (rewriteTupleOperand tupLocal base r)
  | .unaryOp op o => .unaryOp op (rewriteTupleOperand tupLocal base o)
  | .discriminant p => .discriminant p
  | .ref m p => .ref m p
  | .addressOf m p => .addressOf m p
  | .aggregateTuple ops =>
    .aggregateTuple (ops.map (rewriteTupleOperand tupLocal base))
  | .unsupported => .unsupported

/-- Rewrite field projections of `tupLocal` inside a `TerminatorKind`. -/
noncomputable def rewriteTupleTerminator (tupLocal base : Nat) :
    TerminatorKind → TerminatorKind
  | .goto t => .goto t
  | .switchInt d ts => .switchInt (rewriteTupleOperand tupLocal base d) ts
  | .return_ => .return_
  | .unreachable => .unreachable
  | .unwindResume => .unwindResume
  | .assert c e m t u =>
    .assert (rewriteTupleOperand tupLocal base c) e m t u
  | .call f args dst t u =>
    .call f (args.map (rewriteTupleOperand tupLocal base)) dst t u
  | .unsupported => .unsupported

/-- Emit `[StorageLive (base + idx), ..., StorageLive (base + idx + count - 1)]`. -/
noncomputable def mkStorageLivesLoop (base : Nat) :
    Nat → Nat → List StatementKind
  | _, 0 => []
  | idx, count + 1 =>
    .storageLive (base + idx) :: mkStorageLivesLoop base (idx + 1) count

/-- Emit `[StorageDead (base + idx), ..., StorageDead (base + idx + count - 1)]`. -/
noncomputable def mkStorageDeadsLoop (base : Nat) :
    Nat → Nat → List StatementKind
  | _, 0 => []
  | idx, count + 1 =>
    .storageDead (base + idx) :: mkStorageDeadsLoop base (idx + 1) count

/-- Emit sequential assignments `dstBase + i := .use op_i` left-to-right. -/
noncomputable def mkIndexedUseAssignsLoop (dstBase : Nat) :
    Nat → List Operand → List StatementKind
  | _, [] => []
  | idx, opnd :: rest =>
    .assign ⟨dstBase + idx, []⟩ (.use opnd) ::
      mkIndexedUseAssignsLoop dstBase (idx + 1) rest

/-- Pure total `flatMap` over lists (avoiding `List.flatMap` foundation
variation). -/
noncomputable def listFlatMap {α β : Type} (f : α → List β) :
    List α → List β
  | [] => []
  | x :: xs => f x ++ listFlatMap f xs

/-- Lower a single MIR statement under `SROA` for `tupLocal`: lowers
non-aliasing `Rvalue.aggregateTuple` directly to left-to-right scalar field
assignments (`mkIndexedUseAssignsLoop base 0 ops'`, matching
`evalAggregateInPlaceExt` bit-for-bit on `Operand.move` deinitialization and
field-0 `DeadLocal` fault ordering), and uses fresh scratch temps
(`ovfTmpBase`) for unsigned `addWithOverflow` / `subWithOverflow` to preserve
single-time left-to-right operand evaluation, `Operand.move` deinitialization,
self-referencing carry semantics, and write-time `DeadLocal` fault ordering. -/
noncomputable def lowerSroaStmt (tupLocal fieldCount base ovfTmpBase : Nat) :
    StatementKind → List StatementKind
  | .storageLive id =>
    if Nat.beq id tupLocal then
      mkStorageLivesLoop base 0 fieldCount
    else
      [.storageLive id]
  | .storageDead id =>
    if Nat.beq id tupLocal then
      mkStorageDeadsLoop base 0 fieldCount
    else
      [.storageDead id]
  | .assign dst rv =>
    if Nat.beq dst.localId tupLocal then
      match dst.projection with
      | [] =>
        match rv with
        | .aggregateTuple ops =>
          let ops' := ops.map (rewriteTupleOperand tupLocal base)
          mkIndexedUseAssignsLoop base 0 ops'
        | .binaryOp .addWithOverflow lhs rhs =>
          [
            .storageLive ovfTmpBase,
            .storageLive (ovfTmpBase + 1),
            .assign ⟨ovfTmpBase, []⟩
              (.use (rewriteTupleOperand tupLocal base lhs)),
            .assign ⟨ovfTmpBase + 1, []⟩
              (.use (rewriteTupleOperand tupLocal base rhs)),
            .assign ⟨base, []⟩
              (.binaryOp .add (.copy ⟨ovfTmpBase, []⟩)
                (.copy ⟨ovfTmpBase + 1, []⟩)),
            .assign ⟨base + 1, []⟩
              (.binaryOp .lt (.copy ⟨base, []⟩) (.copy ⟨ovfTmpBase, []⟩)),
            .storageDead ovfTmpBase,
            .storageDead (ovfTmpBase + 1)
          ]
        | .binaryOp .subWithOverflow lhs rhs =>
          [
            .storageLive ovfTmpBase,
            .storageLive (ovfTmpBase + 1),
            .assign ⟨ovfTmpBase, []⟩
              (.use (rewriteTupleOperand tupLocal base lhs)),
            .assign ⟨ovfTmpBase + 1, []⟩
              (.use (rewriteTupleOperand tupLocal base rhs)),
            .assign ⟨base, []⟩
              (.binaryOp .sub (.copy ⟨ovfTmpBase, []⟩)
                (.copy ⟨ovfTmpBase + 1, []⟩)),
            .assign ⟨base + 1, []⟩
              (.binaryOp .lt (.copy ⟨ovfTmpBase, []⟩)
                (.copy ⟨ovfTmpBase + 1, []⟩)),
            .storageDead ovfTmpBase,
            .storageDead (ovfTmpBase + 1)
          ]
        | _ => [.assign dst (rewriteTupleRvalue tupLocal base rv)]
      | [.field idx _] =>
        [.assign ⟨base + idx, []⟩ (rewriteTupleRvalue tupLocal base rv)]
      | _ => [.assign dst (rewriteTupleRvalue tupLocal base rv)]
    else
      [.assign dst (rewriteTupleRvalue tupLocal base rv)]
  | .nop => [.nop]
  | .unsupported => [.unsupported]

/-- Deterministically apply one certified `SroaTuplePlan` to `pSrc`, failing
closed (`none`) whenever any non-escape, bounds, or static-typing guard is
violated. -/
noncomputable def applyMirSroaTuple (plan : SroaTuplePlan) (pSrc : Program) :
    Option Program :=
  match Trusted.MirSemantics.getElem? pSrc.bodies plan.defId with
  | none => none
  | some bodySrc =>
    if bodySrc.basicBlocks.isEmpty ||
        !Nat.blt bodySrc.argumentCount plan.tupLocal ||
        !Nat.blt plan.tupLocal bodySrc.locals.length ||
        !bodyAllLocalsInBounds bodySrc then
      none
    else
      match Trusted.MirSemantics.getElem? bodySrc.locals plan.tupLocal with
      | some (.tuple fieldTys) =>
        if !isFlatTupleTy (.tuple fieldTys) ||
            !bodyTupleUsesValid bodySrc plan.tupLocal fieldTys then
          none
        else
          let fieldCount := fieldTys.length
          let base := bodySrc.locals.length
          let hasOvf := bodyHasTupleOvfAssign bodySrc plan.tupLocal
          let ovfTys : List MirTy :=
            if hasOvf then
              match unsignedOvfTupleWidth? fieldTys with
              | some w => [.int w false, .int w false]
              | none => []
            else
              []
          let ovfTmpBase := base + fieldCount
          match setElem? bodySrc.locals plan.tupLocal .unit with
          | none => none
          | some localsUpdated =>
            let localsTgt := localsUpdated ++ fieldTys ++ ovfTys
            let blocksTgt := bodySrc.basicBlocks.map (fun bb => {
              statements :=
                listFlatMap
                  (lowerSroaStmt plan.tupLocal fieldCount base ovfTmpBase)
                  bb.statements
              terminator :=
                rewriteTupleTerminator plan.tupLocal base bb.terminator
              cleanup := bb.cleanup
            })
            let bodyTgt : Body := {
              bodySrc with
              locals := localsTgt
              basicBlocks := blocksTgt
            }
            match setElem? pSrc.bodies plan.defId bodyTgt with
            | none => none
            | some bodiesTgt => some { pSrc with bodies := bodiesTgt }
      | _ => none

/-- Decidable single-local `SROA` validator checking `pSrc --[plan]--> pTgt`. -/
noncomputable def checkMirSroaTuple (plan : SroaTuplePlan)
    (pSrc pTgt : Program) : Bool :=
  match applyMirSroaTuple plan pSrc with
  | some pOut => programEq pOut pTgt
  | none => false

/-- Execute an arbitrary finite `SroaTrace` on `pSrc`. -/
noncomputable def applyMirSroaTrace : SroaTrace → Program → Option Program
  | [], p => some p
  | plan :: rest, p =>
    match applyMirSroaTuple plan p with
    | some pMid => applyMirSroaTrace rest pMid
    | none => none

/-- Decidable multi-tuple `SROA` validator checking `pSrc --[trace]*--> pTgt`. -/
noncomputable def checkMirSroaTrace (trace : SroaTrace)
    (pSrc pTgt : Program) : Bool :=
  match applyMirSroaTrace trace pSrc with
  | some pOut => programEq pOut pTgt
  | none => false

/-! ### Certified Constant-True `Assert` Folding (`AssertConstFold`) -/

/-- Return `some target` when `term` is a statically canonical constant-true
`TerminatorKind.assert` (`cond = .constant ⟨.bool, .scalar bits⟩` with `bits =
1` when `expected = true` or `bits = 0` when `expected = false`). Rejects
non-canonical boolean bit patterns (`bits ≥ 2`) which trigger `.fault
.undefined` or `.fault .unsupported` in `evalConstLit`. -/
noncomputable def constTrueAssertTarget? :
    TerminatorKind → Option BasicBlockId
  | .assert (.constant c) expected _ target _ =>
    match c.ty, c.lit with
    | .bool, .scalar bits =>
      if bits == BitVec.ofNat 128 (if expected then 1 else 0) then
        some target
      else
        none
    | _, _ => none
  | _ => none

/-- Fold a constant-true `TerminatorKind.assert` in `bb` to `.goto target`. -/
noncomputable def applyMirAssertConstFoldBlock (bb : BasicBlock) : BasicBlock :=
  match constTrueAssertTarget? bb.terminator with
  | some target => { bb with terminator := .goto target }
  | none => bb

/-- Fold all constant-true `TerminatorKind.assert` terminators in `body`. -/
noncomputable def applyMirAssertConstFoldBody (body : Body) : Body :=
  { body with basicBlocks := body.basicBlocks.map applyMirAssertConstFoldBlock }

/-- Fold all constant-true `TerminatorKind.assert` terminators across all
bodies of `p`. -/
noncomputable def applyMirAssertConstFold (p : Program) : Program :=
  { p with bodies := p.bodies.map applyMirAssertConstFoldBody }

/-- Check that `bbTgt` matches `bbSrc` up to folding a constant-true
`TerminatorKind.assert` to `.goto target`. -/
noncomputable def checkMirAssertConstFoldBlock (bbSrc bbTgt : BasicBlock) :
    Bool :=
  (bbSrc.cleanup == bbTgt.cleanup) &&
    listRel stmtEq bbSrc.statements bbTgt.statements &&
    (terminatorEq bbSrc.terminator bbTgt.terminator ||
      match constTrueAssertTarget? bbSrc.terminator, bbTgt.terminator with
      | some targetSrc, .goto targetTgt => Nat.beq targetSrc targetTgt
      | _, _ => false)

/-- Check that `bTgt` matches `bSrc` up to constant-true `Assert` folding. -/
noncomputable def checkMirAssertConstFoldBody (bSrc bTgt : Body) : Bool :=
  bodyHeaderEq bSrc bTgt &&
    listRel checkMirAssertConstFoldBlock bSrc.basicBlocks bTgt.basicBlocks

/-- Decidable validator for constant-true `TerminatorKind.assert` folding
(`pSrc --[AssertConstFold]--> pTgt`), accepting both selective and
whole-program folding (`applyMirAssertConstFold`). -/
noncomputable def checkMirAssertConstFold (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel checkMirAssertConstFoldBody pSrc.bodies pTgt.bodies

/-! ### Certified `Assert`-to-`SwitchInt`+`Unreachable` Lowering (`AssertLower`) -/

/-- Check that every `TerminatorKind.assert` in `body` carries a supported
`AssertKind` (`isSupportedAssertKind`), a non-cleanup `UnwindAction`
(`.continue_`, `.terminate`, or `.unreachable`), and a statically `.bool`
condition. -/
noncomputable def bodyAssertsAdmitted (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    match bb.terminator with
    | .assert cond _ msg _ unwind =>
      isSupportedAssertKind msg &&
        isSupportedAssertUnwind unwind &&
        optMirTyEq (operandStaticTy? body.locals cond) .bool
    | _ => true)

/-- Rewrite a single `TerminatorKind.assert` into `.switchInt cond` branching
to `target` on `expected` (`1` or `0`) and falling through to `unreachBb`. -/
noncomputable def lowerAssertTerminator (unreachBb : BasicBlockId) :
    TerminatorKind → TerminatorKind
  | .assert cond expected _ target _ =>
    .switchInt cond {
      branches := [(BitVec.ofNat 128 (if expected then 1 else 0), target)]
      otherwise := unreachBb
    }
  | t => t

/-- Lower all supported `TerminatorKind.assert` terminators in `body` into
`.switchInt` + a fresh `.unreachable` block (leaving assert-free bodies
unchanged), failing closed (`none`) if any block target is out of bounds or any
`.assert` has an unsupported `AssertKind`, a non-`.bool` condition, or a
`.cleanup` unwind action. -/
noncomputable def lowerAssertsInBody (body : Body) : Option Body :=
  if !bodyHasAssert body then
    some body
  else if !bodyAllBlocksInBounds body || !bodyAssertsAdmitted body then
    none
  else
    let unreachBb : BasicBlockId := body.basicBlocks.length
    let loweredBbs :=
      body.basicBlocks.map (fun bb =>
        { bb with terminator := lowerAssertTerminator unreachBb bb.terminator })
    let trapBb : BasicBlock := {
      statements := []
      terminator := .unreachable
      cleanup := false
    }
    some { body with basicBlocks := loweredBbs ++ [trapBb] }

/-- Map an option-returning function over a list, failing closed on `none`. -/
noncomputable def listMapOption {α β : Type} (f : α → Option β) :
    List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, listMapOption f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- Deterministically lower all supported `TerminatorKind.assert` terminators
across all bodies of `p` into `.switchInt` + `.unreachable`. -/
noncomputable def lowerAssertsToSwitchUnreachable (p : Program) :
    Option Program :=
  match listMapOption lowerAssertsInBody p.bodies with
  | some bodies' => some { p with bodies := bodies' }
  | none => none

/-- Decidable validator checking `pSrc --[AssertLower]--> pTgt`. -/
noncomputable def checkMirAssertLower (pSrc pTgt : Program) : Bool :=
  match lowerAssertsToSwitchUnreachable pSrc with
  | some pOut => programEq pOut pTgt
  | none => false

/-! ### Private Helpers from `F1_11_SliceA.lean` -/
/-! ### Stage 4 Helpers — Slice A: Reflection, Lists, Fuel, Type Soundness, & Theorem 1 -/

private theorem if_bool_true {α : Type} {c : Bool} {t e : α} (h : c = true) :
    (if c then t else e) = t := by
  rw [h]; rfl

private theorem if_bool_false {α : Type} {c : Bool} {t e : α} (h : c = false) :
    (if c then t else e) = e := by
  rw [h]; rfl

private theorem bool_and_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => exact ⟨rfl, rfl⟩

private theorem bool_and_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]; rfl

private theorem bool_or_true {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false =>
    cases b with
    | true => exact Or.inr rfl
    | false => cases h

private theorem bool_or_false {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | true => cases h
  | false =>
    cases b with
    | true => cases h
    | false => exact ⟨rfl, rfl⟩

private theorem bool_not_true {a : Bool} (h : (!a) = true) : a = false := by
  cases a with
  | false => rfl
  | true => cases h

private theorem bool_not_false {a : Bool} (h : (!a) = false) : a = true := by
  cases a with
  | true => rfl
  | false => cases h

private theorem bool_beq_eq {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem bool_beq_refl (a : Bool) : (a == a) = true := by
  cases a <;> rfl

private theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem nat_beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ _ => cases h
  | succ _ ih =>
    cases b with
    | zero => cases h
    | succ _ => rw [ih h]

private theorem nat_beq_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact nat_beq_refl a

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hEq : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (nat_beq_eq hEq))

private theorem nat_ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro hEq
  rw [hEq, nat_beq_refl] at h
  cases h

private theorem nat_ble_le {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le b
  | succ _ ih =>
    cases b with
    | zero => cases h
    | succ _ => exact Nat.succ_le_succ (ih h)

private theorem nat_le_ble {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by
  induction a generalizing b with
  | zero => rfl
  | succ k ih =>
    cases b with
    | zero => exact False.elim (Nat.not_succ_le_zero k h)
    | succ _ => exact ih (Nat.le_of_succ_le_succ h)

private theorem nat_ble_false_gt {a b : Nat} (h : Nat.ble a b = false) : b < a := by
  cases Nat.lt_or_ge b a with
  | inl hlt => exact hlt
  | inr hle =>
    rw [nat_le_ble hle] at h
    cases h

private theorem nat_gt_ble_false {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hB : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge (nat_ble_le hB) h)

private theorem nat_blt_lt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  nat_ble_le h

private theorem nat_lt_blt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  nat_le_ble h

private theorem nat_blt_false_ge {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  cases Nat.lt_or_ge a b with
  | inl hlt =>
    rw [nat_lt_blt hlt] at h
    cases h
  | inr hge => exact hge

private theorem nat_ge_blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hB : Nat.blt a b with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge h (nat_blt_lt hB))

private theorem nat_add_ne_zero_left {a b : Nat} (h : 0 < a) : a + b ≠ 0 := by
  intro hEq
  cases a with
  | zero => exact Nat.not_lt_zero 0 h
  | succ _ =>
    rw [Nat.succ_add] at hEq
    cases hEq

private theorem nat_lt_add_right {a b : Nat} (c : Nat) (h : a < b) : a < b + c :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right b c)

private theorem nat_add_lt_add_left_of_lt {a b : Nat} (c : Nat) (h : a < b) :
    c + a < c + b :=
  Nat.add_lt_add_left h c

private theorem nat_lt_of_add_lt_add_left {a b c : Nat} (h : c + a < c + b) :
    a < b := by
  induction c with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | succ _ ih =>
    rw [Nat.succ_add, Nat.succ_add] at h
    exact ih (Nat.lt_of_succ_lt_succ h)

private theorem nat_ne_add_left_of_lt {l base j : Nat} (h : l < base) :
    base + j ≠ l := by
  intro hEq
  exact Nat.not_lt_of_ge (Nat.le_add_right base j) (hEq ▸ h)

private theorem nat_beq_add_left_of_lt {l base j : Nat} (h : l < base) :
    Nat.beq (base + j) l = false :=
  nat_beq_false_of_ne (nat_ne_add_left_of_lt h)

private theorem nat_add_sub_cancel_left (a b : Nat) : (a + b) - a = b := by
  rw [Nat.add_comm]
  exact Nat.add_sub_cancel b a

private theorem nat_sub_add_cancel_of_le {a b : Nat} (h : a ≤ b) :
    a + (b - a) = b := by
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel h

private theorem bitvec_beq_eq {n : Nat} {a b : BitVec n}
    (h : (a == b) = true) : a = b :=
  eq_of_beq h

private theorem bitvec_beq_refl {n : Nat} (a : BitVec n) : (a == a) = true :=
  beq_self_eq_true a

private theorem uint8_beq_eq {a b : UInt8} (h : (a == b) = true) : a = b :=
  eq_of_beq h

private theorem uint8_list_beq_eq {xs ys : List UInt8}
    (h : List.beq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ _ ih =>
    cases ys with
    | nil => cases h
    | cons _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [uint8_beq_eq h1, ih h2]

private theorem uint8_list_beq_refl (xs : List UInt8) : List.beq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x _ ih =>
    change ((x == x) && List.beq _ _) = true
    rw [beq_self_eq_true x, ih]
    rfl

private theorem stringBeq_eq {a b : String} (h : stringBeq a b = true) : a = b := by
  unfold stringBeq at h
  have hL : a.toByteArray.data.toList = b.toByteArray.data.toList :=
    uint8_list_beq_eq h
  cases a with
  | ofByteArray ba _ =>
    cases b with
    | ofByteArray bb _ =>
      cases ba with
      | mk da =>
        cases bb with
        | mk db =>
          cases da with
          | mk la =>
            cases db with
            | mk lb =>
              dsimp at hL
              subst hL
              rfl

private theorem stringBeq_refl (a : String) : stringBeq a a = true := by
  unfold stringBeq
  exact uint8_list_beq_refl a.toByteArray.data.toList

private theorem intWidth_beq_eq {a b : IntWidth}
    (h : IntWidth.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem intWidth_beq_refl (a : IntWidth) : IntWidth.beq a a = true := by
  cases a <;> rfl

private theorem mutability_beq_eq {a b : Mutability}
    (h : Mutability.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem mutability_beq_refl (a : Mutability) : Mutability.beq a a = true := by
  cases a <;> rfl

private theorem natListBeq_eq {a b : List Nat}
    (h : natListBeq a b = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ _ ih =>
    cases b with
    | nil => cases h
    | cons _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, ih h2]

private theorem natListBeq_refl (a : List Nat) : natListBeq a a = true := by
  induction a with
  | nil => rfl
  | cons x _ ih =>
    dsimp [natListBeq]
    rw [nat_beq_refl x, ih]
    rfl

private theorem enumTagRepr_beq_eq {a b : EnumTagRepr}
    (h : EnumTagRepr.beq a b = true) : a = b := by
  cases a with
  | zeroSized =>
    cases b with
    | zeroSized => rfl
    | scalar _ _ => cases h
  | scalar _ _ =>
    cases b with
    | zeroSized => cases h
    | scalar _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [intWidth_beq_eq h1, bool_beq_eq h2]

private theorem enumTagRepr_beq_refl (a : EnumTagRepr) :
    EnumTagRepr.beq a a = true := by
  cases a with
  | zeroSized => rfl
  | scalar w s =>
    dsimp [EnumTagRepr.beq]
    rw [intWidth_beq_refl w]
    cases s <;> rfl

private theorem enumTy_beq_eq {a b : EnumTy}
    (h : EnumTy.beq a b = true) : a = b := by
  cases a with
  | mk _ _ _ _ _ =>
    cases b with
    | mk _ _ _ _ _ =>
      dsimp [EnumTy.beq] at h
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [nat_beq_eq h1, intWidth_beq_eq h2, bool_beq_eq h3,
          enumTagRepr_beq_eq h4, natListBeq_eq h5]

private theorem enumTy_beq_refl (a : EnumTy) : EnumTy.beq a a = true := by
  cases a with
  | mk id w s tr ds =>
    unfold EnumTy.beq
    rw [nat_beq_refl id, intWidth_beq_refl w, enumTagRepr_beq_refl tr,
        natListBeq_refl ds]
    cases s <;> rfl

mutual
  private theorem mirTy_beq_eq : ∀ {a b : MirTy}, MirTy.beq a b = true → a = b
    | .bool, .bool, _ => rfl
    | .int _ _, .int _ _, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [intWidth_beq_eq h1, bool_beq_eq h2]
    | .unit, .unit, _ => rfl
    | .never, .never, _ => rfl
    | .enum _, .enum _, h => by rw [enumTy_beq_eq h]
    | .tuple _, .tuple _, h => by rw [mirTy_beqList_eq h]
    | .ref _ _, .ref _ _, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, mirTy_beq_eq h2]
    | .rawPtr _ _, .rawPtr _ _, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, mirTy_beq_eq h2]
    | .unsupported, .unsupported, _ => rfl
    | .bool, .int _ _, h | .bool, .unit, h | .bool, .never, h
    | .bool, .enum _, h | .bool, .tuple _, h | .bool, .ref _ _, h
    | .bool, .rawPtr _ _, h | .bool, .unsupported, h
    | .int _ _, .bool, h | .int _ _, .unit, h | .int _ _, .never, h
    | .int _ _, .enum _, h | .int _ _, .tuple _, h | .int _ _, .ref _ _, h
    | .int _ _, .rawPtr _ _, h | .int _ _, .unsupported, h
    | .unit, .bool, h | .unit, .int _ _, h | .unit, .never, h
    | .unit, .enum _, h | .unit, .tuple _, h | .unit, .ref _ _, h
    | .unit, .rawPtr _ _, h | .unit, .unsupported, h
    | .never, .bool, h | .never, .int _ _, h | .never, .unit, h
    | .never, .enum _, h | .never, .tuple _, h | .never, .ref _ _, h
    | .never, .rawPtr _ _, h | .never, .unsupported, h
    | .enum _, .bool, h | .enum _, .int _ _, h | .enum _, .unit, h
    | .enum _, .never, h | .enum _, .tuple _, h | .enum _, .ref _ _, h
    | .enum _, .rawPtr _ _, h | .enum _, .unsupported, h
    | .tuple _, .bool, h | .tuple _, .int _ _, h | .tuple _, .unit, h
    | .tuple _, .never, h | .tuple _, .enum _, h | .tuple _, .ref _ _, h
    | .tuple _, .rawPtr _ _, h | .tuple _, .unsupported, h
    | .ref _ _, .bool, h | .ref _ _, .int _ _, h | .ref _ _, .unit, h
    | .ref _ _, .never, h | .ref _ _, .enum _, h | .ref _ _, .tuple _, h
    | .ref _ _, .rawPtr _ _, h | .ref _ _, .unsupported, h
    | .rawPtr _ _, .bool, h | .rawPtr _ _, .int _ _, h | .rawPtr _ _, .unit, h
    | .rawPtr _ _, .never, h | .rawPtr _ _, .enum _, h | .rawPtr _ _, .tuple _, h
    | .rawPtr _ _, .ref _ _, h | .rawPtr _ _, .unsupported, h
    | .unsupported, .bool, h | .unsupported, .int _ _, h | .unsupported, .unit, h
    | .unsupported, .never, h | .unsupported, .enum _, h | .unsupported, .tuple _, h
    | .unsupported, .ref _ _, h | .unsupported, .rawPtr _ _, h =>
      by cases h

  private theorem mirTy_beqList_eq :
      ∀ {a b : List MirTy}, MirTy.beqList a b = true → a = b
    | [], [], _ => rfl
    | _ :: _, _ :: _, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mirTy_beq_eq h1, mirTy_beqList_eq h2]
    | [], _ :: _, h | _ :: _, [], h => by cases h
end

mutual
  private theorem mirTy_beq_refl : ∀ (t : MirTy), MirTy.beq t t = true
    | .bool => rfl
    | .int w s => by
      change (IntWidth.beq w w && (s == s)) = true
      rw [intWidth_beq_refl w, bool_beq_refl s]
      rfl
    | .unit => rfl
    | .never => rfl
    | .enum ety => enumTy_beq_refl ety
    | .tuple fs => mirTy_beqList_refl fs
    | .ref m p => by
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [mutability_beq_refl m, mirTy_beq_refl p]
      rfl
    | .rawPtr m p => by
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [mutability_beq_refl m, mirTy_beq_refl p]
      rfl
    | .unsupported => rfl

  private theorem mirTy_beqList_refl : ∀ (fs : List MirTy), MirTy.beqList fs fs = true
    | [] => rfl
    | x :: xs => by
      change (MirTy.beq x x && MirTy.beqList xs xs) = true
      rw [mirTy_beq_refl x, mirTy_beqList_refl xs]
      rfl
end

private theorem listRel_length {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} (h : listRel r xs ys = true) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ _ ih =>
    cases ys with
    | nil => cases h
    | cons _ _ =>
      let ⟨_, h2⟩ := bool_and_true h
      dsimp [List.length]
      rw [ih h2]

private theorem listRel_eq {α : Type} {r : α → α → Bool}
    (hEq : ∀ x y, r x y = true → x = y) {xs ys : List α}
    (hRel : listRel r xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons x _ ih =>
    cases ys with
    | nil => cases hRel
    | cons y _ =>
      let ⟨h1, h2⟩ := bool_and_true hRel
      rw [hEq x y h1, ih h2]

private theorem listRel_getElem?_left {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} {i : Nat} {x : α}
    (hRel : listRel r xs ys = true)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) :
    ∃ y, Trusted.MirSemantics.getElem? ys i = some y ∧ r x y = true := by
  induction xs generalizing ys i with
  | nil => cases hGet
  | cons a _ ih =>
    cases ys with
    | nil => cases hRel
    | cons b _ =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      cases i with
      | zero =>
        injection hGet with hxa
        subst hxa
        exact ⟨b, rfl, hab⟩
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih hTail hGet

private theorem listRel_getElem?_right {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} {i : Nat} {y : β}
    (hRel : listRel r xs ys = true)
    (hGet : Trusted.MirSemantics.getElem? ys i = some y) :
    ∃ x, Trusted.MirSemantics.getElem? xs i = some x ∧ r x y = true := by
  induction xs generalizing ys i with
  | nil =>
    cases ys with
    | nil => cases hGet
    | cons _ _ => cases hRel
  | cons a _ ih =>
    cases ys with
    | nil => cases hRel
    | cons b _ =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      cases i with
      | zero =>
        injection hGet with hyb
        subst hyb
        exact ⟨a, rfl, hab⟩
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih hTail hGet

private theorem list_map_eq_of_rel {α β γ : Type} {r : α → β → Bool}
    {f : α → γ} {g : β → γ} {xs : List α} {ys : List β}
    (hRel : listRel r xs ys = true)
    (hFG : ∀ a b, r a b = true → f a = g b) :
    xs.map f = ys.map g := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons a _ ih =>
    cases ys with
    | nil => cases hRel
    | cons b _ =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      dsimp [List.map]
      rw [hFG a b hab, ih hTail]

private theorem projElemEq_eq {a b : ProjectionElem}
    (h : projElemEq a b = true) : a = b := by
  cases a with
  | deref => cases b <;> first | rfl | cases h
  | field _ _ =>
    cases b with
    | field _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, mirTy_beq_eq h2]
    | _ => cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem placeEq_eq {a b : Place} (h : placeEq a b = true) : a = b := by
  cases a with
  | mk _ _ =>
    cases b with
    | mk _ _ =>
      dsimp [placeEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, listRel_eq (fun _ _ => projElemEq_eq) h2]

private theorem constLitEq_eq {a b : ConstLit}
    (h : constLitEq a b = true) : a = b := by
  cases a with
  | scalar _ =>
    cases b with
    | scalar _ => rw [bitvec_beq_eq h]
    | zeroSized => cases h
  | zeroSized =>
    cases b with
    | scalar _ => cases h
    | zeroSized => rfl

private theorem constOpEq_eq {a b : ConstOperand}
    (h : constOpEq a b = true) : a = b := by
  cases a with
  | mk _ _ =>
    cases b with
    | mk _ _ =>
      dsimp [constOpEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mirTy_beq_eq h1, constLitEq_eq h2]

private theorem binOpEq_eq {a b : BinOp} (h : binOpEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem unOpEq_eq {a b : UnOp} (h : unOpEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem operandEq_eq {a b : Operand}
    (h : operandEq a b = true) : a = b := by
  cases a with
  | copy _ =>
    cases b with
    | copy _ => rw [placeEq_eq h]
    | _ => cases h
  | move _ =>
    cases b with
    | move _ => rw [placeEq_eq h]
    | _ => cases h
  | constant _ =>
    cases b with
    | constant _ => rw [constOpEq_eq h]
    | _ => cases h

private theorem rvalueEq_eq {a b : Rvalue}
    (h : rvalueEq a b = true) : a = b := by
  cases a with
  | use _ =>
    cases b with
    | use _ => rw [operandEq_eq h]
    | _ => cases h
  | binaryOp _ _ _ =>
    cases b with
    | binaryOp _ _ _ =>
      let ⟨h12, h3⟩ := bool_and_true h
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [binOpEq_eq h1, operandEq_eq h2, operandEq_eq h3]
    | _ => cases h
  | unaryOp _ _ =>
    cases b with
    | unaryOp _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [unOpEq_eq h1, operandEq_eq h2]
    | _ => cases h
  | discriminant _ =>
    cases b with
    | discriminant _ => rw [placeEq_eq h]
    | _ => cases h
  | ref _ _ =>
    cases b with
    | ref _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, placeEq_eq h2]
    | _ => cases h
  | addressOf _ _ =>
    cases b with
    | addressOf _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, placeEq_eq h2]
    | _ => cases h
  | aggregateTuple _ =>
    cases b with
    | aggregateTuple _ =>
      rw [listRel_eq (fun _ _ => operandEq_eq) h]
    | _ => cases h
  | unsupported =>
    cases b <;> first | rfl | cases h

private theorem stmtEq_eq {a b : StatementKind}
    (h : stmtEq a b = true) : a = b := by
  cases a with
  | assign _ _ =>
    cases b with
    | assign _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [placeEq_eq h1, rvalueEq_eq h2]
    | _ => cases h
  | storageLive _ =>
    cases b with
    | storageLive _ => rw [nat_beq_eq h]
    | _ => cases h
  | storageDead _ =>
    cases b with
    | storageDead _ => rw [nat_beq_eq h]
    | _ => cases h
  | nop => cases b <;> first | rfl | cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem switchTargetsEq_eq {a b : SwitchTargets}
    (h : switchTargetsEq a b = true) : a = b := by
  cases a with
  | mk bs1 ow1 =>
    cases b with
    | mk bs2 ow2 =>
      dsimp [switchTargetsEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      have hOw : ow1 = ow2 := nat_beq_eq h1
      have hBs : bs1 = bs2 := listRel_eq (fun x y hxy => by
        cases x with
        | mk _ _ =>
          cases y with
          | mk _ _ =>
            dsimp at hxy
            let ⟨hv, ht⟩ := bool_and_true hxy
            rw [bitvec_beq_eq hv, nat_beq_eq ht]) h2
      rw [hOw, hBs]

private theorem unwindActionEq_eq {a b : UnwindAction}
    (h : unwindActionEq a b = true) : a = b := by
  cases a with
  | cleanup _ =>
    cases b with
    | cleanup _ => rw [nat_beq_eq h]
    | _ => cases h
  | continue_ => cases b <;> first | rfl | cases h
  | unreachable => cases b <;> first | rfl | cases h
  | terminate => cases b <;> first | rfl | cases h

private theorem assertKindEq_eq {a b : AssertKind}
    (h : assertKindEq a b = true) : a = b := by
  cases a with
  | overflow _ =>
    cases b with
    | overflow _ => rw [binOpEq_eq h]
    | _ => cases h
  | overflowNeg => cases b <;> first | rfl | cases h
  | divByZero => cases b <;> first | rfl | cases h
  | remByZero => cases b <;> first | rfl | cases h
  | boundsCheck => cases b <;> first | rfl | cases h
  | misalignedPtrDeref => cases b <;> first | rfl | cases h
  | nullPtrDeref => cases b <;> first | rfl | cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem optBlockEq_eq {a b : Option BasicBlockId}
    (h : optBlockEq a b = true) : a = b := by
  cases a with
  | none => cases b <;> first | rfl | cases h
  | some _ =>
    cases b with
    | some _ => rw [nat_beq_eq h]
    | none => cases h

private theorem terminatorEq_eq {a b : TerminatorKind}
    (h : terminatorEq a b = true) : a = b := by
  cases a with
  | goto _ =>
    cases b with
    | goto _ => rw [nat_beq_eq h]
    | _ => cases h
  | switchInt _ _ =>
    cases b with
    | switchInt _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [operandEq_eq h1, switchTargetsEq_eq h2]
    | _ => cases h
  | return_ => cases b <;> first | rfl | cases h
  | unreachable => cases b <;> first | rfl | cases h
  | unwindResume => cases b <;> first | rfl | cases h
  | assert _ _ _ _ _ =>
    cases b with
    | assert _ _ _ _ _ =>
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [operandEq_eq h1, bool_beq_eq h2, assertKindEq_eq h3,
          nat_beq_eq h4, unwindActionEq_eq h5]
    | _ => cases h
  | call _ _ _ _ _ =>
    cases b with
    | call _ _ _ _ _ =>
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [nat_beq_eq h1, listRel_eq (fun _ _ => operandEq_eq) h2,
          placeEq_eq h3, optBlockEq_eq h4, unwindActionEq_eq h5]
    | _ => cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem blockEq_eq {a b : BasicBlock} (h : blockEq a b = true) : a = b := by
  cases a with
  | mk _ _ _ =>
    cases b with
    | mk _ _ _ =>
      dsimp [blockEq] at h
      let ⟨h12, h3⟩ := bool_and_true h
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [bool_beq_eq h1, listRel_eq (fun _ _ => stmtEq_eq) h2,
          terminatorEq_eq h3]

private theorem scopeEq_eq {a b : VerificationScope}
    (h : scopeEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem scopeEq_refl (a : VerificationScope) : scopeEq a a = true := by
  cases a <;> rfl

private theorem bodyHeaderEq_elim {b₁ b₂ : Body}
    (h : bodyHeaderEq b₁ b₂ = true) :
    b₁.argumentCount = b₂.argumentCount ∧
    b₁.locals = b₂.locals ∧
    b₁.isUnsafe = b₂.isUnsafe ∧
    b₁.identity = b₂.identity := by
  unfold bodyHeaderEq at h
  let ⟨h123, hId⟩ := bool_and_true h
  let ⟨h12, hUns⟩ := bool_and_true h123
  let ⟨hArg, hLoc⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hArg, mirTy_beqList_eq hLoc, bool_beq_eq hUns,
         stringBeq_eq hId⟩

private theorem bodyEq_eq {b₁ b₂ : Body} (h : bodyEq b₁ b₂ = true) : b₁ = b₂ := by
  cases b₁ with
  | mk _ _ _ _ _ =>
    cases b₂ with
    | mk _ _ _ _ _ =>
      unfold bodyEq at h
      let ⟨hHdr, hBbs⟩ := bool_and_true h
      let ⟨hArg, hLoc, hUns, hId⟩ := bodyHeaderEq_elim hHdr
      have hB := listRel_eq (fun _ _ => blockEq_eq) hBbs
      dsimp at hArg hLoc hUns hId hB
      rw [hArg, hLoc, hUns, hId, hB]

private theorem programHeaderEq_elim {p₁ p₂ : Program}
    (h : programHeaderEq p₁ p₂ = true) :
    p₁.pointerWidthBits = p₂.pointerWidthBits ∧
    p₁.mirProfileVersion = p₂.mirProfileVersion ∧
    p₁.entryDefId = p₂.entryDefId ∧
    p₁.scope = p₂.scope := by
  unfold programHeaderEq at h
  let ⟨h123, hSc⟩ := bool_and_true h
  let ⟨h12, hEnt⟩ := bool_and_true h123
  let ⟨hPw, hVer⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hPw, nat_beq_eq hVer, nat_beq_eq hEnt, scopeEq_eq hSc⟩

private theorem programHeaderEq_refl (p : Program) : programHeaderEq p p = true := by
  unfold programHeaderEq
  rw [nat_beq_refl p.pointerWidthBits, nat_beq_refl p.mirProfileVersion,
      nat_beq_refl p.entryDefId, scopeEq_refl p.scope]
  rfl

private theorem programEq_eq {p₁ p₂ : Program} (h : programEq p₁ p₂ = true) :
    p₁ = p₂ := by
  cases p₁ with
  | mk _ _ _ _ _ =>
    cases p₂ with
    | mk _ _ _ _ _ =>
      unfold programEq at h
      let ⟨hHdr, hBods⟩ := bool_and_true h
      let ⟨hPw, hVer, hEnt, hSc⟩ := programHeaderEq_elim hHdr
      have hB := listRel_eq (fun _ _ => bodyEq_eq) hBods
      dsimp at hPw hVer hEnt hSc hB
      rw [hPw, hVer, hEnt, hSc, hB]

/-! ### List, `getElem?`, `setElem?`, `append`, `map`, `all`, `any`, `listFlatMap` Helpers -/

private theorem getElem?_some_lt {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : Trusted.MirSemantics.getElem? xs i = some x) : i < xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons _ xs ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ xs.length
    | succ _ => exact Nat.succ_lt_succ (ih h)

private theorem getElem?_none_of_ge {α : Type} {xs : List α} {i : Nat}
    (h : xs.length ≤ i) : Trusted.MirSemantics.getElem? xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ xs ih =>
    cases i with
    | zero => exact False.elim (Nat.not_succ_le_zero xs.length h)
    | succ _ => exact ih (Nat.le_of_succ_le_succ h)

private theorem getElem?_some_of_lt {α : Type} (xs : List α) (i : Nat)
    (h : i < xs.length) :
    ∃ x, Trusted.MirSemantics.getElem? xs i = some x := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons a _ ih =>
    cases i with
    | zero => exact ⟨a, rfl⟩
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ h)

private theorem getElem?_none_ge {α : Type} {xs : List α} {i : Nat}
    (h : Trusted.MirSemantics.getElem? xs i = none) : xs.length ≤ i := by
  cases Nat.lt_or_ge i xs.length with
  | inl hlt =>
    let ⟨_, hx⟩ := getElem?_some_of_lt xs i hlt
    rw [h] at hx
    cases hx
  | inr hge => exact hge

private theorem list_eq_of_getElem?_eq {α : Type} {xs ys : List α}
    (hLen : xs.length = ys.length)
    (hAt : ∀ i, Trusted.MirSemantics.getElem? xs i =
      Trusted.MirSemantics.getElem? ys i) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons _ _ ih =>
    cases ys with
    | nil => cases hLen
    | cons _ _ =>
      have h0 := hAt 0
      dsimp [Trusted.MirSemantics.getElem?] at h0
      injection h0 with hxy
      subst hxy
      rw [ih (Nat.succ.inj hLen) (fun i => hAt (i + 1))]

private theorem setElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : setElem? xs i v = some xs') : xs'.length = xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons _ _ ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? _ k v with
      | none => rw [hSub] at h; cases h
      | some _ =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        dsimp [List.length]
        rw [ih hSub]

private theorem setElem?_some_lt {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : setElem? xs i v = some xs') : i < xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons _ _ ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? _ k v with
      | none => rw [hSub] at h; cases h
      | some _ => exact Nat.succ_lt_succ (ih hSub)

private theorem setElem?_getElem?_same {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : setElem? xs i v = some xs') :
    Trusted.MirSemantics.getElem? xs' i = some v := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons _ _ ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? _ k v with
      | none => rw [hSub] at h; cases h
      | some _ =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih hSub

private theorem setElem?_getElem?_ne {α : Type} {xs xs' : List α} {i j : Nat} {v : α}
    (h : setElem? xs i v = some xs') (hNe : j ≠ i) :
    Trusted.MirSemantics.getElem? xs' j =
      Trusted.MirSemantics.getElem? xs j := by
  induction xs generalizing xs' i j with
  | nil => cases h
  | cons _ _ ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ _ => rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? _ k v with
      | none => rw [hSub] at h; cases h
      | some _ =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        cases j with
        | zero => rfl
        | succ _ => exact ih hSub (fun hEq => hNe (by rw [hEq]))

private theorem setElem?_some_of_lt {α : Type} (xs : List α) (i : Nat) (v : α)
    (h : i < xs.length) : ∃ xs', setElem? xs i v = some xs' := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons a _ ih =>
    cases i with
    | zero => exact ⟨v :: _, rfl⟩
    | succ k =>
      let ⟨sub, hSub⟩ := ih k (Nat.lt_of_succ_lt_succ h)
      exact ⟨a :: sub, by dsimp [setElem?]; rw [hSub]⟩

private theorem setElem?_none_of_ge {α : Type} (xs : List α) (i : Nat) (v : α)
    (h : xs.length ≤ i) : setElem? xs i v = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i with
    | zero => exact False.elim (Nat.not_succ_le_zero _ h)
    | succ k =>
      dsimp [setElem?]
      rw [ih k (Nat.le_of_succ_le_succ h)]

private theorem list_append_length {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => dsimp [List.length]; rw [Nat.zero_add]
  | cons _ _ ih =>
    dsimp [List.length]
    rw [ih, Nat.succ_add]

private theorem getElem?_append_left {α : Type} (xs ys : List α) (i : Nat)
    (h : i < xs.length) :
    Trusted.MirSemantics.getElem? (xs ++ ys) i =
      Trusted.MirSemantics.getElem? xs i := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons _ _ ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ h)

private theorem getElem?_append_right_add {α : Type} (xs ys : List α) (j : Nat) :
    Trusted.MirSemantics.getElem? (xs ++ ys) (xs.length + j) =
      Trusted.MirSemantics.getElem? ys j := by
  induction xs with
  | nil =>
    dsimp [List.length]
    rw [Nat.zero_add]
  | cons _ _ ih =>
    dsimp [List.length]
    rw [Nat.succ_add]
    exact ih

private theorem getElem?_append_right {α : Type} (xs ys : List α) (i : Nat)
    (h : xs.length ≤ i) :
    Trusted.MirSemantics.getElem? (xs ++ ys) i =
      Trusted.MirSemantics.getElem? ys (i - xs.length) := by
  have hEq := nat_sub_add_cancel_of_le h
  rw [← hEq]
  have hSub := nat_add_sub_cancel_left xs.length (i - xs.length)
  rw [hSub]
  exact getElem?_append_right_add xs ys (i - xs.length)

private theorem setElem?_append_left {α : Type} (xs ys : List α) (i : Nat) (v : α)
    (h : i < xs.length) :
    setElem? (xs ++ ys) i v = (setElem? xs i v).map (fun xs' => xs' ++ ys) := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons _ rest ih =>
    cases i with
    | zero => rfl
    | succ k =>
      dsimp [setElem?]
      rw [ih k (Nat.lt_of_succ_lt_succ h)]
      cases setElem? rest k v <;> rfl

private theorem setElem?_append_right_add {α : Type} (xs ys : List α) (j : Nat)
    (v : α) :
    setElem? (xs ++ ys) (xs.length + j) v =
      (setElem? ys j v).map (fun ys' => xs ++ ys') := by
  induction xs with
  | nil =>
    dsimp [List.length]
    rw [Nat.zero_add]
    cases setElem? ys j v <;> rfl
  | cons _ _ ih =>
    dsimp [List.length]
    rw [Nat.succ_add]
    dsimp [setElem?]
    rw [ih]
    cases setElem? ys j v <;> rfl

private theorem map_length_eq {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    dsimp [List.map, List.length]
    rw [ih]

private theorem getElem?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    Trusted.MirSemantics.getElem? (xs.map f) i =
      (Trusted.MirSemantics.getElem? xs i).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

private theorem map_setElem? {α β : Type} (f : α → β) {xs xs' : List α} {i : Nat}
    {v : α} (h : setElem? xs i v = some xs') :
    setElem? (xs.map f) i (f v) = some (xs'.map f) := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons _ rest ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? rest k v with
      | none => rw [hSub] at h; cases h
      | some sub =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        dsimp [List.map, setElem?]
        rw [ih hSub]

private theorem setElem?_map_eq {α β : Type} (f : α → β) (xs : List α) (i : Nat) (v : α) :
    setElem? (xs.map f) i (f v) = (setElem? xs i v).map (List.map f) := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ rest ih =>
    cases i with
    | zero => rfl
    | succ k =>
      dsimp [List.map, setElem?]
      rw [ih k]
      cases setElem? rest k v <;> rfl

private theorem list_all_getElem? {α : Type} {p : α → Bool} {xs : List α}
    {i : Nat} {x : α} (hAll : xs.all p = true)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) : p x = true := by
  induction xs generalizing i with
  | nil => cases hGet
  | cons _ _ ih =>
    let ⟨ha, hRest⟩ := bool_and_true hAll
    cases i with
    | zero =>
      injection hGet with hEq; subst hEq; exact ha
    | succ _ => exact ih hRest hGet

private theorem list_all_of_forall_getElem? {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = true) :
    xs.all p = true := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    have ha : p a = true := h 0 a rfl
    have hRest : _ = true := ih (fun i x hG => h (i + 1) x hG)
    exact bool_and_intro ha hRest

private theorem list_all_append {α : Type} (p : α → Bool) (xs ys : List α) :
    (xs ++ ys).all p = (xs.all p && ys.all p) := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    dsimp [List.all]
    cases p a with
    | false => rfl
    | true => exact ih

private theorem list_all_map {α β : Type} (p : β → Bool) (f : α → β) (xs : List α) :
    (xs.map f).all p = xs.all (fun a => p (f a)) := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    dsimp [List.map, List.all]
    cases p (f a) with
    | false => rfl
    | true => exact ih

private theorem list_any_append {α : Type} (p : α → Bool) (xs ys : List α) :
    (xs ++ ys).any p = (xs.any p || ys.any p) := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    dsimp [List.any]
    cases p a with
    | true => rfl
    | false => exact ih

private theorem list_any_map {α β : Type} (p : β → Bool) (f : α → β) (xs : List α) :
    (xs.map f).any p = xs.any (fun a => p (f a)) := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    dsimp [List.map, List.any]
    cases p (f a) with
    | true => rfl
    | false => exact ih

private theorem list_any_false_of_forall_getElem? {α : Type} {p : α → Bool}
    {xs : List α}
    (h : ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = false) :
    xs.any p = false := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    have ha : p a = false := h 0 a rfl
    have hRest : _ = false := ih (fun i x hG => h (i + 1) x hG)
    dsimp [List.any]
    rw [ha, hRest]
    rfl

private theorem list_any_true_of_getElem? {α : Type} {p : α → Bool} {xs : List α}
    {i : Nat} {x : α} (hGet : Trusted.MirSemantics.getElem? xs i = some x)
    (hP : p x = true) : xs.any p = true := by
  induction xs generalizing i with
  | nil => cases hGet
  | cons a _ ih =>
    cases i with
    | zero =>
      injection hGet with hEq; subst hEq
      dsimp [List.any]
      rw [hP]
      rfl
    | succ _ =>
      dsimp [List.any]
      rw [ih hGet]
      cases p a <;> rfl

private theorem list_any_exists_getElem? {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.any p = true) :
    ∃ i x, Trusted.MirSemantics.getElem? xs i = some x ∧ p x = true := by
  induction xs with
  | nil => cases h
  | cons a _ ih =>
    dsimp [List.any] at h
    cases hPa : p a with
    | true => exact ⟨0, a, rfl, hPa⟩
    | false =>
      rw [hPa] at h
      let ⟨i, x, hGet, hPx⟩ := ih h
      exact ⟨i + 1, x, hGet, hPx⟩

private theorem list_any_false_getElem? {α : Type} {p : α → Bool} {xs : List α}
    {i : Nat} {x : α} (hAny : xs.any p = false)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) : p x = false := by
  cases hPx : p x with
  | false => rfl
  | true =>
    have hT := list_any_true_of_getElem? hGet hPx
    rw [hAny] at hT
    cases hT

private theorem list_any_eq_of_getElem? {α : Type} {p : α → Bool} {xs ys : List α}
    (hLen : xs.length = ys.length)
    (hAt : ∀ i x y,
      Trusted.MirSemantics.getElem? xs i = some x →
      Trusted.MirSemantics.getElem? ys i = some y →
      p x = p y) :
    xs.any p = ys.any p := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons a _ ih =>
    cases ys with
    | nil => cases hLen
    | cons b _ =>
      have hHead : p a = p b := hAt 0 a b rfl rfl
      have hTail := ih (Nat.succ.inj hLen) (fun i x y hx hy => hAt (i + 1) x y hx hy)
      dsimp [List.any]
      rw [hHead, hTail]

private theorem list_isEmpty_eq_of_length {α β : Type} {xs : List α} {ys : List β}
    (h : xs.length = ys.length) : xs.isEmpty = ys.isEmpty := by
  cases xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ _ =>
    cases ys with
    | nil => cases h
    | cons _ _ => rfl

private theorem list_isEmpty_false_of_pos {α : Type} {xs : List α}
    (h : 0 < xs.length) : xs.isEmpty = false := by
  cases xs with
  | nil => exact False.elim (Nat.not_lt_zero 0 h)
  | cons _ _ => rfl

private theorem list_pos_of_isEmpty_false {α : Type} {xs : List α}
    (h : xs.isEmpty = false) : 0 < xs.length := by
  cases xs with
  | nil => cases h
  | cons _ rest => exact Nat.zero_lt_succ rest.length

private theorem take_append_of_le_length {α : Type} (xs ys : List α) (n : Nat)
    (h : n ≤ xs.length) : (xs ++ ys).take n = xs.take n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ k => exact False.elim (Nat.not_succ_le_zero k h)
  | cons _ _ ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp [List.take]
      rw [ih k (Nat.le_of_succ_le_succ h)]

private theorem drop_append_of_le_length {α : Type} (xs ys : List α) (n : Nat)
    (h : n ≤ xs.length) : (xs ++ ys).drop n = xs.drop n ++ ys := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ k => exact False.elim (Nat.not_succ_le_zero k h)
  | cons _ _ ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k (Nat.le_of_succ_le_succ h)

private theorem drop_length_eq {α : Type} (xs : List α) (n : Nat) :
    (xs.drop n).length = xs.length - n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ _ =>
      dsimp [List.drop, List.length]
      rw [Nat.zero_sub]
  | cons _ _ ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp [List.drop, List.length]
      rw [Nat.succ_sub_succ]
      exact ih k

private theorem take_drop1_append_left {α : Type} (xs ys : List α) (n : Nat)
    (h : n < xs.length) :
    ((xs ++ ys).drop 1).take n = (xs.drop 1).take n := by
  have h1 : 1 ≤ xs.length := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le n) h)
  rw [drop_append_of_le_length xs ys 1 h1]
  have hLe : n ≤ (xs.drop 1).length := by
    rw [drop_length_eq]
    cases xs with
    | nil => exact False.elim (Nat.not_lt_zero n h)
    | cons _ _ =>
      dsimp [List.length] at h
      dsimp [List.length]
      exact Nat.le_of_lt_succ h
  exact take_append_of_le_length (xs.drop 1) ys n hLe

private theorem getElem?_take_drop1 {α : Type} (xs : List α) (n i : Nat)
    (hi : i < n) :
    Trusted.MirSemantics.getElem? ((xs.drop 1).take n) i =
      Trusted.MirSemantics.getElem? xs (i + 1) := by
  cases xs with
  | nil =>
    dsimp [List.drop, List.take]
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero i hi)
    | succ _ => rfl
  | cons _ ys =>
    dsimp [List.drop, Trusted.MirSemantics.getElem?]
    induction ys generalizing n i with
    | nil =>
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero i hi)
      | succ _ => rfl
    | cons _ _ ih =>
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero i hi)
      | succ m =>
        cases i with
        | zero => rfl
        | succ k => exact ih m k (Nat.lt_of_succ_lt_succ hi)

private theorem list_take_length_eq {α : Type} (xs : List α) (n : Nat)
    (h : n ≤ xs.length) : (xs.take n).length = n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ k => exact False.elim (Nat.not_succ_le_zero k h)
  | cons _ _ ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp [List.take, List.length]
      rw [ih k (Nat.le_of_succ_le_succ h)]

private theorem list_take_all_eq {α : Type} (xs : List α) :
    xs.take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    dsimp [List.length, List.take]
    rw [ih]

private theorem list_take_succ_of_getElem? {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : Trusted.MirSemantics.getElem? xs i = some x) :
    xs.take (i + 1) = xs.take i ++ [x] := by
  induction xs generalizing i with
  | nil => cases h
  | cons a _ ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [List.take]
      rw [ih h]

private theorem listFlatMap_append {α β : Type} (f : α → List β) (xs ys : List α) :
    listFlatMap f (xs ++ ys) = listFlatMap f xs ++ listFlatMap f ys := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    dsimp [listFlatMap]
    rw [ih, List.append_assoc]

private theorem list_any_listFlatMap {α β : Type} (p : β → Bool) (f : α → List β)
    (xs : List α) :
    (listFlatMap f xs).any p = xs.any (fun a => (f a).any p) := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    dsimp [listFlatMap, List.any]
    rw [list_any_append, ih]

private theorem list_all_listFlatMap {α β : Type} (p : β → Bool) (f : α → List β)
    (xs : List α) :
    (listFlatMap f xs).all p = xs.all (fun a => (f a).all p) := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    dsimp [listFlatMap, List.all]
    rw [list_all_append, ih]

private theorem listMapOption_length {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} (h : listMapOption f xs = some ys) :
    ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    injection h with hEq; subst hEq; rfl
  | cons a rest ih =>
    dsimp [listMapOption] at h
    cases hFa : f a with
    | none => rw [hFa] at h; cases h
    | some b =>
      rw [hFa] at h
      cases hRest : listMapOption f rest with
      | none => rw [hRest] at h; cases h
      | some bs =>
        rw [hRest] at h
        injection h with hEq; subst hEq
        dsimp [List.length]
        rw [ih hRest]

private theorem listMapOption_getElem?_left {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} {i : Nat} {x : α}
    (hMap : listMapOption f xs = some ys)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) :
    ∃ y, Trusted.MirSemantics.getElem? ys i = some y ∧ f x = some y := by
  induction xs generalizing ys i with
  | nil => cases hGet
  | cons a rest ih =>
    dsimp [listMapOption] at hMap
    cases hFa : f a with
    | none => rw [hFa] at hMap; cases hMap
    | some b =>
      rw [hFa] at hMap
      cases hRest : listMapOption f rest with
      | none => rw [hRest] at hMap; cases hMap
      | some bs =>
        rw [hRest] at hMap
        injection hMap with hEq; subst hEq
        cases i with
        | zero =>
          injection hGet with hxa; subst hxa
          exact ⟨b, rfl, hFa⟩
        | succ k =>
          dsimp [Trusted.MirSemantics.getElem?]
          exact @ih bs k hRest hGet

private theorem listMapOption_getElem?_right {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} {i : Nat} {y : β}
    (hMap : listMapOption f xs = some ys)
    (hGet : Trusted.MirSemantics.getElem? ys i = some y) :
    ∃ x, Trusted.MirSemantics.getElem? xs i = some x ∧ f x = some y := by
  induction xs generalizing ys i with
  | nil =>
    injection hMap with hEq; subst hEq; cases hGet
  | cons a rest ih =>
    dsimp [listMapOption] at hMap
    cases hFa : f a with
    | none => rw [hFa] at hMap; cases hMap
    | some b =>
      rw [hFa] at hMap
      cases hRest : listMapOption f rest with
      | none => rw [hRest] at hMap; cases hMap
      | some bs =>
        rw [hRest] at hMap
        injection hMap with hEq; subst hEq
        cases i with
        | zero =>
          injection hGet with hyb; subst hyb
          exact ⟨a, rfl, hFa⟩
        | succ k =>
          dsimp [Trusted.MirSemantics.getElem?]
          exact @ih bs k hRest hGet

private theorem bodiesHaveUniqueIdentities_eq_of_map_id {bs₁ bs₂ : List Body}
    (hIds : bs₁.map (fun b => b.identity) = bs₂.map (fun b => b.identity)) :
    bodiesHaveUniqueIdentities bs₁ = bodiesHaveUniqueIdentities bs₂ := by
  unfold bodiesHaveUniqueIdentities
  have hAll : bs₁.all (fun b => !stringBeq b.identity "") =
      bs₂.all (fun b => !stringBeq b.identity "") := by
    have h1 := list_all_map (fun s => !stringBeq s "") (fun b : Body => b.identity) bs₁
    have h2 := list_all_map (fun s => !stringBeq s "") (fun b : Body => b.identity) bs₂
    rw [← h1, ← h2, hIds]
  rw [hAll, hIds]

private theorem initLocalsExtLoop_length (body : Body) (args : List Val)
    (base : Nat) (tys : List MirTy) :
    (initLocalsExtLoop body args base tys).length = tys.length := by
  induction tys generalizing base with
  | nil => rfl
  | cons _ _ ih =>
    dsimp [initLocalsExtLoop, List.length]
    rw [ih (base + 1)]

private theorem initLocalsExtLoop_getElem? (body : Body) (args : List Val)
    (base : Nat) (tys : List MirTy) (i : Nat) (ty : MirTy)
    (hTy : Trusted.MirSemantics.getElem? tys i = some ty) :
    Trusted.MirSemantics.getElem? (initLocalsExtLoop body args base tys) i =
      some (if Nat.beq (base + i) 0 then
              liveUninitSlotExt ty
            else if Nat.ble (base + i) body.argumentCount then
              match Trusted.MirSemantics.getElem? args ((base + i) - 1) with
              | some v => initArgSlotExt ty v
              | none => .dead
            else if hasStorageAnnotation body (base + i) then
              .dead
            else
              liveUninitSlotExt ty) := by
  induction tys generalizing base i with
  | nil => cases hTy
  | cons _ _ ih =>
    cases i with
    | zero =>
      injection hTy with hEq; subst hEq; rfl
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTy
      rw [hAdd] at hRec
      exact hRec

/-! ### Deterministic Step, Fuel, Reachability, & Divergence Helpers -/

private noncomputable def evalMirFuel (p : Program) :
    Nat → State → StepResult State TerminalOut
  | 0, s => .step s
  | fuel + 1, s =>
    match evalStep p 0 s with
    | .step s' => evalMirFuel p fuel s'
    | .done out => .done out
    | .fault k => .fault k

private noncomputable def iterMirStep (p : Program) (s₀ : State) : Nat → State
  | 0 => s₀
  | n + 1 =>
    match evalStep p 0 (iterMirStep p s₀ n) with
    | .step s' => s'
    | _ => s₀

private theorem step_iff_evalStep {p : Program} {s : State}
    {res : StepResult State TerminalOut} :
    Step p s res ↔ evalStep p 0 s = res := by
  constructor
  · intro ⟨c, hc, hEval⟩
    have hc0 : c = 0 := hc
    subst hc0
    exact hEval
  · intro h
    exact ⟨0, rfl, h⟩

private theorem stepTupleAssert_iff_evalStepTupleAssert {p : Program} {s : StateExt}
    {res : StepResult StateExt TerminalOutExt} :
    StepTupleAssert p s res ↔ evalStepTupleAssert p 0 s = res := by
  constructor
  · intro ⟨c, hc, hEval⟩
    have hc0 : c = 0 := hc
    subst hc0
    exact hEval
  · intro h
    exact ⟨0, rfl, h⟩

private theorem reaches_head_priv {p : Program} {s₁ s₂ s₃ : State}
    (hFirst : Step p s₁ (.step s₂)) (hRest : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction hRest with
  | refl => exact Reaches.tail (Reaches.refl s₁) hFirst
  | tail _ hLast ih => exact Reaches.tail ih hLast

private theorem reachesTupleAssert_head_priv {p : Program} {s₁ s₂ s₃ : StateExt}
    (hFirst : StepTupleAssert p s₁ (.step s₂))
    (hRest : ReachesTupleAssert p s₂ s₃) :
    ReachesTupleAssert p s₁ s₃ := by
  induction hRest with
  | refl => exact ReachesTupleAssert.tail (ReachesTupleAssert.refl s₁) hFirst
  | tail _ hLast ih => exact ReachesTupleAssert.tail ih hLast

private theorem reaches_trans_priv {p : Program} {s₁ s₂ s₃ : State}
    (h12 : Reaches p s₁ s₂) (h23 : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction h23 with
  | refl => exact h12
  | tail _ hStep ih => exact Reaches.tail ih hStep

private theorem reachesTupleAssert_trans_priv {p : Program} {s₁ s₂ s₃ : StateExt}
    (h12 : ReachesTupleAssert p s₁ s₂) (h23 : ReachesTupleAssert p s₂ s₃) :
    ReachesTupleAssert p s₁ s₃ := by
  induction h23 with
  | refl => exact h12
  | tail _ hStep ih => exact ReachesTupleAssert.tail ih hStep

private theorem evalMirFuel_add (p : Program) (m n : Nat) (s : State) :
    evalMirFuel p (m + n) s =
      match evalMirFuel p m s with
      | .step s' => evalMirFuel p n s'
      | .done out => .done out
      | .fault k => .fault k := by
  induction m generalizing s with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ k ih =>
    rw [Nat.succ_add]
    dsimp [evalMirFuel]
    cases evalStep p 0 s with
    | step s' => exact ih s'
    | done _ => rfl
    | fault _ => rfl

private theorem evalTupleAssertFuel_add (p : Program) (m n : Nat) (s : StateExt) :
    evalTupleAssertFuel p (m + n) s =
      match evalTupleAssertFuel p m s with
      | .step s' => evalTupleAssertFuel p n s'
      | .done out => .done out
      | .fault k => .fault k := by
  induction m generalizing s with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ k ih =>
    rw [Nat.succ_add]
    dsimp [evalTupleAssertFuel]
    cases evalStepTupleAssert p 0 s with
    | step s' => exact ih s'
    | done _ => rfl
    | fault _ => rfl

private theorem reaches_of_evalMirFuel {p : Program} {n : Nat} {s₀ s : State}
    (h : evalMirFuel p n s₀ = .step s) : Reaches p s₀ s := by
  induction n generalizing s₀ with
  | zero =>
    dsimp [evalMirFuel] at h
    injection h with hEq; subst hEq
    exact Reaches.refl s₀
  | succ k ih =>
    dsimp [evalMirFuel] at h
    cases hStep : evalStep p 0 s₀ with
    | step s' =>
      rw [hStep] at h
      exact reaches_head_priv ⟨0, rfl, hStep⟩ (ih h)
    | done _ => rw [hStep] at h; cases h
    | fault _ => rw [hStep] at h; cases h

private theorem exists_evalMirFuel_of_reaches {p : Program} {s₀ s : State}
    (h : Reaches p s₀ s) : ∃ n, evalMirFuel p n s₀ = .step s := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hStep ih =>
    let ⟨n, hn⟩ := ih
    let ⟨c, hc, hEval⟩ := hStep
    have hc0 : c = 0 := hc
    subst hc0
    refine ⟨n + 1, ?_⟩
    rw [evalMirFuel_add, hn]
    dsimp [evalMirFuel]
    rw [hEval]

private theorem reachesTupleAssert_of_evalFuel {p : Program} {n : Nat} {s₀ s : StateExt}
    (h : evalTupleAssertFuel p n s₀ = .step s) : ReachesTupleAssert p s₀ s := by
  induction n generalizing s₀ with
  | zero =>
    dsimp [evalTupleAssertFuel] at h
    injection h with hEq; subst hEq
    exact ReachesTupleAssert.refl s₀
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at h
    cases hStep : evalStepTupleAssert p 0 s₀ with
    | step s' =>
      rw [hStep] at h
      exact reachesTupleAssert_head_priv ⟨0, rfl, hStep⟩ (ih h)
    | done _ => rw [hStep] at h; cases h
    | fault _ => rw [hStep] at h; cases h

private theorem exists_evalTupleAssertFuel_of_reaches {p : Program} {s₀ s : StateExt}
    (h : ReachesTupleAssert p s₀ s) :
    ∃ n, evalTupleAssertFuel p n s₀ = .step s := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hStep ih =>
    let ⟨n, hn⟩ := ih
    let ⟨c, hc, hEval⟩ := hStep
    have hc0 : c = 0 := hc
    subst hc0
    refine ⟨n + 1, ?_⟩
    rw [evalTupleAssertFuel_add, hn]
    dsimp [evalTupleAssertFuel]
    rw [hEval]

private theorem evalTupleAssertFuel_terminal_of_reaches {p : Program}
    {s₀ s : StateExt} {res : StepResult StateExt TerminalOutExt}
    (hR : ReachesTupleAssert p s₀ s)
    (hS : StepTupleAssert p s res) :
    ∃ n, evalTupleAssertFuel p (n + 1) s₀ = res := by
  let ⟨n, hn⟩ := exists_evalTupleAssertFuel_of_reaches hR
  let ⟨c, hc, hEval⟩ := hS
  have hc0 : c = 0 := hc
  subst hc0
  refine ⟨n, ?_⟩
  rw [evalTupleAssertFuel_add, hn]
  dsimp [evalTupleAssertFuel]
  rw [hEval]
  cases res <;> rfl

private theorem reaches_and_step_of_evalTupleAssertFuel_done {p : Program}
    {n : Nat} {s₀ : StateExt} {out : TerminalOutExt}
    (h : evalTupleAssertFuel p n s₀ = .done out) :
    ∃ s, ReachesTupleAssert p s₀ s ∧ StepTupleAssert p s (.done out) := by
  induction n generalizing s₀ with
  | zero => dsimp [evalTupleAssertFuel] at h; cases h
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at h
    cases hStep : evalStepTupleAssert p 0 s₀ with
    | step s' =>
      rw [hStep] at h
      let ⟨s, hR, hT⟩ := ih h
      exact ⟨s, reachesTupleAssert_head_priv ⟨0, rfl, hStep⟩ hR, hT⟩
    | done o =>
      rw [hStep] at h
      injection h with hEq; subst hEq
      exact ⟨s₀, ReachesTupleAssert.refl s₀, ⟨0, rfl, hStep⟩⟩
    | fault _ => rw [hStep] at h; cases h

private theorem reaches_and_step_of_evalTupleAssertFuel_fault {p : Program}
    {n : Nat} {s₀ : StateExt} {fk : FaultKind}
    (h : evalTupleAssertFuel p n s₀ = .fault fk) :
    ∃ s, ReachesTupleAssert p s₀ s ∧ StepTupleAssert p s (.fault fk) := by
  induction n generalizing s₀ with
  | zero => dsimp [evalTupleAssertFuel] at h; cases h
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at h
    cases hStep : evalStepTupleAssert p 0 s₀ with
    | step s' =>
      rw [hStep] at h
      let ⟨s, hR, hT⟩ := ih h
      exact ⟨s, reachesTupleAssert_head_priv ⟨0, rfl, hStep⟩ hR, hT⟩
    | done _ => rw [hStep] at h; cases h
    | fault k' =>
      rw [hStep] at h
      injection h with hEq; subst hEq
      exact ⟨s₀, ReachesTupleAssert.refl s₀, ⟨0, rfl, hStep⟩⟩

private theorem evalMirFuel_mono_of_le {p : Program} {m n : Nat} {s₀ : State}
    (hLe : m ≤ n) :
    (∀ s', evalMirFuel p n s₀ = .step s' →
      ∃ sm, evalMirFuel p m s₀ = .step sm) := by
  intro s' hN
  have hAdd : m + (n - m) = n := nat_sub_add_cancel_of_le hLe
  rw [← hAdd, evalMirFuel_add] at hN
  cases hM : evalMirFuel p m s₀ with
  | step sm => exact ⟨sm, rfl⟩
  | done _ => rw [hM] at hN; cases hN
  | fault _ => rw [hM] at hN; cases hN

private theorem evalTupleAssertFuel_mono_step {p : Program} {m n : Nat} {s₀ : StateExt}
    (hLe : m ≤ n) {s' : StateExt}
    (hN : evalTupleAssertFuel p n s₀ = .step s') :
    ∃ sm, evalTupleAssertFuel p m s₀ = .step sm := by
  have hAdd : m + (n - m) = n := nat_sub_add_cancel_of_le hLe
  rw [← hAdd, evalTupleAssertFuel_add] at hN
  cases hM : evalTupleAssertFuel p m s₀ with
  | step sm => exact ⟨sm, rfl⟩
  | done _ => rw [hM] at hN; cases hN
  | fault _ => rw [hM] at hN; cases hN

private theorem diverges_iff_forall_evalMirFuel (p : Program) (q : Query) :
    Diverges p q ↔
      ∃ s₀ : State,
        initState p q = .ok s₀ ∧
        ∀ n : Nat, ∃ s' : State, evalMirFuel p n s₀ = .step s' := by
  constructor
  · intro ⟨s₀, hInit, trace, h0, hSteps⟩
    refine ⟨s₀, hInit, ?_⟩
    intro n
    have hFuel : ∀ k, evalMirFuel p k s₀ = .step (trace k) := by
      intro k
      induction k with
      | zero => exact congrArg StepResult.step h0.symm
      | succ m ih =>
        rw [evalMirFuel_add, ih]
        dsimp [evalMirFuel]
        let ⟨c, hc, hEv⟩ := hSteps m
        have hc0 : c = 0 := hc
        subst hc0
        rw [hEv]
    exact ⟨trace n, hFuel n⟩
  · intro ⟨s₀, hInit, hAll⟩
    refine ⟨s₀, hInit, iterMirStep p s₀, rfl, ?_⟩
    have hFuel : ∀ k, evalMirFuel p k s₀ = .step (iterMirStep p s₀ k) := by
      intro k
      induction k with
      | zero => rfl
      | succ m ih =>
        let ⟨sNext, hNext⟩ := hAll (m + 1)
        rw [evalMirFuel_add, ih] at hNext
        dsimp [evalMirFuel] at hNext
        cases hEv : evalStep p 0 (iterMirStep p s₀ m) with
        | step s' =>
          rw [hEv] at hNext
          injection hNext with hEq; subst hEq
          rw [evalMirFuel_add, ih]
          dsimp [evalMirFuel, iterMirStep]
          rw [hEv]
        | done _ => rw [hEv] at hNext; cases hNext
        | fault _ => rw [hEv] at hNext; cases hNext
    intro n
    let ⟨sNext, hNext⟩ := hAll (n + 1)
    rw [evalMirFuel_add, hFuel n] at hNext
    dsimp [evalMirFuel] at hNext
    cases hEv : evalStep p 0 (iterMirStep p s₀ n) with
    | step s' =>
      dsimp [iterMirStep]
      rw [hEv]
      exact ⟨0, rfl, hEv⟩
    | done _ => rw [hEv] at hNext; cases hNext
    | fault _ => rw [hEv] at hNext; cases hNext

private theorem evalStatement_never_done {body : Body} {frame : FrameState}
    {mem : CallerMemory} {stmt : StatementKind} {out : TerminalOut} :
    evalStatement body frame mem stmt ≠ .done out := by
  intro h
  cases stmt with
  | nop => dsimp [evalStatement] at h; cases h
  | unsupported => dsimp [evalStatement] at h; cases h
  | storageLive id =>
    dsimp [evalStatement] at h
    cases hTy : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [hTy] at h; cases h
    | some ty =>
      rw [hTy] at h; dsimp at h
      cases hS : setElem? frame.locals id (liveUninitSlot ty) <;>
        (rw [hS] at h; cases h)
  | storageDead id =>
    dsimp [evalStatement] at h
    cases hZ : Nat.beq id 0 with
    | true => rw [hZ] at h; cases h
    | false =>
      rw [hZ] at h; dsimp at h
      cases hS : setElem? frame.locals id .dead <;>
        (rw [hS] at h; cases h)
  | assign dst rv =>
    dsimp [evalStatement] at h
    cases hP : dst.projection.isEmpty with
    | false => rw [hP] at h; cases h
    | true =>
      rw [hP] at h; dsimp at h
      cases hTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hTy] at h; cases h
      | some ty =>
        rw [hTy] at h; dsimp at h
        cases hRv : evalRvalue body.locals frame.locals ty rv with
        | error _ => rw [hRv] at h; cases h
        | ok pair =>
          rw [hRv] at h; dsimp at h
          cases pair with
          | mk v l' =>
            dsimp at h
            cases hW : writePlace l' dst.localId ty v <;>
              (rw [hW] at h; cases h)

private theorem evalTerminator_never_unwound {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : CallerMemory} {um : CallerMemory} :
    evalTerminator body bb frame mem ≠ .done (.unwound um) := by
  intro h
  unfold evalTerminator at h
  cases hT : bb.terminator with
  | goto _ => rw [hT] at h; cases h
  | unreachable => rw [hT] at h; cases h
  | unwindResume => rw [hT] at h; cases h
  | assert _ _ _ _ _ => rw [hT] at h; cases h
  | call _ _ _ _ _ => rw [hT] at h; cases h
  | unsupported => rw [hT] at h; cases h
  | return_ =>
    rw [hT] at h; dsimp at h
    cases hCl : bb.cleanup with
    | true => rw [hCl] at h; cases h
    | false =>
      rw [hCl] at h; dsimp at h
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at h; cases h
      | some sl =>
        rw [h0] at h
        cases sl with
        | dead => cases h
        | live ov =>
          cases ov with
          | none => cases h
          | some _ => cases h
  | switchInt discr targets =>
    rw [hT] at h; dsimp at h
    cases hOp : evalPrimitiveOperand body.locals frame.locals discr with
    | error _ => rw [hOp] at h; cases h
    | ok pair =>
      rw [hOp] at h; dsimp at h
      cases pair with
      | mk dv l' =>
        dsimp at h
        cases dv with
        | scalar sv =>
          dsimp at h
          cases hB : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;>
            (rw [hB] at h; cases h)
        | bool b =>
          dsimp at h
          cases hB : evalBoolSwitchBranches b targets.otherwise targets.branches <;>
            (rw [hB] at h; cases h)
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases h

private theorem evalStep_never_unwound {p : Program} {c : Choice} {s : State}
    {um : CallerMemory} :
    evalStep p c s ≠ .done (.unwound um) := by
  intro h
  unfold evalStep at h
  cases hF : s.frames with
  | nil => rw [hF] at h; cases h
  | cons frame rest =>
    rw [hF] at h
    cases rest with
    | cons _ _ => cases h
    | nil =>
      dsimp at h
      cases hB : Trusted.MirSemantics.getElem? p.bodies frame.defId with
      | none => rw [hB] at h; cases h
      | some body =>
        rw [hB] at h; dsimp at h
        cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [hBb] at h; cases h
        | some bb =>
          rw [hBb] at h; dsimp at h
          cases hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | some stmt =>
            rw [hSt] at h
            exact evalStatement_never_done h
          | none =>
            rw [hSt] at h; dsimp at h
            cases hLen : Nat.beq frame.stmtIdx bb.statements.length with
            | false => rw [hLen] at h; cases h
            | true =>
              rw [hLen] at h; dsimp at h
              exact evalTerminator_never_unwound h

private theorem behavior_unwound_false (p : Program) (q : Query) (um : CallerMemory) :
    ¬ Behavior p q (.unwound um) := by
  intro h
  unfold Behavior ReachesResult at h
  cases hInit : initState p q with
  | error _ => rw [hInit] at h; cases h
  | ok _ =>
    rw [hInit] at h
    let ⟨_, _, c, _, hEv⟩ := h
    exact evalStep_never_unwound hEv

/-! ### Type Soundness Invariant for `M_tupleAssert` (`LocalsWellTyped` & `StateWellTyped`) -/

private noncomputable def SlotWellTyped (ty : MirTy) (slot : LocalSlotExt) : Prop :=
  match ty with
  | .tuple fieldTys =>
    if isFlatTupleTy (.tuple fieldTys) then
      match slot with
      | .dead => True
      | .liveTuple fields =>
        fields.length = fieldTys.length ∧
        ∀ (j : Nat) (fty : MirTy) (v : Val),
          Trusted.MirSemantics.getElem? fieldTys j = some fty →
          Trusted.MirSemantics.getElem? fields j = some (some v) →
          checkVal v fty = true
      | .liveBase _ => False
    else
      False
  | _ =>
    match slot with
    | .dead => True
    | .liveBase optVal =>
      match optVal with
      | none => True
      | some v => checkVal v ty = true
    | .liveTuple _ => False

private noncomputable def LocalsWellTyped (bodyLocals : List MirTy)
    (locals : List LocalSlotExt) : Prop :=
  locals.length = bodyLocals.length ∧
  ∀ (i : Nat) (ty : MirTy) (slot : LocalSlotExt),
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? locals i = some slot →
    SlotWellTyped ty slot

private noncomputable def StateWellTyped (p : Program) (s : StateExt) : Prop :=
  ∃ frame body,
    s.frames = [frame] ∧
    Trusted.MirSemantics.getElem? p.bodies frame.defId = some body ∧
    body.locals.all isSupportedTupleOrScalarTy = true ∧
    LocalsWellTyped body.locals frame.locals

private theorem findDiscrVariantAux_lt {idx : Nat} {bits : BitVec 128}
    {ds : List Nat} {v : Nat}
    (h : findDiscrVariantAux idx bits ds = some v) :
    idx ≤ v ∧ v < idx + ds.length := by
  induction ds generalizing idx with
  | nil => cases h
  | cons d rest ih =>
    dsimp [findDiscrVariantAux] at h
    cases hEq : (BitVec.ofNat 128 d == bits) with
    | true =>
      rw [hEq] at h
      dsimp at h
      injection h with hV; subst hV
      exact ⟨Nat.le_refl idx, by
        dsimp [List.length]
        rw [Nat.add_succ]
        exact Nat.lt_succ_of_le (Nat.le_add_right idx rest.length)⟩
    | false =>
      rw [hEq] at h
      dsimp at h
      let ⟨hGe, hLt⟩ := ih h
      have hAdd : idx + 1 + rest.length = idx + (rest.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 rest.length]
      rw [hAdd] at hLt
      exact ⟨Nat.le_trans (Nat.le_succ idx) hGe, hLt⟩

private theorem findDiscrVariant?_lt {bits : BitVec 128} {ds : List Nat} {v : Nat}
    (h : findDiscrVariant? bits ds = some v) : v < ds.length := by
  let ⟨_, hLt⟩ := findDiscrVariantAux_lt h
  rw [Nat.zero_add] at hLt
  exact hLt

private theorem evalConstLit_checkVal {ty : MirTy} {lit : ConstLit} {v : Val}
    (h : evalConstLit ty lit = .ok v) : checkVal v ty = true := by
  cases ty with
  | int w s =>
    cases lit with
    | zeroSized => cases h
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases hNe : (truncateBits w bits != bits) with
      | true => rw [hNe] at h; cases h
      | false =>
        rw [hNe] at h; dsimp at h
        injection h with hEq; subst hEq
        have hEqB : (truncateBits w bits == bits) = true := by
          unfold bne at hNe
          exact bool_not_false hNe
        have hTrunc : truncateBits w bits = bits := bitvec_beq_eq hEqB
        unfold checkVal Val.ty? ScalarVal.wf
        dsimp
        rw [hTrunc, hEqB]
        dsimp
        exact mirTy_beq_refl (.int w s)
  | bool =>
    cases lit with
    | zeroSized => cases h
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases hNe : (truncateBits .i8 bits != bits) with
      | true => rw [hNe] at h; cases h
      | false =>
        rw [hNe] at h; dsimp at h
        cases h0 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) with
        | true =>
          rw [h0] at h; dsimp at h
          injection h with hEq; subst hEq; rfl
        | false =>
          rw [h0] at h; dsimp at h
          cases h1 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) with
          | true =>
            rw [h1] at h; dsimp at h
            injection h with hEq; subst hEq; rfl
          | false => rw [h1] at h; cases h
  | unit =>
    cases lit with
    | scalar _ => cases h
    | zeroSized =>
      dsimp [evalConstLit] at h
      injection h with hEq; subst hEq; rfl
  | enum ety =>
    cases lit with
    | zeroSized =>
      dsimp [evalConstLit] at h
      cases hZ : isZstEnumTy ety with
      | false => rw [hZ] at h; cases h
      | true =>
        rw [hZ] at h; dsimp at h
        injection h with hEq; subst hEq
        unfold isZstEnumTy at hZ
        cases hTr : ety.tagRepr with
        | scalar _ _ => rw [hTr] at hZ; cases hZ
        | zeroSized =>
          rw [hTr] at hZ
          have hAdm : enumAdmitted ety = true := hZ
          unfold enumAdmitted at hZ
          rw [hTr] at hZ
          let ⟨_, hLen1⟩ := bool_and_true hZ
          have hEq1 : ety.discriminants.length = 1 := nat_beq_eq hLen1
          unfold checkVal Val.ty?
          dsimp
          rw [hAdm, hEq1]
          dsimp
          exact enumTy_beq_refl ety
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases hTr : ety.tagRepr with
      | zeroSized => rw [hTr] at h; cases h
      | scalar tagW tagS =>
        rw [hTr] at h; dsimp at h
        cases hBad : (!enumAdmitted ety || truncateBits tagW bits != bits) with
        | true => rw [hBad] at h; cases h
        | false =>
          rw [hBad] at h; dsimp at h
          let ⟨hNotAdm, _⟩ := bool_or_false hBad
          have hAdm : enumAdmitted ety = true := bool_not_false hNotAdm
          cases hFind : findDiscrVariant?
              (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
              ety.discriminants with
          | none => rw [hFind] at h; cases h
          | some idx =>
            rw [hFind] at h; dsimp at h
            injection h with hEq; subst hEq
            have hLt : idx < ety.discriminants.length := findDiscrVariant?_lt hFind
            unfold checkVal Val.ty?
            dsimp
            rw [hAdm, nat_lt_blt hLt]
            dsimp
            exact enumTy_beq_refl ety
  | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases lit <;> cases h

private theorem liveUninitFieldVal_checkVal {ty : MirTy} {v : Val}
    (h : liveUninitFieldVal ty = some v) : checkVal v ty = true := by
  cases ty with
  | unit =>
    dsimp [liveUninitFieldVal] at h
    injection h with hEq; subst hEq; rfl
  | enum ety =>
    dsimp [liveUninitFieldVal] at h
    cases hZ : isZstEnumTy ety with
    | false => rw [hZ] at h; cases h
    | true =>
      rw [hZ] at h; dsimp at h
      injection h with hEq; subst hEq
      have hC : evalConstLit (.enum ety) .zeroSized = .ok (.enumVal ety 0) := by
        dsimp [evalConstLit]; rw [hZ]; rfl
      exact evalConstLit_checkVal hC
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases h

private theorem slotWellTyped_liveUninitSlotExt {ty : MirTy}
    (hSup : isSupportedTupleOrScalarTy ty = true) :
    SlotWellTyped ty (liveUninitSlotExt ty) := by
  cases ty with
  | tuple fieldTys =>
    unfold isSupportedTupleOrScalarTy isSupportedScalarOrUnitTy at hSup
    change isFlatTupleTy (.tuple fieldTys) = true at hSup
    unfold SlotWellTyped liveUninitSlotExt
    dsimp
    rw [hSup]
    dsimp
    refine ⟨map_length_eq liveUninitFieldVal fieldTys, ?_⟩
    intro j fty v hFty hField
    rw [getElem?_map, hFty] at hField
    dsimp [Option.map] at hField
    injection hField with hLive
    exact liveUninitFieldVal_checkVal hLive
  | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
    unfold SlotWellTyped liveUninitSlotExt
    dsimp
    cases hV : liveUninitFieldVal _ with
    | none => exact True.intro
    | some v => exact liveUninitFieldVal_checkVal hV

private theorem checkArgsMatch_getElem? {vs : List Val} {tys : List MirTy}
    (h : checkArgsMatch vs tys = true) :
    vs.length = tys.length ∧
    ∀ i v ty,
      Trusted.MirSemantics.getElem? vs i = some v →
      Trusted.MirSemantics.getElem? tys i = some ty →
      checkVal v ty = true := by
  induction vs generalizing tys with
  | nil =>
    cases tys with
    | nil =>
      refine ⟨rfl, ?_⟩
      intro _ _ _ hV _; cases hV
    | cons _ _ => cases h
  | cons v rest ih =>
    cases tys with
    | nil => cases h
    | cons ty restTys =>
      let ⟨hv, hRest⟩ := bool_and_true h
      let ⟨hLen, hAt⟩ := ih hRest
      refine ⟨by dsimp [List.length]; rw [hLen], ?_⟩
      intro i v' ty' hV hTy
      cases i with
      | zero =>
        injection hV with hEqV; subst hEqV
        injection hTy with hEqT; subst hEqT
        exact hv
      | succ k => exact hAt k v' ty' hV hTy

private theorem checkArgsMatchExt_getElem? {vs : List Val} {tys : List MirTy}
    (h : checkArgsMatchExt vs tys = true) :
    vs.length = tys.length ∧
    ∀ i v ty,
      Trusted.MirSemantics.getElem? vs i = some v →
      Trusted.MirSemantics.getElem? tys i = some ty →
      checkValExt v ty = true := by
  induction vs generalizing tys with
  | nil =>
    cases tys with
    | nil =>
      refine ⟨rfl, ?_⟩
      intro _ _ _ hV _; cases hV
    | cons _ _ => cases h
  | cons v rest ih =>
    cases tys with
    | nil => cases h
    | cons ty restTys =>
      let ⟨hv, hRest⟩ := bool_and_true h
      let ⟨hLen, hAt⟩ := ih hRest
      refine ⟨by dsimp [List.length]; rw [hLen], ?_⟩
      intro i v' ty' hV hTy
      cases i with
      | zero =>
        injection hV with hEqV; subst hEqV
        injection hTy with hEqT; subst hEqT
        exact hv
      | succ k => exact hAt k v' ty' hV hTy

private theorem slotWellTyped_initArgSlotExt {ty : MirTy} {v : Val}
    (hCheck : checkValExt v ty = true) :
    SlotWellTyped ty (initArgSlotExt ty v) := by
  cases ty with
  | tuple fieldTys =>
    unfold checkValExt at hCheck
    dsimp at hCheck
    cases hFlat : isFlatTupleTy (.tuple fieldTys) with
    | false => rw [hFlat] at hCheck; cases hCheck
    | true =>
      rw [hFlat] at hCheck; dsimp at hCheck
      cases v with
      | tuple vs =>
        dsimp at hCheck
        let ⟨hLen, hAt⟩ := checkArgsMatch_getElem? hCheck
        unfold SlotWellTyped initArgSlotExt
        dsimp
        rw [hFlat]
        dsimp
        refine ⟨by rw [map_length_eq]; exact hLen, ?_⟩
        intro j fty vj hFty hField
        rw [getElem?_map] at hField
        cases hVj : Trusted.MirSemantics.getElem? vs j with
        | none => rw [hVj] at hField; cases hField
        | some v' =>
          rw [hVj] at hField
          dsimp [Option.map] at hField
          injection hField with hEqSome
          injection hEqSome with hEqV
          subst hEqV
          exact hAt j v' fty hVj hFty
      | scalar _ | ptr _ | bool _ | unit | enumVal _ _ | bytes _ => cases hCheck
  | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
    unfold checkValExt at hCheck
    unfold SlotWellTyped initArgSlotExt
    exact hCheck

private theorem initStateTupleAssert_stateWellTyped {p : Program} {q : Query}
    {s₀ : StateExt} (h : initStateTupleAssert p q = .ok s₀) :
    StateWellTyped p s₀ := by
  unfold initStateTupleAssert at h
  cases hHdr : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) with
  | true => rw [hHdr] at h; cases h
  | false =>
    rw [hHdr] at h; dsimp at h
    cases hMem : (!q.callerMem.allocations.isEmpty) with
    | true => rw [hMem] at h; cases h
    | false =>
      rw [hMem] at h; dsimp at h
      cases hBody : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
      | none => rw [hBody] at h; cases h
      | some body =>
        rw [hBody] at h; dsimp at h
        cases hEmpty : body.basicBlocks.isEmpty with
        | true => rw [hEmpty] at h; cases h
        | false =>
          rw [hEmpty] at h; dsimp at h
          cases hArgLt : (!Nat.blt body.argumentCount body.locals.length) with
          | true => rw [hArgLt] at h; cases h
          | false =>
            rw [hArgLt] at h; dsimp at h
            cases hStg : (!storageAnnotationsInBounds body) with
            | true => rw [hStg] at h; cases h
            | false =>
              rw [hStg] at h; dsimp at h
              cases hSup : (!body.locals.all isSupportedTupleOrScalarTy) with
              | true => rw [hSup] at h; cases h
              | false =>
                rw [hSup] at h; dsimp at h
                have hAllSup : body.locals.all isSupportedTupleOrScalarTy = true :=
                  bool_not_false hSup
                cases hArgs : (!checkArgsMatchExt q.args
                    ((body.locals.drop 1).take body.argumentCount)) with
                | true => rw [hArgs] at h; cases h
                | false =>
                  rw [hArgs] at h; dsimp at h
                  have hArgsOk : checkArgsMatchExt q.args
                      ((body.locals.drop 1).take body.argumentCount) = true :=
                    bool_not_false hArgs
                  let ⟨_, hArgAt⟩ := checkArgsMatchExt_getElem? hArgsOk
                  injection h with hEq; subst hEq
                  refine ⟨_, body, rfl, hBody, hAllSup, ?_, ?_⟩
                  · exact initLocalsExtLoop_length body q.args 0 body.locals
                  · intro i ty slot hTy hSlot
                    have hSlotEq := initLocalsExtLoop_getElem? body q.args 0 body.locals i ty hTy
                    rw [hSlotEq] at hSlot
                    injection hSlot with hSlotVal
                    subst hSlotVal
                    rw [Nat.zero_add]
                    have hTySup : isSupportedTupleOrScalarTy ty = true :=
                      list_all_getElem? hAllSup hTy
                    cases hZ : Nat.beq i 0 with
                    | true =>
                      dsimp
                      exact slotWellTyped_liveUninitSlotExt hTySup
                    | false =>
                      dsimp
                      cases hLe : Nat.ble i body.argumentCount with
                      | false =>
                        dsimp
                        cases hasStorageAnnotation body i with
                        | true =>
                          cases ty with
                          | tuple fieldTys =>
                            unfold isSupportedTupleOrScalarTy isSupportedScalarOrUnitTy at hTySup
                            change isFlatTupleTy (.tuple fieldTys) = true at hTySup
                            unfold SlotWellTyped
                            dsimp
                            rw [hTySup]
                            exact True.intro
                          | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                            exact True.intro
                        | false => exact slotWellTyped_liveUninitSlotExt hTySup
                      | true =>
                        dsimp
                        cases hArg : Trusted.MirSemantics.getElem? q.args (i - 1) with
                        | none =>
                          cases ty with
                          | tuple fieldTys =>
                            unfold isSupportedTupleOrScalarTy isSupportedScalarOrUnitTy at hTySup
                            change isFlatTupleTy (.tuple fieldTys) = true at hTySup
                            unfold SlotWellTyped
                            dsimp
                            rw [hTySup]
                            exact True.intro
                          | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                            exact True.intro
                        | some v =>
                          have hNe0 : i ≠ 0 := nat_ne_of_beq_false hZ
                          cases i with
                          | zero => exact False.elim (hNe0 rfl)
                          | succ k =>
                            have hLeArg : k + 1 ≤ body.argumentCount := nat_ble_le hLe
                            have hKLt : k < body.argumentCount := hLeArg
                            have hParamTy : Trusted.MirSemantics.getElem?
                                ((body.locals.drop 1).take body.argumentCount) k = some ty := by
                              rw [getElem?_take_drop1 body.locals body.argumentCount k hKLt]
                              exact hTy
                            have hCheck : checkValExt v ty = true :=
                              hArgAt k v ty hArg hParamTy
                            exact slotWellTyped_initArgSlotExt hCheck

private theorem localsWellTyped_set {bodyLocals : List MirTy}
    {locals locals' : List LocalSlotExt} {idx : Nat} {ty : MirTy}
    {newSlot : LocalSlotExt}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals idx = some ty)
    (hSet : setElem? locals idx newSlot = some locals')
    (hSlotWt : SlotWellTyped ty newSlot) :
    LocalsWellTyped bodyLocals locals' := by
  refine ⟨by rw [setElem?_length hSet, hWt.1], ?_⟩
  intro i ty' sl' hTy' hSl'
  cases hEq : Nat.beq i idx with
  | true =>
    have hi : i = idx := nat_beq_eq hEq
    subst hi
    rw [hTy] at hTy'
    injection hTy' with hEqTy; subst hEqTy
    rw [setElem?_getElem?_same hSet] at hSl'
    injection hSl' with hEqSl; subst hEqSl
    exact hSlotWt
  | false =>
    have hNe : i ≠ idx := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSet hNe] at hSl'
    exact hWt.2 i ty' sl' hTy' hSl'

private theorem slotWellTyped_dead {ty : MirTy}
    (hSup : isSupportedTupleOrScalarTy ty = true) :
    SlotWellTyped ty .dead := by
  cases ty with
  | tuple fieldTys =>
    unfold isSupportedTupleOrScalarTy isSupportedScalarOrUnitTy at hSup
    change isFlatTupleTy (.tuple fieldTys) = true at hSup
    unfold SlotWellTyped
    dsimp
    rw [hSup]
    exact True.intro
  | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
    exact True.intro

private theorem checkVal_of_extractAllInitFields {fieldTys : List MirTy}
    {fields : List (Option Val)} {vs : List Val}
    (hLen : fields.length = fieldTys.length)
    (hAt : ∀ (j : Nat) (fty : MirTy) (v : Val),
      Trusted.MirSemantics.getElem? fieldTys j = some fty →
      Trusted.MirSemantics.getElem? fields j = some (some v) →
      checkVal v fty = true)
    (hExt : extractAllInitFields fields = some vs) :
    checkArgsMatch vs fieldTys = true := by
  induction fields generalizing fieldTys vs with
  | nil =>
    cases fieldTys with
    | nil =>
      injection hExt with hEq; subst hEq; rfl
    | cons _ _ => cases hLen
  | cons f rest ih =>
    cases fieldTys with
    | nil => cases hLen
    | cons fty restTys =>
      cases f with
      | none => cases hExt
      | some v =>
        dsimp [extractAllInitFields] at hExt
        cases hSub : extractAllInitFields rest with
        | none => rw [hSub] at hExt; cases hExt
        | some vs' =>
          rw [hSub] at hExt
          injection hExt with hEq; subst hEq
          have hv : checkVal v fty = true := hAt 0 fty v rfl rfl
          have hTail : checkArgsMatch vs' restTys = true :=
            ih (Nat.succ.inj hLen) (fun j ft v' h1 h2 => hAt (j + 1) ft v' h1 h2) hSub
          exact bool_and_intro hv hTail

private theorem evalOperandToSlotExt_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlotExt} {opnd : Operand} {ty : MirTy}
    {optVal : Option Val}
    (hAllSup : bodyLocals.all isSupportedTupleOrScalarTy = true)
    (hWt : LocalsWellTyped bodyLocals locals)
    (hEv : evalOperandToSlotExt bodyLocals locals opnd = .ok (ty, optVal, locals')) :
    LocalsWellTyped bodyLocals locals' ∧
    (∀ v, optVal = some v → checkValExt v ty = true) := by
  cases opnd with
  | constant c =>
    dsimp [evalOperandToSlotExt] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok v =>
      rw [hC] at hEv
      injection hEv with hPair
      injection hPair with hTyEq hRest
      injection hRest with hOptEq hLocEq
      subst hTyEq; subst hOptEq; subst hLocEq
      refine ⟨hWt, ?_⟩
      intro v' hv'
      injection hv' with hVeq; subst hVeq
      have hCv := evalConstLit_checkVal hC
      cases hCty : c.ty with
      | tuple _ =>
        rw [hCty] at hC
        cases c.lit <;> cases hC
      | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
        rw [hCty] at hCv
        exact hCv
  | copy place =>
    cases place with
    | mk lid proj =>
      dsimp [evalOperandToSlotExt] at hEv
      cases proj with
      | nil =>
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
        | none => rw [hTy] at hEv; cases hEv
        | some declTy =>
          rw [hTy] at hEv
          cases hSl : Trusted.MirSemantics.getElem? locals lid with
          | none => rw [hSl] at hEv; cases hEv
          | some sl =>
            rw [hSl] at hEv; dsimp at hEv
            have hSlWt := hWt.2 lid declTy sl hTy hSl
            cases sl with
            | dead => cases hEv
            | liveBase ov =>
              dsimp at hEv
              cases hFlat : isFlatTupleTy declTy with
              | true => rw [hFlat] at hEv; cases hEv
              | false =>
                rw [hFlat] at hEv; dsimp at hEv
                injection hEv with hPair
                injection hPair with h1 hRest
                injection hRest with h2 h3
                subst h1; subst h2; subst h3
                refine ⟨hWt, ?_⟩
                intro v hv; subst hv
                cases declTy with
                | tuple fieldTys =>
                  have hSup := list_all_getElem? hAllSup hTy
                  unfold isSupportedTupleOrScalarTy isSupportedScalarOrUnitTy at hSup
                  change isFlatTupleTy (.tuple fieldTys) = true at hSup
                  rw [hSup] at hFlat; cases hFlat
                | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                  exact hSlWt
            | liveTuple fields =>
              cases declTy with
              | tuple fieldTys =>
                dsimp at hEv
                cases hCond : (isFlatTupleTy (.tuple fieldTys) &&
                    Nat.beq fields.length fieldTys.length) with
                | false => rw [hCond] at hEv; cases hEv
                | true =>
                  rw [hCond] at hEv; dsimp at hEv
                  let ⟨hFlat, _⟩ := bool_and_true hCond
                  injection hEv with hPair
                  injection hPair with h1 hRest
                  injection hRest with h2 h3
                  subst h1; subst h3
                  refine ⟨hWt, ?_⟩
                  intro v hv
                  rw [← h2] at hv
                  cases hExt : extractAllInitFields fields with
                  | none => rw [hExt] at hv; cases hv
                  | some vs =>
                    rw [hExt] at hv
                    injection hv with hVeq; subst hVeq
                    unfold SlotWellTyped at hSlWt
                    dsimp at hSlWt
                    rw [hFlat] at hSlWt
                    dsimp at hSlWt
                    unfold checkValExt
                    dsimp
                    rw [hFlat]
                    exact checkVal_of_extractAllInitFields hSlWt.1 hSlWt.2 hExt
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                cases hEv
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> cases hEv
        | nil =>
          cases pe with
          | deref => cases hEv
          | unsupported => cases hEv
          | field idx fieldTy =>
            dsimp at hEv
            cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
            | none => rw [hTy] at hEv; cases hEv
            | some declTy =>
              rw [hTy] at hEv
              cases declTy with
              | tuple fieldTys =>
                cases hSl : Trusted.MirSemantics.getElem? locals lid with
                | none => rw [hSl] at hEv; cases hEv
                | some sl =>
                  rw [hSl] at hEv; dsimp at hEv
                  cases hNotFlat : (!isFlatTupleTy (.tuple fieldTys)) with
                  | true => rw [hNotFlat] at hEv; cases hEv
                  | false =>
                    rw [hNotFlat] at hEv; dsimp at hEv
                    have hFlat := bool_not_false hNotFlat
                    cases hFty : Trusted.MirSemantics.getElem? fieldTys idx with
                    | none => rw [hFty] at hEv; cases hEv
                    | some declFieldTy =>
                      rw [hFty] at hEv; dsimp at hEv
                      cases hTyEq : (!MirTy.beq fieldTy declFieldTy) with
                      | true => rw [hTyEq] at hEv; cases hEv
                      | false =>
                        rw [hTyEq] at hEv; dsimp at hEv
                        cases sl with
                        | dead => cases hEv
                        | liveBase _ => cases hEv
                        | liveTuple fields =>
                          dsimp at hEv
                          cases hFv : Trusted.MirSemantics.getElem? fields idx with
                          | none => rw [hFv] at hEv; cases hEv
                          | some ov =>
                            rw [hFv] at hEv
                            injection hEv with hPair
                            injection hPair with h1 hRest
                            injection hRest with h2 h3
                            subst h1; subst h2; subst h3
                            refine ⟨hWt, ?_⟩
                            intro v hv; subst hv
                            have hSlWt := hWt.2 lid (.tuple fieldTys)
                              (.liveTuple fields) hTy hSl
                            unfold SlotWellTyped at hSlWt
                            dsimp at hSlWt
                            rw [hFlat] at hSlWt
                            have hCv := hSlWt.2 idx declFieldTy v hFty hFv
                            unfold isFlatTupleTy at hFlat
                            let ⟨_, hAllSc⟩ := bool_and_true hFlat
                            have hSc := list_all_getElem? hAllSc hFty
                            cases declFieldTy with
                            | tuple _ => cases hSc
                            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                              exact hCv
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                cases hEv
  | move place =>
    cases place with
    | mk lid proj =>
      dsimp [evalOperandToSlotExt] at hEv
      cases proj with
      | nil =>
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
        | none => rw [hTy] at hEv; cases hEv
        | some declTy =>
          rw [hTy] at hEv
          cases hSl : Trusted.MirSemantics.getElem? locals lid with
          | none => rw [hSl] at hEv; cases hEv
          | some sl =>
            rw [hSl] at hEv; dsimp at hEv
            have hSlWt := hWt.2 lid declTy sl hTy hSl
            have hTySup := list_all_getElem? hAllSup hTy
            cases sl with
            | dead => cases hEv
            | liveBase ov =>
              dsimp at hEv
              cases hFlat : isFlatTupleTy declTy with
              | true => rw [hFlat] at hEv; cases hEv
              | false =>
                rw [hFlat] at hEv; dsimp at hEv
                cases hSet : setElem? locals lid
                    (.liveBase (liveUninitFieldVal declTy)) with
                | none => rw [hSet] at hEv; cases hEv
                | some ls' =>
                  rw [hSet] at hEv
                  injection hEv with hPair
                  injection hPair with h1 hRest
                  injection hRest with h2 h3
                  subst h1; subst h2; subst h3
                  have hNewSlotWt : SlotWellTyped declTy
                      (.liveBase (liveUninitFieldVal declTy)) := by
                    cases declTy with
                    | tuple fieldTys =>
                      unfold isSupportedTupleOrScalarTy isSupportedScalarOrUnitTy at hTySup
                      change isFlatTupleTy (.tuple fieldTys) = true at hTySup
                      rw [hTySup] at hFlat; cases hFlat
                    | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                      exact slotWellTyped_liveUninitSlotExt hTySup
                  refine ⟨localsWellTyped_set hWt hTy hSet hNewSlotWt, ?_⟩
                  intro v hv; subst hv
                  cases declTy with
                  | tuple fieldTys =>
                    unfold isSupportedTupleOrScalarTy isSupportedScalarOrUnitTy at hTySup
                    change isFlatTupleTy (.tuple fieldTys) = true at hTySup
                    rw [hTySup] at hFlat; cases hFlat
                  | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                    exact hSlWt
            | liveTuple fields =>
              cases declTy with
              | tuple fieldTys =>
                dsimp at hEv
                cases hCond : (isFlatTupleTy (.tuple fieldTys) &&
                    Nat.beq fields.length fieldTys.length) with
                | false => rw [hCond] at hEv; cases hEv
                | true =>
                  rw [hCond] at hEv; dsimp at hEv
                  let ⟨hFlat, _⟩ := bool_and_true hCond
                  cases hSet : setElem? locals lid
                      (liveUninitSlotExt (.tuple fieldTys)) with
                  | none => rw [hSet] at hEv; cases hEv
                  | some ls' =>
                    rw [hSet] at hEv
                    injection hEv with hPair
                    injection hPair with h1 hRest
                    injection hRest with h2 h3
                    subst h1; subst h3
                    refine ⟨localsWellTyped_set hWt hTy hSet
                      (slotWellTyped_liveUninitSlotExt hTySup), ?_⟩
                    intro v hv
                    rw [← h2] at hv
                    cases hExt : extractAllInitFields fields with
                    | none => rw [hExt] at hv; cases hv
                    | some vs =>
                      rw [hExt] at hv
                      injection hv with hVeq; subst hVeq
                      unfold SlotWellTyped at hSlWt
                      dsimp at hSlWt
                      rw [hFlat] at hSlWt
                      unfold checkValExt
                      dsimp
                      rw [hFlat]
                      exact checkVal_of_extractAllInitFields hSlWt.1 hSlWt.2 hExt
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                cases hEv
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> cases hEv
        | nil =>
          cases pe with
          | deref => cases hEv
          | unsupported => cases hEv
          | field idx fieldTy =>
            dsimp at hEv
            cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
            | none => rw [hTy] at hEv; cases hEv
            | some declTy =>
              rw [hTy] at hEv
              cases declTy with
              | tuple fieldTys =>
                cases hSl : Trusted.MirSemantics.getElem? locals lid with
                | none => rw [hSl] at hEv; cases hEv
                | some sl =>
                  rw [hSl] at hEv; dsimp at hEv
                  cases hNotFlat : (!isFlatTupleTy (.tuple fieldTys)) with
                  | true => rw [hNotFlat] at hEv; cases hEv
                  | false =>
                    rw [hNotFlat] at hEv; dsimp at hEv
                    have hFlat := bool_not_false hNotFlat
                    cases hFty : Trusted.MirSemantics.getElem? fieldTys idx with
                    | none => rw [hFty] at hEv; cases hEv
                    | some declFieldTy =>
                      rw [hFty] at hEv; dsimp at hEv
                      cases hTyEq : (!MirTy.beq fieldTy declFieldTy) with
                      | true => rw [hTyEq] at hEv; cases hEv
                      | false =>
                        rw [hTyEq] at hEv; dsimp at hEv
                        cases sl with
                        | dead => cases hEv
                        | liveBase _ => cases hEv
                        | liveTuple fields =>
                          dsimp at hEv
                          cases hFv : Trusted.MirSemantics.getElem? fields idx with
                          | none => rw [hFv] at hEv; cases hEv
                          | some ov =>
                            rw [hFv] at hEv; dsimp at hEv
                            cases hSetF : setElem? fields idx
                                (liveUninitFieldVal declFieldTy) with
                            | none => rw [hSetF] at hEv; cases hEv
                            | some fields' =>
                              rw [hSetF] at hEv; dsimp at hEv
                              cases hSetL : setElem? locals lid
                                  (.liveTuple fields') with
                              | none => rw [hSetL] at hEv; cases hEv
                              | some ls' =>
                                rw [hSetL] at hEv
                                injection hEv with hPair
                                injection hPair with h1 hRest
                                injection hRest with h2 h3
                                subst h1; subst h2; subst h3
                                have hSlWt := hWt.2 lid (.tuple fieldTys)
                                  (.liveTuple fields) hTy hSl
                                unfold SlotWellTyped at hSlWt
                                dsimp at hSlWt
                                rw [hFlat] at hSlWt
                                have hNewSlotWt : SlotWellTyped (.tuple fieldTys)
                                    (.liveTuple fields') := by
                                  unfold SlotWellTyped
                                  dsimp
                                  rw [hFlat]
                                  refine ⟨by rw [setElem?_length hSetF, hSlWt.1], ?_⟩
                                  intro j ft vj hFt hFj
                                  cases hJEq : Nat.beq j idx with
                                  | true =>
                                    have hj : j = idx := nat_beq_eq hJEq
                                    subst hj
                                    rw [hFty] at hFt
                                    injection hFt with hEqFt; subst hEqFt
                                    rw [setElem?_getElem?_same hSetF] at hFj
                                    injection hFj with hLive
                                    exact liveUninitFieldVal_checkVal hLive
                                  | false =>
                                    have hNe := nat_ne_of_beq_false hJEq
                                    rw [setElem?_getElem?_ne hSetF hNe] at hFj
                                    exact hSlWt.2 j ft vj hFt hFj
                                refine ⟨localsWellTyped_set hWt hTy hSetL hNewSlotWt, ?_⟩
                                intro v hv; subst hv
                                have hCv := hSlWt.2 idx declFieldTy v hFty hFv
                                unfold isFlatTupleTy at hFlat
                                let ⟨_, hAllSc⟩ := bool_and_true hFlat
                                have hSc := list_all_getElem? hAllSc hFty
                                cases declFieldTy with
                                | tuple _ => cases hSc
                                | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                                  exact hCv
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                cases hEv

private theorem evalOperandToSlotExt_staticTy {bodyLocals : List MirTy}
    {locals locals' : List LocalSlotExt} {opnd : Operand} {ty : MirTy}
    {optVal : Option Val}
    (hEv : evalOperandToSlotExt bodyLocals locals opnd = .ok (ty, optVal, locals')) :
    operandStaticTy? bodyLocals opnd = some ty := by
  cases opnd with
  | constant c =>
    dsimp [evalOperandToSlotExt] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok _ =>
      rw [hC] at hEv
      injection hEv with hPair
      injection hPair with hTyEq _
      subst hTyEq
      rfl
  | copy place =>
    cases place with
    | mk lid proj =>
      dsimp [evalOperandToSlotExt] at hEv
      dsimp [operandStaticTy?, placeStaticTy?]
      cases proj with
      | nil =>
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
        | none => rw [hTy] at hEv; cases hEv
        | some declTy =>
          rw [hTy] at hEv; dsimp
          cases hSl : Trusted.MirSemantics.getElem? locals lid with
          | none => rw [hSl] at hEv; cases hEv
          | some sl =>
            rw [hSl] at hEv
            cases sl with
            | dead => cases hEv
            | liveBase _ =>
              dsimp at hEv
              cases hFl : isFlatTupleTy declTy with
              | true => rw [hFl] at hEv; cases hEv
              | false =>
                rw [hFl] at hEv; dsimp at hEv
                injection hEv with hPair
                injection hPair with hTyEq _
                subst hTyEq; rfl
            | liveTuple fields =>
              cases declTy with
              | tuple fieldTys =>
                dsimp at hEv
                cases hC : (isFlatTupleTy (.tuple fieldTys) &&
                    Nat.beq fields.length fieldTys.length) with
                | false => rw [hC] at hEv; cases hEv
                | true =>
                  rw [hC] at hEv; dsimp at hEv
                  injection hEv with hPair
                  injection hPair with hTyEq _
                  subst hTyEq; rfl
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                cases hEv
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> cases hEv
        | nil =>
          cases pe with
          | deref => cases hEv
          | unsupported => cases hEv
          | field idx fieldTy =>
            dsimp at hEv
            cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
            | none => rw [hTy] at hEv; cases hEv
            | some declTy =>
              rw [hTy] at hEv; dsimp
              cases declTy with
              | tuple fieldTys =>
                dsimp
                cases hSl : Trusted.MirSemantics.getElem? locals lid with
                | none => rw [hSl] at hEv; cases hEv
                | some sl =>
                  rw [hSl] at hEv; dsimp at hEv
                  cases hNf : (!isFlatTupleTy (.tuple fieldTys)) with
                  | true => rw [hNf] at hEv; cases hEv
                  | false =>
                    rw [hNf] at hEv; dsimp at hEv
                    rw [bool_not_false hNf]; dsimp
                    cases hFty : Trusted.MirSemantics.getElem? fieldTys idx with
                    | none => rw [hFty] at hEv; cases hEv
                    | some declFieldTy =>
                      rw [hFty] at hEv; dsimp at hEv
                      dsimp
                      cases hNt : (!MirTy.beq fieldTy declFieldTy) with
                      | true => rw [hNt] at hEv; cases hEv
                      | false =>
                        rw [hNt] at hEv; dsimp at hEv
                        rw [bool_not_false hNt]; dsimp
                        cases sl with
                        | dead | liveBase _ => cases hEv
                        | liveTuple fields =>
                          dsimp at hEv
                          cases hFv : Trusted.MirSemantics.getElem? fields idx with
                          | none => rw [hFv] at hEv; cases hEv
                          | some _ =>
                            rw [hFv] at hEv
                            injection hEv with hPair
                            injection hPair with hTyEq _
                            subst hTyEq; rfl
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                cases hEv
  | move place =>
    cases place with
    | mk lid proj =>
      dsimp [evalOperandToSlotExt] at hEv
      dsimp [operandStaticTy?, placeStaticTy?]
      cases proj with
      | nil =>
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
        | none => rw [hTy] at hEv; cases hEv
        | some declTy =>
          rw [hTy] at hEv; dsimp
          cases hSl : Trusted.MirSemantics.getElem? locals lid with
          | none => rw [hSl] at hEv; cases hEv
          | some sl =>
            rw [hSl] at hEv
            cases sl with
            | dead => cases hEv
            | liveBase _ =>
              dsimp at hEv
              cases hFl : isFlatTupleTy declTy with
              | true => rw [hFl] at hEv; cases hEv
              | false =>
                rw [hFl] at hEv; dsimp at hEv
                cases hSet : setElem? locals lid
                    (.liveBase (liveUninitFieldVal declTy)) with
                | none => rw [hSet] at hEv; cases hEv
                | some _ =>
                  rw [hSet] at hEv
                  injection hEv with hPair
                  injection hPair with hTyEq _
                  subst hTyEq; rfl
            | liveTuple fields =>
              cases declTy with
              | tuple fieldTys =>
                dsimp at hEv
                cases hC : (isFlatTupleTy (.tuple fieldTys) &&
                    Nat.beq fields.length fieldTys.length) with
                | false => rw [hC] at hEv; cases hEv
                | true =>
                  rw [hC] at hEv; dsimp at hEv
                  cases hSet : setElem? locals lid
                      (liveUninitSlotExt (.tuple fieldTys)) with
                  | none => rw [hSet] at hEv; cases hEv
                  | some _ =>
                    rw [hSet] at hEv
                    injection hEv with hPair
                    injection hPair with hTyEq _
                    subst hTyEq; rfl
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                cases hEv
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> cases hEv
        | nil =>
          cases pe with
          | deref => cases hEv
          | unsupported => cases hEv
          | field idx fieldTy =>
            dsimp at hEv
            cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
            | none => rw [hTy] at hEv; cases hEv
            | some declTy =>
              rw [hTy] at hEv; dsimp
              cases declTy with
              | tuple fieldTys =>
                dsimp
                cases hSl : Trusted.MirSemantics.getElem? locals lid with
                | none => rw [hSl] at hEv; cases hEv
                | some sl =>
                  rw [hSl] at hEv; dsimp at hEv
                  cases hNf : (!isFlatTupleTy (.tuple fieldTys)) with
                  | true => rw [hNf] at hEv; cases hEv
                  | false =>
                    rw [hNf] at hEv; dsimp at hEv
                    rw [bool_not_false hNf]; dsimp
                    cases hFty : Trusted.MirSemantics.getElem? fieldTys idx with
                    | none => rw [hFty] at hEv; cases hEv
                    | some declFieldTy =>
                      rw [hFty] at hEv; dsimp at hEv
                      dsimp
                      cases hNt : (!MirTy.beq fieldTy declFieldTy) with
                      | true => rw [hNt] at hEv; cases hEv
                      | false =>
                        rw [hNt] at hEv; dsimp at hEv
                        rw [bool_not_false hNt]; dsimp
                        cases sl with
                        | dead | liveBase _ => cases hEv
                        | liveTuple fields =>
                          dsimp at hEv
                          cases hFv : Trusted.MirSemantics.getElem? fields idx with
                          | none => rw [hFv] at hEv; cases hEv
                          | some _ =>
                            rw [hFv] at hEv; dsimp at hEv
                            cases hSf : setElem? fields idx
                                (liveUninitFieldVal declFieldTy) with
                            | none => rw [hSf] at hEv; cases hEv
                            | some fields' =>
                              rw [hSf] at hEv; dsimp at hEv
                              cases hSl' : setElem? locals lid
                                  (.liveTuple fields') with
                              | none => rw [hSl'] at hEv; cases hEv
                              | some _ =>
                                rw [hSl'] at hEv
                                injection hEv with hPair
                                injection hPair with hTyEq _
                                subst hTyEq; rfl
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                cases hEv

private theorem evalPrimitiveOperandExt_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlotExt} {opnd : Operand} {v : Val}
    (hAllSup : bodyLocals.all isSupportedTupleOrScalarTy = true)
    (hWt : LocalsWellTyped bodyLocals locals)
    (hEv : evalPrimitiveOperandExt bodyLocals locals opnd = .ok (v, locals')) :
    LocalsWellTyped bodyLocals locals' ∧
    (∀ ty, optMirTyEq (operandStaticTy? bodyLocals opnd) ty = true →
      checkVal v ty = true) := by
  unfold evalPrimitiveOperandExt at hEv
  cases hSlot : evalOperandToSlotExt bodyLocals locals opnd with
  | error _ => rw [hSlot] at hEv; cases hEv
  | ok triple =>
    rw [hSlot] at hEv
    cases triple with
    | mk srcTy rest =>
      cases rest with
      | mk optVal ls =>
        dsimp at hEv
        cases hPr : (!isPrimitiveReadableTy srcTy) with
        | true => rw [hPr] at hEv; cases hEv
        | false =>
          rw [hPr] at hEv; dsimp at hEv
          have hPrim := bool_not_false hPr
          cases optVal with
          | none => cases hEv
          | some v' =>
            injection hEv with hPair
            injection hPair with h1 h2
            subst h1; subst h2
            let ⟨hWt', hCheck⟩ := evalOperandToSlotExt_preserves_wt hAllSup hWt hSlot
            refine ⟨hWt', ?_⟩
            intro ty hOpt
            have hSt := evalOperandToSlotExt_staticTy hSlot
            rw [hSt] at hOpt
            dsimp [optMirTyEq] at hOpt
            have hEqTy := mirTy_beq_eq hOpt
            subst hEqTy
            have hCext := hCheck v' rfl
            cases srcTy with
            | bool | int _ _ => exact hCext
            | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
              cases hPrim

private theorem evalRvalueExt_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlotExt} {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hAllSup : bodyLocals.all isSupportedTupleOrScalarTy = true)
    (hWt : LocalsWellTyped bodyLocals locals)
    (hEv : evalRvalueExt bodyLocals locals dstTy rv = .ok (v, locals')) :
    LocalsWellTyped bodyLocals locals' := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalueExt] at hEv
    cases hOp : evalOperandToSlotExt bodyLocals locals opnd with
    | error _ => rw [hOp] at hEv; cases hEv
    | ok triple =>
      rw [hOp] at hEv
      cases triple with
      | mk srcTy rest =>
        cases rest with
        | mk optVal ls =>
          dsimp at hEv
          cases hNe : (!MirTy.beq srcTy dstTy) with
          | true => rw [hNe] at hEv; cases hEv
          | false =>
            rw [hNe] at hEv; dsimp at hEv
            cases optVal with
            | none => cases hEv
            | some _ =>
              injection hEv with hPair
              injection hPair with _ h2; subst h2
              exact (evalOperandToSlotExt_preserves_wt hAllSup hWt hOp).1
  | binaryOp op lhs rhs =>
    dsimp [evalRvalueExt] at hEv
    cases hL : evalPrimitiveOperandExt bodyLocals locals lhs with
    | error _ => rw [hL] at hEv; cases hEv
    | ok p1 =>
      rw [hL] at hEv
      cases p1 with
      | mk lVal ls1 =>
        dsimp at hEv
        cases hR : evalPrimitiveOperandExt bodyLocals ls1 rhs with
        | error _ => rw [hR] at hEv; cases hEv
        | ok p2 =>
          rw [hR] at hEv
          cases p2 with
          | mk rVal ls2 =>
            dsimp at hEv
            have hWt1 := (evalPrimitiveOperandExt_preserves_wt hAllSup hWt hL).1
            have hWt2 := (evalPrimitiveOperandExt_preserves_wt hAllSup hWt1 hR).1
            cases hOvf : isWithOverflowBinOp op with
            | true =>
              rw [hOvf] at hEv; dsimp at hEv
              cases hW : evalWithOverflowOp op lVal rVal with
              | error _ => rw [hW] at hEv; cases hEv
              | ok res =>
                rw [hW] at hEv
                cases res with
                | mk _ _ =>
                  dsimp at hEv
                  injection hEv with hPair
                  injection hPair with _ h2; subst h2
                  exact hWt2
            | false =>
              rw [hOvf] at hEv; dsimp at hEv
              cases hB : evalBinOp op lVal rVal with
              | error _ => rw [hB] at hEv; cases hEv
              | ok _ =>
                rw [hB] at hEv
                injection hEv with hPair
                injection hPair with _ h2; subst h2
                exact hWt2
  | unaryOp op opnd =>
    dsimp [evalRvalueExt] at hEv
    cases hO : evalPrimitiveOperandExt bodyLocals locals opnd with
    | error _ => rw [hO] at hEv; cases hEv
    | ok p1 =>
      rw [hO] at hEv
      cases p1 with
      | mk v1 ls1 =>
        dsimp at hEv
        cases hU : evalUnOp op v1 with
        | error _ => rw [hU] at hEv; cases hEv
        | ok _ =>
          rw [hU] at hEv
          injection hEv with hPair
          injection hPair with _ h2; subst h2
          exact (evalPrimitiveOperandExt_preserves_wt hAllSup hWt hO).1
  | discriminant place =>
    dsimp [evalRvalueExt] at hEv
    cases hP : (!place.projection.isEmpty) with
    | true => rw [hP] at hEv; cases hEv
    | false =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some dt =>
        rw [hTy] at hEv
        cases dt with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals place.localId with
          | none => rw [hSl] at hEv; cases hEv
          | some sl =>
            rw [hSl] at hEv; dsimp at hEv
            cases hAdm : (!enumAdmitted ety) with
            | true => rw [hAdm] at hEv; cases hEv
            | false =>
              rw [hAdm] at hEv; dsimp at hEv
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEv
                cases sl with
                | dead | liveTuple _ => cases hEv
                | liveBase ov =>
                  cases ov with
                  | none =>
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEv; cases hEv
                    | some _ =>
                      rw [hD] at hEv
                      injection hEv with hPair; injection hPair with _ h2; subst h2
                      exact hWt
                  | some v' =>
                    cases v' with
                    | enumVal ety' idx =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.beq idx 0) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv
                          injection hEv with hPair; injection hPair with _ h2; subst h2
                          exact hWt
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
              | scalar _ _ =>
                rw [hTr] at hEv
                cases sl with
                | dead | liveTuple _ => cases hEv
                | liveBase ov =>
                  cases ov with
                  | none => cases hEv
                  | some v' =>
                    cases v' with
                    | enumVal ety' idx =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.blt idx ety.discriminants.length) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants idx with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv
                          injection hEv with hPair; injection hPair with _ h2; subst h2
                          exact hWt
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
          cases hEv
  | aggregateTuple _ | ref _ _ | addressOf _ _ | unsupported => cases hEv

private theorem writePlaceExt_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlotExt} {dstId : LocalId} {dstTy : MirTy}
    {val : Val}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (hW : writePlaceExt locals dstId dstTy val = .ok locals') :
    LocalsWellTyped bodyLocals locals' := by
  unfold writePlaceExt at hW
  cases hC : (!checkValExt val dstTy) with
  | true => rw [hC] at hW; cases hW
  | false =>
    rw [hC] at hW; dsimp at hW
    have hCheck := bool_not_false hC
    cases dstTy with
    | tuple fieldTys =>
      cases val with
      | tuple vs =>
        dsimp at hW
        cases hSl : Trusted.MirSemantics.getElem? locals dstId with
        | none => rw [hSl] at hW; cases hW
        | some sl =>
          rw [hSl] at hW
          cases sl with
          | dead | liveBase _ => cases hW
          | liveTuple _ =>
            cases hSet : setElem? locals dstId (.liveTuple (vs.map some)) with
            | none => rw [hSet] at hW; cases hW
            | some ls' =>
              rw [hSet] at hW
              injection hW with hEq; subst hEq
              have hSlotWt := slotWellTyped_initArgSlotExt hCheck
              exact localsWellTyped_set hWt hTy hSet hSlotWt
      | scalar _ | ptr _ | bool _ | unit | enumVal _ _ | bytes _ =>
        unfold checkValExt at hCheck
        dsimp at hCheck
        cases hFl : isFlatTupleTy (.tuple fieldTys) with
        | false => rw [hFl] at hCheck; cases hCheck
        | true => rw [hFl] at hCheck; cases hCheck
    | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
      dsimp at hW
      cases hSl : Trusted.MirSemantics.getElem? locals dstId with
      | none => rw [hSl] at hW; cases hW
      | some sl =>
        rw [hSl] at hW
        cases sl with
        | dead | liveTuple _ => cases hW
        | liveBase _ =>
          dsimp at hW
          cases hSet : setElem? locals dstId (.liveBase (some val)) with
          | none => rw [hSet] at hW; cases hW
          | some ls' =>
            rw [hSet] at hW
            injection hW with hEq; subst hEq
            exact localsWellTyped_set hWt hTy hSet hCheck

private theorem writeTupleFieldExt_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlotExt} {dstId : LocalId} {fieldTys : List MirTy}
    {idx : FieldIdx} {fieldTy : MirTy} {val : Val}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals dstId = some (.tuple fieldTys))
    (hFlat : isFlatTupleTy (.tuple fieldTys) = true)
    (hFty : Trusted.MirSemantics.getElem? fieldTys idx = some fieldTy)
    (hW : writeTupleFieldExt locals dstId idx fieldTy val = .ok locals') :
    LocalsWellTyped bodyLocals locals' := by
  unfold writeTupleFieldExt at hW
  cases hC : (!checkVal val fieldTy) with
  | true => rw [hC] at hW; cases hW
  | false =>
    rw [hC] at hW; dsimp at hW
    have hCheck := bool_not_false hC
    cases hSl : Trusted.MirSemantics.getElem? locals dstId with
    | none => rw [hSl] at hW; cases hW
    | some sl =>
      rw [hSl] at hW
      cases sl with
      | dead | liveBase _ => cases hW
      | liveTuple fields =>
        dsimp at hW
        cases hSf : setElem? fields idx (some val) with
        | none => rw [hSf] at hW; cases hW
        | some fields' =>
          rw [hSf] at hW; dsimp at hW
          cases hSl' : setElem? locals dstId (.liveTuple fields') with
          | none => rw [hSl'] at hW; cases hW
          | some ls' =>
            rw [hSl'] at hW
            injection hW with hEq; subst hEq
            have hSlWt := hWt.2 dstId (.tuple fieldTys) (.liveTuple fields) hTy hSl
            unfold SlotWellTyped at hSlWt
            dsimp at hSlWt
            rw [hFlat] at hSlWt
            have hNewWt : SlotWellTyped (.tuple fieldTys) (.liveTuple fields') := by
              unfold SlotWellTyped
              dsimp
              rw [hFlat]
              refine ⟨by rw [setElem?_length hSf, hSlWt.1], ?_⟩
              intro j ft vj hFt hFj
              cases hJEq : Nat.beq j idx with
              | true =>
                have hj := nat_beq_eq hJEq
                subst hj
                rw [hFty] at hFt
                injection hFt with hEqFt; subst hEqFt
                rw [setElem?_getElem?_same hSf] at hFj
                injection hFj with hEqS
                injection hEqS with hEqV; subst hEqV
                exact hCheck
              | false =>
                have hNe := nat_ne_of_beq_false hJEq
                rw [setElem?_getElem?_ne hSf hNe] at hFj
                exact hSlWt.2 j ft vj hFt hFj
            exact localsWellTyped_set hWt hTy hSl' hNewWt

private theorem evalAggregateInPlaceExt_preserves_wt {bodyLocals : List MirTy}
    {dstId : LocalId} {fullTys : List MirTy}
    (hAllSup : bodyLocals.all isSupportedTupleOrScalarTy = true)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals dstId = some (.tuple fullTys))
    (hFlat : isFlatTupleTy (.tuple fullTys) = true)
    (idx : Nat) (ops : List Operand) (remTys : List MirTy)
    (hRem : ∀ k ft, Trusted.MirSemantics.getElem? remTys k = some ft →
      Trusted.MirSemantics.getElem? fullTys (idx + k) = some ft)
    (locals locals' : List LocalSlotExt)
    (hWt : LocalsWellTyped bodyLocals locals)
    (hEv : evalAggregateInPlaceExt bodyLocals locals dstId idx ops remTys = .ok locals') :
    LocalsWellTyped bodyLocals locals' := by
  induction ops generalizing idx remTys locals with
  | nil =>
    cases remTys with
    | nil =>
      injection hEv with hEq; subst hEq; exact hWt
    | cons _ _ => cases hEv
  | cons opnd restOps ih =>
    cases remTys with
    | nil => cases hEv
    | cons ft restTys =>
      dsimp [evalAggregateInPlaceExt] at hEv
      cases hOp : evalOperandToSlotExt bodyLocals locals opnd with
      | error _ => rw [hOp] at hEv; cases hEv
      | ok triple =>
        rw [hOp] at hEv
        cases triple with
        | mk srcTy rest =>
          cases rest with
          | mk ov ls1 =>
            dsimp at hEv
            cases hNe : (!MirTy.beq srcTy ft) with
            | true => rw [hNe] at hEv; cases hEv
            | false =>
              rw [hNe] at hEv; dsimp at hEv
              cases ov with
              | none => cases hEv
              | some v =>
                dsimp at hEv
                cases hW : writeTupleFieldExt ls1 dstId idx ft v with
                | error _ => rw [hW] at hEv; cases hEv
                | ok ls2 =>
                  rw [hW] at hEv
                  have hWt1 := (evalOperandToSlotExt_preserves_wt hAllSup hWt hOp).1
                  have hFtAt : Trusted.MirSemantics.getElem? fullTys idx = some ft := by
                    have h0 := hRem 0 ft rfl
                    rw [Nat.add_zero] at h0
                    exact h0
                  have hWt2 := writeTupleFieldExt_preserves_wt hWt1 hTy hFlat hFtAt hW
                  exact ih (idx + 1) restTys (fun k ft' hK => by
                    have hStep := hRem (k + 1) ft' hK
                    have hAdd : idx + 1 + k = idx + (k + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 k]
                    rw [hAdd]
                    exact hStep) ls2 hWt2 hEv

private theorem evalNonAggAssign_preserves_wt {body : Body} {frame : FrameStateExt}
    {mem : CallerMemory} {dstId : LocalId} {dstTy : MirTy} {rv : Rvalue}
    {s' : StateExt} {p : Program} {guard : Bool}
    (hBody : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hAllSup : body.locals.all isSupportedTupleOrScalarTy = true)
    (hLocWt : LocalsWellTyped body.locals frame.locals)
    (hTy : Trusted.MirSemantics.getElem? body.locals dstId = some dstTy)
    (hStep :
      ((if guard then
          StepResult.fault FaultKind.unsupported
        else
          match evalRvalueExt body.locals frame.locals dstTy rv with
          | .error k => .fault k
          | .ok (val, localsAfterRval) =>
            match writePlaceExt localsAfterRval dstId dstTy val with
            | .error k => .fault k
            | .ok localsAfterWrite =>
              .step {
                frames := [{
                  frame with
                  stmtIdx := frame.stmtIdx + 1
                  locals := localsAfterWrite
                }]
                callerMem := mem
              }) : StepResult StateExt TerminalOutExt) = .step s') :
    StateWellTyped p s' := by
  cases guard with
  | true => cases hStep
  | false =>
    dsimp at hStep
    cases hRv : evalRvalueExt body.locals frame.locals dstTy rv with
    | error _ => rw [hRv] at hStep; cases hStep
    | ok pair =>
      rw [hRv] at hStep
      cases pair with
      | mk val ls1 =>
        dsimp at hStep
        cases hW : writePlaceExt ls1 dstId dstTy val with
        | error _ => rw [hW] at hStep; cases hStep
        | ok ls2 =>
          rw [hW] at hStep
          injection hStep with hEq; subst hEq
          have hWt1 := evalRvalueExt_preserves_wt hAllSup hLocWt hRv
          exact ⟨_, body, rfl, hBody, hAllSup,
            writePlaceExt_preserves_wt hWt1 hTy hW⟩

private theorem evalStepTupleAssert_preserves_stateWellTyped {p : Program}
    {c : Choice} {s s' : StateExt}
    (hWt : StateWellTyped p s)
    (hStep : evalStepTupleAssert p c s = .step s') :
    StateWellTyped p s' := by
  let ⟨frame, body, hF, hBody, hAllSup, hLocWt⟩ := hWt
  unfold evalStepTupleAssert at hStep
  rw [hF] at hStep
  dsimp at hStep
  rw [hBody] at hStep
  dsimp at hStep
  cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
  | none => rw [hBb] at hStep; cases hStep
  | some bb =>
    rw [hBb] at hStep; dsimp at hStep
    cases hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
    | some stmt =>
      rw [hSt] at hStep
      dsimp at hStep
      cases stmt with
      | nop =>
        dsimp [evalStatementExt] at hStep
        injection hStep with hEq; subst hEq
        exact ⟨_, body, rfl, hBody, hAllSup, hLocWt⟩
      | unsupported => dsimp [evalStatementExt] at hStep; cases hStep
      | storageLive id =>
        dsimp [evalStatementExt] at hStep
        cases hTy : Trusted.MirSemantics.getElem? body.locals id with
        | none => rw [hTy] at hStep; cases hStep
        | some ty =>
          rw [hTy] at hStep; dsimp at hStep
          cases hSet : setElem? frame.locals id (liveUninitSlotExt ty) with
          | none => rw [hSet] at hStep; cases hStep
          | some ls' =>
            rw [hSet] at hStep
            injection hStep with hEq; subst hEq
            have hTySup := list_all_getElem? hAllSup hTy
            exact ⟨_, body, rfl, hBody, hAllSup,
              localsWellTyped_set hLocWt hTy hSet (slotWellTyped_liveUninitSlotExt hTySup)⟩
      | storageDead id =>
        dsimp [evalStatementExt] at hStep
        cases hZ : Nat.beq id 0 with
        | true => rw [hZ] at hStep; cases hStep
        | false =>
          rw [hZ] at hStep; dsimp at hStep
          cases hSet : setElem? frame.locals id .dead with
          | none => rw [hSet] at hStep; cases hStep
          | some ls' =>
            rw [hSet] at hStep
            injection hStep with hEq; subst hEq
            have hLt : id < body.locals.length := by
              rw [← hLocWt.1]; exact setElem?_some_lt hSet
            let ⟨ty, hTy⟩ := getElem?_some_of_lt body.locals id hLt
            have hTySup := list_all_getElem? hAllSup hTy
            exact ⟨_, body, rfl, hBody, hAllSup,
              localsWellTyped_set hLocWt hTy hSet (slotWellTyped_dead hTySup)⟩
      | assign dst rv =>
        cases dst with
        | mk dstId dstProj =>
          dsimp [evalStatementExt] at hStep
          cases dstProj with
          | nil =>
            dsimp at hStep
            cases hTy : Trusted.MirSemantics.getElem? body.locals dstId with
            | none => rw [hTy] at hStep; cases hStep
            | some dstTy =>
              rw [hTy] at hStep; dsimp at hStep
              cases rv with
              | aggregateTuple ops =>
                cases dstTy with
                | tuple fieldTys =>
                  dsimp at hStep
                  cases hBad : (!isFlatTupleTy (.tuple fieldTys) ||
                      !Nat.beq ops.length fieldTys.length ||
                      ops.any (operandMentionsLocal dstId)) with
                  | true => rw [hBad] at hStep; cases hStep
                  | false =>
                    rw [hBad] at hStep; dsimp at hStep
                    let ⟨hBad12, _⟩ := bool_or_false hBad
                    let ⟨hNf, _⟩ := bool_or_false hBad12
                    have hFlat := bool_not_false hNf
                    cases hAgg : evalAggregateInPlaceExt body.locals frame.locals
                        dstId 0 ops fieldTys with
                    | error _ => rw [hAgg] at hStep; cases hStep
                    | ok ls' =>
                      rw [hAgg] at hStep
                      injection hStep with hEq; subst hEq
                      exact ⟨_, body, rfl, hBody, hAllSup,
                        evalAggregateInPlaceExt_preserves_wt hAllSup hTy hFlat 0 ops fieldTys
                          (fun k ft hK => by rw [Nat.zero_add]; exact hK)
                          frame.locals ls' hLocWt hAgg⟩
                | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                  cases hStep
              | use o =>
                dsimp at hStep
                exact evalNonAggAssign_preserves_wt (rv := .use o) (mem := s.callerMem) hBody hAllSup hLocWt hTy hStep
              | binaryOp op l r =>
                dsimp at hStep
                exact evalNonAggAssign_preserves_wt (rv := .binaryOp op l r) (mem := s.callerMem) hBody hAllSup hLocWt hTy hStep
              | unaryOp op o =>
                dsimp at hStep
                exact evalNonAggAssign_preserves_wt (rv := .unaryOp op o) (mem := s.callerMem) hBody hAllSup hLocWt hTy hStep
              | discriminant p' =>
                dsimp at hStep
                exact evalNonAggAssign_preserves_wt (rv := .discriminant p') (mem := s.callerMem) hBody hAllSup hLocWt hTy hStep
              | ref m p' =>
                dsimp at hStep
                exact evalNonAggAssign_preserves_wt (rv := .ref m p') (mem := s.callerMem) hBody hAllSup hLocWt hTy hStep
              | addressOf m p' =>
                dsimp at hStep
                exact evalNonAggAssign_preserves_wt (rv := .addressOf m p') (mem := s.callerMem) hBody hAllSup hLocWt hTy hStep
              | unsupported =>
                dsimp at hStep
                exact evalNonAggAssign_preserves_wt (rv := .unsupported) (mem := s.callerMem) hBody hAllSup hLocWt hTy hStep
          | cons pe rest =>
            cases rest with
            | cons _ _ => cases pe <;> cases hStep
            | nil =>
              cases pe with
              | deref | unsupported => cases hStep
              | field idx fieldTy =>
                dsimp at hStep
                cases hTy : Trusted.MirSemantics.getElem? body.locals dstId with
                | none => rw [hTy] at hStep; cases hStep
                | some dstTy =>
                  rw [hTy] at hStep
                  cases dstTy with
                  | tuple fieldTys =>
                    dsimp at hStep
                    cases hNf : (!isFlatTupleTy (.tuple fieldTys)) with
                    | true => rw [hNf] at hStep; cases hStep
                    | false =>
                      rw [hNf] at hStep; dsimp at hStep
                      have hFlat := bool_not_false hNf
                      cases hFt : Trusted.MirSemantics.getElem? fieldTys idx with
                      | none => rw [hFt] at hStep; cases hStep
                      | some declFt =>
                        rw [hFt] at hStep; dsimp at hStep
                        cases hNt : (!MirTy.beq fieldTy declFt) with
                        | true => rw [hNt] at hStep; cases hStep
                        | false =>
                          rw [hNt] at hStep; dsimp at hStep
                          cases hRv : evalRvalueExt body.locals frame.locals declFt rv with
                          | error _ => rw [hRv] at hStep; cases hStep
                          | ok pair =>
                            rw [hRv] at hStep
                            cases pair with
                            | mk val ls1 =>
                              dsimp at hStep
                              cases hW : writeTupleFieldExt ls1 dstId idx declFt val with
                              | error _ => rw [hW] at hStep; cases hStep
                              | ok ls2 =>
                                rw [hW] at hStep
                                injection hStep with hEq; subst hEq
                                have hWt1 := evalRvalueExt_preserves_wt hAllSup hLocWt hRv
                                exact ⟨_, body, rfl, hBody, hAllSup,
                                  writeTupleFieldExt_preserves_wt hWt1 hTy hFlat hFt hW⟩
                  | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                    cases hStep
    | none =>
      rw [hSt] at hStep; dsimp at hStep
      cases hLen : Nat.beq frame.stmtIdx bb.statements.length with
      | false => rw [hLen] at hStep; cases hStep
      | true =>
        rw [hLen] at hStep; dsimp [evalTerminatorExt] at hStep
        cases hT : bb.terminator with
        | goto target =>
          rw [hT] at hStep; dsimp [jumpToBlockExt] at hStep
          injection hStep with hEq; subst hEq
          exact ⟨_, body, rfl, hBody, hAllSup, hLocWt⟩
        | unreachable | unwindResume | call _ _ _ _ _ | unsupported =>
          rw [hT] at hStep; cases hStep
        | return_ =>
          rw [hT] at hStep; dsimp at hStep
          cases hCl : bb.cleanup with
          | true => rw [hCl] at hStep; cases hStep
          | false =>
            rw [hCl] at hStep; dsimp at hStep
            cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
            | none => rw [h0] at hStep; cases hStep
            | some sl =>
              rw [h0] at hStep
              cases sl with
              | dead => cases hStep
              | liveBase ov => cases ov <;> cases hStep
              | liveTuple fields =>
                cases hB0 : Trusted.MirSemantics.getElem? body.locals 0 with
                | none => rw [hB0] at hStep; cases hStep
                | some t0 =>
                  rw [hB0] at hStep
                  cases t0 with
                  | tuple fieldTys =>
                    dsimp at hStep
                    cases hC : (isFlatTupleTy (.tuple fieldTys) &&
                        Nat.beq fields.length fieldTys.length) with
                    | false => rw [hC] at hStep; cases hStep
                    | true =>
                      rw [hC] at hStep; dsimp at hStep
                      cases hExt : extractAllInitFields fields <;>
                        (rw [hExt] at hStep; cases hStep)
                  | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                    cases hStep
        | switchInt discr targets =>
          rw [hT] at hStep; dsimp at hStep
          cases hOp : evalPrimitiveOperandExt body.locals frame.locals discr with
          | error _ => rw [hOp] at hStep; cases hStep
          | ok pair =>
            rw [hOp] at hStep
            cases pair with
            | mk dv ls1 =>
              dsimp at hStep
              have hWt1 := (evalPrimitiveOperandExt_preserves_wt hAllSup hLocWt hOp).1
              cases dv with
              | scalar sv =>
                dsimp at hStep
                cases hBr : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                | error _ => rw [hBr] at hStep; cases hStep
                | ok target =>
                  rw [hBr] at hStep; dsimp [jumpToBlockExt] at hStep
                  injection hStep with hEq; subst hEq
                  exact ⟨_, body, rfl, hBody, hAllSup, hWt1⟩
              | bool b =>
                dsimp at hStep
                cases hBr : evalBoolSwitchBranches b targets.otherwise targets.branches with
                | error _ => rw [hBr] at hStep; cases hStep
                | ok target =>
                  rw [hBr] at hStep; dsimp [jumpToBlockExt] at hStep
                  injection hStep with hEq; subst hEq
                  exact ⟨_, body, rfl, hBody, hAllSup, hWt1⟩
              | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hStep
        | assert cond expected msg target unwind =>
          rw [hT] at hStep; dsimp at hStep
          cases hOp : evalPrimitiveOperandExt body.locals frame.locals cond with
          | error _ => rw [hOp] at hStep; cases hStep
          | ok pair =>
            rw [hOp] at hStep
            cases pair with
            | mk cv ls1 =>
              dsimp at hStep
              have hWt1 := (evalPrimitiveOperandExt_preserves_wt hAllSup hLocWt hOp).1
              cases cv with
              | bool b =>
                dsimp at hStep
                cases hBeq : (b == expected) with
                | true =>
                  rw [hBeq] at hStep; dsimp [jumpToBlockExt] at hStep
                  injection hStep with hEq; subst hEq
                  exact ⟨_, body, rfl, hBody, hAllSup, hWt1⟩
                | false =>
                  rw [hBeq] at hStep; dsimp at hStep
                  cases hK : (!isSupportedAssertKind msg) with
                  | true => rw [hK] at hStep; cases hStep
                  | false =>
                    rw [hK] at hStep; dsimp at hStep
                    cases unwind <;> cases hStep
              | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hStep

/-! ### Theorem 1: Exact Conservative Extension Over Unmodified `Trusted.MirSemantics` -/

private theorem isFlatTupleTy_false_of_supportedScalar {ty : MirTy}
    (h : isSupportedScalarOrUnitTy ty = true) : isFlatTupleTy ty = false := by
  cases ty <;> first | rfl | cases h

private theorem isSupportedTupleOrScalarTy_of_scalar {ty : MirTy}
    (h : isSupportedScalarOrUnitTy ty = true) :
    isSupportedTupleOrScalarTy ty = true := by
  unfold isSupportedTupleOrScalarTy
  rw [h]; rfl

private theorem liveUninitSlotExt_eq_embed_of_supportedScalar {ty : MirTy}
    (h : isSupportedScalarOrUnitTy ty = true) :
    liveUninitSlotExt ty = embedLocalSlot (liveUninitSlot ty) := by
  cases ty with
  | bool => rfl
  | int _ _ => rfl
  | unit => rfl
  | never => rfl
  | enum ety =>
    dsimp [liveUninitSlotExt, liveUninitSlot, liveUninitFieldVal]
    cases isZstEnumTy ety <;> rfl
  | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h

private theorem liveUninitFieldVal_embed_eq_of_supportedScalar {ty : MirTy}
    (h : isSupportedScalarOrUnitTy ty = true) :
    LocalSlotExt.liveBase (liveUninitFieldVal ty) =
      embedLocalSlot (liveUninitSlot ty) := by
  cases ty with
  | bool | int _ _ | unit | never => rfl
  | enum ety =>
    dsimp [liveUninitFieldVal, liveUninitSlot]
    cases isZstEnumTy ety <;> rfl
  | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h

private theorem checkValExt_eq_checkVal_of_supportedScalar (v : Val) {ty : MirTy}
    (h : isSupportedScalarOrUnitTy ty = true) :
    checkValExt v ty = checkVal v ty := by
  cases ty <;> first | rfl | cases h

private theorem checkArgsMatchExt_eq_of_supportedScalar (args : List Val)
    {tys : List MirTy} (h : tys.all isSupportedScalarOrUnitTy = true) :
    checkArgsMatchExt args tys = checkArgsMatch args tys := by
  induction args generalizing tys with
  | nil =>
    cases tys <;> rfl
  | cons v rest ih =>
    cases tys with
    | nil => rfl
    | cons ty restTys =>
      let ⟨hTy, hRest⟩ := bool_and_true h
      dsimp [checkArgsMatchExt, checkArgsMatch]
      rw [checkValExt_eq_checkVal_of_supportedScalar v hTy, ih hRest]

private theorem initArgSlotExt_eq_embed_of_supportedScalar {ty : MirTy} (v : Val)
    (h : isSupportedScalarOrUnitTy ty = true) :
    initArgSlotExt ty v = embedLocalSlot (.live (some v)) := by
  cases ty <;> first | rfl | cases h

private theorem initLocalsExtLoop_eq_map_embed (body : Body) (args : List Val)
    (idx : Nat) {tys : List MirTy}
    (h : tys.all isSupportedScalarOrUnitTy = true) :
    initLocalsExtLoop body args idx tys =
      (initLocalsLoop body args idx tys).map embedLocalSlot := by
  induction tys generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    let ⟨hTy, hRest⟩ := bool_and_true h
    dsimp [initLocalsExtLoop, initLocalsLoop, List.map]
    rw [ih (idx + 1) hRest]
    cases Nat.beq idx 0 with
    | true =>
      dsimp
      rw [liveUninitSlotExt_eq_embed_of_supportedScalar hTy]
    | false =>
      dsimp
      cases Nat.ble idx body.argumentCount with
      | true =>
        dsimp
        cases Trusted.MirSemantics.getElem? args (idx - 1) with
        | none => rfl
        | some v =>
          dsimp
          rw [initArgSlotExt_eq_embed_of_supportedScalar v hTy]
      | false =>
        dsimp
        cases hasStorageAnnotation body idx with
        | true => rfl
        | false =>
          dsimp
          rw [liveUninitSlotExt_eq_embed_of_supportedScalar hTy]

private theorem list_all_take_drop1 {α : Type} {p : α → Bool} {xs : List α} (n : Nat)
    (h : xs.all p = true) : ((xs.drop 1).take n).all p = true := by
  apply list_all_of_forall_getElem?
  intro i x hGet
  cases Nat.lt_or_ge i n with
  | inl hlt =>
    rw [getElem?_take_drop1 xs n i hlt] at hGet
    exact list_all_getElem? h hGet
  | inr hge =>
    have hLen : ((xs.drop 1).take n).length ≤ n := by
      cases Nat.lt_or_ge (xs.drop 1).length n with
      | inr hLe => rw [list_take_length_eq (xs.drop 1) n hLe]; exact Nat.le_refl n
      | inl hGt =>
        have hEq : (xs.drop 1).take n = xs.drop 1 := by
          have hAux : ∀ (ys : List α) (m : Nat), ys.length ≤ m → ys.take m = ys := by
            intro ys
            induction ys with
            | nil => intro m _; cases m <;> rfl
            | cons a rest ih =>
              intro m hm
              cases m with
              | zero => exact False.elim (Nat.not_succ_le_zero _ hm)
              | succ k =>
                dsimp [List.take]
                rw [ih k (Nat.le_of_succ_le_succ hm)]
          exact hAux (xs.drop 1) n (Nat.le_of_lt hGt)
        rw [hEq]
        exact Nat.le_of_lt hGt
    have hLt := getElem?_some_lt hGet
    exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hLen hge) hLt)

private theorem initStateTupleAssert_eq_of_flatAssertFree {p : Program}
    (hFlat : isFlatAssertFreeProgram p = true) (q : Query) :
    initStateTupleAssert p q =
      match initState p q with
      | .error k => .error k
      | .ok s₀ => .ok (embedState s₀) := by
  unfold initStateTupleAssert initState
  cases hHdr : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) with
  | true => rfl
  | false =>
    dsimp
    cases hMem : (!q.callerMem.allocations.isEmpty) with
    | true => rfl
    | false =>
      dsimp
      cases hBody : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
      | none => rfl
      | some body =>
        dsimp
        have hFlatBody := list_all_getElem? hFlat hBody
        unfold isFlatAssertFreeBody at hFlatBody
        let ⟨hAllScalar, _⟩ := bool_and_true hFlatBody
        have hAllSup : body.locals.all isSupportedTupleOrScalarTy = true :=
          list_all_of_forall_getElem? (fun i ty hTy =>
            isSupportedTupleOrScalarTy_of_scalar (list_all_getElem? hAllScalar hTy))
        cases body.basicBlocks.isEmpty with
        | true => rfl
        | false =>
          dsimp
          cases (!Nat.blt body.argumentCount body.locals.length) with
          | true => rfl
          | false =>
            dsimp
            cases (!storageAnnotationsInBounds body) with
            | true => rfl
            | false =>
              dsimp
              rw [hAllScalar, hAllSup]
              dsimp
              have hParamScalar :
                  ((body.locals.drop 1).take body.argumentCount).all
                    isSupportedScalarOrUnitTy = true :=
                list_all_take_drop1 body.argumentCount hAllScalar
              rw [checkArgsMatchExt_eq_of_supportedScalar q.args hParamScalar]
              cases checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount) with
              | false => rfl
              | true =>
                dsimp [embedState, embedFrame, List.map]
                rw [initLocalsExtLoop_eq_map_embed body q.args 0 hAllScalar]

private theorem evalOperandToSlotExt_embed_eq {bodyLocals : List MirTy}
    (hAllSc : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (locals : List LocalSlot) (opnd : Operand) :
    evalOperandToSlotExt bodyLocals (locals.map embedLocalSlot) opnd =
      match evalOperandToSlot bodyLocals locals opnd with
      | .error k => .error k
      | .ok (ty, ov, ls') => .ok (ty, ov, ls'.map embedLocalSlot) := by
  cases opnd with
  | constant c =>
    dsimp [evalOperandToSlotExt, evalOperandToSlot]
    cases evalConstLit c.ty c.lit <;> rfl
  | copy place =>
    cases place with
    | mk lid proj =>
      dsimp [evalOperandToSlotExt, evalOperandToSlot]
      cases proj with
      | nil =>
        dsimp
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
        | none => rfl
        | some ty =>
          have hSc := list_all_getElem? hAllSc hTy
          have hNotTuple := isFlatTupleTy_false_of_supportedScalar hSc
          rw [getElem?_map]
          cases hSl : Trusted.MirSemantics.getElem? locals lid with
          | none => rfl
          | some sl =>
            cases sl with
            | dead => rfl
            | live ov =>
              dsimp [Option.map, embedLocalSlot]
              rw [hNotTuple]; rfl
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> rfl
        | nil =>
          cases pe with
          | deref | unsupported => rfl
          | field _ _ =>
            dsimp
            cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
            | none => rfl
            | some ty =>
              have hSc := list_all_getElem? hAllSc hTy
              cases ty <;> first | rfl | cases hSc
  | move place =>
    cases place with
    | mk lid proj =>
      dsimp [evalOperandToSlotExt, evalOperandToSlot]
      cases proj with
      | nil =>
        dsimp
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
        | none => rfl
        | some ty =>
          have hSc := list_all_getElem? hAllSc hTy
          have hNotTuple := isFlatTupleTy_false_of_supportedScalar hSc
          rw [getElem?_map]
          cases hSl : Trusted.MirSemantics.getElem? locals lid with
          | none => rfl
          | some sl =>
            cases sl with
            | dead => rfl
            | live ov =>
              dsimp [Option.map, embedLocalSlot]
              rw [hNotTuple]; dsimp
              rw [liveUninitFieldVal_embed_eq_of_supportedScalar hSc]
              rw [setElem?_map_eq]
              cases setElem? locals lid (liveUninitSlot ty) <;> rfl
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> rfl
        | nil =>
          cases pe with
          | deref | unsupported => rfl
          | field _ _ =>
            dsimp
            cases hTy : Trusted.MirSemantics.getElem? bodyLocals lid with
            | none => rfl
            | some ty =>
              have hSc := list_all_getElem? hAllSc hTy
              cases ty <;> first | rfl | cases hSc

private theorem evalPrimitiveOperandExt_embed_eq {bodyLocals : List MirTy}
    (hAllSc : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (locals : List LocalSlot) (opnd : Operand) :
    evalPrimitiveOperandExt bodyLocals (locals.map embedLocalSlot) opnd =
      match evalPrimitiveOperand bodyLocals locals opnd with
      | .error k => .error k
      | .ok (v, ls') => .ok (v, ls'.map embedLocalSlot) := by
  unfold evalPrimitiveOperandExt evalPrimitiveOperand
  rw [evalOperandToSlotExt_embed_eq hAllSc locals opnd]
  cases evalOperandToSlot bodyLocals locals opnd with
  | error _ => rfl
  | ok triple =>
    cases triple with
    | mk ty rest =>
      cases rest with
      | mk ov ls' =>
        dsimp
        cases (!isPrimitiveReadableTy ty) with
        | true => rfl
        | false =>
          dsimp
          cases ov <;> rfl

private theorem truncateScalar_err_unsupported {w : IntWidth} {s : Bool} {v : Int}
    {k : FaultKind} (h : truncateScalar w s v = .error k) :
    k = .unsupported := by
  unfold truncateScalar at h
  cases s with
  | false => cases h
  | true =>
    dsimp only at h
    revert h
    cases (decide (bvToInt (bvOfInt 128 v) < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (bvToInt (bvOfInt 128 v) ≥ HPow.hPow (2 : Int) 127)) with
    | true => intro h; dsimp at h; injection h with hEq; exact hEq.symm
    | false => intro h; cases h

private theorem evalWithOverflowOp_err_unsupported {op : BinOp} {l r : Val}
    {k : FaultKind} (h : evalWithOverflowOp op l r = .error k) :
    k = .unsupported := by
  unfold evalWithOverflowOp at h
  cases l with
  | scalar lv =>
    cases r with
    | scalar rv =>
      dsimp at h
      cases hNe : (!(IntWidth.beq lv.width rv.width && (lv.signed == rv.signed))) with
      | true =>
        rw [hNe] at h; dsimp at h
        injection h with hEq; exact hEq.symm
      | false =>
        rw [hNe] at h; dsimp at h
        cases op with
        | addWithOverflow | subWithOverflow | mulWithOverflow =>
          dsimp at h
          cases hTr : truncateScalar lv.width lv.signed _ with
          | error k' =>
            rw [hTr] at h
            injection h with hEq; subst hEq
            exact truncateScalar_err_unsupported hTr
          | ok _ => rw [hTr] at h; cases h
        | add | addUnchecked | sub | subUnchecked | mul | mulUnchecked
        | div | rem | bitXor | bitAnd | bitOr | shl | shlUnchecked
        | shr | shrUnchecked | eq | lt | le | ne | ge | gt | offset =>
          dsimp at h
          injection h with hEq; exact hEq.symm
    | ptr _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ =>
      dsimp at h; injection h with hEq; exact hEq.symm
  | ptr _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ =>
    dsimp at h; injection h with hEq; exact hEq.symm

private theorem evalBinOp_withOverflow_unsupported {op : BinOp}
    (hOvf : isWithOverflowBinOp op = true) (l r : Val) :
    evalBinOp op l r = .error .unsupported := by
  cases op with
  | addWithOverflow | subWithOverflow | mulWithOverflow =>
    unfold evalBinOp
    cases l with
    | scalar lv =>
      cases r with
      | scalar rv =>
        dsimp [BinOp.isShift]
        cases (!(IntWidth.beq lv.width rv.width && (lv.signed == rv.signed))) <;> rfl
      | ptr _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
    | bool _ =>
      cases r <;> rfl
    | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
  | add | addUnchecked | sub | subUnchecked | mul | mulUnchecked
  | div | rem | bitXor | bitAnd | bitOr | shl | shlUnchecked
  | shr | shrUnchecked | eq | lt | le | ne | ge | gt | offset =>
    cases hOvf

private theorem writePlaceExt_embed_eq (locals : List LocalSlot) (dstId : LocalId)
    {dstTy : MirTy} (hSc : isSupportedScalarOrUnitTy dstTy = true) (val : Val) :
    writePlaceExt (locals.map embedLocalSlot) dstId dstTy val =
      match writePlace locals dstId dstTy val with
      | .error k => .error k
      | .ok ls' => .ok (ls'.map embedLocalSlot) := by
  unfold writePlaceExt writePlace
  rw [checkValExt_eq_checkVal_of_supportedScalar val hSc]
  cases (!checkVal val dstTy) with
  | true => rfl
  | false =>
    dsimp
    have hBody :
        ((match Trusted.MirSemantics.getElem? (locals.map embedLocalSlot) dstId with
          | none => .error .unsupported
          | some .dead => .error .undefined
          | some (.liveBase _) =>
            match setElem? (locals.map embedLocalSlot) dstId (.liveBase (some val)) with
            | some locals' => .ok locals'
            | none => .error .unsupported
          | some (.liveTuple _) => .error .unsupported) : Except FaultKind (List LocalSlotExt)) =
        (match
          ((match Trusted.MirSemantics.getElem? locals dstId with
            | none => .error .unsupported
            | some .dead => .error .undefined
            | some (.live _) =>
              match setElem? locals dstId (.live (some val)) with
              | some locals' => .ok locals'
              | none => .error .unsupported) : Except FaultKind (List LocalSlot)) with
         | .error k => .error k
         | .ok ls' => .ok (ls'.map embedLocalSlot)) := by
      rw [getElem?_map]
      cases Trusted.MirSemantics.getElem? locals dstId with
      | none => rfl
      | some sl =>
        cases sl with
        | dead => rfl
        | live _ =>
          dsimp [Option.map, embedLocalSlot]
          have hS := setElem?_map_eq embedLocalSlot locals dstId (.live (some val))
          dsimp [embedLocalSlot] at hS
          rw [hS]
          cases setElem? locals dstId (.live (some val)) <;> rfl
    cases dstTy with
    | tuple _ => cases hSc
    | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
      dsimp
      exact hBody

private theorem evalAssignRvalueExt_embed_eq {body : Body}
    (hAllSc : body.locals.all isSupportedScalarOrUnitTy = true)
    (frame : FrameState) (mem : CallerMemory) (dstId : LocalId)
    {dstTy : MirTy} (hSc : isSupportedScalarOrUnitTy dstTy = true) (rv : Rvalue) :
    (match evalRvalueExt body.locals (frame.locals.map embedLocalSlot) dstTy rv with
     | .error k => .fault k
     | .ok (val, localsAfterRval) =>
       match writePlaceExt localsAfterRval dstId dstTy val with
       | .error k => .fault k
       | .ok localsAfterWrite =>
         .step {
           frames := [{
             embedFrame frame with
             stmtIdx := frame.stmtIdx + 1
             locals := localsAfterWrite
           }]
           callerMem := mem
         }) =
    liftStepResult
      (match evalRvalue body.locals frame.locals dstTy rv with
       | .error k => .fault k
       | .ok (val, localsAfterRval) =>
         match writePlace localsAfterRval dstId dstTy val with
         | .error k => .fault k
         | .ok localsAfterWrite =>
           .step {
             frames := [{
               frame with
               stmtIdx := frame.stmtIdx + 1
               locals := localsAfterWrite
             }]
             callerMem := mem
           }) := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalueExt, evalRvalue]
    rw [evalOperandToSlotExt_embed_eq hAllSc frame.locals opnd]
    cases evalOperandToSlot body.locals frame.locals opnd with
    | error _ => rfl
    | ok triple =>
      cases triple with
      | mk srcTy rest =>
        cases rest with
        | mk ov ls1 =>
          dsimp
          cases (!MirTy.beq srcTy dstTy) with
          | true => rfl
          | false =>
            dsimp
            cases ov with
            | none => rfl
            | some v =>
              dsimp
              rw [writePlaceExt_embed_eq ls1 dstId hSc v]
              cases writePlace ls1 dstId dstTy v <;> rfl
  | binaryOp op lhs rhs =>
    dsimp [evalRvalueExt, evalRvalue]
    rw [evalPrimitiveOperandExt_embed_eq hAllSc frame.locals lhs]
    cases evalPrimitiveOperand body.locals frame.locals lhs with
    | error _ => rfl
    | ok p1 =>
      cases p1 with
      | mk lVal ls1 =>
        dsimp
        rw [evalPrimitiveOperandExt_embed_eq hAllSc ls1 rhs]
        cases evalPrimitiveOperand body.locals ls1 rhs with
        | error _ => rfl
        | ok p2 =>
          cases p2 with
          | mk rVal ls2 =>
            dsimp
            cases hOvf : isWithOverflowBinOp op with
            | false =>
              dsimp
              cases evalBinOp op lVal rVal with
              | error _ => rfl
              | ok res =>
                dsimp
                rw [writePlaceExt_embed_eq ls2 dstId hSc res]
                cases writePlace ls2 dstId dstTy res <;> rfl
            | true =>
              dsimp
              rw [evalBinOp_withOverflow_unsupported hOvf lVal rVal]
              dsimp
              cases hW : evalWithOverflowOp op lVal rVal with
              | error k =>
                rw [evalWithOverflowOp_err_unsupported hW]; rfl
              | ok pair =>
                cases pair with
                | mk resScalar ovf =>
                  dsimp
                  rw [writePlaceExt_embed_eq ls2 dstId hSc
                    (.tuple [.scalar resScalar, .bool ovf])]
                  unfold writePlace checkVal Val.ty?
                  rfl
  | unaryOp op opnd =>
    dsimp [evalRvalueExt, evalRvalue]
    rw [evalPrimitiveOperandExt_embed_eq hAllSc frame.locals opnd]
    cases evalPrimitiveOperand body.locals frame.locals opnd with
    | error _ => rfl
    | ok p1 =>
      cases p1 with
      | mk v1 ls1 =>
        dsimp
        cases evalUnOp op v1 with
        | error _ => rfl
        | ok res =>
          dsimp
          rw [writePlaceExt_embed_eq ls1 dstId hSc res]
          cases writePlace ls1 dstId dstTy res <;> rfl
  | discriminant place =>
    dsimp [evalRvalueExt, evalRvalue]
    cases (!place.projection.isEmpty) with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? body.locals place.localId with
      | none => rfl
      | some dt =>
        cases dt with
        | enum ety =>
          rw [getElem?_map]
          cases Trusted.MirSemantics.getElem? frame.locals place.localId with
          | none => rfl
          | some sl =>
            dsimp [Option.map]
            cases (!enumAdmitted ety) with
            | true => rfl
            | false =>
              dsimp
              cases sl with
              | dead => cases ety.tagRepr <;> rfl
              | live ov =>
                dsimp [embedLocalSlot]
                cases ety.tagRepr with
                | zeroSized =>
                  cases ov with
                  | none =>
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rfl
                    | some disc =>
                      dsimp
                      rw [writePlaceExt_embed_eq frame.locals dstId hSc _]
                      cases writePlace frame.locals dstId dstTy _ <;> rfl
                  | some v' =>
                    cases v' with
                    | enumVal ety' idx =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.beq idx 0) with
                      | false => rfl
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rfl
                        | some disc =>
                          dsimp
                          rw [writePlaceExt_embed_eq frame.locals dstId hSc _]
                          cases writePlace frame.locals dstId dstTy _ <;> rfl
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => rfl
                | scalar _ _ =>
                  cases ov with
                  | none => rfl
                  | some v' =>
                    cases v' with
                    | enumVal ety' idx =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.blt idx ety.discriminants.length) with
                      | false => rfl
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants idx with
                        | none => rfl
                        | some disc =>
                          dsimp
                          rw [writePlaceExt_embed_eq frame.locals dstId hSc _]
                          cases writePlace frame.locals dstId dstTy _ <;> rfl
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => rfl
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => rfl
  | aggregateTuple _ | ref _ _ | addressOf _ _ | unsupported => rfl

private theorem evalStatementExt_embed_eq {body : Body}
    (hAllSc : body.locals.all isSupportedScalarOrUnitTy = true)
    (frame : FrameState) (mem : CallerMemory) (stmt : StatementKind) :
    evalStatementExt body (embedFrame frame) mem stmt =
      liftStepResult (evalStatement body frame mem stmt) := by
  cases stmt with
  | nop => rfl
  | unsupported => rfl
  | storageLive id =>
    dsimp [evalStatementExt, evalStatement, embedFrame]
    cases hTy : Trusted.MirSemantics.getElem? body.locals id with
    | none => rfl
    | some ty =>
      dsimp
      have hSc := list_all_getElem? hAllSc hTy
      rw [liveUninitSlotExt_eq_embed_of_supportedScalar hSc]
      rw [setElem?_map_eq]
      cases setElem? frame.locals id (liveUninitSlot ty) <;> rfl
  | storageDead id =>
    dsimp [evalStatementExt, evalStatement, embedFrame]
    cases Nat.beq id 0 with
    | true => rfl
    | false =>
      dsimp
      have hS := setElem?_map_eq embedLocalSlot frame.locals id .dead
      dsimp [embedLocalSlot] at hS
      rw [hS]
      cases setElem? frame.locals id .dead <;> rfl
  | assign dst rv =>
    cases dst with
    | mk dstId dstProj =>
      dsimp [evalStatementExt, evalStatement]
      cases dstProj with
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> rfl
        | nil =>
          cases pe with
          | deref | unsupported => rfl
          | field _ _ =>
            dsimp
            cases hTy : Trusted.MirSemantics.getElem? body.locals dstId with
            | none => rfl
            | some ty =>
              have hSc := list_all_getElem? hAllSc hTy
              cases ty <;> first | rfl | cases hSc
      | nil =>
        dsimp
        cases hTy : Trusted.MirSemantics.getElem? body.locals dstId with
        | none => rfl
        | some dstTy =>
          dsimp
          have hSc := list_all_getElem? hAllSc hTy
          cases rv with
          | aggregateTuple ops =>
            cases dstTy <;> first | rfl | cases hSc
          | use o =>
            cases dstTy with
            | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hSc
            | bool | int _ _ | unit | never | enum _ =>
              dsimp [embedFrame]; exact evalAssignRvalueExt_embed_eq hAllSc frame mem dstId hSc (.use o)
          | binaryOp op l r =>
            cases dstTy with
            | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hSc
            | bool | int _ _ | unit | never | enum _ =>
              dsimp [embedFrame]; exact evalAssignRvalueExt_embed_eq hAllSc frame mem dstId hSc (.binaryOp op l r)
          | unaryOp op o =>
            cases dstTy with
            | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hSc
            | bool | int _ _ | unit | never | enum _ =>
              dsimp [embedFrame]; exact evalAssignRvalueExt_embed_eq hAllSc frame mem dstId hSc (.unaryOp op o)
          | discriminant p' =>
            cases dstTy with
            | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hSc
            | bool | int _ _ | unit | never | enum _ =>
              dsimp [embedFrame]; exact evalAssignRvalueExt_embed_eq hAllSc frame mem dstId hSc (.discriminant p')
          | ref m p' =>
            cases dstTy with
            | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hSc
            | bool | int _ _ | unit | never | enum _ =>
              dsimp [embedFrame]; exact evalAssignRvalueExt_embed_eq hAllSc frame mem dstId hSc (.ref m p')
          | addressOf m p' =>
            cases dstTy with
            | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hSc
            | bool | int _ _ | unit | never | enum _ =>
              dsimp [embedFrame]; exact evalAssignRvalueExt_embed_eq hAllSc frame mem dstId hSc (.addressOf m p')
          | unsupported =>
            cases dstTy with
            | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hSc
            | bool | int _ _ | unit | never | enum _ =>
              dsimp [embedFrame]; exact evalAssignRvalueExt_embed_eq hAllSc frame mem dstId hSc .unsupported

private theorem evalTerminatorExt_embed_eq {body : Body} {bb : BasicBlock}
    (hAllSc : body.locals.all isSupportedScalarOrUnitTy = true)
    (hNoAssert : isAssertTerminator bb.terminator = false)
    (frame : FrameState) (mem : CallerMemory) :
    evalTerminatorExt body bb (embedFrame frame) mem =
      liftStepResult (evalTerminator body bb frame mem) := by
  unfold evalTerminatorExt evalTerminator
  cases hT : bb.terminator with
  | goto _ => rfl
  | unreachable => rfl
  | unwindResume => rfl
  | call _ _ _ _ _ => rfl
  | unsupported => rfl
  | assert _ _ _ _ _ =>
    rw [hT] at hNoAssert
    cases hNoAssert
  | return_ =>
    dsimp [embedFrame]
    cases bb.cleanup with
    | true => rfl
    | false =>
      dsimp
      rw [getElem?_map]
      cases Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rfl
      | some sl =>
        cases sl with
        | dead => rfl
        | live ov => cases ov <;> rfl
  | switchInt discr targets =>
    dsimp [embedFrame]
    rw [evalPrimitiveOperandExt_embed_eq hAllSc frame.locals discr]
    cases evalPrimitiveOperand body.locals frame.locals discr with
    | error _ => rfl
    | ok pair =>
      cases pair with
      | mk dv ls1 =>
        dsimp
        cases dv with
        | scalar sv =>
          dsimp
          cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;> rfl
        | bool b =>
          dsimp
          cases evalBoolSwitchBranches b targets.otherwise targets.branches <;> rfl
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl

private theorem evalStepTupleAssert_embed_eq (p : Program) (c : Choice) (s : State)
    (hFlat : stepIsFlatAssertFree p s = true) :
    evalStepTupleAssert p c (embedState s) = liftStepResult (evalStep p c s) := by
  cases s with
  | mk frames callerMem =>
    unfold evalStepTupleAssert evalStep embedState
    unfold stepIsFlatAssertFree at hFlat
    dsimp at hFlat
    dsimp
    cases frames with
    | nil => rfl
    | cons frame rest =>
      cases rest with
      | cons _ _ => rfl
      | nil =>
        dsimp at hFlat
        dsimp [List.map]
        have hDefId : (embedFrame frame).defId = frame.defId := rfl
        have hBlkIdx : (embedFrame frame).blockIdx = frame.blockIdx := rfl
        have hStmtIdx : (embedFrame frame).stmtIdx = frame.stmtIdx := rfl
        rw [hDefId, hBlkIdx, hStmtIdx]
        cases hB : Trusted.MirSemantics.getElem? p.bodies frame.defId with
        | none => rfl
        | some body =>
          rw [hB] at hFlat
          dsimp at hFlat
          unfold isFlatAssertFreeBody at hFlat
          let ⟨hAllSc, hNotAssert⟩ := bool_and_true hFlat
          have hNoAssert := bool_not_true hNotAssert
          unfold bodyHasAssert at hNoAssert
          dsimp
          cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
          | none => rfl
          | some bb =>
            dsimp
            cases hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
            | some stmt =>
              exact evalStatementExt_embed_eq hAllSc frame callerMem stmt
            | none =>
              dsimp
              cases Nat.beq frame.stmtIdx bb.statements.length with
              | false => rfl
              | true =>
                dsimp
                have hBbNoAssert : isAssertTerminator bb.terminator = false :=
                  list_any_false_getElem? (p := fun b => isAssertTerminator b.terminator)
                    hNoAssert hBb
                exact evalTerminatorExt_embed_eq hAllSc hBbNoAssert frame callerMem

private theorem stepIsFlatAssertFree_of_program {p : Program}
    (hFlat : isFlatAssertFreeProgram p = true) (s : State) :
    stepIsFlatAssertFree p s = true := by
  unfold stepIsFlatAssertFree
  cases s.frames with
  | nil => rfl
  | cons frame rest =>
    cases rest with
    | cons _ _ => rfl
    | nil =>
      dsimp
      cases hB : Trusted.MirSemantics.getElem? p.bodies frame.defId with
      | none => rfl
      | some body =>
        dsimp
        unfold isFlatAssertFreeProgram at hFlat
        exact list_all_getElem? hFlat hB

private theorem evalTupleAssertFuel_embed_eq {p : Program}
    (hFlat : isFlatAssertFreeProgram p = true) (n : Nat) (s : State) :
    evalTupleAssertFuel p n (embedState s) = liftStepResult (evalMirFuel p n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    dsimp [evalTupleAssertFuel, evalMirFuel]
    rw [evalStepTupleAssert_embed_eq p 0 s (stepIsFlatAssertFree_of_program hFlat s)]
    cases hEv : evalStep p 0 s with
    | step s' => exact ih s'
    | fault _ => rfl
    | done out =>
      cases out with
      | returned _ => rfl
      | unwound um => exact False.elim (evalStep_never_unwound hEv)

private theorem reachesTupleAssert_of_reaches_embed {p : Program}
    (hFlat : isFlatAssertFreeProgram p = true) {s₀ s : State}
    (h : Reaches p s₀ s) :
    ReachesTupleAssert p (embedState s₀) (embedState s) := by
  let ⟨n, hn⟩ := exists_evalMirFuel_of_reaches h
  have hE := evalTupleAssertFuel_embed_eq hFlat n s₀
  rw [hn] at hE
  exact reachesTupleAssert_of_evalFuel hE

private theorem reaches_of_reachesTupleAssert_embed {p : Program}
    (hFlat : isFlatAssertFreeProgram p = true) {s₀ : State} {sExt : StateExt}
    (h : ReachesTupleAssert p (embedState s₀) sExt) :
    ∃ s : State, sExt = embedState s ∧ Reaches p s₀ s := by
  let ⟨n, hn⟩ := exists_evalTupleAssertFuel_of_reaches h
  have hE := evalTupleAssertFuel_embed_eq hFlat n s₀
  rw [hn] at hE
  cases hM : evalMirFuel p n s₀ with
  | step s =>
    rw [hM] at hE
    dsimp [liftStepResult] at hE
    injection hE with hEq
    exact ⟨s, hEq, reaches_of_evalMirFuel hM⟩
  | fault _ => rw [hM] at hE; cases hE
  | done out =>
    rw [hM] at hE
    cases out <;> cases hE

private theorem bodyStaticAdmitted_eq_of_flat {p : Program} {body : Body}
    (hFlat : isFlatAssertFreeBody body = true) :
    BodyStaticAdmittedTupleAssert p body = BodyStaticAdmitted p body := by
  unfold isFlatAssertFreeBody at hFlat
  let ⟨hAllSc, _⟩ := bool_and_true hFlat
  have hAllSup : body.locals.all isSupportedTupleOrScalarTy = true :=
    list_all_of_forall_getElem? (fun i ty hTy =>
      isSupportedTupleOrScalarTy_of_scalar (list_all_getElem? hAllSc hTy))
  unfold BodyStaticAdmittedTupleAssert BodyStaticAdmitted
  rw [hAllSc, hAllSup]

private theorem validEntryArgs_iff_of_flat {body : Body}
    (hFlat : isFlatAssertFreeBody body = true) (args : List Val) :
    ValidEntryArgsTupleAssert body args ↔ ValidEntryArgs body args := by
  unfold isFlatAssertFreeBody at hFlat
  let ⟨hAllSc, _⟩ := bool_and_true hFlat
  have hParamSc := list_all_take_drop1 body.argumentCount hAllSc
  unfold ValidEntryArgsTupleAssert ValidEntryArgs
  rw [checkArgsMatchExt_eq_of_supportedScalar args hParamSc]

private theorem tupleAssert_conservative_extension_query {p : Program}
    (hFlat : isFlatAssertFreeProgram p = true) (q : Query) :
    (WellFormedTupleAssert p q ↔ WellFormed p q) ∧
    (NoPanicAndWellFormedTupleAssert p q ↔ WellFormed p q) ∧
    (∀ msg : AssertKind, ¬ BehaviorTupleAssert p q (.panic msg)) ∧
    (∀ out : Out,
      BehaviorTupleAssert p q (.ret out) ↔
        Behavior p q (.returned out)) ∧
    (∀ out : TerminalOut,
      Behavior p q out ↔
        match out with
        | .returned o => BehaviorTupleAssert p q (.ret o)
        | .unwound _ => False) ∧
    (∀ k : FaultKind,
      ReachesResultTupleAssert p q (.fault k) ↔
        ReachesResult p q (.fault k)) ∧
    (DivergesTupleAssert p q ↔ Diverges p q) := by
  have hInitEq := initStateTupleAssert_eq_of_flatAssertFree hFlat q
  have hNoPanic : ∀ msg : AssertKind, ¬ BehaviorTupleAssert p q (.panic msg) := by
    intro msg hP
    unfold BehaviorTupleAssert ReachesResultTupleAssert at hP
    rw [hInitEq] at hP
    cases hInit : initState p q with
    | error _ => rw [hInit] at hP; cases hP
    | ok s₀ =>
      rw [hInit] at hP; dsimp at hP
      let ⟨sExt, hR, hSt⟩ := hP
      let ⟨s, hSEq, _⟩ := reaches_of_reachesTupleAssert_embed hFlat hR
      subst hSEq
      let ⟨c, hc, hEv⟩ := hSt
      have hc0 : c = 0 := hc; subst hc0
      rw [evalStepTupleAssert_embed_eq p 0 s (stepIsFlatAssertFree_of_program hFlat s)] at hEv
      cases hM : evalStep p 0 s with
      | step _ => rw [hM] at hEv; cases hEv
      | fault _ => rw [hM] at hEv; cases hEv
      | done out =>
        rw [hM] at hEv
        cases out <;> cases hEv
  have hRetIff : ∀ out : Out,
      BehaviorTupleAssert p q (.ret out) ↔ Behavior p q (.returned out) := by
    intro out
    unfold BehaviorTupleAssert ReachesResultTupleAssert Behavior ReachesResult
    rw [hInitEq]
    cases hInit : initState p q with
    | error _ =>
      dsimp
      constructor <;> (intro h; cases h)
    | ok s₀ =>
      dsimp
      constructor
      · intro ⟨sExt, hR, c, hc, hEv⟩
        have hc0 : c = 0 := hc; subst hc0
        let ⟨s, hSEq, hRM⟩ := reaches_of_reachesTupleAssert_embed hFlat hR
        subst hSEq
        rw [evalStepTupleAssert_embed_eq p 0 s (stepIsFlatAssertFree_of_program hFlat s)] at hEv
        cases hM : evalStep p 0 s with
        | step _ => rw [hM] at hEv; cases hEv
        | fault _ => rw [hM] at hEv; cases hEv
        | done tout =>
          rw [hM] at hEv
          cases tout with
          | unwound _ => cases hEv
          | returned o =>
            dsimp [liftStepResult] at hEv
            injection hEv with hEq1
            injection hEq1 with hEq2; subst hEq2
            exact ⟨s, hRM, 0, rfl, hM⟩
      · intro ⟨s, hRM, c, hc, hEv⟩
        have hc0 : c = 0 := hc; subst hc0
        refine ⟨embedState s, reachesTupleAssert_of_reaches_embed hFlat hRM, 0, rfl, ?_⟩
        rw [evalStepTupleAssert_embed_eq p 0 s (stepIsFlatAssertFree_of_program hFlat s), hEv]
        rfl
  have hFaultIff : ∀ k : FaultKind,
      ReachesResultTupleAssert p q (.fault k) ↔ ReachesResult p q (.fault k) := by
    intro k
    unfold ReachesResultTupleAssert ReachesResult
    rw [hInitEq]
    cases hInit : initState p q with
    | error k' =>
      dsimp
      constructor
      · intro h; injection h with hEq; subst hEq; rfl
      · intro h; injection h with hEq; subst hEq; rfl
    | ok s₀ =>
      dsimp
      constructor
      · intro ⟨sExt, hR, c, hc, hEv⟩
        have hc0 : c = 0 := hc; subst hc0
        let ⟨s, hSEq, hRM⟩ := reaches_of_reachesTupleAssert_embed hFlat hR
        subst hSEq
        rw [evalStepTupleAssert_embed_eq p 0 s (stepIsFlatAssertFree_of_program hFlat s)] at hEv
        cases hM : evalStep p 0 s with
        | step _ => rw [hM] at hEv; cases hEv
        | fault k' =>
          rw [hM] at hEv
          dsimp [liftStepResult] at hEv
          injection hEv with hEq; subst hEq
          exact ⟨s, hRM, 0, rfl, hM⟩
        | done tout =>
          rw [hM] at hEv
          cases tout with
          | returned _ => cases hEv
          | unwound um => exact False.elim (evalStep_never_unwound hM)
      · intro ⟨s, hRM, c, hc, hEv⟩
        have hc0 : c = 0 := hc; subst hc0
        refine ⟨embedState s, reachesTupleAssert_of_reaches_embed hFlat hRM, 0, rfl, ?_⟩
        rw [evalStepTupleAssert_embed_eq p 0 s (stepIsFlatAssertFree_of_program hFlat s), hEv]
        rfl
  have hWfIff : WellFormedTupleAssert p q ↔ WellFormed p q := by
    unfold WellFormedTupleAssert WellFormed
    constructor
    · intro ⟨⟨s₀Ext, hOkExt, _⟩, hNoF⟩
      rw [hInitEq] at hOkExt
      cases hInit : initState p q with
      | error _ => rw [hInit] at hOkExt; cases hOkExt
      | ok s₀ =>
        refine ⟨⟨s₀, rfl, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
        intro k hF
        exact hNoF k ((hFaultIff k).mpr hF)
    · intro ⟨⟨s₀, hInit, _⟩, hNoF⟩
      refine ⟨⟨embedState s₀, by rw [hInitEq, hInit], fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
      intro k hF
      exact hNoF k ((hFaultIff k).mp hF)
  have hDivIff : DivergesTupleAssert p q ↔ Diverges p q := by
    rw [diverges_iff_forall_evalMirFuel]
    unfold DivergesTupleAssert
    constructor
    · intro ⟨s₀Ext, hOkExt, hAll⟩
      rw [hInitEq] at hOkExt
      cases hInit : initState p q with
      | error _ => rw [hInit] at hOkExt; cases hOkExt
      | ok s₀ =>
        rw [hInit] at hOkExt
        injection hOkExt with hEq; subst hEq
        refine ⟨s₀, rfl, ?_⟩
        intro n
        let ⟨sExt, hN⟩ := hAll n
        rw [evalTupleAssertFuel_embed_eq hFlat n s₀] at hN
        cases hM : evalMirFuel p n s₀ with
        | step s' => exact ⟨s', rfl⟩
        | fault _ => rw [hM] at hN; cases hN
        | done out => rw [hM] at hN; cases out <;> cases hN
    · intro ⟨s₀, hInit, hAll⟩
      refine ⟨embedState s₀, by rw [hInitEq, hInit], ?_⟩
      intro n
      let ⟨s', hN⟩ := hAll n
      refine ⟨embedState s', ?_⟩
      rw [evalTupleAssertFuel_embed_eq hFlat n s₀, hN]
      rfl
  refine ⟨hWfIff, ?_, hNoPanic, hRetIff, ?_, hFaultIff, hDivIff⟩
  · unfold NoPanicAndWellFormedTupleAssert
    constructor
    · intro ⟨hW, _⟩; exact hWfIff.mp hW
    · intro hW; exact ⟨hWfIff.mpr hW, hNoPanic⟩
  · intro out
    cases out with
    | returned o => exact (hRetIff o).symm
    | unwound um =>
      constructor
      · intro hB; exact behavior_unwound_false p q um hB
      · intro hF; exact False.elim hF

private theorem tupleAssert_conservative_extension_exact_sliceA
    (p : Program) :
    (∀ (c : Choice) (s : State),
      stepIsFlatAssertFree p s = true →
      evalStepTupleAssert p c (embedState s) =
        liftStepResult (evalStep p c s)) ∧
    (isFlatAssertFreeProgram p = true →
      (∀ q : Query,
        (WellFormedTupleAssert p q ↔ WellFormed p q) ∧
        (NoPanicAndWellFormedTupleAssert p q ↔ WellFormed p q) ∧
        (∀ msg : AssertKind, ¬ BehaviorTupleAssert p q (.panic msg)) ∧
        (∀ out : Out,
          BehaviorTupleAssert p q (.ret out) ↔
            Behavior p q (.returned out)) ∧
        (∀ out : TerminalOut,
          Behavior p q out ↔
            match out with
            | .returned o => BehaviorTupleAssert p q (.ret o)
            | .unwound _ => False) ∧
        (∀ k : FaultKind,
          ReachesResultTupleAssert p q (.fault k) ↔
            ReachesResult p q (.fault k)) ∧
        (DivergesTupleAssert p q ↔ Diverges p q)) ∧
      (∀ (q : Query) (post : Out → Prop),
        SatisfiesPostNoPanicTupleAssert p q post ↔
          SatisfiesPost p q (fun out =>
            match out with | .returned o => post o | .unwound _ => False)) ∧
      (∀ (defId : DefId) (body : Body) (safetyPre : List Val → Prop),
        BodyVerifiedNoPanicTupleAssert p defId body safetyPre ↔
          BodyVerified p defId body safetyPre) ∧
      (∀ specs : Specs,
        (CrateTheoremNoPanicTupleAssert ⟨p, specs⟩ ↔
          CrateTheorem ⟨p, specs⟩) ∧
        (UnitTheoremNoPanicTupleAssert ⟨p, specs⟩ ↔
          UnitTheorem ⟨p, specs⟩))) := by
  refine ⟨fun c s h => evalStepTupleAssert_embed_eq p c s h, ?_⟩
  intro hFlat
  have hQ := fun q => tupleAssert_conservative_extension_query hFlat q
  have hBodyIff : ∀ (defId : DefId) (body : Body) (safetyPre : List Val → Prop),
      BodyVerifiedNoPanicTupleAssert p defId body safetyPre ↔
        BodyVerified p defId body safetyPre := by
    intro defId body safetyPre
    unfold BodyVerifiedNoPanicTupleAssert BodyVerified
    have hEntryFlat : isFlatAssertFreeProgram (entryProgForBody p defId) = true := hFlat
    constructor
    · intro ⟨hGet, hAdm, hAll⟩
      have hFlatBody := list_all_getElem? hFlat hGet
      rw [bodyStaticAdmitted_eq_of_flat hFlatBody] at hAdm
      refine ⟨hGet, hAdm, ?_⟩
      intro args hValid hUns
      have hValidExt := (validEntryArgs_iff_of_flat hFlatBody args).mpr hValid
      exact (tupleAssert_conservative_extension_query hEntryFlat { args := args }).2.1.mp
        (hAll args hValidExt hUns)
    · intro ⟨hGet, hAdm, hAll⟩
      have hFlatBody := list_all_getElem? hFlat hGet
      rw [← bodyStaticAdmitted_eq_of_flat hFlatBody] at hAdm
      refine ⟨hGet, hAdm, ?_⟩
      intro args hValidExt hUns
      have hValid := (validEntryArgs_iff_of_flat hFlatBody args).mp hValidExt
      exact (tupleAssert_conservative_extension_query hEntryFlat { args := args }).2.1.mpr
        (hAll args hValid hUns)
  refine ⟨hQ, ?_, hBodyIff, ?_⟩
  · intro q post
    let ⟨_, hNoP, _, hRet, hTout, _, _⟩ := hQ q
    unfold SatisfiesPostNoPanicTupleAssert SatisfiesPost
    constructor
    · intro ⟨hNP, hPost⟩
      refine ⟨hNoP.mp hNP, ?_⟩
      intro out hBeh
      have hM := (hTout out).mp hBeh
      cases out with
      | returned o => exact hPost o hM
      | unwound _ => exact False.elim hM
    · intro ⟨hWf, hPost⟩
      refine ⟨hNoP.mpr hWf, ?_⟩
      intro out hBeh
      exact hPost (.returned out) ((hRet out).mp hBeh)
  · intro specs
    have hProgIff : ProgramVerifiedNoPanicTupleAssert p specs ↔ ProgramVerified p specs := by
      unfold ProgramVerifiedNoPanicTupleAssert ProgramVerified
      constructor
      · intro ⟨h1, h2, h3, h4, h5, hB, hProp⟩
        exact ⟨h1, h2, h3, h4, h5, fun d b hG => (hBodyIff d b (specs.safety b.identity)).mp (hB d b hG), hProp⟩
      · intro ⟨h1, h2, h3, h4, h5, hB, hProp⟩
        exact ⟨h1, h2, h3, h4, h5, fun d b hG => (hBodyIff d b (specs.safety b.identity)).mpr (hB d b hG), hProp⟩
    constructor
    · unfold CrateTheoremNoPanicTupleAssert CrateTheorem
      constructor
      · intro ⟨hS, hP⟩; exact ⟨hS, hProgIff.mp hP⟩
      · intro ⟨hS, hP⟩; exact ⟨hS, hProgIff.mpr hP⟩
    · unfold UnitTheoremNoPanicTupleAssert UnitTheorem
      constructor
      · intro ⟨hS, hP⟩; exact ⟨hS, hProgIff.mp hP⟩
      · intro ⟨hS, hP⟩; exact ⟨hS, hProgIff.mpr hP⟩


/-! ### Private Helpers from `F1_11_SliceB1.lean` -/
/-! ### Stage 4 Helpers — Slice B: Generic Multi-Step Simulation, Unsigned Overflow, & Theorem 2 (`SROA`) -/

/-! #### Generic Constructive Multi-Step Simulation -> Bidirectional `M_tupleAssert` Equivalence -/

private theorem evalTupleAssertFuel_done_of_le {p : Program} {k m : Nat}
    {s : StateExt} {out : TerminalOutExt}
    (hK : evalTupleAssertFuel p k s = .done out) (hLe : k ≤ m) :
    evalTupleAssertFuel p m s = .done out := by
  have hAdd := nat_sub_add_cancel_of_le hLe
  rw [← hAdd, evalTupleAssertFuel_add, hK]

private theorem evalTupleAssertFuel_fault_of_le {p : Program} {k m : Nat}
    {s : StateExt} {fk : FaultKind}
    (hK : evalTupleAssertFuel p k s = .fault fk) (hLe : k ≤ m) :
    evalTupleAssertFuel p m s = .fault fk := by
  have hAdd := nat_sub_add_cancel_of_le hLe
  rw [← hAdd, evalTupleAssertFuel_add, hK]

private theorem evalTupleAssertFuel_done_unique {p : Program} {m n : Nat}
    {s : StateExt} {o₁ o₂ : TerminalOutExt}
    (h1 : evalTupleAssertFuel p m s = .done o₁)
    (h2 : evalTupleAssertFuel p n s = .done o₂) : o₁ = o₂ := by
  cases Nat.lt_or_ge m n with
  | inl hlt =>
    have hEq := evalTupleAssertFuel_done_of_le h1 (Nat.le_of_lt hlt)
    rw [hEq] at h2
    injection h2
  | inr hge =>
    have hEq := evalTupleAssertFuel_done_of_le h2 hge
    rw [hEq] at h1
    injection h1 with hO
    exact hO.symm

private theorem evalTupleAssertFuel_fault_unique {p : Program} {m n : Nat}
    {s : StateExt} {k₁ k₂ : FaultKind}
    (h1 : evalTupleAssertFuel p m s = .fault k₁)
    (h2 : evalTupleAssertFuel p n s = .fault k₂) : k₁ = k₂ := by
  cases Nat.lt_or_ge m n with
  | inl hlt =>
    have hEq := evalTupleAssertFuel_fault_of_le h1 (Nat.le_of_lt hlt)
    rw [hEq] at h2
    injection h2
  | inr hge =>
    have hEq := evalTupleAssertFuel_fault_of_le h2 hge
    rw [hEq] at h1
    injection h1 with hK
    exact hK.symm

private theorem evalTupleAssertFuel_done_ne_fault {p : Program} {m n : Nat}
    {s : StateExt} {out : TerminalOutExt} {fk : FaultKind}
    (h1 : evalTupleAssertFuel p m s = .done out)
    (h2 : evalTupleAssertFuel p n s = .fault fk) : False := by
  cases Nat.lt_or_ge m n with
  | inl hlt =>
    have hEq := evalTupleAssertFuel_done_of_le h1 (Nat.le_of_lt hlt)
    rw [hEq] at h2
    cases h2
  | inr hge =>
    have hEq := evalTupleAssertFuel_fault_of_le h2 hge
    rw [hEq] at h1
    cases h1

private theorem evalTupleAssertFuel_step_sim_fwd {pSrc pTgt : Program}
    {R : StateExt → StateExt → Prop}
    (hStepSim : ∀ sSrc sTgt sSrc', R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .step sSrc' →
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .step sTgt' ∧ R sSrc' sTgt')
    (n : Nat) {sSrc sTgt sSrc' : StateExt}
    (hR : R sSrc sTgt)
    (hFuel : evalTupleAssertFuel pSrc n sSrc = .step sSrc') :
    ∃ m sTgt', n ≤ m ∧ evalTupleAssertFuel pTgt m sTgt = .step sTgt' ∧ R sSrc' sTgt' := by
  induction n generalizing sSrc sTgt with
  | zero =>
    dsimp [evalTupleAssertFuel] at hFuel
    injection hFuel with hEq; subst hEq
    exact ⟨0, sTgt, Nat.le_refl 0, rfl, hR⟩
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hFuel
    cases hEv : evalStepTupleAssert pSrc 0 sSrc with
    | done _ => rw [hEv] at hFuel; cases hFuel
    | fault _ => rw [hEv] at hFuel; cases hFuel
    | step sMid =>
      rw [hEv] at hFuel
      let ⟨d, sTgtMid, hdPos, hTgtStep, hRMid⟩ := hStepSim sSrc sTgt sMid hR hEv
      let ⟨m, sTgtEnd, hKm, hTgtRest, hREnd⟩ := ih hRMid hFuel
      refine ⟨d + m, sTgtEnd, ?_, ?_, hREnd⟩
      · have hd1 : 1 ≤ d := hdPos
        have hSum : k + 1 ≤ d + m := by
          rw [Nat.add_comm k 1]
          exact Nat.add_le_add hd1 hKm
        exact hSum
      · rw [evalTupleAssertFuel_add, hTgtStep]
        exact hTgtRest

private theorem evalTupleAssertFuel_done_sim_fwd {pSrc pTgt : Program}
    {R : StateExt → StateExt → Prop}
    (hStepSim : ∀ sSrc sTgt sSrc', R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .step sSrc' →
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .step sTgt' ∧ R sSrc' sTgt')
    (hDoneSim : ∀ sSrc sTgt out, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .done out →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .done out)
    (n : Nat) {sSrc sTgt : StateExt} {out : TerminalOutExt}
    (hR : R sSrc sTgt)
    (hFuel : evalTupleAssertFuel pSrc n sSrc = .done out) :
    ∃ m, evalTupleAssertFuel pTgt m sTgt = .done out := by
  induction n generalizing sSrc sTgt with
  | zero => dsimp [evalTupleAssertFuel] at hFuel; cases hFuel
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hFuel
    cases hEv : evalStepTupleAssert pSrc 0 sSrc with
    | fault _ => rw [hEv] at hFuel; cases hFuel
    | done o =>
      rw [hEv] at hFuel
      injection hFuel with hEq; subst hEq
      let ⟨d, _, hD⟩ := hDoneSim sSrc sTgt o hR hEv
      exact ⟨d, hD⟩
    | step sMid =>
      rw [hEv] at hFuel
      let ⟨d, sTgtMid, _, hTgtStep, hRMid⟩ := hStepSim sSrc sTgt sMid hR hEv
      let ⟨m, hTgtRest⟩ := ih hRMid hFuel
      refine ⟨d + m, ?_⟩
      rw [evalTupleAssertFuel_add, hTgtStep]
      exact hTgtRest

private theorem evalTupleAssertFuel_fault_sim_fwd {pSrc pTgt : Program}
    {R : StateExt → StateExt → Prop}
    (hStepSim : ∀ sSrc sTgt sSrc', R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .step sSrc' →
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .step sTgt' ∧ R sSrc' sTgt')
    (hFaultSim : ∀ sSrc sTgt fk, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .fault fk →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .fault fk)
    (n : Nat) {sSrc sTgt : StateExt} {fk : FaultKind}
    (hR : R sSrc sTgt)
    (hFuel : evalTupleAssertFuel pSrc n sSrc = .fault fk) :
    ∃ m, evalTupleAssertFuel pTgt m sTgt = .fault fk := by
  induction n generalizing sSrc sTgt with
  | zero => dsimp [evalTupleAssertFuel] at hFuel; cases hFuel
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hFuel
    cases hEv : evalStepTupleAssert pSrc 0 sSrc with
    | done _ => rw [hEv] at hFuel; cases hFuel
    | fault k' =>
      rw [hEv] at hFuel
      injection hFuel with hEq; subst hEq
      let ⟨d, _, hD⟩ := hFaultSim sSrc sTgt k' hR hEv
      exact ⟨d, hD⟩
    | step sMid =>
      rw [hEv] at hFuel
      let ⟨d, sTgtMid, _, hTgtStep, hRMid⟩ := hStepSim sSrc sTgt sMid hR hEv
      let ⟨m, hTgtRest⟩ := ih hRMid hFuel
      refine ⟨d + m, ?_⟩
      rw [evalTupleAssertFuel_add, hTgtStep]
      exact hTgtRest

private theorem evalTupleAssertFuel_done_sim_bwd {pSrc pTgt : Program}
    {R : StateExt → StateExt → Prop}
    (hStepSim : ∀ sSrc sTgt sSrc', R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .step sSrc' →
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .step sTgt' ∧ R sSrc' sTgt')
    (hDoneSim : ∀ sSrc sTgt out, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .done out →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .done out)
    (hFaultSim : ∀ sSrc sTgt fk, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .fault fk →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .fault fk)
    (bound : Nat) :
    ∀ (m : Nat) (sSrc sTgt : StateExt) (out : TerminalOutExt),
      m ≤ bound →
      R sSrc sTgt →
      evalTupleAssertFuel pTgt m sTgt = .done out →
      ∃ n, evalTupleAssertFuel pSrc n sSrc = .done out := by
  induction bound with
  | zero =>
    intro m _ _ _ hLe _ hTgt
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hLe
    subst hm0
    dsimp [evalTupleAssertFuel] at hTgt
    cases hTgt
  | succ b ih =>
    intro m sSrc sTgt out hLe hR hTgt
    cases hEv : evalStepTupleAssert pSrc 0 sSrc with
    | done o =>
      let ⟨d, _, hD⟩ := hDoneSim sSrc sTgt o hR hEv
      have hEq := evalTupleAssertFuel_done_unique hD hTgt
      subst hEq
      exact ⟨1, by dsimp [evalTupleAssertFuel]; rw [hEv]⟩
    | fault fk =>
      let ⟨d, _, hF⟩ := hFaultSim sSrc sTgt fk hR hEv
      exact False.elim (evalTupleAssertFuel_done_ne_fault hTgt hF)
    | step sSrc' =>
      let ⟨k, sTgt', hkPos, hTgtStep, hR'⟩ := hStepSim sSrc sTgt sSrc' hR hEv
      cases Nat.lt_or_ge m k with
      | inl hlt =>
        let ⟨_, hSm⟩ := evalTupleAssertFuel_mono_step (Nat.le_of_lt hlt) hTgtStep
        rw [hSm] at hTgt
        cases hTgt
      | inr hge =>
        have hSubEq := nat_sub_add_cancel_of_le hge
        rw [← hSubEq, evalTupleAssertFuel_add, hTgtStep] at hTgt
        have hSubLe : m - k ≤ b := by
          have h1 : m - k + 1 ≤ b + 1 := by
            have hK1 : 1 ≤ k := hkPos
            have hM1 : m - k + 1 ≤ m - k + k := Nat.add_le_add_left hK1 (m - k)
            rw [Nat.sub_add_cancel hge] at hM1
            exact Nat.le_trans hM1 hLe
          exact Nat.le_of_succ_le_succ h1
        let ⟨n, hn⟩ := ih (m - k) sSrc' sTgt' out hSubLe hR' hTgt
        exact ⟨n + 1, by dsimp [evalTupleAssertFuel]; rw [hEv]; exact hn⟩

private theorem evalTupleAssertFuel_fault_sim_bwd {pSrc pTgt : Program}
    {R : StateExt → StateExt → Prop}
    (hStepSim : ∀ sSrc sTgt sSrc', R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .step sSrc' →
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .step sTgt' ∧ R sSrc' sTgt')
    (hDoneSim : ∀ sSrc sTgt out, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .done out →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .done out)
    (hFaultSim : ∀ sSrc sTgt fk, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .fault fk →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .fault fk)
    (bound : Nat) :
    ∀ (m : Nat) (sSrc sTgt : StateExt) (fk : FaultKind),
      m ≤ bound →
      R sSrc sTgt →
      evalTupleAssertFuel pTgt m sTgt = .fault fk →
      ∃ n, evalTupleAssertFuel pSrc n sSrc = .fault fk := by
  induction bound with
  | zero =>
    intro m _ _ _ hLe _ hTgt
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hLe
    subst hm0
    dsimp [evalTupleAssertFuel] at hTgt
    cases hTgt
  | succ b ih =>
    intro m sSrc sTgt fk hLe hR hTgt
    cases hEv : evalStepTupleAssert pSrc 0 sSrc with
    | fault k' =>
      let ⟨d, _, hF⟩ := hFaultSim sSrc sTgt k' hR hEv
      have hEq := evalTupleAssertFuel_fault_unique hF hTgt
      subst hEq
      exact ⟨1, by dsimp [evalTupleAssertFuel]; rw [hEv]⟩
    | done o =>
      let ⟨d, _, hD⟩ := hDoneSim sSrc sTgt o hR hEv
      exact False.elim (evalTupleAssertFuel_done_ne_fault hD hTgt)
    | step sSrc' =>
      let ⟨k, sTgt', hkPos, hTgtStep, hR'⟩ := hStepSim sSrc sTgt sSrc' hR hEv
      cases Nat.lt_or_ge m k with
      | inl hlt =>
        let ⟨_, hSm⟩ := evalTupleAssertFuel_mono_step (Nat.le_of_lt hlt) hTgtStep
        rw [hSm] at hTgt
        cases hTgt
      | inr hge =>
        have hSubEq := nat_sub_add_cancel_of_le hge
        rw [← hSubEq, evalTupleAssertFuel_add, hTgtStep] at hTgt
        have hSubLe : m - k ≤ b := by
          have h1 : m - k + 1 ≤ b + 1 := by
            have hK1 : 1 ≤ k := hkPos
            have hM1 : m - k + 1 ≤ m - k + k := Nat.add_le_add_left hK1 (m - k)
            rw [Nat.sub_add_cancel hge] at hM1
            exact Nat.le_trans hM1 hLe
          exact Nat.le_of_succ_le_succ h1
        let ⟨n, hn⟩ := ih (m - k) sSrc' sTgt' fk hSubLe hR' hTgt
        exact ⟨n + 1, by dsimp [evalTupleAssertFuel]; rw [hEv]; exact hn⟩

private theorem evalTupleAssertFuel_div_sim_bwd {pSrc pTgt : Program}
    {R : StateExt → StateExt → Prop}
    (hStepSim : ∀ sSrc sTgt sSrc', R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .step sSrc' →
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .step sTgt' ∧ R sSrc' sTgt')
    (hDoneSim : ∀ sSrc sTgt out, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .done out →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .done out)
    (hFaultSim : ∀ sSrc sTgt fk, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .fault fk →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .fault fk)
    (n : Nat) {sSrc sTgt : StateExt}
    (hR : R sSrc sTgt)
    (hDiv : ∀ m, ∃ s', evalTupleAssertFuel pTgt m sTgt = .step s') :
    ∃ sSrc' sTgt', evalTupleAssertFuel pSrc n sSrc = .step sSrc' ∧ R sSrc' sTgt' ∧
      (∀ m, ∃ s'', evalTupleAssertFuel pTgt m sTgt' = .step s'') := by
  induction n generalizing sSrc sTgt with
  | zero => exact ⟨sSrc, sTgt, rfl, hR, hDiv⟩
  | succ k ih =>
    cases hEv : evalStepTupleAssert pSrc 0 sSrc with
    | done o =>
      let ⟨d, _, hD⟩ := hDoneSim sSrc sTgt o hR hEv
      let ⟨_, hS⟩ := hDiv d
      rw [hD] at hS; cases hS
    | fault fk =>
      let ⟨d, _, hF⟩ := hFaultSim sSrc sTgt fk hR hEv
      let ⟨_, hS⟩ := hDiv d
      rw [hF] at hS; cases hS
    | step sMid =>
      let ⟨d, sTgtMid, _, hTgtStep, hRMid⟩ := hStepSim sSrc sTgt sMid hR hEv
      have hDivMid : ∀ m, ∃ s'', evalTupleAssertFuel pTgt m sTgtMid = .step s'' := by
        intro m
        let ⟨s'', hDm⟩ := hDiv (d + m)
        rw [evalTupleAssertFuel_add, hTgtStep] at hDm
        exact ⟨s'', hDm⟩
      let ⟨sSrc', sTgt', hSrcRest, hR', hDiv'⟩ := ih hRMid hDivMid
      exact ⟨sSrc', sTgt', by dsimp [evalTupleAssertFuel]; rw [hEv]; exact hSrcRest, hR', hDiv'⟩

private theorem query_equiv_of_multistep_sim {pSrc pTgt : Program} {q : Query}
    {R : StateExt → StateExt → Prop}
    (hInitErr : ∀ k, initStateTupleAssert pSrc q = .error k →
      initStateTupleAssert pTgt q = .error k)
    (hInitOk : ∀ s₀Src, initStateTupleAssert pSrc q = .ok s₀Src →
      ∃ s₀Tgt, initStateTupleAssert pTgt q = .ok s₀Tgt ∧ R s₀Src s₀Tgt)
    (hStepSim : ∀ sSrc sTgt sSrc', R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .step sSrc' →
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .step sTgt' ∧ R sSrc' sTgt')
    (hDoneSim : ∀ sSrc sTgt out, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .done out →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .done out)
    (hFaultSim : ∀ sSrc sTgt fk, R sSrc sTgt →
      evalStepTupleAssert pSrc 0 sSrc = .fault fk →
      ∃ k, 0 < k ∧ evalTupleAssertFuel pTgt k sTgt = .fault fk) :
    (WellFormedTupleAssert pTgt q ↔ WellFormedTupleAssert pSrc q) ∧
    (NoPanicAndWellFormedTupleAssert pTgt q ↔
      NoPanicAndWellFormedTupleAssert pSrc q) ∧
    (∀ out : TerminalOutExt,
      BehaviorTupleAssert pTgt q out ↔ BehaviorTupleAssert pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResultTupleAssert pTgt q (.fault k) ↔
        ReachesResultTupleAssert pSrc q (.fault k)) ∧
    (DivergesTupleAssert pTgt q ↔ DivergesTupleAssert pSrc q) := by
  cases hInitSrc : initStateTupleAssert pSrc q with
  | error kErr =>
    have hInitTgt := hInitErr kErr hInitSrc
    have hBeh : ∀ out : TerminalOutExt,
        BehaviorTupleAssert pTgt q out ↔ BehaviorTupleAssert pSrc q out := by
      intro out
      unfold BehaviorTupleAssert ReachesResultTupleAssert
      rw [hInitTgt, hInitSrc]
    have hFault : ∀ k : FaultKind,
        ReachesResultTupleAssert pTgt q (.fault k) ↔
          ReachesResultTupleAssert pSrc q (.fault k) := by
      intro k
      unfold ReachesResultTupleAssert
      rw [hInitTgt, hInitSrc]
    have hWf : WellFormedTupleAssert pTgt q ↔ WellFormedTupleAssert pSrc q := by
      unfold WellFormedTupleAssert
      constructor
      · intro ⟨⟨_, hOk, _⟩, _⟩; rw [hInitTgt] at hOk; cases hOk
      · intro ⟨⟨_, hOk, _⟩, _⟩; rw [hInitSrc] at hOk; cases hOk
    have hNP : NoPanicAndWellFormedTupleAssert pTgt q ↔
        NoPanicAndWellFormedTupleAssert pSrc q := by
      unfold NoPanicAndWellFormedTupleAssert
      constructor
      · intro ⟨hW, _⟩; exact False.elim (by
          let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitTgt] at hOk; cases hOk)
      · intro ⟨hW, _⟩; exact False.elim (by
          let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitSrc] at hOk; cases hOk)
    have hDiv : DivergesTupleAssert pTgt q ↔ DivergesTupleAssert pSrc q := by
      unfold DivergesTupleAssert
      constructor
      · intro ⟨_, hOk, _⟩; rw [hInitTgt] at hOk; cases hOk
      · intro ⟨_, hOk, _⟩; rw [hInitSrc] at hOk; cases hOk
    exact ⟨hWf, hNP, hBeh, hFault, hDiv⟩
  | ok s₀Src =>
    let ⟨s₀Tgt, hInitTgt, hR0⟩ := hInitOk s₀Src hInitSrc
    have hBeh : ∀ out : TerminalOutExt,
        BehaviorTupleAssert pTgt q out ↔ BehaviorTupleAssert pSrc q out := by
      intro out
      unfold BehaviorTupleAssert ReachesResultTupleAssert
      rw [hInitTgt, hInitSrc]
      constructor
      · intro ⟨sEnd, hReach, hSt⟩
        let ⟨m, hm⟩ := evalTupleAssertFuel_terminal_of_reaches hReach hSt
        let ⟨n, hn⟩ := evalTupleAssertFuel_done_sim_bwd hStepSim hDoneSim hFaultSim
          (m + 1) (m + 1) s₀Src s₀Tgt out (Nat.le_refl _) hR0 hm
        exact reaches_and_step_of_evalTupleAssertFuel_done hn
      · intro ⟨sEnd, hReach, hSt⟩
        let ⟨n, hn⟩ := evalTupleAssertFuel_terminal_of_reaches hReach hSt
        let ⟨m, hm⟩ := evalTupleAssertFuel_done_sim_fwd hStepSim hDoneSim (n + 1) hR0 hn
        exact reaches_and_step_of_evalTupleAssertFuel_done hm
    have hFault : ∀ k : FaultKind,
        ReachesResultTupleAssert pTgt q (.fault k) ↔
          ReachesResultTupleAssert pSrc q (.fault k) := by
      intro k
      unfold ReachesResultTupleAssert
      rw [hInitTgt, hInitSrc]
      constructor
      · intro ⟨sEnd, hReach, hSt⟩
        let ⟨m, hm⟩ := evalTupleAssertFuel_terminal_of_reaches hReach hSt
        let ⟨n, hn⟩ := evalTupleAssertFuel_fault_sim_bwd hStepSim hDoneSim hFaultSim
          (m + 1) (m + 1) s₀Src s₀Tgt k (Nat.le_refl _) hR0 hm
        exact reaches_and_step_of_evalTupleAssertFuel_fault hn
      · intro ⟨sEnd, hReach, hSt⟩
        let ⟨n, hn⟩ := evalTupleAssertFuel_terminal_of_reaches hReach hSt
        let ⟨m, hm⟩ := evalTupleAssertFuel_fault_sim_fwd hStepSim hFaultSim (n + 1) hR0 hn
        exact reaches_and_step_of_evalTupleAssertFuel_fault hm
    have hWf : WellFormedTupleAssert pTgt q ↔ WellFormedTupleAssert pSrc q := by
      unfold WellFormedTupleAssert
      constructor
      · intro ⟨_, hNoF⟩
        exact ⟨⟨s₀Src, hInitSrc, fun _ _ => ⟨0, rfl⟩⟩, fun k hF => hNoF k ((hFault k).mpr hF)⟩
      · intro ⟨_, hNoF⟩
        exact ⟨⟨s₀Tgt, hInitTgt, fun _ _ => ⟨0, rfl⟩⟩, fun k hF => hNoF k ((hFault k).mp hF)⟩
    have hNP : NoPanicAndWellFormedTupleAssert pTgt q ↔
        NoPanicAndWellFormedTupleAssert pSrc q := by
      unfold NoPanicAndWellFormedTupleAssert
      constructor
      · intro ⟨hW, hNoP⟩
        exact ⟨hWf.mp hW, fun msg hP => hNoP msg ((hBeh (.panic msg)).mpr hP)⟩
      · intro ⟨hW, hNoP⟩
        exact ⟨hWf.mpr hW, fun msg hP => hNoP msg ((hBeh (.panic msg)).mp hP)⟩
    have hDiv : DivergesTupleAssert pTgt q ↔ DivergesTupleAssert pSrc q := by
      unfold DivergesTupleAssert
      constructor
      · intro ⟨s₀T, hOkT, hAllT⟩
        rw [hInitTgt] at hOkT
        injection hOkT with hEq; subst hEq
        refine ⟨s₀Src, hInitSrc, ?_⟩
        intro n
        let ⟨sSrc', _, hSrcN, _, _⟩ :=
          evalTupleAssertFuel_div_sim_bwd hStepSim hDoneSim hFaultSim n hR0 hAllT
        exact ⟨sSrc', hSrcN⟩
      · intro ⟨s₀S, hOkS, hAllS⟩
        rw [hInitSrc] at hOkS
        injection hOkS with hEq; subst hEq
        refine ⟨s₀Tgt, hInitTgt, ?_⟩
        intro m
        let ⟨sSrc', hSrcM⟩ := hAllS m
        let ⟨k, sTgt', hMk, hTgtK, _⟩ := evalTupleAssertFuel_step_sim_fwd hStepSim m hR0 hSrcM
        exact evalTupleAssertFuel_mono_step hMk hTgtK
    exact ⟨hWf, hNP, hBeh, hFault, hDiv⟩

/-! #### Exact Unsigned Overflow Arithmetic Equivalence (`addWithOverflow` / `subWithOverflow`) -/

private theorem if_true_of_prop {α : Type} {P : Prop} [d : Decidable P] (h : P) (x y : α) :
    (if P then x else y) = x := by
  cases d with
  | isFalse hn => exact False.elim (hn h)
  | isTrue _ => rfl

private theorem nat_mod_eq_of_lt {x y : Nat} (h : x < y) : Nat.mod x y = x :=
  Nat.mod_eq_of_lt h

private theorem nat_mod_lt (x : Nat) {y : Nat} (h : 0 < y) : Nat.mod x y < y :=
  Nat.mod_lt x h

private theorem if_and_false_eq {α : Type} (b : Bool) (x y : α) :
    (if (b && false) = true then x else y) = y := by
  cases b <;> rfl

private theorem intWidth_bitWidth_le_128 (w : IntWidth) : w.bitWidth ≤ 128 := by
  cases w <;> decide

private theorem intWidth_bitWidth_sub_add (w : IntWidth) :
    w.bitWidth - 1 - 0 + 1 = w.bitWidth := by
  cases w <;> rfl

private theorem intWidth_pow2_pos (w : IntWidth) : 0 < Nat.pow 2 w.bitWidth := by
  cases w <;> decide

private theorem intWidth_pow2_le_pow2_128 (w : IntWidth) :
    Nat.pow 2 w.bitWidth ≤ Nat.pow 2 128 := by
  cases w <;> decide

private theorem intWidth_pow2_dvd_128 (w : IntWidth) :
    ∃ q, Nat.pow 2 128 = Nat.pow 2 w.bitWidth * q := by
  cases w with
  | i8 => exact ⟨Nat.pow 2 120, rfl⟩
  | i16 => exact ⟨Nat.pow 2 112, rfl⟩
  | i32 => exact ⟨Nat.pow 2 96, rfl⟩
  | i64 => exact ⟨Nat.pow 2 64, rfl⟩
  | isize => exact ⟨Nat.pow 2 64, rfl⟩
  | i128 => exact ⟨1, rfl⟩

private theorem nat_add_mod_self_right (a m : Nat) :
    Nat.mod (a + m) m = Nat.mod a m := by
  cases m with
  | zero => rfl
  | succ m' =>
    have hEq : Nat.mod (a + Nat.succ m') (Nat.succ m') =
        if 0 < Nat.succ m' ∧ Nat.succ m' ≤ a + Nat.succ m' then
          Nat.mod (a + Nat.succ m' - Nat.succ m') (Nat.succ m')
        else a + Nat.succ m' := Nat.mod_eq_ite (a + Nat.succ m') (Nat.succ m')
    rw [hEq, if_true_of_prop ⟨Nat.zero_lt_succ m', Nat.le_add_left (Nat.succ m') a⟩,
        Nat.add_sub_cancel]

private theorem nat_mul_add_mod (m k r : Nat) :
    Nat.mod (m * k + r) m = Nat.mod r m := by
  induction k with
  | zero => rw [Nat.mul_zero, Nat.zero_add]
  | succ k' ih =>
    rw [Nat.mul_succ, Nat.add_right_comm, nat_add_mod_self_right]
    exact ih

private theorem nat_mod_mod_of_mul (x m q : Nat) :
    Nat.mod (Nat.mod x (m * q)) m = Nat.mod x m := by
  have hDiv : (m * q) * Nat.div x (m * q) + Nat.mod x (m * q) = x :=
    Nat.div_add_mod x (m * q)
  have hMod : Nat.mod (m * (q * Nat.div x (m * q)) + Nat.mod x (m * q)) m =
      Nat.mod (Nat.mod x (m * q)) m :=
    nat_mul_add_mod m (q * Nat.div x (m * q)) (Nat.mod x (m * q))
  rw [← Nat.mul_assoc, hDiv] at hMod
  exact hMod.symm

private theorem bitvec_eq_of_toNat_eq {n : Nat} {a b : BitVec n}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

private theorem bitvec_ofNat_toNat (n x : Nat) :
    (BitVec.ofNat n x).toNat = Nat.mod x (Nat.pow 2 n) := by
  rfl

private theorem nat_shiftRight_zero_eq (n : Nat) : Nat.shiftRight n 0 = n := by
  rfl

private theorem truncateBits_toNat (w : IntWidth) (bv : BitVec 128) :
    (truncateBits w bv).toNat = Nat.mod bv.toNat (Nat.pow 2 w.bitWidth) := by
  unfold truncateBits bvZeroExtend bvExtractLsb bvExtractLsb'
  have hLen := intWidth_bitWidth_sub_add w
  have hModLt : Nat.mod bv.toNat (Nat.pow 2 w.bitWidth) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt bv.toNat (intWidth_pow2_pos w))
      (intWidth_pow2_le_pow2_128 w)
  have hInner : (BitVec.ofNat (w.bitWidth - 1 - 0 + 1) (Nat.shiftRight bv.toNat 0)).toNat =
      Nat.mod bv.toNat (Nat.pow 2 w.bitWidth) := by
    rw [bitvec_ofNat_toNat, nat_shiftRight_zero_eq, hLen]
  rw [bitvec_ofNat_toNat, hInner]
  exact nat_mod_eq_of_lt hModLt

private theorem truncateBits_ofNat_toNat (w : IntWidth) (x : Nat) :
    (truncateBits w (BitVec.ofNat 128 x)).toNat = Nat.mod x (Nat.pow 2 w.bitWidth) := by
  rw [truncateBits_toNat, bitvec_ofNat_toNat]
  let ⟨q, hq⟩ := intWidth_pow2_dvd_128 w
  rw [hq]
  exact nat_mod_mod_of_mul x (Nat.pow 2 w.bitWidth) q

private theorem truncateBits_idem (w : IntWidth) (bv : BitVec 128) :
    truncateBits w (truncateBits w bv) = truncateBits w bv := by
  apply bitvec_eq_of_toNat_eq
  rw [truncateBits_toNat, truncateBits_toNat]
  exact nat_mod_eq_of_lt (Nat.mod_lt bv.toNat (intWidth_pow2_pos w))

private theorem scalarVal_wf_truncateBits (w : IntWidth) (s : Bool) (bv : BitVec 128) :
    ScalarVal.wf ⟨w, s, truncateBits w bv⟩ = true := by
  unfold ScalarVal.wf
  dsimp
  rw [truncateBits_idem w bv]
  exact bitvec_beq_refl _

private theorem int_ofNat_le_ofNat_iff (a b : Nat) :
    (Int.ofNat a ≤ Int.ofNat b) ↔ (a ≤ b) := by
  cases a with
  | zero =>
    constructor
    · intro _; exact Nat.zero_le b
    · intro _; exact Int.NonNeg.mk (b + 0)
  | succ a' =>
    constructor
    · intro h
      cases Nat.lt_or_ge b (a' + 1) with
      | inr hGe => exact hGe
      | inl hLt =>
        have hPos : 0 < (a' + 1) - b := Nat.sub_pos_of_lt hLt
        have hEq : (a' + 1) - b = ((a' + 1) - b - 1) + 1 := (Nat.sub_add_cancel hPos).symm
        change Int.NonNeg (Int.subNatNat b (a' + 1)) at h
        unfold Int.subNatNat at h
        rw [hEq] at h
        cases h
    · intro h
      change Int.NonNeg (Int.subNatNat b (a' + 1))
      unfold Int.subNatNat
      rw [Nat.sub_eq_zero_of_le h]
      exact Int.NonNeg.mk (b - (a' + 1))

private theorem int_ofNat_lt_ofNat_iff (a b : Nat) :
    (Int.ofNat a < Int.ofNat b) ↔ (a < b) :=
  int_ofNat_le_ofNat_iff (a + 1) b

private theorem int_negSucc_lt_zero (n : Nat) : Int.negSucc n < 0 := by
  cases n with
  | zero => exact Int.NonNeg.mk 0
  | succ k => exact Int.NonNeg.mk (0 + (k + 1))

private theorem natCast_int_eq_ofNat (n : Nat) : (n : Int) = Int.ofNat n := rfl

private theorem hpow_two_128_eq : HPow.hPow (2 : Int) 128 = Int.ofNat (Nat.pow 2 128) := by
  rfl

private theorem bvOfInt_ofNat (n : Nat) :
    bvOfInt 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
  unfold bvOfInt intEmod
  dsimp [Int.natAbs, Int.toNat]
  apply bitvec_eq_of_toNat_eq
  rw [bitvec_ofNat_toNat, bitvec_ofNat_toNat]
  exact nat_mod_eq_of_lt (Nat.mod_lt n (intWidth_pow2_pos .i128))

private theorem bvOfInt_natCast (n : Nat) :
    bvOfInt 128 (n : Int) = BitVec.ofNat 128 n :=
  bvOfInt_ofNat n

private theorem bitvec_bne_true_of_ne {n : Nat} {a b : BitVec n} (h : a ≠ b) :
    (a != b) = true := by
  unfold bne
  cases hEq : (a == b) with
  | false => rfl
  | true => exact False.elim (h (bitvec_beq_eq hEq))

private theorem bitvec_bne_false_of_eq {n : Nat} {a b : BitVec n} (h : a = b) :
    (a != b) = false := by
  subst h
  unfold bne
  rw [bitvec_beq_refl]
  rfl

private theorem nat_mod_sub_of_le_lt_double {x m : Nat} (hGe : m ≤ x) (hLt : x < m + m) :
    Nat.mod x m = x - m := by
  have hSubLt : x - m < m := by
    cases Nat.lt_or_ge (x - m) m with
    | inl h => exact h
    | inr h =>
      have hAdd := Nat.add_le_add_right h m
      rw [Nat.sub_add_cancel hGe] at hAdd
      exact False.elim (Nat.not_lt_of_ge hAdd hLt)
  have hEq : m * 1 + (x - m) = x := by
    rw [Nat.mul_one, Nat.add_comm, Nat.sub_add_cancel hGe]
  rw [← hEq, nat_mul_add_mod, nat_mod_eq_of_lt hSubLt, Nat.mul_one, Nat.add_sub_cancel_left]

private theorem unsigned_addWithOverflow_eq (w : IntWidth) (lb rb : BitVec 128) :
    let l : ScalarVal := ⟨w, false, lb⟩
    let r : ScalarVal := ⟨w, false, rb⟩
    let raw := bvOfInt 128 (decodeScalar l + decodeScalar r)
    let sumSv : ScalarVal := ⟨w, false, truncateBits w raw⟩
    evalWithOverflowOp .addWithOverflow (.scalar l) (.scalar r) =
      .ok (sumSv, decide (decodeScalar sumSv < decodeScalar l)) ∧
    evalBinOp .add (.scalar l) (.scalar r) = .ok (.scalar sumSv) ∧
    evalBinOp .lt (.scalar sumSv) (.scalar l) =
      .ok (.bool (decide (decodeScalar sumSv < decodeScalar l))) ∧
    checkVal (.scalar sumSv) (.int w false) = true := by
  dsimp
  have hMatch : (IntWidth.beq w w && (false == false)) = true := by
    rw [intWidth_beq_refl w]; rfl
  have hAddOk : evalBinOp .add (.scalar ⟨w, false, lb⟩) (.scalar ⟨w, false, rb⟩) =
      .ok (.scalar ⟨w, false, truncateBits w (bvOfInt 128
        (decodeScalar ⟨w, false, lb⟩ + decodeScalar ⟨w, false, rb⟩))⟩) := by
    unfold evalBinOp evalArithOp truncateScalar
    dsimp [BinOp.isShift, BinOp.isUnchecked]
    rw [hMatch]
    dsimp
    exact if_and_false_eq _ _ _
  have hLtOk : evalBinOp .lt
      (.scalar ⟨w, false, truncateBits w (bvOfInt 128
        (decodeScalar ⟨w, false, lb⟩ + decodeScalar ⟨w, false, rb⟩))⟩)
      (.scalar ⟨w, false, lb⟩) =
      .ok (.bool (decide (decodeScalar ⟨w, false, truncateBits w (bvOfInt 128
        (decodeScalar ⟨w, false, lb⟩ + decodeScalar ⟨w, false, rb⟩))⟩ <
        decodeScalar ⟨w, false, lb⟩))) := by
    unfold evalBinOp
    dsimp [BinOp.isShift]
    rw [hMatch]
    rfl
  have hCheckOk : checkVal (.scalar ⟨w, false, truncateBits w (bvOfInt 128
      (decodeScalar ⟨w, false, lb⟩ + decodeScalar ⟨w, false, rb⟩))⟩) (.int w false) = true := by
    unfold checkVal Val.ty?
    dsimp
    rw [scalarVal_wf_truncateBits]
    dsimp
    exact mirTy_beq_refl (.int w false)
  refine ⟨?_, hAddOk, hLtOk, hCheckOk⟩
  unfold evalWithOverflowOp truncateScalar
  dsimp
  rw [hMatch]
  dsimp
  let a := (truncateBits w lb).toNat
  let b := (truncateBits w rb).toNat
  have haLt : a < Nat.pow 2 w.bitWidth := by
    change (truncateBits w lb).toNat < Nat.pow 2 w.bitWidth
    rw [truncateBits_toNat]
    exact Nat.mod_lt lb.toNat (intWidth_pow2_pos w)
  have hbLt : b < Nat.pow 2 w.bitWidth := by
    change (truncateBits w rb).toNat < Nat.pow 2 w.bitWidth
    rw [truncateBits_toNat]
    exact Nat.mod_lt rb.toNat (intWidth_pow2_pos w)
  have hNotNeg : decide (((a + b : Nat) : Int) < 0) = false := by
    cases hD : decide (((a + b : Nat) : Int) < 0) with
    | false => rfl
    | true =>
      have hLt : Int.ofNat (a + b) < Int.ofNat 0 := of_decide_eq_true hD
      exact False.elim (Nat.not_lt_zero (a + b) ((int_ofNat_lt_ofNat_iff (a + b) 0).mp hLt))
  have hSumDec : decodeScalar ⟨w, false, truncateBits w (bvOfInt 128 ((a + b : Nat) : Int))⟩ =
      ((Nat.mod (a + b) (Nat.pow 2 w.bitWidth) : Nat) : Int) := by
    unfold decodeScalar
    dsimp
    rw [truncateBits_idem, bvOfInt_natCast, truncateBits_ofNat_toNat]
  have hOvfEq :
      (decide (((a + b : Nat) : Int) < 0) ||
        decide (((a + b : Nat) : Int) ≥ HPow.hPow (2 : Int) 128) ||
        (truncateBits w (bvOfInt 128 ((a + b : Nat) : Int)) !=
          bvOfInt 128 ((a + b : Nat) : Int))) =
      decide (((Nat.mod (a + b) (Nat.pow 2 w.bitWidth) : Nat) : Int) < (a : Int)) := by
    rw [hNotNeg, Bool.false_or]
    have hPowCast : HPow.hPow (2 : Int) 128 = ((Nat.pow 2 128 : Nat) : Int) := rfl
    rw [hPowCast]
    cases Nat.lt_or_ge (a + b) (Nat.pow 2 w.bitWidth) with
    | inl hNoOvf =>
      have hLt128 : a + b < Nat.pow 2 128 :=
        Nat.lt_of_lt_of_le hNoOvf (intWidth_pow2_le_pow2_128 w)
      have hHostF : decide (((a + b : Nat) : Int) ≥ ((Nat.pow 2 128 : Nat) : Int)) = false := by
        cases hD : decide (((a + b : Nat) : Int) ≥ ((Nat.pow 2 128 : Nat) : Int)) with
        | false => rfl
        | true =>
          have hGe : Nat.pow 2 128 ≤ a + b :=
            (int_ofNat_le_ofNat_iff _ _).mp (of_decide_eq_true hD)
          exact False.elim (Nat.not_lt_of_ge hGe hLt128)
      have hTruncEq : truncateBits w (bvOfInt 128 ((a + b : Nat) : Int)) =
          bvOfInt 128 ((a + b : Nat) : Int) := by
        rw [bvOfInt_natCast]
        apply bitvec_eq_of_toNat_eq
        rw [truncateBits_ofNat_toNat, bitvec_ofNat_toNat,
            nat_mod_eq_of_lt hNoOvf, nat_mod_eq_of_lt hLt128]
      have hLossyF : (truncateBits w (bvOfInt 128 ((a + b : Nat) : Int)) !=
          bvOfInt 128 ((a + b : Nat) : Int)) = false :=
        bitvec_bne_false_of_eq hTruncEq
      have hRhsF : decide (((Nat.mod (a + b) (Nat.pow 2 w.bitWidth) : Nat) : Int) < (a : Int)) =
          false := by
        rw [nat_mod_eq_of_lt hNoOvf]
        cases hD : decide (((a + b : Nat) : Int) < (a : Int)) with
        | false => rfl
        | true =>
          have hLt : a + b < a := (int_ofNat_lt_ofNat_iff _ _).mp (of_decide_eq_true hD)
          exact False.elim (Nat.not_lt_of_ge (Nat.le_add_right a b) hLt)
      rw [hHostF, hLossyF, hRhsF]
      rfl
    | inr hOvf =>
      have hDouble : a + b < Nat.pow 2 w.bitWidth + Nat.pow 2 w.bitWidth :=
        Nat.add_lt_add haLt hbLt
      have hModSub : Nat.mod (a + b) (Nat.pow 2 w.bitWidth) =
          (a + b) - Nat.pow 2 w.bitWidth :=
        nat_mod_sub_of_le_lt_double hOvf hDouble
      have hSubLtA : (a + b) - Nat.pow 2 w.bitWidth < a := by
        cases Nat.lt_or_ge ((a + b) - Nat.pow 2 w.bitWidth) a with
        | inl h => exact h
        | inr h =>
          have hAdd := Nat.add_le_add_right h (Nat.pow 2 w.bitWidth)
          rw [Nat.sub_add_cancel hOvf] at hAdd
          have hStrict : a + b < a + Nat.pow 2 w.bitWidth := Nat.add_lt_add_left hbLt a
          exact False.elim (Nat.not_lt_of_ge hAdd hStrict)
      have hRhsT : decide (((Nat.mod (a + b) (Nat.pow 2 w.bitWidth) : Nat) : Int) < (a : Int)) =
          true := by
        rw [hModSub]
        exact decide_eq_true ((int_ofNat_lt_ofNat_iff _ _).mpr hSubLtA)
      rw [hRhsT]
      cases Nat.lt_or_ge (a + b) (Nat.pow 2 128) with
      | inr hGe128 =>
        have hHostT : decide (((a + b : Nat) : Int) ≥ ((Nat.pow 2 128 : Nat) : Int)) = true :=
          decide_eq_true ((int_ofNat_le_ofNat_iff _ _).mpr hGe128)
        rw [hHostT]; rfl
      | inl hLt128 =>
        have hNe : truncateBits w (bvOfInt 128 ((a + b : Nat) : Int)) ≠
            bvOfInt 128 ((a + b : Nat) : Int) := by
          intro hEq
          have hNat := congrArg BitVec.toNat hEq
          rw [bvOfInt_natCast, truncateBits_ofNat_toNat, bitvec_ofNat_toNat,
              nat_mod_eq_of_lt hLt128] at hNat
          have hModLt := nat_mod_lt (a + b) (intWidth_pow2_pos w)
          rw [hNat] at hModLt
          exact Nat.not_lt_of_ge hOvf hModLt
        rw [bitvec_bne_true_of_ne hNe]
        cases decide (((a + b : Nat) : Int) ≥ ((Nat.pow 2 128 : Nat) : Int)) <;> rfl
  have hAddCast : (a : Int) + (b : Int) = ((a + b : Nat) : Int) := rfl
  change Except.ok (ScalarVal.mk w false (truncateBits w (bvOfInt 128 ((a : Int) + (b : Int)))),
      (decide ((a : Int) + (b : Int) < 0) ||
        decide ((a : Int) + (b : Int) ≥ HPow.hPow (2 : Int) 128) ||
        (truncateBits w (bvOfInt 128 ((a : Int) + (b : Int))) !=
          bvOfInt 128 ((a : Int) + (b : Int))))) =
    Except.ok (ScalarVal.mk w false (truncateBits w (bvOfInt 128 ((a : Int) + (b : Int)))),
      decide (decodeScalar (ScalarVal.mk w false (truncateBits w (bvOfInt 128 ((a : Int) + (b : Int))))) <
        (a : Int)))
  rw [hAddCast, hSumDec, hOvfEq]

private theorem int_natCast_sub_lt_zero_of_lt {a b : Nat} (h : a < b) :
    ((a : Int) - (b : Int)) < 0 := by
  cases b with
  | zero => exact False.elim (Nat.not_lt_zero a h)
  | succ b' =>
    have hPos : 0 < (b' + 1) - a := Nat.sub_pos_of_lt h
    have hEq : (b' + 1) - a = ((b' + 1) - a - 1) + 1 := (Nat.sub_add_cancel hPos).symm
    have hSub : ((a : Int) - ((b' + 1 : Nat) : Int)) = Int.negSucc ((b' + 1) - a - 1) := by
      change Int.subNatNat a (b' + 1) = Int.negSucc ((b' + 1) - a - 1)
      unfold Int.subNatNat
      rw [hEq]
      rfl
    rw [hSub]
    exact int_negSucc_lt_zero _

private theorem int_natCast_sub_eq_of_ge {a b : Nat} (h : b ≤ a) :
    ((a : Int) - (b : Int)) = ((a - b : Nat) : Int) := by
  cases b with
  | zero => rfl
  | succ b' =>
    change Int.subNatNat a (b' + 1) = Int.ofNat (a - (b' + 1))
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le h]

private theorem unsigned_subWithOverflow_eq (w : IntWidth) (lb rb : BitVec 128) :
    let l : ScalarVal := ⟨w, false, lb⟩
    let r : ScalarVal := ⟨w, false, rb⟩
    let raw := bvOfInt 128 (decodeScalar l - decodeScalar r)
    let diffSv : ScalarVal := ⟨w, false, truncateBits w raw⟩
    evalWithOverflowOp .subWithOverflow (.scalar l) (.scalar r) =
      .ok (diffSv, decide (decodeScalar l < decodeScalar r)) ∧
    evalBinOp .sub (.scalar l) (.scalar r) = .ok (.scalar diffSv) ∧
    evalBinOp .lt (.scalar l) (.scalar r) =
      .ok (.bool (decide (decodeScalar l < decodeScalar r))) ∧
    checkVal (.scalar diffSv) (.int w false) = true := by
  dsimp
  have hMatch : (IntWidth.beq w w && (false == false)) = true := by
    rw [intWidth_beq_refl w]; rfl
  have hSubOk : evalBinOp .sub (.scalar ⟨w, false, lb⟩) (.scalar ⟨w, false, rb⟩) =
      .ok (.scalar ⟨w, false, truncateBits w (bvOfInt 128
        (decodeScalar ⟨w, false, lb⟩ - decodeScalar ⟨w, false, rb⟩))⟩) := by
    unfold evalBinOp evalArithOp truncateScalar
    dsimp [BinOp.isShift, BinOp.isUnchecked]
    rw [hMatch]
    dsimp
    exact if_and_false_eq _ _ _
  have hLtOk : evalBinOp .lt (.scalar ⟨w, false, lb⟩) (.scalar ⟨w, false, rb⟩) =
      .ok (.bool (decide (decodeScalar ⟨w, false, lb⟩ < decodeScalar ⟨w, false, rb⟩))) := by
    unfold evalBinOp
    dsimp [BinOp.isShift]
    rw [hMatch]
    rfl
  have hCheckOk : checkVal (.scalar ⟨w, false, truncateBits w (bvOfInt 128
      (decodeScalar ⟨w, false, lb⟩ - decodeScalar ⟨w, false, rb⟩))⟩) (.int w false) = true := by
    unfold checkVal Val.ty?
    dsimp
    rw [scalarVal_wf_truncateBits]
    dsimp
    exact mirTy_beq_refl (.int w false)
  refine ⟨?_, hSubOk, hLtOk, hCheckOk⟩
  unfold evalWithOverflowOp truncateScalar
  dsimp
  rw [hMatch]
  dsimp
  let a := (truncateBits w lb).toNat
  let b := (truncateBits w rb).toNat
  have haLt : a < Nat.pow 2 w.bitWidth := by
    change (truncateBits w lb).toNat < Nat.pow 2 w.bitWidth
    rw [truncateBits_toNat]
    exact Nat.mod_lt lb.toNat (intWidth_pow2_pos w)
  have hOvfEq :
      (decide ((a : Int) - (b : Int) < 0) ||
        decide ((a : Int) - (b : Int) ≥ HPow.hPow (2 : Int) 128) ||
        (truncateBits w (bvOfInt 128 ((a : Int) - (b : Int))) !=
          bvOfInt 128 ((a : Int) - (b : Int)))) =
      decide ((a : Int) < (b : Int)) := by
    cases Nat.lt_or_ge a b with
    | inl hlt =>
      have hNegT : decide ((a : Int) - (b : Int) < 0) = true :=
        decide_eq_true (int_natCast_sub_lt_zero_of_lt hlt)
      have hRhsT : decide ((a : Int) < (b : Int)) = true :=
        decide_eq_true ((int_ofNat_lt_ofNat_iff _ _).mpr hlt)
      rw [hNegT, hRhsT]; rfl
    | inr hge =>
      have hPowCast : HPow.hPow (2 : Int) 128 = ((Nat.pow 2 128 : Nat) : Int) := rfl
      rw [int_natCast_sub_eq_of_ge hge, hPowCast]
      have hDiffLtW : a - b < Nat.pow 2 w.bitWidth :=
        Nat.lt_of_le_of_lt (Nat.sub_le a b) haLt
      have hDiffLt128 : a - b < Nat.pow 2 128 :=
        Nat.lt_of_lt_of_le hDiffLtW (intWidth_pow2_le_pow2_128 w)
      have hNotNeg : decide (((a - b : Nat) : Int) < 0) = false := by
        cases hD : decide (((a - b : Nat) : Int) < 0) with
        | false => rfl
        | true =>
          exact False.elim (Nat.not_lt_zero (a - b) ((int_ofNat_lt_ofNat_iff _ _).mp (of_decide_eq_true hD)))
      have hNotGe : decide (((a - b : Nat) : Int) ≥ ((Nat.pow 2 128 : Nat) : Int)) = false := by
        cases hD : decide (((a - b : Nat) : Int) ≥ ((Nat.pow 2 128 : Nat) : Int)) with
        | false => rfl
        | true =>
          exact False.elim (Nat.not_lt_of_ge ((int_ofNat_le_ofNat_iff _ _).mp (of_decide_eq_true hD)) hDiffLt128)
      have hTruncEq : truncateBits w (bvOfInt 128 ((a - b : Nat) : Int)) =
          bvOfInt 128 ((a - b : Nat) : Int) := by
        rw [bvOfInt_natCast]
        apply bitvec_eq_of_toNat_eq
        rw [truncateBits_ofNat_toNat, bitvec_ofNat_toNat,
            nat_mod_eq_of_lt hDiffLtW, nat_mod_eq_of_lt hDiffLt128]
      have hLossyF : (truncateBits w (bvOfInt 128 ((a - b : Nat) : Int)) !=
          bvOfInt 128 ((a - b : Nat) : Int)) = false :=
        bitvec_bne_false_of_eq hTruncEq
      have hRhsF : decide ((a : Int) < (b : Int)) = false := by
        cases hD : decide ((a : Int) < (b : Int)) with
        | false => rfl
        | true =>
          exact False.elim (Nat.not_lt_of_ge hge ((int_ofNat_lt_ofNat_iff _ _).mp (of_decide_eq_true hD)))
      rw [hNotNeg, hNotGe, hLossyF, hRhsF]; rfl
  change Except.ok (ScalarVal.mk w false (truncateBits w (bvOfInt 128 ((a : Int) - (b : Int)))),
      (decide ((a : Int) - (b : Int) < 0) ||
        decide ((a : Int) - (b : Int) ≥ HPow.hPow (2 : Int) 128) ||
        (truncateBits w (bvOfInt 128 ((a : Int) - (b : Int))) !=
          bvOfInt 128 ((a : Int) - (b : Int))))) =
    Except.ok (ScalarVal.mk w false (truncateBits w (bvOfInt 128 ((a : Int) - (b : Int)))),
      decide ((a : Int) < (b : Int)))
  rw [hOvfEq]

/-! #### Static Properties of `SroaCtx` -/

private structure SroaCtx where
  plan : SroaTuplePlan
  pSrc : Program
  pTgt : Program
  bodySrc : Body
  bodyTgt : Body
  fieldTys : List MirTy
  localsUpdated : List MirTy
  ovfTys : List MirTy
  bodiesTgt : List Body
  hGetSrc : Trusted.MirSemantics.getElem? pSrc.bodies plan.defId = some bodySrc
  hNonEmpty : bodySrc.basicBlocks.isEmpty = false
  hArgLt : bodySrc.argumentCount < plan.tupLocal
  hTupLt : plan.tupLocal < bodySrc.locals.length
  hInBounds : bodyAllLocalsInBounds bodySrc = true
  hTupTy : Trusted.MirSemantics.getElem? bodySrc.locals plan.tupLocal = some (.tuple fieldTys)
  hFlatTup : isFlatTupleTy (.tuple fieldTys) = true
  hUsesValid : bodyTupleUsesValid bodySrc plan.tupLocal fieldTys = true
  hOvfTys : ovfTys =
    if bodyHasTupleOvfAssign bodySrc plan.tupLocal then
      match unsignedOvfTupleWidth? fieldTys with
      | some w => [.int w false, .int w false]
      | none => []
    else []
  hSetLoc : setElem? bodySrc.locals plan.tupLocal .unit = some localsUpdated
  hBodyTgt : bodyTgt = {
    bodySrc with
    locals := localsUpdated ++ fieldTys ++ ovfTys
    basicBlocks := bodySrc.basicBlocks.map (fun bb => {
      statements :=
        listFlatMap
          (lowerSroaStmt plan.tupLocal fieldTys.length bodySrc.locals.length
            (bodySrc.locals.length + fieldTys.length))
          bb.statements
      terminator :=
        rewriteTupleTerminator plan.tupLocal bodySrc.locals.length bb.terminator
      cleanup := bb.cleanup
    })
  }
  hSetBody : setElem? pSrc.bodies plan.defId bodyTgt = some bodiesTgt
  hPTgt : pTgt = { pSrc with bodies := bodiesTgt }

private theorem extractSroaCtx {plan : SroaTuplePlan} {pSrc pTgt : Program}
    (h : applyMirSroaTuple plan pSrc = some pTgt) :
    ∃ ctx : SroaCtx, ctx.plan = plan ∧ ctx.pSrc = pSrc ∧ ctx.pTgt = pTgt := by
  unfold applyMirSroaTuple at h
  cases hGet : Trusted.MirSemantics.getElem? pSrc.bodies plan.defId with
  | none => rw [hGet] at h; cases h
  | some bodySrc =>
    rw [hGet] at h; dsimp at h
    cases hGuard1 : (bodySrc.basicBlocks.isEmpty ||
        !Nat.blt bodySrc.argumentCount plan.tupLocal ||
        !Nat.blt plan.tupLocal bodySrc.locals.length ||
        !bodyAllLocalsInBounds bodySrc) with
    | true => rw [hGuard1] at h; cases h
    | false =>
      rw [hGuard1] at h; dsimp at h
      let ⟨hG123, hNotIb⟩ := bool_or_false hGuard1
      let ⟨hG12, hNotTupLt⟩ := bool_or_false hG123
      let ⟨hNonEmpty, hNotArgLt⟩ := bool_or_false hG12
      have hArgLt := nat_blt_lt (bool_not_false hNotArgLt)
      have hTupLt := nat_blt_lt (bool_not_false hNotTupLt)
      have hInBounds := bool_not_false hNotIb
      cases hTy : Trusted.MirSemantics.getElem? bodySrc.locals plan.tupLocal with
      | none => rw [hTy] at h; cases h
      | some t =>
        rw [hTy] at h
        cases t with
        | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
          cases h
        | tuple fieldTys =>
          dsimp at h
          cases hGuard2 : (!isFlatTupleTy (.tuple fieldTys) ||
              !bodyTupleUsesValid bodySrc plan.tupLocal fieldTys) with
          | true => rw [hGuard2] at h; cases h
          | false =>
            rw [hGuard2] at h; dsimp at h
            let ⟨hNotFlat, hNotValid⟩ := bool_or_false hGuard2
            have hFlat := bool_not_false hNotFlat
            have hValid := bool_not_false hNotValid
            cases hSetL : setElem? bodySrc.locals plan.tupLocal .unit with
            | none => rw [hSetL] at h; cases h
            | some localsUpdated =>
              rw [hSetL] at h
              let ovfTys : List MirTy :=
                if bodyHasTupleOvfAssign bodySrc plan.tupLocal then
                  match unsignedOvfTupleWidth? fieldTys with
                  | some w => [.int w false, .int w false]
                  | none => []
                else []
              let bodyTgt : Body := {
                bodySrc with
                locals := localsUpdated ++ fieldTys ++ ovfTys
                basicBlocks := bodySrc.basicBlocks.map (fun bb => {
                  statements :=
                    listFlatMap
                      (lowerSroaStmt plan.tupLocal fieldTys.length bodySrc.locals.length
                        (bodySrc.locals.length + fieldTys.length))
                      bb.statements
                  terminator :=
                    rewriteTupleTerminator plan.tupLocal bodySrc.locals.length bb.terminator
                  cleanup := bb.cleanup
                })
              }
              change (match setElem? pSrc.bodies plan.defId bodyTgt with
                | none => none
                | some bodiesTgt => some { pSrc with bodies := bodiesTgt }) = some pTgt at h
              cases hSetB : setElem? pSrc.bodies plan.defId bodyTgt with
              | none => rw [hSetB] at h; cases h
              | some bodiesTgt =>
                rw [hSetB] at h
                injection h with hPEq
                refine ⟨{
                  plan := plan
                  pSrc := pSrc
                  pTgt := pTgt
                  bodySrc := bodySrc
                  bodyTgt := bodyTgt
                  fieldTys := fieldTys
                  localsUpdated := localsUpdated
                  ovfTys := ovfTys
                  bodiesTgt := bodiesTgt
                  hGetSrc := hGet
                  hNonEmpty := hNonEmpty
                  hArgLt := hArgLt
                  hTupLt := hTupLt
                  hInBounds := hInBounds
                  hTupTy := hTy
                  hFlatTup := hFlat
                  hUsesValid := hValid
                  hOvfTys := rfl
                  hSetLoc := hSetL
                  hBodyTgt := rfl
                  hSetBody := hSetB
                  hPTgt := hPEq.symm
                }, rfl, rfl, rfl⟩

private theorem sroaCtx_fieldCount_pos (ctx : SroaCtx) : 0 < ctx.fieldTys.length := by
  have hFl := ctx.hFlatTup
  unfold isFlatTupleTy at hFl
  let ⟨hNotEmp, _⟩ := bool_and_true hFl
  exact list_pos_of_isEmpty_false (bool_not_true hNotEmp)

private theorem sroaCtx_fieldTys_all_scalar (ctx : SroaCtx) :
    ctx.fieldTys.all isSupportedScalarOrUnitTy = true := by
  have hFl := ctx.hFlatTup
  unfold isFlatTupleTy at hFl
  exact (bool_and_true hFl).2

private theorem sroaCtx_tupLocal_pos (ctx : SroaCtx) : 0 < ctx.plan.tupLocal :=
  Nat.lt_of_le_of_lt (Nat.zero_le ctx.bodySrc.argumentCount) ctx.hArgLt

private theorem sroaCtx_tupLocal_ne_zero (ctx : SroaCtx) : ctx.plan.tupLocal ≠ 0 := by
  intro h
  have hPos := sroaCtx_tupLocal_pos ctx
  rw [h] at hPos
  exact Nat.not_lt_zero 0 hPos

private theorem sroaCtx_base_pos (ctx : SroaCtx) : 0 < ctx.bodySrc.locals.length :=
  Nat.lt_trans (sroaCtx_tupLocal_pos ctx) ctx.hTupLt

private theorem sroaCtx_localsUpdated_len (ctx : SroaCtx) :
    ctx.localsUpdated.length = ctx.bodySrc.locals.length :=
  setElem?_length ctx.hSetLoc

private theorem sroaCtx_localsTgt_len (ctx : SroaCtx) :
    ctx.bodyTgt.locals.length =
      ctx.bodySrc.locals.length + ctx.fieldTys.length + ctx.ovfTys.length := by
  rw [ctx.hBodyTgt]
  dsimp
  rw [list_append_length, list_append_length, sroaCtx_localsUpdated_len]

private theorem sroaCtx_localsTgt_getElem?_lt (ctx : SroaCtx) {i : Nat}
    (hLt : i < ctx.bodySrc.locals.length) (hNe : i ≠ ctx.plan.tupLocal) :
    Trusted.MirSemantics.getElem? ctx.bodyTgt.locals i =
      Trusted.MirSemantics.getElem? ctx.bodySrc.locals i := by
  rw [ctx.hBodyTgt]; dsimp
  have hLt1 : i < ctx.localsUpdated.length := by
    rw [sroaCtx_localsUpdated_len]; exact hLt
  have hLt2 : i < (ctx.localsUpdated ++ ctx.fieldTys).length := by
    rw [list_append_length]; exact nat_lt_add_right _ hLt1
  rw [getElem?_append_left _ _ i hLt2, getElem?_append_left _ _ i hLt1]
  exact setElem?_getElem?_ne ctx.hSetLoc hNe

private theorem sroaCtx_localsTgt_getElem?_field (ctx : SroaCtx) {j : Nat}
    (hLt : j < ctx.fieldTys.length) :
    Trusted.MirSemantics.getElem? ctx.bodyTgt.locals (ctx.bodySrc.locals.length + j) =
      Trusted.MirSemantics.getElem? ctx.fieldTys j := by
  rw [ctx.hBodyTgt]; dsimp
  have hLt2 : ctx.bodySrc.locals.length + j < (ctx.localsUpdated ++ ctx.fieldTys).length := by
    rw [list_append_length, sroaCtx_localsUpdated_len]
    exact Nat.add_lt_add_left hLt _
  rw [getElem?_append_left _ _ _ hLt2]
  rw [← sroaCtx_localsUpdated_len ctx]
  exact getElem?_append_right_add ctx.localsUpdated ctx.fieldTys j

private theorem sroaCtx_localsTgt_getElem?_ovf (ctx : SroaCtx)
    (hHas : bodyHasTupleOvfAssign ctx.bodySrc ctx.plan.tupLocal = true)
    {w : IntWidth} (hW : unsignedOvfTupleWidth? ctx.fieldTys = some w) :
    ctx.ovfTys = [.int w false, .int w false] ∧
    Trusted.MirSemantics.getElem? ctx.bodyTgt.locals
      (ctx.bodySrc.locals.length + ctx.fieldTys.length) = some (.int w false) ∧
    Trusted.MirSemantics.getElem? ctx.bodyTgt.locals
      (ctx.bodySrc.locals.length + ctx.fieldTys.length + 1) = some (.int w false) := by
  have hOvf : ctx.ovfTys = [.int w false, .int w false] := by
    rw [ctx.hOvfTys, hHas, hW]; rfl
  refine ⟨hOvf, ?_, ?_⟩
  · rw [ctx.hBodyTgt]; dsimp
    rw [hOvf]
    have hLen : (ctx.localsUpdated ++ ctx.fieldTys).length =
        ctx.bodySrc.locals.length + ctx.fieldTys.length := by
      rw [list_append_length, sroaCtx_localsUpdated_len]
    have h0 := getElem?_append_right_add (ctx.localsUpdated ++ ctx.fieldTys)
      [.int w false, .int w false] 0
    rw [hLen, Nat.add_zero] at h0
    exact h0
  · rw [ctx.hBodyTgt]; dsimp
    rw [hOvf]
    have hLen : (ctx.localsUpdated ++ ctx.fieldTys).length =
        ctx.bodySrc.locals.length + ctx.fieldTys.length := by
      rw [list_append_length, sroaCtx_localsUpdated_len]
    have h1 := getElem?_append_right_add (ctx.localsUpdated ++ ctx.fieldTys)
      [.int w false, .int w false] 1
    rw [hLen] at h1
    exact h1

private theorem mkStorageLivesLoop_any_marker (base start count id : Nat) :
    (mkStorageLivesLoop base start count).any (stmtHasStorageMarker id) =
      (Nat.ble (base + start) id && Nat.blt id (base + start + count)) := by
  induction count generalizing start with
  | zero =>
    dsimp [mkStorageLivesLoop, List.any]
    cases hLe : Nat.ble (base + start) id with
    | false => rfl
    | true =>
      rw [Bool.true_and]
      exact (nat_ge_blt_false (nat_ble_le hLe)).symm
  | succ k ih =>
    dsimp [mkStorageLivesLoop, List.any, stmtHasStorageMarker]
    rw [ih (start + 1)]
    have hAdd1 : base + (start + 1) = base + start + 1 := (Nat.add_assoc base start 1).symm
    have hAdd2 : base + (start + 1) + k = base + start + (k + 1) := by
      rw [hAdd1, Nat.add_assoc, Nat.add_comm 1 k]
    rw [hAdd2, hAdd1]
    cases hEq : Nat.beq (base + start) id with
    | true =>
      have hId := nat_beq_eq hEq
      subst hId
      dsimp [Bool.or]
      rw [nat_le_ble (Nat.le_refl _)]
      have hLt : base + start < base + start + (k + 1) := by
        rw [Nat.add_succ]
        exact Nat.lt_succ_of_le (Nat.le_add_right _ k)
      rw [nat_lt_blt hLt]; rfl
    | false =>
      have hNe := nat_ne_of_beq_false hEq
      dsimp [Bool.or]
      cases hLe : Nat.ble (base + start) id with
      | false =>
        have hGt : id < base + start := nat_ble_false_gt hLe
        have hGt1 : id < base + start + 1 := Nat.lt_succ_of_lt hGt
        rw [nat_gt_ble_false hGt1]
      | true =>
        have hGe : base + start ≤ id := nat_ble_le hLe
        have hLt : base + start < id := Nat.lt_of_le_of_ne hGe hNe
        rw [nat_le_ble hLt]

private theorem mkStorageDeadsLoop_any_marker (base start count id : Nat) :
    (mkStorageDeadsLoop base start count).any (stmtHasStorageMarker id) =
      (Nat.ble (base + start) id && Nat.blt id (base + start + count)) := by
  induction count generalizing start with
  | zero =>
    dsimp [mkStorageDeadsLoop, List.any]
    cases hLe : Nat.ble (base + start) id with
    | false => rfl
    | true =>
      rw [Bool.true_and]
      exact (nat_ge_blt_false (nat_ble_le hLe)).symm
  | succ k ih =>
    dsimp [mkStorageDeadsLoop, List.any, stmtHasStorageMarker]
    rw [ih (start + 1)]
    have hAdd1 : base + (start + 1) = base + start + 1 := (Nat.add_assoc base start 1).symm
    have hAdd2 : base + (start + 1) + k = base + start + (k + 1) := by
      rw [hAdd1, Nat.add_assoc, Nat.add_comm 1 k]
    rw [hAdd2, hAdd1]
    cases hEq : Nat.beq (base + start) id with
    | true =>
      have hId := nat_beq_eq hEq
      subst hId
      dsimp [Bool.or]
      rw [nat_le_ble (Nat.le_refl _)]
      have hLt : base + start < base + start + (k + 1) := by
        rw [Nat.add_succ]
        exact Nat.lt_succ_of_le (Nat.le_add_right _ k)
      rw [nat_lt_blt hLt]; rfl
    | false =>
      have hNe := nat_ne_of_beq_false hEq
      dsimp [Bool.or]
      cases hLe : Nat.ble (base + start) id with
      | false =>
        have hGt : id < base + start := nat_ble_false_gt hLe
        have hGt1 : id < base + start + 1 := Nat.lt_succ_of_lt hGt
        rw [nat_gt_ble_false hGt1]
      | true =>
        have hGe : base + start ≤ id := nat_ble_le hLe
        have hLt : base + start < id := Nat.lt_of_le_of_ne hGe hNe
        rw [nat_le_ble hLt]

private theorem mkIndexedUseAssignsLoop_any_marker (dstBase start : Nat)
    (ops : List Operand) (id : Nat) :
    (mkIndexedUseAssignsLoop dstBase start ops).any (stmtHasStorageMarker id) = false := by
  induction ops generalizing start with
  | nil => rfl
  | cons _ _ ih =>
    dsimp [mkIndexedUseAssignsLoop, List.any, stmtHasStorageMarker]
    exact ih (start + 1)

private theorem lowerSroaStmt_any_marker_lt {tupLocal fieldCount base ovfTmpBase id : Nat}
    (hOvfGe : base + fieldCount ≤ ovfTmpBase)
    (hIdLt : id < base) (hIdNe : id ≠ tupLocal) (stmt : StatementKind) :
    (lowerSroaStmt tupLocal fieldCount base ovfTmpBase stmt).any
      (stmtHasStorageMarker id) = stmtHasStorageMarker id stmt := by
  have hNotInField : (Nat.ble (base + 0) id && Nat.blt id (base + 0 + fieldCount)) = false := by
    rw [Nat.add_zero, nat_gt_ble_false hIdLt]; rfl
  have hNeOvf0 : Nat.beq ovfTmpBase id = false :=
    nat_beq_false_of_ne (fun h =>
      Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right base fieldCount) hOvfGe) (h ▸ hIdLt))
  have hNeOvf1 : Nat.beq (ovfTmpBase + 1) id = false :=
    nat_beq_false_of_ne (fun h => by
      have hIdLt' := hIdLt
      rw [← h] at hIdLt'
      exact Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right base fieldCount)
        (Nat.le_trans hOvfGe (Nat.le_succ ovfTmpBase))) hIdLt')
  cases stmt with
  | nop | unsupported => rfl
  | storageLive lid =>
    dsimp [lowerSroaStmt]
    cases hEq : Nat.beq lid tupLocal with
    | true =>
      have hLid := nat_beq_eq hEq; subst hLid
      dsimp
      rw [mkStorageLivesLoop_any_marker, hNotInField]
      dsimp [stmtHasStorageMarker]
      exact (nat_beq_false_of_ne (fun h => hIdNe h.symm)).symm
    | false =>
      dsimp [List.any, stmtHasStorageMarker]
      cases Nat.beq lid id <;> rfl
  | storageDead lid =>
    dsimp [lowerSroaStmt]
    cases hEq : Nat.beq lid tupLocal with
    | true =>
      have hLid := nat_beq_eq hEq; subst hLid
      dsimp
      rw [mkStorageDeadsLoop_any_marker, hNotInField]
      dsimp [stmtHasStorageMarker]
      exact (nat_beq_false_of_ne (fun h => hIdNe h.symm)).symm
    | false =>
      dsimp [List.any, stmtHasStorageMarker]
      cases Nat.beq lid id <;> rfl
  | assign dst rv =>
    dsimp [lowerSroaStmt]
    cases Nat.beq dst.localId tupLocal with
    | false => rfl
    | true =>
      dsimp
      cases dst.projection with
      | nil =>
        cases rv with
        | aggregateTuple ops =>
          exact mkIndexedUseAssignsLoop_any_marker base 0 _ id
        | binaryOp op _ _ =>
          cases op with
          | addWithOverflow | subWithOverflow =>
            dsimp [List.any, stmtHasStorageMarker]
            rw [hNeOvf0, hNeOvf1]; rfl
          | add | addUnchecked | sub | subUnchecked | mul | mulUnchecked
          | mulWithOverflow | div | rem | bitXor | bitAnd | bitOr
          | shl | shlUnchecked | shr | shrUnchecked | eq | lt | le
          | ne | ge | gt | offset => rfl
        | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _ | unsupported => rfl
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> rfl
        | nil => cases pe <;> rfl

private theorem lowerSroaStmt_any_marker_field {tupLocal fieldCount base ovfTmpBase j : Nat}
    (hOvfGe : base + fieldCount ≤ ovfTmpBase)
    (hJLt : j < fieldCount) (stmt : StatementKind)
    (hStmtLt : stmtLocalsLt base stmt = true) :
    (lowerSroaStmt tupLocal fieldCount base ovfTmpBase stmt).any
      (stmtHasStorageMarker (base + j)) = stmtHasStorageMarker tupLocal stmt := by
  have hInField :
      (Nat.ble (base + 0) (base + j) && Nat.blt (base + j) (base + 0 + fieldCount)) = true := by
    rw [Nat.add_zero]
    exact bool_and_intro (nat_le_ble (Nat.le_add_right base j))
      (nat_lt_blt (Nat.add_lt_add_left hJLt base))
  have hLtOvf : base + j < ovfTmpBase :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hJLt base) hOvfGe
  have hNeOvf0 : Nat.beq ovfTmpBase (base + j) = false :=
    nat_beq_false_of_ne (fun h => Nat.not_lt_of_ge (Nat.le_refl _) (h ▸ hLtOvf))
  have hNeOvf1 : Nat.beq (ovfTmpBase + 1) (base + j) = false :=
    nat_beq_false_of_ne (fun h => by
      have hLtOvf' := hLtOvf
      rw [← h] at hLtOvf'
      exact Nat.not_lt_of_ge (Nat.le_succ ovfTmpBase) hLtOvf')
  cases stmt with
  | nop | unsupported => rfl
  | storageLive lid =>
    dsimp [stmtLocalsLt] at hStmtLt
    have hLidLt := nat_blt_lt hStmtLt
    dsimp [lowerSroaStmt, stmtHasStorageMarker]
    cases hEq : Nat.beq lid tupLocal with
    | true =>
      dsimp
      rw [mkStorageLivesLoop_any_marker, hInField]
    | false =>
      dsimp [List.any, stmtHasStorageMarker]
      have hNe : lid ≠ base + j := fun h =>
        Nat.not_lt_of_ge (Nat.le_add_right base j) (h ▸ hLidLt)
      rw [nat_beq_false_of_ne hNe]; rfl
  | storageDead lid =>
    dsimp [stmtLocalsLt] at hStmtLt
    have hLidLt := nat_blt_lt hStmtLt
    dsimp [lowerSroaStmt, stmtHasStorageMarker]
    cases hEq : Nat.beq lid tupLocal with
    | true =>
      dsimp
      rw [mkStorageDeadsLoop_any_marker, hInField]
    | false =>
      dsimp [List.any, stmtHasStorageMarker]
      have hNe : lid ≠ base + j := fun h =>
        Nat.not_lt_of_ge (Nat.le_add_right base j) (h ▸ hLidLt)
      rw [nat_beq_false_of_ne hNe]; rfl
  | assign dst rv =>
    dsimp [lowerSroaStmt, stmtHasStorageMarker]
    cases Nat.beq dst.localId tupLocal with
    | false => rfl
    | true =>
      dsimp
      cases dst.projection with
      | nil =>
        cases rv with
        | aggregateTuple ops =>
          exact mkIndexedUseAssignsLoop_any_marker base 0 _ (base + j)
        | binaryOp op _ _ =>
          cases op with
          | addWithOverflow | subWithOverflow =>
            dsimp [List.any, stmtHasStorageMarker]
            rw [hNeOvf0, hNeOvf1]; rfl
          | add | addUnchecked | sub | subUnchecked | mul | mulUnchecked
          | mulWithOverflow | div | rem | bitXor | bitAnd | bitOr
          | shl | shlUnchecked | shr | shrUnchecked | eq | lt | le
          | ne | ge | gt | offset => rfl
        | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _ | unsupported => rfl
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> rfl
        | nil => cases pe <;> rfl

private theorem list_any_congr_getElem? {α : Type} {p q : α → Bool} {xs : List α}
    (hAt : ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = q x) :
    xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    dsimp [List.any]
    rw [hAt 0 a rfl, ih (fun i x h => hAt (i + 1) x h)]

private theorem sroaCtx_hasStorageAnnotation_lt (ctx : SroaCtx) {i : Nat}
    (hLt : i < ctx.bodySrc.locals.length) (hNe : i ≠ ctx.plan.tupLocal) :
    hasStorageAnnotation ctx.bodyTgt i = hasStorageAnnotation ctx.bodySrc i := by
  unfold hasStorageAnnotation
  rw [ctx.hBodyTgt]; dsimp
  rw [list_any_map]
  apply list_any_congr_getElem?
  intro _ bb h1
  dsimp
  rw [list_any_listFlatMap]
  apply list_any_congr_getElem?
  intro _ s1 _
  exact lowerSroaStmt_any_marker_lt (Nat.le_refl _) hLt hNe s1

private theorem sroaCtx_hasStorageAnnotation_field (ctx : SroaCtx) {j : Nat}
    (hJLt : j < ctx.fieldTys.length) :
    hasStorageAnnotation ctx.bodyTgt (ctx.bodySrc.locals.length + j) =
      hasStorageAnnotation ctx.bodySrc ctx.plan.tupLocal := by
  unfold hasStorageAnnotation
  rw [ctx.hBodyTgt]; dsimp
  rw [list_any_map]
  apply list_any_congr_getElem?
  intro _ bb h1
  dsimp
  rw [list_any_listFlatMap]
  have hBbIb := list_all_getElem? ctx.hInBounds h1
  let ⟨hStmtsIb, _⟩ := bool_and_true hBbIb
  apply list_any_congr_getElem?
  intro _ s1 hs1
  have hS1Ib := list_all_getElem? hStmtsIb hs1
  exact lowerSroaStmt_any_marker_field (Nat.le_refl _) hJLt s1 hS1Ib

private theorem sroaCtx_storageAnnotationsInBounds_src (ctx : SroaCtx) :
    storageAnnotationsInBounds ctx.bodySrc = true := by
  unfold storageAnnotationsInBounds
  apply list_all_of_forall_getElem?
  intro bi bb hBb
  have hBbIb := list_all_getElem? ctx.hInBounds hBb
  let ⟨hStmtsIb, _⟩ := bool_and_true hBbIb
  apply list_all_of_forall_getElem?
  intro si stmt hStmt
  have hSIb := list_all_getElem? hStmtsIb hStmt
  cases stmt with
  | storageLive id | storageDead id => exact hSIb
  | assign _ _ | nop | unsupported => rfl

private theorem mkStorageLivesLoop_inBounds (base start count bound : Nat)
    (hLe : base + start + count ≤ bound) :
    (mkStorageLivesLoop base start count).all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id bound
      | _ => true) = true := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    dsimp [mkStorageLivesLoop, List.all]
    have hLt : base + start < bound := by
      have h1 : base + start + 1 ≤ base + start + (k + 1) :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) _
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans h1 hLe)
    rw [nat_lt_blt hLt, Bool.true_and]
    have hNext : base + (start + 1) + k ≤ bound := by
      have hEq : base + (start + 1) + k = base + start + (k + 1) := by
        rw [← Nat.add_assoc base start 1, Nat.add_assoc, Nat.add_comm 1 k]
      rw [hEq]; exact hLe
    exact ih (start + 1) hNext

private theorem mkStorageDeadsLoop_inBounds (base start count bound : Nat)
    (hLe : base + start + count ≤ bound) :
    (mkStorageDeadsLoop base start count).all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id bound
      | _ => true) = true := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    dsimp [mkStorageDeadsLoop, List.all]
    have hLt : base + start < bound := by
      have h1 : base + start + 1 ≤ base + start + (k + 1) :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) _
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans h1 hLe)
    rw [nat_lt_blt hLt, Bool.true_and]
    have hNext : base + (start + 1) + k ≤ bound := by
      have hEq : base + (start + 1) + k = base + start + (k + 1) := by
        rw [← Nat.add_assoc base start 1, Nat.add_assoc, Nat.add_comm 1 k]
      rw [hEq]; exact hLe
    exact ih (start + 1) hNext

private theorem mkIndexedUseAssignsLoop_inBounds (dstBase start : Nat)
    (ops : List Operand) (bound : Nat) :
    (mkIndexedUseAssignsLoop dstBase start ops).all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id bound
      | _ => true) = true := by
  induction ops generalizing start with
  | nil => rfl
  | cons _ _ ih =>
    dsimp [mkIndexedUseAssignsLoop, List.all]
    exact ih (start + 1)

private theorem sroaCtx_storageAnnotationsInBounds_tgt (ctx : SroaCtx) :
    storageAnnotationsInBounds ctx.bodyTgt = true := by
  unfold storageAnnotationsInBounds
  rw [sroaCtx_localsTgt_len ctx]
  rw [ctx.hBodyTgt]; dsimp
  rw [list_all_map]
  apply list_all_of_forall_getElem?
  intro bi bb hBb
  dsimp
  rw [list_all_listFlatMap]
  have hBbIb := list_all_getElem? ctx.hInBounds hBb
  let ⟨hStmtsIb, _⟩ := bool_and_true hBbIb
  have hBbVal := list_all_getElem? ctx.hUsesValid hBb
  let ⟨hStmtsVal, _⟩ := bool_and_true hBbVal
  apply list_all_of_forall_getElem?
  intro si stmt hStmt
  have hSIb := list_all_getElem? hStmtsIb hStmt
  have hSVal := list_all_getElem? hStmtsVal hStmt
  cases stmt with
  | nop | unsupported => rfl
  | storageLive id =>
    dsimp [lowerSroaStmt]
    cases Nat.beq id ctx.plan.tupLocal with
    | true =>
      dsimp
      apply mkStorageLivesLoop_inBounds
      rw [Nat.add_zero]
      exact Nat.le_add_right _ _
    | false =>
      dsimp [List.all]
      have hLt : id < ctx.bodySrc.locals.length := nat_blt_lt hSIb
      rw [nat_lt_blt (nat_lt_add_right _ (nat_lt_add_right _ hLt))]; rfl
  | storageDead id =>
    dsimp [lowerSroaStmt]
    cases Nat.beq id ctx.plan.tupLocal with
    | true =>
      dsimp
      apply mkStorageDeadsLoop_inBounds
      rw [Nat.add_zero]
      exact Nat.le_add_right _ _
    | false =>
      dsimp [List.all]
      have hLt : id < ctx.bodySrc.locals.length := nat_blt_lt hSIb
      rw [nat_lt_blt (nat_lt_add_right _ (nat_lt_add_right _ hLt))]; rfl
  | assign dst rv =>
    cases dst with
    | mk dstId dstProj =>
      dsimp [lowerSroaStmt]
      cases hEq : Nat.beq dstId ctx.plan.tupLocal with
      | false => rfl
      | true =>
        dsimp
        cases dstProj with
        | cons pe rest =>
          cases rest with
          | cons _ _ => cases pe <;> rfl
          | nil => cases pe <;> rfl
        | nil =>
          cases rv with
          | aggregateTuple ops =>
            exact mkIndexedUseAssignsLoop_inBounds _ 0 _ _
          | binaryOp op lhs rhs =>
            cases op with
            | addWithOverflow | subWithOverflow =>
              have hHasOvf : bodyHasTupleOvfAssign ctx.bodySrc ctx.plan.tupLocal = true := by
                unfold bodyHasTupleOvfAssign
                apply list_any_true_of_getElem? hBb
                apply list_any_true_of_getElem? hStmt
                dsimp
                rw [hEq]; rfl
              dsimp [stmtTupleValid] at hSVal
              rw [hEq] at hSVal
              dsimp [isSroaLowerableOvfBinOp] at hSVal
              cases hW : unsignedOvfTupleWidth? ctx.fieldTys with
              | none => rw [hW] at hSVal; cases hSVal
              | some w =>
                have hOvfEq : ctx.ovfTys = [.int w false, .int w false] := by
                  rw [ctx.hOvfTys, hHasOvf, hW]; rfl
                rw [hOvfEq]
                dsimp [List.all, List.length]
                have hLt0 : ctx.bodySrc.locals.length + ctx.fieldTys.length <
                    ctx.bodySrc.locals.length + ctx.fieldTys.length + 2 := by
                  exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
                have hLt1 : ctx.bodySrc.locals.length + ctx.fieldTys.length + 1 <
                    ctx.bodySrc.locals.length + ctx.fieldTys.length + 2 :=
                  Nat.lt_succ_self _
                rw [nat_lt_blt hLt0, nat_lt_blt hLt1]; rfl
            | add | addUnchecked | sub | subUnchecked | mul | mulUnchecked
            | mulWithOverflow | div | rem | bitXor | bitAnd | bitOr
            | shl | shlUnchecked | shr | shrUnchecked | eq | lt | le
            | ne | ge | gt | offset => rfl
          | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _ | unsupported => rfl

private theorem sroaCtx_allSupported_eq (ctx : SroaCtx) :
    ctx.bodyTgt.locals.all isSupportedTupleOrScalarTy =
      ctx.bodySrc.locals.all isSupportedTupleOrScalarTy := by
  have hFieldsSup : ctx.fieldTys.all isSupportedTupleOrScalarTy = true :=
    list_all_of_forall_getElem? (fun _ ty hTy =>
      isSupportedTupleOrScalarTy_of_scalar (list_all_getElem? (sroaCtx_fieldTys_all_scalar ctx) hTy))
  have hOvfSup : ctx.ovfTys.all isSupportedTupleOrScalarTy = true := by
    rw [ctx.hOvfTys]
    cases bodyHasTupleOvfAssign ctx.bodySrc ctx.plan.tupLocal with
    | false => rfl
    | true =>
      dsimp
      cases unsignedOvfTupleWidth? ctx.fieldTys with
      | none => rfl
      | some _ => rfl
  have hSrcTupSup : isSupportedTupleOrScalarTy (.tuple ctx.fieldTys) = true := by
    unfold isSupportedTupleOrScalarTy
    rw [ctx.hFlatTup]; cases isSupportedScalarOrUnitTy (.tuple ctx.fieldTys) <;> rfl
  have hLocUpdEq : ctx.localsUpdated.all isSupportedTupleOrScalarTy =
      ctx.bodySrc.locals.all isSupportedTupleOrScalarTy := by
    cases hSrc : ctx.bodySrc.locals.all isSupportedTupleOrScalarTy with
    | true =>
      apply list_all_of_forall_getElem?
      intro i ty hTy
      cases hEq : Nat.beq i ctx.plan.tupLocal with
      | true =>
        have hi := nat_beq_eq hEq; subst hi
        rw [setElem?_getElem?_same ctx.hSetLoc] at hTy
        injection hTy with hU; subst hU; rfl
      | false =>
        rw [setElem?_getElem?_ne ctx.hSetLoc (nat_ne_of_beq_false hEq)] at hTy
        exact list_all_getElem? hSrc hTy
    | false =>
      cases hUpd : ctx.localsUpdated.all isSupportedTupleOrScalarTy with
      | false => rfl
      | true =>
        have hSrcT : ctx.bodySrc.locals.all isSupportedTupleOrScalarTy = true := by
          apply list_all_of_forall_getElem?
          intro i ty hTy
          cases hEq : Nat.beq i ctx.plan.tupLocal with
          | true =>
            have hi := nat_beq_eq hEq; subst hi
            rw [ctx.hTupTy] at hTy
            injection hTy with hEqT; subst hEqT
            exact hSrcTupSup
          | false =>
            have hGet := setElem?_getElem?_ne ctx.hSetLoc (nat_ne_of_beq_false hEq)
            rw [hTy] at hGet
            exact list_all_getElem? hUpd hGet
        rw [hSrcT] at hSrc; cases hSrc
  rw [ctx.hBodyTgt]; dsimp
  rw [list_all_append, list_all_append, hLocUpdEq, hFieldsSup, hOvfSup]
  cases ctx.bodySrc.locals.all isSupportedTupleOrScalarTy <;> rfl

private theorem sroaCtx_paramTys_eq (ctx : SroaCtx) :
    (ctx.bodyTgt.locals.drop 1).take ctx.bodyTgt.argumentCount =
      (ctx.bodySrc.locals.drop 1).take ctx.bodySrc.argumentCount := by
  have hArgEq : ctx.bodyTgt.argumentCount = ctx.bodySrc.argumentCount := by
    rw [ctx.hBodyTgt]
  rw [hArgEq]
  have hArgLtSrc : ctx.bodySrc.argumentCount < ctx.bodySrc.locals.length :=
    Nat.lt_trans ctx.hArgLt ctx.hTupLt
  have hArgLtTgt : ctx.bodySrc.argumentCount < ctx.bodyTgt.locals.length := by
    rw [sroaCtx_localsTgt_len ctx]
    exact nat_lt_add_right _ (nat_lt_add_right _ hArgLtSrc)
  have hLenSrc : ((ctx.bodySrc.locals.drop 1).take ctx.bodySrc.argumentCount).length =
      ctx.bodySrc.argumentCount := by
    apply list_take_length_eq
    rw [drop_length_eq]
    exact Nat.le_sub_of_add_le hArgLtSrc
  have hLenTgt : ((ctx.bodyTgt.locals.drop 1).take ctx.bodySrc.argumentCount).length =
      ctx.bodySrc.argumentCount := by
    apply list_take_length_eq
    rw [drop_length_eq]
    exact Nat.le_sub_of_add_le hArgLtTgt
  apply list_eq_of_getElem?_eq (by rw [hLenTgt, hLenSrc])
  intro i
  cases Nat.lt_or_ge i ctx.bodySrc.argumentCount with
  | inr hge =>
    rw [getElem?_none_of_ge (by rw [hLenTgt]; exact hge),
        getElem?_none_of_ge (by rw [hLenSrc]; exact hge)]
  | inl hlt =>
    rw [getElem?_take_drop1 _ _ _ hlt, getElem?_take_drop1 _ _ _ hlt]
    have hLtBase : i + 1 < ctx.bodySrc.locals.length :=
      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hlt) (Nat.lt_trans ctx.hArgLt ctx.hTupLt)
    have hNeTup : i + 1 ≠ ctx.plan.tupLocal := fun hEq => by
      have hArgLt' := ctx.hArgLt
      rw [← hEq] at hArgLt'
      exact Nat.not_lt_of_ge (Nat.succ_le_of_lt hlt) hArgLt'
    exact sroaCtx_localsTgt_getElem?_lt ctx hLtBase hNeTup

private theorem sroaCtx_bodyStaticAdmitted_eq (ctx : SroaCtx) :
    BodyStaticAdmittedTupleAssert ctx.pTgt ctx.bodyTgt =
      BodyStaticAdmittedTupleAssert ctx.pSrc ctx.bodySrc := by
  unfold BodyStaticAdmittedTupleAssert
  have hPw : ctx.pTgt.pointerWidthBits = ctx.pSrc.pointerWidthBits := by rw [ctx.hPTgt]
  have hVer : ctx.pTgt.mirProfileVersion = ctx.pSrc.mirProfileVersion := by rw [ctx.hPTgt]
  have hId : ctx.bodyTgt.identity = ctx.bodySrc.identity := by rw [ctx.hBodyTgt]
  have hArg : ctx.bodyTgt.argumentCount = ctx.bodySrc.argumentCount := by rw [ctx.hBodyTgt]
  have hEmp : ctx.bodyTgt.basicBlocks.isEmpty = ctx.bodySrc.basicBlocks.isEmpty := by
    rw [ctx.hBodyTgt]; dsimp
    exact list_isEmpty_eq_of_length (map_length_eq _ _)
  have hArgLtS : Nat.blt ctx.bodySrc.argumentCount ctx.bodySrc.locals.length = true :=
    nat_lt_blt (Nat.lt_trans ctx.hArgLt ctx.hTupLt)
  have hArgLtT : Nat.blt ctx.bodyTgt.argumentCount ctx.bodyTgt.locals.length = true := by
    rw [hArg, sroaCtx_localsTgt_len ctx]
    exact nat_lt_blt (nat_lt_add_right _ (nat_lt_add_right _ (Nat.lt_trans ctx.hArgLt ctx.hTupLt)))
  rw [hPw, hVer, hId, hEmp, hArgLtS, hArgLtT,
      sroaCtx_storageAnnotationsInBounds_src ctx,
      sroaCtx_storageAnnotationsInBounds_tgt ctx,
      sroaCtx_allSupported_eq ctx]

/-! #### Simulation Relation `SroaRelLocals` & `SroaRelState` -/

private noncomputable def SroaRelLocals (tupLocal base : Nat)
    (fieldTys ovfTys : List MirTy)
    (lsSrc lsTgt : List LocalSlotExt) : Prop :=
  lsSrc.length = base ∧
  lsTgt.length = base + fieldTys.length + ovfTys.length ∧
  (∀ i, i < base → i ≠ tupLocal →
    Trusted.MirSemantics.getElem? lsTgt i = Trusted.MirSemantics.getElem? lsSrc i) ∧
  (match Trusted.MirSemantics.getElem? lsSrc tupLocal with
   | some .dead =>
     ∀ j, j < fieldTys.length →
       Trusted.MirSemantics.getElem? lsTgt (base + j) = some .dead
   | some (.liveTuple fields) =>
     fields.length = fieldTys.length ∧
     ∀ j, j < fieldTys.length →
       Trusted.MirSemantics.getElem? lsTgt (base + j) =
         (Trusted.MirSemantics.getElem? fields j).map LocalSlotExt.liveBase
   | _ => False)

private noncomputable def sroaStmtOffset (ctx : SroaCtx) (bbSrc : BasicBlock)
    (stmtIdx : Nat) : Nat :=
  (listFlatMap
    (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length ctx.bodySrc.locals.length
      (ctx.bodySrc.locals.length + ctx.fieldTys.length))
    (bbSrc.statements.take stmtIdx)).length

private noncomputable def SroaRelState (ctx : SroaCtx) (sSrc sTgt : StateExt) : Prop :=
  sSrc.callerMem = sTgt.callerMem ∧
  ∃ fSrc fTgt,
    sSrc.frames = [fSrc] ∧
    sTgt.frames = [fTgt] ∧
    fSrc.defId = ctx.plan.defId ∧
    fTgt.defId = ctx.plan.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    ctx.bodySrc.locals.all isSupportedTupleOrScalarTy = true ∧
    LocalsWellTyped ctx.bodySrc.locals fSrc.locals ∧
    SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length ctx.fieldTys ctx.ovfTys
      fSrc.locals fTgt.locals ∧
    (∀ bbSrc,
      Trusted.MirSemantics.getElem? ctx.bodySrc.basicBlocks fSrc.blockIdx = some bbSrc →
      fSrc.stmtIdx ≤ bbSrc.statements.length ∧
      fTgt.stmtIdx = sroaStmtOffset ctx bbSrc fSrc.stmtIdx)

private theorem sroaRelLocals_set_ne {tupLocal base : Nat}
    {fieldTys ovfTys : List MirTy} {lsSrc lsTgt lsSrc' lsTgt' : List LocalSlotExt}
    {id : Nat} {slot : LocalSlotExt}
    (hRel : SroaRelLocals tupLocal base fieldTys ovfTys lsSrc lsTgt)
    (hLt : id < base) (hNe : id ≠ tupLocal)
    (hSetS : setElem? lsSrc id slot = some lsSrc')
    (hSetT : setElem? lsTgt id slot = some lsTgt') :
    SroaRelLocals tupLocal base fieldTys ovfTys lsSrc' lsTgt' := by
  let ⟨hLenS, hLenT, hAtLt, hTup⟩ := hRel
  refine ⟨by rw [setElem?_length hSetS, hLenS],
          by rw [setElem?_length hSetT, hLenT], ?_, ?_⟩
  · intro i hi hINe
    cases hEq : Nat.beq i id with
    | true =>
      have hId := nat_beq_eq hEq; subst hId
      rw [setElem?_getElem?_same hSetT, setElem?_getElem?_same hSetS]
    | false =>
      have hNeId := nat_ne_of_beq_false hEq
      rw [setElem?_getElem?_ne hSetT hNeId, setElem?_getElem?_ne hSetS hNeId]
      exact hAtLt i hi hINe
  · rw [setElem?_getElem?_ne hSetS (fun h => hNe h.symm)]
    cases hSrcT : Trusted.MirSemantics.getElem? lsSrc tupLocal with
    | none => rw [hSrcT] at hTup; exact hTup
    | some sl =>
      rw [hSrcT] at hTup
      cases sl with
      | liveBase _ => exact hTup
      | dead =>
        intro j hJLt
        rw [setElem?_getElem?_ne hSetT (nat_ne_add_left_of_lt hLt)]
        exact hTup j hJLt
      | liveTuple fields =>
        refine ⟨hTup.1, ?_⟩
        intro j hJLt
        rw [setElem?_getElem?_ne hSetT (nat_ne_add_left_of_lt hLt)]
        exact hTup.2 j hJLt

private theorem sroaRelLocals_set_ovf {tupLocal base : Nat}
    {fieldTys ovfTys : List MirTy} {lsSrc lsTgt lsTgt' : List LocalSlotExt}
    {idx : Nat} {slot : LocalSlotExt}
    (hRel : SroaRelLocals tupLocal base fieldTys ovfTys lsSrc lsTgt)
    (hGe : base + fieldTys.length ≤ idx)
    (hSetT : setElem? lsTgt idx slot = some lsTgt') :
    SroaRelLocals tupLocal base fieldTys ovfTys lsSrc lsTgt' := by
  let ⟨hLenS, hLenT, hAtLt, hTup⟩ := hRel
  refine ⟨hLenS, by rw [setElem?_length hSetT, hLenT], ?_, ?_⟩
  · intro i hi hINe
    have hNe : i ≠ idx := fun h =>
      Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right base fieldTys.length) hGe) (h ▸ hi)
    rw [setElem?_getElem?_ne hSetT hNe]
    exact hAtLt i hi hINe
  · cases hSrcT : Trusted.MirSemantics.getElem? lsSrc tupLocal with
    | none => rw [hSrcT] at hTup; exact hTup
    | some sl =>
      rw [hSrcT] at hTup
      cases sl with
      | liveBase _ => exact hTup
      | dead =>
        intro j hJLt
        have hNe : base + j ≠ idx := fun h =>
          Nat.not_lt_of_ge hGe (h ▸ Nat.add_lt_add_left hJLt base)
        rw [setElem?_getElem?_ne hSetT hNe]
        exact hTup j hJLt
      | liveTuple fields =>
        refine ⟨hTup.1, ?_⟩
        intro j hJLt
        have hNe : base + j ≠ idx := fun h =>
          Nat.not_lt_of_ge hGe (h ▸ Nat.add_lt_add_left hJLt base)
        rw [setElem?_getElem?_ne hSetT hNe]
        exact hTup.2 j hJLt

private theorem sroaRelLocals_set_field {tupLocal base : Nat}
    {fieldTys ovfTys : List MirTy} {lsSrc lsTgt lsSrc' lsTgt' : List LocalSlotExt}
    {fields fields' : List (Option Val)} {idx : Nat} {optV : Option Val}
    (hRel : SroaRelLocals tupLocal base fieldTys ovfTys lsSrc lsTgt)
    (hSrcT : Trusted.MirSemantics.getElem? lsSrc tupLocal = some (.liveTuple fields))
    (hIdxLt : idx < fieldTys.length)
    (hSetF : setElem? fields idx optV = some fields')
    (hSetS : setElem? lsSrc tupLocal (.liveTuple fields') = some lsSrc')
    (hSetT : setElem? lsTgt (base + idx) (.liveBase optV) = some lsTgt') :
    SroaRelLocals tupLocal base fieldTys ovfTys lsSrc' lsTgt' := by
  let ⟨hLenS, hLenT, hAtLt, hTup⟩ := hRel
  rw [hSrcT] at hTup
  refine ⟨by rw [setElem?_length hSetS, hLenS],
          by rw [setElem?_length hSetT, hLenT], ?_, ?_⟩
  · intro i hi hINe
    have hNeT : i ≠ base + idx := fun h =>
      Nat.not_lt_of_ge (Nat.le_add_right base idx) (h ▸ hi)
    rw [setElem?_getElem?_ne hSetT hNeT, setElem?_getElem?_ne hSetS hINe]
    exact hAtLt i hi hINe
  · rw [setElem?_getElem?_same hSetS]
    refine ⟨by rw [setElem?_length hSetF, hTup.1], ?_⟩
    intro j hJLt
    cases hEq : Nat.beq j idx with
    | true =>
      have hj := nat_beq_eq hEq; subst hj
      rw [setElem?_getElem?_same hSetT, setElem?_getElem?_same hSetF]; rfl
    | false =>
      have hNe := nat_ne_of_beq_false hEq
      have hNeBase : base + j ≠ base + idx := fun h => hNe (Nat.add_left_cancel h)
      rw [setElem?_getElem?_ne hSetT hNeBase, setElem?_getElem?_ne hSetF hNe]
      exact hTup.2 j hJLt

/-! #### Operand, Rvalue, & Write Simulation Lemmas -/

private theorem sroa_evalOperandToSlotExt_sim (ctx : SroaCtx)
    {lsSrc lsTgt : List LocalSlotExt} {opnd : Operand}
    (hRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys lsSrc lsTgt)
    (hOpLt : operandLocalsLt ctx.bodySrc.locals.length opnd = true)
    (hOpVal : operandTupleValid ctx.plan.tupLocal ctx.fieldTys opnd = true) :
    match evalOperandToSlotExt ctx.bodySrc.locals lsSrc opnd with
    | .error k =>
      evalOperandToSlotExt ctx.bodyTgt.locals lsTgt
        (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd) = .error k
    | .ok (ty, ov, lsSrc') =>
      ∃ lsTgt',
        evalOperandToSlotExt ctx.bodyTgt.locals lsTgt
          (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd) =
            .ok (ty, ov, lsTgt') ∧
        SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
          ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' ∧
        (∀ k, ctx.bodySrc.locals.length + ctx.fieldTys.length ≤ k →
          Trusted.MirSemantics.getElem? lsTgt' k = Trusted.MirSemantics.getElem? lsTgt k) := by
  let ⟨hLenS, hLenT, hAtLt, hTup⟩ := hRel
  cases opnd with
  | constant c =>
    dsimp [rewriteTupleOperand, evalOperandToSlotExt]
    cases evalConstLit c.ty c.lit with
    | error _ => rfl
    | ok _ => exact ⟨lsTgt, rfl, hRel, fun _ _ => rfl⟩
  | copy place =>
    cases place with
    | mk lid proj =>
      dsimp [operandLocalsLt] at hOpLt
      have hLidLt := nat_blt_lt hOpLt
      dsimp [operandTupleValid] at hOpVal
      dsimp [rewriteTupleOperand, rewriteTuplePlace]
      cases hEq : Nat.beq lid ctx.plan.tupLocal with
      | false =>
        have hNe := nat_ne_of_beq_false hEq
        dsimp [evalOperandToSlotExt]
        rw [sroaCtx_localsTgt_getElem?_lt ctx hLidLt hNe, hAtLt lid hLidLt hNe]
        cases proj with
        | nil =>
          dsimp
          cases Trusted.MirSemantics.getElem? ctx.bodySrc.locals lid with
          | none => rfl
          | some ty =>
            cases Trusted.MirSemantics.getElem? lsSrc lid with
            | none => rfl
            | some sl =>
              cases sl with
              | dead => rfl
              | liveBase ov =>
                dsimp
                cases isFlatTupleTy ty with
                | true => rfl
                | false => exact ⟨lsTgt, rfl, hRel, fun _ _ => rfl⟩
              | liveTuple fields =>
                cases ty with
                | tuple fTys =>
                  dsimp
                  cases (isFlatTupleTy (.tuple fTys) && Nat.beq fields.length fTys.length) with
                  | false => rfl
                  | true => exact ⟨lsTgt, rfl, hRel, fun _ _ => rfl⟩
                | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => rfl
        | cons pe rest =>
          cases rest with
          | cons _ _ => cases pe <;> rfl
          | nil =>
            cases pe with
            | deref | unsupported => rfl
            | field idx fTy =>
              dsimp
              cases Trusted.MirSemantics.getElem? ctx.bodySrc.locals lid with
              | none => rfl
              | some ty =>
                cases ty with
                | tuple fTys =>
                  cases Trusted.MirSemantics.getElem? lsSrc lid with
                  | none => rfl
                  | some sl =>
                    dsimp
                    cases (!isFlatTupleTy (.tuple fTys)) with
                    | true => rfl
                    | false =>
                      dsimp
                      cases Trusted.MirSemantics.getElem? fTys idx with
                      | none => rfl
                      | some dft =>
                        dsimp
                        cases (!MirTy.beq fTy dft) with
                        | true => rfl
                        | false =>
                          dsimp
                          cases sl with
                          | dead | liveBase _ => rfl
                          | liveTuple fields =>
                            dsimp
                            cases Trusted.MirSemantics.getElem? fields idx with
                            | none => rfl
                            | some ov => exact ⟨lsTgt, rfl, hRel, fun _ _ => rfl⟩
                | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => rfl
      | true =>
        have hLid := nat_beq_eq hEq; subst hLid
        rw [hEq] at hOpVal; dsimp [isValidTupleFieldPlace] at hOpVal
        rw [nat_beq_refl, Bool.true_and] at hOpVal
        cases proj with
        | nil => cases hOpVal
        | cons pe rest =>
          cases rest with
          | cons _ _ => cases pe <;> cases hOpVal
          | nil =>
            cases pe with
            | deref | unsupported => cases hOpVal
            | field idx fTy =>
              dsimp at hOpVal
              cases hFty : Trusted.MirSemantics.getElem? ctx.fieldTys idx with
              | none => rw [hFty] at hOpVal; cases hOpVal
              | some dft =>
                rw [hFty] at hOpVal
                dsimp at hOpVal
                have hIdxLt := getElem?_some_lt hFty
                have hSc := list_all_getElem? (sroaCtx_fieldTys_all_scalar ctx) hFty
                have hNotFlat := isFlatTupleTy_false_of_supportedScalar hSc
                dsimp [evalOperandToSlotExt]
                rw [ctx.hTupTy, sroaCtx_localsTgt_getElem?_field ctx hIdxLt, hFty]
                cases hSrcT : Trusted.MirSemantics.getElem? lsSrc ctx.plan.tupLocal with
                | none => rw [hSrcT] at hTup; exact False.elim hTup
                | some sl =>
                  rw [hSrcT] at hTup
                  dsimp
                  rw [ctx.hFlatTup, hFty]; dsimp; rw [hOpVal]; dsimp
                  cases sl with
                  | liveBase _ => exact False.elim hTup
                  | dead =>
                    rw [hTup idx hIdxLt]
                  | liveTuple fields =>
                    dsimp
                    rw [hTup.2 idx hIdxLt]
                    have hFLt : idx < fields.length := by rw [hTup.1]; exact hIdxLt
                    let ⟨ov, hOv⟩ := getElem?_some_of_lt fields idx hFLt
                    rw [hOv]
                    dsimp [Option.map]
                    rw [hNotFlat]
                    exact ⟨lsTgt, rfl, hRel, fun _ _ => rfl⟩
  | move place =>
    cases place with
    | mk lid proj =>
      dsimp [operandLocalsLt] at hOpLt
      have hLidLt := nat_blt_lt hOpLt
      dsimp [operandTupleValid] at hOpVal
      dsimp [rewriteTupleOperand, rewriteTuplePlace]
      cases hEq : Nat.beq lid ctx.plan.tupLocal with
      | false =>
        have hNe := nat_ne_of_beq_false hEq
        dsimp [evalOperandToSlotExt]
        rw [sroaCtx_localsTgt_getElem?_lt ctx hLidLt hNe, hAtLt lid hLidLt hNe]
        have hLtS : lid < lsSrc.length := by rw [hLenS]; exact hLidLt
        have hLtT : lid < lsTgt.length := by
          rw [hLenT]; exact nat_lt_add_right _ (nat_lt_add_right _ hLidLt)
        cases proj with
        | nil =>
          dsimp
          cases Trusted.MirSemantics.getElem? ctx.bodySrc.locals lid with
          | none => rfl
          | some ty =>
            cases Trusted.MirSemantics.getElem? lsSrc lid with
            | none => rfl
            | some sl =>
              cases sl with
              | dead => rfl
              | liveBase ov =>
                dsimp
                cases isFlatTupleTy ty with
                | true => rfl
                | false =>
                  dsimp
                  let ⟨lsS', hSetS⟩ := setElem?_some_of_lt lsSrc lid (.liveBase (liveUninitFieldVal ty)) hLtS
                  let ⟨lsT', hSetT⟩ := setElem?_some_of_lt lsTgt lid (.liveBase (liveUninitFieldVal ty)) hLtT
                  rw [hSetS, hSetT]
                  refine ⟨lsT', rfl, sroaRelLocals_set_ne hRel hLidLt hNe hSetS hSetT, ?_⟩
                  intro k hk
                  have hKNe : k ≠ lid := fun h =>
                    Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right _ _) hk) (h ▸ hLidLt)
                  exact setElem?_getElem?_ne hSetT hKNe
              | liveTuple fields =>
                cases ty with
                | tuple fTys =>
                  dsimp
                  cases (isFlatTupleTy (.tuple fTys) && Nat.beq fields.length fTys.length) with
                  | false => rfl
                  | true =>
                    dsimp
                    let ⟨lsS', hSetS⟩ := setElem?_some_of_lt lsSrc lid (liveUninitSlotExt (.tuple fTys)) hLtS
                    let ⟨lsT', hSetT⟩ := setElem?_some_of_lt lsTgt lid (liveUninitSlotExt (.tuple fTys)) hLtT
                    rw [hSetS, hSetT]
                    refine ⟨lsT', rfl, sroaRelLocals_set_ne hRel hLidLt hNe hSetS hSetT, ?_⟩
                    intro k hk
                    have hKNe : k ≠ lid := fun h =>
                      Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right _ _) hk) (h ▸ hLidLt)
                    exact setElem?_getElem?_ne hSetT hKNe
                | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => rfl
        | cons pe rest =>
          cases rest with
          | cons _ _ => cases pe <;> rfl
          | nil =>
            cases pe with
            | deref | unsupported => rfl
            | field idx fTy =>
              dsimp
              cases Trusted.MirSemantics.getElem? ctx.bodySrc.locals lid with
              | none => rfl
              | some ty =>
                cases ty with
                | tuple fTys =>
                  cases Trusted.MirSemantics.getElem? lsSrc lid with
                  | none => rfl
                  | some sl =>
                    dsimp
                    cases (!isFlatTupleTy (.tuple fTys)) with
                    | true => rfl
                    | false =>
                      dsimp
                      cases Trusted.MirSemantics.getElem? fTys idx with
                      | none => rfl
                      | some dft =>
                        dsimp
                        cases (!MirTy.beq fTy dft) with
                        | true => rfl
                        | false =>
                          dsimp
                          cases sl with
                          | dead | liveBase _ => rfl
                          | liveTuple fields =>
                            dsimp
                            cases Trusted.MirSemantics.getElem? fields idx with
                            | none => rfl
                            | some ov =>
                              dsimp
                              cases hSf : setElem? fields idx (liveUninitFieldVal dft) with
                              | none => rfl
                              | some fields' =>
                                dsimp
                                let ⟨lsS', hSetS⟩ := setElem?_some_of_lt lsSrc lid (.liveTuple fields') hLtS
                                let ⟨lsT', hSetT⟩ := setElem?_some_of_lt lsTgt lid (.liveTuple fields') hLtT
                                rw [hSetS, hSetT]
                                refine ⟨lsT', rfl, sroaRelLocals_set_ne hRel hLidLt hNe hSetS hSetT, ?_⟩
                                intro k hk
                                have hKNe : k ≠ lid := fun h =>
                                  Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right _ _) hk) (h ▸ hLidLt)
                                exact setElem?_getElem?_ne hSetT hKNe
                | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => rfl
      | true =>
        have hLid := nat_beq_eq hEq; subst hLid
        rw [hEq] at hOpVal; dsimp [isValidTupleFieldPlace] at hOpVal
        rw [nat_beq_refl, Bool.true_and] at hOpVal
        cases proj with
        | nil => cases hOpVal
        | cons pe rest =>
          cases rest with
          | cons _ _ => cases pe <;> cases hOpVal
          | nil =>
            cases pe with
            | deref | unsupported => cases hOpVal
            | field idx fTy =>
              dsimp at hOpVal
              cases hFty : Trusted.MirSemantics.getElem? ctx.fieldTys idx with
              | none => rw [hFty] at hOpVal; cases hOpVal
              | some dft =>
                rw [hFty] at hOpVal
                dsimp at hOpVal
                have hIdxLt := getElem?_some_lt hFty
                have hSc := list_all_getElem? (sroaCtx_fieldTys_all_scalar ctx) hFty
                have hNotFlat := isFlatTupleTy_false_of_supportedScalar hSc
                dsimp [evalOperandToSlotExt]
                rw [ctx.hTupTy, sroaCtx_localsTgt_getElem?_field ctx hIdxLt, hFty]
                cases hSrcT : Trusted.MirSemantics.getElem? lsSrc ctx.plan.tupLocal with
                | none => rw [hSrcT] at hTup; exact False.elim hTup
                | some sl =>
                  rw [hSrcT] at hTup
                  dsimp
                  rw [ctx.hFlatTup, hFty]; dsimp; rw [hOpVal]; dsimp
                  cases sl with
                  | liveBase _ => exact False.elim hTup
                  | dead =>
                    rw [hTup idx hIdxLt]
                  | liveTuple fields =>
                    dsimp
                    rw [hTup.2 idx hIdxLt]
                    have hFLt : idx < fields.length := by rw [hTup.1]; exact hIdxLt
                    let ⟨ov, hOv⟩ := getElem?_some_of_lt fields idx hFLt
                    rw [hOv]
                    dsimp [Option.map]
                    rw [hNotFlat]; dsimp
                    let ⟨fields', hSetF⟩ := setElem?_some_of_lt fields idx (liveUninitFieldVal dft) hFLt
                    have hTupLtS : ctx.plan.tupLocal < lsSrc.length := by rw [hLenS]; exact ctx.hTupLt
                    have hFldLtT : ctx.bodySrc.locals.length + idx < lsTgt.length := by
                      rw [hLenT]; exact nat_lt_add_right _ (Nat.add_lt_add_left hIdxLt _)
                    let ⟨lsS', hSetS⟩ := setElem?_some_of_lt lsSrc ctx.plan.tupLocal (.liveTuple fields') hTupLtS
                    let ⟨lsT', hSetT⟩ := setElem?_some_of_lt lsTgt (ctx.bodySrc.locals.length + idx)
                      (.liveBase (liveUninitFieldVal dft)) hFldLtT
                    rw [hSetF]; dsimp; rw [hSetS, hSetT]
                    refine ⟨lsT', rfl,
                      sroaRelLocals_set_field hRel hSrcT hIdxLt hSetF hSetS hSetT, ?_⟩
                    intro k hk
                    have hKNe : k ≠ ctx.bodySrc.locals.length + idx := fun h =>
                      Nat.not_lt_of_ge hk (h ▸ Nat.add_lt_add_left hIdxLt _)
                    exact setElem?_getElem?_ne hSetT hKNe

private theorem sroa_evalPrimitiveOperandExt_sim (ctx : SroaCtx)
    {lsSrc lsTgt : List LocalSlotExt} {opnd : Operand}
    (hRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys lsSrc lsTgt)
    (hOpLt : operandLocalsLt ctx.bodySrc.locals.length opnd = true)
    (hOpVal : operandTupleValid ctx.plan.tupLocal ctx.fieldTys opnd = true) :
    match evalPrimitiveOperandExt ctx.bodySrc.locals lsSrc opnd with
    | .error k =>
      evalPrimitiveOperandExt ctx.bodyTgt.locals lsTgt
        (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd) = .error k
    | .ok (v, lsSrc') =>
      ∃ lsTgt',
        evalPrimitiveOperandExt ctx.bodyTgt.locals lsTgt
          (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd) =
            .ok (v, lsTgt') ∧
        SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
          ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' ∧
        (∀ k, ctx.bodySrc.locals.length + ctx.fieldTys.length ≤ k →
          Trusted.MirSemantics.getElem? lsTgt' k = Trusted.MirSemantics.getElem? lsTgt k) := by
  unfold evalPrimitiveOperandExt
  have hOp := sroa_evalOperandToSlotExt_sim ctx hRel hOpLt hOpVal
  cases hEv : evalOperandToSlotExt ctx.bodySrc.locals lsSrc opnd with
  | error k =>
    rw [hEv] at hOp
    rw [hOp]
  | ok triple =>
    rw [hEv] at hOp
    cases triple with
    | mk ty rest =>
      cases rest with
      | mk ov lsSrc' =>
        let ⟨lsTgt', hTgt, hRel', hPres⟩ := hOp
        rw [hTgt]
        dsimp
        cases (!isPrimitiveReadableTy ty) with
        | true => rfl
        | false =>
          dsimp
          cases ov with
          | none => rfl
          | some v => exact ⟨lsTgt', rfl, hRel', hPres⟩

private theorem sroa_evalRvalueExt_sim (ctx : SroaCtx)
    {lsSrc lsTgt : List LocalSlotExt} {dstTy : MirTy} {rv : Rvalue}
    (hRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys lsSrc lsTgt)
    (hRvLt : rvalueLocalsLt ctx.bodySrc.locals.length rv = true)
    (hRvVal : rvalueTupleValid ctx.plan.tupLocal ctx.fieldTys rv = true) :
    match evalRvalueExt ctx.bodySrc.locals lsSrc dstTy rv with
    | .error k =>
      evalRvalueExt ctx.bodyTgt.locals lsTgt dstTy
        (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv) = .error k
    | .ok (v, lsSrc') =>
      ∃ lsTgt',
        evalRvalueExt ctx.bodyTgt.locals lsTgt dstTy
          (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv) =
            .ok (v, lsTgt') ∧
        SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
          ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' := by
  cases rv with
  | use opnd =>
    dsimp [rewriteTupleRvalue, evalRvalueExt]
    have hOp := sroa_evalOperandToSlotExt_sim ctx hRel hRvLt hRvVal
    cases hEv : evalOperandToSlotExt ctx.bodySrc.locals lsSrc opnd with
    | error k => rw [hEv] at hOp; rw [hOp]
    | ok triple =>
      rw [hEv] at hOp
      cases triple with
      | mk srcTy rest =>
        cases rest with
        | mk ov ls1 =>
          let ⟨lsT1, hTgt, hRel1, _⟩ := hOp
          rw [hTgt]; dsimp
          cases (!MirTy.beq srcTy dstTy) with
          | true => rfl
          | false =>
            dsimp
            cases ov with
            | none => rfl
            | some v => exact ⟨lsT1, rfl, hRel1⟩
  | binaryOp op lhs rhs =>
    let ⟨hLLt, hRLt⟩ := bool_and_true hRvLt
    let ⟨hLVal, hRVal⟩ := bool_and_true hRvVal
    dsimp [rewriteTupleRvalue, evalRvalueExt]
    have hL := sroa_evalPrimitiveOperandExt_sim ctx hRel hLLt hLVal
    cases hEvL : evalPrimitiveOperandExt ctx.bodySrc.locals lsSrc lhs with
    | error k => rw [hEvL] at hL; rw [hL]
    | ok p1 =>
      rw [hEvL] at hL
      cases p1 with
      | mk lv ls1 =>
        let ⟨lsT1, hTgtL, hRel1, _⟩ := hL
        rw [hTgtL]; dsimp
        have hR := sroa_evalPrimitiveOperandExt_sim ctx hRel1 hRLt hRVal
        cases hEvR : evalPrimitiveOperandExt ctx.bodySrc.locals ls1 rhs with
        | error k => rw [hEvR] at hR; rw [hR]
        | ok p2 =>
          rw [hEvR] at hR
          cases p2 with
          | mk rv' ls2 =>
            let ⟨lsT2, hTgtR, hRel2, _⟩ := hR
            rw [hTgtR]; dsimp
            cases isWithOverflowBinOp op with
            | true =>
              dsimp
              cases evalWithOverflowOp op lv rv' with
              | error _ => rfl
              | ok res => cases res with | mk _ _ => exact ⟨lsT2, rfl, hRel2⟩
            | false =>
              dsimp
              cases evalBinOp op lv rv' with
              | error _ => rfl
              | ok _ => exact ⟨lsT2, rfl, hRel2⟩
  | unaryOp op opnd =>
    dsimp [rewriteTupleRvalue, evalRvalueExt]
    have hO := sroa_evalPrimitiveOperandExt_sim ctx hRel hRvLt hRvVal
    cases hEv : evalPrimitiveOperandExt ctx.bodySrc.locals lsSrc opnd with
    | error k => rw [hEv] at hO; rw [hO]
    | ok p1 =>
      rw [hEv] at hO
      cases p1 with
      | mk v1 ls1 =>
        let ⟨lsT1, hTgt, hRel1, _⟩ := hO
        rw [hTgt]; dsimp
        cases evalUnOp op v1 with
        | error _ => rfl
        | ok _ => exact ⟨lsT1, rfl, hRel1⟩
  | discriminant place =>
    dsimp [rvalueLocalsLt] at hRvLt
    dsimp [rvalueTupleValid] at hRvVal
    have hLt := nat_blt_lt hRvLt
    have hNe := nat_ne_of_beq_false (bool_not_true hRvVal)
    dsimp [rewriteTupleRvalue, evalRvalueExt]
    cases (!place.projection.isEmpty) with
    | true => rfl
    | false =>
      dsimp
      rw [sroaCtx_localsTgt_getElem?_lt ctx hLt hNe, hRel.2.2.1 place.localId hLt hNe]
      cases Trusted.MirSemantics.getElem? ctx.bodySrc.locals place.localId with
      | none => rfl
      | some dt =>
        cases dt with
        | enum ety =>
          cases Trusted.MirSemantics.getElem? lsSrc place.localId with
          | none => rfl
          | some sl =>
            dsimp
            cases (!enumAdmitted ety) with
            | true => rfl
            | false =>
              dsimp
              cases sl with
              | dead | liveTuple _ => cases ety.tagRepr <;> rfl
              | liveBase ov =>
                cases ety.tagRepr with
                | zeroSized =>
                  cases ov with
                  | none =>
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rfl
                    | some _ => exact ⟨lsTgt, rfl, hRel⟩
                  | some v' =>
                    cases v' with
                    | enumVal ety' idx =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.beq idx 0) with
                      | false => rfl
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rfl
                        | some _ => exact ⟨lsTgt, rfl, hRel⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => rfl
                | scalar _ _ =>
                  cases ov with
                  | none => rfl
                  | some v' =>
                    cases v' with
                    | enumVal ety' idx =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.blt idx ety.discriminants.length) with
                      | false => rfl
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants idx with
                        | none => rfl
                        | some _ => exact ⟨lsTgt, rfl, hRel⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => rfl
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => rfl
  | aggregateTuple _ | ref _ _ | addressOf _ _ | unsupported => rfl

private theorem sroa_writePlaceExt_ne_sim (ctx : SroaCtx)
    {lsSrc lsTgt : List LocalSlotExt} {dstId : LocalId} {dstTy : MirTy} {val : Val}
    (hRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys lsSrc lsTgt)
    (hLt : dstId < ctx.bodySrc.locals.length)
    (hNe : dstId ≠ ctx.plan.tupLocal) :
    match writePlaceExt lsSrc dstId dstTy val with
    | .error k => writePlaceExt lsTgt dstId dstTy val = .error k
    | .ok lsSrc' =>
      ∃ lsTgt',
        writePlaceExt lsTgt dstId dstTy val = .ok lsTgt' ∧
        SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
          ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' := by
  let ⟨hLenS, hLenT, hAtLt, _⟩ := hRel
  have hLtS : dstId < lsSrc.length := by rw [hLenS]; exact hLt
  have hLtT : dstId < lsTgt.length := by
    rw [hLenT]; exact nat_lt_add_right _ (nat_lt_add_right _ hLt)
  unfold writePlaceExt
  cases (!checkValExt val dstTy) with
  | true => rfl
  | false =>
    dsimp
    have hCaseBase :
        match (match Trusted.MirSemantics.getElem? lsSrc dstId with
         | none => (Except.error FaultKind.unsupported : Except FaultKind (List LocalSlotExt))
         | some .dead => .error .undefined
         | some (.liveBase _) =>
           match setElem? lsSrc dstId (.liveBase (some val)) with
           | some locals' => .ok locals'
           | none => .error .unsupported
         | some (.liveTuple _) => .error .unsupported) with
        | .error k =>
          (match Trusted.MirSemantics.getElem? lsTgt dstId with
           | none => (Except.error FaultKind.unsupported : Except FaultKind (List LocalSlotExt))
           | some .dead => .error .undefined
           | some (.liveBase _) =>
             match setElem? lsTgt dstId (.liveBase (some val)) with
             | some locals' => .ok locals'
             | none => .error .unsupported
           | some (.liveTuple _) => .error .unsupported) = .error k
        | .ok lsSrc' =>
          ∃ lsTgt',
            (match Trusted.MirSemantics.getElem? lsTgt dstId with
             | none => (Except.error FaultKind.unsupported : Except FaultKind (List LocalSlotExt))
             | some .dead => .error .undefined
             | some (.liveBase _) =>
               match setElem? lsTgt dstId (.liveBase (some val)) with
               | some locals' => .ok locals'
               | none => .error .unsupported
             | some (.liveTuple _) => .error .unsupported) = .ok lsTgt' ∧
            SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
              ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' := by
      rw [hAtLt dstId hLt hNe]
      cases Trusted.MirSemantics.getElem? lsSrc dstId with
      | none => rfl
      | some sl =>
        cases sl with
        | dead | liveTuple _ => rfl
        | liveBase _ =>
          let ⟨lsS', hSetS⟩ := setElem?_some_of_lt lsSrc dstId (.liveBase (some val)) hLtS
          let ⟨lsT', hSetT⟩ := setElem?_some_of_lt lsTgt dstId (.liveBase (some val)) hLtT
          rw [hSetS, hSetT]
          exact ⟨lsT', rfl, sroaRelLocals_set_ne hRel hLt hNe hSetS hSetT⟩
    cases dstTy with
    | tuple _ =>
      cases val with
      | tuple vs =>
        dsimp
        rw [hAtLt dstId hLt hNe]
        cases Trusted.MirSemantics.getElem? lsSrc dstId with
        | none => rfl
        | some sl =>
          cases sl with
          | dead | liveBase _ => rfl
          | liveTuple _ =>
            let ⟨lsS', hSetS⟩ := setElem?_some_of_lt lsSrc dstId (.liveTuple (vs.map some)) hLtS
            let ⟨lsT', hSetT⟩ := setElem?_some_of_lt lsTgt dstId (.liveTuple (vs.map some)) hLtT
            rw [hSetS, hSetT]
            exact ⟨lsT', rfl, sroaRelLocals_set_ne hRel hLt hNe hSetS hSetT⟩
      | scalar _ | ptr _ | bool _ | unit | enumVal _ _ | bytes _ => exact hCaseBase
    | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
      exact hCaseBase

private theorem sroa_writeTupleFieldExt_ne_sim (ctx : SroaCtx)
    {lsSrc lsTgt : List LocalSlotExt} {dstId : LocalId} {idx : FieldIdx}
    {fieldTy : MirTy} {val : Val}
    (hRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys lsSrc lsTgt)
    (hLt : dstId < ctx.bodySrc.locals.length)
    (hNe : dstId ≠ ctx.plan.tupLocal) :
    match writeTupleFieldExt lsSrc dstId idx fieldTy val with
    | .error k => writeTupleFieldExt lsTgt dstId idx fieldTy val = .error k
    | .ok lsSrc' =>
      ∃ lsTgt',
        writeTupleFieldExt lsTgt dstId idx fieldTy val = .ok lsTgt' ∧
        SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
          ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' := by
  let ⟨hLenS, hLenT, hAtLt, _⟩ := hRel
  have hLtS : dstId < lsSrc.length := by rw [hLenS]; exact hLt
  have hLtT : dstId < lsTgt.length := by
    rw [hLenT]; exact nat_lt_add_right _ (nat_lt_add_right _ hLt)
  unfold writeTupleFieldExt
  cases (!checkVal val fieldTy) with
  | true => rfl
  | false =>
    dsimp
    rw [hAtLt dstId hLt hNe]
    cases Trusted.MirSemantics.getElem? lsSrc dstId with
    | none => rfl
    | some sl =>
      cases sl with
      | dead | liveBase _ => rfl
      | liveTuple fields =>
        dsimp
        cases setElem? fields idx (some val) with
        | none => rfl
        | some fields' =>
          dsimp
          let ⟨lsS', hSetS⟩ := setElem?_some_of_lt lsSrc dstId (.liveTuple fields') hLtS
          let ⟨lsT', hSetT⟩ := setElem?_some_of_lt lsTgt dstId (.liveTuple fields') hLtT
          rw [hSetS, hSetT]
          exact ⟨lsT', rfl, sroaRelLocals_set_ne hRel hLt hNe hSetS hSetT⟩

private theorem sroa_writeTupleFieldExt_tup_sim (ctx : SroaCtx)
    {lsSrc lsTgt : List LocalSlotExt} {idx : FieldIdx} {fieldTy : MirTy} {val : Val}
    (hRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys lsSrc lsTgt)
    (hFty : Trusted.MirSemantics.getElem? ctx.fieldTys idx = some fieldTy) :
    match writeTupleFieldExt lsSrc ctx.plan.tupLocal idx fieldTy val with
    | .error k =>
      writePlaceExt lsTgt (ctx.bodySrc.locals.length + idx) fieldTy val = .error k
    | .ok lsSrc' =>
      ∃ lsTgt',
        writePlaceExt lsTgt (ctx.bodySrc.locals.length + idx) fieldTy val = .ok lsTgt' ∧
        SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
          ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' := by
  let ⟨hLenS, hLenT, _, hTup⟩ := hRel
  have hIdxLt := getElem?_some_lt hFty
  have hSc := list_all_getElem? (sroaCtx_fieldTys_all_scalar ctx) hFty
  unfold writeTupleFieldExt writePlaceExt
  rw [checkValExt_eq_checkVal_of_supportedScalar val hSc]
  cases (!checkVal val fieldTy) with
  | true => rfl
  | false =>
    dsimp
    have hCore :
        match (match Trusted.MirSemantics.getElem? lsSrc ctx.plan.tupLocal with
         | none => (Except.error FaultKind.unsupported : Except FaultKind (List LocalSlotExt))
         | some .dead => .error .undefined
         | some (.liveTuple fields) =>
           match setElem? fields idx (some val) with
           | none => .error .unsupported
           | some fields' =>
             match setElem? lsSrc ctx.plan.tupLocal (.liveTuple fields') with
             | some locals' => .ok locals'
             | none => .error .unsupported
         | some (.liveBase _) => .error .unsupported) with
        | .error k =>
          (match Trusted.MirSemantics.getElem? lsTgt (ctx.bodySrc.locals.length + idx) with
           | none => (Except.error FaultKind.unsupported : Except FaultKind (List LocalSlotExt))
           | some .dead => .error .undefined
           | some (.liveBase _) =>
             match setElem? lsTgt (ctx.bodySrc.locals.length + idx) (.liveBase (some val)) with
             | some locals' => .ok locals'
             | none => .error .unsupported
           | some (.liveTuple _) => .error .unsupported) = .error k
        | .ok lsSrc' =>
          ∃ lsTgt',
            (match Trusted.MirSemantics.getElem? lsTgt (ctx.bodySrc.locals.length + idx) with
             | none => (Except.error FaultKind.unsupported : Except FaultKind (List LocalSlotExt))
             | some .dead => .error .undefined
             | some (.liveBase _) =>
               match setElem? lsTgt (ctx.bodySrc.locals.length + idx) (.liveBase (some val)) with
               | some locals' => .ok locals'
               | none => .error .unsupported
             | some (.liveTuple _) => .error .unsupported) = .ok lsTgt' ∧
            SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
              ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' := by
      cases hSrcT : Trusted.MirSemantics.getElem? lsSrc ctx.plan.tupLocal with
      | none => rw [hSrcT] at hTup; exact False.elim hTup
      | some sl =>
        rw [hSrcT] at hTup
        cases sl with
        | liveBase _ => exact False.elim hTup
        | dead =>
          rw [hTup idx hIdxLt]
        | liveTuple fields =>
          dsimp
          rw [hTup.2 idx hIdxLt]
          have hFLt : idx < fields.length := by rw [hTup.1]; exact hIdxLt
          let ⟨ov, hOv⟩ := getElem?_some_of_lt fields idx hFLt
          rw [hOv]
          dsimp [Option.map]
          let ⟨fields', hSetF⟩ := setElem?_some_of_lt fields idx (some val) hFLt
          have hTupLtS : ctx.plan.tupLocal < lsSrc.length := by rw [hLenS]; exact ctx.hTupLt
          have hFldLtT : ctx.bodySrc.locals.length + idx < lsTgt.length := by
            rw [hLenT]; exact nat_lt_add_right _ (Nat.add_lt_add_left hIdxLt _)
          let ⟨lsS', hSetS⟩ := setElem?_some_of_lt lsSrc ctx.plan.tupLocal (.liveTuple fields') hTupLtS
          let ⟨lsT', hSetT⟩ := setElem?_some_of_lt lsTgt (ctx.bodySrc.locals.length + idx)
            (.liveBase (some val)) hFldLtT
          rw [hSetF]; dsimp; rw [hSetS, hSetT]
          exact ⟨lsT', rfl, sroaRelLocals_set_field hRel hSrcT hIdxLt hSetF hSetS hSetT⟩
    cases fieldTy with
    | tuple _ => cases hSc
    | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
      dsimp
      exact hCore


/-! ### Private Helpers from `F1_11_SliceB2.lean` -/
private theorem isPrimitiveReadableTy_int (w : IntWidth) (s : Bool) :
    isPrimitiveReadableTy (.int w s) = true := rfl

private theorem isPrimitiveReadableTy_bool :
    isPrimitiveReadableTy .bool = true := rfl

private theorem nat_ne_succ_self (n : Nat) : n ≠ n + 1 := fun h => by
  have hlt : n < n + 1 := Nat.lt_succ_self n
  rw [← h] at hlt
  exact Nat.not_lt_of_ge (Nat.le_refl n) hlt

private theorem nat_succ_ne_self (n : Nat) : n + 1 ≠ n := fun h =>
  nat_ne_succ_self n h.symm

private theorem if_cond_congr {α : Type} {b1 b2 : Bool} (h : b1 = b2) (x y : α) :
    (if b1 = true then x else y) = (if b2 = true then x else y) := by
  subst h; rfl

/-! #### Multi-Step Statement Sequence Execution Lemmas in `bodyTgt` -/

private theorem sroaCtx_getElem?_bodyTgt (ctx : SroaCtx) :
    Trusted.MirSemantics.getElem? ctx.pTgt.bodies ctx.plan.defId = some ctx.bodyTgt := by
  rw [ctx.hPTgt]; dsimp
  exact setElem?_getElem?_same ctx.hSetBody

private theorem sroaCtx_getElem?_bbTgt (ctx : SroaCtx) {blk : BasicBlockId}
    {bbSrc : BasicBlock}
    (hBb : Trusted.MirSemantics.getElem? ctx.bodySrc.basicBlocks blk = some bbSrc) :
    Trusted.MirSemantics.getElem? ctx.bodyTgt.basicBlocks blk =
      some {
        statements :=
          listFlatMap
            (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length ctx.bodySrc.locals.length
              (ctx.bodySrc.locals.length + ctx.fieldTys.length))
            bbSrc.statements
        terminator :=
          rewriteTupleTerminator ctx.plan.tupLocal ctx.bodySrc.locals.length bbSrc.terminator
        cleanup := bbSrc.cleanup
      } := by
  rw [ctx.hBodyTgt]; dsimp
  rw [getElem?_map, hBb]; rfl

private theorem list_take_drop_split {α : Type} (xs : List α) (n : Nat) :
    xs.take n ++ xs.drop n = xs := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons a rest ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp [List.take, List.drop]
      rw [ih k]

private theorem list_drop_of_getElem? {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : Trusted.MirSemantics.getElem? xs i = some x) :
    xs.drop i = x :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => cases h
  | cons a rest ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k => exact ih h

private theorem sroa_bbTgt_stmt_at (ctx : SroaCtx) {bbSrc : BasicBlock}
    {stmtIdx : Nat} {stmt : StatementKind}
    (hStmt : Trusted.MirSemantics.getElem? bbSrc.statements stmtIdx = some stmt)
    (j : Nat) :
    let lowered := lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length
      ctx.bodySrc.locals.length (ctx.bodySrc.locals.length + ctx.fieldTys.length) stmt
    j < lowered.length →
    Trusted.MirSemantics.getElem?
      (listFlatMap (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length
        ctx.bodySrc.locals.length (ctx.bodySrc.locals.length + ctx.fieldTys.length))
        bbSrc.statements)
      (sroaStmtOffset ctx bbSrc stmtIdx + j) =
    Trusted.MirSemantics.getElem? lowered j := by
  intro lowered hJLt
  have hSplit : bbSrc.statements =
      bbSrc.statements.take stmtIdx ++ (stmt :: bbSrc.statements.drop (stmtIdx + 1)) := by
    rw [← list_drop_of_getElem? hStmt, list_take_drop_split]
  have hMap : listFlatMap (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length
      ctx.bodySrc.locals.length (ctx.bodySrc.locals.length + ctx.fieldTys.length))
      bbSrc.statements =
      listFlatMap (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length
        ctx.bodySrc.locals.length (ctx.bodySrc.locals.length + ctx.fieldTys.length))
        (bbSrc.statements.take stmtIdx) ++
      (lowered ++ listFlatMap (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length
        ctx.bodySrc.locals.length (ctx.bodySrc.locals.length + ctx.fieldTys.length))
        (bbSrc.statements.drop (stmtIdx + 1))) := by
    have hCong := congrArg
      (listFlatMap (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length
        ctx.bodySrc.locals.length (ctx.bodySrc.locals.length + ctx.fieldTys.length)))
      hSplit
    rw [listFlatMap_append] at hCong
    exact hCong
  rw [hMap]
  unfold sroaStmtOffset
  rw [getElem?_append_right_add]
  exact getElem?_append_left lowered _ j hJLt

private theorem sroaStmtOffset_succ (ctx : SroaCtx) {bbSrc : BasicBlock}
    {stmtIdx : Nat} {stmt : StatementKind}
    (hStmt : Trusted.MirSemantics.getElem? bbSrc.statements stmtIdx = some stmt) :
    sroaStmtOffset ctx bbSrc (stmtIdx + 1) =
      sroaStmtOffset ctx bbSrc stmtIdx +
        (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length
          ctx.bodySrc.locals.length (ctx.bodySrc.locals.length + ctx.fieldTys.length) stmt).length := by
  unfold sroaStmtOffset
  rw [list_take_succ_of_getElem? hStmt, listFlatMap_append, list_append_length]
  dsimp [listFlatMap]
  rw [List.append_nil]

private theorem mkStorageLivesLoop_length (base start count : Nat) :
    (mkStorageLivesLoop base start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    dsimp [mkStorageLivesLoop, List.length]
    rw [ih (start + 1)]

private theorem mkStorageLivesLoop_getElem? (base start count j : Nat) (h : j < count) :
    Trusted.MirSemantics.getElem? (mkStorageLivesLoop base start count) j =
      some (.storageLive (base + (start + j))) := by
  induction count generalizing start j with
  | zero => exact False.elim (Nat.not_lt_zero j h)
  | succ k ih =>
    cases j with
    | zero =>
      dsimp [mkStorageLivesLoop, Trusted.MirSemantics.getElem?]
    | succ m =>
      dsimp [mkStorageLivesLoop, Trusted.MirSemantics.getElem?]
      rw [ih (start + 1) m (Nat.lt_of_succ_lt_succ h)]
      have hAdd : start + 1 + m = start + (m + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 m]
      rw [hAdd]

private theorem mkStorageDeadsLoop_length (base start count : Nat) :
    (mkStorageDeadsLoop base start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    dsimp [mkStorageDeadsLoop, List.length]
    rw [ih (start + 1)]

private theorem mkStorageDeadsLoop_getElem? (base start count j : Nat) (h : j < count) :
    Trusted.MirSemantics.getElem? (mkStorageDeadsLoop base start count) j =
      some (.storageDead (base + (start + j))) := by
  induction count generalizing start j with
  | zero => exact False.elim (Nat.not_lt_zero j h)
  | succ k ih =>
    cases j with
    | zero =>
      dsimp [mkStorageDeadsLoop, Trusted.MirSemantics.getElem?]
    | succ m =>
      dsimp [mkStorageDeadsLoop, Trusted.MirSemantics.getElem?]
      rw [ih (start + 1) m (Nat.lt_of_succ_lt_succ h)]
      have hAdd : start + 1 + m = start + (m + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 m]
      rw [hAdd]

private theorem mkIndexedUseAssignsLoop_length (dstBase start : Nat) (ops : List Operand) :
    (mkIndexedUseAssignsLoop dstBase start ops).length = ops.length := by
  induction ops generalizing start with
  | nil => rfl
  | cons _ _ ih =>
    dsimp [mkIndexedUseAssignsLoop, List.length]
    rw [ih (start + 1)]

private theorem mkIndexedUseAssignsLoop_getElem? (dstBase start : Nat) (ops : List Operand)
    (j : Nat) (opnd : Operand)
    (h : Trusted.MirSemantics.getElem? ops j = some opnd) :
    Trusted.MirSemantics.getElem? (mkIndexedUseAssignsLoop dstBase start ops) j =
      some (.assign ⟨dstBase + (start + j), []⟩ (.use opnd)) := by
  induction ops generalizing start j with
  | nil => cases h
  | cons a _ ih =>
    cases j with
    | zero =>
      injection h with hEq; subst hEq
      dsimp [mkIndexedUseAssignsLoop, Trusted.MirSemantics.getElem?]
    | succ m =>
      dsimp [mkIndexedUseAssignsLoop, Trusted.MirSemantics.getElem?]
      rw [ih (start + 1) m h]
      have hAdd : start + 1 + m = start + (m + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 m]
      rw [hAdd]

private theorem sroa_exec_storageLives_loop (ctx : SroaCtx) {blk : BasicBlockId}
    {bbTgt : BasicBlock} {mem : CallerMemory}
    (hBbT : Trusted.MirSemantics.getElem? ctx.bodyTgt.basicBlocks blk = some bbTgt)
    (count : Nat) :
    ∀ (start pos : Nat) (ls : List LocalSlotExt),
      start + count = ctx.fieldTys.length →
      ls.length = ctx.bodySrc.locals.length + ctx.fieldTys.length + ctx.ovfTys.length →
      (∀ j, j < count →
        Trusted.MirSemantics.getElem? bbTgt.statements (pos + j) =
          some (.storageLive (ctx.bodySrc.locals.length + (start + j)))) →
      ∃ ls',
        evalTupleAssertFuel ctx.pTgt count
          { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos, locals := ls }],
            callerMem := mem } =
        .step { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos + count, locals := ls' }],
                callerMem := mem } ∧
        ls'.length = ls.length ∧
        (∀ i, i < ctx.bodySrc.locals.length + start →
          Trusted.MirSemantics.getElem? ls' i = Trusted.MirSemantics.getElem? ls i) ∧
        (∀ i, ctx.bodySrc.locals.length + ctx.fieldTys.length ≤ i →
          Trusted.MirSemantics.getElem? ls' i = Trusted.MirSemantics.getElem? ls i) ∧
        (∀ j, j < count →
          Trusted.MirSemantics.getElem? ls' (ctx.bodySrc.locals.length + (start + j)) =
            (Trusted.MirSemantics.getElem? ctx.fieldTys (start + j)).map
              (fun ty => LocalSlotExt.liveBase (liveUninitFieldVal ty))) := by
  induction count with
  | zero =>
    intro start pos ls _ _ _
    refine ⟨ls, by rw [Nat.add_zero]; rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    intro j hj; exact False.elim (Nat.not_lt_zero j hj)
  | succ k ih =>
    intro start pos ls hSum hLen hStmts
    have hStartLt : start < ctx.fieldTys.length := by
      rw [← hSum]
      rw [Nat.add_succ]
      exact Nat.lt_succ_of_le (Nat.le_add_right start k)
    let ⟨fty, hFty⟩ := getElem?_some_of_lt ctx.fieldTys start hStartLt
    have hSc := list_all_getElem? (sroaCtx_fieldTys_all_scalar ctx) hFty
    have hLiveEq : liveUninitSlotExt fty = .liveBase (liveUninitFieldVal fty) := by
      cases fty <;> first | rfl | cases hSc
    have hStmt0 : Trusted.MirSemantics.getElem? bbTgt.statements pos =
        some (.storageLive (ctx.bodySrc.locals.length + start)) := by
      have h0 := hStmts 0 (Nat.zero_lt_succ k)
      rw [Nat.add_zero, Nat.add_zero] at h0
      exact h0
    have hIdxLt : ctx.bodySrc.locals.length + start < ls.length := by
      rw [hLen]
      exact nat_lt_add_right _ (Nat.add_lt_add_left hStartLt _)
    let ⟨ls1, hSet1⟩ := setElem?_some_of_lt ls (ctx.bodySrc.locals.length + start)
      (.liveBase (liveUninitFieldVal fty)) hIdxLt
    have hStep0 : evalStepTupleAssert ctx.pTgt 0
        { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos, locals := ls }],
          callerMem := mem } =
        .step { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos + 1, locals := ls1 }],
                callerMem := mem } := by
      unfold evalStepTupleAssert
      dsimp
      rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmt0]
      dsimp [evalStatementExt]
      rw [sroaCtx_localsTgt_getElem?_field ctx hStartLt, hFty]
      dsimp
      rw [hLiveEq, hSet1]
    have hSumNext : (start + 1) + k = ctx.fieldTys.length := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]; exact hSum
    have hLen1 : ls1.length =
        ctx.bodySrc.locals.length + ctx.fieldTys.length + ctx.ovfTys.length := by
      rw [setElem?_length hSet1, hLen]
    let ⟨ls', hRest, hLen', hPre, hPost, hMid⟩ :=
      ih (start + 1) (pos + 1) ls1 hSumNext hLen1 (fun j hj => by
        have hS := hStmts (j + 1) (Nat.succ_lt_succ hj)
        have hP : pos + 1 + j = pos + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j]
        have hQ : start + 1 + j = start + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j]
        rw [hP, hQ]; exact hS)
    have hPosEq : pos + 1 + k = pos + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [hPosEq] at hRest
    refine ⟨ls', ?_, by rw [hLen', setElem?_length hSet1], ?_, ?_, ?_⟩
    · dsimp [evalTupleAssertFuel]
      rw [hStep0]; exact hRest
    · intro i hi
      have hLt1 : i < ctx.bodySrc.locals.length + (start + 1) := by
        rw [Nat.add_succ]; exact Nat.lt_succ_of_lt hi
      rw [hPre i hLt1]
      exact setElem?_getElem?_ne hSet1 (fun h => Nat.not_lt_of_ge (Nat.le_refl _) (h ▸ hi))
    · intro i hi
      rw [hPost i hi]
      have hNe : i ≠ ctx.bodySrc.locals.length + start := fun h =>
        Nat.not_lt_of_ge hi (h ▸ Nat.add_lt_add_left hStartLt _)
      exact setElem?_getElem?_ne hSet1 hNe
    · intro j hj
      cases j with
      | zero =>
        rw [Nat.add_zero]
        have hLt1 : ctx.bodySrc.locals.length + start < ctx.bodySrc.locals.length + (start + 1) := by
          rw [Nat.add_succ]; exact Nat.lt_succ_self _
        rw [hPre _ hLt1, setElem?_getElem?_same hSet1, hFty]; rfl
      | succ m =>
        have hAdd : start + (m + 1) = start + 1 + m := by rw [Nat.add_assoc, Nat.add_comm 1 m]
        rw [hAdd]
        exact hMid m (Nat.lt_of_succ_lt_succ hj)

private theorem sroa_exec_storageDeads_loop (ctx : SroaCtx) {blk : BasicBlockId}
    {bbTgt : BasicBlock} {mem : CallerMemory}
    (hBbT : Trusted.MirSemantics.getElem? ctx.bodyTgt.basicBlocks blk = some bbTgt)
    (count : Nat) :
    ∀ (start pos : Nat) (ls : List LocalSlotExt),
      start + count = ctx.fieldTys.length →
      ls.length = ctx.bodySrc.locals.length + ctx.fieldTys.length + ctx.ovfTys.length →
      (∀ j, j < count →
        Trusted.MirSemantics.getElem? bbTgt.statements (pos + j) =
          some (.storageDead (ctx.bodySrc.locals.length + (start + j)))) →
      ∃ ls',
        evalTupleAssertFuel ctx.pTgt count
          { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos, locals := ls }],
            callerMem := mem } =
        .step { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos + count, locals := ls' }],
                callerMem := mem } ∧
        ls'.length = ls.length ∧
        (∀ i, i < ctx.bodySrc.locals.length + start →
          Trusted.MirSemantics.getElem? ls' i = Trusted.MirSemantics.getElem? ls i) ∧
        (∀ i, ctx.bodySrc.locals.length + ctx.fieldTys.length ≤ i →
          Trusted.MirSemantics.getElem? ls' i = Trusted.MirSemantics.getElem? ls i) ∧
        (∀ j, j < count →
          Trusted.MirSemantics.getElem? ls' (ctx.bodySrc.locals.length + (start + j)) =
            some .dead) := by
  induction count with
  | zero =>
    intro start pos ls _ _ _
    refine ⟨ls, by rw [Nat.add_zero]; rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    intro j hj; exact False.elim (Nat.not_lt_zero j hj)
  | succ k ih =>
    intro start pos ls hSum hLen hStmts
    have hStartLt : start < ctx.fieldTys.length := by
      rw [← hSum, Nat.add_succ]
      exact Nat.lt_succ_of_le (Nat.le_add_right start k)
    have hStmt0 : Trusted.MirSemantics.getElem? bbTgt.statements pos =
        some (.storageDead (ctx.bodySrc.locals.length + start)) := by
      have h0 := hStmts 0 (Nat.zero_lt_succ k)
      rw [Nat.add_zero, Nat.add_zero] at h0
      exact h0
    have hIdxLt : ctx.bodySrc.locals.length + start < ls.length := by
      rw [hLen]; exact nat_lt_add_right _ (Nat.add_lt_add_left hStartLt _)
    have hNe0 : Nat.beq (ctx.bodySrc.locals.length + start) 0 = false :=
      nat_beq_false_of_ne (nat_add_ne_zero_left (sroaCtx_base_pos ctx))
    let ⟨ls1, hSet1⟩ := setElem?_some_of_lt ls (ctx.bodySrc.locals.length + start) .dead hIdxLt
    have hStep0 : evalStepTupleAssert ctx.pTgt 0
        { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos, locals := ls }],
          callerMem := mem } =
        .step { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos + 1, locals := ls1 }],
                callerMem := mem } := by
      unfold evalStepTupleAssert
      dsimp
      rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmt0]
      dsimp [evalStatementExt]
      rw [hNe0]; dsimp
      rw [hSet1]
    have hSumNext : (start + 1) + k = ctx.fieldTys.length := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]; exact hSum
    have hLen1 : ls1.length =
        ctx.bodySrc.locals.length + ctx.fieldTys.length + ctx.ovfTys.length := by
      rw [setElem?_length hSet1, hLen]
    let ⟨ls', hRest, hLen', hPre, hPost, hMid⟩ :=
      ih (start + 1) (pos + 1) ls1 hSumNext hLen1 (fun j hj => by
        have hS := hStmts (j + 1) (Nat.succ_lt_succ hj)
        have hP : pos + 1 + j = pos + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j]
        have hQ : start + 1 + j = start + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j]
        rw [hP, hQ]; exact hS)
    have hPosEq : pos + 1 + k = pos + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [hPosEq] at hRest
    refine ⟨ls', ?_, by rw [hLen', setElem?_length hSet1], ?_, ?_, ?_⟩
    · dsimp [evalTupleAssertFuel]
      rw [hStep0]; exact hRest
    · intro i hi
      have hLt1 : i < ctx.bodySrc.locals.length + (start + 1) := by
        rw [Nat.add_succ]; exact Nat.lt_succ_of_lt hi
      rw [hPre i hLt1]
      exact setElem?_getElem?_ne hSet1 (fun h => Nat.not_lt_of_ge (Nat.le_refl _) (h ▸ hi))
    · intro i hi
      rw [hPost i hi]
      have hNe : i ≠ ctx.bodySrc.locals.length + start := fun h =>
        Nat.not_lt_of_ge hi (h ▸ Nat.add_lt_add_left hStartLt _)
      exact setElem?_getElem?_ne hSet1 hNe
    · intro j hj
      cases j with
      | zero =>
        rw [Nat.add_zero]
        have hLt1 : ctx.bodySrc.locals.length + start < ctx.bodySrc.locals.length + (start + 1) := by
          rw [Nat.add_succ]; exact Nat.lt_succ_self _
        rw [hPre _ hLt1, setElem?_getElem?_same hSet1]
      | succ m =>
        have hAdd : start + (m + 1) = start + 1 + m := by rw [Nat.add_assoc, Nat.add_comm 1 m]
        rw [hAdd]
        exact hMid m (Nat.lt_of_succ_lt_succ hj)

private theorem sroa_exec_aggregate_loop (ctx : SroaCtx) {blk : BasicBlockId}
    {bbTgt : BasicBlock} {mem : CallerMemory}
    (hBbT : Trusted.MirSemantics.getElem? ctx.bodyTgt.basicBlocks blk = some bbTgt)
    (ops : List Operand) :
    ∀ (remTys : List MirTy) (idx pos : Nat) (lsSrc lsTgt : List LocalSlotExt),
      ops.length = remTys.length →
      (∀ j ft, Trusted.MirSemantics.getElem? remTys j = some ft →
        Trusted.MirSemantics.getElem? ctx.fieldTys (idx + j) = some ft) →
      ops.all (operandLocalsLt ctx.bodySrc.locals.length) = true →
      ops.all (fun o => !operandMentionsLocal ctx.plan.tupLocal o) = true →
      SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
        ctx.fieldTys ctx.ovfTys lsSrc lsTgt →
      (∀ j opnd, Trusted.MirSemantics.getElem? ops j = some opnd →
        Trusted.MirSemantics.getElem? bbTgt.statements (pos + j) =
          some (.assign ⟨ctx.bodySrc.locals.length + (idx + j), []⟩
            (.use (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd)))) →
      match evalAggregateInPlaceExt ctx.bodySrc.locals lsSrc ctx.plan.tupLocal idx ops remTys with
      | .error k =>
        ∃ d, 0 < d ∧
          evalTupleAssertFuel ctx.pTgt d
            { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos, locals := lsTgt }],
              callerMem := mem } = .fault k
      | .ok lsSrc' =>
        ∃ lsTgt',
          evalTupleAssertFuel ctx.pTgt ops.length
            { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos, locals := lsTgt }],
              callerMem := mem } =
          .step { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos + ops.length, locals := lsTgt' }],
                  callerMem := mem } ∧
          SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
            ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' := by
  induction ops with
  | nil =>
    intro remTys idx pos lsSrc lsTgt hLen _ _ _ hRel _
    cases remTys with
    | cons _ _ => cases hLen
    | nil =>
      dsimp [evalAggregateInPlaceExt, List.length]
      exact ⟨lsTgt, rfl, hRel⟩
  | cons opnd restOps ih =>
    intro remTys idx pos lsSrc lsTgt hLen hRem hAllLt hAllNoTup hRel hStmts
    cases remTys with
    | nil => cases hLen
    | cons ft restTys =>
      let ⟨hOpLt, hRestLt⟩ := bool_and_true hAllLt
      let ⟨hOpNoTup, hRestNoTup⟩ := bool_and_true hAllNoTup
      have hOpVal : operandTupleValid ctx.plan.tupLocal ctx.fieldTys opnd = true := by
        cases opnd with
        | constant _ => rfl
        | copy p | move p =>
          dsimp [operandMentionsLocal] at hOpNoTup
          dsimp [operandTupleValid]
          rw [bool_not_true hOpNoTup]; rfl
      have hFtAt : Trusted.MirSemantics.getElem? ctx.fieldTys idx = some ft := by
        have h0 := hRem 0 ft rfl
        rw [Nat.add_zero] at h0; exact h0
      have hIdxLt := getElem?_some_lt hFtAt
      have hSc := list_all_getElem? (sroaCtx_fieldTys_all_scalar ctx) hFtAt
      have hStmt0 : Trusted.MirSemantics.getElem? bbTgt.statements pos =
          some (.assign ⟨ctx.bodySrc.locals.length + idx, []⟩
            (.use (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd))) := by
        have h0 := hStmts 0 opnd rfl
        rw [Nat.add_zero, Nat.add_zero] at h0; exact h0
      have hStepHead : evalStepTupleAssert ctx.pTgt 0
          { frames := [{ defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos, locals := lsTgt }],
            callerMem := mem } =
          match evalOperandToSlotExt ctx.bodyTgt.locals lsTgt
              (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd) with
          | .error k => .fault k
          | .ok (srcTy, optVal, locals₁) =>
            if !MirTy.beq srcTy ft then .fault .unsupported
            else match optVal with
            | none => .fault .undefined
            | some v =>
              match writePlaceExt locals₁ (ctx.bodySrc.locals.length + idx) ft v with
              | .error k => .fault k
              | .ok locals₂ =>
                .step { frames := [{ defId := ctx.plan.defId, blockIdx := blk,
                                     stmtIdx := pos + 1, locals := locals₂ }],
                        callerMem := mem } := by
        unfold evalStepTupleAssert
        dsimp
        rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmt0]
        dsimp [evalStatementExt]
        rw [sroaCtx_localsTgt_getElem?_field ctx hIdxLt, hFtAt]
        cases ft with
        | tuple _ => cases hSc
        | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
          dsimp [evalRvalueExt]
          cases evalOperandToSlotExt ctx.bodyTgt.locals lsTgt
              (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd) with
          | error _ => rfl
          | ok triple =>
            cases triple with
            | mk sTy r1 =>
              cases r1 with
              | mk ov ls1 =>
                dsimp
                cases (!MirTy.beq sTy _) with
                | true => rfl
                | false =>
                  dsimp
                  cases ov with
                  | none => rfl
                  | some v =>
                    rfl
      dsimp [evalAggregateInPlaceExt]
      have hOpSim := sroa_evalOperandToSlotExt_sim ctx hRel hOpLt hOpVal
      cases hEvOp : evalOperandToSlotExt ctx.bodySrc.locals lsSrc opnd with
      | error k =>
        rw [hEvOp] at hOpSim; dsimp
        rw [hOpSim] at hStepHead
        exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStepHead]⟩
      | ok triple =>
        rw [hEvOp] at hOpSim
        cases triple with
        | mk srcTy r1 =>
          cases r1 with
          | mk ov lsSrc1 =>
            dsimp
            let ⟨lsTgt1, hEvTgt, hRel1, _⟩ := hOpSim
            rw [hEvTgt] at hStepHead
            dsimp at hStepHead
            cases hNeTy : (!MirTy.beq srcTy ft) with
            | true =>
              rw [hNeTy] at hStepHead; dsimp at hStepHead; dsimp
              exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStepHead]⟩
            | false =>
              rw [hNeTy] at hStepHead; dsimp at hStepHead; dsimp
              cases ov with
              | none =>
                dsimp at hStepHead; dsimp
                exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStepHead]⟩
              | some v =>
                dsimp at hStepHead; dsimp
                have hWSim := sroa_writeTupleFieldExt_tup_sim ctx (val := v) hRel1 hFtAt
                cases hWSrc : writeTupleFieldExt lsSrc1 ctx.plan.tupLocal idx ft v with
                | error k =>
                  rw [hWSrc] at hWSim; dsimp
                  rw [hWSim] at hStepHead
                  exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStepHead]⟩
                | ok lsSrc2 =>
                  rw [hWSrc] at hWSim; dsimp
                  let ⟨lsTgt2, hWTgt, hRel2⟩ := hWSim
                  rw [hWTgt] at hStepHead
                  dsimp at hStepHead
                  have hIH := ih restTys (idx + 1) (pos + 1) lsSrc2 lsTgt2
                    (Nat.succ.inj hLen)
                    (fun j ft' hj => by
                      have hAdd : idx + 1 + j = idx + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j]
                      rw [hAdd]; exact hRem (j + 1) ft' hj)
                    hRestLt hRestNoTup hRel2
                    (fun j o hj => by
                      have hS := hStmts (j + 1) o hj
                      have hP : pos + 1 + j = pos + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j]
                      have hI : idx + 1 + j = idx + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j]
                      rw [hP, hI]; exact hS)
                  cases hRec : evalAggregateInPlaceExt ctx.bodySrc.locals lsSrc2
                      ctx.plan.tupLocal (idx + 1) restOps restTys with
                  | error k =>
                    rw [hRec] at hIH; dsimp
                    let ⟨d, _, hD⟩ := hIH
                    refine ⟨d + 1, Nat.zero_lt_succ d, ?_⟩
                    dsimp [evalTupleAssertFuel]
                    rw [hStepHead]
                    exact hD
                  | ok lsSrcEnd =>
                    rw [hRec] at hIH; dsimp
                    let ⟨lsTgtEnd, hRestStep, hRelEnd⟩ := hIH
                    have hPosEq : pos + 1 + restOps.length = pos + (restOps.length + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 restOps.length]
                    rw [hPosEq] at hRestStep
                    refine ⟨lsTgtEnd, ?_, hRelEnd⟩
                    dsimp [List.length, evalTupleAssertFuel]
                    rw [hStepHead]
                    exact hRestStep

/-! #### 8-Step Unsigned `addWithOverflow` / `subWithOverflow` Simulation -/

private theorem checkVal_int_inv {v : Val} {w : IntWidth} {s : Bool}
    (h : checkVal v (.int w s) = true) :
    ∃ bits : BitVec 128, v = .scalar ⟨w, s, bits⟩ ∧ truncateBits w bits = bits := by
  cases v with
  | scalar sv =>
    unfold checkVal Val.ty? at h
    dsimp at h
    cases hWf : sv.wf with
    | false => rw [hWf] at h; cases h
    | true =>
      rw [hWf] at h; dsimp at h
      have hTyEq := mirTy_beq_eq h
      cases sv with
      | mk w' s' bits =>
        injection hTyEq with hW hS
        subst hW; subst hS
        unfold ScalarVal.wf at hWf
        dsimp at hWf
        exact ⟨bits, rfl, bitvec_beq_eq hWf⟩
  | ptr _ | bool _ | unit | tuple _ | bytes _ => cases h
  | enumVal ety vIdx =>
    unfold checkVal Val.ty? at h; dsimp at h
    cases hE : (enumAdmitted ety && Nat.blt vIdx ety.discriminants.length) with
    | false => rw [hE] at h; cases h
    | true => rw [hE] at h; cases h

private theorem sroa_exec_ovf_assign (ctx : SroaCtx) {blk : BasicBlockId}
    {bbSrc bbTgt : BasicBlock} {stmtIdx : Nat} {mem : CallerMemory}
    {op : BinOp} {lhs rhs : Operand} {w : IntWidth}
    (hAllSup : ctx.bodySrc.locals.all isSupportedTupleOrScalarTy = true)
    (hBbS : Trusted.MirSemantics.getElem? ctx.bodySrc.basicBlocks blk = some bbSrc)
    (hBbT : Trusted.MirSemantics.getElem? ctx.bodyTgt.basicBlocks blk = some bbTgt)
    (hStmtS : Trusted.MirSemantics.getElem? bbSrc.statements stmtIdx =
      some (.assign ⟨ctx.plan.tupLocal, []⟩ (.binaryOp op lhs rhs)))
    (hOpOvf : op = .addWithOverflow ∨ op = .subWithOverflow)
    (hFieldTys : ctx.fieldTys = [.int w false, .bool])
    (hLLt : operandLocalsLt ctx.bodySrc.locals.length lhs = true)
    (hRLt : operandLocalsLt ctx.bodySrc.locals.length rhs = true)
    (hLVal : operandTupleValid ctx.plan.tupLocal ctx.fieldTys lhs = true)
    (hRVal : operandTupleValid ctx.plan.tupLocal ctx.fieldTys rhs = true)
    (hLTy : optMirTyEq (operandStaticTy? ctx.bodySrc.locals lhs) (.int w false) = true)
    (hRTy : optMirTyEq (operandStaticTy? ctx.bodySrc.locals rhs) (.int w false) = true)
    {lsSrc lsTgt : List LocalSlotExt}
    (hWt : LocalsWellTyped ctx.bodySrc.locals lsSrc)
    (hRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys lsSrc lsTgt)
    (hPosStmt : ∀ j st,
      Trusted.MirSemantics.getElem?
        (lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length ctx.bodySrc.locals.length
          (ctx.bodySrc.locals.length + ctx.fieldTys.length)
          (.assign ⟨ctx.plan.tupLocal, []⟩ (.binaryOp op lhs rhs))) j = some st →
      Trusted.MirSemantics.getElem? bbTgt.statements (sroaStmtOffset ctx bbSrc stmtIdx + j) =
        some st) :
    let pos := sroaStmtOffset ctx bbSrc stmtIdx
    let fSrc : FrameStateExt := { defId := ctx.plan.defId, blockIdx := blk, stmtIdx := stmtIdx, locals := lsSrc }
    let fTgt : FrameStateExt := { defId := ctx.plan.defId, blockIdx := blk, stmtIdx := pos, locals := lsTgt }
    match evalStatementExt ctx.bodySrc fSrc mem (.assign ⟨ctx.plan.tupLocal, []⟩ (.binaryOp op lhs rhs)) with
    | .step sSrc' =>
      ∃ lsTgt',
        evalTupleAssertFuel ctx.pTgt 8 { frames := [fTgt], callerMem := mem } =
          .step { frames := [{ fTgt with stmtIdx := pos + 8, locals := lsTgt' }], callerMem := mem } ∧
        ∃ fSrc', sSrc' = { frames := [fSrc'], callerMem := mem } ∧
          fSrc'.defId = ctx.plan.defId ∧ fSrc'.blockIdx = blk ∧ fSrc'.stmtIdx = stmtIdx + 1 ∧
          SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length ctx.fieldTys ctx.ovfTys
            fSrc'.locals lsTgt'
    | .done _ => False
    | .fault fk =>
      ∃ d, 0 < d ∧ evalTupleAssertFuel ctx.pTgt d { frames := [fTgt], callerMem := mem } = .fault fk := by
  intro pos fSrc fTgt
  have hHasOvf : bodyHasTupleOvfAssign ctx.bodySrc ctx.plan.tupLocal = true := by
    unfold bodyHasTupleOvfAssign
    apply list_any_true_of_getElem? hBbS
    apply list_any_true_of_getElem? hStmtS
    dsimp
    rw [nat_beq_refl]
    cases hOpOvf with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hWOpt : unsignedOvfTupleWidth? ctx.fieldTys = some w := by
    rw [hFieldTys]; rfl
  let ⟨hOvfTysEq, hOvfTy0, hOvfTy1⟩ := sroaCtx_localsTgt_getElem?_ovf ctx hHasOvf hWOpt
  let ovf0 := ctx.bodySrc.locals.length + ctx.fieldTys.length
  have hFieldLen : ctx.fieldTys.length = 2 := by rw [hFieldTys]; rfl
  have hFty0 : Trusted.MirSemantics.getElem? ctx.fieldTys 0 = some (.int w false) := by
    rw [hFieldTys]; rfl
  have hFty1 : Trusted.MirSemantics.getElem? ctx.fieldTys 1 = some .bool := by
    rw [hFieldTys]; rfl
  have hBdyF0 : Trusted.MirSemantics.getElem? ctx.bodyTgt.locals ctx.bodySrc.locals.length =
      some (.int w false) := by
    have h0 := sroaCtx_localsTgt_getElem?_field ctx (j := 0) (by rw [hFieldLen]; decide)
    rw [Nat.add_zero, hFty0] at h0; exact h0
  have hBdyF1 : Trusted.MirSemantics.getElem? ctx.bodyTgt.locals (ctx.bodySrc.locals.length + 1) =
      some .bool := by
    have h1 := sroaCtx_localsTgt_getElem?_field ctx (j := 1) (by rw [hFieldLen]; decide)
    rw [hFty1] at h1; exact h1
  have hOvf0Lt : ovf0 < lsTgt.length := by
    rw [hRel.2.1, hOvfTysEq]; dsimp [List.length]
    exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  have hOvf1Lt : ovf0 + 1 < lsTgt.length := by
    rw [hRel.2.1, hOvfTysEq]; dsimp [List.length]
    exact Nat.lt_succ_self _
  have hOvf0Ne0 : Nat.beq ovf0 0 = false :=
    nat_beq_false_of_ne (nat_add_ne_zero_left (sroaCtx_base_pos ctx))
  have hStmts0 : Trusted.MirSemantics.getElem? bbTgt.statements pos =
      some (.storageLive ovf0) := by
    have h := hPosStmt 0 (.storageLive ovf0) (by
      cases hOpOvf with
      | inl h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl
      | inr h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
    rw [Nat.add_zero] at h; exact h
  have hStmts1 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 1) =
      some (.storageLive (ovf0 + 1)) :=
    hPosStmt 1 (.storageLive (ovf0 + 1)) (by
      cases hOpOvf with
      | inl h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl
      | inr h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
  have hStmts2 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 2) =
      some (.assign ⟨ovf0, []⟩ (.use (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length lhs))) :=
    hPosStmt 2 _ (by
      cases hOpOvf with
      | inl h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl
      | inr h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
  have hStmts3 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 3) =
      some (.assign ⟨ovf0 + 1, []⟩ (.use (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length rhs))) :=
    hPosStmt 3 _ (by
      cases hOpOvf with
      | inl h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl
      | inr h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
  have hStmts6 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 6) =
      some (.storageDead ovf0) :=
    hPosStmt 6 _ (by
      cases hOpOvf with
      | inl h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl
      | inr h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
  have hStmts7 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 7) =
      some (.storageDead (ovf0 + 1)) :=
    hPosStmt 7 _ (by
      cases hOpOvf with
      | inl h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl
      | inr h => subst h; dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
  -- Step 0 & Step 1: storageLive ovf0, storageLive (ovf0 + 1)
  let ⟨lsT1, hSetT1⟩ := setElem?_some_of_lt lsTgt ovf0 (.liveBase none) hOvf0Lt
  have hOvf1Lt1 : ovf0 + 1 < lsT1.length := by rw [setElem?_length hSetT1]; exact hOvf1Lt
  let ⟨lsT2, hSetT2⟩ := setElem?_some_of_lt lsT1 (ovf0 + 1) (.liveBase none) hOvf1Lt1
  have hRel2 : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys lsSrc lsT2 :=
    sroaRelLocals_set_ovf (sroaRelLocals_set_ovf hRel (Nat.le_refl _) hSetT1)
      (Nat.le_succ ovf0) hSetT2
  have hStep0 : evalStepTupleAssert ctx.pTgt 0 { frames := [fTgt], callerMem := mem } =
      .step { frames := [{ fTgt with stmtIdx := pos + 1, locals := lsT1 }], callerMem := mem } := by
    unfold evalStepTupleAssert; dsimp
    rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts0]
    dsimp [evalStatementExt]
    rw [hOvfTy0]; dsimp [liveUninitSlotExt, liveUninitFieldVal]
    rw [hSetT1]
  have hStep1 : evalStepTupleAssert ctx.pTgt 0
      { frames := [{ fTgt with stmtIdx := pos + 1, locals := lsT1 }], callerMem := mem } =
      .step { frames := [{ fTgt with stmtIdx := pos + 2, locals := lsT2 }], callerMem := mem } := by
    unfold evalStepTupleAssert; dsimp
    rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts1]
    dsimp [evalStatementExt]
    rw [hOvfTy1]; dsimp [liveUninitSlotExt, liveUninitFieldVal]
    rw [hSetT2]
  have hStep01 : evalTupleAssertFuel ctx.pTgt 2 { frames := [fTgt], callerMem := mem } =
      .step { frames := [{ fTgt with stmtIdx := pos + 2, locals := lsT2 }], callerMem := mem } := by
    dsimp [evalTupleAssertFuel]; rw [hStep0]; dsimp [evalTupleAssertFuel]; rw [hStep1]
  have hOvf0In2 : Trusted.MirSemantics.getElem? lsT2 ovf0 = some (.liveBase none) := by
    rw [setElem?_getElem?_ne hSetT2 (nat_ne_succ_self ovf0),
        setElem?_getElem?_same hSetT1]
  have hOvf1In2 : Trusted.MirSemantics.getElem? lsT2 (ovf0 + 1) = some (.liveBase none) :=
    setElem?_getElem?_same hSetT2
  -- Unfold LHS evalStatementExt on source
  dsimp [evalStatementExt]
  rw [ctx.hTupTy]; dsimp [isWholeLocalSelfUse, evalRvalueExt]
  -- Evaluate lhs (Step 2)
  have hLSim := sroa_evalOperandToSlotExt_sim ctx hRel2 hLLt hLVal
  have hStep2Base : evalStepTupleAssert ctx.pTgt 0
      { frames := [{ fTgt with stmtIdx := pos + 2, locals := lsT2 }], callerMem := mem } =
      match evalOperandToSlotExt ctx.bodyTgt.locals lsT2
          (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length lhs) with
      | .error k => .fault k
      | .ok (srcTy, ov, ls') =>
        if !MirTy.beq srcTy (.int w false) then .fault .unsupported
        else match ov with
        | none => .fault .undefined
        | some v =>
          match writePlaceExt ls' ovf0 (.int w false) v with
          | .error k => .fault k
          | .ok ls'' =>
            .step { frames := [{ fTgt with stmtIdx := pos + 3, locals := ls'' }], callerMem := mem } := by
    unfold evalStepTupleAssert; dsimp
    rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts2]
    dsimp [evalStatementExt]
    rw [hOvfTy0]; dsimp [evalRvalueExt]
    cases evalOperandToSlotExt ctx.bodyTgt.locals lsT2
        (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length lhs) with
    | error _ => rfl
    | ok triple =>
      cases triple with
      | mk sTy r1 =>
        cases r1 with
        | mk ov ls' =>
          dsimp
          cases (!MirTy.beq sTy (.int w false)) with
          | true => rfl
          | false =>
            dsimp
            cases ov with
            | none => rfl
            | some v =>
              rfl
  unfold evalPrimitiveOperandExt
  cases hEvL : evalOperandToSlotExt ctx.bodySrc.locals lsSrc lhs with
  | error k =>
    rw [hEvL] at hLSim; dsimp
    rw [hLSim] at hStep2Base
    refine ⟨3, Nat.zero_lt_succ 2, ?_⟩
    rw [show (3 : Nat) = 2 + 1 from rfl, evalTupleAssertFuel_add, hStep01]
    dsimp [evalTupleAssertFuel]; rw [hStep2Base]
  | ok trL =>
    rw [hEvL] at hLSim
    cases trL with
    | mk lTy restL =>
      cases restL with
      | mk lOv lsSrc1 =>
        dsimp
        let ⟨lsT3a, hEvLTgt, hRel3a, hPresL⟩ := hLSim
        have hLTyEq : lTy = .int w false := by
          have hSt := evalOperandToSlotExt_staticTy hEvL
          rw [hSt] at hLTy; dsimp [optMirTyEq] at hLTy
          exact mirTy_beq_eq hLTy
        subst hLTyEq
        have hPrimW : (!isPrimitiveReadableTy (.int w false)) = false := rfl
        rw [if_bool_false hPrimW]
        rw [hEvLTgt] at hStep2Base
        dsimp at hStep2Base
        rw [mirTy_beq_refl (.int w false)] at hStep2Base
        dsimp at hStep2Base
        cases lOv with
        | none =>
          dsimp at hStep2Base; dsimp
          refine ⟨3, Nat.zero_lt_succ 2, ?_⟩
          rw [show (3 : Nat) = 2 + 1 from rfl, evalTupleAssertFuel_add, hStep01]
          dsimp [evalTupleAssertFuel]; rw [hStep2Base]
        | some lVal =>
          dsimp at hStep2Base; dsimp
          let ⟨hWt1, hLCheckExt⟩ := evalOperandToSlotExt_preserves_wt hAllSup hWt hEvL
          have hLCheck : checkVal lVal (.int w false) = true := hLCheckExt lVal rfl
          let ⟨lb, hLValEq, _⟩ := checkVal_int_inv hLCheck
          have hOvf0In3a : Trusted.MirSemantics.getElem? lsT3a ovf0 = some (.liveBase none) := by
            rw [hPresL ovf0 (Nat.le_refl _), hOvf0In2]
          have hOvf1In3a : Trusted.MirSemantics.getElem? lsT3a (ovf0 + 1) = some (.liveBase none) := by
            rw [hPresL (ovf0 + 1) (Nat.le_succ ovf0), hOvf1In2]
          have hOvf0Lt3a : ovf0 < lsT3a.length := getElem?_some_lt hOvf0In3a
          let ⟨lsT3, hSetT3⟩ := setElem?_some_of_lt lsT3a ovf0 (.liveBase (some lVal)) hOvf0Lt3a
          have hWriteT3 : writePlaceExt lsT3a ovf0 (.int w false) lVal = .ok lsT3 := by
            unfold writePlaceExt checkValExt
            dsimp
            rw [hLCheck]; dsimp
            rw [hOvf0In3a, hSetT3]
          rw [hWriteT3] at hStep2Base
          have hRel3 : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
              ctx.fieldTys ctx.ovfTys lsSrc1 lsT3 :=
            sroaRelLocals_set_ovf hRel3a (Nat.le_refl _) hSetT3
          have hStep012 : evalTupleAssertFuel ctx.pTgt 3 { frames := [fTgt], callerMem := mem } =
              .step { frames := [{ fTgt with stmtIdx := pos + 3, locals := lsT3 }], callerMem := mem } := by
            rw [show (3 : Nat) = 2 + 1 from rfl, evalTupleAssertFuel_add, hStep01]
            dsimp [evalTupleAssertFuel]; rw [hStep2Base]
          have hOvf0In3 : Trusted.MirSemantics.getElem? lsT3 ovf0 = some (.liveBase (some lVal)) :=
            setElem?_getElem?_same hSetT3
          have hOvf1In3 : Trusted.MirSemantics.getElem? lsT3 (ovf0 + 1) = some (.liveBase none) := by
            rw [setElem?_getElem?_ne hSetT3 (nat_succ_ne_self ovf0),
                hOvf1In3a]
          -- Evaluate rhs (Step 3)
          have hRSim := sroa_evalOperandToSlotExt_sim ctx hRel3 hRLt hRVal
          have hStep3Base : evalStepTupleAssert ctx.pTgt 0
              { frames := [{ fTgt with stmtIdx := pos + 3, locals := lsT3 }], callerMem := mem } =
              match evalOperandToSlotExt ctx.bodyTgt.locals lsT3
                  (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length rhs) with
              | .error k => .fault k
              | .ok (srcTy, ov, ls') =>
                if !MirTy.beq srcTy (.int w false) then .fault .unsupported
                else match ov with
                | none => .fault .undefined
                | some v =>
                  match writePlaceExt ls' (ovf0 + 1) (.int w false) v with
                  | .error k => .fault k
                  | .ok ls'' =>
                    .step { frames := [{ fTgt with stmtIdx := pos + 4, locals := ls'' }], callerMem := mem } := by
            unfold evalStepTupleAssert; dsimp
            rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts3]
            dsimp [evalStatementExt]
            rw [hOvfTy1]; dsimp [evalRvalueExt]
            cases evalOperandToSlotExt ctx.bodyTgt.locals lsT3
                (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length rhs) with
            | error _ => rfl
            | ok triple =>
              cases triple with
              | mk sTy r1 =>
                cases r1 with
                | mk ov ls' =>
                  dsimp
                  cases (!MirTy.beq sTy (.int w false)) with
                  | true => rfl
                  | false =>
                    dsimp
                    cases ov with
                    | none => rfl
                    | some v =>
                      rfl
          cases hEvR : evalOperandToSlotExt ctx.bodySrc.locals lsSrc1 rhs with
          | error k =>
            rw [hEvR] at hRSim; dsimp
            rw [hRSim] at hStep3Base
            refine ⟨4, Nat.zero_lt_succ 3, ?_⟩
            rw [show (4 : Nat) = 3 + 1 from rfl, evalTupleAssertFuel_add, hStep012]
            dsimp [evalTupleAssertFuel]; rw [hStep3Base]
          | ok trR =>
            rw [hEvR] at hRSim
            cases trR with
            | mk rTy restR =>
              cases restR with
              | mk rOv lsSrc2 =>
                dsimp
                let ⟨lsT4a, hEvRTgt, hRel4a, hPresR⟩ := hRSim
                have hRTyEq : rTy = .int w false := by
                  have hSt := evalOperandToSlotExt_staticTy hEvR
                  rw [hSt] at hRTy; dsimp [optMirTyEq] at hRTy
                  exact mirTy_beq_eq hRTy
                subst hRTyEq
                have hPrimW2 : (!isPrimitiveReadableTy (.int w false)) = false := rfl
                rw [if_bool_false hPrimW2]
                rw [hEvRTgt] at hStep3Base
                dsimp at hStep3Base
                rw [mirTy_beq_refl (.int w false)] at hStep3Base
                dsimp at hStep3Base
                cases rOv with
                | none =>
                  dsimp at hStep3Base; dsimp
                  refine ⟨4, Nat.zero_lt_succ 3, ?_⟩
                  rw [show (4 : Nat) = 3 + 1 from rfl, evalTupleAssertFuel_add, hStep012]
                  dsimp [evalTupleAssertFuel]; rw [hStep3Base]
                | some rVal =>
                  dsimp at hStep3Base; dsimp
                  let ⟨_, hRCheckExt⟩ := evalOperandToSlotExt_preserves_wt hAllSup hWt1 hEvR
                  have hRCheck : checkVal rVal (.int w false) = true := hRCheckExt rVal rfl
                  let ⟨rb, hRValEq, _⟩ := checkVal_int_inv hRCheck
                  have hOvf0In4a : Trusted.MirSemantics.getElem? lsT4a ovf0 = some (.liveBase (some lVal)) := by
                    rw [hPresR ovf0 (Nat.le_refl _), hOvf0In3]
                  have hOvf1In4a : Trusted.MirSemantics.getElem? lsT4a (ovf0 + 1) = some (.liveBase none) := by
                    rw [hPresR (ovf0 + 1) (Nat.le_succ ovf0), hOvf1In3]
                  have hOvf1Lt4a : ovf0 + 1 < lsT4a.length := getElem?_some_lt hOvf1In4a
                  let ⟨lsT4, hSetT4⟩ := setElem?_some_of_lt lsT4a (ovf0 + 1) (.liveBase (some rVal)) hOvf1Lt4a
                  have hWriteT4 : writePlaceExt lsT4a (ovf0 + 1) (.int w false) rVal = .ok lsT4 := by
                    unfold writePlaceExt checkValExt
                    dsimp
                    rw [hRCheck]; dsimp
                    rw [hOvf1In4a, hSetT4]
                  rw [hWriteT4] at hStep3Base
                  have hRel4 : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
                      ctx.fieldTys ctx.ovfTys lsSrc2 lsT4 :=
                    sroaRelLocals_set_ovf hRel4a (Nat.le_succ ovf0) hSetT4
                  have hStep0123 : evalTupleAssertFuel ctx.pTgt 4 { frames := [fTgt], callerMem := mem } =
                      .step { frames := [{ fTgt with stmtIdx := pos + 4, locals := lsT4 }], callerMem := mem } := by
                    rw [show (4 : Nat) = 3 + 1 from rfl, evalTupleAssertFuel_add, hStep012]
                    dsimp [evalTupleAssertFuel]; rw [hStep3Base]
                  have hOvf0In4 : Trusted.MirSemantics.getElem? lsT4 ovf0 = some (.liveBase (some lVal)) := by
                    rw [setElem?_getElem?_ne hSetT4 (nat_ne_succ_self ovf0),
                        hOvf0In4a]
                  have hOvf1In4 : Trusted.MirSemantics.getElem? lsT4 (ovf0 + 1) = some (.liveBase (some rVal)) :=
                    setElem?_getElem?_same hSetT4
                  -- Steps 4, 5, 6, 7: split on op = addWithOverflow vs subWithOverflow
                  subst hLValEq; subst hRValEq
                  have hBaseLt4 : ctx.bodySrc.locals.length < lsT4.length := by
                    rw [hRel4.2.1, hFieldLen]; exact nat_lt_add_right _ (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
                  have hBase1Lt4 : ctx.bodySrc.locals.length + 1 < lsT4.length := by
                    rw [hRel4.2.1, hFieldLen]; exact nat_lt_add_right _ (Nat.lt_succ_self _)
                  have hBaseNeOvf0 : ctx.bodySrc.locals.length ≠ ovf0 := fun h => by
                    have hlt : ctx.bodySrc.locals.length < ovf0 := by
                      change ctx.bodySrc.locals.length < ctx.bodySrc.locals.length + ctx.fieldTys.length
                      rw [hFieldLen]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
                    rw [h] at hlt
                    exact Nat.not_lt_of_ge (Nat.le_refl _) hlt
                  have hBaseNeOvf1 : ctx.bodySrc.locals.length ≠ ovf0 + 1 := fun h => by
                    have hlt : ctx.bodySrc.locals.length < ovf0 + 1 := by
                      change ctx.bodySrc.locals.length < ctx.bodySrc.locals.length + ctx.fieldTys.length + 1
                      rw [hFieldLen]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
                    rw [h] at hlt
                    exact Nat.not_lt_of_ge (Nat.le_refl _) hlt
                  cases hOpOvf with
                  | inl hAdd =>
                    subst hAdd
                    let ⟨hOvfEval, hAddEval, hLtEval, hResCheck⟩ := unsigned_addWithOverflow_eq w lb rb
                    let resSv : ScalarVal := ⟨w, false, truncateBits w (bvOfInt 128
                      (decodeScalar ⟨w, false, lb⟩ + decodeScalar ⟨w, false, rb⟩))⟩
                    let ovfB : Bool := decide (decodeScalar resSv < decodeScalar ⟨w, false, lb⟩)
                    dsimp [isWithOverflowBinOp]
                    rw [hOvfEval]; dsimp
                    have hCheckPair : checkValExt (.tuple [.scalar resSv, .bool ovfB])
                        (.tuple ctx.fieldTys) = true := by
                      unfold checkValExt; dsimp
                      rw [ctx.hFlatTup, hFieldTys]
                      dsimp [checkArgsMatch]
                      rw [hResCheck]; rfl
                    have hStmts4 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 4) =
                        some (.assign ⟨ctx.bodySrc.locals.length, []⟩
                          (.binaryOp .add (.copy ⟨ovf0, []⟩) (.copy ⟨ovf0 + 1, []⟩))) :=
                      hPosStmt 4 _ (by dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
                    have hStmts5 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 5) =
                        some (.assign ⟨ctx.bodySrc.locals.length + 1, []⟩
                          (.binaryOp .lt (.copy ⟨ctx.bodySrc.locals.length, []⟩) (.copy ⟨ovf0, []⟩))) :=
                      hPosStmt 5 _ (by dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
                    have hStep4Base : evalStepTupleAssert ctx.pTgt 0
                        { frames := [{ fTgt with stmtIdx := pos + 4, locals := lsT4 }], callerMem := mem } =
                        match writePlaceExt lsT4 ctx.bodySrc.locals.length (.int w false) (.scalar resSv) with
                        | .error k => .fault k
                        | .ok ls' =>
                          .step { frames := [{ fTgt with stmtIdx := pos + 5, locals := ls' }], callerMem := mem } := by
                      unfold evalStepTupleAssert; dsimp
                      rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts4]
                      dsimp [evalStatementExt]
                      rw [hBdyF0]
                      dsimp [evalRvalueExt, evalPrimitiveOperandExt, evalOperandToSlotExt]
                      rw [hOvfTy0, hOvf0In4]
                      dsimp [isFlatTupleTy, isPrimitiveReadableTy_int, isPrimitiveReadableTy_bool]
                      rw [hOvfTy1, hOvf1In4]
                      dsimp [isFlatTupleTy, isPrimitiveReadableTy_int, isPrimitiveReadableTy_bool, isWithOverflowBinOp]
                      rw [hAddEval]
                    unfold writePlaceExt
                    rw [hCheckPair]; dsimp
                    have hTup4 := hRel4.2.2.2
                    cases hSrcT : Trusted.MirSemantics.getElem? lsSrc2 ctx.plan.tupLocal with
                    | none => rw [hSrcT] at hTup4; exact False.elim hTup4
                    | some sl =>
                      rw [hSrcT] at hTup4
                      cases sl with
                      | liveBase _ => exact False.elim hTup4
                      | dead =>
                        have hF0Dead : Trusted.MirSemantics.getElem? lsT4 ctx.bodySrc.locals.length =
                            some .dead := by
                          have h0 := hTup4 0 (by rw [hFieldLen]; decide)
                          rw [Nat.add_zero] at h0; exact h0
                        have hW4Dead : writePlaceExt lsT4 ctx.bodySrc.locals.length (.int w false)
                            (.scalar resSv) = .error .undefined := by
                          unfold writePlaceExt checkValExt; dsimp; rw [hResCheck]; dsimp; rw [hF0Dead]
                        rw [hW4Dead] at hStep4Base
                        refine ⟨5, Nat.zero_lt_succ 4, ?_⟩
                        rw [show (5 : Nat) = 4 + 1 from rfl, evalTupleAssertFuel_add, hStep0123]
                        dsimp [evalTupleAssertFuel]; rw [hStep4Base]
                      | liveTuple fields =>
                        have hF0Live : ∃ ov0, Trusted.MirSemantics.getElem? lsT4 ctx.bodySrc.locals.length =
                            some (.liveBase ov0) := by
                          have hFLt0 : 0 < fields.length := by rw [hTup4.1, hFieldLen]; decide
                          let ⟨ov0, hOv0⟩ := getElem?_some_of_lt fields 0 hFLt0
                          have h0 := hTup4.2 0 (by rw [hFieldLen]; decide)
                          rw [Nat.add_zero, hOv0] at h0
                          exact ⟨ov0, h0⟩
                        have hF1Live : ∃ ov1, Trusted.MirSemantics.getElem? lsT4 (ctx.bodySrc.locals.length + 1) =
                            some (.liveBase ov1) := by
                          have hFLt1 : 1 < fields.length := by rw [hTup4.1, hFieldLen]; decide
                          let ⟨ov1, hOv1⟩ := getElem?_some_of_lt fields 1 hFLt1
                          have h1 := hTup4.2 1 (by rw [hFieldLen]; decide)
                          rw [hOv1] at h1
                          exact ⟨ov1, h1⟩
                        let ⟨ov0, hF0In4⟩ := hF0Live
                        let ⟨ov1, hF1In4⟩ := hF1Live
                        let ⟨lsT5, hSetT5⟩ := setElem?_some_of_lt lsT4 ctx.bodySrc.locals.length
                          (.liveBase (some (.scalar resSv))) hBaseLt4
                        have hW4Ok : writePlaceExt lsT4 ctx.bodySrc.locals.length (.int w false)
                            (.scalar resSv) = .ok lsT5 := by
                          unfold writePlaceExt checkValExt; dsimp; rw [hResCheck]; dsimp
                          rw [hF0In4, hSetT5]
                        rw [hW4Ok] at hStep4Base
                        have hBase1Lt5 : ctx.bodySrc.locals.length + 1 < lsT5.length := by
                          rw [setElem?_length hSetT5]; exact hBase1Lt4
                        let ⟨lsT6, hSetT6⟩ := setElem?_some_of_lt lsT5 (ctx.bodySrc.locals.length + 1)
                          (.liveBase (some (.bool ovfB))) hBase1Lt5
                        have hStep5 : evalStepTupleAssert ctx.pTgt 0
                            { frames := [{ fTgt with stmtIdx := pos + 5, locals := lsT5 }], callerMem := mem } =
                            .step { frames := [{ fTgt with stmtIdx := pos + 6, locals := lsT6 }], callerMem := mem } := by
                          unfold evalStepTupleAssert; dsimp
                          rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts5]
                          dsimp [evalStatementExt]
                          rw [hBdyF1]
                          dsimp [evalRvalueExt, evalPrimitiveOperandExt, evalOperandToSlotExt]
                          rw [hBdyF0, setElem?_getElem?_same hSetT5]
                          dsimp [isFlatTupleTy, isPrimitiveReadableTy_int, isPrimitiveReadableTy_bool]
                          rw [hOvfTy0, setElem?_getElem?_ne hSetT5 (fun h => hBaseNeOvf0 h.symm), hOvf0In4]
                          dsimp [isFlatTupleTy, isPrimitiveReadableTy_int, isPrimitiveReadableTy_bool, isWithOverflowBinOp]
                          rw [hLtEval]; dsimp
                          unfold writePlaceExt checkValExt; dsimp [checkVal, Val.ty?, MirTy.beq]
                          rw [setElem?_getElem?_ne hSetT5 (nat_succ_ne_self _), hF1In4, hSetT6]
                        have hOvf0Lt6 : ovf0 < lsT6.length := by
                          rw [setElem?_length hSetT6, setElem?_length hSetT5, hRel4.2.1, hOvfTysEq]
                          dsimp [List.length]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
                        let ⟨lsT7, hSetT7⟩ := setElem?_some_of_lt lsT6 ovf0 .dead hOvf0Lt6
                        have hOvf1Lt7 : ovf0 + 1 < lsT7.length := by
                          rw [setElem?_length hSetT7, setElem?_length hSetT6, setElem?_length hSetT5,
                              hRel4.2.1, hOvfTysEq]
                          dsimp [List.length]; exact Nat.lt_succ_self _
                        let ⟨lsT8, hSetT8⟩ := setElem?_some_of_lt lsT7 (ovf0 + 1) .dead hOvf1Lt7
                        have hStep6 : evalStepTupleAssert ctx.pTgt 0
                            { frames := [{ fTgt with stmtIdx := pos + 6, locals := lsT6 }], callerMem := mem } =
                            .step { frames := [{ fTgt with stmtIdx := pos + 7, locals := lsT7 }], callerMem := mem } := by
                          unfold evalStepTupleAssert; dsimp
                          rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts6]
                          dsimp [evalStatementExt]; rw [hOvf0Ne0]; dsimp; rw [hSetT7]
                        have hStep7 : evalStepTupleAssert ctx.pTgt 0
                            { frames := [{ fTgt with stmtIdx := pos + 7, locals := lsT7 }], callerMem := mem } =
                            .step { frames := [{ fTgt with stmtIdx := pos + 8, locals := lsT8 }], callerMem := mem } := by
                          unfold evalStepTupleAssert; dsimp
                          rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts7]
                          dsimp [evalStatementExt]; rw [hSetT8]
                        have hTupLtS2 : ctx.plan.tupLocal < lsSrc2.length := by
                          rw [hRel4.1]; exact ctx.hTupLt
                        let ⟨lsSrc3, hSetSrc3⟩ := setElem?_some_of_lt lsSrc2 ctx.plan.tupLocal
                          (.liveTuple [some (.scalar resSv), some (.bool ovfB)]) hTupLtS2
                        dsimp [List.map]; rw [hSetSrc3]; dsimp
                        have hRelFinal : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
                            ctx.fieldTys ctx.ovfTys lsSrc3 lsT8 := by
                          have hLen8 : lsT8.length =
                              ctx.bodySrc.locals.length + ctx.fieldTys.length + ctx.ovfTys.length := by
                            rw [setElem?_length hSetT8, setElem?_length hSetT7,
                                setElem?_length hSetT6, setElem?_length hSetT5, hRel4.2.1]
                          refine ⟨by rw [setElem?_length hSetSrc3, hRel4.1], hLen8, ?_, ?_⟩
                          · intro i hi hINe
                            have hNe0 : i ≠ ctx.bodySrc.locals.length := fun h => by
                              have hi' := hi; rw [h] at hi'; exact Nat.not_lt_of_ge (Nat.le_refl _) hi'
                            have hNe1 : i ≠ ctx.bodySrc.locals.length + 1 := fun h => by
                              have hi' := hi; rw [h] at hi'; exact Nat.not_lt_of_ge (Nat.le_succ _) hi'
                            have hNeO0 : i ≠ ovf0 := fun h => by
                              have hi' := hi; rw [h] at hi'; exact Nat.not_lt_of_ge (Nat.le_add_right _ _) hi'
                            have hNeO1 : i ≠ ovf0 + 1 := fun h => by
                              have hi' := hi; rw [h] at hi'
                              exact Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)) hi'
                            rw [setElem?_getElem?_ne hSetT8 hNeO1, setElem?_getElem?_ne hSetT7 hNeO0,
                                setElem?_getElem?_ne hSetT6 hNe1, setElem?_getElem?_ne hSetT5 hNe0,
                                setElem?_getElem?_ne hSetSrc3 hINe]
                            exact hRel4.2.2.1 i hi hINe
                          · rw [setElem?_getElem?_same hSetSrc3]
                            refine ⟨by rw [hFieldLen]; rfl, ?_⟩
                            intro j hJLt
                            rw [hFieldLen] at hJLt
                            cases j with
                            | zero =>
                              rw [Nat.add_zero]
                              rw [setElem?_getElem?_ne hSetT8 hBaseNeOvf1,
                                  setElem?_getElem?_ne hSetT7 hBaseNeOvf0,
                                  setElem?_getElem?_ne hSetT6 (nat_ne_succ_self _),
                                  setElem?_getElem?_same hSetT5]; rfl
                            | succ k =>
                              cases k with
                              | zero =>
                                have hB1NeO0 : ctx.bodySrc.locals.length + 1 ≠ ovf0 := fun h => by
                                  have hlt : ctx.bodySrc.locals.length + 1 < ovf0 := by
                                    change ctx.bodySrc.locals.length + 1 < ctx.bodySrc.locals.length + ctx.fieldTys.length
                                    rw [hFieldLen]; exact Nat.lt_succ_self _
                                  rw [h] at hlt; exact Nat.not_lt_of_ge (Nat.le_refl _) hlt
                                have hB1NeO1 : ctx.bodySrc.locals.length + 1 ≠ ovf0 + 1 := fun h => by
                                  have hlt : ctx.bodySrc.locals.length + 1 < ovf0 + 1 := by
                                    change ctx.bodySrc.locals.length + 1 < ctx.bodySrc.locals.length + ctx.fieldTys.length + 1
                                    rw [hFieldLen]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
                                  rw [h] at hlt; exact Nat.not_lt_of_ge (Nat.le_refl _) hlt
                                rw [setElem?_getElem?_ne hSetT8 hB1NeO1,
                                    setElem?_getElem?_ne hSetT7 hB1NeO0,
                                    setElem?_getElem?_same hSetT6]; rfl
                              | succ m =>
                                exact False.elim (Nat.not_lt_zero m
                                  (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hJLt)))
                        refine ⟨lsT8, ?_, _, rfl, rfl, rfl, rfl, hRelFinal⟩
                        rw [show (8 : Nat) = 4 + 4 from rfl, evalTupleAssertFuel_add, hStep0123]
                        dsimp [evalTupleAssertFuel]
                        rw [hStep4Base]; dsimp [evalTupleAssertFuel]; rw [hStep5]; dsimp [evalTupleAssertFuel]; rw [hStep6]; dsimp [evalTupleAssertFuel]; rw [hStep7]
                  | inr hSub =>
                    subst hSub
                    let ⟨hOvfEval, hSubEval, hLtEval, hResCheck⟩ := unsigned_subWithOverflow_eq w lb rb
                    let resSv : ScalarVal := ⟨w, false, truncateBits w (bvOfInt 128
                      (decodeScalar ⟨w, false, lb⟩ - decodeScalar ⟨w, false, rb⟩))⟩
                    let ovfB : Bool := decide (decodeScalar ⟨w, false, lb⟩ < decodeScalar ⟨w, false, rb⟩)
                    dsimp [isWithOverflowBinOp]
                    rw [hOvfEval]; dsimp
                    have hCheckPair : checkValExt (.tuple [.scalar resSv, .bool ovfB])
                        (.tuple ctx.fieldTys) = true := by
                      unfold checkValExt; dsimp
                      rw [ctx.hFlatTup, hFieldTys]
                      dsimp [checkArgsMatch]
                      rw [hResCheck]; rfl
                    have hStmts4 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 4) =
                        some (.assign ⟨ctx.bodySrc.locals.length, []⟩
                          (.binaryOp .sub (.copy ⟨ovf0, []⟩) (.copy ⟨ovf0 + 1, []⟩))) :=
                      hPosStmt 4 _ (by dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
                    have hStmts5 : Trusted.MirSemantics.getElem? bbTgt.statements (pos + 5) =
                        some (.assign ⟨ctx.bodySrc.locals.length + 1, []⟩
                          (.binaryOp .lt (.copy ⟨ovf0, []⟩) (.copy ⟨ovf0 + 1, []⟩))) :=
                      hPosStmt 5 _ (by dsimp [lowerSroaStmt]; rw [nat_beq_refl]; rfl)
                    have hStep4Base : evalStepTupleAssert ctx.pTgt 0
                        { frames := [{ fTgt with stmtIdx := pos + 4, locals := lsT4 }], callerMem := mem } =
                        match writePlaceExt lsT4 ctx.bodySrc.locals.length (.int w false) (.scalar resSv) with
                        | .error k => .fault k
                        | .ok ls' =>
                          .step { frames := [{ fTgt with stmtIdx := pos + 5, locals := ls' }], callerMem := mem } := by
                      unfold evalStepTupleAssert; dsimp
                      rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts4]
                      dsimp [evalStatementExt]
                      rw [hBdyF0]
                      dsimp [evalRvalueExt, evalPrimitiveOperandExt, evalOperandToSlotExt]
                      rw [hOvfTy0, hOvf0In4]
                      dsimp [isFlatTupleTy, isPrimitiveReadableTy_int, isPrimitiveReadableTy_bool]
                      rw [hOvfTy1, hOvf1In4]
                      dsimp [isFlatTupleTy, isPrimitiveReadableTy_int, isPrimitiveReadableTy_bool, isWithOverflowBinOp]
                      rw [hSubEval]
                    unfold writePlaceExt
                    rw [hCheckPair]; dsimp
                    have hTup4 := hRel4.2.2.2
                    cases hSrcT : Trusted.MirSemantics.getElem? lsSrc2 ctx.plan.tupLocal with
                    | none => rw [hSrcT] at hTup4; exact False.elim hTup4
                    | some sl =>
                      rw [hSrcT] at hTup4
                      cases sl with
                      | liveBase _ => exact False.elim hTup4
                      | dead =>
                        have hF0Dead : Trusted.MirSemantics.getElem? lsT4 ctx.bodySrc.locals.length =
                            some .dead := by
                          have h0 := hTup4 0 (by rw [hFieldLen]; decide)
                          rw [Nat.add_zero] at h0; exact h0
                        have hW4Dead : writePlaceExt lsT4 ctx.bodySrc.locals.length (.int w false)
                            (.scalar resSv) = .error .undefined := by
                          unfold writePlaceExt checkValExt; dsimp; rw [hResCheck]; dsimp; rw [hF0Dead]
                        rw [hW4Dead] at hStep4Base
                        refine ⟨5, Nat.zero_lt_succ 4, ?_⟩
                        rw [show (5 : Nat) = 4 + 1 from rfl, evalTupleAssertFuel_add, hStep0123]
                        dsimp [evalTupleAssertFuel]; rw [hStep4Base]
                      | liveTuple fields =>
                        have hF0Live : ∃ ov0, Trusted.MirSemantics.getElem? lsT4 ctx.bodySrc.locals.length =
                            some (.liveBase ov0) := by
                          have hFLt0 : 0 < fields.length := by rw [hTup4.1, hFieldLen]; decide
                          let ⟨ov0, hOv0⟩ := getElem?_some_of_lt fields 0 hFLt0
                          have h0 := hTup4.2 0 (by rw [hFieldLen]; decide)
                          rw [Nat.add_zero, hOv0] at h0
                          exact ⟨ov0, h0⟩
                        have hF1Live : ∃ ov1, Trusted.MirSemantics.getElem? lsT4 (ctx.bodySrc.locals.length + 1) =
                            some (.liveBase ov1) := by
                          have hFLt1 : 1 < fields.length := by rw [hTup4.1, hFieldLen]; decide
                          let ⟨ov1, hOv1⟩ := getElem?_some_of_lt fields 1 hFLt1
                          have h1 := hTup4.2 1 (by rw [hFieldLen]; decide)
                          rw [hOv1] at h1
                          exact ⟨ov1, h1⟩
                        let ⟨ov0, hF0In4⟩ := hF0Live
                        let ⟨ov1, hF1In4⟩ := hF1Live
                        let ⟨lsT5, hSetT5⟩ := setElem?_some_of_lt lsT4 ctx.bodySrc.locals.length
                          (.liveBase (some (.scalar resSv))) hBaseLt4
                        have hW4Ok : writePlaceExt lsT4 ctx.bodySrc.locals.length (.int w false)
                            (.scalar resSv) = .ok lsT5 := by
                          unfold writePlaceExt checkValExt; dsimp; rw [hResCheck]; dsimp
                          rw [hF0In4, hSetT5]
                        rw [hW4Ok] at hStep4Base
                        have hBase1Lt5 : ctx.bodySrc.locals.length + 1 < lsT5.length := by
                          rw [setElem?_length hSetT5]; exact hBase1Lt4
                        let ⟨lsT6, hSetT6⟩ := setElem?_some_of_lt lsT5 (ctx.bodySrc.locals.length + 1)
                          (.liveBase (some (.bool ovfB))) hBase1Lt5
                        have hStep5 : evalStepTupleAssert ctx.pTgt 0
                            { frames := [{ fTgt with stmtIdx := pos + 5, locals := lsT5 }], callerMem := mem } =
                            .step { frames := [{ fTgt with stmtIdx := pos + 6, locals := lsT6 }], callerMem := mem } := by
                          unfold evalStepTupleAssert; dsimp
                          rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts5]
                          dsimp [evalStatementExt]
                          rw [hBdyF1]
                          dsimp [evalRvalueExt, evalPrimitiveOperandExt, evalOperandToSlotExt]
                          rw [hOvfTy0, setElem?_getElem?_ne hSetT5 (fun h => hBaseNeOvf0 h.symm), hOvf0In4]
                          dsimp [isFlatTupleTy, isPrimitiveReadableTy_int, isPrimitiveReadableTy_bool]
                          rw [hOvfTy1, setElem?_getElem?_ne hSetT5 (fun h => hBaseNeOvf1 h.symm), hOvf1In4]
                          dsimp [isFlatTupleTy, isPrimitiveReadableTy_int, isPrimitiveReadableTy_bool, isWithOverflowBinOp]
                          rw [hLtEval]; dsimp
                          unfold writePlaceExt checkValExt; dsimp [checkVal, Val.ty?, MirTy.beq]
                          rw [setElem?_getElem?_ne hSetT5 (nat_succ_ne_self _), hF1In4, hSetT6]
                        have hOvf0Lt6 : ovf0 < lsT6.length := by
                          rw [setElem?_length hSetT6, setElem?_length hSetT5, hRel4.2.1, hOvfTysEq]
                          dsimp [List.length]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
                        let ⟨lsT7, hSetT7⟩ := setElem?_some_of_lt lsT6 ovf0 .dead hOvf0Lt6
                        have hOvf1Lt7 : ovf0 + 1 < lsT7.length := by
                          rw [setElem?_length hSetT7, setElem?_length hSetT6, setElem?_length hSetT5,
                              hRel4.2.1, hOvfTysEq]
                          dsimp [List.length]; exact Nat.lt_succ_self _
                        let ⟨lsT8, hSetT8⟩ := setElem?_some_of_lt lsT7 (ovf0 + 1) .dead hOvf1Lt7
                        have hStep6 : evalStepTupleAssert ctx.pTgt 0
                            { frames := [{ fTgt with stmtIdx := pos + 6, locals := lsT6 }], callerMem := mem } =
                            .step { frames := [{ fTgt with stmtIdx := pos + 7, locals := lsT7 }], callerMem := mem } := by
                          unfold evalStepTupleAssert; dsimp
                          rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts6]
                          dsimp [evalStatementExt]; rw [hOvf0Ne0]; dsimp; rw [hSetT7]
                        have hStep7 : evalStepTupleAssert ctx.pTgt 0
                            { frames := [{ fTgt with stmtIdx := pos + 7, locals := lsT7 }], callerMem := mem } =
                            .step { frames := [{ fTgt with stmtIdx := pos + 8, locals := lsT8 }], callerMem := mem } := by
                          unfold evalStepTupleAssert; dsimp
                          rw [sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbT]; dsimp; rw [hStmts7]
                          dsimp [evalStatementExt]; rw [hSetT8]
                        have hTupLtS2 : ctx.plan.tupLocal < lsSrc2.length := by
                          rw [hRel4.1]; exact ctx.hTupLt
                        let ⟨lsSrc3, hSetSrc3⟩ := setElem?_some_of_lt lsSrc2 ctx.plan.tupLocal
                          (.liveTuple [some (.scalar resSv), some (.bool ovfB)]) hTupLtS2
                        dsimp [List.map]; rw [hSetSrc3]; dsimp
                        have hRelFinal : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
                            ctx.fieldTys ctx.ovfTys lsSrc3 lsT8 := by
                          have hLen8 : lsT8.length =
                              ctx.bodySrc.locals.length + ctx.fieldTys.length + ctx.ovfTys.length := by
                            rw [setElem?_length hSetT8, setElem?_length hSetT7,
                                setElem?_length hSetT6, setElem?_length hSetT5, hRel4.2.1]
                          refine ⟨by rw [setElem?_length hSetSrc3, hRel4.1], hLen8, ?_, ?_⟩
                          · intro i hi hINe
                            have hNe0 : i ≠ ctx.bodySrc.locals.length := fun h => by
                              have hi' := hi; rw [h] at hi'; exact Nat.not_lt_of_ge (Nat.le_refl _) hi'
                            have hNe1 : i ≠ ctx.bodySrc.locals.length + 1 := fun h => by
                              have hi' := hi; rw [h] at hi'; exact Nat.not_lt_of_ge (Nat.le_succ _) hi'
                            have hNeO0 : i ≠ ovf0 := fun h => by
                              have hi' := hi; rw [h] at hi'; exact Nat.not_lt_of_ge (Nat.le_add_right _ _) hi'
                            have hNeO1 : i ≠ ovf0 + 1 := fun h => by
                              have hi' := hi; rw [h] at hi'
                              exact Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)) hi'
                            rw [setElem?_getElem?_ne hSetT8 hNeO1, setElem?_getElem?_ne hSetT7 hNeO0,
                                setElem?_getElem?_ne hSetT6 hNe1, setElem?_getElem?_ne hSetT5 hNe0,
                                setElem?_getElem?_ne hSetSrc3 hINe]
                            exact hRel4.2.2.1 i hi hINe
                          · rw [setElem?_getElem?_same hSetSrc3]
                            refine ⟨by rw [hFieldLen]; rfl, ?_⟩
                            intro j hJLt
                            rw [hFieldLen] at hJLt
                            cases j with
                            | zero =>
                              rw [Nat.add_zero]
                              rw [setElem?_getElem?_ne hSetT8 hBaseNeOvf1,
                                  setElem?_getElem?_ne hSetT7 hBaseNeOvf0,
                                  setElem?_getElem?_ne hSetT6 (nat_ne_succ_self _),
                                  setElem?_getElem?_same hSetT5]; rfl
                            | succ k =>
                              cases k with
                              | zero =>
                                have hB1NeO0 : ctx.bodySrc.locals.length + 1 ≠ ovf0 := fun h => by
                                  have hlt : ctx.bodySrc.locals.length + 1 < ovf0 := by
                                    change ctx.bodySrc.locals.length + 1 < ctx.bodySrc.locals.length + ctx.fieldTys.length
                                    rw [hFieldLen]; exact Nat.lt_succ_self _
                                  rw [h] at hlt; exact Nat.not_lt_of_ge (Nat.le_refl _) hlt
                                have hB1NeO1 : ctx.bodySrc.locals.length + 1 ≠ ovf0 + 1 := fun h => by
                                  have hlt : ctx.bodySrc.locals.length + 1 < ovf0 + 1 := by
                                    change ctx.bodySrc.locals.length + 1 < ctx.bodySrc.locals.length + ctx.fieldTys.length + 1
                                    rw [hFieldLen]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
                                  rw [h] at hlt; exact Nat.not_lt_of_ge (Nat.le_refl _) hlt
                                rw [setElem?_getElem?_ne hSetT8 hB1NeO1,
                                    setElem?_getElem?_ne hSetT7 hB1NeO0,
                                    setElem?_getElem?_same hSetT6]; rfl
                              | succ m =>
                                exact False.elim (Nat.not_lt_zero m
                                  (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hJLt)))
                        refine ⟨lsT8, ?_, _, rfl, rfl, rfl, rfl, hRelFinal⟩
                        rw [show (8 : Nat) = 4 + 4 from rfl, evalTupleAssertFuel_add, hStep0123]
                        dsimp [evalTupleAssertFuel]
                        rw [hStep4Base]; dsimp [evalTupleAssertFuel]; rw [hStep5]; dsimp [evalTupleAssertFuel]; rw [hStep6]; dsimp [evalTupleAssertFuel]; rw [hStep7]

/-! #### Master `SROA` Step Simulation, Init Simulation, & Theorem 2 -/

private theorem sroa_operandMentionsLocal_rewrite_ne {tupLocal base dstId : Nat}
    {fieldTys : List MirTy}
    (hDstLt : dstId < base) (hDstNe : dstId ≠ tupLocal)
    (opnd : Operand)
    (hOpVal : operandTupleValid tupLocal fieldTys opnd = true) :
    operandMentionsLocal dstId (rewriteTupleOperand tupLocal base opnd) =
      operandMentionsLocal dstId opnd := by
  cases opnd with
  | constant _ => rfl
  | copy p | move p =>
    dsimp [rewriteTupleOperand, rewriteTuplePlace, operandMentionsLocal]
    cases hEq : Nat.beq p.localId tupLocal with
    | false => rfl
    | true =>
      have hLid := nat_beq_eq hEq; subst hLid
      dsimp [operandTupleValid] at hOpVal
      rw [hEq] at hOpVal; dsimp [isValidTupleFieldPlace] at hOpVal
      rw [nat_beq_refl, Bool.true_and] at hOpVal
      cases hProj : p.projection with
      | nil => rw [hProj] at hOpVal; cases hOpVal
      | cons pe rest =>
        rw [hProj] at hOpVal
        cases rest with
        | cons _ _ => cases pe <;> cases hOpVal
        | nil =>
          cases pe with
          | deref | unsupported => cases hOpVal
          | field idx _ =>
            dsimp
            rw [nat_beq_false_of_ne (nat_ne_add_left_of_lt hDstLt),
                nat_beq_false_of_ne (fun h => hDstNe h.symm)]

private theorem sroa_isWholeLocalSelfUse_rewrite_ne {tupLocal base dstId : Nat}
    {fieldTys : List MirTy}
    (hDstLt : dstId < base) (hDstNe : dstId ≠ tupLocal)
    (rv : Rvalue)
    (hRvVal : rvalueTupleValid tupLocal fieldTys rv = true) :
    isWholeLocalSelfUse dstId (rewriteTupleRvalue tupLocal base rv) =
      isWholeLocalSelfUse dstId rv := by
  cases rv with
  | use opnd =>
    cases opnd with
    | constant _ => rfl
    | copy p | move p =>
      dsimp [rewriteTupleRvalue, rewriteTupleOperand, rewriteTuplePlace, isWholeLocalSelfUse]
      cases hEq : Nat.beq p.localId tupLocal with
      | false => rfl
      | true =>
        have hLid := nat_beq_eq hEq; subst hLid
        dsimp [rvalueTupleValid, operandTupleValid] at hRvVal
        rw [hEq] at hRvVal; dsimp [isValidTupleFieldPlace] at hRvVal
        rw [nat_beq_refl, Bool.true_and] at hRvVal
        cases hProj : p.projection with
        | nil => rw [hProj] at hRvVal; cases hRvVal
        | cons pe rest =>
          rw [hProj] at hRvVal
          cases rest with
          | cons _ _ => cases pe <;> cases hRvVal
          | nil =>
            cases pe with
            | deref | unsupported => cases hRvVal
            | field idx _ =>
              dsimp
              rw [nat_beq_false_of_ne (nat_ne_add_left_of_lt hDstLt)]; rfl
  | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
  | addressOf _ _ | aggregateTuple _ | unsupported => rfl

private theorem sroa_aggregate_ne_sim (ctx : SroaCtx) {dstId : LocalId}
    (hDstLt : dstId < ctx.bodySrc.locals.length)
    (hDstNe : dstId ≠ ctx.plan.tupLocal)
    (ops : List Operand) :
    ∀ (idx : Nat) (remTys : List MirTy) (lsSrc lsTgt : List LocalSlotExt),
      ops.all (operandLocalsLt ctx.bodySrc.locals.length) = true →
      ops.all (operandTupleValid ctx.plan.tupLocal ctx.fieldTys) = true →
      SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
        ctx.fieldTys ctx.ovfTys lsSrc lsTgt →
      match evalAggregateInPlaceExt ctx.bodySrc.locals lsSrc dstId idx ops remTys with
      | .error k =>
        evalAggregateInPlaceExt ctx.bodyTgt.locals lsTgt dstId idx
          (ops.map (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length)) remTys =
          .error k
      | .ok lsSrc' =>
        ∃ lsTgt',
          evalAggregateInPlaceExt ctx.bodyTgt.locals lsTgt dstId idx
            (ops.map (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length)) remTys =
            .ok lsTgt' ∧
          SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
            ctx.fieldTys ctx.ovfTys lsSrc' lsTgt' := by
  induction ops with
  | nil =>
    intro idx remTys lsSrc lsTgt _ _ hRel
    cases remTys with
    | nil => exact ⟨lsTgt, rfl, hRel⟩
    | cons _ _ => rfl
  | cons opnd restOps ih =>
    intro idx remTys lsSrc lsTgt hAllLt hAllVal hRel
    cases remTys with
    | nil => rfl
    | cons ft restTys =>
      let ⟨hOpLt, hRestLt⟩ := bool_and_true hAllLt
      let ⟨hOpVal, hRestVal⟩ := bool_and_true hAllVal
      dsimp [List.map, evalAggregateInPlaceExt]
      have hOpSim := sroa_evalOperandToSlotExt_sim ctx hRel hOpLt hOpVal
      cases hEv : evalOperandToSlotExt ctx.bodySrc.locals lsSrc opnd with
      | error k => rw [hEv] at hOpSim; rw [hOpSim]
      | ok triple =>
        rw [hEv] at hOpSim
        cases triple with
        | mk srcTy r1 =>
          cases r1 with
          | mk ov ls1 =>
            let ⟨lsT1, hEvT, hRel1, _⟩ := hOpSim
            rw [hEvT]; dsimp
            cases (!MirTy.beq srcTy ft) with
            | true => rfl
            | false =>
              dsimp
              cases ov with
              | none => rfl
              | some v =>
                dsimp
                have hWSim := sroa_writeTupleFieldExt_ne_sim ctx (idx := idx) (fieldTy := ft) (val := v)
                  hRel1 hDstLt hDstNe
                cases hW : writeTupleFieldExt ls1 dstId idx ft v with
                | error k => rw [hW] at hWSim; rw [hWSim]
                | ok ls2 =>
                  rw [hW] at hWSim
                  let ⟨lsT2, hWT, hRel2⟩ := hWSim
                  rw [hWT]; dsimp
                  exact ih (idx + 1) restTys ls2 lsT2 hRestLt hRestVal hRel2

private noncomputable def ctxLowerStmt (ctx : SroaCtx) (stmt : StatementKind) : List StatementKind :=
  lowerSroaStmt ctx.plan.tupLocal ctx.fieldTys.length
    ctx.bodySrc.locals.length (ctx.bodySrc.locals.length + ctx.fieldTys.length) stmt

private theorem sroa_term_sim (ctx : SroaCtx) {fSrc fTgt : FrameStateExt}
    {memS : CallerMemory} {bbSrc : BasicBlock}
    (hDefS : fSrc.defId = ctx.plan.defId)
    (hDefT : fTgt.defId = ctx.plan.defId)
    (hAllSup : ctx.bodySrc.locals.all isSupportedTupleOrScalarTy = true)
    (hLocWt : LocalsWellTyped ctx.bodySrc.locals fSrc.locals)
    (hLocRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys fSrc.locals fTgt.locals)
    (hTermIb : terminatorLocalsLt ctx.bodySrc.locals.length bbSrc.terminator = true)
    (hTermVal : terminatorTupleValid ctx.plan.tupLocal ctx.fieldTys bbSrc.terminator = true)
    (hTgtStep : evalStepTupleAssert ctx.pTgt 0 { frames := [fTgt], callerMem := memS } =
      evalTerminatorExt ctx.bodyTgt
        { statements := listFlatMap (ctxLowerStmt ctx) bbSrc.statements,
          terminator := rewriteTupleTerminator ctx.plan.tupLocal ctx.bodySrc.locals.length bbSrc.terminator,
          cleanup := bbSrc.cleanup }
        fTgt memS) :
    match evalTerminatorExt ctx.bodySrc bbSrc fSrc memS with
    | .step sSrc' =>
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel ctx.pTgt k { frames := [fTgt], callerMem := memS } = .step sTgt' ∧
        SroaRelState ctx sSrc' sTgt'
    | .done out =>
      ∃ k, 0 < k ∧ evalTupleAssertFuel ctx.pTgt k { frames := [fTgt], callerMem := memS } = .done out
    | .fault fk =>
      ∃ k, 0 < k ∧ evalTupleAssertFuel ctx.pTgt k { frames := [fTgt], callerMem := memS } = .fault fk := by
  have hMkJump : ∀ (tgt : BasicBlockId) (lsS' lsT' : List LocalSlotExt),
      LocalsWellTyped ctx.bodySrc.locals lsS' →
      SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length ctx.fieldTys ctx.ovfTys lsS' lsT' →
      SroaRelState ctx
        { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := lsS' }], callerMem := memS }
        { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := lsT' }], callerMem := memS } := by
    intro tgt lsS' lsT' hWt' hRel'
    refine ⟨rfl, _, _, rfl, rfl, hDefS, hDefT, rfl, hAllSup, hWt', hRel', ?_⟩
    intro _ _
    exact ⟨Nat.zero_le _, rfl⟩
  unfold evalTerminatorExt at hTgtStep; unfold evalTerminatorExt
  dsimp at hTgtStep
  cases hTerm : bbSrc.terminator with
  | goto target =>
    rw [hTerm] at hTgtStep
    dsimp [rewriteTupleTerminator, jumpToBlockExt] at hTgtStep; dsimp [rewriteTupleTerminator, jumpToBlockExt]
    refine ⟨1, _, Nat.zero_lt_succ 0, ?_, hMkJump target fSrc.locals fTgt.locals hLocWt hLocRel⟩
    dsimp [evalTupleAssertFuel]; rw [hTgtStep]
  | unreachable =>
    rw [hTerm] at hTgtStep; dsimp [rewriteTupleTerminator] at hTgtStep; dsimp [rewriteTupleTerminator]
    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
  | unwindResume =>
    rw [hTerm] at hTgtStep; dsimp [rewriteTupleTerminator] at hTgtStep; dsimp [rewriteTupleTerminator]
    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
  | call _ _ _ _ _ =>
    rw [hTerm] at hTgtStep; dsimp [rewriteTupleTerminator] at hTgtStep; dsimp [rewriteTupleTerminator]
    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
  | unsupported =>
    rw [hTerm] at hTgtStep; dsimp [rewriteTupleTerminator] at hTgtStep; dsimp [rewriteTupleTerminator]
    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
  | return_ =>
    rw [hTerm] at hTgtStep
    dsimp [rewriteTupleTerminator] at hTgtStep; dsimp [rewriteTupleTerminator]
    have h0Lt : 0 < ctx.bodySrc.locals.length := sroaCtx_base_pos ctx
    have h0Ne : 0 ≠ ctx.plan.tupLocal := fun h => sroaCtx_tupLocal_ne_zero ctx h.symm
    rw [hLocRel.2.2.1 0 h0Lt h0Ne, sroaCtx_localsTgt_getElem?_lt ctx h0Lt h0Ne] at hTgtStep
    cases hCl : bbSrc.cleanup with
    | true =>
      rw [hCl] at hTgtStep; dsimp at hTgtStep; dsimp
      exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
    | false =>
      rw [hCl] at hTgtStep; dsimp at hTgtStep; dsimp
      cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
      | none =>
        rw [h0] at hTgtStep; dsimp at hTgtStep; dsimp
        exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
      | some sl =>
        rw [h0] at hTgtStep
        cases sl with
        | dead =>
          dsimp at hTgtStep; dsimp
          exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
        | liveBase ov =>
          cases ov <;> (
            dsimp at hTgtStep; dsimp
            exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩)
        | liveTuple fields =>
          dsimp at hTgtStep; dsimp
          cases hB0 : Trusted.MirSemantics.getElem? ctx.bodySrc.locals 0 with
          | none =>
            rw [hB0] at hTgtStep; dsimp at hTgtStep; dsimp
            exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
          | some t0 =>
            rw [hB0] at hTgtStep
            cases t0 with
            | tuple fTys =>
              dsimp at hTgtStep; dsimp
              cases hC : (isFlatTupleTy (.tuple fTys) && Nat.beq fields.length fTys.length) with
              | false =>
                rw [hC] at hTgtStep; dsimp at hTgtStep; dsimp
                exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
              | true =>
                rw [hC] at hTgtStep; dsimp at hTgtStep; dsimp
                cases hExt : extractAllInitFields fields <;> (
                  rw [hExt] at hTgtStep; dsimp at hTgtStep; dsimp
                  exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩)
            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
              dsimp at hTgtStep; dsimp
              exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
  | switchInt discr targets =>
    rw [hTerm] at hTermIb hTermVal hTgtStep
    dsimp [terminatorLocalsLt] at hTermIb
    dsimp [terminatorTupleValid] at hTermVal
    dsimp [rewriteTupleTerminator] at hTgtStep; dsimp [rewriteTupleTerminator]
    have hOpSim := sroa_evalPrimitiveOperandExt_sim ctx hLocRel hTermIb hTermVal
    cases hEv : evalPrimitiveOperandExt ctx.bodySrc.locals fSrc.locals discr with
    | error k =>
      rw [hEv] at hOpSim; rw [hOpSim] at hTgtStep; dsimp at hTgtStep; dsimp
      exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
    | ok p1 =>
      rw [hEv] at hOpSim
      cases p1 with
      | mk dv lsS1 =>
        let ⟨lsT1, hEvT, hRel1, _⟩ := hOpSim
        have hWt1 := (evalPrimitiveOperandExt_preserves_wt hAllSup hLocWt hEv).1
        rw [hEvT] at hTgtStep; dsimp at hTgtStep; dsimp
        cases dv with
        | scalar sv =>
          dsimp at hTgtStep; dsimp
          cases hBr : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
          | error k =>
            rw [hBr] at hTgtStep; dsimp at hTgtStep; dsimp
            exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
          | ok target =>
            rw [hBr] at hTgtStep; dsimp [jumpToBlockExt] at hTgtStep; dsimp [jumpToBlockExt]
            refine ⟨1, _, Nat.zero_lt_succ 0, ?_, hMkJump target lsS1 lsT1 hWt1 hRel1⟩
            dsimp [evalTupleAssertFuel]; rw [hTgtStep]
        | bool b =>
          dsimp at hTgtStep; dsimp
          cases hBr : evalBoolSwitchBranches b targets.otherwise targets.branches with
          | error k =>
            rw [hBr] at hTgtStep; dsimp at hTgtStep; dsimp
            exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
          | ok target =>
            rw [hBr] at hTgtStep; dsimp [jumpToBlockExt] at hTgtStep; dsimp [jumpToBlockExt]
            refine ⟨1, _, Nat.zero_lt_succ 0, ?_, hMkJump target lsS1 lsT1 hWt1 hRel1⟩
            dsimp [evalTupleAssertFuel]; rw [hTgtStep]
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ =>
          dsimp at hTgtStep; dsimp
          exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
  | assert cond expected msg target unwind =>
    rw [hTerm] at hTermIb hTermVal hTgtStep
    dsimp [terminatorLocalsLt] at hTermIb
    dsimp [terminatorTupleValid] at hTermVal
    dsimp [rewriteTupleTerminator] at hTgtStep; dsimp [rewriteTupleTerminator]
    have hOpSim := sroa_evalPrimitiveOperandExt_sim ctx hLocRel hTermIb hTermVal
    cases hEv : evalPrimitiveOperandExt ctx.bodySrc.locals fSrc.locals cond with
    | error k =>
      rw [hEv] at hOpSim; rw [hOpSim] at hTgtStep; dsimp at hTgtStep; dsimp
      exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
    | ok p1 =>
      rw [hEv] at hOpSim
      cases p1 with
      | mk cv lsS1 =>
        let ⟨lsT1, hEvT, hRel1, _⟩ := hOpSim
        have hWt1 := (evalPrimitiveOperandExt_preserves_wt hAllSup hLocWt hEv).1
        rw [hEvT] at hTgtStep; dsimp at hTgtStep; dsimp
        cases cv with
        | bool b =>
          dsimp at hTgtStep; dsimp
          cases hBeq : (b == expected) with
          | true =>
            rw [hBeq] at hTgtStep; dsimp [jumpToBlockExt] at hTgtStep; dsimp [jumpToBlockExt]
            refine ⟨1, _, Nat.zero_lt_succ 0, ?_, hMkJump target lsS1 lsT1 hWt1 hRel1⟩
            dsimp [evalTupleAssertFuel]; rw [hTgtStep]
          | false =>
            rw [hBeq] at hTgtStep; dsimp at hTgtStep; dsimp
            cases hK : (!isSupportedAssertKind msg) with
            | true =>
              rw [hK] at hTgtStep; dsimp at hTgtStep; dsimp
              exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩
            | false =>
              rw [hK] at hTgtStep; dsimp at hTgtStep; dsimp
              cases unwind <;> (
                dsimp at hTgtStep; dsimp
                exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩)
        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ =>
          dsimp at hTgtStep; dsimp
          exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgtStep]⟩

private theorem sroa_evalStatement_assign_whole_ne (ctx : SroaCtx)
    {fSrc fTgt : FrameStateExt} {memS : CallerMemory}
    (dstId : LocalId) (rv : Rvalue)
    (hDstLt : dstId < ctx.bodySrc.locals.length)
    (hDstNe : dstId ≠ ctx.plan.tupLocal)
    (hLocRel : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
      ctx.fieldTys ctx.ovfTys fSrc.locals fTgt.locals)
    (hRvLt : rvalueLocalsLt ctx.bodySrc.locals.length rv = true)
    (hRvVal : rvalueTupleValid ctx.plan.tupLocal ctx.fieldTys rv = true) :
    match evalStatementExt ctx.bodySrc fSrc memS (.assign ⟨dstId, []⟩ rv) with
    | .done _ => False
    | .fault k =>
      evalStatementExt ctx.bodyTgt fTgt memS
        (.assign ⟨dstId, []⟩ (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv)) = .fault k
    | .step sSrc' =>
      ∃ lsS' lsT',
        sSrc' = { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := lsS' }], callerMem := memS } ∧
        evalStatementExt ctx.bodyTgt fTgt memS
          (.assign ⟨dstId, []⟩ (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv)) =
          .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := lsT' }], callerMem := memS } ∧
        SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length ctx.fieldTys ctx.ovfTys lsS' lsT' := by
  have hEvalWrite : ∀ (ty : MirTy) (rv' : Rvalue),
      rvalueLocalsLt ctx.bodySrc.locals.length rv' = true →
      rvalueTupleValid ctx.plan.tupLocal ctx.fieldTys rv' = true →
      match (match evalRvalueExt ctx.bodySrc.locals fSrc.locals ty rv' with
             | .error k => (StepResult.fault k : StepResult StateExt TerminalOutExt)
             | .ok (val, ls1) =>
               match writePlaceExt ls1 dstId ty val with
               | .error k => .fault k
               | .ok ls2 =>
                 .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := ls2 }],
                         callerMem := memS }) with
      | .done _ => False
      | .fault k =>
        (match evalRvalueExt ctx.bodyTgt.locals fTgt.locals ty
            (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv') with
         | .error k => (StepResult.fault k : StepResult StateExt TerminalOutExt)
         | .ok (val, ls1) =>
           match writePlaceExt ls1 dstId ty val with
           | .error k => .fault k
           | .ok ls2 =>
             .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := ls2 }],
                     callerMem := memS }) = .fault k
      | .step sSrc' =>
        ∃ lsS' lsT',
          sSrc' = { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := lsS' }], callerMem := memS } ∧
          (match evalRvalueExt ctx.bodyTgt.locals fTgt.locals ty
              (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv') with
           | .error k => (StepResult.fault k : StepResult StateExt TerminalOutExt)
           | .ok (val, ls1) =>
             match writePlaceExt ls1 dstId ty val with
             | .error k => .fault k
             | .ok ls2 =>
               .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := ls2 }],
                       callerMem := memS }) =
            .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := lsT' }], callerMem := memS } ∧
          SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length ctx.fieldTys ctx.ovfTys lsS' lsT' := by
    intro ty rv' hLt' hVal'
    have hRvSim := sroa_evalRvalueExt_sim ctx (dstTy := ty) hLocRel hLt' hVal'
    cases hR : evalRvalueExt ctx.bodySrc.locals fSrc.locals ty rv' with
    | error k => rw [hR] at hRvSim; rw [hRvSim]
    | ok pr =>
      rw [hR] at hRvSim
      cases pr with
      | mk val ls1 =>
        dsimp
        let ⟨lsT1, hRT, hRel1⟩ := hRvSim
        rw [hRT]; dsimp
        have hWSim := sroa_writePlaceExt_ne_sim ctx (dstTy := ty) (val := val) hRel1 hDstLt hDstNe
        cases hW : writePlaceExt ls1 dstId ty val with
        | error k => rw [hW] at hWSim; rw [hWSim]
        | ok ls2 =>
          rw [hW] at hWSim
          let ⟨lsT2, hWT, hRel2⟩ := hWSim
          rw [hWT]; dsimp
          exact ⟨ls2, lsT2, rfl, rfl, hRel2⟩
  dsimp [evalStatementExt]
  rw [sroaCtx_localsTgt_getElem?_lt ctx hDstLt hDstNe]
  cases hTy : Trusted.MirSemantics.getElem? ctx.bodySrc.locals dstId with
  | none => rfl
  | some dstTy =>
    dsimp
    cases hRvCase : rv with
    | aggregateTuple ops =>
      rw [hRvCase] at hRvLt hRvVal
      dsimp [rewriteTupleRvalue]
      cases dstTy with
      | tuple fTys =>
        dsimp
        have hAnyEq : (ops.map (rewriteTupleOperand ctx.plan.tupLocal
            ctx.bodySrc.locals.length)).any (operandMentionsLocal dstId) =
            ops.any (operandMentionsLocal dstId) := by
          rw [list_any_map]
          apply list_any_congr_getElem?
          intro j o1 h1
          exact sroa_operandMentionsLocal_rewrite_ne hDstLt hDstNe o1
            (list_all_getElem? hRvVal h1)
        rw [map_length_eq, hAnyEq]
        cases (!isFlatTupleTy (.tuple fTys) || !Nat.beq ops.length fTys.length ||
            ops.any (operandMentionsLocal dstId)) with
        | true => rfl
        | false =>
          dsimp
          have hAggSim := sroa_aggregate_ne_sim ctx hDstLt hDstNe ops 0 fTys
            fSrc.locals fTgt.locals hRvLt hRvVal hLocRel
          cases hAgg : evalAggregateInPlaceExt ctx.bodySrc.locals fSrc.locals dstId 0 ops fTys with
          | error k => rw [hAgg] at hAggSim; rw [hAggSim]
          | ok lsS' =>
            rw [hAgg] at hAggSim
            let ⟨lsT', hAggT, hRel'⟩ := hAggSim
            rw [hAggT]; dsimp
            exact ⟨lsS', lsT', rfl, rfl, hRel'⟩
      | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => rfl
    | use o =>
      rw [hRvCase] at hRvLt hRvVal
      have hSelf := sroa_isWholeLocalSelfUse_rewrite_ne hDstLt hDstNe (.use o) hRvVal
      cases dstTy with
      | tuple fTys =>
        dsimp
        rw [hSelf]
        cases isWholeLocalSelfUse dstId (.use o) with
        | true => rfl
        | false =>
          dsimp
          exact hEvalWrite (.tuple fTys) (.use o) hRvLt hRvVal
      | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
        dsimp
        exact hEvalWrite _ (.use o) hRvLt hRvVal
    | binaryOp op l r =>
      rw [hRvCase] at hRvLt hRvVal
      cases dstTy <;> (
        dsimp [isWholeLocalSelfUse]
        exact hEvalWrite _ (.binaryOp op l r) hRvLt hRvVal)
    | unaryOp op o =>
      rw [hRvCase] at hRvLt hRvVal
      cases dstTy <;> (
        dsimp [isWholeLocalSelfUse]
        exact hEvalWrite _ (.unaryOp op o) hRvLt hRvVal)
    | discriminant pl =>
      rw [hRvCase] at hRvLt hRvVal
      cases dstTy <;> (
        dsimp [isWholeLocalSelfUse]
        exact hEvalWrite _ (.discriminant pl) hRvLt hRvVal)
    | ref _ _ | addressOf _ _ | unsupported =>
      cases dstTy <;> rfl

private theorem sroa_step_sim_all (ctx : SroaCtx) {sSrc sTgt : StateExt}
    (hRelS : SroaRelState ctx sSrc sTgt) :
    match evalStepTupleAssert ctx.pSrc 0 sSrc with
    | .step sSrc' =>
      ∃ k sTgt', 0 < k ∧ evalTupleAssertFuel ctx.pTgt k sTgt = .step sTgt' ∧
        SroaRelState ctx sSrc' sTgt'
    | .done out =>
      ∃ k, 0 < k ∧ evalTupleAssertFuel ctx.pTgt k sTgt = .done out
    | .fault fk =>
      ∃ k, 0 < k ∧ evalTupleAssertFuel ctx.pTgt k sTgt = .fault fk := by
  let ⟨hMemEq, fSrc, fTgt, hFS, hFT, hDefS, hDefT, hBlkEq, hAllSup, hLocWt, hLocRel, hOff⟩ := hRelS
  cases sSrc with
  | mk framesS memS =>
    cases sTgt with
    | mk framesT memT =>
      dsimp at hMemEq hFS hFT
      subst hMemEq; subst hFS; subst hFT
      have hStateWtSrc : StateWellTyped ctx.pSrc { frames := [fSrc], callerMem := memS } :=
        ⟨fSrc, ctx.bodySrc, rfl, by rw [hDefS]; exact ctx.hGetSrc, hAllSup, hLocWt⟩
      unfold evalStepTupleAssert
      dsimp
      rw [hDefS, ctx.hGetSrc]; dsimp
      cases hBbS : Trusted.MirSemantics.getElem? ctx.bodySrc.basicBlocks fSrc.blockIdx with
      | none =>
        dsimp
        have hBbTNone : Trusted.MirSemantics.getElem? ctx.bodyTgt.basicBlocks fTgt.blockIdx = none := by
          rw [← hBlkEq, ctx.hBodyTgt]; dsimp
          rw [getElem?_map, hBbS]; rfl
        refine ⟨1, Nat.zero_lt_succ 0, ?_⟩
        dsimp [evalTupleAssertFuel, evalStepTupleAssert]
        rw [hDefT, sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbTNone]
      | some bbSrc =>
        dsimp
        have hBbT := sroaCtx_getElem?_bbTgt ctx hBbS
        have hBbTAt : Trusted.MirSemantics.getElem? ctx.bodyTgt.basicBlocks fTgt.blockIdx =
            some { statements := listFlatMap (ctxLowerStmt ctx) bbSrc.statements,
                   terminator := rewriteTupleTerminator ctx.plan.tupLocal ctx.bodySrc.locals.length bbSrc.terminator,
                   cleanup := bbSrc.cleanup } := by
          rw [← hBlkEq]; exact hBbT
        let ⟨hStmtLe, hStmtOff⟩ := hOff bbSrc hBbS
        have hBbIb := list_all_getElem? ctx.hInBounds hBbS
        let ⟨hStmtsIb, hTermIb⟩ := bool_and_true hBbIb
        have hBbVal := list_all_getElem? ctx.hUsesValid hBbS
        let ⟨hStmtsVal, hTermVal⟩ := bool_and_true hBbVal
        cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
        | none =>
          dsimp
          have hGe := getElem?_none_ge hStS
          have hEqLen : fSrc.stmtIdx = bbSrc.statements.length := Nat.le_antisymm hStmtLe hGe
          have hBeqS : Nat.beq fSrc.stmtIdx bbSrc.statements.length = true := nat_beq_of_eq hEqLen
          rw [hBeqS]; dsimp
          have hTgtIdxEq : fTgt.stmtIdx = (listFlatMap (ctxLowerStmt ctx) bbSrc.statements).length := by
            rw [hStmtOff, hEqLen]
            unfold sroaStmtOffset ctxLowerStmt
            rw [list_take_all_eq]
          have hStTNone : Trusted.MirSemantics.getElem?
              (listFlatMap (ctxLowerStmt ctx) bbSrc.statements) fTgt.stmtIdx = none :=
            getElem?_none_of_ge (by rw [hTgtIdxEq]; exact Nat.le_refl _)
          have hBeqT : Nat.beq fTgt.stmtIdx (listFlatMap (ctxLowerStmt ctx) bbSrc.statements).length = true :=
            nat_beq_of_eq hTgtIdxEq
          have hTgtStep : evalStepTupleAssert ctx.pTgt 0 { frames := [fTgt], callerMem := memS } =
              evalTerminatorExt ctx.bodyTgt
                { statements := listFlatMap (ctxLowerStmt ctx) bbSrc.statements,
                  terminator := rewriteTupleTerminator ctx.plan.tupLocal ctx.bodySrc.locals.length bbSrc.terminator,
                  cleanup := bbSrc.cleanup }
                fTgt memS := by
            unfold evalStepTupleAssert; dsimp
            rw [hDefT, sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbTAt]; dsimp; rw [hStTNone]; dsimp; rw [hBeqT]; dsimp
          exact sroa_term_sim ctx hDefS hDefT hAllSup hLocWt hLocRel hTermIb hTermVal hTgtStep
        | some stmt =>
          have hSIb := list_all_getElem? hStmtsIb hStS
          have hSVal := list_all_getElem? hStmtsVal hStS
          have hStmtIdxLt : fSrc.stmtIdx < bbSrc.statements.length := getElem?_some_lt hStS
          have hStmtSuccLe : fSrc.stmtIdx + 1 ≤ bbSrc.statements.length := Nat.succ_le_of_lt hStmtIdxLt
          have hOffSucc : sroaStmtOffset ctx bbSrc (fSrc.stmtIdx + 1) =
              sroaStmtOffset ctx bbSrc fSrc.stmtIdx + (ctxLowerStmt ctx stmt).length :=
            sroaStmtOffset_succ ctx hStS
          have hAtLowered : ∀ j st,
              Trusted.MirSemantics.getElem? (ctxLowerStmt ctx stmt) j = some st →
              Trusted.MirSemantics.getElem?
                (listFlatMap (ctxLowerStmt ctx) bbSrc.statements) (fTgt.stmtIdx + j) = some st := by
            intro j st hj
            rw [hStmtOff]
            have hJLt := getElem?_some_lt hj
            have hAt := sroa_bbTgt_stmt_at ctx hStS j hJLt
            unfold ctxLowerStmt at hj; unfold ctxLowerStmt
            rw [hAt, hj]
          have hMkNextStateN : ∀ (nSteps : Nat) (lsS' lsT' : List LocalSlotExt),
              (ctxLowerStmt ctx stmt).length = nSteps →
              evalStatementExt ctx.bodySrc fSrc memS stmt =
                .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := lsS' }], callerMem := memS } →
              SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length ctx.fieldTys ctx.ovfTys lsS' lsT' →
              SroaRelState ctx
                { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := lsS' }], callerMem := memS }
                { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + nSteps, locals := lsT' }], callerMem := memS } := by
            intro nSteps lsS' lsT' hLenN hEvStep hRel'
            have hSrcStep : evalStepTupleAssert ctx.pSrc 0 { frames := [fSrc], callerMem := memS } =
                .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := lsS' }], callerMem := memS } := by
              unfold evalStepTupleAssert; dsimp
              rw [hDefS, ctx.hGetSrc]; dsimp; rw [hBbS]; dsimp; rw [hStS]; dsimp
              rw [hDefS] at hEvStep
              exact hEvStep
            have hWtNext := evalStepTupleAssert_preserves_stateWellTyped hStateWtSrc hSrcStep
            let ⟨fN, bN, hFN, hBN, _, hLocWt'⟩ := hWtNext
            injection hFN with hFNEq; subst hFNEq
            dsimp at hBN
            rw [hDefS, ctx.hGetSrc] at hBN
            injection hBN with hBNEq; subst hBNEq
            refine ⟨rfl, _, _, rfl, rfl, hDefS, hDefT, hBlkEq, hAllSup, hLocWt', hRel', ?_⟩
            intro bb' hBb'
            rw [hBbS] at hBb'; injection hBb' with hBbEq; subst hBbEq
            exact ⟨hStmtSuccLe, by rw [hOffSucc, hStmtOff, hLenN]⟩
          have hMkNextState : ∀ (lsS' lsT' : List LocalSlotExt),
              (∃ st1, ctxLowerStmt ctx stmt = [st1]) →
              evalStatementExt ctx.bodySrc fSrc memS stmt =
                .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := lsS' }], callerMem := memS } →
              SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length ctx.fieldTys ctx.ovfTys lsS' lsT' →
              SroaRelState ctx
                { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := lsS' }], callerMem := memS }
                { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := lsT' }], callerMem := memS } := by
            intro lsS' lsT' ⟨st1, hLow1⟩ hEv hR
            exact hMkNextStateN 1 lsS' lsT' (by rw [hLow1]; rfl) hEv hR
          have hSingleStep : ∀ (stmtTgt : StatementKind),
              ctxLowerStmt ctx stmt = [stmtTgt] →
              evalStepTupleAssert ctx.pTgt 0 { frames := [fTgt], callerMem := memS } =
                evalStatementExt ctx.bodyTgt fTgt memS stmtTgt := by
            intro stmtTgt hLow
            have hSt0 : Trusted.MirSemantics.getElem?
                (listFlatMap (ctxLowerStmt ctx) bbSrc.statements) fTgt.stmtIdx = some stmtTgt := by
              have h0 := hAtLowered 0 stmtTgt (by rw [hLow]; rfl)
              rw [Nat.add_zero] at h0; exact h0
            unfold evalStepTupleAssert; dsimp
            rw [hDefT, sroaCtx_getElem?_bodyTgt ctx]; dsimp; rw [hBbTAt]; dsimp; rw [hSt0]
          dsimp
          cases stmt with
          | nop =>
            have hLow : ctxLowerStmt ctx .nop = [.nop] := rfl
            have hTgt1 := hSingleStep .nop hLow
            dsimp [evalStatementExt] at hTgt1; dsimp [evalStatementExt]
            refine ⟨1, _, Nat.zero_lt_succ 0, ?_, hMkNextState fSrc.locals fTgt.locals ⟨_, hLow⟩ rfl hLocRel⟩
            dsimp [evalTupleAssertFuel]; rw [hTgt1]
          | unsupported =>
            have hLow : ctxLowerStmt ctx .unsupported = [.unsupported] := rfl
            have hTgt1 := hSingleStep .unsupported hLow
            dsimp [evalStatementExt] at hTgt1; dsimp [evalStatementExt]
            exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
          | storageLive id =>
            dsimp [stmtLocalsLt] at hSIb
            have hIdLt := nat_blt_lt hSIb
            cases hEqTup : Nat.beq id ctx.plan.tupLocal with
            | false =>
              have hIdNe := nat_ne_of_beq_false hEqTup
              have hLow : ctxLowerStmt ctx (.storageLive id) = [.storageLive id] := by
                unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [hEqTup]; rfl
              have hTgt1 := hSingleStep (.storageLive id) hLow
              dsimp [evalStatementExt] at hTgt1; dsimp [evalStatementExt]
              rw [sroaCtx_localsTgt_getElem?_lt ctx hIdLt hIdNe] at hTgt1
              cases hTy : Trusted.MirSemantics.getElem? ctx.bodySrc.locals id with
              | none =>
                rw [hTy] at hTgt1; dsimp at hTgt1; dsimp
                exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
              | some ty =>
                rw [hTy] at hTgt1; dsimp at hTgt1; dsimp
                have hLtS : id < fSrc.locals.length := by rw [hLocRel.1]; exact hIdLt
                have hLtT : id < fTgt.locals.length := by
                  rw [hLocRel.2.1]; exact nat_lt_add_right _ (nat_lt_add_right _ hIdLt)
                let ⟨lsS', hSetS⟩ := setElem?_some_of_lt fSrc.locals id (liveUninitSlotExt ty) hLtS
                let ⟨lsT', hSetT⟩ := setElem?_some_of_lt fTgt.locals id (liveUninitSlotExt ty) hLtT
                rw [hSetS]; rw [hSetT] at hTgt1; dsimp at hTgt1; dsimp
                have hRel' := sroaRelLocals_set_ne hLocRel hIdLt hIdNe hSetS hSetT
                refine ⟨1, _, Nat.zero_lt_succ 0, ?_,
                  hMkNextState lsS' lsT' ⟨_, hLow⟩ (by dsimp [evalStatementExt]; rw [hTy]; dsimp; rw [hSetS]) hRel'⟩
                dsimp [evalTupleAssertFuel]; rw [hTgt1]
            | true =>
              have hIdEq := nat_beq_eq hEqTup; subst hIdEq
              have hLow : ctxLowerStmt ctx (.storageLive ctx.plan.tupLocal) =
                  mkStorageLivesLoop ctx.bodySrc.locals.length 0 ctx.fieldTys.length := by
                unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [nat_beq_refl]; rfl
              have hLowLen : (ctxLowerStmt ctx (.storageLive ctx.plan.tupLocal)).length = ctx.fieldTys.length := by
                rw [hLow]; exact mkStorageLivesLoop_length _ 0 _
              have hPosK : 0 < ctx.fieldTys.length := sroaCtx_fieldCount_pos ctx
              dsimp [evalStatementExt]
              rw [ctx.hTupTy]; dsimp
              have hTupLtS : ctx.plan.tupLocal < fSrc.locals.length := by rw [hLocRel.1]; exact ctx.hTupLt
              let ⟨lsS', hSetS⟩ := setElem?_some_of_lt fSrc.locals ctx.plan.tupLocal
                (liveUninitSlotExt (.tuple ctx.fieldTys)) hTupLtS
              rw [hSetS]; dsimp
              let ⟨lsT', hExecT, hLenT', hPre, _, hFields⟩ :=
                sroa_exec_storageLives_loop ctx (mem := memS) hBbTAt ctx.fieldTys.length
                  0 fTgt.stmtIdx fTgt.locals (Nat.zero_add _) hLocRel.2.1 (fun j hj => by
                    have hM := mkStorageLivesLoop_getElem? ctx.bodySrc.locals.length 0 ctx.fieldTys.length j hj
                    rw [← hLow] at hM
                    exact hAtLowered j _ hM)
              have hRel' : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
                  ctx.fieldTys ctx.ovfTys lsS' lsT' := by
                refine ⟨by rw [setElem?_length hSetS, hLocRel.1],
                        by rw [hLenT', hLocRel.2.1], ?_, ?_⟩
                · intro i hi hINe
                  have hLt0 : i < ctx.bodySrc.locals.length + 0 := by rw [Nat.add_zero]; exact hi
                  rw [hPre i hLt0, setElem?_getElem?_ne hSetS hINe]
                  exact hLocRel.2.2.1 i hi hINe
                · rw [setElem?_getElem?_same hSetS]
                  unfold liveUninitSlotExt; dsimp
                  rw [ctx.hFlatTup]; dsimp
                  refine ⟨map_length_eq liveUninitFieldVal ctx.fieldTys, ?_⟩
                  intro j hJLt
                  have hFj := hFields j hJLt
                  rw [Nat.zero_add] at hFj
                  rw [hFj, getElem?_map]
                  cases Trusted.MirSemantics.getElem? ctx.fieldTys j <;> rfl
              have hFTOwn : fTgt =
                  { defId := ctx.plan.defId, blockIdx := fTgt.blockIdx,
                    stmtIdx := fTgt.stmtIdx, locals := fTgt.locals } := by
                cases fTgt; dsimp at hDefT; subst hDefT; rfl
              rw [← hFTOwn, ← hDefT] at hExecT
              refine ⟨ctx.fieldTys.length,
                { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + ctx.fieldTys.length, locals := lsT' }],
                  callerMem := memS },
                hPosK, hExecT,
                hMkNextStateN ctx.fieldTys.length lsS' lsT' hLowLen
                  (by dsimp [evalStatementExt]; rw [ctx.hTupTy]; dsimp; rw [hSetS]) hRel'⟩
          | storageDead id =>
            dsimp [stmtLocalsLt] at hSIb
            have hIdLt := nat_blt_lt hSIb
            cases hEqTup : Nat.beq id ctx.plan.tupLocal with
            | false =>
              have hIdNe := nat_ne_of_beq_false hEqTup
              have hLow : ctxLowerStmt ctx (.storageDead id) = [.storageDead id] := by
                unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [hEqTup]; rfl
              have hTgt1 := hSingleStep (.storageDead id) hLow
              dsimp [evalStatementExt] at hTgt1; dsimp [evalStatementExt]
              cases hZ : Nat.beq id 0 with
              | true =>
                rw [hZ] at hTgt1; dsimp at hTgt1; dsimp
                exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
              | false =>
                rw [hZ] at hTgt1; dsimp at hTgt1; dsimp
                have hLtS : id < fSrc.locals.length := by rw [hLocRel.1]; exact hIdLt
                have hLtT : id < fTgt.locals.length := by
                  rw [hLocRel.2.1]; exact nat_lt_add_right _ (nat_lt_add_right _ hIdLt)
                let ⟨lsS', hSetS⟩ := setElem?_some_of_lt fSrc.locals id .dead hLtS
                let ⟨lsT', hSetT⟩ := setElem?_some_of_lt fTgt.locals id .dead hLtT
                rw [hSetS]; rw [hSetT] at hTgt1; dsimp at hTgt1; dsimp
                have hRel' := sroaRelLocals_set_ne hLocRel hIdLt hIdNe hSetS hSetT
                refine ⟨1, _, Nat.zero_lt_succ 0, ?_,
                  hMkNextState lsS' lsT' ⟨_, hLow⟩ (by dsimp [evalStatementExt]; rw [hZ]; dsimp; rw [hSetS]) hRel'⟩
                dsimp [evalTupleAssertFuel]; rw [hTgt1]
            | true =>
              have hIdEq := nat_beq_eq hEqTup; subst hIdEq
              have hLow : ctxLowerStmt ctx (.storageDead ctx.plan.tupLocal) =
                  mkStorageDeadsLoop ctx.bodySrc.locals.length 0 ctx.fieldTys.length := by
                unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [nat_beq_refl]; rfl
              have hLowLen : (ctxLowerStmt ctx (.storageDead ctx.plan.tupLocal)).length = ctx.fieldTys.length := by
                rw [hLow]; exact mkStorageDeadsLoop_length _ 0 _
              have hPosK : 0 < ctx.fieldTys.length := sroaCtx_fieldCount_pos ctx
              have hNe0 : Nat.beq ctx.plan.tupLocal 0 = false :=
                nat_beq_false_of_ne (sroaCtx_tupLocal_ne_zero ctx)
              dsimp [evalStatementExt]
              rw [hNe0]; dsimp
              have hTupLtS : ctx.plan.tupLocal < fSrc.locals.length := by rw [hLocRel.1]; exact ctx.hTupLt
              let ⟨lsS', hSetS⟩ := setElem?_some_of_lt fSrc.locals ctx.plan.tupLocal .dead hTupLtS
              rw [hSetS]; dsimp
              let ⟨lsT', hExecT, hLenT', hPre, _, hDeads⟩ :=
                sroa_exec_storageDeads_loop ctx (mem := memS) hBbTAt ctx.fieldTys.length
                  0 fTgt.stmtIdx fTgt.locals (Nat.zero_add _) hLocRel.2.1 (fun j hj => by
                    have hM := mkStorageDeadsLoop_getElem? ctx.bodySrc.locals.length 0 ctx.fieldTys.length j hj
                    rw [← hLow] at hM
                    exact hAtLowered j _ hM)
              have hRel' : SroaRelLocals ctx.plan.tupLocal ctx.bodySrc.locals.length
                  ctx.fieldTys ctx.ovfTys lsS' lsT' := by
                refine ⟨by rw [setElem?_length hSetS, hLocRel.1],
                        by rw [hLenT', hLocRel.2.1], ?_, ?_⟩
                · intro i hi hINe
                  have hLt0 : i < ctx.bodySrc.locals.length + 0 := by rw [Nat.add_zero]; exact hi
                  rw [hPre i hLt0, setElem?_getElem?_ne hSetS hINe]
                  exact hLocRel.2.2.1 i hi hINe
                · rw [setElem?_getElem?_same hSetS]
                  intro j hJLt
                  have hDj := hDeads j hJLt
                  rw [Nat.zero_add] at hDj; exact hDj
              have hFTOwn : fTgt =
                  { defId := ctx.plan.defId, blockIdx := fTgt.blockIdx,
                    stmtIdx := fTgt.stmtIdx, locals := fTgt.locals } := by
                cases fTgt; dsimp at hDefT; subst hDefT; rfl
              rw [← hFTOwn, ← hDefT] at hExecT
              refine ⟨ctx.fieldTys.length,
                { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + ctx.fieldTys.length, locals := lsT' }],
                  callerMem := memS },
                hPosK, hExecT,
                hMkNextStateN ctx.fieldTys.length lsS' lsT' hLowLen
                  (by dsimp [evalStatementExt]; rw [hNe0]; dsimp; rw [hSetS]) hRel'⟩
          | assign dst rv =>
            cases dst with
            | mk dstId dstProj =>
              let ⟨hDstLtB, hRvLt⟩ := bool_and_true hSIb
              have hDstLt := nat_blt_lt hDstLtB
              cases hEqTup : Nat.beq dstId ctx.plan.tupLocal with
              | false =>
                have hDstNe := nat_ne_of_beq_false hEqTup
                dsimp [stmtTupleValid] at hSVal
                rw [hEqTup] at hSVal; dsimp at hSVal
                have hLow : ctxLowerStmt ctx (.assign ⟨dstId, dstProj⟩ rv) =
                    [.assign ⟨dstId, dstProj⟩
                      (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv)] := by
                  unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [hEqTup]; rfl
                have hTgt1 := hSingleStep _ hLow
                cases dstProj with
                | cons pe rest =>
                  cases rest with
                  | cons _ _ =>
                    cases pe <;> (
                      dsimp [evalStatementExt] at hTgt1; dsimp [evalStatementExt]
                      exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩)
                  | nil =>
                    cases pe with
                    | deref | unsupported =>
                      dsimp [evalStatementExt] at hTgt1; dsimp [evalStatementExt]
                      exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                    | field idx fTy =>
                      dsimp [evalStatementExt] at hTgt1; dsimp [evalStatementExt]
                      rw [sroaCtx_localsTgt_getElem?_lt ctx hDstLt hDstNe] at hTgt1
                      cases hTy : Trusted.MirSemantics.getElem? ctx.bodySrc.locals dstId with
                      | none =>
                        rw [hTy] at hTgt1; dsimp at hTgt1; dsimp
                        exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                      | some dTy =>
                        rw [hTy] at hTgt1
                        cases dTy with
                        | tuple fTys =>
                          dsimp at hTgt1; dsimp
                          cases hNf : (!isFlatTupleTy (.tuple fTys)) with
                          | true =>
                            rw [hNf] at hTgt1; dsimp at hTgt1; dsimp
                            exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                          | false =>
                            rw [hNf] at hTgt1; dsimp at hTgt1; dsimp
                            cases hFt : Trusted.MirSemantics.getElem? fTys idx with
                            | none =>
                              rw [hFt] at hTgt1; dsimp at hTgt1; dsimp
                              exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                            | some dft =>
                              rw [hFt] at hTgt1; dsimp at hTgt1; dsimp
                              cases hNt : (!MirTy.beq fTy dft) with
                              | true =>
                                rw [hNt] at hTgt1; dsimp at hTgt1; dsimp
                                exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                              | false =>
                                rw [hNt] at hTgt1; dsimp at hTgt1; dsimp
                                have hRvSim := sroa_evalRvalueExt_sim ctx (dstTy := dft) hLocRel hRvLt hSVal
                                cases hRv : evalRvalueExt ctx.bodySrc.locals fSrc.locals dft rv with
                                | error k =>
                                  rw [hRv] at hRvSim; rw [hRvSim] at hTgt1; dsimp at hTgt1; dsimp
                                  exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                                | ok pair =>
                                  rw [hRv] at hRvSim
                                  cases pair with
                                  | mk val lsS1 =>
                                    dsimp
                                    let ⟨lsT1, hRvT, hRel1⟩ := hRvSim
                                    rw [hRvT] at hTgt1; dsimp at hTgt1
                                    have hWSim := sroa_writeTupleFieldExt_ne_sim ctx (idx := idx)
                                      (fieldTy := dft) (val := val) hRel1 hDstLt hDstNe
                                    cases hW : writeTupleFieldExt lsS1 dstId idx dft val with
                                    | error k =>
                                      rw [hW] at hWSim; rw [hWSim] at hTgt1; dsimp at hTgt1; dsimp
                                      exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                                    | ok lsS2 =>
                                      rw [hW] at hWSim
                                      let ⟨lsT2, hWT, hRel2⟩ := hWSim
                                      rw [hWT] at hTgt1; dsimp at hTgt1; dsimp
                                      refine ⟨1, _, Nat.zero_lt_succ 0, ?_,
                                        hMkNextState lsS2 lsT2 ⟨_, hLow⟩ (by
                                          dsimp [evalStatementExt]; rw [hTy]; dsimp
                                          rw [hNf]; dsimp; rw [hFt]; dsimp; rw [hNt]; dsimp
                                          rw [hRv]; dsimp; rw [hW]) hRel2⟩
                                      dsimp [evalTupleAssertFuel]; rw [hTgt1]
                        | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                          dsimp at hTgt1; dsimp
                          exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                | nil =>
                  have hWhole := sroa_evalStatement_assign_whole_ne ctx (fSrc := fSrc) (fTgt := fTgt)
                    (memS := memS) dstId rv hDstLt hDstNe hLocRel hRvLt hSVal
                  cases hEvA : evalStatementExt ctx.bodySrc fSrc memS (.assign ⟨dstId, []⟩ rv) with
                  | done out => rw [hEvA] at hWhole; exact False.elim hWhole
                  | fault fk =>
                    rw [hEvA] at hWhole; rw [hWhole] at hTgt1
                    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                  | step sSrc' =>
                    rw [hEvA] at hWhole
                    let ⟨lsS2, lsT2, hSEq, hTEq, hRel2⟩ := hWhole
                    subst hSEq
                    rw [hTEq] at hTgt1; dsimp
                    refine ⟨1, _, Nat.zero_lt_succ 0, ?_, hMkNextState lsS2 lsT2 ⟨_, hLow⟩ hEvA hRel2⟩
                    dsimp [evalTupleAssertFuel]; rw [hTgt1]
              | true =>
                have hDstEq := nat_beq_eq hEqTup; subst hDstEq
                dsimp [stmtTupleValid] at hSVal
                rw [nat_beq_refl] at hSVal; dsimp at hSVal
                cases dstProj with
                | cons pe rest =>
                  cases rest with
                  | cons _ _ => cases pe <;> cases hSVal
                  | nil =>
                    cases pe with
                    | deref | unsupported => cases hSVal
                    | field idx fTy =>
                      let ⟨hValidField, hRvVal⟩ := bool_and_true hSVal
                      dsimp [isValidTupleFieldPlace] at hValidField
                      rw [nat_beq_refl, Bool.true_and] at hValidField
                      cases hFty : Trusted.MirSemantics.getElem? ctx.fieldTys idx with
                      | none => rw [hFty] at hValidField; cases hValidField
                      | some dft =>
                        rw [hFty] at hValidField; dsimp at hValidField
                        have hIdxLt := getElem?_some_lt hFty
                        have hSc := list_all_getElem? (sroaCtx_fieldTys_all_scalar ctx) hFty
                        have hLow : ctxLowerStmt ctx (.assign ⟨ctx.plan.tupLocal, [.field idx fTy]⟩ rv) =
                            [.assign ⟨ctx.bodySrc.locals.length + idx, []⟩
                              (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv)] := by
                          unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [nat_beq_refl]; rfl
                        have hTgt1 := hSingleStep _ hLow
                        dsimp [evalStatementExt] at hTgt1; dsimp [evalStatementExt]
                        rw [ctx.hTupTy]; dsimp; rw [ctx.hFlatTup, hFty]; dsimp; rw [hValidField]; dsimp
                        rw [sroaCtx_localsTgt_getElem?_field ctx hIdxLt, hFty] at hTgt1
                        dsimp at hTgt1
                        cases hRvCase : rv with
                        | aggregateTuple ops =>
                          rw [hRvCase] at hTgt1
                          dsimp [rewriteTupleRvalue, evalRvalueExt] at hTgt1; dsimp [rewriteTupleRvalue, evalRvalueExt]
                          cases dft with
                          | tuple _ => cases hSc
                          | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                            dsimp at hTgt1
                            exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt1]⟩
                        | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _
                        | ref _ _ | addressOf _ _ | unsupported =>
                          rw [← hRvCase]
                          have hTgt2 : evalStepTupleAssert ctx.pTgt 0 { frames := [fTgt], callerMem := memS } =
                              match evalRvalueExt ctx.bodyTgt.locals fTgt.locals dft
                                  (rewriteTupleRvalue ctx.plan.tupLocal ctx.bodySrc.locals.length rv) with
                              | .error k => .fault k
                              | .ok (val, ls1) =>
                                match writePlaceExt ls1 (ctx.bodySrc.locals.length + idx) dft val with
                                | .error k => .fault k
                                | .ok ls2 =>
                                  .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := ls2 }],
                                          callerMem := memS } := by
                            rw [hTgt1, hRvCase]; dsimp [rewriteTupleRvalue]
                            cases dft with
                            | tuple _ => cases hSc
                            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => rfl
                          have hRvSim := sroa_evalRvalueExt_sim ctx (dstTy := dft) hLocRel hRvLt hRvVal
                          cases hRv : evalRvalueExt ctx.bodySrc.locals fSrc.locals dft rv with
                          | error k =>
                            rw [hRv] at hRvSim; rw [hRvSim] at hTgt2; dsimp at hTgt2; dsimp
                            exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt2]⟩
                          | ok pair =>
                            rw [hRv] at hRvSim
                            cases pair with
                            | mk val lsS1 =>
                              dsimp
                              let ⟨lsT1, hRvT, hRel1⟩ := hRvSim
                              rw [hRvT] at hTgt2; dsimp at hTgt2
                              have hWSim := sroa_writeTupleFieldExt_tup_sim ctx (val := val) hRel1 hFty
                              cases hW : writeTupleFieldExt lsS1 ctx.plan.tupLocal idx dft val with
                              | error k =>
                                rw [hW] at hWSim; rw [hWSim] at hTgt2; dsimp at hTgt2; dsimp
                                exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hTgt2]⟩
                              | ok lsS2 =>
                                rw [hW] at hWSim
                                let ⟨lsT2, hWT, hRel2⟩ := hWSim
                                rw [hWT] at hTgt2; dsimp at hTgt2; dsimp
                                refine ⟨1, _, Nat.zero_lt_succ 0, ?_,
                                  hMkNextState lsS2 lsT2 ⟨_, hLow⟩ (by
                                    dsimp [evalStatementExt]; rw [ctx.hTupTy]; dsimp; rw [ctx.hFlatTup, hFty]; dsimp; rw [hValidField]
                                    dsimp; rw [hRv]; dsimp; rw [hW]) hRel2⟩
                                dsimp [evalTupleAssertFuel]; rw [hTgt2]
                | nil =>
                  cases rv with
                  | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _ | unsupported =>
                    cases hSVal
                  | aggregateTuple ops =>
                    let ⟨hNoSelf, hRelTys⟩ := bool_and_true hSVal
                    have hOpsLen : ops.length = ctx.fieldTys.length := listRel_length hRelTys
                    have hNoAny : ops.any (operandMentionsLocal ctx.plan.tupLocal) = false :=
                      list_any_false_of_forall_getElem? (fun j o hj =>
                        bool_not_true (list_all_getElem? (p := fun o => !operandMentionsLocal ctx.plan.tupLocal o) hNoSelf hj))
                    have hLow : ctxLowerStmt ctx (.assign ⟨ctx.plan.tupLocal, []⟩ (.aggregateTuple ops)) =
                        mkIndexedUseAssignsLoop ctx.bodySrc.locals.length 0
                          (ops.map (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length)) := by
                      unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [nat_beq_refl]; rfl
                    have hLowLen : (ctxLowerStmt ctx (.assign ⟨ctx.plan.tupLocal, []⟩ (.aggregateTuple ops))).length =
                        ops.length := by
                      rw [hLow, mkIndexedUseAssignsLoop_length, map_length_eq]
                    have hPosOps : 0 < ops.length := by rw [hOpsLen]; exact sroaCtx_fieldCount_pos ctx
                    have hFTOwn : fTgt =
                        { defId := ctx.plan.defId, blockIdx := fTgt.blockIdx,
                          stmtIdx := fTgt.stmtIdx, locals := fTgt.locals } := by
                      cases fTgt; dsimp at hDefT; subst hDefT; rfl
                    have hAggExec := sroa_exec_aggregate_loop ctx (mem := memS) hBbTAt ops
                      ctx.fieldTys 0 fTgt.stmtIdx fSrc.locals fTgt.locals hOpsLen
                      (fun j ft hj => by rw [Nat.zero_add]; exact hj)
                      hRvLt hNoSelf hLocRel (fun j opnd hj => by
                        have hMapAt : Trusted.MirSemantics.getElem?
                            (ops.map (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length)) j =
                            some (rewriteTupleOperand ctx.plan.tupLocal ctx.bodySrc.locals.length opnd) := by
                          rw [getElem?_map, hj]; rfl
                        have hM := mkIndexedUseAssignsLoop_getElem? ctx.bodySrc.locals.length 0 _ j _ hMapAt
                        rw [← hLow] at hM
                        exact hAtLowered j _ hM)
                    dsimp [evalStatementExt]
                    rw [ctx.hTupTy]; dsimp; rw [ctx.hFlatTup, nat_beq_of_eq hOpsLen, hNoAny]; dsimp
                    cases hAggS : evalAggregateInPlaceExt ctx.bodySrc.locals fSrc.locals
                        ctx.plan.tupLocal 0 ops ctx.fieldTys with
                    | error k =>
                      rw [hAggS] at hAggExec; dsimp
                      let ⟨d, hdPos, hD⟩ := hAggExec
                      exact ⟨d, hdPos, by rw [hFTOwn]; exact hD⟩
                    | ok lsS' =>
                      rw [hAggS] at hAggExec; dsimp
                      let ⟨lsT', hExecT, hRel'⟩ := hAggExec
                      rw [← hFTOwn, ← hDefT] at hExecT
                      refine ⟨ops.length,
                        { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + ops.length, locals := lsT' }],
                          callerMem := memS },
                        hPosOps, hExecT,
                        hMkNextStateN ops.length lsS' lsT' hLowLen (by
                          dsimp [evalStatementExt]
                          rw [ctx.hTupTy]; dsimp; rw [ctx.hFlatTup, nat_beq_of_eq hOpsLen, hNoAny]; dsimp
                          rw [hAggS]) hRel'⟩
                  | binaryOp op lhs rhs =>
                    dsimp at hSVal
                    cases hOvfOp : isSroaLowerableOvfBinOp op with
                    | false => rw [hOvfOp] at hSVal; cases hSVal
                    | true =>
                      rw [hOvfOp] at hSVal; dsimp at hSVal
                      cases hW : unsignedOvfTupleWidth? ctx.fieldTys with
                      | none => rw [hW] at hSVal; cases hSVal
                      | some w =>
                        rw [hW] at hSVal; dsimp at hSVal
                        have hFieldTysEq : ctx.fieldTys = [.int w false, .bool] := by
                          cases hFTs : ctx.fieldTys with
                          | nil => rw [hFTs] at hW; cases hW
                          | cons t0 r0 =>
                            rw [hFTs] at hW
                            cases t0 with
                            | int w' s' =>
                              cases s' with
                              | true => cases hW
                              | false =>
                                cases r0 with
                                | nil => cases hW
                                | cons t1 r1 =>
                                  cases t1 with
                                  | bool =>
                                    cases r1 with
                                    | cons _ _ => cases hW
                                    | nil =>
                                      injection hW with hWeq; subst hWeq; rfl
                                  | int _ _ | unit | never | enum _ | tuple _
                                  | ref _ _ | rawPtr _ _ | unsupported => cases hW
                            | bool | unit | never | enum _ | tuple _
                            | ref _ _ | rawPtr _ _ | unsupported => cases hW
                        have hOpDisj : op = .addWithOverflow ∨ op = .subWithOverflow := by
                          cases op with
                          | addWithOverflow => exact Or.inl rfl
                          | subWithOverflow => exact Or.inr rfl
                          | add | addUnchecked | sub | subUnchecked | mul | mulUnchecked
                          | mulWithOverflow | div | rem | bitXor | bitAnd | bitOr
                          | shl | shlUnchecked | shr | shrUnchecked | eq | lt | le
                          | ne | ge | gt | offset => cases hOvfOp
                        let ⟨hS123, hRTy⟩ := bool_and_true hSVal
                        let ⟨hS12, hLTy⟩ := bool_and_true hS123
                        let ⟨hLVal, hRVal⟩ := bool_and_true hS12
                        let ⟨hLLt, hRLt⟩ := bool_and_true hRvLt
                        have hLowLen8 : (ctxLowerStmt ctx (.assign ⟨ctx.plan.tupLocal, []⟩ (.binaryOp op lhs rhs))).length = 8 := by
                          cases hOpDisj with
                          | inl h => subst h; unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [nat_beq_refl]; rfl
                          | inr h => subst h; unfold ctxLowerStmt lowerSroaStmt; dsimp; rw [nat_beq_refl]; rfl
                        have hFSOwn : fSrc =
                            { defId := ctx.plan.defId, blockIdx := fSrc.blockIdx,
                              stmtIdx := fSrc.stmtIdx, locals := fSrc.locals } := by
                          cases fSrc; dsimp at hDefS; subst hDefS; rfl
                        have hFTOwn : fTgt =
                            { defId := ctx.plan.defId, blockIdx := fSrc.blockIdx,
                              stmtIdx := sroaStmtOffset ctx bbSrc fSrc.stmtIdx, locals := fTgt.locals } := by
                          cases fTgt; dsimp at hDefT hBlkEq hStmtOff
                          subst hDefT; subst hBlkEq; subst hStmtOff; rfl
                        have hOvfSim := sroa_exec_ovf_assign ctx (mem := memS) hAllSup hBbS
                          (by rw [hBlkEq]; exact hBbTAt) hStS hOpDisj hFieldTysEq
                          hLLt hRLt hLVal hRVal hLTy hRTy hLocWt hLocRel (fun j st hj => by
                            have hA := hAtLowered j st hj
                            rw [hStmtOff] at hA; exact hA)
                        dsimp at hOvfSim
                        rw [← hFSOwn, ← hFTOwn] at hOvfSim
                        cases hEvStmt : evalStatementExt ctx.bodySrc fSrc memS
                            (.assign ⟨ctx.plan.tupLocal, []⟩ (.binaryOp op lhs rhs)) with
                        | done out => rw [hEvStmt] at hOvfSim; exact False.elim hOvfSim
                        | fault fk =>
                          rw [hEvStmt] at hOvfSim
                          exact hOvfSim
                        | step sSrc' =>
                          rw [hEvStmt] at hOvfSim
                          let ⟨lsTgt', hFuel8, fSrc', hSSrc'Eq, hD', hB', hI', hRel'⟩ := hOvfSim
                          subst hSSrc'Eq
                          have hFS'Eq : fSrc' = { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := fSrc'.locals } := by
                            cases fSrc'; cases fSrc; dsimp at hDefS hD' hB' hI'
                            subst hDefS; subst hD'; subst hB'; subst hI'; rfl
                          rw [hFS'Eq] at hEvStmt; rw [hFS'Eq]
                          have hState' := hMkNextStateN 8 fSrc'.locals lsTgt' hLowLen8 hEvStmt hRel'
                          rw [← hStmtOff] at hFuel8
                          have hFuel8' : evalTupleAssertFuel ctx.pTgt 8 { frames := [fTgt], callerMem := memS } =
                              .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 8, locals := lsTgt' }],
                                      callerMem := memS } := by
                            cases fTgt; cases fSrc; dsimp at hDefT hBlkEq hFuel8; dsimp
                            subst hDefT; subst hBlkEq; exact hFuel8
                          exact ⟨8,
                            { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 8, locals := lsTgt' }],
                              callerMem := memS },
                            Nat.zero_lt_succ 7, hFuel8', hState'⟩

private theorem sroa_init_sim (ctx : SroaCtx) (q : Query)
    (hEntry : ctx.pSrc.entryDefId = ctx.plan.defId) :
    (∀ k, initStateTupleAssert ctx.pSrc q = .error k →
      initStateTupleAssert ctx.pTgt q = .error k) ∧
    (∀ s₀Src, initStateTupleAssert ctx.pSrc q = .ok s₀Src →
      ∃ s₀Tgt, initStateTupleAssert ctx.pTgt q = .ok s₀Tgt ∧
        SroaRelState ctx s₀Src s₀Tgt) := by
  have hPw : ctx.pTgt.pointerWidthBits = ctx.pSrc.pointerWidthBits := by rw [ctx.hPTgt]
  have hVer : ctx.pTgt.mirProfileVersion = ctx.pSrc.mirProfileVersion := by rw [ctx.hPTgt]
  have hEntT : ctx.pTgt.entryDefId = ctx.plan.defId := by rw [ctx.hPTgt]; exact hEntry
  have hGetS : Trusted.MirSemantics.getElem? ctx.pSrc.bodies ctx.pSrc.entryDefId = some ctx.bodySrc := by
    rw [hEntry]; exact ctx.hGetSrc
  have hGetT : Trusted.MirSemantics.getElem? ctx.pTgt.bodies ctx.pTgt.entryDefId = some ctx.bodyTgt := by
    rw [hEntT]; exact sroaCtx_getElem?_bodyTgt ctx
  have hEmpT : ctx.bodyTgt.basicBlocks.isEmpty = false := by
    rw [ctx.hBodyTgt]; dsimp
    rw [list_isEmpty_eq_of_length (map_length_eq _ _)]
    exact ctx.hNonEmpty
  have hArgLtS : Nat.blt ctx.bodySrc.argumentCount ctx.bodySrc.locals.length = true :=
    nat_lt_blt (Nat.lt_trans ctx.hArgLt ctx.hTupLt)
  have hArgLtT : Nat.blt ctx.bodyTgt.argumentCount ctx.bodyTgt.locals.length = true := by
    rw [ctx.hBodyTgt]; dsimp
    rw [list_append_length, list_append_length, sroaCtx_localsUpdated_len]
    exact nat_lt_blt (nat_lt_add_right _ (nat_lt_add_right _ (Nat.lt_trans ctx.hArgLt ctx.hTupLt)))
  have hCommon : ∀ {r : Except FaultKind StateExt},
      initStateTupleAssert ctx.pSrc q = r →
      (match r with
       | .error k => initStateTupleAssert ctx.pTgt q = .error k
       | .ok s₀Src =>
         ∃ s₀Tgt, initStateTupleAssert ctx.pTgt q = .ok s₀Tgt ∧
           SroaRelState ctx s₀Src s₀Tgt) := by
    intro r hInitS
    unfold initStateTupleAssert at hInitS; unfold initStateTupleAssert
    rw [hGetS] at hInitS
    rw [hPw, hVer, hGetT]
    cases hHdr : (!Nat.beq ctx.pSrc.pointerWidthBits 64 || !Nat.beq ctx.pSrc.mirProfileVersion 1) with
    | true =>
      rw [hHdr] at hInitS; dsimp at hInitS; subst hInitS; rfl
    | false =>
      rw [hHdr] at hInitS; dsimp at hInitS; dsimp
      cases hMem : (!q.callerMem.allocations.isEmpty) with
      | true =>
        rw [hMem] at hInitS; dsimp at hInitS; subst hInitS; rfl
      | false =>
        rw [hMem] at hInitS; dsimp at hInitS; dsimp
        rw [ctx.hNonEmpty, hArgLtS, sroaCtx_storageAnnotationsInBounds_src ctx] at hInitS
        rw [hEmpT, hArgLtT, sroaCtx_storageAnnotationsInBounds_tgt ctx,
            sroaCtx_allSupported_eq ctx, sroaCtx_paramTys_eq ctx]
        dsimp at hInitS; dsimp
        cases hSup : ctx.bodySrc.locals.all isSupportedTupleOrScalarTy with
        | false =>
          rw [hSup] at hInitS; dsimp at hInitS; subst hInitS; rfl
        | true =>
          rw [hSup] at hInitS; dsimp at hInitS; dsimp
          cases hArgs : checkArgsMatchExt q.args
              ((ctx.bodySrc.locals.drop 1).take ctx.bodySrc.argumentCount) with
          | false =>
            rw [hArgs] at hInitS; dsimp at hInitS; subst hInitS; rfl
          | true =>
            rw [hArgs] at hInitS; dsimp at hInitS; dsimp
            subst hInitS
            dsimp
            have hWtInit : StateWellTyped ctx.pSrc
                { frames :=
                    [{ defId := ctx.pSrc.entryDefId, blockIdx := 0, stmtIdx := 0,
                       locals := initLocalsExtLoop ctx.bodySrc q.args 0 ctx.bodySrc.locals }],
                  callerMem := q.callerMem } := by
              apply initStateTupleAssert_stateWellTyped (q := q)
              unfold initStateTupleAssert
              rw [hHdr]; dsimp; rw [hMem]; dsimp; rw [hGetS]; dsimp
              rw [ctx.hNonEmpty, hArgLtS, sroaCtx_storageAnnotationsInBounds_src ctx, hSup, hArgs]; rfl
            let ⟨fW, bW, hFW, hBW, _, hLocWt0⟩ := hWtInit
            injection hFW with hFWEq; subst hFWEq
            dsimp at hBW; rw [hGetS] at hBW; injection hBW with hBWEq; subst hBWEq
            refine ⟨_, rfl, rfl, _, _, rfl, rfl, hEntry, hEntT, rfl, hSup, hLocWt0, ?_, ?_⟩
            · -- SroaRelLocals at entry
              have hLenS := initLocalsExtLoop_length ctx.bodySrc q.args 0 ctx.bodySrc.locals
              have hLenT : (initLocalsExtLoop ctx.bodyTgt q.args 0 ctx.bodyTgt.locals).length =
                  ctx.bodySrc.locals.length + ctx.fieldTys.length + ctx.ovfTys.length := by
                rw [initLocalsExtLoop_length, sroaCtx_localsTgt_len ctx]
              have hArgEq : ctx.bodyTgt.argumentCount = ctx.bodySrc.argumentCount := by rw [ctx.hBodyTgt]
              refine ⟨hLenS, hLenT, ?_, ?_⟩
              · intro i hi hINe
                let ⟨ty, hTyS⟩ := getElem?_some_of_lt ctx.bodySrc.locals i hi
                have hTyT : Trusted.MirSemantics.getElem? ctx.bodyTgt.locals i = some ty := by
                  rw [sroaCtx_localsTgt_getElem?_lt ctx hi hINe, hTyS]
                rw [initLocalsExtLoop_getElem? ctx.bodyTgt q.args 0 ctx.bodyTgt.locals i ty hTyT,
                    initLocalsExtLoop_getElem? ctx.bodySrc q.args 0 ctx.bodySrc.locals i ty hTyS,
                    Nat.zero_add, hArgEq, sroaCtx_hasStorageAnnotation_lt ctx hi hINe]
              · have hTupAt := initLocalsExtLoop_getElem? ctx.bodySrc q.args 0 ctx.bodySrc.locals
                  ctx.plan.tupLocal (.tuple ctx.fieldTys) ctx.hTupTy
                rw [hTupAt, Nat.zero_add,
                    nat_beq_false_of_ne (sroaCtx_tupLocal_ne_zero ctx),
                    nat_gt_ble_false ctx.hArgLt]
                dsimp
                cases hAnn : hasStorageAnnotation ctx.bodySrc ctx.plan.tupLocal with
                | true =>
                  dsimp
                  intro j hJLt
                  let ⟨fty, hFty⟩ := getElem?_some_of_lt ctx.fieldTys j hJLt
                  have hTyT : Trusted.MirSemantics.getElem? ctx.bodyTgt.locals
                      (ctx.bodySrc.locals.length + j) = some fty := by
                    rw [sroaCtx_localsTgt_getElem?_field ctx hJLt, hFty]
                  rw [initLocalsExtLoop_getElem? ctx.bodyTgt q.args 0 ctx.bodyTgt.locals
                        (ctx.bodySrc.locals.length + j) fty hTyT, Nat.zero_add]
                  have hNe0 : Nat.beq (ctx.bodySrc.locals.length + j) 0 = false :=
                    nat_beq_false_of_ne (nat_add_ne_zero_left (sroaCtx_base_pos ctx))
                  have hGtArg : ctx.bodyTgt.argumentCount < ctx.bodySrc.locals.length + j := by
                    rw [hArgEq]
                    exact Nat.lt_of_lt_of_le (Nat.lt_trans ctx.hArgLt ctx.hTupLt) (Nat.le_add_right _ j)
                  rw [hNe0, nat_gt_ble_false hGtArg, sroaCtx_hasStorageAnnotation_field ctx hJLt, hAnn]; rfl
                | false =>
                  dsimp [liveUninitSlotExt]
                  rw [ctx.hFlatTup]; dsimp
                  refine ⟨map_length_eq liveUninitFieldVal ctx.fieldTys, ?_⟩
                  intro j hJLt
                  let ⟨fty, hFty⟩ := getElem?_some_of_lt ctx.fieldTys j hJLt
                  have hTyT : Trusted.MirSemantics.getElem? ctx.bodyTgt.locals
                      (ctx.bodySrc.locals.length + j) = some fty := by
                    rw [sroaCtx_localsTgt_getElem?_field ctx hJLt, hFty]
                  rw [initLocalsExtLoop_getElem? ctx.bodyTgt q.args 0 ctx.bodyTgt.locals
                        (ctx.bodySrc.locals.length + j) fty hTyT, Nat.zero_add]
                  have hNe0 : Nat.beq (ctx.bodySrc.locals.length + j) 0 = false :=
                    nat_beq_false_of_ne (nat_add_ne_zero_left (sroaCtx_base_pos ctx))
                  have hGtArg : ctx.bodyTgt.argumentCount < ctx.bodySrc.locals.length + j := by
                    rw [hArgEq]
                    exact Nat.lt_of_lt_of_le (Nat.lt_trans ctx.hArgLt ctx.hTupLt) (Nat.le_add_right _ j)
                  rw [hNe0, nat_gt_ble_false hGtArg, sroaCtx_hasStorageAnnotation_field ctx hJLt, hAnn]
                  dsimp
                  have hSc := list_all_getElem? (sroaCtx_fieldTys_all_scalar ctx) hFty
                  have hLiveEq : liveUninitSlotExt fty = .liveBase (liveUninitFieldVal fty) := by
                    cases fty <;> first | rfl | cases hSc
                  rw [hLiveEq, getElem?_map, hFty]; rfl
            · intro bb' _
              exact ⟨Nat.zero_le _, rfl⟩
  refine ⟨fun k h => hCommon h, fun s₀ h => hCommon h⟩

private theorem sroa_query_equiv_other_entry (ctx : SroaCtx) (q : Query)
    (hNe : ctx.pSrc.entryDefId ≠ ctx.plan.defId) :
    (WellFormedTupleAssert ctx.pTgt q ↔ WellFormedTupleAssert ctx.pSrc q) ∧
    (NoPanicAndWellFormedTupleAssert ctx.pTgt q ↔
      NoPanicAndWellFormedTupleAssert ctx.pSrc q) ∧
    (∀ out : TerminalOutExt,
      BehaviorTupleAssert ctx.pTgt q out ↔ BehaviorTupleAssert ctx.pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResultTupleAssert ctx.pTgt q (.fault k) ↔
        ReachesResultTupleAssert ctx.pSrc q (.fault k)) ∧
    (DivergesTupleAssert ctx.pTgt q ↔ DivergesTupleAssert ctx.pSrc q) := by
  have hPw : ctx.pTgt.pointerWidthBits = ctx.pSrc.pointerWidthBits := by rw [ctx.hPTgt]
  have hVer : ctx.pTgt.mirProfileVersion = ctx.pSrc.mirProfileVersion := by rw [ctx.hPTgt]
  have hEnt : ctx.pTgt.entryDefId = ctx.pSrc.entryDefId := by rw [ctx.hPTgt]
  have hGetEq : Trusted.MirSemantics.getElem? ctx.pTgt.bodies ctx.pSrc.entryDefId =
      Trusted.MirSemantics.getElem? ctx.pSrc.bodies ctx.pSrc.entryDefId := by
    rw [ctx.hPTgt]; dsimp
    exact setElem?_getElem?_ne ctx.hSetBody hNe
  have hInitEq : initStateTupleAssert ctx.pTgt q = initStateTupleAssert ctx.pSrc q := by
    unfold initStateTupleAssert
    rw [hPw, hVer, hEnt, hGetEq]
  let R : StateExt → StateExt → Prop := fun s1 s2 =>
    s1 = s2 ∧ (∀ f, s1.frames = [f] → f.defId ≠ ctx.plan.defId)
  have hStepPres : ∀ s c,
      (∀ f, s.frames = [f] → f.defId ≠ ctx.plan.defId) →
      evalStepTupleAssert ctx.pTgt c s = evalStepTupleAssert ctx.pSrc c s ∧
      (∀ s', evalStepTupleAssert ctx.pSrc c s = .step s' →
        ∀ f', s'.frames = [f'] → f'.defId ≠ ctx.plan.defId) := by
    intro s c hDefNe
    unfold evalStepTupleAssert
    cases hF : s.frames with
    | nil => exact ⟨rfl, fun _ h => by cases h⟩
    | cons frame rest =>
      cases rest with
      | cons _ _ => exact ⟨rfl, fun _ h => by cases h⟩
      | nil =>
        have hFNe : frame.defId ≠ ctx.plan.defId := hDefNe frame hF
        have hBodyEq : Trusted.MirSemantics.getElem? ctx.pTgt.bodies frame.defId =
            Trusted.MirSemantics.getElem? ctx.pSrc.bodies frame.defId := by
          rw [ctx.hPTgt]; dsimp
          exact setElem?_getElem?_ne ctx.hSetBody hFNe
        dsimp
        rw [hBodyEq]
        refine ⟨rfl, ?_⟩
        intro s' hEv f' hF'
        cases hB : Trusted.MirSemantics.getElem? ctx.pSrc.bodies frame.defId with
        | none => rw [hB] at hEv; cases hEv
        | some body =>
          rw [hB] at hEv; dsimp at hEv
          cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
          | none => rw [hBb] at hEv; cases hEv
          | some bb =>
            rw [hBb] at hEv; dsimp at hEv
            cases hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
            | some stmt =>
              rw [hSt] at hEv
              have hKeepDef : f'.defId = frame.defId := by
                cases stmt with
                | nop =>
                  dsimp [evalStatementExt] at hEv; injection hEv with hEq; subst hEq
                  dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                | unsupported => cases hEv
                | storageLive id =>
                  dsimp [evalStatementExt] at hEv
                  cases hT : Trusted.MirSemantics.getElem? body.locals id with
                  | none => rw [hT] at hEv; cases hEv
                  | some ty =>
                    rw [hT] at hEv; dsimp at hEv
                    cases hS : setElem? frame.locals id (liveUninitSlotExt ty) with
                    | none => rw [hS] at hEv; cases hEv
                    | some _ =>
                      rw [hS] at hEv; injection hEv with hEq; subst hEq
                      dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                | storageDead id =>
                  dsimp [evalStatementExt] at hEv
                  cases hZ : Nat.beq id 0 with
                  | true => rw [hZ] at hEv; cases hEv
                  | false =>
                    rw [hZ] at hEv; dsimp at hEv
                    cases hS : setElem? frame.locals id .dead with
                    | none => rw [hS] at hEv; cases hEv
                    | some _ =>
                      rw [hS] at hEv; injection hEv with hEq; subst hEq
                      dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                | assign dst rv =>
                  cases dst with
                  | mk did dproj =>
                    dsimp [evalStatementExt] at hEv
                    cases dproj with
                    | nil =>
                      dsimp at hEv
                      cases hT : Trusted.MirSemantics.getElem? body.locals did with
                      | none => rw [hT] at hEv; cases hEv
                      | some dty =>
                        rw [hT] at hEv; dsimp at hEv
                        cases rv with
                        | aggregateTuple ops =>
                          cases dty with
                          | tuple fTys =>
                            dsimp at hEv
                            cases hBad : (!isFlatTupleTy (.tuple fTys) ||
                                !Nat.beq ops.length fTys.length ||
                                ops.any (operandMentionsLocal did)) with
                            | true => rw [hBad] at hEv; cases hEv
                            | false =>
                              rw [hBad] at hEv; dsimp at hEv
                              cases hA : evalAggregateInPlaceExt body.locals frame.locals did 0 ops fTys with
                              | error _ => rw [hA] at hEv; cases hEv
                              | ok _ =>
                                rw [hA] at hEv; injection hEv with hEq; subst hEq
                                dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                          | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                            cases hEv
                        | ref _ _ | addressOf _ _ | unsupported =>
                          dsimp [evalRvalueExt] at hEv
                          cases dty <;> cases hEv
                        | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _ =>
                          dsimp at hEv
                          have hEvNonAgg : ∀ (rvX : Rvalue) (guard : Bool),
                              (if guard = true then
                                 (StepResult.fault FaultKind.unsupported : StepResult StateExt TerminalOutExt)
                               else
                                 match evalRvalueExt body.locals frame.locals dty rvX with
                                 | .error k => .fault k
                                 | .ok (v, ls1) =>
                                   match writePlaceExt ls1 did dty v with
                                   | .error k => .fault k
                                   | .ok ls2 =>
                                     .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := ls2 }],
                                             callerMem := s.callerMem }) = .step s' →
                              f'.defId = frame.defId := by
                            intro rvX guard hEvG
                            cases guard with
                            | true => cases hEvG
                            | false =>
                              dsimp at hEvG
                              cases hR : evalRvalueExt body.locals frame.locals dty rvX with
                              | error _ => rw [hR] at hEvG; cases hEvG
                              | ok pr =>
                                rw [hR] at hEvG
                                cases pr with
                                | mk v ls1 =>
                                  dsimp at hEvG
                                  cases hW : writePlaceExt ls1 did dty v with
                                  | error _ => rw [hW] at hEvG; cases hEvG
                                  | ok _ =>
                                    rw [hW] at hEvG; injection hEvG with hEq; subst hEq
                                    dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                          exact hEvNonAgg _ _ hEv
                    | cons pe rest =>
                      cases rest with
                      | cons _ _ => cases pe <;> cases hEv
                      | nil =>
                        cases pe with
                        | deref | unsupported => cases hEv
                        | field idx fty =>
                          dsimp at hEv
                          cases hT : Trusted.MirSemantics.getElem? body.locals did with
                          | none => rw [hT] at hEv; cases hEv
                          | some dty =>
                            rw [hT] at hEv
                            cases dty with
                            | tuple fTys =>
                              dsimp at hEv
                              cases hNf : (!isFlatTupleTy (.tuple fTys)) with
                              | true => rw [hNf] at hEv; cases hEv
                              | false =>
                                rw [hNf] at hEv; dsimp at hEv
                                cases hFt : Trusted.MirSemantics.getElem? fTys idx with
                                | none => rw [hFt] at hEv; cases hEv
                                | some dft =>
                                  rw [hFt] at hEv; dsimp at hEv
                                  cases hNt : (!MirTy.beq fty dft) with
                                  | true => rw [hNt] at hEv; cases hEv
                                  | false =>
                                    rw [hNt] at hEv; dsimp at hEv
                                    cases hR : evalRvalueExt body.locals frame.locals dft rv with
                                    | error _ => rw [hR] at hEv; cases hEv
                                    | ok pr =>
                                      rw [hR] at hEv
                                      cases pr with
                                      | mk v ls1 =>
                                        dsimp at hEv
                                        cases hW : writeTupleFieldExt ls1 did idx dft v with
                                        | error _ => rw [hW] at hEv; cases hEv
                                        | ok _ =>
                                          rw [hW] at hEv; injection hEv with hEq; subst hEq
                                          dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                              cases hEv
              rw [hKeepDef]; exact hFNe
            | none =>
              rw [hSt] at hEv; dsimp at hEv
              cases hLen : Nat.beq frame.stmtIdx bb.statements.length with
              | false => rw [hLen] at hEv; cases hEv
              | true =>
                rw [hLen] at hEv; dsimp [evalTerminatorExt] at hEv
                have hKeepDef : f'.defId = frame.defId := by
                  cases hTm : bb.terminator with
                  | goto _ =>
                    rw [hTm] at hEv; dsimp [jumpToBlockExt] at hEv
                    injection hEv with hEq; subst hEq
                    dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                  | unreachable | unwindResume | call _ _ _ _ _ | unsupported =>
                    rw [hTm] at hEv; cases hEv
                  | return_ =>
                    rw [hTm] at hEv; dsimp at hEv
                    cases hCl : bb.cleanup with
                    | true => rw [hCl] at hEv; cases hEv
                    | false =>
                      rw [hCl] at hEv; dsimp at hEv
                      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
                      | none => rw [h0] at hEv; cases hEv
                      | some sl =>
                        rw [h0] at hEv
                        cases sl with
                        | dead => cases hEv
                        | liveBase ov => cases ov <;> cases hEv
                        | liveTuple fields =>
                          cases hB0 : Trusted.MirSemantics.getElem? body.locals 0 with
                          | none => rw [hB0] at hEv; cases hEv
                          | some t0 =>
                            rw [hB0] at hEv
                            cases t0 with
                            | tuple fTys =>
                              dsimp at hEv
                              cases hC : (isFlatTupleTy (.tuple fTys) && Nat.beq fields.length fTys.length) with
                              | false => rw [hC] at hEv; cases hEv
                              | true =>
                                rw [hC] at hEv; dsimp at hEv
                                cases hE : extractAllInitFields fields <;> (rw [hE] at hEv; cases hEv)
                            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
                              cases hEv
                  | switchInt discr targets =>
                    rw [hTm] at hEv; dsimp at hEv
                    cases hOp : evalPrimitiveOperandExt body.locals frame.locals discr with
                    | error _ => rw [hOp] at hEv; cases hEv
                    | ok pr =>
                      rw [hOp] at hEv
                      cases pr with
                      | mk dv ls1 =>
                        dsimp at hEv
                        cases dv with
                        | scalar sv =>
                          dsimp at hEv
                          cases hBr : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                          | error _ => rw [hBr] at hEv; cases hEv
                          | ok _ =>
                            rw [hBr] at hEv; dsimp [jumpToBlockExt] at hEv
                            injection hEv with hEq; subst hEq
                            dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                        | bool b =>
                          dsimp at hEv
                          cases hBr : evalBoolSwitchBranches b targets.otherwise targets.branches with
                          | error _ => rw [hBr] at hEv; cases hEv
                          | ok _ =>
                            rw [hBr] at hEv; dsimp [jumpToBlockExt] at hEv
                            injection hEv with hEq; subst hEq
                            dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
                  | assert cond expected msg target unwind =>
                    rw [hTm] at hEv; dsimp at hEv
                    cases hOp : evalPrimitiveOperandExt body.locals frame.locals cond with
                    | error _ => rw [hOp] at hEv; cases hEv
                    | ok pr =>
                      rw [hOp] at hEv
                      cases pr with
                      | mk cv ls1 =>
                        dsimp at hEv
                        cases cv with
                        | bool b =>
                          dsimp at hEv
                          cases hBeq : (b == expected) with
                          | true =>
                            rw [hBeq] at hEv; dsimp [jumpToBlockExt] at hEv
                            injection hEv with hEq; subst hEq
                            dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
                          | false =>
                            rw [hBeq] at hEv; dsimp at hEv
                            cases hK : (!isSupportedAssertKind msg) with
                            | true => rw [hK] at hEv; cases hEv
                            | false =>
                              rw [hK] at hEv; dsimp at hEv
                              cases unwind <;> cases hEv
                        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
                rw [hKeepDef]; exact hFNe
  apply query_equiv_of_multistep_sim (R := R)
  · intro k hErr; rw [hInitEq, hErr]
  · intro s₀ hOk
    refine ⟨s₀, by rw [hInitEq, hOk], rfl, ?_⟩
    intro f hF
    unfold initStateTupleAssert at hOk
    cases h1 : (!Nat.beq ctx.pSrc.pointerWidthBits 64 || !Nat.beq ctx.pSrc.mirProfileVersion 1) with
    | true => rw [h1] at hOk; cases hOk
    | false =>
      rw [h1] at hOk; dsimp at hOk
      cases h2 : (!q.callerMem.allocations.isEmpty) with
      | true => rw [h2] at hOk; cases hOk
      | false =>
        rw [h2] at hOk; dsimp at hOk
        cases h3 : Trusted.MirSemantics.getElem? ctx.pSrc.bodies ctx.pSrc.entryDefId with
        | none => rw [h3] at hOk; cases hOk
        | some b =>
          rw [h3] at hOk; dsimp at hOk
          cases h4 : b.basicBlocks.isEmpty with
          | true => rw [h4] at hOk; cases hOk
          | false =>
            rw [h4] at hOk; dsimp at hOk
            cases h5 : (!Nat.blt b.argumentCount b.locals.length) with
            | true => rw [h5] at hOk; cases hOk
            | false =>
              rw [h5] at hOk; dsimp at hOk
              cases h6 : (!storageAnnotationsInBounds b) with
              | true => rw [h6] at hOk; cases hOk
              | false =>
                rw [h6] at hOk; dsimp at hOk
                cases h7 : (!b.locals.all isSupportedTupleOrScalarTy) with
                | true => rw [h7] at hOk; cases hOk
                | false =>
                  rw [h7] at hOk; dsimp at hOk
                  cases h8 : (!checkArgsMatchExt q.args ((b.locals.drop 1).take b.argumentCount)) with
                  | true => rw [h8] at hOk; cases hOk
                  | false =>
                    rw [h8] at hOk; dsimp at hOk
                    injection hOk with hSEq; subst hSEq
                    dsimp at hF; injection hF with hFEq; subst hFEq
                    exact hNe
  · intro s1 s2 s1' ⟨hEq, hDef⟩ hStep
    subst hEq
    let ⟨hStepEq, hPres⟩ := hStepPres s1 0 hDef
    exact ⟨1, s1', Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStepEq, hStep],
      rfl, hPres s1' hStep⟩
  · intro s1 s2 out ⟨hEq, hDef⟩ hDone
    subst hEq
    let ⟨hStepEq, _⟩ := hStepPres s1 0 hDef
    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStepEq, hDone]⟩
  · intro s1 s2 fk ⟨hEq, hDef⟩ hFault
    subst hEq
    let ⟨hStepEq, _⟩ := hStepPres s1 0 hDef
    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStepEq, hFault]⟩

private theorem sroa_query_equiv (ctx : SroaCtx) (q : Query) :
    (WellFormedTupleAssert ctx.pTgt q ↔ WellFormedTupleAssert ctx.pSrc q) ∧
    (NoPanicAndWellFormedTupleAssert ctx.pTgt q ↔
      NoPanicAndWellFormedTupleAssert ctx.pSrc q) ∧
    (∀ out : TerminalOutExt,
      BehaviorTupleAssert ctx.pTgt q out ↔ BehaviorTupleAssert ctx.pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResultTupleAssert ctx.pTgt q (.fault k) ↔
        ReachesResultTupleAssert ctx.pSrc q (.fault k)) ∧
    (DivergesTupleAssert ctx.pTgt q ↔ DivergesTupleAssert ctx.pSrc q) := by
  cases hEnt : Nat.beq ctx.pSrc.entryDefId ctx.plan.defId with
  | false =>
    exact sroa_query_equiv_other_entry ctx q (nat_ne_of_beq_false hEnt)
  | true =>
    let ⟨hInitErr, hInitOk⟩ := sroa_init_sim ctx q (nat_beq_eq hEnt)
    apply query_equiv_of_multistep_sim (R := SroaRelState ctx) hInitErr hInitOk
    · intro sSrc sTgt sSrc' hR hEv
      have hSim := sroa_step_sim_all ctx hR
      rw [hEv] at hSim; exact hSim
    · intro sSrc sTgt out hR hEv
      have hSim := sroa_step_sim_all ctx hR
      rw [hEv] at hSim; exact hSim
    · intro sSrc sTgt fk hR hEv
      have hSim := sroa_step_sim_all ctx hR
      rw [hEv] at hSim; exact hSim

private theorem applyMirSroaTuple_entryProgForBody {plan : SroaTuplePlan}
    {pSrc pTgt : Program} (defId : DefId)
    (h : applyMirSroaTuple plan pSrc = some pTgt) :
    applyMirSroaTuple plan (entryProgForBody pSrc defId) =
      some (entryProgForBody pTgt defId) := by
  let ⟨ctx, hP, hS, hT⟩ := extractSroaCtx h
  subst hP; subst hS; subst hT
  have h1 := h
  unfold entryProgForBody
  unfold applyMirSroaTuple at h1; unfold applyMirSroaTuple
  dsimp at h1; dsimp
  cases hGet : Trusted.MirSemantics.getElem? ctx.pSrc.bodies ctx.plan.defId with
  | none => rw [hGet] at h1; cases h1
  | some b =>
    rw [hGet] at h1; dsimp at h1; dsimp
    cases hG1 : (b.basicBlocks.isEmpty ||
        !Nat.blt b.argumentCount ctx.plan.tupLocal ||
        !Nat.blt ctx.plan.tupLocal b.locals.length ||
        !bodyAllLocalsInBounds b) with
    | true => rw [hG1] at h1; cases h1
    | false =>
      rw [hG1] at h1; dsimp at h1; dsimp
      cases hTy : Trusted.MirSemantics.getElem? b.locals ctx.plan.tupLocal with
      | none => rw [hTy] at h1; cases h1
      | some t =>
        rw [hTy] at h1
        cases t with
        | tuple fTys =>
          dsimp at h1; dsimp
          cases hG2 : (!isFlatTupleTy (.tuple fTys) || !bodyTupleUsesValid b ctx.plan.tupLocal fTys) with
          | true => rw [hG2] at h1; cases h1
          | false =>
            rw [hG2] at h1; dsimp at h1; dsimp
            cases hSL : setElem? b.locals ctx.plan.tupLocal .unit with
            | none => rw [hSL] at h1; cases h1
            | some lu =>
              rw [hSL] at h1; dsimp at h1; dsimp
              cases hSB : setElem? ctx.pSrc.bodies ctx.plan.defId _ with
              | none => rw [hSB] at h1; cases h1
              | some bs =>
                rw [hSB] at h1
                injection h1 with hEq
                rw [← hEq]
        | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
          cases h1

private theorem mirSroaTuple_sound_bidirectional_iff_sliceB
    (plan : SroaTuplePlan) (pSrc pTgt : Program)
    (hPlan : checkMirSroaTuple plan pSrc pTgt = true) :
    FullSemanticEquivTupleAssert pSrc pTgt := by
  unfold checkMirSroaTuple at hPlan
  cases hApp : applyMirSroaTuple plan pSrc with
  | none => rw [hApp] at hPlan; cases hPlan
  | some pOut =>
    rw [hApp] at hPlan
    have hEq := programEq_eq hPlan
    subst hEq
    let ⟨ctx, hP, hS, hT⟩ := extractSroaCtx hApp
    subst hP; subst hS; subst hT
    have hQ := fun q => sroa_query_equiv ctx q
    refine ⟨hQ, ?_, ?_⟩
    · intro q post
      let ⟨_, hNP, hBeh, _, _⟩ := hQ q
      unfold SatisfiesPostNoPanicTupleAssert
      constructor
      · intro ⟨hN, hP'⟩
        exact ⟨hNP.mp hN, fun out hB => hP' out ((hBeh (.ret out)).mpr hB)⟩
      · intro ⟨hN, hP'⟩
        exact ⟨hNP.mpr hN, fun out hB => hP' out ((hBeh (.ret out)).mp hB)⟩
    · intro defId bSrc bTgt safetyPre hGetS hGetT
      have hEntryApp := applyMirSroaTuple_entryProgForBody defId hApp
      let ⟨ctxE, _, hES, hET⟩ := extractSroaCtx hEntryApp
      have hEntryQ : ∀ q, NoPanicAndWellFormedTupleAssert (entryProgForBody ctx.pTgt defId) q ↔
          NoPanicAndWellFormedTupleAssert (entryProgForBody ctx.pSrc defId) q := by
        intro q
        have hEqQ := (sroa_query_equiv ctxE q).2.1
        rw [hES, hET] at hEqQ
        exact hEqQ
      cases hDefEq : Nat.beq defId ctx.plan.defId with
      | false =>
        have hNe := nat_ne_of_beq_false hDefEq
        have hBodiesEq : Trusted.MirSemantics.getElem? ctx.pTgt.bodies defId =
            Trusted.MirSemantics.getElem? ctx.pSrc.bodies defId := by
          rw [ctx.hPTgt]; dsimp
          exact setElem?_getElem?_ne ctx.hSetBody hNe
        rw [hBodiesEq, hGetS] at hGetT
        injection hGetT with hBEq; subst hBEq
        have hAdmEq : BodyStaticAdmittedTupleAssert ctx.pTgt bSrc =
            BodyStaticAdmittedTupleAssert ctx.pSrc bSrc := by
          unfold BodyStaticAdmittedTupleAssert
          have hPw : ctx.pTgt.pointerWidthBits = ctx.pSrc.pointerWidthBits := by rw [ctx.hPTgt]
          have hVer : ctx.pTgt.mirProfileVersion = ctx.pSrc.mirProfileVersion := by rw [ctx.hPTgt]
          rw [hPw, hVer]
        unfold BodyVerifiedNoPanicTupleAssert
        rw [hAdmEq]
        constructor
        · intro ⟨_, hAdm, hAll⟩
          exact ⟨hGetS, hAdm, fun args hV hU => (hEntryQ { args := args }).mp (hAll args hV hU)⟩
        · intro ⟨_, hAdm, hAll⟩
          exact ⟨by rw [hBodiesEq]; exact hGetS, hAdm,
            fun args hV hU => (hEntryQ { args := args }).mpr (hAll args hV hU)⟩
      | true =>
        have hDef := nat_beq_eq hDefEq; subst hDef
        rw [ctx.hGetSrc] at hGetS; injection hGetS with hBS; subst hBS
        rw [sroaCtx_getElem?_bodyTgt ctx] at hGetT; injection hGetT with hBT; subst hBT
        have hUnsEq : ctx.bodyTgt.isUnsafe = ctx.bodySrc.isUnsafe := by rw [ctx.hBodyTgt]
        have hValidIff : ∀ args, ValidEntryArgsTupleAssert ctx.bodyTgt args ↔
            ValidEntryArgsTupleAssert ctx.bodySrc args := by
          intro args
          unfold ValidEntryArgsTupleAssert
          rw [sroaCtx_paramTys_eq ctx]
        unfold BodyVerifiedNoPanicTupleAssert
        rw [sroaCtx_bodyStaticAdmitted_eq ctx, hUnsEq]
        constructor
        · intro ⟨_, hAdm, hAll⟩
          exact ⟨ctx.hGetSrc, hAdm, fun args hV hU =>
            (hEntryQ { args := args }).mp (hAll args ((hValidIff args).mpr hV) hU)⟩
        · intro ⟨_, hAdm, hAll⟩
          exact ⟨sroaCtx_getElem?_bodyTgt ctx, hAdm, fun args hV hU =>
            (hEntryQ { args := args }).mpr (hAll args ((hValidIff args).mp hV) hU)⟩


/-! ### Private Helpers from `F1_11_SliceC.lean` -/
/-! ### Stage 4 Helpers — Slice C: Theorems 3 (`AssertConstFold`), 4 (`SroaTrace + AssertLower`), & 5 (`OptPipeline`) -/

/-! #### Section 1: Equivalence & `ProgramMetadataCompat` Combinators -/

private theorem fullSemanticEquivTupleAssert_refl (p : Program) :
    FullSemanticEquivTupleAssert p p := by
  refine ⟨fun _ => ⟨Iff.rfl, Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, Iff.rfl⟩,
          fun _ _ => Iff.rfl, ?_⟩
  intro _ b₁ b₂ _ h1 h2
  rw [h1] at h2; injection h2 with hEq; subst hEq
  exact Iff.rfl

private theorem fullSemanticEquivTupleAssert_trans {p₁ p₂ p₃ : Program}
    (h12 : FullSemanticEquivTupleAssert p₁ p₂)
    (h23 : FullSemanticEquivTupleAssert p₂ p₃)
    (hLen12 : p₁.bodies.length = p₂.bodies.length) :
    FullSemanticEquivTupleAssert p₁ p₃ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let ⟨w12, np12, b12, f12, d12⟩ := h12.1 q
    let ⟨w23, np23, b23, f23, d23⟩ := h23.1 q
    exact ⟨Iff.trans w23 w12, Iff.trans np23 np12,
           fun out => Iff.trans (b23 out) (b12 out),
           fun k => Iff.trans (f23 k) (f12 k),
           Iff.trans d23 d12⟩
  · intro q post
    exact Iff.trans (h23.2.1 q post) (h12.2.1 q post)
  · intro defId b₁ b₃ safetyPre hb1 hb3
    have hLt1 : defId < p₁.bodies.length := getElem?_some_lt hb1
    have hLt2 : defId < p₂.bodies.length := by rw [← hLen12]; exact hLt1
    let ⟨b₂, hb2⟩ := getElem?_some_of_lt p₂.bodies defId hLt2
    exact Iff.trans (h23.2.2 defId b₂ b₃ safetyPre hb2 hb3)
      (h12.2.2 defId b₁ b₂ safetyPre hb1 hb2)

private theorem noPanicEquiv_of_fullSemanticEquivTupleAssert {p₁ p₂ : Program}
    (h : FullSemanticEquivTupleAssert p₁ p₂) :
    NoPanicSemanticEquivTupleAssert p₁ p₂ := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro q
  let ⟨_, hNP, hBeh, _, hDiv⟩ := h.1 q
  exact ⟨hNP, fun out => hBeh (.ret out), hDiv⟩

private theorem noPanicSemanticEquivTupleAssert_trans {p₁ p₂ p₃ : Program}
    (h12 : NoPanicSemanticEquivTupleAssert p₁ p₂)
    (h23 : NoPanicSemanticEquivTupleAssert p₂ p₃)
    (hLen12 : p₁.bodies.length = p₂.bodies.length) :
    NoPanicSemanticEquivTupleAssert p₁ p₃ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let ⟨np12, b12, d12⟩ := h12.1 q
    let ⟨np23, b23, d23⟩ := h23.1 q
    exact ⟨Iff.trans np23 np12,
           fun out => Iff.trans (b23 out) (b12 out),
           Iff.trans d23 d12⟩
  · intro q post
    exact Iff.trans (h23.2.1 q post) (h12.2.1 q post)
  · intro defId b₁ b₃ safetyPre hb1 hb3
    have hLt1 : defId < p₁.bodies.length := getElem?_some_lt hb1
    have hLt2 : defId < p₂.bodies.length := by rw [← hLen12]; exact hLt1
    let ⟨b₂, hb2⟩ := getElem?_some_of_lt p₂.bodies defId hLt2
    exact Iff.trans (h23.2.2 defId b₂ b₃ safetyPre hb2 hb3)
      (h12.2.2 defId b₁ b₂ safetyPre hb1 hb2)

private theorem listRel_id_refl (bs : List Body) :
    listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) bs bs = true := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    dsimp [listRel]
    rw [stringBeq_refl b.identity, Bool.true_and]
    exact ih

private theorem listRel_id_trans {bs₁ bs₂ bs₃ : List Body}
    (h12 : listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) bs₁ bs₂ = true)
    (h23 : listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) bs₂ bs₃ = true) :
    listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) bs₁ bs₃ = true := by
  induction bs₁ generalizing bs₂ bs₃ with
  | nil =>
    cases bs₂ with
    | cons _ _ => cases h12
    | nil =>
      cases bs₃ with
      | cons _ _ => cases h23
      | nil => rfl
  | cons b1 r1 ih =>
    cases bs₂ with
    | nil => cases h12
    | cons b2 r2 =>
      cases bs₃ with
      | nil => cases h23
      | cons b3 r3 =>
        let ⟨hb12, hr12⟩ := bool_and_true h12
        let ⟨hb23, hr23⟩ := bool_and_true h23
        dsimp [listRel]
        have hIdEq : b1.identity = b3.identity :=
          Eq.trans (stringBeq_eq hb12) (stringBeq_eq hb23)
        rw [hIdEq, stringBeq_refl, Bool.true_and]
        exact ih hr12 hr23

private theorem programHeaderEq_of_eq {p₁ p₂ : Program}
    (hPw : p₁.pointerWidthBits = p₂.pointerWidthBits)
    (hVer : p₁.mirProfileVersion = p₂.mirProfileVersion)
    (hEnt : p₁.entryDefId = p₂.entryDefId)
    (hSc : p₁.scope = p₂.scope) :
    programHeaderEq p₁ p₂ = true := by
  unfold programHeaderEq
  rw [hPw, hVer, hEnt, hSc,
      nat_beq_refl, nat_beq_refl, nat_beq_refl, scopeEq_refl]
  rfl

private theorem programMetadataCompat_refl (p : Program) :
    ProgramMetadataCompat p p = true := by
  unfold ProgramMetadataCompat
  rw [programHeaderEq_refl p, listRel_id_refl p.bodies]
  rfl

private theorem programMetadataCompat_trans {p₁ p₂ p₃ : Program}
    (h12 : ProgramMetadataCompat p₁ p₂ = true)
    (h23 : ProgramMetadataCompat p₂ p₃ = true) :
    ProgramMetadataCompat p₁ p₃ = true := by
  unfold ProgramMetadataCompat at h12 h23; unfold ProgramMetadataCompat
  let ⟨hh12, hb12⟩ := bool_and_true h12
  let ⟨hh23, hb23⟩ := bool_and_true h23
  let ⟨pw12, v12, e12, s12⟩ := programHeaderEq_elim hh12
  let ⟨pw23, v23, e23, s23⟩ := programHeaderEq_elim hh23
  exact bool_and_intro
    (programHeaderEq_of_eq (Eq.trans pw12 pw23) (Eq.trans v12 v23)
      (Eq.trans e12 e23) (Eq.trans s12 s23))
    (listRel_id_trans hb12 hb23)

private theorem programMetadataCompat_bodies_len {p₁ p₂ : Program}
    (hMeta : ProgramMetadataCompat p₁ p₂ = true) :
    p₁.bodies.length = p₂.bodies.length := by
  unfold ProgramMetadataCompat at hMeta
  exact listRel_length (bool_and_true hMeta).2

private theorem programMetadataCompat_unitProgForDef {p₁ p₂ : Program} (u : DefId)
    (hMeta : ProgramMetadataCompat p₁ p₂ = true) :
    ProgramMetadataCompat (unitProgForDef p₁ u) (unitProgForDef p₂ u) = true := by
  unfold ProgramMetadataCompat at hMeta; unfold ProgramMetadataCompat
  let ⟨hh, hb⟩ := bool_and_true hMeta
  let ⟨pw, v, _, _⟩ := programHeaderEq_elim hh
  exact bool_and_intro (programHeaderEq_of_eq pw v rfl rfl) hb

private theorem bodiesHaveUniqueIdentities_eq_of_rel {bs₁ bs₂ : List Body}
    (hRel : listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) bs₁ bs₂ = true) :
    bodiesHaveUniqueIdentities bs₁ = bodiesHaveUniqueIdentities bs₂ := by
  unfold bodiesHaveUniqueIdentities
  have hAllEq : (bs₁.all fun b => !stringBeq b.identity "") =
      (bs₂.all fun b => !stringBeq b.identity "") := by
    induction bs₁ generalizing bs₂ with
    | nil =>
      cases bs₂ with
      | nil => rfl
      | cons _ _ => cases hRel
    | cons b1 r1 ih =>
      cases bs₂ with
      | nil => cases hRel
      | cons b2 r2 =>
        let ⟨hb, hr⟩ := bool_and_true hRel
        dsimp [List.all]
        rw [stringBeq_eq hb, ih hr]
  have hMapEq : bs₁.map (fun b => b.identity) = bs₂.map (fun b => b.identity) :=
    list_map_eq_of_rel hRel (fun _ _ h => stringBeq_eq h)
  rw [hAllEq, hMapEq]

private theorem programVerifiedNoPanicTupleAssert_iff {p₁ p₂ : Program} {specs : Specs}
    (hMeta : ProgramMetadataCompat p₁ p₂ = true)
    (hEqv : NoPanicSemanticEquivTupleAssert p₁ p₂)
    (hSpec : SpecsPropertyNoPanicInvariant specs) :
    ProgramVerifiedNoPanicTupleAssert p₁ specs ↔
      ProgramVerifiedNoPanicTupleAssert p₂ specs := by
  unfold ProgramMetadataCompat at hMeta
  let ⟨hHdr, hBodiesRel⟩ := bool_and_true hMeta
  let ⟨hPw, hVer, hEnt, _⟩ := programHeaderEq_elim hHdr
  have hLen : p₁.bodies.length = p₂.bodies.length := listRel_length hBodiesRel
  have hEmp : p₁.bodies.isEmpty = p₂.bodies.isEmpty := list_isEmpty_eq_of_length hLen
  have hUniq : bodiesHaveUniqueIdentities p₁.bodies = bodiesHaveUniqueIdentities p₂.bodies :=
    bodiesHaveUniqueIdentities_eq_of_rel hBodiesRel
  have hProp : specs.property p₁ ↔ specs.property p₂ := hSpec p₁ p₂ hEqv
  unfold ProgramVerifiedNoPanicTupleAssert
  rw [hPw, hVer, hEmp, hEnt, hLen, hUniq]
  constructor
  · intro ⟨c1, c2, c3, c4, c5, hBodies1, hP1⟩
    refine ⟨c1, c2, c3, c4, c5, ?_, hProp.mp hP1⟩
    intro defId b₂ hb2
    let ⟨b₁, hb1, hIdB⟩ := listRel_getElem?_right hBodiesRel hb2
    have hIdEq : b₁.identity = b₂.identity := stringBeq_eq hIdB
    have hBv1 := hBodies1 defId b₁ hb1
    rw [hIdEq] at hBv1
    exact (hEqv.2.2 defId b₁ b₂ (specs.safety b₂.identity) hb1 hb2).mpr hBv1
  · intro ⟨c1, c2, c3, c4, c5, hBodies2, hP2⟩
    refine ⟨c1, c2, c3, c4, c5, ?_, hProp.mpr hP2⟩
    intro defId b₁ hb1
    let ⟨b₂, hb2, hIdB⟩ := listRel_getElem?_left hBodiesRel hb1
    have hIdEq : b₁.identity = b₂.identity := stringBeq_eq hIdB
    have hBv2 := hBodies2 defId b₂ hb2
    rw [← hIdEq] at hBv2
    exact (hEqv.2.2 defId b₁ b₂ (specs.safety b₁.identity) hb1 hb2).mp hBv2

private theorem crateAndUnitTheoremNoPanicTupleAssert_iff {p₁ p₂ : Program} {specs : Specs}
    (hMeta : ProgramMetadataCompat p₁ p₂ = true)
    (hEqv : NoPanicSemanticEquivTupleAssert p₁ p₂)
    (hSpec : SpecsPropertyNoPanicInvariant specs) :
    (CrateTheoremNoPanicTupleAssert ⟨p₁, specs⟩ ↔
      CrateTheoremNoPanicTupleAssert ⟨p₂, specs⟩) ∧
    (UnitTheoremNoPanicTupleAssert ⟨p₁, specs⟩ ↔
      UnitTheoremNoPanicTupleAssert ⟨p₂, specs⟩) := by
  have hSc : p₁.scope = p₂.scope := by
    unfold ProgramMetadataCompat at hMeta
    exact (programHeaderEq_elim (bool_and_true hMeta).1).2.2.2
  have hPv := programVerifiedNoPanicTupleAssert_iff hMeta hEqv hSpec
  unfold CrateTheoremNoPanicTupleAssert UnitTheoremNoPanicTupleAssert
  dsimp
  rw [hSc]
  exact ⟨⟨fun ⟨hs, hp⟩ => ⟨hs, hPv.mp hp⟩, fun ⟨hs, hp⟩ => ⟨hs, hPv.mpr hp⟩⟩,
         ⟨fun ⟨hs, hp⟩ => ⟨hs, hPv.mp hp⟩, fun ⟨hs, hp⟩ => ⟨hs, hPv.mpr hp⟩⟩⟩

/-! #### Section 2: Theorem 3 (`AssertConstFold` Bidirectional Soundness) -/

private theorem evalStatementExt_congr_locals {b₁ b₂ : Body}
    (hLoc : b₁.locals = b₂.locals)
    (frame : FrameStateExt) (mem : CallerMemory) (stmt : StatementKind) :
    evalStatementExt b₁ frame mem stmt = evalStatementExt b₂ frame mem stmt := by
  unfold evalStatementExt
  rw [hLoc]

private theorem evalTerminatorExt_congr_locals {b₁ b₂ : Body}
    (hLoc : b₁.locals = b₂.locals)
    (bb : BasicBlock) (frame : FrameStateExt) (mem : CallerMemory) :
    evalTerminatorExt b₁ bb frame mem = evalTerminatorExt b₂ bb frame mem := by
  unfold evalTerminatorExt
  rw [hLoc]

private theorem evalConstLit_canonical_bool (expected : Bool) :
    evalConstLit .bool (.scalar (BitVec.ofNat 128 (if expected then 1 else 0))) =
      .ok (.bool expected) := by
  cases expected <;> rfl

private theorem frame_with_same_locals (frame : FrameStateExt) :
    { frame with locals := frame.locals } = frame := by
  cases frame; rfl

private theorem constTrueAssertTarget_eval_eq (body : Body) (bbSrc bbTgt : BasicBlock)
    (frame : FrameStateExt) (mem : CallerMemory) (target : BasicBlockId)
    (hConst : constTrueAssertTarget? bbSrc.terminator = some target)
    (hTgt : bbTgt.terminator = .goto target) :
    evalTerminatorExt body bbTgt frame mem = evalTerminatorExt body bbSrc frame mem := by
  cases hTerm : bbSrc.terminator with
  | goto _ | switchInt _ _ | return_ | unreachable | unwindResume
  | call _ _ _ _ _ | unsupported =>
    rw [hTerm] at hConst; cases hConst
  | assert cond expected msg tgtSrc unwind =>
    rw [hTerm] at hConst
    cases cond with
    | copy _ | move _ => cases hConst
    | constant c =>
      cases c with
      | mk cTy cLit =>
        dsimp [constTrueAssertTarget?] at hConst
        cases cTy with
        | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
          cases hConst
        | bool =>
          cases cLit with
          | zeroSized => cases hConst
          | scalar bits =>
            dsimp at hConst
            cases hBits : (bits == BitVec.ofNat 128 (if expected then 1 else 0)) with
            | false => rw [hBits] at hConst; cases hConst
            | true =>
              rw [hBits] at hConst; dsimp at hConst
              injection hConst with hTgtEq; subst hTgtEq
              have hBitsEq := bitvec_beq_eq hBits
              subst hBitsEq
              unfold evalTerminatorExt
              rw [hTgt, hTerm]
              dsimp [evalPrimitiveOperandExt, evalOperandToSlotExt]
              rw [evalConstLit_canonical_bool expected]
              dsimp [isPrimitiveReadableTy_bool]
              rw [bool_beq_refl expected]; dsimp

private theorem assertConstFoldBlock_props {bbSrc bbTgt : BasicBlock}
    (h : checkMirAssertConstFoldBlock bbSrc bbTgt = true) :
    bbSrc.cleanup = bbTgt.cleanup ∧
    bbSrc.statements = bbTgt.statements ∧
    (bbSrc.terminator = bbTgt.terminator ∨
      ∃ target, constTrueAssertTarget? bbSrc.terminator = some target ∧
        bbTgt.terminator = .goto target) := by
  unfold checkMirAssertConstFoldBlock at h
  let ⟨h12, hTermOr⟩ := bool_and_true h
  let ⟨hCl, hStmts⟩ := bool_and_true h12
  refine ⟨bool_beq_eq hCl, listRel_eq (fun _ _ => stmtEq_eq) hStmts, ?_⟩
  cases bool_or_true hTermOr with
  | inl hEq => exact Or.inl (terminatorEq_eq hEq)
  | inr hFold =>
    cases hC : constTrueAssertTarget? bbSrc.terminator with
    | none => rw [hC] at hFold; cases hFold
    | some tSrc =>
      rw [hC] at hFold
      cases hT : bbTgt.terminator with
      | goto tTgt =>
        rw [hT] at hFold; dsimp at hFold
        have hTEq := nat_beq_eq hFold; subst hTEq
        exact Or.inr ⟨tSrc, rfl, rfl⟩
      | switchInt _ _ | return_ | unreachable | assert _ _ _ _ _
      | unwindResume | call _ _ _ _ _ | unsupported =>
        rw [hT] at hFold; cases hFold

private theorem assertConstFoldBody_hasStorageAnnotation {bSrc bTgt : Body}
    (h : checkMirAssertConstFoldBody bSrc bTgt = true) (id : LocalId) :
    hasStorageAnnotation bTgt id = hasStorageAnnotation bSrc id := by
  unfold checkMirAssertConstFoldBody at h
  let ⟨_, hBbs⟩ := bool_and_true h
  unfold hasStorageAnnotation
  apply list_any_eq_of_getElem? (listRel_length hBbs).symm
  intro i bbT bbS hT hS
  let ⟨bbT', hT', hBlk⟩ := listRel_getElem?_left hBbs hS
  rw [hT] at hT'; injection hT' with hEq; subst hEq
  let ⟨_, hStEq, _⟩ := assertConstFoldBlock_props hBlk
  rw [hStEq]

private theorem list_all_eq_of_rel {α β : Type} {r : α → β → Bool}
    {p : α → Bool} {q : β → Bool} {xs : List α} {ys : List β}
    (hRel : listRel r xs ys = true)
    (hPQ : ∀ a b, r a b = true → q b = p a) :
    ys.all q = xs.all p := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons a _ ih =>
    cases ys with
    | nil => cases hRel
    | cons b _ =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      dsimp [List.all]
      rw [hPQ a b hab, ih hTail]

private theorem assertConstFoldBody_storageAnnotationsInBounds {bSrc bTgt : Body}
    (h : checkMirAssertConstFoldBody bSrc bTgt = true) :
    storageAnnotationsInBounds bTgt = storageAnnotationsInBounds bSrc := by
  unfold checkMirAssertConstFoldBody at h
  let ⟨hHdr, hBbs⟩ := bool_and_true h
  let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hHdr
  unfold storageAnnotationsInBounds
  dsimp
  rw [← hLocEq]
  exact list_all_eq_of_rel hBbs (fun _ _ hBlk => by
    let ⟨_, hStEq, _⟩ := assertConstFoldBlock_props hBlk
    rw [hStEq])

private theorem assertConstFoldBody_initLocalsExtLoop_eq {bSrc bTgt : Body}
    (h : checkMirAssertConstFoldBody bSrc bTgt = true)
    (args : List Val) (idx : Nat) (rem : List MirTy) :
    initLocalsExtLoop bTgt args idx rem = initLocalsExtLoop bSrc args idx rem := by
  unfold checkMirAssertConstFoldBody at h
  let ⟨hHdr, _⟩ := bool_and_true h
  let ⟨hArgEq, _, _, _⟩ := bodyHeaderEq_elim hHdr
  induction rem generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    dsimp [initLocalsExtLoop]
    rw [← hArgEq, assertConstFoldBody_hasStorageAnnotation h idx, ih (idx + 1)]

private theorem assertConstFold_initState_eq {pSrc pTgt : Program}
    (hFold : checkMirAssertConstFold pSrc pTgt = true) (q : Query) :
    initStateTupleAssert pTgt q = initStateTupleAssert pSrc q := by
  unfold checkMirAssertConstFold at hFold
  let ⟨hHdr, hBodies⟩ := bool_and_true hFold
  let ⟨hPw, hVer, hEnt, _⟩ := programHeaderEq_elim hHdr
  unfold initStateTupleAssert
  rw [← hPw, ← hVer, ← hEnt]
  cases hGetS : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId with
  | none =>
    have hGe : pSrc.bodies.length ≤ pSrc.entryDefId := getElem?_none_ge hGetS
    have hGeT : pTgt.bodies.length ≤ pSrc.entryDefId := by
      rw [← listRel_length hBodies]; exact hGe
    rw [getElem?_none_of_ge hGeT]
  | some bSrc =>
    let ⟨bTgt, hGetT, hBodyFold⟩ := listRel_getElem?_left hBodies hGetS
    rw [hGetT]; dsimp
    let ⟨hBHdr, hBbs⟩ := bool_and_true hBodyFold
    let ⟨hArgEq, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    have hEmpEq : bTgt.basicBlocks.isEmpty = bSrc.basicBlocks.isEmpty :=
      list_isEmpty_eq_of_length (listRel_length hBbs).symm
    rw [hEmpEq, ← hArgEq, ← hLocEq,
        assertConstFoldBody_storageAnnotationsInBounds hBodyFold,
        assertConstFoldBody_initLocalsExtLoop_eq hBodyFold]

private theorem assertConstFold_evalStep_eq {pSrc pTgt : Program}
    (hFold : checkMirAssertConstFold pSrc pTgt = true)
    (c : Choice) (s : StateExt) :
    evalStepTupleAssert pTgt c s = evalStepTupleAssert pSrc c s := by
  unfold checkMirAssertConstFold at hFold
  let ⟨_, hBodies⟩ := bool_and_true hFold
  unfold evalStepTupleAssert
  cases s.frames with
  | nil => rfl
  | cons frame rest =>
    cases rest with
    | cons _ _ => rfl
    | nil =>
      dsimp
      cases hGetS : Trusted.MirSemantics.getElem? pSrc.bodies frame.defId with
      | none =>
        have hGeT : pTgt.bodies.length ≤ frame.defId := by
          rw [← listRel_length hBodies]; exact getElem?_none_ge hGetS
        rw [getElem?_none_of_ge hGeT]
      | some bSrc =>
        let ⟨bTgt, hGetT, hBodyFold⟩ := listRel_getElem?_left hBodies hGetS
        rw [hGetT]; dsimp
        let ⟨hBHdr, hBbs⟩ := bool_and_true hBodyFold
        let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
        cases hBbS : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
        | none =>
          have hGeBb : bTgt.basicBlocks.length ≤ frame.blockIdx := by
            rw [← listRel_length hBbs]; exact getElem?_none_ge hBbS
          rw [getElem?_none_of_ge hGeBb]
        | some bbSrc =>
          let ⟨bbTgt, hBbT, hBlkFold⟩ := listRel_getElem?_left hBbs hBbS
          rw [hBbT]; dsimp
          let ⟨hClEq, hStEq, hTermCase⟩ := assertConstFoldBlock_props hBlkFold
          rw [← hStEq]
          cases Trusted.MirSemantics.getElem? bbSrc.statements frame.stmtIdx with
          | some stmt =>
            dsimp
            exact evalStatementExt_congr_locals hLocEq.symm frame s.callerMem stmt
          | none =>
            dsimp
            cases Nat.beq frame.stmtIdx bbSrc.statements.length with
            | false => rfl
            | true =>
              dsimp
              rw [evalTerminatorExt_congr_locals hLocEq.symm bbTgt frame s.callerMem]
              cases hTermCase with
              | inl hTermEq =>
                have hBbEq : bbTgt = bbSrc := by
                  cases bbSrc; cases bbTgt
                  dsimp at hClEq hStEq hTermEq
                  subst hClEq; subst hStEq; subst hTermEq; rfl
                rw [hBbEq]
              | inr hFoldT =>
                let ⟨target, hConst, hGoto⟩ := hFoldT
                exact constTrueAssertTarget_eval_eq bSrc bbSrc bbTgt frame s.callerMem target hConst hGoto

private theorem checkMirAssertConstFold_entryProgForBody {pSrc pTgt : Program} (defId : DefId)
    (hFold : checkMirAssertConstFold pSrc pTgt = true) :
    checkMirAssertConstFold (entryProgForBody pSrc defId) (entryProgForBody pTgt defId) = true := by
  unfold checkMirAssertConstFold at hFold; unfold checkMirAssertConstFold
  let ⟨hHdr, hBodies⟩ := bool_and_true hFold
  let ⟨hPw, hVer, _, hSc⟩ := programHeaderEq_elim hHdr
  exact bool_and_intro (programHeaderEq_of_eq hPw hVer rfl hSc) hBodies

private theorem checkMirAssertConstFold_metadataCompat {pSrc pTgt : Program}
    (hFold : checkMirAssertConstFold pSrc pTgt = true) :
    ProgramMetadataCompat pSrc pTgt = true := by
  unfold checkMirAssertConstFold at hFold
  let ⟨hHdr, hBodies⟩ := bool_and_true hFold
  unfold ProgramMetadataCompat
  refine bool_and_intro hHdr ?_
  have hRelHelper : ∀ (bs1 bs2 : List Body),
      listRel checkMirAssertConstFoldBody bs1 bs2 = true →
      listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) bs1 bs2 = true := by
    intro bs1
    induction bs1 with
    | nil =>
      intro bs2 hR
      cases bs2 with
      | nil => rfl
      | cons _ _ => cases hR
    | cons b1 r1 ih =>
      intro bs2 hR
      cases bs2 with
      | nil => cases hR
      | cons b2 r2 =>
        let ⟨hb, hr⟩ := bool_and_true hR
        let ⟨hBHdr, _⟩ := bool_and_true hb
        let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim hBHdr
        dsimp [listRel]
        rw [hIdEq, stringBeq_refl, Bool.true_and]
        exact ih r2 hr
  exact hRelHelper pSrc.bodies pTgt.bodies hBodies

private theorem query_equiv_of_exact_step_eq {pSrc pTgt : Program} (q : Query)
    (hInit : initStateTupleAssert pTgt q = initStateTupleAssert pSrc q)
    (hStep : ∀ s, evalStepTupleAssert pTgt 0 s = evalStepTupleAssert pSrc 0 s) :
    (WellFormedTupleAssert pTgt q ↔ WellFormedTupleAssert pSrc q) ∧
    (NoPanicAndWellFormedTupleAssert pTgt q ↔
      NoPanicAndWellFormedTupleAssert pSrc q) ∧
    (∀ out : TerminalOutExt,
      BehaviorTupleAssert pTgt q out ↔ BehaviorTupleAssert pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResultTupleAssert pTgt q (.fault k) ↔
        ReachesResultTupleAssert pSrc q (.fault k)) ∧
    (DivergesTupleAssert pTgt q ↔ DivergesTupleAssert pSrc q) := by
  apply query_equiv_of_multistep_sim (R := Eq)
  · intro k hErr; rw [hInit, hErr]
  · intro s₀ hOk; exact ⟨s₀, by rw [hInit, hOk], rfl⟩
  · intro s1 s2 s1' hEq hSt; subst hEq
    exact ⟨1, s1', Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStep, hSt], rfl⟩
  · intro s1 s2 out hEq hDn; subst hEq
    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStep, hDn]⟩
  · intro s1 s2 fk hEq hFl; subst hEq
    exact ⟨1, Nat.zero_lt_succ 0, by dsimp [evalTupleAssertFuel]; rw [hStep, hFl]⟩

private theorem mirAssertConstFold_sound_bidirectional_iff_sliceC
    (pSrc pTgt : Program)
    (hFold : checkMirAssertConstFold pSrc pTgt = true) :
    FullSemanticEquivTupleAssert pSrc pTgt := by
  have hQ : ∀ q,
      (WellFormedTupleAssert pTgt q ↔ WellFormedTupleAssert pSrc q) ∧
      (NoPanicAndWellFormedTupleAssert pTgt q ↔
        NoPanicAndWellFormedTupleAssert pSrc q) ∧
      (∀ out : TerminalOutExt,
        BehaviorTupleAssert pTgt q out ↔ BehaviorTupleAssert pSrc q out) ∧
      (∀ k : FaultKind,
        ReachesResultTupleAssert pTgt q (.fault k) ↔
          ReachesResultTupleAssert pSrc q (.fault k)) ∧
      (DivergesTupleAssert pTgt q ↔ DivergesTupleAssert pSrc q) := fun q =>
    query_equiv_of_exact_step_eq q
      (assertConstFold_initState_eq hFold q)
      (assertConstFold_evalStep_eq hFold 0)
  refine ⟨hQ, ?_, ?_⟩
  · intro q post
    let ⟨_, hNP, hBeh, _, _⟩ := hQ q
    unfold SatisfiesPostNoPanicTupleAssert
    exact ⟨fun ⟨hW, hB⟩ => ⟨hNP.mp hW, fun o ho => hB o ((hBeh (.ret o)).mpr ho)⟩,
           fun ⟨hW, hB⟩ => ⟨hNP.mpr hW, fun o ho => hB o ((hBeh (.ret o)).mp ho)⟩⟩
  · intro defId bSrc bTgt safetyPre hbS hbT
    have hEntFold := checkMirAssertConstFold_entryProgForBody defId hFold
    unfold checkMirAssertConstFold at hFold
    let ⟨hHdr, hBodies⟩ := bool_and_true hFold
    let ⟨hPw, hVer, _, _⟩ := programHeaderEq_elim hHdr
    let ⟨bTgt', hbT', hBodyFold⟩ := listRel_getElem?_left hBodies hbS
    rw [hbT] at hbT'; injection hbT' with hEq; subst hEq
    let ⟨hBHdr, hBbs⟩ := bool_and_true hBodyFold
    let ⟨hArgEq, hLocEq, hUnsEq, hIdEq⟩ := bodyHeaderEq_elim hBHdr
    have hEmpEq : bTgt.basicBlocks.isEmpty = bSrc.basicBlocks.isEmpty :=
      list_isEmpty_eq_of_length (listRel_length hBbs).symm
    have hStaticEq : BodyStaticAdmittedTupleAssert pTgt bTgt =
        BodyStaticAdmittedTupleAssert pSrc bSrc := by
      unfold BodyStaticAdmittedTupleAssert
      rw [← hPw, ← hVer, ← hIdEq, hEmpEq, ← hArgEq, ← hLocEq,
          assertConstFoldBody_storageAnnotationsInBounds hBodyFold]
    unfold BodyVerifiedNoPanicTupleAssert ValidEntryArgsTupleAssert
    rw [hStaticEq, ← hLocEq, ← hArgEq, ← hUnsEq]
    constructor
    · intro ⟨_, hAdm, hAll⟩
      refine ⟨hbS, hAdm, ?_⟩
      intro args hV hSafe
      have hEntQ := query_equiv_of_exact_step_eq { args := args }
        (assertConstFold_initState_eq hEntFold { args := args })
        (assertConstFold_evalStep_eq hEntFold 0)
      exact hEntQ.2.1.mp (hAll args hV hSafe)
    · intro ⟨_, hAdm, hAll⟩
      refine ⟨hbT, hAdm, ?_⟩
      intro args hV hSafe
      have hEntQ := query_equiv_of_exact_step_eq { args := args }
        (assertConstFold_initState_eq hEntFold { args := args })
        (assertConstFold_evalStep_eq hEntFold 0)
      exact hEntQ.2.1.mpr (hAll args hV hSafe)

/-! #### Section 3: Multi-Step `SroaTrace` Soundness & Commutation With `unitProgForDef` -/

private theorem mirSroaTuple_apply_sound {plan : SroaTuplePlan} {pSrc pTgt : Program}
    (hApp : applyMirSroaTuple plan pSrc = some pTgt) :
    FullSemanticEquivTupleAssert pSrc pTgt := by
  let ⟨ctx, hP, hS, hT⟩ := extractSroaCtx hApp
  subst hP; subst hS; subst hT
  have hQ := fun q => sroa_query_equiv ctx q
  refine ⟨hQ, ?_, ?_⟩
  · intro q post
    let ⟨_, hNP, hBeh, _, _⟩ := hQ q
    unfold SatisfiesPostNoPanicTupleAssert
    exact ⟨fun ⟨hW, hB⟩ => ⟨hNP.mp hW, fun o ho => hB o ((hBeh (.ret o)).mpr ho)⟩,
           fun ⟨hW, hB⟩ => ⟨hNP.mpr hW, fun o ho => hB o ((hBeh (.ret o)).mp ho)⟩⟩
  · intro defId bSrc bTgt safetyPre hbS hbT
    have hEntryApp := applyMirSroaTuple_entryProgForBody defId hApp
    let ⟨ctxE, _, hES, hET⟩ := extractSroaCtx hEntryApp
    have hQE := fun q => sroa_query_equiv ctxE q
    rw [hES, hET] at hQE
    cases hEqDef : Nat.beq defId ctx.plan.defId with
    | true =>
      have hDef := nat_beq_eq hEqDef; subst hDef
      rw [ctx.hGetSrc] at hbS; injection hbS with h1; subst h1
      rw [sroaCtx_getElem?_bodyTgt ctx] at hbT; injection hbT with h2; subst h2
      have hUns : ctx.bodyTgt.isUnsafe = ctx.bodySrc.isUnsafe := by rw [ctx.hBodyTgt]
      unfold BodyVerifiedNoPanicTupleAssert ValidEntryArgsTupleAssert
      rw [sroaCtx_bodyStaticAdmitted_eq ctx, sroaCtx_paramTys_eq ctx, hUns]
      exact ⟨fun ⟨_, hAdm, hAll⟩ => ⟨ctx.hGetSrc, hAdm, fun args hV hS => (hQE { args := args }).2.1.mp (hAll args hV hS)⟩,
             fun ⟨_, hAdm, hAll⟩ => ⟨sroaCtx_getElem?_bodyTgt ctx, hAdm, fun args hV hS => (hQE { args := args }).2.1.mpr (hAll args hV hS)⟩⟩
    | false =>
      have hNe := nat_ne_of_beq_false hEqDef
      have hSame : Trusted.MirSemantics.getElem? ctx.pTgt.bodies defId =
          Trusted.MirSemantics.getElem? ctx.pSrc.bodies defId := by
        rw [ctx.hPTgt]; dsimp
        exact setElem?_getElem?_ne ctx.hSetBody hNe
      rw [hSame, hbS] at hbT; injection hbT with hEqB; subst hEqB
      have hAdmEq : BodyStaticAdmittedTupleAssert ctx.pTgt bSrc =
          BodyStaticAdmittedTupleAssert ctx.pSrc bSrc := by
        unfold BodyStaticAdmittedTupleAssert
        rw [ctx.hPTgt]
      unfold BodyVerifiedNoPanicTupleAssert
      rw [hAdmEq]
      exact ⟨fun ⟨_, hAdm, hAll⟩ => ⟨hbS, hAdm, fun args hV hS => (hQE { args := args }).2.1.mp (hAll args hV hS)⟩,
             fun ⟨_, hAdm, hAll⟩ => ⟨by rw [hSame]; exact hbS, hAdm, fun args hV hS => (hQE { args := args }).2.1.mpr (hAll args hV hS)⟩⟩

private theorem listRel_id_setElem? {bs bs' : List Body} {idx : Nat} {bOld bNew : Body}
    (hGet : Trusted.MirSemantics.getElem? bs idx = some bOld)
    (hSet : setElem? bs idx bNew = some bs')
    (hId : bNew.identity = bOld.identity) :
    listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) bs bs' = true := by
  induction bs generalizing bs' idx with
  | nil => cases hGet
  | cons b rest ih =>
    cases idx with
    | zero =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      injection hGet with hBOld; subst hBOld
      dsimp [setElem?] at hSet
      injection hSet with hBs'; subst hBs'
      dsimp [listRel]
      rw [hId, stringBeq_refl, Bool.true_and]
      exact listRel_id_refl rest
    | succ k =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      dsimp [setElem?] at hSet
      cases hSub : setElem? rest k bNew with
      | none => rw [hSub] at hSet; cases hSet
      | some rest' =>
        rw [hSub] at hSet
        injection hSet with hBs'; subst hBs'
        dsimp [listRel]
        rw [stringBeq_refl, Bool.true_and]
        exact ih hGet hSub

private theorem applyMirSroaTuple_metadataCompat {plan : SroaTuplePlan} {pSrc pTgt : Program}
    (hApp : applyMirSroaTuple plan pSrc = some pTgt) :
    ProgramMetadataCompat pSrc pTgt = true := by
  let ⟨ctx, hP, hS, hT⟩ := extractSroaCtx hApp
  subst hP; subst hS; subst hT
  unfold ProgramMetadataCompat
  have hHdr : programHeaderEq ctx.pSrc ctx.pTgt = true := by
    rw [ctx.hPTgt]
    exact programHeaderEq_of_eq rfl rfl rfl rfl
  have hIdEq : ctx.bodyTgt.identity = ctx.bodySrc.identity := by rw [ctx.hBodyTgt]
  have hRel : listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity)
      ctx.pSrc.bodies ctx.pTgt.bodies = true := by
    rw [ctx.hPTgt]; dsimp
    exact listRel_id_setElem? ctx.hGetSrc ctx.hSetBody hIdEq
  exact bool_and_intro hHdr hRel

private theorem applyMirSroaTuple_unitProgForDef {plan : SroaTuplePlan}
    {pSrc pTgt : Program} (u : DefId)
    (hApp : applyMirSroaTuple plan pSrc = some pTgt) :
    applyMirSroaTuple plan (unitProgForDef pSrc u) =
      some (unitProgForDef pTgt u) := by
  unfold unitProgForDef
  unfold applyMirSroaTuple at hApp; unfold applyMirSroaTuple
  dsimp
  cases hGet : Trusted.MirSemantics.getElem? pSrc.bodies plan.defId with
  | none => rw [hGet] at hApp; cases hApp
  | some b =>
    rw [hGet] at hApp; dsimp at hApp; dsimp
    cases hG1 : (b.basicBlocks.isEmpty ||
        !Nat.blt b.argumentCount plan.tupLocal ||
        !Nat.blt plan.tupLocal b.locals.length ||
        !bodyAllLocalsInBounds b) with
    | true => rw [hG1] at hApp; cases hApp
    | false =>
      rw [hG1] at hApp; dsimp at hApp; dsimp
      cases hTy : Trusted.MirSemantics.getElem? b.locals plan.tupLocal with
      | none => rw [hTy] at hApp; cases hApp
      | some t =>
        rw [hTy] at hApp
        cases t with
        | tuple fTys =>
          dsimp at hApp; dsimp
          cases hG2 : (!isFlatTupleTy (.tuple fTys) || !bodyTupleUsesValid b plan.tupLocal fTys) with
          | true => rw [hG2] at hApp; cases hApp
          | false =>
            rw [hG2] at hApp; dsimp at hApp; dsimp
            cases hSL : setElem? b.locals plan.tupLocal .unit with
            | none => rw [hSL] at hApp; cases hApp
            | some lu =>
              rw [hSL] at hApp; dsimp at hApp; dsimp
              cases hSB : setElem? pSrc.bodies plan.defId _ with
              | none => rw [hSB] at hApp; cases hApp
              | some bs =>
                rw [hSB] at hApp
                injection hApp with hEq
                rw [← hEq]
        | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
          cases hApp

private theorem applyMirSroaTrace_sound (trace : SroaTrace) :
    ∀ {pSrc pTgt : Program},
      applyMirSroaTrace trace pSrc = some pTgt →
      FullSemanticEquivTupleAssert pSrc pTgt ∧
      ProgramMetadataCompat pSrc pTgt = true ∧
      (∀ u : DefId, applyMirSroaTrace trace (unitProgForDef pSrc u) =
        some (unitProgForDef pTgt u)) := by
  induction trace with
  | nil =>
    intro pSrc pTgt h
    injection h with hEq; subst hEq
    exact ⟨fullSemanticEquivTupleAssert_refl pSrc,
           programMetadataCompat_refl pSrc,
           fun _ => rfl⟩
  | cons plan rest ih =>
    intro pSrc pTgt h
    dsimp [applyMirSroaTrace] at h
    cases hStep : applyMirSroaTuple plan pSrc with
    | none => rw [hStep] at h; cases h
    | some pMid =>
      rw [hStep] at h
      have hEq1 := mirSroaTuple_apply_sound hStep
      have hMeta1 := applyMirSroaTuple_metadataCompat hStep
      let ⟨hEq2, hMeta2, hUnit2⟩ := ih h
      refine ⟨fullSemanticEquivTupleAssert_trans hEq1 hEq2
                (programMetadataCompat_bodies_len hMeta1),
              programMetadataCompat_trans hMeta1 hMeta2,
              ?_⟩
      intro u
      dsimp [applyMirSroaTrace]
      rw [applyMirSroaTuple_unitProgForDef u hStep]
      exact hUnit2 u

private theorem checkMirSroaTrace_sound {trace : SroaTrace} {pSrc pMid : Program}
    (hSroa : checkMirSroaTrace trace pSrc pMid = true) :
    FullSemanticEquivTupleAssert pSrc pMid ∧
    ProgramMetadataCompat pSrc pMid = true ∧
    (∀ u : DefId, FullSemanticEquivTupleAssert (unitProgForDef pSrc u) (unitProgForDef pMid u)) := by
  unfold checkMirSroaTrace at hSroa
  cases hApp : applyMirSroaTrace trace pSrc with
  | none => rw [hApp] at hSroa; cases hSroa
  | some pOut =>
    rw [hApp] at hSroa
    have hEq := programEq_eq hSroa; subst hEq
    let ⟨hFull, hMeta, hUnitApp⟩ := applyMirSroaTrace_sound trace hApp
    refine ⟨hFull, hMeta, ?_⟩
    intro u
    exact (applyMirSroaTrace_sound trace (hUnitApp u)).1

/-! #### Section 4: `AssertLower` Soundness (`lowerAssertsToSwitchUnreachable`) -/

private theorem evalSwitchBranches_target_lt (w : IntWidth) (bits : BitVec 128)
    (otherwise bound : Nat) (branches : List (BitVec 128 × BasicBlockId))
    (hOth : Nat.blt otherwise bound = true)
    (hBrs : branches.all (fun br => Nat.blt br.2 bound) = true)
    {target : BasicBlockId}
    (hOk : evalSwitchBranches w bits otherwise branches = .ok target) :
    target < bound := by
  induction branches with
  | nil =>
    injection hOk with hEq; subst hEq
    exact nat_blt_lt hOth
  | cons br rest ih =>
    cases br with
    | mk caseBits tgt =>
      let ⟨hHead, hTail⟩ := bool_and_true hBrs
      dsimp [evalSwitchBranches] at hOk
      cases h1 : (truncateBits w caseBits != caseBits) with
      | true => rw [h1] at hOk; cases hOk
      | false =>
        rw [h1] at hOk; dsimp at hOk
        cases h2 : (truncateBits w bits == truncateBits w caseBits) with
        | true =>
          rw [h2] at hOk; injection hOk with hEq; subst hEq
          exact nat_blt_lt hHead
        | false =>
          rw [h2] at hOk; dsimp at hOk
          exact ih hTail hOk

private theorem evalBoolSwitchBranches_target_lt (b : Bool)
    (otherwise bound : Nat) (branches : List (BitVec 128 × BasicBlockId))
    (hOth : Nat.blt otherwise bound = true)
    (hBrs : branches.all (fun br => Nat.blt br.2 bound) = true)
    {target : BasicBlockId}
    (hOk : evalBoolSwitchBranches b otherwise branches = .ok target) :
    target < bound := by
  induction branches with
  | nil =>
    injection hOk with hEq; subst hEq
    exact nat_blt_lt hOth
  | cons br rest ih =>
    cases br with
    | mk caseBits tgt =>
      let ⟨hHead, hTail⟩ := bool_and_true hBrs
      dsimp [evalBoolSwitchBranches] at hOk
      cases hC : evalConstLit .bool (.scalar caseBits) with
      | error _ => rw [hC] at hOk; cases hOk
      | ok cv =>
        rw [hC] at hOk
        cases cv with
        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hOk
        | bool cb =>
          cases cb with
          | false =>
            dsimp at hOk
            cases hNB : (!b) with
            | true => rw [hNB] at hOk; injection hOk with hEq; subst hEq; exact nat_blt_lt hHead
            | false => rw [hNB] at hOk; dsimp at hOk; exact ih hTail hOk
          | true =>
            dsimp at hOk
            cases b with
            | true => dsimp at hOk; injection hOk with hEq; subst hEq; exact nat_blt_lt hHead
            | false => dsimp at hOk; exact ih hTail hOk

private theorem evalBoolSwitchBranches_lowered_assert (b expected : Bool)
    (target unreachBb : BasicBlockId) :
    evalBoolSwitchBranches b unreachBb
      [(BitVec.ofNat 128 (if expected then 1 else 0), target)] =
      .ok (if b == expected then target else unreachBb) := by
  cases b <;> cases expected <;> rfl

private theorem checkVal_bool_inv {v : Val} (h : checkVal v .bool = true) :
    ∃ b : Bool, v = .bool b := by
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | scalar sv =>
    unfold checkVal Val.ty? at h; dsimp at h
    cases hW : sv.wf <;> (rw [hW] at h; cases h)
  | enumVal ety vIdx =>
    unfold checkVal Val.ty? at h; dsimp at h
    cases hE : (enumAdmitted ety && Nat.blt vIdx ety.discriminants.length) <;>
      (rw [hE] at h; cases h)
  | ptr _ | unit | tuple _ | bytes _ => cases h

private theorem lowerAssertsInBody_props {bMid bFlat : Body}
    (h : lowerAssertsInBody bMid = some bFlat) :
    bFlat.argumentCount = bMid.argumentCount ∧
    bFlat.locals = bMid.locals ∧
    bFlat.isUnsafe = bMid.isUnsafe ∧
    bFlat.identity = bMid.identity ∧
    ((bodyHasAssert bMid = false ∧ bFlat = bMid) ∨
     (bodyHasAssert bMid = true ∧
      bodyAllBlocksInBounds bMid = true ∧
      bodyAssertsAdmitted bMid = true ∧
      bFlat = { bMid with
        basicBlocks :=
          bMid.basicBlocks.map (fun bb =>
            { bb with terminator := lowerAssertTerminator bMid.basicBlocks.length bb.terminator }) ++
          [{ statements := [], terminator := .unreachable, cleanup := false }] })) := by
  unfold lowerAssertsInBody at h
  cases hHas : bodyHasAssert bMid with
  | false =>
    rw [hHas] at h; dsimp at h
    injection h with hEq; subst hEq
    exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | true =>
    rw [hHas] at h; dsimp at h
    cases hG : (!bodyAllBlocksInBounds bMid || !bodyAssertsAdmitted bMid) with
    | true => rw [hG] at h; cases h
    | false =>
      rw [hG] at h; dsimp at h
      let ⟨hNotIb, hNotAdm⟩ := bool_or_false hG
      injection h with hEq
      have hFlatEq := hEq.symm
      rw [hFlatEq]
      exact ⟨rfl, rfl, rfl, rfl,
             Or.inr ⟨rfl, bool_not_false hNotIb, bool_not_false hNotAdm, rfl⟩⟩

private theorem lowerAssertsInBody_hasStorageAnnotation {bMid bFlat : Body}
    (h : lowerAssertsInBody bMid = some bFlat) (id : LocalId) :
    hasStorageAnnotation bFlat id = hasStorageAnnotation bMid id := by
  let ⟨_, _, _, _, hCases⟩ := lowerAssertsInBody_props h
  cases hCases with
  | inl hNo => rw [hNo.2]
  | inr hYes =>
    let ⟨_, _, _, hEq⟩ := hYes
    rw [hEq]
    unfold hasStorageAnnotation
    dsimp
    rw [list_any_append, list_any_map]
    dsimp [List.any]
    repeat rw [Bool.or_false]

private theorem lowerAssertsInBody_storageAnnotationsInBounds {bMid bFlat : Body}
    (h : lowerAssertsInBody bMid = some bFlat) :
    storageAnnotationsInBounds bFlat = storageAnnotationsInBounds bMid := by
  let ⟨_, _, _, _, hCases⟩ := lowerAssertsInBody_props h
  cases hCases with
  | inl hNo => rw [hNo.2]
  | inr hYes =>
    let ⟨_, _, _, hEq⟩ := hYes
    rw [hEq]
    unfold storageAnnotationsInBounds
    dsimp
    rw [list_all_append, list_all_map]
    dsimp [List.all]
    repeat rw [Bool.and_true]

private theorem lowerAssertsInBody_basicBlocks_isEmpty {bMid bFlat : Body}
    (h : lowerAssertsInBody bMid = some bFlat) :
    bFlat.basicBlocks.isEmpty = bMid.basicBlocks.isEmpty := by
  let ⟨_, _, _, _, hCases⟩ := lowerAssertsInBody_props h
  cases hCases with
  | inl hNo => rw [hNo.2]
  | inr hYes =>
    let ⟨hHas, _, _, hEq⟩ := hYes
    have hMidNE : bMid.basicBlocks.isEmpty = false := by
      cases hBbs : bMid.basicBlocks with
      | nil =>
        unfold bodyHasAssert at hHas
        rw [hBbs] at hHas; cases hHas
      | cons _ _ => rfl
    have hFlatNE : bFlat.basicBlocks.isEmpty = false := by
      rw [hEq]; dsimp
      apply list_isEmpty_false_of_pos
      rw [list_append_length]
      dsimp [List.length]
      exact Nat.zero_lt_succ _
    rw [hFlatNE, hMidNE]

private theorem lowerAssertsInBody_initLocalsExtLoop_eq {bMid bFlat : Body}
    (h : lowerAssertsInBody bMid = some bFlat)
    (args : List Val) (idx : Nat) (rem : List MirTy) :
    initLocalsExtLoop bFlat args idx rem = initLocalsExtLoop bMid args idx rem := by
  let ⟨hArg, _, _, _, _⟩ := lowerAssertsInBody_props h
  induction rem generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    dsimp [initLocalsExtLoop]
    rw [hArg, lowerAssertsInBody_hasStorageAnnotation h idx, ih (idx + 1)]

private theorem assertLower_initState_eq {pMid pFlat : Program}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat) (q : Query) :
    initStateTupleAssert pFlat q = initStateTupleAssert pMid q := by
  unfold lowerAssertsToSwitchUnreachable at hLow
  cases hMap : listMapOption lowerAssertsInBody pMid.bodies with
  | none => rw [hMap] at hLow; cases hLow
  | some bodies' =>
    rw [hMap] at hLow; injection hLow with hPEq; subst hPEq
    unfold initStateTupleAssert
    dsimp
    cases hGetM : Trusted.MirSemantics.getElem? pMid.bodies pMid.entryDefId with
    | none =>
      have hGeF : bodies'.length ≤ pMid.entryDefId := by
        rw [listMapOption_length hMap]; exact getElem?_none_ge hGetM
      rw [getElem?_none_of_ge hGeF]
    | some bMid =>
      let ⟨bFlat, hGetF, hBF⟩ := listMapOption_getElem?_left hMap hGetM
      rw [hGetF]; dsimp
      let ⟨hArg, hLoc, _, _, _⟩ := lowerAssertsInBody_props hBF
      rw [lowerAssertsInBody_basicBlocks_isEmpty hBF, hArg, hLoc,
          lowerAssertsInBody_storageAnnotationsInBounds hBF,
          lowerAssertsInBody_initLocalsExtLoop_eq hBF]

private noncomputable def AssertLowerInv (pMid : Program) (s : StateExt) : Prop :=
  StateWellTyped pMid s ∧
  ∀ frame bMid,
    s.frames = [frame] →
    Trusted.MirSemantics.getElem? pMid.bodies frame.defId = some bMid →
    bodyHasAssert bMid = true →
    frame.blockIdx < bMid.basicBlocks.length

private theorem assertLower_init_inv {pMid : Program} {q : Query} {s₀ : StateExt}
    (hOk : initStateTupleAssert pMid q = .ok s₀) :
    AssertLowerInv pMid s₀ := by
  refine ⟨initStateTupleAssert_stateWellTyped hOk, ?_⟩
  intro frame bMid hFrames hBody _
  unfold initStateTupleAssert at hOk
  cases h1 : (!Nat.beq pMid.pointerWidthBits 64 || !Nat.beq pMid.mirProfileVersion 1) with
  | true => rw [h1] at hOk; cases hOk
  | false =>
    rw [h1] at hOk; dsimp at hOk
    cases h2 : (!q.callerMem.allocations.isEmpty) with
    | true => rw [h2] at hOk; cases hOk
    | false =>
      rw [h2] at hOk; dsimp at hOk
      cases h3 : Trusted.MirSemantics.getElem? pMid.bodies pMid.entryDefId with
      | none => rw [h3] at hOk; cases hOk
      | some b =>
        rw [h3] at hOk; dsimp at hOk
        cases h4 : b.basicBlocks.isEmpty with
        | true => rw [h4] at hOk; cases hOk
        | false =>
          rw [h4] at hOk; dsimp at hOk
          cases h5 : (!Nat.blt b.argumentCount b.locals.length) with
          | true => rw [h5] at hOk; cases hOk
          | false =>
            rw [h5] at hOk; dsimp at hOk
            cases h6 : (!storageAnnotationsInBounds b) with
            | true => rw [h6] at hOk; cases hOk
            | false =>
              rw [h6] at hOk; dsimp at hOk
              cases h7 : (!b.locals.all isSupportedTupleOrScalarTy) with
              | true => rw [h7] at hOk; cases hOk
              | false =>
                rw [h7] at hOk; dsimp at hOk
                cases h8 : (!checkArgsMatchExt q.args ((b.locals.drop 1).take b.argumentCount)) with
                | true => rw [h8] at hOk; cases hOk
                | false =>
                  rw [h8] at hOk; dsimp at hOk
                  injection hOk with hSEq; subst hSEq
                  dsimp at hFrames; injection hFrames with hFEq; subst hFEq
                  dsimp at hBody; dsimp
                  rw [h3] at hBody; injection hBody with hBEq; subst hBEq
                  exact list_pos_of_isEmpty_false h4

private theorem evalStatementExt_preserves_def_blk {body : Body} {frame f' : FrameStateExt}
    {mem : CallerMemory} {stmt : StatementKind} {s' : StateExt}
    (hEv : evalStatementExt body frame mem stmt = .step s')
    (hF' : s'.frames = [f']) :
    f'.defId = frame.defId ∧ f'.blockIdx = frame.blockIdx := by
  cases stmt with
  | nop =>
    dsimp [evalStatementExt] at hEv; injection hEv with hEq; subst hEq
    dsimp at hF'; injection hF' with hFEq; subst hFEq; exact ⟨rfl, rfl⟩
  | unsupported => cases hEv
  | storageLive id =>
    dsimp [evalStatementExt] at hEv
    cases h1 : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [h1] at hEv; cases hEv
    | some ty =>
      rw [h1] at hEv; dsimp at hEv
      cases h2 : setElem? frame.locals id (liveUninitSlotExt ty) with
      | none => rw [h2] at hEv; cases hEv
      | some _ =>
        rw [h2] at hEv; injection hEv with hEq; subst hEq
        dsimp at hF'; injection hF' with hFEq; subst hFEq; exact ⟨rfl, rfl⟩
  | storageDead id =>
    dsimp [evalStatementExt] at hEv
    cases h1 : Nat.beq id 0 with
    | true => rw [h1] at hEv; cases hEv
    | false =>
      rw [h1] at hEv; dsimp at hEv
      cases h2 : setElem? frame.locals id .dead with
      | none => rw [h2] at hEv; cases hEv
      | some _ =>
        rw [h2] at hEv; injection hEv with hEq; subst hEq
        dsimp at hF'; injection hF' with hFEq; subst hFEq; exact ⟨rfl, rfl⟩
  | assign dst rv =>
    cases dst with
    | mk did dproj =>
      dsimp [evalStatementExt] at hEv
      cases dproj with
      | nil =>
        dsimp at hEv
        cases hT : Trusted.MirSemantics.getElem? body.locals did with
        | none => rw [hT] at hEv; cases hEv
        | some dty =>
          rw [hT] at hEv; dsimp at hEv
          cases rv with
          | aggregateTuple ops =>
            cases dty with
            | tuple fTys =>
              dsimp at hEv
              cases hBad : (!isFlatTupleTy (.tuple fTys) || !Nat.beq ops.length fTys.length ||
                  ops.any (operandMentionsLocal did)) with
              | true => rw [hBad] at hEv; cases hEv
              | false =>
                rw [hBad] at hEv; dsimp at hEv
                cases hA : evalAggregateInPlaceExt body.locals frame.locals did 0 ops fTys with
                | error _ => rw [hA] at hEv; cases hEv
                | ok _ =>
                  rw [hA] at hEv; injection hEv with hEq; subst hEq
                  dsimp at hF'; injection hF' with hFEq; subst hFEq; exact ⟨rfl, rfl⟩
            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
          | ref _ _ | addressOf _ _ | unsupported =>
            dsimp [evalRvalueExt] at hEv
            cases dty <;> cases hEv
          | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _ =>
            dsimp at hEv
            have hHelper : ∀ (rvX : Rvalue) (guard : Bool),
                (if guard = true then
                   (StepResult.fault FaultKind.unsupported : StepResult StateExt TerminalOutExt)
                 else
                   match evalRvalueExt body.locals frame.locals dty rvX with
                   | .error k => .fault k
                   | .ok (v, ls1) =>
                     match writePlaceExt ls1 did dty v with
                     | .error k => .fault k
                     | .ok ls2 =>
                       .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := ls2 }],
                               callerMem := mem }) = .step s' →
                f'.defId = frame.defId ∧ f'.blockIdx = frame.blockIdx := by
              intro rvX guard hG
              cases guard with
              | true => cases hG
              | false =>
                dsimp at hG
                cases hR : evalRvalueExt body.locals frame.locals dty rvX with
                | error _ => rw [hR] at hG; cases hG
                | ok pr =>
                  rw [hR] at hG
                  cases pr with
                  | mk v ls1 =>
                    dsimp at hG
                    cases hW : writePlaceExt ls1 did dty v with
                    | error _ => rw [hW] at hG; cases hG
                    | ok _ =>
                      rw [hW] at hG; injection hG with hEq; subst hEq
                      dsimp at hF'; injection hF' with hFEq; subst hFEq; exact ⟨rfl, rfl⟩
            exact hHelper _ _ hEv
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> cases hEv
        | nil =>
          cases pe with
          | deref | unsupported => cases hEv
          | field idx fty =>
            dsimp at hEv
            cases hT : Trusted.MirSemantics.getElem? body.locals did with
            | none => rw [hT] at hEv; cases hEv
            | some dty =>
              rw [hT] at hEv
              cases dty with
              | tuple fTys =>
                dsimp at hEv
                cases hNf : (!isFlatTupleTy (.tuple fTys)) with
                | true => rw [hNf] at hEv; cases hEv
                | false =>
                  rw [hNf] at hEv; dsimp at hEv
                  cases hFt : Trusted.MirSemantics.getElem? fTys idx with
                  | none => rw [hFt] at hEv; cases hEv
                  | some dft =>
                    rw [hFt] at hEv; dsimp at hEv
                    cases hNt : (!MirTy.beq fty dft) with
                    | true => rw [hNt] at hEv; cases hEv
                    | false =>
                      rw [hNt] at hEv; dsimp at hEv
                      cases hR : evalRvalueExt body.locals frame.locals dft rv with
                      | error _ => rw [hR] at hEv; cases hEv
                      | ok pr =>
                        rw [hR] at hEv
                        cases pr with
                        | mk v ls1 =>
                          dsimp at hEv
                          cases hW : writeTupleFieldExt ls1 did idx dft v with
                          | error _ => rw [hW] at hEv; cases hEv
                          | ok _ =>
                            rw [hW] at hEv; injection hEv with hEq; subst hEq
                            dsimp at hF'; injection hF' with hFEq; subst hFEq; exact ⟨rfl, rfl⟩
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv

private theorem evalTerminatorExt_preserves_defId {body : Body} {bb : BasicBlock}
    {frame f' : FrameStateExt} {mem : CallerMemory} {s' : StateExt}
    (hEv : evalTerminatorExt body bb frame mem = .step s')
    (hF' : s'.frames = [f']) :
    f'.defId = frame.defId := by
  unfold evalTerminatorExt at hEv
  cases hTm : bb.terminator with
  | goto _ =>
    rw [hTm] at hEv; dsimp [jumpToBlockExt] at hEv
    injection hEv with hEq; subst hEq; dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
  | unreachable | unwindResume | call _ _ _ _ _ | unsupported =>
    rw [hTm] at hEv; cases hEv
  | return_ =>
    rw [hTm] at hEv; dsimp at hEv
    cases hCl : bb.cleanup with
    | true => rw [hCl] at hEv; cases hEv
    | false =>
      rw [hCl] at hEv; dsimp at hEv
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at hEv; cases hEv
      | some sl =>
        rw [h0] at hEv
        cases sl with
        | dead => cases hEv
        | liveBase ov => cases ov <;> cases hEv
        | liveTuple fields =>
          cases hB0 : Trusted.MirSemantics.getElem? body.locals 0 with
          | none => rw [hB0] at hEv; cases hEv
          | some t0 =>
            rw [hB0] at hEv
            cases t0 with
            | tuple fTys =>
              dsimp at hEv
              cases hC : (isFlatTupleTy (.tuple fTys) && Nat.beq fields.length fTys.length) with
              | false => rw [hC] at hEv; cases hEv
              | true =>
                rw [hC] at hEv; dsimp at hEv
                cases hE : extractAllInitFields fields <;> (rw [hE] at hEv; cases hEv)
            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | switchInt discr ts =>
    rw [hTm] at hEv; dsimp at hEv
    cases hOp : evalPrimitiveOperandExt body.locals frame.locals discr with
    | error _ => rw [hOp] at hEv; cases hEv
    | ok pr =>
      rw [hOp] at hEv
      cases pr with
      | mk dv ls1 =>
        dsimp at hEv
        cases dv with
        | scalar sv =>
          dsimp at hEv
          cases hBr : evalSwitchBranches sv.width sv.bits ts.otherwise ts.branches with
          | error _ => rw [hBr] at hEv; cases hEv
          | ok _ =>
            rw [hBr] at hEv; dsimp [jumpToBlockExt] at hEv
            injection hEv with hEq; subst hEq; dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
        | bool b =>
          dsimp at hEv
          cases hBr : evalBoolSwitchBranches b ts.otherwise ts.branches with
          | error _ => rw [hBr] at hEv; cases hEv
          | ok _ =>
            rw [hBr] at hEv; dsimp [jumpToBlockExt] at hEv
            injection hEv with hEq; subst hEq; dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
  | assert cond expected msg target unwind =>
    rw [hTm] at hEv; dsimp at hEv
    cases hOp : evalPrimitiveOperandExt body.locals frame.locals cond with
    | error _ => rw [hOp] at hEv; cases hEv
    | ok pr =>
      rw [hOp] at hEv
      cases pr with
      | mk cv ls1 =>
        dsimp at hEv
        cases cv with
        | bool b =>
          dsimp at hEv
          cases hBeq : (b == expected) with
          | true =>
            rw [hBeq] at hEv; dsimp [jumpToBlockExt] at hEv
            injection hEv with hEq; subst hEq; dsimp at hF'; injection hF' with hFEq; subst hFEq; rfl
          | false =>
            rw [hBeq] at hEv; dsimp at hEv
            cases hK : (!isSupportedAssertKind msg) with
            | true => rw [hK] at hEv; cases hEv
            | false => rw [hK] at hEv; dsimp at hEv; cases unwind <;> cases hEv
        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

private theorem evalTerminatorExt_preserves_blk_inBounds {body : Body} {bb : BasicBlock}
    {frame f' : FrameStateExt} {mem : CallerMemory} {s' : StateExt}
    (hTermIb : terminatorBlocksLt body.basicBlocks.length bb.terminator = true)
    (hEv : evalTerminatorExt body bb frame mem = .step s')
    (hF' : s'.frames = [f']) :
    f'.blockIdx < body.basicBlocks.length := by
  unfold evalTerminatorExt at hEv
  cases hTm : bb.terminator with
  | goto target =>
    rw [hTm] at hTermIb hEv
    dsimp [terminatorBlocksLt] at hTermIb
    dsimp [jumpToBlockExt] at hEv
    injection hEv with hEq; subst hEq
    dsimp at hF'; injection hF' with hFEq; subst hFEq
    exact nat_blt_lt hTermIb
  | unreachable | unwindResume | call _ _ _ _ _ | unsupported =>
    rw [hTm] at hEv; cases hEv
  | return_ =>
    rw [hTm] at hEv; dsimp at hEv
    cases hCl : bb.cleanup with
    | true => rw [hCl] at hEv; cases hEv
    | false =>
      rw [hCl] at hEv; dsimp at hEv
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at hEv; cases hEv
      | some sl =>
        rw [h0] at hEv
        cases sl with
        | dead => cases hEv
        | liveBase ov => cases ov <;> cases hEv
        | liveTuple fields =>
          cases hB0 : Trusted.MirSemantics.getElem? body.locals 0 with
          | none => rw [hB0] at hEv; cases hEv
          | some t0 =>
            rw [hB0] at hEv
            cases t0 with
            | tuple fTys =>
              dsimp at hEv
              cases hC : (isFlatTupleTy (.tuple fTys) && Nat.beq fields.length fTys.length) with
              | false => rw [hC] at hEv; cases hEv
              | true =>
                rw [hC] at hEv; dsimp at hEv
                cases hE : extractAllInitFields fields <;> (rw [hE] at hEv; cases hEv)
            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | switchInt discr ts =>
    rw [hTm] at hTermIb hEv
    let ⟨hOth, hBrs⟩ := bool_and_true hTermIb
    dsimp at hEv
    cases hOp : evalPrimitiveOperandExt body.locals frame.locals discr with
    | error _ => rw [hOp] at hEv; cases hEv
    | ok pr =>
      rw [hOp] at hEv
      cases pr with
      | mk dv ls1 =>
        dsimp at hEv
        cases dv with
        | scalar sv =>
          dsimp at hEv
          cases hBr : evalSwitchBranches sv.width sv.bits ts.otherwise ts.branches with
          | error _ => rw [hBr] at hEv; cases hEv
          | ok target =>
            rw [hBr] at hEv; dsimp [jumpToBlockExt] at hEv
            injection hEv with hEq; subst hEq
            dsimp at hF'; injection hF' with hFEq; subst hFEq
            exact evalSwitchBranches_target_lt sv.width sv.bits ts.otherwise _ ts.branches hOth hBrs hBr
        | bool b =>
          dsimp at hEv
          cases hBr : evalBoolSwitchBranches b ts.otherwise ts.branches with
          | error _ => rw [hBr] at hEv; cases hEv
          | ok target =>
            rw [hBr] at hEv; dsimp [jumpToBlockExt] at hEv
            injection hEv with hEq; subst hEq
            dsimp at hF'; injection hF' with hFEq; subst hFEq
            exact evalBoolSwitchBranches_target_lt b ts.otherwise _ ts.branches hOth hBrs hBr
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
  | assert cond expected msg target unwind =>
    rw [hTm] at hTermIb hEv
    let ⟨hTgtLt, _⟩ := bool_and_true hTermIb
    dsimp at hEv
    cases hOp : evalPrimitiveOperandExt body.locals frame.locals cond with
    | error _ => rw [hOp] at hEv; cases hEv
    | ok pr =>
      rw [hOp] at hEv
      cases pr with
      | mk cv ls1 =>
        dsimp at hEv
        cases cv with
        | bool b =>
          dsimp at hEv
          cases hBeq : (b == expected) with
          | true =>
            rw [hBeq] at hEv; dsimp [jumpToBlockExt] at hEv
            injection hEv with hEq; subst hEq
            dsimp at hF'; injection hF' with hFEq; subst hFEq
            exact nat_blt_lt hTgtLt
          | false =>
            rw [hBeq] at hEv; dsimp at hEv
            cases hK : (!isSupportedAssertKind msg) with
            | true => rw [hK] at hEv; cases hEv
            | false => rw [hK] at hEv; dsimp at hEv; cases unwind <;> cases hEv
        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

private theorem assertLower_preserves_inv {pMid pFlat : Program} {s s' : StateExt}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat)
    (hInv : AssertLowerInv pMid s)
    (hStep : evalStepTupleAssert pMid 0 s = .step s') :
    AssertLowerInv pMid s' := by
  let ⟨hWt, hBlkInv⟩ := hInv
  refine ⟨evalStepTupleAssert_preserves_stateWellTyped hWt hStep, ?_⟩
  intro f' bMid' hF' hB' hHas'
  let ⟨frame, bMid, hF, hB, _, _⟩ := hWt
  unfold evalStepTupleAssert at hStep
  rw [hF] at hStep; dsimp at hStep
  rw [hB] at hStep; dsimp at hStep
  cases hBb : Trusted.MirSemantics.getElem? bMid.basicBlocks frame.blockIdx with
  | none => rw [hBb] at hStep; cases hStep
  | some bb =>
    rw [hBb] at hStep; dsimp at hStep
    cases hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
    | some stmt =>
      rw [hSt] at hStep; dsimp at hStep
      let ⟨hDefEq, hBlkEq⟩ := evalStatementExt_preserves_def_blk hStep hF'
      rw [hDefEq, hB] at hB'; injection hB' with hBEq; subst hBEq
      rw [hBlkEq]
      exact hBlkInv frame bMid hF hB hHas'
    | none =>
      rw [hSt] at hStep; dsimp at hStep
      cases hLen : Nat.beq frame.stmtIdx bb.statements.length with
      | false => rw [hLen] at hStep; cases hStep
      | true =>
        rw [hLen] at hStep; dsimp at hStep
        have hDefEq := evalTerminatorExt_preserves_defId hStep hF'
        rw [hDefEq, hB] at hB'; injection hB' with hBEq; subst hBEq
        unfold lowerAssertsToSwitchUnreachable at hLow
        cases hMap : listMapOption lowerAssertsInBody pMid.bodies with
        | none => rw [hMap] at hLow; cases hLow
        | some bodies' =>
          let ⟨bFlat, _, hBF⟩ := listMapOption_getElem?_left hMap hB
          let ⟨_, _, _, _, hCases⟩ := lowerAssertsInBody_props hBF
          cases hCases with
          | inl hNo => rw [hNo.1] at hHas'; cases hHas'
          | inr hYes =>
            let ⟨_, hAllBlkIb, _, _⟩ := hYes
            have hTermIb := list_all_getElem? hAllBlkIb hBb
            exact evalTerminatorExt_preserves_blk_inBounds hTermIb hStep hF'

private theorem evalStatementExt_never_panic {body : Body} {frame : FrameStateExt}
    {mem : CallerMemory} {stmt : StatementKind} (msg : AssertKind) :
    evalStatementExt body frame mem stmt ≠ .done (.panic msg) := by
  intro hEv
  cases stmt with
  | nop | unsupported => cases hEv
  | storageLive id =>
    dsimp [evalStatementExt] at hEv
    cases h1 : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [h1] at hEv; cases hEv
    | some ty =>
      rw [h1] at hEv; dsimp at hEv
      cases h2 : setElem? frame.locals id (liveUninitSlotExt ty) <;> (rw [h2] at hEv; cases hEv)
  | storageDead id =>
    dsimp [evalStatementExt] at hEv
    cases h1 : Nat.beq id 0 with
    | true => rw [h1] at hEv; cases hEv
    | false =>
      rw [h1] at hEv; dsimp at hEv
      cases h2 : setElem? frame.locals id .dead <;> (rw [h2] at hEv; cases hEv)
  | assign dst rv =>
    cases dst with
    | mk did dproj =>
      dsimp [evalStatementExt] at hEv
      cases dproj with
      | nil =>
        dsimp at hEv
        cases hT : Trusted.MirSemantics.getElem? body.locals did with
        | none => rw [hT] at hEv; cases hEv
        | some dty =>
          rw [hT] at hEv; dsimp at hEv
          cases rv with
          | aggregateTuple ops =>
            cases dty with
            | tuple fTys =>
              dsimp at hEv
              cases hBad : (!isFlatTupleTy (.tuple fTys) || !Nat.beq ops.length fTys.length ||
                  ops.any (operandMentionsLocal did)) with
              | true => rw [hBad] at hEv; cases hEv
              | false =>
                rw [hBad] at hEv; dsimp at hEv
                cases hA : evalAggregateInPlaceExt body.locals frame.locals did 0 ops fTys <;>
                  (rw [hA] at hEv; cases hEv)
            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
          | ref _ _ | addressOf _ _ | unsupported =>
            dsimp [evalRvalueExt] at hEv; cases dty <;> cases hEv
          | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _ =>
            dsimp at hEv
            have hNoDone : ∀ (rvX : Rvalue) (guard : Bool),
                (if guard = true then
                   (StepResult.fault FaultKind.unsupported : StepResult StateExt TerminalOutExt)
                 else
                   match evalRvalueExt body.locals frame.locals dty rvX with
                   | .error k => .fault k
                   | .ok (v, ls1) =>
                     match writePlaceExt ls1 did dty v with
                     | .error k => .fault k
                     | .ok ls2 =>
                       .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := ls2 }],
                               callerMem := mem }) ≠ .done (.panic msg) := by
              intro rvX guard hG
              cases guard with
              | true => cases hG
              | false =>
                dsimp at hG
                cases hR : evalRvalueExt body.locals frame.locals dty rvX with
                | error _ => rw [hR] at hG; cases hG
                | ok pr =>
                  rw [hR] at hG
                  cases pr with
                  | mk v ls1 =>
                    dsimp at hG
                    cases hW : writePlaceExt ls1 did dty v <;> (rw [hW] at hG; cases hG)
            exact hNoDone _ _ hEv
      | cons pe rest =>
        cases rest with
        | cons _ _ => cases pe <;> cases hEv
        | nil =>
          cases pe with
          | deref | unsupported => cases hEv
          | field idx fty =>
            dsimp at hEv
            cases hT : Trusted.MirSemantics.getElem? body.locals did with
            | none => rw [hT] at hEv; cases hEv
            | some dty =>
              rw [hT] at hEv
              cases dty with
              | tuple fTys =>
                dsimp at hEv
                cases hNf : (!isFlatTupleTy (.tuple fTys)) with
                | true => rw [hNf] at hEv; cases hEv
                | false =>
                  rw [hNf] at hEv; dsimp at hEv
                  cases hFt : Trusted.MirSemantics.getElem? fTys idx with
                  | none => rw [hFt] at hEv; cases hEv
                  | some dft =>
                    rw [hFt] at hEv; dsimp at hEv
                    cases hNt : (!MirTy.beq fty dft) with
                    | true => rw [hNt] at hEv; cases hEv
                    | false =>
                      rw [hNt] at hEv; dsimp at hEv
                      cases hR : evalRvalueExt body.locals frame.locals dft rv with
                      | error _ => rw [hR] at hEv; cases hEv
                      | ok pr =>
                        rw [hR] at hEv
                        cases pr with
                        | mk v ls1 =>
                          dsimp at hEv
                          cases hW : writeTupleFieldExt ls1 did idx dft v <;> (rw [hW] at hEv; cases hEv)
              | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv

private theorem evalTerminatorExt_nonAssert_never_panic {body : Body} {bb : BasicBlock}
    {frame : FrameStateExt} {mem : CallerMemory}
    (hNotAs : isAssertTerminator bb.terminator = false) (msg : AssertKind) :
    evalTerminatorExt body bb frame mem ≠ .done (.panic msg) := by
  intro hEv
  unfold evalTerminatorExt at hEv
  cases hTm : bb.terminator with
  | assert _ _ _ _ _ => rw [hTm] at hNotAs; cases hNotAs
  | goto _ | unreachable | unwindResume | call _ _ _ _ _ | unsupported =>
    rw [hTm] at hEv; cases hEv
  | return_ =>
    rw [hTm] at hEv; dsimp at hEv
    cases hCl : bb.cleanup with
    | true => rw [hCl] at hEv; cases hEv
    | false =>
      rw [hCl] at hEv; dsimp at hEv
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at hEv; cases hEv
      | some sl =>
        rw [h0] at hEv
        cases sl with
        | dead => cases hEv
        | liveBase ov => cases ov <;> cases hEv
        | liveTuple fields =>
          cases hB0 : Trusted.MirSemantics.getElem? body.locals 0 with
          | none => rw [hB0] at hEv; cases hEv
          | some t0 =>
            rw [hB0] at hEv
            cases t0 with
            | tuple fTys =>
              dsimp at hEv
              cases hC : (isFlatTupleTy (.tuple fTys) && Nat.beq fields.length fTys.length) with
              | false => rw [hC] at hEv; cases hEv
              | true =>
                rw [hC] at hEv; dsimp at hEv
                cases hE : extractAllInitFields fields <;> (rw [hE] at hEv; cases hEv)
            | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | switchInt discr ts =>
    rw [hTm] at hEv; dsimp at hEv
    cases hOp : evalPrimitiveOperandExt body.locals frame.locals discr with
    | error _ => rw [hOp] at hEv; cases hEv
    | ok pr =>
      rw [hOp] at hEv
      cases pr with
      | mk dv ls1 =>
        dsimp at hEv
        cases dv with
        | scalar sv =>
          dsimp at hEv
          cases hBr : evalSwitchBranches sv.width sv.bits ts.otherwise ts.branches <;>
            (rw [hBr] at hEv; cases hEv)
        | bool b =>
          dsimp at hEv
          cases hBr : evalBoolSwitchBranches b ts.otherwise ts.branches <;>
            (rw [hBr] at hEv; cases hEv)
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

private theorem assertLower_step_rel {pMid pFlat : Program} {s : StateExt}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat)
    (hInv : AssertLowerInv pMid s) :
    (evalStepTupleAssert pFlat 0 s = evalStepTupleAssert pMid 0 s ∧
      ∀ msg, evalStepTupleAssert pMid 0 s ≠ .done (.panic msg)) ∨
    (((∃ msg, evalStepTupleAssert pMid 0 s = .done (.panic msg)) ∨
        evalStepTupleAssert pMid 0 s = .fault .undefined) ∧
      ∃ sTrap,
        evalStepTupleAssert pFlat 0 s = .step sTrap ∧
        evalStepTupleAssert pFlat 0 sTrap = .fault .undefined) := by
  let ⟨hWt, hBlkInv⟩ := hInv
  let ⟨frame, bMid, hFrames, hGetM, hAllSup, hLocWt⟩ := hWt
  cases s with
  | mk frs mem =>
    dsimp at hFrames; subst hFrames
    unfold lowerAssertsToSwitchUnreachable at hLow
    cases hMap : listMapOption lowerAssertsInBody pMid.bodies with
    | none => rw [hMap] at hLow; cases hLow
    | some bodies' =>
      rw [hMap] at hLow; injection hLow with hPEq; subst hPEq
      let ⟨bFlat, hGetF, hBF⟩ := listMapOption_getElem?_left hMap hGetM
      let ⟨_, hLocEq, _, _, hCases⟩ := lowerAssertsInBody_props hBF
      cases hCases with
      | inl hNoAs =>
        let ⟨hNoAssert, hBEq⟩ := hNoAs
        rw [hBEq] at hGetF
        apply Or.inl
        have hStepEq : evalStepTupleAssert { pMid with bodies := bodies' } 0
            { frames := [frame], callerMem := mem } =
            evalStepTupleAssert pMid 0 { frames := [frame], callerMem := mem } := by
          unfold evalStepTupleAssert; dsimp; rw [hGetF, hGetM]
        refine ⟨hStepEq, ?_⟩
        intro msg
        unfold evalStepTupleAssert; dsimp; rw [hGetM]; dsimp
        cases hBb : Trusted.MirSemantics.getElem? bMid.basicBlocks frame.blockIdx with
        | none => intro h; cases h
        | some bb =>
          dsimp
          cases hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | some stmt => exact evalStatementExt_never_panic msg
          | none =>
            dsimp
            cases Nat.beq frame.stmtIdx bb.statements.length with
            | false => intro h; cases h
            | true =>
              dsimp
              unfold bodyHasAssert at hNoAssert
              have hNotAs : isAssertTerminator bb.terminator = false :=
                list_any_false_getElem? (p := fun b : BasicBlock => isAssertTerminator b.terminator) hNoAssert hBb
              exact evalTerminatorExt_nonAssert_never_panic hNotAs msg
      | inr hYes =>
        let ⟨hHasAs, _, hAdm, hFlatDef⟩ := hYes
        have hBlkLt : frame.blockIdx < bMid.basicBlocks.length :=
          hBlkInv frame bMid rfl hGetM hHasAs
        let ⟨bbMid, hBbM⟩ := getElem?_some_of_lt bMid.basicBlocks frame.blockIdx hBlkLt
        let loweredBbs := bMid.basicBlocks.map (fun bb =>
          { bb with terminator := lowerAssertTerminator bMid.basicBlocks.length bb.terminator })
        let trapBb : BasicBlock := { statements := [], terminator := .unreachable, cleanup := false }
        have hBbF : Trusted.MirSemantics.getElem? bFlat.basicBlocks frame.blockIdx =
            some { bbMid with terminator := lowerAssertTerminator bMid.basicBlocks.length bbMid.terminator } := by
          rw [hFlatDef]; dsimp
          have hLtMap : frame.blockIdx < loweredBbs.length := by
            rw [map_length_eq]; exact hBlkLt
          rw [getElem?_append_left loweredBbs [trapBb] frame.blockIdx hLtMap,
              getElem?_map, hBbM]; rfl
        cases hSt : Trusted.MirSemantics.getElem? bbMid.statements frame.stmtIdx with
        | some stmt =>
          apply Or.inl
          have hStepEq : evalStepTupleAssert { pMid with bodies := bodies' } 0
              { frames := [frame], callerMem := mem } =
              evalStepTupleAssert pMid 0 { frames := [frame], callerMem := mem } := by
            unfold evalStepTupleAssert; dsimp
            rw [hGetF, hGetM]; dsimp
            rw [hBbF, hBbM]; dsimp
            rw [hSt]; dsimp
            exact evalStatementExt_congr_locals hLocEq frame mem stmt
          refine ⟨hStepEq, ?_⟩
          intro msg
          unfold evalStepTupleAssert; dsimp; rw [hGetM]; dsimp; rw [hBbM]; dsimp; rw [hSt]
          exact evalStatementExt_never_panic msg
        | none =>
          cases hLen : Nat.beq frame.stmtIdx bbMid.statements.length with
          | false =>
            apply Or.inl
            have hStepEq : evalStepTupleAssert { pMid with bodies := bodies' } 0
                { frames := [frame], callerMem := mem } =
                evalStepTupleAssert pMid 0 { frames := [frame], callerMem := mem } := by
              unfold evalStepTupleAssert; dsimp
              rw [hGetF, hGetM]; dsimp
              rw [hBbF, hBbM]; dsimp
              rw [hSt]; dsimp; rw [hLen]; dsimp
            refine ⟨hStepEq, ?_⟩
            intro msg
            unfold evalStepTupleAssert; dsimp; rw [hGetM]; dsimp; rw [hBbM]; dsimp; rw [hSt]; dsimp; rw [hLen]; dsimp
            intro h; cases h
          | true =>
            have hMidStep : evalStepTupleAssert pMid 0 { frames := [frame], callerMem := mem } =
                evalTerminatorExt bMid bbMid frame mem := by
              unfold evalStepTupleAssert; dsimp
              rw [hGetM]; dsimp; rw [hBbM]; dsimp; rw [hSt]; dsimp; rw [hLen]; dsimp
            have hFlatStep : evalStepTupleAssert { pMid with bodies := bodies' } 0
                { frames := [frame], callerMem := mem } =
                evalTerminatorExt bMid
                  { bbMid with terminator := lowerAssertTerminator bMid.basicBlocks.length bbMid.terminator }
                  frame mem := by
              unfold evalStepTupleAssert; dsimp
              rw [hGetF]; dsimp; rw [hBbF]; dsimp; rw [hSt]; dsimp; rw [hLen]; dsimp
              exact evalTerminatorExt_congr_locals hLocEq _ frame mem
            cases hTm : bbMid.terminator with
            | goto _ | switchInt _ _ | return_ | unreachable | unwindResume
            | call _ _ _ _ _ | unsupported =>
              apply Or.inl
              have hLowId : lowerAssertTerminator bMid.basicBlocks.length bbMid.terminator =
                  bbMid.terminator := by
                rw [hTm]; rfl
              have hBbId : { bbMid with terminator := lowerAssertTerminator bMid.basicBlocks.length bbMid.terminator } =
                  bbMid := by
                rw [hLowId]
              refine ⟨by rw [hFlatStep, hMidStep, hBbId], ?_⟩
              intro msg
              rw [hMidStep]
              apply evalTerminatorExt_nonAssert_never_panic
              rw [hTm]; rfl
            | assert cond expected msg target unwind =>
              have hBbAdm := list_all_getElem? hAdm hBbM
              rw [hTm] at hBbAdm; dsimp at hBbAdm
              let ⟨hAdm12, hCondTy⟩ := bool_and_true hBbAdm
              let ⟨hSupMsg, hSupUnw⟩ := bool_and_true hAdm12
              unfold evalTerminatorExt at hMidStep hFlatStep
              rw [hTm] at hMidStep hFlatStep
              dsimp [lowerAssertTerminator] at hMidStep hFlatStep
              cases hEvC : evalPrimitiveOperandExt bMid.locals frame.locals cond with
              | error k =>
                rw [hEvC] at hMidStep hFlatStep; dsimp at hMidStep hFlatStep
                apply Or.inl
                refine ⟨by rw [hFlatStep, hMidStep], ?_⟩
                intro msg' h; rw [hMidStep] at h; cases h
              | ok pr =>
                rw [hEvC] at hMidStep hFlatStep
                cases pr with
                | mk cv ls' =>
                  dsimp at hMidStep hFlatStep
                  -- Establish `cv = .bool b` from `StateWellTyped` + `hCondTy`
                  have hCheckBool : checkVal cv .bool = true := by
                    unfold evalPrimitiveOperandExt at hEvC
                    cases hSl : evalOperandToSlotExt bMid.locals frame.locals cond with
                    | error _ => rw [hSl] at hEvC; cases hEvC
                    | ok tr =>
                      rw [hSl] at hEvC
                      cases tr with
                      | mk ty r1 =>
                        cases r1 with
                        | mk ov ls1 =>
                          dsimp at hEvC
                          cases hPr : (!isPrimitiveReadableTy ty) with
                          | true => rw [hPr] at hEvC; cases hEvC
                          | false =>
                            rw [hPr] at hEvC; dsimp at hEvC
                            cases ov with
                            | none => cases hEvC
                            | some v =>
                              injection hEvC with hPairEq
                              injection hPairEq with hVEq _
                              subst hVEq
                              have hSt := evalOperandToSlotExt_staticTy hSl
                              rw [hSt] at hCondTy; dsimp [optMirTyEq] at hCondTy
                              have hTyBool := mirTy_beq_eq hCondTy
                              subst hTyBool
                              exact (evalOperandToSlotExt_preserves_wt hAllSup hLocWt hSl).2 v rfl
                  let ⟨b, hCvBool⟩ := checkVal_bool_inv hCheckBool
                  subst hCvBool
                  dsimp at hMidStep hFlatStep
                  rw [evalBoolSwitchBranches_lowered_assert b expected target bMid.basicBlocks.length] at hFlatStep
                  dsimp at hFlatStep
                  cases hBeq : (b == expected) with
                  | true =>
                    rw [hBeq] at hMidStep hFlatStep; dsimp at hMidStep hFlatStep
                    apply Or.inl
                    refine ⟨by rw [hFlatStep, hMidStep], ?_⟩
                    intro msg' h
                    rw [hMidStep] at h; dsimp [jumpToBlockExt] at h; cases h
                  | false =>
                    rw [hBeq] at hMidStep hFlatStep; dsimp at hMidStep hFlatStep
                    have hNotSupF : (!isSupportedAssertKind msg) = false := by
                      rw [hSupMsg]; rfl
                    rw [hNotSupF] at hMidStep; dsimp at hMidStep
                    apply Or.inr
                    refine ⟨?_, ?_⟩
                    · cases unwind with
                      | continue_ => rw [hMidStep]; exact Or.inl ⟨msg, rfl⟩
                      | terminate => rw [hMidStep]; exact Or.inl ⟨msg, rfl⟩
                      | unreachable => rw [hMidStep]; exact Or.inr rfl
                      | cleanup _ => cases hSupUnw
                    · refine ⟨{ frames := [{ frame with blockIdx := bMid.basicBlocks.length, stmtIdx := 0, locals := ls' }],
                                callerMem := mem },
                              hFlatStep, ?_⟩
                      unfold evalStepTupleAssert; dsimp
                      rw [hGetF]; dsimp
                      have hTrapAt : Trusted.MirSemantics.getElem? bFlat.basicBlocks bMid.basicBlocks.length =
                          some trapBb := by
                        rw [hFlatDef]; dsimp
                        have hMapLen : loweredBbs.length = bMid.basicBlocks.length := map_length_eq _ _
                        have hApp := getElem?_append_right_add loweredBbs [trapBb] 0
                        rw [hMapLen, Nat.add_zero] at hApp
                        exact hApp
                      rw [hTrapAt]; rfl

private theorem assertLower_fuel_step_fwd {pMid pFlat : Program} {n : Nat} {s s' : StateExt}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat)
    (hInv : AssertLowerInv pMid s)
    (hMid : evalTupleAssertFuel pMid n s = .step s') :
    evalTupleAssertFuel pFlat n s = .step s' ∧ AssertLowerInv pMid s' := by
  induction n generalizing s with
  | zero =>
    dsimp [evalTupleAssertFuel] at hMid; dsimp [evalTupleAssertFuel]
    injection hMid with hEq; subst hEq
    exact ⟨rfl, hInv⟩
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hMid; dsimp [evalTupleAssertFuel]
    cases assertLower_step_rel hLow hInv with
    | inr hTrap =>
      cases hTrap.1 with
      | inl hP =>
        let ⟨_, hMidP⟩ := hP
        rw [hMidP] at hMid; cases hMid
      | inr hMidF =>
        rw [hMidF] at hMid; cases hMid
    | inl hSame =>
      rw [hSame.1]
      cases hSt : evalStepTupleAssert pMid 0 s with
      | done _ => rw [hSt] at hMid; cases hMid
      | fault _ => rw [hSt] at hMid; cases hMid
      | step s₁ =>
        rw [hSt] at hMid
        exact ih (assertLower_preserves_inv hLow hInv hSt) hMid

private theorem assertLower_fuel_ret_fwd {pMid pFlat : Program} {n : Nat} {s : StateExt} {out : Out}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat)
    (hInv : AssertLowerInv pMid s)
    (hMid : evalTupleAssertFuel pMid n s = .done (.ret out)) :
    evalTupleAssertFuel pFlat n s = .done (.ret out) := by
  induction n generalizing s with
  | zero => cases hMid
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hMid; dsimp [evalTupleAssertFuel]
    cases assertLower_step_rel hLow hInv with
    | inr hTrap =>
      cases hTrap.1 with
      | inl hP =>
        let ⟨_, hMidP⟩ := hP
        rw [hMidP] at hMid; cases hMid
      | inr hMidF =>
        rw [hMidF] at hMid; cases hMid
    | inl hSame =>
      rw [hSame.1]
      cases hSt : evalStepTupleAssert pMid 0 s with
      | done o => rw [hSt] at hMid; exact hMid
      | fault _ => rw [hSt] at hMid; cases hMid
      | step s₁ =>
        rw [hSt] at hMid
        exact ih (assertLower_preserves_inv hLow hInv hSt) hMid

private theorem assertLower_fuel_ret_bwd {pMid pFlat : Program} {m : Nat} {s : StateExt}
    {out : TerminalOutExt}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat)
    (hInv : AssertLowerInv pMid s)
    (hFlat : evalTupleAssertFuel pFlat m s = .done out) :
    (∃ o : Out, out = .ret o) ∧ evalTupleAssertFuel pMid m s = .done out := by
  induction m generalizing s with
  | zero => cases hFlat
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hFlat; dsimp [evalTupleAssertFuel]
    cases assertLower_step_rel hLow hInv with
    | inr hTrap =>
      let ⟨_, sTrap, hF1, hF2⟩ := hTrap
      rw [hF1] at hFlat
      cases k with
      | zero => cases hFlat
      | succ k' =>
        dsimp [evalTupleAssertFuel] at hFlat
        rw [hF2] at hFlat; cases hFlat
    | inl hSame =>
      let ⟨hStepEq, hNoPanic⟩ := hSame
      rw [hStepEq] at hFlat
      cases hSt : evalStepTupleAssert pMid 0 s with
      | fault _ => rw [hSt] at hFlat; cases hFlat
      | step s₁ =>
        rw [hSt] at hFlat
        exact ih (assertLower_preserves_inv hLow hInv hSt) hFlat
      | done o =>
        rw [hSt] at hFlat
        injection hFlat with hOEq; subst hOEq
        cases o with
        | ret rv => exact ⟨⟨rv, rfl⟩, rfl⟩
        | panic msg => exact False.elim (hNoPanic msg hSt)

private theorem assertLower_fuel_panic_to_fault {pMid pFlat : Program} {n : Nat}
    {s : StateExt} {msg : AssertKind}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat)
    (hInv : AssertLowerInv pMid s)
    (hMid : evalTupleAssertFuel pMid n s = .done (.panic msg)) :
    evalTupleAssertFuel pFlat (n + 1) s = .fault .undefined := by
  induction n generalizing s with
  | zero => cases hMid
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hMid
    cases assertLower_step_rel hLow hInv with
    | inl hSame =>
      let ⟨hStepEq, hNoPanic⟩ := hSame
      cases hSt : evalStepTupleAssert pMid 0 s with
      | fault _ => rw [hSt] at hMid; cases hMid
      | done o =>
        rw [hSt] at hMid; injection hMid with hEq; subst hEq
        exact False.elim (hNoPanic msg hSt)
      | step s₁ =>
        rw [hSt] at hMid
        change (match evalStepTupleAssert pFlat 0 s with
          | .step s' => evalTupleAssertFuel pFlat (k + 1) s'
          | .done out => .done out
          | .fault fk => .fault fk) = .fault .undefined
        rw [hStepEq, hSt]
        exact ih (assertLower_preserves_inv hLow hInv hSt) hMid
    | inr hTrap =>
      let ⟨_, sTrap, hF1, hF2⟩ := hTrap
      have h2 : evalTupleAssertFuel pFlat 2 s = .fault .undefined := by
        dsimp [evalTupleAssertFuel]; rw [hF1]; dsimp [evalTupleAssertFuel]; rw [hF2]
      exact evalTupleAssertFuel_fault_of_le h2
        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))

private theorem assertLower_fuel_fault_fwd {pMid pFlat : Program} {n : Nat}
    {s : StateExt} {fk : FaultKind}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat)
    (hInv : AssertLowerInv pMid s)
    (hMid : evalTupleAssertFuel pMid n s = .fault fk) :
    evalTupleAssertFuel pFlat (n + 1) s = .fault fk := by
  induction n generalizing s with
  | zero => cases hMid
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hMid
    cases assertLower_step_rel hLow hInv with
    | inl hSame =>
      let ⟨hStepEq, _⟩ := hSame
      cases hSt : evalStepTupleAssert pMid 0 s with
      | done _ => rw [hSt] at hMid; cases hMid
      | fault fk' =>
        rw [hSt] at hMid; injection hMid with hEq; subst hEq
        have h1 : evalTupleAssertFuel pFlat 1 s = .fault fk' := by
          dsimp [evalTupleAssertFuel]; rw [hStepEq, hSt]
        exact evalTupleAssertFuel_fault_of_le h1 (Nat.succ_le_succ (Nat.zero_le (k + 1)))
      | step s₁ =>
        rw [hSt] at hMid
        change (match evalStepTupleAssert pFlat 0 s with
          | .step s' => evalTupleAssertFuel pFlat (k + 1) s'
          | .done out => .done out
          | .fault fk'' => .fault fk'') = .fault fk
        rw [hStepEq, hSt]
        exact ih (assertLower_preserves_inv hLow hInv hSt) hMid
    | inr hTrap =>
      let ⟨hMidOr, sTrap, hF1, hF2⟩ := hTrap
      cases hMidOr with
      | inl hP =>
        let ⟨_, hMidP⟩ := hP
        rw [hMidP] at hMid; cases hMid
      | inr hMidF =>
        rw [hMidF] at hMid; injection hMid with hEq; subst hEq
        have h2 : evalTupleAssertFuel pFlat 2 s = .fault .undefined := by
          dsimp [evalTupleAssertFuel]; rw [hF1]; dsimp [evalTupleAssertFuel]; rw [hF2]
        exact evalTupleAssertFuel_fault_of_le h2
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))

private theorem assertLower_fuel_fault_bwd {pMid pFlat : Program} {m : Nat}
    {s : StateExt} {fk : FaultKind}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat)
    (hInv : AssertLowerInv pMid s)
    (hFlat : evalTupleAssertFuel pFlat m s = .fault fk) :
    (∃ k' : FaultKind, evalTupleAssertFuel pMid m s = .fault k') ∨
    (∃ msg : AssertKind, evalTupleAssertFuel pMid m s = .done (.panic msg)) := by
  induction m generalizing s with
  | zero => cases hFlat
  | succ k ih =>
    dsimp [evalTupleAssertFuel] at hFlat; dsimp [evalTupleAssertFuel]
    cases assertLower_step_rel hLow hInv with
    | inr hTrap =>
      cases hTrap.1 with
      | inl hP =>
        let ⟨msg, hMidP⟩ := hP
        rw [hMidP]; exact Or.inr ⟨msg, rfl⟩
      | inr hMidF =>
        rw [hMidF]; exact Or.inl ⟨.undefined, rfl⟩
    | inl hSame =>
      let ⟨hStepEq, _⟩ := hSame
      rw [hStepEq] at hFlat
      cases hSt : evalStepTupleAssert pMid 0 s with
      | done _ => rw [hSt] at hFlat; cases hFlat
      | fault k' => rw [hSt] at hFlat; exact Or.inl ⟨k', rfl⟩
      | step s₁ =>
        rw [hSt] at hFlat
        exact ih (assertLower_preserves_inv hLow hInv hSt) hFlat

private theorem assertLower_query_equiv {pMid pFlat : Program}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat) (q : Query) :
    (NoPanicAndWellFormedTupleAssert pFlat q ↔
      NoPanicAndWellFormedTupleAssert pMid q) ∧
    (∀ out : Out,
      BehaviorTupleAssert pFlat q (.ret out) ↔
        BehaviorTupleAssert pMid q (.ret out)) ∧
    (DivergesTupleAssert pFlat q ↔ DivergesTupleAssert pMid q) ∧
    ((∃ msg : AssertKind, BehaviorTupleAssert pMid q (.panic msg)) →
      ReachesResultTupleAssert pFlat q (.fault .undefined)) := by
  have hInit := assertLower_initState_eq hLow q
  cases hInitM : initStateTupleAssert pMid q with
  | error kErr =>
    have hInitF : initStateTupleAssert pFlat q = .error kErr := by rw [hInit, hInitM]
    have hNP : NoPanicAndWellFormedTupleAssert pFlat q ↔
        NoPanicAndWellFormedTupleAssert pMid q := by
      unfold NoPanicAndWellFormedTupleAssert WellFormedTupleAssert
      constructor
      · intro ⟨⟨⟨_, hOk, _⟩, _⟩, _⟩; rw [hInitF] at hOk; cases hOk
      · intro ⟨⟨⟨_, hOk, _⟩, _⟩, _⟩; rw [hInitM] at hOk; cases hOk
    have hRet : ∀ out : Out,
        BehaviorTupleAssert pFlat q (.ret out) ↔ BehaviorTupleAssert pMid q (.ret out) := by
      intro out; unfold BehaviorTupleAssert ReachesResultTupleAssert; rw [hInitF, hInitM]
    have hDiv : DivergesTupleAssert pFlat q ↔ DivergesTupleAssert pMid q := by
      unfold DivergesTupleAssert
      constructor
      · intro ⟨_, hOk, _⟩; rw [hInitF] at hOk; cases hOk
      · intro ⟨_, hOk, _⟩; rw [hInitM] at hOk; cases hOk
    have hPan : (∃ msg : AssertKind, BehaviorTupleAssert pMid q (.panic msg)) →
        ReachesResultTupleAssert pFlat q (.fault .undefined) := by
      intro ⟨msg, hB⟩
      unfold BehaviorTupleAssert ReachesResultTupleAssert at hB
      rw [hInitM] at hB; cases hB
    exact ⟨hNP, hRet, hDiv, hPan⟩
  | ok s₀ =>
    have hInitF : initStateTupleAssert pFlat q = .ok s₀ := by rw [hInit, hInitM]
    have hInv0 : AssertLowerInv pMid s₀ := assertLower_init_inv hInitM
    have hRet : ∀ out : Out,
        BehaviorTupleAssert pFlat q (.ret out) ↔ BehaviorTupleAssert pMid q (.ret out) := by
      intro out
      unfold BehaviorTupleAssert ReachesResultTupleAssert
      rw [hInitF, hInitM]
      constructor
      · intro ⟨sEnd, hR, hS⟩
        let ⟨m, hm⟩ := evalTupleAssertFuel_terminal_of_reaches hR hS
        have hMidDone := (assertLower_fuel_ret_bwd hLow hInv0 hm).2
        exact reaches_and_step_of_evalTupleAssertFuel_done hMidDone
      · intro ⟨sEnd, hR, hS⟩
        let ⟨n, hn⟩ := evalTupleAssertFuel_terminal_of_reaches hR hS
        have hFlatDone := assertLower_fuel_ret_fwd hLow hInv0 hn
        exact reaches_and_step_of_evalTupleAssertFuel_done hFlatDone
    have hNoFlatPanic : ∀ msg : AssertKind, ¬ BehaviorTupleAssert pFlat q (.panic msg) := by
      intro msg hB
      unfold BehaviorTupleAssert ReachesResultTupleAssert at hB
      rw [hInitF] at hB
      let ⟨sEnd, hR, hS⟩ := hB
      let ⟨m, hm⟩ := evalTupleAssertFuel_terminal_of_reaches hR hS
      let ⟨⟨o, hOEq⟩, _⟩ := assertLower_fuel_ret_bwd hLow hInv0 hm
      cases hOEq
    have hPanToFault : (∃ msg : AssertKind, BehaviorTupleAssert pMid q (.panic msg)) →
        ReachesResultTupleAssert pFlat q (.fault .undefined) := by
      intro ⟨msg, hB⟩
      unfold BehaviorTupleAssert ReachesResultTupleAssert at hB
      unfold ReachesResultTupleAssert
      rw [hInitM] at hB; rw [hInitF]
      let ⟨sEnd, hR, hS⟩ := hB
      let ⟨n, hn⟩ := evalTupleAssertFuel_terminal_of_reaches hR hS
      have hFl := assertLower_fuel_panic_to_fault hLow hInv0 hn
      exact reaches_and_step_of_evalTupleAssertFuel_fault hFl
    have hNP : NoPanicAndWellFormedTupleAssert pFlat q ↔
        NoPanicAndWellFormedTupleAssert pMid q := by
      unfold NoPanicAndWellFormedTupleAssert WellFormedTupleAssert
      constructor
      · intro ⟨⟨_, hNoF_flat⟩, _⟩
        refine ⟨⟨⟨s₀, hInitM, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_⟩
        · intro fk hFMid
          unfold ReachesResultTupleAssert at hFMid
          rw [hInitM] at hFMid
          let ⟨sEnd, hR, hS⟩ := hFMid
          let ⟨n, hn⟩ := evalTupleAssertFuel_terminal_of_reaches hR hS
          have hFFlat : ReachesResultTupleAssert pFlat q (.fault fk) := by
            unfold ReachesResultTupleAssert; rw [hInitF]
            exact reaches_and_step_of_evalTupleAssertFuel_fault (assertLower_fuel_fault_fwd hLow hInv0 hn)
          exact hNoF_flat fk hFFlat
        · intro msg hPMid
          exact hNoF_flat .undefined (hPanToFault ⟨msg, hPMid⟩)
      · intro ⟨⟨_, hNoF_mid⟩, hNoP_mid⟩
        refine ⟨⟨⟨s₀, hInitF, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, hNoFlatPanic⟩
        intro fk hFFlat
        unfold ReachesResultTupleAssert at hFFlat
        rw [hInitF] at hFFlat
        let ⟨sEnd, hR, hS⟩ := hFFlat
        let ⟨m, hm⟩ := evalTupleAssertFuel_terminal_of_reaches hR hS
        cases assertLower_fuel_fault_bwd hLow hInv0 hm with
        | inl hM =>
          let ⟨k', hk'⟩ := hM
          have hFMid : ReachesResultTupleAssert pMid q (.fault k') := by
            unfold ReachesResultTupleAssert; rw [hInitM]
            exact reaches_and_step_of_evalTupleAssertFuel_fault hk'
          exact hNoF_mid k' hFMid
        | inr hP =>
          let ⟨msg, hpm⟩ := hP
          have hPMid : BehaviorTupleAssert pMid q (.panic msg) := by
            unfold BehaviorTupleAssert ReachesResultTupleAssert; rw [hInitM]
            exact reaches_and_step_of_evalTupleAssertFuel_done hpm
          exact hNoP_mid msg hPMid
    have hDiv : DivergesTupleAssert pFlat q ↔ DivergesTupleAssert pMid q := by
      unfold DivergesTupleAssert
      constructor
      · intro ⟨sF, hOkF, hAllF⟩
        rw [hInitF] at hOkF; injection hOkF with hEq; subst hEq
        refine ⟨s₀, hInitM, ?_⟩
        intro n
        cases hMidN : evalTupleAssertFuel pMid n s₀ with
        | step s' => exact ⟨s', rfl⟩
        | fault fk =>
          have hFl := assertLower_fuel_fault_fwd hLow hInv0 hMidN
          let ⟨s', hStF⟩ := hAllF (n + 1)
          rw [hFl] at hStF; cases hStF
        | done out =>
          cases out with
          | ret o =>
            have hDn := assertLower_fuel_ret_fwd hLow hInv0 hMidN
            let ⟨s', hStF⟩ := hAllF n
            rw [hDn] at hStF; cases hStF
          | panic msg =>
            have hFl := assertLower_fuel_panic_to_fault hLow hInv0 hMidN
            let ⟨s', hStF⟩ := hAllF (n + 1)
            rw [hFl] at hStF; cases hStF
      · intro ⟨sM, hOkM, hAllM⟩
        rw [hInitM] at hOkM; injection hOkM with hEq; subst hEq
        refine ⟨s₀, hInitF, ?_⟩
        intro n
        let ⟨s', hStM⟩ := hAllM n
        exact ⟨s', (assertLower_fuel_step_fwd hLow hInv0 hStM).1⟩
    exact ⟨hNP, hRet, hDiv, hPanToFault⟩

private theorem lowerAssertsToSwitchUnreachable_entryProgForBody {pMid pFlat : Program}
    (defId : DefId) (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat) :
    lowerAssertsToSwitchUnreachable (entryProgForBody pMid defId) =
      some (entryProgForBody pFlat defId) := by
  unfold entryProgForBody
  unfold lowerAssertsToSwitchUnreachable at hLow; unfold lowerAssertsToSwitchUnreachable
  dsimp
  cases hMap : listMapOption lowerAssertsInBody pMid.bodies with
  | none => rw [hMap] at hLow; cases hLow
  | some bodies' =>
    rw [hMap] at hLow; injection hLow with hEq; subst hEq; rfl

private theorem lowerAssertsToSwitchUnreachable_unitProgForDef {pMid pFlat : Program}
    (u : DefId) (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat) :
    lowerAssertsToSwitchUnreachable (unitProgForDef pMid u) =
      some (unitProgForDef pFlat u) := by
  unfold unitProgForDef
  unfold lowerAssertsToSwitchUnreachable at hLow; unfold lowerAssertsToSwitchUnreachable
  dsimp
  cases hMap : listMapOption lowerAssertsInBody pMid.bodies with
  | none => rw [hMap] at hLow; cases hLow
  | some bodies' =>
    rw [hMap] at hLow; injection hLow with hEq; subst hEq; rfl

private theorem lowerAssertsToSwitchUnreachable_metadataCompat {pMid pFlat : Program}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat) :
    ProgramMetadataCompat pMid pFlat = true := by
  unfold lowerAssertsToSwitchUnreachable at hLow
  cases hMap : listMapOption lowerAssertsInBody pMid.bodies with
  | none => rw [hMap] at hLow; cases hLow
  | some bodies' =>
    rw [hMap] at hLow; injection hLow with hEq; subst hEq
    unfold ProgramMetadataCompat
    refine bool_and_intro (programHeaderEq_of_eq rfl rfl rfl rfl) ?_
    dsimp
    have hRelMap : ∀ (bs1 bs2 : List Body),
        listMapOption lowerAssertsInBody bs1 = some bs2 →
        listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) bs1 bs2 = true := by
      intro bs1
      induction bs1 with
      | nil =>
        intro bs2 hM
        injection hM with hE; subst hE; rfl
      | cons b1 r1 ih =>
        intro bs2 hM
        dsimp [listMapOption] at hM
        cases hB1 : lowerAssertsInBody b1 with
        | none => rw [hB1] at hM; cases hM
        | some b2 =>
          rw [hB1] at hM
          cases hR1 : listMapOption lowerAssertsInBody r1 with
          | none => rw [hR1] at hM; cases hM
          | some r2 =>
            rw [hR1] at hM; injection hM with hE; subst hE
            let ⟨_, _, _, hIdEq, _⟩ := lowerAssertsInBody_props hB1
            dsimp [listRel]
            rw [hIdEq, stringBeq_refl, Bool.true_and]
            exact ih r2 hR1
    exact hRelMap pMid.bodies bodies' hMap

private theorem assertLower_apply_sound {pMid pFlat : Program}
    (hLow : lowerAssertsToSwitchUnreachable pMid = some pFlat) :
    NoPanicSemanticEquivTupleAssert pMid pFlat ∧
    ProgramMetadataCompat pMid pFlat = true ∧
    (∀ q : Query,
      (∃ msg : AssertKind, BehaviorTupleAssert pMid q (.panic msg)) →
        ReachesResultTupleAssert pFlat q (.fault .undefined)) := by
  have hQ := fun q => assertLower_query_equiv hLow q
  refine ⟨⟨fun q => ⟨(hQ q).1, (hQ q).2.1, (hQ q).2.2.1⟩, ?_, ?_⟩,
          lowerAssertsToSwitchUnreachable_metadataCompat hLow,
          fun q => (hQ q).2.2.2⟩
  · intro q post
    let ⟨hNP, hRet, _, _⟩ := hQ q
    unfold SatisfiesPostNoPanicTupleAssert
    exact ⟨fun ⟨hW, hB⟩ => ⟨hNP.mp hW, fun o ho => hB o ((hRet o).mpr ho)⟩,
           fun ⟨hW, hB⟩ => ⟨hNP.mpr hW, fun o ho => hB o ((hRet o).mp ho)⟩⟩
  · intro defId bMid bFlat safetyPre hbM hbF
    have hEntLow := lowerAssertsToSwitchUnreachable_entryProgForBody defId hLow
    unfold lowerAssertsToSwitchUnreachable at hLow
    cases hMap : listMapOption lowerAssertsInBody pMid.bodies with
    | none => rw [hMap] at hLow; cases hLow
    | some bodies' =>
      rw [hMap] at hLow; injection hLow with hPEq; subst hPEq
      let ⟨bFlat', hbF', hBF⟩ := listMapOption_getElem?_left hMap hbM
      dsimp at hbF
      rw [hbF] at hbF'; injection hbF' with hBEq; subst hBEq
      let ⟨hArgEq, hLocEq, hUnsEq, hIdEq, _⟩ := lowerAssertsInBody_props hBF
      have hStaticEq : BodyStaticAdmittedTupleAssert { pMid with bodies := bodies' } bFlat =
          BodyStaticAdmittedTupleAssert pMid bMid := by
        unfold BodyStaticAdmittedTupleAssert
        dsimp
        rw [hIdEq, lowerAssertsInBody_basicBlocks_isEmpty hBF, hArgEq, hLocEq,
            lowerAssertsInBody_storageAnnotationsInBounds hBF]
      unfold BodyVerifiedNoPanicTupleAssert ValidEntryArgsTupleAssert
      rw [hStaticEq, hLocEq, hArgEq, hUnsEq]
      constructor
      · intro ⟨_, hAdm, hAll⟩
        refine ⟨hbM, hAdm, ?_⟩
        intro args hV hSafe
        exact (assertLower_query_equiv hEntLow { args := args }).1.mp (hAll args hV hSafe)
      · intro ⟨_, hAdm, hAll⟩
        refine ⟨hbF, hAdm, ?_⟩
        intro args hV hSafe
        exact (assertLower_query_equiv hEntLow { args := args }).1.mpr (hAll args hV hSafe)

private theorem checkMirAssertLower_sound {pMid pFlat : Program}
    (hLower : checkMirAssertLower pMid pFlat = true) :
    NoPanicSemanticEquivTupleAssert pMid pFlat ∧
    ProgramMetadataCompat pMid pFlat = true ∧
    (∀ q : Query,
      (∃ msg : AssertKind, BehaviorTupleAssert pMid q (.panic msg)) →
        ReachesResultTupleAssert pFlat q (.fault .undefined)) ∧
    (∀ u : DefId,
      NoPanicSemanticEquivTupleAssert (unitProgForDef pMid u) (unitProgForDef pFlat u)) := by
  unfold checkMirAssertLower at hLower
  cases hLow : lowerAssertsToSwitchUnreachable pMid with
  | none => rw [hLow] at hLower; cases hLower
  | some pOut =>
    rw [hLow] at hLower
    have hEq := programEq_eq hLower; subst hEq
    let ⟨hNP, hMeta, hPan⟩ := assertLower_apply_sound hLow
    refine ⟨hNP, hMeta, hPan, ?_⟩
    intro u
    exact (assertLower_apply_sound (lowerAssertsToSwitchUnreachable_unitProgForDef u hLow)).1

/-! #### Section 5: Theorem 4 & Theorem 5 Assembly -/

private theorem mirSroaAndAssertLower_noPanic_reduces_to_trusted_mir_sliceC
    (sroaTrace : SroaTrace) (pSrc pMid pFlat : Program) (specs : Specs)
    (hSroa : checkMirSroaTrace sroaTrace pSrc pMid = true)
    (hLower : checkMirAssertLower pMid pFlat = true)
    (hFlat : isFlatAssertFreeProgram pFlat = true)
    (hSpec : SpecsPropertyNoPanicInvariant specs) :
    (∀ q : Query,
      (NoPanicAndWellFormedTupleAssert pSrc q ↔ WellFormed pFlat q) ∧
      (∀ out : Out,
        BehaviorTupleAssert pSrc q (.ret out) ↔
          Behavior pFlat q (.returned out)) ∧
      (DivergesTupleAssert pSrc q ↔ Diverges pFlat q) ∧
      ((∃ msg : AssertKind, BehaviorTupleAssert pSrc q (.panic msg)) →
        ReachesResult pFlat q (.fault .undefined))) ∧
    (CrateTheoremNoPanicTupleAssert ⟨pSrc, specs⟩ ↔
      CrateTheorem ⟨pFlat, specs⟩) ∧
    (UnitTheoremNoPanicTupleAssert ⟨pSrc, specs⟩ ↔
      UnitTheorem ⟨pFlat, specs⟩) ∧
    (∀ u : DefId,
      UnitTheoremNoPanicTupleAssert ⟨unitProgForDef pSrc u, specs⟩ ↔
        UnitTheorem ⟨unitProgForDef pFlat u, specs⟩) := by
  let ⟨hFullSroa, hMetaSroa, hUnitSroa⟩ := checkMirSroaTrace_sound hSroa
  have hNPSroa := noPanicEquiv_of_fullSemanticEquivTupleAssert hFullSroa
  let ⟨hNPLow, hMetaLow, hPanLow, hUnitLow⟩ := checkMirAssertLower_sound hLower
  have hNPChain := noPanicSemanticEquivTupleAssert_trans hNPSroa hNPLow
    (programMetadataCompat_bodies_len hMetaSroa)
  have hMetaChain := programMetadataCompat_trans hMetaSroa hMetaLow
  have hThm1 := (tupleAssert_conservative_extension_exact_sliceA pFlat).2 hFlat
  let ⟨hCrateIff, hUnitIff⟩ := crateAndUnitTheoremNoPanicTupleAssert_iff hMetaChain hNPChain hSpec
  let ⟨hFlatCrate, hFlatUnit⟩ := hThm1.2.2.2 specs
  refine ⟨?_, Iff.trans hCrateIff hFlatCrate, Iff.trans hUnitIff hFlatUnit, ?_⟩
  · intro q
    let ⟨hNP_q, hRet_q, hDiv_q⟩ := hNPChain.1 q
    let ⟨_, hFlatNP_q, _, hFlatRet_q, _, hFlatFault_q, hFlatDiv_q⟩ := hThm1.1 q
    refine ⟨Iff.trans hNP_q.symm hFlatNP_q,
            fun out => Iff.trans (hRet_q out).symm (hFlatRet_q out),
            Iff.trans hDiv_q.symm hFlatDiv_q,
            ?_⟩
    intro ⟨msg, hPanSrc⟩
    have hPanMid : BehaviorTupleAssert pMid q (.panic msg) :=
      ((hFullSroa.1 q).2.2.1 (.panic msg)).mpr hPanSrc
    exact (hFlatFault_q .undefined).mp (hPanLow q ⟨msg, hPanMid⟩)
  · intro u
    have hFlatU : isFlatAssertFreeProgram (unitProgForDef pFlat u) = true := hFlat
    have hThm1U := (tupleAssert_conservative_extension_exact_sliceA (unitProgForDef pFlat u)).2 hFlatU
    have hNPU := noPanicSemanticEquivTupleAssert_trans
      (noPanicEquiv_of_fullSemanticEquivTupleAssert (hUnitSroa u))
      (hUnitLow u)
      (programMetadataCompat_bodies_len (programMetadataCompat_unitProgForDef u hMetaSroa))
    have hMetaU := programMetadataCompat_unitProgForDef u hMetaChain
    let ⟨_, hUnitUIff⟩ := crateAndUnitTheoremNoPanicTupleAssert_iff hMetaU hNPU hSpec
    exact Iff.trans hUnitUIff (hThm1U.2.2.2 specs).2

private theorem noPanicEquiv_of_flat_fullSemanticEquiv {pFlat pOpt : Program}
    (hFlatMid : isFlatAssertFreeProgram pFlat = true)
    (hFlatOpt : isFlatAssertFreeProgram pOpt = true)
    (hPostOpt : FullSemanticEquiv pFlat pOpt) :
    NoPanicSemanticEquivTupleAssert pFlat pOpt := by
  have hTFlat := (tupleAssert_conservative_extension_exact_sliceA pFlat).2 hFlatMid
  have hTOpt := (tupleAssert_conservative_extension_exact_sliceA pOpt).2 hFlatOpt
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let ⟨hWf, hBeh, _, hDiv⟩ := hPostOpt.1 q
    let ⟨_, hNP_F, _, hRet_F, _, _, hDiv_F⟩ := hTFlat.1 q
    let ⟨_, hNP_O, _, hRet_O, _, _, hDiv_O⟩ := hTOpt.1 q
    exact ⟨Iff.trans hNP_O (Iff.trans hWf hNP_F.symm),
           fun out => Iff.trans (hRet_O out) (Iff.trans (hBeh (.returned out)) (hRet_F out).symm),
           Iff.trans hDiv_O (Iff.trans hDiv hDiv_F.symm)⟩
  · intro q post
    exact Iff.trans (hTOpt.2.1 q post)
      (Iff.trans (hPostOpt.2.1 q _) (hTFlat.2.1 q post).symm)
  · intro defId bFlat bOpt safetyPre hbF hbO
    exact Iff.trans (hTOpt.2.2.1 defId bOpt safetyPre)
      (Iff.trans (hPostOpt.2.2 defId bFlat bOpt safetyPre hbF hbO)
        (hTFlat.2.2.1 defId bFlat safetyPre).symm)

private theorem mirSroaAssert_then_optPipeline_vc_transport_sliceC
    (sroaTrace : SroaTrace)
    (pSrc pSroa pFolded pFlat pOpt : Program) (specs : Specs)
    (hSroa : checkMirSroaTrace sroaTrace pSrc pSroa = true)
    (hFold : checkMirAssertConstFold pSroa pFolded = true)
    (hLower : checkMirAssertLower pFolded pFlat = true)
    (hFlatMid : isFlatAssertFreeProgram pFlat = true)
    (hFlatOpt : isFlatAssertFreeProgram pOpt = true)
    (hMeta : ProgramMetadataCompat pFlat pOpt = true)
    (hPostOpt : FullSemanticEquiv pFlat pOpt)
    (hSpec : SpecsPropertyNoPanicInvariant specs) :
    (∀ q : Query,
      (NoPanicAndWellFormedTupleAssert pSrc q ↔ WellFormed pOpt q) ∧
      (∀ out : Out,
        BehaviorTupleAssert pSrc q (.ret out) ↔
          Behavior pOpt q (.returned out)) ∧
      (DivergesTupleAssert pSrc q ↔ Diverges pOpt q)) ∧
    (CrateTheoremNoPanicTupleAssert ⟨pSrc, specs⟩ ↔
      CrateTheorem ⟨pOpt, specs⟩) ∧
    (UnitTheoremNoPanicTupleAssert ⟨pSrc, specs⟩ ↔
      UnitTheorem ⟨pOpt, specs⟩) := by
  let ⟨hFull1, hMeta1, _⟩ := checkMirSroaTrace_sound hSroa
  have hNP1 := noPanicEquiv_of_fullSemanticEquivTupleAssert hFull1
  have hFull2 := mirAssertConstFold_sound_bidirectional_iff_sliceC pSroa pFolded hFold
  have hNP2 := noPanicEquiv_of_fullSemanticEquivTupleAssert hFull2
  have hMeta2 := checkMirAssertConstFold_metadataCompat hFold
  let ⟨hNP3, hMeta3, _, _⟩ := checkMirAssertLower_sound hLower
  have hNP4 := noPanicEquiv_of_flat_fullSemanticEquiv hFlatMid hFlatOpt hPostOpt
  have hNP12 := noPanicSemanticEquivTupleAssert_trans hNP1 hNP2
    (programMetadataCompat_bodies_len hMeta1)
  have hMeta12 := programMetadataCompat_trans hMeta1 hMeta2
  have hNP123 := noPanicSemanticEquivTupleAssert_trans hNP12 hNP3
    (programMetadataCompat_bodies_len hMeta12)
  have hMeta123 := programMetadataCompat_trans hMeta12 hMeta3
  have hNPAll := noPanicSemanticEquivTupleAssert_trans hNP123 hNP4
    (programMetadataCompat_bodies_len hMeta123)
  have hMetaAll := programMetadataCompat_trans hMeta123 hMeta
  have hTOpt := (tupleAssert_conservative_extension_exact_sliceA pOpt).2 hFlatOpt
  let ⟨hCrateIff, hUnitIff⟩ := crateAndUnitTheoremNoPanicTupleAssert_iff hMetaAll hNPAll hSpec
  let ⟨hOptCrate, hOptUnit⟩ := hTOpt.2.2.2 specs
  refine ⟨?_, Iff.trans hCrateIff hOptCrate, Iff.trans hUnitIff hOptUnit⟩
  intro q
  let ⟨hNP_q, hRet_q, hDiv_q⟩ := hNPAll.1 q
  let ⟨_, hOptNP_q, _, hOptRet_q, _, _, hOptDiv_q⟩ := hTOpt.1 q
  exact ⟨Iff.trans hNP_q.symm hOptNP_q,
         fun out => Iff.trans (hRet_q out).symm (hOptRet_q out),
         Iff.trans hDiv_q.symm hOptDiv_q⟩

/-! ## Part III: Five Core Target Theorems Directly Over Unmodified `Trusted.MirSemantics` -/

/-- **Theorem 1 (Exact Conservative Extension of `M_tupleAssert` Over
Unmodified `Trusted.MirSemantics`):**
1. On any `p : Program`, any `c : Choice`, and any `s : State` whose active
   body (if in bounds) is flat and assert-free (`stepIsFlatAssertFree p s =
   true`), `evalStepTupleAssert p c (embedState s)` matches
   `liftStepResult (evalStep p c s)` identically.
2. Whenever `isFlatAssertFreeProgram p = true`, `WellFormedTupleAssert`,
   `NoPanicAndWellFormedTupleAssert`, `BehaviorTupleAssert`,
   `ReachesResultTupleAssert (.fault k)`, `DivergesTupleAssert`,
   `SatisfiesPostNoPanicTupleAssert`, `BodyVerifiedNoPanicTupleAssert`,
   `CrateTheoremNoPanicTupleAssert`, and `UnitTheoremNoPanicTupleAssert` are
   bidirectionally equivalent (`↔`) to Anneal's unmodified
   `Trusted.MirSemantics` judgments (and no panic outcome is reachable). -/
theorem tupleAssert_conservative_extension_exact
    (p : Program) :
    (∀ (c : Choice) (s : State),
      stepIsFlatAssertFree p s = true →
      evalStepTupleAssert p c (embedState s) =
        liftStepResult (evalStep p c s)) ∧
    (isFlatAssertFreeProgram p = true →
      (∀ q : Query,
        (WellFormedTupleAssert p q ↔ WellFormed p q) ∧
        (NoPanicAndWellFormedTupleAssert p q ↔ WellFormed p q) ∧
        (∀ msg : AssertKind, ¬ BehaviorTupleAssert p q (.panic msg)) ∧
        (∀ out : Out,
          BehaviorTupleAssert p q (.ret out) ↔
            Behavior p q (.returned out)) ∧
        (∀ out : TerminalOut,
          Behavior p q out ↔
            match out with
            | .returned o => BehaviorTupleAssert p q (.ret o)
            | .unwound _ => False) ∧
        (∀ k : FaultKind,
          ReachesResultTupleAssert p q (.fault k) ↔
            ReachesResult p q (.fault k)) ∧
        (DivergesTupleAssert p q ↔ Diverges p q)) ∧
      (∀ (q : Query) (post : Out → Prop),
        SatisfiesPostNoPanicTupleAssert p q post ↔
          SatisfiesPost p q (fun out =>
            match out with | .returned o => post o | .unwound _ => False)) ∧
      (∀ (defId : DefId) (body : Body) (safetyPre : List Val → Prop),
        BodyVerifiedNoPanicTupleAssert p defId body safetyPre ↔
          BodyVerified p defId body safetyPre) ∧
      (∀ specs : Specs,
        (CrateTheoremNoPanicTupleAssert ⟨p, specs⟩ ↔
          CrateTheorem ⟨p, specs⟩) ∧
        (UnitTheoremNoPanicTupleAssert ⟨p, specs⟩ ↔
          UnitTheorem ⟨p, specs⟩))) := by
  exact tupleAssert_conservative_extension_exact_sliceA p

/-- **Theorem 2 (Certified Tuple & Unsigned `*WithOverflow` `SROA`
Bidirectional Soundness):**
For any `plan : SroaTuplePlan`, `checkMirSroaTuple plan pSrc pTgt = true`
implies `FullSemanticEquivTupleAssert pSrc pTgt` (`↔` across well-formedness,
panic-freedom, exact return and panic outcomes, exact fault kinds, divergence,
postconditions, and per-body verification, including self-referencing overflow
carries, `Operand.move` aliasing, and `DeadLocal` fault ordering). -/
theorem mirSroaTuple_sound_bidirectional_iff
    (plan : SroaTuplePlan) (pSrc pTgt : Program)
    (hPlan : checkMirSroaTuple plan pSrc pTgt = true) :
    FullSemanticEquivTupleAssert pSrc pTgt := by
  exact mirSroaTuple_sound_bidirectional_iff_sliceB plan pSrc pTgt hPlan

/-- **Theorem 3 (Constant-True `Assert` Folding Bidirectional Soundness):**
For any `pSrc pTgt : Program`, `checkMirAssertConstFold pSrc pTgt = true`
implies `FullSemanticEquivTupleAssert pSrc pTgt` (`↔` across all
`M_tupleAssert` judgments). -/
theorem mirAssertConstFold_sound_bidirectional_iff
    (pSrc pTgt : Program)
    (hFold : checkMirAssertConstFold pSrc pTgt = true) :
    FullSemanticEquivTupleAssert pSrc pTgt := by
  exact mirAssertConstFold_sound_bidirectional_iff_sliceC pSrc pTgt hFold

/-- **Theorem 4 (Tuple `SROA` + `Assert` Lowering Reduction Into Anneal's
Unmodified `Trusted.MirSemantics`):**
Whenever `checkMirSroaTrace sroaTrace pSrc pMid = true`,
`checkMirAssertLower pMid pFlat = true`, `isFlatAssertFreeProgram pFlat = true`,
and `SpecsPropertyNoPanicInvariant specs`, panic-free and UB-free verification
of `pSrc` in `M_tupleAssert` (`NoPanicAndWellFormedTupleAssert`, return
`Behavior`, `Diverges`, `CrateTheoremNoPanicTupleAssert`, and
`UnitTheoremNoPanicTupleAssert` across both whole-crate subjects and arbitrary
proof units `u : DefId`) reduces bidirectionally (`↔`) directly to Anneal's
unmodified `Trusted.MirSemantics.{WellFormed, Behavior, Diverges, CrateTheorem,
UnitTheorem}` on `pFlat`, while any defined `Assert` panic in `pSrc` maps to
`.fault .undefined` in `pFlat`. -/
theorem mirSroaAndAssertLower_noPanic_reduces_to_trusted_mir
    (sroaTrace : SroaTrace) (pSrc pMid pFlat : Program) (specs : Specs)
    (hSroa : checkMirSroaTrace sroaTrace pSrc pMid = true)
    (hLower : checkMirAssertLower pMid pFlat = true)
    (hFlat : isFlatAssertFreeProgram pFlat = true)
    (hSpec : SpecsPropertyNoPanicInvariant specs) :
    (∀ q : Query,
      (NoPanicAndWellFormedTupleAssert pSrc q ↔ WellFormed pFlat q) ∧
      (∀ out : Out,
        BehaviorTupleAssert pSrc q (.ret out) ↔
          Behavior pFlat q (.returned out)) ∧
      (DivergesTupleAssert pSrc q ↔ Diverges pFlat q) ∧
      ((∃ msg : AssertKind, BehaviorTupleAssert pSrc q (.panic msg)) →
        ReachesResult pFlat q (.fault .undefined))) ∧
    (CrateTheoremNoPanicTupleAssert ⟨pSrc, specs⟩ ↔
      CrateTheorem ⟨pFlat, specs⟩) ∧
    (UnitTheoremNoPanicTupleAssert ⟨pSrc, specs⟩ ↔
      UnitTheorem ⟨pFlat, specs⟩) ∧
    (∀ u : DefId,
      UnitTheoremNoPanicTupleAssert ⟨unitProgForDef pSrc u, specs⟩ ↔
        UnitTheorem ⟨unitProgForDef pFlat u, specs⟩) := by
  exact mirSroaAndAssertLower_noPanic_reduces_to_trusted_mir_sliceC sroaTrace pSrc pMid pFlat specs hSroa hLower hFlat hSpec

/-- **Theorem 5 (Vertical Composition With Post-Lowering `Trusted.MirSemantics`
Optimization Pipelines):**
Composing `SroaTrace` (`pSrc -> pSroa`), optional constant-true `Assert`
folding (`pSroa -> pFolded`), `Assert` lowering (`pFolded -> pFlat`), and any
post-lowering intraprocedural equivalence `FullSemanticEquiv pFlat pOpt` (such
as the 5-family `MirOptTrace` pipeline in `F1-5`--`F1-9`) preserving flat
assert-freedom and program metadata transports `NoPanicAndWellFormedTupleAssert`,
return `Behavior`, `Diverges`, `CrateTheoremNoPanicTupleAssert`, and
`UnitTheoremNoPanicTupleAssert` bidirectionally (`↔`) directly to unmodified
`Trusted.MirSemantics` on `pOpt`. -/
theorem mirSroaAssert_then_optPipeline_vc_transport
    (sroaTrace : SroaTrace)
    (pSrc pSroa pFolded pFlat pOpt : Program) (specs : Specs)
    (hSroa : checkMirSroaTrace sroaTrace pSrc pSroa = true)
    (hFold : checkMirAssertConstFold pSroa pFolded = true)
    (hLower : checkMirAssertLower pFolded pFlat = true)
    (hFlatMid : isFlatAssertFreeProgram pFlat = true)
    (hFlatOpt : isFlatAssertFreeProgram pOpt = true)
    (hMeta : ProgramMetadataCompat pFlat pOpt = true)
    (hPostOpt : FullSemanticEquiv pFlat pOpt)
    (hSpec : SpecsPropertyNoPanicInvariant specs) :
    (∀ q : Query,
      (NoPanicAndWellFormedTupleAssert pSrc q ↔ WellFormed pOpt q) ∧
      (∀ out : Out,
        BehaviorTupleAssert pSrc q (.ret out) ↔
          Behavior pOpt q (.returned out)) ∧
      (DivergesTupleAssert pSrc q ↔ Diverges pOpt q)) ∧
    (CrateTheoremNoPanicTupleAssert ⟨pSrc, specs⟩ ↔
      CrateTheorem ⟨pOpt, specs⟩) ∧
    (UnitTheoremNoPanicTupleAssert ⟨pSrc, specs⟩ ↔
      UnitTheorem ⟨pOpt, specs⟩) := by
  exact mirSroaAssert_then_optPipeline_vc_transport_sliceC sroaTrace pSrc pSroa pFolded pFlat pOpt specs hSroa hFold hLower hFlatMid hFlatOpt hMeta hPostOpt hSpec

/-! ## Part IV: Deterministic Adequacy, Sharpness Counterexamples (`CE1`--`CE10`), & `checked_add_pair` Witness (`0` `sorry`) -/

/-! ### Deterministic Fuel-Indexed Adequacy for Unmodified `Trusted.MirSemantics` -/

noncomputable def execOutcome (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) : Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
    match evalStep p 0 s with
    | .step s' => execOutcome p onDone onFault fuel s'
    | .done out => onDone out
    | .fault k => onFault k

noncomputable def execReturns (p : Program) (fuel : Nat) (q : Query)
    (expected : Val) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ =>
    execOutcome p (fun out => out = .returned ⟨expected, ⟨[]⟩⟩)
      (fun _ => False) fuel s₀

noncomputable def execFaults (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initState p q with
  | .error k => k = expected
  | .ok s₀ =>
    execOutcome p (fun _ => False) (fun k => k = expected) fuel s₀

theorem reaches_head_det {p : Program} {s₁ s₂ s₃ : State}
    (hFirst : Step p s₁ (.step s₂)) (hRest : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction hRest with
  | refl => exact Reaches.tail (Reaches.refl s₁) hFirst
  | tail _ hLast ih => exact Reaches.tail ih hLast

theorem execOutcome_reaches_inv {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s₁ s₂ : State} {fuel : Nat}
    (hExec : execOutcome p onDone onFault fuel s₁)
    (hReach : Reaches p s₁ s₂) :
    ∃ fuel', execOutcome p onDone onFault fuel' s₂ := by
  induction hReach with
  | refl => exact ⟨fuel, hExec⟩
  | tail _ hStep ih =>
    let ⟨f, hf⟩ := ih
    cases f with
    | zero => exact False.elim hf
    | succ f' =>
      let ⟨c, hc, hEval⟩ := hStep
      have hc0 : c = 0 := hc
      subst hc0
      dsimp [execOutcome] at hf
      rw [hEval] at hf
      exact ⟨f', hf⟩

theorem execOutcome_terminal {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (hExec : execOutcome p onDone onFault fuel s) :
    ∃ sEnd res, Reaches p s sEnd ∧ Step p sEnd res ∧
      match res with
      | .step _ => False
      | .done out => onDone out
      | .fault k => onFault k := by
  induction fuel generalizing s with
  | zero => exact False.elim hExec
  | succ f ih =>
    dsimp [execOutcome] at hExec
    cases hEval : evalStep p 0 s with
    | step s' =>
      rw [hEval] at hExec
      let ⟨sEnd, res, hR, hT, hPost⟩ := ih hExec
      exact ⟨sEnd, res, reaches_head_det ⟨0, rfl, hEval⟩ hR, hT, hPost⟩
    | done out =>
      rw [hEval] at hExec
      exact ⟨s, .done out, Reaches.refl s, ⟨0, rfl, hEval⟩, hExec⟩
    | fault k =>
      rw [hEval] at hExec
      exact ⟨s, .fault k, Reaches.refl s, ⟨0, rfl, hEval⟩, hExec⟩

theorem positiveCanary_of_execReturns {p : Program} {fuel : Nat}
    {q : Query} {expected : Val}
    (h : execReturns p fuel q expected) :
    PositiveCanaryClaim p q expected := by
  unfold execReturns at h
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_⟩
    · intro k hFault
      change (match initState p q with
        | .error k' => StepResult.fault k = .fault k'
        | .ok sInit => ∃ s, Reaches p sInit s ∧ Step p s (.fault k)) at hFault
      rw [hInit] at hFault
      let ⟨sF, hReach, c, hc, hEval⟩ := hFault
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := execOutcome_reaches_inv h hReach
      cases f' with
      | zero => exact hf'
      | succ f'' =>
        dsimp [execOutcome] at hf'
        rw [hEval] at hf'
        exact hf'
    · change (match initState p q with
        | .error k' =>
          (StepResult.done (TerminalOut.returned ⟨expected, ⟨[]⟩⟩) :
            StepResult State TerminalOut) = .fault k'
        | .ok sInit =>
          ∃ s, Reaches p sInit s ∧
            Step p s (.done (.returned ⟨expected, ⟨[]⟩⟩)))
      rw [hInit]
      let ⟨sEnd, res, hR, hStep, hRes⟩ := execOutcome_terminal h
      cases res with
      | step _ => exact False.elim hRes
      | fault _ => exact False.elim hRes
      | done out =>
        subst hRes
        exact ⟨sEnd, hR, hStep⟩

theorem negativeCanary_of_execFaults {p : Program} {fuel : Nat}
    {q : Query} {expectedFault otherFault : FaultKind}
    (hNe : otherFault ≠ expectedFault)
    (h : execFaults p fuel q expectedFault) :
    NegativeCanaryClaim p q expectedFault otherFault := by
  unfold execFaults at h
  cases hInit : initState p q with
  | error k =>
    rw [hInit] at h
    subst h
    refine ⟨?_, ?_, ?_⟩
    · change (match initState p q with
        | .error k' => StepResult.fault k = .fault k'
        | .ok sInit => ∃ s, Reaches p sInit s ∧ Step p s (.fault k))
      rw [hInit]
    · intro hOther
      change (match initState p q with
        | .error k' => StepResult.fault otherFault = .fault k'
        | .ok sInit =>
          ∃ s, Reaches p sInit s ∧ Step p s (.fault otherFault)) at hOther
      rw [hInit] at hOther
      cases hOther
      exact hNe rfl
    · intro hWf
      let ⟨⟨_, hOk, _⟩, _⟩ := hWf
      rw [hInit] at hOk
      cases hOk
  | ok s₀ =>
    rw [hInit] at h
    have hReachExp : ReachesResult p q (.fault expectedFault) := by
      change (match initState p q with
        | .error k' => StepResult.fault expectedFault = .fault k'
        | .ok sInit =>
          ∃ s, Reaches p sInit s ∧ Step p s (.fault expectedFault))
      rw [hInit]
      let ⟨sEnd, res, hR, hStep, hRes⟩ := execOutcome_terminal h
      cases res with
      | step _ => exact False.elim hRes
      | done _ => exact False.elim hRes
      | fault k =>
        subst hRes
        exact ⟨sEnd, hR, hStep⟩
    refine ⟨hReachExp, ?_, ?_⟩
    · intro hOther
      change (match initState p q with
        | .error k' => StepResult.fault otherFault = .fault k'
        | .ok sInit =>
          ∃ s, Reaches p sInit s ∧ Step p s (.fault otherFault)) at hOther
      rw [hInit] at hOther
      let ⟨sF, hReach, c, hc, hEval⟩ := hOther
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := execOutcome_reaches_inv h hReach
      cases f' with
      | zero => exact hf'
      | succ f'' =>
        dsimp [execOutcome] at hf'
        rw [hEval] at hf'
        exact hNe hf'
    · intro hWf
      exact hWf.2 expectedFault hReachExp

/-! ### Deterministic Fuel-Indexed Adequacy for `M_tupleAssert` -/

/-- Whether a `StepResult` is terminal (`.done _` or `.fault _`). -/
noncomputable def isTerminalStepResult {α β : Type} :
    StepResult α β → Prop
  | .step _ => False
  | .done _ => True
  | .fault _ => True

/-- Positive normal-return canary in `M_tupleAssert`: panic-free, UB-free, and
returns `expectedRet` with empty `callerMem`. -/
noncomputable def PositiveCanaryClaimTupleAssert (p : Program) (q : Query)
    (expectedRet : Val) : Prop :=
  NoPanicAndWellFormedTupleAssert p q ∧
  BehaviorTupleAssert p q (.ret ⟨expectedRet, ⟨[]⟩⟩)

/-- Defined-panic canary in `M_tupleAssert`: UB-free (`WellFormedTupleAssert`),
reaches `.done (.panic expectedMsg)`, falsifies
`NoPanicAndWellFormedTupleAssert`, and never returns normally. -/
noncomputable def PanicCanaryClaimTupleAssert (p : Program) (q : Query)
    (expectedMsg : AssertKind) : Prop :=
  WellFormedTupleAssert p q ∧
  BehaviorTupleAssert p q (.panic expectedMsg) ∧
  ¬ NoPanicAndWellFormedTupleAssert p q ∧
  (∀ out : Out, ¬ BehaviorTupleAssert p q (.ret out))

/-- Negative fault canary in `M_tupleAssert`: reaches `.fault expectedFault`,
never reaches `.fault otherFault`, and falsifies `WellFormedTupleAssert`. -/
noncomputable def NegativeCanaryClaimTupleAssert (p : Program) (q : Query)
    (expectedFault otherFault : FaultKind) : Prop :=
  ReachesResultTupleAssert p q (.fault expectedFault) ∧
  ¬ ReachesResultTupleAssert p q (.fault otherFault) ∧
  ¬ WellFormedTupleAssert p q

noncomputable def execReturnsTupleAssert (p : Program) (fuel : Nat)
    (q : Query) (expected : Val) : Prop :=
  match initStateTupleAssert p q with
  | .error _ => False
  | .ok s₀ =>
    evalTupleAssertFuel p fuel s₀ = .done (.ret ⟨expected, ⟨[]⟩⟩)

noncomputable def execPanicsTupleAssert (p : Program) (fuel : Nat)
    (q : Query) (expectedMsg : AssertKind) : Prop :=
  match initStateTupleAssert p q with
  | .error _ => False
  | .ok s₀ =>
    evalTupleAssertFuel p fuel s₀ = .done (.panic expectedMsg)

noncomputable def execFaultsTupleAssert (p : Program) (fuel : Nat)
    (q : Query) (expected : FaultKind) : Prop :=
  match initStateTupleAssert p q with
  | .error k => k = expected
  | .ok s₀ => evalTupleAssertFuel p fuel s₀ = .fault expected

theorem reachesTupleAssert_head_det {p : Program}
    {s₁ s₂ s₃ : StateExt}
    (hFirst : StepTupleAssert p s₁ (.step s₂))
    (hRest : ReachesTupleAssert p s₂ s₃) :
    ReachesTupleAssert p s₁ s₃ := by
  induction hRest with
  | refl => exact ReachesTupleAssert.tail (ReachesTupleAssert.refl s₁) hFirst
  | tail _ hLast ih => exact ReachesTupleAssert.tail ih hLast

theorem evalTupleAssertFuel_reaches_inv {p : Program}
    {res : StepResult StateExt TerminalOutExt}
    {s₁ s₂ : StateExt} {fuel : Nat}
    (hExec : evalTupleAssertFuel p fuel s₁ = res)
    (hTerm : isTerminalStepResult res)
    (hReach : ReachesTupleAssert p s₁ s₂) :
    ∃ fuel', evalTupleAssertFuel p fuel' s₂ = res := by
  induction hReach with
  | refl => exact ⟨fuel, hExec⟩
  | tail _ hStep ih =>
    let ⟨f, hf⟩ := ih
    cases f with
    | zero =>
      dsimp [evalTupleAssertFuel] at hf
      subst hf
      exact False.elim hTerm
    | succ f' =>
      let ⟨c, hc, hEval⟩ := hStep
      have hc0 : c = 0 := hc
      subst hc0
      dsimp [evalTupleAssertFuel] at hf
      rw [hEval] at hf
      exact ⟨f', hf⟩

theorem evalTupleAssertFuel_terminal {p : Program}
    {res : StepResult StateExt TerminalOutExt}
    {fuel : Nat} {s : StateExt}
    (hExec : evalTupleAssertFuel p fuel s = res)
    (hTerm : isTerminalStepResult res) :
    ∃ sEnd, ReachesTupleAssert p s sEnd ∧ StepTupleAssert p sEnd res := by
  induction fuel generalizing s with
  | zero =>
    dsimp [evalTupleAssertFuel] at hExec
    subst hExec
    exact False.elim hTerm
  | succ f ih =>
    dsimp [evalTupleAssertFuel] at hExec
    cases hEval : evalStepTupleAssert p 0 s with
    | step s' =>
      rw [hEval] at hExec
      let ⟨sEnd, hR, hT⟩ := ih hExec
      exact ⟨sEnd, reachesTupleAssert_head_det ⟨0, rfl, hEval⟩ hR, hT⟩
    | done out =>
      rw [hEval] at hExec
      subst hExec
      exact ⟨s, ReachesTupleAssert.refl s, ⟨0, rfl, hEval⟩⟩
    | fault k =>
      rw [hEval] at hExec
      subst hExec
      exact ⟨s, ReachesTupleAssert.refl s, ⟨0, rfl, hEval⟩⟩

theorem positiveCanaryTupleAssert_of_exec {p : Program}
    {fuel : Nat} {q : Query} {expected : Val}
    (h : execReturnsTupleAssert p fuel q expected) :
    PositiveCanaryClaimTupleAssert p q expected := by
  unfold execReturnsTupleAssert at h
  cases hInit : initStateTupleAssert p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    refine ⟨⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_⟩, ?_⟩
    · intro k hFault
      unfold ReachesResultTupleAssert at hFault
      rw [hInit] at hFault
      let ⟨sF, hReach, c, hc, hEval⟩ := hFault
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalTupleAssertFuel_reaches_inv h True.intro hReach
      cases f' with
      | zero =>
        dsimp [evalTupleAssertFuel] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalTupleAssertFuel] at hf'
        rw [hEval] at hf'
        cases hf'
    · intro msg hPanic
      unfold BehaviorTupleAssert ReachesResultTupleAssert at hPanic
      rw [hInit] at hPanic
      let ⟨sP, hReach, c, hc, hEval⟩ := hPanic
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalTupleAssertFuel_reaches_inv h True.intro hReach
      cases f' with
      | zero =>
        dsimp [evalTupleAssertFuel] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalTupleAssertFuel] at hf'
        rw [hEval] at hf'
        cases hf'
    · unfold BehaviorTupleAssert ReachesResultTupleAssert
      rw [hInit]
      exact evalTupleAssertFuel_terminal h True.intro

theorem panicCanaryTupleAssert_of_exec {p : Program}
    {fuel : Nat} {q : Query} {expectedMsg : AssertKind}
    (h : execPanicsTupleAssert p fuel q expectedMsg) :
    PanicCanaryClaimTupleAssert p q expectedMsg := by
  unfold execPanicsTupleAssert at h
  cases hInit : initStateTupleAssert p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    have hBehPanic : BehaviorTupleAssert p q (.panic expectedMsg) := by
      unfold BehaviorTupleAssert ReachesResultTupleAssert
      rw [hInit]
      exact evalTupleAssertFuel_terminal h True.intro
    refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, hBehPanic, ?_, ?_⟩
    · intro k hFault
      unfold ReachesResultTupleAssert at hFault
      rw [hInit] at hFault
      let ⟨sF, hReach, c, hc, hEval⟩ := hFault
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalTupleAssertFuel_reaches_inv h True.intro hReach
      cases f' with
      | zero =>
        dsimp [evalTupleAssertFuel] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalTupleAssertFuel] at hf'
        rw [hEval] at hf'
        cases hf'
    · intro hNoPanic
      exact hNoPanic.2 expectedMsg hBehPanic
    · intro out hRet
      unfold BehaviorTupleAssert ReachesResultTupleAssert at hRet
      rw [hInit] at hRet
      let ⟨sR, hReach, c, hc, hEval⟩ := hRet
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalTupleAssertFuel_reaches_inv h True.intro hReach
      cases f' with
      | zero =>
        dsimp [evalTupleAssertFuel] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalTupleAssertFuel] at hf'
        rw [hEval] at hf'
        cases hf'

theorem negativeCanaryTupleAssert_of_exec {p : Program}
    {fuel : Nat} {q : Query} {expectedFault otherFault : FaultKind}
    (hNe : otherFault ≠ expectedFault)
    (h : execFaultsTupleAssert p fuel q expectedFault) :
    NegativeCanaryClaimTupleAssert p q expectedFault otherFault := by
  unfold execFaultsTupleAssert at h
  cases hInit : initStateTupleAssert p q with
  | error k =>
    rw [hInit] at h
    subst h
    refine ⟨?_, ?_, ?_⟩
    · unfold ReachesResultTupleAssert; rw [hInit]
    · intro hOther
      unfold ReachesResultTupleAssert at hOther
      rw [hInit] at hOther
      cases hOther
      exact hNe rfl
    · intro hWf
      let ⟨⟨_, hOk, _⟩, _⟩ := hWf
      rw [hInit] at hOk
      cases hOk
  | ok s₀ =>
    rw [hInit] at h
    have hReachExp : ReachesResultTupleAssert p q (.fault expectedFault) := by
      unfold ReachesResultTupleAssert
      rw [hInit]
      exact evalTupleAssertFuel_terminal h True.intro
    refine ⟨hReachExp, ?_, ?_⟩
    · intro hOther
      unfold ReachesResultTupleAssert at hOther
      rw [hInit] at hOther
      let ⟨sF, hReach, c, hc, hEval⟩ := hOther
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalTupleAssertFuel_reaches_inv h True.intro hReach
      cases f' with
      | zero =>
        dsimp [evalTupleAssertFuel] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalTupleAssertFuel] at hf'
        rw [hEval] at hf'
        injection hf' with hEq
        exact hNe hEq
    · intro hWf
      exact hWf.2 expectedFault hReachExp

/-! ### Sharpness Counterexample 1 (`CE1`): `u32::MAX + 1` Overflows to Defined Panic & Lowers to `.fault .undefined` -/

/-- `fn checked_add_u32(a: u32, b: u32) -> u32` using `BinOp.addWithOverflow`
and `TerminatorKind.assert`. -/
noncomputable def progCe1AddOverflow : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, u32Ty, .tuple [u32Ty, .bool]]
    identity := "ce1::checked_add_u32"
    basicBlocks := [
      {
        statements := [
          .storageLive 3,
          .assign ⟨3, []⟩
            (.binaryOp .addWithOverflow (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator :=
          .assert (.copy ⟨3, [.field 1 .bool]⟩) false (.overflow .add) 1
            .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨3, [.field 0 u32Ty]⟩)),
          .storageDead 3
        ]
        terminator := .return_
      }
    ]
  }]

/-- SROA-flattened `progCe1AddOverflow` (`_3` scalarized to `_4 : u32`, `_5 :
bool`, with scratch temps `_6, _7 : u32`). -/
noncomputable def progCe1Sroa : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, u32Ty, .unit, u32Ty, .bool, u32Ty, u32Ty]
    identity := "ce1::checked_add_u32"
    basicBlocks := [
      {
        statements := [
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .storageLive 7,
          .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨7, []⟩ (.use (.copy ⟨2, []⟩)),
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨6, []⟩) (.copy ⟨7, []⟩)),
          .assign ⟨5, []⟩ (.binaryOp .lt (.copy ⟨4, []⟩) (.copy ⟨6, []⟩)),
          .storageDead 6,
          .storageDead 7
        ]
        terminator :=
          .assert (.copy ⟨5, []⟩) false (.overflow .add) 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨4, []⟩)),
          .storageDead 4,
          .storageDead 5
        ]
        terminator := .return_
      }
    ]
  }]

/-- Fully flat assert-free `progCe1Flat` after `SROA` + `AssertLower`. -/
noncomputable def progCe1Flat : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, u32Ty, .unit, u32Ty, .bool, u32Ty, u32Ty]
    identity := "ce1::checked_add_u32"
    basicBlocks := [
      {
        statements := [
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .storageLive 7,
          .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨7, []⟩ (.use (.copy ⟨2, []⟩)),
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨6, []⟩) (.copy ⟨7, []⟩)),
          .assign ⟨5, []⟩ (.binaryOp .lt (.copy ⟨4, []⟩) (.copy ⟨6, []⟩)),
          .storageDead 6,
          .storageDead 7
        ]
        terminator := .switchInt (.copy ⟨5, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨4, []⟩)),
          .storageDead 4,
          .storageDead 5
        ]
        terminator := .return_
      },
      {
        statements := []
        terminator := .unreachable
        cleanup := false
      }
    ]
  }]

/-- **Sharpness Theorem CE1:** Unsigned `u32::MAX + 1` via `addWithOverflow` +
`assert(!_3.1)` reaches defined panic `.done (.panic (.overflow .add))` in
`M_tupleAssert` (preserved across `SROA`) and lowers via `AssertLower` into
`.fault .undefined` in unmodified `Trusted.MirSemantics`, while non-overflowing
`(10, 32)` returns `42_u32` identically in both machines. -/
theorem ce1_u32_max_add_overflow_panics_then_lowers_to_ub :
    checkMirSroaTuple ⟨0, 3⟩ progCe1AddOverflow progCe1Sroa = true ∧
    checkMirAssertLower progCe1Sroa progCe1Flat = true ∧
    isFlatAssertFreeProgram progCe1Flat = true ∧
    PanicCanaryClaimTupleAssert progCe1AddOverflow queryU32MaxPlusOne
      (.overflow .add) ∧
    PanicCanaryClaimTupleAssert progCe1Sroa queryU32MaxPlusOne
      (.overflow .add) ∧
    NegativeCanaryClaim progCe1Flat queryU32MaxPlusOne
      .undefined .unsupported ∧
    PositiveCanaryClaimTupleAssert progCe1AddOverflow
      { args := [u32Val 10, u32Val 32] } (u32Val 42) ∧
    PositiveCanaryClaim progCe1Flat
      { args := [u32Val 10, u32Val 32] } (u32Val 42) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact panicCanaryTupleAssert_of_exec (fuel := 6) rfl
  · exact panicCanaryTupleAssert_of_exec (fuel := 16) rfl
  · exact negativeCanary_of_execFaults (fuel := 20) (by intro h; cases h) rfl
  · exact positiveCanaryTupleAssert_of_exec (fuel := 10) rfl
  · exact positiveCanary_of_execReturns (fuel := 25) rfl

/-! ### Sharpness Counterexample 2 (`CE2`): `0_u32 - 1_u32` Underflows to Defined Panic & Lowers to `.fault .undefined` -/

/-- `fn checked_sub_u32(a: u32, b: u32) -> u32` using `BinOp.subWithOverflow`
and `TerminatorKind.assert`. -/
noncomputable def progCe2SubUnderflow : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, u32Ty, .tuple [u32Ty, .bool]]
    identity := "ce2::checked_sub_u32"
    basicBlocks := [
      {
        statements := [
          .storageLive 3,
          .assign ⟨3, []⟩
            (.binaryOp .subWithOverflow (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator :=
          .assert (.copy ⟨3, [.field 1 .bool]⟩) false (.overflow .sub) 1
            .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨3, [.field 0 u32Ty]⟩)),
          .storageDead 3
        ]
        terminator := .return_
      }
    ]
  }]

/-- SROA-flattened `progCe2SubUnderflow`. -/
noncomputable def progCe2Sroa : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, u32Ty, .unit, u32Ty, .bool, u32Ty, u32Ty]
    identity := "ce2::checked_sub_u32"
    basicBlocks := [
      {
        statements := [
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .storageLive 7,
          .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨7, []⟩ (.use (.copy ⟨2, []⟩)),
          .assign ⟨4, []⟩ (.binaryOp .sub (.copy ⟨6, []⟩) (.copy ⟨7, []⟩)),
          .assign ⟨5, []⟩ (.binaryOp .lt (.copy ⟨6, []⟩) (.copy ⟨7, []⟩)),
          .storageDead 6,
          .storageDead 7
        ]
        terminator :=
          .assert (.copy ⟨5, []⟩) false (.overflow .sub) 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨4, []⟩)),
          .storageDead 4,
          .storageDead 5
        ]
        terminator := .return_
      }
    ]
  }]

/-- Fully flat assert-free `progCe2Flat` after `SROA` + `AssertLower`. -/
noncomputable def progCe2Flat : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, u32Ty, .unit, u32Ty, .bool, u32Ty, u32Ty]
    identity := "ce2::checked_sub_u32"
    basicBlocks := [
      {
        statements := [
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .storageLive 7,
          .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨7, []⟩ (.use (.copy ⟨2, []⟩)),
          .assign ⟨4, []⟩ (.binaryOp .sub (.copy ⟨6, []⟩) (.copy ⟨7, []⟩)),
          .assign ⟨5, []⟩ (.binaryOp .lt (.copy ⟨6, []⟩) (.copy ⟨7, []⟩)),
          .storageDead 6,
          .storageDead 7
        ]
        terminator := .switchInt (.copy ⟨5, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨4, []⟩)),
          .storageDead 4,
          .storageDead 5
        ]
        terminator := .return_
      },
      {
        statements := []
        terminator := .unreachable
        cleanup := false
      }
    ]
  }]

/-- **Sharpness Theorem CE2:** Unsigned `0_u32 - 1_u32` via `subWithOverflow` +
`assert(!_3.1)` reaches defined panic `.done (.panic (.overflow .sub))` in
`M_tupleAssert` (preserved across `SROA`) and lowers to `.fault .undefined` in
unmodified `Trusted.MirSemantics`, while `(50, 8)` returns `42_u32`. -/
theorem ce2_u32_zero_sub_one_underflow_panics_then_lowers_to_ub :
    checkMirSroaTuple ⟨0, 3⟩ progCe2SubUnderflow progCe2Sroa = true ∧
    checkMirAssertLower progCe2Sroa progCe2Flat = true ∧
    isFlatAssertFreeProgram progCe2Flat = true ∧
    PanicCanaryClaimTupleAssert progCe2SubUnderflow
      { args := [u32Val 0, u32Val 1] } (.overflow .sub) ∧
    PanicCanaryClaimTupleAssert progCe2Sroa
      { args := [u32Val 0, u32Val 1] } (.overflow .sub) ∧
    NegativeCanaryClaim progCe2Flat
      { args := [u32Val 0, u32Val 1] } .undefined .unsupported ∧
    PositiveCanaryClaimTupleAssert progCe2SubUnderflow
      { args := [u32Val 50, u32Val 8] } (u32Val 42) ∧
    PositiveCanaryClaim progCe2Flat
      { args := [u32Val 50, u32Val 8] } (u32Val 42) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact panicCanaryTupleAssert_of_exec (fuel := 6) rfl
  · exact panicCanaryTupleAssert_of_exec (fuel := 16) rfl
  · exact negativeCanary_of_execFaults (fuel := 20) (by intro h; cases h) rfl
  · exact positiveCanaryTupleAssert_of_exec (fuel := 10) rfl
  · exact positiveCanary_of_execReturns (fuel := 25) rfl

/-! ### Sharpness Counterexample 3 (`CE3`): Field-Granular `Operand.move` Deinitialization -/

/-- `move (_2.0); copy (_2.1)` succeeds returning `20_u32`. -/
noncomputable def progCe3MoveOtherFieldOk : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, .tuple [u32Ty, u32Ty]]
    identity := "ce3::move_field0_copy_field1"
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .assign ⟨2, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 20)⟩
        ]),
        .assign ⟨1, []⟩ (.use (.move ⟨2, [.field 0 u32Ty]⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, [.field 1 u32Ty]⟩)),
        .storageDead 2
      ]
      terminator := .return_
    }]
  }]

/-- `move (_2.0); copy (_2.0)` faults with `.fault .undefined` (use after
field-granular move). -/
noncomputable def progCe3MoveSameFieldUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, .tuple [u32Ty, u32Ty]]
    identity := "ce3::move_field0_copy_field0"
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .assign ⟨2, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 20)⟩
        ]),
        .assign ⟨1, []⟩ (.use (.move ⟨2, [.field 0 u32Ty]⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, [.field 0 u32Ty]⟩)),
        .storageDead 2
      ]
      terminator := .return_
    }]
  }]

/-- SROA-flattened `progCe3MoveOtherFieldOk`. -/
noncomputable def progCe3MoveOtherFieldSroa : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, .unit, u32Ty, u32Ty]
    identity := "ce3::move_field0_copy_field1"
    basicBlocks := [{
      statements := [
        .storageLive 3,
        .storageLive 4,
        .assign ⟨3, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
        .assign ⟨4, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 20)⟩)),
        .assign ⟨1, []⟩ (.use (.move ⟨3, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨4, []⟩)),
        .storageDead 3,
        .storageDead 4
      ]
      terminator := .return_
    }]
  }]

/-- SROA-flattened `progCe3MoveSameFieldUb`. -/
noncomputable def progCe3MoveSameFieldSroa : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, .unit, u32Ty, u32Ty]
    identity := "ce3::move_field0_copy_field0"
    basicBlocks := [{
      statements := [
        .storageLive 3,
        .storageLive 4,
        .assign ⟨3, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
        .assign ⟨4, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 20)⟩)),
        .assign ⟨1, []⟩ (.use (.move ⟨3, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩)),
        .storageDead 3,
        .storageDead 4
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE3:** Field-granular `Operand.move` deinitializes
strictly the moved field: `move (_2.0); copy (_2.1)` returns `20_u32` whereas
`move (_2.0); copy (_2.0)` faults with `.fault .undefined`, and `SROA`
preserves both behaviors identically into unmodified `Trusted.MirSemantics`. -/
theorem ce3_field_granular_move_deinit_distinct_vs_same_field :
    checkMirSroaTuple ⟨0, 2⟩ progCe3MoveOtherFieldOk progCe3MoveOtherFieldSroa =
      true ∧
    checkMirSroaTuple ⟨0, 2⟩ progCe3MoveSameFieldUb progCe3MoveSameFieldSroa =
      true ∧
    isFlatAssertFreeProgram progCe3MoveOtherFieldSroa = true ∧
    isFlatAssertFreeProgram progCe3MoveSameFieldSroa = true ∧
    PositiveCanaryClaimTupleAssert progCe3MoveOtherFieldOk queryEmpty
      (u32Val 20) ∧
    PositiveCanaryClaim progCe3MoveOtherFieldSroa queryEmpty (u32Val 20) ∧
    NegativeCanaryClaimTupleAssert progCe3MoveSameFieldUb queryEmpty
      .undefined .unsupported ∧
    NegativeCanaryClaim progCe3MoveSameFieldSroa queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact positiveCanaryTupleAssert_of_exec (fuel := 10) rfl
  · exact positiveCanary_of_execReturns (fuel := 25) rfl
  · exact negativeCanaryTupleAssert_of_exec (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanary_of_execFaults (fuel := 25) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 4 (`CE4`): Escaping Tuple Local (`Rvalue.ref`) Rejected by `SROA` -/

/-- Tuple local `_2` escaping via `Rvalue.ref .shared ⟨2, []⟩`. -/
noncomputable def progCe4EscapingRef : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, .tuple [u32Ty, u32Ty]]
    identity := "ce4::escaping_tuple_ref"
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .assign ⟨2, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩
        ]),
        .assign ⟨1, []⟩ (.ref .shared ⟨2, []⟩),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, [.field 0 u32Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Tuple local `_2` escaping via field borrow `Rvalue.ref .shared ⟨2, [.field
0 u32Ty]⟩`. -/
noncomputable def progCe4EscapingFieldRef : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, .tuple [u32Ty, u32Ty]]
    identity := "ce4::escaping_field_ref"
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .assign ⟨2, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩
        ]),
        .assign ⟨1, []⟩ (.ref .shared ⟨2, [.field 0 u32Ty]⟩),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, [.field 0 u32Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE4:** Any tuple local (or field thereof) borrowed via
`Rvalue.ref` is rejected fail-closed by `applyMirSroaTuple` /
`checkMirSroaTuple`, and fails closed with `.fault .unsupported` in
`M_tupleAssert`. -/
theorem ce4_escaping_tuple_ref_rejected_by_sroa :
    applyMirSroaTuple ⟨0, 2⟩ progCe4EscapingRef = none ∧
    checkMirSroaTuple ⟨0, 2⟩ progCe4EscapingRef progCe4EscapingRef = false ∧
    applyMirSroaTuple ⟨0, 2⟩ progCe4EscapingFieldRef = none ∧
    NegativeCanaryClaimTupleAssert progCe4EscapingRef queryEmpty
      .unsupported .undefined := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact negativeCanaryTupleAssert_of_exec (fuel := 10)
    (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 5 (`CE5`): `StorageDead` + `StorageLive` Resets Tuple Fields to Uninitialized -/

/-- `StorageLive 1; _1 = (10, 20); StorageDead 1; StorageLive 1; _0 = copy
(_1.0); return`. -/
noncomputable def progCe5StorageReset : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .tuple [u32Ty, u32Ty]]
    identity := "ce5::storage_reset_tuple"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 20)⟩
        ]),
        .storageDead 1,
        .storageLive 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 u32Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- SROA-flattened `progCe5StorageReset`. -/
noncomputable def progCe5Sroa : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .unit, u32Ty, u32Ty]
    identity := "ce5::storage_reset_tuple"
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .storageLive 3,
        .assign ⟨2, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
        .assign ⟨3, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 20)⟩)),
        .storageDead 2,
        .storageDead 3,
        .storageLive 2,
        .storageLive 3,
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE5:** `StorageDead` followed by `StorageLive` on a
tuple local resets all non-ZST fields to uninitialized (`none`), so reading a
field faults with `.fault .undefined` both in `M_tupleAssert` and after `SROA`
in unmodified `Trusted.MirSemantics`. -/
theorem ce5_storageDead_then_storageLive_resets_tuple_fields_to_uninit :
    checkMirSroaTuple ⟨0, 1⟩ progCe5StorageReset progCe5Sroa = true ∧
    isFlatAssertFreeProgram progCe5Sroa = true ∧
    NegativeCanaryClaimTupleAssert progCe5StorageReset queryEmpty
      .undefined .unsupported ∧
    NegativeCanaryClaim progCe5Sroa queryEmpty .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact negativeCanaryTupleAssert_of_exec (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanary_of_execFaults (fuel := 25) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 6 (`CE6`): `Assert` Polarity Swap & Invalid-Bool Constant-Fold Rejection -/

/-- Parameterized single-assert program asserting `_1 == expected`. -/
noncomputable def mkProgCe6AssertPolarity (expected : Bool) : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, .bool]
    identity := "ce6::assert_polarity"
    basicBlocks := [
      {
        statements := []
        terminator :=
          .assert (.copy ⟨1, []⟩) expected .boundsCheck 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- Constant-true `assert(const true, expected = true)` program. -/
noncomputable def progCe6ConstTrueAssert : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce6::const_true_assert"
    basicBlocks := [
      {
        statements := []
        terminator :=
          .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩)
            true .boundsCheck 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- Folded target `.goto 1` for `progCe6ConstTrueAssert`. -/
noncomputable def progCe6ConstTrueFolded : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce6::const_true_assert"
    basicBlocks := [
      {
        statements := []
        terminator := .goto 1
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- Invalid boolean bit pattern (`bits = 2`) in `TerminatorKind.assert`: must
fault `.undefined` and MUST be rejected by `checkMirAssertConstFold`. -/
noncomputable def progCe6InvalidBoolAssert : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce6::const_true_assert"
    basicBlocks := [
      {
        statements := []
        terminator :=
          .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 2)⟩)
            true .boundsCheck 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- **Sharpness Theorem CE6:** Flipping `expected` in `TerminatorKind.assert`
swaps normal return (`1_u32`) and defined panic (`.boundsCheck`) on both
`true` and `false` inputs; moreover, `checkMirAssertConstFold` admits folding
canonical `bits = 1` (`true`) to `.goto 1` while rejecting non-canonical
`bits = 2` (which faults `.fault .undefined`). -/
theorem ce6_assert_expected_polarity_swaps_return_and_panic_and_const_fold :
    PositiveCanaryClaimTupleAssert (mkProgCe6AssertPolarity true)
      { args := [.bool true] } (u32Val 1) ∧
    PanicCanaryClaimTupleAssert (mkProgCe6AssertPolarity false)
      { args := [.bool true] } .boundsCheck ∧
    PanicCanaryClaimTupleAssert (mkProgCe6AssertPolarity true)
      { args := [.bool false] } .boundsCheck ∧
    PositiveCanaryClaimTupleAssert (mkProgCe6AssertPolarity false)
      { args := [.bool false] } (u32Val 1) ∧
    checkMirAssertConstFold progCe6ConstTrueAssert progCe6ConstTrueFolded =
      true ∧
    checkMirAssertConstFold progCe6InvalidBoolAssert progCe6ConstTrueFolded =
      false ∧
    NegativeCanaryClaimTupleAssert progCe6InvalidBoolAssert queryEmpty
      .undefined .unsupported := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · exact positiveCanaryTupleAssert_of_exec (fuel := 6) rfl
  · exact panicCanaryTupleAssert_of_exec (fuel := 6) rfl
  · exact panicCanaryTupleAssert_of_exec (fuel := 6) rfl
  · exact positiveCanaryTupleAssert_of_exec (fuel := 6) rfl
  · exact negativeCanaryTupleAssert_of_exec (fuel := 6)
      (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 7 (`CE7`): Self-Aliasing `aggregateTuple` Rejection & Field-0 `DeadLocal` Ordering -/

/-- Self-aliasing move-swap `_1 = (move _1.1, move _1.0)`: must fail closed
with `.fault .unsupported` in `M_tupleAssert` and `none` in `SROA` rather than
masking in-place `InvalidUninitBytes` UB. -/
noncomputable def progCe7SelfMoveSwap : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .tuple [u32Ty, u32Ty]]
    identity := "ce7::self_move_swap"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 20)⟩
        ]),
        .assign ⟨1, []⟩ (.aggregateTuple [
          .move ⟨1, [.field 1 u32Ty]⟩,
          .move ⟨1, [.field 0 u32Ty]⟩
        ]),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 u32Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Self-aliasing copy-swap `_1 = (copy _1.1, copy _1.0)`: must fail closed
with `.fault .unsupported` in `M_tupleAssert` and `none` in `SROA`. -/
noncomputable def progCe7SelfCopySwap : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .tuple [u32Ty, u32Ty]]
    identity := "ce7::self_copy_swap"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 20)⟩
        ]),
        .assign ⟨1, []⟩ (.aggregateTuple [
          .copy ⟨1, [.field 1 u32Ty]⟩,
          .copy ⟨1, [.field 0 u32Ty]⟩
        ]),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 u32Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Dead destination `_1 = (const 10_u32, bad_u32_const)` where `bad_u32_const`
exceeds 32 bits (`4294967296`): in-place sequential write triggers `DeadLocal`
(`.undefined`) on field 0 BEFORE evaluating operand 1 (`.unsupported`). -/
noncomputable def progCe7DeadDstField0Order : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .tuple [u32Ty, u32Ty]]
    identity := "ce7::dead_dst_field0_order"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .storageDead 1,
        .assign ⟨1, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 4294967296)⟩
        ])
      ]
      terminator := .return_
    }]
  }]

/-- SROA-flattened `progCe7DeadDstField0Order`. -/
noncomputable def progCe7DeadDstField0Sroa : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .unit, u32Ty, u32Ty]
    identity := "ce7::dead_dst_field0_order"
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .storageLive 3,
        .storageDead 2,
        .storageDead 3,
        .assign ⟨2, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
        .assign ⟨3, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 4294967296)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE7:** Self-aliasing `Rvalue.aggregateTuple`
assignments (`_1 = (move _1.1, move _1.0)` and `_1 = (copy _1.1, copy _1.0)`)
fail closed with `.fault .unsupported` in `M_tupleAssert` and are rejected by
`SROA`; on a dead destination `_1 = (10_u32, bad_u32)`, both `M_tupleAssert`
and `SROA` fault with `.fault .undefined` (`DeadLocal` on field 0) before
evaluating operand 1. -/
theorem ce7_aggregate_self_aliasing_rejected_and_dead_dst_field0_order :
    applyMirSroaTuple ⟨0, 1⟩ progCe7SelfMoveSwap = none ∧
    applyMirSroaTuple ⟨0, 1⟩ progCe7SelfCopySwap = none ∧
    NegativeCanaryClaimTupleAssert progCe7SelfMoveSwap queryEmpty
      .unsupported .undefined ∧
    NegativeCanaryClaimTupleAssert progCe7SelfCopySwap queryEmpty
      .unsupported .undefined ∧
    checkMirSroaTuple ⟨0, 1⟩ progCe7DeadDstField0Order
      progCe7DeadDstField0Sroa = true ∧
    isFlatAssertFreeProgram progCe7DeadDstField0Sroa = true ∧
    NegativeCanaryClaimTupleAssert progCe7DeadDstField0Order queryEmpty
      .undefined .unsupported ∧
    NegativeCanaryClaim progCe7DeadDstField0Sroa queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · exact negativeCanaryTupleAssert_of_exec (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanaryTupleAssert_of_exec (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanaryTupleAssert_of_exec (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanary_of_execFaults (fuel := 15) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 8 (`CE8`): Failing `Assert` Unwind & `AssertKind` Fail-Closed Boundaries -/

/-- Failing `TerminatorKind.assert` with `UnwindAction.unreachable`: must fault
with `.fault .undefined` (matching `Miri.Interpreter.ControlFlow.unwindToBlock`)
and lower cleanly via `AssertLower` into `.unreachable`. -/
noncomputable def progCe8AssertUnwindUnreachable : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce8::assert_unwind_unreachable"
    basicBlocks := [
      {
        statements := []
        terminator :=
          .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩)
            true .boundsCheck 1 .unreachable
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- `AssertLower` target for `progCe8AssertUnwindUnreachable`. -/
noncomputable def progCe8AssertUnwindUnreachableFlat : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce8::assert_unwind_unreachable"
    basicBlocks := [
      {
        statements := []
        terminator :=
          .switchInt (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩) {
            branches := [(BitVec.ofNat 128 1, 1)]
            otherwise := 2
          }
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      },
      {
        statements := []
        terminator := .unreachable
        cleanup := false
      }
    ]
  }]

/-- Failing `TerminatorKind.assert` with `UnwindAction.cleanup 1`: must fail
closed with `.fault .unsupported` in `M_tupleAssert` and `none` in
`AssertLower`. -/
noncomputable def progCe8AssertUnwindCleanup : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce8::assert_unwind_cleanup"
    basicBlocks := [
      {
        statements := []
        terminator :=
          .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩)
            true .boundsCheck 1 (.cleanup 1)
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- Failing `TerminatorKind.assert` with `AssertKind.unsupported`: must fail
closed with `.fault .unsupported` in `M_tupleAssert` and `none` in
`AssertLower`. -/
noncomputable def progCe8AssertKindUnsupported : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce8::assert_kind_unsupported"
    basicBlocks := [
      {
        statements := []
        terminator :=
          .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩)
            true .unsupported 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- Failing `TerminatorKind.assert` with invalid non-overflowing
`AssertKind.overflow .bitAnd`: must fail closed with `.fault .unsupported` in
`M_tupleAssert` and `none` in `AssertLower`. -/
noncomputable def progCe8AssertKindInvalidOvf : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce8::assert_kind_invalid_ovf"
    basicBlocks := [
      {
        statements := []
        terminator :=
          .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩)
            true (.overflow .bitAnd) 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- **Sharpness Theorem CE8:** A failing `TerminatorKind.assert` with
`UnwindAction.unreachable` faults with `.fault .undefined` (matching
`AssertLower`'s `.unreachable` target in unmodified `Trusted.MirSemantics`),
while `.cleanup _`, `AssertKind.unsupported`, and invalid
`AssertKind.overflow .bitAnd` fail closed with `.fault .unsupported` in
`M_tupleAssert` and `none` in `lowerAssertsToSwitchUnreachable`. -/
theorem ce8_assert_unwind_and_kind_fail_closed_boundaries :
    checkMirAssertLower progCe8AssertUnwindUnreachable
      progCe8AssertUnwindUnreachableFlat = true ∧
    isFlatAssertFreeProgram progCe8AssertUnwindUnreachableFlat = true ∧
    NegativeCanaryClaimTupleAssert progCe8AssertUnwindUnreachable queryEmpty
      .undefined .unsupported ∧
    NegativeCanaryClaim progCe8AssertUnwindUnreachableFlat queryEmpty
      .undefined .unsupported ∧
    lowerAssertsToSwitchUnreachable progCe8AssertUnwindCleanup = none ∧
    NegativeCanaryClaimTupleAssert progCe8AssertUnwindCleanup queryEmpty
      .unsupported .undefined ∧
    lowerAssertsToSwitchUnreachable progCe8AssertKindUnsupported = none ∧
    NegativeCanaryClaimTupleAssert progCe8AssertKindUnsupported queryEmpty
      .unsupported .undefined ∧
    lowerAssertsToSwitchUnreachable progCe8AssertKindInvalidOvf = none ∧
    NegativeCanaryClaimTupleAssert progCe8AssertKindInvalidOvf queryEmpty
      .unsupported .undefined := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, ?_, rfl, ?_, rfl, ?_⟩
  · exact negativeCanaryTupleAssert_of_exec (fuel := 6)
      (by intro h; cases h) rfl
  · exact negativeCanary_of_execFaults (fuel := 6) (by intro h; cases h) rfl
  · exact negativeCanaryTupleAssert_of_exec (fuel := 6)
      (by intro h; cases h) rfl
  · exact negativeCanaryTupleAssert_of_exec (fuel := 6)
      (by intro h; cases h) rfl
  · exact negativeCanaryTupleAssert_of_exec (fuel := 6)
      (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 9 (`CE9`): Whole-Tuple Self-Copy & Self-Move Rejection -/

/-- Whole-tuple self-copy `_1 = copy _1` on `(u32, u32, u32)`: must fail closed
with `.fault .unsupported` rather than masking `copyRangesOverlap` UB. -/
noncomputable def progCe9TupleSelfCopy : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .tuple [u32Ty, u32Ty, u32Ty]]
    identity := "ce9::tuple_self_copy"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 3)⟩
        ]),
        .assign ⟨1, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 u32Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Whole-tuple self-move `_1 = move _1` on `(u32, u32, u32)`: must fail closed
with `.fault .unsupported`. -/
noncomputable def progCe9TupleSelfMove : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .tuple [u32Ty, u32Ty, u32Ty]]
    identity := "ce9::tuple_self_move"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 3)⟩
        ]),
        .assign ⟨1, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 u32Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Distinct-local whole-tuple copy `_2 = copy _1` on `(u32, u32, u32)`:
disjoint locals do not overlap and return `1_u32`. -/
noncomputable def progCe9TupleDistinctCopy : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [
      u32Ty,
      .tuple [u32Ty, u32Ty, u32Ty],
      .tuple [u32Ty, u32Ty, u32Ty]
    ]
    identity := "ce9::tuple_distinct_copy"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .storageLive 2,
        .assign ⟨1, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 3)⟩
        ]),
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, [.field 0 u32Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE9:** Whole-tuple self-copy (`_1 = copy _1`) and
self-move (`_1 = move _1`) fail closed with `.fault .unsupported` in
`M_tupleAssert`, whereas non-overlapping whole-tuple copy between distinct
locals (`_2 = copy _1`) succeeds and returns `1_u32`. -/
theorem ce9_whole_tuple_self_copy_move_rejected_vs_distinct_copy_ok :
    NegativeCanaryClaimTupleAssert progCe9TupleSelfCopy queryEmpty
      .unsupported .undefined ∧
    NegativeCanaryClaimTupleAssert progCe9TupleSelfMove queryEmpty
      .unsupported .undefined ∧
    PositiveCanaryClaimTupleAssert progCe9TupleDistinctCopy queryEmpty
      (u32Val 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact negativeCanaryTupleAssert_of_exec (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanaryTupleAssert_of_exec (fuel := 10)
      (by intro h; cases h) rfl
  · exact positiveCanaryTupleAssert_of_exec (fuel := 10) rfl

/-! ### Sharpness Counterexample 10 (`CE10`): 128-Bit `i128` & `u128` Overflow Boundaries -/

/-- `u128` type descriptor (`IntWidth.i128`, unsigned). -/
noncomputable def u128Ty : MirTy := .int .i128 false

/-- `i128` type descriptor (`IntWidth.i128`, signed). -/
noncomputable def i128Ty : MirTy := .int .i128 true

/-- Construct a `u128` scalar `Val`. -/
noncomputable def u128Val (n : Nat) : Val := scalarNatVal .i128 false n

/-- Construct an `i128` scalar `Val` from its raw 128-bit two's-complement bit
pattern. -/
noncomputable def i128Val (bits : Nat) : Val := scalarNatVal .i128 true bits

/-- Raw bit pattern of `i128::MIN` (`Nat.pow 2 127`). -/
noncomputable def i128MinBits : Nat :=
  170141183460469231731687303715884105728

/-- Raw bit pattern of `i128::MAX` (`Nat.pow 2 127 - 1`). -/
noncomputable def i128MaxBits : Nat :=
  170141183460469231731687303715884105727

/-- Raw bit pattern of `u128::MAX` (and signed `i128` minus-one,
`Nat.pow 2 128 - 1`). -/
noncomputable def u128MaxBits : Nat :=
  340282366920938463463374607431768211455

/-- Raw bit pattern of `u128::MAX - 1` (`Nat.pow 2 128 - 2`). -/
noncomputable def u128MaxMinus1Bits : Nat :=
  340282366920938463463374607431768211454

/-- `fn checked_add_u128(a: u128, b: u128) -> u128` using
`BinOp.addWithOverflow` and `TerminatorKind.assert`. -/
noncomputable def progCe10CheckedAddU128 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u128Ty, u128Ty, u128Ty, .tuple [u128Ty, .bool]]
    identity := "ce10::checked_add_u128"
    basicBlocks := [
      {
        statements := [
          .storageLive 3,
          .assign ⟨3, []⟩
            (.binaryOp .addWithOverflow (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator :=
          .assert (.copy ⟨3, [.field 1 .bool]⟩) false (.overflow .add) 1
            .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨3, [.field 0 u128Ty]⟩)),
          .storageDead 3
        ]
        terminator := .return_
      }
    ]
  }]

/-- SROA-flattened `progCe10CheckedAddU128`. -/
noncomputable def progCe10Sroa : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u128Ty, u128Ty, u128Ty, .unit, u128Ty, .bool, u128Ty, u128Ty]
    identity := "ce10::checked_add_u128"
    basicBlocks := [
      {
        statements := [
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .storageLive 7,
          .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨7, []⟩ (.use (.copy ⟨2, []⟩)),
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨6, []⟩) (.copy ⟨7, []⟩)),
          .assign ⟨5, []⟩ (.binaryOp .lt (.copy ⟨4, []⟩) (.copy ⟨6, []⟩)),
          .storageDead 6,
          .storageDead 7
        ]
        terminator :=
          .assert (.copy ⟨5, []⟩) false (.overflow .add) 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨4, []⟩)),
          .storageDead 4,
          .storageDead 5
        ]
        terminator := .return_
      }
    ]
  }]

/-- Flat assert-free target `progCe10Flat` after `SROA` + `AssertLower`. -/
noncomputable def progCe10Flat : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u128Ty, u128Ty, u128Ty, .unit, u128Ty, .bool, u128Ty, u128Ty]
    identity := "ce10::checked_add_u128"
    basicBlocks := [
      {
        statements := [
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .storageLive 7,
          .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨7, []⟩ (.use (.copy ⟨2, []⟩)),
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨6, []⟩) (.copy ⟨7, []⟩)),
          .assign ⟨5, []⟩ (.binaryOp .lt (.copy ⟨4, []⟩) (.copy ⟨6, []⟩)),
          .storageDead 6,
          .storageDead 7
        ]
        terminator := .switchInt (.copy ⟨5, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨4, []⟩)),
          .storageDead 4,
          .storageDead 5
        ]
        terminator := .return_
      },
      {
        statements := []
        terminator := .unreachable
        cleanup := false
      }
    ]
  }]

/-- **Sharpness Theorem CE10:** `evalWithOverflowOp` detects 128-bit host-range
overflow exactly on `i128::MIN * minus_one`, `i128::MAX + 1`,
`i128::MIN - 1`, `u128::MAX + 1`, `0_u128 - 1_u128`, and `u128::MAX * 2` while
returning non-overflowing `0` on `i128::MIN * 0`; moreover, `checked_add_u128`
lowers cleanly via `SROA` + `AssertLower` into unmodified
`Trusted.MirSemantics`. -/
theorem ce10_i128_u128_with_overflow_boundaries :
    evalWithOverflowOp .mulWithOverflow
      (i128Val i128MinBits) (i128Val u128MaxBits) =
      .ok (⟨.i128, true, BitVec.ofNat 128 i128MinBits⟩, true) ∧
    evalWithOverflowOp .mulWithOverflow
      (i128Val i128MinBits) (i128Val 0) =
      .ok (⟨.i128, true, BitVec.ofNat 128 0⟩, false) ∧
    evalWithOverflowOp .addWithOverflow
      (i128Val i128MaxBits) (i128Val 1) =
      .ok (⟨.i128, true, BitVec.ofNat 128 i128MinBits⟩, true) ∧
    evalWithOverflowOp .subWithOverflow
      (i128Val i128MinBits) (i128Val 1) =
      .ok (⟨.i128, true, BitVec.ofNat 128 i128MaxBits⟩, true) ∧
    evalWithOverflowOp .addWithOverflow
      (u128Val u128MaxBits) (u128Val 1) =
      .ok (⟨.i128, false, BitVec.ofNat 128 0⟩, true) ∧
    evalWithOverflowOp .subWithOverflow
      (u128Val 0) (u128Val 1) =
      .ok (⟨.i128, false, BitVec.ofNat 128 u128MaxBits⟩, true) ∧
    evalWithOverflowOp .mulWithOverflow
      (u128Val u128MaxBits) (u128Val 2) =
      .ok (⟨.i128, false, BitVec.ofNat 128 u128MaxMinus1Bits⟩, true) ∧
    checkMirSroaTuple ⟨0, 3⟩ progCe10CheckedAddU128 progCe10Sroa = true ∧
    checkMirAssertLower progCe10Sroa progCe10Flat = true ∧
    isFlatAssertFreeProgram progCe10Flat = true ∧
    PanicCanaryClaimTupleAssert progCe10CheckedAddU128
      { args := [u128Val u128MaxBits, u128Val 1] } (.overflow .add) ∧
    NegativeCanaryClaim progCe10Flat
      { args := [u128Val u128MaxBits, u128Val 1] } .undefined .unsupported ∧
    PositiveCanaryClaimTupleAssert progCe10CheckedAddU128
      { args := [u128Val u128MaxMinus1Bits, u128Val 1] }
      (u128Val u128MaxBits) ∧
    PositiveCanaryClaim progCe10Flat
      { args := [u128Val u128MaxMinus1Bits, u128Val 1] }
      (u128Val u128MaxBits) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact panicCanaryTupleAssert_of_exec (fuel := 6) rfl
  · exact negativeCanary_of_execFaults (fuel := 20) (by intro h; cases h) rfl
  · exact positiveCanaryTupleAssert_of_exec (fuel := 10) rfl
  · exact positiveCanary_of_execReturns (fuel := 25) rfl

/-! ### Constructive End-to-End Witness (`checked_add_pair(a: u32, b: u32) -> u32`) -/

/-- Realistic Rust MIR `fn checked_add_pair(a: u32, b: u32) -> u32`:
constructs `_3 : (u32, u32) = (a, b)` via `Rvalue.aggregateTuple`, computes
`_4 : (u32, bool) = addWithOverflow(move _3.0, move _3.1)`, checks
`assert(move _4.1 == false, .overflow .add)` in `bb0`, and returns `move _4.0`
in `bb1`. -/
noncomputable def pWitnessSrc : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [
      u32Ty,
      u32Ty,
      u32Ty,
      .tuple [u32Ty, u32Ty],
      .tuple [u32Ty, .bool]
    ]
    identity := "witness::checked_add_pair"
    basicBlocks := [
      {
        statements := [
          .storageLive 3,
          .assign ⟨3, []⟩ (.aggregateTuple [.copy ⟨1, []⟩, .copy ⟨2, []⟩]),
          .storageLive 4,
          .assign ⟨4, []⟩ (.binaryOp .addWithOverflow
            (.move ⟨3, [.field 0 u32Ty]⟩) (.move ⟨3, [.field 1 u32Ty]⟩))
        ]
        terminator :=
          .assert (.move ⟨4, [.field 1 .bool]⟩) false (.overflow .add) 1
            .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.move ⟨4, [.field 0 u32Ty]⟩)),
          .storageDead 4,
          .storageDead 3
        ]
        terminator := .return_
      }
    ]
  }]

/-- Two-step `SroaTrace` flattening `_3 : (u32, u32)` then `_4 : (u32, bool)`. -/
noncomputable def witnessSroaTrace : SroaTrace := [⟨0, 3⟩, ⟨0, 4⟩]

/-- Post-`SroaTrace` program `pWitnessSroa` (all locals scalar/unit, `_3` ->
`_5, _6`, `_4` -> `_7, _8` with ovf temps `_9, _10`). -/
noncomputable def pWitnessSroa : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [
      u32Ty, u32Ty, u32Ty, .unit, .unit,
      u32Ty, u32Ty,
      u32Ty, .bool, u32Ty, u32Ty
    ]
    identity := "witness::checked_add_pair"
    basicBlocks := [
      {
        statements := [
          .storageLive 5,
          .storageLive 6,
          .assign ⟨5, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨6, []⟩ (.use (.copy ⟨2, []⟩)),
          .storageLive 7,
          .storageLive 8,
          .storageLive 9,
          .storageLive 10,
          .assign ⟨9, []⟩ (.use (.move ⟨5, []⟩)),
          .assign ⟨10, []⟩ (.use (.move ⟨6, []⟩)),
          .assign ⟨7, []⟩ (.binaryOp .add (.copy ⟨9, []⟩) (.copy ⟨10, []⟩)),
          .assign ⟨8, []⟩ (.binaryOp .lt (.copy ⟨7, []⟩) (.copy ⟨9, []⟩)),
          .storageDead 9,
          .storageDead 10
        ]
        terminator :=
          .assert (.move ⟨8, []⟩) false (.overflow .add) 1 .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.move ⟨7, []⟩)),
          .storageDead 7,
          .storageDead 8,
          .storageDead 5,
          .storageDead 6
        ]
        terminator := .return_
      }
    ]
  }]

/-- Fully flat assert-free target `pWitnessFlat` after `SroaTrace` +
`AssertLower`, directly executable in unmodified `Trusted.MirSemantics`. -/
noncomputable def pWitnessFlat : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [
      u32Ty, u32Ty, u32Ty, .unit, .unit,
      u32Ty, u32Ty,
      u32Ty, .bool, u32Ty, u32Ty
    ]
    identity := "witness::checked_add_pair"
    basicBlocks := [
      {
        statements := [
          .storageLive 5,
          .storageLive 6,
          .assign ⟨5, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨6, []⟩ (.use (.copy ⟨2, []⟩)),
          .storageLive 7,
          .storageLive 8,
          .storageLive 9,
          .storageLive 10,
          .assign ⟨9, []⟩ (.use (.move ⟨5, []⟩)),
          .assign ⟨10, []⟩ (.use (.move ⟨6, []⟩)),
          .assign ⟨7, []⟩ (.binaryOp .add (.copy ⟨9, []⟩) (.copy ⟨10, []⟩)),
          .assign ⟨8, []⟩ (.binaryOp .lt (.copy ⟨7, []⟩) (.copy ⟨9, []⟩)),
          .storageDead 9,
          .storageDead 10
        ]
        terminator := .switchInt (.move ⟨8, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.move ⟨7, []⟩)),
          .storageDead 7,
          .storageDead 8,
          .storageDead 5,
          .storageDead 6
        ]
        terminator := .return_
      },
      {
        statements := []
        terminator := .unreachable
        cleanup := false
      }
    ]
  }]

/-- **Constructive End-to-End Witness
(`witness_checked_add_pair_sroa_assert_reduces_to_trusted`):**
Demonstrates end-to-end non-vacuity on `checked_add_pair(a: u32, b: u32) ->
u32` exercising `aggregateTuple`, `ProjectionElem.field`, `Operand.move`,
`BinOp.addWithOverflow`, and `TerminatorKind.assert`:
1. `pWitnessSrc` is not flat/assert-free and faults with `.fault .unsupported`
   in unmodified `Trusted.MirSemantics`;
2. `checkMirSroaTrace witnessSroaTrace pWitnessSrc pWitnessSroa = true` and
   `checkMirAssertLower pWitnessSroa pWitnessFlat = true` produce a flat,
   assert-free `pWitnessFlat` (`pWitnessSrc ≠ pWitnessFlat`);
3. On `(10_u32, 32_u32)`, `pWitnessSrc` and `pWitnessSroa` return `42_u32` in
   `M_tupleAssert`, and `pWitnessFlat` returns `42_u32` directly in Anneal's
   unmodified `Trusted.MirSemantics`; and
4. On `(u32::MAX, 1_u32)`, `pWitnessSrc` panics with `.overflow .add` in
   `M_tupleAssert` while `pWitnessFlat` reaches `.fault .undefined` in
   unmodified `Trusted.MirSemantics`. -/
theorem witness_checked_add_pair_sroa_assert_reduces_to_trusted :
    isFlatAssertFreeProgram pWitnessSrc = false ∧
    isFlatAssertFreeProgram pWitnessFlat = true ∧
    checkMirSroaTrace witnessSroaTrace pWitnessSrc pWitnessSroa = true ∧
    checkMirAssertLower pWitnessSroa pWitnessFlat = true ∧
    pWitnessSrc ≠ pWitnessFlat ∧
    NegativeCanaryClaim pWitnessSrc { args := [u32Val 10, u32Val 32] }
      .unsupported .undefined ∧
    PositiveCanaryClaimTupleAssert pWitnessSrc
      { args := [u32Val 10, u32Val 32] } (u32Val 42) ∧
    PositiveCanaryClaimTupleAssert pWitnessSroa
      { args := [u32Val 10, u32Val 32] } (u32Val 42) ∧
    PositiveCanaryClaim pWitnessFlat
      { args := [u32Val 10, u32Val 32] } (u32Val 42) ∧
    PositiveCanaryClaimTupleAssert pWitnessFlat
      { args := [u32Val 10, u32Val 32] } (u32Val 42) ∧
    PanicCanaryClaimTupleAssert pWitnessSrc queryU32MaxPlusOne
      (.overflow .add) ∧
    NegativeCanaryClaim pWitnessFlat queryU32MaxPlusOne
      .undefined .unsupported := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hFlat : isFlatAssertFreeProgram pWitnessSrc =
        isFlatAssertFreeProgram pWitnessFlat := by
      rw [hEq]
    cases hFlat
  · exact negativeCanary_of_execFaults (fuel := 10) (by intro h; cases h) rfl
  · exact positiveCanaryTupleAssert_of_exec (fuel := 15) rfl
  · exact positiveCanaryTupleAssert_of_exec (fuel := 35) rfl
  · exact positiveCanary_of_execReturns (fuel := 35) rfl
  · exact positiveCanaryTupleAssert_of_exec (fuel := 35) rfl
  · exact panicCanaryTupleAssert_of_exec (fuel := 15) rfl
  · exact negativeCanary_of_execFaults (fuel := 35) (by intro h; cases h) rfl

end VrustcFormal.F1_11
