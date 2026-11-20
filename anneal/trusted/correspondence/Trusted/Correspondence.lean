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
import Miri.Interpreter.IntegerCast
import Miri.Interpreter.LocalAccess
import Miri.Interpreter.Place
import Miri.Interpreter.Projection
import Miri.Interpreter.Rvalue
import Miri.Interpreter.Aggregate
import Miri.Interpreter.Discriminant
import Miri.Interpreter.Step
import Miri.Interpreter.ControlFlow
import Miri.Interpreter.Call
import Trusted.MirAst
import Trusted.MirSemantics

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# MIR Correspondence Specification (`Trusted.Correspondence`)

**HUMAN COMPREHENSION PRIORITY:**
This module states the top-level MIR correspondence theorem
(`CorrespondenceClaim`), the bidirectional fault-equivalence theorem
(`FaultEquivalenceClaim`), the Miri move-deinitialization wiring theorem
(`MiriMoveDeinitWiringClaim`), and the one-to-one simulation invariant
(`SimulationInv`) together with all of their adapter definitions. Because this
file is the human-audited specification bridge between `Trusted.MirSemantics`
($M_{\text{anneal}}$) and `vendor/lean-miri/` ($M_{\text{ref}}$), **human
comprehension takes priority over every other concern** across
`CorrespondenceClaim` and all of its transitive dependencies
(`Trusted.Correspondence`, `Trusted.MirSemantics`, and `Trusted.MirAst`). Every
definition in this module is written to be maximally direct, self-evident to a
human auditor, and accompanied by explicit boundary documentation so any gap or
scoping restriction is immediately visible rather than subtle.

This module defines five components:

1. **Reference-indexed MIR syntax (`RefProg`):** Mirrors `Miri.MIR.Syntax` by
   replacing inline structural `MirTy` values with `TyId := Nat` indices into a
   single deduplicated program type table `RefProg.types : List MirTy`, while
   carrying explicit `pointerWidthBits : Nat` and `mirProfileVersion : Nat`
   fields plus `scope : VerificationScope := .unit`.
2. **Canonical type-interning codec (`encodeProg` / `decodeProg`):** Starts
   from the empty type table `[]`, interns every structural `MirTy` in
   bottom-up topological order, and provides an unconditional left-inverse
   decoder `decodeProg`.
3. **Reference semantics ($M_{\text{ref}}$) and step-budget quantification:**
   Defines a hybrid reference evaluator over `RefProg` / `RefState` that
   resolves `RefProg` bodies, basic blocks, and statements over list-indexed
   frames and delegates step, statement, terminator, rvalue, operand, and
   scalar/integer evaluation (plus `_0` `StorageDead` rejection) to
   `vendor/lean-miri` (pinned at `proofs-rs/lean-miri` commit
   `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `miri` commit
   `7fa591d7d4dd9af8154becbc8332f8096f8323b1`, `rustc` commit
   `8144389c895da997dbdecaa635e41d6a50be6ffd`) with explicit
   `stepsExecuted` and `maxSteps` tracking and runtime `Operand.move`
   deinitialization (`deinitMovedPlace = true`). Move deinitialization is not
   upstream behavior: `deinitMovedPlace = true` enables Anneal's own
   conservative, opt-in patch to ten `vendor/lean-miri` files on top of
   `lean-miri@c92d1d97` (listed under `patched_files` in
   `vendor/lean-miri/UPSTREAM_PIN.json`), whereas `eval_operand` at
   `rustc@8144389c` still evaluates `Move` exactly like `Copy` (see the
   upstream `FIXME` quoted at `evalRefMiriOperandToSlot`). The evaluator
   routes:
   - constant decoding, scalar validity checks, unary/binary integer and boolean
     arithmetic (including the overflowing operators), integer casts, and
     `SwitchInt` case comparisons through `Miri.Memory.ScalarInt`,
     `Miri.Interpreter.IntegerOps`, and `Miri.Interpreter.IntegerCast`;
   - operand evaluation (`evalRefMiriOperandToSlot`, `evalRefPlaceOperand`,
     `readRefPrimitiveSlot`) through `Miri.Interpreter.evalOperand`, applying
     value-tree place projections (`refProjectPlaceTy?`,
     `refReadPlaceSlotPath?`, and `refWritePlaceSlotPath?`) after resolving
     array indices via `Miri.Interpreter.project`;
   - local place writes (`writeRefPlace`) through
     `Miri.Interpreter.evalPlaceToOp` and
     `Miri.Interpreter.placeWriteLocalImmediate`;
   - rvalue dispatch and left-to-right operand sequencing (`evalRefMiriRvalue`)
     through `Miri.Interpreter.evalRvalueIntoPlace`,
     `Miri.Interpreter.writeAggregate`, `Miri.Interpreter.writeRepeat`,
     `Miri.Interpreter.Discriminant.{readDiscriminant, writeDiscriminant,
     discriminantForVariant}`, and `Miri.Interpreter.runRvalue`;
   - `toLeBytes` and `fromLeBytes` through `Miri.Memory.Allocation`
     (`Allocation.{fromBytes, writeScalar, getBytesStripProvenance,
     readScalar}`) under an explicit little-endian `TargetDataLayout`;
   - outer step and statement dispatch (`evalRefStep`, `evalRefStatement`)
     through `Miri.Interpreter.Step.step` and
     `Miri.Interpreter.Step.evalStatement`, delegating `_0` `StorageDead`
     rejection to `Miri.Interpreter.Frame.storageDead` (while `storageLive`
     calls `Miri.Interpreter.Frame.storageLive` on a dummy single-local
     frame, always returning `.ok ()`, because adapter locals are modeled
     in the wrapper frame); and
   - basic-block jumps, terminators, direct crate-local calls, `CoreBuiltin`
     calls, `Assert` panics, and multi-frame unwinding (`evalRefTerminator`)
     through `Miri.Interpreter.Step.step`,
     `Miri.Interpreter.ControlFlow.goToBlock`,
     `Miri.Interpreter.ControlFlow.returnToBlock`,
     `Miri.Interpreter.ControlFlow.evalTerminator`,
     `Miri.Interpreter.ControlFlow.unwindToBlock`,
     `Miri.Interpreter.ControlFlow.returnFromCurrentFrame`,
     `Miri.Interpreter.Call.evalCallTerminator`,
     `Miri.Interpreter.Stack.pushFrame`,
     `Miri.Interpreter.IntegerIntrinsic.run`, and
     `Miri.Interpreter.IntegerArithmeticIntrinsic.saturatingArith`:

   **Tier 2 adapter boundary (explicit human-audit scope):**
   Because Tier 2 locals in $M_{\text{ref}}$ are still stored as value trees
   (`SlotVal`) rather than byte-level `Miri.Memory.Allocation`s, Pass 2
   independently cross-checks the following Tier 2 rules against
   `vendor/lean-miri`: array `Index` / `ConstantIndex` (`fromEnd`) bounds
   (`Miri.Interpreter.project`), direct and niche discriminant decoding
   (`Discriminant.readDiscriminant`), uninhabited/niche/non-enum
   `SetDiscriminant` checks (`Discriminant.writeDiscriminant` +
   `tagForVariant`), `checked_{add,sub,mul}` overflow (`IntegerOps.binary`),
   little-endian byte codecs (`Allocation.{writeScalar, readScalar}`),
   aggregate sequencing (`writeAggregate`), and array repeat sequencing
   (`writeRepeat`). By contrast, `SlotVal` field/downcast projection,
   `.enumUntagged` partial-write shells (`SlotVal.toVal?`), partial-move
   uninit propagation, niche-path traversal (`refNicheResolveFromTy`), ZST /
   uninhabited predicates, and the may-alias overlap guard are currently
   defined inside this value-tree adapter (checked for self-consistency with
   $M_{\text{anneal}}$ and by human audit until $M_{\text{ref}}$ moves to
   byte-backed `Miri.Memory.MemoryState` / `Allocation`s in Tier 3).

   > "pub fn step(&mut self) -> InterpResult<'tcx, bool> { ...
   > if let Some(stmt) = basic_block.statements.get(loc.statement_index) { ...
   > self.eval_statement(stmt)?; ... return interp_ok(true); } ...
   > let terminator = basic_block.terminator();
   > self.eval_terminator(terminator)?; ... interp_ok(true) }"
   > (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
   > `8144389c895da997dbdecaa635e41d6a50be6ffd`)
4. **Top-level correspondence claims (`CorrespondenceClaim`,
   `FaultEquivalenceClaim`, `MiriMoveDeinitWiringClaim`, and core simulation /
   canary `*Claim` propositions):** States UB transfer together with exact
   terminal-behavior and divergence equivalence (`WellFormed p q →
   RefWellFormed (encodeProg p) q ∧ (∀ out, Behavior p q out ↔ RefBehavior
   (encodeProg p) q out) ∧ (Diverges p q ↔ RefDiverges (encodeProg p) q)`),
   bidirectional fault equivalence for `.undefined` (`.ub`) and `.unsupported`
   (`.blocked`), and the direct wiring contract of
   `Miri.Interpreter.ExecutionMachine.step` (`Miri.Interpreter.Step.step` over
   `ExecutionMachine.stepHooks`) and `deinitMovedPlace` on
   `Miri.Interpreter.ExecutionMachine.{withValidation,operandHooks}` and
   `Miri.Interpreter.evalOperand`.
5. **Fail-closed target, profile, and stack shape:** `initRefState` rejects
   programs whose `pointerWidthBits` is not 64 or whose `mirProfileVersion` is
   not 1 (matching `Trusted.MirSemantics.initState`) and starts the reference
   stack as `[callerSentinelFrame retTy, entryFrame]`. Direct crate-local calls
   push callee frames on top of that stack (stored bottom-to-top after the
   sentinel, matching `Miri.Interpreter.Stack.frames`), and returns/unwinds pop
   them while preserving the sentinel.
-/

/-- Interned type-table index (`Miri.MIR.TyId`). -/
abbrev TyId := Nat

/-! ## Reference-Indexed AST with `TyId` Indirection (`Miri.MIR` Boundary) -/

/-- Reference place projection element indexing `RefProg.types` via `TyId`. -/
inductive RefProjectionElem where
  | deref
  | field (fieldIdx : FieldIdx) (ty : TyId)
  | downcast (variantIdx : Nat)
  | index (idxLocal : LocalId)
  | constantIndex (offset : Nat) (minLength : Nat) (fromEnd : Bool)
  | unsupported

/-- Reference MIR place (`Miri.MIR.Place`). -/
structure RefPlace where
  localId : LocalId
  projection : List RefProjectionElem := []

/-- Reference constant operand indexing `RefProg.types` via `TyId`. -/
structure RefConstOperand where
  ty : TyId
  lit : ConstLit

/-- Reference MIR operand (`Miri.MIR.Operand`). -/
inductive RefOperand where
  | copy (place : RefPlace)
  | move (place : RefPlace)
  | constant (c : RefConstOperand)

/-- Reference aggregate construction kind indexing `RefProg.types` via
`TyId`. -/
inductive RefAggregateKind where
  | tuple
  | adtStruct (styId : TyId)
  | adtEnum (etyId : TyId) (variantIdx : Nat)
  | array (elemTyId : TyId)

/-- Reference MIR rvalue (`Miri.MIR.Rvalue`). -/
inductive RefRvalue where
  | use (op : RefOperand)
  | binaryOp (op : BinOp) (lhs rhs : RefOperand)
  | unaryOp (op : UnOp) (opnd : RefOperand)
  | discriminant (place : RefPlace)
  | ref (mutability : Mutability) (place : RefPlace)
  | addressOf (mutability : Mutability) (place : RefPlace)
  | aggregate (kind : RefAggregateKind) (fields : List RefOperand)
  | repeat_ (op : RefOperand) (count : Nat)
  | cast (kind : CastKind) (op : RefOperand) (ty : TyId)
  | unsupported

/-- Backward-compatible tuple aggregate alias on `RefRvalue`. -/
noncomputable def RefRvalue.aggregateTuple (fields : List RefOperand) :
    RefRvalue :=
  .aggregate .tuple fields

/-- Reference MIR statement (`Miri.MIR.StatementKind`). -/
inductive RefStatementKind where
  | assign (dst : RefPlace) (rvalue : RefRvalue)
  | setDiscriminant (place : RefPlace) (variantIdx : Nat)
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | nop
  | unsupported

/-- Reference MIR terminator (`Miri.MIR.TerminatorKind`). -/
inductive RefTerminatorKind where
  | goto (target : BasicBlockId)
  | switchInt (discr : RefOperand) (targets : SwitchTargets)
  | return_
  | unreachable
  | unwindResume
  | assert (cond : RefOperand) (expected : Bool) (msg : AssertKind)
      (target : BasicBlockId) (unwind : UnwindAction)
  | call (callee : DefId) (args : List RefOperand) (dst : RefPlace)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | callBuiltin (builtin : CoreBuiltin) (args : List RefOperand)
      (dst : RefPlace) (target : Option BasicBlockId) (unwind : UnwindAction)
  | unsupported

/-- Reference MIR basic block (`Miri.MIR.BasicBlock`). -/
structure RefBasicBlock where
  statements : List RefStatementKind
  terminator : RefTerminatorKind
  cleanup : Bool := false

/-- Reference MIR function body (`Miri.MIR.Body`) whose local declarations
store `TyId` indices into `RefProg.types`.

`isUnsafe` and `identity` are inert in $M_{\text{ref}}$: `encodeProg` and
`decodeProg` preserve them for structural alignment with `Body`, and neither
`initRefState` nor `evalRefStep` consults them. -/
structure RefBody where
  argumentCount : Nat
  locals : List TyId
  basicBlocks : List RefBasicBlock
  isUnsafe : Bool := false
  identity : String := ""

/-- Reference program with a single-source deduplicated `types : List MirTy`
table indexed by `TyId`.

Every `TyId` in a reference program resolves through `types[tyId]?`:
`initRefState` resolves the entry body's local declarations once and caches
each local's `MirTy` in `RefLocalState.cachedLayout`, and a constant operand
resolves `types[c.ty]?` when `evalRefMiriOperandToSlot` evaluates it. Adapters
derive type-specific `lean-miri` layouts from that cached `MirTy` where
semantics depend on it (`refLocalLayoutForTy` in `evalRefPlaceOperand` so
`isZst` governs move deinitialization for `MirTy.unit` and admitted 1-variant
ZST enums, and `refEnumLayoutData` plus `refScalarLayoutData` /
`refTagScalarLayout?` for enum constant and `Discriminant` evaluation); all
other single-local and rvalue adapter sites use the fixed 8-byte placeholder
`refSizedLocalLayout` (see the authoritative call-site list on
`refSizedLocalLayout`). Each `Miri.Interpreter.Frame` that the adapters build
carries its local's layout pre-cached, so `Miri.Interpreter.localToOp` never
mutates `frame.locals` during read-only accesses.

`pointerWidthBits` and `mirProfileVersion` carry `Program.pointerWidthBits` and
`Program.mirProfileVersion` across the codec so that `initRefState`
independently rejects non-64-bit targets and unsupported MIR profile versions,
matching `Trusted.MirSemantics.initState`. `scope` carries `Program.scope` for
structural round-trip alignment only and is inert in $M_{\text{ref}}$ (never
consulted by `initRefState` or `evalRefStep`). -/
structure RefProg where
  bodies : List RefBody
  entryDefId : DefId := 0
  types : List MirTy
  pointerWidthBits : Nat
  mirProfileVersion : Nat
  scope : VerificationScope := .unit

/-! ## Canonical Type Interning and Codec (`encodeProg` / `decodeProg`) -/

/-- Return the first index `i` in `ts` where `MirTy.beq ts[i] ty = true`. -/
noncomputable def indexOfTy : List MirTy → MirTy → Option TyId
  | [], _ => none
  | t :: ts, ty =>
    if MirTy.beq t ty then some 0
    else
      match indexOfTy ts ty with
      | some i => some (i + 1)
      | none => none

/-- Append `ty` to `ts` if and only if no structurally equal type is already
present. -/
noncomputable def insertTy (ty : MirTy) : List MirTy → List MirTy
  | [] => [ty]
  | t :: ts => if MirTy.beq t ty then t :: ts else t :: insertTy ty ts

/-- Resolve `ty` to its interned `TyId` in `ts` (defaulting to `0` if
absent). -/
noncomputable def lookupTyId (ts : List MirTy) (ty : MirTy) : TyId :=
  (indexOfTy ts ty).getD 0

/-- Check that `ts` contains no duplicate `MirTy` entries under `MirTy.beq`. -/
noncomputable def typesAreCanonical : List MirTy → Bool
  | [] => true
  | t :: ts => (indexOfTy ts t).isNone && typesAreCanonical ts

mutual
  /-- Recursively intern structural sub-types (`pointee` in `.ref`/`.rawPtr`,
  `fields` in `.adtStruct`/`.tuple`, `variantFields` in `.enum`, and `elemTy`
  in `.array`) in bottom-up topological order before interning the enclosing
  `MirTy`, guaranteeing that pointee, field, variant, and element types are
  always present in `(encodeProg p).types`. -/
  noncomputable def collectTy (acc : List MirTy) : MirTy → List MirTy
    | .bool => insertTy .bool acc
    | .int w s => insertTy (.int w s) acc
    | .unit => insertTy .unit acc
    | .never => insertTy .never acc
    | .adtStruct ⟨id, fs⟩ =>
      insertTy (.adtStruct ⟨id, fs⟩) (collectTyList acc fs)
    | .enum ⟨id, dw, ds, tr, d, vf⟩ =>
      insertTy (.enum ⟨id, dw, ds, tr, d, vf⟩) (collectTyListList acc vf)
    | .unsupported => insertTy .unsupported acc
    | .ref m p => insertTy (.ref m p) (collectTy acc p)
    | .rawPtr m p => insertTy (.rawPtr m p) (collectTy acc p)
    | .tuple fs => insertTy (.tuple fs) (collectTyList acc fs)
    | .array elemTy len =>
      insertTy (.array elemTy len) (collectTy acc elemTy)

  /-- Intern a list of `MirTy` descriptors left-to-right. -/
  noncomputable def collectTyList (acc : List MirTy) : List MirTy → List MirTy
    | [] => acc
    | ty :: tys => collectTyList (collectTy acc ty) tys

  /-- Intern a list of per-variant `MirTy` lists left-to-right. -/
  noncomputable def collectTyListList (acc : List MirTy) :
      List (List MirTy) → List MirTy
    | [] => acc
    | fs :: fss => collectTyListList (collectTyList acc fs) fss
end

/-- Map a pure function over an `Option`. -/
noncomputable def optMap {α β : Type} (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none => none

/-- Combine two `Option` results with a binary constructor. -/
noncomputable def optMap2 {α β γ : Type} (f : α → β → γ)
    (ox : Option α) (oy : Option β) : Option γ :=
  match ox with
  | some x =>
    match oy with
    | some y => some (f x y)
    | none => none
  | none => none

/-- Traverse a list left-to-right with a fallible element decoder. -/
noncomputable def mapOption {α β : Type} (f : α → Option β) :
    List α → Option (List β)
  | [] => some []
  | x :: xs => optMap2 List.cons (f x) (mapOption f xs)

/-- Intern any `MirTy` carried inside a `ProjectionElem`. -/
noncomputable def collectProjElem (acc : List MirTy) :
    ProjectionElem → List MirTy
  | .field _ ty => collectTy acc ty
  | .deref | .downcast _ | .index _ | .constantIndex _ _ _
  | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in `p.projection`. -/
noncomputable def collectPlace (acc : List MirTy) (p : Place) : List MirTy :=
  p.projection.foldl collectProjElem acc

/-- Intern all `MirTy` descriptors carried in an `Operand`. -/
noncomputable def collectOperand (acc : List MirTy) : Operand → List MirTy
  | .copy p | .move p => collectPlace acc p
  | .constant c => collectTy acc c.ty

/-- Intern any `MirTy` carried inside an `AggregateKind`. -/
noncomputable def collectAggregateKind (acc : List MirTy) :
    AggregateKind → List MirTy
  | .tuple => acc
  | .adtStruct sty => collectTy acc (.adtStruct sty)
  | .adtEnum ety _ => collectTy acc (.enum ety)
  | .array elemTy => collectTy acc elemTy

/-- Intern all `MirTy` descriptors carried in an `Rvalue`. -/
noncomputable def collectRvalue (acc : List MirTy) : Rvalue → List MirTy
  | .use op => collectOperand acc op
  | .binaryOp _ l r => collectOperand (collectOperand acc l) r
  | .unaryOp _ op => collectOperand acc op
  | .discriminant p | .ref _ p | .addressOf _ p => collectPlace acc p
  | .aggregate kind ops =>
    ops.foldl collectOperand (collectAggregateKind acc kind)
  | .repeat_ op _ => collectOperand acc op
  | .cast _ op ty => collectTy (collectOperand acc op) ty
  | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a `StatementKind`. -/
noncomputable def collectStmt (acc : List MirTy) : StatementKind → List MirTy
  | .assign dst rv => collectRvalue (collectPlace acc dst) rv
  | .setDiscriminant p _ => collectPlace acc p
  | .storageLive _ | .storageDead _ | .nop | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a `TerminatorKind`. -/
noncomputable def collectTerminator (acc : List MirTy) :
    TerminatorKind → List MirTy
  | .switchInt d _ => collectOperand acc d
  | .assert c _ _ _ _ => collectOperand acc c
  | .call _ args dst _ _ | .callBuiltin _ args dst _ _ =>
    collectPlace (args.foldl collectOperand acc) dst
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a `BasicBlock`. -/
noncomputable def collectBasicBlock (acc : List MirTy)
    (bb : BasicBlock) : List MirTy :=
  collectTerminator (bb.statements.foldl collectStmt acc) bb.terminator

/-- Intern all `MirTy` descriptors in a function `Body`. -/
noncomputable def collectBody (acc : List MirTy) (b : Body) : List MirTy :=
  b.basicBlocks.foldl collectBasicBlock (collectTyList acc b.locals)

/-- Collect the canonical deduplicated type table for `p : Program`, starting
from `[]` and interning every `MirTy` bottom-up. -/
noncomputable def collectProgTypes (p : Program) : List MirTy :=
  p.bodies.foldl collectBody []

/-- Encode a `ProjectionElem` against type table `ts`. -/
noncomputable def encodeProjElem (ts : List MirTy) :
    ProjectionElem → RefProjectionElem
  | .deref => .deref
  | .field idx ty => .field idx (lookupTyId ts ty)
  | .downcast v => .downcast v
  | .index idxLocal => .index idxLocal
  | .constantIndex offset minLength fromEnd =>
    .constantIndex offset minLength fromEnd
  | .unsupported => .unsupported

/-- Encode a `Place` against type table `ts`. -/
noncomputable def encodePlace (ts : List MirTy) (p : Place) : RefPlace :=
  ⟨p.localId, p.projection.map (encodeProjElem ts)⟩

/-- Encode an `Operand` against type table `ts`. -/
noncomputable def encodeOperand (ts : List MirTy) : Operand → RefOperand
  | .copy p => .copy (encodePlace ts p)
  | .move p => .move (encodePlace ts p)
  | .constant c => .constant ⟨lookupTyId ts c.ty, c.lit⟩

/-- Encode an `AggregateKind` against type table `ts`. -/
noncomputable def encodeAggregateKind (ts : List MirTy) :
    AggregateKind → RefAggregateKind
  | .tuple => .tuple
  | .adtStruct sty => .adtStruct (lookupTyId ts (.adtStruct sty))
  | .adtEnum ety v => .adtEnum (lookupTyId ts (.enum ety)) v
  | .array elemTy => .array (lookupTyId ts elemTy)

/-- Encode an `Rvalue` against type table `ts`. -/
noncomputable def encodeRvalue (ts : List MirTy) : Rvalue → RefRvalue
  | .use op => .use (encodeOperand ts op)
  | .binaryOp op l r => .binaryOp op (encodeOperand ts l) (encodeOperand ts r)
  | .unaryOp op opnd => .unaryOp op (encodeOperand ts opnd)
  | .discriminant p => .discriminant (encodePlace ts p)
  | .ref m p => .ref m (encodePlace ts p)
  | .addressOf m p => .addressOf m (encodePlace ts p)
  | .aggregate kind ops =>
    .aggregate (encodeAggregateKind ts kind) (ops.map (encodeOperand ts))
  | .repeat_ op count => .repeat_ (encodeOperand ts op) count
  | .cast kind op ty => .cast kind (encodeOperand ts op) (lookupTyId ts ty)
  | .unsupported => .unsupported

/-- Encode a `StatementKind` against type table `ts`. -/
noncomputable def encodeStmt (ts : List MirTy) :
    StatementKind → RefStatementKind
  | .assign dst rv => .assign (encodePlace ts dst) (encodeRvalue ts rv)
  | .setDiscriminant p v => .setDiscriminant (encodePlace ts p) v
  | .storageLive id => .storageLive id
  | .storageDead id => .storageDead id
  | .nop => .nop
  | .unsupported => .unsupported

/-- Encode a `TerminatorKind` against type table `ts`. -/
noncomputable def encodeTerminator (ts : List MirTy) :
    TerminatorKind → RefTerminatorKind
  | .goto t => .goto t
  | .switchInt d targets => .switchInt (encodeOperand ts d) targets
  | .return_ => .return_
  | .unreachable => .unreachable
  | .unwindResume => .unwindResume
  | .assert c exp msg t u => .assert (encodeOperand ts c) exp msg t u
  | .call callee args dst t u =>
    .call callee (args.map (encodeOperand ts)) (encodePlace ts dst) t u
  | .callBuiltin builtin args dst t u =>
    .callBuiltin builtin (args.map (encodeOperand ts)) (encodePlace ts dst) t u
  | .unsupported => .unsupported

/-- Encode a `BasicBlock` against type table `ts`. -/
noncomputable def encodeBasicBlock (ts : List MirTy)
    (bb : BasicBlock) : RefBasicBlock :=
  ⟨bb.statements.map (encodeStmt ts),
   encodeTerminator ts bb.terminator,
   bb.cleanup⟩

/-- Encode a `Body` against type table `ts`. -/
noncomputable def encodeBody (ts : List MirTy) (b : Body) : RefBody :=
  ⟨b.argumentCount,
   b.locals.map (lookupTyId ts),
   b.basicBlocks.map (encodeBasicBlock ts),
   b.isUnsafe,
   b.identity⟩

/-- Total encoder from `Program` to `RefProg`. -/
noncomputable def encodeProg (p : Program) : RefProg :=
  let ts := collectProgTypes p
  ⟨p.bodies.map (encodeBody ts), p.entryDefId, ts, p.pointerWidthBits,
   p.mirProfileVersion, p.scope⟩

/-- Decode a `RefProjectionElem` against type table `ts`. -/
noncomputable def decodeProjElem (ts : List MirTy) :
    RefProjectionElem → Option ProjectionElem
  | .deref => some .deref
  | .field idx tyId =>
    optMap (ProjectionElem.field idx) (MirSemantics.getElem? ts tyId)
  | .downcast v => some (.downcast v)
  | .index idxLocal => some (.index idxLocal)
  | .constantIndex offset minLength fromEnd =>
    some (.constantIndex offset minLength fromEnd)
  | .unsupported => some .unsupported

/-- Decode a `RefPlace` against type table `ts`. -/
noncomputable def decodePlace (ts : List MirTy) (p : RefPlace) : Option Place :=
  optMap (Place.mk p.localId) (mapOption (decodeProjElem ts) p.projection)

/-- Decode a `RefOperand` against type table `ts`. -/
noncomputable def decodeOperand (ts : List MirTy) : RefOperand → Option Operand
  | .copy p => optMap Operand.copy (decodePlace ts p)
  | .move p => optMap Operand.move (decodePlace ts p)
  | .constant c =>
    optMap (fun ty => .constant ⟨ty, c.lit⟩) (MirSemantics.getElem? ts c.ty)

/-- Decode a `RefAggregateKind` against type table `ts`. -/
noncomputable def decodeAggregateKind (ts : List MirTy) :
    RefAggregateKind → Option AggregateKind
  | .tuple => some .tuple
  | .adtStruct styId =>
    match MirSemantics.getElem? ts styId with
    | some (.adtStruct sty) => some (.adtStruct sty)
    | _ => none
  | .adtEnum etyId v =>
    match MirSemantics.getElem? ts etyId with
    | some (.enum ety) => some (.adtEnum ety v)
    | _ => none
  | .array elemTyId =>
    optMap AggregateKind.array (MirSemantics.getElem? ts elemTyId)

/-- Decode a `RefRvalue` against type table `ts`. -/
noncomputable def decodeRvalue (ts : List MirTy) : RefRvalue → Option Rvalue
  | .use op => optMap Rvalue.use (decodeOperand ts op)
  | .binaryOp op l r =>
    optMap2 (Rvalue.binaryOp op) (decodeOperand ts l) (decodeOperand ts r)
  | .unaryOp op opnd => optMap (Rvalue.unaryOp op) (decodeOperand ts opnd)
  | .discriminant p => optMap Rvalue.discriminant (decodePlace ts p)
  | .ref m p => optMap (Rvalue.ref m) (decodePlace ts p)
  | .addressOf m p => optMap (Rvalue.addressOf m) (decodePlace ts p)
  | .aggregate kind ops =>
    optMap2 Rvalue.aggregate (decodeAggregateKind ts kind)
      (mapOption (decodeOperand ts) ops)
  | .repeat_ op count =>
    optMap (fun op' => Rvalue.repeat_ op' count) (decodeOperand ts op)
  | .cast kind op tyId =>
    optMap2 (Rvalue.cast kind) (decodeOperand ts op)
      (MirSemantics.getElem? ts tyId)
  | .unsupported => some .unsupported

/-- Decode a `RefStatementKind` against type table `ts`. -/
noncomputable def decodeStmt (ts : List MirTy) :
    RefStatementKind → Option StatementKind
  | .assign dst rv =>
    optMap2 StatementKind.assign (decodePlace ts dst) (decodeRvalue ts rv)
  | .setDiscriminant p v =>
    optMap (fun p' => StatementKind.setDiscriminant p' v) (decodePlace ts p)
  | .storageLive id => some (.storageLive id)
  | .storageDead id => some (.storageDead id)
  | .nop => some .nop
  | .unsupported => some .unsupported

/-- Decode a `RefTerminatorKind` against type table `ts`. -/
noncomputable def decodeTerminator (ts : List MirTy) :
    RefTerminatorKind → Option TerminatorKind
  | .goto t => some (.goto t)
  | .switchInt d targets =>
    optMap (fun d' => .switchInt d' targets) (decodeOperand ts d)
  | .return_ => some .return_
  | .unreachable => some .unreachable
  | .unwindResume => some .unwindResume
  | .assert c exp msg t u =>
    optMap (fun c' => .assert c' exp msg t u) (decodeOperand ts c)
  | .call callee args dst t u =>
    optMap2 (fun args' dst' => .call callee args' dst' t u)
      (mapOption (decodeOperand ts) args) (decodePlace ts dst)
  | .callBuiltin builtin args dst t u =>
    optMap2 (fun args' dst' => .callBuiltin builtin args' dst' t u)
      (mapOption (decodeOperand ts) args) (decodePlace ts dst)
  | .unsupported => some .unsupported

/-- Decode a `RefBasicBlock` against type table `ts`. -/
noncomputable def decodeBasicBlock (ts : List MirTy)
    (bb : RefBasicBlock) : Option BasicBlock :=
  optMap2 (fun stmts term => ⟨stmts, term, bb.cleanup⟩)
    (mapOption (decodeStmt ts) bb.statements)
    (decodeTerminator ts bb.terminator)

/-- Resolve a list of `TyId` local declarations against type table `ts`. -/
noncomputable def decodeLocalTys (ts : List MirTy) :
    List TyId → Option (List MirTy) :=
  mapOption (MirSemantics.getElem? ts)

/-- Decode a `RefBody` against type table `ts`. -/
noncomputable def decodeBody (ts : List MirTy) (b : RefBody) : Option Body :=
  optMap2 (fun locals bbs => ⟨b.argumentCount, locals, bbs, b.isUnsafe,
      b.identity⟩)
    (decodeLocalTys ts b.locals)
    (mapOption (decodeBasicBlock ts) b.basicBlocks)

/-- Total decoder inverting `encodeProg` (`∀ p, decodeProg (encodeProg p) =
some p`). -/
noncomputable def decodeProg (rp : RefProg) : Option Program :=
  optMap (fun bodies => ⟨bodies, rp.entryDefId, rp.pointerWidthBits,
      rp.mirProfileVersion, rp.scope⟩)
    (mapOption (decodeBody rp.types) rp.bodies)

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
the entry frame that owns its return destination slot `_0`. Active frames sit
above the sentinel in bottom-to-top order (`callerSentinelFrame retTy ::
active.reverse`), where the entry frame carries `returnCont = none` and each
callee frame pushed by `TerminatorKind.call` carries `returnCont = some cont`.
-/
structure RefFrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List RefLocalState
  isCallerSentinel : Bool := false
  returnCont : Option ReturnContinuation := none

/-- Reference machine state for $M_{\text{ref}}$, which executes
`Miri.Interpreter.Step.step` over
`StepState SlotVal LocalLayout Unit RefStepMachine` using Anneal-authored
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
`StepResult (StepState SlotVal LocalLayout Unit RefStepMachine) Bool`
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

Statement and terminator evaluators return the updated active call stack in
bottom-to-top order (`frames := active'.reverse`). On `.step`, this function
restores the caller `sentinel` beneath that stack and increments
`stepsExecuted`. -/
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

/-- Independent $M_{\text{ref}}$ lookup of variant `v`'s payload field types in
`ety`. -/
noncomputable def refFieldsForVariant? (ety : EnumTy) (v : Nat) :
    Option (List MirTy) :=
  if !Nat.blt v ety.discriminants.length ||
      !Nat.beq ety.variantFields.length ety.discriminants.length then
    none
  else
    MirSemantics.getElem? ety.variantFields v

/-- Independent $M_{\text{ref}}$ check whether `ety` has any variant with
payload fields. -/
noncomputable def refHasEnumPayloadFields (ety : EnumTy) : Bool :=
  ety.variantFields.any (fun fs => !fs.isEmpty)

mutual
  /-- Independent $M_{\text{ref}}$ structural uninhabitedness check matching
  `Miri.ABI.LayoutData.isUninhabited`. -/
  noncomputable def refIsTypeUninhabited : MirTy → Bool
    | .bool | .int _ _ | .unit => false
    | .never => true
    | .adtStruct ⟨_, fs⟩ => refAnyFieldUninhabited fs
    | .enum ⟨_, _, _, _, ds, vf⟩ =>
      if ds.isEmpty || !Nat.beq vf.length ds.length then
        true
      else
        refAllVariantsUninhabited vf
    | .tuple fs => refAnyFieldUninhabited fs
    | .array elemTy len => !Nat.beq len 0 && refIsTypeUninhabited elemTy
    | _ => true

  /-- Independent $M_{\text{ref}}$ check whether any field type in `tys` is
  uninhabited. -/
  noncomputable def refAnyFieldUninhabited : List MirTy → Bool
    | [] => false
    | ty :: tys => refIsTypeUninhabited ty || refAnyFieldUninhabited tys

  /-- Independent $M_{\text{ref}}$ check whether every variant field list in
  `vss` is uninhabited. -/
  noncomputable def refAllVariantsUninhabited : List (List MirTy) → Bool
    | [] => true
    | fs :: fss =>
      refAnyFieldUninhabited fs && refAllVariantsUninhabited fss
end

/-- Independent $M_{\text{ref}}$ per-variant uninhabitedness check matching
`Miri.ABI.LayoutData.isVariantUninhabited`. -/
noncomputable def refIsVariantUninhabited (ety : EnumTy) (v : Nat) : Bool :=
  match refFieldsForVariant? ety v with
  | none => true
  | some fs => refAnyFieldUninhabited fs

mutual
  /-- Independent $M_{\text{ref}}$ structural 0-byte ZST check (`Size.ZERO`). -/
  noncomputable def refIsZeroSizedTy : MirTy → Bool
    | .unit | .never => true
    | .bool | .int _ _ => false
    | .adtStruct ⟨_, fs⟩ => refAreAllZeroSizedTys fs
    | .enum ⟨_, _, _, tagRepr, ds, vf⟩ =>
      let zstFlags := refVariantZeroSizedFlags vf
      match tagRepr with
      | .zeroSized =>
        Nat.beq ds.length 1 && Nat.beq vf.length 1 &&
          !(zstFlags.any (fun b => !b))
      | .single v =>
        if !Nat.blt v ds.length || !Nat.beq vf.length ds.length then
          false
        else
          match MirSemantics.getElem? zstFlags v with
          | some b => b
          | none => false
      | .scalar _ _ | .niche _ _ _ _ _ _ _ _ _ => false
    | .tuple fs => refAreAllZeroSizedTys fs
    | .array elemTy len => Nat.beq len 0 || refIsZeroSizedTy elemTy
    | _ => false

  /-- Independent $M_{\text{ref}}$ check that all types in `tys` are 0-byte
  ZSTs. -/
  noncomputable def refAreAllZeroSizedTys : List MirTy → Bool
    | [] => true
    | ty :: tys => refIsZeroSizedTy ty && refAreAllZeroSizedTys tys

  /-- Independent $M_{\text{ref}}$ per-variant ZST flag list. -/
  noncomputable def refVariantZeroSizedFlags : List (List MirTy) → List Bool
    | [] => []
    | fs :: fss => refAreAllZeroSizedTys fs :: refVariantZeroSizedFlags fss
end

/-- Follow `path` inside a `MirTy` in $M_{\text{ref}}$ to locate the leaf scalar
type of an `EnumTagRepr.niche` layout. -/
noncomputable def refNicheResolveFromTy : MirTy → List Nat → Option MirTy
  | ty, [] => some ty
  | .adtStruct sty, idx :: rest =>
    match MirSemantics.getElem? sty.fields idx with
    | some fTy => refNicheResolveFromTy fTy rest
    | none => none
  | .tuple fs, idx :: rest =>
    match MirSemantics.getElem? fs idx with
    | some fTy => refNicheResolveFromTy fTy rest
    | none => none
  | .array elemTy len, idx :: rest =>
    if Nat.blt idx len then refNicheResolveFromTy elemTy rest else none
  | _, _ :: _ => none

/-- Resolve a non-empty `nichePath` from `untagged`'s payload fields in
$M_{\text{ref}}$. -/
noncomputable def refNicheLeafTy? (nichePath : List Nat)
    (varFields : List MirTy) : Option MirTy :=
  match nichePath with
  | [] => none
  | idx :: rest =>
    match MirSemantics.getElem? varFields idx with
    | some fTy => refNicheResolveFromTy fTy rest
    | none => none

/-- Independent $M_{\text{ref}}$ check that a niche leaf type matches primitive
tag representation `(tagW, tagS)`. -/
noncomputable def refNicheLeafMatchesTag (tagW : IntWidth) (tagS : Bool) :
    MirTy → Bool
  | .bool => IntWidth.beq tagW .i8 && !tagS
  | .int w s => IntWidth.beq w tagW && (s == tagS)
  | .enum innerEty =>
    match innerEty.tagRepr with
    | .scalar w s =>
      !refHasEnumPayloadFields innerEty && IntWidth.beq w tagW && (s == tagS)
    | _ => false
  | _ => false

/-- Check via `@Nat.rec` and `Miri.ABI.WrappingRange.contains` that every niche
tag `nicheStart + k` (`0 ≤ k < count`) truncated via `Miri.ABI.Size.truncate`
lies inside `⟨vs, ve⟩`. -/
noncomputable def refAllNicheTagsInValidRange (tagW : IntWidth)
    (vs ve nicheStart : BitVec 128) (count : Nat) : Bool :=
  let range : Miri.ABI.WrappingRange := ⟨vs, ve⟩
  let sz := toMiriSize tagW
  @Nat.rec (fun _ => Bool)
    true
    (fun k ih =>
      ih &&
        match sz.truncate (BitVec.ofNat 128 k + nicheStart) with
        | .ok trunc => range.contains trunc
        | .error _ => false)
    count

/-- Check via `@Nat.rec` in $M_{\text{ref}}$ that every variant `k < total` with
`k ≠ singleVar` is uninhabited. -/
noncomputable def refOtherVariantsUninhabited (ety : EnumTy) (singleVar : Nat)
    (total : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k ih => ih && (Nat.beq k singleVar || refIsVariantUninhabited ety k))
    total

/-- Check via `@Nat.rec` in $M_{\text{ref}}$ that every variant `k < total` with
`k ≠ untagged` is either uninhabited or niche-encoded (`start ≤ k ≤ last` with
ZST-only fields). -/
noncomputable def refOtherVariantsValidForNiche (ety : EnumTy)
    (untagged start last total : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k ih =>
      let okK : Bool :=
        if Nat.beq k untagged then
          true
        else if refIsVariantUninhabited ety k then
          true
        else
          Nat.ble start k &&
            Nat.ble k last &&
            match refFieldsForVariant? ety k with
            | some fs => refAreAllZeroSizedTys fs
            | none => false
      ih && okK)
    total

/-- Core non-recursive enum admission check in $M_{\text{ref}}$ using
`Miri.Memory.ScalarInt.tryFromUInt`, `Miri.ABI.Size.truncate`, and
`Miri.ABI.WrappingRange.contains`. -/
noncomputable def refEnumAdmittedCore (ety : EnumTy) : Bool :=
  !ety.discriminants.isEmpty &&
    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&
    Nat.beq ety.variantFields.length ety.discriminants.length &&
    ety.discriminants.all (fun d =>
      Nat.blt d (Nat.pow 2 128) &&
        match Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 d)
            (toMiriSize ety.discrWidth) with
        | .ok (some _) => true
        | .ok none => false
        | .error _ => false) &&
    refNatListPairwiseNe ety.discriminants &&
    match ety.tagRepr with
    | .zeroSized =>
      Nat.beq ety.discriminants.length 1 && !refHasEnumPayloadFields ety
    | .single v =>
      Nat.blt v ety.discriminants.length &&
        refOtherVariantsUninhabited ety v ety.discriminants.length
    | .scalar tagW tagS =>
      ety.discriminants.all (fun d =>
        let dBits := BitVec.ofNat 128 d
        match (toMiriSize tagW).truncate dBits with
        | .ok truncTag =>
          match refMiriTagToDiscrBits tagW tagS ety.discrWidth truncTag with
          | some recovered => recovered == dBits
          | none => false
        | .error _ => false)
    | .niche tagW tagS vs ve nichePath untagged start last nicheStart =>
      let sz := toMiriSize tagW
      let fitsTag (b : BitVec 128) : Bool :=
        match Miri.Memory.ScalarInt.tryFromUInt b sz with
        | .ok (some _) => true
        | _ => false
      !nichePath.isEmpty &&
        Nat.blt untagged ety.discriminants.length &&
        Nat.blt last ety.discriminants.length &&
        Nat.ble start last &&
        fitsTag vs &&
        fitsTag ve &&
        fitsTag nicheStart &&
        Nat.blt (last - start) (Nat.pow 2 tagW.bitWidth) &&
        refAllNicheTagsInValidRange tagW vs ve nicheStart
          (last - start + 1) &&
        refOtherVariantsValidForNiche ety untagged start last
          ety.discriminants.length &&
        match refFieldsForVariant? ety untagged with
        | none => false
        | some uFields =>
          match refNicheLeafTy? nichePath uFields with
          | some leafTy => refNicheLeafMatchesTag tagW tagS leafTy
          | none => false

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

mutual
  /-- Independent $M_{\text{ref}}$ supported local-type check: `.bool`, `.int`,
  `.unit`, `.never`, `.adtStruct`, admitted `.enum`, non-empty `.tuple`, or
  fixed `.array` (`len < 2^64`) of supported types. -/
  noncomputable def refIsSupportedLocalTy : MirTy → Bool
    | .bool | .int _ _ | .unit | .never => true
    | .adtStruct ⟨_, fs⟩ => refAreSupportedFieldTys fs
    | .enum ⟨id, dw, ds, tr, d, vf⟩ =>
      refEnumAdmittedCore ⟨id, dw, ds, tr, d, vf⟩ &&
        refAreSupportedVariantFieldLists vf
    | .tuple fields => !fields.isEmpty && refAreSupportedFieldTys fields
    | .array elemTy len =>
      Nat.blt len (Nat.pow 2 64) && refIsSupportedLocalTy elemTy
    | _ => false

  /-- Independent $M_{\text{ref}}$ check that every field type is a supported
  local type. -/
  noncomputable def refAreSupportedFieldTys : List MirTy → Bool
    | [] => true
    | ty :: tys => refIsSupportedLocalTy ty && refAreSupportedFieldTys tys

  /-- Independent $M_{\text{ref}}$ check that every variant's field list
  contains only supported local types. -/
  noncomputable def refAreSupportedVariantFieldLists :
      List (List MirTy) → Bool
    | [] => true
    | fs :: fss =>
      refAreSupportedFieldTys fs && refAreSupportedVariantFieldLists fss
end

/-- Independent $M_{\text{ref}}$ enum admission check (fieldless and payload,
including direct, single, and niche layouts). -/
noncomputable def refEnumAdmitted (ety : EnumTy) : Bool :=
  refEnumAdmittedCore ety && refAreSupportedVariantFieldLists ety.variantFields

/-- Independent $M_{\text{ref}}$ 0-byte ZST 1-variant fieldless enum check
(`Variants.Single 0`). -/
noncomputable def refIsZstEnumTy (ety : EnumTy) : Bool :=
  match ety.tagRepr with
  | .zeroSized => refEnumAdmitted ety
  | _ => false

/-- Independent $M_{\text{ref}}$ primitive-readable type check. -/
noncomputable def refIsPrimitiveReadableTy : MirTy → Bool
  | .bool | .int _ _ => true
  | _ => false

/-- Replicate `v : Val` `n` times in $M_{\text{ref}}$ via `@Nat.rec`. -/
noncomputable def refReplicateVal (n : Nat) (v : Val) : List Val :=
  @Nat.rec (fun _ => List Val) [] (fun _ ih => v :: ih) n

/-- Replicate `sv : SlotVal` `n` times in $M_{\text{ref}}$ via `@Nat.rec`. -/
noncomputable def refReplicateSlotVal (n : Nat) (sv : SlotVal) : List SlotVal :=
  @Nat.rec (fun _ => List SlotVal) [] (fun _ ih => sv :: ih) n

mutual
  /-- Independent $M_{\text{ref}}$ contents of a newly live slot of type `ty`:
  inhabited for 0-byte ZSTs, recursively initialized per field/element for
  structs, tuples, arrays, and inhabited `.single` enums, and `.uninit`
  otherwise. -/
  noncomputable def refUninitSlotVal : MirTy → SlotVal
    | .unit => .unit
    | .adtStruct ⟨id, fs⟩ => .structVal ⟨id, fs⟩ (refUninitSlotVals fs)
    | .enum ⟨id, dw, ds, tr, d, vf⟩ =>
      let ety : EnumTy := ⟨id, dw, ds, tr, d, vf⟩
      let initVfs := refUninitVariantSlotLists vf
      match tr with
      | .zeroSized =>
        if refEnumAdmittedCore ety && refAreSupportedVariantFieldLists vf then
          .enumVal ety 0 []
        else
          .uninit
      | .single v =>
        if !(refEnumAdmittedCore ety && refAreSupportedVariantFieldLists vf) ||
            refIsTypeUninhabited (.enum ety) then
          .uninit
        else
          match MirSemantics.getElem? initVfs v with
          | some initFs => .enumVal ety v initFs
          | none => .uninit
      | _ => .uninit
    | .tuple fields => .tuple (refUninitSlotVals fields)
    | .array elemTy len =>
      .array elemTy (refReplicateSlotVal len (refUninitSlotVal elemTy))
    | _ => .uninit

  /-- Independent $M_{\text{ref}}$ contents of newly live fields. -/
  noncomputable def refUninitSlotVals : List MirTy → List SlotVal
    | [] => []
    | ty :: tys => refUninitSlotVal ty :: refUninitSlotVals tys

  /-- Independent $M_{\text{ref}}$ contents of newly live variant field lists.
  -/
  noncomputable def refUninitVariantSlotLists :
      List (List MirTy) → List (List SlotVal)
    | [] => []
    | fs :: fss => refUninitSlotVals fs :: refUninitVariantSlotLists fss
end

/-- Independent $M_{\text{ref}}$ initial live slot for `ty`: allocated storage
holding `refUninitSlotVal ty`. -/
noncomputable def refLiveUninitSlot (ty : MirTy) : LocalSlot :=
  .live (refUninitSlotVal ty)

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

/-- Default 0-field `Miri.ABI.VariantLayout` template for `Variants.Multiple`.
-/
noncomputable def refInhabitedVariantLayout : Miri.ABI.VariantLayout := {
  size := Miri.ABI.Size.ZERO
  backendRepr := .Memory (sized := true)
  fieldOffsets := Array.empty
  fieldsInMemoryOrder := Array.empty
  largestNiche := none
  uninhabited := false
}

/-- Build per-variant `Miri.ABI.VariantLayout` entries recording
`refIsVariantUninhabited ety idx` for each variant `idx`. -/
noncomputable def refVariantLayoutsLoop (ety : EnumTy) :
    Nat → List Nat → List Miri.ABI.VariantLayout
  | _, [] => []
  | idx, _ :: rest =>
    { refInhabitedVariantLayout with
      uninhabited := refIsVariantUninhabited ety idx } ::
      refVariantLayoutsLoop ety (idx + 1) rest

/-- `Miri.ABI.LayoutData` for an enum `ety : EnumTy` across `.zeroSized`,
`.single`, `.scalar`, and `.niche` tag representations:
- `.zeroSized`: `Variants.Single 0` (`Size.ZERO`);
- `.single v₀`: `Variants.Single v₀` (`Size.ZERO` if ZST, else 8 bytes);
- `.scalar tagW tagS`: `Variants.Multiple tag .Direct 0 variants`;
- `.niche tagW tagS vs ve _ untagged start last nicheStart`:
  `Variants.Multiple tag (.Niche untagged start last nicheStart) 0 variants`
  with `tag := .Initialized (.Int (toMiriInteger tagW) tagS) ⟨vs, ve⟩`. -/
noncomputable def refEnumLayoutData (ety : EnumTy) : Miri.ABI.LayoutData :=
  let uninh := refIsTypeUninhabited (.enum ety)
  match ety.tagRepr with
  | .zeroSized =>
    { refBaseLayoutData (.Memory (sized := true)) Miri.ABI.Size.ZERO with
      uninhabited := uninh }
  | .single v₀ =>
    let sz :=
      if refIsZeroSizedTy (.enum ety) then
        Miri.ABI.Size.ZERO
      else
        Miri.ABI.Size.ofBytes 8
    { refBaseLayoutData (.Memory (sized := true)) sz with
      variants := .Single v₀
      uninhabited := uninh }
  | .scalar tagW tagS =>
    let tag : Miri.ABI.Scalar :=
      .Union (value := .Int (toMiriInteger tagW) tagS)
    let variants := Array.mk (refVariantLayoutsLoop ety 0 ety.discriminants)
    { refScalarLayoutData tagW tagS with
      variants := .Multiple tag .Direct 0 variants
      uninhabited := uninh }
  | .niche tagW tagS vs ve _ untagged start last nicheStart =>
    let tag : Miri.ABI.Scalar :=
      .Initialized (value := .Int (toMiriInteger tagW) tagS)
        (validRange := ⟨vs, ve⟩)
    let variants := Array.mk (refVariantLayoutsLoop ety 0 ety.discriminants)
    { refScalarLayoutData tagW tagS with
      variants :=
        .Multiple tag (.Niche untagged start last nicheStart) 0 variants
      uninhabited := uninh }

/-- Single `Miri.Interpreter.DiscriminantHooks` adapter for read-only
`Miri.Interpreter.Discriminant.readDiscriminant` and
`Miri.Interpreter.Discriminant.discriminantForVariant` over `ety : EnumTy`. -/
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
      .error (.invalidProgram "non-zero tag field on enum") s
  readImmediate := fun _ op s =>
    match op.op with
    | .immediate .uninit =>
      .error (.undefinedBehavior "InvalidUninitBytes(None)") s
    | .immediate imm => .ok ⟨imm, op.layout⟩ s
    | .indirect _ => .error (.unsupported "memory enum place unsupported") s
  destLayout := fun _ =>
    ⟨1, refScalarLayoutData ety.discrWidth ety.discrSigned⟩
  projectWrite := fun _ _ _ s =>
    .error (.unsupported "write not supported on read-only DiscriminantHooks") s
  writeScalar := fun _ _ _ s =>
    .error (.unsupported "write not supported on read-only DiscriminantHooks") s
  toOp := fun _ _ s =>
    .error (.unsupported "write not supported on read-only DiscriminantHooks") s
  scalarMayBeNull := fun _ _ s => .ok true s
}

/-- Extract raw scalar bits along `path` inside a `Val` in $M_{\text{ref}}$ for
niche-tag validity checking. -/
noncomputable def refExtractValNicheBits : Val → List Nat → Option (BitVec 128)
  | .bool b, [] => some (BitVec.ofNat 128 (if b then 1 else 0))
  | .scalar sv, [] => some (miriScalar sv.width sv.bits).data
  | .enumVal innerEty innerVar [], [] =>
    match innerEty.tagRepr,
        MirSemantics.getElem? innerEty.discriminants innerVar with
    | .scalar w _, some d =>
      some (miriScalar w (BitVec.ofNat 128 d)).data
    | _, _ => none
  | .structVal _ fs, idx :: rest =>
    match MirSemantics.getElem? fs idx with
    | some fVal => refExtractValNicheBits fVal rest
    | none => none
  | .tuple fs, idx :: rest =>
    match MirSemantics.getElem? fs idx with
    | some fVal => refExtractValNicheBits fVal rest
    | none => none
  | .array _ elems, idx :: rest =>
    match MirSemantics.getElem? elems idx with
    | some eVal => refExtractValNicheBits eVal rest
    | none => none
  | _, _ => none

/-- Extract raw scalar bits along non-empty `nichePath` inside `fields :
List Val` in $M_{\text{ref}}$. -/
noncomputable def refExtractValNicheBitsFromFields (nichePath : List Nat)
    (fields : List Val) : Option (BitVec 128) :=
  match nichePath with
  | [] => none
  | idx :: rest =>
    match MirSemantics.getElem? fields idx with
    | some fVal => refExtractValNicheBits fVal rest
    | none => none

/-- Validate niche-tag invariants on `.enumVal ety variant fields` in
$M_{\text{ref}}$ by delegating untagged-variant niche decoding directly to
`Miri.Interpreter.Discriminant.readDiscriminant`. -/
noncomputable def refEnumValNicheValid (ety : EnumTy) (variant : Nat)
    (fields : List Val) : Bool :=
  match ety.tagRepr with
  | .niche tagW _ _ _ nichePath untagged start last _ =>
    if Nat.beq variant untagged then
      match refExtractValNicheBitsFromFields nichePath fields with
      | none => false
      | some bits =>
        match Miri.Memory.ScalarInt.truncateFromUInt bits
            (toMiriSize tagW) with
        | .ok (tagSc, _) =>
          let op : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
            ⟨.immediate (.scalar (.fromScalarInt tagSc)),
              ⟨0, refEnumLayoutData ety⟩⟩
          match Miri.Interpreter.Discriminant.readDiscriminant
              (refDiscriminantHooks Unit ety) () op () with
          | .ok decoded _ => Nat.beq decoded untagged
          | .error _ _ => false
        | .error _ => false
    else
      Nat.ble start variant && Nat.ble variant last
  | .single v => Nat.beq variant v
  | .zeroSized => Nat.beq variant 0
  | .scalar _ _ => true

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
  | .adtStruct sty, .zeroSized =>
    if refAreSupportedFieldTys sty.fields && refAreAllZeroSizedTys sty.fields &&
        !refIsTypeUninhabited (.adtStruct sty) then
      match (refUninitSlotVal (.adtStruct sty)).toVal? with
      | some v => .ok v
      | none => .error .unsupported
    else
      .error .unsupported
  | .array elemTy 0, .zeroSized =>
    if refIsSupportedLocalTy elemTy then
      .ok (.array elemTy [])
    else
      .error .unsupported
  | .enum ety, .zeroSized =>
    if refIsZstEnumTy ety then
      .ok (.enumVal ety 0 [])
    else
      match ety.tagRepr with
      | .single v₀ =>
        if refEnumAdmitted ety && !refIsVariantUninhabited ety v₀ then
          match refFieldsForVariant? ety v₀ with
          | some [] => .ok (.enumVal ety v₀ [])
          | _ => .error .unsupported
        else
          .error .unsupported
      | _ => .error .unsupported
  | .enum ety, .scalar bits =>
    if !refEnumAdmitted ety then
      .error .unsupported
    else
      match ety.tagRepr with
      | .scalar tagW _ | .niche tagW _ _ _ _ _ _ _ _ =>
        match Miri.Memory.ScalarInt.tryFromUInt bits (toMiriSize tagW) with
        | .ok (some sc) =>
          let op : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
            ⟨.immediate (.scalar (.fromScalarInt sc)),
              ⟨0, refEnumLayoutData ety⟩⟩
          match Miri.Interpreter.Discriminant.readDiscriminant
              (refDiscriminantHooks Unit ety) () op () with
          | .ok v _ =>
            match refFieldsForVariant? ety v with
            | some [] => .ok (.enumVal ety v [])
            | _ => .error .unsupported
          | .error (.undefinedBehavior _) _
          | .error (.stack (.localExpectedLive _)) _ => .error .undefined
          | .error _ _ => .error .unsupported
        | _ => .error .unsupported
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
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

On integers, `.AddWithOverflow`, `.SubWithOverflow`, and `.MulWithOverflow`
return the two-field tuple `(wrapped, overflowed)` that
`Miri.Interpreter.IntegerOps.binary` reports as
`IntegerResult.withOverflow`, matching `binary_op`:

> "return interp_ok(if with_overflow {
>     let overflow = ImmTy::from_bool(overflow, *self.tcx);
>     ImmTy::from_pair(res, overflow, self)
> } else {
>     res
> });" -/
noncomputable def evalRefMiriBinOp (op : Miri.MIR.BinOp) (lhs rhs : Val) :
    Except FaultKind Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    match op with
    | .Offset => .error .unsupported
    | .AddWithOverflow | .SubWithOverflow | .MulWithOverflow =>
      match Miri.Interpreter.IntegerOps.binary op
          (miriIntValue l) (miriIntValue r) with
      | .ok (.withOverflow sc overflow) =>
        .ok (.tuple [.scalar ⟨l.width, l.signed, sc.data⟩, .bool overflow])
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported
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

/-- Reference `IntToInt` cast evaluator calling
`Miri.Interpreter.IntegerCast.cast`
(`vendor/lean-miri/Miri/Interpreter/IntegerCast.lean`), matching
`cast_from_int_like` in `compiler/rustc_const_eval/src/interpret/cast.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "let v = match src_layout.ty.kind() {
>     ty::Uint(_) | ty::RawPtr(..) | ty::FnPtr(..) =>
>         scalar.to_uint(src_layout.size)?,
>     ty::Int(_) => scalar.to_int(src_layout.size)? as u128,
>     ty::Bool => scalar.to_bool()?.into(),
>     ty::Char => scalar.to_char()?.into(),
>     ...
> };
>
> interp_ok(match *cast_ty.kind() {
>     // int -> int
>     ty::Int(_) | ty::Uint(_) => {
>         let size = match *cast_ty.kind() { ... };
>         let v = size.truncate(v);
>         Scalar::from_uint(v, size)
>     }
>     ...
> })"

Casts an integer or `bool` source `src` to the integer target type `castTy`.
A target type that is not an integer type, or a source that is neither an
integer nor a `bool`, returns `.error .unsupported`. -/
noncomputable def evalRefMiriIntToIntCast (src : Val) (castTy : MirTy) :
    Except FaultKind Val :=
  match castTy with
  | .int w s =>
    let target : Miri.Interpreter.IntegerCastTarget :=
      .integer (toMiriIntType w s)
    match src with
    | .scalar sv =>
      match Miri.Interpreter.IntegerCast.cast
          (.integer (toMiriIntType sv.width sv.signed))
          (miriScalar sv.width sv.bits) target with
      | .ok sc => .ok (.scalar ⟨w, s, sc.data⟩)
      | .error _ => .error .unsupported
    | .bool b =>
      match Miri.Interpreter.IntegerCast.cast .boolean
          (Miri.Memory.ScalarInt.ofBool b) target with
      | .ok sc => .ok (.scalar ⟨w, s, sc.data⟩)
      | .error _ => .error .unsupported
    | _ => .error .unsupported
  | _ => .error .unsupported

mutual
  /-- Reference scalar/boolean/unit/struct/enum/tuple/array value validity and
  type check calling `Miri.Memory.ScalarInt.tryFromUInt`,
  `Miri.Memory.ScalarInt.ofBool`, and
  `Miri.Interpreter.Discriminant.readDiscriminant` (via
  `refEnumValNicheValid`). -/
  noncomputable def checkRefVal : Val → MirTy → Bool
    | .scalar sv, .int w s =>
      match Miri.Memory.ScalarInt.tryFromUInt sv.bits
          (toMiriSize sv.width) with
      | .ok (some _) => IntWidth.beq sv.width w && (sv.signed == s)
      | _ => false
    | .bool b, .bool =>
      match (Miri.Memory.ScalarInt.ofBool b).tryToBool with
      | .ok _ => true
      | .error _ => false
    | .unit, .unit => true
    | .structVal sty fields, .adtStruct dstSty =>
      refAreSupportedFieldTys sty.fields &&
        !refIsTypeUninhabited (.adtStruct sty) &&
        checkRefVals fields sty.fields &&
        StructTy.beq sty dstSty
    | .enumVal ety v fields, .enum ety' =>
      refEnumAdmitted ety &&
        !refIsVariantUninhabited ety v &&
        refEnumValNicheValid ety v fields &&
        (match refFieldsForVariant? ety v with
         | some expectedTys => checkRefVals fields expectedTys
         | none => false) &&
        EnumTy.beq ety ety'
    | .tuple fields, .tuple fieldTys =>
      !fields.isEmpty && checkRefVals fields fieldTys
    | .array elemTy elems, .array dstElemTy len =>
      refIsSupportedLocalTy elemTy &&
        Nat.blt elems.length (Nat.pow 2 64) &&
        !(!Nat.beq elems.length 0 && refIsTypeUninhabited elemTy) &&
        checkRefAllHaveTy elems elemTy &&
        MirTy.beq elemTy dstElemTy &&
        Nat.beq elems.length len
    | _, _ => false

  /-- Check field values `vs` against field types `tys` position by position
  under `checkRefVal`, requiring equal lengths. -/
  noncomputable def checkRefVals : List Val → List MirTy → Bool
    | [], [] => true
    | v :: vs, ty :: tys => checkRefVal v ty && checkRefVals vs tys
    | _, _ => false

  /-- Check that every element of `vs` has type `elemTy` under `checkRefVal`. -/
  noncomputable def checkRefAllHaveTy : List Val → MirTy → Bool
    | [], _ => true
    | v :: vs, elemTy => checkRefVal v elemTy && checkRefAllHaveTy vs elemTy
end

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
reference stack has one fixed shape. Returning or unwinding from the entry
frame ends the execution with `.returned` or `.unwound` (`evalRefTerminator`)
instead of resuming the sentinel. Its `defId`, `blockIdx`, and `stmtIdx` are
unused. -/
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
          | some v => .live v.toSlotVal
          | none => .dead
        else if refHasStorageAnnotation rbody idx then
          .dead
        else
          refLiveUninitSlot ty
      ⟨slot, some ty⟩ :: initRefLocalsLoop rbody args (idx + 1) rest

/-- Independent $M_{\text{ref}}$ static body-entry admission check shared by
`initRefState` and `refCallHooks.findMirOrEvalFn`: checks non-empty basic
blocks, `argumentCount < localTys.length`, in-bounds storage annotations, and
supported local types (`refIsSupportedLocalTy`). -/
noncomputable def refBodyEntryAdmitted (rbody : RefBody)
    (localTys : List MirTy) : Bool :=
  !rbody.basicBlocks.isEmpty &&
    Nat.blt rbody.argumentCount localTys.length &&
    refStorageAnnotationsInBounds rbody &&
    localTys.all refIsSupportedLocalTy

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
        if !refBodyEntryAdmitted rbody localTys then
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

/-! ### `Miri.Interpreter` Evaluator Wiring Adapters -/

/-- Canonical 8-byte sized `Miri.Interpreter.LocalLayout` (`isZst = false`) used
as a fixed placeholder at adapter sites that do not branch on per-type size.

Authoritative call-site list: `mkSingleLocalMiriFrame` (which feeds
`mkRefStepStateWith`, `mkRefTermStepState`, `writeRefPlace`, and
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
local type—including non-ZST types, tuples, and uninhabited `!`
(`MirTy.never`). Note that although `rustc` treats `!` as a 0-byte ZST, using
`refSizedLocalLayout` (`isZst = false`) for `.never` makes moving a `!` local
take Miri's non-ZST deinitialization path (`.live .uninit`), and the difference
is unobservable because `!` is uninhabited and can never be initialized, read,
or written. A tuple also takes the non-ZST path even when all of its fields are
ZSTs; this is unobservable too, because `evalRefPlaceOperand` records a
moved-out local as `refLiveUninitSlot ty` on both paths, which keeps every ZST
field initialized.
`StorageLive` (`refStepHooksFor.storageLive`) does not call
`refLocalLayoutForTy`: it runs `Miri.Interpreter.Frame.storageLive` on a dummy
dead local `0` (where `refLocalStorageHooks.veryTriviallySized` returns
`.ok true` so `refLocalStorageHooks.layout` is skipped and the call always
returns `.ok ()`), discards the resulting Miri frame, and writes
`refLiveUninitSlot localTy` directly (whose catch-all arm initializes `!` to
`.live .uninit`). -/
noncomputable def refLocalLayoutForTy (ty : MirTy) :
    Miri.Interpreter.LocalLayout :=
  if refIsZeroSizedTy ty && !refIsTypeUninhabited ty then
    refLocalLayoutZst
  else
    refSizedLocalLayout

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

/-- Lift a `LocalSlot` into `Miri.Interpreter.LocalValue SlotVal`.

A live adapter local is stored in Miri frames as an initialized pointer
immediate that carries its `SlotVal` contents as provenance, whether or not
those contents are initialized. An uninitialized local (`.live .uninit`, or a
tuple with an `.uninit` field) is therefore never `Immediate.uninit`, so
Miri's own `.uninit` check never fires on adapter frames and
uninitialized-read UB is enforced explicitly by the adapter hooks through
`SlotVal.toVal?` (`readRefPrimitiveSlot`, `refRvalueHooks.copyOp`,
`refAggregateHooks.copyOpNoValidate`, `refControlHooksFor.copyReturn`, and
`encodeRefEnumTagOp` -> `Miri.Interpreter.Discriminant.readDiscriminant`). -/
noncomputable def slotToMiriLocalValue :
    LocalSlot → Miri.Interpreter.LocalValue SlotVal
  | .dead => .dead
  | .live sv => .live (.immediate (payloadToMiriImmediate sv))

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
noncomputable def mkSingleLocalMiriFrameWithLayout {Prov : Type}
    (lv : Miri.Interpreter.LocalValue Prov)
    (layout : Miri.Interpreter.LocalLayout) (cleanup : Bool) :
    Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Unit := {
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
noncomputable def mkSingleLocalMiriFrame {Prov : Type}
    (lv : Miri.Interpreter.LocalValue Prov) (cleanup : Bool) :
    Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Unit :=
  mkSingleLocalMiriFrameWithLayout lv refSizedLocalLayout cleanup

/-- Construct a two-local `Miri.Interpreter.Frame` holding `lv₀` at `_0` and
`lv₁` at `_1` for `Miri.Interpreter.Frame.storageDead` (which forbids
`StorageDead` on return place `_0` and deallocates `_1`). -/
noncomputable def mkTwoLocalMiriFrame
    (lv₀ lv₁ : Miri.Interpreter.LocalValue SlotVal) :
    Miri.Interpreter.Frame SlotVal Miri.Interpreter.LocalLayout Unit := {
  mkSingleLocalMiriFrame lv₀ false with
  locals := Array.mk [⟨lv₀, some refSizedLocalLayout⟩,
                      ⟨lv₁, some refSizedLocalLayout⟩]
}

/-- `Miri.Interpreter.LocalAccessHooks` with `deinitMovedPlace` configured for
`Miri.Interpreter.evalOperand` and `Miri.Interpreter.evalPlaceToOp`.

`project` fails closed: the adapter passes only unprojected places to these two
functions, because an adapter local is not Miri memory. Each live local is
stored in its single-local frame as one immediate that carries the local's
whole `SlotVal` (see `slotToMiriLocalValue`), so the adapter applies place
projections to that `SlotVal` itself (`refProjectPlaceTy?`,
`refReadPlaceSlotPath?`, and `refWritePlaceSlotPath?`) after Miri has read the
local. -/
noncomputable def refLocalAccessHooks (deinitMovedPlace : Bool) :
    Miri.Interpreter.LocalAccessHooks SlotVal Unit Unit := {
  layout := fun frame state _ _ => ⟨frame, state, .ok refSizedLocalLayout⟩
  validationInProgress := fun _ => true
  afterLocalRead := fun frame state _ => ⟨frame, state, .ok ()⟩
  project := fun frame state _ _ =>
    ⟨frame, state, .error (.resolver "projections applied by the adapter")⟩
  checkPlaceType := fun frame state _ _ => ⟨frame, state, .ok ()⟩
  runtimeChecks := fun frame state _ =>
    ⟨frame, state, .error (.resolver "runtimeChecks unsupported")⟩
  constant := fun frame state _ _ =>
    ⟨frame, state, .error (.resolver "constant handled via evalRefConstLit")⟩
  deinitMovedPlace := deinitMovedPlace
}

/-- Independent $M_{\text{ref}}$ projected place type (`MirTy` or downcasted
enum variant awaiting `.Field`), mirroring `rustc_middle::mir::tcx::PlaceTy`. -/
inductive RefPlaceTy where
  | ty (t : MirTy)
  | variant (ety : EnumTy) (variantIdx : Nat)

/-- Step-by-step static type projection in $M_{\text{ref}}$ over `RefPlaceTy`
for `.Field`, `.Downcast`, `.ConstantIndex`, and `.Index`. -/
noncomputable def refProjectPlaceTy? (types : List MirTy) :
    RefPlaceTy → List Miri.MIR.ProjectionElem → Option RefPlaceTy
  | pty, [] => some pty
  | .ty (.tuple fieldTys), .Field idx tyId :: rest =>
    match MirSemantics.getElem? fieldTys idx,
        MirSemantics.getElem? types tyId with
    | some fieldTy, some statedTy =>
      if MirTy.beq fieldTy statedTy then
        refProjectPlaceTy? types (.ty fieldTy) rest
      else
        none
    | _, _ => none
  | .ty (.adtStruct sty), .Field idx tyId :: rest =>
    match MirSemantics.getElem? sty.fields idx,
        MirSemantics.getElem? types tyId with
    | some fieldTy, some statedTy =>
      if MirTy.beq fieldTy statedTy then
        refProjectPlaceTy? types (.ty fieldTy) rest
      else
        none
    | _, _ => none
  | .variant ety v, .Field idx tyId :: rest =>
    match refFieldsForVariant? ety v, MirSemantics.getElem? types tyId with
    | some varFields, some statedTy =>
      match MirSemantics.getElem? varFields idx with
      | some fieldTy =>
        if MirTy.beq fieldTy statedTy then
          refProjectPlaceTy? types (.ty fieldTy) rest
        else
          none
      | none => none
    | _, _ => none
  | .ty (.enum ety), .Downcast _ v :: rest =>
    if refEnumAdmitted ety && Nat.blt v ety.discriminants.length then
      refProjectPlaceTy? types (.variant ety v) rest
    else
      none
  | .ty (.array elemTy len), .ConstantIndex _ _ _ :: rest =>
    if Nat.blt len (Nat.pow 2 64) then
      refProjectPlaceTy? types (.ty elemTy) rest
    else
      none
  | .ty (.array elemTy len), .Index _ :: rest =>
    if Nat.blt len (Nat.pow 2 64) then
      refProjectPlaceTy? types (.ty elemTy) rest
    else
      none
  | _, _ :: _ => none

/-- Static type of the place reached from `ty` by `proj` in $M_{\text{ref}}$, or
`none` if ill-typed or ending in a bare `.Downcast`. -/
noncomputable def refProjectTy? (types : List MirTy) (ty : MirTy)
    (proj : List Miri.MIR.ProjectionElem) : Option MirTy :=
  match refProjectPlaceTy? types (.ty ty) proj with
  | some (.ty resTy) => some resTy
  | _ => none

/-- Read a `usize` array-index local in $M_{\text{ref}}$ via
`Miri.Interpreter.evalPlaceToOp` without moving it, for
`Miri.Interpreter.ProjectionCx.localIndex`. -/
noncomputable def refProjLocalIndex (rlocals : List RefLocalState)
    (idxLocal : LocalId) : Except Miri.Interpreter.ProjectionError UInt64 :=
  match MirSemantics.getElem? rlocals idxLocal with
  | some ⟨slot, some (.int .isize false)⟩ =>
    let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
    match Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false) frame₀ ()
        ⟨0, Array.empty⟩ (some refSizedLocalLayout) with
    | ⟨_, _, .ok ⟨.immediate imm, _⟩⟩ =>
      match miriImmediateToPayload? imm with
      | some (.scalar sv) =>
        .ok (UInt64.ofNat (miriScalar .isize sv.bits).data.toNat)
      | some .uninit =>
        .error (.machineError (.undefinedBehavior "uninit usize index local"))
      | _ => .error (.invariant "non-scalar usize index local")
    | _ => .error (.machineError (.undefinedBehavior "dead usize index local"))
  | _ => .error (.invariant "non-usize index local")

/-- Construct the base `OpTy Miri.Memory.Provenance` layout for a single
`Miri.Interpreter.project` step from `curPty : RefPlaceTy` and `elem`. -/
noncomputable def refBaseOpForProjStep (curPty : RefPlaceTy)
    (elem : Miri.MIR.ProjectionElem) :
    Miri.Interpreter.OpTy Miri.Memory.Provenance :=
  let fieldsShape : Miri.ABI.FieldsShape :=
    match curPty, elem with
    | .ty (.tuple fieldTys), .Field _ _ =>
      .Arbitrary (Array.replicate fieldTys.length Miri.ABI.Size.ZERO)
        Array.empty
    | .ty (.adtStruct sty), .Field _ _ =>
      .Arbitrary (Array.replicate sty.fields.length Miri.ABI.Size.ZERO)
        Array.empty
    | .variant ety v, .Field _ _ =>
      match refFieldsForVariant? ety v with
      | some varFields =>
        .Arbitrary (Array.replicate varFields.length Miri.ABI.Size.ZERO)
          Array.empty
      | none => .Primitive
    | .ty (.array _ len), .ConstantIndex _ _ _
    | .ty (.array _ len), .Index _ =>
      if Nat.blt len (Nat.pow 2 64) then
        .Array (Miri.ABI.Size.ofBytes 1) (UInt64.ofNat len)
      else
        .Primitive
    | _, _ => .Primitive
  let layoutData : Miri.ABI.LayoutData :=
    { refSizedLocalLayout.layout with fields := fieldsShape }
  ⟨.indirect ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩, ⟨0, layoutData⟩⟩

/-- Build the `Miri.Interpreter.ProjectionCx` for a single step of
`Miri.Interpreter.project` at `curPty`. -/
noncomputable def refProjectionCx (curPty : RefPlaceTy)
    (localIndexFn : Miri.MIR.LocalId →
      Except Miri.Interpreter.ProjectionError UInt64) :
    Miri.Interpreter.ProjectionCx Miri.Memory.Provenance := {
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  maxSizeOfVal := Miri.ABI.Size.ofBytes (UInt64.ofNat (Nat.pow 2 64 - 1))
  isSliceOrStr := fun _ => .ok false
  field := fun _ idx =>
    match curPty with
    | .ty (.tuple fieldTys) =>
      match MirSemantics.getElem? fieldTys idx with
      | some _ => .ok refSizedLocalLayout
      | none => .error (.invariant "tuple field out of bounds")
    | .ty (.adtStruct sty) =>
      match MirSemantics.getElem? sty.fields idx with
      | some _ => .ok refSizedLocalLayout
      | none => .error (.invariant "struct field out of bounds")
    | .variant ety v =>
      match refFieldsForVariant? ety v with
      | some varFields =>
        match MirSemantics.getElem? varFields idx with
        | some _ => .ok refSizedLocalLayout
        | none => .error (.invariant "variant field out of bounds")
      | none => .error (.invariant "variant out of bounds")
    | .ty (.array _ len) =>
      if Nat.blt len (Nat.pow 2 64) && Nat.beq idx 0 then
        .ok refSizedLocalLayout
      else
        .error (.invariant "invalid array element layout query")
    | _ => .error (.invariant "field projection on non-aggregate")
  variant := fun _ v =>
    match curPty with
    | .ty (.enum ety) =>
      if refEnumAdmitted ety && Nat.blt v ety.discriminants.length then
        .ok refSizedLocalLayout
      else
        .error (.invariant "invalid enum downcast")
    | _ => .error (.invariant "downcast on non-enum")
  dynamicAlign := fun _ _ => .ok none
  packedAlign := fun _ => .ok none
  immediateOffset := fun imm _ _ _ => .ok imm
  memoryOffset := fun mp offset _ _ => .ok { mp with ptr := ⟨offset, none⟩ }
  subsliceLayout := fun _ _ => .error (.obligation "Subslice unsupported")
  layoutOf := fun _ => .error (.obligation "UnwrapUnsafeBinder unsupported")
  deref := fun _ => .error (.obligation "Deref unsupported")
  localIndex := fun localId =>
    match curPty with
    | .ty (.array _ len) =>
      if Nat.blt len (Nat.pow 2 64) then
        localIndexFn localId
      else
        .error (.invariant "oversized array length")
    | _ => .error (.invariant "index on non-array")
}

/-- Map a `Miri.Interpreter.ProjectionError` to $M_{\text{anneal}}$'s two-pole
`FaultKind`. -/
noncomputable def projErrorToFaultKind :
    Miri.Interpreter.ProjectionError → FaultKind
  | .bounds _ _ => .undefined
  | .machineError (.undefinedBehavior _) => .undefined
  | .machineError (.stack (.localExpectedLive _)) => .undefined
  | _ => .unsupported

/-- Execute a single projection step via `Miri.Interpreter.project`
(`projectField`, `projectDowncast`, `projectIndex`, `projectConstantIndex`),
returning the next `RefPlaceTy` and canonicalized `Miri.MIR.ProjectionElem`. -/
noncomputable def refProjectStep (types : List MirTy)
    (localIndexFn : Miri.MIR.LocalId →
      Except Miri.Interpreter.ProjectionError UInt64)
    (curPty : RefPlaceTy) (elem : Miri.MIR.ProjectionElem) :
    Except FaultKind (RefPlaceTy × Miri.MIR.ProjectionElem) :=
  let cx := refProjectionCx curPty localIndexFn
  let base := refBaseOpForProjStep curPty elem
  match Miri.Interpreter.project cx base elem with
  | .error err => .error (projErrorToFaultKind err)
  | .ok outOp =>
    match curPty, elem with
    | .ty (.tuple fieldTys), .Field idx tyId =>
      match MirSemantics.getElem? fieldTys idx,
          MirSemantics.getElem? types tyId with
      | some fieldTy, some statedTy =>
        if MirTy.beq fieldTy statedTy then
          .ok (.ty fieldTy, .Field idx tyId)
        else
          .error .unsupported
      | _, _ => .error .unsupported
    | .ty (.adtStruct sty), .Field idx tyId =>
      match MirSemantics.getElem? sty.fields idx,
          MirSemantics.getElem? types tyId with
      | some fieldTy, some statedTy =>
        if MirTy.beq fieldTy statedTy then
          .ok (.ty fieldTy, .Field idx tyId)
        else
          .error .unsupported
      | _, _ => .error .unsupported
    | .variant ety v, .Field idx tyId =>
      match refFieldsForVariant? ety v, MirSemantics.getElem? types tyId with
      | some varFields, some statedTy =>
        match MirSemantics.getElem? varFields idx with
        | some fieldTy =>
          if MirTy.beq fieldTy statedTy then
            .ok (.ty fieldTy, .Field idx tyId)
          else
            .error .unsupported
        | none => .error .unsupported
      | _, _ => .error .unsupported
    | .ty (.enum ety), .Downcast _ v =>
      .ok (.variant ety v, .Downcast none v)
    | .ty (.array elemTy _), .ConstantIndex _ _ _
    | .ty (.array elemTy _), .Index _ =>
      match outOp.op with
      | .indirect mp =>
        let idx := mp.ptr.offset.bytes.toNat
        .ok (.ty elemTy, .ConstantIndex idx (idx + 1) false)
      | .immediate _ => .error .unsupported
    | _, _ => .error .unsupported

/-- Resolve a `List Miri.MIR.ProjectionElem` left-to-right via
`Miri.Interpreter.project`, turning `.Index` and `.ConstantIndex` steps into
canonical in-bounds `.ConstantIndex idx (idx + 1) false` steps. -/
noncomputable def refResolveProjPath (types : List MirTy)
    (rlocals : List RefLocalState) :
    RefPlaceTy → List Miri.MIR.ProjectionElem →
      Except FaultKind (List Miri.MIR.ProjectionElem)
  | .ty _, [] => .ok []
  | .variant _ _, [] => .error .unsupported
  | curPty, elem :: rest =>
    match refProjectStep types (refProjLocalIndex rlocals) curPty elem with
    | .error k => .error k
    | .ok (nextPty, canonElem) =>
      match refResolveProjPath types rlocals nextPty rest with
      | .ok rest' => .ok (canonElem :: rest')
      | .error k => .error k

/-- Project element `index` of a fixed array `.array elemTy len` via
`Miri.Interpreter.projectArrayFields` and
`Miri.Interpreter.ProjectionArrayIterator.next`
(`vendor/lean-miri/Miri/Interpreter/Projection.lean`) for array aggregate
construction. -/
noncomputable def refProjectArrayAggregateElem (elemTy : MirTy) (len index : Nat) :
    Except Miri.Interpreter.StepError Miri.MIR.ProjectionElem :=
  let arrPty : RefPlaceTy := .ty (.array elemTy len)
  let cx := refProjectionCx arrPty
    (fun _ => .error (.invariant "no dynamic localIndex in array aggregate"))
  let fieldsShape : Miri.ABI.FieldsShape :=
    .Array Miri.ABI.Size.ZERO (UInt64.ofNat len)
  let base : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
    ⟨.indirect ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩,
      ⟨0, { refSizedLocalLayout.layout with fields := fieldsShape }⟩⟩
  match Miri.Interpreter.projectArrayFields cx base refLocalLayoutZst with
  | .error _ => .error (.unsupported "projectArrayFields failed")
  | .ok iter =>
    if !Nat.blt index len then
      .error (.unsupported "array aggregate element index out of bounds")
    else
      let iterAtIdx := { iter with nextIndex := UInt64.ofNat index }
      match Miri.Interpreter.ProjectionArrayIterator.next cx iterAtIdx with
      | .ok (some (idxU64, _)) _ =>
        let idx := idxU64.toNat
        .ok (.ConstantIndex idx (idx + 1) false)
      | _ => .error (.unsupported "ProjectionArrayIterator.next failed")

/-- Independent $M_{\text{ref}}$ subslot reader over canonicalized projections
starting at `pty : RefPlaceTy`. -/
noncomputable def refReadPlaceSlotPath? :
    RefPlaceTy → SlotVal → List Miri.MIR.ProjectionElem → Option SlotVal
  | .ty _, sv, [] => some sv
  | .variant _ _, _, [] => none
  | .ty (.tuple fieldTys), .tuple fields, .Field idx _ :: rest =>
    match MirSemantics.getElem? fieldTys idx,
        MirSemantics.getElem? fields idx with
    | some fTy, some field => refReadPlaceSlotPath? (.ty fTy) field rest
    | _, _ => none
  | .ty (.adtStruct sty), .structVal sty' fields, .Field idx _ :: rest =>
    if !StructTy.beq sty sty' then
      none
    else
      match MirSemantics.getElem? sty.fields idx,
          MirSemantics.getElem? fields idx with
      | some fTy, some field => refReadPlaceSlotPath? (.ty fTy) field rest
      | _, _ => none
  | .ty (.enum ety), sv, .Downcast _ v :: rest =>
    if Nat.blt v ety.discriminants.length then
      refReadPlaceSlotPath? (.variant ety v) sv rest
    else
      none
  | .variant ety v, sv, .Field idx _ :: rest =>
    match refFieldsForVariant? ety v with
    | none => none
    | some varFields =>
      match MirSemantics.getElem? varFields idx with
      | none => none
      | some fTy =>
        match sv with
        | .uninit =>
          refReadPlaceSlotPath? (.ty fTy) (refUninitSlotVal fTy) rest
        | .enumVal ety' v' fields =>
          if !EnumTy.beq ety ety' then
            none
          else if Nat.beq v' v then
            match MirSemantics.getElem? fields idx with
            | some field => refReadPlaceSlotPath? (.ty fTy) field rest
            | none => none
          else
            match refFieldsForVariant? ety v' with
            | some activeFieldTys =>
              if refAreAllZeroSizedTys activeFieldTys then
                refReadPlaceSlotPath? (.ty fTy) (refUninitSlotVal fTy) rest
              else
                none
            | none => none
        | .enumUntagged ety' v' fields =>
          if EnumTy.beq ety ety' && Nat.beq v' v then
            match MirSemantics.getElem? fields idx with
            | some field => refReadPlaceSlotPath? (.ty fTy) field rest
            | none => none
          else
            none
        | _ => none
  | .ty (.array elemTy len), .array elemTy' elems,
      .ConstantIndex idx _ false :: rest =>
    if !MirTy.beq elemTy elemTy' || !Nat.beq elems.length len then
      none
    else
      match MirSemantics.getElem? elems idx with
      | some elem => refReadPlaceSlotPath? (.ty elemTy) elem rest
      | none => none
  | _, _, _ :: _ => none

/-- Independent $M_{\text{ref}}$ subslot writer over canonicalized projections
starting at `pty : RefPlaceTy`. -/
noncomputable def refWritePlaceSlotPath? :
    RefPlaceTy → SlotVal → List Miri.MIR.ProjectionElem → SlotVal →
      Option SlotVal
  | .ty _, _, [], new => some new
  | .variant _ _, _, [], _ => none
  | .ty (.tuple fieldTys), .tuple fields, .Field idx _ :: rest, new =>
    match MirSemantics.getElem? fieldTys idx,
        MirSemantics.getElem? fields idx with
    | some fTy, some field =>
      match refWritePlaceSlotPath? (.ty fTy) field rest new with
      | some field' =>
        match MirSemantics.setElem? fields idx field' with
        | some fields' => some (.tuple fields')
        | none => none
      | none => none
    | _, _ => none
  | .ty (.adtStruct sty), .structVal sty' fields, .Field idx _ :: rest, new =>
    if !StructTy.beq sty sty' then
      none
    else
      match MirSemantics.getElem? sty.fields idx,
          MirSemantics.getElem? fields idx with
      | some fTy, some field =>
        match refWritePlaceSlotPath? (.ty fTy) field rest new with
        | some field' =>
          match MirSemantics.setElem? fields idx field' with
          | some fields' => some (.structVal sty fields')
          | none => none
        | none => none
      | _, _ => none
  | .ty (.enum ety), sv, .Downcast _ v :: rest, new =>
    if Nat.blt v ety.discriminants.length then
      refWritePlaceSlotPath? (.variant ety v) sv rest new
    else
      none
  | .variant ety v, sv, .Field idx _ :: rest, new =>
    match refFieldsForVariant? ety v with
    | none => none
    | some varFields =>
      match MirSemantics.getElem? varFields idx with
      | none => none
      | some fTy =>
        match sv with
        | .uninit =>
          let initFields := refUninitSlotVals varFields
          match MirSemantics.getElem? initFields idx with
          | none => none
          | some field =>
            match refWritePlaceSlotPath? (.ty fTy) field rest new with
            | some field' =>
              match MirSemantics.setElem? initFields idx field' with
              | some fields' => some (.enumUntagged ety v fields')
              | none => none
            | none => none
        | .enumUntagged ety' v' fields =>
          if !(EnumTy.beq ety ety' && Nat.beq v' v) then
            none
          else
            match MirSemantics.getElem? fields idx with
            | none => none
            | some field =>
              match refWritePlaceSlotPath? (.ty fTy) field rest new with
              | some field' =>
                match MirSemantics.setElem? fields idx field' with
                | some fields' => some (.enumUntagged ety v fields')
                | none => none
              | none => none
        | .enumVal ety' v' fields =>
          if !EnumTy.beq ety ety' then
            none
          else if Nat.beq v' v then
            match MirSemantics.getElem? fields idx with
            | none => none
            | some field =>
              match refWritePlaceSlotPath? (.ty fTy) field rest new with
              | some field' =>
                match MirSemantics.setElem? fields idx field' with
                | some fields' => some (.enumVal ety v fields')
                | none => none
              | none => none
          else
            let initFields := refUninitSlotVals varFields
            match MirSemantics.getElem? initFields idx with
            | none => none
            | some field =>
              match refWritePlaceSlotPath? (.ty fTy) field rest new with
              | some field' =>
                match MirSemantics.setElem? initFields idx field' with
                | some fields' => some (.enumUntagged ety v fields')
                | none => none
              | none => none
        | _ => none
  | .ty (.array elemTy len), .array elemTy' elems,
      .ConstantIndex idx _ false :: rest, new =>
    if !MirTy.beq elemTy elemTy' || !Nat.beq elems.length len then
      none
    else
      match MirSemantics.getElem? elems idx with
      | some elem =>
        match refWritePlaceSlotPath? (.ty elemTy) elem rest new with
        | some elem' =>
          match MirSemantics.setElem? elems idx elem' with
          | some elems' => some (.array elemTy elems')
          | none => none
        | none => none
      | none => none
  | _, _, _ :: _, _ => none

/-- Destination place resolved by `refRvalueHooks.evalPlace`,
`refStepHooksFor.evalPlace`, and `refAggregateHooks`: base local `localId`,
canonicalized `projection`, and projected `pty : RefPlaceTy`. -/
structure RefDest where
  localId : LocalId
  projection : List Miri.MIR.ProjectionElem
  pty : RefPlaceTy

/-- Extract the standalone `MirTy` of a `RefDest` (`none` on a bare downcasted
`.variant` awaiting `.Field`). -/
noncomputable def RefDest.ty? (d : RefDest) : Option MirTy :=
  match d.pty with
  | .ty t => some t
  | .variant _ _ => none

/-- Write `val` into canonicalized destination `dst` in `rlocals`, preserving
the cached layout of the destination local. -/
noncomputable def writeRefPlace (rlocals : List RefLocalState)
    (dst : RefDest) (val : Val) : Except FaultKind (List RefLocalState) :=
  match dst.ty? with
  | none => .error .unsupported
  | some dstTy =>
    if !checkRefVal val dstTy then
      .error .unsupported
    else
      match MirSemantics.getElem? rlocals dst.localId with
      | some ⟨slot, some localTy⟩ =>
        let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
        match Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false) frame₀
            () ⟨0, Array.empty⟩ (some refSizedLocalLayout) with
        | ⟨_, _, .ok ⟨.immediate imm, _⟩⟩ =>
          let root : SlotVal :=
            match miriImmediateToPayload? imm with
            | some sv => sv
            | none => .uninit
          match refWritePlaceSlotPath? (.ty localTy) root dst.projection
              val.toSlotVal with
          | none => .error .unsupported
          | some root' =>
            match Miri.Interpreter.placeWriteLocalImmediate
                EStateM.get EStateM.set (pure true)
                (fun _ _ => pure ()) (fun _ _ => pure ())
                0 refSizedLocalLayout (payloadToMiriImmediate root') frame₀ with
            | .ok () frame₁ =>
              match frame₁.getLocal 0,
                  MirSemantics.setElem? rlocals dst.localId
                    ⟨.live root', some localTy⟩ with
              | .ok ⟨.live (.immediate _), _⟩, some rlocals' => .ok rlocals'
              | .ok ⟨.live (.immediate _), _⟩, none => .error .unsupported
              | _, _ => .error .undefined
            | .error _ _ => .error .undefined
        | _ => .error .undefined
      | _ => .error .unsupported

/-- Evaluate a `.Copy` (`isMove = false`) or `.Move` (`isMove = true`) of the
place `⟨localId, proj⟩` in `rlocals`, resolving projections via
`Miri.Interpreter.project` (`refResolveProjPath`) and reading/updating subslots
via `refReadPlaceSlotPath?` and `refWritePlaceSlotPath?`. -/
noncomputable def evalRefPlaceOperand (types : List MirTy)
    (rlocals : List RefLocalState) (localId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (isMove : Bool) :
    Except FaultKind (MirTy × SlotVal × List RefLocalState) :=
  match MirSemantics.getElem? rlocals localId with
  | some ⟨slot, some localTy⟩ =>
    let layout := refLocalLayoutForTy localTy
    let frame₀ :=
      mkSingleLocalMiriFrameWithLayout (slotToMiriLocalValue slot) layout
        false
    match proj with
    | [] =>
      let mirOp : Miri.MIR.Operand :=
        if isMove then .Move ⟨0, Array.empty⟩ else .Copy ⟨0, Array.empty⟩
      match Miri.Interpreter.evalOperand (refLocalAccessHooks true) frame₀ ()
          mirOp (some layout) with
      | ⟨frame₁, _, .ok ⟨.immediate imm, outLayout⟩⟩ =>
        let root : SlotVal :=
          match miriImmediateToPayload? imm with
          | some sv => sv
          | none => .uninit
        if !isMove then
          .ok (localTy, root, rlocals)
        else
          let postSlot? : Option LocalSlot :=
            match frame₁.getLocal 0 with
            | .ok ⟨.live (.immediate .uninit), _⟩ =>
              some (refLiveUninitSlot localTy)
            | .ok ⟨.live (.immediate _), _⟩ =>
              if outLayout.layout.isZst then
                some (refLiveUninitSlot localTy)
              else
                none
            | _ => none
          match postSlot? with
          | some postSlot =>
            match MirSemantics.setElem? rlocals localId
                ⟨postSlot, some localTy⟩ with
            | some rlocals' => .ok (localTy, root, rlocals')
            | none => .error .unsupported
          | none => .error .undefined
      | _ => .error .undefined
    | _ :: _ =>
      match Miri.Interpreter.evalOperand (refLocalAccessHooks true) frame₀ ()
          (.Copy ⟨0, Array.empty⟩) (some layout) with
      | ⟨_, _, .ok ⟨.immediate imm, _⟩⟩ =>
        let root : SlotVal :=
          match miriImmediateToPayload? imm with
          | some sv => sv
          | none => .uninit
        match refProjectTy? types localTy proj with
        | none => .error .unsupported
        | some ty =>
          match refResolveProjPath types rlocals (.ty localTy) proj with
          | .error k => .error k
          | .ok resolvedProj =>
            match refReadPlaceSlotPath? (.ty localTy) root resolvedProj with
            | none => .error .unsupported
            | some sv =>
              if !isMove then
                .ok (ty, sv, rlocals)
              else
                match refWritePlaceSlotPath? (.ty localTy) root resolvedProj
                    (refUninitSlotVal ty) with
                | some root' =>
                  match MirSemantics.setElem? rlocals localId
                      ⟨.live root', some localTy⟩ with
                  | some rlocals' => .ok (ty, sv, rlocals')
                  | none => .error .unsupported
                | none => .error .unsupported
      | _ => .error .undefined
  | _ => .error .unsupported

/-- Map `RefProjectionElem` to `Miri.MIR.ProjectionElem`. -/
noncomputable def toMiriProjElem :
    RefProjectionElem → Miri.MIR.ProjectionElem
  | .deref => .Deref
  | .field idx ty => .Field idx ty
  | .downcast v => .Downcast none v
  | .index idxLocal => .Index idxLocal
  | .constantIndex offset minLength fromEnd =>
    .ConstantIndex offset minLength fromEnd
  | .unsupported => .PhantomDeref

/-- Map `RefPlace` to `Miri.MIR.Place`, preserving `localId` and every
projection element (`toMiriProjElem`). -/
noncomputable def toMiriPlace (rp : RefPlace) : Miri.MIR.Place :=
  ⟨rp.localId, Array.mk (rp.projection.map toMiriProjElem)⟩

/-- Map `RefOperand` to `Miri.MIR.Operand` so
`Miri.Interpreter.evalRvalueIntoPlace` and
`Miri.Interpreter.ControlFlow.evalTerminator` receive real operands. -/
noncomputable def toMiriOperand : RefOperand → Miri.MIR.Operand
  | .copy rp => .Copy (toMiriPlace rp)
  | .move rp => .Move (toMiriPlace rp)
  | .constant c =>
    let cv : Miri.MIR.ConstValue :=
      match c.lit with
      | .scalar bits => .Scalar (.Int bits.toNat 16)
      | .zeroSized => .ZeroSized
    .Constant ⟨⟨0⟩, none, .Val cv c.ty⟩

/-- Map `Trusted.MirAst.CastKind` to `Miri.MIR.CastKind`. -/
noncomputable def toMiriCastKind : CastKind → Miri.MIR.CastKind
  | .intToInt => .IntToInt
  | .unsupported => .Transmute

/-- Map `RefAggregateKind` to `Miri.MIR.AggregateKind`. -/
noncomputable def toMiriAggregateKind :
    RefAggregateKind → Miri.MIR.AggregateKind
  | .tuple => .Tuple
  | .adtStruct styId => .Adt styId 0 Array.empty none none
  | .adtEnum etyId v => .Adt etyId v Array.empty none none
  | .array elemTyId => .Array elemTyId

/-- Map `RefRvalue` to `Miri.MIR.Rvalue` for
`Miri.Interpreter.Step.evalStatement` and
`Miri.Interpreter.evalRvalueIntoPlace`. -/
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
  | .aggregate kind ops =>
    .Aggregate (toMiriAggregateKind kind) (Array.mk (ops.map toMiriOperand))
  | .repeat_ op count => .Repeat (toMiriOperand op) (.Param count "" none)
  | .cast kind op ty => .Cast (toMiriCastKind kind) (toMiriOperand op) ty
  | .unsupported => .CopyForDeref ⟨0, Array.empty⟩

/-- Stage 1 of reference operand evaluation over `Miri.MIR.Operand` (shared by
`refRvalueHooks.evalOperand`, `refAggregateHooks.evalOperand`, and
`refTerminatorHooksFor.{evalDiscriminant, readAssertCondition}`), calling
`Miri.Interpreter.evalOperand`
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
not that either model matches upstream Miri or MiniRust. Canary `D14`
(`CanaryD14OverflowTupleFieldMovesClaim`) does the same for moves of single
tuple fields.

Delegates `.Copy` and `.Move` of a place to `evalRefPlaceOperand`
(`Miri.Interpreter.evalOperand` with `refLocalLayoutForTy`, followed by the
adapter's field projection), and decodes `.Constant` via `types[tyId]?` and
`evalRefConstLit` (ignoring the carrier `sizeBytes` field). -/
noncomputable def evalRefMiriOperandToSlot (types : List MirTy)
    (rlocals : List RefLocalState) :
    Miri.MIR.Operand →
      Except FaultKind (MirTy × SlotVal × List RefLocalState)
  | .Copy place =>
    evalRefPlaceOperand types rlocals place.localId place.projection.toList
      false
  | .Move place =>
    evalRefPlaceOperand types rlocals place.localId place.projection.toList
      true
  | .Constant ⟨_, _, .Val (.Scalar (.Int bitsNat _)) tyId⟩ =>
    match MirSemantics.getElem? types tyId with
    | none => .error .unsupported
    | some ty =>
      match evalRefConstLit ty (.scalar (BitVec.ofNat 128 bitsNat)) with
      | .ok v => .ok (ty, v.toSlotVal, rlocals)
      | .error k => .error k
  | .Constant ⟨_, _, .Val .ZeroSized tyId⟩ =>
    match MirSemantics.getElem? types tyId with
    | none => .error .unsupported
    | some ty =>
      match evalRefConstLit ty .zeroSized with
      | .ok v => .ok (ty, v.toSlotVal, rlocals)
      | .error k => .error k
  | _ => .error .unsupported

/-- Stage 2A of reference operand evaluation (shared by
`refRvalueHooks.{readImmediate, cast}` and
`refTerminatorHooksFor.{evalDiscriminant, readAssertCondition}`): checks
`refIsPrimitiveReadableTy ty` before inspecting `sv` for uninit UB, matching
`Miri.Interpreter.readImmediate`
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
UB directly: uninitialized contents (`sv.toVal? = none`) fault with
`.undefined`. -/
noncomputable def readRefPrimitiveSlot (ty : MirTy) (sv : SlotVal) :
    Except FaultKind Val :=
  if !refIsPrimitiveReadableTy ty then
    .error .unsupported
  else
    match sv.toVal? with
    | some v => .ok v
    | none => .error .undefined

/-- Lift `FaultKind` into `Miri.Interpreter.StepError` inside `RvalueM`. -/
noncomputable def faultToStepError : FaultKind → Miri.Interpreter.StepError
  | .undefined => .undefinedBehavior "reference UB"
  | .unsupported => .unsupported "reference unsupported"

/-- Extract raw scalar bits along `path` inside a `SlotVal` in $M_{\text{ref}}$
for niche-tag discriminant reading (`Except FaultKind (BitVec 128)`). -/
noncomputable def refExtractSlotNicheBits :
    SlotVal → List Nat → Except FaultKind (BitVec 128)
  | .uninit, _ => .error .undefined
  | .enumUntagged _ _ _, _ => .error .undefined
  | .bool b, [] => .ok (BitVec.ofNat 128 (if b then 1 else 0))
  | .scalar sv, [] => .ok (miriScalar sv.width sv.bits).data
  | .enumVal innerEty innerVar [], [] =>
    match innerEty.tagRepr,
        MirSemantics.getElem? innerEty.discriminants innerVar with
    | .scalar w _, some d => .ok (miriScalar w (BitVec.ofNat 128 d)).data
    | _, _ => .error .unsupported
  | .structVal _ fs, idx :: rest =>
    match MirSemantics.getElem? fs idx with
    | some fSv => refExtractSlotNicheBits fSv rest
    | none => .error .unsupported
  | .tuple fs, idx :: rest =>
    match MirSemantics.getElem? fs idx with
    | some fSv => refExtractSlotNicheBits fSv rest
    | none => .error .unsupported
  | .array _ elems, idx :: rest =>
    match MirSemantics.getElem? elems idx with
    | some eSv => refExtractSlotNicheBits eSv rest
    | none => .error .unsupported
  | _, _ => .error .unsupported

/-- Extract raw scalar bits along non-empty `nichePath` inside `fields :
List SlotVal` in $M_{\text{ref}}$. -/
noncomputable def refExtractSlotNicheBitsFromFields (nichePath : List Nat)
    (fields : List SlotVal) : Except FaultKind (BitVec 128) :=
  match nichePath with
  | [] => .error .unsupported
  | idx :: rest =>
    match MirSemantics.getElem? fields idx with
    | some fSv => refExtractSlotNicheBits fSv rest
    | none => .error .unsupported

/-- Re-encode an enum's `(ety, sv)` slot payload into a
`Miri.Interpreter.OpTy Miri.Memory.Provenance` across `.zeroSized`, `.single`,
`.scalar`, and `.niche` layouts for
`Miri.Interpreter.Discriminant.readDiscriminant`. -/
noncomputable def encodeRefEnumTagOp (ety : EnumTy) (sv : SlotVal) :
    Except Miri.Interpreter.StepError
      (Miri.Interpreter.OpTy Miri.Memory.Provenance) :=
  let layout : Miri.Interpreter.LocalLayout := ⟨0, refEnumLayoutData ety⟩
  match ety.tagRepr with
  | .zeroSized =>
    match sv with
    | .uninit => .ok ⟨.immediate .uninit, layout⟩
    | .enumVal ety' v [] =>
      if EnumTy.beq ety ety' && Nat.beq v 0 then
        .ok ⟨.immediate .uninit, layout⟩
      else
        .error (.unsupported "mismatched ZST enum variant in slot")
    | _ => .error (.unsupported "non-enum value in ZST enum slot")
  | .single v₀ =>
    match sv with
    | .uninit => .ok ⟨.immediate .uninit, layout⟩
    | .enumVal ety' v _ | .enumUntagged ety' v _ =>
      if EnumTy.beq ety ety' && Nat.beq v v₀ then
        .ok ⟨.immediate .uninit, layout⟩
      else
        .error (.unsupported "mismatched single-variant enum in slot")
    | _ => .error (.unsupported "non-enum value in single-variant enum slot")
  | .scalar tagW _ =>
    match sv with
    | .uninit | .enumUntagged _ _ _ => .ok ⟨.immediate .uninit, layout⟩
    | .enumVal ety' v _ =>
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
    | _ => .error (.unsupported "non-enum value in scalar enum slot")
  | .niche tagW _ _ _ nichePath untagged start last nicheStart =>
    match sv with
    | .uninit => .ok ⟨.immediate .uninit, layout⟩
    | .enumVal ety' v fields =>
      if !EnumTy.beq ety ety' then
        .error (.unsupported "mismatched niche enum type in slot")
      else if Nat.beq v untagged then
        match refExtractSlotNicheBitsFromFields nichePath fields with
        | .error .undefined => .ok ⟨.immediate .uninit, layout⟩
        | .error .unsupported =>
          .error (.unsupported "invalid niche field path in slot")
        | .ok bits =>
          match Miri.Memory.ScalarInt.truncateFromUInt bits
              (toMiriSize tagW) with
          | .ok (tagSc, _) =>
            .ok ⟨.immediate (.scalar (.fromScalarInt tagSc)), layout⟩
          | .error _ => .error (.invalidProgram "niche tag truncate failure")
      else if Nat.ble start v && Nat.ble v last then
        let nicheBits := BitVec.ofNat 128 (v - start) + nicheStart
        match Miri.Memory.ScalarInt.truncateFromUInt nicheBits
            (toMiriSize tagW) with
        | .ok (tagSc, _) =>
          .ok ⟨.immediate (.scalar (.fromScalarInt tagSc)), layout⟩
        | .error _ => .error (.invalidProgram "niche tag truncate failure")
      else
        .error (.unsupported "out-of-range niche enum variant in slot")
    | .enumUntagged ety' v fields =>
      if !EnumTy.beq ety ety' then
        .error (.unsupported "mismatched untagged niche enum type in slot")
      else if Nat.beq v untagged then
        match refExtractSlotNicheBitsFromFields nichePath fields with
        | .error .undefined => .ok ⟨.immediate .uninit, layout⟩
        | .error .unsupported =>
          .error (.unsupported "invalid niche field path in untagged slot")
        | .ok bits =>
          match Miri.Memory.ScalarInt.truncateFromUInt bits
              (toMiriSize tagW) with
          | .ok (tagSc, _) =>
            .ok ⟨.immediate (.scalar (.fromScalarInt tagSc)), layout⟩
          | .error _ => .error (.invalidProgram "niche tag truncate failure")
      else
        .ok ⟨.immediate .uninit, layout⟩
    | _ => .error (.unsupported "non-enum value in niche enum slot")

/-- State threaded through `Miri.Interpreter.evalRvalueIntoPlace` (`RvalueM`):
carries `locals : List RefLocalState`, `destEvaluated : Bool` (so a second
`evalPlace` call from unmodeled `.Ref`/`.RawPtr` fails closed with
`.unsupported`), and `discrEnum : Option EnumTy` (cached by `evalPlaceToOp` for
`discriminantForVariant`). -/
structure RefRvalueState where
  locals : List RefLocalState
  destEvaluated : Bool := false
  discrEnum : Option EnumTy := none

/-- Evaluate an enum place `src` (unprojected or projected) via
`evalRefPlaceOperand` for `RvalueHooks.evalPlaceToOp` (`.Discriminant src`),
recording `ety` in `RefRvalueState.discrEnum`. -/
noncomputable def evalRefEnumPlaceToOp (types : List MirTy)
    (src : Miri.MIR.Place) (s : RefRvalueState) :
    EStateM.Result Miri.Interpreter.StepError RefRvalueState
      (Miri.Interpreter.OpTy (MirTy × SlotVal)) :=
  match evalRefPlaceOperand types s.locals src.localId src.projection.toList
      false with
  | .error k => .error (faultToStepError k) s
  | .ok (srcTy, sv, rlocals₁) =>
    match srcTy with
    | .enum ety =>
      if !refEnumAdmitted ety then
        .error (.unsupported "unadmitted enum in Discriminant")
          { s with locals := rlocals₁ }
      else
        let layout : Miri.Interpreter.LocalLayout :=
          ⟨0, refEnumLayoutData ety⟩
        .ok ⟨.immediate (payloadToMiriImmediate (.enum ety, sv)), layout⟩
          { s with locals := rlocals₁, discrEnum := some ety }
    | _ =>
      .error (.unsupported "Discriminant on non-enum place")
        { s with locals := rlocals₁ }

/-- Compute the payload field slots of `ety` at `variantIdx` when updating
slot `curSv` via `SetDiscriminant`, matching `evalSetDiscriminantResolved`. -/
noncomputable def refSetDiscrNextFields? (ety : EnumTy) (variantIdx : Nat)
    (varFields : List MirTy) : SlotVal → Option (List SlotVal)
  | .uninit => some (refUninitSlotVals varFields)
  | .enumUntagged ety' v' fs =>
    if EnumTy.beq ety ety' && Nat.beq v' variantIdx then some fs else none
  | .enumVal ety' v' fs =>
    if !EnumTy.beq ety ety' then
      none
    else if Nat.beq v' variantIdx then
      some fs
    else
      some (refUninitSlotVals varFields)
  | _ => none

/-- Read the destination enum subslot and compute `nextFields` for
`SetDiscriminant` in $M_{\text{ref}}$, routing base-local liveness through
`Miri.Interpreter.evalPlaceToOp`. -/
noncomputable def refPrepSetDiscriminant (rlocals : List RefLocalState)
    (rdest : RefDest) (ety : EnumTy) (variantIdx : Nat) :
    Except FaultKind (MirTy × SlotVal × SlotVal × List SlotVal) :=
  match MirSemantics.getElem? rlocals rdest.localId with
  | some ⟨slot, some localTy⟩ =>
    let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
    match Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false) frame₀ ()
        ⟨0, Array.empty⟩ (some refSizedLocalLayout) with
    | ⟨_, _, .ok ⟨.immediate imm, _⟩⟩ =>
      let root : SlotVal :=
        match miriImmediateToPayload? imm with
        | some sv => sv
        | none => .uninit
      match refReadPlaceSlotPath? (.ty localTy) root rdest.projection,
          refFieldsForVariant? ety variantIdx with
      | some curSv, some varFields =>
        match refSetDiscrNextFields? ety variantIdx varFields curSv with
        | some nextFields => .ok (localTy, root, curSv, nextFields)
        | none => .error .unsupported
      | _, _ => .error .unsupported
    | _ => .error .undefined
  | _ => .error .unsupported

/-- `Miri.Interpreter.DiscriminantHooks` for `SetDiscriminant` and enum
aggregate `writeDiscriminant`, driving
`Miri.Interpreter.Discriminant.{writeDiscriminant, tagForVariant,
readDiscriminant, discriminantForVariant}`. -/
noncomputable def refWriteDiscriminantHooks (S : Type)
    (getLocals : S → List RefLocalState) (dstTy : MirTy)
    (etyOpt : Option EnumTy) (variantIdx : Nat) :
    Miri.Interpreter.DiscriminantHooks Miri.Memory.Provenance S Unit
      RefDest := {
  runtimeTarget := Miri.ABI.RuntimeTargetDataLayout.default
  discriminantLayout := fun _ ty s =>
    match etyOpt with
    | some ety =>
      if Nat.beq ty 0 then
        .ok ⟨1, refScalarLayoutData ety.discrWidth ety.discrSigned⟩ s
      else
        .error (.invalidProgram "unexpected enum TyId in discriminantLayout") s
    | none => .ok ⟨1, refScalarLayoutData .isize true⟩ s
  tagLayout := fun _ tag s =>
    match refTagScalarLayout? tag with
    | some l => .ok ⟨0, l⟩ s
    | none => .error (.invalidProgram "non-integer enum tag") s
  discriminantValue := fun _ ty variant s =>
    match etyOpt with
    | some ety =>
      if Nat.beq ty 0 then
        match MirSemantics.getElem? ety.discriminants variant with
        | some disc => .ok (some (1, BitVec.ofNat 128 disc)) s
        | none => .error (.invalidProgram "enum variant out of bounds") s
      else
        .error (.invalidProgram "unexpected enum TyId in discriminantValue") s
    | none => .ok none s
  variantForDiscriminant := fun _ ty discrBits s =>
    match etyOpt with
    | some ety =>
      if Nat.beq ty 0 then
        .ok (refFindDiscrVariant? discrBits ety.discriminants) s
      else
        .error (.invalidProgram
          "unexpected enum TyId in variantForDiscriminant") s
    | none => .ok none s
  adtVariantCount := fun _ _ s =>
    match etyOpt with
    | some ety => .ok ety.discriminants.length s
    | none => .ok 1 s
  projectRead := fun _ op field s =>
    if Nat.beq field 0 then
      match op.layout.layout.variants with
      | .Multiple tag _ _ _ =>
        match refTagScalarLayout? tag with
        | some tl => .ok ⟨op.op, ⟨0, tl⟩⟩ s
        | none => .error (.invalidProgram "non-integer enum tag") s
      | _ => .error (.invalidProgram "projectRead on non-Multiple enum") s
    else
      .error (.invalidProgram "non-zero tag field on enum") s
  readImmediate := fun _ op s =>
    match op.op with
    | .immediate .uninit =>
      .error (.undefinedBehavior "InvalidUninitBytes(None)") s
    | .immediate imm => .ok ⟨imm, op.layout⟩ s
    | .indirect _ => .error (.unsupported "memory enum place unsupported") s
  destLayout := fun _ =>
    match etyOpt with
    | some ety => ⟨0, refEnumLayoutData ety⟩
    | none =>
      ⟨0, { refBaseLayoutData (.Memory (sized := true))
              (Miri.ABI.Size.ofBytes 0) with
            variants := .Single 0
            uninhabited := refIsTypeUninhabited dstTy }⟩
  projectWrite := fun _ dest field s =>
    if Nat.beq field 0 then
      .ok dest s
    else
      .error (.invalidProgram "non-zero tag field in projectWrite") s
  writeScalar := fun _ sc dest s =>
    match etyOpt with
    | some ety =>
      match refPrepSetDiscriminant (getLocals s) dest ety variantIdx with
      | .ok (_, _, _, nextFields) =>
        let expectedSv : SlotVal := .enumVal ety variantIdx nextFields
        match encodeRefEnumTagOp ety expectedSv with
        | .ok expectedOp =>
          match expectedOp.op, sc.tryToScalarInt with
          | .immediate (.scalar expectedSc), .ok (.integer actualInt) =>
            match expectedSc.tryToScalarInt with
            | .ok (.integer expectedInt) =>
              if actualInt == expectedInt then
                .ok () s
              else
                .error (.invalidProgram "writeDiscriminant tag mismatch") s
            | _ => .error (.invalidProgram "expected tag not scalar int") s
          | _, _ => .error (.invalidProgram "writeDiscriminant non-scalar tag") s
        | .error err => .error err s
      | .error k => .error (faultToStepError k) s
    | none => .error (.invalidProgram "writeScalar on non-enum SetDiscriminant") s
  toOp := fun _ dest s =>
    match etyOpt with
    | some ety =>
      match refPrepSetDiscriminant (getLocals s) dest ety variantIdx with
      | .error k => .error (faultToStepError k) s
      | .ok (_, _, curSv, _) =>
        let layout : Miri.Interpreter.LocalLayout := ⟨0, refEnumLayoutData ety⟩
        match ety.tagRepr with
        | .zeroSized | .single _ => .ok ⟨.immediate .uninit, layout⟩ s
        | _ =>
          match encodeRefEnumTagOp ety curSv with
          | .ok op => .ok op s
          | .error err => .error err s
    | none =>
      match MirSemantics.getElem? (getLocals s) dest.localId with
      | none => .error (.unsupported "missing SetDiscriminant local") s
      | some ⟨.dead, some _⟩ =>
        .error (.stack (.localExpectedLive dest.localId)) s
      | some ⟨.live root, some localTy⟩ =>
        match refReadPlaceSlotPath? (.ty localTy) root dest.projection with
        | some _ =>
          let layout : Miri.Interpreter.LocalLayout :=
            ⟨0, { refBaseLayoutData (.Memory (sized := true))
                    (Miri.ABI.Size.ofBytes 0) with
                  variants := .Single 0
                  uninhabited := refIsTypeUninhabited dstTy }⟩
          .ok ⟨.immediate .uninit, layout⟩ s
        | none => .error (.unsupported "invalid SetDiscriminant projection") s
      | _ => .error (.unsupported "missing SetDiscriminant local type") s
  scalarMayBeNull := fun _ _ s => .ok true s
}

/-- Execute `SetDiscriminant` on resolved destination `rdest` in `rlocals` via
`Miri.Interpreter.Discriminant.writeDiscriminant` and
`Miri.Interpreter.placeWriteLocalImmediate`. -/
noncomputable def evalRefSetDiscriminant (rlocals : List RefLocalState)
    (rdest : RefDest) (variantIdx : Nat) :
    Except FaultKind (List RefLocalState) :=
  match MirSemantics.getElem? rlocals rdest.localId with
  | none => .error .unsupported
  | some ⟨slot, some localTy⟩ =>
    let dstInfo? : Except FaultKind (MirTy × Option EnumTy) :=
      match rdest.pty with
      | .ty (.enum ety) =>
        if refEnumAdmitted ety then
          .ok (.enum ety, some ety)
        else
          .error .unsupported
      | .ty t => .ok (t, none)
      | .variant _ _ => .error .unsupported
    match dstInfo? with
    | .error k => .error k
    | .ok (dstTy, etyOpt) =>
      let checkNonEnumPlace? : Except FaultKind Unit :=
        match etyOpt with
        | some _ => .ok ()
        | none =>
          match slot with
          | .dead => .error .undefined
          | .live root =>
            match refReadPlaceSlotPath? (.ty localTy) root rdest.projection with
            | some _ => .ok ()
            | none => .error .unsupported
      match checkNonEnumPlace? with
      | .error k => .error k
      | .ok () =>
        match Miri.Interpreter.Discriminant.writeDiscriminant
            (refWriteDiscriminantHooks (List RefLocalState) id dstTy etyOpt
              variantIdx)
            () variantIdx rdest rlocals with
        | .error (.undefinedBehavior _) _
        | .error (.stack (.localExpectedLive _)) _ => .error .undefined
        | .error _ _ => .error .unsupported
        | .ok () _ =>
          match etyOpt with
          | none => .ok rlocals
          | some ety =>
            match refPrepSetDiscriminant rlocals rdest ety variantIdx with
            | .error k => .error k
            | .ok (localTy, root, _, nextFields) =>
              let newEnumSv : SlotVal := .enumVal ety variantIdx nextFields
              match refWritePlaceSlotPath? (.ty localTy) root rdest.projection
                  newEnumSv with
              | none => .error .unsupported
              | some root' =>
                let frame₀ :=
                  mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
                match Miri.Interpreter.placeWriteLocalImmediate
                    EStateM.get EStateM.set (pure true)
                    (fun _ _ => pure ()) (fun _ _ => pure ())
                    0 refSizedLocalLayout (payloadToMiriImmediate root')
                    frame₀ with
                | .ok () frame₁ =>
                  match frame₁.getLocal 0,
                      MirSemantics.setElem? rlocals rdest.localId
                        ⟨.live root', some localTy⟩ with
                  | .ok ⟨.live (.immediate _), _⟩, some rlocals' =>
                    .ok rlocals'
                  | .ok ⟨.live (.immediate _), _⟩, none => .error .unsupported
                  | _, _ => .error .undefined
                | .error _ _ => .error .undefined
  | _ => .error .unsupported

/-- Independent $M_{\text{ref}}$ check that two non-downcast
`Miri.MIR.ProjectionElem` steps may alias the same subplace. -/
noncomputable def refProjElemMayAlias :
    Miri.MIR.ProjectionElem → Miri.MIR.ProjectionElem → Bool
  | .Field i _, .Field j _ => Nat.beq i j
  | .ConstantIndex o₁ _ false, .ConstantIndex o₂ _ false => Nat.beq o₁ o₂
  | .ConstantIndex o₁ _ true, .ConstantIndex o₂ _ true => Nat.beq o₁ o₂
  | _, _ => true

/-- Independent $M_{\text{ref}}$ prefix-overlap check on projection lists
(treating `.Downcast` across distinct variants as overlapping in memory). -/
noncomputable def refProjPrefixMayAlias :
    List Miri.MIR.ProjectionElem → List Miri.MIR.ProjectionElem → Bool
  | [], _ => true
  | _ :: _, [] => false
  | .Downcast _ v₁ :: as, .Downcast _ v₂ :: bs =>
    if Nat.beq v₁ v₂ then refProjPrefixMayAlias as bs else true
  | .Downcast _ _ :: _, _ :: _ => true
  | _ :: _, .Downcast _ _ :: _ => true
  | a :: as, b :: bs => refProjElemMayAlias a b && refProjPrefixMayAlias as bs

/-- Independent $M_{\text{ref}}$ conservative place-overlap check over
`Miri.MIR.Place`. -/
noncomputable def refPlacesMayOverlap (a b : Miri.MIR.Place) : Bool :=
  Nat.beq a.localId b.localId &&
    (refProjPrefixMayAlias a.projection.toList b.projection.toList ||
      refProjPrefixMayAlias b.projection.toList a.projection.toList)

/-- Independent $M_{\text{ref}}$ check whether `mirOp` reads a place that may
overlap `dst`. -/
noncomputable def refOperandMayOverlapPlace (dst : Miri.MIR.Place) :
    Miri.MIR.Operand → Bool
  | .Copy src => refPlacesMayOverlap dst src
  | .Move src => refPlacesMayOverlap dst src
  | .Constant _ => false
  | .RuntimeChecks _ => false

/-- Independent $M_{\text{ref}}$ check whether any operand in `ops` reads a
place that may overlap `dst`. -/
noncomputable def refAnyOperandMayOverlapPlace (dst : Miri.MIR.Place) :
    List Miri.MIR.Operand → Bool
  | [] => false
  | opnd :: rest =>
    refOperandMayOverlapPlace dst opnd ||
      refAnyOperandMayOverlapPlace dst rest

/-- Independent $M_{\text{ref}}$ check whether `mirOp` is a `.Move` whose source
place may overlap `dst`. -/
noncomputable def refMoveOperandMayOverlapPlace (dst : Miri.MIR.Place) :
    Miri.MIR.Operand → Bool
  | .Move src => refPlacesMayOverlap dst src
  | .Copy _ => false
  | .Constant _ => false
  | .RuntimeChecks _ => false

/-- Independent $M_{\text{ref}}$ check whether any `.Move` operand in `ops` may
overlap `dst`. -/
noncomputable def refAnyMoveOperandMayOverlapPlace (dst : Miri.MIR.Place) :
    List Miri.MIR.Operand → Bool
  | [] => false
  | opnd :: rest =>
    refMoveOperandMayOverlapPlace dst opnd ||
      refAnyMoveOperandMayOverlapPlace dst rest

/-- Independent $M_{\text{ref}}$ tuple-type predicate. -/
noncomputable def refIsTupleTy : MirTy → Bool
  | .tuple _ => true
  | _ => false

/-- Independent $M_{\text{ref}}$ compound overlap-protected destination type
check (`.tuple`, non-ZST `.adtStruct`, non-ZST payload `.enum`, or non-ZST
`.array`). -/
noncomputable def refIsCompoundOverlapProtectedTy (ty : MirTy) : Bool :=
  match ty with
  | .tuple _ => true
  | .adtStruct _ | .array _ _ => !refIsZeroSizedTy ty
  | .enum ety => !refIsZeroSizedTy (.enum ety) && refHasEnumPayloadFields ety
  | _ => false

/-- Independent $M_{\text{ref}}$ fail-closed aliasing guard for `.Assign`:
rejects `Rvalue.Use` on compound non-ZST destinations overlapping `dst` and
`Rvalue.Aggregate` (across `.Tuple`, `.Adt` struct/enum, and `.Array`) where
any operand overlaps `dst`. -/
noncomputable def refAssignHasUnsupportedOverlap (dst : Miri.MIR.Place)
    (dstTy : MirTy) : Miri.MIR.Rvalue → Bool
  | .Use opnd _ =>
    refIsCompoundOverlapProtectedTy dstTy &&
      refOperandMayOverlapPlace dst opnd
  | .Aggregate _ ops => refAnyOperandMayOverlapPlace dst ops.toList
  | .Repeat opnd _ => refOperandMayOverlapPlace dst opnd
  | _ => false

/-- `Miri.Interpreter.AggregateHooks` for `Miri.Interpreter.writeAggregate`
(`vendor/lean-miri/Miri/Interpreter/Aggregate.lean`) across `.Tuple`, `.Adt`
(structs and enums), and `.Array` aggregates. -/
noncomputable def refAggregateHooks (types : List MirTy) :
    Miri.Interpreter.AggregateHooks (MirTy × SlotVal) RefRvalueState
      Unit RefDest := {
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  placeLayout := fun _ => refSizedLocalLayout
  evalOperand := fun _ mirOp _ s =>
    match evalRefMiriOperandToSlot types s.locals mirOp with
    | .error k => .error (faultToStepError k) s
    | .ok (ty, sv, locals') =>
      .ok ⟨.immediate (payloadToMiriImmediate (ty, sv)),
          refSizedLocalLayout⟩
        { s with locals := locals' }
  readPointer := fun _ _ s =>
    .error (.unsupported "raw pointer aggregate unsupported") s
  readScalar := fun _ _ s =>
    .error (.unsupported "raw pointer aggregate unsupported") s
  projectDowncast := fun _ dest variantIdx s =>
    match dest.pty with
    | .ty (.adtStruct _) =>
      if Nat.beq variantIdx 0 then
        .ok dest s
      else
        .error (.unsupported "non-zero struct variant in aggregate") s
    | .ty (.enum ety) =>
      if refEnumAdmitted ety && Nat.blt variantIdx ety.discriminants.length then
        .ok ⟨dest.localId, dest.projection ++ [.Downcast none variantIdx],
          .variant ety variantIdx⟩ s
      else
        .error (.unsupported "invalid enum variant in aggregate") s
    | _ => .error (.unsupported "projectDowncast on non-ADT aggregate") s
  projectField := fun _ dest fieldIdx s =>
    match dest.pty with
    | .ty (.tuple fieldTys) =>
      match MirSemantics.getElem? fieldTys fieldIdx with
      | some fieldTy =>
        .ok ⟨dest.localId, dest.projection ++ [.Field fieldIdx 0],
          .ty fieldTy⟩ s
      | none => .error (.unsupported "tuple aggregate field out of bounds") s
    | .ty (.adtStruct sty) =>
      match MirSemantics.getElem? sty.fields fieldIdx with
      | some fieldTy =>
        .ok ⟨dest.localId, dest.projection ++ [.Field fieldIdx 0],
          .ty fieldTy⟩ s
      | none => .error (.unsupported "struct aggregate field out of bounds") s
    | .variant ety v =>
      match refFieldsForVariant? ety v with
      | some varFields =>
        match MirSemantics.getElem? varFields fieldIdx with
        | some fieldTy =>
          .ok ⟨dest.localId, dest.projection ++ [.Field fieldIdx 0],
            .ty fieldTy⟩ s
        | none => .error (.unsupported "enum aggregate field out of bounds") s
      | none => .error (.unsupported "enum aggregate variant out of bounds") s
    | .ty (.array elemTy len) =>
      match refProjectArrayAggregateElem elemTy len fieldIdx with
      | .ok elemProj =>
        .ok ⟨dest.localId, dest.projection ++ [elemProj], .ty elemTy⟩ s
      | .error err => .error err s
    | _ => .error (.unsupported "aggregate field on non-aggregate") s
  copyOp := fun _ _ _ s =>
    .error (.unsupported "raw pointer aggregate copyOp unsupported") s
  copyOpNoValidate := fun _ op dest _ s =>
    match op.op, dest.ty? with
    | .immediate imm, some dstTy =>
      match miriImmediateToPayload? imm with
      | some (srcTy, sv) =>
        if !(MirTy.beq srcTy dstTy) then
          .error (.unsupported "aggregate field type mismatch") s
        else
          match sv.toVal? with
          | none =>
            .error (.undefinedBehavior "uninit aggregate field operand") s
          | some v =>
            match writeRefPlace s.locals dest v with
            | .error k => .error (faultToStepError k) s
            | .ok locals' => .ok () { s with locals := locals' }
      | none => .error (.invalidProgram "missing aggregate operand payload") s
    | .immediate _, none =>
      .error (.unsupported "aggregate field write into bare variant") s
    | .indirect _, _ =>
      .error (.unsupported "indirect aggregate operand unsupported") s
  writeDiscriminant := fun _ variantIdx dest s =>
    match dest.pty with
    | .ty .unit =>
      match writeRefPlace s.locals dest .unit with
      | .error k => .error (faultToStepError k) s
      | .ok locals' => .ok () { s with locals := locals' }
    | .ty (.tuple _) => .ok () s
    | .ty (.adtStruct sty) =>
      if sty.fields.isEmpty then
        match writeRefPlace s.locals dest (.structVal sty []) with
        | .error k => .error (faultToStepError k) s
        | .ok locals' => .ok () { s with locals := locals' }
      else
        .ok () s
    | .ty (.enum _) =>
      match evalRefSetDiscriminant s.locals dest variantIdx with
      | .error k => .error (faultToStepError k) s
      | .ok locals' => .ok () { s with locals := locals' }
    | .ty (.array elemTy len) =>
      if Nat.beq len 0 then
        match writeRefPlace s.locals dest (.array elemTy []) with
        | .error k => .error (faultToStepError k) s
        | .ok locals' => .ok () { s with locals := locals' }
      else
        .ok () s
    | _ => .error (.unsupported "unsupported aggregate destination") s
  enforceValidity := fun _ _ s => .ok false s
  validate := fun _ _ s => .ok () s
  forceAllocation := fun _ _ s =>
    .error (.unsupported "Repeat unsupported") s
  length := fun _ _ s =>
    .error (.unsupported "Repeat unsupported") s
  getPlaceAllocMut := fun _ _ s =>
    .error (.unsupported "Repeat unsupported") s
  projectIndex := fun _ _ _ s =>
    .error (.unsupported "Repeat unsupported") s
  placePointer := fun _ =>
    .error (.unsupported "Repeat unsupported")
  wrappingOffset := fun _ _ =>
    .error (.unsupported "Repeat unsupported")
  memCopyRepeatedly := fun _ _ _ _ _ _ s =>
    .error (.unsupported "Repeat unsupported") s
}

/-- Validate aggregate kind and arity against `dest.pty` before invoking
`Miri.Interpreter.writeAggregate`. -/
noncomputable def refAggregateValidShape (types : List MirTy)
    (kind : Miri.MIR.AggregateKind) (arity : Nat) (dest : RefDest) : Bool :=
  match kind, dest.pty with
  | .Tuple, .ty .unit => Nat.beq arity 0
  | .Tuple, .ty (.tuple fieldTys) =>
    !fieldTys.isEmpty && Nat.beq arity fieldTys.length
  | .Adt tyId v _ _ none, .ty (.adtStruct dstSty) =>
    match MirSemantics.getElem? types tyId with
    | some (.adtStruct sty) =>
      Nat.beq v 0 &&
        StructTy.beq sty dstSty &&
        Nat.beq arity sty.fields.length &&
        refAreSupportedFieldTys sty.fields &&
        !refIsTypeUninhabited (.adtStruct sty)
    | _ => false
  | .Adt tyId v _ _ none, .ty (.enum dstEty) =>
    match MirSemantics.getElem? types tyId with
    | some (.enum ety) =>
      EnumTy.beq ety dstEty &&
        refEnumAdmitted ety &&
        match refFieldsForVariant? ety v with
        | some varFieldTys => Nat.beq arity varFieldTys.length
        | none => false
    | _ => false
  | .Array elemTyId, .ty (.array dstElemTy len) =>
    match MirSemantics.getElem? types elemTyId with
    | some elemTy =>
      MirTy.beq elemTy dstElemTy &&
        Nat.beq arity len &&
        refIsSupportedLocalTy elemTy &&
        Nat.blt len (Nat.pow 2 64)
    | none => false
  | _, _ => false

/-- State carried through `Miri.Interpreter.writeRepeat` (`refRepeatHooks`). -/
structure RefRepeatState where
  locals : List RefLocalState
  elemVal : Option Val

/-- `Miri.Interpreter.AggregateHooks` driving `Miri.Interpreter.writeRepeat`
(`vendor/lean-miri/Miri/Interpreter/Aggregate.lean`) for `[op; len]`. -/
noncomputable def refRepeatHooks (types : List MirTy) (elemTy : MirTy)
    (len : Nat) (dst : RefDest) :
    Miri.Interpreter.AggregateHooks (MirTy × SlotVal) RefRepeatState
      Unit RefDest := {
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  placeLayout := fun _ => refSizedLocalLayout
  evalOperand := fun _ mirOp _ s =>
    match evalRefMiriOperandToSlot types s.locals mirOp with
    | .error k => .error (faultToStepError k) s
    | .ok (srcTy, sv, locals') =>
      if !(MirTy.beq srcTy elemTy) then
        .error (.unsupported "repeat operand type mismatch") s
      else
        .ok ⟨.immediate (payloadToMiriImmediate (srcTy, sv)),
            refSizedLocalLayout⟩
          { s with locals := locals' }
  readPointer := fun _ _ s =>
    .error (.unsupported "repeat readPointer unsupported") s
  readScalar := fun _ _ s =>
    .error (.unsupported "repeat readScalar unsupported") s
  projectDowncast := fun _ _ _ s =>
    .error (.unsupported "repeat projectDowncast unsupported") s
  projectField := fun _ _ _ s =>
    .error (.unsupported "repeat projectField unsupported") s
  copyOp := fun _ op _ s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (_, sv) =>
        match sv.toVal? with
        | none => .error (.undefinedBehavior "uninit repeat operand") s
        | some v => .ok () { s with elemVal := some v }
      | none => .error (.invalidProgram "missing repeat operand payload") s
    | .indirect _ => .error (.unsupported "indirect repeat operand") s
  copyOpNoValidate := fun _ _ _ _ s =>
    .error (.unsupported "repeat copyOpNoValidate unsupported") s
  writeDiscriminant := fun _ _ _ s =>
    .error (.unsupported "repeat writeDiscriminant unsupported") s
  enforceValidity := fun _ _ s => .ok false s
  validate := fun _ _ s => .ok () s
  forceAllocation := fun _ dest s => .ok dest s
  length := fun _ _ s => .ok (UInt64.ofNat len) s
  getPlaceAllocMut := fun _ dest s =>
    match writeRefPlace s.locals dest (.array elemTy []) with
    | .error k => .error (faultToStepError k) s
    | .ok locals' => .ok () { s with locals := locals' }
  projectIndex := fun _ dest _ s => .ok dest s
  placePointer := fun _ => .ok ⟨Miri.ABI.Size.ZERO, none⟩
  wrappingOffset := fun ptr _ => .ok ptr
  memCopyRepeatedly := fun _ _ _ _ _ _ s =>
    match s.elemVal with
    | none => .error (.invalidProgram "missing repeat elemVal") s
    | some v =>
      match writeRefPlace s.locals dst (.array elemTy (refReplicateVal len v)) with
      | .error k => .error (faultToStepError k) s
      | .ok locals' => .ok () { s with locals := locals' }
}

/-- `Miri.Interpreter.RvalueHooks` closing over `types : List MirTy` and an
optional repeat count, instantiated with provenance carrier `MirTy × SlotVal`,
state `RefRvalueState`, and place value `RefDest` to drive
`Miri.Interpreter.evalRvalueIntoPlace`, `Miri.Interpreter.writeAggregate`,
`Miri.Interpreter.writeRepeat`, and `Miri.Interpreter.Discriminant`. -/
noncomputable def refRvalueHooks (types : List MirTy)
    (repeatCount : Option Nat := none) :
    Miri.Interpreter.RvalueHooks (MirTy × SlotVal) RefRvalueState Unit
      RefDest := {
  placeLayout := fun _ => refSizedLocalLayout
  evalPlace := fun _ place _ s =>
    if s.destEvaluated then
      .error (.unsupported "Ref/RawPtr unsupported") s
    else
      match MirSemantics.getElem? s.locals place.localId with
      | some ⟨_, some localTy⟩ =>
        match refProjectTy? types localTy place.projection.toList with
        | none => .error (.unsupported "unsupported place projection") s
        | some dstTy =>
          match refResolveProjPath types s.locals (.ty localTy)
              place.projection.toList with
          | .error k =>
            .error (faultToStepError k) { s with destEvaluated := true }
          | .ok resolvedProj =>
            .ok ⟨place.localId, resolvedProj, .ty dstTy⟩
              { s with destEvaluated := true }
      | _ => .error (.unsupported "missing destination local") s
  evalOperand := fun _ mirOp _ s =>
    match evalRefMiriOperandToSlot types s.locals mirOp with
    | .error k => .error (faultToStepError k) s
    | .ok (ty, sv, locals') =>
      .ok ⟨.immediate (payloadToMiriImmediate (ty, sv)),
          refSizedLocalLayout⟩
        { s with locals := locals' }
  evalPlaceToOp := fun _ src _ s =>
    evalRefEnumPlaceToOp types src s
  readImmediate := fun _ op s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (ty, sv) =>
        match readRefPrimitiveSlot ty sv with
        | .error k => .error (faultToStepError k) s
        | .ok v =>
          .ok ⟨payloadToMiriImmediate (ty, v.toSlotVal),
            refSizedLocalLayout⟩ s
      | none => .error (.invalidProgram "missing operand payload") s
    | .indirect _ => .error (.unsupported "indirect operand unsupported") s
  writeImmediate := fun _ imm dest s =>
    match miriImmediateToPayload? imm with
    | some (_, sv) =>
      match sv.toVal? with
      | some v =>
        match writeRefPlace s.locals dest v with
        | .error k => .error (faultToStepError k) s
        | .ok locals' => .ok () { s with locals := locals' }
      | none => .error (.invalidProgram "uninit rvalue result payload") s
    | none => .error (.invalidProgram "missing rvalue result payload") s
  writePointer := fun _ _ _ s =>
    .error (.unsupported "ThreadLocalRef unsupported") s
  threadLocalPointer := fun _ _ s =>
    .error (.unsupported "ThreadLocalRef unsupported") s
  withRetagMode := fun _ _ act => act
  copyOp := fun _ op dest s =>
    match op.op, dest.ty? with
    | .immediate imm, some dstTy =>
      match miriImmediateToPayload? imm with
      | some (srcTy, sv) =>
        if !(MirTy.beq srcTy dstTy) then
          .error (.unsupported "Use type mismatch") s
        else
          match sv.toVal? with
          | none => .error (.undefinedBehavior "uninit Use operand") s
          | some v =>
            match writeRefPlace s.locals dest v with
            | .error k => .error (faultToStepError k) s
            | .ok locals' => .ok () { s with locals := locals' }
      | none => .error (.invalidProgram "missing Use operand payload") s
    | .immediate _, none =>
      .error (.unsupported "Use into bare variant") s
    | .indirect _, _ => .error (.unsupported "indirect Use operand") s
  copyOpAllowTransmute := fun _ _ _ s =>
    .error (.unsupported "transmute copy unsupported") s
  binaryOp := fun _ miriOp lhs rhs s =>
    match miriImmediateToPayload? lhs.imm, miriImmediateToPayload? rhs.imm with
    | some (lTy, lSv), some (_, rSv) =>
      match lSv.toVal?, rSv.toVal? with
      | some lVal, some rVal =>
        match evalRefMiriBinOp miriOp lVal rVal with
        | .error k => .error (faultToStepError k) s
        | .ok v =>
          let resTy : MirTy :=
            match miriOp with
            | .Eq | .Lt | .Le | .Ne | .Ge | .Gt => .bool
            | .AddWithOverflow | .SubWithOverflow | .MulWithOverflow =>
              .tuple [lTy, .bool]
            | _ => lTy
          .ok ⟨payloadToMiriImmediate (resTy, v.toSlotVal),
            refSizedLocalLayout⟩ s
      | _, _ => .error (.invalidProgram "uninit BinaryOp operands") s
    | _, _ => .error (.invalidProgram "missing BinaryOp operands") s
  unaryOp := fun _ miriOp val s =>
    match miriImmediateToPayload? val.imm with
    | some (ty, sv) =>
      match sv.toVal? with
      | some v =>
        match evalRefMiriUnOp miriOp v with
        | .error k => .error (faultToStepError k) s
        | .ok u =>
          .ok ⟨payloadToMiriImmediate (ty, u.toSlotVal),
            refSizedLocalLayout⟩ s
      | none => .error (.invalidProgram "uninit UnaryOp operand") s
    | none => .error (.invalidProgram "missing UnaryOp operand") s
  writeAggregate := fun c kind operands dest s =>
    if !refAggregateValidShape types kind operands.size dest then
      .error (.unsupported "aggregate shape mismatch") s
    else
      Miri.Interpreter.writeAggregate (refAggregateHooks types) c kind
        operands dest s
  writeRepeat := fun c opnd dest s =>
    match dest.pty, repeatCount with
    | .ty (.array elemTy len), some count =>
      if !Nat.beq count len || !Nat.blt len (Nat.pow 2 64) then
        .error (.unsupported "repeat count mismatch") s
      else
        match Miri.Interpreter.writeRepeat
            (refRepeatHooks types elemTy len dest) c opnd dest
            ⟨s.locals, none⟩ with
        | .ok () rs' => .ok () { s with locals := rs'.locals }
        | .error err rs' => .error err { s with locals := rs'.locals }
    | _, _ => .error (.unsupported "Repeat unsupported") s
  forceAllocation := fun _ _ s =>
    .error (.unsupported "Ref/RawPtr unsupported") s
  toRef := fun _ _ s =>
    .error (.unsupported "Ref/RawPtr unsupported") s
  enforceValidity := fun _ _ s => .ok false s
  retagPtrValue := fun _ _ _ s => .ok none s
  placeBaseRaw := fun _ _ s => .ok false s
  normalize := fun _ ty s => .ok ty s
  cast := fun _ src kind tyId dest s =>
    match src.op, dest.ty? with
    | .immediate imm, some dstTy =>
      match miriImmediateToPayload? imm with
      | some (srcTy, sv) =>
        match readRefPrimitiveSlot srcTy sv with
        | .error k => .error (faultToStepError k) s
        | .ok v =>
          match kind with
          | .IntToInt =>
            match MirSemantics.getElem? types tyId with
            | some castTy =>
              if !(MirTy.beq castTy dstTy) then
                .error (.unsupported "Cast type mismatch") s
              else
                match evalRefMiriIntToIntCast v castTy with
                | .error k => .error (faultToStepError k) s
                | .ok res =>
                  match writeRefPlace s.locals dest res with
                  | .error k => .error (faultToStepError k) s
                  | .ok locals' => .ok () { s with locals := locals' }
            | none => .error (.unsupported "missing Cast target type") s
          | _ => .error (.unsupported "non-IntToInt Cast unsupported") s
      | none => .error (.invalidProgram "missing Cast operand payload") s
    | .immediate _, none =>
      .error (.unsupported "Cast into bare variant") s
    | .indirect _, _ => .error (.unsupported "indirect Cast operand") s
  readDiscriminant := fun c op s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (.enum ety, sv) =>
        match encodeRefEnumTagOp ety sv with
        | .error err => .error err s
        | .ok miriOp =>
          Miri.Interpreter.Discriminant.readDiscriminant
            (refDiscriminantHooks RefRvalueState ety) c miriOp s
      | _ => .error (.invalidProgram "non-enum Discriminant operand") s
    | .indirect _ => .error (.unsupported "indirect enum local unsupported") s
  discriminantForVariant := fun c ty variant s =>
    if !Nat.beq ty 0 then
      .error (.invalidProgram "unexpected enum TyId in discriminantForVariant") s
    else
      match s.discrEnum with
      | some ety =>
        match Miri.Interpreter.Discriminant.discriminantForVariant
            (refDiscriminantHooks RefRvalueState ety) c 0 variant s with
        | .error err s' => .error err s'
        | .ok discr s' =>
          match discr.imm with
          | .scalar msc =>
            match msc.tryToScalarInt with
            | .ok (.integer sc) =>
              let sv : SlotVal :=
                .scalar ⟨ety.discrWidth, ety.discrSigned, sc.data⟩
              .ok ⟨payloadToMiriImmediate
                    (.int ety.discrWidth ety.discrSigned, sv),
                  discr.layout⟩ s'
            | _ =>
              .error (.invalidProgram "non-integer discriminant scalar") s'
          | _ =>
            .error (.invalidProgram "non-scalar discriminant immediate") s'
      | none =>
        .error (.invalidProgram "missing cached enum in discriminantForVariant") s
}

/-- Reference rvalue evaluator over `Miri.MIR.Rvalue` and `Miri.MIR.Place`,
enforcing the fail-closed destination-overlap guard
(`refAssignHasUnsupportedOverlap`) before delegating destination place
resolution, outer dispatch, left-to-right operand sequencing, aggregates,
operator dispatch, discriminant reading, and destination writes to
`Miri.Interpreter.evalRvalueIntoPlace`, `Miri.Interpreter.writeAggregate`,
`Miri.Interpreter.Discriminant`, `Miri.Interpreter.placeWriteLocalImmediate`,
and `Miri.Interpreter.runRvalue`. -/
noncomputable def evalRefMiriRvalue (types : List MirTy)
    (rlocals : List RefLocalState) (dst : Miri.MIR.Place)
    (mirRv : Miri.MIR.Rvalue) :
    Except FaultKind (List RefLocalState) :=
  match MirSemantics.getElem? rlocals dst.localId with
  | some ⟨_, some localTy⟩ =>
    match refProjectTy? types localTy dst.projection.toList with
    | some dstTy =>
      if refAssignHasUnsupportedOverlap dst dstTy mirRv then
        .error .unsupported
      else
        let repeatCount : Option Nat :=
          match mirRv with
          | .Repeat _ (.Param count _ _) => some count
          | _ => none
        match Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace
              (refRvalueHooks types repeatCount) () mirRv dst)
            ⟨rlocals, false, none⟩ with
        | (st', .ok ()) => .ok st'.locals
        | (_, .error (.undefinedBehavior _))
        | (_, .error (.stack (.localExpectedLive _))) => .error .undefined
        | _ => .error .unsupported
    | none => .error .unsupported
  | _ => .error .unsupported

/-- `Miri.Interpreter.LocalStorageHooks` for
`Miri.Interpreter.Frame.storageLive` and
`Miri.Interpreter.Frame.storageDead`. -/
noncomputable def refLocalStorageHooks :
    Miri.Interpreter.LocalStorageHooks
      SlotVal Miri.Interpreter.LocalLayout Unit Unit := {
  veryTriviallySized := fun _ => .ok true
  layout := fun s _ _ => ⟨s, .ok refSizedLocalLayout⟩
  isSized := fun _ => true
  afterLocalWrite := fun s _ _ => ⟨s, .ok ()⟩
  allocateDyn := fun s _ _ =>
    ⟨s, .error (.allocationFailure "unsized local unsupported")⟩
  deallocateStack := fun s _ => ⟨s, .ok ()⟩
}

/-- Step-by-step static type projection in $M_{\text{ref}}$ over decoded
`ProjectionElem`s for `refControlHooksFor.copyReturn`. -/
noncomputable def refProjectReturnPlaceTy? :
    RefPlaceTy → List ProjectionElem → Option RefPlaceTy
  | pty, [] => some pty
  | .ty (.tuple fieldTys), .field idx statedTy :: rest =>
    match MirSemantics.getElem? fieldTys idx with
    | some fieldTy =>
      if MirTy.beq fieldTy statedTy then
        refProjectReturnPlaceTy? (.ty fieldTy) rest
      else
        none
    | none => none
  | .ty (.adtStruct sty), .field idx statedTy :: rest =>
    match MirSemantics.getElem? sty.fields idx with
    | some fieldTy =>
      if MirTy.beq fieldTy statedTy then
        refProjectReturnPlaceTy? (.ty fieldTy) rest
      else
        none
    | none => none
  | .variant ety v, .field idx statedTy :: rest =>
    match refFieldsForVariant? ety v with
    | some varFields =>
      match MirSemantics.getElem? varFields idx with
      | some fieldTy =>
        if MirTy.beq fieldTy statedTy then
          refProjectReturnPlaceTy? (.ty fieldTy) rest
        else
          none
      | none => none
    | none => none
  | .ty (.enum ety), .downcast v :: rest =>
    if refEnumAdmitted ety && Nat.blt v ety.discriminants.length then
      refProjectReturnPlaceTy? (.variant ety v) rest
    else
      none
  | .ty (.array elemTy len), .constantIndex _ _ _ :: rest =>
    if Nat.blt len (Nat.pow 2 64) then
      refProjectReturnPlaceTy? (.ty elemTy) rest
    else
      none
  | .ty (.array elemTy len), .index _ :: rest =>
    if Nat.blt len (Nat.pow 2 64) then
      refProjectReturnPlaceTy? (.ty elemTy) rest
    else
      none
  | _, _ :: _ => none

/-- Independent $M_{\text{ref}}$ type projection over decoded `Place`
projections used by `refControlHooksFor.copyReturn` when writing a callee's
return value into its caller's saved destination place. -/
noncomputable def refProjectReturnTy? (ty : MirTy)
    (proj : List ProjectionElem) : Option MirTy :=
  match refProjectReturnPlaceTy? (.ty ty) proj with
  | some (.ty resTy) => some resTy
  | _ => none

/-- Validate and canonicalize an already-static `ReturnContinuation.dst`
projection path in $M_{\text{ref}}$ via `Miri.Interpreter.project` (rejecting
any unresolved dynamic `.index`, `.deref`, or `.unsupported` step). -/
noncomputable def refResolveStaticReturnProj :
    RefPlaceTy → List ProjectionElem →
      Except FaultKind (List Miri.MIR.ProjectionElem)
  | .ty _, [] => .ok []
  | .variant _ _, [] => .error .unsupported
  | curPty, .field idx statedTy :: rest =>
    let noIdx : Miri.MIR.LocalId →
        Except Miri.Interpreter.ProjectionError UInt64 :=
      fun _ => .error (.invariant "dynamic index in static return proj")
    let mirElem : Miri.MIR.ProjectionElem := .Field idx 0
    match Miri.Interpreter.project (refProjectionCx curPty noIdx)
        (refBaseOpForProjStep curPty mirElem) mirElem with
    | .error err => .error (projErrorToFaultKind err)
    | .ok _ =>
      let fieldTy? : Option MirTy :=
        match curPty with
        | .ty (.tuple fieldTys) => MirSemantics.getElem? fieldTys idx
        | .ty (.adtStruct sty) => MirSemantics.getElem? sty.fields idx
        | .variant ety v =>
          match refFieldsForVariant? ety v with
          | some varFields => MirSemantics.getElem? varFields idx
          | none => none
        | _ => none
      match fieldTy? with
      | some fieldTy =>
        if MirTy.beq fieldTy statedTy then
          match refResolveStaticReturnProj (.ty fieldTy) rest with
          | .ok rest' => .ok (mirElem :: rest')
          | .error k => .error k
        else
          .error .unsupported
      | none => .error .unsupported
  | curPty, .downcast v :: rest =>
    let noIdx : Miri.MIR.LocalId →
        Except Miri.Interpreter.ProjectionError UInt64 :=
      fun _ => .error (.invariant "dynamic index in static return proj")
    let mirElem : Miri.MIR.ProjectionElem := .Downcast none v
    match Miri.Interpreter.project (refProjectionCx curPty noIdx)
        (refBaseOpForProjStep curPty mirElem) mirElem with
    | .error err => .error (projErrorToFaultKind err)
    | .ok _ =>
      match curPty with
      | .ty (.enum ety) =>
        match refResolveStaticReturnProj (.variant ety v) rest with
        | .ok rest' => .ok (mirElem :: rest')
        | .error k => .error k
      | _ => .error .unsupported
  | curPty, .constantIndex offset minLength fromEnd :: rest =>
    let noIdx : Miri.MIR.LocalId →
        Except Miri.Interpreter.ProjectionError UInt64 :=
      fun _ => .error (.invariant "dynamic index in static return proj")
    let mirElem : Miri.MIR.ProjectionElem :=
      .ConstantIndex offset minLength fromEnd
    match Miri.Interpreter.project (refProjectionCx curPty noIdx)
        (refBaseOpForProjStep curPty mirElem) mirElem with
    | .error err => .error (projErrorToFaultKind err)
    | .ok outOp =>
      match curPty, outOp.op with
      | .ty (.array elemTy _), .indirect mp =>
        let idx := mp.ptr.offset.bytes.toNat
        match refResolveStaticReturnProj (.ty elemTy) rest with
        | .ok rest' => .ok (.ConstantIndex idx (idx + 1) false :: rest')
        | .error k => .error k
      | _, _ => .error .unsupported
  | _, _ :: _ => .error .unsupported

/-- Decode a `Miri.MIR.ProjectionElem` against type table `ts` to recover the
resolved `ProjectionElem` for a callee's `ReturnContinuation.dst`. -/
noncomputable def decodeMiriProjElem (ts : List MirTy) :
    Miri.MIR.ProjectionElem → Option ProjectionElem
  | .Deref => some .deref
  | .Field idx tyId =>
    optMap (ProjectionElem.field idx) (MirSemantics.getElem? ts tyId)
  | .Downcast _ v => some (.downcast v)
  | .Index idxLocal => some (.index idxLocal)
  | .ConstantIndex offset minLength fromEnd =>
    some (.constantIndex offset minLength fromEnd)
  | _ => some .unsupported

/-- Decode a `Miri.MIR.Place` against type table `ts` into a resolved `Place`
(`decodeMiriPlace ts (toMiriPlace rp) = decodePlace ts rp`). -/
noncomputable def decodeMiriPlace (ts : List MirTy)
    (p : Miri.MIR.Place) : Option Place :=
  optMap (Place.mk p.localId)
    (mapOption (decodeMiriProjElem ts) p.projection.toList)

/-- Independent $M_{\text{ref}}$ destination-liveness check for
`Miri.Interpreter.Call.initStackFrame` (`placeToOp destination`): delegates base
local liveness to `Miri.Interpreter.evalPlaceToOp` and checks that writing
`refUninitSlotVal dstTy` along `dst.projection` succeeds
(`refWritePlaceSlotPath?`). -/
noncomputable def refCheckPlaceLive (rlocals : List RefLocalState)
    (dst : RefDest) : Except FaultKind Unit :=
  match dst.ty? with
  | none => .error .unsupported
  | some dstTy =>
    match MirSemantics.getElem? rlocals dst.localId with
    | some ⟨slot, some localTy⟩ =>
      let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
      match Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false) frame₀
          () ⟨0, Array.empty⟩ (some refSizedLocalLayout) with
      | ⟨_, _, .ok ⟨.immediate imm, _⟩⟩ =>
        let root : SlotVal :=
          match miriImmediateToPayload? imm with
          | some sv => sv
          | none => .uninit
        match refWritePlaceSlotPath? (.ty localTy) root dst.projection
            (refUninitSlotVal dstTy) with
        | some _ => .ok ()
        | none => .error .unsupported
      | _ => .error .undefined
    | _ => .error .unsupported

/-- Independent $M_{\text{ref}}$ call-entry destination deinitialization for
`Miri.Interpreter.Call.initStackFrame` (`protectArgument destinationMplace`):
reads the destination local through `Miri.Interpreter.evalPlaceToOp`, writes
`refUninitSlotVal dstTy` at `dst.projection` (`refWritePlaceSlotPath?`), and
commits the updated slot via `Miri.Interpreter.placeWriteLocalImmediate`. -/
noncomputable def refDeinitPlace (rlocals : List RefLocalState)
    (dst : RefDest) : Except FaultKind (List RefLocalState) :=
  match dst.ty? with
  | none => .error .unsupported
  | some dstTy =>
    match MirSemantics.getElem? rlocals dst.localId with
    | some ⟨slot, some localTy⟩ =>
      let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
      match Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false) frame₀
          () ⟨0, Array.empty⟩ (some refSizedLocalLayout) with
      | ⟨_, _, .ok ⟨.immediate imm, _⟩⟩ =>
        let root : SlotVal :=
          match miriImmediateToPayload? imm with
          | some sv => sv
          | none => .uninit
        match refWritePlaceSlotPath? (.ty localTy) root dst.projection
            (refUninitSlotVal dstTy) with
        | none => .error .unsupported
        | some root' =>
          match Miri.Interpreter.placeWriteLocalImmediate
              EStateM.get EStateM.set (pure true)
              (fun _ _ => pure ()) (fun _ _ => pure ())
              0 refSizedLocalLayout (payloadToMiriImmediate root') frame₀ with
          | .ok () frame₁ =>
            match frame₁.getLocal 0,
                MirSemantics.setElem? rlocals dst.localId
                  ⟨.live root', some localTy⟩ with
            | .ok ⟨.live (.immediate _), _⟩, some rlocals' => .ok rlocals'
            | .ok ⟨.live (.immediate _), _⟩, none => .error .unsupported
            | _, _ => .error .undefined
          | .error _ _ => .error .undefined
      | _ => .error .undefined
    | _ => .error .unsupported

/-- Stage 2 left-to-right primitive-operand reading for `CoreBuiltin` argument
lists in $M_{\text{ref}}$ (`readRefPrimitiveSlot`). -/
noncomputable def refReadPrimitiveArgs :
    List (MirTy × SlotVal) → Except FaultKind (List Val)
  | [] => .ok []
  | (ty, sv) :: rest =>
    match readRefPrimitiveSlot ty sv with
    | .error k => .error k
    | .ok v =>
      match refReadPrimitiveArgs rest with
      | .error k => .error k
      | .ok vs => .ok (v :: vs)

/-- Stage 2 `CoreBuiltin` argument reader in $M_{\text{ref}}$: `.fromLeBytes`
accepts a single `[u8; N]` fixed byte array (`len < 2^64`, faulting with
`.undefined` if any element is `.uninit`), while all other builtins delegate to
`refReadPrimitiveArgs`. -/
noncomputable def refReadBuiltinArgs (builtin : CoreBuiltin)
    (pairs : List (MirTy × SlotVal)) : Except FaultKind (List Val) :=
  match builtin with
  | .fromLeBytes =>
    match pairs with
    | [(.array (.int .i8 false) len, sv)] =>
      if !Nat.blt len (Nat.pow 2 64) then
        .error .unsupported
      else
        match sv.toVal? with
        | none => .error .undefined
        | some v => .ok [v]
    | _ => .error .unsupported
  | _ => refReadPrimitiveArgs pairs

/-- Independent $M_{\text{ref}}$ check that `ety` has the canonical 2-variant
`core::option::Option<T>` payload shape (`None` at `0`, `Some(innerTy)` at `1`).
-/
noncomputable def refIsOptionEnumForTy (ety : EnumTy) (innerTy : MirTy) :
    Bool :=
  refEnumAdmitted ety &&
    Nat.beq ety.discriminants.length 2 &&
    match refFieldsForVariant? ety 0, refFieldsForVariant? ety 1 with
    | some [], some [fTy] => MirTy.beq fTy innerTy
    | _, _ => false

/-- Evaluate `checked_{add,sub,mul}` in $M_{\text{ref}}$ via `evalRefMiriBinOp`
(`Miri.Interpreter.IntegerOps.binary`) into `Option<T>`. -/
noncomputable def evalRefCheckedArithOp (op : Miri.MIR.BinOp) (dstTy : MirTy)
    (l r : ScalarVal) : Except FaultKind Val :=
  match dstTy with
  | .enum ety =>
    if !refIsOptionEnumForTy ety (.int l.width l.signed) then
      .error .unsupported
    else
      match evalRefMiriBinOp op (.scalar l) (.scalar r) with
      | .ok (.tuple [.scalar wrapped, .bool false]) =>
        let res : Val := .enumVal ety 1 [.scalar wrapped]
        if checkRefVal res (.enum ety) then .ok res else .error .unsupported
      | .ok (.tuple [.scalar _, .bool true]) =>
        let res : Val := .enumVal ety 0 []
        if checkRefVal res (.enum ety) then .ok res else .error .unsupported
      | .error k => .error k
      | .ok _ => .error .unsupported
  | _ => .error .unsupported

/-- Explicit little-endian 64-bit `Miri.ABI.TargetDataLayout` for routing
`toLeBytes` and `fromLeBytes` through `Miri.Memory.Allocation`. -/
noncomputable def refLittleEndianTargetLayout : Miri.ABI.TargetDataLayout := {
  endian := .little
  pointerWidth := Miri.ABI.RuntimeTargetDataLayout.default.base.pointerWidth
}

/-- Replicate a byte `b : UInt8` `n` times via `@Nat.rec` (no `_unsafe_rec`). -/
noncomputable def refReplicateUInt8 (n : Nat) (b : UInt8) : List UInt8 :=
  @Nat.rec (fun _ => List UInt8) [] (fun _ ih => b :: ih) n

/-- Map `UInt8` bytes read from a `Miri.Memory.Allocation` to `u8` runtime
`Val`s in $M_{\text{ref}}$. -/
noncomputable def refUInt8ListToVals : List UInt8 → List Val
  | [] => []
  | b :: bs =>
    .scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩ :: refUInt8ListToVals bs

/-- Extract validated `UInt8` bytes from `u8` runtime `Val`s in $M_{\text{ref}}$
via `Miri.Memory.ScalarInt.tryFromUInt`. -/
noncomputable def refValsToUInt8List? : List Val → Option (List UInt8)
  | [] => some []
  | .scalar ⟨.i8, false, bits⟩ :: rest =>
    match Miri.Memory.ScalarInt.tryFromUInt bits (toMiriSize .i8) with
    | .ok (some sc) =>
      match refValsToUInt8List? rest with
      | some bs => some (UInt8.ofNat sc.data.toNat :: bs)
      | none => none
    | _ => none
  | _ :: _ => none

/-- Encode scalar `sv` to little-endian `u8` runtime `Val`s by writing `sv`
into a fresh `Miri.Memory.Allocation` via `Allocation.writeScalar` and reading
the bytes back via `Allocation.getBytesStripProvenance`. -/
noncomputable def refAllocScalarToLeBytes (sv : ScalarVal) :
    Except FaultKind (List Val) :=
  let sz := toMiriSize sv.width
  let range : Miri.Memory.AllocRange := ⟨Miri.ABI.Size.ZERO, sz⟩
  let zeros : Array UInt8 := Array.mk (refReplicateUInt8 sv.width.byteSize 0)
  match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance) zeros
      Miri.ABI.Align.ONE .Mut with
  | .error _ => .error .unsupported
  | .ok alloc₀ =>
    let sc : Miri.Memory.Scalar Miri.Memory.Provenance :=
      .fromScalarInt (miriScalar sv.width sv.bits)
    match Miri.Memory.Allocation.writeScalar refLittleEndianTargetLayout range
        sc alloc₀ with
    | .error _ _ => .error .unsupported
    | .ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout range with
      | .error _ => .error .unsupported
      | .ok bytes => .ok (refUInt8ListToVals bytes.toList)

/-- Decode little-endian `u8` runtime `Val`s `elems` into a scalar of width `w`
and signedness `s` by loading `elems` into a `Miri.Memory.Allocation` via
`Allocation.fromBytes` and reading via `Allocation.readScalar`. -/
noncomputable def refAllocScalarFromLeBytes (w : IntWidth) (s : Bool)
    (elems : List Val) : Except FaultKind Val :=
  let sz := toMiriSize w
  let range : Miri.Memory.AllocRange := ⟨Miri.ABI.Size.ZERO, sz⟩
  match refValsToUInt8List? elems with
  | none => .error .unsupported
  | some bs =>
    match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk bs) Miri.ABI.Align.ONE .Not with
    | .error _ => .error .unsupported
    | .ok alloc =>
      match Miri.Memory.Allocation.readScalar alloc refLittleEndianTargetLayout
          range false with
      | .error _ => .error .unsupported
      | .ok sc =>
        match sc.toBits sz with
        | .error _ => .error .unsupported
        | .ok bits => .ok (.scalar ⟨w, s, (miriScalar w bits).data⟩)

/-- Bijective `Nat` tag encoding each `CoreBuiltin` into a `Miri.MIR.DefId`
for `Miri.Interpreter.CallInstance.kind = .Intrinsic tag`. -/
noncomputable def coreBuiltinTag : CoreBuiltin → Nat
  | .wrappingAdd => 0
  | .wrappingSub => 1
  | .wrappingMul => 2
  | .wrappingShl => 3
  | .wrappingShr => 4
  | .overflowingAdd => 5
  | .overflowingSub => 6
  | .overflowingMul => 7
  | .saturatingAdd => 8
  | .saturatingSub => 9
  | .leadingZeros => 10
  | .trailingZeros => 11
  | .isMultipleOf => 12
  | .cmpMin => 13
  | .cmpMax => 14
  | .checkedAdd => 15
  | .checkedSub => 16
  | .checkedMul => 17
  | .toLeBytes => 18
  | .fromLeBytes => 19

/-- Left-inverse decoder for `coreBuiltinTag`. -/
noncomputable def coreBuiltinOfTag? : Nat → Option CoreBuiltin
  | 0 => some .wrappingAdd
  | 1 => some .wrappingSub
  | 2 => some .wrappingMul
  | 3 => some .wrappingShl
  | 4 => some .wrappingShr
  | 5 => some .overflowingAdd
  | 6 => some .overflowingSub
  | 7 => some .overflowingMul
  | 8 => some .saturatingAdd
  | 9 => some .saturatingSub
  | 10 => some .leadingZeros
  | 11 => some .trailingZeros
  | 12 => some .isMultipleOf
  | 13 => some .cmpMin
  | 14 => some .cmpMax
  | 15 => some .checkedAdd
  | 16 => some .checkedSub
  | 17 => some .checkedMul
  | 18 => some .toLeBytes
  | 19 => some .fromLeBytes
  | _ => none

/-- Reference `CoreBuiltin` evaluator routing every recognized `core::num` and
`core::cmp` builtin through `vendor/lean-miri` primitives:
- `wrapping{Add,Sub,Mul,Shl,Shr}`, `overflowing{Add,Sub,Mul}`,
  `checked{Add,Sub,Mul}`, `isMultipleOf`, and `cmp{Min,Max}` through
  `evalRefMiriBinOp` (`Miri.Interpreter.IntegerOps.binary`);
- `saturating{Add,Sub}` through
  `Miri.Interpreter.IntegerArithmeticIntrinsic.saturatingArith`
  (`vendor/lean-miri/Miri/Interpreter/IntegerCast.lean`);
- `leadingZeros` and `trailingZeros` through
  `Miri.Interpreter.IntegerIntrinsic.run` (`.ctlz` / `.cttz`,
  `vendor/lean-miri/Miri/Interpreter/IntegerCast.lean`);
- `toLeBytes` and `fromLeBytes` through `Miri.Memory.Allocation`
  (`Allocation.{fromBytes, writeScalar, getBytesStripProvenance, readScalar}`)
  under `refLittleEndianTargetLayout`. -/
noncomputable def evalRefCoreBuiltin (builtin : CoreBuiltin) (dstTy : MirTy)
    (args : List Val) : Except FaultKind Val :=
  match builtin, args with
  | .wrappingAdd, [.scalar l, .scalar r] =>
    evalRefMiriBinOp .Add (.scalar l) (.scalar r)
  | .wrappingSub, [.scalar l, .scalar r] =>
    evalRefMiriBinOp .Sub (.scalar l) (.scalar r)
  | .wrappingMul, [.scalar l, .scalar r] =>
    evalRefMiriBinOp .Mul (.scalar l) (.scalar r)
  | .wrappingShl, [.scalar l, .scalar r] =>
    if IntWidth.beq r.width .i32 && !r.signed then
      evalRefMiriBinOp .Shl (.scalar l) (.scalar r)
    else
      .error .unsupported
  | .wrappingShr, [.scalar l, .scalar r] =>
    if IntWidth.beq r.width .i32 && !r.signed then
      evalRefMiriBinOp .Shr (.scalar l) (.scalar r)
    else
      .error .unsupported
  | .overflowingAdd, [.scalar l, .scalar r] =>
    evalRefMiriBinOp .AddWithOverflow (.scalar l) (.scalar r)
  | .overflowingSub, [.scalar l, .scalar r] =>
    evalRefMiriBinOp .SubWithOverflow (.scalar l) (.scalar r)
  | .overflowingMul, [.scalar l, .scalar r] =>
    evalRefMiriBinOp .MulWithOverflow (.scalar l) (.scalar r)
  | .saturatingAdd, [.scalar l, .scalar r] =>
    match Miri.Interpreter.IntegerArithmeticIntrinsic.saturatingArith
        .add (miriIntValue l) (miriIntValue r) with
    | .ok sc => .ok (.scalar ⟨l.width, l.signed, sc.data⟩)
    | .error _ => .error .unsupported
  | .saturatingSub, [.scalar l, .scalar r] =>
    match Miri.Interpreter.IntegerArithmeticIntrinsic.saturatingArith
        .sub (miriIntValue l) (miriIntValue r) with
    | .ok sc => .ok (.scalar ⟨l.width, l.signed, sc.data⟩)
    | .error _ => .error .unsupported
  | .checkedAdd, [.scalar l, .scalar r] =>
    evalRefCheckedArithOp .AddWithOverflow dstTy l r
  | .checkedSub, [.scalar l, .scalar r] =>
    evalRefCheckedArithOp .SubWithOverflow dstTy l r
  | .checkedMul, [.scalar l, .scalar r] =>
    evalRefCheckedArithOp .MulWithOverflow dstTy l r
  | .leadingZeros, [.scalar sv] =>
    match Miri.Interpreter.IntegerIntrinsic.run .ctlz
        (miriScalar sv.width sv.bits) (toMiriIntType sv.width sv.signed)
        (toMiriIntType .i32 false) with
    | .ok sc => .ok (.scalar ⟨.i32, false, sc.data⟩)
    | .error _ => .error .unsupported
  | .trailingZeros, [.scalar sv] =>
    match Miri.Interpreter.IntegerIntrinsic.run .cttz
        (miriScalar sv.width sv.bits) (toMiriIntType sv.width sv.signed)
        (toMiriIntType .i32 false) with
    | .ok sc => .ok (.scalar ⟨.i32, false, sc.data⟩)
    | .error _ => .error .unsupported
  | .isMultipleOf, [.scalar l, .scalar r] =>
    if l.signed || r.signed || !IntWidth.beq l.width r.width then
      .error .unsupported
    else
      let zero : Val := .scalar ⟨l.width, false, BitVec.ofNat 128 0⟩
      match evalRefMiriBinOp .Eq (.scalar r) zero with
      | .ok (.bool true) => evalRefMiriBinOp .Eq (.scalar l) zero
      | .ok (.bool false) =>
        match evalRefMiriBinOp .Rem (.scalar l) (.scalar r) with
        | .ok remVal => evalRefMiriBinOp .Eq remVal zero
        | .error k => .error k
      | .error k => .error k
      | .ok _ => .error .unsupported
  | .toLeBytes, [.scalar sv] =>
    match dstTy with
    | .array (.int .i8 false) len =>
      if !Nat.beq len sv.width.byteSize then
        .error .unsupported
      else
        match refAllocScalarToLeBytes sv with
        | .error k => .error k
        | .ok vals => .ok (.array (.int .i8 false) vals)
    | _ => .error .unsupported
  | .fromLeBytes, [.array (.int .i8 false) elems] =>
    match dstTy with
    | .int w s =>
      if !Nat.beq elems.length w.byteSize then
        .error .unsupported
      else
        refAllocScalarFromLeBytes w s elems
    | _ => .error .unsupported
  | .cmpMin, [.scalar l, .scalar r] =>
    match evalRefMiriBinOp .Le (.scalar l) (.scalar r) with
    | .ok (.bool true) =>
      .ok (.scalar ⟨l.width, l.signed, (miriScalar l.width l.bits).data⟩)
    | .ok (.bool false) =>
      .ok (.scalar ⟨r.width, r.signed, (miriScalar r.width r.bits).data⟩)
    | .error k => .error k
    | .ok _ => .error .unsupported
  | .cmpMax, [.scalar l, .scalar r] =>
    match evalRefMiriBinOp .Ge (.scalar l) (.scalar r) with
    | .ok (.bool true) =>
      .ok (.scalar ⟨l.width, l.signed, (miriScalar l.width l.bits).data⟩)
    | .ok (.bool false) =>
      .ok (.scalar ⟨r.width, r.signed, (miriScalar r.width r.bits).data⟩)
    | .error k => .error k
    | .ok _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Provenance carrier threaded through `Miri.Interpreter.StepState` and
`Miri.Interpreter.CallHooks` so evaluated call destinations (`dst`) and
evaluated call arguments (`arg`) travel directly inside Miri's
`RuntimeStackPlace` and `OpTy` values. -/
inductive RefCallProv where
  | dst (dest : RefDest) (place : Place)
  | arg (ty : MirTy) (sv : SlotVal)

/-- Extract the evaluated `(MirTy, SlotVal)` argument payload carried inside an
`OpTy RefCallProv` (handling both immediate `.Copy`/`.Constant`/disjoint `.Move`
arguments and indirect non-disjoint `.Move` arguments uniformly). -/
noncomputable def extractRefCallArg?
    (op : Miri.Interpreter.OpTy RefCallProv) : Option (MirTy × SlotVal) :=
  match op.op with
  | .immediate imm =>
    match miriImmediateToPayload? imm with
    | some (.arg ty sv) => some (ty, sv)
    | _ => none
  | .indirect mp =>
    match mp.ptr.provenance with
    | some (.arg ty sv) => some (ty, sv)
    | _ => none

/-- In-progress callee frame accumulated across `pushRaw`, `passArgument`, and
`pushDone` inside `Miri.Interpreter.Call.initStackFrame`. -/
structure RefCalleeInit where
  defId : DefId
  rbody : RefBody
  localTys : List MirTy
  argValsRev : List Val
  returnCont : ReturnContinuation

/-- Machine state threaded through `Miri.Interpreter.Step.step`: holds the
active call stack `frames` top-to-bottom (current frame at the head), an
optional in-progress callee initialization record `calleeInit` populated during
`Miri.Interpreter.Call.initStackFrame`, and an optional `terminal` outcome (set
by `ControlHooks.copyReturn` on a root normal return and by
`ControlHooks.cleanupFrame` when unwinding leaves the root frame). -/
structure RefStepMachine where
  frames : List RefFrameState
  calleeInit : Option RefCalleeInit := none
  terminal : Option (StepResult RefState TerminalOut) := none

/-- Construct a single-frame `Miri.Interpreter.StepState` over `bbs` at
location `.mir ⟨blockIdx, 0⟩` with frame `cleanup` flag and top-to-bottom
active frames `rframe :: rcallers`. -/
noncomputable def mkRefStepStateWith (rframe : RefFrameState)
    (rcallers : List RefFrameState) (bbs : Array Miri.MIR.BasicBlock)
    (blockIdx : BasicBlockId) (cleanup : Bool) :
    Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout Unit
      RefStepMachine := {
  stack := ⟨Array.mk [{
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) cleanup with
    body := { refDummyMirBody cleanup with basicBlocks := bbs }
    location := .mir ⟨blockIdx, 0⟩
  }]⟩
  machine := { frames := rframe :: rcallers }
}

/-- Minimal `Miri.Interpreter.StepState` with a single statement `stmt` at
location `.mir ⟨0, 0⟩` so `Miri.Interpreter.Step.step` executes its statement
dispatch and statement-index increment path. -/
noncomputable def mkRefStmtStepState (rframe : RefFrameState)
    (rcallers : List RefFrameState) (stmt : Miri.MIR.Statement) :
    Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout Unit
      RefStepMachine :=
  mkRefStepStateWith rframe rcallers
    (Array.mk [{ refDummyMirBlock false with statements := Array.mk [stmt] }])
    0 false

/-- Map `Trusted.MirAst.UnwindAction` to `Miri.MIR.UnwindAction`.
`.terminate` maps to `.Terminate .Abi`; the reference machine rejects every
`.Terminate` reason in `refControlHooksFor.unwindTerminate`. -/
noncomputable def toMiriUnwindAction : UnwindAction → Miri.MIR.UnwindAction
  | .continue_ => .Continue
  | .cleanup target => .Cleanup target
  | .unreachable => .Unreachable
  | .terminate => .Terminate .Abi

/-- Construct a suspended `Miri.Interpreter.Frame` mirroring caller frame `rf`
on the Miri call stack (`bodyIdentity = 0` iff `rf.returnCont.isNone`, carrying
`rf`'s `returnContinuation` for multi-frame unwind propagation). -/
noncomputable def mkRefCallerMiriFrame (rf : RefFrameState) :
    Miri.Interpreter.Frame RefCallProv Miri.Interpreter.LocalLayout Unit := {
  mkSingleLocalMiriFrame
    (.dead : Miri.Interpreter.LocalValue RefCallProv) false with
  bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
    (if rf.returnCont.isNone then 0 else 1)
  returnContinuation :=
    match rf.returnCont with
    | none => .goto (some 0) .Continue
    | some c => .goto c.target (toMiriUnwindAction c.unwind)
  location := .mir ⟨0, 1⟩
}

/-- Build the bottom-to-top list of suspended Miri caller frames from the
top-to-bottom caller list `rcallers` (`mkCallerMiriFrames (c :: cs) =
mkCallerMiriFrames cs ++ [mkRefCallerMiriFrame c]`). -/
noncomputable def mkCallerMiriFrames :
    List RefFrameState →
    List (Miri.Interpreter.Frame RefCallProv Miri.Interpreter.LocalLayout Unit)
  | [] => []
  | rf :: rest => mkCallerMiriFrames rest ++ [mkRefCallerMiriFrame rf]

/-- Multi-frame `Miri.Interpreter.StepState` at terminator position
(`statements := Array.empty`, `location := .mir ⟨0, 1⟩`) so
`Miri.Interpreter.Step.step` executes its `beforeTerminator` + `terminator`
(`Miri.Interpreter.ControlFlow.evalTerminator`) path.

Setting `location := .mir ⟨0, 1⟩` (with `statements := Array.empty`) both
enters the terminator branch of `Step.step` and ensures a builtin call whose
`target = some 0` updates `location` to `.mir ⟨0, 0⟩ ≠ .mir ⟨0, 1⟩`, satisfying
Miri's call-progress check.

The stack mirrors `callerSentinelFrame :: (rframe :: rcallers).reverse`: a
sentinel frame sits beneath the root frame so
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame` can pop the root frame
while unwinding without triggering "unwinding past the topmost stack frame". -/
noncomputable def mkRefTermStepState (rframe : RefFrameState)
    (rcallers : List RefFrameState) (term : Miri.MIR.Terminator)
    (cleanup : Bool) :
    Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout Unit
      RefStepMachine :=
  let sentinelFrame :=
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) false
  let topFrame : Miri.Interpreter.Frame RefCallProv
      Miri.Interpreter.LocalLayout Unit := {
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) cleanup with
    body := {
      refDummyMirBody cleanup with
      basicBlocks :=
        Array.mk [{ refDummyMirBlock cleanup with terminator := term }]
    }
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
      (if rframe.returnCont.isNone then 0 else 1)
    returnContinuation :=
      match rframe.returnCont with
      | none => .goto (some 0) .Continue
      | some c => .goto c.target (toMiriUnwindAction c.unwind)
    location := .mir ⟨0, 1⟩
  }
  { stack := ⟨Array.mk
      ((sentinelFrame :: mkCallerMiriFrames rcallers) ++ [topFrame])⟩
    machine := { frames := rframe :: rcallers } }

/-- Minimal `Miri.Interpreter.StepState` with `basicBlocks := Array.empty` at
location `.mir ⟨blockIdx, 0⟩`. Because `basicBlocks` is empty,
`Miri.Interpreter.Step.step` always takes its out-of-bounds `.invalidBlock`
error path here (making the fallback `_ => .ub` arm in `evalRefStep`
unreachable). -/
noncomputable def mkRefInvalidBlockStepState (rframe : RefFrameState)
    (rcallers : List RefFrameState) (blockIdx : BasicBlockId) :
    Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout Unit
      RefStepMachine :=
  mkRefStepStateWith rframe rcallers Array.empty blockIdx false

/-- Extract the active `.mir loc` from the top frame of `st`, returning `none`
on an empty stack or `.unwinding` frame. -/
noncomputable def extractMirLocation? {P M : Type}
    (st : Miri.Interpreter.StepState P
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
  | .setDiscriminant place variantIdx =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .SetDiscriminant (toMiriPlace place) variantIdx }
  | .assign dst rvalue =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assign (toMiriPlace dst) (toMiriRvalue rvalue) }
  | .unsupported =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Intrinsic (.Assume (.Copy ⟨0, Array.empty⟩)) }

/-- Placeholder operand for the operand fields of `Miri.MIR.AssertKind`.

`Trusted.MirAst.AssertKind` drops the operands of an assert message, so
`toMiriAssertKind` fills each operand field with this placeholder. The
reference machine never evaluates it: `refTerminatorHooksFor.assertPanic`
reads only the message's constructor (and the operator of `.Overflow`). -/
noncomputable def refAssertOperandPlaceholder : Miri.MIR.Operand :=
  .Copy ⟨0, Array.empty⟩

/-- Map `Trusted.MirAst.AssertKind` to `Miri.MIR.AssertKind`, filling every
dropped message operand with `refAssertOperandPlaceholder`.

`.unsupported` maps to the fail-closed sentinel `.InvalidEnumConstruction`,
which `refIsOperandFreeAssertKind` rejects. -/
noncomputable def toMiriAssertKind : AssertKind → Miri.MIR.AssertKind
  | .boundsCheck =>
    .BoundsCheck refAssertOperandPlaceholder refAssertOperandPlaceholder
  | .overflow op =>
    .Overflow (toMiriBinOp op) refAssertOperandPlaceholder
      refAssertOperandPlaceholder
  | .overflowNeg => .OverflowNeg refAssertOperandPlaceholder
  | .divByZero => .DivisionByZero refAssertOperandPlaceholder
  | .remByZero => .RemainderByZero refAssertOperandPlaceholder
  | .misalignedPtrDeref =>
    .MisalignedPointerDereference refAssertOperandPlaceholder
      refAssertOperandPlaceholder
  | .nullPtrDeref => .NullPointerDereference
  | .unsupported => .InvalidEnumConstruction refAssertOperandPlaceholder

/-- Independent $M_{\text{ref}}$ check that a failing `Assert` with message
`msg` panics through a panic function that takes no operand.

`toMiriAssertKind` cannot restore the message operands that
`Trusted.MirAst.AssertKind` drops, so the reference machine accepts only the
messages whose panic never reads one: `.Overflow` of `.Add`, `.Sub`, `.Mul`,
`.Div`, `.Rem`, `.Shl`, or `.Shr`, and `.OverflowNeg`, `.DivisionByZero`,
`.RemainderByZero`, and `.NullPointerDereference` (see Miri's `assert_panic`
and `AssertKind::panic_function`, both quoted at
`Trusted.MirSemantics.isOperandFreeAssertKind`). Every other message is
rejected, so a failing assertion never skips the evaluation of a message
operand. -/
noncomputable def refIsOperandFreeAssertKind : Miri.MIR.AssertKind → Bool
  | .Overflow op _ _ =>
    match op with
    | .Add | .Sub | .Mul | .Div | .Rem | .Shl | .Shr => true
    | _ => false
  | .OverflowNeg _ | .DivisionByZero _ | .RemainderByZero _
  | .NullPointerDereference => true
  | _ => false

/-- Map `RefTerminatorKind` to its `Miri.MIR.Terminator` constructor for
`Miri.Interpreter.Step.step`, `Miri.Interpreter.ControlFlow.evalTerminator`,
and `Miri.Interpreter.Call.evalCallTerminator`.

- `.goto`, `.return_`, `.unreachable`, `.unwindResume`, `.switchInt`, `.assert`,
  `.call`, and `.callBuiltin` translate to their corresponding
  `Miri.MIR.TerminatorKind` constructors.
- `.call callee ...` encodes the function operand as a zero-sized constant with
  even `TyId = 2 * callee`, which `refCallHooks.resolve` maps to
  `CallInstance.kind = .Item callee`.
- `.callBuiltin builtin ...` encodes the function operand as a zero-sized
  constant with odd `TyId = 2 * coreBuiltinTag builtin + 1`, which
  `refCallHooks.resolve` maps to
  `CallInstance.kind = .Intrinsic (coreBuiltinTag builtin)`.
- `.unsupported` routes to the fail-closed sentinel `.UnwindTerminate .Abi`
  (firing `unwindTerminate` -> `.fault .unsupported`). -/
noncomputable def toMiriTerminatorForDispatch :
    RefTerminatorKind → Miri.MIR.Terminator
  | .goto target =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Goto target Array.empty }
  | .return_ =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
  | .unreachable =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Unreachable }
  | .unwindResume =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .UnwindResume }
  | .switchInt discr targets =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .SwitchInt (toMiriOperand discr)
        { cases := Array.mk
            (targets.branches.map (fun b => .Case b.1.toNat b.2))
          otherwise := targets.otherwise } }
  | .assert cond expected msg target unwind =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assert (toMiriOperand cond) expected (toMiriAssertKind msg)
        target (toMiriUnwindAction unwind) }
  | .call callee args dst target unwind =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Call
        (.Constant ⟨⟨0⟩, none, .Val .ZeroSized (2 * callee)⟩)
        (Array.mk (args.map (fun a => ⟨⟨0⟩, toMiriOperand a⟩)))
        (toMiriPlace dst) target (toMiriUnwindAction unwind) .Normal ⟨0⟩ }
  | .callBuiltin builtin args dst target unwind =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Call
        (.Constant ⟨⟨0⟩, none,
          .Val .ZeroSized (2 * coreBuiltinTag builtin + 1)⟩)
        (Array.mk (args.map (fun a => ⟨⟨0⟩, toMiriOperand a⟩)))
        (toMiriPlace dst) target (toMiriUnwindAction unwind) .Normal ⟨0⟩ }
  | .unsupported =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .UnwindTerminate .Abi }

/-- `Miri.Interpreter.CallHooks` wiring direct crate-local calls (`.call`) and
core numeric/comparison builtins (`.callBuiltin`) directly through
`Miri.Interpreter.Call.{evalCallTerminator, evalCalleeAndArgs, initFnCall,
initStackFrame, passArgument, run}`, `Miri.Interpreter.Stack.pushFrame`,
`Miri.Interpreter.ControlFlow.{goToBlock, returnToBlock}`,
`Miri.Interpreter.IntegerOps.binary`, `Miri.Interpreter.IntegerIntrinsic.run`,
and `Miri.Interpreter.IntegerArithmeticIntrinsic.saturatingArith`
(`vendor/lean-miri/Miri/Interpreter/{Call,Stack,ControlFlow,IntegerCast}.lean`),
matching `eval_callee_and_args` and `init_stack_frame` in
`compiler/rustc_const_eval/src/interpret/call.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`).

Move deinitialization of `.Move` arguments runs inside `evalPlace ... true` via
`evalRefMiriOperandToSlot` (`Miri.Interpreter.evalOperand` with
`deinitMovedPlace = true`), so `CallHooks.deinitMovedPlace` is set to `false`
to avoid redundant stack-memory snapshots for immediate locals. -/
noncomputable def refCallHooks (rp : RefProg) :
    Miri.Interpreter.CallHooks RefCallProv
      (Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout
        Unit RefStepMachine)
      Unit Unit Unit Unit Nat Unit := {
  debugAssertions := false
  getFrame := fun st =>
    match st.stack.currentFrame? with
    | some frame => .ok frame st
    | none => .error (.stack .emptyStack) st
  setFrame := fun frame st =>
    if st.stack.frames.isEmpty then
      .error (.stack .emptyStack) st
    else
      .ok () { st with stack := ⟨st.stack.frames.pop.push frame⟩ }
  frameIndex := fun st =>
    match st.stack.frameIndex with
    | .ok idx => .ok idx st
    | .error e => .error (.stack e) st
  evalOperand := fun _ mirOp st =>
    match st.machine.frames with
    | top :: rest =>
      match evalRefMiriOperandToSlot rp.types top.locals mirOp with
      | .error k => .error (faultToStepError k) st
      | .ok (ty, sv, locals') =>
        .ok ⟨.immediate (payloadToMiriImmediate (.arg ty sv)),
            refSizedLocalLayout⟩
          { st with machine := { st.machine with
              frames := { top with locals := locals' } :: rest } }
    | [] => .error (.unsupported "empty frames in call operand") st
  evalOperandAt := fun _ path mirOp st =>
    if Nat.beq path.size 2 then
      match mirOp with
      | .Constant ⟨_, _, .Val .ZeroSized encodedId⟩ =>
        .ok ⟨.immediate .uninit,
          { refSizedLocalLayout with ty := encodedId }⟩ st
      | _ => .error (.invalidProgram "non-constant callee") st
    else
      match st.machine.frames with
      | top :: rest =>
        match evalRefMiriOperandToSlot rp.types top.locals mirOp with
        | .error k => .error (faultToStepError k) st
        | .ok (ty, sv, locals') =>
          .ok ⟨.immediate (payloadToMiriImmediate (.arg ty sv)),
              refSizedLocalLayout⟩
            { st with machine := { st.machine with
                frames := { top with locals := locals' } :: rest } }
      | [] => .error (.unsupported "empty frames in call operand") st
  evalPlace := fun _ place isMove st =>
    if isMove then
      match st.machine.frames with
      | top :: rest =>
        match evalRefMiriOperandToSlot rp.types top.locals (.Move place) with
        | .error k => .error (faultToStepError k) st
        | .ok (ty, sv, locals') =>
          let mp : Miri.Interpreter.MPlaceTy RefCallProv :=
            ⟨⟨⟨Miri.ABI.Size.ZERO, some (.arg ty sv)⟩, .none, none⟩,
              refSizedLocalLayout⟩
          .ok (.memory mp)
            { st with machine := { st.machine with
                frames := { top with locals := locals' } :: rest } }
      | [] => .error (.unsupported "empty frames in move call arg") st
    else
      match st.machine.calleeInit with
      | some _ =>
        .ok (.frameLocal 0 place.localId none refSizedLocalLayout
          (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)) st
      | none =>
        match st.machine.frames with
        | top :: _ =>
          match MirSemantics.getElem? top.locals place.localId with
          | some ⟨_, some localTy⟩ =>
            match refProjectTy? rp.types localTy place.projection.toList with
            | none => .error (.unsupported "unsupported call destination") st
            | some dstTy =>
              match refResolveProjPath rp.types top.locals (.ty localTy)
                  place.projection.toList with
              | .error k => .error (faultToStepError k) st
              | .ok resolvedMiriProj =>
                match mapOption (decodeMiriProjElem rp.types)
                    resolvedMiriProj with
                | some resolvedDecodedProj =>
                  let rdest : RefDest :=
                    ⟨place.localId, resolvedMiriProj, .ty dstTy⟩
                  let decodedPlace : Place :=
                    ⟨place.localId, resolvedDecodedProj⟩
                  let mp : Miri.Interpreter.MPlaceTy RefCallProv :=
                    ⟨⟨⟨Miri.ABI.Size.ZERO, some (.dst rdest decodedPlace)⟩,
                        .none, none⟩,
                      refSizedLocalLayout⟩
                  .ok (.memory mp) st
                | none =>
                  .error (.unsupported "undecodable call destination") st
          | _ => .error (.unsupported "missing call destination local") st
        | [] => .error (.unsupported "empty frames in call destination") st
  placeToOp := fun _ rplace st =>
    match rplace with
    | .memory mp =>
      match mp.mplace.ptr.provenance with
      | some (.arg ty sv) =>
        .ok ⟨.immediate (payloadToMiriImmediate (.arg ty sv)),
          refSizedLocalLayout⟩ st
      | some (.dst rdest _) =>
        match st.machine.frames with
        | top :: _ =>
          match refCheckPlaceLive top.locals rdest with
          | .ok () => .ok ⟨.indirect mp.mplace, mp.layout⟩ st
          | .error k => .error (faultToStepError k) st
        | [] => .error (.unsupported "empty frames in destination liveness") st
      | none => .error (.invalidProgram "unexpected call place in placeToOp") st
    | _ => .error (.invalidProgram "unexpected call place in placeToOp") st
  forceAllocation := fun _ rplace st =>
    match rplace with
    | .memory mp => .ok mp st
    | _ => .error (.unsupported "forceAllocation on non-memory call arg") st
  functionSignature := fun _ _ st => .ok (0, ()) st
  functionKind := fun tyId st => .ok (.FnDef tyId Array.empty) st
  readPointer := fun _ _ st => .error (.unsupported "FnPtr unsupported") st
  getPtrFn := fun _ _ st => .error (.unsupported "FnPtr unsupported") st
  resolve := fun _ encodedId _ st =>
    if Nat.beq (Nat.mod encodedId 2) 0 then
      .ok { kind := .Item (Nat.div encodedId 2), args := Array.empty } st
    else
      .ok { kind := .Intrinsic (Nat.div encodedId 2), args := Array.empty } st
  fnAbiOfFnPtr := fun _ _ _ st => .error (.unsupported "FnPtr unsupported") st
  fnAbiOfInstance := fun _ inst _ st =>
    match inst.kind with
    | .Item callee =>
      match MirSemantics.getElem? rp.bodies callee with
      | some rbody => .ok rbody.argumentCount st
      | none => .ok 0 st
    | _ => .ok 0 st
  requiresCallerLocation := fun _ st => .ok false st
  callerLocation := fun st => .ok ⟨0⟩ st
  abiCanUnwind := fun _ => true
  abiVariadic := fun _ => false
  abiFixedCount := fun n => n
  abiArgs := fun n => Array.replicate n ()
  abiReturn := fun _ => ()
  sameConvention := fun _ _ => true
  isRustCall := fun _ => false
  rustAbi := ()
  argLayout := fun _ => refSizedLocalLayout
  argIsIgnore := fun _ => false
  isOneZst := fun _ => false
  checkArgumentCompat := fun _ _ _ st => .ok true st
  checkTargetFeatures := fun _ _ st => .ok () st
  tupleFields := fun _ st => .error (.unsupported "spread arg unsupported") st
  projectFnArg := fun _ _ _ st =>
    .error (.unsupported "RustCall unsupported") st
  localLayout := fun _ _ st => .ok refSizedLocalLayout st
  localSpan := fun _ _ st => .ok ⟨0⟩ st
  storageLiveDyn := fun _ _ _ st => .ok () st
  copyAllowTransmute := fun _ copied dest st =>
    match st.machine.calleeInit, extractRefCallArg? copied, dest with
    | some ci, some (argTy, sv), .frameLocal _ localId _ _ _ =>
      match MirSemantics.getElem? ci.localTys localId with
      | none => .error (.unsupported "missing callee parameter type") st
      | some paramTy =>
        if !(MirTy.beq argTy paramTy) then
          .error (.unsupported "call argument type mismatch") st
        else
          match sv.toVal? with
          | none => .error (.undefinedBehavior "uninit call argument") st
          | some v =>
            if !checkRefVal v paramTy then
              .error (.unsupported "invalid call argument value") st
            else
              .ok () { st with machine := { st.machine with
                calleeInit := some { ci with
                  argValsRev := v :: ci.argValsRev } } }
    | _, _, _ => .error (.invalidProgram "invalid copyAllowTransmute state") st
  protectArgument := fun _ mplace st =>
    match mplace.mplace.ptr.provenance with
    | some (.dst rdest _) =>
      match st.machine.frames with
      | top :: rest =>
        match refDeinitPlace top.locals rdest with
        | .ok localsAfterDeinit =>
          .ok () { st with machine := { st.machine with
            frames := { top with locals := localsAfterDeinit } :: rest } }
        | .error k => .error (faultToStepError k) st
      | [] => .error (.unsupported "empty frames in destination deinit") st
    | _ => .ok () st
  withRetagMode := fun _ _ act => act
  nonCapturingClosure := fun _ _ _ st => .ok false st
  allocateStack := fun _ _ st =>
    .error (.unsupported "allocateStack unsupported") st
  copyToMemory := fun _ _ _ st =>
    .error (.unsupported "copyToMemory unsupported") st
  vaListPtr := fun _ _ st => .error (.unsupported "varargs unsupported") st
  writeZeroBytes := fun _ _ _ st =>
    .error (.unsupported "varargs unsupported") st
  vaListKeyField := fun _ _ st => .error (.unsupported "varargs unsupported") st
  writePointerToMemory := fun _ _ _ st =>
    .error (.unsupported "varargs unsupported") st
  pushRaw := fun _ fnInstance loadedBody destination cont st =>
    match fnInstance.kind, destination with
    | .Item callee, .memory ⟨⟨⟨_, some (.dst _ decodedPlace)⟩, _, _⟩, _⟩ =>
      match MirSemantics.getElem? rp.bodies callee with
      | some rbody =>
        match decodeLocalTys rp.types rbody.locals with
        | some localTys =>
          let unwind' : UnwindAction :=
            match cont with
            | .goto _ (.Cleanup blk) => .cleanup blk
            | .goto _ .Unreachable => .unreachable
            | .goto _ (.Terminate _) => .terminate
            | _ => .continue_
          let target' : Option BasicBlockId :=
            match cont with
            | .goto t _ => t
            | .stop _ => none
          let newFrame : Miri.Interpreter.Frame RefCallProv
              Miri.Interpreter.LocalLayout Unit :=
            Miri.Interpreter.Frame.create loadedBody fnInstance () cont
              destination ⟨0⟩
              (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)
          match st.stack.pushFrame newFrame with
          | .ok stack' =>
            .ok () {
              stack := stack'
              machine := { st.machine with
                calleeInit := some {
                  defId := callee
                  rbody := rbody
                  localTys := localTys
                  argValsRev := []
                  returnCont := ⟨decodedPlace, target', unwind'⟩
                } }
            }
          | .error e => .error (.stack e) st
        | none => .error (.unsupported "bad callee locals in pushRaw") st
      | none => .error (.unsupported "missing callee body in pushRaw") st
    | _, _ => .error (.invalidProgram "invalid pushRaw arguments") st
  pushDone := fun _ st =>
    match st.machine.calleeInit with
    | some ci =>
      let calleeLocals :=
        initRefLocalsLoop ci.rbody ci.argValsRev.reverse 0 ci.localTys
      let calleeFrame : RefFrameState := {
        defId := ci.defId
        blockIdx := 0
        stmtIdx := 0
        locals := calleeLocals
        isCallerSentinel := false
        returnCont := some ci.returnCont
      }
      match Miri.Interpreter.ControlFlow.goToBlock 0 st with
      | (st', .ok ()) =>
        .ok () { st' with machine := { st'.machine with
          frames := calleeFrame :: st'.machine.frames
          calleeInit := none } }
      | (st', .error e) => .error e st'
    | none => .error (.invalidProgram "missing calleeInit in pushDone") st
  popRaw := fun _ st => .error (.unsupported "TailCall unsupported") st
  cleanup := fun _ _ _ st => .error (.unsupported "TailCall unsupported") st
  afterFrameInit := fun _ st => .ok () st
  callExtra := fun _ _ _ _ _ _ _ st =>
    .error (.unsupported "callExtra unsupported") st
  callIntrinsic := fun _ fnInstance args dest target _ st =>
    match fnInstance.kind, dest, st.machine.frames with
    | .Intrinsic tag, .memory ⟨⟨⟨_, some (.dst rdest _)⟩, _, _⟩, _⟩,
        top :: rest =>
      match rdest.ty?, coreBuiltinOfTag? tag,
          mapOption extractRefCallArg? args.toList with
      | some dstTy, some builtin, some argPairs =>
        match refReadBuiltinArgs builtin argPairs with
        | .error k => .error (faultToStepError k) st
        | .ok argVals =>
          match evalRefCoreBuiltin builtin dstTy argVals with
          | .error k => .error (faultToStepError k) st
          | .ok resVal =>
            match writeRefPlace top.locals rdest resVal with
            | .error k => .error (faultToStepError k) st
            | .ok localsAfterWrite =>
              let st1 := { st with machine := { st.machine with
                frames := { top with locals := localsAfterWrite } :: rest } }
              match Miri.Interpreter.ControlFlow.returnToBlock target st1 with
              | (st2, .ok ()) => .ok none st2
              | (st2, .error e) => .error e st2
      | _, _, _ => .error (.unsupported "invalid builtin call arguments") st
    | _, _, _ => .error (.invalidProgram "invalid callIntrinsic state") st
  callLlvmIntrinsic := fun _ _ _ _ _ st =>
    .error (.unsupported "LlvmIntrinsic unsupported") st
  findMirOrEvalFn := fun _ fnInstance _ args dest _ _ st =>
    match fnInstance.kind, dest with
    | .Item callee, .memory ⟨⟨⟨_, some (.dst rdest _)⟩, _, _⟩, _⟩ =>
      match rdest.ty?, MirSemantics.getElem? rp.bodies callee with
      | _, none => .error (.unsupported "callee body out of bounds") st
      | none, _ => .error (.unsupported "bare variant call destination") st
      | some dstTy, some rbody =>
        match decodeLocalTys rp.types rbody.locals with
        | none => .error (.unsupported "callee local types invalid") st
        | some localTys =>
          if !refBodyEntryAdmitted rbody localTys then
            .error (.unsupported "callee body not admitted") st
          else if !Nat.beq args.size rbody.argumentCount then
            .error (.unsupported "call argument count mismatch") st
          else
            match MirSemantics.getElem? localTys 0 with
            | none => .error (.unsupported "callee missing return local") st
            | some calleeRetTy =>
              if !MirTy.beq calleeRetTy dstTy then
                .error (.unsupported "call return type mismatch") st
              else
                let mirBody : Miri.MIR.Body := {
                  refDummyMirBody false with
                  argumentCount := rbody.argumentCount
                  spreadArgument := none
                }
                let loaded : Miri.Interpreter.LoadedBody := {
                  identity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex 1
                  body := mirBody
                }
                .ok (some (loaded, fnInstance)) st
    | _, _ => .error (.unsupported "invalid direct call target") st
  resolveVirtual := fun _ _ _ _ _ _ st =>
    .error (.unsupported "virtual call unsupported") st
  isDynamic := fun _ st => .ok false st
  unpackDynForDrop := fun _ _ st => .error (.unsupported "drop unsupported") st
  resolveDropGlue := fun _ _ st => .error (.unsupported "drop unsupported") st
  mplaceToMutRef := fun _ _ st => .error (.unsupported "drop unsupported") st
  fakeUnitReturn := fun _ st => .error (.unsupported "drop unsupported") st
  deinitMovedPlace := false
}

/-- `Miri.Interpreter.ControlHooks` for
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame` and
`Miri.Interpreter.ControlFlow.unwindToBlock`: the frame-popping half of
`refTerminatorHooksFor`, shared with `refStepHooksFor.returnFromCurrentFrame`.

`popFrame` pops both the Miri frame (`Miri.Interpreter.Stack.popFrame`) and the
top `RefFrameState` from `RefStepMachine.frames`:

- `copyReturn` (normal return) reads `_0` of the popped frame. On a root frame
  (`returnCont = none`, remaining stack `[]`), it records
  `.done (.returned ⟨retVal, callerMem⟩)` and `cleanupFrame` returns `.noJump`.
  On a callee frame (`returnCont = some cont`, remaining stack `caller ::
  rest`), it writes `retVal` into `cont.dst` in `caller` via `writeRefPlace`,
  and `cleanupFrame` returns `.normal` so `returnFromCurrentFrame` follows
  `Miri.Interpreter.ControlFlow.returnToBlock cont.target` (raising UB
  `"Unreachable"` when `cont.target = none`).
- `cleanupFrame` with `unwinding = true` records `.done (.unwound callerMem)`
  and returns `.noJump` when unwinding leaves the root frame (`bodyIdentity =
  0`, remaining stack `[]`); when unwinding leaves a callee frame
  (`bodyIdentity ≠ 0`, non-empty remaining stack), it returns `.normal` so
  `returnFromCurrentFrame` applies `ControlFlow.unwindToBlock` to the caller's
  `cont.unwind`.

Uninitialized-read UB in `copyReturn`: adapter frames never store
`Immediate.uninit` (see `slotToMiriLocalValue`), so `copyReturn` itself
rejects an uninitialized return place `_0` (contents with `sv.toVal? = none`
fault with `.undefined`; so does a dead `_0`, matching
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

`unwindTerminate` fails closed (`.fault .unsupported`): aborting the process
is unmodeled. -/
noncomputable def refControlHooksFor (rp : RefProg)
    (callerMem : CallerMemory) :
    Miri.Interpreter.ControlHooks RefCallProv Miri.Interpreter.LocalLayout
      Unit RefStepMachine Unit (Option RefFrameState) := {
  bodySpan := fun _ => .ok ⟨0⟩
  returnOperand := fun _ st => (st, .ok st.machine.frames.head?)
  popFrame := fun _ st =>
    match st.stack.popFrame, st.machine.frames with
    | .ok (stack', frame), _ :: rest =>
      ({ stack := stack', machine := { st.machine with frames := rest } },
        .ok frame)
    | .error e, _ => (st, .error (.stack e))
    | _, [] => (st, .error (.unsupported "empty frames in popFrame"))
  copyReturn := fun _ popped? _ st =>
    match popped? with
    | none => (st, .error (.unsupported "missing popped frame"))
    | some popped =>
      match MirSemantics.getElem? popped.locals 0 with
      | some ⟨.live sv, some _⟩ =>
        match sv.toVal? with
        | some retVal =>
          match popped.returnCont, st.machine.frames with
          | none, [] =>
            ({ st with machine := { st.machine with
                terminal := some (.done (.returned ⟨retVal, callerMem⟩)) } },
              .ok ())
          | some cont, caller :: rest =>
            match MirSemantics.getElem? rp.bodies caller.defId with
            | none => (st, .error (.unsupported "missing caller body"))
            | some _ =>
              match MirSemantics.getElem? caller.locals cont.dst.localId with
              | some ⟨_, some localTy⟩ =>
                match refProjectReturnTy? localTy cont.dst.projection with
                | none =>
                  (st, .error (.unsupported "unsupported return destination"))
                | some dstTy =>
                  match refResolveStaticReturnProj (.ty localTy)
                      cont.dst.projection with
                  | .error k => (st, .error (faultToStepError k))
                  | .ok resolvedMiriProj =>
                    let rdest : RefDest :=
                      ⟨cont.dst.localId, resolvedMiriProj, .ty dstTy⟩
                    match writeRefPlace caller.locals rdest retVal with
                    | .error k => (st, .error (faultToStepError k))
                    | .ok callerLocals' =>
                      ({ st with machine := { st.machine with
                          frames :=
                            { caller with locals := callerLocals' } :: rest } },
                        .ok ())
              | _ =>
                (st, .error (.unsupported "missing caller return local"))
          | _, _ => (st, .error (.unsupported "malformed call stack"))
        | none => (st, .error (.undefinedBehavior "uninit return place"))
      | some ⟨.dead, some _⟩ =>
        (st, .error (.undefinedBehavior "dead return place"))
      | _ => (st, .error (.unsupported "missing return place"))
  cleanupFrame := fun _ unwinding frame st =>
    if unwinding then
      match frame.bodyIdentity ==
              Miri.Interpreter.BodyIdentity.ofCanonicalIndex 0,
          st.machine.frames with
      | true, [] =>
        ({ st with machine := { st.machine with
            terminal := some (.done (.unwound callerMem)) } }, .ok .noJump)
      | false, _ :: _ => (st, .ok .normal)
      | _, _ => (st, .error (.unsupported "malformed unwind stack"))
    else if st.machine.terminal.isSome then
      (st, .ok .noJump)
    else
      (st, .ok .normal)
  unwindTerminate := fun _ _ st =>
    (st, .error (.unsupported "UnwindTerminate unsupported"))
}

/-- `Miri.Interpreter.TerminatorHooks` for
`Miri.Interpreter.ControlFlow.evalTerminator`, extending the frame-popping
hooks `refControlHooksFor` and wiring `.Call` through
`Miri.Interpreter.Call.evalCallTerminator` (`refCallHooks`).

`evalDiscriminant` evaluates Miri's passed `op : Miri.MIR.Operand` via
`evalRefMiriOperandToSlot` and `readRefPrimitiveSlot`, threading post-move
locals through the active frame at the head of `RefStepMachine.frames`.
`compareSwitchCase` decodes each case literal via `evalRefConstLit` and
compares via `evalRefMiriBinOp .Eq`. `assertPanic` checks
`refIsOperandFreeAssertKind` and invokes `ControlFlow.unwindToBlock`. `call`
runs `Miri.Interpreter.Call.evalCallTerminator (refCallHooks rp) c 2 term`. -/
noncomputable def refTerminatorHooksFor (rp : RefProg)
    (callerMem : CallerMemory) :
    Miri.Interpreter.TerminatorHooks RefCallProv Miri.Interpreter.LocalLayout
      Unit RefStepMachine Unit (Option RefFrameState) Val := {
  toControlHooks := refControlHooksFor rp callerMem
  evalDiscriminant := fun _ op st =>
    match st.machine.frames with
    | top :: rest =>
      match evalRefMiriOperandToSlot rp.types top.locals op with
      | .error k => (st, .error (faultToStepError k))
      | .ok (ty, sv, rlocalsAfterDiscr) =>
        match readRefPrimitiveSlot ty sv with
        | .error k => (st, .error (faultToStepError k))
        | .ok discrVal =>
          match discrVal with
          | .scalar _ | .bool _ =>
            ({ st with machine := { st.machine with
                frames := { top with locals := rlocalsAfterDiscr } :: rest } },
              .ok discrVal)
          | _ =>
            (st, .error (.unsupported "non-scalar SwitchInt discriminant"))
    | [] => (st, .error (.unsupported "empty frames in SwitchInt"))
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
  call := fun c term st =>
    match term.kind with
    | .Call _ args dst _ _ _ _ =>
      if refAnyMoveOperandMayOverlapPlace dst
          (args.toList.map (fun a => a.operand)) then
        (st, .error (.unsupported "overlapping move call arg and dest"))
      else
        Miri.Interpreter.Call.run
          (Miri.Interpreter.Call.evalCallTerminator (refCallHooks rp) c 2 term)
          st
    | _ =>
      Miri.Interpreter.Call.run
        (Miri.Interpreter.Call.evalCallTerminator (refCallHooks rp) c 2 term)
        st
  tailCall := fun _ _ st => (st, .error (.unsupported "TailCall unsupported"))
  drop := fun _ _ _ _ st => (st, .error (.unsupported "Drop unsupported"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ op st =>
    match st.machine.frames with
    | top :: rest =>
      match evalRefMiriOperandToSlot rp.types top.locals op with
      | .error k => (st, .error (faultToStepError k))
      | .ok (ty, sv, rlocalsAfterCond) =>
        match readRefPrimitiveSlot ty sv with
        | .error k => (st, .error (faultToStepError k))
        | .ok condVal =>
          match condVal with
          | .bool b =>
            ({ st with machine := { st.machine with
                frames := { top with locals := rlocalsAfterCond } :: rest } },
              .ok b)
          | _ => (st, .error (.unsupported "non-bool Assert condition"))
    | [] => (st, .error (.unsupported "empty frames in Assert"))
  assertPanic := fun c msg unwind st =>
    if !refIsOperandFreeAssertKind msg then
      (st, .error (.unsupported "Assert message operands unsupported"))
    else
      Miri.Interpreter.ControlFlow.unwindToBlock
        (refControlHooksFor rp callerMem) c unwind st
}

/-- `Miri.Interpreter.StepHooks` routing `.Assign`, `.SetDiscriminant`,
`.StorageLive`, `.StorageDead`, and terminators through
`Miri.Interpreter.Step.step`, `Miri.Interpreter.Step.evalStatement`,
`Miri.Interpreter.Discriminant.writeDiscriminant`,
`Miri.Interpreter.Frame.storageLive`, `Miri.Interpreter.Frame.storageDead`,
`Miri.Interpreter.ControlFlow.evalTerminator`,
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`, and
`Miri.Interpreter.Call.evalCallTerminator`. -/
noncomputable def refStepHooksFor (rp : RefProg)
    (callerMem : CallerMemory) :
    Miri.Interpreter.StepHooks RefCallProv Miri.Interpreter.LocalLayout Unit
      RefStepMachine Unit RefDest := {
  assign := fun _ dst rvalue st =>
    match st.machine.frames with
    | top :: rest =>
      match evalRefMiriRvalue rp.types top.locals dst rvalue with
      | .error k => (st, .error (faultToStepError k))
      | .ok rlocalsAfterWrite =>
        ({ st with machine := { st.machine with
            frames := { top with locals := rlocalsAfterWrite } :: rest } },
          .ok ())
    | [] => (st, .error (.unsupported "empty frames in assign"))
  evalPlace := fun _ place _ st =>
    match st.machine.frames with
    | top :: _ =>
      match MirSemantics.getElem? top.locals place.localId with
      | some ⟨_, some localTy⟩ =>
        match refProjectTy? rp.types localTy place.projection.toList with
        | none => (st, .error (.unsupported "ill-typed SetDiscriminant place"))
        | some dstTy =>
          match refResolveProjPath rp.types top.locals (.ty localTy)
              place.projection.toList with
          | .error k => (st, .error (faultToStepError k))
          | .ok resolvedProj =>
            (st, .ok ⟨place.localId, resolvedProj, .ty dstTy⟩)
      | _ => (st, .error (.unsupported "missing SetDiscriminant local"))
    | [] => (st, .error (.unsupported "empty frames in SetDiscriminant"))
  writeDiscriminant := fun _ variantIdx rdest st =>
    match st.machine.frames with
    | top :: rest =>
      match evalRefSetDiscriminant top.locals rdest variantIdx with
      | .error k => (st, .error (faultToStepError k))
      | .ok rlocalsAfterWrite =>
        ({ st with machine := { st.machine with
            frames := { top with locals := rlocalsAfterWrite } :: rest } },
          .ok ())
    | [] => (st, .error (.unsupported "empty frames in writeDiscriminant"))
  storageLive := fun _ localId st =>
    let res := Miri.Interpreter.Frame.storageLive
      (mkSingleLocalMiriFrame
        (.dead : Miri.Interpreter.LocalValue SlotVal) false)
      () refLocalStorageHooks 0
    match res.outcome, st.machine.frames with
    | .error e, _ => (st, .error (.stack e))
    | .ok (), top :: rest =>
      match MirSemantics.getElem? top.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? top.locals localId
            ⟨refLiveUninitSlot localTy, some localTy⟩ with
        | some rlocals' =>
          ({ st with machine := { st.machine with
              frames := { top with locals := rlocals' } :: rest } },
            .ok ())
        | none => (st, .error (.unsupported "storageLive local out of bounds"))
      | _ => (st, .error (.unsupported "storageLive missing cached layout"))
    | .ok (), [] => (st, .error (.unsupported "empty frames in storageLive"))
  storageDead := fun _ localId st =>
    let res := Miri.Interpreter.Frame.storageDead
      (mkTwoLocalMiriFrame .dead .dead) () refLocalStorageHooks
      (if Nat.beq localId 0 then 0 else 1)
    match res.outcome, st.machine.frames with
    | .error e, _ => (st, .error (.stack e))
    | .ok (), top :: rest =>
      match MirSemantics.getElem? top.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? top.locals localId
            ⟨.dead, some localTy⟩ with
        | some rlocals' =>
          ({ st with machine := { st.machine with
              frames := { top with locals := rlocals' } :: rest } },
            .ok ())
        | none => (st, .error (.unsupported "storageDead local out of bounds"))
      | _ => (st, .error (.unsupported "storageDead missing cached layout"))
    | .ok (), [] => (st, .error (.unsupported "empty frames in storageDead"))
  intrinsic := fun _ _ st => (st, .error (.unsupported "Intrinsic"))
  incrementConstEvalCounter := fun _ st => (st, .ok ())
  returnFromCurrentFrame :=
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (refControlHooksFor rp callerMem)
  beforeTerminator := fun _ st => (st, .ok ())
  terminator :=
    Miri.Interpreter.ControlFlow.evalTerminator
      (refTerminatorHooksFor rp callerMem)
}

/-- Bounded structural loop draining `.unwinding` Miri frames via
`Miri.Interpreter.Step.step` (`returnFromCurrentFrame` + `unwindToBlock`) until
unwinding reaches a cleanup block (`.mir loc`), leaves the root frame
(`terminal = some (.done (.unwound callerMem))`), or faults (`.unreachable` UB
or `.terminate` / malformed stack `.unsupported`).

Because $M_{\text{anneal}}$ (`Trusted.MirSemantics.unwindFrame`) propagates
across frames without `.cleanup` handlers in one small-step transition,
`evalRefTerminator` invokes `drainRefUnwind` with `fuel := rcallers.length + 1`
(sufficient to unwind every active frame on the stack) so both machines stay in
exact 1-to-1 small-step lockstep. -/
noncomputable def drainRefUnwind (rp : RefProg) (callerMem : CallerMemory) :
    Nat →
    Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout Unit
      RefStepMachine →
    StepResult RefState TerminalOut
  | 0, _ => .fault .unsupported
  | fuel + 1, st =>
    match Miri.Interpreter.Step.step (refStepHooksFor rp callerMem) () st with
    | (st', .ok true) =>
      match st'.machine.terminal with
      | some res => res
      | none =>
        match extractMirLocation? st', st'.machine.frames with
        | some loc, top :: rest =>
          .step {
            frames := ({
              top with
              blockIdx := loc.block
              stmtIdx := loc.statementIndex
            } :: rest).reverse
            callerMem
          }
        | none, _ => drainRefUnwind rp callerMem fuel st'
        | _, _ => .fault .unsupported
    | (_, .error (.undefinedBehavior _)) => .fault .undefined
    | (_, _) => .fault .unsupported

/-- Reference statement evaluator delegating outer step and statement dispatch
to `Miri.Interpreter.Step.step` and `Miri.Interpreter.Step.evalStatement`,
`_0` `StorageDead` rejection to `Miri.Interpreter.Frame.storageDead`, and
exercising `Miri.Interpreter.Frame.storageLive` (whose dummy-frame call always
returns `.ok ()`; see `refStepHooksFor`)
(`vendor/lean-miri/Miri/Interpreter/{Step,Stack}.lean`), matching
`eval_statement` in `compiler/rustc_const_eval/src/interpret/step.rs` and
`storage_live` / `storage_dead` in
`compiler/rustc_const_eval/src/interpret/stack.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def evalRefStatement (rp : RefProg) (rframe : RefFrameState)
    (rcallers : List RefFrameState) (callerMem : CallerMemory)
    (stmt : RefStatementKind) : StepResult RefState TerminalOut :=
  match Miri.Interpreter.Step.step
      (refStepHooksFor rp callerMem) ()
      (mkRefStmtStepState rframe rcallers
        (toMiriStatementForDispatch stmt)) with
  | (st', .ok true) =>
    match extractMirLocation? st', st'.machine.frames with
    | some loc, top :: rest =>
      .step {
        frames := ({
          top with
          stmtIdx := rframe.stmtIdx + loc.statementIndex
        } :: rest).reverse
        callerMem
      }
    | _, _ => .fault .unsupported
  | (_, .error (.undefinedBehavior _)) => .fault .undefined
  | (_, _) => .fault .unsupported

/-- Reference terminator evaluator delegating outer step, terminator dispatch,
direct crate-local calls, `CoreBuiltin` intrinsic calls, `SwitchInt` branch
selection, `Assert` checking, `goToBlock`/`returnToBlock` jumps, multi-frame
unwinding, and frame pushing/popping to `Miri.Interpreter.Step.step`,
`Miri.Interpreter.ControlFlow.{evalTerminator, goToBlock, returnToBlock,
unwindToBlock, returnFromCurrentFrame}`,
`Miri.Interpreter.Call.evalCallTerminator`, and
`Miri.Interpreter.Stack.{pushFrame, popFrame}`
(`vendor/lean-miri/Miri/Interpreter/{Step,ControlFlow,Call,Stack}.lean`). -/
noncomputable def evalRefTerminator (rp : RefProg) (rbb : RefBasicBlock)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) : StepResult RefState TerminalOut :=
  match Miri.Interpreter.Step.step
      (refStepHooksFor rp callerMem) ()
      (mkRefTermStepState rframe rcallers
        (toMiriTerminatorForDispatch rbb.terminator) rbb.cleanup) with
  | (st', .ok true) =>
    match st'.machine.terminal with
    | some res => res
    | none =>
      match extractMirLocation? st', st'.machine.frames with
      | some loc, top :: rest =>
        .step {
          frames := ({
            top with
            blockIdx := loc.block
            stmtIdx := loc.statementIndex
          } :: rest).reverse
          callerMem
        }
      | none, _ => drainRefUnwind rp callerMem (rcallers.length + 1) st'
      | _, _ => .fault .unsupported
  | (_, .error (.undefinedBehavior _)) => .fault .undefined
  | (_, _) => .fault .unsupported

/-- Single-step evaluator of $M_{\text{ref}}$:
checks `rs.stepsExecuted < rs.maxSteps` first, returning `.exhaustedStepLimit`
when the step budget is reached, and otherwise validates the stack shape
(`sentinel :: activeBottomToTop` with `sentinel.isCallerSentinel = true`, no
active frame marked sentinel, and `activeBottomToTop.reverse = rframe ::
rcallers`), resolves the active `RefBody` and `RefBasicBlock`, and delegates
statement, terminator, and out-of-bounds block transitions to
`Miri.Interpreter.Step.step` (`evalRefStatement`, `evalRefTerminator`, and
`mkRefInvalidBlockStepState`), incrementing `stepsExecuted := rs.stepsExecuted
+ 1` on each running step. -/
noncomputable def evalRefStep (rp : RefProg) (_c : Choice)
    (rs : RefState) : RefOutcome :=
  if !Nat.blt rs.stepsExecuted rs.maxSteps then
    .exhaustedStepLimit
  else
    match rs.frames with
    | sentinel :: activeBottomToTop =>
      if !sentinel.isCallerSentinel ||
          activeBottomToTop.any (fun f => f.isCallerSentinel) then
        .blocked
      else
        match activeBottomToTop.reverse with
        | rframe :: rcallers =>
          match MirSemantics.getElem? rp.bodies rframe.defId with
          | none => .blocked
          | some rbody =>
            match MirSemantics.getElem? rbody.basicBlocks rframe.blockIdx with
            | none =>
              match Miri.Interpreter.Step.step
                  (refStepHooksFor rp rs.callerMem) ()
                  (mkRefInvalidBlockStepState rframe rcallers
                    rframe.blockIdx) with
              | (_, .error (.invalidBlock _)) => .blocked
              | _ => .ub
            | some rbb =>
              match MirSemantics.getElem? rbb.statements rframe.stmtIdx with
              | some rstmt =>
                stepResultToRefOutcome sentinel rs.stepsExecuted rs.maxSteps
                  (evalRefStatement rp rframe rcallers rs.callerMem rstmt)
              | none =>
                if Nat.beq rframe.stmtIdx rbb.statements.length then
                  stepResultToRefOutcome sentinel rs.stepsExecuted rs.maxSteps
                    (evalRefTerminator rp rbb rframe rcallers rs.callerMem)
                else
                  .blocked
        | [] => .blocked
    | [] => .blocked

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

/-! ## One-to-One Simulation Invariant (`SimulationInv`) -/

/-- Pair each runtime `LocalSlot` with its pre-cached `some ty` layout. -/
noncomputable def zipRefLocals :
    List MirTy → List LocalSlot → List RefLocalState
  | ty :: tys, slot :: slots => ⟨slot, some ty⟩ :: zipRefLocals tys slots
  | _, _ => []

/-- Lift an $M_{\text{anneal}}$ `FrameState` to its unique $M_{\text{ref}}$
`RefFrameState` with `cachedLayout` populated from `bodyLocals`. -/
noncomputable def liftFrame (bodyLocals : List MirTy)
    (f : FrameState) : RefFrameState :=
  { defId := f.defId
    blockIdx := f.blockIdx
    stmtIdx := f.stmtIdx
    locals := zipRefLocals bodyLocals f.locals
    isCallerSentinel := false
    returnCont := f.returnCont }

/-- Lift a top-to-bottom stack of $M_{\text{anneal}}$ `FrameState`s to
$M_{\text{ref}}$ `RefFrameState`s by looking up each frame's `body.locals` in
`p.bodies`. -/
noncomputable def liftFrames (p : Program) :
    List FrameState → List RefFrameState
  | [] => []
  | f :: fs =>
    let bodyLocals :=
      match MirSemantics.getElem? p.bodies f.defId with
      | some body => body.locals
      | none => []
    liftFrame bodyLocals f :: liftFrames p fs

/-- Lift an $M_{\text{anneal}}$ `StepResult` to $M_{\text{ref}}$, converting
the active top-to-bottom call stack `fs` into bottom-to-top order
`(liftFrames p fs).reverse`. -/
noncomputable def mapStepRes (p : Program) :
    StepResult State TerminalOut → StepResult RefState TerminalOut
  | .step { frames := fs, callerMem := cm } =>
    .step { frames := (liftFrames p fs).reverse, callerMem := cm }
  | .done out => .done out
  | .fault k => .fault k

/-- Frame-level one-to-one simulation invariant: relates $M_{\text{anneal}}$
frame `f` to $M_{\text{ref}}$ frame `rf` via exact equality
`rf = liftFrame body.locals f`. -/
def FrameSimInv (p : Program) (f : FrameState)
    (rf : RefFrameState) : Prop :=
  ∃ body : Body,
    MirSemantics.getElem? p.bodies f.defId = some body ∧
    f.locals.length = body.locals.length ∧
    rf = liftFrame body.locals f

/-- Stack-level one-to-one simulation invariant relating top-to-bottom
$M_{\text{anneal}}$ frames `fs` and top-to-bottom $M_{\text{ref}}$ frames
`rfs` element by element under `FrameSimInv`. -/
def FramesSimInv (p : Program) (fs : List FrameState)
    (rfs : List RefFrameState) : Prop :=
  @List.rec FrameState (fun _ => List RefFrameState → Prop)
    (fun rfs =>
      match rfs with
      | [] => True
      | _ :: _ => False)
    (fun f _ ih rfs =>
      match rfs with
      | [] => False
      | rf :: rfs' => FrameSimInv p f rf ∧ ih rfs')
    fs rfs

/-- Type of the entry function's return place `_0`, which types the caller
sentinel's destination slot (`callerSentinelFrame`). -/
noncomputable def entryRetTy? (p : Program) : Option MirTy :=
  match MirSemantics.getElem? p.bodies p.entryDefId with
  | some body => MirSemantics.getElem? body.locals 0
  | none => none

/-- Whole-state one-to-one simulation invariant between $M_{\text{anneal}}$ and
$M_{\text{ref}}$: constrains every field of `s` and `rs` (up to the explicit
step counters `rs.stepsExecuted` and `rs.maxSteps`), placing the fixed caller
sentinel for the entry function's return type beneath the reversed (bottom-to-
top) lifted image of `s.frames`. -/
def SimulationInv (p : Program) (s : State) (rs : RefState) :
    Prop :=
  ∃ rfs : List RefFrameState, ∃ retTy : MirTy,
    s.frames ≠ [] ∧
    rs.frames = callerSentinelFrame retTy :: rfs.reverse ∧
    rs.callerMem = s.callerMem ∧
    entryRetTy? p = some retTy ∧
    FramesSimInv p s.frames rfs

/-! ## Trusted Top-Level Correspondence and Canary Claims -/

/-- Trusted statement of the correspondence theorem between
$M_{\text{anneal}}$ (`Trusted.MirSemantics`) and $M_{\text{ref}}$
(`Trusted.Correspondence`). For every well-formed `(p, q)`:
1. `encodeProg p` is well-formed in $M_{\text{ref}}$ under every step budget
   (UB transfer);
2. both machines exhibit exactly the same terminal behaviors; and
3. `(p, q)` diverges in $M_{\text{anneal}}$ if and only if `encodeProg p`
   diverges in $M_{\text{ref}}$.

The behavior and divergence equivalences rule out reference executions that
$M_{\text{anneal}}$ omits, so a postcondition proved over `Behavior` cannot
miss an outcome that the reference model permits. -/
def CorrespondenceClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q →
    RefWellFormed (encodeProg p) q ∧
    (∀ (out : TerminalOut),
      Behavior p q out ↔ RefBehavior (encodeProg p) q out) ∧
    (Diverges p q ↔ RefDiverges (encodeProg p) q)

/-- Trusted statement of bidirectional fault equivalence for all
`k : FaultKind` (`.undefined` ↔ `.ub` and `.unsupported` ↔ `.blocked`). -/
def FaultEquivalenceClaim : Prop :=
  ∀ (p : Program) (q : Query) (k : FaultKind),
    ReachesResult p q (.fault k) ↔
    ∃ maxSteps,
      RefReachesOutcome (encodeProg p) q maxSteps (faultToRefOutcome k)

/-- Trusted statement verifying the direct consumer-side wiring of
`Miri.Interpreter.ExecutionMachine.step` (`Miri.Interpreter.Step.step` over
`Miri.Interpreter.ExecutionMachine.stepHooks`) and `deinitMovedPlace` in
`vendor/lean-miri` (`Miri.Interpreter.ExecutionMachine.withValidation`,
`Miri.Interpreter.ExecutionMachine.operandHooks`, and
`Miri.Interpreter.evalOperand`).

Its operand-evaluation conjuncts cover the move behavior of
`Miri.Interpreter.evalOperand`
(`vendor/lean-miri/Miri/Interpreter/LocalAccess.lean`), the only operand path
of the reference adapter (`evalRefPlaceOperand`). For
`Miri.Interpreter.OperandMachine.evalOperand`, the claim fixes only the
`deinitMovedPlace` flag that `operandHooks` passes to it, not its move
behavior. `ExecutionMachine` uses `OperandMachine.evalOperand` to build
`rvalueHooks`, `intrinsicHooks`, and `stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`, lines 182, 267,
and 403 at the pinned digest); that operand path is trusted by human audit, as
`docs/mir-correspondence-design.md` Section 2.4 records. -/
def MiriMoveDeinitWiringClaim : Prop :=
  (∀ {K U C O X Host : Type} [DecidableEq K]
      (cfg : Miri.Interpreter.ExecutionMachine.Config K U C O X Host)
      (limits : Miri.Interpreter.ExecutionMachine.Limits)
      (c : C)
      (state : Miri.Interpreter.MachineHooks.State K U),
    Miri.Interpreter.ExecutionMachine.step cfg limits c state =
      let (state', out) := Miri.Interpreter.Step.step
        (Miri.Interpreter.ExecutionMachine.stepHooks cfg limits) c
        { state with
          machine := { state.machine with pendingMoveDeinit := false } }
      ( { state' with
          machine := { state'.machine with pendingMoveDeinit := false } },
        out )) ∧
  (∀ {K U C O X Host : Type} [DecidableEq K]
      (cfg : Miri.Interpreter.ExecutionMachine.Config K U C O X Host)
      (limits : Miri.Interpreter.ExecutionMachine.Limits),
    cfg.deinitMovedPlace = true →
    (Miri.Interpreter.ExecutionMachine.withValidation
        cfg limits).access.deinitMovedPlace = true ∧
    (Miri.Interpreter.ExecutionMachine.operandHooks
        cfg).deinitMovedPlace = true) ∧
  (∀ {Prov Extra State : Type}
      (hooks : Miri.Interpreter.LocalAccessHooks Prov Extra State)
      (frame : Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Extra)
      (state : State)
      (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = false →
    Miri.Interpreter.evalOperand hooks frame state
        (.Move ⟨localId, Array.empty⟩) known =
      Miri.Interpreter.evalPlaceToOp hooks frame state
        ⟨localId, Array.empty⟩ known) ∧
  (∀ {Prov Extra State : Type}
      (hooks : Miri.Interpreter.LocalAccessHooks Prov Extra State)
      (frame frame₁ frame₂ :
        Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Extra)
      (state state₁ : State)
      (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout)
      (imm : Miri.Interpreter.Immediate Prov)
      (layout : Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = true →
    Miri.Interpreter.evalPlaceToOp hooks frame state
        ⟨localId, Array.empty⟩ known =
      ⟨frame₁, state₁, .ok ⟨.immediate imm, layout⟩⟩ →
    frame₁.replaceLocalValue localId
        (.live (if layout.layout.isZst then .immediate imm
          else .immediate .uninit)) =
      .ok frame₂ →
    Miri.Interpreter.evalOperand hooks frame state
        (.Move ⟨localId, Array.empty⟩) known =
      ⟨frame₂, state₁, .ok ⟨.immediate imm, layout⟩⟩) ∧
  (∀ {K U : Type}
      (m : Miri.Interpreter.MachineHooks.MachineState K U) (isMove : Bool),
    (Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit
       (Miri.Interpreter.MachineHooks.recordPendingMoveDeinit m isMove)).2 =
      isMove) ∧
  (∀ {P S C E Other Extern FnABI ArgABI : Type}
      (h : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI)
      (choice : C)
      (place : Miri.Interpreter.MPlaceTy P)
      (snap : Miri.Interpreter.OpTy P),
    Miri.Interpreter.FnArg.copyFnArg (.InPlace place (some snap)) = snap ∧
    Miri.Interpreter.Call.deinitInPlaceArg h choice place (some snap) =
      Bind.bind (h.restoreInPlaceMovedBytes choice snap place)
        (fun _ => h.deinitInPlaceArgument choice place))

/-- Trusted claim for `Anneal.MirCorrespondenceProof.decodeProg_encodeProg`. -/
def DecodeProgEncodeProgClaim : Prop :=
  ∀ (p : Program), decodeProg (encodeProg p) = some p

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeProg_types_canonical`. -/
def EncodeProgTypesCanonicalClaim : Prop :=
  ∀ (p : Program), typesAreCanonical (encodeProg p).types = true

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeStmt_no_dormant_noops`. -/
def EncodeStmtNoDormantNoopsClaim : Prop :=
  ∀ (ts : List MirTy) (s : StatementKind),
    encodeStmt ts s = .nop ↔ s = .nop

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeRvalue_binaryOp_iff`. -/
def EncodeRvalueBinaryOpIffClaim : Prop :=
  ∀ (ts : List MirTy) (rv : Rvalue) (op : BinOp) (l' r' : RefOperand),
    encodeRvalue ts rv = .binaryOp op l' r' ↔
      ∃ l r : Operand, rv = .binaryOp op l r ∧
        encodeOperand ts l = l' ∧ encodeOperand ts r = r'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeRvalue_unaryOp_iff`. -/
def EncodeRvalueUnaryOpIffClaim : Prop :=
  ∀ (ts : List MirTy) (rv : Rvalue) (op : UnOp) (o' : RefOperand),
    encodeRvalue ts rv = .unaryOp op o' ↔
      ∃ o : Operand, rv = .unaryOp op o ∧ encodeOperand ts o = o'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeStmt_assign_iff`. -/
def EncodeStmtAssignIffClaim : Prop :=
  ∀ (ts : List MirTy) (s : StatementKind) (dst' : RefPlace) (rv' : RefRvalue),
    encodeStmt ts s = .assign dst' rv' ↔
      ∃ (dst : Place) (rv : Rvalue), s = .assign dst rv ∧
        encodePlace ts dst = dst' ∧ encodeRvalue ts rv = rv'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.state_unique_of_simulationInv`. -/
def StateUniqueOfSimulationInvClaim : Prop :=
  ∀ {p : Program} {s₁ s₂ : State} {rs : RefState},
    SimulationInv p s₁ rs → SimulationInv p s₂ rs → s₁ = s₂

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refState_unique_of_simulationInv`. -/
def RefStateUniqueOfSimulationInvClaim : Prop :=
  ∀ {p : Program} {s : State} {rs₁ rs₂ : RefState},
    SimulationInv p s rs₁ → SimulationInv p s rs₂ →
    rs₁.stepsExecuted = rs₂.stepsExecuted →
    rs₁.maxSteps = rs₂.maxSteps →
    rs₁ = rs₂

/-- Trusted claim for `Anneal.MirCorrespondenceProof.initRefState_sim`. -/
def InitRefStateSimClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {q : Query} (maxSteps : Nat),
    decodeProg rp = some p →
    (∀ k, initState p q = .error k → initRefState rp q maxSteps = .error k) ∧
    (∀ s₀, initState p q = .ok s₀ →
      ∃ rs₀, initRefState rp q maxSteps = .ok rs₀ ∧
        SimulationInv p s₀ rs₀ ∧
        rs₀.stepsExecuted = 0 ∧
        rs₀.maxSteps = maxSteps)

/-- Trusted claim for `Anneal.MirCorrespondenceProof.evalRefStep_eq`. -/
def EvalRefStepEqClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s : State} {rs : RefState}
    {rfs : List RefFrameState} {retTy : MirTy},
    decodeProg rp = some p →
    s.frames ≠ [] →
    rs.frames = callerSentinelFrame retTy :: rfs.reverse →
    rs.callerMem = s.callerMem →
    FramesSimInv p s.frames rfs →
    Nat.blt rs.stepsExecuted rs.maxSteps = true →
    ∀ (c : Choice),
      evalRefStep rp c rs =
        stepResultToRefOutcome (callerSentinelFrame retTy) rs.stepsExecuted
          rs.maxSteps (mapStepRes p (evalStep p c s))

/-- Trusted claim for `Anneal.MirCorrespondenceProof.sim_of_refStep`. -/
def SimOfRefStepClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s : State} {rs rs' : RefState},
    decodeProg rp = some p →
    SimulationInv p s rs →
    RefStep rp rs (.running rs') →
    ∃ s' : State, Step p s (.step s') ∧ SimulationInv p s' rs'

/-- Trusted claim for `Anneal.MirCorrespondenceProof.sim_of_refReaches`. -/
def SimOfRefReachesClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s₀ : State} {rs₀ rs : RefState},
    decodeProg rp = some p →
    SimulationInv p s₀ rs₀ →
    RefReaches rp rs₀ rs →
    ∃ s : State, Reaches p s₀ s ∧ SimulationInv p s rs

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refWellFormed_of_wellFormed`. -/
def RefWellFormedOfWellFormedClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q → RefWellFormed (encodeProg p) q

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refBehavior_of_behavior`. -/
def RefBehaviorOfBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    Behavior p q out → RefBehavior (encodeProg p) q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.behavior_of_refBehavior`. -/
def BehaviorOfRefBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    RefBehavior (encodeProg p) q out → Behavior p q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.behavior_iff_refBehavior`. -/
def BehaviorIffRefBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    Behavior p q out ↔ RefBehavior (encodeProg p) q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.diverges_iff_refDiverges`. -/
def DivergesIffRefDivergesClaim : Prop :=
  ∀ (p : Program) (q : Query),
    Diverges p q ↔ RefDiverges (encodeProg p) q

/-! ### Correspondence Canary Programs and Claims (`D6`–`D24`)

`D6`–`D9` are self-consistency canaries of Anneal's deliberately stricter
move-deinitialization rule (see `evalRefMiriOperandToSlot`): `eval_operand` at
`rustc@8144389c` evaluates `Move` like `Copy`, so these canaries check that
$M_{\text{anneal}}$ and $M_{\text{ref}}$ agree on the stricter rule rather than
anchoring either model independently against upstream Miri or MiniRust. -/

/-- `D6` (Use-After-Move UB):
`_2 = move _1; _0 = copy _1; return` deinitializes `_1` on `move _1` and
faults with `.fault .undefined` (`.ub` in $M_{\text{ref}}$) on the subsequent
`copy _1`. -/
noncomputable def progUseAfterMoveD6 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Input query `(42u32)` for canaries `D6`–`D8`. -/
noncomputable def queryU32_42 : Query where
  args := [u32Val 42]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D6_use_after_move_ub`. -/
def CanaryD6UseAfterMoveUbClaim : Prop :=
  ReachesResult progUseAfterMoveD6 queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progUseAfterMoveD6 queryU32_42 (.fault .unsupported) ∧
  ¬ WellFormed progUseAfterMoveD6 queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progUseAfterMoveD6)
    queryU32_42 maxSteps .ub)

/-- `D7a` (`BinaryOp` left-to-right `copy _1` then `move _1` succeeds):
`_0 = BinOp(Add, copy _1, move _1); return` reads `_1` in `lhs`, then reads
and deinitializes `_1` in `rhs`, and returns `84`. -/
noncomputable def progBinOpCopyThenMoveD7a : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7a_binop_copy_then_move_ok`. -/
def CanaryD7aBinopCopyThenMoveOkClaim : Prop :=
  WellFormed progBinOpCopyThenMoveD7a queryU32_42 ∧
  Behavior progBinOpCopyThenMoveD7a queryU32_42
    (.returned ⟨u32Val 84, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progBinOpCopyThenMoveD7a) queryU32_42 ∧
  RefBehavior (encodeProg progBinOpCopyThenMoveD7a) queryU32_42
    (.returned ⟨u32Val 84, ⟨[]⟩⟩)

/-- `D7b` (`BinaryOp` left-to-right `move _1` then `copy _1` faults with UB):
`_0 = BinOp(Add, move _1, copy _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = copy _1`. -/
noncomputable def progBinOpMoveThenCopyD7b : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.move ⟨1, []⟩) (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7b_binop_move_then_copy_ub`. -/
def CanaryD7bBinopMoveThenCopyUbClaim : Prop :=
  ReachesResult progBinOpMoveThenCopyD7b queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progBinOpMoveThenCopyD7b queryU32_42
    (.fault .unsupported) ∧
  ¬ WellFormed progBinOpMoveThenCopyD7b queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progBinOpMoveThenCopyD7b)
    queryU32_42 maxSteps .ub)

/-- `D7c` (`BinaryOp` left-to-right `move _1` then `move _1` faults with UB):
`_0 = BinOp(Add, move _1, move _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = move _1`. -/
noncomputable def progBinOpMoveThenMoveD7c : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.move ⟨1, []⟩) (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7c_binop_move_then_move_ub`. -/
def CanaryD7cBinopMoveThenMoveUbClaim : Prop :=
  ReachesResult progBinOpMoveThenMoveD7c queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progBinOpMoveThenMoveD7c queryU32_42
    (.fault .unsupported) ∧
  ¬ WellFormed progBinOpMoveThenMoveD7c queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progBinOpMoveThenMoveD7c)
    queryU32_42 maxSteps .ub)

/-- `D8` (Self-move `_1 = move _1` preserves initialized value):
`_1 = move _1; _0 = copy _1; return` reads `42` from `_1`, deinitializes `_1`
to `.live .uninit`, and then writes `42` back into `_1`, so the subsequent
`_0 = copy _1` succeeds and returns `42`. -/
noncomputable def progSelfMoveD8 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D8_self_move_ok`. -/
def CanaryD8SelfMoveOkClaim : Prop :=
  WellFormed progSelfMoveD8 queryU32_42 ∧
  Behavior progSelfMoveD8 queryU32_42 (.returned ⟨u32Val 42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progSelfMoveD8) queryU32_42 ∧
  RefBehavior (encodeProg progSelfMoveD8) queryU32_42
    (.returned ⟨u32Val 42, ⟨[]⟩⟩)

/-- `D9` (Move of 0-Byte ZST `MirTy.unit` Remains Initialized):
`_2 = move _1; _0 = copy _1; return` where `_1 : ()` sets `_1` to
`liveUninitSlot .unit = .live .unit`, so subsequent `_0 = copy _1`
succeeds and returns `.unit`. -/
noncomputable def progMoveUnitZstD9 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit, .unit, .unit]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D9_move_unit_zst_ok`. -/
def CanaryD9MoveUnitZstOkClaim : Prop :=
  WellFormed progMoveUnitZstD9 queryEmpty ∧
  Behavior progMoveUnitZstD9 queryEmpty (.returned ⟨.unit, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progMoveUnitZstD9) queryEmpty ∧
  RefBehavior (encodeProg progMoveUnitZstD9) queryEmpty
    (.returned ⟨.unit, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D10_add_unchecked_overflow_ub`. -/
def CanaryD10AddUncheckedOverflowUbClaim : Prop :=
  ReachesResult progAddUncheckedU32 queryU32MaxPlusOne
    (.fault .undefined) ∧
  ¬ WellFormed progAddUncheckedU32 queryU32MaxPlusOne ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progAddUncheckedU32)
    queryU32MaxPlusOne maxSteps .ub) ∧
  Behavior progAddU32 queryU32MaxPlusOne (.returned ⟨u32Val 0, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg progAddU32) queryU32MaxPlusOne
    (.returned ⟨u32Val 0, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D11_enum_discriminant_and_const_ok`:
exercises explicit-repr `#[repr(u8)]` non-index enum constant tag decoding +
`u8` `Rvalue.discriminant` and signed `i8` -> `isize` tag sign-extension in
both $M_{\text{anneal}}$ and $M_{\text{ref}}$ (`Miri.Interpreter.Discriminant`).
-/
def CanaryD11EnumDiscriminantAndConstOkClaim : Prop :=
  WellFormed progEnumExplicitReprU8 queryEmpty ∧
  Behavior progEnumExplicitReprU8 queryEmpty
    (.returned ⟨u8Val 20, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progEnumExplicitReprU8) queryEmpty ∧
  RefBehavior (encodeProg progEnumExplicitReprU8) queryEmpty
    (.returned ⟨u8Val 20, ⟨[]⟩⟩) ∧
  WellFormed progEnumSignedTagIsize queryEmpty ∧
  Behavior progEnumSignedTagIsize queryEmpty
    (.returned ⟨scalarNatVal .isize true (Nat.pow 2 64 - 1), ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progEnumSignedTagIsize) queryEmpty ∧
  RefBehavior (encodeProg progEnumSignedTagIsize) queryEmpty
    (.returned ⟨scalarNatVal .isize true (Nat.pow 2 64 - 1), ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D12_zst_enum_move_and_discr_ok`:
exercises 1-variant inhabited ZST enum implicit return, non-deinitializing
`Operand.move`, `ConstLit.zeroSized`, and `Variants.Single 0`
`Rvalue.discriminant` in both $M_{\text{anneal}}$ and $M_{\text{ref}}$. -/
def CanaryD12ZstEnumMoveAndDiscrOkClaim : Prop :=
  WellFormed progZstSingleEnumImplicitRet queryEmpty ∧
  Behavior progZstSingleEnumImplicitRet queryEmpty
    (.returned ⟨.enumVal canarySingleZstEnumTy 0 [], ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progZstSingleEnumImplicitRet) queryEmpty ∧
  RefBehavior (encodeProg progZstSingleEnumImplicitRet) queryEmpty
    (.returned ⟨.enumVal canarySingleZstEnumTy 0 [], ⟨[]⟩⟩) ∧
  WellFormed progZstSingleEnumMoveAndDiscr queryEmpty ∧
  Behavior progZstSingleEnumMoveAndDiscr queryEmpty
    (.returned ⟨scalarNatVal .isize true 42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progZstSingleEnumMoveAndDiscr) queryEmpty ∧
  RefBehavior (encodeProg progZstSingleEnumMoveAndDiscr) queryEmpty
    (.returned ⟨scalarNatVal .isize true 42, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D13_enum_invalid_tag_and_uninit_ub`:
exercises invalid constant scalar tag `1` on `ReprU8 { A = 10, B = 20 }` and
reading `Rvalue.discriminant` from an uninitialized scalar-tagged enum local,
both faulting with `.undefined` / `.ub` in $M_{\text{anneal}}$ and
$M_{\text{ref}}$. -/
def CanaryD13EnumInvalidTagAndUninitUbClaim : Prop :=
  ReachesResult progEnumInvalidTagConstUb queryEmpty (.fault .undefined) ∧
  ¬ ReachesResult progEnumInvalidTagConstUb queryEmpty (.fault .unsupported) ∧
  ¬ WellFormed progEnumInvalidTagConstUb queryEmpty ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progEnumInvalidTagConstUb)
    queryEmpty maxSteps .ub) ∧
  ReachesResult progEnumUninitDiscrUb queryEmpty (.fault .undefined) ∧
  ¬ ReachesResult progEnumUninitDiscrUb queryEmpty (.fault .unsupported) ∧
  ¬ WellFormed progEnumUninitDiscrUb queryEmpty ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progEnumUninitDiscrUb)
    queryEmpty maxSteps .ub)

/-- `usize` type descriptor on 64-bit targets (`IntWidth.isize`, unsigned). -/
noncomputable def usizeTy : MirTy := .int .isize false

/-- Construct a `usize` scalar `Val` from `n : Nat`. -/
noncomputable def usizeVal (n : Nat) : Val := scalarNatVal .isize false n

/-- Type descriptor of the pair `(usize, bool)` that an overflowing `usize`
operator returns. -/
noncomputable def usizeBoolPairTy : MirTy := .tuple [usizeTy, .bool]

/-- `D14` (overflowing operator, sequential tuple field moves, and tuple
aggregate), shaped like the checked addition in
`fuchsia_merkle_core::div_ceil_usize`:
`_3 = op(copy _1, copy _2); _4 = move (_3.1: bool); _5 = move (_3.0: usize);
_0 = (move _5, move _4); return`.

`op` is `.addWithOverflow`, `.subWithOverflow`, or `.mulWithOverflow`, so `_3`
holds the pair `(wrapped, overflowed)`. Moving `_3.1` deinitializes only that
field, so the following move of `_3.0` still succeeds. The aggregate rebuilds
the pair from the two moved fields. -/
noncomputable def progOverflowTupleD14 (op : BinOp) : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [usizeBoolPairTy, usizeTy, usizeTy, usizeBoolPairTy, .bool,
      usizeTy]
    basicBlocks := [{
      statements := [
        .assign ⟨3, []⟩ (.binaryOp op (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)),
        .assign ⟨4, []⟩ (.use (.move ⟨3, [.field 1 .bool]⟩)),
        .assign ⟨5, []⟩ (.use (.move ⟨3, [.field 0 usizeTy]⟩)),
        .assign ⟨0, []⟩ (.aggregateTuple [.move ⟨5, []⟩, .move ⟨4, []⟩])
      ]
      terminator := .return_
    }]
  }]

/-- `D14` (field write after field move):
`_2 = AddWithOverflow(copy _1, copy _1); _3 = move (_2.1: bool);
(_2.1: bool) = const true; _0 = move _2; return`.

The move deinitializes only `_2.1`, and the field write initializes it again
without touching `_2.0`, so the final whole-tuple move (which requires every
field to be initialized) succeeds. -/
noncomputable def progTupleFieldWriteD14 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [usizeBoolPairTy, usizeTy, usizeBoolPairTy, .bool]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩
          (.binaryOp .addWithOverflow (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)),
        .assign ⟨3, []⟩ (.use (.move ⟨2, [.field 1 .bool]⟩)),
        .assign ⟨2, [.field 1 .bool]⟩
          (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.use (.move ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D14` (use of a moved-out tuple field is UB):
`_2 = AddWithOverflow(copy _1, copy _1); _3 = move (_2.1: bool);
_0 = copy (_2.1: bool); return` reads `_2.1` after the move deinitialized it
and faults with `.fault .undefined` (`.ub` in $M_{\text{ref}}$). -/
noncomputable def progTupleFieldUseAfterMoveD14 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.bool, usizeTy, usizeBoolPairTy, .bool]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩
          (.binaryOp .addWithOverflow (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)),
        .assign ⟨3, []⟩ (.use (.move ⟨2, [.field 1 .bool]⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, [.field 1 .bool]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D14_overflow_tuple_field_moves`:
exercises `BinOp.addWithOverflow`, `BinOp.subWithOverflow`, and
`BinOp.mulWithOverflow` on `usize` (with and without overflow), sequential
moves of single tuple fields, a tuple aggregate, a field write, and the UB of
reading a moved-out field, in both $M_{\text{anneal}}$ and $M_{\text{ref}}$
(`Miri.Interpreter.IntegerOps.binary`).

- `usize::MAX + 1` wraps to `0` and overflows.
- `0 - 1` wraps to `usize::MAX` and overflows.
- `2^63 * 2` wraps to `0` and overflows.
- `30 + 12 = 42` does not overflow.
- `21 + 21 = 42` with the overflow field moved out and rewritten to `true`. -/
def CanaryD14OverflowTupleFieldMovesClaim : Prop :=
  WellFormed (progOverflowTupleD14 .addWithOverflow)
    { args := [usizeVal (Nat.pow 2 64 - 1), usizeVal 1] } ∧
  Behavior (progOverflowTupleD14 .addWithOverflow)
    { args := [usizeVal (Nat.pow 2 64 - 1), usizeVal 1] }
    (.returned ⟨.tuple [usizeVal 0, .bool true], ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (progOverflowTupleD14 .addWithOverflow))
    { args := [usizeVal (Nat.pow 2 64 - 1), usizeVal 1] } ∧
  RefBehavior (encodeProg (progOverflowTupleD14 .addWithOverflow))
    { args := [usizeVal (Nat.pow 2 64 - 1), usizeVal 1] }
    (.returned ⟨.tuple [usizeVal 0, .bool true], ⟨[]⟩⟩) ∧
  WellFormed (progOverflowTupleD14 .subWithOverflow)
    { args := [usizeVal 0, usizeVal 1] } ∧
  Behavior (progOverflowTupleD14 .subWithOverflow)
    { args := [usizeVal 0, usizeVal 1] }
    (.returned
      ⟨.tuple [usizeVal (Nat.pow 2 64 - 1), .bool true], ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (progOverflowTupleD14 .subWithOverflow))
    { args := [usizeVal 0, usizeVal 1] } ∧
  RefBehavior (encodeProg (progOverflowTupleD14 .subWithOverflow))
    { args := [usizeVal 0, usizeVal 1] }
    (.returned
      ⟨.tuple [usizeVal (Nat.pow 2 64 - 1), .bool true], ⟨[]⟩⟩) ∧
  WellFormed (progOverflowTupleD14 .mulWithOverflow)
    { args := [usizeVal (Nat.pow 2 63), usizeVal 2] } ∧
  Behavior (progOverflowTupleD14 .mulWithOverflow)
    { args := [usizeVal (Nat.pow 2 63), usizeVal 2] }
    (.returned ⟨.tuple [usizeVal 0, .bool true], ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (progOverflowTupleD14 .mulWithOverflow))
    { args := [usizeVal (Nat.pow 2 63), usizeVal 2] } ∧
  RefBehavior (encodeProg (progOverflowTupleD14 .mulWithOverflow))
    { args := [usizeVal (Nat.pow 2 63), usizeVal 2] }
    (.returned ⟨.tuple [usizeVal 0, .bool true], ⟨[]⟩⟩) ∧
  WellFormed (progOverflowTupleD14 .addWithOverflow)
    { args := [usizeVal 30, usizeVal 12] } ∧
  Behavior (progOverflowTupleD14 .addWithOverflow)
    { args := [usizeVal 30, usizeVal 12] }
    (.returned ⟨.tuple [usizeVal 42, .bool false], ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (progOverflowTupleD14 .addWithOverflow))
    { args := [usizeVal 30, usizeVal 12] } ∧
  RefBehavior (encodeProg (progOverflowTupleD14 .addWithOverflow))
    { args := [usizeVal 30, usizeVal 12] }
    (.returned ⟨.tuple [usizeVal 42, .bool false], ⟨[]⟩⟩) ∧
  WellFormed progTupleFieldWriteD14 { args := [usizeVal 21] } ∧
  Behavior progTupleFieldWriteD14 { args := [usizeVal 21] }
    (.returned ⟨.tuple [usizeVal 42, .bool true], ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progTupleFieldWriteD14)
    { args := [usizeVal 21] } ∧
  RefBehavior (encodeProg progTupleFieldWriteD14) { args := [usizeVal 21] }
    (.returned ⟨.tuple [usizeVal 42, .bool true], ⟨[]⟩⟩) ∧
  ReachesResult progTupleFieldUseAfterMoveD14 { args := [usizeVal 21] }
    (.fault .undefined) ∧
  ¬ ReachesResult progTupleFieldUseAfterMoveD14 { args := [usizeVal 21] }
    (.fault .unsupported) ∧
  ¬ WellFormed progTupleFieldUseAfterMoveD14 { args := [usizeVal 21] } ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progTupleFieldUseAfterMoveD14)
    { args := [usizeVal 21] } maxSteps .ub)

/-- Single-block cast test program:
`fn cast(a: srcTy) -> dstTy { _0 = copy _1 as dstTy (kind); return }` -/
noncomputable def mkCastProg (kind : CastKind) (srcTy dstTy : MirTy) :
    Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [dstTy, srcTy]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.cast kind (.copy ⟨1, []⟩) dstTy)
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D15_int_to_int_cast`: exercises
`CastKind.intToInt` in both $M_{\text{anneal}}$ and $M_{\text{ref}}$
(`Miri.Interpreter.IntegerCast.cast`).

- Signed widening sign-extends: `-1i8 as i64 = -1i64` (bits `2^64 - 1`).
- Cross-signedness widening: `-1i8 as u64 = u64::MAX` and `255u8 as i64 = 255`.
- Unsigned widening zero-extends: `255u8 as u64 = 255u64`.
- Narrowing truncates: `300u64 as u8 = 44u8`.
- `true as u64 = 1u64`.
- `u8 as bool` and `CastKind.unsupported` fault with `.fault .unsupported`
  (`.blocked` in $M_{\text{ref}}$). -/
def CanaryD15IntToIntCastClaim : Prop :=
  WellFormed (mkCastProg .intToInt i8Ty (.int .i64 true))
    { args := [i8Val 255] } ∧
  Behavior (mkCastProg .intToInt i8Ty (.int .i64 true))
    { args := [i8Val 255] }
    (.returned ⟨scalarNatVal .i64 true (Nat.pow 2 64 - 1), ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkCastProg .intToInt i8Ty (.int .i64 true)))
    { args := [i8Val 255] } ∧
  RefBehavior (encodeProg (mkCastProg .intToInt i8Ty (.int .i64 true)))
    { args := [i8Val 255] }
    (.returned ⟨scalarNatVal .i64 true (Nat.pow 2 64 - 1), ⟨[]⟩⟩) ∧
  WellFormed (mkCastProg .intToInt i8Ty (.int .i64 false))
    { args := [i8Val 255] } ∧
  Behavior (mkCastProg .intToInt i8Ty (.int .i64 false))
    { args := [i8Val 255] }
    (.returned ⟨scalarNatVal .i64 false (Nat.pow 2 64 - 1), ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkCastProg .intToInt i8Ty (.int .i64 false)))
    { args := [i8Val 255] } ∧
  RefBehavior (encodeProg (mkCastProg .intToInt i8Ty (.int .i64 false)))
    { args := [i8Val 255] }
    (.returned ⟨scalarNatVal .i64 false (Nat.pow 2 64 - 1), ⟨[]⟩⟩) ∧
  WellFormed (mkCastProg .intToInt u8Ty (.int .i64 true))
    { args := [u8Val 255] } ∧
  Behavior (mkCastProg .intToInt u8Ty (.int .i64 true))
    { args := [u8Val 255] }
    (.returned ⟨scalarNatVal .i64 true 255, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkCastProg .intToInt u8Ty (.int .i64 true)))
    { args := [u8Val 255] } ∧
  RefBehavior (encodeProg (mkCastProg .intToInt u8Ty (.int .i64 true)))
    { args := [u8Val 255] }
    (.returned ⟨scalarNatVal .i64 true 255, ⟨[]⟩⟩) ∧
  WellFormed (mkCastProg .intToInt u8Ty (.int .i64 false))
    { args := [u8Val 255] } ∧
  Behavior (mkCastProg .intToInt u8Ty (.int .i64 false))
    { args := [u8Val 255] }
    (.returned ⟨scalarNatVal .i64 false 255, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkCastProg .intToInt u8Ty (.int .i64 false)))
    { args := [u8Val 255] } ∧
  RefBehavior (encodeProg (mkCastProg .intToInt u8Ty (.int .i64 false)))
    { args := [u8Val 255] }
    (.returned ⟨scalarNatVal .i64 false 255, ⟨[]⟩⟩) ∧
  WellFormed (mkCastProg .intToInt (.int .i64 false) u8Ty)
    { args := [scalarNatVal .i64 false 300] } ∧
  Behavior (mkCastProg .intToInt (.int .i64 false) u8Ty)
    { args := [scalarNatVal .i64 false 300] }
    (.returned ⟨u8Val 44, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkCastProg .intToInt (.int .i64 false) u8Ty))
    { args := [scalarNatVal .i64 false 300] } ∧
  RefBehavior (encodeProg (mkCastProg .intToInt (.int .i64 false) u8Ty))
    { args := [scalarNatVal .i64 false 300] }
    (.returned ⟨u8Val 44, ⟨[]⟩⟩) ∧
  WellFormed (mkCastProg .intToInt .bool (.int .i64 false))
    { args := [.bool true] } ∧
  Behavior (mkCastProg .intToInt .bool (.int .i64 false))
    { args := [.bool true] }
    (.returned ⟨scalarNatVal .i64 false 1, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkCastProg .intToInt .bool (.int .i64 false)))
    { args := [.bool true] } ∧
  RefBehavior (encodeProg (mkCastProg .intToInt .bool (.int .i64 false)))
    { args := [.bool true] }
    (.returned ⟨scalarNatVal .i64 false 1, ⟨[]⟩⟩) ∧
  ReachesResult (mkCastProg .intToInt u8Ty .bool)
    { args := [u8Val 1] } (.fault .unsupported) ∧
  ¬ ReachesResult (mkCastProg .intToInt u8Ty .bool)
    { args := [u8Val 1] } (.fault .undefined) ∧
  ¬ WellFormed (mkCastProg .intToInt u8Ty .bool)
    { args := [u8Val 1] } ∧
  (∃ maxSteps,
    RefReachesOutcome
      (encodeProg (mkCastProg .intToInt u8Ty .bool))
      { args := [u8Val 1] } maxSteps .blocked) ∧
  ReachesResult (mkCastProg .unsupported u8Ty (.int .i64 false))
    { args := [u8Val 255] } (.fault .unsupported) ∧
  ¬ ReachesResult (mkCastProg .unsupported u8Ty (.int .i64 false))
    { args := [u8Val 255] } (.fault .undefined) ∧
  ¬ WellFormed (mkCastProg .unsupported u8Ty (.int .i64 false))
    { args := [u8Val 255] } ∧
  (∃ maxSteps,
    RefReachesOutcome
      (encodeProg (mkCastProg .unsupported u8Ty (.int .i64 false)))
      { args := [u8Val 255] } maxSteps .blocked)

/-- Checked `usize` increment, shaped like the overflow check that `rustc`
emits for `a + 1` (and like the one in
`fuchsia_merkle_core::div_ceil_usize`):

- `bb0`: `_2 = AddWithOverflow(copy _1, const 1_usize);
  assert(!move (_2.1: bool), msg) -> [success: bb1, unwind]`
- `bb1`: `_0 = move (_2.0: usize); return`
- `bb2` (a cleanup block iff `resumeInCleanup`): `nop; resume`

The assertion passes when the addition does not overflow (`_2.1 = false`).
`msg` is the assert message, `unwind` is the unwind action of a failing
assertion, and `bb2` is the cleanup target used by canary `D18`. -/
noncomputable def mkCheckedIncProg (msg : AssertKind) (unwind : UnwindAction)
    (resumeInCleanup : Bool) : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [usizeTy, usizeTy, usizeBoolPairTy]
    basicBlocks := [
      {
        statements := [
          .assign ⟨2, []⟩
            (.binaryOp .addWithOverflow (.copy ⟨1, []⟩)
              (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator :=
          .assert (.move ⟨2, [.field 1 .bool]⟩) false msg 1 unwind
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.move ⟨2, [.field 0 usizeTy]⟩))
        ]
        terminator := .return_
      },
      {
        statements := [.nop]
        terminator := .unwindResume
        cleanup := resumeInCleanup
      }
    ]
  }]

/-- Input query `(usize::MAX)`, on which the checked increment overflows. -/
noncomputable def queryUsizeMax : Query where
  args := [usizeVal (Nat.pow 2 64 - 1)]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D16_assert_pass_and_unwind_ok`:
exercises `TerminatorKind.assert` in both $M_{\text{anneal}}$ and
$M_{\text{ref}}$ (`Miri.Interpreter.ControlFlow.evalTerminator`).

- A passing assertion jumps to its target: `41 + 1` returns `42`.
- A failing assertion with `unwind continue` panics and unwinds out of the
  entry function: `usize::MAX + 1` ends with `.unwound`. This execution is
  well-formed: a panic is not Undefined Behavior. -/
def CanaryD16AssertPassAndUnwindContinueClaim : Prop :=
  WellFormed (mkCheckedIncProg (.overflow .add) .continue_ true)
    { args := [usizeVal 41] } ∧
  Behavior (mkCheckedIncProg (.overflow .add) .continue_ true)
    { args := [usizeVal 41] } (.returned ⟨usizeVal 42, ⟨[]⟩⟩) ∧
  RefWellFormed
    (encodeProg (mkCheckedIncProg (.overflow .add) .continue_ true))
    { args := [usizeVal 41] } ∧
  RefBehavior
    (encodeProg (mkCheckedIncProg (.overflow .add) .continue_ true))
    { args := [usizeVal 41] } (.returned ⟨usizeVal 42, ⟨[]⟩⟩) ∧
  WellFormed (mkCheckedIncProg (.overflow .add) .continue_ true)
    queryUsizeMax ∧
  Behavior (mkCheckedIncProg (.overflow .add) .continue_ true)
    queryUsizeMax (.unwound ⟨[]⟩) ∧
  RefWellFormed
    (encodeProg (mkCheckedIncProg (.overflow .add) .continue_ true))
    queryUsizeMax ∧
  RefBehavior
    (encodeProg (mkCheckedIncProg (.overflow .add) .continue_ true))
    queryUsizeMax (.unwound ⟨[]⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D17_assert_unwind_unreachable_ub`:
exercises the fault poles of a failing `TerminatorKind.assert` in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$.

- `unwind unreachable`: unwinding out of a frame that does not allow it is
  Undefined Behavior (`.fault .undefined`, `.ub` in $M_{\text{ref}}$;
  `Miri.Interpreter.ControlFlow.unwindToBlock`).
- A message that carries operands (`AssertKind.boundsCheck`) is unmodeled
  (`.fault .unsupported`, `.blocked` in $M_{\text{ref}}$).
- `unwind terminate` is unmodeled (`.fault .unsupported`, `.blocked` in
  $M_{\text{ref}}$). -/
def CanaryD17AssertUnwindUnreachableUbClaim : Prop :=
  ReachesResult (mkCheckedIncProg (.overflow .add) .unreachable true)
    queryUsizeMax (.fault .undefined) ∧
  ¬ ReachesResult (mkCheckedIncProg (.overflow .add) .unreachable true)
    queryUsizeMax (.fault .unsupported) ∧
  ¬ WellFormed (mkCheckedIncProg (.overflow .add) .unreachable true)
    queryUsizeMax ∧
  (∃ maxSteps,
    RefReachesOutcome
      (encodeProg (mkCheckedIncProg (.overflow .add) .unreachable true))
      queryUsizeMax maxSteps .ub) ∧
  ReachesResult (mkCheckedIncProg .boundsCheck .continue_ true)
    queryUsizeMax (.fault .unsupported) ∧
  ¬ ReachesResult (mkCheckedIncProg .boundsCheck .continue_ true)
    queryUsizeMax (.fault .undefined) ∧
  ¬ WellFormed (mkCheckedIncProg .boundsCheck .continue_ true)
    queryUsizeMax ∧
  (∃ maxSteps,
    RefReachesOutcome
      (encodeProg (mkCheckedIncProg .boundsCheck .continue_ true))
      queryUsizeMax maxSteps .blocked) ∧
  ReachesResult (mkCheckedIncProg (.overflow .add) .terminate true)
    queryUsizeMax (.fault .unsupported) ∧
  ¬ ReachesResult (mkCheckedIncProg (.overflow .add) .terminate true)
    queryUsizeMax (.fault .undefined) ∧
  ¬ WellFormed (mkCheckedIncProg (.overflow .add) .terminate true)
    queryUsizeMax ∧
  (∃ maxSteps,
    RefReachesOutcome
      (encodeProg (mkCheckedIncProg (.overflow .add) .terminate true))
      queryUsizeMax maxSteps .blocked)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D18_assert_cleanup_and_resume`:
exercises a failing `TerminatorKind.assert` with `unwind cleanup bb2` and
`TerminatorKind.unwindResume` in both $M_{\text{anneal}}$ and $M_{\text{ref}}$
(`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`).

- When `bb2` is a cleanup block, the failing assertion jumps to it, the block
  runs, and `resume` unwinds out of the entry function (`.unwound`).
- When `bb2` is not a cleanup block, `resume` is unmodeled
  (`.fault .unsupported`, `.blocked` in $M_{\text{ref}}$): unwinding returns
  only from cleanup blocks. -/
def CanaryD18AssertCleanupAndUnwindResumeClaim : Prop :=
  WellFormed (mkCheckedIncProg (.overflow .add) (.cleanup 2) true)
    queryUsizeMax ∧
  Behavior (mkCheckedIncProg (.overflow .add) (.cleanup 2) true)
    queryUsizeMax (.unwound ⟨[]⟩) ∧
  RefWellFormed
    (encodeProg (mkCheckedIncProg (.overflow .add) (.cleanup 2) true))
    queryUsizeMax ∧
  RefBehavior
    (encodeProg (mkCheckedIncProg (.overflow .add) (.cleanup 2) true))
    queryUsizeMax (.unwound ⟨[]⟩) ∧
  ReachesResult (mkCheckedIncProg (.overflow .add) (.cleanup 2) false)
    queryUsizeMax (.fault .unsupported) ∧
  ¬ ReachesResult (mkCheckedIncProg (.overflow .add) (.cleanup 2) false)
    queryUsizeMax (.fault .undefined) ∧
  ¬ WellFormed (mkCheckedIncProg (.overflow .add) (.cleanup 2) false)
    queryUsizeMax ∧
  (∃ maxSteps,
    RefReachesOutcome
      (encodeProg (mkCheckedIncProg (.overflow .add) (.cleanup 2) false))
      queryUsizeMax maxSteps .blocked)

/-- `D19` (destination-overlapping tuple aggregate):
`_1 : (u32, u32) = (10, 20); _1 = (const 99u32, copy (_1.0)); _0 = move _1;
return`. Because operand `1` aliases `dst = _1`, both $M_{\text{anneal}}$ and
$M_{\text{ref}}$ fail closed with `.fault .unsupported` (`.blocked`), avoiding
divergent evaluation order and `rust-lang/rust#68364` overlap UB. -/
noncomputable def progTupleAggregateAliasD19 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.tuple [u32Ty, u32Ty], .tuple [u32Ty, u32Ty]]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.aggregateTuple [
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩,
          .copy ⟨1, [.field 0 u32Ty]⟩
        ]),
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D19` (self-field tuple aggregate):
`_1 : ((u32, u32, u32), u32); _1 = (copy (_1.0), const 5u32); _0 = move _1;
return`. Fails closed with `.fault .unsupported` (`.blocked`) rather than
hiding `BackendRepr::Memory` `copyRangesOverlap` UB. -/
noncomputable def progTupleAggregateSelfFieldD19 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [
      .tuple [.tuple [u32Ty, u32Ty, u32Ty], u32Ty],
      .tuple [.tuple [u32Ty, u32Ty, u32Ty], u32Ty]
    ]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.aggregateTuple [
          .copy ⟨1, [.field 0 (.tuple [u32Ty, u32Ty, u32Ty])]⟩,
          .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩
        ]),
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D19` (non-ZST tuple self-copy / self-move):
`_1 : (u32, u32, u32); _1 = copy/move _1; _0 = move _1; return`. Fails closed
with `.fault .unsupported` (`.blocked`) rather than proving `WellFormed` on
in-memory `overlapping copy_nonoverlapping` UB. -/
noncomputable def progTupleSelfUseD19 (isMove : Bool) : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.tuple [u32Ty, u32Ty, u32Ty], .tuple [u32Ty, u32Ty, u32Ty]]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩
          (.use (if isMove then .move ⟨1, []⟩ else .copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D19` (nested tuple subfield self-copy):
`_1 : ((u32, u32, u32), u32); _1.0 = copy (_1.0); _0 = move _1; return`. Fails
closed with `.fault .unsupported` (`.blocked`). -/
noncomputable def progTupleSubfieldSelfCopyD19 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [
      .tuple [.tuple [u32Ty, u32Ty, u32Ty], u32Ty],
      .tuple [.tuple [u32Ty, u32Ty, u32Ty], u32Ty]
    ]
    basicBlocks := [{
      statements := [
        .assign ⟨1, [.field 0 (.tuple [u32Ty, u32Ty, u32Ty])]⟩
          (.use (.copy ⟨1, [.field 0 (.tuple [u32Ty, u32Ty, u32Ty])]⟩)),
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D19` (positive control: disjoint sibling field copy and empty unit tuple
aggregate): `_1 : (u32, u32); _2 : () = (); _1.0 = copy (_1.1); _0 = move _1;
return`. Disjoint sibling fields and unit aggregates remain admitted and
return `(20, 20)`. -/
noncomputable def progTupleDisjointFieldAndUnitAggD19 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.tuple [u32Ty, u32Ty], .tuple [u32Ty, u32Ty], .unit]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.aggregateTuple []),
        .assign ⟨1, [.field 0 u32Ty]⟩ (.use (.copy ⟨1, [.field 1 u32Ty]⟩)),
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D19_tuple_overlap_fail_closed`:
verifies that both $M_{\text{anneal}}$ and $M_{\text{ref}}$
(`Miri.Interpreter.writeAggregate` + `refAssignHasUnsupportedOverlap`) fail
closed (`.fault .unsupported` / `.blocked`) on destination-overlapping tuple
aggregates and tuple self-copy/self-move (at whole-local and nested-field
granularity), while admitting disjoint sibling-field copies and empty `.unit`
aggregates. -/
def CanaryD19TupleOverlapFailClosedClaim : Prop :=
  let qPair : Query := { args := [.tuple [u32Val 10, u32Val 20]] }
  let qTriple : Query := { args := [.tuple [u32Val 1, u32Val 2, u32Val 3]] }
  let qNested : Query :=
    { args := [.tuple [.tuple [u32Val 1, u32Val 2, u32Val 3], u32Val 4]] }
  ReachesResult progTupleAggregateAliasD19 qPair (.fault .unsupported) ∧
  ¬ ReachesResult progTupleAggregateAliasD19 qPair (.fault .undefined) ∧
  ¬ WellFormed progTupleAggregateAliasD19 qPair ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progTupleAggregateAliasD19)
    qPair maxSteps .blocked) ∧
  ReachesResult progTupleAggregateSelfFieldD19 qNested (.fault .unsupported) ∧
  ¬ ReachesResult progTupleAggregateSelfFieldD19 qNested (.fault .undefined) ∧
  ¬ WellFormed progTupleAggregateSelfFieldD19 qNested ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progTupleAggregateSelfFieldD19)
    qNested maxSteps .blocked) ∧
  ReachesResult (progTupleSelfUseD19 false) qTriple (.fault .unsupported) ∧
  ¬ ReachesResult (progTupleSelfUseD19 false) qTriple (.fault .undefined) ∧
  ¬ WellFormed (progTupleSelfUseD19 false) qTriple ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg (progTupleSelfUseD19 false))
    qTriple maxSteps .blocked) ∧
  ReachesResult (progTupleSelfUseD19 true) qTriple (.fault .unsupported) ∧
  ¬ ReachesResult (progTupleSelfUseD19 true) qTriple (.fault .undefined) ∧
  ¬ WellFormed (progTupleSelfUseD19 true) qTriple ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg (progTupleSelfUseD19 true))
    qTriple maxSteps .blocked) ∧
  ReachesResult progTupleSubfieldSelfCopyD19 qNested (.fault .unsupported) ∧
  ¬ ReachesResult progTupleSubfieldSelfCopyD19 qNested (.fault .undefined) ∧
  ¬ WellFormed progTupleSubfieldSelfCopyD19 qNested ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progTupleSubfieldSelfCopyD19)
    qNested maxSteps .blocked) ∧
  WellFormed progTupleDisjointFieldAndUnitAggD19 qPair ∧
  Behavior progTupleDisjointFieldAndUnitAggD19 qPair
    (.returned ⟨.tuple [u32Val 20, u32Val 20], ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progTupleDisjointFieldAndUnitAggD19) qPair ∧
  RefBehavior (encodeProg progTupleDisjointFieldAndUnitAggD19) qPair
    (.returned ⟨.tuple [u32Val 20, u32Val 20], ⟨[]⟩⟩)

/-- `D20` (direct crate-local call and return):
Body `0` (`fn(a: u32) -> u32`) calls body `1` (`fn(x: u32, y: u32) -> u32`)
with `[move _1, const 10u32]`, stores the result in `_2`, and returns `_2`.
Body `1` computes `_0 = copy _1 + copy _2; return`. -/
noncomputable def progDirectCallD20 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 1
      locals := [u32Ty, u32Ty, u32Ty]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1
            [.move ⟨1, []⟩, .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩]
            ⟨2, []⟩ (some 1) .continue_
        },
        {
          statements := [.assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
          terminator := .return_
        }
      ]
    },
    {
      argumentCount := 2
      locals := [u32Ty, u32Ty, u32Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator := .return_
      }]
    }
  ]

/-- `D20` (left-to-right move deinitialization across call arguments):
Body `0` calls body `1` with `[move _1, copy _1]`. Argument `0` deinitializes
`_1`, so argument `1` (`copy _1`) faults with `.undefined` / `.ub` during
argument validation in both $M_{\text{anneal}}$ and $M_{\text{ref}}$. -/
noncomputable def progCallUseAfterMoveArgD20 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 1
      locals := [u32Ty, u32Ty]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [.move ⟨1, []⟩, .copy ⟨1, []⟩]
            ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    },
    {
      argumentCount := 2
      locals := [u32Ty, u32Ty, u32Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator := .return_
      }]
    }
  ]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D20_direct_call_and_return`: exercises
direct crate-local `TerminatorKind.call` argument evaluation, move
deinitialization, callee frame push/return, and caller destination writeback in
both $M_{\text{anneal}}$ and $M_{\text{ref}}$
(`Miri.Interpreter.Call.evalCallTerminator`). -/
def CanaryD20DirectCallAndReturnClaim : Prop :=
  let q32 : Query := { args := [u32Val 32] }
  WellFormed progDirectCallD20 q32 ∧
  Behavior progDirectCallD20 q32 (.returned ⟨u32Val 42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progDirectCallD20) q32 ∧
  RefBehavior (encodeProg progDirectCallD20) q32 (.returned ⟨u32Val 42, ⟨[]⟩⟩) ∧
  ReachesResult progCallUseAfterMoveArgD20 q32 (.fault .undefined) ∧
  ¬ ReachesResult progCallUseAfterMoveArgD20 q32 (.fault .unsupported) ∧
  ¬ WellFormed progCallUseAfterMoveArgD20 q32 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progCallUseAfterMoveArgD20)
    q32 maxSteps .ub)

/-- `D21` (multi-frame call and unwind propagation):
Body `0` calls body `1` with unwind action `callerUnwind`, while body `1` runs
a checked `usize` increment (`usize::MAX + 1`) that panics into its own cleanup
block (`bb2: nop; unwindResume`) and unwinds back into body `0`. -/
noncomputable def mkMultiFrameUnwindProgD21 (callerUnwind : UnwindAction) :
    Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 1
      locals := [usizeTy, usizeTy]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) callerUnwind
        },
        {
          statements := []
          terminator := .return_
        },
        {
          statements := [.nop]
          terminator := .unwindResume
          cleanup := true
        }
      ]
    },
    {
      argumentCount := 1
      locals := [usizeTy, usizeTy, usizeBoolPairTy]
      basicBlocks := [
        {
          statements := [
            .assign ⟨2, []⟩
              (.binaryOp .addWithOverflow (.copy ⟨1, []⟩)
                (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 1)⟩))
          ]
          terminator := .assert (.move ⟨2, [.field 1 .bool]⟩) false
            (.overflow .add) 1 (.cleanup 2)
        },
        {
          statements := [
            .assign ⟨0, []⟩ (.use (.move ⟨2, [.field 0 usizeTy]⟩))
          ]
          terminator := .return_
        },
        {
          statements := [.nop]
          terminator := .unwindResume
          cleanup := true
        }
      ]
    }
  ]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D21_multi_frame_unwind`: exercises
multi-frame panic unwind propagation from callee cleanup through caller cleanup
(`.cleanup 2`), directly through caller (`.continue_`), and into UB at a
non-unwinding call boundary (`.unreachable`) in both $M_{\text{anneal}}$ and
$M_{\text{ref}}$. -/
def CanaryD21MultiFrameUnwindClaim : Prop :=
  WellFormed (mkMultiFrameUnwindProgD21 (.cleanup 2)) queryUsizeMax ∧
  Behavior (mkMultiFrameUnwindProgD21 (.cleanup 2)) queryUsizeMax
    (.unwound ⟨[]⟩) ∧
  RefWellFormed (encodeProg (mkMultiFrameUnwindProgD21 (.cleanup 2)))
    queryUsizeMax ∧
  RefBehavior (encodeProg (mkMultiFrameUnwindProgD21 (.cleanup 2)))
    queryUsizeMax (.unwound ⟨[]⟩) ∧
  WellFormed (mkMultiFrameUnwindProgD21 .continue_) queryUsizeMax ∧
  Behavior (mkMultiFrameUnwindProgD21 .continue_) queryUsizeMax
    (.unwound ⟨[]⟩) ∧
  RefWellFormed (encodeProg (mkMultiFrameUnwindProgD21 .continue_))
    queryUsizeMax ∧
  RefBehavior (encodeProg (mkMultiFrameUnwindProgD21 .continue_))
    queryUsizeMax (.unwound ⟨[]⟩) ∧
  ReachesResult (mkMultiFrameUnwindProgD21 .unreachable) queryUsizeMax
    (.fault .undefined) ∧
  ¬ ReachesResult (mkMultiFrameUnwindProgD21 .unreachable) queryUsizeMax
    (.fault .unsupported) ∧
  ¬ WellFormed (mkMultiFrameUnwindProgD21 .unreachable) queryUsizeMax ∧
  (∃ maxSteps, RefReachesOutcome
    (encodeProg (mkMultiFrameUnwindProgD21 .unreachable))
    queryUsizeMax maxSteps .ub)

/-- Single-body unary `CoreBuiltin` harness (`_0 = builtin(copy _1); return`).
-/
noncomputable def mkUnaryBuiltinProgD22 (builtin : CoreBuiltin)
    (retTy argTy : MirTy) : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [retTy, argTy]
    basicBlocks := [
      {
        statements := []
        terminator := .callBuiltin builtin [.copy ⟨1, []⟩]
          ⟨0, []⟩ (some 1) .continue_
      },
      {
        statements := []
        terminator := .return_
      }
    ]
  }]

/-- Single-body binary `CoreBuiltin` harness
(`_0 = builtin(copy _1, copy _2); return`). -/
noncomputable def mkBinaryBuiltinProgD22 (builtin : CoreBuiltin)
    (retTy arg1Ty arg2Ty : MirTy) : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [retTy, arg1Ty, arg2Ty]
    basicBlocks := [
      {
        statements := []
        terminator := .callBuiltin builtin [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
          ⟨0, []⟩ (some 1) .continue_
      },
      {
        statements := []
        terminator := .return_
      }
    ]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D22_core_builtins`: exercises
`TerminatorKind.callBuiltin` across `saturatingSub`, `saturatingAdd`,
`leadingZeros`, `trailingZeros`, `wrappingAdd`, `wrappingShl`,
`overflowingAdd`, `isMultipleOf`, `cmpMin`, and `cmpMax` (plus fail-closed
ill-typed signed `isMultipleOf`) in both $M_{\text{anneal}}$ and
$M_{\text{ref}}$. -/
def CanaryD22CoreBuiltinsClaim : Prop :=
  let u32PairTy : MirTy := .tuple [u32Ty, .bool]
  let i32Ty : MirTy := .int .i32 true
  let pSatSub := mkBinaryBuiltinProgD22 .saturatingSub u32Ty u32Ty u32Ty
  let pSatAdd := mkBinaryBuiltinProgD22 .saturatingAdd i8Ty i8Ty i8Ty
  let pClz := mkUnaryBuiltinProgD22 .leadingZeros u32Ty u32Ty
  let pCtz := mkUnaryBuiltinProgD22 .trailingZeros u32Ty u32Ty
  let pWrapAdd := mkBinaryBuiltinProgD22 .wrappingAdd u32Ty u32Ty u32Ty
  let pWrapShl := mkBinaryBuiltinProgD22 .wrappingShl u32Ty u32Ty u32Ty
  let pOvfAdd := mkBinaryBuiltinProgD22 .overflowingAdd u32PairTy u32Ty u32Ty
  let pMult := mkBinaryBuiltinProgD22 .isMultipleOf .bool u32Ty u32Ty
  let pMultBad := mkBinaryBuiltinProgD22 .isMultipleOf .bool i32Ty i32Ty
  let pMin := mkBinaryBuiltinProgD22 .cmpMin i8Ty i8Ty i8Ty
  let pMax := mkBinaryBuiltinProgD22 .cmpMax i8Ty i8Ty i8Ty
  Behavior pSatSub { args := [u32Val 3, u32Val 10] }
    (.returned ⟨u32Val 0, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pSatSub) { args := [u32Val 3, u32Val 10] }
    (.returned ⟨u32Val 0, ⟨[]⟩⟩) ∧
  Behavior pSatAdd { args := [i8Val 100, i8Val 50] }
    (.returned ⟨i8Val 127, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pSatAdd) { args := [i8Val 100, i8Val 50] }
    (.returned ⟨i8Val 127, ⟨[]⟩⟩) ∧
  Behavior pClz { args := [u32Val 0] } (.returned ⟨u32Val 32, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pClz) { args := [u32Val 0] }
    (.returned ⟨u32Val 32, ⟨[]⟩⟩) ∧
  Behavior pClz { args := [u32Val 12] } (.returned ⟨u32Val 28, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pClz) { args := [u32Val 12] }
    (.returned ⟨u32Val 28, ⟨[]⟩⟩) ∧
  Behavior pCtz { args := [u32Val 0] } (.returned ⟨u32Val 32, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pCtz) { args := [u32Val 0] }
    (.returned ⟨u32Val 32, ⟨[]⟩⟩) ∧
  Behavior pCtz { args := [u32Val 12] } (.returned ⟨u32Val 2, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pCtz) { args := [u32Val 12] }
    (.returned ⟨u32Val 2, ⟨[]⟩⟩) ∧
  Behavior pWrapAdd queryU32MaxPlusOne (.returned ⟨u32Val 0, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pWrapAdd) queryU32MaxPlusOne
    (.returned ⟨u32Val 0, ⟨[]⟩⟩) ∧
  Behavior pWrapShl { args := [u32Val 1, u32Val 33] }
    (.returned ⟨u32Val 2, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pWrapShl) { args := [u32Val 1, u32Val 33] }
    (.returned ⟨u32Val 2, ⟨[]⟩⟩) ∧
  Behavior pOvfAdd queryU32MaxPlusOne
    (.returned ⟨.tuple [u32Val 0, .bool true], ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pOvfAdd) queryU32MaxPlusOne
    (.returned ⟨.tuple [u32Val 0, .bool true], ⟨[]⟩⟩) ∧
  Behavior pMult { args := [u32Val 12, u32Val 4] }
    (.returned ⟨.bool true, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pMult) { args := [u32Val 12, u32Val 4] }
    (.returned ⟨.bool true, ⟨[]⟩⟩) ∧
  Behavior pMult { args := [u32Val 0, u32Val 0] }
    (.returned ⟨.bool true, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pMult) { args := [u32Val 0, u32Val 0] }
    (.returned ⟨.bool true, ⟨[]⟩⟩) ∧
  Behavior pMult { args := [u32Val 5, u32Val 0] }
    (.returned ⟨.bool false, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pMult) { args := [u32Val 5, u32Val 0] }
    (.returned ⟨.bool false, ⟨[]⟩⟩) ∧
  Behavior pMin { args := [i8Val 251, i8Val 3] }
    (.returned ⟨i8Val 251, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pMin) { args := [i8Val 251, i8Val 3] }
    (.returned ⟨i8Val 251, ⟨[]⟩⟩) ∧
  Behavior pMax { args := [i8Val 251, i8Val 3] }
    (.returned ⟨i8Val 3, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg pMax) { args := [i8Val 251, i8Val 3] }
    (.returned ⟨i8Val 3, ⟨[]⟩⟩) ∧
  ReachesResult pMultBad
    { args := [scalarNatVal .i32 true 4, scalarNatVal .i32 true 2] }
    (.fault .unsupported) ∧
  ¬ WellFormed pMultBad
    { args := [scalarNatVal .i32 true 4, scalarNatVal .i32 true 2] } ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg pMultBad)
    { args := [scalarNatVal .i32 true 4, scalarNatVal .i32 true 2] }
    maxSteps .blocked)

/-- `D23` (diverging direct call returning normally is UB):
Body `0` calls body `1` with `target := none`, and body `1` executes `.return_`.
Returning into a diverging call site faults with `.undefined` / `.ub`
(`Miri.Interpreter.ControlFlow.returnToBlock none`). -/
noncomputable def progDivergingCallReturnD23 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [{
        statements := []
        terminator := .call 1 [] ⟨0, []⟩ none .continue_
      }]
    },
    {
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      }]
    }
  ]

/-- `D23` (diverging `CoreBuiltin` call with `target := none` is UB):
Body `0` invokes `.callBuiltin .wrappingAdd` with `target := none`, faulting
with `.undefined` / `.ub` (`Miri.Interpreter.ControlFlow.returnToBlock none`).
-/
noncomputable def progDivergingBuiltinD23 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    basicBlocks := [{
      statements := []
      terminator := .callBuiltin .wrappingAdd
        [.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩,
         .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩]
        ⟨0, []⟩ none .continue_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D23_diverging_call_return_ub`: exercises
normal return to a `target := none` diverging call continuation for both direct
`.call` and `.callBuiltin`, faulting with `.fault .undefined` / `.ub` via
`Miri.Interpreter.ControlFlow.returnToBlock none`. -/
def CanaryD23DivergingCallReturnUbClaim : Prop :=
  ReachesResult progDivergingCallReturnD23 queryEmpty (.fault .undefined) ∧
  ¬ ReachesResult progDivergingCallReturnD23 queryEmpty (.fault .unsupported) ∧
  ¬ WellFormed progDivergingCallReturnD23 queryEmpty ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progDivergingCallReturnD23)
    queryEmpty maxSteps .ub) ∧
  ReachesResult progDivergingBuiltinD23 queryEmpty (.fault .undefined) ∧
  ¬ ReachesResult progDivergingBuiltinD23 queryEmpty (.fault .unsupported) ∧
  ¬ WellFormed progDivergingBuiltinD23 queryEmpty ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progDivergingBuiltinD23)
    queryEmpty maxSteps .ub)

/-- `D24` (call-entry destination deinitialization observed on unwind):
Body `0` initializes `_1 = 7u32` and calls unwinding body `1` with destination
`_1` and `.cleanup 2`. Call entry deinitializes `_1`, so when body `1` panics
and unwinds into cleanup block `2`, reading `_1` faults with `.undefined` /
`.ub` rather than reading the stale `7u32`. -/
noncomputable def progCallDeinitUnwindReadD24 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty]
      basicBlocks := [
        {
          statements := [
            .assign ⟨1, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩))
          ]
          terminator := .call 1 [] ⟨1, []⟩ (some 1) (.cleanup 2)
        },
        {
          statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
          terminator := .return_
        },
        {
          statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
          terminator := .unwindResume
          cleanup := true
        }
      ]
    },
    {
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [{
        statements := []
        terminator := .assert
          (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩) true
          (.overflow .add) 0 .continue_
      }]
    }
  ]

/-- `D24` (direct `.call` with `.move` argument overlapping `dst`):
Body `0` executes `_1 = callee(move _1)`. Because `rustc`/Miri rejects
overlapping moved arguments and destinations under Tree Borrows / Stacked
Borrows protectors, both $M_{\text{anneal}}$ and $M_{\text{ref}}$ fail closed
with `.fault .unsupported` / `.blocked`. -/
noncomputable def progCallMoveOverlapDstD24 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 1
      locals := [u32Ty, u32Ty]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [.move ⟨1, []⟩] ⟨1, []⟩ (some 1) .continue_
        },
        {
          statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
          terminator := .return_
        }
      ]
    },
    {
      argumentCount := 1
      locals := [u32Ty, u32Ty]
      basicBlocks := [{
        statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        terminator := .return_
      }]
    }
  ]

/-- `D24` (`.callBuiltin` with `.move` argument overlapping `dst`):
Body `0` executes `_1 = wrapping_add(move _1, 1u32)` and fails closed with
`.fault .unsupported` / `.blocked`. -/
noncomputable def progBuiltinMoveOverlapDstD24 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [
      {
        statements := []
        terminator := .callBuiltin .wrappingAdd
          [.move ⟨1, []⟩, .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩]
          ⟨1, []⟩ (some 1) .continue_
      },
      {
        statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        terminator := .return_
      }
    ]
  }]

/-- `D24` positive contrast: `.copy` arguments overlapping `dst` remain
admitted for both direct `.call` and `.callBuiltin`
(`_1 = id(copy _1); _1 = wrapping_add(copy _1, 1); _0 = copy _1`). -/
noncomputable def progCallAndBuiltinCopyOverlapDstD24 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 1
      locals := [u32Ty, u32Ty]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨1, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .callBuiltin .wrappingAdd
            [.copy ⟨1, []⟩, .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩]
            ⟨1, []⟩ (some 2) .continue_
        },
        {
          statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
          terminator := .return_
        }
      ]
    },
    {
      argumentCount := 1
      locals := [u32Ty, u32Ty]
      basicBlocks := [{
        statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        terminator := .return_
      }]
    }
  ]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D24_call_deinit_and_overlap`: exercises
(1) call-entry `dst` deinitialization observed as `.undefined`/`.ub` when a
caller cleanup block reads `dst` after callee unwind, (2) fail-closed
`.unsupported`/`.blocked` on `.move` arguments overlapping `dst` for both
direct `.call` and `.callBuiltin`, and (3) positive contrast admitting `.copy`
arguments overlapping `dst` for both `.call` and `.callBuiltin`. -/
def CanaryD24CallDeinitAndOverlapClaim : Prop :=
  let q9 : Query := { args := [u32Val 9] }
  ReachesResult progCallDeinitUnwindReadD24 queryEmpty (.fault .undefined) ∧
  ¬ ReachesResult progCallDeinitUnwindReadD24 queryEmpty (.fault .unsupported) ∧
  ¬ WellFormed progCallDeinitUnwindReadD24 queryEmpty ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progCallDeinitUnwindReadD24)
    queryEmpty maxSteps .ub) ∧
  ReachesResult progCallMoveOverlapDstD24 q9 (.fault .unsupported) ∧
  ¬ ReachesResult progCallMoveOverlapDstD24 q9 (.fault .undefined) ∧
  ¬ WellFormed progCallMoveOverlapDstD24 q9 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progCallMoveOverlapDstD24)
    q9 maxSteps .blocked) ∧
  ReachesResult progBuiltinMoveOverlapDstD24 q9 (.fault .unsupported) ∧
  ¬ ReachesResult progBuiltinMoveOverlapDstD24 q9 (.fault .undefined) ∧
  ¬ WellFormed progBuiltinMoveOverlapDstD24 q9 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progBuiltinMoveOverlapDstD24)
    q9 maxSteps .blocked) ∧
  WellFormed progCallAndBuiltinCopyOverlapDstD24 q9 ∧
  Behavior progCallAndBuiltinCopyOverlapDstD24 q9
    (.returned ⟨u32Val 10, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progCallAndBuiltinCopyOverlapDstD24) q9 ∧
  RefBehavior (encodeProg progCallAndBuiltinCopyOverlapDstD24) q9
    (.returned ⟨u32Val 10, ⟨[]⟩⟩)

/-! ### Tier 2 Pass 2 Canaries (`D25`–`D27`) -/

/-- `u64` type descriptor (`IntWidth.i64`, unsigned). -/
noncomputable def u64Ty : MirTy := .int .i64 false

/-- Construct a `u64` scalar `Val` from `n : Nat`. -/
noncomputable def u64Val (n : Nat) : Val := scalarNatVal .i64 false n

/-- `U64Range { min: u64, max: u64 }` struct type descriptor (`D25`). -/
noncomputable def u64RangeSty : StructTy where
  id := 0
  fields := [u64Ty, u64Ty]

/-- `MirTy.adtStruct u64RangeSty`. -/
noncomputable def u64RangeTy : MirTy := .adtStruct u64RangeSty

/-- Zero-sized marker struct `struct Marker;` (`fields = []`) for `D25`. -/
noncomputable def zstMarkerSty : StructTy where
  id := 1
  fields := []

/-- `MirTy.adtStruct zstMarkerSty`. -/
noncomputable def zstMarkerTy : MirTy := .adtStruct zstMarkerSty

/-- `D25` (`U64Range { min, max }` struct aggregate, ZST struct, sibling field
move, and field write):
Takes `r1, r2 : U64Range`, constructs ZST `Marker {}` (`_3`) and copies it
(`_4`), adds `r1.min + r2.min` and `r1.max + r2.max` into `_5 : U64Range`,
moves `_5.min` into `_6` (deinitializing `_5.min` while keeping `_5.max` live),
writes `(_5.min) = copy _6 + 1`, and returns `move _5`. -/
noncomputable def progStructAddAndRewriteD25 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [
      u64RangeTy, u64RangeTy, u64RangeTy, zstMarkerTy, zstMarkerTy,
      u64RangeTy, u64Ty, u64Ty, u64Ty
    ]
    basicBlocks := [{
      statements := [
        .assign ⟨3, []⟩ (.aggregate (.adtStruct zstMarkerSty) []),
        .assign ⟨4, []⟩ (.use (.move ⟨3, []⟩)),
        .assign ⟨7, []⟩
          (.binaryOp .add (.copy ⟨1, [.field 0 u64Ty]⟩)
            (.copy ⟨2, [.field 0 u64Ty]⟩)),
        .assign ⟨8, []⟩
          (.binaryOp .add (.copy ⟨1, [.field 1 u64Ty]⟩)
            (.copy ⟨2, [.field 1 u64Ty]⟩)),
        .assign ⟨5, []⟩
          (.aggregate (.adtStruct u64RangeSty) [.move ⟨7, []⟩, .move ⟨8, []⟩]),
        .assign ⟨6, []⟩ (.use (.move ⟨5, [.field 0 u64Ty]⟩)),
        .assign ⟨5, [.field 0 u64Ty]⟩
          (.binaryOp .add (.copy ⟨6, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.use (.move ⟨5, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D25` (use of moved-out struct field is UB):
Moves `_1.0` out of `U64Range` and then reads `_1.0`, faulting with
`.fault .undefined` (`.ub` in $M_{\text{ref}}$). -/
noncomputable def progStructFieldUseAfterMoveD25 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u64Ty, u64RangeTy, u64Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, [.field 0 u64Ty]⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 u64Ty]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D25` (destination-overlapping struct aggregate fails closed):
`_1 = U64Range { min: 1, max: copy (_1.0) }` fails closed with
`.fault .unsupported` (`.blocked` in $M_{\text{ref}}$). -/
noncomputable def progStructOverlapAliasD25 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u64RangeTy, u64RangeTy]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.aggregate (.adtStruct u64RangeSty) [
          .constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩,
          .copy ⟨1, [.field 0 u64Ty]⟩
        ]),
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D25_struct_and_field`: exercises
`MirTy.adtStruct`, `AggregateKind.adtStruct` (non-ZST `U64Range` and ZST
`Marker`), struct field reads/writes/moves, use-after-move UB on a moved struct
field, and fail-closed destination-overlapping struct aggregates in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$ (`Miri.Interpreter.writeAggregate` and
`Miri.Interpreter.projectField`). -/
def CanaryD25StructAndFieldClaim : Prop :=
  let r1 : Val := .structVal u64RangeSty [u64Val 10, u64Val 20]
  let r2 : Val := .structVal u64RangeSty [u64Val 5, u64Val 30]
  let rOut : Val := .structVal u64RangeSty [u64Val 16, u64Val 50]
  WellFormed progStructAddAndRewriteD25 { args := [r1, r2] } ∧
  Behavior progStructAddAndRewriteD25 { args := [r1, r2] }
    (.returned ⟨rOut, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progStructAddAndRewriteD25) { args := [r1, r2] } ∧
  RefBehavior (encodeProg progStructAddAndRewriteD25) { args := [r1, r2] }
    (.returned ⟨rOut, ⟨[]⟩⟩) ∧
  ReachesResult progStructFieldUseAfterMoveD25 { args := [r1] }
    (.fault .undefined) ∧
  ¬ ReachesResult progStructFieldUseAfterMoveD25 { args := [r1] }
    (.fault .unsupported) ∧
  ¬ WellFormed progStructFieldUseAfterMoveD25 { args := [r1] } ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progStructFieldUseAfterMoveD25)
    { args := [r1] } maxSteps .ub) ∧
  ReachesResult progStructOverlapAliasD25 { args := [r1] }
    (.fault .unsupported) ∧
  ¬ ReachesResult progStructOverlapAliasD25 { args := [r1] }
    (.fault .undefined) ∧
  ¬ WellFormed progStructOverlapAliasD25 { args := [r1] } ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progStructOverlapAliasD25)
    { args := [r1] } maxSteps .blocked)

/-- Direct-tagged `Option<u64>` enum descriptor (`None = 0`, `Some(u64) = 1`,
64-bit tag matching `rustc` ABI layout). -/
noncomputable def optionU64EnumTy : EnumTy where
  id := 0
  discrWidth := .isize
  discrSigned := true
  tagRepr := .scalar .i64 false
  discriminants := [0, 1]
  variantFields := [[], [u64Ty]]

/-- `MirTy.enum optionU64EnumTy`. -/
noncomputable def optionU64Ty : MirTy := .enum optionU64EnumTy

/-- Niche-encoded `Option<bool>` enum descriptor (`None = 0` niche-encoded at
tag `2`, `Some(bool) = 1` untagged with `validRange = 0..=2`). -/
noncomputable def optionBoolNicheEnumTy : EnumTy where
  id := 1
  discrWidth := .isize
  discrSigned := true
  tagRepr := .niche .i8 false (BitVec.ofNat 128 0) (BitVec.ofNat 128 2)
    [0] 1 0 0 (BitVec.ofNat 128 2)
  discriminants := [0, 1]
  variantFields := [[], [.bool]]

/-- `MirTy.enum optionBoolNicheEnumTy`. -/
noncomputable def optionBoolNicheTy : MirTy := .enum optionBoolNicheEnumTy

/-- Enum with uninhabited variant `1` carrying `!` (`MirTy.never`) for testing
`SetDiscriminant` uninhabited-variant UB. -/
noncomputable def partiallyInhabitedEnumTy : EnumTy where
  id := 2
  discrWidth := .isize
  discrSigned := true
  tagRepr := .single 0
  discriminants := [0, 1]
  variantFields := [[u64Ty], [.never]]

/-- `D26` (`Option<u64>` `Downcast` + `Field` + `SetDiscriminant` construction
into `.uninit` local `_2`, payload read, and `.adtEnum` aggregate):
Writes `((_2 as 1).0) = copy _1 + 1`, executes `SetDiscriminant(_2, 1)`, reads
`_3 = copy ((_2 as 1).0)`, and builds `_0 = Aggregate(.adtEnum ... 1, [_3])`.
-/
noncomputable def progOptionU64SetDiscrDowncastD26 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [optionU64Ty, u64Ty, optionU64Ty, u64Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨2, [.downcast 1, .field 0 u64Ty]⟩
          (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .setDiscriminant ⟨2, []⟩ 1,
        .assign ⟨3, []⟩ (.use (.copy ⟨2, [.downcast 1, .field 0 u64Ty]⟩)),
        .assign ⟨0, []⟩
          (.aggregate (.adtEnum optionU64EnumTy 1) [.move ⟨3, []⟩])
      ]
      terminator := .return_
    }]
  }]

/-- `D26` (niche-encoded `Option<bool>` construction and `Rvalue.discriminant`
read): constructs `_2 = Some(copy _1)` (`SetDiscriminant(_2, 1)` after writing
`((_2 as 1).0)`) and `_3 = None` (`SetDiscriminant(_3, 0)`), reads both
discriminants via `Rvalue.discriminant`, and returns `(discr(_2), discr(_3))`.
-/
noncomputable def progOptionBoolNicheDiscrD26 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [
      .tuple [.int .isize true, .int .isize true],
      .bool, optionBoolNicheTy, optionBoolNicheTy,
      .int .isize true, .int .isize true
    ]
    basicBlocks := [{
      statements := [
        .assign ⟨2, [.downcast 1, .field 0 .bool]⟩ (.use (.copy ⟨1, []⟩)),
        .setDiscriminant ⟨2, []⟩ 1,
        .setDiscriminant ⟨3, []⟩ 0,
        .assign ⟨4, []⟩ (.discriminant ⟨2, []⟩),
        .assign ⟨5, []⟩ (.discriminant ⟨3, []⟩),
        .assign ⟨0, []⟩ (.aggregate .tuple [.move ⟨4, []⟩, .move ⟨5, []⟩])
      ]
      terminator := .return_
    }]
  }]

/-- `D26` (reading a partial downcasted enum shell before `SetDiscriminant`
sets the active tag is UB):
Writes `((_1 as 1).0) = 42u64` into `.uninit` `_1 : Option<u64>` (which
materializes `.enumUntagged` without faulting) and then attempts `_0 = move _1`
without `SetDiscriminant(_1, 1)`, faulting with `.fault .undefined` / `.ub`. -/
noncomputable def progUninitDowncastReadBeforeSetDiscrUbD26 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [optionU64Ty, optionU64Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨1, [.downcast 1, .field 0 u64Ty]⟩
          (.use (.constant ⟨u64Ty, .scalar (BitVec.ofNat 128 42)⟩)),
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D26` (Niche `SetDiscriminant` of `untagged` on `.uninit` enum is UB):
Executes `SetDiscriminant(_1, 1)` (`Some`) on `.uninit` `_1 : Option<bool>`
without initializing `((_1 as 1).0)`, faulting with `.fault .undefined` / `.ub`
(`InvalidNichedEnumVariantWritten`). -/
noncomputable def progNicheSetDiscrUntaggedOnUninitUbD26 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit, optionBoolNicheTy]
    basicBlocks := [{
      statements := [
        .setDiscriminant ⟨1, []⟩ 1,
        .assign ⟨0, []⟩ (.aggregate .tuple [])
      ]
      terminator := .return_
    }]
  }]

/-- `D26` (`SetDiscriminant(_1, 0)` on `.unit` `()` is a no-op matching
`Miri.ABI.Variants.Single 0`): returns `()`. -/
noncomputable def progUnitSetDiscrNoopD26 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit, .unit]
    basicBlocks := [{
      statements := [
        .setDiscriminant ⟨1, []⟩ 0
      ]
      terminator := .return_
    }]
  }]

/-- `D26` (`SetDiscriminant(_1, 1)` on `.unit` `()` faults UB matching
`Miri.ABI.LayoutData.isVariantUninhabited` on `Variants.Single 0`). -/
noncomputable def progUnitSetDiscrBadVariantUbD26 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit, .unit]
    basicBlocks := [{
      statements := [
        .setDiscriminant ⟨1, []⟩ 1
      ]
      terminator := .return_
    }]
  }]

/-- `D26` (`SetDiscriminant` on an uninhabited enum variant is UB):
Executes `SetDiscriminant(_1, 1)` on `partiallyInhabitedEnumTy` (where variant
`1` has payload `[.never]`) and faults cleanly with `.fault .undefined` / `.ub`.
-/
noncomputable def progUninhabitedVariantSetDiscrUbD26 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit, .enum partiallyInhabitedEnumTy]
    basicBlocks := [{
      statements := [
        .setDiscriminant ⟨1, []⟩ 1
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D26_payload_niche_enum_and_checked_arith`:
exercises payload enum `Option<u64>` construction (`Downcast` + `Field` +
`SetDiscriminant` and `.adtEnum` aggregate), niche-encoded `Option<bool>`
construction and `Rvalue.discriminant` tag decoding, `CoreBuiltin.checkedAdd`
overflow (`None`) vs non-overflow (`Some`), untagged partial-shell read UB,
niche untagged-on-uninit UB, non-enum `SetDiscriminant` (`variant 0` no-op,
`variant 1` UB), and uninhabited-variant `SetDiscriminant` UB. -/
def CanaryD26PayloadNicheEnumAndCheckedArithClaim : Prop :=
  let pCheckedAdd := mkBinaryBuiltinProgD22 .checkedAdd optionU64Ty u64Ty u64Ty
  let some42 : Val := .enumVal optionU64EnumTy 1 [u64Val 42]
  let noneU64 : Val := .enumVal optionU64EnumTy 0 []
  let isize10Pair : Val :=
    .tuple [scalarNatVal .isize true 1, scalarNatVal .isize true 0]
  let qOvfU64 : Query := { args := [u64Val (Nat.pow 2 64 - 1), u64Val 1] }
  WellFormed progOptionU64SetDiscrDowncastD26 { args := [u64Val 41] } ∧
  Behavior progOptionU64SetDiscrDowncastD26 { args := [u64Val 41] }
    (.returned ⟨some42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progOptionU64SetDiscrDowncastD26)
    { args := [u64Val 41] } ∧
  RefBehavior (encodeProg progOptionU64SetDiscrDowncastD26)
    { args := [u64Val 41] } (.returned ⟨some42, ⟨[]⟩⟩) ∧
  WellFormed progOptionBoolNicheDiscrD26 { args := [.bool true] } ∧
  Behavior progOptionBoolNicheDiscrD26 { args := [.bool true] }
    (.returned ⟨isize10Pair, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progOptionBoolNicheDiscrD26)
    { args := [.bool true] } ∧
  RefBehavior (encodeProg progOptionBoolNicheDiscrD26)
    { args := [.bool true] } (.returned ⟨isize10Pair, ⟨[]⟩⟩) ∧
  WellFormed pCheckedAdd { args := [u64Val 40, u64Val 2] } ∧
  Behavior pCheckedAdd { args := [u64Val 40, u64Val 2] }
    (.returned ⟨some42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg pCheckedAdd) { args := [u64Val 40, u64Val 2] } ∧
  RefBehavior (encodeProg pCheckedAdd) { args := [u64Val 40, u64Val 2] }
    (.returned ⟨some42, ⟨[]⟩⟩) ∧
  WellFormed pCheckedAdd qOvfU64 ∧
  Behavior pCheckedAdd qOvfU64 (.returned ⟨noneU64, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg pCheckedAdd) qOvfU64 ∧
  RefBehavior (encodeProg pCheckedAdd) qOvfU64 (.returned ⟨noneU64, ⟨[]⟩⟩) ∧
  ReachesResult progUninitDowncastReadBeforeSetDiscrUbD26 queryEmpty
    (.fault .undefined) ∧
  ¬ ReachesResult progUninitDowncastReadBeforeSetDiscrUbD26 queryEmpty
    (.fault .unsupported) ∧
  (∃ maxSteps, RefReachesOutcome
    (encodeProg progUninitDowncastReadBeforeSetDiscrUbD26)
    queryEmpty maxSteps .ub) ∧
  ReachesResult progNicheSetDiscrUntaggedOnUninitUbD26 queryEmpty
    (.fault .undefined) ∧
  ¬ ReachesResult progNicheSetDiscrUntaggedOnUninitUbD26 queryEmpty
    (.fault .unsupported) ∧
  (∃ maxSteps, RefReachesOutcome
    (encodeProg progNicheSetDiscrUntaggedOnUninitUbD26)
    queryEmpty maxSteps .ub) ∧
  WellFormed progUnitSetDiscrNoopD26 queryEmpty ∧
  Behavior progUnitSetDiscrNoopD26 queryEmpty (.returned ⟨.unit, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progUnitSetDiscrNoopD26) queryEmpty ∧
  RefBehavior (encodeProg progUnitSetDiscrNoopD26) queryEmpty
    (.returned ⟨.unit, ⟨[]⟩⟩) ∧
  ReachesResult progUnitSetDiscrBadVariantUbD26 queryEmpty
    (.fault .undefined) ∧
  ¬ ReachesResult progUnitSetDiscrBadVariantUbD26 queryEmpty
    (.fault .unsupported) ∧
  (∃ maxSteps, RefReachesOutcome
    (encodeProg progUnitSetDiscrBadVariantUbD26) queryEmpty maxSteps .ub) ∧
  ReachesResult progUninhabitedVariantSetDiscrUbD26 queryEmpty
    (.fault .undefined) ∧
  ¬ ReachesResult progUninhabitedVariantSetDiscrUbD26 queryEmpty
    (.fault .unsupported) ∧
  (∃ maxSteps, RefReachesOutcome
    (encodeProg progUninhabitedVariantSetDiscrUbD26) queryEmpty maxSteps .ub)

/-- `[u8; 4]` fixed array type descriptor (`D27`). -/
noncomputable def u8Array4Ty : MirTy := .array u8Ty 4

/-- `[u8; 3]` fixed array type descriptor (`D27`). -/
noncomputable def u8Array3Ty : MirTy := .array u8Ty 3

/-- `D27` (`[u8; 4]` aggregate, forward & `fromEnd` `ConstantIndex`, passing
`Assert(.boundsCheck)`, and dynamic `Index` read/write preserving `idxLocal`):
Constructs `_2 = [10, 20, 30, 40]`, reads `_3 = _2[0]` (`constantIndex 0 4
false`) and `_4 = _2[4 - 1]` (`constantIndex 1 4 true`), checks `idx < 4` via
`Assert(.boundsCheck)`, reads `_5 = _2[idx]` (`index _1`), copies `_1` into `_6`
(confirming `ProjectionElem.index` does not deinitialize `idxLocal`), writes
`_2[idx] = _3 + _4 + _5` (`10 + 40 + 30 = 80` at `idx = 2`), and returns `_2`.
-/
noncomputable def progArrayAggregateAndIndexD27 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [
      u8Array4Ty, usizeTy, u8Array4Ty, u8Ty, u8Ty, u8Ty, usizeTy, .bool, u8Ty
    ]
    basicBlocks := [
      {
        statements := [
          .assign ⟨2, []⟩ (.aggregate (.array u8Ty) [
            .constant ⟨u8Ty, .scalar (BitVec.ofNat 128 10)⟩,
            .constant ⟨u8Ty, .scalar (BitVec.ofNat 128 20)⟩,
            .constant ⟨u8Ty, .scalar (BitVec.ofNat 128 30)⟩,
            .constant ⟨u8Ty, .scalar (BitVec.ofNat 128 40)⟩
          ]),
          .assign ⟨3, []⟩
            (.use (.copy ⟨2, [.constantIndex 0 4 false]⟩)),
          .assign ⟨4, []⟩
            (.use (.copy ⟨2, [.constantIndex 1 4 true]⟩)),
          .assign ⟨7, []⟩
            (.binaryOp .lt (.copy ⟨1, []⟩)
              (.constant ⟨usizeTy, .scalar (BitVec.ofNat 128 4)⟩))
        ]
        terminator := .assert (.move ⟨7, []⟩) true .boundsCheck 1 .continue_
      },
      {
        statements := [
          .assign ⟨5, []⟩ (.use (.copy ⟨2, [.index 1]⟩)),
          .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
          .assign ⟨8, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)),
          .assign ⟨2, [.index 1]⟩
            (.binaryOp .add (.copy ⟨8, []⟩) (.copy ⟨5, []⟩)),
          .assign ⟨0, []⟩ (.use (.move ⟨2, []⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- `D27` (dynamic `ProjectionElem.index` out-of-bounds is UB):
Reads `_1[index _2]` on `_1 : [u8; 4]` with `_2 : usize` out of bounds (`4`),
faulting with `.fault .undefined` / `.ub` (`Miri.Interpreter.projectIndex`). -/
noncomputable def progArrayDynamicIndexOobUbD27 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u8Ty, u8Array4Ty, usizeTy]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.index 2]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D27` (Miri Divergence Watch-Out #1a —
`DIV-LM-CONSTANT-INDEX-NAT-SUB-SATURATION`, `offset > minLength` with
`fromEnd = true` fails closed):
`ConstantIndex 4 1 true` on `[u8; 3]` (`len = 3 >= minLength = 1`, `offset = 4
> len = 3`) must NOT saturate `3 - 4` to `0`; both $M_{\text{anneal}}$ and
$M_{\text{ref}}$ (`Miri.Interpreter.projectConstantIndex`) fail closed with
`.fault .unsupported` / `.blocked`. -/
noncomputable def progConstIndexFromEndGtMinLenBlockedD27 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u8Ty, u8Array3Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.constantIndex 4 1 true]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D27` (Miri Divergence Watch-Out #1b —
`DIV-LM-CONSTANT-INDEX-NAT-SUB-SATURATION`, `len < minLength` with
`fromEnd = true` faults with UB):
`ConstantIndex 4 5 true` on `[u8; 3]` (`len = 3 < minLength = 5`) faults with
`.fault .undefined` / `.ub` (`ProjectionError.bounds`). -/
noncomputable def progConstIndexFromEndLtMinLenUbD27 : Program where
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u8Ty, u8Array3Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.constantIndex 4 5 true]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D27_array_indexing_and_le_bytes`:
exercises `[u8; 4]` array aggregate construction, forward and `fromEnd`
`ConstantIndex`, passing `Assert(.boundsCheck)`, dynamic `Index` read/write
(preserving `idxLocal`), out-of-bounds dynamic `Index` UB, Miri Divergence
Watch-Out #1 (`DIV-LM-CONSTANT-INDEX-NAT-SUB-SATURATION`), and `toLeBytes` /
`fromLeBytes` round-tripping in both $M_{\text{anneal}}$ and $M_{\text{ref}}$.
-/
def CanaryD27ArrayIndexingAndLeBytesClaim : Prop :=
  let arr4In : Val :=
    .array u8Ty [u8Val 10, u8Val 20, u8Val 30, u8Val 40]
  let arr4Out : Val :=
    .array u8Ty [u8Val 10, u8Val 20, u8Val 80, u8Val 40]
  let arr3In : Val := .array u8Ty [u8Val 7, u8Val 8, u8Val 9]
  let leArr : Val := .array u8Ty [u8Val 4, u8Val 3, u8Val 2, u8Val 1]
  let u32Word : Val := u32Val 0x01020304
  let pToLe := mkUnaryBuiltinProgD22 .toLeBytes u8Array4Ty u32Ty
  let pFromLe := mkUnaryBuiltinProgD22 .fromLeBytes u32Ty u8Array4Ty
  WellFormed progArrayAggregateAndIndexD27 { args := [usizeVal 2] } ∧
  Behavior progArrayAggregateAndIndexD27 { args := [usizeVal 2] }
    (.returned ⟨arr4Out, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progArrayAggregateAndIndexD27)
    { args := [usizeVal 2] } ∧
  RefBehavior (encodeProg progArrayAggregateAndIndexD27)
    { args := [usizeVal 2] } (.returned ⟨arr4Out, ⟨[]⟩⟩) ∧
  ReachesResult progArrayDynamicIndexOobUbD27 { args := [arr4In, usizeVal 4] }
    (.fault .undefined) ∧
  ¬ ReachesResult progArrayDynamicIndexOobUbD27 { args := [arr4In, usizeVal 4] }
    (.fault .unsupported) ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progArrayDynamicIndexOobUbD27)
    { args := [arr4In, usizeVal 4] } maxSteps .ub) ∧
  ReachesResult progConstIndexFromEndGtMinLenBlockedD27 { args := [arr3In] }
    (.fault .unsupported) ∧
  ¬ ReachesResult progConstIndexFromEndGtMinLenBlockedD27 { args := [arr3In] }
    (.fault .undefined) ∧
  (∃ maxSteps, RefReachesOutcome
    (encodeProg progConstIndexFromEndGtMinLenBlockedD27)
    { args := [arr3In] } maxSteps .blocked) ∧
  ReachesResult progConstIndexFromEndLtMinLenUbD27 { args := [arr3In] }
    (.fault .undefined) ∧
  ¬ ReachesResult progConstIndexFromEndLtMinLenUbD27 { args := [arr3In] }
    (.fault .unsupported) ∧
  (∃ maxSteps, RefReachesOutcome
    (encodeProg progConstIndexFromEndLtMinLenUbD27)
    { args := [arr3In] } maxSteps .ub) ∧
  WellFormed pToLe { args := [u32Word] } ∧
  Behavior pToLe { args := [u32Word] } (.returned ⟨leArr, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg pToLe) { args := [u32Word] } ∧
  RefBehavior (encodeProg pToLe) { args := [u32Word] }
    (.returned ⟨leArr, ⟨[]⟩⟩) ∧
  WellFormed pFromLe { args := [leArr] } ∧
  Behavior pFromLe { args := [leArr] } (.returned ⟨u32Word, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg pFromLe) { args := [leArr] } ∧
  RefBehavior (encodeProg pFromLe) { args := [leArr] }
    (.returned ⟨u32Word, ⟨[]⟩⟩)

end Trusted.Correspondence
