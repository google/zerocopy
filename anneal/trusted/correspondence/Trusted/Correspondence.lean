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
import Miri.Interpreter.Aggregate
import Miri.Interpreter.Discriminant
import Miri.Interpreter.Step
import Miri.Interpreter.ControlFlow
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
     tuple field projections to the local contents that Miri reads
     (`refProjectTy?`, `refReadSlotPath?`, and `refWriteSlotPath?`);
   - local place writes (`writeRefPlace`) through
     `Miri.Interpreter.evalPlaceToOp` and
     `Miri.Interpreter.placeWriteLocalImmediate`;
   - rvalue dispatch and left-to-right operand sequencing (`evalRefMiriRvalue`)
     through `Miri.Interpreter.evalRvalueIntoPlace`,
     `Miri.Interpreter.writeAggregate`,
     `Miri.Interpreter.Discriminant.{readDiscriminant, discriminantForVariant}`,
     and `Miri.Interpreter.runRvalue`;
   - outer step and statement dispatch (`evalRefStep`, `evalRefStatement`)
     through `Miri.Interpreter.Step.step` and
     `Miri.Interpreter.Step.evalStatement`, delegating `_0` `StorageDead`
     rejection to `Miri.Interpreter.Frame.storageDead` (while `storageLive`
     calls `Miri.Interpreter.Frame.storageLive` on a dummy single-local
     frame, always returning `.ok ()`, because adapter locals are modeled
     in the wrapper frame); and
   - basic-block jumps, terminators, `Assert` panics, and unwinding
     (`evalRefTerminator`) through `Miri.Interpreter.Step.step`,
     `Miri.Interpreter.ControlFlow.goToBlock`,
     `Miri.Interpreter.ControlFlow.evalTerminator`,
     `Miri.Interpreter.ControlFlow.unwindToBlock`, and
     `Miri.Interpreter.ControlFlow.returnFromCurrentFrame`:

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
   stack as `[callerSentinelFrame retTy, entryFrame]`, which `evalRefStep`
   requires and preserves.
-/

/-- Interned type-table index (`Miri.MIR.TyId`). -/
abbrev TyId := Nat

/-! ## Reference-Indexed AST with `TyId` Indirection (`Miri.MIR` Boundary) -/

/-- Reference place projection element indexing `RefProg.types` via `TyId`. -/
inductive RefProjectionElem where
  | deref
  | field (fieldIdx : FieldIdx) (ty : TyId)
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

/-- Reference MIR rvalue (`Miri.MIR.Rvalue`). -/
inductive RefRvalue where
  | use (op : RefOperand)
  | binaryOp (op : BinOp) (lhs rhs : RefOperand)
  | unaryOp (op : UnOp) (opnd : RefOperand)
  | discriminant (place : RefPlace)
  | ref (mutability : Mutability) (place : RefPlace)
  | addressOf (mutability : Mutability) (place : RefPlace)
  | aggregateTuple (fields : List RefOperand)
  | cast (kind : CastKind) (op : RefOperand) (ty : TyId)
  | unsupported

/-- Reference MIR statement (`Miri.MIR.StatementKind`). -/
inductive RefStatementKind where
  | assign (dst : RefPlace) (rvalue : RefRvalue)
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
  /-- Recursively intern all structural sub-types (`pointee` in `.ref`/`.rawPtr`
  and `fields` in `.tuple`) in bottom-up topological order before interning the
  enclosing `MirTy`, guaranteeing that pointee and field layouts are always
  present in `(encodeProg p).types`. -/
  noncomputable def collectTy (acc : List MirTy) : MirTy → List MirTy
    | .bool => insertTy .bool acc
    | .int w s => insertTy (.int w s) acc
    | .unit => insertTy .unit acc
    | .never => insertTy .never acc
    | .enum ety => insertTy (.enum ety) acc
    | .unsupported => insertTy .unsupported acc
    | .ref m p => insertTy (.ref m p) (collectTy acc p)
    | .rawPtr m p => insertTy (.rawPtr m p) (collectTy acc p)
    | .tuple fs => insertTy (.tuple fs) (collectTyList acc fs)

  /-- Intern a list of `MirTy` descriptors left-to-right. -/
  noncomputable def collectTyList (acc : List MirTy) : List MirTy → List MirTy
    | [] => acc
    | ty :: tys => collectTyList (collectTy acc ty) tys
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
  | .deref | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in `p.projection`. -/
noncomputable def collectPlace (acc : List MirTy) (p : Place) : List MirTy :=
  p.projection.foldl collectProjElem acc

/-- Intern all `MirTy` descriptors carried in an `Operand`. -/
noncomputable def collectOperand (acc : List MirTy) : Operand → List MirTy
  | .copy p | .move p => collectPlace acc p
  | .constant c => collectTy acc c.ty

/-- Intern all `MirTy` descriptors carried in an `Rvalue`. -/
noncomputable def collectRvalue (acc : List MirTy) : Rvalue → List MirTy
  | .use op => collectOperand acc op
  | .binaryOp _ l r => collectOperand (collectOperand acc l) r
  | .unaryOp _ op => collectOperand acc op
  | .discriminant p | .ref _ p | .addressOf _ p => collectPlace acc p
  | .aggregateTuple ops => ops.foldl collectOperand acc
  | .cast _ op ty => collectTy (collectOperand acc op) ty
  | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a `StatementKind`. -/
noncomputable def collectStmt (acc : List MirTy) : StatementKind → List MirTy
  | .assign dst rv => collectRvalue (collectPlace acc dst) rv
  | .storageLive _ | .storageDead _ | .nop | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a `TerminatorKind`. -/
noncomputable def collectTerminator (acc : List MirTy) :
    TerminatorKind → List MirTy
  | .switchInt d _ => collectOperand acc d
  | .assert c _ _ _ _ => collectOperand acc c
  | .call _ args dst _ _ =>
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
  | .unsupported => .unsupported

/-- Encode a `Place` against type table `ts`. -/
noncomputable def encodePlace (ts : List MirTy) (p : Place) : RefPlace :=
  ⟨p.localId, p.projection.map (encodeProjElem ts)⟩

/-- Encode an `Operand` against type table `ts`. -/
noncomputable def encodeOperand (ts : List MirTy) : Operand → RefOperand
  | .copy p => .copy (encodePlace ts p)
  | .move p => .move (encodePlace ts p)
  | .constant c => .constant ⟨lookupTyId ts c.ty, c.lit⟩

/-- Encode an `Rvalue` against type table `ts`. -/
noncomputable def encodeRvalue (ts : List MirTy) : Rvalue → RefRvalue
  | .use op => .use (encodeOperand ts op)
  | .binaryOp op l r => .binaryOp op (encodeOperand ts l) (encodeOperand ts r)
  | .unaryOp op opnd => .unaryOp op (encodeOperand ts opnd)
  | .discriminant p => .discriminant (encodePlace ts p)
  | .ref m p => .ref m (encodePlace ts p)
  | .addressOf m p => .addressOf m (encodePlace ts p)
  | .aggregateTuple ops => .aggregateTuple (ops.map (encodeOperand ts))
  | .cast kind op ty => .cast kind (encodeOperand ts op) (lookupTyId ts ty)
  | .unsupported => .unsupported

/-- Encode a `StatementKind` against type table `ts`. -/
noncomputable def encodeStmt (ts : List MirTy) :
    StatementKind → RefStatementKind
  | .assign dst rv => .assign (encodePlace ts dst) (encodeRvalue ts rv)
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

/-- Decode a `RefRvalue` against type table `ts`. -/
noncomputable def decodeRvalue (ts : List MirTy) : RefRvalue → Option Rvalue
  | .use op => optMap Rvalue.use (decodeOperand ts op)
  | .binaryOp op l r =>
    optMap2 (Rvalue.binaryOp op) (decodeOperand ts l) (decodeOperand ts r)
  | .unaryOp op opnd => optMap (Rvalue.unaryOp op) (decodeOperand ts opnd)
  | .discriminant p => optMap Rvalue.discriminant (decodePlace ts p)
  | .ref m p => optMap (Rvalue.ref m) (decodePlace ts p)
  | .addressOf m p => optMap (Rvalue.addressOf m) (decodePlace ts p)
  | .aggregateTuple ops =>
    optMap Rvalue.aggregateTuple (mapOption (decodeOperand ts) ops)
  | .cast kind op tyId =>
    optMap2 (Rvalue.cast kind) (decodeOperand ts op)
      (MirSemantics.getElem? ts tyId)
  | .unsupported => some .unsupported

/-- Decode a `RefStatementKind` against type table `ts`. -/
noncomputable def decodeStmt (ts : List MirTy) :
    RefStatementKind → Option StatementKind
  | .assign dst rv =>
    optMap2 StatementKind.assign (decodePlace ts dst) (decodeRvalue ts rv)
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

mutual
  /-- Independent $M_{\text{ref}}$ supported local-type check: `.bool`, `.int`,
  `.unit`, `.never`, an admitted fieldless `.enum`, or a non-empty `.tuple` of
  supported types. -/
  noncomputable def refIsSupportedLocalTy : MirTy → Bool
    | .bool | .int _ _ | .unit | .never => true
    | .enum ety => refEnumAdmitted ety
    | .tuple fields => !fields.isEmpty && refAreSupportedFieldTys fields
    | _ => false

  /-- Independent $M_{\text{ref}}$ check that every field type of a tuple is a
  supported local type. -/
  noncomputable def refAreSupportedFieldTys : List MirTy → Bool
    | [] => true
    | ty :: tys => refIsSupportedLocalTy ty && refAreSupportedFieldTys tys
end

/-- Independent $M_{\text{ref}}$ primitive-readable type check. -/
noncomputable def refIsPrimitiveReadableTy : MirTy → Bool
  | .bool | .int _ _ => true
  | _ => false

mutual
  /-- Independent $M_{\text{ref}}$ contents of a newly live slot of type `ty`:
  inhabited for 0-byte ZSTs (`.unit` and admitted `.zeroSized` 1-variant
  enums), field by field for tuples, and `.uninit` otherwise. -/
  noncomputable def refUninitSlotVal : MirTy → SlotVal
    | .unit => .unit
    | .enum ety => if refIsZstEnumTy ety then .enumVal ety 0 else .uninit
    | .tuple fields => .tuple (refUninitSlotVals fields)
    | _ => .uninit

  /-- Independent $M_{\text{ref}}$ contents of the newly live fields of a
  tuple slot, one per field type. -/
  noncomputable def refUninitSlotVals : List MirTy → List SlotVal
    | [] => []
    | ty :: tys => refUninitSlotVal ty :: refUninitSlotVals tys
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
`readImmediate` because `encodeRefEnumTagOp` maps uninitialized contents to
`Immediate.uninit`. -/
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
  /-- Reference scalar/boolean/unit/enum/tuple value validity and type check
  calling `Miri.Memory.ScalarInt.tryFromUInt` and
  `Miri.Memory.ScalarInt.ofBool`. A tuple value has a tuple type when it is
  non-empty and its fields have the field types position by position
  (`checkRefVals`). -/
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
    | .enumVal ety v, .enum ety' =>
      (refEnumAdmitted ety && Nat.blt v ety.discriminants.length) &&
        EnumTy.beq ety ety'
    | .tuple fields, .tuple fieldTys =>
      !fields.isEmpty && checkRefVals fields fieldTys
    | _, _ => false

  /-- Check field values `vs` against field types `tys` position by position
  under `checkRefVal`, requiring equal lengths. -/
  noncomputable def checkRefVals : List Val → List MirTy → Bool
    | [], [] => true
    | v :: vs, ty :: tys => checkRefVal v ty && checkRefVals vs tys
    | _, _ => false
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
noncomputable def mkSingleLocalMiriFrameWithLayout
    (lv : Miri.Interpreter.LocalValue SlotVal)
    (layout : Miri.Interpreter.LocalLayout) (cleanup : Bool) :
    Miri.Interpreter.Frame SlotVal Miri.Interpreter.LocalLayout Unit := {
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
    (lv : Miri.Interpreter.LocalValue SlotVal) (cleanup : Bool) :
    Miri.Interpreter.Frame SlotVal Miri.Interpreter.LocalLayout Unit :=
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
whole `SlotVal` (see `slotToMiriLocalValue`), so the adapter applies field
projections to that `SlotVal` itself (`refProjectTy?`, `refReadSlotPath?`, and
`refWriteSlotPath?`) after Miri has read the local. -/
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

/-- Independent $M_{\text{ref}}$ type of the part of a place of type `ty` that
the projection `proj` selects, or `none` if `proj` does not apply to `ty`.

Only `Miri.MIR.ProjectionElem.Field` on a tuple type applies. A field
projection states its field's type as a `TyId`; it applies only when the field
index is in bounds, the `TyId` resolves in `types`, and the resolved type
equals the tuple's field type at that index. Every other projection element
returns `none`. -/
noncomputable def refProjectTy? (types : List MirTy) :
    MirTy → List Miri.MIR.ProjectionElem → Option MirTy
  | ty, [] => some ty
  | ty, elem :: rest =>
    match ty, elem with
    | .tuple fieldTys, .Field idx tyId =>
      match MirSemantics.getElem? fieldTys idx,
          MirSemantics.getElem? types tyId with
      | some fieldTy, some statedTy =>
        if MirTy.beq fieldTy statedTy then
          refProjectTy? types fieldTy rest
        else
          none
      | _, _ => none
    | _, _ => none

/-- Independent $M_{\text{ref}}$ contents of the part of slot contents `sv`
that the projection `proj` selects, or `none` if `proj` does not apply to
`sv`. -/
noncomputable def refReadSlotPath? :
    SlotVal → List Miri.MIR.ProjectionElem → Option SlotVal
  | sv, [] => some sv
  | sv, elem :: rest =>
    match sv, elem with
    | .tuple fields, .Field idx _ =>
      match MirSemantics.getElem? fields idx with
      | some field => refReadSlotPath? field rest
      | none => none
    | _, _ => none

/-- Independent $M_{\text{ref}}$ slot contents `sv` with the part that the
projection `proj` selects replaced by `new`, or `none` if `proj` does not
apply to `sv`. Every other part of `sv` keeps its contents. -/
noncomputable def refWriteSlotPath? :
    SlotVal → List Miri.MIR.ProjectionElem → SlotVal → Option SlotVal
  | _, [], new => some new
  | sv, elem :: rest, new =>
    match sv, elem with
    | .tuple fields, .Field idx _ =>
      match MirSemantics.getElem? fields idx with
      | some field =>
        match refWriteSlotPath? field rest new with
        | some field' =>
          match MirSemantics.setElem? fields idx field' with
          | some fields' => some (.tuple fields')
          | none => none
        | none => none
      | none => none
    | _, _ => none

/-- Destination place resolved by `refRvalueHooks.evalPlace`: the local
`localId`, the projection `projection` into that local, and the type `ty` of
the part of the local that the projection selects (`refProjectTy?`). -/
structure RefDest where
  localId : LocalId
  projection : List Miri.MIR.ProjectionElem
  ty : MirTy

/-- Write `val` into the destination `dst` in `rlocals`, preserving the cached
layout of the destination local.

The write checks `val` against `dst.ty` (`checkRefVal`), reads the current
contents of the destination local through `Miri.Interpreter.evalPlaceToOp`
(`vendor/lean-miri/Miri/Interpreter/LocalAccess.lean`), replaces the part that
`dst.projection` selects with `val` (`refWriteSlotPath?`), and writes the
updated contents back through `Miri.Interpreter.placeWriteLocalImmediate`
(`vendor/lean-miri/Miri/Interpreter/Place.lean`). A dead destination local
fails Miri's read and is UB (`.error .undefined`). A projection that does not
apply to the current contents returns `.error .unsupported`. An unprojected
write replaces the whole contents, so its result does not depend on what the
local held. -/
noncomputable def writeRefPlace (rlocals : List RefLocalState)
    (dst : RefDest) (val : Val) : Except FaultKind (List RefLocalState) :=
  if !checkRefVal val dst.ty then
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
        match refWriteSlotPath? root dst.projection val.toSlotVal with
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
place `⟨localId, proj⟩` in `rlocals`, returning the type and contents of the
part that `proj` selects together with the locals after the access.

The local is read through `Miri.Interpreter.evalOperand`
(`deinitMovedPlace = true`) on a single-local frame. A dead local fails that
read and is UB (`.error .undefined`).

- Unprojected access (`proj = []`): a move runs Miri's `.Move`, which leaves a
  non-ZST local as `Immediate.uninit` and keeps a ZST local
  (`outLayout.layout.isZst`: `MirTy.unit` and admitted 1-variant ZST enums)
  initialized. In both cases the adapter records the moved-out local as
  `refLiveUninitSlot localTy`, whose non-ZST parts are uninitialized.
- Projected access (`proj ≠ []`): the adapter reads the whole local with
  Miri's `.Copy` and applies the field projection to its contents
  (`refProjectTy?` and `refReadSlotPath?`); a projection that does not apply
  returns `.error .unsupported`. A move then replaces only the selected part
  with `refUninitSlotVal ty` (`refWriteSlotPath?`), so every other field keeps
  its contents. `Miri.Interpreter.evalOperand` handles a projected `Move` by
  forcing the local into memory (`LocalAccessHooks.forceLocalAllocation`),
  which adapter frames do not model, so this per-field deinitialization is an
  Anneal-written rule that `Trusted.MirSemantics.evalPlaceOperand` mirrors.
  Canary `D14` (`CanaryD14OverflowTupleFieldMovesClaim`) checks that the two
  models agree on it. -/
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
        match refProjectTy? types localTy proj, refReadSlotPath? root proj with
        | some ty, some sv =>
          if !isMove then
            .ok (ty, sv, rlocals)
          else
            match refWriteSlotPath? root proj (refUninitSlotVal ty) with
            | some root' =>
              match MirSemantics.setElem? rlocals localId
                  ⟨.live root', some localTy⟩ with
              | some rlocals' => .ok (ty, sv, rlocals')
              | none => .error .unsupported
            | none => .error .unsupported
        | _, _ => .error .unsupported
      | _ => .error .undefined
  | _ => .error .unsupported

/-- Map `RefProjectionElem` to `Miri.MIR.ProjectionElem`.

`.unsupported` maps to the fail-closed sentinel `.PhantomDeref`: like `.Deref`,
it is not a field projection, so `refProjectTy?` rejects any place that
contains it (`.fault .unsupported`). -/
noncomputable def toMiriProjElem :
    RefProjectionElem → Miri.MIR.ProjectionElem
  | .deref => .Deref
  | .field idx ty => .Field idx ty
  | .unsupported => .PhantomDeref

/-- Map `RefPlace` to `Miri.MIR.Place`, preserving `localId` and every
projection element (`toMiriProjElem`). -/
noncomputable def toMiriPlace (rp : RefPlace) : Miri.MIR.Place :=
  ⟨rp.localId, Array.mk (rp.projection.map toMiriProjElem)⟩

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

/-- Map `Trusted.MirAst.CastKind` to `Miri.MIR.CastKind`.

`.unsupported` maps to the fail-closed sentinel `.Transmute`, which
`refRvalueHooks.cast` rejects like every cast kind other than `.IntToInt`
(`.fault .unsupported`). -/
noncomputable def toMiriCastKind : CastKind → Miri.MIR.CastKind
  | .intToInt => .IntToInt
  | .unsupported => .Transmute

/-- Map `RefRvalue` to `Miri.MIR.Rvalue` for
`Miri.Interpreter.Step.evalStatement` and
`Miri.Interpreter.evalRvalueIntoPlace`.

Supported rvalues (`.use`, `.binaryOp`, `.unaryOp`, `.discriminant`,
`.aggregateTuple`, and `.cast`) and unmodeled AST rvalues (`.ref` and
`.addressOf`) translate to their real `Miri.MIR.Rvalue` constructors so
`evalRvalueIntoPlace` routes them through its real dispatch arms
(`writeAggregate` for `.aggregateTuple`, `cast` for `.cast`, and
`forceAllocation` for `.ref`/`.addressOf`). `.cast` keeps its target type as
the real `RefProg.types` index that `refRvalueHooks.cast` resolves.
`.unsupported` uses `.CopyForDeref ⟨0, Array.empty⟩` as a fail-closed sentinel
that `evalRvalueIntoPlace` rejects directly with `.invalidProgram` (`.fault
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

/-- Re-encode a fieldless enum's `(ety, sv)` slot payload into a
`Miri.Interpreter.OpTy Miri.Memory.Provenance` (`.uninit` for `.zeroSized` or
uninitialized scalar tags, and `Miri.Memory.ScalarInt.truncateFromUInt` for
initialized scalar tags) for `Miri.Interpreter.Discriminant.readDiscriminant`.
-/
noncomputable def encodeRefEnumTagOp (ety : EnumTy) (sv : SlotVal) :
    Except Miri.Interpreter.StepError
      (Miri.Interpreter.OpTy Miri.Memory.Provenance) :=
  let layout : Miri.Interpreter.LocalLayout := ⟨0, refEnumLayoutData ety⟩
  match ety.tagRepr, sv with
  | .zeroSized, .uninit => .ok ⟨.immediate .uninit, layout⟩
  | .zeroSized, .enumVal ety' v =>
    if EnumTy.beq ety ety' && Nat.beq v 0 then
      .ok ⟨.immediate .uninit, layout⟩
    else
      .error (.unsupported "mismatched ZST enum variant in slot")
  | .zeroSized, _ =>
    .error (.unsupported "non-enum value in ZST enum slot")
  | .scalar _ _, .uninit => .ok ⟨.immediate .uninit, layout⟩
  | .scalar tagW _, .enumVal ety' v =>
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
  | .scalar _ _, _ =>
    .error (.unsupported "non-enum value in scalar enum slot")

/-- Evaluate an unprojected enum local `src` to
`Miri.Interpreter.OpTy (MirTy × SlotVal)` via
`Miri.Interpreter.evalPlaceToOp` (`Miri.Interpreter.localToOp`) for
`RvalueHooks.evalPlaceToOp` (`.Discriminant src`), returning layout
`⟨enumTyId, refEnumLayoutData ety⟩` where `enumTyId` is the real
`RefProg.types` index of `.enum ety` (forwarded by Miri as `op.layout.ty` to
`discriminantForVariant`). -/
noncomputable def evalRefEnumPlaceToOp (types : List MirTy)
    (src : Miri.MIR.Place) (rlocals : List RefLocalState) :
    EStateM.Result Miri.Interpreter.StepError (List RefLocalState)
      (Miri.Interpreter.OpTy (MirTy × SlotVal)) :=
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
            let sv : SlotVal :=
              match miriImmediateToPayload? imm with
              | some sv => sv
              | none => .uninit
            .ok ⟨.immediate (payloadToMiriImmediate (.enum ety, sv)),
              layout⟩ rlocals
    | _ => .error (.unsupported "Discriminant on non-enum local") rlocals

/-- Independent $M_{\text{ref}}$ check that two `Miri.MIR.ProjectionElem` steps
may alias the same subplace: two `.Field` steps alias iff they select the same
field index, and any non-`.Field` step is treated conservatively as potentially
aliasing. -/
noncomputable def refProjElemMayAlias :
    Miri.MIR.ProjectionElem → Miri.MIR.ProjectionElem → Bool
  | .Field i _, .Field j _ => Nat.beq i j
  | _, _ => true

/-- Independent $M_{\text{ref}}$ prefix-overlap check on projection lists. -/
noncomputable def refProjPrefixMayAlias :
    List Miri.MIR.ProjectionElem → List Miri.MIR.ProjectionElem → Bool
  | [], _ => true
  | _ :: _, [] => false
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

/-- Independent $M_{\text{ref}}$ tuple-type predicate. -/
noncomputable def refIsTupleTy : MirTy → Bool
  | .tuple _ => true
  | _ => false

/-- Independent $M_{\text{ref}}$ fail-closed aliasing guard for `.Assign`:
rejects `Rvalue.Use` on a tuple destination whose operand overlaps `dst`
(in-memory `copy_nonoverlapping` UB on `BackendRepr::Memory` or padded
`ScalarPair` tuples) and `Rvalue.Aggregate .Tuple` where any operand overlaps
`dst` (`write_aggregate` / `rust-lang/rust#68364` overlap UB). -/
noncomputable def refAssignHasUnsupportedOverlap (dst : Miri.MIR.Place)
    (dstTy : MirTy) : Miri.MIR.Rvalue → Bool
  | .Use opnd _ => refIsTupleTy dstTy && refOperandMayOverlapPlace dst opnd
  | .Aggregate .Tuple ops => refAnyOperandMayOverlapPlace dst ops.toList
  | _ => false

/-- `Miri.Interpreter.AggregateHooks` for `Miri.Interpreter.writeAggregate`
(`vendor/lean-miri/Miri/Interpreter/Aggregate.lean`), matching `write_aggregate`
in `compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "for (field_index, operand) in operands.iter_enumerated() {
>     let field_index = active_field_index.unwrap_or(field_index);
>     let field_dest = self.project_field(&variant_dest, field_index)?;
>     let op = self.eval_operand(operand, Some(field_dest.layout))?;
>     ...
>     self.copy_op_no_validate(&op, &field_dest, /*allow_transmute*/ false)?;
> }
> self.write_discriminant(variant_index, dest)?;
> ...
> if M::enforce_validity(self, dest.layout()) {
>     self.validate_place(
>         dest,
>         M::enforce_validity_recursively(self, dest.layout()),
>         /*reset_provenance_and_padding*/ true,
>     )?;
> }"

Each field iteration projects `dest.projection ++ [.Field fieldIdx 0]`,
evaluates the operand via `evalRefMiriOperandToSlot`, checks static type
equality (`MirTy.beq`), enforces uninitialized-field validation UB via
`SlotVal.toVal?` (since adapter frames never store `Immediate.uninit`; see
`slotToMiriLocalValue`), and writes the field immediately via `writeRefPlace`.
For an empty `.unit` tuple aggregate (`operands = #[]`), the loop runs zero
times and `writeDiscriminant` commits `Val.unit` via `writeRefPlace` (checking
destination liveness). -/
noncomputable def refAggregateHooks (types : List MirTy) :
    Miri.Interpreter.AggregateHooks (MirTy × SlotVal) (List RefLocalState)
      Unit RefDest := {
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  placeLayout := fun _ => refSizedLocalLayout
  evalOperand := fun _ mirOp _ s =>
    match evalRefMiriOperandToSlot types s mirOp with
    | .error k => .error (faultToStepError k) s
    | .ok (ty, sv, locals') =>
      .ok ⟨.immediate (payloadToMiriImmediate (ty, sv)),
          refSizedLocalLayout⟩
        locals'
  readPointer := fun _ _ s =>
    .error (.unsupported "raw pointer aggregate unsupported") s
  readScalar := fun _ _ s =>
    .error (.unsupported "raw pointer aggregate unsupported") s
  projectDowncast := fun _ _ _ s =>
    .error (.unsupported "ADT aggregate unsupported") s
  projectField := fun _ dest fieldIdx s =>
    match dest.ty with
    | .tuple fieldTys =>
      match MirSemantics.getElem? fieldTys fieldIdx with
      | some fieldTy =>
        .ok ⟨dest.localId, dest.projection ++ [.Field fieldIdx 0], fieldTy⟩ s
      | none => .error (.unsupported "aggregate field out of bounds") s
    | _ => .error (.unsupported "aggregate field on non-tuple") s
  copyOp := fun _ _ _ s =>
    .error (.unsupported "raw pointer aggregate copyOp unsupported") s
  copyOpNoValidate := fun _ op dest _ s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (srcTy, sv) =>
        if !(MirTy.beq srcTy dest.ty) then
          .error (.unsupported "aggregate field type mismatch") s
        else
          match sv.toVal? with
          | none =>
            .error (.undefinedBehavior "uninit aggregate field operand") s
          | some v =>
            match writeRefPlace s dest v with
            | .error k => .error (faultToStepError k) s
            | .ok locals' => .ok () locals'
      | none => .error (.invalidProgram "missing aggregate operand payload") s
    | .indirect _ =>
      .error (.unsupported "indirect aggregate operand unsupported") s
  writeDiscriminant := fun _ _ dest s =>
    match dest.ty with
    | .unit =>
      match writeRefPlace s dest .unit with
      | .error k => .error (faultToStepError k) s
      | .ok locals' => .ok () locals'
    | .tuple _ => .ok () s
    | _ => .error (.unsupported "non-tuple aggregate destination") s
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

/-- `Miri.Interpreter.RvalueHooks` closing over only `types : List MirTy`,
instantiated with provenance carrier `MirTy × SlotVal`, state
`List RefLocalState`, and place value `RefDest` to drive real
`Miri.MIR.Rvalue`, `Miri.MIR.Operand`, and `Miri.MIR.Place` terms through
`Miri.Interpreter.evalRvalueIntoPlace` and `Miri.Interpreter.Discriminant`
(`vendor/lean-miri/Miri/Interpreter/{Rvalue,Discriminant}.lean`).

Destination places: `evalPlace` reads the destination local's cached type and
applies the destination projection to it (`refProjectTy?`), so the `RefDest`
that it returns carries the type of the part being assigned. A missing local
or a projection that does not apply fails closed (`.fault .unsupported`)
before the rvalue is evaluated.

Value and type transport: `evalOperand` and `evalPlaceToOp` embed
`(MirTy, SlotVal)` directly into Miri's `Immediate (MirTy × SlotVal)` carrier
via `payloadToMiriImmediate`; `readImmediate`, `copyOp`, `binaryOp`, `unaryOp`,
`cast`, `readDiscriminant`, and `writeImmediate` decode the `Immediate` /
`OpTy` arguments Miri passes them via `miriImmediateToPayload?`, reading the
carried contents as a value with `SlotVal.toVal?`; `copyOp` checks `MirTy.beq`
and commits to `dest : RefDest` via `writeRefPlace`; and `writeImmediate`
discards the `MirTy` tag carried in the `Immediate` payload (so the result
`MirTy` tags attached by `binaryOp`, `unaryOp`, and `discriminantForVariant`
are unconsumed, and `assertRvalueLayout` over constant `refSizedLocalLayout` is
vacuous) and relies on `writeRefPlace` (`checkRefVal`) as the effective
result-type check against `dest.ty`. For `.Discriminant`, `evalPlaceToOp`
carries the enum's real `RefProg.types` index in `op.layout.ty`,
`readDiscriminant` re-encodes the decoded enum payload at
`Miri.Memory.Provenance` via `encodeRefEnumTagOp`, and `discriminantForVariant`
resolves `types[ty]?` from Miri's forwarded `ty` parameter before calling
`Miri.Interpreter.Discriminant.discriminantForVariant` at the closed hook's
private `TyId 0`—so the rvalue state is plain `List RefLocalState` with no
call-order side-channel fields.

Casts: `cast` reads the operand as a primitive (`readRefPrimitiveSlot`),
accepts only `Miri.MIR.CastKind.IntToInt`, resolves the target type
`types[ty]?`, requires it to equal `dest.ty`, and converts the value with
`evalRefMiriIntToIntCast` (`Miri.Interpreter.IntegerCast.cast`), following the
`Cast` arm of `eval_rvalue_into_place` and the `IntToInt` arm of `cast`:

> "Cast(cast_kind, ref operand, cast_ty) => {
>     let src = self.eval_operand(operand, None)?;
>     let cast_ty =
>         self.instantiate_from_current_frame_and_normalize_erasing_regions(
>             cast_ty)?;
>     self.cast(&src, cast_kind, cast_ty, &dest)?;
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)
>
> "CastKind::IntToInt | CastKind::IntToFloat => {
>     let src = self.read_immediate(src)?;
>     let res = self.int_to_int_or_float(&src, cast_layout)?;
>     self.write_immediate(*res, dest)?;
> }"
> (`compiler/rustc_const_eval/src/interpret/cast.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Tuple aggregates: `writeAggregate` accepts only `Miri.MIR.AggregateKind.Tuple`
with matching operand/destination arity (`operands = #[]` at `.unit` or
non-empty `operands` matching `.tuple fieldTys`) and delegates field-by-field
projection, operand evaluation, field writes, and `writeDiscriminant` directly
to `Miri.Interpreter.writeAggregate` (`refAggregateHooks`), matching
`write_aggregate` in `rustc@8144389c` and
`Trusted.MirSemantics.writeAggregateTuple`.

Hook coverage: `.use`, `.binaryOp`, `.unaryOp`, `.discriminant`, `.cast`, and
`.aggregateTuple` exercise `evalPlace`, `placeLayout`, `evalOperand`,
`evalPlaceToOp`, `readImmediate`, `copyOp`, `binaryOp`, `unaryOp`, `normalize`,
`cast`, `writeAggregate`, `readDiscriminant`, `discriminantForVariant`,
`writeImmediate`, and `withRetagMode`. `.ref` and `.addressOf` fail closed in
`forceAllocation` (after `placeBaseRaw` and `evalPlace`). The remaining
`RvalueHooks` fields (`writePointer`, `threadLocalPointer`,
`copyOpAllowTransmute`, `writeRepeat`, `toRef`, `enforceValidity`, and
`retagPtrValue`) are required by the `RvalueHooks` record but unreachable under
the `RefRvalue` fragment (`toRef`, `enforceValidity`, and `retagPtrValue` are
gated behind `forceAllocation`).

Uninitialized-read UB in `copyOp`: adapter frames never store
`Immediate.uninit` (see `slotToMiriLocalValue`), so `copyOp` itself rejects an
uninitialized `.use` operand (`sv.toVal? = none` faults with `.undefined`).
This Anneal-written rule matches `Rvalue::Use` in `rustc`, which copies the
operand with `copy_op`:

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
    Miri.Interpreter.RvalueHooks (MirTy × SlotVal) (List RefLocalState) Unit
      RefDest := {
  placeLayout := fun _ => refSizedLocalLayout
  evalPlace := fun _ place _ s =>
    match MirSemantics.getElem? s place.localId with
    | some ⟨_, some localTy⟩ =>
      match refProjectTy? types localTy place.projection.toList with
      | some ty => .ok ⟨place.localId, place.projection.toList, ty⟩ s
      | none => .error (.unsupported "unsupported place projection") s
    | _ => .error (.unsupported "missing destination local") s
  evalOperand := fun _ mirOp _ s =>
    match evalRefMiriOperandToSlot types s mirOp with
    | .error k => .error (faultToStepError k) s
    | .ok (ty, sv, locals') =>
      .ok ⟨.immediate (payloadToMiriImmediate (ty, sv)),
          refSizedLocalLayout⟩
        locals'
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
        match writeRefPlace s dest v with
        | .error k => .error (faultToStepError k) s
        | .ok locals' => .ok () locals'
      | none => .error (.invalidProgram "uninit rvalue result payload") s
    | none => .error (.invalidProgram "missing rvalue result payload") s
  writePointer := fun _ _ _ s =>
    .error (.unsupported "ThreadLocalRef unsupported") s
  threadLocalPointer := fun _ _ s =>
    .error (.unsupported "ThreadLocalRef unsupported") s
  withRetagMode := fun _ _ act => act
  copyOp := fun _ op dest s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (srcTy, sv) =>
        if !(MirTy.beq srcTy dest.ty) then
          .error (.unsupported "Use type mismatch") s
        else
          -- Uninitialized `.use` operands are UB (`copy_op` validation in
          -- `rustc@8144389c`; see the docstring above).
          match sv.toVal? with
          | none => .error (.undefinedBehavior "uninit Use operand") s
          | some v =>
            match writeRefPlace s dest v with
            | .error k => .error (faultToStepError k) s
            | .ok locals' => .ok () locals'
      | none => .error (.invalidProgram "missing Use operand payload") s
    | .indirect _ => .error (.unsupported "indirect Use operand") s
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
    match kind with
    | .Tuple =>
      let validShape : Bool :=
        match dest.ty with
        | .unit => Nat.beq operands.size 0
        | .tuple fieldTys =>
          !fieldTys.isEmpty && Nat.beq operands.size fieldTys.length
        | _ => false
      if !validShape then
        .error (.unsupported "tuple aggregate shape mismatch") s
      else
        Miri.Interpreter.writeAggregate (refAggregateHooks types) c kind
          operands dest s
    | _ => .error (.unsupported "non-tuple Aggregate unsupported") s
  writeRepeat := fun _ _ _ s =>
    .error (.unsupported "Repeat unsupported") s
  forceAllocation := fun _ _ s =>
    .error (.unsupported "Ref/RawPtr unsupported") s
  toRef := fun _ _ s =>
    .error (.unsupported "Ref/RawPtr unsupported") s
  enforceValidity := fun _ _ s => .ok false s
  retagPtrValue := fun _ _ _ s => .ok none s
  placeBaseRaw := fun _ _ s => .ok false s
  normalize := fun _ ty s => .ok ty s
  cast := fun _ src kind tyId dest s =>
    match src.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (srcTy, sv) =>
        match readRefPrimitiveSlot srcTy sv with
        | .error k => .error (faultToStepError k) s
        | .ok v =>
          match kind with
          | .IntToInt =>
            match MirSemantics.getElem? types tyId with
            | some castTy =>
              if !(MirTy.beq castTy dest.ty) then
                .error (.unsupported "Cast type mismatch") s
              else
                match evalRefMiriIntToIntCast v castTy with
                | .error k => .error (faultToStepError k) s
                | .ok res =>
                  match writeRefPlace s dest res with
                  | .error k => .error (faultToStepError k) s
                  | .ok locals' => .ok () locals'
            | none => .error (.unsupported "missing Cast target type") s
          | _ => .error (.unsupported "non-IntToInt Cast unsupported") s
      | none => .error (.invalidProgram "missing Cast operand payload") s
    | .indirect _ => .error (.unsupported "indirect Cast operand") s
  readDiscriminant := fun c op s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (.enum ety, sv) =>
        match encodeRefEnumTagOp ety sv with
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
            let sv : SlotVal :=
              .scalar ⟨ety.discrWidth, ety.discrSigned, sc.data⟩
            .ok ⟨payloadToMiriImmediate
                  (.int ety.discrWidth ety.discrSigned, sv),
                discr.layout⟩ s'
          | _ => .error (.invalidProgram "non-integer discriminant scalar") s'
        | _ => .error (.invalidProgram "non-scalar discriminant immediate") s'
    | _ =>
      .error (.invalidProgram "non-enum TyId in discriminantForVariant") s
}

/-- Reference rvalue evaluator over `Miri.MIR.Rvalue` and `Miri.MIR.Place`,
enforcing the fail-closed destination-overlap guard
(`refAssignHasUnsupportedOverlap`) for tuple `.Use` and `.Aggregate .Tuple`
before delegating destination place resolution, outer dispatch, left-to-right
operand sequencing, field-by-field tuple aggregates, operator dispatch,
discriminant reading, and destination writes to
`Miri.Interpreter.evalRvalueIntoPlace`, `Miri.Interpreter.writeAggregate`,
`Miri.Interpreter.Discriminant.{readDiscriminant, discriminantForVariant}`,
`Miri.Interpreter.placeWriteLocalImmediate`, and `Miri.Interpreter.runRvalue`
(`vendor/lean-miri/Miri/Interpreter/{Rvalue,Aggregate,Discriminant,Place}.lean`),
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
  match MirSemantics.getElem? rlocals dst.localId with
  | some ⟨_, some localTy⟩ =>
    match refProjectTy? types localTy dst.projection.toList with
    | some dstTy =>
      if refAssignHasUnsupportedOverlap dst dstTy mirRv then
        .error .unsupported
      else
        match Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace
              (refRvalueHooks types) () mirRv dst) rlocals with
        | (rlocals', .ok ()) => .ok rlocals'
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

/-- Machine state threaded through `Miri.Interpreter.Step.step`: holds the
active frame's `locals` (updated in place by `.Assign`, `.StorageLive`,
`.StorageDead`, `.SwitchInt` discriminant moves, and `.Assert` condition
moves) and an optional `terminal` outcome (set by `ControlHooks.copyReturn` on
a normal return and by `ControlHooks.cleanupFrame` when the entry frame
unwinds). -/
structure RefStepMachine where
  locals : List RefLocalState
  terminal : Option (StepResult RefState TerminalOut) := none

/-- Construct a single-frame `Miri.Interpreter.StepState` over `bbs` at
location `.mir ⟨blockIdx, 0⟩` with frame `cleanup` flag and initial
`locals := rlocals`. -/
noncomputable def mkRefStepStateWith (rlocals : List RefLocalState)
    (bbs : Array Miri.MIR.BasicBlock) (blockIdx : BasicBlockId)
    (cleanup : Bool) :
    Miri.Interpreter.StepState SlotVal Miri.Interpreter.LocalLayout Unit
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
    Miri.Interpreter.StepState SlotVal Miri.Interpreter.LocalLayout Unit
      RefStepMachine :=
  mkRefStepStateWith rlocals
    (Array.mk [{ refDummyMirBlock false with statements := Array.mk [stmt] }])
    0 false

/-- Minimal two-frame `Miri.Interpreter.StepState` at terminator position
(`statements := Array.empty`, `location := .mir ⟨0, 0⟩`) so
`Miri.Interpreter.Step.step` executes its `beforeTerminator` + `terminator`
(`Miri.Interpreter.ControlFlow.evalTerminator`) path.

The stack mirrors the reference stack `[sentinel, rframe]` that `evalRefStep`
requires: a caller frame beneath the executing entry frame. The entry frame's
return continuation is `.goto (some 0) .Continue`, the continuation of a callee
whose caller resumes at a block after a normal return and keeps unwinding
(`UnwindAction.Continue`) after an unwinding one. With the caller frame
present, `Miri.Interpreter.ControlFlow.returnFromCurrentFrame` can pop the
entry frame while unwinding; on a one-frame stack it would instead report
"unwinding past the topmost stack frame" as UB. The caller frame never
executes: `evalRefTerminator` ends the execution as soon as the entry frame is
popped. -/
noncomputable def mkRefTermStepState (rlocals : List RefLocalState)
    (term : Miri.MIR.Terminator) (cleanup : Bool) :
    Miri.Interpreter.StepState SlotVal Miri.Interpreter.LocalLayout Unit
      RefStepMachine := {
  stack := ⟨Array.mk [
    mkSingleLocalMiriFrame .dead false,
    { mkSingleLocalMiriFrame .dead cleanup with
      body := {
        refDummyMirBody cleanup with
        basicBlocks :=
          Array.mk [{ refDummyMirBlock cleanup with terminator := term }]
      }
      returnContinuation := .goto (some 0) .Continue
      location := .mir ⟨0, 0⟩ }]⟩
  machine := { locals := rlocals }
}

/-- Minimal `Miri.Interpreter.StepState` with `basicBlocks := Array.empty` at
location `.mir ⟨blockIdx, 0⟩`. Because `basicBlocks` is empty,
`Miri.Interpreter.Step.step` always takes its out-of-bounds `.invalidBlock`
error path here (making the fallback `_ => .ub` arm in `evalRefStep`
unreachable). -/
noncomputable def mkRefInvalidBlockStepState (rlocals : List RefLocalState)
    (blockIdx : BasicBlockId) :
    Miri.Interpreter.StepState SlotVal Miri.Interpreter.LocalLayout Unit
      RefStepMachine :=
  mkRefStepStateWith rlocals Array.empty blockIdx false

/-- Extract the active `.mir loc` from the top frame of `st`, returning `none`
on an empty stack or `.unwinding` frame. -/
noncomputable def extractMirLocation? {M : Type}
    (st : Miri.Interpreter.StepState SlotVal
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

/-- Map `Trusted.MirAst.UnwindAction` to `Miri.MIR.UnwindAction`.
`.terminate` maps to `.Terminate .Abi`; the reference machine rejects every
`.Terminate` reason in `refControlHooksFor.unwindTerminate`. -/
noncomputable def toMiriUnwindAction : UnwindAction → Miri.MIR.UnwindAction
  | .continue_ => .Continue
  | .cleanup target => .Cleanup target
  | .unreachable => .Unreachable
  | .terminate => .Terminate .Abi

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
`Miri.Interpreter.Step.step` and
`Miri.Interpreter.ControlFlow.evalTerminator`.

- `.goto`, `.return_`, `.unreachable`, `.unwindResume`, `.switchInt`, and
  `.assert` translate to their corresponding `Miri.MIR.TerminatorKind`
  constructors. For `.switchInt`, each `BitVec 128` case literal is encoded
  losslessly as `caseBits.toNat` in `Miri.MIR.SwitchTarget.Case`, driving
  `evalDiscriminant`, `compareSwitchCase`, and `ControlFlow.goToBlock`. For
  `.assert`, the condition, expected value, message (`toMiriAssertKind`),
  target, and unwind action (`toMiriUnwindAction`) drive `readAssertCondition`,
  `assertPanic`, and `ControlFlow.goToBlock`.
- The unmodeled terminators `.call` and `.unsupported` route to the fail-closed
  sentinel `.UnwindTerminate .Abi` (firing `unwindTerminate` -> `.fault
  .unsupported`). Routing `.call` directly would only construct unused
  placeholder callee fields before `call` fails closed. -/
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
  | .call _ _ _ _ _ | .unsupported =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .UnwindTerminate .Abi }

/-- `Miri.Interpreter.ControlHooks` for
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame` and
`Miri.Interpreter.ControlFlow.unwindToBlock`: the frame-popping half of
`refTerminatorHooksFor`, shared with `refStepHooksFor.returnFromCurrentFrame`.

`popFrame` pops the executing entry frame with
`Miri.Interpreter.Stack.popFrame`. Because the reference machine executes
only the entry function, popping its frame ends the execution, and the two
hooks that run after the pop record how it ended in `RefStepMachine.terminal`:

- `copyReturn` (normal return) reads the return place `_0` and records
  `.done (.returned ⟨retVal, callerMem⟩)`.
- `cleanupFrame` with `unwinding = true` records
  `.done (.unwound callerMem)`: the panic leaves the entry function.

Uninitialized-read UB in `copyReturn`: adapter frames never store
`Immediate.uninit` (see `slotToMiriLocalValue`), so `copyReturn` itself
rejects an uninitialized return place `_0` (contents with
`sv.toVal? = none` fault with `.undefined`; so does a dead `_0`, matching
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
at `refRvalueHooks`).

`unwindTerminate` fails closed (`.fault .unsupported`): aborting the process
is unmodeled. -/
noncomputable def refControlHooksFor (callerMem : CallerMemory) :
    Miri.Interpreter.ControlHooks SlotVal Miri.Interpreter.LocalLayout
      Unit RefStepMachine Unit Unit := {
  bodySpan := fun _ => .ok ⟨0⟩
  returnOperand := fun _ st => (st, .ok ())
  popFrame := fun _ st =>
    match st.stack.popFrame with
    | .ok (stack', frame) => ({ st with stack := stack' }, .ok frame)
    | .error e => (st, .error (.stack e))
  copyReturn := fun _ _ _ st =>
    -- An uninitialized `_0` is UB (`copy_op_allow_transmute` validation in
    -- `rustc@8144389c`; see the docstring above).
    match MirSemantics.getElem? st.machine.locals 0 with
    | some ⟨.live sv, some _⟩ =>
      match sv.toVal? with
      | some retVal =>
        ({ st with machine := { st.machine with
            terminal := some (.done (.returned ⟨retVal, callerMem⟩)) } },
          .ok ())
      | none => (st, .error (.undefinedBehavior "uninit return place"))
    | some ⟨.dead, some _⟩ =>
      (st, .error (.undefinedBehavior "dead return place"))
    | _ => (st, .error (.unsupported "missing return place"))
  cleanupFrame := fun _ unwinding _ st =>
    if unwinding then
      ({ st with machine := { st.machine with
          terminal := some (.done (.unwound callerMem)) } }, .ok .normal)
    else
      (st, .ok .normal)
  unwindTerminate := fun _ _ st =>
    (st, .error (.unsupported "UnwindTerminate unsupported"))
}

/-- `Miri.Interpreter.TerminatorHooks` for
`Miri.Interpreter.ControlFlow.evalTerminator`, extending the frame-popping
hooks `refControlHooksFor`.

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

`Assert`: `readAssertCondition` evaluates the condition operand like
`evalDiscriminant` and requires a `bool` (`.fault .unsupported` otherwise).
`ignoreOptionalOverflowChecks` is `false`, so
`Miri.Interpreter.ControlFlow.evalTerminator` never skips a check (see
`Trusted.MirAst.TerminatorKind` for the producer obligation in sessions that
disable overflow checks). When the condition differs from the expected value,
`evalTerminator` calls `assertPanic`, which rejects a message that carries an
operand (`refIsOperandFreeAssertKind`) and otherwise starts unwinding with
`Miri.Interpreter.ControlFlow.unwindToBlock`, matching `eval_terminator` in
`compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

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

`assertPanic` abstracts the panic runtime between the failed assertion and the
start of unwinding. Miri's `assert_panic` calls the panic lang item with
`ReturnContinuation::Goto { ret: None, unwind }` (quoted at
`Trusted.MirSemantics.isOperandFreeAssertKind`), and the unwinding that the
panic starts reaches the asserting frame along `unwind`. `assertPanic` applies
`unwind` to the asserting frame directly and assumes the `unwind` panic
strategy, like `Trusted.MirSemantics.evalTerminator`.

Hook coverage: `.return_` and `.unwindResume` exercise `bodySpan`,
`returnOperand`, `popFrame`, `copyReturn`, and `cleanupFrame`; `.switchInt`
exercises `evalDiscriminant` and `compareSwitchCase`; `.assert` exercises
`ignoreOptionalOverflowChecks`, `readAssertCondition`, and `assertPanic`; and
`.call` and `.unsupported` route through `.UnwindTerminate .Abi` and fail
closed in `unwindTerminate`. The remaining `TerminatorHooks` fields (`call`,
`tailCall`, and `drop`) are required by the record, fail closed, and are
unreachable under the `RefTerminatorKind` fragment. -/
noncomputable def refTerminatorHooksFor (types : List MirTy)
    (callerMem : CallerMemory) :
    Miri.Interpreter.TerminatorHooks SlotVal Miri.Interpreter.LocalLayout
      Unit RefStepMachine Unit Unit Val := {
  toControlHooks := refControlHooksFor callerMem
  evalDiscriminant := fun _ op st =>
    match evalRefMiriOperandToSlot types st.machine.locals op with
    | .error k => (st, .error (faultToStepError k))
    | .ok (ty, sv, rlocalsAfterDiscr) =>
      match readRefPrimitiveSlot ty sv with
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
  call := fun _ _ st => (st, .error (.unsupported "Call unsupported"))
  tailCall := fun _ _ st => (st, .error (.unsupported "TailCall unsupported"))
  drop := fun _ _ _ _ st => (st, .error (.unsupported "Drop unsupported"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ op st =>
    match evalRefMiriOperandToSlot types st.machine.locals op with
    | .error k => (st, .error (faultToStepError k))
    | .ok (ty, sv, rlocalsAfterCond) =>
      match readRefPrimitiveSlot ty sv with
      | .error k => (st, .error (faultToStepError k))
      | .ok condVal =>
        match condVal with
        | .bool b =>
          ({ st with machine :=
              { st.machine with locals := rlocalsAfterCond } },
            .ok b)
        | _ => (st, .error (.unsupported "non-bool Assert condition"))
  assertPanic := fun c msg unwind st =>
    if !refIsOperandFreeAssertKind msg then
      (st, .error (.unsupported "Assert message operands unsupported"))
    else
      Miri.Interpreter.ControlFlow.unwindToBlock (refControlHooksFor callerMem)
        c unwind st
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

Hook coverage: `.assign`, `.storageLive`, `.storageDead`, `.unsupported`
(via `.Intrinsic (.Assume ...)`), and terminators exercise `assign`,
`storageLive`, `storageDead`, `intrinsic`, `beforeTerminator`, and `terminator`.
`returnFromCurrentFrame` runs when `Miri.Interpreter.Step.step` steps a frame
whose location is `.unwinding` (the second step of `evalRefTerminator` after a
failed `Assert` whose unwind action is `Continue`); it pops that frame with
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame` over
`refControlHooksFor`. The remaining `StepHooks` fields (`evalPlace`,
`writeDiscriminant`, and `incrementConstEvalCounter`) are required by the
record but unreachable under the `RefStatementKind` fragment (`evalPlace` and
`writeDiscriminant` fail closed). -/
noncomputable def refStepHooksFor (types : List MirTy)
    (callerMem : CallerMemory) :
    Miri.Interpreter.StepHooks SlotVal Miri.Interpreter.LocalLayout Unit
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
  returnFromCurrentFrame :=
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      (refControlHooksFor callerMem)
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
`SwitchInt` branch selection, `Assert` checking, `goToBlock` jumps, unwinding,
and frame popping to `Miri.Interpreter.Step.step`,
`Miri.Interpreter.ControlFlow.evalTerminator`,
`Miri.Interpreter.ControlFlow.goToBlock`,
`Miri.Interpreter.ControlFlow.unwindToBlock`, and
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
>         Assert { ref cond, expected, ref msg, target, unwind } => { ... }
>         ...
>         UnwindResume => {
>             ...
>             self.return_from_current_stack_frame(/* unwinding */ true)?;
>             return interp_ok(());
>         }
>         ...
>         Unreachable => throw_ub!(Unreachable),
>         ...
>     }
>     interp_ok(())
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

The terminator runs as one `Step.step` over the two-frame state
`mkRefTermStepState`. Its result is read in this order:

1. A recorded `RefStepMachine.terminal` outcome: the entry frame was popped by
   a normal return (`.done (.returned ...)`) or, for `UnwindResume` in a
   cleanup block, by an unwinding one (`.done (.unwound callerMem)`).
2. Otherwise a `.mir` location of the entry frame: the terminator jumped to
   that block (`Goto`, `SwitchInt`, a passing `Assert`, or a failing `Assert`
   whose unwind action is a cleanup block).
3. Otherwise the entry frame has started unwinding without a cleanup block (a
   failing `Assert` whose unwind action is `Continue` leaves its location as
   `.unwinding`). Miri pops such a frame on its next step, so the evaluator
   runs `Step.step` once more: `returnFromCurrentFrame` pops the entry frame
   and records `.done (.unwound callerMem)`. $M_{\text{anneal}}$ has no
   unwinding frame state, so both Miri steps form one reference step, matching
   the single `Trusted.MirSemantics.evalTerminator` step that ends in
   `.done (.unwound callerMem)`.

An error of either step is `.fault .undefined` when Miri reports UB and
`.fault .unsupported` otherwise. -/
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
      | none =>
        match Miri.Interpreter.Step.step
            (refStepHooksFor types callerMem) () st' with
        | (st'', .ok true) =>
          match st''.machine.terminal with
          | some res => res
          | none => .fault .unsupported
        | (_, .error (.undefinedBehavior _)) => .fault .undefined
        | (_, _) => .fault .unsupported
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
    isCallerSentinel := false }

/-- Lift an $M_{\text{anneal}}$ single-frame `StepResult` to
$M_{\text{ref}}$. -/
noncomputable def mapStepRes (bodyLocals : List MirTy) :
    StepResult State TerminalOut → StepResult RefState TerminalOut
  | .step { frames := [f'], callerMem := cm } =>
    .step { frames := [liftFrame bodyLocals f'], callerMem := cm }
  | .step { frames := _, callerMem := cm } =>
    .step { frames := [], callerMem := cm }
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

/-- Type of the entry function's return place `_0`, which types the caller
sentinel's destination slot (`callerSentinelFrame`). -/
noncomputable def entryRetTy? (p : Program) : Option MirTy :=
  match MirSemantics.getElem? p.bodies p.entryDefId with
  | some body => MirSemantics.getElem? body.locals 0
  | none => none

/-- Whole-state one-to-one simulation invariant between $M_{\text{anneal}}$ and
$M_{\text{ref}}$: constrains every field of `s` and `rs` (up to the explicit
step counters `rs.stepsExecuted` and `rs.maxSteps`), placing the fixed caller
sentinel for the entry function's return type beneath the lifted image of the
single $M_{\text{anneal}}$ frame executing `p.entryDefId`. -/
def SimulationInv (p : Program) (s : State) (rs : RefState) :
    Prop :=
  ∃ f : FrameState, ∃ rf : RefFrameState, ∃ retTy : MirTy,
    s.frames = [f] ∧
    rs.frames = [callerSentinelFrame retTy, rf] ∧
    rs.callerMem = s.callerMem ∧
    entryRetTy? p = some retTy ∧
    f.defId = p.entryDefId ∧
    FrameSimInv p f rf

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
    {f : FrameState} {rf : RefFrameState} {retTy : MirTy} {body : Body},
    decodeProg rp = some p →
    s.frames = [f] →
    rs.frames = [callerSentinelFrame retTy, rf] →
    rs.callerMem = s.callerMem →
    MirSemantics.getElem? p.bodies f.defId = some body →
    f.locals.length = body.locals.length →
    rf = liftFrame body.locals f →
    Nat.blt rs.stepsExecuted rs.maxSteps = true →
    ∀ (c : Choice),
      evalRefStep rp c rs =
        stepResultToRefOutcome (callerSentinelFrame retTy) rs.stepsExecuted
          rs.maxSteps (mapStepRes body.locals (evalStep p c s))

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

/-! ### Correspondence Canary Programs and Claims (`D6`–`D18`)

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
    (.returned ⟨.enumVal canarySingleZstEnumTy 0, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progZstSingleEnumImplicitRet) queryEmpty ∧
  RefBehavior (encodeProg progZstSingleEnumImplicitRet) queryEmpty
    (.returned ⟨.enumVal canarySingleZstEnumTy 0, ⟨[]⟩⟩) ∧
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

end Trusted.Correspondence
