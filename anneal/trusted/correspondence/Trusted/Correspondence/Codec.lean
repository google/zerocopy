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
import Trusted.MirAst
import Trusted.MirModel

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Reference-Indexed MIR AST and Type Codec (`Trusted.Correspondence.Codec`)

Defines the `TyId`-indexed reference AST (`RefProg`) and total canonical type
interning codec (`encodeProg` / `decodeProg`). Imports only `Trusted.MirAst`
and `Trusted.MirModel`, never `Trusted.MirSemantics`.
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
  | cast (kind : CastKind) (opnd : RefOperand) (ty : TyId)
  | discriminant (place : RefPlace)
  | ref (mutability : Mutability) (place : RefPlace)
  | addressOf (mutability : Mutability) (place : RefPlace)
  | aggregateTuple (fields : List RefOperand)
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
each local's `LocalLayout` via `refLocalLayoutForTy` on the real
`Miri.Interpreter.Frame`, while `refExecutionConfig` resolves `TyId`s on demand
through `resolveTy` (`tyIdFor` / `auxTyCode` for built-in layouts such as
`boolLayout` and `usizeLayout`, and `refLocalLayoutForTy` for local, constant,
and discriminant queries). Each frame entry carries its `LocalLayout`
pre-cached so `OperandMachine.localToOp` never mutates `frame.locals` during
read-only accesses.

`pointerWidthBits`, `targetEndian`, and `mirProfileVersion` carry
`Program.pointerWidthBits`, `Program.targetEndian`, and
`Program.mirProfileVersion` across the codec so that `initRefState`
independently rejects non-64-bit targets and unsupported MIR profile versions,
matching `Trusted.MirSemantics.initState`, and `refExecutionConfig` /
`evalRefStep` configure `lean-miri`'s runtime target byte order from
`rp.targetEndian`. `scope` carries `Program.scope` for
structural round-trip alignment only and is inert in $M_{\text{ref}}$ (never
consulted by `initRefState` or `evalRefStep`). -/
structure RefProg where
  bodies : List RefBody
  entryDefId : DefId := 0
  types : List MirTy
  pointerWidthBits : Nat
  targetEndian : TargetEndian
  mirProfileVersion : Nat
  scope : VerificationScope

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
    | .char => insertTy .char acc
    | .ordering => insertTy .ordering acc
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
  | .cast _ op ty => collectTy (collectOperand acc op) ty
  | .discriminant p | .ref _ p | .addressOf _ p => collectPlace acc p
  | .aggregateTuple ops => ops.foldl collectOperand acc
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
  | .cast k opnd ty => .cast k (encodeOperand ts opnd) (lookupTyId ts ty)
  | .discriminant p => .discriminant (encodePlace ts p)
  | .ref m p => .ref m (encodePlace ts p)
  | .addressOf m p => .addressOf m (encodePlace ts p)
  | .aggregateTuple ops => .aggregateTuple (ops.map (encodeOperand ts))
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
   p.targetEndian, p.mirProfileVersion, p.scope⟩

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
  | .cast k opnd tyId =>
    optMap2 (Rvalue.cast k) (decodeOperand ts opnd)
      (MirSemantics.getElem? ts tyId)
  | .discriminant p => optMap Rvalue.discriminant (decodePlace ts p)
  | .ref m p => optMap (Rvalue.ref m) (decodePlace ts p)
  | .addressOf m p => optMap (Rvalue.addressOf m) (decodePlace ts p)
  | .aggregateTuple ops =>
    optMap Rvalue.aggregateTuple (mapOption (decodeOperand ts) ops)
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
      rp.targetEndian, rp.mirProfileVersion, rp.scope⟩)
    (mapOption (decodeBody rp.types) rp.bodies)

end Trusted.Correspondence
