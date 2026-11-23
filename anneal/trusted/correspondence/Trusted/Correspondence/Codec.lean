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
import Miri.MIR.Syntax
import Trusted.MirAst
import Trusted.MirModel

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Direct `Miri.MIR` Codec and Type Interning (`Trusted.Correspondence.Codec`)

Defines `MiriProg` directly over upstream `Miri.MIR.Body` and the total
canonical type-interning codec (`encodeToMiri` / `decodeProg`). Replaces any
intermediate shadow AST with direct 2-hop lowering `Trusted.MirAst.Program` →
`MiriProg`. Imports only `Init.*`, `Miri.MIR.Syntax`, `Trusted.MirAst`, and
`Trusted.MirModel`, never `Trusted.MirSemantics`.
-/

/-- Interned type-table index (`Miri.MIR.TyId`). -/
abbrev TyId := Nat

/-- Inert per-body metadata (`Body.isUnsafe` and `Body.identity`) not carried on
`Miri.MIR.Body`. Neither `initRefState` nor `evalRefStep` consults it. -/
structure MiriBodyMeta where
  isUnsafe : Bool := false
  identity : String := ""

/-- Direct `Miri.MIR.Body`-backed reference program paired with a single
canonical deduplicated `types : List MirTy` table indexed by `TyId`, inert
body metadata `bodyMeta`, target `pointerWidthBits`, `mirProfileVersion`, and
capture `scope`.

Every `TyId` in `MiriProg` resolves through `types[tyId]?`: `initRefState`
resolves the entry body's local declarations once and caches each local's
`LocalLayout` via `refLocalLayoutForTy` on the real `Miri.Interpreter.Frame`,
while `refExecutionConfig` resolves `TyId`s on demand through `resolveTy`
(`tyIdFor` / `auxTyCode` for built-in layouts such as `boolLayout` and
`usizeLayout`, and `refLocalLayoutForTy` for local, constant, and discriminant
queries). Each frame entry carries its `LocalLayout` pre-cached so
`OperandMachine.localToOp` never mutates `frame.locals` during read-only
accesses.

`pointerWidthBits` and `mirProfileVersion` carry `Program.pointerWidthBits` and
`Program.mirProfileVersion` across the codec so `initRefState` independently
rejects non-64-bit targets and unsupported MIR profile versions, matching
`Trusted.MirSemantics.initState`. `scope` and `bodyMeta` carry inert alignment
fields (`Program.scope`, `Body.isUnsafe`, `Body.identity`) and are never
consulted by `initRefState` or `evalRefStep`. -/
structure MiriProg where
  bodies : List Miri.MIR.Body
  bodyMeta : List MiriBodyMeta
  entryDefId : DefId := 0
  types : List MirTy
  pointerWidthBits : Nat
  mirProfileVersion : Nat
  scope : VerificationScope

/-! ## Canonical Type Interning (`collectProgTypes`) -/

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
  present in `(encodeToMiri p).types`. -/
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

/-! ## Operator and Primitive Bijections -/

/-- Map `Trusted.MirAst.UnOp` to `Miri.MIR.UnOp`. -/
noncomputable def toMiriUnOp : UnOp → Miri.MIR.UnOp
  | .not => .Not
  | .neg => .Neg
  | .ptrMetadata => .PtrMetadata

/-- Left inverse of `toMiriUnOp`. -/
noncomputable def fromMiriUnOp : Miri.MIR.UnOp → Option UnOp
  | .Not => some .not
  | .Neg => some .neg
  | .PtrMetadata => some .ptrMetadata

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
  | .cmp => .Cmp
  | .offset => .Offset

/-- Left inverse of `toMiriBinOp`. -/
noncomputable def fromMiriBinOp : Miri.MIR.BinOp → Option BinOp
  | .Add => some .add
  | .AddUnchecked => some .addUnchecked
  | .AddWithOverflow => some .addWithOverflow
  | .Sub => some .sub
  | .SubUnchecked => some .subUnchecked
  | .SubWithOverflow => some .subWithOverflow
  | .Mul => some .mul
  | .MulUnchecked => some .mulUnchecked
  | .MulWithOverflow => some .mulWithOverflow
  | .Div => some .div
  | .Rem => some .rem
  | .BitXor => some .bitXor
  | .BitAnd => some .bitAnd
  | .BitOr => some .bitOr
  | .Shl => some .shl
  | .ShlUnchecked => some .shlUnchecked
  | .Shr => some .shr
  | .ShrUnchecked => some .shrUnchecked
  | .Eq => some .eq
  | .Lt => some .lt
  | .Le => some .le
  | .Ne => some .ne
  | .Ge => some .ge
  | .Gt => some .gt
  | .Cmp => some .cmp
  | .Offset => some .offset

/-- Map `Trusted.MirAst.Mutability` to an integer tag. -/
noncomputable def mutabilityToNat : Mutability → Nat
  | .shared => 0
  | .mut => 1

/-- Left inverse of `mutabilityToNat`. -/
noncomputable def natToMutability : Nat → Option Mutability
  | 0 => some .shared
  | 1 => some .mut
  | _ => none

/-- Encode `Trusted.MirAst.AssertKind` directly inside `Miri.MIR.MirConst`. -/
noncomputable def encodeAssertConst : AssertKind → Miri.MIR.MirConst
  | .overflow op => .Ty 0 (.Expr (.Binop (toMiriBinOp op)) Array.empty)
  | .overflowNeg => .Ty 1 .Error
  | .divByZero => .Ty 2 .Error
  | .remByZero => .Ty 3 .Error
  | .boundsCheck => .Ty 4 .Error
  | .misalignedPtrDeref => .Ty 5 .Error
  | .nullPtrDeref => .Ty 6 .Error
  | .unsupported => .Ty 7 .Error

/-- Left inverse of `encodeAssertConst`. -/
noncomputable def decodeAssertConst : Miri.MIR.MirConst → Option AssertKind
  | .Ty 0 (.Expr (.Binop op) _) =>
    optMap AssertKind.overflow (fromMiriBinOp op)
  | .Ty 1 .Error => some .overflowNeg
  | .Ty 2 .Error => some .divByZero
  | .Ty 3 .Error => some .remByZero
  | .Ty 4 .Error => some .boundsCheck
  | .Ty 5 .Error => some .misalignedPtrDeref
  | .Ty 6 .Error => some .nullPtrDeref
  | .Ty 7 .Error => some .unsupported
  | _ => none

/-- Map `Trusted.MirAst.UnwindAction` to `Miri.MIR.UnwindAction`. -/
noncomputable def toMiriUnwindAction : UnwindAction → Miri.MIR.UnwindAction
  | .continue_ => .Continue
  | .unreachable => .Unreachable
  | .terminate => .Terminate .Abi
  | .cleanup bb => .Cleanup bb

/-- Left inverse of `toMiriUnwindAction`. -/
noncomputable def fromMiriUnwindAction :
    Miri.MIR.UnwindAction → Option UnwindAction
  | .Continue => some .continue_
  | .Unreachable => some .unreachable
  | .Terminate .Abi => some .terminate
  | .Cleanup bb => some (.cleanup bb)
  | .Terminate .InCleanup => none

/-! ## Direct 2-Hop Codec (`encodeToMiri` / `decodeProg`) -/

/-- Encode a `ProjectionElem` directly into `Miri.MIR.ProjectionElem` against
type table `ts`.

Notice `.field idx ty` encodes as `.ConstantIndex idx (lookupTyId ts ty) false`
(and `.unsupported` as `.PhantomDeref`) rather than `.Field`, because `Config`
implements `.Field` for valid discriminant/overflow-pair reads whereas Day-1
`Trusted.MirSemantics` rejects every non-empty place projection with
`.unsupported`. Every supported Day-1 `MirTy` has a non-array layout, so both
`OperandMachine.evalPlaceToOp` and `PlaceDynamic.evalPlace` reject
`.ConstantIndex`, `.Deref`, and `.PhantomDeref` fail-closed with
`.invalidProgram` or `.unsupported` (both mapped to `.blocked`) without
allocating or mutating memory. -/
noncomputable def encodeProjElem (ts : List MirTy) :
    ProjectionElem → Miri.MIR.ProjectionElem
  | .deref => .Deref
  | .field idx ty => .ConstantIndex idx (lookupTyId ts ty) false
  | .unsupported => .PhantomDeref

/-- Left inverse of `encodeProjElem`. -/
noncomputable def decodeProjElem (ts : List MirTy) :
    Miri.MIR.ProjectionElem → Option ProjectionElem
  | .Deref => some .deref
  | .ConstantIndex idx tyId false =>
    optMap (ProjectionElem.field idx) (MirSemantics.getElem? ts tyId)
  | .PhantomDeref => some .unsupported
  | _ => none

/-- Encode a `Place` directly into `Miri.MIR.Place` against type table
`ts`. -/
noncomputable def encodePlace (ts : List MirTy) (p : Place) : Miri.MIR.Place :=
  ⟨p.localId, Array.mk (p.projection.map (encodeProjElem ts))⟩

/-- Decode a `Miri.MIR.Place` against type table `ts`. -/
noncomputable def decodePlace (ts : List MirTy)
    (p : Miri.MIR.Place) : Option Place :=
  optMap (Place.mk p.localId)
    (mapOption (decodeProjElem ts) p.projection.toList)

/-- Encode a `ConstOperand` directly into `Miri.MIR.ConstOperand` against
type table `ts`. -/
noncomputable def encodeConstOperand (ts : List MirTy)
    (c : ConstOperand) : Miri.MIR.ConstOperand :=
  let cv : Miri.MIR.ConstValue :=
    match c.lit with
    | .scalar bits => .Scalar (.Int bits.toNat 16)
    | .zeroSized => .ZeroSized
  ⟨⟨0⟩, none, .Val cv (lookupTyId ts c.ty)⟩

/-- Left inverse of `encodeConstOperand` on `.Val (.Scalar (.Int _ 16) |
.ZeroSized)` constants. -/
noncomputable def decodeConstOperand (ts : List MirTy)
    (c : Miri.MIR.ConstOperand) : Option ConstOperand :=
  match c.value with
  | .Val (.Scalar (.Int bitsNat 16)) tyId =>
    optMap (fun ty => ⟨ty, .scalar (BitVec.ofNat 128 bitsNat)⟩)
      (MirSemantics.getElem? ts tyId)
  | .Val .ZeroSized tyId =>
    optMap (fun ty => ⟨ty, .zeroSized⟩) (MirSemantics.getElem? ts tyId)
  | _ => none

/-- Encode an `Operand` directly into `Miri.MIR.Operand` against type table
`ts`. -/
noncomputable def encodeOperand (ts : List MirTy) :
    Operand → Miri.MIR.Operand
  | .copy p => .Copy (encodePlace ts p)
  | .move p => .Move (encodePlace ts p)
  | .constant c => .Constant (encodeConstOperand ts c)

/-- Decode a `Miri.MIR.Operand` against type table `ts`. -/
noncomputable def decodeOperand (ts : List MirTy) :
    Miri.MIR.Operand → Option Operand
  | .Copy p => optMap Operand.copy (decodePlace ts p)
  | .Move p => optMap Operand.move (decodePlace ts p)
  | .Constant c => optMap Operand.constant (decodeConstOperand ts c)
  | .RuntimeChecks _ => none

/-- Prefix-free encoding of an `Operand` inside `List Miri.MIR.ProjectionElem`
for invertible `.CopyForDeref` transport of unmodeled Day-1 rvalues. Note
`encodeProjElem` never emits `.Downcast`, `.OpaqueCast`, `.UnwrapUnsafeBinder`,
or `.Subslice _ _ _`. -/
noncomputable def encodeOperandElems (ts : List MirTy) :
    Operand → List Miri.MIR.ProjectionElem
  | .copy p =>
    .OpaqueCast p.localId ::
      (p.projection.map (encodeProjElem ts) ++ [.Downcast none 0])
  | .move p =>
    .UnwrapUnsafeBinder p.localId ::
      (p.projection.map (encodeProjElem ts) ++ [.Downcast none 0])
  | .constant c =>
    match c.lit with
    | .scalar bits => [.Subslice (lookupTyId ts c.ty) bits.toNat true]
    | .zeroSized => [.Subslice (lookupTyId ts c.ty) 0 false]

/-- Encode a list of `Operand`s by concatenating prefix-free encodings. -/
noncomputable def encodeOperandListElems (ts : List MirTy) :
    List Operand → List Miri.MIR.ProjectionElem
  | [] => []
  | op :: ops => encodeOperandElems ts op ++ encodeOperandListElems ts ops

/-- Decode projection elements up to the terminating `.Downcast none 0`
sentinel. -/
noncomputable def decodeProjUntilStop (ts : List MirTy) :
    List Miri.MIR.ProjectionElem →
      Option (List ProjectionElem × List Miri.MIR.ProjectionElem)
  | [] => none
  | .Downcast none 0 :: rest => some ([], rest)
  | e :: rest =>
    match decodeProjElem ts e, decodeProjUntilStop ts rest with
    | some e', some (es, rem) => some (e' :: es, rem)
    | _, _ => none

/-- Decode one prefix-encoded `Operand` from `List Miri.MIR.ProjectionElem`. -/
noncomputable def decodeOperandElems (ts : List MirTy) :
    List Miri.MIR.ProjectionElem →
      Option (Operand × List Miri.MIR.ProjectionElem)
  | .OpaqueCast localId :: rest =>
    optMap (fun pair => (.copy ⟨localId, pair.1⟩, pair.2))
      (decodeProjUntilStop ts rest)
  | .UnwrapUnsafeBinder localId :: rest =>
    optMap (fun pair => (.move ⟨localId, pair.1⟩, pair.2))
      (decodeProjUntilStop ts rest)
  | .Subslice tyId bitsNat true :: rest =>
    optMap
      (fun ty =>
        (.constant ⟨ty, .scalar (BitVec.ofNat 128 bitsNat)⟩, rest))
      (MirSemantics.getElem? ts tyId)
  | .Subslice tyId _ false :: rest =>
    optMap (fun ty => (.constant ⟨ty, .zeroSized⟩, rest))
      (MirSemantics.getElem? ts tyId)
  | _ => none

/-- Fuel-bounded decoder for `encodeOperandListElems`. Passing `elems.length`
suffices because every encoded operand consumes at least one projection
element. -/
noncomputable def decodeOperandListLoop (fuel : Nat) (ts : List MirTy)
    (elems : List Miri.MIR.ProjectionElem) : Option (List Operand) :=
  match elems with
  | [] => some []
  | _ :: _ =>
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match decodeOperandElems ts elems with
      | some (op, rest) =>
        optMap (List.cons op) (decodeOperandListLoop fuel' ts rest)
      | none => none

/-- Encode an `Rvalue` directly into `Miri.MIR.Rvalue` against type table `ts`.

Day-1 unmodeled rvalues (`.cast .unsupported`, `.ref`, `.addressOf`,
`.aggregateTuple`, and `.unsupported`) encode into distinct, disjoint
`.CopyForDeref ⟨tag, ...⟩` payloads rather than `.Cast`/`.Ref`/`.RawPtr`/
`.Aggregate`, because `evalRvalueIntoPlace` evaluates operands or allocates
places before rejecting those forms whereas Day-1 `Trusted.MirSemantics` fails
immediately with `.unsupported`, and `evalRvalueIntoPlace` rejects every
`.CopyForDeref _` with `.invalidProgram` (mapped to `.blocked`) once the
destination place resolves. -/
noncomputable def encodeRvalue (ts : List MirTy) :
    Rvalue → Miri.MIR.Rvalue
  | .use op => .Use (encodeOperand ts op) .No
  | .binaryOp op lhs rhs =>
    .BinaryOp (toMiriBinOp op) (encodeOperand ts lhs)
      (encodeOperand ts rhs)
  | .unaryOp op opnd => .UnaryOp (toMiriUnOp op) (encodeOperand ts opnd)
  | .cast .intToInt opnd ty =>
    .Cast .IntToInt (encodeOperand ts opnd) (lookupTyId ts ty)
  | .discriminant p => .Discriminant (encodePlace ts p)
  | .unsupported => .CopyForDeref ⟨0, Array.empty⟩
  | .cast .unsupported opnd ty =>
    .CopyForDeref
      ⟨1, Array.mk (.OpaqueCast (lookupTyId ts ty) ::
        encodeOperandElems ts opnd)⟩
  | .ref m p =>
    .CopyForDeref
      ⟨2, Array.mk (.OpaqueCast (mutabilityToNat m) :: .Index p.localId ::
        p.projection.map (encodeProjElem ts))⟩
  | .addressOf m p =>
    .CopyForDeref
      ⟨3, Array.mk (.OpaqueCast (mutabilityToNat m) :: .Index p.localId ::
        p.projection.map (encodeProjElem ts))⟩
  | .aggregateTuple ops =>
    .CopyForDeref ⟨4, Array.mk (encodeOperandListElems ts ops)⟩

/-- Decode unmodeled `.CopyForDeref` encodings back to `Trusted.MirAst.Rvalue`.
-/
noncomputable def decodeCopyForDeref (ts : List MirTy) :
    Miri.MIR.Place → Option Rvalue
  | ⟨0, elems⟩ => if elems.isEmpty then some .unsupported else none
  | ⟨1, elems⟩ =>
    match elems.toList with
    | .OpaqueCast tyId :: opElems =>
      match decodeOperandElems ts opElems, MirSemantics.getElem? ts tyId with
      | some (op', []), some ty => some (.cast .unsupported op' ty)
      | _, _ => none
    | _ => none
  | ⟨2, elems⟩ =>
    match elems.toList with
    | .OpaqueCast mCode :: .Index localId :: projElems =>
      optMap2 (fun m proj => .ref m ⟨localId, proj⟩)
        (natToMutability mCode) (mapOption (decodeProjElem ts) projElems)
    | _ => none
  | ⟨3, elems⟩ =>
    match elems.toList with
    | .OpaqueCast mCode :: .Index localId :: projElems =>
      optMap2 (fun m proj => .addressOf m ⟨localId, proj⟩)
        (natToMutability mCode) (mapOption (decodeProjElem ts) projElems)
    | _ => none
  | ⟨4, elems⟩ =>
    let xs := elems.toList
    optMap Rvalue.aggregateTuple (decodeOperandListLoop xs.length ts xs)
  | _ => none

/-- Left inverse of `encodeRvalue`. -/
noncomputable def decodeRvalue (ts : List MirTy) :
    Miri.MIR.Rvalue → Option Rvalue
  | .Use op .No => optMap Rvalue.use (decodeOperand ts op)
  | .BinaryOp op lhs rhs =>
    match fromMiriBinOp op, decodeOperand ts lhs, decodeOperand ts rhs with
    | some op', some lhs', some rhs' => some (.binaryOp op' lhs' rhs')
    | _, _, _ => none
  | .UnaryOp op opnd =>
    match fromMiriUnOp op, decodeOperand ts opnd with
    | some op', some opnd' => some (.unaryOp op' opnd')
    | _, _ => none
  | .Cast .IntToInt opnd tyId =>
    optMap2 (Rvalue.cast .intToInt) (decodeOperand ts opnd)
      (MirSemantics.getElem? ts tyId)
  | .Discriminant p => optMap Rvalue.discriminant (decodePlace ts p)
  | .CopyForDeref pl => decodeCopyForDeref ts pl
  | _ => none

/-- Encode a `StatementKind` directly into `Miri.MIR.StatementKind` against
type table `ts`. `.unsupported` lowers to `.Intrinsic (.Assume (.RuntimeChecks
.UbChecks))`, which `Config`'s `refOperandLeaves.runtimeChecks` rejects
immediately with `.unsupported` without touching `body.locals` or colliding
with `.Assign` or `.Nop`. -/
noncomputable def encodeStmt (ts : List MirTy) :
    StatementKind → Miri.MIR.StatementKind
  | .assign dst rv => .Assign (encodePlace ts dst) (encodeRvalue ts rv)
  | .storageLive id => .StorageLive id
  | .storageDead id => .StorageDead id
  | .nop => .Nop
  | .unsupported => .Intrinsic (.Assume (.RuntimeChecks .UbChecks))

/-- Left inverse of `encodeStmt`. -/
noncomputable def decodeStmt (ts : List MirTy) :
    Miri.MIR.StatementKind → Option StatementKind
  | .Assign dst rv =>
    optMap2 StatementKind.assign (decodePlace ts dst) (decodeRvalue ts rv)
  | .StorageLive id => some (.storageLive id)
  | .StorageDead id => some (.storageDead id)
  | .Nop => some .nop
  | .Intrinsic (.Assume (.RuntimeChecks .UbChecks)) => some .unsupported
  | _ => none

/-- Encode `SwitchTargets` into `Miri.MIR.SwitchTargets`. -/
noncomputable def encodeSwitchTargets (targets : SwitchTargets) :
    Miri.MIR.SwitchTargets :=
  { cases := Array.mk (targets.branches.map (fun b => .Case b.1.toNat b.2))
    otherwise := targets.otherwise }

/-- Decode `Miri.MIR.SwitchTargets` back to `Trusted.MirAst.SwitchTargets`. -/
noncomputable def decodeSwitchTargets (targets : Miri.MIR.SwitchTargets) :
    SwitchTargets :=
  { branches := targets.cases.toList.map
      (fun c => match c with | .Case bits target => (BitVec.ofNat 128 bits, target))
    otherwise := targets.otherwise }

/-- Default `Miri.MIR.InlineAsmOptions` used for invertible `.InlineAsm`
transport of `.call` terminators. -/
noncomputable def defaultInlineAsmOptions : Miri.MIR.InlineAsmOptions :=
  ⟨false, false, false, false, false, false, false, false, false⟩

/-- Encode a `TerminatorKind` directly into `Miri.MIR.TerminatorKind` against
type table `ts`. Day-1 unmodeled terminators encode into disjoint terminators
(`.FalseEdge`, `.InlineAsm`, `.CoroutineDrop`) that
`ControlFlow.evalTerminator` rejects immediately with `.unsupported` /
`.invalidProgram` (`.blocked`) before evaluating operands or unwinding. -/
noncomputable def encodeTerminator (ts : List MirTy) :
    TerminatorKind → Miri.MIR.TerminatorKind
  | .goto t => .Goto t Array.empty
  | .switchInt d targets =>
    .SwitchInt (encodeOperand ts d) (encodeSwitchTargets targets)
  | .return_ => .Return
  | .unreachable => .Unreachable
  | .unwindResume => .FalseEdge 0 0
  | .assert c exp msg t u =>
    .InlineAsm
      { asmMacro := .NakedAsm
        template := Array.empty
        operands := Array.mk
          [ .In (.Reg .X86 "") (encodeOperand ts c)
          , .Const ⟨⟨0⟩, none, encodeAssertConst msg⟩ ]
        options := { defaultInlineAsmOptions with pure := exp }
        lineSpans := Array.empty
        targets := Array.mk [t]
        unwind := toMiriUnwindAction u }
  | .call callee args dst t u =>
    .InlineAsm
      { asmMacro := .Asm
        template := Array.empty
        operands := Array.mk
          (.Out (.Reg .X86 "") false (some (encodePlace ts dst)) ::
            args.map (fun a => .In (.Reg .X86 "") (encodeOperand ts a)))
        options := defaultInlineAsmOptions
        lineSpans := Array.empty
        targets :=
          match t with
          | none => Array.mk [callee]
          | some target => Array.mk [callee, target]
        unwind := toMiriUnwindAction u }
  | .unsupported => .CoroutineDrop

/-- Decode call argument operands from `.InlineAsm` `.In` entries. -/
noncomputable def decodeCallArgs (ts : List MirTy) :
    List Miri.MIR.InlineAsmOperand → Option (List Operand)
  | [] => some []
  | .In (.Reg .X86 "") op :: rest =>
    optMap2 List.cons (decodeOperand ts op) (decodeCallArgs ts rest)
  | _ => none

/-- Left inverse of `encodeTerminator`. -/
noncomputable def decodeTerminator (ts : List MirTy) :
    Miri.MIR.TerminatorKind → Option TerminatorKind
  | .Goto t _ => some (.goto t)
  | .SwitchInt d targets =>
    optMap (fun d' => .switchInt d' (decodeSwitchTargets targets))
      (decodeOperand ts d)
  | .Return => some .return_
  | .Unreachable => some .unreachable
  | .FalseEdge 0 0 => some .unwindResume
  | .InlineAsm asm =>
    match asm.asmMacro with
    | .NakedAsm =>
      match asm.operands.toList, asm.targets.toList,
          fromMiriUnwindAction asm.unwind with
      | [.In (.Reg arch reg) c, .Const ⟨_, _, mc⟩], [t], some u =>
        if (arch == .X86 && reg == "") = true then
          optMap2 (fun c' msg => .assert c' asm.options.pure msg t u)
            (decodeOperand ts c) (decodeAssertConst mc)
        else none
      | _, _, _ => none
    | .Asm =>
      match asm.operands.toList, asm.targets.toList,
          fromMiriUnwindAction asm.unwind with
      | .Out (.Reg arch reg) false (some dst) :: argOps, [callee], some u =>
        if (arch == .X86 && reg == "") = true then
          optMap2 (fun args' dst' => .call callee args' dst' none u)
            (decodeCallArgs ts argOps) (decodePlace ts dst)
        else none
      | .Out (.Reg arch reg) false (some dst) :: argOps,
          [callee, target], some u =>
        if (arch == .X86 && reg == "") = true then
          optMap2 (fun args' dst' => .call callee args' dst' (some target) u)
            (decodeCallArgs ts argOps) (decodePlace ts dst)
        else none
      | _, _, _ => none
  | .CoroutineDrop => some .unsupported
  | _ => none

/-- Encode a `BasicBlock` directly into `Miri.MIR.BasicBlock`. -/
noncomputable def encodeBasicBlock (ts : List MirTy)
    (bb : BasicBlock) : Miri.MIR.BasicBlock :=
  { statements := Array.mk (bb.statements.map (fun s =>
      { sourceInfo := ⟨⟨0⟩, 0⟩, kind := encodeStmt ts s }))
    terminator := { sourceInfo := ⟨⟨0⟩, 0⟩,
                    kind := encodeTerminator ts bb.terminator }
    cleanup := bb.cleanup }

/-- Decode a `Miri.MIR.BasicBlock` against type table `ts`. -/
noncomputable def decodeBasicBlock (ts : List MirTy)
    (bb : Miri.MIR.BasicBlock) : Option BasicBlock :=
  optMap2 (fun stmts term => ⟨stmts, term, bb.cleanup⟩)
    (mapOption (fun st => decodeStmt ts st.kind) bb.statements.toList)
    (decodeTerminator ts bb.terminator.kind)

/-- Resolve a list of `TyId` local declarations against type table `ts`. -/
noncomputable def decodeLocalTys (ts : List MirTy) :
    List TyId → Option (List MirTy) :=
  mapOption (MirSemantics.getElem? ts)

/-- Encode a `Body` directly into `Miri.MIR.Body` (`Runtime(PostCleanup)`
phase). -/
noncomputable def encodeBody (ts : List MirTy) (b : Body) : Miri.MIR.Body :=
  { phase := .Runtime .PostCleanup
    argumentCount := b.argumentCount
    spreadArgument := none
    locals := Array.mk (b.locals.map (lookupTyId ts))
    basicBlocks := Array.mk (b.basicBlocks.map (encodeBasicBlock ts)) }

/-- Extract inert body metadata `(isUnsafe, identity)` for `MiriProg`. -/
noncomputable def encodeBodyMeta (b : Body) : MiriBodyMeta :=
  ⟨b.isUnsafe, b.identity⟩

/-- Decode a `Miri.MIR.Body` paired with its `MiriBodyMeta` against type table
`ts`, rejecting non-`Runtime(PostCleanup)` bodies or populated
`spreadArgument`. -/
noncomputable def decodeBody (ts : List MirTy) (bm : MiriBodyMeta)
    (b : Miri.MIR.Body) : Option Body :=
  match b.phase, b.spreadArgument with
  | .Runtime .PostCleanup, none =>
    optMap2 (fun locals bbs =>
        ⟨b.argumentCount, locals, bbs, bm.isUnsafe, bm.identity⟩)
      (decodeLocalTys ts b.locals.toList)
      (mapOption (decodeBasicBlock ts) b.basicBlocks.toList)
  | _, _ => none

/-- Decode parallel lists of `Miri.MIR.Body` and `MiriBodyMeta` against type
table `ts`. -/
noncomputable def decodeBodies (ts : List MirTy) :
    List Miri.MIR.Body → List MiriBodyMeta → Option (List Body)
  | [], [] => some []
  | rb :: rbs, bm :: bms =>
    optMap2 List.cons (decodeBody ts bm rb) (decodeBodies ts rbs bms)
  | _, _ => none

/-- Total direct encoder from `Trusted.MirAst.Program` to `MiriProg` (carrying
`Miri.MIR.Body` directly, with no intermediate shadow AST). -/
noncomputable def encodeToMiri (p : Program) : MiriProg :=
  let ts := collectProgTypes p
  ⟨p.bodies.map (encodeBody ts),
   p.bodies.map encodeBodyMeta,
   p.entryDefId,
   ts,
   p.pointerWidthBits,
   p.mirProfileVersion,
   p.scope⟩

/-- Total left-inverse decoder inverting `encodeToMiri` (`∀ p, decodeProg
(encodeToMiri p) = some p`). -/
noncomputable def decodeProg (rp : MiriProg) : Option Program :=
  optMap (fun bodies =>
      ⟨bodies, rp.entryDefId, rp.pointerWidthBits, rp.mirProfileVersion,
       rp.scope⟩)
    (decodeBodies rp.types rp.bodies rp.bodyMeta)

end Trusted.Correspondence
