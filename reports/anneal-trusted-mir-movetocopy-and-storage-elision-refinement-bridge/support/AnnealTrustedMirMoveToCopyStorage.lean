-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirSemantics

namespace VrustcFormal.F1_1b

open Trusted.MirAst Trusted.MirSemantics

/-!
# Direct `Trusted.MirSemantics` Bridge: `MoveToCopy` and `RemoveStorageMarkers` (`VrustcFormal.F1_1b`)

This module bridges verified MIR pre-normalization passes directly onto Anneal's
actual TCB syntax (`Trusted.MirAst`) and small-step operational semantics
(`Trusted.MirSemantics`, where `Operand.move` enforces `deinitMovedPlace = true`
and `StatementKind.storageLive`/`storageDead` govern local-slot liveness and
`hasStorageAnnotation` entry initialization).

All public theorem statements reference strictly `Init.*`, `Trusted.MirAst.*`,
`Trusted.MirSemantics.*`, and pure definitions in `VrustcFormal.F1_1b` (zero
surrogate MIR AST, zero `Anneal.*` dependencies in theorem types).

## Core Asymmetry Mechanized Directly on $M_{\text{anneal}}$

1. **Unconditional Forward Codegen Refinement (`pSrc → pTgt`):**
   - Rewriting any subset of `Operand.move p` occurrences to `Operand.copy p`
     (`isMoveToCopyProgram pSrc pTgt = true`), or eliding all in-bounds
     `StorageLive(id)` (`0 ≤ id < locals.length`) and non-return
     `StorageDead(id)` (`1 ≤ id < locals.length`) markers to `.nop`
     (`isRemoveStorageMarkersProgram pSrc pTgt = true`), **unconditionally**
     preserves `WellFormed`, exact finite `Behavior` (`↔`), infinite `Diverges`
     (`↔`), `SatisfiesPost`, and `BodyVerified` whenever `pSrc` is well-formed.
   - **Critical all-or-nothing invariant for `RemoveStorageMarkers`:** Partial
     elision that rewrites `StorageLive(id)` to `.nop` while retaining
     `StorageDead(id)` is **unsound** because `hasStorageAnnotation bTgt id`
     remains `true` (`initLocalsLoop` initializes `id` to `.dead`, causing
     subsequent assignments in `pTgt` to fault `.undefined`; locked by
     `ce_partial_storageLive_only_elision_unsound`).

2. **Certified Reverse Verification-Condition Transport (`pTgt → pSrc`):**
   - Unconditional reverse transport (`WellFormed pTgt q → WellFormed pSrc q`)
     is **false** for both passes on $M_{\text{anneal}}$ (locked by
     `ce_vc_transport_moveToCopy_unsound_without_cert`,
     `ce_vc_transport_storageDead_unsound_without_cert`, and
     `ce_storageLive_wipes_value_in_TrustedMir`).
   - Pairing `isMoveToCopyProgram` with `checkNoUseAfterMoveProgram` (or
     `isRemoveStorageMarkersProgram` with `checkStorageSafeProgram`) restores
     full **bidirectional** equivalence (`↔`) for `WellFormed`, `Behavior`,
     `ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and `BodyVerified`
     across **all** queries `q : Query` (even faulting or diverging queries).
-/

/-! ## Part I: Decidable Structural Rewrite Relations on `Trusted.MirAst.Program` -/

/-- Pairwise boolean relation over two lists of equal length. -/
noncomputable def listRel {α β : Type} (r : α → β → Bool) : List α → List β → Bool
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
def constLitEq : ConstLit → ConstLit → Bool
  | .scalar b₁, .scalar b₂ => b₁ == b₂
  | .zeroSized, .zeroSized => true
  | _, _ => false

/-- Structural equality on `ConstOperand`. -/
noncomputable def constOpEq (c₁ c₂ : ConstOperand) : Bool :=
  MirTy.beq c₁.ty c₂.ty && constLitEq c₁.lit c₂.lit

/-- Structural equality on `BinOp`. -/
def binOpEq : BinOp → BinOp → Bool
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
def unOpEq : UnOp → UnOp → Bool
  | .not, .not | .neg, .neg | .ptrMetadata, .ptrMetadata => true
  | _, _ => false

/-- Structural equality on `SwitchTargets`. -/
noncomputable def switchTargetsEq (t₁ t₂ : SwitchTargets) : Bool :=
  Nat.beq t₁.otherwise t₂.otherwise &&
    listRel (fun a b => (a.1 == b.1) && Nat.beq a.2 b.2) t₁.branches t₂.branches

/-- Structural equality on `UnwindAction`. -/
def unwindActionEq : UnwindAction → UnwindAction → Bool
  | .continue_, .continue_ | .unreachable, .unreachable | .terminate, .terminate => true
  | .cleanup b₁, .cleanup b₂ => Nat.beq b₁ b₂
  | _, _ => false

/-- Structural equality on `AssertKind`. -/
def assertKindEq : AssertKind → AssertKind → Bool
  | .overflow o₁, .overflow o₂ => binOpEq o₁ o₂
  | .overflowNeg, .overflowNeg | .divByZero, .divByZero | .remByZero, .remByZero
  | .boundsCheck, .boundsCheck | .misalignedPtrDeref, .misalignedPtrDeref
  | .nullPtrDeref, .nullPtrDeref | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `Option BasicBlockId`. -/
def optBlockEq : Option BasicBlockId → Option BasicBlockId → Bool
  | none, none => true
  | some b₁, some b₂ => Nat.beq b₁ b₂
  | _, _ => false

/-- Structural equality on `VerificationScope`. -/
def scopeEq : VerificationScope → VerificationScope → Bool
  | .unit, .unit | .crate, .crate => true
  | _, _ => false

/-- `MoveToCopy` operand relation: permits `.move p ↦ .copy p` (for identical
`p`) while preserving `.copy`, `.move`, and `.constant` otherwise. -/
noncomputable def isMoveToCopyOperand : Operand → Operand → Bool
  | .copy p₁, .copy p₂ => placeEq p₁ p₂
  | .move p₁, .move p₂ => placeEq p₁ p₂
  | .move p₁, .copy p₂ => placeEq p₁ p₂
  | .constant c₁, .constant c₂ => constOpEq c₁ c₂
  | _, _ => false

/-- Exact structural equality on `Operand` (used by `RemoveStorageMarkers`). -/
noncomputable def operandEq : Operand → Operand → Bool
  | .copy p₁, .copy p₂ => placeEq p₁ p₂
  | .move p₁, .move p₂ => placeEq p₁ p₂
  | .constant c₁, .constant c₂ => constOpEq c₁ c₂
  | _, _ => false

/-- Parametric `Rvalue` relation lifted from an operand relation `opRel`. -/
noncomputable def rvalueRel (opRel : Operand → Operand → Bool) : Rvalue → Rvalue → Bool
  | .use o₁, .use o₂ => opRel o₁ o₂
  | .binaryOp op₁ l₁ r₁, .binaryOp op₂ l₂ r₂ =>
    binOpEq op₁ op₂ && opRel l₁ l₂ && opRel r₁ r₂
  | .unaryOp op₁ o₁, .unaryOp op₂ o₂ => unOpEq op₁ op₂ && opRel o₁ o₂
  | .discriminant p₁, .discriminant p₂ => placeEq p₁ p₂
  | .ref m₁ p₁, .ref m₂ p₂ => Mutability.beq m₁ m₂ && placeEq p₁ p₂
  | .addressOf m₁ p₁, .addressOf m₂ p₂ => Mutability.beq m₁ m₂ && placeEq p₁ p₂
  | .aggregateTuple fs₁, .aggregateTuple fs₂ => listRel opRel fs₁ fs₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Parametric `TerminatorKind` relation lifted from `opRel`. -/
noncomputable def terminatorRel (opRel : Operand → Operand → Bool) :
    TerminatorKind → TerminatorKind → Bool
  | .goto t₁, .goto t₂ => Nat.beq t₁ t₂
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ => opRel d₁ d₂ && switchTargetsEq ts₁ ts₂
  | .return_, .return_ => true
  | .unreachable, .unreachable => true
  | .unwindResume, .unwindResume => true
  | .assert c₁ e₁ m₁ t₁ u₁, .assert c₂ e₂ m₂ t₂ u₂ =>
    opRel c₁ c₂ && (e₁ == e₂) && assertKindEq m₁ m₂ && Nat.beq t₁ t₂ && unwindActionEq u₁ u₂
  | .call f₁ as₁ d₁ t₁ u₁, .call f₂ as₂ d₂ t₂ u₂ =>
    Nat.beq f₁ f₂ && listRel opRel as₁ as₂ && placeEq d₁ d₂ &&
      optBlockEq t₁ t₂ && unwindActionEq u₁ u₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Statement-level `MoveToCopy` relation (all storage markers preserved). -/
noncomputable def isMoveToCopyStmt : StatementKind → StatementKind → Bool
  | .assign d₁ rv₁, .assign d₂ rv₂ =>
    placeEq d₁ d₂ && rvalueRel isMoveToCopyOperand rv₁ rv₂
  | .storageLive i₁, .storageLive i₂ => Nat.beq i₁ i₂
  | .storageDead i₁, .storageDead i₂ => Nat.beq i₁ i₂
  | .nop, .nop => true
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Block-level `MoveToCopy` relation. -/
noncomputable def isMoveToCopyBlock (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel isMoveToCopyStmt b₁.statements b₂.statements &&
    terminatorRel isMoveToCopyOperand b₁.terminator b₂.terminator

/-- Body-level `MoveToCopy` relation. -/
noncomputable def isMoveToCopyBody (b₁ b₂ : Body) : Bool :=
  Nat.beq b₁.argumentCount b₂.argumentCount &&
    MirTy.beqList b₁.locals b₂.locals &&
    (b₁.isUnsafe == b₂.isUnsafe) &&
    stringBeq b₁.identity b₂.identity &&
    listRel isMoveToCopyBlock b₁.basicBlocks b₂.basicBlocks

/-- Program-level `MoveToCopy` relation. -/
noncomputable def isMoveToCopyProgram (pSrc pTgt : Program) : Bool :=
  Nat.beq pSrc.pointerWidthBits pTgt.pointerWidthBits &&
    Nat.beq pSrc.mirProfileVersion pTgt.mirProfileVersion &&
    Nat.beq pSrc.entryDefId pTgt.entryDefId &&
    scopeEq pSrc.scope pTgt.scope &&
    listRel isMoveToCopyBody pSrc.bodies pTgt.bodies

/-- Statement-level `RemoveStorageMarkers` relation (matching `rustc`'s
`RemoveStorageMarkers` pass): rewrites every in-bounds `.storageLive id`
(`0 ≤ id < numLocals`) and every in-bounds non-return `.storageDead id`
(`1 ≤ id < numLocals`) to `.nop`, while preserving `.storageDead 0` and any
out-of-bounds markers so `.unsupported` faults cannot silently disappear. -/
noncomputable def isRemoveStorageMarkersStmt (numLocals : Nat) :
    StatementKind → StatementKind → Bool
  | .assign d₁ rv₁, .assign d₂ rv₂ =>
    placeEq d₁ d₂ && rvalueRel operandEq rv₁ rv₂
  | .storageLive id, .nop => Nat.blt id numLocals
  | .storageLive i₁, .storageLive i₂ => !Nat.blt i₁ numLocals && Nat.beq i₁ i₂
  | .storageDead id, .nop => !Nat.beq id 0 && Nat.blt id numLocals
  | .storageDead i₁, .storageDead i₂ =>
    (Nat.beq i₁ 0 || !Nat.blt i₁ numLocals) && Nat.beq i₁ i₂
  | .nop, .nop => true
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Block-level `RemoveStorageMarkers` relation. -/
noncomputable def isRemoveStorageMarkersBlock (numLocals : Nat)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (isRemoveStorageMarkersStmt numLocals) b₁.statements b₂.statements &&
    terminatorRel operandEq b₁.terminator b₂.terminator

/-- Body-level `RemoveStorageMarkers` relation. -/
noncomputable def isRemoveStorageMarkersBody (b₁ b₂ : Body) : Bool :=
  Nat.beq b₁.argumentCount b₂.argumentCount &&
    MirTy.beqList b₁.locals b₂.locals &&
    (b₁.isUnsafe == b₂.isUnsafe) &&
    stringBeq b₁.identity b₂.identity &&
    listRel (isRemoveStorageMarkersBlock b₁.locals.length) b₁.basicBlocks b₂.basicBlocks

/-- Program-level `RemoveStorageMarkers` relation. -/
noncomputable def isRemoveStorageMarkersProgram (pSrc pTgt : Program) : Bool :=
  Nat.beq pSrc.pointerWidthBits pTgt.pointerWidthBits &&
    Nat.beq pSrc.mirProfileVersion pTgt.mirProfileVersion &&
    Nat.beq pSrc.entryDefId pTgt.entryDefId &&
    scopeEq pSrc.scope pTgt.scope &&
    listRel isRemoveStorageMarkersBody pSrc.bodies pTgt.bodies

/-! ## Part II: Decidable CFG Abstract-Interpretation Certificate Checkers -/

/-- Whether `ty` is an inhabited 0-byte ZST whose `liveUninitSlot` is already
`.live (some _)` (`MirTy.unit` or an admitted 1-variant `.zeroSized` enum). -/
noncomputable def isAlwaysInhabitedZst (ty : MirTy) : Bool :=
  match ty with
  | .unit => true
  | .enum ety => isZstEnumTy ety
  | _ => false

/-- Three-state abstract local slot for `StorageSafe` & `NoUseAfterMove`
verification-condition transport:
- `liveInit`: slot is live and holds an identical initialized value in `pSrc`
  and `pTgt`.
- `liveUninit`: slot is live in both `pSrc` and `pTgt` (may be uninitialized in
  `pSrc`).
- `dead`: slot may be `.dead` in `pSrc` (all reads and writes forbidden). -/
inductive AbsSlot where
  | liveInit
  | liveUninit
  | dead

/-- Abstract-slot entailment (`exitSlot` is at least as initialized/live as
`entrySlot`): `.liveInit ⊑ .liveUninit ⊑ .dead`. -/
def absSlotImplies : AbsSlot → AbsSlot → Bool
  | _, .dead => true
  | .liveInit, .liveUninit => true
  | .liveUninit, .liveUninit => true
  | .liveInit, .liveInit => true
  | _, _ => false

/-- Pointwise entailment across local-variable abstract states. -/
noncomputable def absEnvImplies : List AbsSlot → List AbsSlot → Bool :=
  listRel absSlotImplies

/-- Per-body CFG certificate: optional abstract entry state per basic block
(`none` marks statically unreachable blocks; `some env` has length
`body.locals.length`). -/
abbrev BodyAbsCert := List (Option (List AbsSlot))

/-- Per-program CFG certificate: one `BodyAbsCert` per body in `p.bodies`. -/
abbrev ProgramAbsCert := List BodyAbsCert

/-- Entry abstract state for local `idx` of type `ty` in `body`, mirroring
`Trusted.MirSemantics.initLocalsLoop`. -/
noncomputable def initAbsSlot (body : Body) (idx : Nat) (ty : MirTy) : AbsSlot :=
  if Nat.beq idx 0 then
    if isAlwaysInhabitedZst ty then .liveInit else .liveUninit
  else if Nat.ble idx body.argumentCount then
    .liveInit
  else if hasStorageAnnotation body idx then
    .dead
  else if isAlwaysInhabitedZst ty then
    .liveInit
  else
    .liveUninit

/-- Construct the exact entry abstract environment for block `0` of `body`. -/
noncomputable def initAbsEnvLoop (body : Body) : Nat → List MirTy → List AbsSlot
  | _, [] => []
  | idx, ty :: rest => initAbsSlot body idx ty :: initAbsEnvLoop body (idx + 1) rest

/-- Abstract transition for `Operand` (used by both `MoveToCopy` and
`StorageSafe` abstract-interpretation checkers):
- `.constant c`: environment unchanged.
- `.copy p`: requires `p.projection.isEmpty` and `env[p.localId] == .liveInit`.
- `.move p`: requires `p.projection.isEmpty` and `env[p.localId] == .liveInit`,
  then updates `env[p.localId]` to `.liveInit` if `isAlwaysInhabitedZst ty`,
  else `.liveUninit`. -/
noncomputable def stepAbsOperand (bodyLocals : List MirTy) (env : List AbsSlot) :
    Operand → Option (List AbsSlot)
  | .constant _ => some env
  | .copy p =>
    if !p.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some _, some .liveInit => some env
      | _, _ => none
  | .move p =>
    if !p.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some .liveInit =>
        let nextSlot := if isAlwaysInhabitedZst ty then .liveInit else .liveUninit
        setElem? env p.localId nextSlot
      | _, _ => none

/-- Abstract transition for `Rvalue` (threading left-to-right operand effects in
`.binaryOp lhs rhs` so M4 patterns `copy _k + move _k` pass while
`move _k + copy _k` fail). Note that `.ref`, `.addressOf`, `.aggregateTuple`,
and `.unsupported` immediately fault `.unsupported` in `evalRvalue` for both
`pSrc` and `pTgt` without reading `locals`, though rejecting them or handling
supported arms preserves lockstep; we handle all four executable `evalRvalue`
constructors (`use`, `binaryOp`, `unaryOp`, `discriminant`). -/
noncomputable def stepAbsRvalue (bodyLocals : List MirTy) (env : List AbsSlot) :
    Rvalue → Option (List AbsSlot)
  | .use opnd => stepAbsOperand bodyLocals env opnd
  | .binaryOp _ lhs rhs =>
    match stepAbsOperand bodyLocals env lhs with
    | none => none
    | some env₁ => stepAbsOperand bodyLocals env₁ rhs
  | .unaryOp _ opnd => stepAbsOperand bodyLocals env opnd
  | .discriminant p =>
    if !p.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some (.enum ety), some slot =>
        if isZstEnumTy ety then
          match slot with
          | .dead => none
          | .liveInit | .liveUninit => some env
        else
          match slot with
          | .liveInit => some env
          | _ => none
      | _, _ => none
  | _ => none

/-- Abstract transition for `StatementKind`. When `requireLiveDst = true`
(`StorageSafe` mode), `.assign dst _` requires `envAfterRval[dst.localId]` not
to be `.dead`, `.storageLive id` requires `id < bodyLocals.length`, and
`.storageDead id` requires `0 < id < bodyLocals.length`. -/
noncomputable def stepAbsStmt (requireLiveDst : Bool) (bodyLocals : List MirTy)
    (env : List AbsSlot) : StatementKind → Option (List AbsSlot)
  | .nop => some env
  | .storageLive id =>
    match Trusted.MirSemantics.getElem? bodyLocals id with
    | none => none
    | some ty =>
      let nextSlot := if isAlwaysInhabitedZst ty then .liveInit else .liveUninit
      setElem? env id nextSlot
  | .storageDead id =>
    if Nat.beq id 0 then none
    else setElem? env id .dead
  | .assign dst rv =>
    if !dst.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => none
      | some _ =>
        match stepAbsRvalue bodyLocals env rv with
        | none => none
        | some env₁ =>
          match Trusted.MirSemantics.getElem? env₁ dst.localId with
          | none => none
          | some .dead =>
            if requireLiveDst then none else setElem? env₁ dst.localId .liveInit
          | some .liveInit | some .liveUninit =>
            setElem? env₁ dst.localId .liveInit
  | .unsupported => none

/-- Step a list of statements sequentially. -/
noncomputable def stepAbsStmts (requireLiveDst : Bool) (bodyLocals : List MirTy) :
    List AbsSlot → List StatementKind → Option (List AbsSlot)
  | env, [] => some env
  | env, s :: ss =>
    match stepAbsStmt requireLiveDst bodyLocals env s with
    | none => none
    | some env' => stepAbsStmts requireLiveDst bodyLocals env' ss

/-- Check that edge jump to `target` is covered by `cert` (if `target` is in
bounds of `body.basicBlocks`, `cert[target]` must be `some tgtEnv` entailed by
`exitEnv`; out-of-bounds targets fault `.unsupported` identically in both
programs at the next step). -/
noncomputable def checkEdgeTarget (numBlocks : Nat) (cert : BodyAbsCert)
    (exitEnv : List AbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? cert target with
    | some (some tgtEnv) => absEnvImplies exitEnv tgtEnv
    | _ => false

/-- Check a single basic block `bb` under `cert`. Note that terminators that
immediately fault in `Trusted.MirSemantics.evalTerminator` without reading
`locals` (`.unreachable`, `.unwindResume`, `.assert`, `.call`, `.unsupported`)
fault identically in both `pSrc` and `pTgt` in 1 step and are therefore safe at
any reachable exit environment. -/
noncomputable def checkAbsBlock (requireLiveDst : Bool) (body : Body)
    (cert : BodyAbsCert) (bbIdx : Nat) (bb : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx with
  | none => false
  | some none => true
  | some (some entryEnv) =>
    Nat.beq entryEnv.length body.locals.length &&
      match stepAbsStmts requireLiveDst body.locals entryEnv bb.statements with
      | none => false
      | some exitEnv =>
        let numBlocks := body.basicBlocks.length
        match bb.terminator with
        | .goto target => checkEdgeTarget numBlocks cert exitEnv target
        | .return_ =>
          if bb.cleanup then true
          else
            match Trusted.MirSemantics.getElem? exitEnv 0 with
            | some .liveInit => true
            | _ => false
        | .switchInt discr targets =>
          match stepAbsOperand body.locals exitEnv discr with
          | none => false
          | some afterDiscrEnv =>
            checkEdgeTarget numBlocks cert afterDiscrEnv targets.otherwise &&
              targets.branches.all (fun br =>
                checkEdgeTarget numBlocks cert afterDiscrEnv br.2)
        | .unreachable | .unwindResume | .assert _ _ _ _ _
        | .call _ _ _ _ _ | .unsupported => true

/-- Check all blocks `idx ..` of `body`. -/
noncomputable def checkAbsBlocksLoop (requireLiveDst : Bool) (body : Body)
    (cert : BodyAbsCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bb :: rest =>
    checkAbsBlock requireLiveDst body cert idx bb &&
      checkAbsBlocksLoop requireLiveDst body cert (idx + 1) rest

/-- Unified body-level abstract-interpretation certificate checker. -/
noncomputable def checkAbsBody (requireLiveDst : Bool) (body : Body)
    (cert : BodyAbsCert) : Bool :=
  Nat.beq cert.length body.basicBlocks.length &&
    (if body.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) => absEnvImplies (initAbsEnvLoop body 0 body.locals) env₀
       | _ => false) &&
    (if requireLiveDst then storageAnnotationsInBounds body else true) &&
    checkAbsBlocksLoop requireLiveDst body cert 0 body.basicBlocks

/-- `NoUseAfterMove` certificate checker for `MoveToCopy` reverse VC transport. -/
noncomputable def checkNoUseAfterMoveBody (body : Body) (cert : BodyAbsCert) : Bool :=
  checkAbsBody false body cert

/-- Program-level `NoUseAfterMove` certificate checker. -/
noncomputable def checkNoUseAfterMoveProgram (pSrc : Program)
    (cert : ProgramAbsCert) : Bool :=
  listRel checkNoUseAfterMoveBody pSrc.bodies cert

/-- `StorageSafe` certificate checker for `RemoveStorageMarkers` reverse VC
transport. -/
noncomputable def checkStorageSafeBody (body : Body) (cert : BodyAbsCert) : Bool :=
  checkAbsBody true body cert

/-- Program-level `StorageSafe` certificate checker. -/
noncomputable def checkStorageSafeProgram (pSrc : Program)
    (cert : ProgramAbsCert) : Bool :=
  listRel checkStorageSafeBody pSrc.bodies cert

/-! ### Private Proof Helpers — Layer A: Reflection and List Lemmas -/

private theorem bool_and_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => exact ⟨rfl, rfl⟩

private theorem bool_or_true {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false =>
    cases b with
    | true => exact Or.inr rfl
    | false => cases h

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

private theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

private theorem nat_beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ _ => cases h
  | succ k ih =>
    cases b with
    | zero => cases h
    | succ m =>
      have hkm : k = m := ih h
      rw [hkm]

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hEq : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (nat_beq_eq hEq))

private theorem nat_ble_le {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le b
  | succ k ih =>
    cases b with
    | zero => cases h
    | succ m => exact Nat.succ_le_succ (ih h)

private theorem nat_le_ble {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by
  induction a generalizing b with
  | zero => rfl
  | succ k ih =>
    cases b with
    | zero => exact False.elim (Nat.not_succ_le_zero k h)
    | succ m => exact ih (Nat.le_of_succ_le_succ h)

private theorem nat_blt_lt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  nat_ble_le h

private theorem nat_lt_blt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  nat_le_ble h

private theorem nat_blt_false_ge {a b : Nat} (h : Nat.blt a b = false) :
    b ≤ a := by
  cases Nat.lt_or_ge a b with
  | inl hlt =>
    have hT : Nat.blt a b = true := nat_lt_blt hlt
    rw [hT] at h
    cases h
  | inr hge => exact hge

private theorem nat_ge_blt_false {a b : Nat} (h : b ≤ a) :
    Nat.blt a b = false := by
  cases hB : Nat.blt a b with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge h (nat_blt_lt hB))

private theorem bitvec_beq_eq {n : Nat} {a b : BitVec n}
    (h : (a == b) = true) : a = b := by
  exact eq_of_beq h

private theorem uint8_beq_eq {a b : UInt8} (h : (a == b) = true) : a = b := by
  exact eq_of_beq h

private theorem uint8_list_beq_eq {xs ys : List UInt8}
    (h : List.beq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [uint8_beq_eq h1, ih h2]

private theorem stringBeq_empty_congr {a b : String} (h : stringBeq a b = true) :
    stringBeq a "" = stringBeq b "" := by
  unfold stringBeq at h
  have hBytes : a.toByteArray.data.toList = b.toByteArray.data.toList :=
    uint8_list_beq_eq h
  unfold stringBeq
  rw [hBytes]

private theorem listRel_length {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} (h : listRel r xs ys = true) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ xs ih =>
    cases ys with
    | nil => cases h
    | cons _ ys =>
      let ⟨_, h2⟩ := bool_and_true h
      dsimp [List.length]
      rw [ih h2]

private theorem listRel_getElem?_left {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} {i : Nat} {x : α}
    (hRel : listRel r xs ys = true)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) :
    ∃ y, Trusted.MirSemantics.getElem? ys i = some y ∧ r x y = true := by
  induction xs generalizing ys i with
  | nil => cases hGet
  | cons a xs ih =>
    cases ys with
    | nil => cases hRel
    | cons b ys =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      cases i with
      | zero =>
        injection hGet with hxa
        subst hxa
        exact ⟨b, rfl, hab⟩
      | succ k =>
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
  | cons a xs ih =>
    cases ys with
    | nil => cases hRel
    | cons b ys =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      cases i with
      | zero =>
        injection hGet with hyb
        subst hyb
        exact ⟨a, rfl, hab⟩
      | succ k =>
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih hTail hGet

private theorem listRel_getElem?_none_iff {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} (i : Nat)
    (hRel : listRel r xs ys = true) :
    Trusted.MirSemantics.getElem? xs i = none ↔
      Trusted.MirSemantics.getElem? ys i = none := by
  constructor
  · intro hNone
    cases hY : Trusted.MirSemantics.getElem? ys i with
    | none => rfl
    | some y =>
      let ⟨x, hX, _⟩ := listRel_getElem?_right hRel hY
      rw [hNone] at hX
      cases hX
  · intro hNone
    cases hX : Trusted.MirSemantics.getElem? xs i with
    | none => rfl
    | some x =>
      let ⟨y, hY, _⟩ := listRel_getElem?_left hRel hX
      rw [hNone] at hY
      cases hY

private theorem listRel_eq {α : Type} {r : α → α → Bool}
    (hEq : ∀ x y, r x y = true → x = y) {xs ys : List α}
    (hRel : listRel r xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons x xs ih =>
    cases ys with
    | nil => cases hRel
    | cons y ys =>
      let ⟨h1, h2⟩ := bool_and_true hRel
      rw [hEq x y h1, ih h2]

private theorem getElem?_some_lt {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : Trusted.MirSemantics.getElem? xs i = some x) : i < xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons _ xs ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ xs.length
    | succ k => exact Nat.succ_lt_succ (ih h)

private theorem getElem?_none_of_ge {α : Type} {xs : List α} {i : Nat}
    (h : xs.length ≤ i) : Trusted.MirSemantics.getElem? xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ xs ih =>
    cases i with
    | zero => exact False.elim (Nat.not_succ_le_zero xs.length h)
    | succ k => exact ih (Nat.le_of_succ_le_succ h)

private theorem getElem?_some_of_lt {α : Type} (xs : List α) (i : Nat)
    (h : i < xs.length) : ∃ x, Trusted.MirSemantics.getElem? xs i = some x := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons a xs ih =>
    cases i with
    | zero => exact ⟨a, rfl⟩
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ h)

private theorem setElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : setElem? xs i v = some xs') : xs'.length = xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons a xs ih =>
    cases i with
    | zero =>
      injection h with hEq
      subst hEq
      rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? xs k v with
      | none => rw [hSub] at h; cases h
      | some sub =>
        rw [hSub] at h
        injection h with hEq
        subst hEq
        dsimp [List.length]
        rw [ih hSub]

private theorem setElem?_getElem?_same {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : setElem? xs i v = some xs') :
    Trusted.MirSemantics.getElem? xs' i = some v := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons a xs ih =>
    cases i with
    | zero =>
      injection h with hEq
      subst hEq
      rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? xs k v with
      | none => rw [hSub] at h; cases h
      | some sub =>
        rw [hSub] at h
        injection h with hEq
        subst hEq
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih hSub

private theorem setElem?_getElem?_ne {α : Type} {xs xs' : List α} {i j : Nat} {v : α}
    (h : setElem? xs i v = some xs') (hNe : j ≠ i) :
    Trusted.MirSemantics.getElem? xs' j = Trusted.MirSemantics.getElem? xs j := by
  induction xs generalizing xs' i j with
  | nil => cases h
  | cons a xs ih =>
    cases i with
    | zero =>
      injection h with hEq
      subst hEq
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ m => rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? xs k v with
      | none => rw [hSub] at h; cases h
      | some sub =>
        rw [hSub] at h
        injection h with hEq
        subst hEq
        cases j with
        | zero => rfl
        | succ m =>
          have hmk : m ≠ k := fun hEq => hNe (by rw [hEq])
          exact ih hSub hmk

private theorem setElem?_some_of_lt {α : Type} (xs : List α) (i : Nat) (v : α)
    (h : i < xs.length) : ∃ xs', setElem? xs i v = some xs' := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons a xs ih =>
    cases i with
    | zero => exact ⟨v :: xs, rfl⟩
    | succ k =>
      let ⟨sub, hSub⟩ := ih k (Nat.lt_of_succ_lt_succ h)
      exact ⟨a :: sub, by dsimp [setElem?]; rw [hSub]⟩

private theorem setElem?_none_of_ge {α : Type} (xs : List α) (i : Nat) (v : α)
    (h : xs.length ≤ i) : setElem? xs i v = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons a xs ih =>
    cases i with
    | zero => exact False.elim (Nat.not_succ_le_zero xs.length h)
    | succ k =>
      dsimp [setElem?]
      rw [ih k (Nat.le_of_succ_le_succ h)]

private theorem drop_eq_cons_of_getElem? {α : Type} {xs : List α} {n : Nat} {x : α}
    (h : Trusted.MirSemantics.getElem? xs n = some x) :
    xs.drop n = x :: xs.drop (n + 1) := by
  induction xs generalizing n with
  | nil => cases h
  | cons a xs ih =>
    cases n with
    | zero =>
      injection h with hxa
      subst hxa
      rfl
    | succ k => exact ih h

private theorem drop_length_nil {α : Type} (xs : List α) :
    xs.drop xs.length = [] := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => exact ih

private theorem list_all_getElem? {α : Type} {p : α → Bool} {xs : List α}
    {i : Nat} {x : α} (hAll : xs.all p = true)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) : p x = true := by
  induction xs generalizing i with
  | nil => cases hGet
  | cons a xs ih =>
    dsimp [List.all] at hAll
    let ⟨ha, hxs⟩ := bool_and_true hAll
    cases i with
    | zero =>
      injection hGet with hxa
      subst hxa
      exact ha
    | succ k => exact ih hxs hGet

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
    | cons y ys ih =>
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero i hi)
      | succ m =>
        cases i with
        | zero => rfl
        | succ k => exact ih m k (Nat.lt_of_succ_lt_succ hi)

private theorem checkArgsMatch_getElem? {args : List Val} {tys : List MirTy}
    {i : Nat} {ty : MirTy}
    (hMatch : checkArgsMatch args tys = true)
    (hTy : Trusted.MirSemantics.getElem? tys i = some ty) :
    ∃ v, Trusted.MirSemantics.getElem? args i = some v ∧ checkVal v ty = true := by
  induction args generalizing tys i with
  | nil =>
    cases tys with
    | nil => cases hTy
    | cons _ _ => cases hMatch
  | cons a args ih =>
    cases tys with
    | nil => cases hMatch
    | cons t tys =>
      let ⟨h1, h2⟩ := bool_and_true hMatch
      cases i with
      | zero =>
        injection hTy with hEq
        subst hEq
        exact ⟨a, rfl, h1⟩
      | succ k => exact ih h2 hTy

private theorem intWidth_beq_eq {a b : IntWidth}
    (h : IntWidth.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem intWidth_beq_refl (a : IntWidth) : IntWidth.beq a a = true := by
  cases a <;> rfl

private theorem mutability_beq_eq {a b : Mutability}
    (h : Mutability.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem mutability_beq_refl (a : Mutability) :
    Mutability.beq a a = true := by
  cases a <;> rfl

private theorem natListBeq_eq {a b : List Nat}
    (h : natListBeq a b = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases b with
    | nil => cases h
    | cons y ys =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, ih h2]

private theorem natListBeq_refl (a : List Nat) : natListBeq a a = true := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
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
  | scalar w1 s1 =>
    cases b with
    | zeroSized => cases h
    | scalar w2 s2 =>
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
  | mk id1 w1 s1 tr1 ds1 =>
    cases b with
    | mk id2 w2 s2 tr2 ds2 =>
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
    | .int w1 s1, .int w2 s2, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [intWidth_beq_eq h1, bool_beq_eq h2]
    | .unit, .unit, _ => rfl
    | .never, .never, _ => rfl
    | .enum e1, .enum e2, h => by rw [enumTy_beq_eq h]
    | .tuple fs1, .tuple fs2, h => by rw [mirTy_beqList_eq h]
    | .ref m1 p1, .ref m2 p2, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, mirTy_beq_eq h2]
    | .rawPtr m1 p1, .rawPtr m2 p2, h => by
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
    | x :: xs, y :: ys, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mirTy_beq_eq h1, mirTy_beqList_eq h2]
    | [], _ :: _, h | _ :: _, [], h => by cases h
end

private theorem projElemEq_eq {a b : ProjectionElem}
    (h : projElemEq a b = true) : a = b := by
  cases a with
  | deref => cases b <;> first | rfl | cases h
  | field i1 t1 =>
    cases b with
    | field i2 t2 =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, mirTy_beq_eq h2]
    | _ => cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem placeEq_eq {a b : Place} (h : placeEq a b = true) : a = b := by
  cases a with
  | mk l1 p1 =>
    cases b with
    | mk l2 p2 =>
      dsimp [placeEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, listRel_eq (fun _ _ => projElemEq_eq) h2]

private theorem constLitEq_eq {a b : ConstLit}
    (h : constLitEq a b = true) : a = b := by
  cases a with
  | scalar b1 =>
    cases b with
    | scalar b2 => rw [bitvec_beq_eq h]
    | zeroSized => cases h
  | zeroSized =>
    cases b with
    | scalar _ => cases h
    | zeroSized => rfl

private theorem constOpEq_eq {a b : ConstOperand}
    (h : constOpEq a b = true) : a = b := by
  cases a with
  | mk t1 l1 =>
    cases b with
    | mk t2 l2 =>
      dsimp [constOpEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mirTy_beq_eq h1, constLitEq_eq h2]

private theorem binOpEq_eq {a b : BinOp} (h : binOpEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem unOpEq_eq {a b : UnOp} (h : unOpEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

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
        | mk xv xt =>
          cases y with
          | mk yv yt =>
            dsimp at hxy
            let ⟨hv, ht⟩ := bool_and_true hxy
            rw [bitvec_beq_eq hv, nat_beq_eq ht]) h2
      rw [hOw, hBs]

private theorem operandEq_eq {a b : Operand}
    (h : operandEq a b = true) : a = b := by
  cases a with
  | copy p1 =>
    cases b with
    | copy p2 => rw [placeEq_eq h]
    | _ => cases h
  | move p1 =>
    cases b with
    | move p2 => rw [placeEq_eq h]
    | _ => cases h
  | constant c1 =>
    cases b with
    | constant c2 => rw [constOpEq_eq h]
    | _ => cases h

private theorem operandEq_imp_moveToCopy {a b : Operand}
    (h : operandEq a b = true) : isMoveToCopyOperand a b = true := by
  cases a <;> cases b <;> first | exact h | cases h

private theorem rvalueRel_operandEq_eq {a b : Rvalue}
    (h : rvalueRel operandEq a b = true) : a = b := by
  cases a with
  | use o1 =>
    cases b with
    | use o2 => rw [operandEq_eq h]
    | _ => cases h
  | binaryOp op1 l1 r1 =>
    cases b with
    | binaryOp op2 l2 r2 =>
      let ⟨h12, h3⟩ := bool_and_true h
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [binOpEq_eq h1, operandEq_eq h2, operandEq_eq h3]
    | _ => cases h
  | unaryOp op1 o1 =>
    cases b with
    | unaryOp op2 o2 =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [unOpEq_eq h1, operandEq_eq h2]
    | _ => cases h
  | discriminant p1 =>
    cases b with
    | discriminant p2 => rw [placeEq_eq h]
    | _ => cases h
  | ref m1 p1 =>
    cases b with
    | ref m2 p2 =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, placeEq_eq h2]
    | _ => cases h
  | addressOf m1 p1 =>
    cases b with
    | addressOf m2 p2 =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, placeEq_eq h2]
    | _ => cases h
  | aggregateTuple fs1 =>
    cases b with
    | aggregateTuple fs2 =>
      rw [listRel_eq (fun _ _ => operandEq_eq) h]
    | _ => cases h
  | unsupported =>
    cases b <;> first | rfl | cases h

private theorem unwindActionEq_eq {a b : UnwindAction}
    (h : unwindActionEq a b = true) : a = b := by
  cases a with
  | cleanup b1 =>
    cases b with
    | cleanup b2 => rw [nat_beq_eq h]
    | _ => cases h
  | continue_ => cases b <;> first | rfl | cases h
  | unreachable => cases b <;> first | rfl | cases h
  | terminate => cases b <;> first | rfl | cases h

private theorem assertKindEq_eq {a b : AssertKind}
    (h : assertKindEq a b = true) : a = b := by
  cases a with
  | overflow o1 =>
    cases b with
    | overflow o2 => rw [binOpEq_eq h]
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
  | some b1 =>
    cases b with
    | some b2 => rw [nat_beq_eq h]
    | none => cases h

private theorem terminatorRel_operandEq_eq {a b : TerminatorKind}
    (h : terminatorRel operandEq a b = true) : a = b := by
  cases a with
  | goto t1 =>
    cases b with
    | goto t2 => rw [nat_beq_eq h]
    | _ => cases h
  | switchInt d1 ts1 =>
    cases b with
    | switchInt d2 ts2 =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [operandEq_eq h1, switchTargetsEq_eq h2]
    | _ => cases h
  | return_ => cases b <;> first | rfl | cases h
  | unreachable => cases b <;> first | rfl | cases h
  | unwindResume => cases b <;> first | rfl | cases h
  | assert c1 e1 m1 t1 u1 =>
    cases b with
    | assert c2 e2 m2 t2 u2 =>
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [operandEq_eq h1, bool_beq_eq h2, assertKindEq_eq h3,
          nat_beq_eq h4, unwindActionEq_eq h5]
    | _ => cases h
  | call f1 as1 d1 t1 u1 =>
    cases b with
    | call f2 as2 d2 t2 u2 =>
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [nat_beq_eq h1, listRel_eq (fun _ _ => operandEq_eq) h2,
          placeEq_eq h3, optBlockEq_eq h4, unwindActionEq_eq h5]
    | _ => cases h
  | unsupported => cases b <;> first | rfl | cases h

/-! ### Private Proof Helpers — Layer B: Deterministic Simulation Lifting -/

private noncomputable def iterState (p : Program) (s₀ : State) : Nat → State
  | 0 => s₀
  | n + 1 =>
    match evalStep p 0 (iterState p s₀ n) with
    | .step s' => s'
    | .done _ => iterState p s₀ n
    | .fault _ => iterState p s₀ n

private theorem step_iff_evalStep {p : Program} {s : State}
    {res : StepResult State TerminalOut} :
    Step p s res ↔ evalStep p 0 s = res := by
  constructor
  · intro h
    let ⟨c, hc, hEval⟩ := h
    have hc0 : c = 0 := hc
    subst hc0
    exact hEval
  · intro h
    exact ⟨0, rfl, h⟩

private theorem reaches_fwd_sim {p1 p2 : Program} {R : State → State → Prop}
    {s₀ t₀ s : State}
    (hStep : ∀ a b a', R a b → evalStep p1 0 a = .step a' →
      ∃ b', evalStep p2 0 b = .step b' ∧ R a' b')
    (hInit : R s₀ t₀) (hReach : Reaches p1 s₀ s) :
    ∃ t, Reaches p2 t₀ t ∧ R s t := by
  induction hReach with
  | refl => exact ⟨t₀, Reaches.refl t₀, hInit⟩
  | tail _ hSt ih =>
    let ⟨t, hRt, hRel⟩ := ih
    have hEval : evalStep p1 0 _ = .step _ := step_iff_evalStep.mp hSt
    let ⟨t', hEval2, hRel'⟩ := hStep _ _ _ hRel hEval
    exact ⟨t', Reaches.tail hRt (step_iff_evalStep.mpr hEval2), hRel'⟩

private theorem diverges_fwd_sim {p1 p2 : Program} {q : Query}
    {R : State → State → Prop} {s₀ t₀ : State}
    (hInit1 : initState p1 q = .ok s₀) (hInit2 : initState p2 q = .ok t₀)
    (hRel0 : R s₀ t₀)
    (hStep : ∀ a b a', R a b → evalStep p1 0 a = .step a' →
      ∃ b', evalStep p2 0 b = .step b' ∧ R a' b') :
    Diverges p1 q → Diverges p2 q := by
  intro hDiv
  let ⟨s₀', hOk', trace1, hTr0, hTrStep⟩ := hDiv
  rw [hInit1] at hOk'
  injection hOk' with hEqS
  subst hEqS
  have hInv : ∀ n, R (trace1 n) (iterState p2 t₀ n) := by
    intro n
    induction n with
    | zero =>
      rw [hTr0]
      exact hRel0
    | succ k ih =>
      have hEval1 : evalStep p1 0 (trace1 k) = .step (trace1 (k + 1)) :=
        step_iff_evalStep.mp (hTrStep k)
      let ⟨b', hEval2, hRel'⟩ := hStep _ _ _ ih hEval1
      dsimp [iterState]
      rw [hEval2]
      exact hRel'
  refine ⟨t₀, hInit2, iterState p2 t₀, rfl, ?_⟩
  intro n
  have hEval1 : evalStep p1 0 (trace1 n) = .step (trace1 (n + 1)) :=
    step_iff_evalStep.mp (hTrStep n)
  let ⟨b', hEval2, _⟩ := hStep _ _ _ (hInv n) hEval1
  apply step_iff_evalStep.mpr
  dsimp [iterState]
  rw [hEval2]

private theorem fwd_sim_lift {pSrc pTgt : Program} {q : Query}
    {R : State → State → Prop}
    (hInit : ∀ s₀, initState pSrc q = .ok s₀ →
      ∃ t₀, initState pTgt q = .ok t₀ ∧ R s₀ t₀)
    (hStep : ∀ s t, R s t →
      (∀ s', evalStep pSrc 0 s = .step s' →
        ∃ t', evalStep pTgt 0 t = .step t' ∧ R s' t') ∧
      (∀ out, evalStep pSrc 0 s = .done out →
        evalStep pTgt 0 t = .done out))
    (hWfSrc : WellFormed pSrc q) :
    WellFormed pTgt q ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨⟨s₀, hInitSrc, _⟩, hNoFaultSrc⟩ := hWfSrc
  let ⟨t₀, hInitTgt, hRel0⟩ := hInit s₀ hInitSrc
  have hNoFaultAt : ∀ s, Reaches pSrc s₀ s → ∀ k, evalStep pSrc 0 s ≠ .fault k := by
    intro s hRs k hF
    apply hNoFaultSrc k
    unfold ReachesResult
    rw [hInitSrc]
    exact ⟨s, hRs, step_iff_evalStep.mpr hF⟩
  have hBackReach : ∀ t, Reaches pTgt t₀ t → ∃ s, Reaches pSrc s₀ s ∧ R s t := by
    intro t hRt
    induction hRt with
    | refl => exact ⟨s₀, Reaches.refl s₀, hRel0⟩
    | tail _ hStTgt ih =>
      let ⟨s, hRs, hRel⟩ := ih
      have hEvalTgt : evalStep pTgt 0 _ = .step _ := step_iff_evalStep.mp hStTgt
      cases hEvalSrc : evalStep pSrc 0 s with
      | fault k => exact False.elim (hNoFaultAt s hRs k hEvalSrc)
      | done out =>
        have hDT : evalStep pTgt 0 _ = .done out := (hStep s _ hRel).2 out hEvalSrc
        rw [hDT] at hEvalTgt
        cases hEvalTgt
      | step s' =>
        let ⟨t', hST, hRel'⟩ := (hStep s _ hRel).1 s' hEvalSrc
        rw [hST] at hEvalTgt
        injection hEvalTgt with hEqT
        subst hEqT
        exact ⟨s', Reaches.tail hRs (step_iff_evalStep.mpr hEvalSrc), hRel'⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨t₀, hInitTgt, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
    intro k hFaultTgt
    unfold ReachesResult at hFaultTgt
    rw [hInitTgt] at hFaultTgt
    let ⟨t, hRt, hStTgt⟩ := hFaultTgt
    have hEvalTgt : evalStep pTgt 0 t = .fault k := step_iff_evalStep.mp hStTgt
    let ⟨s, hRs, hRel⟩ := hBackReach t hRt
    cases hEvalSrc : evalStep pSrc 0 s with
    | fault k' => exact hNoFaultAt s hRs k' hEvalSrc
    | done out =>
      have hDT := (hStep s t hRel).2 out hEvalSrc
      rw [hDT] at hEvalTgt
      cases hEvalTgt
    | step s' =>
      let ⟨t', hST, _⟩ := (hStep s t hRel).1 s' hEvalSrc
      rw [hST] at hEvalTgt
      cases hEvalTgt
  · intro out
    constructor
    · intro hBehTgt
      unfold Behavior ReachesResult at hBehTgt
      rw [hInitTgt] at hBehTgt
      let ⟨t, hRt, hStTgt⟩ := hBehTgt
      have hEvalTgt : evalStep pTgt 0 t = .done out := step_iff_evalStep.mp hStTgt
      let ⟨s, hRs, hRel⟩ := hBackReach t hRt
      cases hEvalSrc : evalStep pSrc 0 s with
      | fault k => exact False.elim (hNoFaultAt s hRs k hEvalSrc)
      | step s' =>
        let ⟨t', hST, _⟩ := (hStep s t hRel).1 s' hEvalSrc
        rw [hST] at hEvalTgt
        cases hEvalTgt
      | done out' =>
        have hDT := (hStep s t hRel).2 out' hEvalSrc
        rw [hDT] at hEvalTgt
        injection hEvalTgt with hEqO
        subst hEqO
        unfold Behavior ReachesResult
        rw [hInitSrc]
        exact ⟨s, hRs, step_iff_evalStep.mpr hEvalSrc⟩
    · intro hBehSrc
      unfold Behavior ReachesResult at hBehSrc
      rw [hInitSrc] at hBehSrc
      let ⟨s, hRs, hStSrc⟩ := hBehSrc
      have hEvalSrc : evalStep pSrc 0 s = .done out := step_iff_evalStep.mp hStSrc
      let ⟨t, hRt, hRel⟩ := reaches_fwd_sim (fun a b a' hr hs => (hStep a b hr).1 a' hs) hRel0 hRs
      unfold Behavior ReachesResult
      rw [hInitTgt]
      exact ⟨t, hRt, step_iff_evalStep.mpr ((hStep s t hRel).2 out hEvalSrc)⟩
  · constructor
    · intro hDivTgt
      let ⟨t₀', hOk', traceTgt, hTr0, hTrStep⟩ := hDivTgt
      rw [hInitTgt] at hOk'
      injection hOk' with hEqT
      subst hEqT
      have hInv : ∀ n, Reaches pSrc s₀ (iterState pSrc s₀ n) ∧
          R (iterState pSrc s₀ n) (traceTgt n) := by
        intro n
        induction n with
        | zero =>
          rw [hTr0]
          exact ⟨Reaches.refl s₀, hRel0⟩
        | succ k ih =>
          let ⟨hRs, hRel⟩ := ih
          have hEvalTgt : evalStep pTgt 0 (traceTgt k) = .step (traceTgt (k + 1)) :=
            step_iff_evalStep.mp (hTrStep k)
          cases hEvalSrc : evalStep pSrc 0 (iterState pSrc s₀ k) with
          | fault fk => exact False.elim (hNoFaultAt _ hRs fk hEvalSrc)
          | done out =>
            have hDT := (hStep _ _ hRel).2 out hEvalSrc
            rw [hDT] at hEvalTgt
            cases hEvalTgt
          | step s' =>
            let ⟨t', hST, hRel'⟩ := (hStep _ _ hRel).1 s' hEvalSrc
            rw [hST] at hEvalTgt
            injection hEvalTgt with hEqT'
            subst hEqT'
            dsimp [iterState]
            rw [hEvalSrc]
            exact ⟨Reaches.tail hRs (step_iff_evalStep.mpr hEvalSrc), hRel'⟩
      refine ⟨s₀, hInitSrc, iterState pSrc s₀, rfl, ?_⟩
      intro n
      let ⟨hRs, hRel⟩ := hInv n
      have hEvalTgt : evalStep pTgt 0 (traceTgt n) = .step (traceTgt (n + 1)) :=
        step_iff_evalStep.mp (hTrStep n)
      cases hEvalSrc : evalStep pSrc 0 (iterState pSrc s₀ n) with
      | fault fk => exact False.elim (hNoFaultAt _ hRs fk hEvalSrc)
      | done out =>
        have hDT := (hStep _ _ hRel).2 out hEvalSrc
        rw [hDT] at hEvalTgt
        cases hEvalTgt
      | step s' =>
        apply step_iff_evalStep.mpr
        dsimp [iterState]
        rw [hEvalSrc]
    · exact diverges_fwd_sim hInitSrc hInitTgt hRel0
        (fun a b a' hr hs => (hStep a b hr).1 a' hs)

private theorem bisim_lift {pSrc pTgt : Program} {q : Query}
    {R : State → State → Prop}
    (hInitErr : ∀ k, initState pSrc q = .error k ↔ initState pTgt q = .error k)
    (hInitOk : ∀ s₀ t₀, initState pSrc q = .ok s₀ → initState pTgt q = .ok t₀ →
      R s₀ t₀)
    (hStep : ∀ s t, R s t →
      (∀ s', evalStep pSrc 0 s = .step s' →
        ∃ t', evalStep pTgt 0 t = .step t' ∧ R s' t') ∧
      (∀ t', evalStep pTgt 0 t = .step t' →
        ∃ s', evalStep pSrc 0 s = .step s' ∧ R s' t') ∧
      (∀ out, evalStep pSrc 0 s = .done out ↔ evalStep pTgt 0 t = .done out) ∧
      (∀ k, evalStep pSrc 0 s = .fault k ↔ evalStep pTgt 0 t = .fault k)) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  cases hInitSrc : initState pSrc q with
  | error kErr =>
    have hInitTgt : initState pTgt q = .error kErr := (hInitErr kErr).mp hInitSrc
    refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitTgt] at hOk; cases hOk
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitSrc] at hOk; cases hOk
    · intro out
      unfold Behavior ReachesResult
      rw [hInitTgt, hInitSrc]
    · intro k
      unfold ReachesResult
      rw [hInitTgt, hInitSrc]
    · constructor
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitTgt] at hOk; cases hOk
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitSrc] at hOk; cases hOk
  | ok s₀ =>
    cases hInitTgt : initState pTgt q with
    | error kErr =>
      have hContra := (hInitErr kErr).mpr hInitTgt
      rw [hInitSrc] at hContra
      cases hContra
    | ok t₀ =>
      have hRel0 : R s₀ t₀ := hInitOk s₀ t₀ hInitSrc hInitTgt
      have hBehIff : ∀ out, Behavior pTgt q out ↔ Behavior pSrc q out := by
        intro out
        unfold Behavior ReachesResult
        rw [hInitTgt, hInitSrc]
        constructor
        · intro h
          let ⟨t, hRt, hSt⟩ := h
          let ⟨s, hRs, hRel⟩ := reaches_fwd_sim
            (R := fun b a => R a b)
            (fun b a b' hr hb => (hStep a b hr).2.1 b' hb) hRel0 hRt
          exact ⟨s, hRs, step_iff_evalStep.mpr
            (((hStep s t hRel).2.2.1 out).mpr (step_iff_evalStep.mp hSt))⟩
        · intro h
          let ⟨s, hRs, hSt⟩ := h
          let ⟨t, hRt, hRel⟩ := reaches_fwd_sim
            (fun a b a' hr ha => (hStep a b hr).1 a' ha) hRel0 hRs
          exact ⟨t, hRt, step_iff_evalStep.mpr
            (((hStep s t hRel).2.2.1 out).mp (step_iff_evalStep.mp hSt))⟩
      have hFaultIff : ∀ k, ReachesResult pTgt q (.fault k) ↔
          ReachesResult pSrc q (.fault k) := by
        intro k
        unfold ReachesResult
        rw [hInitTgt, hInitSrc]
        constructor
        · intro h
          let ⟨t, hRt, hSt⟩ := h
          let ⟨s, hRs, hRel⟩ := reaches_fwd_sim
            (R := fun b a => R a b)
            (fun b a b' hr hb => (hStep a b hr).2.1 b' hb) hRel0 hRt
          exact ⟨s, hRs, step_iff_evalStep.mpr
            (((hStep s t hRel).2.2.2 k).mpr (step_iff_evalStep.mp hSt))⟩
        · intro h
          let ⟨s, hRs, hSt⟩ := h
          let ⟨t, hRt, hRel⟩ := reaches_fwd_sim
            (fun a b a' hr ha => (hStep a b hr).1 a' ha) hRel0 hRs
          exact ⟨t, hRt, step_iff_evalStep.mpr
            (((hStep s t hRel).2.2.2 k).mp (step_iff_evalStep.mp hSt))⟩
      refine ⟨?_, hBehIff, hFaultIff, ?_⟩
      · constructor
        · intro hW
          refine ⟨⟨s₀, hInitSrc, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
          intro k hF
          exact hW.2 k ((hFaultIff k).mpr hF)
        · intro hW
          refine ⟨⟨t₀, hInitTgt, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
          intro k hF
          exact hW.2 k ((hFaultIff k).mp hF)
      · constructor
        · exact diverges_fwd_sim (R := fun b a => R a b) hInitTgt hInitSrc hRel0
            (fun b a b' hr hb => (hStep a b hr).2.1 b' hb)
        · exact diverges_fwd_sim hInitSrc hInitTgt hRel0
            (fun a b a' hr ha => (hStep a b hr).1 a' ha)

/-! ### Private Proof Helpers — Layer C1: Slot Typing & Forward Step Lemmas -/

private noncomputable def SlotWellTyped (ty : MirTy) : LocalSlot → Prop
  | .dead => True
  | .live none => isAlwaysInhabitedZst ty = false
  | .live (some v) => checkVal v ty = true

private theorem isZstEnumTy_elim {ety : EnumTy} (h : isZstEnumTy ety = true) :
    ety.tagRepr = .zeroSized ∧ enumAdmitted ety = true ∧
      ety.discriminants.length = 1 := by
  unfold isZstEnumTy at h
  cases hTr : ety.tagRepr with
  | scalar _ _ => rw [hTr] at h; cases h
  | zeroSized =>
    rw [hTr] at h
    have hAdm : enumAdmitted ety = true := h
    unfold enumAdmitted at h
    rw [hTr] at h
    let ⟨_, hLen1⟩ := bool_and_true h
    exact ⟨rfl, hAdm, nat_beq_eq hLen1⟩

private theorem checkVal_unit_eq {v : Val} (h : checkVal v .unit = true) :
    v = .unit := by
  unfold checkVal at h
  cases v with
  | unit => rfl
  | bool _ => cases h
  | ptr _ => cases h
  | tuple _ => cases h
  | bytes _ => cases h
  | scalar sv =>
    dsimp [Val.ty?] at h
    cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
  | enumVal ety k =>
    dsimp [Val.ty?] at h
    cases hC : (enumAdmitted ety && Nat.blt k ety.discriminants.length) <;>
      rw [hC] at h <;> cases h

private theorem checkVal_zstEnum_eq {ety : EnumTy} {v : Val}
    (hZst : isZstEnumTy ety = true) (h : checkVal v (.enum ety) = true) :
    v = .enumVal ety 0 := by
  let ⟨_, _, hLen1⟩ := isZstEnumTy_elim hZst
  unfold checkVal at h
  cases v with
  | enumVal ety' k =>
    dsimp [Val.ty?] at h
    cases hC : (enumAdmitted ety' && Nat.blt k ety'.discriminants.length) with
    | false => rw [hC] at h; cases h
    | true =>
      rw [hC] at h
      have hEq : ety' = ety := enumTy_beq_eq h
      subst hEq
      let ⟨_, hLt⟩ := bool_and_true hC
      have hKlt : k < 1 := by
        rw [← hLen1]
        exact nat_blt_lt hLt
      cases k with
      | zero => rfl
      | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hKlt))
  | bool _ => cases h
  | unit => cases h
  | ptr _ => cases h
  | tuple _ => cases h
  | bytes _ => cases h
  | scalar sv =>
    dsimp [Val.ty?] at h
    cases hWf : sv.wf <;> rw [hWf] at h <;> cases h

private theorem liveUninitSlot_isLive (ty : MirTy) :
    ∃ opt, liveUninitSlot ty = .live opt := by
  cases ty with
  | unit => exact ⟨some .unit, rfl⟩
  | enum ety =>
    dsimp [liveUninitSlot]
    cases isZstEnumTy ety with
    | true => exact ⟨some (.enumVal ety 0), rfl⟩
    | false => exact ⟨none, rfl⟩
  | bool => exact ⟨none, rfl⟩
  | int _ _ => exact ⟨none, rfl⟩
  | never => exact ⟨none, rfl⟩
  | tuple _ => exact ⟨none, rfl⟩
  | ref _ _ => exact ⟨none, rfl⟩
  | rawPtr _ _ => exact ⟨none, rfl⟩
  | unsupported => exact ⟨none, rfl⟩

private theorem liveUninitSlot_wellTyped (ty : MirTy) :
    SlotWellTyped ty (liveUninitSlot ty) := by
  cases ty with
  | unit => rfl
  | enum ety =>
    dsimp [liveUninitSlot]
    cases hZ : isZstEnumTy ety with
    | false => exact hZ
    | true =>
      let ⟨_, hAdm, hLen1⟩ := isZstEnumTy_elim hZ
      dsimp [SlotWellTyped, checkVal, Val.ty?]
      rw [hAdm, hLen1]
      dsimp [Nat.blt, Nat.ble, MirTy.beq]
      exact enumTy_beq_refl ety
  | bool => rfl
  | int _ _ => rfl
  | never => rfl
  | tuple _ => rfl
  | ref _ _ => rfl
  | rawPtr _ _ => rfl
  | unsupported => rfl

private theorem liveUninitSlot_of_not_zst {ty : MirTy}
    (h : isAlwaysInhabitedZst ty = false) :
    liveUninitSlot ty = .live none := by
  cases ty with
  | unit => cases h
  | enum ety =>
    dsimp [isAlwaysInhabitedZst] at h
    dsimp [liveUninitSlot]
    rw [h]
    rfl
  | bool => rfl
  | int _ _ => rfl
  | never => rfl
  | tuple _ => rfl
  | ref _ _ => rfl
  | rawPtr _ _ => rfl
  | unsupported => rfl

private theorem slot_eq_liveUninit_of_zst {ty : MirTy} {opt : Option Val}
    (hZst : isAlwaysInhabitedZst ty = true)
    (hWt : SlotWellTyped ty (.live opt)) :
    LocalSlot.live opt = liveUninitSlot ty := by
  cases opt with
  | none =>
    dsimp [SlotWellTyped] at hWt
    rw [hZst] at hWt
    cases hWt
  | some v =>
    dsimp [SlotWellTyped] at hWt
    cases ty with
    | unit => rw [checkVal_unit_eq hWt]; rfl
    | enum ety =>
      dsimp [isAlwaysInhabitedZst] at hZst
      rw [checkVal_zstEnum_eq hZst hWt]
      dsimp [liveUninitSlot]
      rw [hZst]
      rfl
    | bool => cases hZst
    | int _ _ => cases hZst
    | never => cases hZst
    | tuple _ => cases hZst
    | ref _ _ => cases hZst
    | rawPtr _ _ => cases hZst
    | unsupported => cases hZst

private def SlotFwdRefines (allowDead : Bool) : LocalSlot → LocalSlot → Prop
  | .dead, .dead => allowDead = false
  | .dead, .live _ => allowDead = true
  | .live none, .live _ => True
  | .live (some v1), .live (some v2) => v1 = v2
  | _, _ => False

private theorem slotFwdRefines_refl_live (allowDead : Bool) (opt : Option Val) :
    SlotFwdRefines allowDead (.live opt) (.live opt) := by
  cases opt with
  | none => exact True.intro
  | some _ => rfl

private theorem slotFwdRefines_liveUninit_left {allowDead : Bool} {ty : MirTy}
    {optTgt : Option Val} (hWt : SlotWellTyped ty (.live optTgt)) :
    SlotFwdRefines allowDead (liveUninitSlot ty) (.live optTgt) := by
  cases hZ : isAlwaysInhabitedZst ty with
  | false =>
    rw [liveUninitSlot_of_not_zst hZ]
    exact True.intro
  | true =>
    rw [slot_eq_liveUninit_of_zst hZ hWt]
    let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
    rw [hOpt]
    exact slotFwdRefines_refl_live allowDead opt

private def LocalsFwdRefines (allowDead : Bool) (bodyLocals : List MirTy)
    (localsSrc localsTgt : List LocalSlot) : Prop :=
  localsSrc.length = bodyLocals.length ∧
  localsTgt.length = bodyLocals.length ∧
  ∀ i ty s1 s2,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? localsSrc i = some s1 →
    Trusted.MirSemantics.getElem? localsTgt i = some s2 →
    SlotFwdRefines allowDead s1 s2 ∧ SlotWellTyped ty s2

private theorem localsFwdRefines_set_both {allowDead : Bool}
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' localsTgt' : List LocalSlot}
    {id : Nat} {ty : MirTy} {s1' s2' : LocalSlot}
    (hInv : LocalsFwdRefines allowDead bodyLocals localsSrc localsTgt)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSet1 : setElem? localsSrc id s1' = some localsSrc')
    (hSet2 : setElem? localsTgt id s2' = some localsTgt')
    (hSlot : SlotFwdRefines allowDead s1' s2')
    (hWt : SlotWellTyped ty s2') :
    LocalsFwdRefines allowDead bodyLocals localsSrc' localsTgt' := by
  let ⟨hLen1, hLen2, hAll⟩ := hInv
  refine ⟨by rw [setElem?_length hSet1, hLen1],
          by rw [setElem?_length hSet2, hLen2], ?_⟩
  intro i tyi a b hTyi hA hB
  cases hEq : Nat.beq i id with
  | true =>
    have hi : i = id := nat_beq_eq hEq
    subst hi
    rw [hTy] at hTyi; injection hTyi with hEqTy; subst hEqTy
    rw [setElem?_getElem?_same hSet1] at hA; injection hA with hEqA; subst hEqA
    rw [setElem?_getElem?_same hSet2] at hB; injection hB with hEqB; subst hEqB
    exact ⟨hSlot, hWt⟩
  | false =>
    have hNe : i ≠ id := fun h => by rw [h, nat_beq_refl] at hEq; cases hEq
    rw [setElem?_getElem?_ne hSet1 hNe] at hA
    rw [setElem?_getElem?_ne hSet2 hNe] at hB
    exact hAll i tyi a b hTyi hA hB

private theorem localsFwdRefines_set_left {allowDead : Bool}
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {id : Nat} {ty : MirTy} {s1' s2 : LocalSlot}
    (hInv : LocalsFwdRefines allowDead bodyLocals localsSrc localsTgt)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hGet2 : Trusted.MirSemantics.getElem? localsTgt id = some s2)
    (hSet1 : setElem? localsSrc id s1' = some localsSrc')
    (hSlot : SlotFwdRefines allowDead s1' s2) :
    LocalsFwdRefines allowDead bodyLocals localsSrc' localsTgt := by
  let ⟨hLen1, hLen2, hAll⟩ := hInv
  refine ⟨by rw [setElem?_length hSet1, hLen1], hLen2, ?_⟩
  intro i tyi a b hTyi hA hB
  cases hEq : Nat.beq i id with
  | true =>
    have hi : i = id := nat_beq_eq hEq
    subst hi
    rw [hTy] at hTyi; injection hTyi with hEqTy; subst hEqTy
    rw [setElem?_getElem?_same hSet1] at hA; injection hA with hEqA; subst hEqA
    rw [hGet2] at hB; injection hB with hEqB; subst hEqB
    let ⟨s1Old, hGet1Old⟩ := getElem?_some_of_lt localsSrc i
      (by rw [hLen1]; exact getElem?_some_lt hTy)
    let ⟨_, hWt⟩ := hAll i ty s1Old s2 hTy hGet1Old hGet2
    exact ⟨hSlot, hWt⟩
  | false =>
    have hNe : i ≠ id := fun h => by rw [h, nat_beq_refl] at hEq; cases hEq
    rw [setElem?_getElem?_ne hSet1 hNe] at hA
    exact hAll i tyi a b hTyi hA hB

private theorem evalOperandToSlot_fwd {allowDead : Bool}
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {opSrc opTgt : Operand} {ty : MirTy} {v : Val}
    (hInv : LocalsFwdRefines allowDead bodyLocals localsSrc localsTgt)
    (hOp : isMoveToCopyOperand opSrc opTgt = true)
    (hEval : evalOperandToSlot bodyLocals localsSrc opSrc =
      .ok (ty, some v, localsSrc')) :
    ∃ localsTgt',
      evalOperandToSlot bodyLocals localsTgt opTgt =
        .ok (ty, some v, localsTgt') ∧
      LocalsFwdRefines allowDead bodyLocals localsSrc' localsTgt' := by
  let ⟨hLen1, hLen2, hAll⟩ := hInv
  cases opSrc with
  | constant c1 =>
    cases opTgt with
    | constant c2 =>
      have hc : c1 = c2 := constOpEq_eq hOp
      subst hc
      dsimp [evalOperandToSlot] at hEval
      cases hC : evalConstLit c1.ty c1.lit with
      | error _ => rw [hC] at hEval; cases hEval
      | ok val =>
        rw [hC] at hEval
        injection hEval with hEq
        injection hEq with hTyEq hRest
        injection hRest with hVEq hLocEq
        injection hVEq with hV
        subst hTyEq; subst hV; subst hLocEq
        refine ⟨localsTgt, ?_, hInv⟩
        dsimp [evalOperandToSlot]
        rw [hC]
    | _ => cases hOp
  | copy p1 =>
    cases opTgt with
    | copy p2 =>
      have hp : p1 = p2 := placeEq_eq hOp
      subst hp
      dsimp [evalOperandToSlot] at hEval
      cases hProj : p1.projection.isEmpty with
      | false => rw [hProj] at hEval; cases hEval
      | true =>
        rw [hProj] at hEval
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals p1.localId with
        | none => rw [hTy] at hEval; cases hEval
        | some t =>
          rw [hTy] at hEval
          cases hS1 : Trusted.MirSemantics.getElem? localsSrc p1.localId with
          | none => rw [hS1] at hEval; cases hEval
          | some slot1 =>
            rw [hS1] at hEval
            cases slot1 with
            | dead => cases hEval
            | live opt1 =>
              dsimp at hEval
              injection hEval with hEq
              injection hEq with hTyEq hRest
              injection hRest with hOptEq hLocEq
              subst hTyEq; subst hOptEq; subst hLocEq
              let ⟨slot2, hS2⟩ := getElem?_some_of_lt localsTgt p1.localId
                (by rw [hLen2]; exact getElem?_some_lt hTy)
              let ⟨hRef, _⟩ := hAll p1.localId t (.live (some v)) slot2 hTy hS1 hS2
              cases slot2 with
              | dead => cases hRef
              | live opt2 =>
                cases opt2 with
                | none => cases hRef
                | some v2 =>
                  have hv : v = v2 := hRef
                  subst hv
                  refine ⟨localsTgt, ?_, hInv⟩
                  dsimp [evalOperandToSlot]
                  rw [hProj, hTy, hS2]
                  rfl
    | _ => cases hOp
  | move p1 =>
    cases opTgt with
    | constant _ => cases hOp
    | move p2 =>
      have hp : p1 = p2 := placeEq_eq hOp
      subst hp
      dsimp [evalOperandToSlot] at hEval
      cases hProj : p1.projection.isEmpty with
      | false => rw [hProj] at hEval; cases hEval
      | true =>
        rw [hProj] at hEval
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals p1.localId with
        | none => rw [hTy] at hEval; cases hEval
        | some t =>
          rw [hTy] at hEval
          cases hS1 : Trusted.MirSemantics.getElem? localsSrc p1.localId with
          | none => rw [hS1] at hEval; cases hEval
          | some slot1 =>
            rw [hS1] at hEval
            cases slot1 with
            | dead => cases hEval
            | live opt1 =>
              dsimp at hEval
              cases hSet1 : setElem? localsSrc p1.localId (liveUninitSlot t) with
              | none => rw [hSet1] at hEval; cases hEval
              | some locs1' =>
                rw [hSet1] at hEval
                injection hEval with hEq
                injection hEq with hTyEq hRest
                injection hRest with hOptEq hLocEq
                subst hTyEq; subst hOptEq; subst hLocEq
                let ⟨slot2, hS2⟩ := getElem?_some_of_lt localsTgt p1.localId
                  (by rw [hLen2]; exact getElem?_some_lt hTy)
                let ⟨hRef, _⟩ := hAll p1.localId t (.live (some v)) slot2 hTy hS1 hS2
                cases slot2 with
                | dead => cases hRef
                | live opt2 =>
                  cases opt2 with
                  | none => cases hRef
                  | some v2 =>
                    have hv : v = v2 := hRef
                    subst hv
                    let ⟨locs2', hSet2⟩ := setElem?_some_of_lt localsTgt p1.localId
                      (liveUninitSlot t) (by rw [hLen2]; exact getElem?_some_lt hTy)
                    let ⟨optU, hOptU⟩ := liveUninitSlot_isLive t
                    refine ⟨locs2', ?_, localsFwdRefines_set_both hInv hTy hSet1 hSet2
                      (by rw [hOptU]; exact slotFwdRefines_refl_live allowDead optU)
                      (liveUninitSlot_wellTyped t)⟩
                    dsimp [evalOperandToSlot]
                    rw [hProj, hTy, hS2]
                    dsimp
                    rw [hSet2]
    | copy p2 =>
      have hp : p1 = p2 := placeEq_eq hOp
      subst hp
      dsimp [evalOperandToSlot] at hEval
      cases hProj : p1.projection.isEmpty with
      | false => rw [hProj] at hEval; cases hEval
      | true =>
        rw [hProj] at hEval
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals p1.localId with
        | none => rw [hTy] at hEval; cases hEval
        | some t =>
          rw [hTy] at hEval
          cases hS1 : Trusted.MirSemantics.getElem? localsSrc p1.localId with
          | none => rw [hS1] at hEval; cases hEval
          | some slot1 =>
            rw [hS1] at hEval
            cases slot1 with
            | dead => cases hEval
            | live opt1 =>
              dsimp at hEval
              cases hSet1 : setElem? localsSrc p1.localId (liveUninitSlot t) with
              | none => rw [hSet1] at hEval; cases hEval
              | some locs1' =>
                rw [hSet1] at hEval
                injection hEval with hEq
                injection hEq with hTyEq hRest
                injection hRest with hOptEq hLocEq
                subst hTyEq; subst hOptEq; subst hLocEq
                let ⟨slot2, hS2⟩ := getElem?_some_of_lt localsTgt p1.localId
                  (by rw [hLen2]; exact getElem?_some_lt hTy)
                let ⟨hRef, hWt2⟩ := hAll p1.localId t (.live (some v)) slot2 hTy hS1 hS2
                cases slot2 with
                | dead => cases hRef
                | live opt2 =>
                  cases opt2 with
                  | none => cases hRef
                  | some v2 =>
                    have hv : v = v2 := hRef
                    subst hv
                    refine ⟨localsTgt, ?_, localsFwdRefines_set_left hInv hTy hS2 hSet1
                      (slotFwdRefines_liveUninit_left hWt2)⟩
                    dsimp [evalOperandToSlot]
                    rw [hProj, hTy, hS2]
                    rfl

private theorem evalPrimitiveOperand_fwd {allowDead : Bool}
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {opSrc opTgt : Operand} {v : Val}
    (hInv : LocalsFwdRefines allowDead bodyLocals localsSrc localsTgt)
    (hOp : isMoveToCopyOperand opSrc opTgt = true)
    (hEval : evalPrimitiveOperand bodyLocals localsSrc opSrc = .ok (v, localsSrc')) :
    ∃ localsTgt',
      evalPrimitiveOperand bodyLocals localsTgt opTgt = .ok (v, localsTgt') ∧
      LocalsFwdRefines allowDead bodyLocals localsSrc' localsTgt' := by
  dsimp [evalPrimitiveOperand] at hEval
  cases hS : evalOperandToSlot bodyLocals localsSrc opSrc with
  | error _ => rw [hS] at hEval; cases hEval
  | ok res =>
    let ⟨ty, optVal, locs1⟩ := res
    rw [hS] at hEval
    dsimp at hEval
    cases hPrim : isPrimitiveReadableTy ty with
    | false => rw [hPrim] at hEval; cases hEval
    | true =>
      rw [hPrim] at hEval
      dsimp at hEval
      cases optVal with
      | none => cases hEval
      | some v0 =>
        injection hEval with hEq
        injection hEq with hV hL
        subst hV; subst hL
        let ⟨locs2, hT, hInv'⟩ := evalOperandToSlot_fwd hInv hOp hS
        refine ⟨locs2, ?_, hInv'⟩
        dsimp [evalPrimitiveOperand]
        rw [hT]
        dsimp
        rw [hPrim]
        rfl

private theorem evalRvalue_fwd {allowDead : Bool}
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {dstTy : MirTy} {rvSrc rvTgt : Rvalue} {v : Val}
    (hInv : LocalsFwdRefines allowDead bodyLocals localsSrc localsTgt)
    (hRv : rvalueRel isMoveToCopyOperand rvSrc rvTgt = true)
    (hEval : evalRvalue bodyLocals localsSrc dstTy rvSrc = .ok (v, localsSrc')) :
    ∃ localsTgt',
      evalRvalue bodyLocals localsTgt dstTy rvTgt = .ok (v, localsTgt') ∧
      LocalsFwdRefines allowDead bodyLocals localsSrc' localsTgt' := by
  cases rvSrc with
  | use o1 =>
    cases rvTgt with
    | use o2 =>
      dsimp [evalRvalue] at hEval
      cases hS : evalOperandToSlot bodyLocals localsSrc o1 with
      | error _ => rw [hS] at hEval; cases hEval
      | ok res =>
        let ⟨srcTy, optVal, locs1⟩ := res
        rw [hS] at hEval
        dsimp at hEval
        cases hEqTy : MirTy.beq srcTy dstTy with
        | false => rw [hEqTy] at hEval; cases hEval
        | true =>
          rw [hEqTy] at hEval
          dsimp at hEval
          cases optVal with
          | none => cases hEval
          | some v0 =>
            injection hEval with hEq
            injection hEq with hV hL
            subst hV; subst hL
            let ⟨locs2, hT, hInv'⟩ := evalOperandToSlot_fwd hInv hRv hS
            refine ⟨locs2, ?_, hInv'⟩
            dsimp [evalRvalue]
            rw [hT]
            dsimp
            rw [hEqTy]
            rfl
    | _ => cases hRv
  | binaryOp op1 l1 r1 =>
    cases rvTgt with
    | binaryOp op2 l2 r2 =>
      let ⟨h12, hR⟩ := bool_and_true hRv
      let ⟨hOp, hL⟩ := bool_and_true h12
      have hOpEq : op1 = op2 := binOpEq_eq hOp
      subst hOpEq
      dsimp [evalRvalue] at hEval
      cases hEL : evalPrimitiveOperand bodyLocals localsSrc l1 with
      | error _ => rw [hEL] at hEval; cases hEval
      | ok resL =>
        let ⟨lv, locs1⟩ := resL
        rw [hEL] at hEval
        dsimp at hEval
        cases hER : evalPrimitiveOperand bodyLocals locs1 r1 with
        | error _ => rw [hER] at hEval; cases hEval
        | ok resR =>
          let ⟨rv, locs2⟩ := resR
          rw [hER] at hEval
          dsimp at hEval
          cases hBin : evalBinOp op1 lv rv with
          | error _ => rw [hBin] at hEval; cases hEval
          | ok resV =>
            rw [hBin] at hEval
            injection hEval with hEq
            injection hEq with hV hLoc
            subst hV; subst hLoc
            let ⟨tLocs1, hTL, hInv1⟩ := evalPrimitiveOperand_fwd hInv hL hEL
            let ⟨tLocs2, hTR, hInv2⟩ := evalPrimitiveOperand_fwd hInv1 hR hER
            refine ⟨tLocs2, ?_, hInv2⟩
            dsimp [evalRvalue]
            rw [hTL]
            dsimp
            rw [hTR]
            dsimp
            rw [hBin]
    | _ => cases hRv
  | unaryOp op1 o1 =>
    cases rvTgt with
    | unaryOp op2 o2 =>
      let ⟨hOp, hO⟩ := bool_and_true hRv
      have hOpEq : op1 = op2 := unOpEq_eq hOp
      subst hOpEq
      dsimp [evalRvalue] at hEval
      cases hEO : evalPrimitiveOperand bodyLocals localsSrc o1 with
      | error _ => rw [hEO] at hEval; cases hEval
      | ok resO =>
        let ⟨ov, locs1⟩ := resO
        rw [hEO] at hEval
        dsimp at hEval
        cases hUn : evalUnOp op1 ov with
        | error _ => rw [hUn] at hEval; cases hEval
        | ok resV =>
          rw [hUn] at hEval
          injection hEval with hEq
          injection hEq with hV hLoc
          subst hV; subst hLoc
          let ⟨tLocs1, hTO, hInv1⟩ := evalPrimitiveOperand_fwd hInv hO hEO
          refine ⟨tLocs1, ?_, hInv1⟩
          dsimp [evalRvalue]
          rw [hTO]
          dsimp
          rw [hUn]
    | _ => cases hRv
  | discriminant p1 =>
    cases rvTgt with
    | discriminant p2 =>
      have hp : p1 = p2 := placeEq_eq hRv
      subst hp
      let ⟨_, hLen2, hAll⟩ := hInv
      dsimp [evalRvalue] at hEval
      cases hProj : p1.projection.isEmpty with
      | false => rw [hProj] at hEval; cases hEval
      | true =>
        rw [hProj] at hEval
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals p1.localId with
        | none => rw [hTy] at hEval; cases hEval
        | some ty =>
          rw [hTy] at hEval
          cases ty with
          | enum ety =>
            cases hS1 : Trusted.MirSemantics.getElem? localsSrc p1.localId with
            | none => rw [hS1] at hEval; cases hEval
            | some slot1 =>
              rw [hS1] at hEval
              dsimp at hEval
              cases hAdm : enumAdmitted ety with
              | false => rw [hAdm] at hEval; cases hEval
              | true =>
                rw [hAdm] at hEval
                dsimp at hEval
                let ⟨slot2, hS2⟩ := getElem?_some_of_lt localsTgt p1.localId
                  (by rw [hLen2]; exact getElem?_some_lt hTy)
                let ⟨hRef, hWt2⟩ := hAll p1.localId (.enum ety) slot1 slot2 hTy hS1 hS2
                cases hTr : ety.tagRepr with
                | zeroSized =>
                  rw [hTr] at hEval
                  cases slot1 with
                  | dead => cases hEval
                  | live opt1 =>
                    cases slot2 with
                    | dead => cases opt1 <;> cases hRef
                    | live opt2 =>
                      have hZstE : isZstEnumTy ety = true := by
                        unfold isZstEnumTy
                        rw [hTr]
                        exact hAdm
                      have hZst : isAlwaysInhabitedZst (.enum ety) = true := hZstE
                      have hS2Eq : LocalSlot.live opt2 = .live (some (.enumVal ety 0)) := by
                        have hEqU := slot_eq_liveUninit_of_zst hZst hWt2
                        dsimp [liveUninitSlot] at hEqU
                        rw [hZstE] at hEqU
                        exact hEqU
                      injection hS2Eq with hOpt2
                      subst hOpt2
                      cases opt1 with
                      | none =>
                        dsimp at hEval
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEval; cases hEval
                        | some disc =>
                          rw [hD] at hEval
                          injection hEval with hEq
                          injection hEq with hV hL
                          subst hV; subst hL
                          refine ⟨localsTgt, ?_, hInv⟩
                          dsimp [evalRvalue]
                          rw [hProj, hTy, hS2]
                          dsimp
                          rw [hAdm]
                          dsimp
                          rw [hTr]
                          dsimp
                          rw [enumTy_beq_refl ety]
                          dsimp [Nat.beq]
                          rw [hD]
                      | some v1 =>
                        have hv1 : v1 = .enumVal ety 0 := hRef
                        subst hv1
                        dsimp at hEval
                        rw [enumTy_beq_refl ety] at hEval
                        dsimp [Nat.beq] at hEval
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEval; cases hEval
                        | some disc =>
                          rw [hD] at hEval
                          injection hEval with hEq
                          injection hEq with hV hL
                          subst hV; subst hL
                          refine ⟨localsTgt, ?_, hInv⟩
                          dsimp [evalRvalue]
                          rw [hProj, hTy, hS2]
                          dsimp
                          rw [hAdm]
                          dsimp
                          rw [hTr]
                          dsimp
                          rw [enumTy_beq_refl ety]
                          dsimp [Nat.beq]
                          rw [hD]
                | scalar tw ts =>
                  rw [hTr] at hEval
                  cases slot1 with
                  | dead => cases hEval
                  | live opt1 =>
                    cases opt1 with
                    | none => cases hEval
                    | some v1 =>
                      cases slot2 with
                      | dead => cases hRef
                      | live opt2 =>
                        cases opt2 with
                        | none => cases hRef
                        | some v2 =>
                          have hv : v1 = v2 := hRef
                          subst hv
                          cases v1 with
                          | enumVal ety' k =>
                            dsimp at hEval
                            cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                            | false => rw [hC] at hEval; cases hEval
                            | true =>
                              rw [hC] at hEval
                              dsimp at hEval
                              cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                              | none => rw [hD] at hEval; cases hEval
                              | some disc =>
                                rw [hD] at hEval
                                injection hEval with hEq
                                injection hEq with hV hL
                                subst hV; subst hL
                                refine ⟨localsTgt, ?_, hInv⟩
                                dsimp [evalRvalue]
                                rw [hProj, hTy, hS2]
                                dsimp
                                rw [hAdm]
                                dsimp
                                rw [hTr]
                                dsimp
                                rw [hC]
                                dsimp
                                rw [hD]
                          | scalar _ => cases hEval
                          | ptr _ => cases hEval
                          | bool _ => cases hEval
                          | unit => cases hEval
                          | tuple _ => cases hEval
                          | bytes _ => cases hEval
          | bool => cases hEval
          | int _ _ => cases hEval
          | unit => cases hEval
          | never => cases hEval
          | tuple _ => cases hEval
          | ref _ _ => cases hEval
          | rawPtr _ _ => cases hEval
          | unsupported => cases hEval
    | _ => cases hRv
  | ref _ _ => cases hEval
  | addressOf _ _ => cases hEval
  | aggregateTuple _ => cases hEval
  | unsupported => cases hEval

private theorem writePlace_fwd {allowDead : Bool}
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {dstId : LocalId} {dstTy : MirTy} {val : Val}
    (hInv : LocalsFwdRefines allowDead bodyLocals localsSrc localsTgt)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (hWrite : writePlace localsSrc dstId dstTy val = .ok localsSrc') :
    ∃ localsTgt',
      writePlace localsTgt dstId dstTy val = .ok localsTgt' ∧
      LocalsFwdRefines allowDead bodyLocals localsSrc' localsTgt' := by
  let ⟨_, hLen2, hAll⟩ := hInv
  dsimp [writePlace] at hWrite
  cases hChk : checkVal val dstTy with
  | false => rw [hChk] at hWrite; cases hWrite
  | true =>
    rw [hChk] at hWrite
    cases hS1 : Trusted.MirSemantics.getElem? localsSrc dstId with
    | none => rw [hS1] at hWrite; cases hWrite
    | some slot1 =>
      rw [hS1] at hWrite
      cases slot1 with
      | dead => cases hWrite
      | live opt1 =>
        cases hSet1 : setElem? localsSrc dstId (.live (some val)) with
        | none => rw [hSet1] at hWrite; cases hWrite
        | some locs1' =>
          rw [hSet1] at hWrite
          injection hWrite with hEq
          subst hEq
          let ⟨slot2, hS2⟩ := getElem?_some_of_lt localsTgt dstId
            (by rw [hLen2]; exact getElem?_some_lt hTy)
          let ⟨hRef, _⟩ := hAll dstId dstTy (.live opt1) slot2 hTy hS1 hS2
          cases slot2 with
          | dead => cases opt1 <;> cases hRef
          | live opt2 =>
            let ⟨locs2', hSet2⟩ := setElem?_some_of_lt localsTgt dstId
              (.live (some val)) (by rw [hLen2]; exact getElem?_some_lt hTy)
            refine ⟨locs2', ?_, localsFwdRefines_set_both hInv hTy hSet1 hSet2 rfl hChk⟩
            dsimp [writePlace]
            rw [hChk]
            dsimp
            rw [hS2]
            dsimp
            rw [hSet2]

private theorem evalTerminator_fwd {allowDead : Bool}
    {bSrc bTgt : Body} {bbSrc bbTgt : BasicBlock}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hLocsEq : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hTerm : terminatorRel isMoveToCopyOperand bbSrc.terminator bbTgt.terminator = true)
    (hInv : LocalsFwdRefines allowDead bSrc.locals fSrc.locals fTgt.locals) :
    (∀ s', evalTerminator bSrc bbSrc fSrc cm = .step s' →
      ∃ fSrc' fTgt',
        s' = { frames := [fSrc'], callerMem := cm } ∧
        evalTerminator bTgt bbTgt fTgt cm = .step { frames := [fTgt'], callerMem := cm } ∧
        fSrc'.defId = fSrc.defId ∧ fTgt'.defId = fTgt.defId ∧
        fSrc'.blockIdx = fTgt'.blockIdx ∧
        fSrc'.stmtIdx = fTgt'.stmtIdx ∧
        LocalsFwdRefines allowDead bSrc.locals fSrc'.locals fTgt'.locals) ∧
    (∀ out, evalTerminator bSrc bbSrc fSrc cm = .done out →
      evalTerminator bTgt bbTgt fTgt cm = .done out) := by
  cases hTS : bbSrc.terminator with
  | goto t1 =>
    cases hTT : bbTgt.terminator with
    | goto t2 =>
      rw [hTS, hTT] at hTerm
      have ht : t1 = t2 := nat_beq_eq hTerm
      subst ht
      constructor
      · intro s' hEv
        dsimp [evalTerminator] at hEv
        rw [hTS] at hEv
        dsimp [jumpToBlock] at hEv
        injection hEv with hEqS
        subst hEqS
        refine ⟨{ fSrc with blockIdx := t1, stmtIdx := 0 },
                { fTgt with blockIdx := t1, stmtIdx := 0 }, rfl, ?_,
                rfl, rfl, rfl, rfl, hInv⟩
        dsimp [evalTerminator]
        rw [hTT]
        rfl
      · intro out hEv
        dsimp [evalTerminator] at hEv
        rw [hTS] at hEv
        cases hEv
    | _ => rw [hTS, hTT] at hTerm; cases hTerm
  | return_ =>
    cases hTT : bbTgt.terminator with
    | return_ =>
      constructor
      · intro s' hEv
        dsimp [evalTerminator] at hEv
        rw [hTS] at hEv
        dsimp at hEv
        cases hC : bbSrc.cleanup with
        | true => rw [hC] at hEv; cases hEv
        | false =>
          rw [hC] at hEv
          dsimp at hEv
          cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
          | none => rw [h0] at hEv; cases hEv
          | some sl =>
            rw [h0] at hEv
            cases sl with
            | dead => cases hEv
            | live opt => cases opt <;> cases hEv
      · intro out hEv
        dsimp [evalTerminator] at hEv
        rw [hTS] at hEv
        dsimp at hEv
        cases hC : bbSrc.cleanup with
        | true => rw [hC] at hEv; cases hEv
        | false =>
          rw [hC] at hEv
          dsimp at hEv
          cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
          | none => rw [h0] at hEv; cases hEv
          | some sl =>
            rw [h0] at hEv
            cases sl with
            | dead => cases hEv
            | live opt =>
              cases opt with
              | none => cases hEv
              | some rv =>
                dsimp at hEv
                injection hEv with hEqOut
                subst hEqOut
                let ⟨hLen1, hLen2, hAll⟩ := hInv
                let ⟨ty0, hTy0⟩ := getElem?_some_of_lt bSrc.locals 0
                  (by rw [← hLen1]; exact getElem?_some_lt h0)
                let ⟨sl2, h02⟩ := getElem?_some_of_lt fTgt.locals 0
                  (by rw [hLen2]; exact getElem?_some_lt hTy0)
                let ⟨hRef, _⟩ := hAll 0 ty0 (.live (some rv)) sl2 hTy0 h0 h02
                cases sl2 with
                | dead => cases hRef
                | live opt2 =>
                  cases opt2 with
                  | none => cases hRef
                  | some rv2 =>
                    have hrv : rv = rv2 := hRef
                    subst hrv
                    dsimp [evalTerminator]
                    rw [hTT]
                    dsimp
                    rw [← hClean, hC]
                    dsimp
                    rw [h02]
    | _ => rw [hTS, hTT] at hTerm; cases hTerm
  | switchInt d1 ts1 =>
    cases hTT : bbTgt.terminator with
    | switchInt d2 ts2 =>
      rw [hTS, hTT] at hTerm
      let ⟨hD, hTs⟩ := bool_and_true hTerm
      have hTsEq : ts1 = ts2 := switchTargetsEq_eq hTs
      subst hTsEq
      constructor
      · intro s' hEv
        dsimp [evalTerminator] at hEv
        rw [hTS] at hEv
        dsimp at hEv
        cases hP : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
        | error _ => rw [hP] at hEv; cases hEv
        | ok res =>
          let ⟨dv, locs1⟩ := res
          rw [hP] at hEv
          dsimp at hEv
          let ⟨locs2, hPT, hInv'⟩ := evalPrimitiveOperand_fwd hInv hD hP
          cases dv with
          | scalar sv =>
            dsimp at hEv
            cases hTR : evalSwitchBranches sv.width sv.bits ts1.otherwise ts1.branches with
            | error _ => rw [hTR] at hEv; cases hEv
            | ok tgt =>
              rw [hTR] at hEv
              dsimp [jumpToBlock] at hEv
              injection hEv with hEqS
              subst hEqS
              refine ⟨{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs1 },
                      { fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2 },
                      rfl, ?_, rfl, rfl, rfl, rfl, hInv'⟩
              dsimp [evalTerminator]
              rw [hTT]
              dsimp
              rw [← hLocsEq, hPT]
              dsimp
              rw [hTR]
              rfl
          | bool b =>
            dsimp at hEv
            cases hTR : evalBoolSwitchBranches b ts1.otherwise ts1.branches with
            | error _ => rw [hTR] at hEv; cases hEv
            | ok tgt =>
              rw [hTR] at hEv
              dsimp [jumpToBlock] at hEv
              injection hEv with hEqS
              subst hEqS
              refine ⟨{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs1 },
                      { fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2 },
                      rfl, ?_, rfl, rfl, rfl, rfl, hInv'⟩
              dsimp [evalTerminator]
              rw [hTT]
              dsimp
              rw [← hLocsEq, hPT]
              dsimp
              rw [hTR]
              rfl
          | ptr _ => cases hEv
          | unit => cases hEv
          | enumVal _ _ => cases hEv
          | tuple _ => cases hEv
          | bytes _ => cases hEv
      · intro out hEv
        dsimp [evalTerminator] at hEv
        rw [hTS] at hEv
        dsimp at hEv
        cases hP : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
        | error _ => rw [hP] at hEv; cases hEv
        | ok res =>
          let ⟨dv, locs1⟩ := res
          rw [hP] at hEv
          dsimp at hEv
          cases dv with
          | scalar sv =>
            dsimp at hEv
            cases hTR : evalSwitchBranches sv.width sv.bits ts1.otherwise ts1.branches <;>
              rw [hTR] at hEv <;> cases hEv
          | bool b =>
            dsimp at hEv
            cases hTR : evalBoolSwitchBranches b ts1.otherwise ts1.branches <;>
              rw [hTR] at hEv <;> cases hEv
          | ptr _ => cases hEv
          | unit => cases hEv
          | enumVal _ _ => cases hEv
          | tuple _ => cases hEv
          | bytes _ => cases hEv
    | _ => rw [hTS, hTT] at hTerm; cases hTerm
  | unreachable =>
    constructor <;> (intro _ hEv; dsimp [evalTerminator] at hEv; rw [hTS] at hEv; cases hEv)
  | unwindResume =>
    constructor <;> (intro _ hEv; dsimp [evalTerminator] at hEv; rw [hTS] at hEv; cases hEv)
  | assert _ _ _ _ _ =>
    constructor <;> (intro _ hEv; dsimp [evalTerminator] at hEv; rw [hTS] at hEv; cases hEv)
  | call _ _ _ _ _ =>
    constructor <;> (intro _ hEv; dsimp [evalTerminator] at hEv; rw [hTS] at hEv; cases hEv)
  | unsupported =>
    constructor <;> (intro _ hEv; dsimp [evalTerminator] at hEv; rw [hTS] at hEv; cases hEv)

private theorem list_all_eq_of_rel {α β : Type} {r : α → β → Bool}
    {p : α → Bool} {q : β → Bool} {xs : List α} {ys : List β}
    (hRel : listRel r xs ys = true)
    (hPQ : ∀ a b, r a b = true → p a = q b) :
    xs.all p = ys.all q := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons a xs ih =>
    cases ys with
    | nil => cases hRel
    | cons b ys =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      dsimp [List.all]
      rw [hPQ a b hab, ih hTail]

private theorem list_any_eq_of_rel {α β : Type} {r : α → β → Bool}
    {p : α → Bool} {q : β → Bool} {xs : List α} {ys : List β}
    (hRel : listRel r xs ys = true)
    (hPQ : ∀ a b, r a b = true → p a = q b) :
    xs.any p = ys.any q := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons a xs ih =>
    cases ys with
    | nil => cases hRel
    | cons b ys =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      dsimp [List.any]
      rw [hPQ a b hab, ih hTail]

private theorem list_any_false_of_forall {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = false) :
    xs.any p = false := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    dsimp [List.any]
    rw [h 0 a rfl]
    exact ih (fun i x hi => h (i + 1) x hi)

private theorem moveToCopy_hasStorageAnnotation_eq {b1 b2 : Body} (idx : LocalId)
    (h : isMoveToCopyBody b1 b2 = true) :
    hasStorageAnnotation b1 idx = hasStorageAnnotation b2 idx := by
  unfold isMoveToCopyBody at h
  let ⟨_, hBlocks⟩ := bool_and_true h
  unfold hasStorageAnnotation
  exact list_any_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
    unfold isMoveToCopyBlock at hbb
    let ⟨h12, _⟩ := bool_and_true hbb
    let ⟨_, hStmts⟩ := bool_and_true h12
    exact list_any_eq_of_rel hStmts (fun s1 s2 hs => by
      cases s1 with
      | assign _ _ => cases s2 <;> first | rfl | cases hs
      | nop => cases s2 <;> first | rfl | cases hs
      | unsupported => cases s2 <;> first | rfl | cases hs
      | storageLive i1 =>
        cases s2 with
        | storageLive i2 =>
          have hi : i1 = i2 := nat_beq_eq hs
          rw [hi]
        | _ => cases hs
      | storageDead i1 =>
        cases s2 with
        | storageDead i2 =>
          have hi : i1 = i2 := nat_beq_eq hs
          rw [hi]
        | _ => cases hs))

private theorem moveToCopy_storageAnnotationsInBounds_eq {b1 b2 : Body}
    (h : isMoveToCopyBody b1 b2 = true) :
    storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 := by
  unfold isMoveToCopyBody at h
  let ⟨h1234, hBlocks⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨_, hLocs⟩ := bool_and_true h12
  have hLocEq : b1.locals = b2.locals := mirTy_beqList_eq hLocs
  unfold storageAnnotationsInBounds
  rw [hLocEq]
  exact list_all_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
    unfold isMoveToCopyBlock at hbb
    let ⟨h1, _⟩ := bool_and_true hbb
    let ⟨_, hStmts⟩ := bool_and_true h1
    exact list_all_eq_of_rel hStmts (fun s1 s2 hs => by
      cases s1 with
      | assign _ _ => cases s2 <;> first | rfl | cases hs
      | nop => cases s2 <;> first | rfl | cases hs
      | unsupported => cases s2 <;> first | rfl | cases hs
      | storageLive i1 =>
        cases s2 with
        | storageLive i2 => rw [nat_beq_eq hs]
        | _ => cases hs
      | storageDead i1 =>
        cases s2 with
        | storageDead i2 => rw [nat_beq_eq hs]
        | _ => cases hs))

private theorem removeStorage_storageAnnotationsInBounds_eq {b1 b2 : Body}
    (h : isRemoveStorageMarkersBody b1 b2 = true) :
    storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 := by
  unfold isRemoveStorageMarkersBody at h
  let ⟨h1234, hBlocks⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨_, hLocs⟩ := bool_and_true h12
  have hLocEq : b1.locals = b2.locals := mirTy_beqList_eq hLocs
  unfold storageAnnotationsInBounds
  rw [hLocEq]
  exact list_all_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
    unfold isRemoveStorageMarkersBlock at hbb
    let ⟨h1, _⟩ := bool_and_true hbb
    let ⟨_, hStmts⟩ := bool_and_true h1
    exact list_all_eq_of_rel hStmts (fun s1 s2 hs => by
      rw [hLocEq] at hs
      cases s1 with
      | assign _ _ => cases s2 <;> first | rfl | cases hs
      | nop => cases s2 <;> first | rfl | cases hs
      | unsupported => cases s2 <;> first | rfl | cases hs
      | storageLive i1 =>
        cases s2 with
        | nop => exact hs
        | storageLive i2 =>
          let ⟨_, hEq⟩ := bool_and_true hs
          rw [nat_beq_eq hEq]
        | _ => cases hs
      | storageDead i1 =>
        cases s2 with
        | nop =>
          let ⟨_, hLt⟩ := bool_and_true hs
          exact hLt
        | storageDead i2 =>
          let ⟨_, hEq⟩ := bool_and_true hs
          rw [nat_beq_eq hEq]
        | _ => cases hs))

private theorem removeStorage_no_storageAnnotation {b1 b2 : Body} {idx : LocalId}
    (h : isRemoveStorageMarkersBody b1 b2 = true)
    (hPos : 0 < idx) (hLt : idx < b2.locals.length) :
    hasStorageAnnotation b2 idx = false := by
  unfold isRemoveStorageMarkersBody at h
  let ⟨h1234, hBlocks⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨_, hLocs⟩ := bool_and_true h12
  have hLocEq : b1.locals = b2.locals := mirTy_beqList_eq hLocs
  unfold hasStorageAnnotation
  apply list_any_false_of_forall
  intro bi bb2 hBB2
  let ⟨bb1, _, hRelBB⟩ := listRel_getElem?_right hBlocks hBB2
  unfold isRemoveStorageMarkersBlock at hRelBB
  let ⟨h1, _⟩ := bool_and_true hRelBB
  let ⟨_, hStmts⟩ := bool_and_true h1
  apply list_any_false_of_forall
  intro si s2 hS2
  let ⟨s1, _, hRelS⟩ := listRel_getElem?_right hStmts hS2
  rw [hLocEq] at hRelS
  cases s2 with
  | assign _ _ => rfl
  | nop => rfl
  | unsupported => rfl
  | storageLive i2 =>
    cases s1 with
    | storageLive i1 =>
      let ⟨hNotLt, hEq⟩ := bool_and_true hRelS
      have h12Eq : i1 = i2 := nat_beq_eq hEq
      subst h12Eq
      have hGe : b2.locals.length ≤ i1 := nat_blt_false_ge (bool_not_true hNotLt)
      dsimp [stmtHasStorageMarker]
      exact nat_beq_false_of_ne (fun hEqIdx => by
        subst hEqIdx
        exact Nat.not_lt_of_ge hGe hLt)
    | _ => cases hRelS
  | storageDead i2 =>
    cases s1 with
    | storageDead i1 =>
      let ⟨hOr, hEq⟩ := bool_and_true hRelS
      have h12Eq : i1 = i2 := nat_beq_eq hEq
      subst h12Eq
      dsimp [stmtHasStorageMarker]
      cases bool_or_true hOr with
      | inl hZero =>
        have hi0 : i1 = 0 := nat_beq_eq hZero
        subst hi0
        exact nat_beq_false_of_ne (fun hEqIdx => by
          subst hEqIdx
          exact Nat.lt_irrefl 0 hPos)
      | inr hNotLt =>
        have hGe : b2.locals.length ≤ i1 := nat_blt_false_ge (bool_not_true hNotLt)
        exact nat_beq_false_of_ne (fun hEqIdx => by
          subst hEqIdx
          exact Nat.not_lt_of_ge hGe hLt)
    | _ => cases hRelS

private theorem initLocalsLoop_length (body : Body) (args : List Val)
    (base : Nat) (tys : List MirTy) :
    (initLocalsLoop body args base tys).length = tys.length := by
  induction tys generalizing base with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [initLocalsLoop, List.length]
    rw [ih (base + 1)]

private theorem initLocalsLoop_getElem? (body : Body) (args : List Val)
    (base : Nat) (tys : List MirTy) (i : Nat) (ty : MirTy)
    (hTy : Trusted.MirSemantics.getElem? tys i = some ty) :
    Trusted.MirSemantics.getElem? (initLocalsLoop body args base tys) i =
      some (if Nat.beq (base + i) 0 then
              liveUninitSlot ty
            else if Nat.ble (base + i) body.argumentCount then
              match Trusted.MirSemantics.getElem? args ((base + i) - 1) with
              | some v => .live (some v)
              | none => .dead
            else if hasStorageAnnotation body (base + i) then
              .dead
            else
              liveUninitSlot ty) := by
  induction tys generalizing base i with
  | nil => cases hTy
  | cons t rest ih =>
    cases i with
    | zero =>
      injection hTy with hEq
      subst hEq
      rfl
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTy
      rw [hAdd] at hRec
      exact hRec

private theorem initLocalsLoop_eq_of_moveToCopy {b1 b2 : Body} (args : List Val)
    (h : isMoveToCopyBody b1 b2 = true) :
    initLocalsLoop b1 args 0 b1.locals = initLocalsLoop b2 args 0 b2.locals := by
  have hCopy := h
  unfold isMoveToCopyBody at h
  let ⟨h1234, _⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨hArg, hLocs⟩ := bool_and_true h12
  have hArgEq : b1.argumentCount = b2.argumentCount := nat_beq_eq hArg
  have hLocEq : b1.locals = b2.locals := mirTy_beqList_eq hLocs
  rw [← hLocEq]
  have hLoop : ∀ base tys, initLocalsLoop b1 args base tys =
      initLocalsLoop b2 args base tys := by
    intro base tys
    induction tys generalizing base with
    | nil => rfl
    | cons ty rest ih =>
      dsimp [initLocalsLoop]
      rw [hArgEq, moveToCopy_hasStorageAnnotation_eq base hCopy, ih (base + 1)]
  exact hLoop 0 b1.locals

private theorem body_fields_of_moveToCopy {b1 b2 : Body}
    (h : isMoveToCopyBody b1 b2 = true) :
    b1.argumentCount = b2.argumentCount ∧
    b1.locals = b2.locals ∧
    b1.isUnsafe = b2.isUnsafe ∧
    stringBeq b1.identity "" = stringBeq b2.identity "" ∧
    b1.basicBlocks.length = b2.basicBlocks.length ∧
    storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 := by
  have hS := moveToCopy_storageAnnotationsInBounds_eq h
  unfold isMoveToCopyBody at h
  let ⟨h1234, hB⟩ := bool_and_true h
  let ⟨h123, hId⟩ := bool_and_true h1234
  let ⟨h12, hU⟩ := bool_and_true h123
  let ⟨hA, hL⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hA, mirTy_beqList_eq hL, bool_beq_eq hU,
         stringBeq_empty_congr hId, listRel_length hB, hS⟩

private theorem body_fields_of_removeStorage {b1 b2 : Body}
    (h : isRemoveStorageMarkersBody b1 b2 = true) :
    b1.argumentCount = b2.argumentCount ∧
    b1.locals = b2.locals ∧
    b1.isUnsafe = b2.isUnsafe ∧
    stringBeq b1.identity "" = stringBeq b2.identity "" ∧
    b1.basicBlocks.length = b2.basicBlocks.length ∧
    storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 := by
  have hS := removeStorage_storageAnnotationsInBounds_eq h
  unfold isRemoveStorageMarkersBody at h
  let ⟨h1234, hB⟩ := bool_and_true h
  let ⟨h123, hId⟩ := bool_and_true h1234
  let ⟨h12, hU⟩ := bool_and_true h123
  let ⟨hA, hL⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hA, mirTy_beqList_eq hL, bool_beq_eq hU,
         stringBeq_empty_congr hId, listRel_length hB, hS⟩

private theorem bodyStaticAdmitted_eq_of_fields {p1 p2 : Program} {b1 b2 : Body}
    (hPw : p1.pointerWidthBits = p2.pointerWidthBits)
    (hVer : p1.mirProfileVersion = p2.mirProfileVersion)
    (hArg : b1.argumentCount = b2.argumentCount)
    (hLoc : b1.locals = b2.locals)
    (hId : stringBeq b1.identity "" = stringBeq b2.identity "")
    (hBLen : b1.basicBlocks.length = b2.basicBlocks.length)
    (hSt : storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2) :
    BodyStaticAdmitted p1 b1 = BodyStaticAdmitted p2 b2 := by
  unfold BodyStaticAdmitted
  rw [hPw, hVer, hId, list_isEmpty_eq_of_length hBLen, hArg, hLoc, hSt]

private theorem initState_equiv {bodyRel : Body → Body → Bool}
    {pSrc pTgt : Program} (q : Query)
    (hPw : pSrc.pointerWidthBits = pTgt.pointerWidthBits)
    (hVer : pSrc.mirProfileVersion = pTgt.mirProfileVersion)
    (hEnt : pSrc.entryDefId = pTgt.entryDefId)
    (hBodies : listRel bodyRel pSrc.bodies pTgt.bodies = true)
    (hFields : ∀ b1 b2, bodyRel b1 b2 = true →
      b1.argumentCount = b2.argumentCount ∧
      b1.locals = b2.locals ∧
      b1.basicBlocks.length = b2.basicBlocks.length ∧
      storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2) :
    (∀ k, initState pSrc q = .error k ↔ initState pTgt q = .error k) ∧
    (∀ s₀, initState pSrc q = .ok s₀ →
      ∃ t₀ bSrc bTgt,
        initState pTgt q = .ok t₀ ∧
        Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some bSrc ∧
        Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some bTgt ∧
        bodyRel bSrc bTgt = true ∧
        bSrc.basicBlocks.isEmpty = false ∧
        bSrc.argumentCount < bSrc.locals.length ∧
        storageAnnotationsInBounds bSrc = true ∧
        checkArgsMatch q.args ((bSrc.locals.drop 1).take bSrc.argumentCount) = true ∧
        s₀ = {
          frames := [{
            defId := pSrc.entryDefId
            blockIdx := 0
            stmtIdx := 0
            locals := initLocalsLoop bSrc q.args 0 bSrc.locals
          }]
          callerMem := q.callerMem
        } ∧
        t₀ = {
          frames := [{
            defId := pTgt.entryDefId
            blockIdx := 0
            stmtIdx := 0
            locals := initLocalsLoop bTgt q.args 0 bTgt.locals
          }]
          callerMem := q.callerMem
        }) := by
  have hMain :
      (∃ k, initState pSrc q = .error k ∧ initState pTgt q = .error k) ∨
      (∃ bSrc bTgt,
        Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some bSrc ∧
        Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some bTgt ∧
        bodyRel bSrc bTgt = true ∧
        bSrc.basicBlocks.isEmpty = false ∧
        bSrc.argumentCount < bSrc.locals.length ∧
        storageAnnotationsInBounds bSrc = true ∧
        checkArgsMatch q.args ((bSrc.locals.drop 1).take bSrc.argumentCount) = true ∧
        initState pSrc q = .ok {
          frames := [{
            defId := pSrc.entryDefId
            blockIdx := 0
            stmtIdx := 0
            locals := initLocalsLoop bSrc q.args 0 bSrc.locals
          }]
          callerMem := q.callerMem
        } ∧
        initState pTgt q = .ok {
          frames := [{
            defId := pTgt.entryDefId
            blockIdx := 0
            stmtIdx := 0
            locals := initLocalsLoop bTgt q.args 0 bTgt.locals
          }]
          callerMem := q.callerMem
        }) := by
    cases hC1 : (!Nat.beq pSrc.pointerWidthBits 64 || !Nat.beq pSrc.mirProfileVersion 1) with
    | true =>
      left
      refine ⟨.unsupported, ?_, ?_⟩
      · unfold initState; rw [hC1]; rfl
      · unfold initState; rw [← hPw, ← hVer, hC1]; rfl
    | false =>
      cases hC2 : (!q.callerMem.allocations.isEmpty) with
      | true =>
        left
        refine ⟨.unsupported, ?_, ?_⟩
        · unfold initState; rw [hC1, hC2]; rfl
        · unfold initState; rw [← hPw, ← hVer, hC1, hC2]; rfl
      | false =>
        cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId with
        | none =>
          have hBT : Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = none := by
            rw [← hEnt]
            exact (listRel_getElem?_none_iff pSrc.entryDefId hBodies).mp hBS
          left
          refine ⟨.unsupported, ?_, ?_⟩
          · unfold initState; rw [hC1, hC2]; dsimp; rw [hBS]
          · unfold initState; rw [← hPw, ← hVer, hC1, hC2]; dsimp; rw [hBT]
        | some bSrc =>
          let ⟨bTgt, hBT0, hRelB⟩ := listRel_getElem?_left hBodies hBS
          have hBT : Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some bTgt := by
            rw [← hEnt]; exact hBT0
          let ⟨hArg, hLoc, hBLen, hSt⟩ := hFields bSrc bTgt hRelB
          have hEmpty : bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty :=
            list_isEmpty_eq_of_length hBLen
          cases hE : bSrc.basicBlocks.isEmpty with
          | true =>
            left
            refine ⟨.unsupported, ?_, ?_⟩
            · unfold initState; rw [hC1, hC2]; dsimp; rw [hBS]; dsimp; rw [hE]; rfl
            · unfold initState; rw [← hPw, ← hVer, hC1, hC2]; dsimp; rw [hBT]; dsimp
              rw [← hEmpty, hE]; rfl
          | false =>
            cases hAL : Nat.blt bSrc.argumentCount bSrc.locals.length with
            | false =>
              left
              refine ⟨.unsupported, ?_, ?_⟩
              · unfold initState; rw [hC1, hC2]; dsimp; rw [hBS]; dsimp
                rw [hE, hAL]; rfl
              · unfold initState; rw [← hPw, ← hVer, hC1, hC2]; dsimp; rw [hBT]; dsimp
                rw [← hEmpty, hE, ← hArg, ← hLoc, hAL]; rfl
            | true =>
              cases hSB : storageAnnotationsInBounds bSrc with
              | false =>
                left
                refine ⟨.unsupported, ?_, ?_⟩
                · unfold initState; rw [hC1, hC2]; dsimp; rw [hBS]; dsimp
                  rw [hE, hAL, hSB]; rfl
                · unfold initState; rw [← hPw, ← hVer, hC1, hC2]; dsimp; rw [hBT]; dsimp
                  rw [← hEmpty, hE, ← hArg, ← hLoc, hAL, ← hSt, hSB]; rfl
              | true =>
                cases hSup : bSrc.locals.all isSupportedScalarOrUnitTy with
                | false =>
                  left
                  refine ⟨.unsupported, ?_, ?_⟩
                  · unfold initState; rw [hC1, hC2]; dsimp; rw [hBS]; dsimp
                    rw [hE, hAL, hSB, hSup]; rfl
                  · unfold initState; rw [← hPw, ← hVer, hC1, hC2]; dsimp; rw [hBT]; dsimp
                    rw [← hEmpty, hE, ← hArg, ← hLoc, hAL, ← hSt, hSB, hSup]; rfl
                | true =>
                  cases hArgs : checkArgsMatch q.args ((bSrc.locals.drop 1).take bSrc.argumentCount) with
                  | false =>
                    left
                    refine ⟨.unsupported, ?_, ?_⟩
                    · unfold initState; rw [hC1, hC2]; dsimp; rw [hBS]; dsimp
                      rw [hE, hAL, hSB, hSup, hArgs]; rfl
                    · unfold initState; rw [← hPw, ← hVer, hC1, hC2]; dsimp; rw [hBT]; dsimp
                      rw [← hEmpty, hE, ← hArg, ← hLoc, hAL, ← hSt, hSB, hSup, hArgs]; rfl
                  | true =>
                    right
                    refine ⟨bSrc, bTgt, rfl, hBT, hRelB, hE, nat_blt_lt hAL, hSB, hArgs, ?_, ?_⟩
                    · unfold initState; rw [hC1, hC2]; dsimp; rw [hBS]; dsimp
                      rw [hE, hAL, hSB, hSup, hArgs]; rfl
                    · unfold initState; rw [← hPw, ← hVer, hC1, hC2]; dsimp; rw [hBT]; dsimp
                      rw [← hEmpty, hE, ← hArg, ← hLoc, hAL, ← hSt, hSB, hSup, hArgs]; rfl
  constructor
  · intro k
    cases hMain with
    | inl hErr =>
      let ⟨k0, h1, h2⟩ := hErr
      rw [h1, h2]
    | inr hOk =>
      let ⟨_, _, _, _, _, _, _, _, _, h1, h2⟩ := hOk
      rw [h1, h2]
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  · intro s₀ hInitS
    cases hMain with
    | inl hErr =>
      let ⟨_, h1, _⟩ := hErr
      rw [h1] at hInitS
      cases hInitS
    | inr hOk =>
      let ⟨bSrc, bTgt, hBS, hBT, hRelB, hE, hAL, hSB, hArgs, h1, h2⟩ := hOk
      rw [h1] at hInitS
      injection hInitS with hEqS
      subst hEqS
      exact ⟨_, bSrc, bTgt, h2, hBS, hBT, hRelB, hE, hAL, hSB, hArgs, rfl, rfl⟩

private theorem listRel_mono {α β : Type} {r1 r2 : α → β → Bool}
    (hImp : ∀ a b, r1 a b = true → r2 a b = true)
    {xs : List α} {ys : List β} (h : listRel r1 xs ys = true) :
    listRel r2 xs ys = true := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      let ⟨h1, h2⟩ := bool_and_true h
      dsimp [listRel]
      rw [hImp x y h1, ih h2]
      rfl

private theorem rvalueRel_operandEq_imp_moveToCopy {rv1 rv2 : Rvalue}
    (h : rvalueRel operandEq rv1 rv2 = true) :
    rvalueRel isMoveToCopyOperand rv1 rv2 = true := by
  cases rv1 with
  | use o1 =>
    cases rv2 with
    | use o2 => exact operandEq_imp_moveToCopy h
    | _ => cases h
  | binaryOp op1 l1 r1 =>
    cases rv2 with
    | binaryOp op2 l2 r2 =>
      let ⟨h12, hR⟩ := bool_and_true h
      let ⟨hOp, hL⟩ := bool_and_true h12
      dsimp [rvalueRel]
      rw [hOp, operandEq_imp_moveToCopy hL, operandEq_imp_moveToCopy hR]
      rfl
    | _ => cases h
  | unaryOp op1 o1 =>
    cases rv2 with
    | unaryOp op2 o2 =>
      let ⟨hOp, hO⟩ := bool_and_true h
      dsimp [rvalueRel]
      rw [hOp, operandEq_imp_moveToCopy hO]
      rfl
    | _ => cases h
  | discriminant _ => cases rv2 <;> first | exact h | cases h
  | ref _ _ => cases rv2 <;> first | exact h | cases h
  | addressOf _ _ => cases rv2 <;> first | exact h | cases h
  | aggregateTuple fs1 =>
    cases rv2 with
    | aggregateTuple fs2 =>
      exact listRel_mono (fun _ _ => operandEq_imp_moveToCopy) h
    | _ => cases h
  | unsupported => cases rv2 <;> first | exact h | cases h

private theorem terminatorRel_operandEq_imp_moveToCopy {t1 t2 : TerminatorKind}
    (h : terminatorRel operandEq t1 t2 = true) :
    terminatorRel isMoveToCopyOperand t1 t2 = true := by
  cases t1 with
  | goto _ => cases t2 <;> first | exact h | cases h
  | return_ => cases t2 <;> first | exact h | cases h
  | unreachable => cases t2 <;> first | exact h | cases h
  | unwindResume => cases t2 <;> first | exact h | cases h
  | unsupported => cases t2 <;> first | exact h | cases h
  | switchInt d1 ts1 =>
    cases t2 with
    | switchInt d2 ts2 =>
      let ⟨hD, hTs⟩ := bool_and_true h
      dsimp [terminatorRel]
      rw [operandEq_imp_moveToCopy hD, hTs]
      rfl
    | _ => cases h
  | assert c1 e1 m1 t1 u1 =>
    cases t2 with
    | assert c2 e2 m2 t2 u2 =>
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      dsimp [terminatorRel]
      rw [operandEq_imp_moveToCopy h1, h2, h3, h4, h5]
      rfl
    | _ => cases h
  | call f1 as1 d1 t1 u1 =>
    cases t2 with
    | call f2 as2 d2 t2 u2 =>
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      dsimp [terminatorRel]
      rw [h1, listRel_mono (fun _ _ => operandEq_imp_moveToCopy) h2, h3, h4, h5]
      rfl
    | _ => cases h

private theorem initLocalsLoop_fwd_moveToCopy {bSrc bTgt : Body} {args : List Val}
    (hRel : isMoveToCopyBody bSrc bTgt = true)
    (hArgs : checkArgsMatch args ((bSrc.locals.drop 1).take bSrc.argumentCount) = true) :
    LocalsFwdRefines false bSrc.locals
      (initLocalsLoop bSrc args 0 bSrc.locals)
      (initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨_, hLocEq, _, _, _, _⟩ := body_fields_of_moveToCopy hRel
  rw [← initLocalsLoop_eq_of_moveToCopy args hRel]
  refine ⟨initLocalsLoop_length bSrc args 0 bSrc.locals,
          initLocalsLoop_length bSrc args 0 bSrc.locals, ?_⟩
  intro i ty s1 s2 hTy hS1 hS2
  rw [hS1] at hS2; injection hS2 with hEqS; subst hEqS
  have hGet := initLocalsLoop_getElem? bSrc args 0 bSrc.locals i ty hTy
  rw [Nat.zero_add] at hGet
  rw [hGet] at hS1
  injection hS1 with hS1Eq
  subst hS1Eq
  cases i with
  | zero =>
    dsimp [Nat.beq]
    let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
    exact ⟨by rw [hOpt]; exact slotFwdRefines_refl_live false opt,
           liveUninitSlot_wellTyped ty⟩
  | succ k =>
    dsimp [Nat.beq]
    cases hLe : Nat.ble (k + 1) bSrc.argumentCount with
    | true =>
      dsimp
      have hKlt : k < bSrc.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((bSrc.locals.drop 1).take bSrc.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 bSrc.locals bSrc.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]
      exact ⟨rfl, hChk⟩
    | false =>
      dsimp
      cases hasStorageAnnotation bSrc (k + 1) with
      | true => exact ⟨rfl, True.intro⟩
      | false =>
        let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
        exact ⟨by rw [hOpt]; exact slotFwdRefines_refl_live false opt,
               liveUninitSlot_wellTyped ty⟩

private theorem initLocalsLoop_fwd_removeStorage {bSrc bTgt : Body} {args : List Val}
    (hRel : isRemoveStorageMarkersBody bSrc bTgt = true)
    (hArgs : checkArgsMatch args ((bSrc.locals.drop 1).take bSrc.argumentCount) = true) :
    LocalsFwdRefines true bSrc.locals
      (initLocalsLoop bSrc args 0 bSrc.locals)
      (initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨hArgEq, hLocEq, _, _, _, _⟩ := body_fields_of_removeStorage hRel
  refine ⟨initLocalsLoop_length bSrc args 0 bSrc.locals,
          by rw [initLocalsLoop_length, hLocEq], ?_⟩
  intro i ty s1 s2 hTy hS1 hS2
  have hTy2 : Trusted.MirSemantics.getElem? bTgt.locals i = some ty := by
    rw [← hLocEq]; exact hTy
  have hGet1 := initLocalsLoop_getElem? bSrc args 0 bSrc.locals i ty hTy
  have hGet2 := initLocalsLoop_getElem? bTgt args 0 bTgt.locals i ty hTy2
  rw [Nat.zero_add] at hGet1 hGet2
  rw [hGet1] at hS1; injection hS1 with hS1Eq; subst hS1Eq
  rw [hGet2] at hS2; injection hS2 with hS2Eq; subst hS2Eq
  cases i with
  | zero =>
    dsimp [Nat.beq]
    let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
    exact ⟨by rw [hOpt]; exact slotFwdRefines_refl_live true opt,
           liveUninitSlot_wellTyped ty⟩
  | succ k =>
    dsimp [Nat.beq]
    rw [← hArgEq]
    cases hLe : Nat.ble (k + 1) bSrc.argumentCount with
    | true =>
      dsimp
      have hKlt : k < bSrc.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((bSrc.locals.drop 1).take bSrc.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 bSrc.locals bSrc.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]
      exact ⟨rfl, hChk⟩
    | false =>
      dsimp
      have hNoAnn : hasStorageAnnotation bTgt (k + 1) = false :=
        removeStorage_no_storageAnnotation hRel (Nat.zero_lt_succ k)
          (getElem?_some_lt hTy2)
      rw [hNoAnn]
      dsimp
      let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
      cases hasStorageAnnotation bSrc (k + 1) with
      | true =>
        exact ⟨by rw [hOpt]; rfl, liveUninitSlot_wellTyped ty⟩
      | false =>
        exact ⟨by rw [hOpt]; exact slotFwdRefines_refl_live true opt,
               liveUninitSlot_wellTyped ty⟩

private def StateFwdRel (allowDead : Bool) (bodyRel : Body → Body → Bool)
    (pSrc pTgt : Program) (s t : State) : Prop :=
  s.callerMem = t.callerMem ∧
  ∃ fSrc fTgt bSrc bTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt ∧
    bodyRel bSrc bTgt = true ∧
    LocalsFwdRefines allowDead bSrc.locals fSrc.locals fTgt.locals

private theorem evalStatement_never_done (body : Body) (frame : FrameState)
    (cm : CallerMemory) (stmt : StatementKind) (out : TerminalOut) :
    evalStatement body frame cm stmt ≠ .done out := by
  intro h
  cases stmt with
  | nop => cases h
  | unsupported => cases h
  | storageLive id =>
    dsimp [evalStatement] at h
    cases hTy : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [hTy] at h; cases h
    | some ty =>
      rw [hTy] at h; dsimp at h
      cases hS : setElem? frame.locals id (liveUninitSlot ty) <;>
        rw [hS] at h <;> cases h
  | storageDead id =>
    dsimp [evalStatement] at h
    cases hZ : Nat.beq id 0 with
    | true => rw [hZ] at h; cases h
    | false =>
      rw [hZ] at h; dsimp at h
      cases hS : setElem? frame.locals id .dead <;> rw [hS] at h <;> cases h
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
        cases hR : evalRvalue body.locals frame.locals ty rv with
        | error _ => rw [hR] at h; cases h
        | ok res =>
          let ⟨v, locs1⟩ := res
          rw [hR] at h; dsimp at h
          cases hW : writePlace locs1 dst.localId ty v <;> rw [hW] at h <;> cases h

private theorem evalStatement_moveToCopy_fwd
    {bSrc bTgt : Body} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmtSrc stmtTgt : StatementKind} {s' : State}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hStmt : isMoveToCopyStmt stmtSrc stmtTgt = true)
    (hInv : LocalsFwdRefines false bSrc.locals fSrc.locals fTgt.locals)
    (hEv : evalStatement bSrc fSrc cm stmtSrc = .step s') :
    ∃ fSrc' fTgt',
      s' = { frames := [fSrc'], callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmtTgt = .step { frames := [fTgt'], callerMem := cm } ∧
      fSrc'.defId = fSrc.defId ∧ fTgt'.defId = fTgt.defId ∧
      fSrc'.blockIdx = fSrc.blockIdx ∧ fTgt'.blockIdx = fTgt.blockIdx ∧
      fSrc'.stmtIdx = fSrc.stmtIdx + 1 ∧ fTgt'.stmtIdx = fTgt.stmtIdx + 1 ∧
      LocalsFwdRefines false bSrc.locals fSrc'.locals fTgt'.locals := by
  let ⟨_, hLen2, _⟩ := hInv
  cases stmtSrc with
  | nop =>
    cases stmtTgt with
    | nop =>
      injection hEv with hEq
      subst hEq
      exact ⟨{ fSrc with stmtIdx := fSrc.stmtIdx + 1 },
             { fTgt with stmtIdx := fTgt.stmtIdx + 1 }, rfl, rfl,
             rfl, rfl, rfl, rfl, rfl, rfl, hInv⟩
    | _ => cases hStmt
  | unsupported => cases hEv
  | storageLive i1 =>
    cases stmtTgt with
    | storageLive i2 =>
      have hi : i1 = i2 := nat_beq_eq hStmt
      subst hi
      dsimp [evalStatement] at hEv
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals i1 with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv; dsimp at hEv
        cases hSet1 : setElem? fSrc.locals i1 (liveUninitSlot ty) with
        | none => rw [hSet1] at hEv; cases hEv
        | some locs1' =>
          rw [hSet1] at hEv; dsimp at hEv
          injection hEv with hEq; subst hEq
          let ⟨locs2', hSet2⟩ := setElem?_some_of_lt fTgt.locals i1
            (liveUninitSlot ty) (by rw [hLen2]; exact getElem?_some_lt hTy)
          let ⟨optU, hOptU⟩ := liveUninitSlot_isLive ty
          refine ⟨{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                  { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' },
                  rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
                  localsFwdRefines_set_both hInv hTy hSet1 hSet2
                    (by rw [hOptU]; exact slotFwdRefines_refl_live false optU)
                    (liveUninitSlot_wellTyped ty)⟩
          dsimp [evalStatement]
          rw [← hLocEq, hTy]; dsimp; rw [hSet2]
    | _ => cases hStmt
  | storageDead i1 =>
    cases stmtTgt with
    | storageDead i2 =>
      have hi : i1 = i2 := nat_beq_eq hStmt
      subst hi
      dsimp [evalStatement] at hEv
      cases hZ : Nat.beq i1 0 with
      | true => rw [hZ] at hEv; cases hEv
      | false =>
        rw [hZ] at hEv; dsimp at hEv
        cases hSet1 : setElem? fSrc.locals i1 .dead with
        | none => rw [hSet1] at hEv; cases hEv
        | some locs1' =>
          rw [hSet1] at hEv; dsimp at hEv
          injection hEv with hEq; subst hEq
          have hLt1 : i1 < bSrc.locals.length := by
            cases Nat.lt_or_ge i1 bSrc.locals.length with
            | inl hlt => exact hlt
            | inr hge =>
              have hNone := setElem?_none_of_ge fSrc.locals i1 .dead
                (by rw [hInv.1]; exact hge)
              rw [hNone] at hSet1; cases hSet1
          let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals i1 hLt1
          let ⟨locs2', hSet2⟩ := setElem?_some_of_lt fTgt.locals i1 .dead
            (by rw [hLen2]; exact hLt1)
          refine ⟨{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                  { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' },
                  rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
                  localsFwdRefines_set_both hInv hTy hSet1 hSet2 rfl True.intro⟩
          dsimp [evalStatement]
          rw [hZ]; dsimp; rw [hSet2]
    | _ => cases hStmt
  | assign d1 rv1 =>
    cases stmtTgt with
    | assign d2 rv2 =>
      let ⟨hD, hRv⟩ := bool_and_true hStmt
      have hd : d1 = d2 := placeEq_eq hD
      subst hd
      dsimp [evalStatement] at hEv
      cases hP : d1.projection.isEmpty with
      | false => rw [hP] at hEv; cases hEv
      | true =>
        rw [hP] at hEv; dsimp at hEv
        cases hTy : Trusted.MirSemantics.getElem? bSrc.locals d1.localId with
        | none => rw [hTy] at hEv; cases hEv
        | some dstTy =>
          rw [hTy] at hEv; dsimp at hEv
          cases hR : evalRvalue bSrc.locals fSrc.locals dstTy rv1 with
          | error _ => rw [hR] at hEv; cases hEv
          | ok res =>
            let ⟨val, locs1⟩ := res
            rw [hR] at hEv; dsimp at hEv
            cases hW : writePlace locs1 d1.localId dstTy val with
            | error _ => rw [hW] at hEv; cases hEv
            | ok locs1' =>
              rw [hW] at hEv; dsimp at hEv
              injection hEv with hEq; subst hEq
              let ⟨locs2, hR2, hInv1⟩ := evalRvalue_fwd hInv hRv hR
              let ⟨locs2', hW2, hInv2⟩ := writePlace_fwd hInv1 hTy hW
              refine ⟨{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' },
                      rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hInv2⟩
              dsimp [evalStatement]
              rw [hP]; dsimp
              rw [← hLocEq, hTy]; dsimp
              rw [hR2]; dsimp
              rw [hW2]
    | _ => cases hStmt

private theorem evalStatement_removeStorage_fwd
    {bSrc bTgt : Body} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmtSrc stmtTgt : StatementKind} {s' : State}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hStmt : isRemoveStorageMarkersStmt bSrc.locals.length stmtSrc stmtTgt = true)
    (hInv : LocalsFwdRefines true bSrc.locals fSrc.locals fTgt.locals)
    (hEv : evalStatement bSrc fSrc cm stmtSrc = .step s') :
    ∃ fSrc' fTgt',
      s' = { frames := [fSrc'], callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmtTgt = .step { frames := [fTgt'], callerMem := cm } ∧
      fSrc'.defId = fSrc.defId ∧ fTgt'.defId = fTgt.defId ∧
      fSrc'.blockIdx = fSrc.blockIdx ∧ fTgt'.blockIdx = fTgt.blockIdx ∧
      fSrc'.stmtIdx = fSrc.stmtIdx + 1 ∧ fTgt'.stmtIdx = fTgt.stmtIdx + 1 ∧
      LocalsFwdRefines true bSrc.locals fSrc'.locals fTgt'.locals := by
  let ⟨hLen1, hLen2, hAll⟩ := hInv
  cases stmtSrc with
  | nop =>
    cases stmtTgt with
    | nop =>
      injection hEv with hEq; subst hEq
      exact ⟨{ fSrc with stmtIdx := fSrc.stmtIdx + 1 },
             { fTgt with stmtIdx := fTgt.stmtIdx + 1 }, rfl, rfl,
             rfl, rfl, rfl, rfl, rfl, rfl, hInv⟩
    | _ => cases hStmt
  | unsupported => cases hEv
  | storageLive id =>
    cases stmtTgt with
    | nop =>
      dsimp [evalStatement] at hEv
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals id with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv; dsimp at hEv
        cases hSet1 : setElem? fSrc.locals id (liveUninitSlot ty) with
        | none => rw [hSet1] at hEv; cases hEv
        | some locs1' =>
          rw [hSet1] at hEv; dsimp at hEv
          injection hEv with hEq; subst hEq
          let ⟨s1, hS1⟩ := getElem?_some_of_lt fSrc.locals id
            (by rw [hLen1]; exact getElem?_some_lt hTy)
          let ⟨s2, hS2⟩ := getElem?_some_of_lt fTgt.locals id
            (by rw [hLen2]; exact getElem?_some_lt hTy)
          let ⟨hRef, hWt2⟩ := hAll id ty s1 s2 hTy hS1 hS2
          cases s2 with
          | dead =>
            cases s1 with
            | dead => cases hRef
            | live opt => cases opt <;> cases hRef
          | live opt2 =>
            exact ⟨{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                   { fTgt with stmtIdx := fTgt.stmtIdx + 1 }, rfl, rfl,
                   rfl, rfl, rfl, rfl, rfl, rfl,
                   localsFwdRefines_set_left hInv hTy hS2 hSet1
                     (slotFwdRefines_liveUninit_left hWt2)⟩
    | storageLive i2 =>
      let ⟨hNotLt, _⟩ := bool_and_true hStmt
      have hGe : bSrc.locals.length ≤ id := nat_blt_false_ge (bool_not_true hNotLt)
      dsimp [evalStatement] at hEv
      rw [getElem?_none_of_ge hGe] at hEv
      cases hEv
    | _ => cases hStmt
  | storageDead id =>
    cases stmtTgt with
    | nop =>
      let ⟨_, hLtB⟩ := bool_and_true hStmt
      have hLt : id < bSrc.locals.length := nat_blt_lt hLtB
      dsimp [evalStatement] at hEv
      cases hZ : Nat.beq id 0 with
      | true => rw [hZ] at hEv; cases hEv
      | false =>
        rw [hZ] at hEv; dsimp at hEv
        cases hSet1 : setElem? fSrc.locals id .dead with
        | none => rw [hSet1] at hEv; cases hEv
        | some locs1' =>
          rw [hSet1] at hEv; dsimp at hEv
          injection hEv with hEq; subst hEq
          let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals id hLt
          let ⟨s1, hS1⟩ := getElem?_some_of_lt fSrc.locals id (by rw [hLen1]; exact hLt)
          let ⟨s2, hS2⟩ := getElem?_some_of_lt fTgt.locals id (by rw [hLen2]; exact hLt)
          let ⟨hRef, _⟩ := hAll id ty s1 s2 hTy hS1 hS2
          cases s2 with
          | dead =>
            cases s1 with
            | dead => cases hRef
            | live opt => cases opt <;> cases hRef
          | live opt2 =>
            exact ⟨{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                   { fTgt with stmtIdx := fTgt.stmtIdx + 1 }, rfl, rfl,
                   rfl, rfl, rfl, rfl, rfl, rfl,
                   localsFwdRefines_set_left hInv hTy hS2 hSet1 rfl⟩
    | storageDead i2 =>
      let ⟨hOr, _⟩ := bool_and_true hStmt
      dsimp [evalStatement] at hEv
      cases bool_or_true hOr with
      | inl hZero =>
        rw [hZero] at hEv; cases hEv
      | inr hNotLt =>
        have hGe : bSrc.locals.length ≤ id := nat_blt_false_ge (bool_not_true hNotLt)
        cases hZ : Nat.beq id 0 with
        | true => rw [hZ] at hEv; cases hEv
        | false =>
          rw [hZ] at hEv; dsimp at hEv
          rw [setElem?_none_of_ge fSrc.locals id .dead (by rw [hLen1]; exact hGe)] at hEv
          cases hEv
    | _ => cases hStmt
  | assign d1 rv1 =>
    cases stmtTgt with
    | assign d2 rv2 =>
      let ⟨hD, hRvEq⟩ := bool_and_true hStmt
      have hd : d1 = d2 := placeEq_eq hD
      subst hd
      have hRv : rvalueRel isMoveToCopyOperand rv1 rv2 = true :=
        rvalueRel_operandEq_imp_moveToCopy hRvEq
      dsimp [evalStatement] at hEv
      cases hP : d1.projection.isEmpty with
      | false => rw [hP] at hEv; cases hEv
      | true =>
        rw [hP] at hEv; dsimp at hEv
        cases hTy : Trusted.MirSemantics.getElem? bSrc.locals d1.localId with
        | none => rw [hTy] at hEv; cases hEv
        | some dstTy =>
          rw [hTy] at hEv; dsimp at hEv
          cases hR : evalRvalue bSrc.locals fSrc.locals dstTy rv1 with
          | error _ => rw [hR] at hEv; cases hEv
          | ok res =>
            let ⟨val, locs1⟩ := res
            rw [hR] at hEv; dsimp at hEv
            cases hW : writePlace locs1 d1.localId dstTy val with
            | error _ => rw [hW] at hEv; cases hEv
            | ok locs1' =>
              rw [hW] at hEv; dsimp at hEv
              injection hEv with hEq; subst hEq
              let ⟨locs2, hR2, hInv1⟩ := evalRvalue_fwd hInv hRv hR
              let ⟨locs2', hW2, hInv2⟩ := writePlace_fwd hInv1 hTy hW
              refine ⟨{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' },
                      rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hInv2⟩
              dsimp [evalStatement]
              rw [hP]; dsimp
              rw [← hLocEq, hTy]; dsimp
              rw [hR2]; dsimp
              rw [hW2]
    | _ => cases hStmt

private theorem evalStep_fwd_generic {allowDead : Bool}
    {bodyRel : Body → Body → Bool} {blockRel : Body → BasicBlock → BasicBlock → Bool}
    {stmtRel : Body → StatementKind → StatementKind → Bool}
    {pSrc pTgt : Program} {s t : State}
    (hBodyBlocks : ∀ b1 b2, bodyRel b1 b2 = true →
      b1.locals = b2.locals ∧ listRel (blockRel b1) b1.basicBlocks b2.basicBlocks = true)
    (hBlockParts : ∀ b1 bb1 bb2, blockRel b1 bb1 bb2 = true →
      bb1.cleanup = bb2.cleanup ∧
      listRel (stmtRel b1) bb1.statements bb2.statements = true ∧
      terminatorRel isMoveToCopyOperand bb1.terminator bb2.terminator = true)
    (hStmtFwd : ∀ b1 b2 f1 f2 cm st1 st2 s',
      bodyRel b1 b2 = true →
      stmtRel b1 st1 st2 = true →
      LocalsFwdRefines allowDead b1.locals f1.locals f2.locals →
      evalStatement b1 f1 cm st1 = .step s' →
      ∃ f1' f2',
        s' = { frames := [f1'], callerMem := cm } ∧
        evalStatement b2 f2 cm st2 = .step { frames := [f2'], callerMem := cm } ∧
        f1'.defId = f1.defId ∧ f2'.defId = f2.defId ∧
        f1'.blockIdx = f1.blockIdx ∧ f2'.blockIdx = f2.blockIdx ∧
        f1'.stmtIdx = f1.stmtIdx + 1 ∧ f2'.stmtIdx = f2.stmtIdx + 1 ∧
        LocalsFwdRefines allowDead b1.locals f1'.locals f2'.locals)
    (hRel : StateFwdRel allowDead bodyRel pSrc pTgt s t) :
    (∀ s', evalStep pSrc 0 s = .step s' →
      ∃ t', evalStep pTgt 0 t = .step t' ∧
        StateFwdRel allowDead bodyRel pSrc pTgt s' t') ∧
    (∀ out, evalStep pSrc 0 s = .done out →
      evalStep pTgt 0 t = .done out) := by
  let ⟨hCm, fSrc, fTgt, bSrc, bTgt, hFS, hFT, hDef, hBlk, hStmt, hBS, hBT, hBody, hInv⟩ := hRel
  let ⟨hLocEq, hBlocks⟩ := hBodyBlocks bSrc bTgt hBody
  cases hBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
  | none =>
    constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; cases hEv)
  | some bbSrc =>
    let ⟨bbTgt, hBBT, hBBRel⟩ := listRel_getElem?_left hBlocks hBBS
    let ⟨hClean, hStmtsRel, hTermRel⟩ := hBlockParts bSrc bbSrc bbTgt hBBRel
    have hStmtsLen : bbSrc.statements.length = bbTgt.statements.length :=
      listRel_length hStmtsRel
    cases hSS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
    | some stmtSrc =>
      let ⟨stmtTgt, hST, hSRel⟩ := listRel_getElem?_left hStmtsRel hSS
      constructor
      · intro s' hEv
        unfold evalStep at hEv
        rw [hFS] at hEv; dsimp at hEv
        rw [hBS] at hEv; dsimp at hEv
        rw [hBBS] at hEv; dsimp at hEv
        rw [hSS] at hEv; dsimp at hEv
        let ⟨f1', f2', hEqS, hEv2, hD1, hD2, hB1, hB2, hSt1, hSt2, hInv'⟩ :=
          hStmtFwd bSrc bTgt fSrc fTgt s.callerMem stmtSrc stmtTgt s' hBody hSRel hInv hEv
        subst hEqS
        refine ⟨{ frames := [f2'], callerMem := t.callerMem }, ?_,
          hCm, f1', f2', bSrc, bTgt, rfl, rfl,
          by rw [hD1, hD2, hDef], by rw [hB1, hB2, hBlk],
          by rw [hSt1, hSt2, hStmt],
          by rw [hD1]; exact hBS, by rw [hD2]; exact hBT, hBody, hInv'⟩
        unfold evalStep
        rw [hFT]; dsimp
        rw [hBT]; dsimp
        rw [← hBlk, hBBT]; dsimp
        rw [← hStmt, hST]; dsimp
        rw [← hCm]
        exact hEv2
      · intro out hEv
        unfold evalStep at hEv
        rw [hFS] at hEv; dsimp at hEv
        rw [hBS] at hEv; dsimp at hEv
        rw [hBBS] at hEv; dsimp at hEv
        rw [hSS] at hEv; dsimp at hEv
        exact False.elim (evalStatement_never_done bSrc fSrc s.callerMem stmtSrc out hEv)
    | none =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
        rw [← hStmt]
        exact (listRel_getElem?_none_iff fSrc.stmtIdx hStmtsRel).mp hSS
      cases hAtEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
      | false =>
        constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS] at hEv; dsimp at hEv; rw [hAtEnd] at hEv; cases hEv)
      | true =>
        have hTerm := evalTerminator_fwd (cm := s.callerMem) hLocEq hClean hTermRel hInv
        constructor
        · intro s' hEv
          unfold evalStep at hEv
          rw [hFS] at hEv; dsimp at hEv
          rw [hBS] at hEv; dsimp at hEv
          rw [hBBS] at hEv; dsimp at hEv
          rw [hSS] at hEv; dsimp at hEv
          rw [hAtEnd] at hEv; dsimp at hEv
          let ⟨f1', f2', hEqS, hEv2, hD1, hD2, hBlk', hStmt', hInv'⟩ := hTerm.1 s' hEv
          subst hEqS
          refine ⟨{ frames := [f2'], callerMem := t.callerMem }, ?_,
            hCm, f1', f2', bSrc, bTgt, rfl, rfl,
            by rw [hD1, hD2, hDef], hBlk', hStmt',
            by rw [hD1]; exact hBS, by rw [hD2]; exact hBT, hBody, hInv'⟩
          unfold evalStep
          rw [hFT]; dsimp
          rw [hBT]; dsimp
          rw [← hBlk, hBBT]; dsimp
          rw [hST]; dsimp
          rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
          rw [← hCm]
          exact hEv2
        · intro out hEv
          unfold evalStep at hEv
          rw [hFS] at hEv; dsimp at hEv
          rw [hBS] at hEv; dsimp at hEv
          rw [hBBS] at hEv; dsimp at hEv
          rw [hSS] at hEv; dsimp at hEv
          rw [hAtEnd] at hEv; dsimp at hEv
          unfold evalStep
          rw [hFT]; dsimp
          rw [hBT]; dsimp
          rw [← hBlk, hBBT]; dsimp
          rw [hST]; dsimp
          rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
          rw [← hCm]
          exact hTerm.2 out hEv

private theorem moveToCopy_program_parts {pSrc pTgt : Program}
    (h : isMoveToCopyProgram pSrc pTgt = true) :
    pSrc.pointerWidthBits = pTgt.pointerWidthBits ∧
    pSrc.mirProfileVersion = pTgt.mirProfileVersion ∧
    pSrc.entryDefId = pTgt.entryDefId ∧
    listRel isMoveToCopyBody pSrc.bodies pTgt.bodies = true := by
  unfold isMoveToCopyProgram at h
  let ⟨h1234, hBodies⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, hEnt⟩ := bool_and_true h123
  let ⟨hPw, hVer⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hPw, nat_beq_eq hVer, nat_beq_eq hEnt, hBodies⟩

private theorem removeStorage_program_parts {pSrc pTgt : Program}
    (h : isRemoveStorageMarkersProgram pSrc pTgt = true) :
    pSrc.pointerWidthBits = pTgt.pointerWidthBits ∧
    pSrc.mirProfileVersion = pTgt.mirProfileVersion ∧
    pSrc.entryDefId = pTgt.entryDefId ∧
    listRel isRemoveStorageMarkersBody pSrc.bodies pTgt.bodies = true := by
  unfold isRemoveStorageMarkersProgram at h
  let ⟨h1234, hBodies⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, hEnt⟩ := bool_and_true h123
  let ⟨hPw, hVer⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hPw, nat_beq_eq hVer, nat_beq_eq hEnt, hBodies⟩

private theorem moveToCopy_entryProg {pSrc pTgt : Program} (defId : DefId)
    (h : isMoveToCopyProgram pSrc pTgt = true) :
    isMoveToCopyProgram (entryProgForBody pSrc defId)
      (entryProgForBody pTgt defId) = true := by
  unfold isMoveToCopyProgram at h
  let ⟨h1234, hBodies⟩ := bool_and_true h
  let ⟨h123, hSc⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨hPw, hVer⟩ := bool_and_true h12
  unfold isMoveToCopyProgram entryProgForBody
  dsimp
  rw [hPw, hVer, nat_beq_refl defId, hSc, hBodies]
  rfl

private theorem removeStorage_entryProg {pSrc pTgt : Program} (defId : DefId)
    (h : isRemoveStorageMarkersProgram pSrc pTgt = true) :
    isRemoveStorageMarkersProgram (entryProgForBody pSrc defId)
      (entryProgForBody pTgt defId) = true := by
  unfold isRemoveStorageMarkersProgram at h
  let ⟨h1234, hBodies⟩ := bool_and_true h
  let ⟨h123, hSc⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨hPw, hVer⟩ := bool_and_true h12
  unfold isRemoveStorageMarkersProgram entryProgForBody
  dsimp
  rw [hPw, hVer, nat_beq_refl defId, hSc, hBodies]
  rfl

private theorem moveToCopy_fwd_query {pSrc pTgt : Program} (q : Query)
    (hRel : isMoveToCopyProgram pSrc pTgt = true)
    (hWf : WellFormed pSrc q) :
    WellFormed pTgt q ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨hPw, hVer, hEnt, hBodies⟩ := moveToCopy_program_parts hRel
  have hInitEq := initState_equiv q hPw hVer hEnt hBodies (fun b1 b2 hb => by
    let ⟨hA, hL, _, _, hBL, hSt⟩ := body_fields_of_moveToCopy hb
    exact ⟨hA, hL, hBL, hSt⟩)
  apply fwd_sim_lift (R := StateFwdRel false isMoveToCopyBody pSrc pTgt)
  · intro s₀ hInitS
    let ⟨t₀, bSrc, bTgt, hInitT, hBS, hBT, hRelB, _, _, _, hArgs, hS0, hT0⟩ :=
      hInitEq.2 s₀ hInitS
    subst hS0; subst hT0
    refine ⟨_, hInitT, rfl, _, _, bSrc, bTgt, rfl, rfl, hEnt, rfl, rfl, hBS, hBT, hRelB,
      initLocalsLoop_fwd_moveToCopy hRelB hArgs⟩
  · intro s t hSt
    exact evalStep_fwd_generic
      (blockRel := fun _ => isMoveToCopyBlock)
      (stmtRel := fun _ => isMoveToCopyStmt)
      (fun b1 b2 hb => by
        let ⟨_, hL, _, _, _, _⟩ := body_fields_of_moveToCopy hb
        unfold isMoveToCopyBody at hb
        let ⟨_, hB⟩ := bool_and_true hb
        exact ⟨hL, hB⟩)
      (fun _ bb1 bb2 hbb => by
        unfold isMoveToCopyBlock at hbb
        let ⟨h12, hT⟩ := bool_and_true hbb
        let ⟨hC, hS⟩ := bool_and_true h12
        exact ⟨bool_beq_eq hC, hS, hT⟩)
      (fun b1 b2 f1 f2 cm st1 st2 s' hb hst hInv hEv =>
        evalStatement_moveToCopy_fwd (body_fields_of_moveToCopy hb).2.1 hst hInv hEv)
      hSt
  · exact hWf

private theorem removeStorage_fwd_query {pSrc pTgt : Program} (q : Query)
    (hRel : isRemoveStorageMarkersProgram pSrc pTgt = true)
    (hWf : WellFormed pSrc q) :
    WellFormed pTgt q ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨hPw, hVer, hEnt, hBodies⟩ := removeStorage_program_parts hRel
  have hInitEq := initState_equiv q hPw hVer hEnt hBodies (fun b1 b2 hb => by
    let ⟨hA, hL, _, _, hBL, hSt⟩ := body_fields_of_removeStorage hb
    exact ⟨hA, hL, hBL, hSt⟩)
  apply fwd_sim_lift (R := StateFwdRel true isRemoveStorageMarkersBody pSrc pTgt)
  · intro s₀ hInitS
    let ⟨t₀, bSrc, bTgt, hInitT, hBS, hBT, hRelB, _, _, _, hArgs, hS0, hT0⟩ :=
      hInitEq.2 s₀ hInitS
    subst hS0; subst hT0
    refine ⟨_, hInitT, rfl, _, _, bSrc, bTgt, rfl, rfl, hEnt, rfl, rfl, hBS, hBT, hRelB,
      initLocalsLoop_fwd_removeStorage hRelB hArgs⟩
  · intro s t hSt
    exact evalStep_fwd_generic
      (blockRel := fun b => isRemoveStorageMarkersBlock b.locals.length)
      (stmtRel := fun b => isRemoveStorageMarkersStmt b.locals.length)
      (fun b1 b2 hb => by
        let ⟨_, hL, _, _, _, _⟩ := body_fields_of_removeStorage hb
        unfold isRemoveStorageMarkersBody at hb
        let ⟨_, hB⟩ := bool_and_true hb
        exact ⟨hL, hB⟩)
      (fun _ bb1 bb2 hbb => by
        unfold isRemoveStorageMarkersBlock at hbb
        let ⟨h12, hT⟩ := bool_and_true hbb
        let ⟨hC, hS⟩ := bool_and_true h12
        exact ⟨bool_beq_eq hC, hS, terminatorRel_operandEq_imp_moveToCopy hT⟩)
      (fun b1 b2 f1 f2 cm st1 st2 s' hb hst hInv hEv =>
        evalStatement_removeStorage_fwd (body_fields_of_removeStorage hb).2.1 hst hInv hEv)
      hSt
  · exact hWf

/-! ### Private Proof Helpers — Layer C3: Certified Bisimulation Lemmas -/

private noncomputable def SlotCertBisim (reqLiveDst : Bool) (ty : MirTy) :
    AbsSlot → LocalSlot → LocalSlot → Prop
  | .liveInit, s1, s2 =>
    ∃ v, s1 = .live (some v) ∧ s2 = .live (some v) ∧ checkVal v ty = true
  | .liveUninit, s1, s2 =>
    (∃ opt1, s1 = .live opt1) ∧ (∃ opt2, s2 = .live opt2) ∧
    SlotWellTyped ty s1 ∧ SlotWellTyped ty s2
  | .dead, s1, s2 =>
    (if reqLiveDst then (∃ opt2, s2 = .live opt2) else (s1 = .dead ↔ s2 = .dead)) ∧
    SlotWellTyped ty s1 ∧ SlotWellTyped ty s2

private theorem slotCertBisim_mono {req : Bool} {ty : MirTy}
    {a b : AbsSlot} {s1 s2 : LocalSlot}
    (hImp : absSlotImplies a b = true)
    (h : SlotCertBisim req ty a s1 s2) :
    SlotCertBisim req ty b s1 s2 := by
  cases a with
  | liveInit =>
    let ⟨v, h1, h2, hChk⟩ := h
    subst h1; subst h2
    cases b with
    | liveInit => exact ⟨v, rfl, rfl, hChk⟩
    | liveUninit => exact ⟨⟨some v, rfl⟩, ⟨some v, rfl⟩, hChk, hChk⟩
    | dead =>
      refine ⟨?_, hChk, hChk⟩
      cases req with
      | true => exact ⟨some v, rfl⟩
      | false => exact ⟨(fun hD => by cases hD), (fun hD => by cases hD)⟩
  | liveUninit =>
    let ⟨⟨o1, h1⟩, ⟨o2, h2⟩, hW1, hW2⟩ := h
    subst h1; subst h2
    cases b with
    | liveInit => cases hImp
    | liveUninit => exact ⟨⟨o1, rfl⟩, ⟨o2, rfl⟩, hW1, hW2⟩
    | dead =>
      refine ⟨?_, hW1, hW2⟩
      cases req with
      | true => exact ⟨o2, rfl⟩
      | false => exact ⟨(fun hD => by cases hD), (fun hD => by cases hD)⟩
  | dead =>
    cases b with
    | liveInit => cases hImp
    | liveUninit => cases hImp
    | dead => exact h

private noncomputable def LocalsCertBisim (req : Bool) (bodyLocals : List MirTy)
    (env : List AbsSlot) (localsSrc localsTgt : List LocalSlot) : Prop :=
  env.length = bodyLocals.length ∧
  localsSrc.length = bodyLocals.length ∧
  localsTgt.length = bodyLocals.length ∧
  ∀ i ty a s1 s2,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? env i = some a →
    Trusted.MirSemantics.getElem? localsSrc i = some s1 →
    Trusted.MirSemantics.getElem? localsTgt i = some s2 →
    SlotCertBisim req ty a s1 s2

private theorem localsCertBisim_mono {req : Bool} {bodyLocals : List MirTy}
    {env1 env2 : List AbsSlot} {localsSrc localsTgt : List LocalSlot}
    (hImp : absEnvImplies env1 env2 = true)
    (h : LocalsCertBisim req bodyLocals env1 localsSrc localsTgt) :
    LocalsCertBisim req bodyLocals env2 localsSrc localsTgt := by
  let ⟨hELen, hLen1, hLen2, hAll⟩ := h
  refine ⟨by rw [← listRel_length hImp, hELen], hLen1, hLen2, ?_⟩
  intro i ty b s1 s2 hTy hB hS1 hS2
  let ⟨a, hA, hAB⟩ := listRel_getElem?_right hImp hB
  exact slotCertBisim_mono hAB (hAll i ty a s1 s2 hTy hA hS1 hS2)

private theorem localsCertBisim_set_all {req : Bool} {bodyLocals : List MirTy}
    {env env' : List AbsSlot} {locs1 locs2 locs1' locs2' : List LocalSlot}
    {id : Nat} {ty : MirTy} {a' : AbsSlot} {s1' s2' : LocalSlot}
    (h : LocalsCertBisim req bodyLocals env locs1 locs2)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSE : setElem? env id a' = some env')
    (hS1 : setElem? locs1 id s1' = some locs1')
    (hS2 : setElem? locs2 id s2' = some locs2')
    (hSlot : SlotCertBisim req ty a' s1' s2') :
    LocalsCertBisim req bodyLocals env' locs1' locs2' := by
  let ⟨hELen, hLen1, hLen2, hAll⟩ := h
  refine ⟨by rw [setElem?_length hSE, hELen],
          by rw [setElem?_length hS1, hLen1],
          by rw [setElem?_length hS2, hLen2], ?_⟩
  intro i tyi ai x1 x2 hTyi hAi hX1 hX2
  cases hEq : Nat.beq i id with
  | true =>
    have hi : i = id := nat_beq_eq hEq
    subst hi
    rw [hTy] at hTyi; injection hTyi with hEqT; subst hEqT
    rw [setElem?_getElem?_same hSE] at hAi; injection hAi with hEqA; subst hEqA
    rw [setElem?_getElem?_same hS1] at hX1; injection hX1 with hEq1; subst hEq1
    rw [setElem?_getElem?_same hS2] at hX2; injection hX2 with hEq2; subst hEq2
    exact hSlot
  | false =>
    have hNe : i ≠ id := fun h0 => by rw [h0, nat_beq_refl] at hEq; cases hEq
    rw [setElem?_getElem?_ne hSE hNe] at hAi
    rw [setElem?_getElem?_ne hS1 hNe] at hX1
    rw [setElem?_getElem?_ne hS2 hNe] at hX2
    exact hAll i tyi ai x1 x2 hTyi hAi hX1 hX2

private theorem localsCertBisim_set_env_left {req : Bool} {bodyLocals : List MirTy}
    {env env' : List AbsSlot} {locs1 locs2 locs1' : List LocalSlot}
    {id : Nat} {ty : MirTy} {a' : AbsSlot} {s1' s2 : LocalSlot}
    (h : LocalsCertBisim req bodyLocals env locs1 locs2)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hG2 : Trusted.MirSemantics.getElem? locs2 id = some s2)
    (hSE : setElem? env id a' = some env')
    (hS1 : setElem? locs1 id s1' = some locs1')
    (hSlot : SlotCertBisim req ty a' s1' s2) :
    LocalsCertBisim req bodyLocals env' locs1' locs2 := by
  let ⟨hELen, hLen1, hLen2, hAll⟩ := h
  refine ⟨by rw [setElem?_length hSE, hELen],
          by rw [setElem?_length hS1, hLen1], hLen2, ?_⟩
  intro i tyi ai x1 x2 hTyi hAi hX1 hX2
  cases hEq : Nat.beq i id with
  | true =>
    have hi : i = id := nat_beq_eq hEq
    subst hi
    rw [hTy] at hTyi; injection hTyi with hEqT; subst hEqT
    rw [setElem?_getElem?_same hSE] at hAi; injection hAi with hEqA; subst hEqA
    rw [setElem?_getElem?_same hS1] at hX1; injection hX1 with hEq1; subst hEq1
    rw [hG2] at hX2; injection hX2 with hEq2; subst hEq2
    exact hSlot
  | false =>
    have hNe : i ≠ id := fun h0 => by rw [h0, nat_beq_refl] at hEq; cases hEq
    rw [setElem?_getElem?_ne hSE hNe] at hAi
    rw [setElem?_getElem?_ne hS1 hNe] at hX1
    exact hAll i tyi ai x1 x2 hTyi hAi hX1 hX2

private theorem slotCertBisim_liveUninit_pair {req : Bool} (ty : MirTy) :
    SlotCertBisim req ty
      (if isAlwaysInhabitedZst ty then .liveInit else .liveUninit)
      (liveUninitSlot ty) (liveUninitSlot ty) := by
  cases hZ : isAlwaysInhabitedZst ty with
  | false =>
    dsimp
    rw [liveUninitSlot_of_not_zst hZ]
    exact ⟨⟨none, rfl⟩, ⟨none, rfl⟩, hZ, hZ⟩
  | true =>
    dsimp
    cases ty with
    | unit => exact ⟨.unit, rfl, rfl, rfl⟩
    | enum ety =>
      dsimp [isAlwaysInhabitedZst] at hZ
      have hWt := liveUninitSlot_wellTyped (.enum ety)
      dsimp [liveUninitSlot] at hWt
      rw [hZ] at hWt
      dsimp [liveUninitSlot]
      rw [hZ]
      exact ⟨.enumVal ety 0, rfl, rfl, hWt⟩
    | bool => cases hZ
    | int _ _ => cases hZ
    | never => cases hZ
    | tuple _ => cases hZ
    | ref _ _ => cases hZ
    | rawPtr _ _ => cases hZ
    | unsupported => cases hZ

private theorem slotCertBisim_liveUninit_left {req : Bool} {ty : MirTy}
    {opt2 : Option Val} (hWt2 : SlotWellTyped ty (.live opt2)) :
    SlotCertBisim req ty
      (if isAlwaysInhabitedZst ty then .liveInit else .liveUninit)
      (liveUninitSlot ty) (.live opt2) := by
  cases hZ : isAlwaysInhabitedZst ty with
  | false =>
    dsimp
    rw [liveUninitSlot_of_not_zst hZ]
    exact ⟨⟨none, rfl⟩, ⟨opt2, rfl⟩, hZ, hWt2⟩
  | true =>
    have hEq := slot_eq_liveUninit_of_zst hZ hWt2
    rw [hEq]
    have hPair := slotCertBisim_liveUninit_pair (req := req) ty
    rw [hZ] at hPair
    exact hPair

private theorem evalOperandToSlot_cert_bisim {req : Bool}
    {bodyLocals : List MirTy} {env env' : List AbsSlot}
    {locs1 locs2 : List LocalSlot} {opSrc opTgt : Operand}
    (hInv : LocalsCertBisim req bodyLocals env locs1 locs2)
    (hOp : isMoveToCopyOperand opSrc opTgt = true)
    (hStep : stepAbsOperand bodyLocals env opSrc = some env') :
    (∃ k,
      evalOperandToSlot bodyLocals locs1 opSrc = .error k ∧
      evalOperandToSlot bodyLocals locs2 opTgt = .error k) ∨
    (∃ ty v locs1' locs2',
      evalOperandToSlot bodyLocals locs1 opSrc = .ok (ty, some v, locs1') ∧
      evalOperandToSlot bodyLocals locs2 opTgt = .ok (ty, some v, locs2') ∧
      LocalsCertBisim req bodyLocals env' locs1' locs2') := by
  let ⟨_, hLen1, hLen2, hAll⟩ := hInv
  cases opSrc with
  | constant c1 =>
    cases opTgt with
    | constant c2 =>
      have hc : c1 = c2 := constOpEq_eq hOp
      subst hc
      injection hStep with hEqE; subst hEqE
      cases hC : evalConstLit c1.ty c1.lit with
      | error k =>
        left
        refine ⟨k, ?_, ?_⟩ <;> (dsimp [evalOperandToSlot]; rw [hC])
      | ok v =>
        right
        refine ⟨c1.ty, v, locs1, locs2, ?_, ?_, hInv⟩ <;>
          (dsimp [evalOperandToSlot]; rw [hC])
    | _ => cases hOp
  | copy p1 =>
    cases opTgt with
    | copy p2 =>
      have hp : p1 = p2 := placeEq_eq hOp
      subst hp
      dsimp [stepAbsOperand] at hStep
      cases hP : p1.projection.isEmpty with
      | false => rw [hP] at hStep; cases hStep
      | true =>
        rw [hP] at hStep; dsimp at hStep
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals p1.localId with
        | none => rw [hTy] at hStep; cases hStep
        | some ty =>
          rw [hTy] at hStep
          cases hA : Trusted.MirSemantics.getElem? env p1.localId with
          | none => rw [hA] at hStep; cases hStep
          | some a =>
            rw [hA] at hStep
            cases a with
            | liveUninit => cases hStep
            | dead => cases hStep
            | liveInit =>
              dsimp at hStep
              injection hStep with hEqE; subst hEqE
              let ⟨s1, hS1⟩ := getElem?_some_of_lt locs1 p1.localId
                (by rw [hLen1]; exact getElem?_some_lt hTy)
              let ⟨s2, hS2⟩ := getElem?_some_of_lt locs2 p1.localId
                (by rw [hLen2]; exact getElem?_some_lt hTy)
              let ⟨v, h1, h2, _⟩ := hAll p1.localId ty .liveInit s1 s2 hTy hA hS1 hS2
              subst h1; subst h2
              right
              refine ⟨ty, v, locs1, locs2, ?_, ?_, hInv⟩
              · dsimp [evalOperandToSlot]; rw [hP, hTy, hS1]; rfl
              · dsimp [evalOperandToSlot]; rw [hP, hTy, hS2]; rfl
    | _ => cases hOp
  | move p1 =>
    dsimp [stepAbsOperand] at hStep
    cases hP : p1.projection.isEmpty with
    | false => rw [hP] at hStep; cases hStep
    | true =>
      rw [hP] at hStep; dsimp at hStep
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p1.localId with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep
        cases hA : Trusted.MirSemantics.getElem? env p1.localId with
        | none => rw [hA] at hStep; cases hStep
        | some a =>
          rw [hA] at hStep
          cases a with
          | liveUninit => cases hStep
          | dead => cases hStep
          | liveInit =>
            dsimp at hStep
            let ⟨s1, hS1⟩ := getElem?_some_of_lt locs1 p1.localId
              (by rw [hLen1]; exact getElem?_some_lt hTy)
            let ⟨s2, hS2⟩ := getElem?_some_of_lt locs2 p1.localId
              (by rw [hLen2]; exact getElem?_some_lt hTy)
            let ⟨v, h1, h2, hChk⟩ := hAll p1.localId ty .liveInit s1 s2 hTy hA hS1 hS2
            subst h1; subst h2
            let ⟨locs1', hSet1⟩ := setElem?_some_of_lt locs1 p1.localId
              (liveUninitSlot ty) (by rw [hLen1]; exact getElem?_some_lt hTy)
            cases opTgt with
            | constant _ => cases hOp
            | move p2 =>
              have hp : p1 = p2 := placeEq_eq hOp
              subst hp
              let ⟨locs2', hSet2⟩ := setElem?_some_of_lt locs2 p1.localId
                (liveUninitSlot ty) (by rw [hLen2]; exact getElem?_some_lt hTy)
              right
              refine ⟨ty, v, locs1', locs2', ?_, ?_,
                localsCertBisim_set_all hInv hTy hStep hSet1 hSet2
                  (slotCertBisim_liveUninit_pair ty)⟩
              · dsimp [evalOperandToSlot]; rw [hP, hTy, hS1]; dsimp; rw [hSet1]
              · dsimp [evalOperandToSlot]; rw [hP, hTy, hS2]; dsimp; rw [hSet2]
            | copy p2 =>
              have hp : p1 = p2 := placeEq_eq hOp
              subst hp
              right
              refine ⟨ty, v, locs1', locs2, ?_, ?_,
                localsCertBisim_set_env_left hInv hTy hS2 hStep hSet1
                  (slotCertBisim_liveUninit_left hChk)⟩
              · dsimp [evalOperandToSlot]; rw [hP, hTy, hS1]; dsimp; rw [hSet1]
              · dsimp [evalOperandToSlot]; rw [hP, hTy, hS2]; rfl

private theorem evalPrimitiveOperand_cert_bisim {req : Bool}
    {bodyLocals : List MirTy} {env env' : List AbsSlot}
    {locs1 locs2 : List LocalSlot} {opSrc opTgt : Operand}
    (hInv : LocalsCertBisim req bodyLocals env locs1 locs2)
    (hOp : isMoveToCopyOperand opSrc opTgt = true)
    (hStep : stepAbsOperand bodyLocals env opSrc = some env') :
    (∃ k,
      evalPrimitiveOperand bodyLocals locs1 opSrc = .error k ∧
      evalPrimitiveOperand bodyLocals locs2 opTgt = .error k) ∨
    (∃ v locs1' locs2',
      evalPrimitiveOperand bodyLocals locs1 opSrc = .ok (v, locs1') ∧
      evalPrimitiveOperand bodyLocals locs2 opTgt = .ok (v, locs2') ∧
      LocalsCertBisim req bodyLocals env' locs1' locs2') := by
  cases evalOperandToSlot_cert_bisim hInv hOp hStep with
  | inl hErr =>
    let ⟨k, h1, h2⟩ := hErr
    left
    refine ⟨k, ?_, ?_⟩
    · dsimp [evalPrimitiveOperand]; rw [h1]
    · dsimp [evalPrimitiveOperand]; rw [h2]
  | inr hOk =>
    let ⟨ty, v, l1, l2, h1, h2, hInv'⟩ := hOk
    cases hP : isPrimitiveReadableTy ty with
    | false =>
      left
      refine ⟨.unsupported, ?_, ?_⟩
      · dsimp [evalPrimitiveOperand]; rw [h1]; dsimp; rw [hP]; rfl
      · dsimp [evalPrimitiveOperand]; rw [h2]; dsimp; rw [hP]; rfl
    | true =>
      right
      refine ⟨v, l1, l2, ?_, ?_, hInv'⟩
      · dsimp [evalPrimitiveOperand]; rw [h1]; dsimp; rw [hP]; rfl
      · dsimp [evalPrimitiveOperand]; rw [h2]; dsimp; rw [hP]; rfl

private theorem evalRvalue_cert_bisim {req : Bool}
    {bodyLocals : List MirTy} {env env' : List AbsSlot}
    {locs1 locs2 : List LocalSlot} {dstTy : MirTy} {rvSrc rvTgt : Rvalue}
    (hInv : LocalsCertBisim req bodyLocals env locs1 locs2)
    (hRv : rvalueRel isMoveToCopyOperand rvSrc rvTgt = true)
    (hStep : stepAbsRvalue bodyLocals env rvSrc = some env') :
    (∃ k,
      evalRvalue bodyLocals locs1 dstTy rvSrc = .error k ∧
      evalRvalue bodyLocals locs2 dstTy rvTgt = .error k) ∨
    (∃ v locs1' locs2',
      evalRvalue bodyLocals locs1 dstTy rvSrc = .ok (v, locs1') ∧
      evalRvalue bodyLocals locs2 dstTy rvTgt = .ok (v, locs2') ∧
      LocalsCertBisim req bodyLocals env' locs1' locs2') := by
  cases rvSrc with
  | use o1 =>
    cases rvTgt with
    | use o2 =>
      cases evalOperandToSlot_cert_bisim hInv hRv hStep with
      | inl hErr =>
        let ⟨k, h1, h2⟩ := hErr
        left
        refine ⟨k, ?_, ?_⟩
        · dsimp [evalRvalue]; rw [h1]
        · dsimp [evalRvalue]; rw [h2]
      | inr hOk =>
        let ⟨srcTy, v, l1, l2, h1, h2, hInv'⟩ := hOk
        cases hEqTy : MirTy.beq srcTy dstTy with
        | false =>
          left
          refine ⟨.unsupported, ?_, ?_⟩
          · dsimp [evalRvalue]; rw [h1]; dsimp; rw [hEqTy]; rfl
          · dsimp [evalRvalue]; rw [h2]; dsimp; rw [hEqTy]; rfl
        | true =>
          right
          refine ⟨v, l1, l2, ?_, ?_, hInv'⟩
          · dsimp [evalRvalue]; rw [h1]; dsimp; rw [hEqTy]; rfl
          · dsimp [evalRvalue]; rw [h2]; dsimp; rw [hEqTy]; rfl
    | _ => cases hRv
  | binaryOp op1 l1 r1 =>
    cases rvTgt with
    | binaryOp op2 l2 r2 =>
      let ⟨h12, hR⟩ := bool_and_true hRv
      let ⟨hOp, hL⟩ := bool_and_true h12
      have hOpEq : op1 = op2 := binOpEq_eq hOp
      subst hOpEq
      dsimp [stepAbsRvalue] at hStep
      cases hSL : stepAbsOperand bodyLocals env l1 with
      | none => rw [hSL] at hStep; cases hStep
      | some env1 =>
        rw [hSL] at hStep; dsimp at hStep
        cases evalPrimitiveOperand_cert_bisim hInv hL hSL with
        | inl hErr =>
          let ⟨k, h1, h2⟩ := hErr
          left
          refine ⟨k, ?_, ?_⟩
          · dsimp [evalRvalue]; rw [h1]
          · dsimp [evalRvalue]; rw [h2]
        | inr hOkL =>
          let ⟨lv, locsL1, locsL2, hL1, hL2, hInv1⟩ := hOkL
          cases evalPrimitiveOperand_cert_bisim hInv1 hR hStep with
          | inl hErr =>
            let ⟨k, h1, h2⟩ := hErr
            left
            refine ⟨k, ?_, ?_⟩
            · dsimp [evalRvalue]; rw [hL1]; dsimp; rw [h1]
            · dsimp [evalRvalue]; rw [hL2]; dsimp; rw [h2]
          | inr hOkR =>
            let ⟨rv, locsR1, locsR2, hR1, hR2, hInv2⟩ := hOkR
            cases hBin : evalBinOp op1 lv rv with
            | error k =>
              left
              refine ⟨k, ?_, ?_⟩
              · dsimp [evalRvalue]; rw [hL1]; dsimp; rw [hR1]; dsimp; rw [hBin]
              · dsimp [evalRvalue]; rw [hL2]; dsimp; rw [hR2]; dsimp; rw [hBin]
            | ok resV =>
              right
              refine ⟨resV, locsR1, locsR2, ?_, ?_, hInv2⟩
              · dsimp [evalRvalue]; rw [hL1]; dsimp; rw [hR1]; dsimp; rw [hBin]
              · dsimp [evalRvalue]; rw [hL2]; dsimp; rw [hR2]; dsimp; rw [hBin]
    | _ => cases hRv
  | unaryOp op1 o1 =>
    cases rvTgt with
    | unaryOp op2 o2 =>
      let ⟨hOp, hO⟩ := bool_and_true hRv
      have hOpEq : op1 = op2 := unOpEq_eq hOp
      subst hOpEq
      cases evalPrimitiveOperand_cert_bisim hInv hO hStep with
      | inl hErr =>
        let ⟨k, h1, h2⟩ := hErr
        left
        refine ⟨k, ?_, ?_⟩
        · dsimp [evalRvalue]; rw [h1]
        · dsimp [evalRvalue]; rw [h2]
      | inr hOk =>
        let ⟨ov, l1, l2, h1, h2, hInv1⟩ := hOk
        cases hUn : evalUnOp op1 ov with
        | error k =>
          left
          refine ⟨k, ?_, ?_⟩
          · dsimp [evalRvalue]; rw [h1]; dsimp; rw [hUn]
          · dsimp [evalRvalue]; rw [h2]; dsimp; rw [hUn]
        | ok resV =>
          right
          refine ⟨resV, l1, l2, ?_, ?_, hInv1⟩
          · dsimp [evalRvalue]; rw [h1]; dsimp; rw [hUn]
          · dsimp [evalRvalue]; rw [h2]; dsimp; rw [hUn]
    | _ => cases hRv
  | discriminant p1 =>
    cases rvTgt with
    | discriminant p2 =>
      have hp : p1 = p2 := placeEq_eq hRv
      subst hp
      let ⟨_, hLen1, hLen2, hAll⟩ := hInv
      dsimp [stepAbsRvalue] at hStep
      cases hP : p1.projection.isEmpty with
      | false => rw [hP] at hStep; cases hStep
      | true =>
        rw [hP] at hStep; dsimp at hStep
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals p1.localId with
        | none => rw [hTy] at hStep; cases hStep
        | some ty =>
          rw [hTy] at hStep
          cases ty with
          | enum ety =>
            cases hA : Trusted.MirSemantics.getElem? env p1.localId with
            | none => rw [hA] at hStep; cases hStep
            | some a =>
              rw [hA] at hStep
              let ⟨s1, hS1⟩ := getElem?_some_of_lt locs1 p1.localId
                (by rw [hLen1]; exact getElem?_some_lt hTy)
              let ⟨s2, hS2⟩ := getElem?_some_of_lt locs2 p1.localId
                (by rw [hLen2]; exact getElem?_some_lt hTy)
              have hSlot := hAll p1.localId (.enum ety) a s1 s2 hTy hA hS1 hS2
              dsimp at hStep
              have hEqAndEnv : s1 = s2 ∧ env = env' := by
                cases hZ : isZstEnumTy ety with
                | true =>
                  rw [hZ] at hStep; dsimp at hStep
                  have hZst : isAlwaysInhabitedZst (.enum ety) = true := hZ
                  cases a with
                  | dead => cases hStep
                  | liveInit =>
                    injection hStep with hE
                    let ⟨v, h1, h2, _⟩ := hSlot
                    exact ⟨by rw [h1, h2], hE⟩
                  | liveUninit =>
                    injection hStep with hE
                    let ⟨⟨o1, h1⟩, ⟨o2, h2⟩, hW1, hW2⟩ := hSlot
                    subst h1; subst h2
                    exact ⟨by rw [slot_eq_liveUninit_of_zst hZst hW1,
                                  slot_eq_liveUninit_of_zst hZst hW2], hE⟩
                | false =>
                  rw [hZ] at hStep; dsimp at hStep
                  cases a with
                  | dead => cases hStep
                  | liveUninit => cases hStep
                  | liveInit =>
                    injection hStep with hE
                    let ⟨v, h1, h2, _⟩ := hSlot
                    exact ⟨by rw [h1, h2], hE⟩
              let ⟨hSEq, hEEq⟩ := hEqAndEnv
              subst hSEq; subst hEEq
              cases hAdm : enumAdmitted ety with
              | false =>
                left
                refine ⟨.unsupported, ?_, ?_⟩
                · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; rfl
                · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; rfl
              | true =>
                cases hTr : ety.tagRepr with
                | zeroSized =>
                  cases s1 with
                  | dead =>
                    left
                    refine ⟨.undefined, ?_, ?_⟩
                    · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; rfl
                    · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; rfl
                  | live opt =>
                    cases opt with
                    | none =>
                      cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                      | none =>
                        left
                        refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hD]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hD]
                      | some d =>
                        right
                        refine ⟨.scalar ⟨ety.discrWidth, ety.discrSigned,
                            truncateBits ety.discrWidth (BitVec.ofNat 128 d)⟩,
                          locs1, locs2, ?_, ?_, hInv⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hD]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hD]
                    | some val =>
                      cases val with
                      | enumVal ety' k =>
                        cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                        | false =>
                          left
                          refine ⟨.unsupported, ?_, ?_⟩
                          · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; rfl
                          · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; rfl
                        | true =>
                          cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                          | none =>
                            left
                            refine ⟨.unsupported, ?_, ?_⟩
                            · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
                            · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
                          | some d =>
                            right
                            refine ⟨.scalar ⟨ety.discrWidth, ety.discrSigned,
                                truncateBits ety.discrWidth (BitVec.ofNat 128 d)⟩,
                              locs1, locs2, ?_, ?_, hInv⟩
                            · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
                            · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
                      | scalar _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | ptr _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | bool _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | unit =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | tuple _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | bytes _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                | scalar _ _ =>
                  cases s1 with
                  | dead =>
                    left; refine ⟨.undefined, ?_, ?_⟩
                    · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; rfl
                    · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; rfl
                  | live opt =>
                    cases opt with
                    | none =>
                      left; refine ⟨.undefined, ?_, ?_⟩
                      · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                    | some val =>
                      cases val with
                      | enumVal ety' k =>
                        cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                        | false =>
                          left; refine ⟨.unsupported, ?_, ?_⟩
                          · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; rfl
                          · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; rfl
                        | true =>
                          cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                          | none =>
                            left; refine ⟨.unsupported, ?_, ?_⟩
                            · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
                            · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
                          | some d =>
                            right
                            refine ⟨.scalar ⟨ety.discrWidth, ety.discrSigned,
                                truncateBits ety.discrWidth (BitVec.ofNat 128 d)⟩,
                              locs1, locs2, ?_, ?_, hInv⟩
                            · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
                            · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
                      | scalar _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | ptr _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | bool _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | unit =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | tuple _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                      | bytes _ =>
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]
          | bool => cases hStep
          | int _ _ => cases hStep
          | unit => cases hStep
          | never => cases hStep
          | tuple _ => cases hStep
          | ref _ _ => cases hStep
          | rawPtr _ _ => cases hStep
          | unsupported => cases hStep
    | _ => cases hRv
  | ref _ _ => cases hStep
  | addressOf _ _ => cases hStep
  | aggregateTuple _ => cases hStep
  | unsupported => cases hStep

private theorem evalSwitchBranches_target_ok {P : BasicBlockId → Bool}
    {w : IntWidth} {discrBits : BitVec 128} {ow tgt : BasicBlockId}
    {bs : List (BitVec 128 × BasicBlockId)}
    (hOw : P ow = true) (hBs : bs.all (fun br => P br.2) = true)
    (hEv : evalSwitchBranches w discrBits ow bs = .ok tgt) :
    P tgt = true := by
  induction bs with
  | nil =>
    injection hEv with hEq; subst hEq; exact hOw
  | cons br rest ih =>
    let ⟨cb, tb⟩ := br
    dsimp [List.all] at hBs
    let ⟨hTb, hRest⟩ := bool_and_true hBs
    dsimp [evalSwitchBranches] at hEv
    cases hOvf : (truncateBits w cb != cb) with
    | true => rw [hOvf] at hEv; cases hEv
    | false =>
      rw [hOvf] at hEv; dsimp at hEv
      cases hM : (truncateBits w discrBits == truncateBits w cb) with
      | true =>
        rw [hM] at hEv; dsimp at hEv
        injection hEv with hEq; subst hEq; exact hTb
      | false =>
        rw [hM] at hEv; dsimp at hEv
        exact ih hRest hEv

private theorem evalBoolSwitchBranches_target_ok {P : BasicBlockId → Bool}
    {discr : Bool} {ow tgt : BasicBlockId}
    {bs : List (BitVec 128 × BasicBlockId)}
    (hOw : P ow = true) (hBs : bs.all (fun br => P br.2) = true)
    (hEv : evalBoolSwitchBranches discr ow bs = .ok tgt) :
    P tgt = true := by
  induction bs with
  | nil =>
    injection hEv with hEq; subst hEq; exact hOw
  | cons br rest ih =>
    let ⟨cb, tb⟩ := br
    dsimp [List.all] at hBs
    let ⟨hTb, hRest⟩ := bool_and_true hBs
    dsimp [evalBoolSwitchBranches] at hEv
    cases hC : evalConstLit .bool (.scalar cb) with
    | error _ => rw [hC] at hEv; cases hEv
    | ok v =>
      rw [hC] at hEv
      cases v with
      | bool b =>
        cases b with
        | false =>
          dsimp at hEv
          cases discr with
          | false => injection hEv with hEq; subst hEq; exact hTb
          | true => exact ih hRest hEv
        | true =>
          dsimp at hEv
          cases discr with
          | true => injection hEv with hEq; subst hEq; exact hTb
          | false => exact ih hRest hEv
      | scalar _ => cases hEv
      | ptr _ => cases hEv
      | unit => cases hEv
      | enumVal _ _ => cases hEv
      | tuple _ => cases hEv
      | bytes _ => cases hEv

private theorem checkAbsBlocksLoop_getElem? (req : Bool) (body : Body)
    (cert : BodyAbsCert) (base : Nat) (bbs : List BasicBlock)
    (i : Nat) (bb : BasicBlock)
    (hLoop : checkAbsBlocksLoop req body cert base bbs = true)
    (hGet : Trusted.MirSemantics.getElem? bbs i = some bb) :
    checkAbsBlock req body cert (base + i) bb = true := by
  induction bbs generalizing base i with
  | nil => cases hGet
  | cons b rest ih =>
    dsimp [checkAbsBlocksLoop] at hLoop
    let ⟨hHead, hTail⟩ := bool_and_true hLoop
    cases i with
    | zero =>
      injection hGet with hEq; subst hEq; exact hHead
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTail hGet
      rw [hAdd] at hRec
      exact hRec

private noncomputable def BlockTermOk (body : Body) (bCert : BodyAbsCert)
    (bb : BasicBlock) (exitEnv : List AbsSlot) : Prop :=
  let numBlocks := body.basicBlocks.length
  match bb.terminator with
  | .goto target => checkEdgeTarget numBlocks bCert exitEnv target = true
  | .return_ =>
    if bb.cleanup then True
    else Trusted.MirSemantics.getElem? exitEnv 0 = some .liveInit
  | .switchInt discr targets =>
    ∃ afterDiscrEnv,
      stepAbsOperand body.locals exitEnv discr = some afterDiscrEnv ∧
      checkEdgeTarget numBlocks bCert afterDiscrEnv targets.otherwise = true ∧
      targets.branches.all (fun br =>
        checkEdgeTarget numBlocks bCert afterDiscrEnv br.2) = true
  | .unreachable | .unwindResume | .assert _ _ _ _ _
  | .call _ _ _ _ _ | .unsupported => True

private theorem checkAbsBlock_elim {req : Bool} {body : Body} {bCert : BodyAbsCert}
    {bbIdx : Nat} {bb : BasicBlock} {entryEnv : List AbsSlot}
    (hBlk : checkAbsBlock req body bCert bbIdx bb = true)
    (hEntry : Trusted.MirSemantics.getElem? bCert bbIdx = some (some entryEnv)) :
    entryEnv.length = body.locals.length ∧
    ∃ exitEnv,
      stepAbsStmts req body.locals entryEnv bb.statements = some exitEnv ∧
      BlockTermOk body bCert bb exitEnv := by
  unfold checkAbsBlock at hBlk
  rw [hEntry] at hBlk; dsimp at hBlk
  let ⟨hLen, hRest⟩ := bool_and_true hBlk
  refine ⟨nat_beq_eq hLen, ?_⟩
  cases hSt : stepAbsStmts req body.locals entryEnv bb.statements with
  | none => rw [hSt] at hRest; cases hRest
  | some exitEnv =>
    rw [hSt] at hRest; dsimp at hRest
    refine ⟨exitEnv, rfl, ?_⟩
    unfold BlockTermOk
    cases hT : bb.terminator with
    | goto target => rw [hT] at hRest; exact hRest
    | return_ =>
      rw [hT] at hRest; dsimp at hRest
      cases hC : bb.cleanup with
      | true => exact True.intro
      | false =>
        rw [hC] at hRest; dsimp at hRest; dsimp
        cases h0 : Trusted.MirSemantics.getElem? exitEnv 0 with
        | none => rw [h0] at hRest; cases hRest
        | some a =>
          rw [h0] at hRest
          cases a with
          | liveInit => rfl
          | liveUninit => cases hRest
          | dead => cases hRest
    | switchInt discr targets =>
      rw [hT] at hRest; dsimp at hRest
      cases hOp : stepAbsOperand body.locals exitEnv discr with
      | none => rw [hOp] at hRest; cases hRest
      | some afterEnv =>
        rw [hOp] at hRest; dsimp at hRest
        let ⟨hOw, hBs⟩ := bool_and_true hRest
        exact ⟨afterEnv, hOp, hOw, hBs⟩
    | unreachable => exact True.intro
    | unwindResume => exact True.intro
    | assert _ _ _ _ _ => exact True.intro
    | call _ _ _ _ _ => exact True.intro
    | unsupported => exact True.intro

private theorem initAbsEnvLoop_length (body : Body) (base : Nat)
    (tys : List MirTy) :
    (initAbsEnvLoop body base tys).length = tys.length := by
  induction tys generalizing base with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [initAbsEnvLoop, List.length]
    rw [ih (base + 1)]

private theorem initAbsEnvLoop_getElem? (body : Body) (base : Nat)
    (tys : List MirTy) (i : Nat) (ty : MirTy)
    (hTy : Trusted.MirSemantics.getElem? tys i = some ty) :
    Trusted.MirSemantics.getElem? (initAbsEnvLoop body base tys) i =
      some (initAbsSlot body (base + i) ty) := by
  induction tys generalizing base i with
  | nil => cases hTy
  | cons t rest ih =>
    cases i with
    | zero => injection hTy with hEq; subst hEq; rfl
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTy
      rw [hAdd] at hRec
      exact hRec

private theorem initLocals_cert_bisim_moveToCopy {bSrc bTgt : Body} {args : List Val}
    (hRel : isMoveToCopyBody bSrc bTgt = true)
    (hArgs : checkArgsMatch args ((bSrc.locals.drop 1).take bSrc.argumentCount) = true) :
    LocalsCertBisim false bSrc.locals
      (initAbsEnvLoop bSrc 0 bSrc.locals)
      (initLocalsLoop bSrc args 0 bSrc.locals)
      (initLocalsLoop bTgt args 0 bTgt.locals) := by
  rw [← initLocalsLoop_eq_of_moveToCopy args hRel]
  refine ⟨initAbsEnvLoop_length bSrc 0 bSrc.locals,
          initLocalsLoop_length bSrc args 0 bSrc.locals,
          initLocalsLoop_length bSrc args 0 bSrc.locals, ?_⟩
  intro i ty a s1 s2 hTy hA hS1 hS2
  rw [hS1] at hS2; injection hS2 with hEqS; subst hEqS
  have hAG := initAbsEnvLoop_getElem? bSrc 0 bSrc.locals i ty hTy
  have hSG := initLocalsLoop_getElem? bSrc args 0 bSrc.locals i ty hTy
  rw [Nat.zero_add] at hAG hSG
  rw [hAG] at hA; injection hA with hAEq; subst hAEq
  rw [hSG] at hS1; injection hS1 with hS1Eq; subst hS1Eq
  cases i with
  | zero =>
    dsimp [initAbsSlot, Nat.beq]
    exact slotCertBisim_liveUninit_pair ty
  | succ k =>
    dsimp [initAbsSlot, Nat.beq]
    cases hLe : Nat.ble (k + 1) bSrc.argumentCount with
    | true =>
      dsimp
      have hKlt : k < bSrc.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((bSrc.locals.drop 1).take bSrc.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 bSrc.locals bSrc.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]
      exact ⟨v, rfl, rfl, hChk⟩
    | false =>
      dsimp
      cases hasStorageAnnotation bSrc (k + 1) with
      | true =>
        exact ⟨⟨fun h => h, fun h => h⟩, True.intro, True.intro⟩
      | false =>
        exact slotCertBisim_liveUninit_pair ty

private theorem initLocals_cert_bisim_removeStorage {bSrc bTgt : Body} {args : List Val}
    (hRel : isRemoveStorageMarkersBody bSrc bTgt = true)
    (hArgs : checkArgsMatch args ((bSrc.locals.drop 1).take bSrc.argumentCount) = true) :
    LocalsCertBisim true bSrc.locals
      (initAbsEnvLoop bSrc 0 bSrc.locals)
      (initLocalsLoop bSrc args 0 bSrc.locals)
      (initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨hArgEq, hLocEq, _, _, _, _⟩ := body_fields_of_removeStorage hRel
  refine ⟨initAbsEnvLoop_length bSrc 0 bSrc.locals,
          initLocalsLoop_length bSrc args 0 bSrc.locals,
          by rw [initLocalsLoop_length, hLocEq], ?_⟩
  intro i ty a s1 s2 hTy hA hS1 hS2
  have hTy2 : Trusted.MirSemantics.getElem? bTgt.locals i = some ty := by
    rw [← hLocEq]; exact hTy
  have hAG := initAbsEnvLoop_getElem? bSrc 0 bSrc.locals i ty hTy
  have hSG1 := initLocalsLoop_getElem? bSrc args 0 bSrc.locals i ty hTy
  have hSG2 := initLocalsLoop_getElem? bTgt args 0 bTgt.locals i ty hTy2
  rw [Nat.zero_add] at hAG hSG1 hSG2
  rw [hAG] at hA; injection hA with hAEq; subst hAEq
  rw [hSG1] at hS1; injection hS1 with hS1Eq; subst hS1Eq
  rw [hSG2] at hS2; injection hS2 with hS2Eq; subst hS2Eq
  cases i with
  | zero =>
    dsimp [initAbsSlot, Nat.beq]
    exact slotCertBisim_liveUninit_pair ty
  | succ k =>
    dsimp [initAbsSlot, Nat.beq]
    rw [← hArgEq]
    cases hLe : Nat.ble (k + 1) bSrc.argumentCount with
    | true =>
      dsimp
      have hKlt : k < bSrc.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((bSrc.locals.drop 1).take bSrc.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 bSrc.locals bSrc.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]
      exact ⟨v, rfl, rfl, hChk⟩
    | false =>
      dsimp
      have hNoAnn : hasStorageAnnotation bTgt (k + 1) = false :=
        removeStorage_no_storageAnnotation hRel (Nat.zero_lt_succ k)
          (getElem?_some_lt hTy2)
      rw [hNoAnn]; dsimp
      cases hasStorageAnnotation bSrc (k + 1) with
      | true =>
        exact ⟨liveUninitSlot_isLive ty, True.intro, liveUninitSlot_wellTyped ty⟩
      | false =>
        exact slotCertBisim_liveUninit_pair ty

private noncomputable def StateCertBisim (req : Bool) (bodyRel : Body → Body → Bool)
    (pSrc pTgt : Program) (cert : ProgramAbsCert) (s t : State) : Prop :=
  s.callerMem = t.callerMem ∧
  ∃ fSrc fTgt bSrc bTgt bCert,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt ∧
    Trusted.MirSemantics.getElem? cert fSrc.defId = some bCert ∧
    bodyRel bSrc bTgt = true ∧
    checkAbsBody req bSrc bCert = true ∧
    (Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = none ∨
      ∃ bbSrc curEnv exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc ∧
        fSrc.stmtIdx ≤ bbSrc.statements.length ∧
        stepAbsStmts req bSrc.locals curEnv (bbSrc.statements.drop fSrc.stmtIdx) = some exitEnv ∧
        BlockTermOk bSrc bCert bbSrc exitEnv ∧
        LocalsCertBisim req bSrc.locals curEnv fSrc.locals fTgt.locals)

private theorem bisim_step_of_disj {pSrc pTgt : Program} {R : State → State → Prop}
    {s t : State}
    (h : (∃ s' t', evalStep pSrc 0 s = .step s' ∧ evalStep pTgt 0 t = .step t' ∧ R s' t') ∨
         (∃ out, evalStep pSrc 0 s = .done out ∧ evalStep pTgt 0 t = .done out) ∨
         (∃ k, evalStep pSrc 0 s = .fault k ∧ evalStep pTgt 0 t = .fault k)) :
    (∀ s', evalStep pSrc 0 s = .step s' →
      ∃ t', evalStep pTgt 0 t = .step t' ∧ R s' t') ∧
    (∀ t', evalStep pTgt 0 t = .step t' →
      ∃ s', evalStep pSrc 0 s = .step s' ∧ R s' t') ∧
    (∀ out, evalStep pSrc 0 s = .done out ↔ evalStep pTgt 0 t = .done out) ∧
    (∀ k, evalStep pSrc 0 s = .fault k ↔ evalStep pTgt 0 t = .fault k) := by
  cases h with
  | inl hSt =>
    let ⟨s', t', h1, h2, hR⟩ := hSt
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx; rw [h1] at hx; injection hx with heq; subst heq; exact ⟨t', h2, hR⟩
    · intro y hy; rw [h2] at hy; injection hy with heq; subst heq; exact ⟨s', h1, hR⟩
    · intro out; rw [h1, h2]; exact ⟨(fun hx => by cases hx), (fun hx => by cases hx)⟩
    · intro k; rw [h1, h2]; exact ⟨(fun hx => by cases hx), (fun hx => by cases hx)⟩
  | inr hDF =>
    cases hDF with
    | inl hDone =>
      let ⟨o, h1, h2⟩ := hDone
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx; rw [h1] at hx; cases hx
      · intro y hy; rw [h2] at hy; cases hy
      · intro out; rw [h1, h2]
      · intro k; rw [h1, h2]
    | inr hFault =>
      let ⟨k0, h1, h2⟩ := hFault
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx; rw [h1] at hx; cases hx
      · intro y hy; rw [h2] at hy; cases hy
      · intro out; rw [h1, h2]
      · intro k; rw [h1, h2]

private theorem evalStatement_moveToCopy_cert_bisim
    {bSrc bTgt : Body} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {env env' : List AbsSlot} {stmtSrc stmtTgt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hStmt : isMoveToCopyStmt stmtSrc stmtTgt = true)
    (hStep : stepAbsStmt false bSrc.locals env stmtSrc = some env')
    (hInv : LocalsCertBisim false bSrc.locals env fSrc.locals fTgt.locals) :
    (∃ k,
      evalStatement bSrc fSrc cm stmtSrc = .fault k ∧
      evalStatement bTgt fTgt cm stmtTgt = .fault k) ∨
    (∃ l1' l2',
      evalStatement bSrc fSrc cm stmtSrc =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmtTgt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                callerMem := cm } ∧
      LocalsCertBisim false bSrc.locals env' l1' l2') := by
  let ⟨hELen, hLen1, hLen2, hAll⟩ := hInv
  cases stmtSrc with
  | nop =>
    cases stmtTgt with
    | nop =>
      injection hStep with hEqE; subst hEqE
      right
      exact ⟨fSrc.locals, fTgt.locals, rfl, rfl, hInv⟩
    | _ => cases hStmt
  | unsupported => cases hStep
  | storageLive i1 =>
    cases stmtTgt with
    | storageLive i2 =>
      have hi : i1 = i2 := nat_beq_eq hStmt
      subst hi
      dsimp [stepAbsStmt] at hStep
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals i1 with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep; dsimp at hStep
        let ⟨l1', hS1⟩ := setElem?_some_of_lt fSrc.locals i1 (liveUninitSlot ty)
          (by rw [hLen1]; exact getElem?_some_lt hTy)
        let ⟨l2', hS2⟩ := setElem?_some_of_lt fTgt.locals i1 (liveUninitSlot ty)
          (by rw [hLen2]; exact getElem?_some_lt hTy)
        right
        refine ⟨l1', l2', ?_, ?_,
          localsCertBisim_set_all hInv hTy hStep hS1 hS2 (slotCertBisim_liveUninit_pair ty)⟩
        · dsimp [evalStatement]; rw [hTy]; dsimp; rw [hS1]
        · dsimp [evalStatement]; rw [← hLocEq, hTy]; dsimp; rw [hS2]
    | _ => cases hStmt
  | storageDead i1 =>
    cases stmtTgt with
    | storageDead i2 =>
      have hi : i1 = i2 := nat_beq_eq hStmt
      subst hi
      dsimp [stepAbsStmt] at hStep
      cases hZ : Nat.beq i1 0 with
      | true => rw [hZ] at hStep; cases hStep
      | false =>
        rw [hZ] at hStep; dsimp at hStep
        have hLt : i1 < bSrc.locals.length := by
          cases Nat.lt_or_ge i1 bSrc.locals.length with
          | inl hlt => exact hlt
          | inr hge =>
            rw [setElem?_none_of_ge env i1 .dead (by rw [hELen]; exact hge)] at hStep
            cases hStep
        let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals i1 hLt
        let ⟨l1', hS1⟩ := setElem?_some_of_lt fSrc.locals i1 .dead (by rw [hLen1]; exact hLt)
        let ⟨l2', hS2⟩ := setElem?_some_of_lt fTgt.locals i1 .dead (by rw [hLen2]; exact hLt)
        right
        refine ⟨l1', l2', ?_, ?_,
          localsCertBisim_set_all hInv hTy hStep hS1 hS2
            ⟨⟨fun h => h, fun h => h⟩, True.intro, True.intro⟩⟩
        · dsimp [evalStatement]; rw [hZ]; dsimp; rw [hS1]
        · dsimp [evalStatement]; rw [hZ]; dsimp; rw [hS2]
    | _ => cases hStmt
  | assign d1 rv1 =>
    cases stmtTgt with
    | assign d2 rv2 =>
      let ⟨hD, hRv⟩ := bool_and_true hStmt
      have hd : d1 = d2 := placeEq_eq hD
      subst hd
      dsimp [stepAbsStmt] at hStep
      cases hP : d1.projection.isEmpty with
      | false => rw [hP] at hStep; cases hStep
      | true =>
        rw [hP] at hStep; dsimp at hStep
        cases hTy : Trusted.MirSemantics.getElem? bSrc.locals d1.localId with
        | none => rw [hTy] at hStep; cases hStep
        | some dstTy =>
          rw [hTy] at hStep; dsimp at hStep
          cases hSR : stepAbsRvalue bSrc.locals env rv1 with
          | none => rw [hSR] at hStep; cases hStep
          | some env1 =>
            rw [hSR] at hStep; dsimp at hStep
            cases hA1 : Trusted.MirSemantics.getElem? env1 d1.localId with
            | none => rw [hA1] at hStep; cases hStep
            | some a1 =>
              rw [hA1] at hStep
              have hSetEnv : setElem? env1 d1.localId .liveInit = some env' := by
                cases a1 <;> exact hStep
              cases evalRvalue_cert_bisim (dstTy := dstTy) hInv hRv hSR with
              | inl hErr =>
                let ⟨k, h1, h2⟩ := hErr
                left
                refine ⟨k, ?_, ?_⟩
                · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [h1]
                · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [h2]
              | inr hOk =>
                let ⟨val, l1, l2, hR1, hR2, hInv1⟩ := hOk
                let ⟨_, hL1, hL2, hAll1⟩ := hInv1
                cases hChk : checkVal val dstTy with
                | false =>
                  left
                  refine ⟨.unsupported, ?_, ?_⟩
                  · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [hR1]; dsimp
                    dsimp [writePlace]; rw [hChk]; rfl
                  · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [hR2]; dsimp
                    dsimp [writePlace]; rw [hChk]; rfl
                | true =>
                  let ⟨s1, hG1⟩ := getElem?_some_of_lt l1 d1.localId
                    (by rw [hL1]; exact getElem?_some_lt hTy)
                  let ⟨s2, hG2⟩ := getElem?_some_of_lt l2 d1.localId
                    (by rw [hL2]; exact getElem?_some_lt hTy)
                  have hSlot := hAll1 d1.localId dstTy a1 s1 s2 hTy hA1 hG1 hG2
                  have hDeadIff : s1 = .dead ↔ s2 = .dead := by
                    cases a1 with
                    | liveInit =>
                      let ⟨_, h1, h2, _⟩ := hSlot
                      rw [h1, h2]
                    | liveUninit =>
                      let ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _⟩ := hSlot
                      rw [h1, h2]; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
                    | dead => exact hSlot.1
                  cases s1 with
                  | dead =>
                    have hs2 : s2 = .dead := hDeadIff.mp rfl
                    subst hs2
                    left
                    refine ⟨.undefined, ?_, ?_⟩
                    · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [hR1]; dsimp
                      dsimp [writePlace]; rw [hChk]; dsimp; rw [hG1]
                    · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [hR2]; dsimp
                      dsimp [writePlace]; rw [hChk]; dsimp; rw [hG2]
                  | live opt1 =>
                    cases s2 with
                    | dead => exact False.elim (by cases hDeadIff.mpr rfl)
                    | live opt2 =>
                      let ⟨l1', hW1⟩ := setElem?_some_of_lt l1 d1.localId (.live (some val))
                        (by rw [hL1]; exact getElem?_some_lt hTy)
                      let ⟨l2', hW2⟩ := setElem?_some_of_lt l2 d1.localId (.live (some val))
                        (by rw [hL2]; exact getElem?_some_lt hTy)
                      right
                      refine ⟨l1', l2', ?_, ?_,
                        localsCertBisim_set_all hInv1 hTy hSetEnv hW1 hW2
                          ⟨val, rfl, rfl, hChk⟩⟩
                      · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [hR1]; dsimp
                        dsimp [writePlace]; rw [hChk]; dsimp; rw [hG1]; dsimp; rw [hW1]
                      · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [hR2]; dsimp
                        dsimp [writePlace]; rw [hChk]; dsimp; rw [hG2]; dsimp; rw [hW2]
    | _ => cases hStmt

private theorem evalStatement_removeStorage_cert_bisim
    {bSrc bTgt : Body} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {env env' : List AbsSlot} {stmtSrc stmtTgt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hStmt : isRemoveStorageMarkersStmt bSrc.locals.length stmtSrc stmtTgt = true)
    (hStep : stepAbsStmt true bSrc.locals env stmtSrc = some env')
    (hInv : LocalsCertBisim true bSrc.locals env fSrc.locals fTgt.locals) :
    (∃ k,
      evalStatement bSrc fSrc cm stmtSrc = .fault k ∧
      evalStatement bTgt fTgt cm stmtTgt = .fault k) ∨
    (∃ l1' l2',
      evalStatement bSrc fSrc cm stmtSrc =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmtTgt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                callerMem := cm } ∧
      LocalsCertBisim true bSrc.locals env' l1' l2') := by
  let ⟨hELen, hLen1, hLen2, hAll⟩ := hInv
  cases stmtSrc with
  | nop =>
    cases stmtTgt with
    | nop =>
      injection hStep with hEqE; subst hEqE
      right; exact ⟨fSrc.locals, fTgt.locals, rfl, rfl, hInv⟩
    | _ => cases hStmt
  | unsupported => cases hStep
  | storageLive id =>
    cases stmtTgt with
    | nop =>
      dsimp [stepAbsStmt] at hStep
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals id with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep; dsimp at hStep
        let ⟨a, hA⟩ := getElem?_some_of_lt env id (by rw [hELen]; exact getElem?_some_lt hTy)
        let ⟨s1, hG1⟩ := getElem?_some_of_lt fSrc.locals id (by rw [hLen1]; exact getElem?_some_lt hTy)
        let ⟨s2, hG2⟩ := getElem?_some_of_lt fTgt.locals id (by rw [hLen2]; exact getElem?_some_lt hTy)
        have hSlot := hAll id ty a s1 s2 hTy hA hG1 hG2
        have hLive2 : ∃ opt2, s2 = .live opt2 ∧ SlotWellTyped ty (.live opt2) := by
          cases a with
          | liveInit => let ⟨v, _, h2, hC⟩ := hSlot; exact ⟨some v, h2, hC⟩
          | liveUninit => let ⟨_, ⟨o2, h2⟩, _, hW2⟩ := hSlot; rw [h2] at hW2; exact ⟨o2, h2, hW2⟩
          | dead => let ⟨⟨o2, h2⟩, _, hW2⟩ := hSlot; rw [h2] at hW2; exact ⟨o2, h2, hW2⟩
        let ⟨opt2, hS2Eq, hWt2⟩ := hLive2
        subst hS2Eq
        let ⟨l1', hSet1⟩ := setElem?_some_of_lt fSrc.locals id (liveUninitSlot ty)
          (by rw [hLen1]; exact getElem?_some_lt hTy)
        right
        refine ⟨l1', fTgt.locals, ?_, rfl,
          localsCertBisim_set_env_left hInv hTy hG2 hStep hSet1
            (slotCertBisim_liveUninit_left hWt2)⟩
        dsimp [evalStatement]; rw [hTy]; dsimp; rw [hSet1]
    | storageLive i2 =>
      let ⟨hNotLt, _⟩ := bool_and_true hStmt
      have hGe : bSrc.locals.length ≤ id := nat_blt_false_ge (bool_not_true hNotLt)
      dsimp [stepAbsStmt] at hStep
      rw [getElem?_none_of_ge hGe] at hStep
      cases hStep
    | _ => cases hStmt
  | storageDead id =>
    cases stmtTgt with
    | nop =>
      let ⟨_, hLtB⟩ := bool_and_true hStmt
      have hLt : id < bSrc.locals.length := nat_blt_lt hLtB
      dsimp [stepAbsStmt] at hStep
      cases hZ : Nat.beq id 0 with
      | true => rw [hZ] at hStep; cases hStep
      | false =>
        rw [hZ] at hStep; dsimp at hStep
        let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals id hLt
        let ⟨a, hA⟩ := getElem?_some_of_lt env id (by rw [hELen]; exact hLt)
        let ⟨s1, hG1⟩ := getElem?_some_of_lt fSrc.locals id (by rw [hLen1]; exact hLt)
        let ⟨s2, hG2⟩ := getElem?_some_of_lt fTgt.locals id (by rw [hLen2]; exact hLt)
        have hSlot := hAll id ty a s1 s2 hTy hA hG1 hG2
        have hLive2 : ∃ opt2, s2 = .live opt2 ∧ SlotWellTyped ty (.live opt2) := by
          cases a with
          | liveInit => let ⟨v, _, h2, hC⟩ := hSlot; exact ⟨some v, h2, hC⟩
          | liveUninit => let ⟨_, ⟨o2, h2⟩, _, hW2⟩ := hSlot; rw [h2] at hW2; exact ⟨o2, h2, hW2⟩
          | dead => let ⟨⟨o2, h2⟩, _, hW2⟩ := hSlot; rw [h2] at hW2; exact ⟨o2, h2, hW2⟩
        let ⟨opt2, hS2Eq, hWt2⟩ := hLive2
        subst hS2Eq
        let ⟨l1', hSet1⟩ := setElem?_some_of_lt fSrc.locals id .dead (by rw [hLen1]; exact hLt)
        right
        refine ⟨l1', fTgt.locals, ?_, rfl,
          localsCertBisim_set_env_left hInv hTy hG2 hStep hSet1
            ⟨⟨opt2, rfl⟩, True.intro, hWt2⟩⟩
        dsimp [evalStatement]; rw [hZ]; dsimp; rw [hSet1]
    | storageDead i2 =>
      let ⟨hOr, _⟩ := bool_and_true hStmt
      dsimp [stepAbsStmt] at hStep
      cases bool_or_true hOr with
      | inl hZero => rw [hZero] at hStep; cases hStep
      | inr hNotLt =>
        have hGe : bSrc.locals.length ≤ id := nat_blt_false_ge (bool_not_true hNotLt)
        cases hZ : Nat.beq id 0 with
        | true => rw [hZ] at hStep; cases hStep
        | false =>
          rw [hZ] at hStep; dsimp at hStep
          rw [setElem?_none_of_ge env id .dead (by rw [hELen]; exact hGe)] at hStep
          cases hStep
    | _ => cases hStmt
  | assign d1 rv1 =>
    cases stmtTgt with
    | assign d2 rv2 =>
      let ⟨hD, hRvEq⟩ := bool_and_true hStmt
      have hd : d1 = d2 := placeEq_eq hD
      subst hd
      have hRv : rvalueRel isMoveToCopyOperand rv1 rv2 = true :=
        rvalueRel_operandEq_imp_moveToCopy hRvEq
      dsimp [stepAbsStmt] at hStep
      cases hP : d1.projection.isEmpty with
      | false => rw [hP] at hStep; cases hStep
      | true =>
        rw [hP] at hStep; dsimp at hStep
        cases hTy : Trusted.MirSemantics.getElem? bSrc.locals d1.localId with
        | none => rw [hTy] at hStep; cases hStep
        | some dstTy =>
          rw [hTy] at hStep; dsimp at hStep
          cases hSR : stepAbsRvalue bSrc.locals env rv1 with
          | none => rw [hSR] at hStep; cases hStep
          | some env1 =>
            rw [hSR] at hStep; dsimp at hStep
            cases hA1 : Trusted.MirSemantics.getElem? env1 d1.localId with
            | none => rw [hA1] at hStep; cases hStep
            | some a1 =>
              rw [hA1] at hStep
              cases a1 with
              | dead => cases hStep
              | liveInit | liveUninit =>
                cases evalRvalue_cert_bisim (dstTy := dstTy) hInv hRv hSR with
                | inl hErr =>
                  let ⟨k, h1, h2⟩ := hErr
                  left
                  refine ⟨k, ?_, ?_⟩
                  · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [h1]
                  · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [h2]
                | inr hOk =>
                  let ⟨val, l1, l2, hR1, hR2, hInv1⟩ := hOk
                  let ⟨_, hL1, hL2, hAll1⟩ := hInv1
                  cases hChk : checkVal val dstTy with
                  | false =>
                    left
                    refine ⟨.unsupported, ?_, ?_⟩
                    · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [hR1]; dsimp
                      dsimp [writePlace]; rw [hChk]; rfl
                    · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [hR2]; dsimp
                      dsimp [writePlace]; rw [hChk]; rfl
                  | true =>
                    let ⟨s1, hG1⟩ := getElem?_some_of_lt l1 d1.localId
                      (by rw [hL1]; exact getElem?_some_lt hTy)
                    let ⟨s2, hG2⟩ := getElem?_some_of_lt l2 d1.localId
                      (by rw [hL2]; exact getElem?_some_lt hTy)
                    have hSlot := hAll1 d1.localId dstTy _ s1 s2 hTy hA1 hG1 hG2
                    have hLiveBoth : (∃ o1, s1 = .live o1) ∧ (∃ o2, s2 = .live o2) := by
                      first
                      | (let ⟨v, h1, h2, _⟩ := hSlot; exact ⟨⟨some v, h1⟩, ⟨some v, h2⟩⟩)
                      | (let ⟨h1, h2, _, _⟩ := hSlot; exact ⟨h1, h2⟩)
                    let ⟨⟨o1, hS1Eq⟩, ⟨o2, hS2Eq⟩⟩ := hLiveBoth
                    subst hS1Eq; subst hS2Eq
                    let ⟨l1', hW1⟩ := setElem?_some_of_lt l1 d1.localId (.live (some val))
                      (by rw [hL1]; exact getElem?_some_lt hTy)
                    let ⟨l2', hW2⟩ := setElem?_some_of_lt l2 d1.localId (.live (some val))
                      (by rw [hL2]; exact getElem?_some_lt hTy)
                    right
                    refine ⟨l1', l2', ?_, ?_,
                      localsCertBisim_set_all hInv1 hTy hStep hW1 hW2
                        ⟨val, rfl, rfl, hChk⟩⟩
                    · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [hR1]; dsimp
                      dsimp [writePlace]; rw [hChk]; dsimp; rw [hG1]; dsimp; rw [hW1]
                    · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [hR2]; dsimp
                      dsimp [writePlace]; rw [hChk]; dsimp; rw [hG2]; dsimp; rw [hW2]
    | _ => cases hStmt

private theorem jump_target_cert_bisim {req : Bool}
    {bSrc : Body} {bCert : BodyAbsCert} {env : List AbsSlot}
    {l1 l2 : List LocalSlot} {tgt : BasicBlockId}
    (hBodyCert : checkAbsBody req bSrc bCert = true)
    (hEdge : checkEdgeTarget bSrc.basicBlocks.length bCert env tgt = true)
    (hInv : LocalsCertBisim req bSrc.locals env l1 l2) :
    Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = none ∨
    ∃ bbNext entryEnv exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbNext ∧
      0 ≤ bbNext.statements.length ∧
      stepAbsStmts req bSrc.locals entryEnv (bbNext.statements.drop 0) = some exitEnv ∧
      BlockTermOk bSrc bCert bbNext exitEnv ∧
      LocalsCertBisim req bSrc.locals entryEnv l1 l2 := by
  unfold checkEdgeTarget at hEdge
  cases hLt : Nat.blt tgt bSrc.basicBlocks.length with
  | false =>
    left
    exact getElem?_none_of_ge (nat_blt_false_ge hLt)
  | true =>
    rw [hLt] at hEdge; dsimp at hEdge
    cases hC : Trusted.MirSemantics.getElem? bCert tgt with
    | none => rw [hC] at hEdge; cases hEdge
    | some optEnv =>
      rw [hC] at hEdge
      cases optEnv with
      | none => cases hEdge
      | some tgtEnv =>
        dsimp at hEdge
        let ⟨bbNext, hBB⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt (nat_blt_lt hLt)
        unfold checkAbsBody at hBodyCert
        let ⟨_, hLoop⟩ := bool_and_true hBodyCert
        have hBlkOk : checkAbsBlock req bSrc bCert tgt bbNext = true := by
          have h0 := checkAbsBlocksLoop_getElem? req bSrc bCert 0 bSrc.basicBlocks tgt bbNext hLoop hBB
          rw [Nat.zero_add] at h0
          exact h0
        let ⟨_, exitEnv, hStmts, hTermOk⟩ := checkAbsBlock_elim hBlkOk hC
        right
        exact ⟨bbNext, tgtEnv, exitEnv, hBB, Nat.zero_le _, hStmts, hTermOk,
               localsCertBisim_mono hEdge hInv⟩

private theorem evalStep_cert_bisim_generic {req : Bool}
    {bodyRel : Body → Body → Bool} {blockRel : Body → BasicBlock → BasicBlock → Bool}
    {stmtRel : Body → StatementKind → StatementKind → Bool}
    {pSrc pTgt : Program} {cert : ProgramAbsCert} {s t : State}
    (hBodyBlocks : ∀ b1 b2, bodyRel b1 b2 = true →
      b1.locals = b2.locals ∧ listRel (blockRel b1) b1.basicBlocks b2.basicBlocks = true)
    (hBlockParts : ∀ b1 bb1 bb2, blockRel b1 bb1 bb2 = true →
      bb1.cleanup = bb2.cleanup ∧
      listRel (stmtRel b1) bb1.statements bb2.statements = true ∧
      terminatorRel isMoveToCopyOperand bb1.terminator bb2.terminator = true)
    (hStmtBisim : ∀ b1 b2 f1 f2 cm env env' st1 st2,
      bodyRel b1 b2 = true →
      stmtRel b1 st1 st2 = true →
      stepAbsStmt req b1.locals env st1 = some env' →
      LocalsCertBisim req b1.locals env f1.locals f2.locals →
      (∃ k, evalStatement b1 f1 cm st1 = .fault k ∧
            evalStatement b2 f2 cm st2 = .fault k) ∨
      (∃ l1' l2',
        evalStatement b1 f1 cm st1 =
          .step { frames := [{ f1 with stmtIdx := f1.stmtIdx + 1, locals := l1' }],
                  callerMem := cm } ∧
        evalStatement b2 f2 cm st2 =
          .step { frames := [{ f2 with stmtIdx := f2.stmtIdx + 1, locals := l2' }],
                  callerMem := cm } ∧
        LocalsCertBisim req b1.locals env' l1' l2'))
    (hRel : StateCertBisim req bodyRel pSrc pTgt cert s t) :
    (∃ s' t', evalStep pSrc 0 s = .step s' ∧ evalStep pTgt 0 t = .step t' ∧
      StateCertBisim req bodyRel pSrc pTgt cert s' t') ∨
    (∃ out, evalStep pSrc 0 s = .done out ∧ evalStep pTgt 0 t = .done out) ∨
    (∃ k, evalStep pSrc 0 s = .fault k ∧ evalStep pTgt 0 t = .fault k) := by
  let ⟨hCm, fSrc, fTgt, bSrc, bTgt, bCert, hFS, hFT, hDef, hBlk, hStmt,
       hBS, hBT, hBC, hBody, hCertB, hBlkState⟩ := hRel
  let ⟨hLocEq, hBlocks⟩ := hBodyBlocks bSrc bTgt hBody
  cases hBlkState with
  | inl hNoBB =>
    have hNoBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
      rw [← hBlk]; exact (listRel_getElem?_none_iff fSrc.blockIdx hBlocks).mp hNoBB
    right; right
    refine ⟨.unsupported, ?_, ?_⟩
    · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hNoBB]
    · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hNoBBT]
  | inr hInBB =>
    let ⟨bbSrc, curEnv, exitEnv, hBBS, hStmtLe, hDropStmts, hTermOk, hInv⟩ := hInBB
    let ⟨bbTgt, hBBT0, hBBRel⟩ := listRel_getElem?_left hBlocks hBBS
    have hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
      rw [← hBlk]; exact hBBT0
    let ⟨hClean, hStmtsRel, hTermRel⟩ := hBlockParts bSrc bbSrc bbTgt hBBRel
    have hStmtsLen : bbSrc.statements.length = bbTgt.statements.length :=
      listRel_length hStmtsRel
    cases hSS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
    | some stmtSrc =>
      let ⟨stmtTgt, hST0, hSRel⟩ := listRel_getElem?_left hStmtsRel hSS
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some stmtTgt := by
        rw [← hStmt]; exact hST0
      rw [drop_eq_cons_of_getElem? hSS] at hDropStmts
      dsimp [stepAbsStmts] at hDropStmts
      cases hStep1 : stepAbsStmt req bSrc.locals curEnv stmtSrc with
      | none => rw [hStep1] at hDropStmts; cases hDropStmts
      | some nextEnv =>
        rw [hStep1] at hDropStmts; dsimp at hDropStmts
        cases hStmtBisim bSrc bTgt fSrc fTgt s.callerMem curEnv nextEnv stmtSrc stmtTgt
            hBody hSRel hStep1 hInv with
        | inl hF =>
          let ⟨k, hF1, hF2⟩ := hF
          right; right
          refine ⟨k, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp; rw [hSS]; exact hF1
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp; rw [hST]; dsimp
            rw [← hCm]; exact hF2
        | inr hSt =>
          let ⟨l1', l2', hSt1, hSt2, hInv'⟩ := hSt
          left
          refine ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                    callerMem := s.callerMem },
                  { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                    callerMem := t.callerMem }, ?_, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp; rw [hSS]; exact hSt1
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp; rw [hST]; dsimp
            rw [← hCm]; exact hSt2
          · refine ⟨hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, hBlk, by rw [hStmt],
              hBS, hBT, hBC, hBody, hCertB, Or.inr ⟨bbSrc, nextEnv, exitEnv, hBBS,
              getElem?_some_lt hSS, hDropStmts, hTermOk, hInv'⟩⟩
    | none =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
        rw [← hStmt]; exact (listRel_getElem?_none_iff fSrc.stmtIdx hStmtsRel).mp hSS
      have hGe : bbSrc.statements.length ≤ fSrc.stmtIdx := by
        cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
        | inr hge => exact hge
        | inl hlt =>
          let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
          rw [hSS] at hx; cases hx
      have hIdxEq : fSrc.stmtIdx = bbSrc.statements.length :=
        Nat.le_antisymm hStmtLe hGe
      have hAtEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length = true := by
        rw [hIdxEq]; exact nat_beq_refl _
      rw [hIdxEq, drop_length_nil] at hDropStmts
      injection hDropStmts with hEnvEq
      subst hEnvEq
      unfold BlockTermOk at hTermOk
      cases hTS : bbSrc.terminator with
      | goto t1 =>
        cases hTT : bbTgt.terminator with
        | goto t2 =>
          rw [hTS, hTT] at hTermRel
          have ht : t1 = t2 := nat_beq_eq hTermRel
          subst ht
          rw [hTS] at hTermOk
          left
          refine ⟨{ frames := [{ fSrc with blockIdx := t1, stmtIdx := 0 }], callerMem := s.callerMem },
                  { frames := [{ fTgt with blockIdx := t1, stmtIdx := 0 }], callerMem := t.callerMem },
                  ?_, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
            rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; rfl
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
            rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
            unfold evalTerminator; rw [hTT]; rfl
          · exact ⟨hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, rfl, rfl,
              hBS, hBT, hBC, hBody, hCertB,
              jump_target_cert_bisim hCertB hTermOk hInv⟩
        | _ => rw [hTS, hTT] at hTermRel; cases hTermRel
      | return_ =>
        cases hTT : bbTgt.terminator with
        | return_ =>
          rw [hTS] at hTermOk
          cases hC : bbSrc.cleanup with
          | true =>
            right; right
            refine ⟨.unsupported, ?_, ?_⟩
            · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
              rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp
              rw [hC]; rfl
            · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
              rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
              unfold evalTerminator; rw [hTT]; dsimp; rw [← hClean, hC]; rfl
          | false =>
            rw [hC] at hTermOk; dsimp at hTermOk
            let ⟨hELen, hL1, hL2, hAll⟩ := hInv
            have h0Lt : 0 < bSrc.locals.length := by
              rw [← hELen]; exact getElem?_some_lt hTermOk
            let ⟨ty0, hTy0⟩ := getElem?_some_of_lt bSrc.locals 0 h0Lt
            let ⟨s1, hG1⟩ := getElem?_some_of_lt fSrc.locals 0 (by rw [hL1]; exact h0Lt)
            let ⟨s2, hG2⟩ := getElem?_some_of_lt fTgt.locals 0 (by rw [hL2]; exact h0Lt)
            let ⟨rv, h1, h2, _⟩ := hAll 0 ty0 .liveInit s1 s2 hTy0 hTermOk hG1 hG2
            subst h1; subst h2
            right; left
            refine ⟨.returned ⟨rv, s.callerMem⟩, ?_, ?_⟩
            · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
              rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp
              rw [hC]; dsimp; rw [hG1]
            · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
              rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
              unfold evalTerminator; rw [hTT]; dsimp; rw [← hClean, hC]; dsimp
              rw [hG2, ← hCm]
        | _ => rw [hTS, hTT] at hTermRel; cases hTermRel
      | switchInt d1 ts1 =>
        cases hTT : bbTgt.terminator with
        | switchInt d2 ts2 =>
          rw [hTS, hTT] at hTermRel
          let ⟨hDRel, hTsRel⟩ := bool_and_true hTermRel
          have hTsEq : ts1 = ts2 := switchTargetsEq_eq hTsRel
          subst hTsEq
          rw [hTS] at hTermOk
          let ⟨afterEnv, hStepOp, hOwOk, hBsOk⟩ := hTermOk
          cases evalPrimitiveOperand_cert_bisim hInv hDRel hStepOp with
          | inl hErr =>
            let ⟨k, h1, h2⟩ := hErr
            right; right
            refine ⟨k, ?_, ?_⟩
            · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
              rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
            · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
              rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
              unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
          | inr hOk =>
            let ⟨dv, l1, l2, h1, h2, hInv1⟩ := hOk
            cases dv with
            | scalar sv =>
              cases hSw : evalSwitchBranches sv.width sv.bits ts1.otherwise ts1.branches with
              | error k =>
                right; right
                refine ⟨k, ?_, ?_⟩
                · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                  rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp
                  rw [h1]; dsimp; rw [hSw]
                · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                  rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                  unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]; dsimp; rw [hSw]
              | ok tgt =>
                have hTgtOk := evalSwitchBranches_target_ok hOwOk hBsOk hSw
                left
                refine ⟨{ frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1 }],
                          callerMem := s.callerMem },
                        { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2 }],
                          callerMem := t.callerMem }, ?_, ?_, ?_⟩
                · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                  rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp
                  rw [h1]; dsimp; rw [hSw]; rfl
                · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                  rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                  unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]; dsimp; rw [hSw]; rfl
                · exact ⟨hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, rfl, rfl,
                    hBS, hBT, hBC, hBody, hCertB,
                    jump_target_cert_bisim hCertB hTgtOk hInv1⟩
            | bool b =>
              cases hSw : evalBoolSwitchBranches b ts1.otherwise ts1.branches with
              | error k =>
                right; right
                refine ⟨k, ?_, ?_⟩
                · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                  rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp
                  rw [h1]; dsimp; rw [hSw]
                · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                  rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                  unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]; dsimp; rw [hSw]
              | ok tgt =>
                have hTgtOk := evalBoolSwitchBranches_target_ok hOwOk hBsOk hSw
                left
                refine ⟨{ frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1 }],
                          callerMem := s.callerMem },
                        { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2 }],
                          callerMem := t.callerMem }, ?_, ?_, ?_⟩
                · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                  rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp
                  rw [h1]; dsimp; rw [hSw]; rfl
                · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                  rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                  unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]; dsimp; rw [hSw]; rfl
                · exact ⟨hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, rfl, rfl,
                    hBS, hBT, hBC, hBody, hCertB,
                    jump_target_cert_bisim hCertB hTgtOk hInv1⟩
            | ptr _ =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
            | unit =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
            | enumVal _ _ =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
            | tuple _ =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
            | bytes _ =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
                rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
                rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
                unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
        | _ => rw [hTS, hTT] at hTermRel; cases hTermRel
      | unreachable =>
        cases hTT : bbTgt.terminator with
        | unreachable =>
          right; right; refine ⟨.undefined, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
            rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
            rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
            unfold evalTerminator; rw [hTT]
        | _ => rw [hTS, hTT] at hTermRel; cases hTermRel
      | unwindResume =>
        cases hTT : bbTgt.terminator with
        | unwindResume =>
          right; right; refine ⟨.unsupported, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
            rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
            rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
            unfold evalTerminator; rw [hTT]
        | _ => rw [hTS, hTT] at hTermRel; cases hTermRel
      | assert _ _ _ _ _ =>
        cases hTT : bbTgt.terminator with
        | assert _ _ _ _ _ =>
          right; right; refine ⟨.unsupported, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
            rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
            rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
            unfold evalTerminator; rw [hTT]
        | _ => rw [hTS, hTT] at hTermRel; cases hTermRel
      | call _ _ _ _ _ =>
        cases hTT : bbTgt.terminator with
        | call _ _ _ _ _ =>
          right; right; refine ⟨.unsupported, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
            rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
            rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
            unfold evalTerminator; rw [hTT]
        | _ => rw [hTS, hTT] at hTermRel; cases hTermRel
      | unsupported =>
        cases hTT : bbTgt.terminator with
        | unsupported =>
          right; right; refine ⟨.unsupported, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
            rw [hSS]; dsimp; rw [hAtEnd]; dsimp; unfold evalTerminator; rw [hTS]
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
            rw [hST]; dsimp; rw [← hStmt, ← hStmtsLen, hAtEnd]; dsimp
            unfold evalTerminator; rw [hTT]
        | _ => rw [hTS, hTT] at hTermRel; cases hTermRel

private theorem entry_block_cert_bisim {req : Bool}
    {bSrc : Body} {bCert : BodyAbsCert} {l1 l2 : List LocalSlot}
    (hBodyCert : checkAbsBody req bSrc bCert = true)
    (hNonEmpty : bSrc.basicBlocks.isEmpty = false)
    (hInitLocs : LocalsCertBisim req bSrc.locals (initAbsEnvLoop bSrc 0 bSrc.locals) l1 l2) :
    ∃ bb0 env0 exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks 0 = some bb0 ∧
      0 ≤ bb0.statements.length ∧
      stepAbsStmts req bSrc.locals env0 (bb0.statements.drop 0) = some exitEnv ∧
      BlockTermOk bSrc bCert bb0 exitEnv ∧
      LocalsCertBisim req bSrc.locals env0 l1 l2 := by
  have hCertCopy := hBodyCert
  unfold checkAbsBody at hCertCopy
  let ⟨h123, hLoop⟩ := bool_and_true hCertCopy
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨_, hEntry⟩ := bool_and_true h12
  rw [hNonEmpty] at hEntry; dsimp at hEntry
  cases hC0 : Trusted.MirSemantics.getElem? bCert 0 with
  | none => rw [hC0] at hEntry; cases hEntry
  | some optEnv =>
    rw [hC0] at hEntry
    cases optEnv with
    | none => cases hEntry
    | some env0 =>
      dsimp at hEntry
      have h0Lt : 0 < bSrc.basicBlocks.length := by
        cases hBBs : bSrc.basicBlocks with
        | nil => rw [hBBs] at hNonEmpty; cases hNonEmpty
        | cons _ _ => exact Nat.zero_lt_succ _
      let ⟨bb0, hBB0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
      have hBlk0 : checkAbsBlock req bSrc bCert 0 bb0 = true :=
        checkAbsBlocksLoop_getElem? req bSrc bCert 0 bSrc.basicBlocks 0 bb0 hLoop hBB0
      let ⟨_, exitEnv, hStmts, hTermOk⟩ := checkAbsBlock_elim hBlk0 hC0
      exact ⟨bb0, env0, exitEnv, hBB0, Nat.zero_le _, hStmts, hTermOk,
             localsCertBisim_mono hEntry hInitLocs⟩

private theorem moveToCopy_cert_bisim_query {pSrc pTgt : Program}
    {cert : ProgramAbsCert} (q : Query)
    (hRel : isMoveToCopyProgram pSrc pTgt = true)
    (hCert : checkNoUseAfterMoveProgram pSrc cert = true) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨hPw, hVer, hEnt, hBodies⟩ := moveToCopy_program_parts hRel
  have hInitEq := initState_equiv q hPw hVer hEnt hBodies (fun b1 b2 hb => by
    let ⟨hA, hL, _, _, hBL, hSt⟩ := body_fields_of_moveToCopy hb
    exact ⟨hA, hL, hBL, hSt⟩)
  apply bisim_lift (R := StateCertBisim false isMoveToCopyBody pSrc pTgt cert)
  · exact hInitEq.1
  · intro s₀ t₀ hIS hIT
    let ⟨t₀', bSrc, bTgt, hIT', hBS, hBT, hRelB, hNE, _, _, hArgs, hS0, hT0⟩ :=
      hInitEq.2 s₀ hIS
    rw [hIT'] at hIT; injection hIT with hEqT; subst hEqT; subst hS0; subst hT0
    let ⟨bCert, hBC, hCertB⟩ := listRel_getElem?_left hCert hBS
    let ⟨bb0, env0, exitEnv, hBB0, hLe0, hStmts, hTermOk, hInv0⟩ :=
      entry_block_cert_bisim hCertB hNE (initLocals_cert_bisim_moveToCopy hRelB hArgs)
    exact ⟨rfl, _, _, bSrc, bTgt, bCert, rfl, rfl, hEnt, rfl, rfl,
           hBS, hBT, hBC, hRelB, hCertB,
           Or.inr ⟨bb0, env0, exitEnv, hBB0, hLe0, hStmts, hTermOk, hInv0⟩⟩
  · intro s t hSt
    apply bisim_step_of_disj
    exact evalStep_cert_bisim_generic
      (blockRel := fun _ => isMoveToCopyBlock)
      (stmtRel := fun _ => isMoveToCopyStmt)
      (fun b1 b2 hb => by
        let ⟨_, hL, _, _, _, _⟩ := body_fields_of_moveToCopy hb
        unfold isMoveToCopyBody at hb
        let ⟨_, hB⟩ := bool_and_true hb
        exact ⟨hL, hB⟩)
      (fun _ bb1 bb2 hbb => by
        unfold isMoveToCopyBlock at hbb
        let ⟨h12, hT⟩ := bool_and_true hbb
        let ⟨hC, hS⟩ := bool_and_true h12
        exact ⟨bool_beq_eq hC, hS, hT⟩)
      (fun b1 b2 f1 f2 cm env env' st1 st2 hb hst hStep hInv =>
        evalStatement_moveToCopy_cert_bisim (body_fields_of_moveToCopy hb).2.1 hst hStep hInv)
      hSt

private theorem removeStorage_cert_bisim_query {pSrc pTgt : Program}
    {cert : ProgramAbsCert} (q : Query)
    (hRel : isRemoveStorageMarkersProgram pSrc pTgt = true)
    (hCert : checkStorageSafeProgram pSrc cert = true) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨hPw, hVer, hEnt, hBodies⟩ := removeStorage_program_parts hRel
  have hInitEq := initState_equiv q hPw hVer hEnt hBodies (fun b1 b2 hb => by
    let ⟨hA, hL, _, _, hBL, hSt⟩ := body_fields_of_removeStorage hb
    exact ⟨hA, hL, hBL, hSt⟩)
  apply bisim_lift (R := StateCertBisim true isRemoveStorageMarkersBody pSrc pTgt cert)
  · exact hInitEq.1
  · intro s₀ t₀ hIS hIT
    let ⟨t₀', bSrc, bTgt, hIT', hBS, hBT, hRelB, hNE, _, _, hArgs, hS0, hT0⟩ :=
      hInitEq.2 s₀ hIS
    rw [hIT'] at hIT; injection hIT with hEqT; subst hEqT; subst hS0; subst hT0
    let ⟨bCert, hBC, hCertB⟩ := listRel_getElem?_left hCert hBS
    let ⟨bb0, env0, exitEnv, hBB0, hLe0, hStmts, hTermOk, hInv0⟩ :=
      entry_block_cert_bisim hCertB hNE (initLocals_cert_bisim_removeStorage hRelB hArgs)
    exact ⟨rfl, _, _, bSrc, bTgt, bCert, rfl, rfl, hEnt, rfl, rfl,
           hBS, hBT, hBC, hRelB, hCertB,
           Or.inr ⟨bb0, env0, exitEnv, hBB0, hLe0, hStmts, hTermOk, hInv0⟩⟩
  · intro s t hSt
    apply bisim_step_of_disj
    exact evalStep_cert_bisim_generic
      (blockRel := fun b => isRemoveStorageMarkersBlock b.locals.length)
      (stmtRel := fun b => isRemoveStorageMarkersStmt b.locals.length)
      (fun b1 b2 hb => by
        let ⟨_, hL, _, _, _, _⟩ := body_fields_of_removeStorage hb
        unfold isRemoveStorageMarkersBody at hb
        let ⟨_, hB⟩ := bool_and_true hb
        exact ⟨hL, hB⟩)
      (fun _ bb1 bb2 hbb => by
        unfold isRemoveStorageMarkersBlock at hbb
        let ⟨h12, hT⟩ := bool_and_true hbb
        let ⟨hC, hS⟩ := bool_and_true h12
        exact ⟨bool_beq_eq hC, hS, terminatorRel_operandEq_imp_moveToCopy hT⟩)
      (fun b1 b2 f1 f2 cm env env' st1 st2 hb hst hStep hInv =>
        evalStatement_removeStorage_cert_bisim (body_fields_of_removeStorage hb).2.1 hst hStep hInv)
      hSt

/-! ## Part III: Core Target Theorems Over `Trusted.MirSemantics` -/

/-- **Theorem 1 (Unconditional Codegen Forward Refinement for `MoveToCopy`):**
Replacing any subset of `Operand.move p` occurrences with `Operand.copy p`
across `pSrc : Trusted.MirAst.Program` unconditionally refines $M_{\text{anneal}}$
execution whenever `pSrc` is `WellFormed`: it preserves `WellFormed`, exact
finite `Behavior` (`↔`), infinite `Diverges` (`↔`), `SatisfiesPost`, and
`BodyVerified` without requiring any static liveness certificate. -/
theorem codegen_moveToCopy_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isMoveToCopyProgram pSrc pTgt = true) :
    (∀ q : Query,
      WellFormed pSrc q →
      WellFormed pTgt q ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (Diverges pTgt q ↔ Diverges pSrc q)) ∧
    (∀ (q : Query) (post : TerminalOut → Prop),
      SatisfiesPost pSrc q post → SatisfiesPost pTgt q post) ∧
    (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      BodyVerified pSrc defId bSrc safetyPre →
      BodyVerified pTgt defId bTgt safetyPre) := by
  refine ⟨fun q hWf => moveToCopy_fwd_query q hRel hWf, ?_, ?_⟩
  · intro q post hSat
    let ⟨hWfT, hBehIff, _⟩ := moveToCopy_fwd_query q hRel hSat.1
    exact ⟨hWfT, fun out hB => hSat.2 out ((hBehIff out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hBS hBT hVer
    let ⟨hPw, hVerV, _, hBodies⟩ := moveToCopy_program_parts hRel
    let ⟨bTgt', hBT', hRelB⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hArg, hLoc, hUns, hId, hBLen, hSt⟩ := body_fields_of_moveToCopy hRelB
    refine ⟨hBT, ?_, ?_⟩
    · rw [← bodyStaticAdmitted_eq_of_fields hPw hVerV hArg hLoc hId hBLen hSt]
      exact hVer.2.1
    · intro args hArgs hPre
      have hArgsSrc : ValidEntryArgs bSrc args := by
        unfold ValidEntryArgs; rw [hArg, hLoc]; exact hArgs
      have hPreSrc : bSrc.isUnsafe = true → safetyPre args := by
        rw [hUns]; exact hPre
      exact (moveToCopy_fwd_query { args := args } (moveToCopy_entryProg defId hRel)
        (hVer.2.2 args hArgsSrc hPreSrc)).1

/-- **Theorem 2 (Certified Bidirectional VC Transport for `MoveToCopy`):**
When `isMoveToCopyProgram pSrc pTgt = true` is paired with a valid
`checkNoUseAfterMoveProgram pSrc cert = true` certificate, `pTgt` and `pSrc`
are in exact operational equivalence across **all** queries `q : Query`
(preserving `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`,
`SatisfiesPost`, and `BodyVerified` in both directions, enabling Anneal proofs
discharged on non-destructive-read `pTgt` to transport back to `pSrc` with
`deinitMovedPlace = true`). -/
theorem vc_transport_moveToCopy_certified_iff
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isMoveToCopyProgram pSrc pTgt = true)
    (hCert : checkNoUseAfterMoveProgram pSrc cert = true) :
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
        BodyVerified pSrc defId bSrc safetyPre)) := by
  refine ⟨fun q => moveToCopy_cert_bisim_query q hRel hCert, ?_, ?_⟩
  · intro q post
    let ⟨hWfIff, hBehIff, _, _⟩ := moveToCopy_cert_bisim_query q hRel hCert
    constructor
    · intro hSat
      exact ⟨hWfIff.mp hSat.1, fun out hB => hSat.2 out ((hBehIff out).mpr hB)⟩
    · intro hSat
      exact ⟨hWfIff.mpr hSat.1, fun out hB => hSat.2 out ((hBehIff out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hBS hBT
    let ⟨hPw, hVerV, _, hBodies⟩ := moveToCopy_program_parts hRel
    let ⟨bTgt', hBT', hRelB⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hArg, hLoc, hUns, hId, hBLen, hSt⟩ := body_fields_of_moveToCopy hRelB
    have hAdm := bodyStaticAdmitted_eq_of_fields hPw hVerV hArg hLoc hId hBLen hSt
    constructor
    · intro hVer
      refine ⟨hBS, by rw [hAdm]; exact hVer.2.1, ?_⟩
      intro args hArgs hPre
      have hArgsT : ValidEntryArgs bTgt args := by
        unfold ValidEntryArgs; rw [← hArg, ← hLoc]; exact hArgs
      have hPreT : bTgt.isUnsafe = true → safetyPre args := by
        rw [← hUns]; exact hPre
      exact (moveToCopy_cert_bisim_query { args := args }
        (moveToCopy_entryProg defId hRel) hCert).1.mp
        (hVer.2.2 args hArgsT hPreT)
    · intro hVer
      refine ⟨hBT, by rw [← hAdm]; exact hVer.2.1, ?_⟩
      intro args hArgs hPre
      have hArgsS : ValidEntryArgs bSrc args := by
        unfold ValidEntryArgs; rw [hArg, hLoc]; exact hArgs
      have hPreS : bSrc.isUnsafe = true → safetyPre args := by
        rw [hUns]; exact hPre
      exact (moveToCopy_cert_bisim_query { args := args }
        (moveToCopy_entryProg defId hRel) hCert).1.mpr
        (hVer.2.2 args hArgsS hPreS)

/-- **Theorem 3 (Unconditional Codegen Forward Refinement for
`RemoveStorageMarkers`):**
Eliding all in-bounds `StorageLive(id)` (`0 ≤ id < locals.length`) and
non-return `StorageDead(id)` (`1 ≤ id < locals.length`) statements to `.nop`
across `pSrc : Trusted.MirAst.Program` unconditionally preserves `WellFormed`,
exact finite `Behavior` (`↔`), infinite `Diverges` (`↔`), `SatisfiesPost`, and
`BodyVerified` whenever `pSrc` is `WellFormed`. -/
theorem codegen_removeStorageMarkers_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isRemoveStorageMarkersProgram pSrc pTgt = true) :
    (∀ q : Query,
      WellFormed pSrc q →
      WellFormed pTgt q ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (Diverges pTgt q ↔ Diverges pSrc q)) ∧
    (∀ (q : Query) (post : TerminalOut → Prop),
      SatisfiesPost pSrc q post → SatisfiesPost pTgt q post) ∧
    (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      BodyVerified pSrc defId bSrc safetyPre →
      BodyVerified pTgt defId bTgt safetyPre) := by
  refine ⟨fun q hWf => removeStorage_fwd_query q hRel hWf, ?_, ?_⟩
  · intro q post hSat
    let ⟨hWfT, hBehIff, _⟩ := removeStorage_fwd_query q hRel hSat.1
    exact ⟨hWfT, fun out hB => hSat.2 out ((hBehIff out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hBS hBT hVer
    let ⟨hPw, hVerV, _, hBodies⟩ := removeStorage_program_parts hRel
    let ⟨bTgt', hBT', hRelB⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hArg, hLoc, hUns, hId, hBLen, hSt⟩ := body_fields_of_removeStorage hRelB
    refine ⟨hBT, ?_, ?_⟩
    · rw [← bodyStaticAdmitted_eq_of_fields hPw hVerV hArg hLoc hId hBLen hSt]
      exact hVer.2.1
    · intro args hArgs hPre
      have hArgsSrc : ValidEntryArgs bSrc args := by
        unfold ValidEntryArgs; rw [hArg, hLoc]; exact hArgs
      have hPreSrc : bSrc.isUnsafe = true → safetyPre args := by
        rw [hUns]; exact hPre
      exact (removeStorage_fwd_query { args := args } (removeStorage_entryProg defId hRel)
        (hVer.2.2 args hArgsSrc hPreSrc)).1

/-- **Theorem 4 (Certified Bidirectional VC Transport for `RemoveStorageMarkers`):**
When `isRemoveStorageMarkersProgram pSrc pTgt = true` is paired with a valid
`checkStorageSafeProgram pSrc cert = true` certificate, `pTgt` and `pSrc`
satisfy bidirectional equivalence (`↔`) for `WellFormed`, `Behavior`,
`ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and `BodyVerified`
across all queries `q : Query`. -/
theorem vc_transport_removeStorageMarkers_certified_iff
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isRemoveStorageMarkersProgram pSrc pTgt = true)
    (hCert : checkStorageSafeProgram pSrc cert = true) :
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
        BodyVerified pSrc defId bSrc safetyPre)) := by
  refine ⟨fun q => removeStorage_cert_bisim_query q hRel hCert, ?_, ?_⟩
  · intro q post
    let ⟨hWfIff, hBehIff, _, _⟩ := removeStorage_cert_bisim_query q hRel hCert
    constructor
    · intro hSat
      exact ⟨hWfIff.mp hSat.1, fun out hB => hSat.2 out ((hBehIff out).mpr hB)⟩
    · intro hSat
      exact ⟨hWfIff.mpr hSat.1, fun out hB => hSat.2 out ((hBehIff out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hBS hBT
    let ⟨hPw, hVerV, _, hBodies⟩ := removeStorage_program_parts hRel
    let ⟨bTgt', hBT', hRelB⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hArg, hLoc, hUns, hId, hBLen, hSt⟩ := body_fields_of_removeStorage hRelB
    have hAdm := bodyStaticAdmitted_eq_of_fields hPw hVerV hArg hLoc hId hBLen hSt
    constructor
    · intro hVer
      refine ⟨hBS, by rw [hAdm]; exact hVer.2.1, ?_⟩
      intro args hArgs hPre
      have hArgsT : ValidEntryArgs bTgt args := by
        unfold ValidEntryArgs; rw [← hArg, ← hLoc]; exact hArgs
      have hPreT : bTgt.isUnsafe = true → safetyPre args := by
        rw [← hUns]; exact hPre
      exact (removeStorage_cert_bisim_query { args := args }
        (removeStorage_entryProg defId hRel) hCert).1.mp
        (hVer.2.2 args hArgsT hPreT)
    · intro hVer
      refine ⟨hBT, by rw [← hAdm]; exact hVer.2.1, ?_⟩
      intro args hArgs hPre
      have hArgsS : ValidEntryArgs bSrc args := by
        unfold ValidEntryArgs; rw [hArg, hLoc]; exact hArgs
      have hPreS : bSrc.isUnsafe = true → safetyPre args := by
        rw [hUns]; exact hPre
      exact (removeStorage_cert_bisim_query { args := args }
        (removeStorage_entryProg defId hRel) hCert).1.mpr
        (hVer.2.2 args hArgsS hPreS)

/-! ## Part IV: Deterministic `evalStep` Adequacy Helpers for Concrete Witnesses -/

/-- Fuel-bounded deterministic `c = 0` outcome evaluator over
`Trusted.MirSemantics.evalStep` into `Prop`. -/
noncomputable def execOutcome (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) : Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
    match evalStep p 0 s with
    | .step s' => execOutcome p onDone onFault fuel s'
    | .done out => onDone out
    | .fault k => onFault k

/-- Whole-program deterministic normal-return verifier from `initState p q`. -/
def execReturns (p : Program) (fuel : Nat) (q : Query) (expected : Val) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ =>
    execOutcome p (fun out => out = .returned ⟨expected, ⟨[]⟩⟩)
      (fun _ => False) fuel s₀

/-- Whole-program deterministic fault verifier from `initState p q`. -/
def execFaults (p : Program) (fuel : Nat) (q : Query)
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

/-- Adequacy for positive canaries: `execReturns p fuel q expected` implies
`Trusted.MirSemantics.PositiveCanaryClaim p q expected`. -/
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
      unfold ReachesResult at hFault
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
    · unfold Behavior ReachesResult
      rw [hInit]
      let ⟨sEnd, res, hR, hStep, hRes⟩ := execOutcome_terminal h
      cases res with
      | step _ => exact False.elim hRes
      | fault _ => exact False.elim hRes
      | done out =>
        subst hRes
        exact ⟨sEnd, hR, hStep⟩

/-- Adequacy for negative fault canaries: `execFaults p fuel q expectedFault`
implies `Trusted.MirSemantics.NegativeCanaryClaim p q expectedFault otherFault`
whenever `otherFault ≠ expectedFault`. -/
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
    · unfold ReachesResult; rw [hInit]
    · intro hOther
      unfold ReachesResult at hOther
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
      unfold ReachesResult
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
      unfold ReachesResult at hOther
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

/-! ## Part V: Proved Stage 1 Non-Vacuity Canaries & Sharpness Counterexamples -/

/-- Helper constant operand for `u32`. -/
noncomputable def constU32 (n : Nat) : Operand :=
  .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- **Witness 1 (Loop + Left-to-Right M4 `copy _1 + move _1` Canary):**
Counted 3-block loop on `Trusted.MirAst.Program` ending with M4 left-to-right
`BinOp.add (.copy ⟨1, []⟩) (.move ⟨1, []⟩)`, rewritten via `MoveToCopy` and
certified by `checkNoUseAfterMoveProgram`. -/
noncomputable def m4LoopSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, .bool]
    identity := "m4_loop"
    basicBlocks := [
      -- bb0: goto bb1 (loop header)
      { statements := [], terminator := .goto 1 },
      -- bb1: _2 = lt(copy _1, const 10u32);
      -- switchInt(move _2) [1 -> bb2, otherwise -> bb3]
      {
        statements := [
          .assign ⟨2, []⟩ (.binaryOp .lt (.copy ⟨1, []⟩) (constU32 10))
        ]
        terminator := .switchInt (.move ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 1, 2)]
          otherwise := 3
        }
      },
      -- bb2 (loop latch): _1 = add(move _1, const 4u32); goto bb1
      {
        statements := [
          .assign ⟨1, []⟩ (.binaryOp .add (.move ⟨1, []⟩) (constU32 4))
        ]
        terminator := .goto 1
      },
      -- bb3 (exit with M4 `copy _1 + move _1`): _0 = add(copy _1, move _1); return
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.move ⟨1, []⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def m4LoopTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, .bool]
    identity := "m4_loop"
    basicBlocks := [
      { statements := [], terminator := .goto 1 },
      {
        statements := [
          .assign ⟨2, []⟩ (.binaryOp .lt (.copy ⟨1, []⟩) (constU32 10))
        ]
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 1, 2)]
          otherwise := 3
        }
      },
      {
        statements := [
          .assign ⟨1, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (constU32 4))
        ]
        terminator := .goto 1
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩))
        ]
        terminator := .return_
      }
    ]
  }]

def m4LoopCert : ProgramAbsCert :=
  [[
    some [.liveUninit, .liveInit, .liveUninit],
    some [.liveUninit, .liveInit, .liveUninit],
    some [.liveUninit, .liveInit, .liveUninit],
    some [.liveUninit, .liveInit, .liveUninit]
  ]]

theorem canary_moveToCopy_loop_and_m4_accepted :
    isMoveToCopyProgram m4LoopSrc m4LoopTgt = true ∧
    checkNoUseAfterMoveProgram m4LoopSrc m4LoopCert = true ∧
    PositiveCanaryClaim m4LoopSrc { args := [u32Val 3] } (u32Val 22) ∧
    PositiveCanaryClaim m4LoopTgt { args := [u32Val 3] } (u32Val 22) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 16) rfl
  · exact positiveCanary_of_execReturns (fuel := 16) rfl

/-- **Witness 2 (`RemoveStorageMarkers` Multi-Block Canary on `progStmtsAndCf`):**
Elides all `StorageLive(2)` and `StorageDead(2)` markers from
`Trusted.MirSemantics.progStmtsAndCf` (`SwitchInt(move _2)`), certified by
`checkStorageSafeProgram`. -/
noncomputable def progStmtsAndCfNoStorage : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    basicBlocks := [
      {
        statements := [
          .nop,
          .nop,
          .nop,
          .nop,
          .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩))
        ]
        terminator := .goto 1
      },
      {
        statements := []
        terminator := .switchInt (.move ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 10, 2)]
          otherwise := 3
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩)),
          .nop
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩)),
          .nop
        ]
        terminator := .return_
      }
    ]
  }]

def progStmtsAndCfStorageCert : ProgramAbsCert :=
  [[
    some [.liveUninit, .liveInit, .dead],
    some [.liveUninit, .liveInit, .liveInit],
    some [.liveUninit, .liveInit, .liveUninit],
    some [.liveUninit, .liveInit, .liveUninit]
  ]]

theorem canary_removeStorageMarkers_scoped_cf_accepted :
    isRemoveStorageMarkersProgram progStmtsAndCf progStmtsAndCfNoStorage = true ∧
    checkStorageSafeProgram progStmtsAndCf progStmtsAndCfStorageCert = true ∧
    PositiveCanaryClaim progStmtsAndCfNoStorage { args := [u32Val 10] } (u32Val 100) ∧
    PositiveCanaryClaim progStmtsAndCfNoStorage { args := [u32Val 99] } (u32Val 200) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 12) rfl
  · exact positiveCanary_of_execReturns (fuel := 12) rfl

/-- **Witness 3 (Sharpness Counterexample: Unconditional Reverse `MoveToCopy`
VC Transport Is False on `Trusted.MirSemantics`):**
`pSrc` executes `_0 = move _1; _0 = copy _1; return`, while `pTgt` rewrites
`move _1 ↦ copy _1`. `pTgt` is `WellFormed` (returns `7u32`), whereas `pSrc`
faults with `.fault .undefined` under `deinitMovedPlace = true`, and
`checkNoUseAfterMoveProgram` unconditionally rejects `pSrc` for **every**
candidate certificate `cert`. -/
noncomputable def ceMoveAfterMoveSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def ceMoveAfterMoveTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

theorem bool_and_false (b : Bool) : (b && false) = false := by
  cases b <;> rfl

theorem ce_vc_transport_moveToCopy_unsound_without_cert :
    isMoveToCopyProgram ceMoveAfterMoveSrc ceMoveAfterMoveTgt = true ∧
    PositiveCanaryClaim ceMoveAfterMoveTgt { args := [u32Val 7] } (u32Val 7) ∧
    NegativeCanaryClaim ceMoveAfterMoveSrc { args := [u32Val 7] }
      .undefined .unsupported ∧
    (∀ cert : ProgramAbsCert,
      checkNoUseAfterMoveProgram ceMoveAfterMoveSrc cert = false) := by
  refine ⟨rfl, positiveCanary_of_execReturns (fuel := 5) rfl,
    negativeCanary_of_execFaults (by intro h; cases h) (fuel := 5) rfl, ?_⟩
  intro cert
  cases cert with
  | nil => rfl
  | cons bCert rest =>
    cases rest with
    | cons _ _ => exact bool_and_false _
    | nil =>
      cases bCert with
      | nil => rfl
      | cons bb0 bbRest =>
        cases bbRest with
        | cons _ _ => rfl
        | nil =>
          cases bb0 with
          | none => rfl
          | some env =>
            cases env with
            | nil => rfl
            | cons s0 env1 =>
              cases env1 with
              | nil => cases s0 <;> rfl
              | cons s1 env2 =>
                cases env2 with
                | cons _ _ => cases s0 <;> cases s1 <;> rfl
                | nil => cases s0 <;> cases s1 <;> rfl

/-- **Witness 4 (Sharpness Counterexample: Unconditional Reverse
`RemoveStorageMarkers` VC Transport Is False on `StorageDead`):**
`pSrc` executes `StorageLive(1); _1 = 42; StorageDead(1); _0 = copy _1; return`.
Eliding storage markers produces a `WellFormed` `pTgt` returning `42u32`, while
`pSrc` faults `.fault .undefined` (`DeadLocal`), and `checkStorageSafeProgram`
rejects **every** certificate `cert`. -/
noncomputable def ceReadAfterDeadSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (constU32 42)),
        .storageDead 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def ceReadAfterDeadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .nop,
        .assign ⟨1, []⟩ (.use (constU32 42)),
        .nop,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

theorem ce_vc_transport_storageDead_unsound_without_cert :
    isRemoveStorageMarkersProgram ceReadAfterDeadSrc ceReadAfterDeadTgt = true ∧
    PositiveCanaryClaim ceReadAfterDeadTgt queryEmpty (u32Val 42) ∧
    NegativeCanaryClaim ceReadAfterDeadSrc queryEmpty .undefined .unsupported ∧
    (∀ cert : ProgramAbsCert,
      checkStorageSafeProgram ceReadAfterDeadSrc cert = false) := by
  refine ⟨rfl, positiveCanary_of_execReturns (fuel := 7) rfl,
    negativeCanary_of_execFaults (by intro h; cases h) (fuel := 7) rfl, ?_⟩
  intro cert
  cases cert with
  | nil => rfl
  | cons bCert rest =>
    cases rest with
    | cons _ _ => exact bool_and_false _
    | nil =>
      cases bCert with
      | nil => rfl
      | cons bb0 bbRest =>
        cases bbRest with
        | cons _ _ => rfl
        | nil =>
          cases bb0 with
          | none => rfl
          | some env =>
            cases env with
            | nil => rfl
            | cons s0 env1 =>
              cases env1 with
              | nil => cases s0 <;> rfl
              | cons s1 env2 =>
                cases env2 with
                | cons _ _ => cases s0 <;> cases s1 <;> rfl
                | nil => cases s0 <;> cases s1 <;> rfl

/-- **Witness 5 (Sharpness Counterexample: `StorageLive` Wipes Prior Value in
`Trusted.MirSemantics`):**
`pSrc` executes `StorageLive(1); _1 = 42; StorageLive(1); _0 = copy _1; return`.
Eliding storage markers leaves `_1 == 42` in `pTgt` (`WellFormed`), whereas
the second `StorageLive(1)` in `pSrc` resets `_1` to `liveUninitSlot u32Ty`
(`.live none`), faulting `.fault .undefined` on `copy _1`. -/
noncomputable def ceStorageLiveWipesSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (constU32 42)),
        .storageLive 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

theorem ce_storageLive_wipes_value_in_TrustedMir :
    isRemoveStorageMarkersProgram ceStorageLiveWipesSrc ceReadAfterDeadTgt = true ∧
    PositiveCanaryClaim ceReadAfterDeadTgt queryEmpty (u32Val 42) ∧
    NegativeCanaryClaim ceStorageLiveWipesSrc queryEmpty .undefined .unsupported ∧
    (∀ cert : ProgramAbsCert,
      checkStorageSafeProgram ceStorageLiveWipesSrc cert = false) := by
  refine ⟨rfl, positiveCanary_of_execReturns (fuel := 7) rfl,
    negativeCanary_of_execFaults (by intro h; cases h) (fuel := 7) rfl, ?_⟩
  intro cert
  cases cert with
  | nil => rfl
  | cons bCert rest =>
    cases rest with
    | cons _ _ => exact bool_and_false _
    | nil =>
      cases bCert with
      | nil => rfl
      | cons bb0 bbRest =>
        cases bbRest with
        | cons _ _ => rfl
        | nil =>
          cases bb0 with
          | none => rfl
          | some env =>
            cases env with
            | nil => rfl
            | cons s0 env1 =>
              cases env1 with
              | nil => cases s0 <;> rfl
              | cons s1 env2 =>
                cases env2 with
                | cons _ _ => cases s0 <;> cases s1 <;> rfl
                | nil => cases s0 <;> cases s1 <;> rfl

/-- **Witness 6 (Sharpness Counterexample: Partial `StorageLive`-Only Elision
Is Unsound for Codegen Because `hasStorageAnnotation` Remains `true`):**
`pSrc` executes `StorageLive(1); _1 = 99; _0 = copy _1; StorageDead(1); return`
(`WellFormed`, returns `99u32`). Rewriting *only* `StorageLive(1) ↦ .nop` while
keeping `StorageDead(1)` leaves `hasStorageAnnotation = true`, so `initLocalsLoop`
initializes `_1` to `.dead` and `_1 = 99` faults `.fault .undefined`! Rejected
by `isRemoveStorageMarkersProgram`. -/
noncomputable def cePartialElideSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (constU32 99)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

noncomputable def cePartialElideBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .nop,
        .assign ⟨1, []⟩ (.use (constU32 99)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

theorem ce_partial_storageLive_only_elision_unsound :
    isRemoveStorageMarkersProgram cePartialElideSrc cePartialElideBadTgt = false ∧
    PositiveCanaryClaim cePartialElideSrc queryEmpty (u32Val 99) ∧
    NegativeCanaryClaim cePartialElideBadTgt queryEmpty .undefined .unsupported := by
  refine ⟨rfl, positiveCanary_of_execReturns (fuel := 7) rfl,
    negativeCanary_of_execFaults (by intro h; cases h) (fuel := 7) rfl⟩

/-- **Witness 7 (Inhabited 0-Byte ZST `.unit` Move-Then-Copy Remains Valid in
`Trusted.MirSemantics` and Accepted by `checkNoUseAfterMoveProgram`):** -/
noncomputable def zstUnitMoveThenCopyProg : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.unit, .unit]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

def zstUnitMoveCert : ProgramAbsCert :=
  [[some [.liveInit, .liveInit]]]

theorem canary_zst_unit_move_then_copy_valid_in_TrustedMir :
    checkNoUseAfterMoveProgram zstUnitMoveThenCopyProg zstUnitMoveCert = true ∧
    PositiveCanaryClaim zstUnitMoveThenCopyProg { args := [.unit] } .unit := by
  exact ⟨rfl, positiveCanary_of_execReturns (fuel := 5) rfl⟩

/-- **Witness 8 (Sharpness Counterexample: Left-to-Right M4 Operand Order
`move _1 + copy _1` Faults `.undefined` and Is Rejected by
`checkNoUseAfterMoveProgram`):** -/
noncomputable def ceM4ReversedSrc : Program where
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

noncomputable def ceM4ReversedTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

theorem ce_m4_reversed_move_then_copy_rejected :
    isMoveToCopyProgram ceM4ReversedSrc ceM4ReversedTgt = true ∧
    PositiveCanaryClaim ceM4ReversedTgt { args := [u32Val 9] } (u32Val 18) ∧
    NegativeCanaryClaim ceM4ReversedSrc { args := [u32Val 9] }
      .undefined .unsupported ∧
    (∀ cert : ProgramAbsCert,
      checkNoUseAfterMoveProgram ceM4ReversedSrc cert = false) := by
  refine ⟨rfl, positiveCanary_of_execReturns (fuel := 4) rfl,
    negativeCanary_of_execFaults (by intro h; cases h) (fuel := 4) rfl, ?_⟩
  intro cert
  cases cert with
  | nil => rfl
  | cons bCert rest =>
    cases rest with
    | cons _ _ => exact bool_and_false _
    | nil =>
      cases bCert with
      | nil => rfl
      | cons bb0 bbRest =>
        cases bbRest with
        | cons _ _ => rfl
        | nil =>
          cases bb0 with
          | none => rfl
          | some env =>
            cases env with
            | nil => rfl
            | cons s0 env1 =>
              cases env1 with
              | nil => cases s0 <;> rfl
              | cons s1 env2 =>
                cases env2 with
                | cons _ _ => cases s0 <;> cases s1 <;> rfl
                | nil => cases s0 <;> cases s1 <;> rfl

/-- **Witness 9 (1-Variant `.zeroSized` Enum `Rvalue.discriminant` Under
`RemoveStorageMarkers`):** Verifies `Trusted.MirSemantics.evalRvalue`
`.discriminant` on an inhabited 0-byte 1-variant enum (`discriminants := [7]`)
across `StorageLive`/`StorageDead` elision. -/
noncomputable def zstEnum1 : EnumTy where
  id := 1
  discrWidth := .i32
  discrSigned := false
  tagRepr := .zeroSized
  discriminants := [7]

noncomputable def zstEnumDiscrSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .enum zstEnum1]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

noncomputable def zstEnumDiscrTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .enum zstEnum1]
    basicBlocks := [{
      statements := [
        .nop,
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .nop
      ]
      terminator := .return_
    }]
  }]

def zstEnumDiscrCert : ProgramAbsCert :=
  [[some [.liveUninit, .dead]]]

theorem canary_zst_enum_discriminant_storage_elision :
    isRemoveStorageMarkersProgram zstEnumDiscrSrc zstEnumDiscrTgt = true ∧
    checkStorageSafeProgram zstEnumDiscrSrc zstEnumDiscrCert = true ∧
    PositiveCanaryClaim zstEnumDiscrSrc queryEmpty (u32Val 7) ∧
    PositiveCanaryClaim zstEnumDiscrTgt queryEmpty (u32Val 7) := by
  refine ⟨rfl, rfl, positiveCanary_of_execReturns (fuel := 6) rfl,
    positiveCanary_of_execReturns (fuel := 6) rfl⟩

end VrustcFormal.F1_1b
