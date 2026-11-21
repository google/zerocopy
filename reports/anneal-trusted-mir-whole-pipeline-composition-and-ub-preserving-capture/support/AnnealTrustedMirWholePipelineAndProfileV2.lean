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

namespace VrustcFormal.F1_9

open Trusted.MirAst Trusted.MirSemantics

/-!
# Whole-Pipeline Multi-Pass `Trusted.MirSemantics` Composition & UB-Preserving `MirProfileV2` (`VrustcFormal.F1_9`)

This module unifies two interlocking formal pillars for verified Rust MIR
compilation and verification-condition (VC) transport directly over Anneal's
unmodified TCB syntax (`Trusted.MirAst`) and small-step operational semantics
(`Trusted.MirSemantics`, grounded in `rust-lang/rust` commits
`8144389c895da997dbdecaa635e41d6a50be6ffd` and
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, plus live empirical censuses `E3-7`,
`E3-10`, `E3-14`, `E3-16`, and `E3-22`):

1. **Half A — Arbitrary-Length Certified Multi-Pass `MirOptTrace` Over
   Unmodified `Trusted.MirAst.Program` & `Trusted.MirSemantics`:**
   - Defines an inductive single-step pass witness `MirOptStep` and arbitrary
     finite pipeline trace `MirOptTrace := List MirOptStep` with executable
     checkers `checkMirOptStep` and `checkMirOptTrace`, composing five distinct
     MIR optimization families:
     1. `.moveToCopyDead` (`Operand.move ⟨l, []⟩` -> `Operand.copy ⟨l, []⟩` under
        co-inductive all-paths post-point deadness, bridging `F1-1b`),
     2. `.simplifyCfgBranch` (redundant `SwitchInt` arm pruning `target ==
        otherwise` and `AbsSlot`-certified uniform-target `SwitchInt` -> `Goto`
        collapse, bridging `F1-5`),
     3. `.instSimplifyAlgAndConst` (certified `x + 0 -> x`, `0 + x -> x`,
        `x - 0 -> x`, `x * 1 -> x`, `1 * x -> x`, `x ^ 0 -> x`, `0 ^ x -> x`
        on `BinOp.bitXor`, adjacent `!!b -> b` on `.bool`, and `ConstAbsSlot`
        constant propagation `.copy ⟨src, []⟩ -> .constant c`, bridging `F1-6`
        and `F1-8`),
     4. `.copyAndDestPropAndDse` (certified intra-block `CopyProp`, adjacent
        `DestinationPropagation` `_tmp = rval; _dst = move/copy _tmp -> _dst =
        rval; .nop`, and totality-certified `DeadStoreElimination`
        `_dead = total_rval -> .nop`, bridging `F1-7`), and
     5. `.compactUnusedTrailingLocals (newCount : Nat)` (`SimplifyLocals`
        compaction of unused trailing non-argument, non-return local slots
        `idx >= newCount` with zero references and zero storage markers,
        mechanizing `E3-7` / `R3`).
   - Establishes single-step soundness (`mirOptStep_sound_bidirectional_iff`),
     arbitrary-length inductive pipeline soundness
     (`mirOptTrace_sound_bidirectional_iff`), and bidirectional whole-crate and
     proof-unit obligation transport (`mirOptTrace_crate_and_unit_vc_transport_iff`)
     directly on `Trusted.MirSemantics.CrateTheorem` and `UnitTheorem`.

2. **Half B — `MirProfileV2` (`StatementKindV2`: `.v1`, `.placeMention`, and
   `.assume`) Mechanizing `E3-22` (`-Zmir-preserve-ub` `RemovePlaceMention`) and
   `E3-16` (`UnreachablePropagation` `Assume` Cliff):**
   - Extends `Trusted.MirAst.StatementKind` conservatively with
     `StatementKindV2.placeMention (p : PlaceV2)` (distinguishing live/dead
     local checks, RFC 2582 zero-offset raw-pointer dereferences `*_raw_ptr`
     that remain defined even on null or misaligned pointers, and non-zero
     `inbounds` field-offset projections `((*_raw_ptr).field)` that fault with
     `FaultKindV2.invalidPointerOffset` on null/dangling pointers per
     `interpret/step.rs:119-122` and `E3-22`) and `StatementKindV2.assume cond`
     (evaluating `.bool true => step` vs. `.bool false => .fault
     .unreachableExecuted` per `NonDivergingIntrinsic::Assume` and `E3-16`).
   - Proves exact conservative extension over `Trusted.MirAst.Program`
     (`profileV2_conservative_extension_exact`), certified bidirectional
     `RemovePlaceMention` equivalence (`removePlaceMention_certified_bidirectional_iff`,
     discharging all `986` `zerocopy` `-Zmir-preserve-ub=yes` `PlaceMention`s
     while rejecting null non-zero field-offset UB erasure), and certified
     bidirectional `UnreachablePropagation` `SwitchInt -> .assume` equivalence
     (`unreachableProp_switchBoolToAssume_bidirectional_iff`, discharging all
     `385` `zerocopy` `assume` rewrites).
-/

/-! ## Part I: Half A — Certified 5-Family `MirOptStep` & `MirOptTrace` Over `Trusted.MirAst.Program` -/

/-- Pairwise boolean relation over two lists of equal length. -/
noncomputable def listRel {α β : Type} (r : α → β → Bool) :
    List α → List β → Bool
  | [], [] => true
  | x :: xs, y :: ys => r x y && listRel r xs ys
  | _, _ => false

/-- Total `Option`-collecting map over a list. -/
noncomputable def mapOption {α β : Type} (f : α → Option β) :
    List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, mapOption f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- Check whether `x` occurs in `ys`. -/
noncomputable def natElem (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => Nat.beq x y || natElem x ys

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

/-! ### Local-Use, Move, Bounds, and Co-Inductive Deadness Helpers -/

/-- Static `MirTy` lookup for unprojected `Place`s and `ConstOperand`s. -/
noncomputable def operandStaticTy? (bodyLocals : List MirTy) :
    Operand → Option MirTy
  | .copy p | .move p =>
    if p.projection.isEmpty then
      Trusted.MirSemantics.getElem? bodyLocals p.localId
    else
      none
  | .constant c => some c.ty

/-- Whether `opnd` mentions `id` via `.copy` or `.move`. -/
noncomputable def operandTouchesLocal (id : LocalId) : Operand → Bool
  | .copy p | .move p => Nat.beq p.localId id
  | .constant _ => false

/-- Whether `opnd` is a `.move` touching `id`. -/
noncomputable def operandMovesLocal (id : LocalId) : Operand → Bool
  | .move p => Nat.beq p.localId id
  | .copy _ | .constant _ => false

/-- Whether `rv` mentions `id` in any operand, discriminant, borrow, or
unsupported construct (conservatively returning `true` on `.unsupported`). -/
noncomputable def rvalueTouchesLocal (id : LocalId) : Rvalue → Bool
  | .use opnd | .unaryOp _ opnd => operandTouchesLocal id opnd
  | .binaryOp _ lhs rhs =>
    operandTouchesLocal id lhs || operandTouchesLocal id rhs
  | .discriminant p | .ref _ p | .addressOf _ p => Nat.beq p.localId id
  | .aggregateTuple fs => fs.any (operandTouchesLocal id)
  | .unsupported => true

/-- Whether `rv` moves or borrows `id` (invalidating any copy alias involving
`id` before evaluating `rv`). -/
noncomputable def rvalueMutatesOrBorrowsLocal (id : LocalId) : Rvalue → Bool
  | .use opnd | .unaryOp _ opnd => operandMovesLocal id opnd
  | .binaryOp _ lhs rhs =>
    operandMovesLocal id lhs || operandMovesLocal id rhs
  | .discriminant _ => false
  | .ref _ p | .addressOf _ p => Nat.beq p.localId id
  | .aggregateTuple fs => fs.any (operandMovesLocal id)
  | .unsupported => true

/-- Check that `opnd` contains no `Operand.move` of any local other than an
unprojected `allowedLocal`. -/
noncomputable def operandNoMoveExcept (allowedLocal : LocalId) : Operand → Bool
  | .copy _ | .constant _ => true
  | .move p => p.projection.isEmpty && Nat.beq p.localId allowedLocal

/-- Check that `rv` contains no `Operand.move` of any local `l ≠ dst`. -/
noncomputable def rvalueNoMoveExcept (dst : LocalId) : Rvalue → Bool
  | .use opnd | .unaryOp _ opnd => operandNoMoveExcept dst opnd
  | .binaryOp _ lhs rhs =>
    operandNoMoveExcept dst lhs && operandNoMoveExcept dst rhs
  | .discriminant _ | .ref _ _ | .addressOf _ _ | .unsupported => true
  | .aggregateTuple fs => fs.all (operandNoMoveExcept dst)

/-- Per-body dead-on-entry local sets (`deadAtEntry[bbIdx]` lists locals `d ≠ 0`
certified dead at entry to basic block `bbIdx`). -/
abbrev BodyDeadCert := List (List LocalId)

/-- Per-program dead-on-entry certificate. -/
abbrev ProgramDeadCert := List BodyDeadCert

/-- Check whether `d` is certified dead on entry to in-bounds block `target`. -/
noncomputable def isDeadAtTarget (deadAtEntry : BodyDeadCert)
    (numBlocks : Nat) (d : LocalId) (target : BasicBlockId) : Bool :=
  Nat.blt target numBlocks &&
    match Trusted.MirSemantics.getElem? deadAtEntry target with
    | some ds => natElem d ds
    | none => false

/-- Check whether local `d` (`d ≠ 0` checked by callers) is never read or
touched along any CFG path starting at `(stmts, term)` before an unprojected
assignment `⟨d, []⟩ = ...` (with `d < numLocals`), `StorageLive(d)` (`d <
numLocals`), `StorageDead(d)` (`d < numLocals`), or `.return_` / `.unreachable`. -/
noncomputable def isDeadAcrossCfg (numLocals : Nat)
    (deadAtEntry : BodyDeadCert) (numBlocks : Nat) (d : LocalId) :
    List StatementKind → TerminatorKind → Bool
  | [], .return_ => true
  | [], .unreachable => true
  | [], .goto target => isDeadAtTarget deadAtEntry numBlocks d target
  | [], .switchInt discr targets =>
    !operandTouchesLocal d discr &&
      isDeadAtTarget deadAtEntry numBlocks d targets.otherwise &&
      targets.branches.all (fun br =>
        isDeadAtTarget deadAtEntry numBlocks d br.2)
  | [], _ => false
  | .nop :: rest, term =>
    isDeadAcrossCfg numLocals deadAtEntry numBlocks d rest term
  | .storageLive id :: rest, term =>
    if Nat.beq id d && Nat.blt id numLocals then true
    else isDeadAcrossCfg numLocals deadAtEntry numBlocks d rest term
  | .storageDead id :: rest, term =>
    if Nat.beq id d && Nat.blt id numLocals then true
    else isDeadAcrossCfg numLocals deadAtEntry numBlocks d rest term
  | .assign lhs rv :: rest, term =>
    lhs.projection.isEmpty &&
      Nat.blt lhs.localId numLocals &&
      !rvalueTouchesLocal d rv &&
      if Nat.beq lhs.localId d then
        true
      else
        isDeadAcrossCfg numLocals deadAtEntry numBlocks d rest term
  | .unsupported :: _, _ => false

noncomputable def checkDeadAtEntryLoop (body : Body)
    (deadAtEntry : BodyDeadCert) : Nat → BodyDeadCert → Bool
  | _, [] => true
  | bbIdx, ds :: rest =>
    (match Trusted.MirSemantics.getElem? body.basicBlocks bbIdx with
     | none => false
     | some bb =>
       ds.all (fun d =>
         !Nat.beq d 0 &&
           Nat.blt d body.locals.length &&
           isDeadAcrossCfg body.locals.length deadAtEntry
             body.basicBlocks.length d bb.statements bb.terminator)) &&
      checkDeadAtEntryLoop body deadAtEntry (bbIdx + 1) rest

noncomputable def checkBodyDeadCert (body : Body)
    (deadAtEntry : BodyDeadCert) : Bool :=
  Nat.beq deadAtEntry.length body.basicBlocks.length &&
    checkDeadAtEntryLoop body deadAtEntry 0 deadAtEntry

/-! ### Shared Abstract Domains (`AbsSlot`, `ConstAbsSlot`, `NonZeroAbsSlot`) -/

/-- Whether `ty` is an inhabited 0-byte ZST whose `liveUninitSlot` is already
initialized (`MirTy.unit` or an admitted 1-variant `.zeroSized` enum). -/
noncomputable def isAlwaysInhabitedZst (ty : MirTy) : Bool :=
  match ty with
  | .unit => true
  | .enum ety => isZstEnumTy ety
  | _ => false

/-- 3-point abstract local domain (`liveInit ⊑ liveUninit ⊑ dead`). -/
inductive AbsSlot where
  | liveInit
  | liveUninit
  | dead

noncomputable def absSlotImplies : AbsSlot → AbsSlot → Bool
  | _, .dead => true
  | .liveInit, .liveUninit | .liveUninit, .liveUninit => true
  | .liveInit, .liveInit => true
  | _, _ => false

noncomputable def absEnvImplies : List AbsSlot → List AbsSlot → Bool :=
  listRel absSlotImplies

abbrev BodyAbsCert := List (Option (List AbsSlot))
abbrev ProgramAbsCert := List BodyAbsCert

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

noncomputable def initAbsEnvLoop (body : Body) :
    Nat → List MirTy → List AbsSlot
  | _, [] => []
  | idx, ty :: rest =>
    initAbsSlot body idx ty :: initAbsEnvLoop body (idx + 1) rest

noncomputable def deinitMoveOperandAbs (bodyLocals : List MirTy)
    (env : List AbsSlot) : Operand → List AbsSlot
  | .move p =>
    if !p.projection.isEmpty then env
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => env
      | some ty =>
        let nextSlot := if isAlwaysInhabitedZst ty then .liveInit else .liveUninit
        match setElem? env p.localId nextSlot with
        | some env' => env'
        | none => env
  | _ => env

noncomputable def deinitMovesInRvalueAbs (bodyLocals : List MirTy)
    (env : List AbsSlot) : Rvalue → List AbsSlot
  | .use opnd | .unaryOp _ opnd => deinitMoveOperandAbs bodyLocals env opnd
  | .binaryOp _ lhs rhs =>
    let env₁ := deinitMoveOperandAbs bodyLocals env lhs
    deinitMoveOperandAbs bodyLocals env₁ rhs
  | _ => env

noncomputable def stepPlainStmtAbs (bodyLocals : List MirTy)
    (env : List AbsSlot) : StatementKind → Option (List AbsSlot)
  | .nop | .unsupported => some env
  | .storageLive id =>
    match Trusted.MirSemantics.getElem? bodyLocals id with
    | none => none
    | some ty =>
      let nextSlot := if isAlwaysInhabitedZst ty then .liveInit else .liveUninit
      setElem? env id nextSlot
  | .storageDead id =>
    if Nat.beq id 0 then none else setElem? env id .dead
  | .assign dst rv =>
    if !dst.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => none
      | some _ =>
        let env₁ := deinitMovesInRvalueAbs bodyLocals env rv
        setElem? env₁ dst.localId .liveInit

noncomputable def stepPlainStmtsAbs (bodyLocals : List MirTy) :
    List AbsSlot → List StatementKind → Option (List AbsSlot)
  | env, [] => some env
  | env, s :: ss =>
    match stepPlainStmtAbs bodyLocals env s with
    | none => none
    | some env' => stepPlainStmtsAbs bodyLocals env' ss

noncomputable def checkAbsEdge (numBlocks : Nat) (cert : BodyAbsCert)
    (exitEnv : List AbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? cert target with
    | some (some tgtEnv) => absEnvImplies exitEnv tgtEnv
    | _ => false

noncomputable def checkAbsTerminatorEdges (bodyLocals : List MirTy)
    (numBlocks : Nat) (cert : BodyAbsCert) (exitEnv : List AbsSlot) :
    TerminatorKind → Bool
  | .goto target => checkAbsEdge numBlocks cert exitEnv target
  | .switchInt discr targets =>
    let afterDiscrEnv := deinitMoveOperandAbs bodyLocals exitEnv discr
    checkAbsEdge numBlocks cert afterDiscrEnv targets.otherwise &&
      targets.branches.all (fun br =>
        checkAbsEdge numBlocks cert afterDiscrEnv br.2)
  | _ => true

/-- 5-point constant & liveness lattice (`bottom ⊑ knownConst ty lit ⊑
liveUnknown ⊑ liveUninit ⊑ dead`). -/
inductive ConstAbsSlot where
  | bottom
  | knownConst (ty : MirTy) (lit : ConstLit)
  | liveUnknown
  | liveUninit
  | dead

noncomputable def constSlotImplies : ConstAbsSlot → ConstAbsSlot → Bool
  | .bottom, _ => true
  | _, .dead => true
  | .knownConst _ _, .liveUninit
  | .liveUnknown, .liveUninit
  | .liveUninit, .liveUninit => true
  | .knownConst _ _, .liveUnknown
  | .liveUnknown, .liveUnknown => true
  | .knownConst ty₁ lit₁, .knownConst ty₂ lit₂ =>
    MirTy.beq ty₁ ty₂ && constLitEq lit₁ lit₂
  | _, _ => false

noncomputable def constEnvImplies :
    List ConstAbsSlot → List ConstAbsSlot → Bool :=
  listRel constSlotImplies

abbrev BodyConstCert := List (Option (List ConstAbsSlot))
abbrev ProgramConstCert := List BodyConstCert

noncomputable def liveUninitConstSlot (ty : MirTy) : ConstAbsSlot :=
  if isAlwaysInhabitedZst ty then .liveUnknown else .liveUninit

noncomputable def initConstSlot (body : Body) (idx : Nat)
    (ty : MirTy) : ConstAbsSlot :=
  if Nat.beq idx 0 then
    liveUninitConstSlot ty
  else if Nat.ble idx body.argumentCount then
    .liveUnknown
  else if hasStorageAnnotation body idx then
    .dead
  else
    liveUninitConstSlot ty

noncomputable def initConstEnvLoop (body : Body) :
    Nat → List MirTy → List ConstAbsSlot
  | _, [] => []
  | idx, ty :: rest =>
    initConstSlot body idx ty :: initConstEnvLoop body (idx + 1) rest

noncomputable def validTypedConstOperand (ty : MirTy)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty ty &&
    isSupportedScalarOrUnitTy ty &&
    match evalConstLit ty c.lit with
    | .ok v => checkVal v ty
    | .error _ => false

noncomputable def evalOperandConst? (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : Operand → Option (MirTy × ConstLit)
  | .constant c =>
    if validTypedConstOperand c.ty c then some (c.ty, c.lit) else none
  | .copy p | .move p =>
    if !p.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some (.knownConst cTy cLit) =>
        if validTypedConstOperand ty ⟨cTy, cLit⟩ then
          some (ty, cLit)
        else
          none
      | _, _ => none

noncomputable def deinitMoveOperandConst (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : Operand → List ConstAbsSlot
  | .move p =>
    if !p.projection.isEmpty then env
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => env
      | some ty =>
        match setElem? env p.localId (liveUninitConstSlot ty) with
        | some env' => env'
        | none => env
  | _ => env

noncomputable def deinitMovesInRvalueConst (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : Rvalue → List ConstAbsSlot
  | .use opnd | .unaryOp _ opnd => deinitMoveOperandConst bodyLocals env opnd
  | .binaryOp _ lhs rhs =>
    let env₁ := deinitMoveOperandConst bodyLocals env lhs
    deinitMoveOperandConst bodyLocals env₁ rhs
  | _ => env

noncomputable def rvalueConstSlot (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (dstTy : MirTy) : Rvalue → ConstAbsSlot
  | .use opnd =>
    match evalOperandConst? bodyLocals env opnd with
    | some (opTy, lit) =>
      if MirTy.beq opTy dstTy then .knownConst dstTy lit else .liveUnknown
    | none => .liveUnknown
  | _ => .liveUnknown

noncomputable def stepPlainStmtConst (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : StatementKind → Option (List ConstAbsSlot)
  | .nop | .unsupported => some env
  | .storageLive id =>
    match Trusted.MirSemantics.getElem? bodyLocals id with
    | none => none
    | some ty => setElem? env id (liveUninitConstSlot ty)
  | .storageDead id =>
    if Nat.beq id 0 then none else setElem? env id .dead
  | .assign dst rv =>
    if !dst.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => none
      | some dstTy =>
        let dstSlot := rvalueConstSlot bodyLocals env dstTy rv
        let env₁ := deinitMovesInRvalueConst bodyLocals env rv
        setElem? env₁ dst.localId dstSlot

noncomputable def refineSwitchBranchEnv (bodyLocals : List MirTy)
    (afterDiscrEnv : List ConstAbsSlot) (discr : Operand)
    (caseBits : BitVec 128) : List ConstAbsSlot :=
  match discr with
  | .copy p =>
    if !p.projection.isEmpty then afterDiscrEnv
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? afterDiscrEnv p.localId with
      | some ty, some curSlot =>
        if isPrimitiveReadableTy ty &&
            constSlotImplies curSlot .liveUnknown &&
            validTypedConstOperand ty ⟨ty, .scalar caseBits⟩ then
          match setElem? afterDiscrEnv p.localId
              (.knownConst ty (.scalar caseBits)) with
          | some refined => refined
          | none => afterDiscrEnv
        else
          afterDiscrEnv
      | _, _ => afterDiscrEnv
  | _ => afterDiscrEnv

noncomputable def checkConstEdge (numBlocks : Nat) (cert : BodyConstCert)
    (edgeEnv : List ConstAbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? cert target with
    | some (some tgtEnv) => constEnvImplies edgeEnv tgtEnv
    | _ => false

noncomputable def checkConstTerminatorEdges (bodyLocals : List MirTy)
    (numBlocks : Nat) (cert : BodyConstCert) (exitEnv : List ConstAbsSlot) :
    TerminatorKind → Bool
  | .goto target => checkConstEdge numBlocks cert exitEnv target
  | .switchInt discr targets =>
    let afterDiscrEnv := deinitMoveOperandConst bodyLocals exitEnv discr
    checkConstEdge numBlocks cert afterDiscrEnv targets.otherwise &&
      targets.branches.all (fun br =>
        let armEnv := refineSwitchBranchEnv bodyLocals afterDiscrEnv discr br.1
        checkConstEdge numBlocks cert armEnv br.2)
  | _ => true

/-! ### Pass Family 1: `.moveToCopyDead` (`F1-1b`) -/

noncomputable def rewriteMoveToCopyDeadRvalue (canKillAfter : LocalId → Bool) :
    Rvalue → Rvalue
  | .use (.move p) =>
    if p.projection.isEmpty && canKillAfter p.localId then
      .use (.copy p)
    else
      .use (.move p)
  | .unaryOp uop (.move p) =>
    if p.projection.isEmpty && canKillAfter p.localId then
      .unaryOp uop (.copy p)
    else
      .unaryOp uop (.move p)
  | .binaryOp bop lhs rhs =>
    let lhs' :=
      match lhs with
      | .move p =>
        if p.projection.isEmpty &&
            !operandTouchesLocal p.localId rhs &&
            canKillAfter p.localId then
          .copy p
        else
          lhs
      | _ => lhs
    let rhs' :=
      match rhs with
      | .move p =>
        if p.projection.isEmpty && canKillAfter p.localId then
          .copy p
        else
          rhs
      | _ => rhs
    .binaryOp bop lhs' rhs'
  | rv => rv

noncomputable def rewriteMoveToCopyDeadStmts (numLocals : Nat)
    (deadAtEntry : BodyDeadCert) (numBlocks : Nat) (term : TerminatorKind) :
    List StatementKind → List StatementKind
  | [] => []
  | s :: rest =>
    let rest' :=
      rewriteMoveToCopyDeadStmts numLocals deadAtEntry numBlocks term rest
    let s' :=
      match s with
      | .assign dst rv =>
        if dst.projection.isEmpty && Nat.blt dst.localId numLocals then
          let canKill := fun l =>
            !Nat.beq l 0 &&
              (Nat.beq dst.localId l ||
                isDeadAcrossCfg numLocals deadAtEntry numBlocks l rest term)
          .assign dst (rewriteMoveToCopyDeadRvalue canKill rv)
        else
          s
      | _ => s
    s' :: rest'

noncomputable def rewriteMoveToCopyDeadTerm (deadAtEntry : BodyDeadCert)
    (numBlocks : Nat) : TerminatorKind → TerminatorKind
  | .switchInt (.move p) targets =>
    if p.projection.isEmpty &&
        !Nat.beq p.localId 0 &&
        isDeadAtTarget deadAtEntry numBlocks p.localId targets.otherwise &&
        targets.branches.all (fun br =>
          isDeadAtTarget deadAtEntry numBlocks p.localId br.2) then
      .switchInt (.copy p) targets
    else
      .switchInt (.move p) targets
  | term => term

noncomputable def applyMoveToCopyDeadBody (deadAtEntry : BodyDeadCert)
    (b : Body) : Option Body :=
  if !checkBodyDeadCert b deadAtEntry then
    none
  else
    let numLocals := b.locals.length
    let numBlocks := b.basicBlocks.length
    let bbs' := b.basicBlocks.map (fun bb => {
      statements := rewriteMoveToCopyDeadStmts numLocals deadAtEntry
        numBlocks bb.terminator bb.statements
      terminator := rewriteMoveToCopyDeadTerm deadAtEntry numBlocks
        bb.terminator
      cleanup := bb.cleanup
    })
    some { b with basicBlocks := bbs' }

noncomputable def applyMoveToCopyDeadProgram (cert : ProgramDeadCert)
    (p : Program) : Option Program :=
  if !Nat.beq cert.length p.bodies.length then
    none
  else
    match mapOption (fun pr => applyMoveToCopyDeadBody pr.1 pr.2)
        (List.zip cert p.bodies) with
    | some bodies' => some { p with bodies := bodies' }
    | none => none

/-! ### Pass Family 2: `.simplifyCfgBranch` (`F1-5`) -/

noncomputable def validSwitchBranchesForTy (ty : MirTy)
    (branches : List (BitVec 128 × BasicBlockId)) : Bool :=
  match ty with
  | .int w _ => branches.all (fun br => truncateBits w br.1 == br.1)
  | .bool =>
    branches.all (fun br =>
      match evalConstLit .bool (.scalar br.1) with
      | .ok (.bool _) => true
      | _ => false)
  | _ => false

noncomputable def resolveConstSwitchTarget (c : ConstOperand)
    (targets : SwitchTargets) : Option BasicBlockId :=
  if !isPrimitiveReadableTy c.ty then
    none
  else
    match evalConstLit c.ty c.lit with
    | .error _ => none
    | .ok (.scalar sv) =>
      match evalSwitchBranches sv.width sv.bits targets.otherwise
          targets.branches with
      | .ok target => some target
      | .error _ => none
    | .ok (.bool b) =>
      match evalBoolSwitchBranches b targets.otherwise targets.branches with
      | .ok target => some target
      | .error _ => none
    | .ok _ => none

noncomputable def allSwitchTargetsEq (targets : SwitchTargets)
    (target : BasicBlockId) : Bool :=
  Nat.beq targets.otherwise target &&
    targets.branches.all (fun br => Nat.beq br.2 target)

noncomputable def hasCaseBitsIn (c : BitVec 128) :
    List (BitVec 128 × BasicBlockId) → Bool
  | [] => false
  | (c', _) :: rest => (c == c') || hasCaseBitsIn c rest

noncomputable def pruneOtherwiseBranches (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → List (BitVec 128 × BasicBlockId)
  | [] => []
  | (c, tgt) :: rest =>
    let rest' := pruneOtherwiseBranches otherwise rest
    if Nat.beq tgt otherwise && !hasCaseBitsIn c rest then
      rest'
    else
      (c, tgt) :: rest'

noncomputable def canCollapseUniformSwitch (bodyLocals : List MirTy)
    (exitEnv : List AbsSlot) (discr : Operand) (targets : SwitchTargets) :
    Bool :=
  match discr with
  | .constant c =>
    match resolveConstSwitchTarget c targets with
    | some _ => true
    | none => false
  | .copy p =>
    p.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? exitEnv p.localId with
      | some ty, some .liveInit =>
        isPrimitiveReadableTy ty &&
          validSwitchBranchesForTy ty targets.branches
      | _, _ => false
  | .move _ => false

noncomputable def simplifySwitchTerminator (bodyLocals : List MirTy)
    (exitEnv : List AbsSlot) : TerminatorKind → TerminatorKind
  | .switchInt discr targets =>
    let targets' : SwitchTargets :=
      match operandStaticTy? bodyLocals discr with
      | some ty =>
        if isPrimitiveReadableTy ty &&
            validSwitchBranchesForTy ty targets.branches then
          {
            branches := pruneOtherwiseBranches targets.otherwise targets.branches
            otherwise := targets.otherwise
          }
        else
          targets
      | none => targets
    if allSwitchTargetsEq targets' targets'.otherwise &&
        canCollapseUniformSwitch bodyLocals exitEnv discr targets' then
      .goto targets'.otherwise
    else
      .switchInt discr targets'
  | term => term

noncomputable def applySimplifyCfgBranchBlocks (b : Body) (cert : BodyAbsCert) :
    Nat → List BasicBlock → Option (List BasicBlock)
  | _, [] => some []
  | bbIdx, bb :: rest =>
    match Trusted.MirSemantics.getElem? cert bbIdx with
    | none => none
    | some none =>
      match applySimplifyCfgBranchBlocks b cert (bbIdx + 1) rest with
      | some rest' => some (bb :: rest')
      | none => none
    | some (some entryEnv) =>
      if !Nat.beq entryEnv.length b.locals.length then
        none
      else
        match stepPlainStmtsAbs b.locals entryEnv bb.statements with
        | none => none
        | some exitEnv =>
          if !checkAbsTerminatorEdges b.locals b.basicBlocks.length cert
              exitEnv bb.terminator then
            none
          else
            let bb' : BasicBlock := {
              bb with
              terminator := simplifySwitchTerminator b.locals exitEnv
                bb.terminator
            }
            match applySimplifyCfgBranchBlocks b cert (bbIdx + 1) rest with
            | some rest' => some (bb' :: rest')
            | none => none

noncomputable def applySimplifyCfgBranchBody (cert : BodyAbsCert)
    (b : Body) : Option Body :=
  if !Nat.beq cert.length b.basicBlocks.length then
    none
  else if !b.basicBlocks.isEmpty &&
      !(match Trusted.MirSemantics.getElem? cert 0 with
        | some (some env₀) =>
          absEnvImplies (initAbsEnvLoop b 0 b.locals) env₀
        | _ => false) then
    none
  else
    match applySimplifyCfgBranchBlocks b cert 0 b.basicBlocks with
    | some bbs' => some { b with basicBlocks := bbs' }
    | none => none

noncomputable def applySimplifyCfgBranchProgram (cert : ProgramAbsCert)
    (p : Program) : Option Program :=
  if !Nat.beq cert.length p.bodies.length then
    none
  else
    match mapOption (fun pr => applySimplifyCfgBranchBody pr.1 pr.2)
        (List.zip cert p.bodies) with
    | some bodies' => some { p with bodies := bodies' }
    | none => none

/-! ### Pass Family 3: `.instSimplifyAlgAndConst` (`F1-6` + `F1-8`) -/

noncomputable def isFalseBoolConst (c : ConstOperand) : Bool :=
  MirTy.beq c.ty .bool && constLitEq c.lit (.scalar (BitVec.ofNat 128 0))

noncomputable def isIntZeroConst (w : IntWidth) (s : Bool)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty (.int w s) && constLitEq c.lit (.scalar (BitVec.ofNat 128 0))

noncomputable def isIntOneConst (w : IntWidth) (s : Bool)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty (.int w s) && constLitEq c.lit (.scalar (BitVec.ofNat 128 1))

noncomputable def isAlgLeftNeutral (dstTy : MirTy) (op : BinOp)
    (c : ConstOperand) : Bool :=
  match dstTy with
  | .int w s =>
    match op with
    | .add | .addUnchecked | .bitXor => isIntZeroConst w s c
    | .mul | .mulUnchecked => isIntOneConst w s c
    | _ => false
  | .bool =>
    match op with
    | .bitXor => isFalseBoolConst c
    | _ => false
  | _ => false

noncomputable def isAlgRightNeutral (dstTy : MirTy) (op : BinOp)
    (c : ConstOperand) : Bool :=
  match dstTy with
  | .int w s =>
    match op with
    | .add | .addUnchecked | .sub | .subUnchecked | .bitXor =>
      isIntZeroConst w s c
    | .mul | .mulUnchecked => isIntOneConst w s c
    | _ => false
  | .bool =>
    match op with
    | .bitXor => isFalseBoolConst c
    | _ => false
  | _ => false

noncomputable def constPropOperand (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : Operand → Operand
  | .copy p =>
    if !p.projection.isEmpty then .copy p
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some (.knownConst cTy cLit) =>
        if validTypedConstOperand ty ⟨cTy, cLit⟩ then
          .constant ⟨ty, cLit⟩
        else
          .copy p
      | _, _ => .copy p
  | opnd => opnd

noncomputable def constPropRvalue (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : Rvalue → Rvalue
  | .use o => .use (constPropOperand bodyLocals env o)
  | .unaryOp uop o => .unaryOp uop (constPropOperand bodyLocals env o)
  | .binaryOp bop lhs rhs =>
    let lhs' := constPropOperand bodyLocals env lhs
    let env₁ := deinitMoveOperandConst bodyLocals env lhs
    let rhs' := constPropOperand bodyLocals env₁ rhs
    .binaryOp bop lhs' rhs'
  | rv => rv

noncomputable def foldAlgNeutralRvalue (bodyLocals : List MirTy)
    (dstTy : MirTy) : Rvalue → Rvalue
  | .binaryOp op lhs rhs =>
    match lhs, operandStaticTy? bodyLocals rhs with
    | .constant c, some rhsTy =>
      if MirTy.beq rhsTy dstTy && isAlgLeftNeutral dstTy op c then
        .use rhs
      else
        match rhs, operandStaticTy? bodyLocals lhs with
        | .constant cR, some lhsTy =>
          if MirTy.beq lhsTy dstTy && isAlgRightNeutral dstTy op cR then
            .use lhs
          else
            .binaryOp op lhs rhs
        | _, _ => .binaryOp op lhs rhs
    | _, _ =>
      match rhs, operandStaticTy? bodyLocals lhs with
      | .constant cR, some lhsTy =>
        if MirTy.beq lhsTy dstTy && isAlgRightNeutral dstTy op cR then
          .use lhs
        else
          .binaryOp op lhs rhs
      | _, _ => .binaryOp op lhs rhs
  | rv => rv

/-- Match adjacent boolean double-negation
`_tmp = UnaryOp(.not, copy _b); _dst = UnaryOp(.not, copy _tmp)` with
`_tmp ≠ _b` and all three locals of static type `.bool`, returning
`some (_dst = Use(copy _b))`. -/
noncomputable def matchBoolDoubleNotSecond? (bodyLocals : List MirTy) :
    StatementKind → StatementKind → Option StatementKind
  | .assign tmp (.unaryOp .not (.copy bPlace)),
      .assign dst (.unaryOp .not (.copy tmp')) =>
    if bPlace.projection.isEmpty &&
        tmp.projection.isEmpty &&
        tmp'.projection.isEmpty &&
        dst.projection.isEmpty &&
        Nat.beq tmp.localId tmp'.localId &&
        !Nat.beq tmp.localId bPlace.localId then
      match Trusted.MirSemantics.getElem? bodyLocals bPlace.localId,
          Trusted.MirSemantics.getElem? bodyLocals tmp.localId,
          Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | some .bool, some .bool, some .bool =>
        some (.assign dst (.use (.copy bPlace)))
      | _, _, _ => none
    else
      none
  | _, _ => none

noncomputable def rewriteInstSimplifySingleStmt (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (s : StatementKind) : StatementKind :=
  match s with
  | .assign dst rv =>
    if !dst.projection.isEmpty then s
    else
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => s
      | some dstTy =>
        let rv₁ := constPropRvalue bodyLocals env rv
        let rv₂ := foldAlgNeutralRvalue bodyLocals dstTy rv₁
        .assign dst rv₂
  | _ => s

noncomputable def rewriteInstSimplifyStmts (bodyLocals : List MirTy) :
    List ConstAbsSlot → List StatementKind →
    Option (List StatementKind × List ConstAbsSlot)
  | env, [] => some ([], env)
  | env, s₁ :: s₂ :: rest =>
    match matchBoolDoubleNotSecond? bodyLocals s₁ s₂ with
    | some t₂ =>
      let t₁ := rewriteInstSimplifySingleStmt bodyLocals env s₁
      match stepPlainStmtConst bodyLocals env s₁ with
      | none => none
      | some env₁ =>
        match stepPlainStmtConst bodyLocals env₁ s₂ with
        | none => none
        | some env₂ =>
          match rewriteInstSimplifyStmts bodyLocals env₂ rest with
          | some (rest', exitEnv) => some (t₁ :: t₂ :: rest', exitEnv)
          | none => none
    | none =>
      let t₁ := rewriteInstSimplifySingleStmt bodyLocals env s₁
      match stepPlainStmtConst bodyLocals env s₁ with
      | none => none
      | some env₁ =>
        match rewriteInstSimplifyStmts bodyLocals env₁ (s₂ :: rest) with
        | some (rest', exitEnv) => some (t₁ :: rest', exitEnv)
        | none => none
  | env, [s₁] =>
    let t₁ := rewriteInstSimplifySingleStmt bodyLocals env s₁
    match stepPlainStmtConst bodyLocals env s₁ with
    | some exitEnv => some ([t₁], exitEnv)
    | none => none

noncomputable def rewriteInstSimplifyTerm (bodyLocals : List MirTy)
    (exitEnv : List ConstAbsSlot) : TerminatorKind → TerminatorKind
  | .switchInt discr targets =>
    .switchInt (constPropOperand bodyLocals exitEnv discr) targets
  | term => term

noncomputable def applyInstSimplifyBlocks (b : Body) (cert : BodyConstCert) :
    Nat → List BasicBlock → Option (List BasicBlock)
  | _, [] => some []
  | bbIdx, bb :: rest =>
    match Trusted.MirSemantics.getElem? cert bbIdx with
    | none => none
    | some none =>
      match applyInstSimplifyBlocks b cert (bbIdx + 1) rest with
      | some rest' => some (bb :: rest')
      | none => none
    | some (some entryEnv) =>
      if !Nat.beq entryEnv.length b.locals.length then
        none
      else
        match rewriteInstSimplifyStmts b.locals entryEnv bb.statements with
        | none => none
        | some (stmts', exitEnv) =>
          if !checkConstTerminatorEdges b.locals b.basicBlocks.length cert
              exitEnv bb.terminator then
            none
          else
            let bb' : BasicBlock := {
              statements := stmts'
              terminator := rewriteInstSimplifyTerm b.locals exitEnv
                bb.terminator
              cleanup := bb.cleanup
            }
            match applyInstSimplifyBlocks b cert (bbIdx + 1) rest with
            | some rest' => some (bb' :: rest')
            | none => none

noncomputable def applyInstSimplifyAlgAndConstBody (cert : BodyConstCert)
    (b : Body) : Option Body :=
  if !Nat.beq cert.length b.basicBlocks.length then
    none
  else if !b.basicBlocks.isEmpty &&
      !(match Trusted.MirSemantics.getElem? cert 0 with
        | some (some env₀) =>
          constEnvImplies (initConstEnvLoop b 0 b.locals) env₀
        | _ => false) then
    none
  else
    match applyInstSimplifyBlocks b cert 0 b.basicBlocks with
    | some bbs' => some { b with basicBlocks := bbs' }
    | none => none

noncomputable def applyInstSimplifyAlgAndConstProgram (cert : ProgramConstCert)
    (p : Program) : Option Program :=
  if !Nat.beq cert.length p.bodies.length then
    none
  else
    match mapOption (fun pr => applyInstSimplifyAlgAndConstBody pr.1 pr.2)
        (List.zip cert p.bodies) with
    | some bodies' => some { p with bodies := bodies' }
    | none => none

/-! ### Pass Family 4: `.copyAndDestPropAndDse` (`F1-7`) -/

abbrev CopyAliases := List (LocalId × LocalId)

noncomputable def lookupCopyAlias (d : LocalId) : CopyAliases → Option LocalId
  | [] => none
  | (dst, src) :: rest =>
    if Nat.beq d dst then some src else lookupCopyAlias d rest

noncomputable def killCopyAliasesTouching (id : LocalId) :
    CopyAliases → CopyAliases
  | [] => []
  | (dst, src) :: rest =>
    if Nat.beq dst id || Nat.beq src id then
      killCopyAliasesTouching id rest
    else
      (dst, src) :: killCopyAliasesTouching id rest

noncomputable def filterAliasesForRvalue (rv : Rvalue) :
    CopyAliases → CopyAliases
  | [] => []
  | (dst, src) :: rest =>
    if rvalueMutatesOrBorrowsLocal dst rv ||
        rvalueMutatesOrBorrowsLocal src rv then
      filterAliasesForRvalue rv rest
    else
      (dst, src) :: filterAliasesForRvalue rv rest

noncomputable def rewriteCopyPropOperand (aliases : CopyAliases) :
    Operand → Operand
  | .copy p =>
    if !p.projection.isEmpty then .copy p
    else
      match lookupCopyAlias p.localId aliases with
      | some src => .copy ⟨src, []⟩
      | none => .copy p
  | opnd => opnd

noncomputable def rewriteCopyPropRvalue (aliases : CopyAliases)
    (rv : Rvalue) : Rvalue :=
  let safe := filterAliasesForRvalue rv aliases
  match rv with
  | .use o => .use (rewriteCopyPropOperand safe o)
  | .unaryOp uop o => .unaryOp uop (rewriteCopyPropOperand safe o)
  | .binaryOp bop l r =>
    .binaryOp bop (rewriteCopyPropOperand safe l)
      (rewriteCopyPropOperand safe r)
  | .discriminant p =>
    if p.projection.isEmpty then
      match lookupCopyAlias p.localId safe with
      | some src => .discriminant ⟨src, []⟩
      | none => .discriminant p
    else
      .discriminant p
  | _ => rv

noncomputable def rewriteCopyPropStmts (bodyLocals : List MirTy) :
    CopyAliases → List AbsSlot → List StatementKind →
    Option (List StatementKind × CopyAliases × List AbsSlot)
  | aliases, env, [] => some ([], aliases, env)
  | aliases, env, sSrc :: rest =>
    match sSrc with
    | .nop =>
      match rewriteCopyPropStmts bodyLocals aliases env rest with
      | some (rest', exitAliases, exitEnv) =>
        some (.nop :: rest', exitAliases, exitEnv)
      | none => none
    | .unsupported =>
      match rewriteCopyPropStmts bodyLocals [] env rest with
      | some (rest', exitAliases, exitEnv) =>
        some (.unsupported :: rest', exitAliases, exitEnv)
      | none => none
    | .storageLive id =>
      match stepPlainStmtAbs bodyLocals env sSrc with
      | none => none
      | some env' =>
        let aliases' := killCopyAliasesTouching id aliases
        match rewriteCopyPropStmts bodyLocals aliases' env' rest with
        | some (rest', exitAliases, exitEnv) =>
          some (.storageLive id :: rest', exitAliases, exitEnv)
        | none => none
    | .storageDead id =>
      match stepPlainStmtAbs bodyLocals env sSrc with
      | none => none
      | some env' =>
        let aliases' := killCopyAliasesTouching id aliases
        match rewriteCopyPropStmts bodyLocals aliases' env' rest with
        | some (rest', exitAliases, exitEnv) =>
          some (.storageDead id :: rest', exitAliases, exitEnv)
        | none => none
    | .assign dst rvSrc =>
      if !dst.projection.isEmpty then
        none
      else
        match stepPlainStmtAbs bodyLocals env sSrc with
        | none => none
        | some env' =>
          let rvTgt := rewriteCopyPropRvalue aliases rvSrc
          let afterRval := filterAliasesForRvalue rvSrc aliases
          let afterKill := killCopyAliasesTouching dst.localId afterRval
          let aliases' :=
            match rvTgt with
            | .use (.copy pHead) =>
              if pHead.projection.isEmpty &&
                  !Nat.beq dst.localId pHead.localId then
                match Trusted.MirSemantics.getElem? bodyLocals dst.localId,
                    Trusted.MirSemantics.getElem? bodyLocals pHead.localId,
                    Trusted.MirSemantics.getElem? env dst.localId,
                    Trusted.MirSemantics.getElem? env pHead.localId with
                | some dstTy, some srcTy, some dstSlot, some .liveInit =>
                  if MirTy.beq dstTy srcTy &&
                      isSupportedScalarOrUnitTy dstTy &&
                      absSlotImplies dstSlot .liveUninit then
                    (dst.localId, pHead.localId) :: afterKill
                  else
                    afterKill
                | _, _, _, _ => afterKill
              else
                afterKill
            | _ => afterKill
          match rewriteCopyPropStmts bodyLocals aliases' env' rest with
          | some (rest', exitAliases, exitEnv) =>
            some (.assign dst rvTgt :: rest', exitAliases, exitEnv)
          | none => none

noncomputable def rewriteCopyPropTerm (aliases : CopyAliases) :
    TerminatorKind → TerminatorKind
  | .switchInt discr targets =>
    .switchInt (rewriteCopyPropOperand aliases discr) targets
  | term => term

noncomputable def applyCopyPropBlocks (b : Body) (cert : BodyAbsCert) :
    Nat → List BasicBlock → Option (List BasicBlock)
  | _, [] => some []
  | bbIdx, bb :: rest =>
    match Trusted.MirSemantics.getElem? cert bbIdx with
    | none => none
    | some none =>
      match applyCopyPropBlocks b cert (bbIdx + 1) rest with
      | some rest' => some (bb :: rest')
      | none => none
    | some (some entryEnv) =>
      if !Nat.beq entryEnv.length b.locals.length then
        none
      else
        match rewriteCopyPropStmts b.locals [] entryEnv bb.statements with
        | none => none
        | some (stmts', exitAliases, exitEnv) =>
          if !checkAbsTerminatorEdges b.locals b.basicBlocks.length cert
              exitEnv bb.terminator then
            none
          else
            let bb' : BasicBlock := {
              statements := stmts'
              terminator := rewriteCopyPropTerm exitAliases bb.terminator
              cleanup := bb.cleanup
            }
            match applyCopyPropBlocks b cert (bbIdx + 1) rest with
            | some rest' => some (bb' :: rest')
            | none => none

noncomputable def applyCopyPropBody (cert : BodyAbsCert) (b : Body) :
    Option Body :=
  if !Nat.beq cert.length b.basicBlocks.length then
    none
  else if !b.basicBlocks.isEmpty &&
      !(match Trusted.MirSemantics.getElem? cert 0 with
        | some (some env₀) =>
          absEnvImplies (initAbsEnvLoop b 0 b.locals) env₀
        | _ => false) then
    none
  else
    match applyCopyPropBlocks b cert 0 b.basicBlocks with
    | some bbs' => some { b with basicBlocks := bbs' }
    | none => none

noncomputable def applyCopyPropProgram (cert : ProgramAbsCert)
    (p : Program) : Option Program :=
  if !Nat.beq cert.length p.bodies.length then
    none
  else
    match mapOption (fun pr => applyCopyPropBody pr.1 pr.2)
        (List.zip cert p.bodies) with
    | some bodies' => some { p with bodies := bodies' }
    | none => none

/-- Per-body certificate for `DestinationPropagation`. -/
structure BodyDestPropCert where
  liveCert : BodyAbsCert
  deadAtEntry : BodyDeadCert := []

abbrev ProgramDestPropCert := List BodyDestPropCert

noncomputable def isDestPropCopyOrMoveTmp (tmp : LocalId) : Rvalue → Bool
  | .use (.move p) | .use (.copy p) =>
    p.projection.isEmpty && Nat.beq p.localId tmp
  | _ => false

noncomputable def matchDestPropCandidate? (bodyLocals : List MirTy)
    (env : List AbsSlot) (s₁ s₂ : StatementKind) :
    Option (LocalId × Place × Rvalue) :=
  match s₁, s₂ with
  | .assign tmpPlace rv₁, .assign dstPlace rvUse =>
    if !(tmpPlace.projection.isEmpty && dstPlace.projection.isEmpty) then
      none
    else
      let tmp := tmpPlace.localId
      let dst := dstPlace.localId
      if !Nat.beq tmp 0 &&
          !Nat.beq tmp dst &&
          !rvalueTouchesLocal tmp rv₁ &&
          isDestPropCopyOrMoveTmp tmp rvUse then
        match Trusted.MirSemantics.getElem? bodyLocals tmp,
            Trusted.MirSemantics.getElem? bodyLocals dst,
            Trusted.MirSemantics.getElem? env tmp,
            Trusted.MirSemantics.getElem? env dst with
        | some tmpTy, some dstTy, some tmpSlot, some dstSlot =>
          if MirTy.beq tmpTy dstTy &&
              isSupportedScalarOrUnitTy dstTy &&
              absSlotImplies tmpSlot .liveUninit &&
              absSlotImplies dstSlot .liveUninit then
            some (tmp, dstPlace, rv₁)
          else
            none
        | _, _, _, _ => none
      else
        none
  | _, _ => none

noncomputable def rewriteDestPropStmts (bodyLocals : List MirTy)
    (deadAtEntry : BodyDeadCert) (numBlocks : Nat) (term : TerminatorKind) :
    List AbsSlot → List StatementKind →
    Option (List StatementKind × List AbsSlot)
  | env, [] => some ([], env)
  | env, s₁ :: s₂ :: rest =>
    match matchDestPropCandidate? bodyLocals env s₁ s₂ with
    | some (tmp, dstPlace, rv₁) =>
      match stepPlainStmtAbs bodyLocals env s₁ with
      | none => none
      | some env₁ =>
        match stepPlainStmtAbs bodyLocals env₁ s₂ with
        | none => none
        | some env₂ =>
          match rewriteDestPropStmts bodyLocals deadAtEntry numBlocks term
              env₂ rest with
          | none => none
          | some (restTgt, exitEnv) =>
            if isDeadAcrossCfg bodyLocals.length deadAtEntry numBlocks tmp
                restTgt term then
              some (.assign dstPlace rv₁ :: .nop :: restTgt, exitEnv)
            else
              match rewriteDestPropStmts bodyLocals deadAtEntry numBlocks term
                  env₁ (s₂ :: rest) with
              | some (tailTgt, exitEnv') => some (s₁ :: tailTgt, exitEnv')
              | none => none
    | none =>
      match stepPlainStmtAbs bodyLocals env s₁ with
      | none => none
      | some env₁ =>
        match rewriteDestPropStmts bodyLocals deadAtEntry numBlocks term
            env₁ (s₂ :: rest) with
        | some (tailTgt, exitEnv) => some (s₁ :: tailTgt, exitEnv)
        | none => none
  | env, [s₁] =>
    match stepPlainStmtAbs bodyLocals env s₁ with
    | some exitEnv => some ([s₁], exitEnv)
    | none => none

noncomputable def applyDestPropBlocks (b : Body) (cert : BodyDestPropCert) :
    Nat → List BasicBlock → Option (List BasicBlock)
  | _, [] => some []
  | bbIdx, bb :: rest =>
    match Trusted.MirSemantics.getElem? cert.liveCert bbIdx with
    | none => none
    | some none =>
      match applyDestPropBlocks b cert (bbIdx + 1) rest with
      | some rest' => some (bb :: rest')
      | none => none
    | some (some entryEnv) =>
      if !Nat.beq entryEnv.length b.locals.length then
        none
      else
        match rewriteDestPropStmts b.locals cert.deadAtEntry
            b.basicBlocks.length bb.terminator entryEnv bb.statements with
        | none => none
        | some (stmts', exitEnv) =>
          if !checkAbsTerminatorEdges b.locals b.basicBlocks.length
              cert.liveCert exitEnv bb.terminator then
            none
          else
            let bb' : BasicBlock := { bb with statements := stmts' }
            match applyDestPropBlocks b cert (bbIdx + 1) rest with
            | some rest' => some (bb' :: rest')
            | none => none

noncomputable def applyDestPropBody (cert : BodyDestPropCert) (b : Body) :
    Option Body :=
  if !Nat.beq cert.liveCert.length b.basicBlocks.length then
    none
  else if !b.basicBlocks.isEmpty &&
      !(match Trusted.MirSemantics.getElem? cert.liveCert 0 with
        | some (some env₀) =>
          absEnvImplies (initAbsEnvLoop b 0 b.locals) env₀
        | _ => false) then
    none
  else
    match applyDestPropBlocks b cert 0 b.basicBlocks with
    | none => none
    | some bbs' =>
      let bOut : Body := { b with basicBlocks := bbs' }
      if checkBodyDeadCert bOut cert.deadAtEntry then
        some bOut
      else
        none

noncomputable def applyDestPropProgram (cert : ProgramDestPropCert)
    (p : Program) : Option Program :=
  if !Nat.beq cert.length p.bodies.length then
    none
  else
    match mapOption (fun pr => applyDestPropBody pr.1 pr.2)
        (List.zip cert p.bodies) with
    | some bodies' => some { p with bodies := bodies' }
    | none => none

/-- 4-point non-zero & initialization lattice for totality-certified DSE
(`liveNonZero ⊑ liveInit ⊑ liveUninit ⊑ dead`). -/
inductive NonZeroAbsSlot where
  | liveNonZero
  | liveInit
  | liveUninit
  | dead

noncomputable def nonZeroSlotImplies : NonZeroAbsSlot → NonZeroAbsSlot → Bool
  | _, .dead => true
  | .liveNonZero, .liveUninit
  | .liveInit, .liveUninit
  | .liveUninit, .liveUninit => true
  | .liveNonZero, .liveInit | .liveInit, .liveInit => true
  | .liveNonZero, .liveNonZero => true
  | _, _ => false

noncomputable def nonZeroEnvImplies :
    List NonZeroAbsSlot → List NonZeroAbsSlot → Bool :=
  listRel nonZeroSlotImplies

structure BodyDseCert where
  nzCert : List (Option (List NonZeroAbsSlot))
  deadAtEntry : BodyDeadCert := []

abbrev ProgramDseCert := List BodyDseCert

noncomputable def initNonZeroSlot (body : Body) (idx : Nat)
    (ty : MirTy) : NonZeroAbsSlot :=
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

noncomputable def initNonZeroEnvLoop (body : Body) :
    Nat → List MirTy → List NonZeroAbsSlot
  | _, [] => []
  | idx, ty :: rest =>
    initNonZeroSlot body idx ty :: initNonZeroEnvLoop body (idx + 1) rest

noncomputable def isValidNonZeroIntConst (w : IntWidth) (s : Bool)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty (.int w s) &&
    match evalConstLit (.int w s) c.lit with
    | .ok (.scalar sv) => decodeScalar sv != 0
    | _ => false

noncomputable def isCertifiedSignedSafeDivisor (w : IntWidth) : Operand → Bool
  | .constant c =>
    MirTy.beq c.ty (.int w true) &&
      match evalConstLit (.int w true) c.lit with
      | .ok (.scalar sv) =>
        let v := decodeScalar sv
        (v != 0) && (v != Neg.neg 1)
      | _ => false
  | _ => false

noncomputable def constProducesNonZeroScalar (dstTy : MirTy)
    (c : ConstOperand) : Bool :=
  match dstTy with
  | .int w s => isValidNonZeroIntConst w s c
  | _ => false

noncomputable def deinitMoveOperandNonZero (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) : Operand → List NonZeroAbsSlot
  | .move p =>
    if !p.projection.isEmpty then env
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => env
      | some ty =>
        let nextSlot := if isAlwaysInhabitedZst ty then .liveInit else .liveUninit
        match setElem? env p.localId nextSlot with
        | some env' => env'
        | none => env
  | _ => env

noncomputable def deinitMovesInRvalueNonZero (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) : Rvalue → List NonZeroAbsSlot
  | .use opnd | .unaryOp _ opnd => deinitMoveOperandNonZero bodyLocals env opnd
  | .binaryOp _ lhs rhs =>
    let env₁ := deinitMoveOperandNonZero bodyLocals env lhs
    deinitMoveOperandNonZero bodyLocals env₁ rhs
  | _ => env

noncomputable def rvalueProducesNonZero (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) (dstTy : MirTy) : Rvalue → Bool
  | .use (.constant c) => constProducesNonZeroScalar dstTy c
  | .use (.copy p) | .use (.move p) =>
    p.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some srcTy, some .liveNonZero => MirTy.beq srcTy dstTy
      | _, _ => false
  | _ => false

noncomputable def isCertifiedNonZeroDivisor (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) (w : IntWidth) (s : Bool) : Operand → Bool
  | .constant c => isValidNonZeroIntConst w s c
  | .copy p =>
    p.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some .liveNonZero => MirTy.beq ty (.int w s)
      | _, _ => false
  | .move _ => false

noncomputable def operandCertifiedPrimitiveTy? (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) (allowedMoveLocal : LocalId) :
    Operand → Option MirTy
  | .constant c =>
    if !isPrimitiveReadableTy c.ty then none
    else
      match evalConstLit c.ty c.lit with
      | .ok v => if checkVal v c.ty then some c.ty else none
      | .error _ => none
  | .copy p =>
    if !p.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some slot =>
        if isPrimitiveReadableTy ty && nonZeroSlotImplies slot .liveInit then
          some ty
        else
          none
      | _, _ => none
  | .move p =>
    if !(p.projection.isEmpty && Nat.beq p.localId allowedMoveLocal) then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some slot =>
        if isPrimitiveReadableTy ty && nonZeroSlotImplies slot .liveInit then
          some ty
        else
          none
      | _, _ => none

noncomputable def binOpCertifiedTotal (bodyLocals : List MirTy)
    (envAfterLhs : List NonZeroAbsSlot) (op : BinOp)
    (lhsTy rhsTy dstTy : MirTy) (rhs : Operand) : Bool :=
  match op with
  | .add | .sub | .mul =>
    match lhsTy with
    | .int w s => MirTy.beq rhsTy (.int w s) && MirTy.beq dstTy (.int w s)
    | _ => false
  | .bitAnd | .bitOr | .bitXor =>
    (MirTy.beq lhsTy .bool && MirTy.beq rhsTy .bool && MirTy.beq dstTy .bool) ||
      match lhsTy with
      | .int w s => MirTy.beq rhsTy (.int w s) && MirTy.beq dstTy (.int w s)
      | _ => false
  | .eq | .ne | .lt | .le | .gt | .ge =>
    MirTy.beq dstTy .bool &&
      ((MirTy.beq lhsTy .bool && MirTy.beq rhsTy .bool) ||
        match lhsTy with
        | .int w s => MirTy.beq rhsTy (.int w s)
        | _ => false)
  | .shl | .shr =>
    match lhsTy, rhsTy with
    | .int w s, .int _ _ => MirTy.beq dstTy (.int w s)
    | _, _ => false
  | .div | .rem =>
    match lhsTy with
    | .int w false =>
      MirTy.beq rhsTy (.int w false) &&
        MirTy.beq dstTy (.int w false) &&
        isCertifiedNonZeroDivisor bodyLocals envAfterLhs w false rhs
    | .int w true =>
      MirTy.beq rhsTy (.int w true) &&
        MirTy.beq dstTy (.int w true) &&
        isCertifiedSignedSafeDivisor w rhs
    | _ => false
  | _ => false

noncomputable def rvalueCertifiedTotal (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) (dst : LocalId) (dstTy : MirTy)
    (rv : Rvalue) : Bool :=
  isSupportedScalarOrUnitTy dstTy &&
    rvalueNoMoveExcept dst rv &&
    match rv with
    | .use (.constant c) =>
      MirTy.beq c.ty dstTy &&
        match evalConstLit dstTy c.lit with
        | .ok v => checkVal v dstTy
        | .error _ => false
    | .use (.copy p) | .use (.move p) =>
      p.projection.isEmpty &&
        match Trusted.MirSemantics.getElem? bodyLocals p.localId,
            Trusted.MirSemantics.getElem? env p.localId with
        | some srcTy, some slot =>
          MirTy.beq srcTy dstTy && nonZeroSlotImplies slot .liveInit
        | _, _ => false
    | .unaryOp op opnd =>
      match operandCertifiedPrimitiveTy? bodyLocals env dst opnd with
      | none => false
      | some opTy =>
        MirTy.beq opTy dstTy &&
          match op, opTy with
          | .not, .bool | .not, .int _ _ => true
          | .neg, .int _ true => true
          | _, _ => false
    | .binaryOp op (.constant c₁) (.constant c₂) =>
      isPrimitiveReadableTy c₁.ty &&
        isPrimitiveReadableTy c₂.ty &&
        match evalConstLit c₁.ty c₁.lit, evalConstLit c₂.ty c₂.lit with
        | .ok v₁, .ok v₂ =>
          match evalBinOp op v₁ v₂ with
          | .ok res => checkVal res dstTy
          | .error _ => false
        | _, _ => false
    | .binaryOp op lhs rhs =>
      match operandCertifiedPrimitiveTy? bodyLocals env dst lhs with
      | none => false
      | some lhsTy =>
        let env₁ := deinitMoveOperandNonZero bodyLocals env lhs
        match operandCertifiedPrimitiveTy? bodyLocals env₁ dst rhs with
        | none => false
        | some rhsTy =>
          binOpCertifiedTotal bodyLocals env₁ op lhsTy rhsTy dstTy rhs
    | .discriminant p =>
      p.projection.isEmpty &&
        match Trusted.MirSemantics.getElem? bodyLocals p.localId,
            Trusted.MirSemantics.getElem? env p.localId with
        | some (.enum ety), some slot =>
          enumAdmitted ety &&
            MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned) &&
            (if isZstEnumTy ety then
               nonZeroSlotImplies slot .liveUninit
             else
               nonZeroSlotImplies slot .liveInit)
        | _, _ => false
    | _ => false

noncomputable def stepPlainStmtNonZero (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) : StatementKind → Option (List NonZeroAbsSlot)
  | .nop | .unsupported => some env
  | .storageLive id =>
    match Trusted.MirSemantics.getElem? bodyLocals id with
    | none => none
    | some ty =>
      let nextSlot := if isAlwaysInhabitedZst ty then .liveInit else .liveUninit
      setElem? env id nextSlot
  | .storageDead id =>
    if Nat.beq id 0 then none else setElem? env id .dead
  | .assign dst rv =>
    if !dst.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => none
      | some dstTy =>
        let dstSlot :=
          if rvalueProducesNonZero bodyLocals env dstTy rv then
            .liveNonZero
          else
            .liveInit
        let env₁ := deinitMovesInRvalueNonZero bodyLocals env rv
        setElem? env₁ dst.localId dstSlot

noncomputable def hasValidZeroGuard (w : IntWidth) :
    List (BitVec 128 × BasicBlockId) → Bool
  | [] => false
  | (caseBits, _) :: rest =>
    if truncateBits w caseBits != caseBits then
      false
    else if caseBits == BitVec.ofNat 128 0 then
      true
    else
      hasValidZeroGuard w rest

noncomputable def checkNonZeroEdge (numBlocks : Nat)
    (nzCert : List (Option (List NonZeroAbsSlot)))
    (exitEnv : List NonZeroAbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? nzCert target with
    | some (some tgtEnv) => nonZeroEnvImplies exitEnv tgtEnv
    | _ => false

noncomputable def checkNonZeroTerminatorEdges (bodyLocals : List MirTy)
    (numBlocks : Nat) (nzCert : List (Option (List NonZeroAbsSlot)))
    (exitEnv : List NonZeroAbsSlot) : TerminatorKind → Bool
  | .goto target => checkNonZeroEdge numBlocks nzCert exitEnv target
  | .switchInt discr targets =>
    let afterDiscrEnv := deinitMoveOperandNonZero bodyLocals exitEnv discr
    let otherwiseEnv :=
      match discr with
      | .copy p =>
        if !p.projection.isEmpty then afterDiscrEnv
        else
          match Trusted.MirSemantics.getElem? bodyLocals p.localId,
              Trusted.MirSemantics.getElem? afterDiscrEnv p.localId with
          | some (.int w _), some curSlot =>
            if nonZeroSlotImplies curSlot .liveInit &&
                hasValidZeroGuard w targets.branches then
              match setElem? afterDiscrEnv p.localId .liveNonZero with
              | some refined => refined
              | none => afterDiscrEnv
            else
              afterDiscrEnv
          | _, _ => afterDiscrEnv
      | _ => afterDiscrEnv
    checkNonZeroEdge numBlocks nzCert otherwiseEnv targets.otherwise &&
      targets.branches.all (fun br =>
        checkNonZeroEdge numBlocks nzCert afterDiscrEnv br.2)
  | _ => true

noncomputable def rewriteCertifiedDseStmts (bodyLocals : List MirTy)
    (deadAtEntry : BodyDeadCert) (numBlocks : Nat) (term : TerminatorKind) :
    List NonZeroAbsSlot → List StatementKind →
    Option (List StatementKind × List NonZeroAbsSlot)
  | env, [] => some ([], env)
  | env, sSrc :: restSrc =>
    match stepPlainStmtNonZero bodyLocals env sSrc with
    | none => none
    | some env' =>
      match rewriteCertifiedDseStmts bodyLocals deadAtEntry numBlocks term
          env' restSrc with
      | none => none
      | some (restTgt, exitEnv) =>
        let elimHere : Bool :=
          match sSrc with
          | .assign dstPlace rval =>
            dstPlace.projection.isEmpty &&
              !Nat.beq dstPlace.localId 0 &&
              Nat.blt dstPlace.localId bodyLocals.length &&
              isDeadAcrossCfg bodyLocals.length deadAtEntry numBlocks
                dstPlace.localId restTgt term &&
              match Trusted.MirSemantics.getElem? bodyLocals dstPlace.localId,
                  Trusted.MirSemantics.getElem? env dstPlace.localId with
              | some dstTy, some dstSlot =>
                nonZeroSlotImplies dstSlot .liveUninit &&
                  rvalueCertifiedTotal bodyLocals env dstPlace.localId dstTy
                    rval
              | _, _ => false
          | _ => false
        let sTgt := if elimHere then .nop else sSrc
        some (sTgt :: restTgt, exitEnv)

noncomputable def applyCertifiedDseBlocks (b : Body) (cert : BodyDseCert) :
    Nat → List BasicBlock → Option (List BasicBlock)
  | _, [] => some []
  | bbIdx, bb :: rest =>
    match Trusted.MirSemantics.getElem? cert.nzCert bbIdx with
    | none => none
    | some none =>
      match applyCertifiedDseBlocks b cert (bbIdx + 1) rest with
      | some rest' => some (bb :: rest')
      | none => none
    | some (some entryEnv) =>
      if !Nat.beq entryEnv.length b.locals.length then
        none
      else
        match rewriteCertifiedDseStmts b.locals cert.deadAtEntry
            b.basicBlocks.length bb.terminator entryEnv bb.statements with
        | none => none
        | some (stmts', exitEnv) =>
          if !checkNonZeroTerminatorEdges b.locals b.basicBlocks.length
              cert.nzCert exitEnv bb.terminator then
            none
          else
            let bb' : BasicBlock := { bb with statements := stmts' }
            match applyCertifiedDseBlocks b cert (bbIdx + 1) rest with
            | some rest' => some (bb' :: rest')
            | none => none

noncomputable def applyCertifiedDseBody (cert : BodyDseCert) (b : Body) :
    Option Body :=
  if !Nat.beq cert.nzCert.length b.basicBlocks.length then
    none
  else if !b.basicBlocks.isEmpty &&
      !(match Trusted.MirSemantics.getElem? cert.nzCert 0 with
        | some (some env₀) =>
          nonZeroEnvImplies (initNonZeroEnvLoop b 0 b.locals) env₀
        | _ => false) then
    none
  else
    match applyCertifiedDseBlocks b cert 0 b.basicBlocks with
    | none => none
    | some bbs' =>
      let bOut : Body := { b with basicBlocks := bbs' }
      if checkBodyDeadCert bOut cert.deadAtEntry then
        some bOut
      else
        none

noncomputable def applyCertifiedDseProgram (cert : ProgramDseCert)
    (p : Program) : Option Program :=
  if !Nat.beq cert.length p.bodies.length then
    none
  else
    match mapOption (fun pr => applyCertifiedDseBody pr.1 pr.2)
        (List.zip cert p.bodies) with
    | some bodies' => some { p with bodies := bodies' }
    | none => none

/-- Combined certificate bundle for Pass Family 4 (`CopyProp` ->
`DestinationPropagation` -> totality-certified `DeadStoreElimination`). -/
structure CopyDestDseCert where
  copyCert : ProgramAbsCert
  destCert : ProgramDestPropCert
  dseCert : ProgramDseCert

noncomputable def applyCopyAndDestPropAndDseProgram (cert : CopyDestDseCert)
    (p : Program) : Option Program :=
  match applyCopyPropProgram cert.copyCert p with
  | none => none
  | some p₁ =>
    match applyDestPropProgram cert.destCert p₁ with
    | none => none
    | some p₂ => applyCertifiedDseProgram cert.dseCert p₂

/-! ### Pass Family 5: `.compactUnusedTrailingLocals (newCount : Nat)` (`E3-7` / `R3`) -/

noncomputable def operandLocalsLt (bound : Nat) : Operand → Bool
  | .copy p | .move p => Nat.blt p.localId bound
  | .constant _ => true

noncomputable def rvalueLocalsLt (bound : Nat) : Rvalue → Bool
  | .use o | .unaryOp _ o => operandLocalsLt bound o
  | .binaryOp _ l r => operandLocalsLt bound l && operandLocalsLt bound r
  | .discriminant p | .ref _ p | .addressOf _ p => Nat.blt p.localId bound
  | .aggregateTuple fs => fs.all (operandLocalsLt bound)
  | .unsupported => true

noncomputable def stmtLocalsLt (bound : Nat) : StatementKind → Bool
  | .assign dst rv => Nat.blt dst.localId bound && rvalueLocalsLt bound rv
  | .storageLive id | .storageDead id => Nat.blt id bound
  | .nop | .unsupported => true

noncomputable def terminatorLocalsLt (bound : Nat) : TerminatorKind → Bool
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .switchInt d _ => operandLocalsLt bound d
  | .assert c _ _ _ _ => operandLocalsLt bound c
  | .call _ args dst _ _ =>
    args.all (operandLocalsLt bound) && Nat.blt dst.localId bound

noncomputable def blockAllLocalsLt (bound : Nat) (bb : BasicBlock) : Bool :=
  bb.statements.all (stmtLocalsLt bound) &&
    terminatorLocalsLt bound bb.terminator

/-- Check that `b.locals` can be safely compacted to `newCount` slots:
1. `b.argumentCount < newCount ≤ b.locals.length` (retaining `_0` and all
   parameter slots `_1 .. _argumentCount`);
2. All dropped trailing types `(b.locals.drop newCount)` belong to
   `isSupportedScalarOrUnitTy` (preventing compaction from masking an
   unsupported-type static admission failure in `initState` / `BodyStaticAdmitted`);
3. Every basic block in `b.basicBlocks` references only `LocalId < newCount` in
   all statements, storage annotations, and terminators. -/
noncomputable def canCompactBodyLocals (newCount : Nat) (b : Body) : Bool :=
  Nat.blt b.argumentCount newCount &&
    Nat.ble newCount b.locals.length &&
    (b.locals.drop newCount).all isSupportedScalarOrUnitTy &&
    b.basicBlocks.all (blockAllLocalsLt newCount)

noncomputable def applyCompactTrailingLocalsBody (newCount : Nat)
    (b : Body) : Option Body :=
  if canCompactBodyLocals newCount b then
    some { b with locals := b.locals.take newCount }
  else
    none

noncomputable def applyCompactTrailingLocalsProgram (newCount : Nat)
    (p : Program) : Option Program :=
  match mapOption (applyCompactTrailingLocalsBody newCount) p.bodies with
  | some bodies' => some { p with bodies := bodies' }
  | none => none

/-! ### Unified `MirOptStep`, `MirOptTrace`, & Top-Level Semantic Contracts -/

/-- Certified single-step MIR optimization pass sum type unifying the five
pass families over unmodified `Trusted.MirAst.Program`. -/
inductive MirOptStep where
  | moveToCopyDead (cert : ProgramDeadCert)
  | simplifyCfgBranch (cert : ProgramAbsCert)
  | instSimplifyAlgAndConst (cert : ProgramConstCert)
  | copyAndDestPropAndDse (cert : CopyDestDseCert)
  | compactUnusedTrailingLocals (newCount : Nat)

/-- Arbitrary-length sequence of certified MIR optimization steps. -/
abbrev MirOptTrace := List MirOptStep

/-- Deterministically execute one certified `MirOptStep` on `pSrc`. -/
noncomputable def applyMirOptStep (step : MirOptStep)
    (pSrc : Program) : Option Program :=
  match step with
  | .moveToCopyDead cert => applyMoveToCopyDeadProgram cert pSrc
  | .simplifyCfgBranch cert => applySimplifyCfgBranchProgram cert pSrc
  | .instSimplifyAlgAndConst cert =>
    applyInstSimplifyAlgAndConstProgram cert pSrc
  | .copyAndDestPropAndDse cert =>
    applyCopyAndDestPropAndDseProgram cert pSrc
  | .compactUnusedTrailingLocals newCount =>
    applyCompactTrailingLocalsProgram newCount pSrc

/-- Executable single-step validator checking `pSrc --[step]--> pTgt`. -/
noncomputable def checkMirOptStep (step : MirOptStep)
    (pSrc pTgt : Program) : Bool :=
  match applyMirOptStep step pSrc with
  | some pOut => programEq pOut pTgt
  | none => false

/-- Deterministically execute an arbitrary-length `MirOptTrace` from `pSrc`. -/
noncomputable def applyMirOptTrace : MirOptTrace → Program → Option Program
  | [], p => some p
  | step :: rest, p =>
    match applyMirOptStep step p with
    | some pMid => applyMirOptTrace rest pMid
    | none => none

/-- Executable arbitrary-length multi-pass pipeline validator checking
`pPostCleanup --[trace]*--> pOptimized`. -/
noncomputable def checkMirOptTrace (trace : MirOptTrace)
    (pPostCleanup pOptimized : Program) : Bool :=
  match applyMirOptTrace trace pPostCleanup with
  | some pOut => programEq pOut pOptimized
  | none => false

/-- Bundled bidirectional operational and verification equivalence between
`pSrc` and `pTgt` across all $M_{\text{anneal}}$ judgments (`WellFormed`,
`Behavior`, `ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and
`BodyVerified`). -/
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

/-- Select body `u` of `p` as a `.unit`-scoped proof-unit subject for
`Trusted.MirSemantics.UnitTheorem`. -/
noncomputable def unitProgForDef (p : Program) (u : DefId) : Program :=
  { p with entryDefId := u, scope := .unit }

/-- Semantic invariance of `specs.property` across `FullSemanticEquiv`
programs (satisfied automatically by `property := fun _ => True` and by any
behavioral contract over `WellFormed`, `Behavior`, or `Diverges`). -/
noncomputable def SpecsPropertyInvariant (specs : Specs) : Prop :=
  ∀ p₁ p₂ : Program, FullSemanticEquiv p₁ p₂ →
    (specs.property p₁ ↔ specs.property p₂)

/-! ## Part II: Half B — `MirProfileV2` (`PlaceMention` & `Assume`) & Exact `Trusted.MirAst` Embedding -/

/-- Profile tag distinguishing exact embedded `mirProfileVersion = 1` programs
(`embedProgramV1`) from extended `mirProfileVersion = 2` programs admitting
raw-pointer `PlaceMention` and `NonDivergingIntrinsic::Assume`. -/
inductive ProfileModeV2 where
  | v1Embedded
  | v2Extended

noncomputable def profileModeEq : ProfileModeV2 → ProfileModeV2 → Bool
  | .v1Embedded, .v1Embedded | .v2Extended, .v2Extended => true
  | _, _ => false

/-- Refined fault classification in `MirProfileV2`, splitting modeled Undefined
Behavior into general `.undefined`, `inbounds` pointer-offset UB
`.invalidPointerOffset` (`E3-22`), and `.assume false` / `Unreachable` UB
`.unreachableExecuted` (`E3-16`) while projecting conservatively onto
`Trusted.MirSemantics.FaultKind` via `FaultKindV2.toV1`. -/
inductive FaultKindV2 where
  | undefined
  | invalidPointerOffset
  | unreachableExecuted
  | unsupported

noncomputable def FaultKindV2.ofV1 : FaultKind → FaultKindV2
  | .undefined => .undefined
  | .unsupported => .unsupported

noncomputable def FaultKindV2.toV1 : FaultKindV2 → FaultKind
  | .undefined | .invalidPointerOffset | .unreachableExecuted => .undefined
  | .unsupported => .unsupported

/-- Single-step and multi-step outcome type for `MirProfileV2`. -/
inductive StepResultV2 (S O : Type) where
  | step (next : S)
  | done (out : O)
  | fault (kind : FaultKindV2)

noncomputable def mapStepResultV1ToV2 :
    StepResult State TerminalOut → StepResultV2 State TerminalOut
  | .step s => .step s
  | .done out => .done out
  | .fault k => .fault (FaultKindV2.ofV1 k)

noncomputable def mapStepResultV2ToV1 :
    StepResultV2 State TerminalOut → StepResult State TerminalOut
  | .step s => .step s
  | .done out => .done out
  | .fault k => .fault k.toV1

/-- Extended place expression for `StatementKindV2.placeMention`
(`compiler/rustc_const_eval/src/interpret/step.rs:119-122` and `E3-22`):
- `.local localId`: unprojected local place `_localId` (checks live local slot
  without requiring initialized scalar value).
- `.rawDeref ptrLocal`: RFC 2582 zero-offset raw-pointer dereference
  `(*_ptrLocal)` (requires a live initialized `Val.ptr` in `_ptrLocal`, legal
  even when null or misaligned because zero-offset raw place creation performs
  neither `inbounds` pointer arithmetic nor a memory load).
- `.rawDerefFieldOffset ptrLocal byteOffset`: projected raw-pointer field place
  `((*_ptrLocal).field)` at byte offset `byteOffset` (`inbounds` offset check:
  defined at `byteOffset = 0`, whereas `byteOffset > 0` requires a live
  allocation in `callerMem` covering `offsetBytes + byteOffset` and faults with
  `.invalidPointerOffset` on null, dangling, or out-of-bounds pointers). -/
inductive PlaceV2 where
  | local (localId : LocalId)
  | rawDeref (ptrLocal : LocalId)
  | rawDerefFieldOffset (ptrLocal : LocalId) (byteOffset : Nat)

noncomputable def placeV2Eq : PlaceV2 → PlaceV2 → Bool
  | .local i₁, .local i₂ => Nat.beq i₁ i₂
  | .rawDeref p₁, .rawDeref p₂ => Nat.beq p₁ p₂
  | .rawDerefFieldOffset p₁ o₁, .rawDerefFieldOffset p₂ o₂ =>
    Nat.beq p₁ p₂ && Nat.beq o₁ o₂
  | _, _ => false

/-- Syntactic safety predicate for `RemovePlaceMention`: admits local mentions
and RFC 2582 zero-offset raw-pointer dereferences while rejecting non-zero
`inbounds` field-offset projections (`byteOffset > 0`). -/
noncomputable def isSafePlaceMention : PlaceV2 → Bool
  | .local _ => true
  | .rawDeref _ => true
  | .rawDerefFieldOffset _ byteOffset => Nat.beq byteOffset 0

/-- Extended MIR statement syntax in `MirProfileV2`:
- `.v1 s`: exact embedding of `Trusted.MirAst.StatementKind`,
- `.placeMention p`: `StatementKind::PlaceMention(p)` (`E3-22`),
- `.assume cond`: `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(cond))`
  (`E3-16`). -/
inductive StatementKindV2 where
  | v1 (stmt : StatementKind)
  | placeMention (place : PlaceV2)
  | assume (cond : Operand)

noncomputable def stmtV2Eq : StatementKindV2 → StatementKindV2 → Bool
  | .v1 s₁, .v1 s₂ => stmtEq s₁ s₂
  | .placeMention p₁, .placeMention p₂ => placeV2Eq p₁ p₂
  | .assume c₁, .assume c₂ => operandEq c₁ c₂
  | _, _ => false

structure BasicBlockV2 where
  statements : List StatementKindV2
  terminator : TerminatorKind
  cleanup : Bool := false

noncomputable def blockV2Eq (b₁ b₂ : BasicBlockV2) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel stmtV2Eq b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

structure BodyV2 where
  argumentCount : Nat
  locals : List MirTy
  basicBlocks : List BasicBlockV2
  isUnsafe : Bool := false
  identity : String := ""

noncomputable def bodyHeaderV2Eq (b₁ b₂ : BodyV2) : Bool :=
  Nat.beq b₁.argumentCount b₂.argumentCount &&
    MirTy.beqList b₁.locals b₂.locals &&
    (b₁.isUnsafe == b₂.isUnsafe) &&
    stringBeq b₁.identity b₂.identity

structure ProgramV2 where
  bodies : List BodyV2
  entryDefId : DefId := 0
  pointerWidthBits : Nat
  mirProfileVersion : Nat
  scope : VerificationScope := .unit
  profileMode : ProfileModeV2 := .v2Extended

noncomputable def programHeaderV2Eq (p₁ p₂ : ProgramV2) : Bool :=
  Nat.beq p₁.pointerWidthBits p₂.pointerWidthBits &&
    Nat.beq p₁.mirProfileVersion p₂.mirProfileVersion &&
    Nat.beq p₁.entryDefId p₂.entryDefId &&
    scopeEq p₁.scope p₂.scope &&
    profileModeEq p₁.profileMode p₂.profileMode

/-- Exact embedding of `Trusted.MirAst.BasicBlock` into `BasicBlockV2`. -/
noncomputable def embedBlockV1 (bb : BasicBlock) : BasicBlockV2 := {
  statements := bb.statements.map StatementKindV2.v1
  terminator := bb.terminator
  cleanup := bb.cleanup
}

/-- Exact embedding of `Trusted.MirAst.Body` into `BodyV2`. -/
noncomputable def embedBodyV1 (b : Body) : BodyV2 := {
  argumentCount := b.argumentCount
  locals := b.locals
  basicBlocks := b.basicBlocks.map embedBlockV1
  isUnsafe := b.isUnsafe
  identity := b.identity
}

/-- Exact conservative embedding of `Trusted.MirAst.Program` into `ProgramV2`. -/
noncomputable def embedProgramV1 (p : Program) : ProgramV2 := {
  bodies := p.bodies.map embedBodyV1
  entryDefId := p.entryDefId
  pointerWidthBits := p.pointerWidthBits
  mirProfileVersion := p.mirProfileVersion
  scope := p.scope
  profileMode := .v1Embedded
}

/-! ### Operational Semantics of `MirProfileV2` (`initStateV2`, `evalStepV2`, `evalBodyV2`) -/

noncomputable def stmtV2HasStorageMarker (localId : LocalId) :
    StatementKindV2 → Bool
  | .v1 s => stmtHasStorageMarker localId s
  | .placeMention _ | .assume _ => false

noncomputable def hasStorageAnnotationV2 (body : BodyV2)
    (localId : LocalId) : Bool :=
  body.basicBlocks.any (fun bb =>
    bb.statements.any (stmtV2HasStorageMarker localId))

noncomputable def storageAnnotationsInBoundsV2 (body : BodyV2) : Bool :=
  let numLocals := body.locals.length
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .v1 (.storageLive id) | .v1 (.storageDead id) => Nat.blt id numLocals
      | _ => true))

noncomputable def isSupportedProfileV2Ty : MirTy → Bool
  | .rawPtr _ pointee => isSupportedProfileV2Ty pointee
  | ty => isSupportedScalarOrUnitTy ty

noncomputable def checkValV2 (v : Val) (ty : MirTy) : Bool :=
  match v, ty with
  | .ptr pv, .rawPtr _ pointee =>
    IntWidth.beq pv.width .isize && isSupportedProfileV2Ty pointee
  | _, _ => checkVal v ty

noncomputable def checkValForMode (mode : ProfileModeV2) (v : Val)
    (ty : MirTy) : Bool :=
  match mode with
  | .v1Embedded => checkVal v ty
  | .v2Extended => checkValV2 v ty

noncomputable def checkArgsMatchForMode (mode : ProfileModeV2) :
    List Val → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys =>
    checkValForMode mode v ty && checkArgsMatchForMode mode vs tys
  | _, _ => false

noncomputable def initLocalsLoopV2 (body : BodyV2) (args : List Val) :
    Nat → List MirTy → List LocalSlot
  | _, [] => []
  | idx, ty :: rest =>
    let slot : LocalSlot :=
      if Nat.beq idx 0 then
        liveUninitSlot ty
      else if Nat.ble idx body.argumentCount then
        match Trusted.MirSemantics.getElem? args (idx - 1) with
        | some v => .live (some v)
        | none => .dead
      else if hasStorageAnnotationV2 body idx then
        .dead
      else
        liveUninitSlot ty
    slot :: initLocalsLoopV2 body args (idx + 1) rest

noncomputable def callerMemWfV2 (cm : CallerMemory) : Bool :=
  natListPairwiseNe (cm.allocations.map (fun a => a.allocId))

noncomputable def initStateV2 (p : ProgramV2) (q : Query) :
    Except FaultKindV2 State :=
  let profileOk : Bool :=
    match p.profileMode with
    | .v1Embedded =>
      Nat.beq p.pointerWidthBits 64 &&
        Nat.beq p.mirProfileVersion 1 &&
        q.callerMem.allocations.isEmpty
    | .v2Extended =>
      Nat.beq p.pointerWidthBits 64 &&
        Nat.beq p.mirProfileVersion 2 &&
        callerMemWfV2 q.callerMem
  if !profileOk then
    .error .unsupported
  else
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | none => .error .unsupported
    | some body =>
      let tyPred :=
        match p.profileMode with
        | .v1Embedded => isSupportedScalarOrUnitTy
        | .v2Extended => isSupportedProfileV2Ty
      if body.basicBlocks.isEmpty then
        .error .unsupported
      else if !Nat.blt body.argumentCount body.locals.length then
        .error .unsupported
      else if !storageAnnotationsInBoundsV2 body then
        .error .unsupported
      else if !body.locals.all tyPred then
        .error .unsupported
      else
        let paramTys := (body.locals.drop 1).take body.argumentCount
        if !checkArgsMatchForMode p.profileMode q.args paramTys then
          .error .unsupported
        else
          let locals := initLocalsLoopV2 body q.args 0 body.locals
          let frame : FrameState := {
            defId := p.entryDefId
            blockIdx := 0
            stmtIdx := 0
            locals := locals
          }
          .ok { frames := [frame], callerMem := q.callerMem }

noncomputable def findLiveAlloc? (aid : AllocId) :
    List Allocation → Option Allocation
  | [] => none
  | a :: rest =>
    if Nat.beq a.allocId aid then
      if a.live then some a else none
    else
      findLiveAlloc? aid rest

noncomputable def evalPlaceMentionV2 (body : BodyV2) (frame : FrameState)
    (callerMem : CallerMemory) (p : PlaceV2) : Except FaultKindV2 Unit :=
  match p with
  | .local localId =>
    match Trusted.MirSemantics.getElem? body.locals localId,
        Trusted.MirSemantics.getElem? frame.locals localId with
    | some _, some (.live _) => .ok ()
    | some _, some .dead => .error .undefined
    | _, _ => .error .unsupported
  | .rawDeref ptrLocal =>
    match Trusted.MirSemantics.getElem? body.locals ptrLocal,
        Trusted.MirSemantics.getElem? frame.locals ptrLocal with
    | some (.rawPtr _ pointee), some (.live (some (.ptr pv))) =>
      if IntWidth.beq pv.width .isize && isSupportedProfileV2Ty pointee then
        .ok ()
      else
        .error .unsupported
    | some (.rawPtr _ _), some (.live none) => .error .undefined
    | some (.rawPtr _ _), some .dead => .error .undefined
    | _, _ => .error .unsupported
  | .rawDerefFieldOffset ptrLocal byteOffset =>
    match Trusted.MirSemantics.getElem? body.locals ptrLocal,
        Trusted.MirSemantics.getElem? frame.locals ptrLocal with
    | some (.rawPtr _ pointee), some (.live (some (.ptr pv))) =>
      if !(IntWidth.beq pv.width .isize && isSupportedProfileV2Ty pointee) then
        .error .unsupported
      else if Nat.beq byteOffset 0 then
        .ok ()
      else
        match pv.allocId with
        | none => .error .invalidPointerOffset
        | some aid =>
          match findLiveAlloc? aid callerMem.allocations with
          | some alloc =>
            if Nat.ble (pv.offsetBytes.toNat + byteOffset)
                alloc.bytes.length then
              .ok ()
            else
              .error .invalidPointerOffset
          | none => .error .invalidPointerOffset
    | some (.rawPtr _ _), some (.live none) => .error .undefined
    | some (.rawPtr _ _), some .dead => .error .undefined
    | _, _ => .error .unsupported

noncomputable def writePlaceV2 (mode : ProfileModeV2) (locals : List LocalSlot)
    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    Except FaultKindV2 (List LocalSlot) :=
  if !checkValForMode mode val dstTy then
    .error .unsupported
  else
    match Trusted.MirSemantics.getElem? locals dstLocalId with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.live _) =>
      match setElem? locals dstLocalId (.live (some val)) with
      | some locals' => .ok locals'
      | none => .error .unsupported

noncomputable def evalV1StatementInV2 (mode : ProfileModeV2) (body : BodyV2)
    (frame : FrameState) (callerMem : CallerMemory) (stmt : StatementKind) :
    StepResultV2 State TerminalOut :=
  match stmt with
  | .nop =>
    .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }], callerMem }
  | .storageLive localId =>
    match Trusted.MirSemantics.getElem? body.locals localId with
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
      match Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
        match evalRvalue body.locals frame.locals dstTy rvalue with
        | .error k => .fault (FaultKindV2.ofV1 k)
        | .ok (val, localsAfterRval) =>
          match writePlaceV2 mode localsAfterRval dst.localId dstTy val with
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

noncomputable def evalStatementV2 (mode : ProfileModeV2) (body : BodyV2)
    (frame : FrameState) (callerMem : CallerMemory)
    (stmt : StatementKindV2) : StepResultV2 State TerminalOut :=
  match stmt with
  | .v1 s => evalV1StatementInV2 mode body frame callerMem s
  | .placeMention p =>
    match evalPlaceMentionV2 body frame callerMem p with
    | .ok () =>
      .step {
        frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }]
        callerMem
      }
    | .error k => .fault k
  | .assume cond =>
    match evalPrimitiveOperand body.locals frame.locals cond with
    | .error k => .fault (FaultKindV2.ofV1 k)
    | .ok (.bool true, locals') =>
      .step {
        frames := [{
          frame with
          stmtIdx := frame.stmtIdx + 1
          locals := locals'
        }]
        callerMem
      }
    | .ok (.bool false, _) => .fault .unreachableExecuted
    | .ok (_, _) => .fault .unsupported

noncomputable def evalTerminatorV2 (body : BodyV2) (bb : BasicBlockV2)
    (frame : FrameState) (callerMem : CallerMemory) :
    StepResultV2 State TerminalOut :=
  match bb.terminator with
  | .goto target =>
    .step {
      frames := [{ frame with blockIdx := target, stmtIdx := 0 }]
      callerMem
    }
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    else
      match Trusted.MirSemantics.getElem? frame.locals 0 with
      | some (.live (some retVal)) =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some (.live none) | some .dead => .fault .undefined
      | none => .fault .unsupported
  | .unreachable =>
    .fault .unreachableExecuted
  | .switchInt discr targets =>
    match evalPrimitiveOperand body.locals frame.locals discr with
    | .error k => .fault (FaultKindV2.ofV1 k)
    | .ok (discrVal, localsAfterDiscr) =>
      let targetRes : Except FaultKind BasicBlockId :=
        match discrVal with
        | .scalar sv =>
          evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches
        | .bool b =>
          evalBoolSwitchBranches b targets.otherwise targets.branches
        | _ => .error .unsupported
      match targetRes with
      | .error k => .fault (FaultKindV2.ofV1 k)
      | .ok target =>
        .step {
          frames := [{
            frame with
            blockIdx := target
            stmtIdx := 0
            locals := localsAfterDiscr
          }]
          callerMem
        }
  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>
    .fault .unsupported

/-- Single-step operational evaluator for `MirProfileV2`. -/
noncomputable def evalStepV2 (p : ProgramV2) (_c : Choice) (s : State) :
    StepResultV2 State TerminalOut :=
  match s.frames with
  | [frame] =>
    match Trusted.MirSemantics.getElem? p.bodies frame.defId with
    | none => .fault .unsupported
    | some body =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some stmt => evalStatementV2 p.profileMode body frame s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminatorV2 body bb frame s.callerMem
          else
            .fault .unsupported
  | _ => .fault .unsupported

/-- Deterministic fuel-indexed multi-step evaluator for `MirProfileV2`. -/
noncomputable def evalBodyV2 (p : ProgramV2) :
    Nat → State → StepResultV2 State TerminalOut
  | 0, s => .step s
  | fuel + 1, s =>
    match evalStepV2 p 0 s with
    | .step s' => evalBodyV2 p fuel s'
    | .done out => .done out
    | .fault k => .fault k

noncomputable def ValidChoiceV2 (_p : ProgramV2) (_s : State)
    (c : Choice) : Prop :=
  c = 0

noncomputable def StepV2 (p : ProgramV2) (s : State)
    (res : StepResultV2 State TerminalOut) : Prop :=
  ∃ c : Choice, ValidChoiceV2 p s c ∧ evalStepV2 p c s = res

inductive ReachesV2 (p : ProgramV2) : State → State → Prop where
  | refl (s : State) : ReachesV2 p s s
  | tail {s₁ s₂ s₃ : State} :
      ReachesV2 p s₁ s₂ →
      StepV2 p s₂ (.step s₃) →
      ReachesV2 p s₁ s₃

noncomputable def ReachesResultV2 (p : ProgramV2) (q : Query)
    (res : StepResultV2 State TerminalOut) : Prop :=
  match initStateV2 p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : State, ReachesV2 p s₀ s ∧ StepV2 p s res

noncomputable def WellFormedV2 (p : ProgramV2) (q : Query) : Prop :=
  (∃ s₀ : State, initStateV2 p q = .ok s₀ ∧
    ∀ s : State, ReachesV2 p s₀ s → ∃ c : Choice, ValidChoiceV2 p s c) ∧
  (∀ k : FaultKindV2, ¬ ReachesResultV2 p q (.fault k))

noncomputable def BehaviorV2 (p : ProgramV2) (q : Query)
    (out : TerminalOut) : Prop :=
  ReachesResultV2 p q (.done out)

noncomputable def DivergesV2 (p : ProgramV2) (q : Query) : Prop :=
  ∃ s₀ : State,
    initStateV2 p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧
      ∀ n : Nat, StepV2 p (trace n) (.step (trace (n + 1)))

noncomputable def SatisfiesPostV2 (p : ProgramV2) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  WellFormedV2 p q ∧ ∀ out : TerminalOut, BehaviorV2 p q out → post out

noncomputable def entryProgForBodyV2 (p : ProgramV2)
    (defId : DefId) : ProgramV2 :=
  { p with entryDefId := defId }

noncomputable def ValidEntryArgsV2 (mode : ProfileModeV2) (body : BodyV2)
    (args : List Val) : Prop :=
  checkArgsMatchForMode mode args
    ((body.locals.drop 1).take body.argumentCount) = true

noncomputable def BodyStaticAdmittedV2 (p : ProgramV2) (body : BodyV2) : Bool :=
  let versionOk :=
    match p.profileMode with
    | .v1Embedded => Nat.beq p.mirProfileVersion 1
    | .v2Extended => Nat.beq p.mirProfileVersion 2
  let tyPred :=
    match p.profileMode with
    | .v1Embedded => isSupportedScalarOrUnitTy
    | .v2Extended => isSupportedProfileV2Ty
  Nat.beq p.pointerWidthBits 64 &&
    versionOk &&
    !stringBeq body.identity "" &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBoundsV2 body &&
    body.locals.all tyPred

noncomputable def BodyVerifiedV2 (p : ProgramV2) (defId : DefId) (body : BodyV2)
    (safetyPre : List Val → Prop) : Prop :=
  Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
  BodyStaticAdmittedV2 p body = true ∧
  ∀ args : List Val,
    ValidEntryArgsV2 p.profileMode body args →
    (body.isUnsafe = true → safetyPre args) →
    WellFormedV2 (entryProgForBodyV2 p defId) { args := args }

/-- Bundled bidirectional operational and verification equivalence in
`MirProfileV2`. -/
noncomputable def FullSemanticEquivV2 (pSrc pTgt : ProgramV2) : Prop :=
  (∀ q : Query,
    (WellFormedV2 pTgt q ↔ WellFormedV2 pSrc q) ∧
    (∀ out : TerminalOut, BehaviorV2 pTgt q out ↔ BehaviorV2 pSrc q out) ∧
    (∀ k : FaultKindV2,
      ReachesResultV2 pTgt q (.fault k) ↔ ReachesResultV2 pSrc q (.fault k)) ∧
    (DivergesV2 pTgt q ↔ DivergesV2 pSrc q)) ∧
  (∀ (q : Query) (post : TerminalOut → Prop),
    SatisfiesPostV2 pTgt q post ↔ SatisfiesPostV2 pSrc q post) ∧
  (∀ (defId : DefId) (bSrc bTgt : BodyV2) (safetyPre : List Val → Prop),
    Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
    Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
    (BodyVerifiedV2 pTgt defId bTgt safetyPre ↔
      BodyVerifiedV2 pSrc defId bSrc safetyPre))

/-! ### Certified `E3-22` `RemovePlaceMention` & `E3-16` `UnreachablePropagation` Checkers -/

noncomputable def initAbsSlotV2 (body : BodyV2) (idx : Nat)
    (ty : MirTy) : AbsSlot :=
  if Nat.beq idx 0 then
    if isAlwaysInhabitedZst ty then .liveInit else .liveUninit
  else if Nat.ble idx body.argumentCount then
    .liveInit
  else if hasStorageAnnotationV2 body idx then
    .dead
  else if isAlwaysInhabitedZst ty then
    .liveInit
  else
    .liveUninit

noncomputable def initAbsEnvLoopV2 (body : BodyV2) :
    Nat → List MirTy → List AbsSlot
  | _, [] => []
  | idx, ty :: rest =>
    initAbsSlotV2 body idx ty :: initAbsEnvLoopV2 body (idx + 1) rest

noncomputable def stepPlainStmtAbsV2 (bodyLocals : List MirTy)
    (env : List AbsSlot) : StatementKindV2 → Option (List AbsSlot)
  | .v1 s => stepPlainStmtAbs bodyLocals env s
  | .placeMention _ => some env
  | .assume cond => some (deinitMoveOperandAbs bodyLocals env cond)

noncomputable def stepPlainStmtsAbsV2 (bodyLocals : List MirTy) :
    List AbsSlot → List StatementKindV2 → Option (List AbsSlot)
  | env, [] => some env
  | env, s :: ss =>
    match stepPlainStmtAbsV2 bodyLocals env s with
    | none => none
    | some env' => stepPlainStmtsAbsV2 bodyLocals env' ss

noncomputable def preservesAllStorageAnnotationsLoopV2 (bSrc bTgt : BodyV2) :
    Nat → Bool
  | 0 => true
  | idx + 1 =>
    (hasStorageAnnotationV2 bSrc idx == hasStorageAnnotationV2 bTgt idx) &&
      preservesAllStorageAnnotationsLoopV2 bSrc bTgt idx

noncomputable def preservesAllStorageAnnotationsV2
    (bSrc bTgt : BodyV2) : Bool :=
  (storageAnnotationsInBoundsV2 bSrc == storageAnnotationsInBoundsV2 bTgt) &&
    preservesAllStorageAnnotationsLoopV2 bSrc bTgt bSrc.locals.length

/-- Syntactic `RemovePlaceMention` statement relation: erases safe
`StatementKindV2.placeMention p` (`isSafePlaceMention p = true`) to `.v1 .nop`
or preserves statements via `stmtV2Eq`. -/
noncomputable def isRemovePlaceMentionStmt
    (sSrc sTgt : StatementKindV2) : Bool :=
  stmtV2Eq sSrc sTgt ||
    match sSrc, sTgt with
    | .placeMention p, .v1 .nop => isSafePlaceMention p
    | _, _ => false

noncomputable def isRemovePlaceMentionBlock
    (b₁ b₂ : BasicBlockV2) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel isRemovePlaceMentionStmt b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isRemovePlaceMentionBody (b₁ b₂ : BodyV2) : Bool :=
  bodyHeaderV2Eq b₁ b₂ &&
    listRel isRemovePlaceMentionBlock b₁.basicBlocks b₂.basicBlocks

noncomputable def isRemovePlaceMentionProgram
    (pSrc pTgt : ProgramV2) : Bool :=
  programHeaderV2Eq pSrc pTgt &&
    profileModeEq pSrc.profileMode .v2Extended &&
    listRel isRemovePlaceMentionBody pSrc.bodies pTgt.bodies

noncomputable def placeMentionCertifiedInEnv (bodyLocals : List MirTy)
    (env : List AbsSlot) (p : PlaceV2) : Bool :=
  isSafePlaceMention p &&
    match p with
    | .local localId =>
      match Trusted.MirSemantics.getElem? bodyLocals localId,
          Trusted.MirSemantics.getElem? env localId with
      | some _, some slot => absSlotImplies slot .liveUninit
      | _, _ => false
    | .rawDeref ptrLocal | .rawDerefFieldOffset ptrLocal _ =>
      match Trusted.MirSemantics.getElem? bodyLocals ptrLocal,
          Trusted.MirSemantics.getElem? env ptrLocal with
      | some (.rawPtr _ pointee), some .liveInit =>
        isSupportedProfileV2Ty pointee
      | _, _ => false

noncomputable def stepRemovePlaceMentionCertStmts (bodyLocals : List MirTy) :
    List AbsSlot → List StatementKindV2 → List StatementKindV2 →
    Option (List AbsSlot)
  | env, [], [] => some env
  | env, sSrc :: restSrc, sTgt :: restTgt =>
    let okHere : Bool :=
      match sSrc, sTgt with
      | .placeMention p, .v1 .nop =>
        placeMentionCertifiedInEnv bodyLocals env p
      | _, _ => stmtV2Eq sSrc sTgt
    if !okHere then
      none
    else
      match stepPlainStmtAbsV2 bodyLocals env sSrc with
      | none => none
      | some env' =>
        stepRemovePlaceMentionCertStmts bodyLocals env' restSrc restTgt
  | _, _, _ => none

noncomputable def checkRemovePlaceMentionBlocks (bSrc bTgt : BodyV2)
    (cert : BodyAbsCert) : Nat → List BasicBlockV2 → Bool
  | _, [] => true
  | bbIdx, bbSrc :: rest =>
    let okBlock : Bool :=
      match Trusted.MirSemantics.getElem? cert bbIdx,
          Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
      | some none, some bbTgt => blockV2Eq bbSrc bbTgt
      | some (some entryEnv), some bbTgt =>
        Nat.beq entryEnv.length bSrc.locals.length &&
          (bbSrc.cleanup == bbTgt.cleanup) &&
          terminatorEq bbSrc.terminator bbTgt.terminator &&
          match stepRemovePlaceMentionCertStmts bSrc.locals entryEnv
              bbSrc.statements bbTgt.statements with
          | none => false
          | some exitEnv =>
            checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
              cert exitEnv bbSrc.terminator
      | _, _ => false
    okBlock && checkRemovePlaceMentionBlocks bSrc bTgt cert (bbIdx + 1) rest

noncomputable def checkRemovePlaceMentionBody (cert : BodyAbsCert)
    (bSrc bTgt : BodyV2) : Bool :=
  bodyHeaderV2Eq bSrc bTgt &&
    preservesAllStorageAnnotationsV2 bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    Nat.beq bSrc.basicBlocks.length bTgt.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         absEnvImplies (initAbsEnvLoopV2 bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkRemovePlaceMentionBlocks bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkRemovePlaceMentionProgram (cert : ProgramAbsCert)
    (pSrc pTgt : ProgramV2) : Bool :=
  isRemovePlaceMentionProgram pSrc pTgt &&
    Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkRemovePlaceMentionBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-- Match an `UnreachablePropagation` rewrite at block `bbIdx` (`E3-16`,
`compiler/rustc_mir_transform/src/unreachable_prop.rs`):
`bbSrc = { stmts, SwitchInt(op) [0 -> bbUnreach, otherwise -> bbNext] }`
(where `bSrc.basicBlocks[bbUnreach]` is an empty `.unreachable` block) rewritten
to `bbTgt = { stmts ++ [.assume op], Goto bbNext }`, returning `some op`. -/
noncomputable def matchSwitchBoolToAssumeAt? (bSrc : BodyV2)
    (bbIdx : BasicBlockId) (bbSrc bbTgt : BasicBlockV2) : Option Operand :=
  if !(bbSrc.cleanup == bbTgt.cleanup) then
    none
  else
    match bbSrc.terminator, bbTgt.terminator with
    | .switchInt op { branches := [(caseBits, bbUnreach)], otherwise := bbNext },
        .goto gotoNext =>
      if !(caseBits == BitVec.ofNat 128 0 &&
            Nat.beq bbNext gotoNext &&
            !Nat.beq bbUnreach bbIdx) then
        none
      else
        match Trusted.MirSemantics.getElem? bSrc.basicBlocks bbUnreach with
        | some blkUnreach =>
          if blkUnreach.statements.isEmpty &&
              terminatorEq blkUnreach.terminator .unreachable &&
              listRel stmtV2Eq (bbSrc.statements ++ [.assume op])
                bbTgt.statements then
            some op
          else
            none
        | none => none
    | _, _ => none

noncomputable def isUnreachablePropAssumeBlocks (bSrc : BodyV2) :
    Nat → List BasicBlockV2 → List BasicBlockV2 → Bool
  | _, [], [] => true
  | bbIdx, bbSrc :: restSrc, bbTgt :: restTgt =>
    let okHere :=
      blockV2Eq bbSrc bbTgt ||
        match matchSwitchBoolToAssumeAt? bSrc bbIdx bbSrc bbTgt with
        | some _ => true
        | none => false
    okHere &&
      isUnreachablePropAssumeBlocks bSrc (bbIdx + 1) restSrc restTgt
  | _, _, _ => false

noncomputable def isUnreachablePropAssumeBody (bSrc bTgt : BodyV2) : Bool :=
  bodyHeaderV2Eq bSrc bTgt &&
    isUnreachablePropAssumeBlocks bSrc 0 bSrc.basicBlocks bTgt.basicBlocks

noncomputable def isUnreachablePropAssumeProgram
    (pSrc pTgt : ProgramV2) : Bool :=
  programHeaderV2Eq pSrc pTgt &&
    listRel isUnreachablePropAssumeBody pSrc.bodies pTgt.bodies

noncomputable def operandCertifiedBoolInEnv (bodyLocals : List MirTy)
    (env : List AbsSlot) : Operand → Bool
  | .constant c => MirTy.beq c.ty .bool
  | .copy p | .move p =>
    p.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some .bool, some slot => absSlotImplies slot .liveUninit
      | _, _ => false

noncomputable def checkUnreachablePropAssumeBlocks (bSrc bTgt : BodyV2)
    (cert : BodyAbsCert) : Nat → List BasicBlockV2 → Bool
  | _, [] => true
  | bbIdx, bbSrc :: rest =>
    let okBlock : Bool :=
      match Trusted.MirSemantics.getElem? cert bbIdx,
          Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
      | some none, some bbTgt => blockV2Eq bbSrc bbTgt
      | some (some entryEnv), some bbTgt =>
        Nat.beq entryEnv.length bSrc.locals.length &&
          match stepPlainStmtsAbsV2 bSrc.locals entryEnv bbSrc.statements with
          | none => false
          | some exitEnv =>
            checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
              cert exitEnv bbSrc.terminator &&
              (blockV2Eq bbSrc bbTgt ||
                match matchSwitchBoolToAssumeAt? bSrc bbIdx bbSrc bbTgt with
                | some op => operandCertifiedBoolInEnv bSrc.locals exitEnv op
                | none => false)
      | _, _ => false
    okBlock && checkUnreachablePropAssumeBlocks bSrc bTgt cert (bbIdx + 1) rest

noncomputable def checkUnreachablePropAssumeBody (cert : BodyAbsCert)
    (bSrc bTgt : BodyV2) : Bool :=
  bodyHeaderV2Eq bSrc bTgt &&
    preservesAllStorageAnnotationsV2 bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    Nat.beq bSrc.basicBlocks.length bTgt.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         absEnvImplies (initAbsEnvLoopV2 bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkUnreachablePropAssumeBlocks bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkUnreachablePropAssumeProgram (cert : ProgramAbsCert)
    (pSrc pTgt : ProgramV2) : Bool :=
  isUnreachablePropAssumeProgram pSrc pTgt &&
    Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkUnreachablePropAssumeBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Stage 4 Private Helpers — Layer A: Reflection, List, & AST Equality -/

private theorem if_bool_true {α : Type} {c : Bool} {t e : α} (h : c = true) :
    (if c then t else e) = t := by
  rw [h]; rfl

private theorem if_bool_false {α : Type} {c : Bool} {t e : α} (h : c = false) :
    (if c then t else e) = e := by
  rw [h]; rfl

private theorem ite_prop_true {α : Type} {P : Prop} {inst : Decidable P}
    {t e : α} (h : P) : (@ite α P inst t e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

private theorem ite_prop_false {α : Type} {P : Prop} {inst : Decidable P}
    {t e : α} (h : ¬ P) : (@ite α P inst t e) = e := by
  cases inst with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

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
    | succ m => rw [ih h]

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

private theorem nat_beq_symm (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  cases h : Nat.beq a b with
  | true => rw [nat_beq_eq h]; exact (nat_beq_refl _).symm
  | false =>
    exact (nat_beq_false_of_ne (fun hEq => nat_ne_of_beq_false h hEq.symm)).symm

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
    rw [nat_lt_blt hlt] at h
    cases h
  | inr hge => exact hge

private theorem nat_ge_blt_false {a b : Nat} (h : b ≤ a) :
    Nat.blt a b = false := by
  cases hB : Nat.blt a b with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge h (nat_blt_lt hB))

private theorem natElem_mem {x : Nat} {ys : List Nat} (h : natElem x ys = true) :
    x ∈ ys := by
  induction ys with
  | nil => cases h
  | cons y rest ih =>
    dsimp [natElem] at h
    cases bool_or_true h with
    | inl hEq =>
      rw [nat_beq_eq hEq]
      exact List.Mem.head rest
    | inr hRest =>
      exact List.Mem.tail y (ih hRest)

private theorem list_all_mem_true {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (hAll : xs.all p = true) (hMem : x ∈ xs) : p x = true := by
  induction hMem with
  | head rest => exact (bool_and_true hAll).1
  | tail _ _ ih => exact ih (bool_and_true hAll).2

private theorem list_any_false_forall {α : Type} {p : α → Bool} {xs : List α}
    (hAny : xs.any p = false) : ∀ x, x ∈ xs → p x = false := by
  induction xs with
  | nil => intro _ hMem; cases hMem
  | cons a rest ih =>
    dsimp [List.any] at hAny
    let ⟨ha, hRest⟩ := bool_or_false hAny
    intro x hMem
    cases hMem with
    | head _ => exact ha
    | tail _ hM => exact ih hRest x hM

private theorem bitvec_beq_eq {n : Nat} {a b : BitVec n}
    (h : (a == b) = true) : a = b :=
  eq_of_beq h

private theorem bitvec_beq_refl {n : Nat} (x : BitVec n) : (x == x) = true :=
  decide_eq_true rfl

private theorem bitvec_eq_of_toNat_eq {n : Nat} {a b : BitVec n}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

private theorem uint8_beq_eq {a b : UInt8} (h : (a == b) = true) : a = b :=
  eq_of_beq h

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

private theorem listRel_mono {α β : Type} {r₁ r₂ : α → β → Bool}
    (hImp : ∀ x y, r₁ x y = true → r₂ x y = true)
    {xs : List α} {ys : List β} (hRel : listRel r₁ xs ys = true) :
    listRel r₂ xs ys = true := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons a xs ih =>
    cases ys with
    | nil => cases hRel
    | cons b ys =>
      let ⟨h1, h2⟩ := bool_and_true hRel
      exact bool_and_intro (hImp a b h1) (ih h2)

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
    (hEq : ∀ x y, r x y = true → x = y) {xs : List α} {ys : List α}
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
  | cons x xs ih =>
    cases ys with
    | nil => cases hLen
    | cons y ys =>
      have h0 := hAt 0
      dsimp [Trusted.MirSemantics.getElem?] at h0
      injection h0 with hxy
      subst hxy
      rw [ih (Nat.succ.inj hLen) (fun i => hAt (i + 1))]

private theorem setElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : setElem? xs i v = some xs') : xs'.length = xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons a xs ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? xs k v with
      | none => rw [hSub] at h; cases h
      | some sub =>
        rw [hSub] at h
        injection h with hEq; subst hEq
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
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? xs k v with
      | none => rw [hSub] at h; cases h
      | some sub =>
        rw [hSub] at h
        injection h with hEq; subst hEq
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
      injection h with hEq; subst hEq
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ _ => rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? xs k v with
      | none => rw [hSub] at h; cases h
      | some sub =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        cases j with
        | zero => rfl
        | succ m => exact ih hSub (fun hEq => hNe (by rw [hEq]))

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

private theorem drop_zero_eq {α : Type} (xs : List α) : xs.drop 0 = xs := rfl

private theorem drop_eq_cons_of_getElem? {α : Type} {xs : List α} {n : Nat} {x : α}
    (h : Trusted.MirSemantics.getElem? xs n = some x) :
    xs.drop n = x :: xs.drop (n + 1) := by
  induction xs generalizing n with
  | nil => cases h
  | cons a xs ih =>
    cases n with
    | zero =>
      injection h with hxa; subst hxa; rfl
    | succ _ => exact ih h

private theorem getElem?_of_drop_eq_cons {α : Type} {xs rest : List α} {n : Nat} {x : α}
    (h : xs.drop n = x :: rest) :
    Trusted.MirSemantics.getElem? xs n = some x ∧ xs.drop (n + 1) = rest := by
  induction xs generalizing n with
  | nil => cases n <;> cases h
  | cons a xs ih =>
    cases n with
    | zero =>
      injection h with h1 h2
      subst h1; subst h2
      exact ⟨rfl, rfl⟩
    | succ _ => exact ih h

private theorem drop_eq_nil_of_ge {α : Type} {xs : List α} {n : Nat}
    (h : xs.length ≤ n) : xs.drop n = [] := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons _ xs ih =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero xs.length h)
    | succ k => exact ih (Nat.le_of_succ_le_succ h)

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

private theorem list_eq_nil_of_isEmpty {α : Type} {xs : List α}
    (h : xs.isEmpty = true) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons _ _ => cases h

private theorem list_pos_of_isEmpty_false {α : Type} {xs : List α}
    (h : xs.isEmpty = false) : 0 < xs.length := by
  cases xs with
  | nil => cases h
  | cons _ rest => exact Nat.zero_lt_succ rest.length

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
      | succ _ => exact ih h2 hTy

private theorem map_length_eq {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
    dsimp [List.map, List.length]
    rw [ih]

private theorem getElem?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    Trusted.MirSemantics.getElem? (xs.map f) i =
      (Trusted.MirSemantics.getElem? xs i).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

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
  | cons a xs ih =>
    cases ys with
    | nil => cases hRel
    | cons b ys =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      dsimp [List.map]
      rw [hFG a b hab, ih hTail]

private theorem listRel_zip_getElem? {α β γ : Type} {f : (α × β) → γ → Bool}
    {cs : List α} {xs : List β} {ys : List γ}
    (hLenC : cs.length = xs.length)
    (hRel : listRel f (List.zip cs xs) ys = true)
    {i : Nat} {x : β}
    (hX : Trusted.MirSemantics.getElem? xs i = some x) :
    ∃ c y,
      Trusted.MirSemantics.getElem? cs i = some c ∧
      Trusted.MirSemantics.getElem? ys i = some y ∧
      f (c, x) y = true := by
  induction xs generalizing cs ys i with
  | nil => cases hX
  | cons x₀ xs ih =>
    cases cs with
    | nil => cases hLenC
    | cons c₀ cs =>
      dsimp [List.zip] at hRel
      cases ys with
      | nil => cases hRel
      | cons y₀ ys =>
        let ⟨hHead, hTail⟩ := bool_and_true hRel
        have hLenTail : cs.length = xs.length := Nat.succ.inj hLenC
        cases i with
        | zero =>
          injection hX with hxEq; subst hxEq
          exact ⟨c₀, y₀, rfl, rfl, hHead⟩
        | succ _ =>
          dsimp [Trusted.MirSemantics.getElem?] at hX
          dsimp [Trusted.MirSemantics.getElem?]
          exact ih hLenTail hTail hX

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

private theorem rvalueEq_eq {a b : Rvalue}
    (h : rvalueEq a b = true) : a = b := by
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

private theorem stmtEq_eq {a b : StatementKind}
    (h : stmtEq a b = true) : a = b := by
  cases a with
  | assign d1 rv1 =>
    cases b with
    | assign d2 rv2 =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [placeEq_eq h1, rvalueEq_eq h2]
    | _ => cases h
  | storageLive i1 =>
    cases b with
    | storageLive i2 => rw [nat_beq_eq h]
    | _ => cases h
  | storageDead i1 =>
    cases b with
    | storageDead i2 => rw [nat_beq_eq h]
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
        | mk xv xt =>
          cases y with
          | mk yv yt =>
            dsimp at hxy
            let ⟨hv, ht⟩ := bool_and_true hxy
            rw [bitvec_beq_eq hv, nat_beq_eq ht]) h2
      rw [hOw, hBs]

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

private theorem terminatorEq_eq {a b : TerminatorKind}
    (h : terminatorEq a b = true) : a = b := by
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

private theorem programHeaderEq_entryProg {p₁ p₂ : Program} (defId : DefId)
    (h : programHeaderEq p₁ p₂ = true) :
    programHeaderEq (entryProgForBody p₁ defId)
      (entryProgForBody p₂ defId) = true := by
  let ⟨hPw, hVer, _, hSc⟩ := programHeaderEq_elim h
  unfold programHeaderEq entryProgForBody
  dsimp
  rw [hPw, hVer, hSc, nat_beq_refl, nat_beq_refl, nat_beq_refl, scopeEq_refl]
  rfl

/-! ### Stage 4 Private Helpers — Layer B: Simulation, Lockstep Bisimulation,
& `initState` -/

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

private theorem lockstep_inv_query_iff {pSrc pTgt : Program} {q : Query}
    {Inv : State → Prop}
    (hInitEq : initState pSrc q = initState pTgt q)
    (hInitInv : ∀ s₀, initState pSrc q = .ok s₀ → Inv s₀)
    (hStep : ∀ s, Inv s →
      evalStep pSrc 0 s = evalStep pTgt 0 s ∧
      (∀ s', evalStep pSrc 0 s = .step s' → Inv s')) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  cases hInitSrc : initState pSrc q with
  | error kErr =>
    have hInitTgt : initState pTgt q = .error kErr := by
      rw [← hInitEq]; exact hInitSrc
    refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitTgt] at hOk; cases hOk
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitSrc] at hOk; cases hOk
    · intro out; unfold Behavior ReachesResult; rw [hInitTgt, hInitSrc]
    · intro k; unfold ReachesResult; rw [hInitTgt, hInitSrc]
    · constructor
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitTgt] at hOk; cases hOk
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitSrc] at hOk; cases hOk
  | ok s₀ =>
    have hInitTgt : initState pTgt q = .ok s₀ := by
      rw [← hInitEq]; exact hInitSrc
    have hInv0 : Inv s₀ := hInitInv s₀ hInitSrc
    have hReachSrc : ∀ s, Reaches pSrc s₀ s → Reaches pTgt s₀ s ∧ Inv s := by
      intro s hR
      induction hR with
      | refl => exact ⟨Reaches.refl s₀, hInv0⟩
      | tail _ hSt ih =>
        let ⟨hRt, hInvS⟩ := ih
        have hEvS := step_iff_evalStep.mp hSt
        let ⟨hEqEv, hNextInv⟩ := hStep _ hInvS
        have hEvT := hEqEv.symm.trans hEvS
        exact ⟨Reaches.tail hRt (step_iff_evalStep.mpr hEvT),
               hNextInv _ hEvS⟩
    have hReachTgt : ∀ s, Reaches pTgt s₀ s → Reaches pSrc s₀ s ∧ Inv s := by
      intro s hR
      induction hR with
      | refl => exact ⟨Reaches.refl s₀, hInv0⟩
      | tail _ hSt ih =>
        let ⟨hRs, hInvS⟩ := ih
        have hEvT := step_iff_evalStep.mp hSt
        let ⟨hEqEv, hNextInv⟩ := hStep _ hInvS
        have hEvS := hEqEv.trans hEvT
        exact ⟨Reaches.tail hRs (step_iff_evalStep.mpr hEvS),
               hNextInv _ hEvS⟩
    have hResIff : ∀ res, ReachesResult pTgt q res ↔ ReachesResult pSrc q res := by
      intro res
      unfold ReachesResult
      rw [hInitTgt, hInitSrc]
      constructor
      · intro h
        let ⟨s, hRt, hStT⟩ := h
        let ⟨hRs, hInvS⟩ := hReachTgt s hRt
        have hEvS : evalStep pSrc 0 s = res := by
          rw [(hStep s hInvS).1]; exact step_iff_evalStep.mp hStT
        exact ⟨s, hRs, step_iff_evalStep.mpr hEvS⟩
      · intro h
        let ⟨s, hRs, hStS⟩ := h
        let ⟨hRt, hInvS⟩ := hReachSrc s hRs
        have hEvT : evalStep pTgt 0 s = res := by
          rw [← (hStep s hInvS).1]; exact step_iff_evalStep.mp hStS
        exact ⟨s, hRt, step_iff_evalStep.mpr hEvT⟩
    refine ⟨?_, fun out => hResIff (.done out), fun k => hResIff (.fault k), ?_⟩
    · constructor
      · intro hW
        exact ⟨⟨s₀, hInitSrc, fun _ _ => ⟨0, rfl⟩⟩,
               fun fk hF => hW.2 fk ((hResIff (.fault fk)).mpr hF)⟩
      · intro hW
        exact ⟨⟨s₀, hInitTgt, fun _ _ => ⟨0, rfl⟩⟩,
               fun fk hF => hW.2 fk ((hResIff (.fault fk)).mp hF)⟩
    · constructor
      · intro hDivT
        let ⟨t₀, hOkT, tr, h0, hSt⟩ := hDivT
        rw [hInitTgt] at hOkT; injection hOkT with hEqT; subst hEqT
        have hTrInv : ∀ n, Inv (tr n) := by
          intro n
          induction n with
          | zero => rw [h0]; exact hInv0
          | succ m ih =>
            have hEvT := step_iff_evalStep.mp (hSt m)
            have hEvS : evalStep pSrc 0 (tr m) = .step (tr (m + 1)) := by
              rw [(hStep (tr m) ih).1]; exact hEvT
            exact (hStep (tr m) ih).2 (tr (m + 1)) hEvS
        refine ⟨s₀, hInitSrc, tr, h0, fun n => step_iff_evalStep.mpr ?_⟩
        rw [(hStep (tr n) (hTrInv n)).1]
        exact step_iff_evalStep.mp (hSt n)
      · intro hDivS
        let ⟨s₀', hOkS, tr, h0, hSt⟩ := hDivS
        rw [hInitSrc] at hOkS; injection hOkS with hEqS; subst hEqS
        have hTrInv : ∀ n, Inv (tr n) := by
          intro n
          induction n with
          | zero => rw [h0]; exact hInv0
          | succ m ih =>
            have hEvS := step_iff_evalStep.mp (hSt m)
            exact (hStep (tr m) ih).2 (tr (m + 1)) hEvS
        refine ⟨s₀, hInitTgt, tr, h0, fun n => step_iff_evalStep.mpr ?_⟩
        rw [← (hStep (tr n) (hTrInv n)).1]
        exact step_iff_evalStep.mp (hSt n)

private noncomputable def StepOutcomeBisim (pSrc pTgt : Program)
    (R : State → State → Prop) (s t : State) : Prop :=
  (∃ s' t',
    evalStep pSrc 0 s = .step s' ∧
    evalStep pTgt 0 t = .step t' ∧
    R s' t') ∨
  (∃ out,
    evalStep pSrc 0 s = .done out ∧
    evalStep pTgt 0 t = .done out) ∨
  (∃ fk,
    evalStep pSrc 0 s = .fault fk ∧
    evalStep pTgt 0 t = .fault fk)

private theorem bisim_lockstep_query_iff {pSrc pTgt : Program} {q : Query}
    {R : State → State → Prop}
    (hInitEq : initState pSrc q = initState pTgt q)
    (hInitRel : ∀ s₀, initState pSrc q = .ok s₀ → R s₀ s₀)
    (hStep : ∀ s t, R s t → StepOutcomeBisim pSrc pTgt R s t) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  cases hInitSrc : initState pSrc q with
  | error kErr =>
    have hInitTgt : initState pTgt q = .error kErr := by
      rw [← hInitEq]; exact hInitSrc
    refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitTgt] at hOk; cases hOk
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitSrc] at hOk; cases hOk
    · intro out; unfold Behavior ReachesResult; rw [hInitTgt, hInitSrc]
    · intro k; unfold ReachesResult; rw [hInitTgt, hInitSrc]
    · constructor
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitTgt] at hOk; cases hOk
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitSrc] at hOk; cases hOk
  | ok s₀ =>
    have hInitTgt : initState pTgt q = .ok s₀ := by
      rw [← hInitEq]; exact hInitSrc
    have hR0 : R s₀ s₀ := hInitRel s₀ hInitSrc
    have hStepSrc : ∀ s t s', R s t → evalStep pSrc 0 s = .step s' →
        ∃ t', evalStep pTgt 0 t = .step t' ∧ R s' t' := by
      intro s t s' hR hEvS
      cases hStep s t hR with
      | inl h1 =>
        let ⟨s1, t1, hS1, hT1, hR1⟩ := h1
        rw [hEvS] at hS1; injection hS1 with hEq; subst hEq
        exact ⟨t1, hT1, hR1⟩
      | inr h23 =>
        cases h23 with
        | inl h2 =>
          let ⟨_, hS2, _⟩ := h2; rw [hEvS] at hS2; cases hS2
        | inr h3 =>
          let ⟨_, hS3, _⟩ := h3; rw [hEvS] at hS3; cases hS3
    have hStepTgt : ∀ s t t', R s t → evalStep pTgt 0 t = .step t' →
        ∃ s', evalStep pSrc 0 s = .step s' ∧ R s' t' := by
      intro s t t' hR hEvT
      cases hStep s t hR with
      | inl h1 =>
        let ⟨s1, t1, hS1, hT1, hR1⟩ := h1
        rw [hEvT] at hT1; injection hT1 with hEq; subst hEq
        exact ⟨s1, hS1, hR1⟩
      | inr h23 =>
        cases h23 with
        | inl h2 =>
          let ⟨_, _, hT2⟩ := h2; rw [hEvT] at hT2; cases hT2
        | inr h3 =>
          let ⟨_, _, hT3⟩ := h3; rw [hEvT] at hT3; cases hT3
    have hReachSrc : ∀ s, Reaches pSrc s₀ s → ∃ t, Reaches pTgt s₀ t ∧ R s t := by
      intro s hRs
      induction hRs with
      | refl => exact ⟨s₀, Reaches.refl s₀, hR0⟩
      | tail _ hSt ih =>
        let ⟨t, hRt, hRst⟩ := ih
        let ⟨t', hEvT, hR'⟩ := hStepSrc _ t _ hRst (step_iff_evalStep.mp hSt)
        exact ⟨t', Reaches.tail hRt (step_iff_evalStep.mpr hEvT), hR'⟩
    have hReachTgt : ∀ t, Reaches pTgt s₀ t → ∃ s, Reaches pSrc s₀ s ∧ R s t := by
      intro t hRt
      induction hRt with
      | refl => exact ⟨s₀, Reaches.refl s₀, hR0⟩
      | tail _ hSt ih =>
        let ⟨s, hRs, hRst⟩ := ih
        let ⟨s', hEvS, hR'⟩ := hStepTgt s _ _ hRst (step_iff_evalStep.mp hSt)
        exact ⟨s', Reaches.tail hRs (step_iff_evalStep.mpr hEvS), hR'⟩
    have hDoneIff : ∀ out,
        ReachesResult pTgt q (.done out) ↔ ReachesResult pSrc q (.done out) := by
      intro out
      unfold ReachesResult; rw [hInitTgt, hInitSrc]
      constructor
      · intro ⟨t, hRt, hStT⟩
        let ⟨s, hRs, hRst⟩ := hReachTgt t hRt
        have hEvT := step_iff_evalStep.mp hStT
        cases hStep s t hRst with
        | inl h1 => let ⟨_, _, _, hT1, _⟩ := h1; rw [hEvT] at hT1; cases hT1
        | inr h23 =>
          cases h23 with
          | inl h2 =>
            let ⟨out', hS2, hT2⟩ := h2
            rw [hEvT] at hT2; injection hT2 with hEq; subst hEq
            exact ⟨s, hRs, step_iff_evalStep.mpr hS2⟩
          | inr h3 => let ⟨_, _, hT3⟩ := h3; rw [hEvT] at hT3; cases hT3
      · intro ⟨s, hRs, hStS⟩
        let ⟨t, hRt, hRst⟩ := hReachSrc s hRs
        have hEvS := step_iff_evalStep.mp hStS
        cases hStep s t hRst with
        | inl h1 => let ⟨_, _, hS1, _, _⟩ := h1; rw [hEvS] at hS1; cases hS1
        | inr h23 =>
          cases h23 with
          | inl h2 =>
            let ⟨out', hS2, hT2⟩ := h2
            rw [hEvS] at hS2; injection hS2 with hEq; subst hEq
            exact ⟨t, hRt, step_iff_evalStep.mpr hT2⟩
          | inr h3 => let ⟨_, hS3, _⟩ := h3; rw [hEvS] at hS3; cases hS3
    have hFaultIff : ∀ fk,
        ReachesResult pTgt q (.fault fk) ↔ ReachesResult pSrc q (.fault fk) := by
      intro fk
      unfold ReachesResult; rw [hInitTgt, hInitSrc]
      constructor
      · intro ⟨t, hRt, hStT⟩
        let ⟨s, hRs, hRst⟩ := hReachTgt t hRt
        have hEvT := step_iff_evalStep.mp hStT
        cases hStep s t hRst with
        | inl h1 => let ⟨_, _, _, hT1, _⟩ := h1; rw [hEvT] at hT1; cases hT1
        | inr h23 =>
          cases h23 with
          | inl h2 => let ⟨_, _, hT2⟩ := h2; rw [hEvT] at hT2; cases hT2
          | inr h3 =>
            let ⟨fk', hS3, hT3⟩ := h3
            rw [hEvT] at hT3; injection hT3 with hEq; subst hEq
            exact ⟨s, hRs, step_iff_evalStep.mpr hS3⟩
      · intro ⟨s, hRs, hStS⟩
        let ⟨t, hRt, hRst⟩ := hReachSrc s hRs
        have hEvS := step_iff_evalStep.mp hStS
        cases hStep s t hRst with
        | inl h1 => let ⟨_, _, hS1, _, _⟩ := h1; rw [hEvS] at hS1; cases hS1
        | inr h23 =>
          cases h23 with
          | inl h2 => let ⟨_, hS2, _⟩ := h2; rw [hEvS] at hS2; cases hS2
          | inr h3 =>
            let ⟨fk', hS3, hT3⟩ := h3
            rw [hEvS] at hS3; injection hS3 with hEq; subst hEq
            exact ⟨t, hRt, step_iff_evalStep.mpr hT3⟩
    refine ⟨?_, hDoneIff, hFaultIff, ?_⟩
    · constructor
      · intro hW
        exact ⟨⟨s₀, hInitSrc, fun _ _ => ⟨0, rfl⟩⟩,
               fun fk hF => hW.2 fk ((hFaultIff fk).mpr hF)⟩
      · intro hW
        exact ⟨⟨s₀, hInitTgt, fun _ _ => ⟨0, rfl⟩⟩,
               fun fk hF => hW.2 fk ((hFaultIff fk).mp hF)⟩
    · constructor
      · intro ⟨t₀, hOkT, trT, h0T, hStT⟩
        rw [hInitTgt] at hOkT; injection hOkT with hEqT; subst hEqT
        have hInv : ∀ n, R (iterState pSrc s₀ n) (trT n) := by
          intro n
          induction n with
          | zero => rw [h0T]; exact hR0
          | succ k ih =>
            let ⟨s', hEvS, hR'⟩ :=
              hStepTgt _ _ _ ih (step_iff_evalStep.mp (hStT k))
            dsimp [iterState]; rw [hEvS]; exact hR'
        refine ⟨s₀, hInitSrc, iterState pSrc s₀, rfl, fun n => ?_⟩
        let ⟨s', hEvS, _⟩ :=
          hStepTgt _ _ _ (hInv n) (step_iff_evalStep.mp (hStT n))
        apply step_iff_evalStep.mpr
        dsimp [iterState]; rw [hEvS]
      · intro ⟨s₀', hOkS, trS, h0S, hStS⟩
        rw [hInitSrc] at hOkS; injection hOkS with hEqS; subst hEqS
        have hInv : ∀ n, R (trS n) (iterState pTgt s₀ n) := by
          intro n
          induction n with
          | zero => rw [h0S]; exact hR0
          | succ k ih =>
            let ⟨t', hEvT, hR'⟩ :=
              hStepSrc _ _ _ ih (step_iff_evalStep.mp (hStS k))
            dsimp [iterState]; rw [hEvT]; exact hR'
        refine ⟨s₀, hInitTgt, iterState pTgt s₀, rfl, fun n => ?_⟩
        let ⟨t', hEvT, _⟩ :=
          hStepSrc _ _ _ (hInv n) (step_iff_evalStep.mp (hStS n))
        apply step_iff_evalStep.mpr
        dsimp [iterState]; rw [hEvT]

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
    let ⟨t', hEval2, hRel'⟩ := hStep _ _ _ hRel (step_iff_evalStep.mp hSt)
    exact ⟨t', Reaches.tail hRt (step_iff_evalStep.mpr hEval2), hRel'⟩

private theorem diverges_fwd_sim {p1 p2 : Program} {q : Query}
    {R : State → State → Prop} {s₀ t₀ : State}
    (hInit1 : initState p1 q = .ok s₀) (hInit2 : initState p2 q = .ok t₀)
    (hRel0 : R s₀ t₀)
    (hStep : ∀ a b a', R a b → evalStep p1 0 a = .step a' →
      ∃ b', evalStep p2 0 b = .step b' ∧ R a' b') :
    Diverges p1 q → Diverges p2 q := by
  intro ⟨s₀', hOk', trace1, hTr0, hTrStep⟩
  rw [hInit1] at hOk'; injection hOk' with hEqS; subst hEqS
  have hInv : ∀ n, R (trace1 n) (iterState p2 t₀ n) := by
    intro n
    induction n with
    | zero => rw [hTr0]; exact hRel0
    | succ k ih =>
      let ⟨b', hEval2, hRel'⟩ :=
        hStep _ _ _ ih (step_iff_evalStep.mp (hTrStep k))
      dsimp [iterState]; rw [hEval2]; exact hRel'
  refine ⟨t₀, hInit2, iterState p2 t₀, rfl, fun n => ?_⟩
  let ⟨_, hEval2, _⟩ :=
    hStep _ _ _ (hInv n) (step_iff_evalStep.mp (hTrStep n))
  apply step_iff_evalStep.mpr
  dsimp [iterState]; rw [hEval2]

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
    unfold ReachesResult; rw [hInitSrc]
    exact ⟨s, hRs, step_iff_evalStep.mpr hF⟩
  have hBackReach : ∀ t, Reaches pTgt t₀ t → ∃ s, Reaches pSrc s₀ s ∧ R s t := by
    intro t hRt
    induction hRt with
    | refl => exact ⟨s₀, Reaches.refl s₀, hRel0⟩
    | tail _ hStTgt ih =>
      let ⟨s, hRs, hRel⟩ := ih
      have hEvalTgt := step_iff_evalStep.mp hStTgt
      cases hEvalSrc : evalStep pSrc 0 s with
      | fault k => exact False.elim (hNoFaultAt s hRs k hEvalSrc)
      | done out =>
        rw [(hStep s _ hRel).2 out hEvalSrc] at hEvalTgt; cases hEvalTgt
      | step s' =>
        let ⟨t', hST, hRel'⟩ := (hStep s _ hRel).1 s' hEvalSrc
        rw [hST] at hEvalTgt; injection hEvalTgt with hEqT; subst hEqT
        exact ⟨s', Reaches.tail hRs (step_iff_evalStep.mpr hEvalSrc), hRel'⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨t₀, hInitTgt, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
    intro k hFaultTgt
    unfold ReachesResult at hFaultTgt; rw [hInitTgt] at hFaultTgt
    let ⟨t, hRt, hStTgt⟩ := hFaultTgt
    have hEvalTgt := step_iff_evalStep.mp hStTgt
    let ⟨s, hRs, hRel⟩ := hBackReach t hRt
    cases hEvalSrc : evalStep pSrc 0 s with
    | fault k' => exact hNoFaultAt s hRs k' hEvalSrc
    | done out => rw [(hStep s t hRel).2 out hEvalSrc] at hEvalTgt; cases hEvalTgt
    | step s' =>
      let ⟨_, hST, _⟩ := (hStep s t hRel).1 s' hEvalSrc
      rw [hST] at hEvalTgt; cases hEvalTgt
  · intro out
    constructor
    · intro hBehTgt
      unfold Behavior ReachesResult at hBehTgt; rw [hInitTgt] at hBehTgt
      let ⟨t, hRt, hStTgt⟩ := hBehTgt
      have hEvalTgt := step_iff_evalStep.mp hStTgt
      let ⟨s, hRs, hRel⟩ := hBackReach t hRt
      cases hEvalSrc : evalStep pSrc 0 s with
      | fault k => exact False.elim (hNoFaultAt s hRs k hEvalSrc)
      | step s' =>
        let ⟨_, hST, _⟩ := (hStep s t hRel).1 s' hEvalSrc
        rw [hST] at hEvalTgt; cases hEvalTgt
      | done out' =>
        rw [(hStep s t hRel).2 out' hEvalSrc] at hEvalTgt
        injection hEvalTgt with hEqO; subst hEqO
        unfold Behavior ReachesResult; rw [hInitSrc]
        exact ⟨s, hRs, step_iff_evalStep.mpr hEvalSrc⟩
    · intro hBehSrc
      unfold Behavior ReachesResult at hBehSrc; rw [hInitSrc] at hBehSrc
      let ⟨s, hRs, hStSrc⟩ := hBehSrc
      have hEvalSrc := step_iff_evalStep.mp hStSrc
      let ⟨t, hRt, hRel⟩ :=
        reaches_fwd_sim (fun a b a' hr hs => (hStep a b hr).1 a' hs) hRel0 hRs
      unfold Behavior ReachesResult; rw [hInitTgt]
      exact ⟨t, hRt, step_iff_evalStep.mpr ((hStep s t hRel).2 out hEvalSrc)⟩
  · constructor
    · intro ⟨t₀', hOk', traceTgt, hTr0, hTrStep⟩
      rw [hInitTgt] at hOk'; injection hOk' with hEqT; subst hEqT
      have hInv : ∀ n, Reaches pSrc s₀ (iterState pSrc s₀ n) ∧
          R (iterState pSrc s₀ n) (traceTgt n) := by
        intro n
        induction n with
        | zero => rw [hTr0]; exact ⟨Reaches.refl s₀, hRel0⟩
        | succ k ih =>
          let ⟨hRs, hRel⟩ := ih
          have hEvalTgt := step_iff_evalStep.mp (hTrStep k)
          cases hEvalSrc : evalStep pSrc 0 (iterState pSrc s₀ k) with
          | fault fk => exact False.elim (hNoFaultAt _ hRs fk hEvalSrc)
          | done out =>
            rw [(hStep _ _ hRel).2 out hEvalSrc] at hEvalTgt; cases hEvalTgt
          | step s' =>
            let ⟨t', hST, hRel'⟩ := (hStep _ _ hRel).1 s' hEvalSrc
            rw [hST] at hEvalTgt; injection hEvalTgt with hEqT'; subst hEqT'
            dsimp [iterState]; rw [hEvalSrc]
            exact ⟨Reaches.tail hRs (step_iff_evalStep.mpr hEvalSrc), hRel'⟩
      refine ⟨s₀, hInitSrc, iterState pSrc s₀, rfl, fun n => ?_⟩
      let ⟨hRs, hRel⟩ := hInv n
      have hEvalTgt := step_iff_evalStep.mp (hTrStep n)
      cases hEvalSrc : evalStep pSrc 0 (iterState pSrc s₀ n) with
      | fault fk => exact False.elim (hNoFaultAt _ hRs fk hEvalSrc)
      | done out =>
        rw [(hStep _ _ hRel).2 out hEvalSrc] at hEvalTgt; cases hEvalTgt
      | step _ =>
        apply step_iff_evalStep.mpr
        dsimp [iterState]; rw [hEvalSrc]
    · exact diverges_fwd_sim hInitSrc hInitTgt hRel0
        (fun a b a' hr hs => (hStep a b hr).1 a' hs)

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
  | cons _ rest ih =>
    cases i with
    | zero =>
      injection hTy with hEq; subst hEq; rfl
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTy
      rw [hAdd] at hRec
      exact hRec

private theorem initLocalsLoop_eq_of_storage_eq {b1 b2 : Body} (args : List Val)
    (hArg : b1.argumentCount = b2.argumentCount)
    (hLoc : b1.locals = b2.locals)
    (hSt : ∀ idx, idx < b1.locals.length →
      Nat.ble idx b1.argumentCount = false →
      hasStorageAnnotation b1 idx = hasStorageAnnotation b2 idx) :
    initLocalsLoop b1 args 0 b1.locals = initLocalsLoop b2 args 0 b2.locals := by
  rw [← hLoc]
  have hLoop : ∀ base tys,
      base + tys.length = b1.locals.length →
      initLocalsLoop b1 args base tys = initLocalsLoop b2 args base tys := by
    intro base tys hSum
    induction tys generalizing base with
    | nil => rfl
    | cons ty rest ih =>
      dsimp [List.length] at hSum
      have hBaseLt : base < b1.locals.length := by
        rw [← hSum]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self base)
          (by rw [Nat.add_succ]; exact Nat.succ_le_succ (Nat.le_add_right base rest.length))
      have hSumNext : (base + 1) + rest.length = b1.locals.length := by
        rw [Nat.add_assoc, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
        exact hSum
      dsimp [initLocalsLoop]
      rw [ih (base + 1) hSumNext]
      cases Nat.beq base 0 with
      | true => rfl
      | false =>
        rw [← hArg]
        cases hLe : Nat.ble base b1.argumentCount with
        | true => rfl
        | false => rw [hSt base hBaseLt hLe]
  exact hLoop 0 b1.locals (Nat.zero_add b1.locals.length)

private theorem bodyStaticAdmitted_eq_of_fields {p1 p2 : Program} {b1 b2 : Body}
    (hPw : p1.pointerWidthBits = p2.pointerWidthBits)
    (hVer : p1.mirProfileVersion = p2.mirProfileVersion)
    (hArg : b1.argumentCount = b2.argumentCount)
    (hLoc : b1.locals = b2.locals)
    (hId : b1.identity = b2.identity)
    (hEmpty : b1.basicBlocks.isEmpty = b2.basicBlocks.isEmpty)
    (hSt : storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2) :
    BodyStaticAdmitted p1 b1 = BodyStaticAdmitted p2 b2 := by
  unfold BodyStaticAdmitted
  rw [hPw, hVer, hId, hEmpty, hArg, hLoc, hSt]

private theorem initState_eq_of_matching_entry {p1 p2 : Program} (q : Query)
    (hHdr : programHeaderEq p1 p2 = true)
    (hNone : Trusted.MirSemantics.getElem? p1.bodies p1.entryDefId = none ↔
      Trusted.MirSemantics.getElem? p2.bodies p2.entryDefId = none)
    (hSome : ∀ b1, Trusted.MirSemantics.getElem? p1.bodies p1.entryDefId = some b1 →
      ∃ b2, Trusted.MirSemantics.getElem? p2.bodies p2.entryDefId = some b2 ∧
        bodyHeaderEq b1 b2 = true ∧
        b1.basicBlocks.isEmpty = b2.basicBlocks.isEmpty ∧
        storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 ∧
        initLocalsLoop b1 q.args 0 b1.locals = initLocalsLoop b2 q.args 0 b2.locals) :
    initState p1 q = initState p2 q := by
  let ⟨hPw, hVer, hEnt, _⟩ := programHeaderEq_elim hHdr
  unfold initState
  rw [hPw, hVer]
  cases (!Nat.beq p2.pointerWidthBits 64 || !Nat.beq p2.mirProfileVersion 1) with
  | true => rfl
  | false =>
    rw [if_bool_false rfl, if_bool_false rfl]
    cases (!q.callerMem.allocations.isEmpty) with
    | true => rfl
    | false =>
      rw [if_bool_false rfl, if_bool_false rfl]
      cases hB1 : Trusted.MirSemantics.getElem? p1.bodies p1.entryDefId with
      | none => rw [hNone.mp hB1]
      | some b1 =>
        let ⟨b2, hB2, hBHdr, hEmpty, hSt, hLocsLoop⟩ := hSome b1 hB1
        let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
        rw [hB2]; dsimp
        rw [hLocsLoop, hEmpty, hArg, hLoc, hSt, hEnt]

private theorem initState_ok_elim {p : Program} {q : Query} {s₀ : State}
    (hOk : initState p q = .ok s₀) :
    (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) = false ∧
    (!q.callerMem.allocations.isEmpty) = false ∧
    ∃ body,
      Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body ∧
      body.basicBlocks.isEmpty = false ∧
      Nat.blt body.argumentCount body.locals.length = true ∧
      storageAnnotationsInBounds body = true ∧
      body.locals.all isSupportedScalarOrUnitTy = true ∧
      checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount) = true ∧
      s₀ = {
        frames := [{
          defId := p.entryDefId
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop body q.args 0 body.locals
        }]
        callerMem := q.callerMem
      } := by
  unfold initState at hOk
  cases hC1 : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) with
  | true => rw [if_bool_true hC1] at hOk; cases hOk
  | false =>
    rw [if_bool_false hC1] at hOk
    cases hC2 : (!q.callerMem.allocations.isEmpty) with
    | true => rw [if_bool_true hC2] at hOk; cases hOk
    | false =>
      rw [if_bool_false hC2] at hOk
      cases hB : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
      | none => rw [hB] at hOk; cases hOk
      | some body =>
        rw [hB] at hOk; dsimp at hOk
        cases hE : body.basicBlocks.isEmpty with
        | true => rw [if_bool_true hE] at hOk; cases hOk
        | false =>
          rw [if_bool_false hE] at hOk
          cases hAL : (!Nat.blt body.argumentCount body.locals.length) with
          | true => rw [if_bool_true hAL] at hOk; cases hOk
          | false =>
            rw [if_bool_false hAL] at hOk
            cases hSB : (!storageAnnotationsInBounds body) with
            | true => rw [if_bool_true hSB] at hOk; cases hOk
            | false =>
              rw [if_bool_false hSB] at hOk
              cases hSup : (!body.locals.all isSupportedScalarOrUnitTy) with
              | true => rw [if_bool_true hSup] at hOk; cases hOk
              | false =>
                rw [if_bool_false hSup] at hOk
                cases hArgs : (!checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount)) with
                | true => rw [if_bool_true hArgs] at hOk; cases hOk
                | false =>
                  rw [if_bool_false hArgs] at hOk
                  injection hOk with hEqS
                  exact ⟨rfl, rfl, body, rfl, hE, bool_not_false hAL,
                    bool_not_false hSB, bool_not_false hSup, bool_not_false hArgs,
                    by rw [← hEqS]⟩

private theorem fullSemanticEquiv_of_query_iff {pSrc pTgt : Program}
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hBodyFields : ∀ defId bSrc bTgt,
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      bodyHeaderEq bSrc bTgt = true ∧
      bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
      storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt)
    (hQuery : ∀ q,
      (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (∀ k : FaultKind,
        ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
      (Diverges pTgt q ↔ Diverges pSrc q))
    (hEntryQuery : ∀ defId args,
      WellFormed (entryProgForBody pTgt defId) { args := args } ↔
        WellFormed (entryProgForBody pSrc defId) { args := args }) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hPw, hVer, _, _⟩ := programHeaderEq_elim hHdr
  refine ⟨hQuery, ?_, ?_⟩
  · intro q post
    let ⟨hWfIff, hBehIff, _, _⟩ := hQuery q
    constructor
    · intro hSat
      exact ⟨hWfIff.mp hSat.1, fun out hB => hSat.2 out ((hBehIff out).mpr hB)⟩
    · intro hSat
      exact ⟨hWfIff.mpr hSat.1, fun out hB => hSat.2 out ((hBehIff out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hBS hBT
    let ⟨hBHdr, hEmpty, hSt⟩ := hBodyFields defId bSrc bTgt hBS hBT
    let ⟨hArg, hLoc, hUns, hId⟩ := bodyHeaderEq_elim hBHdr
    have hAdm := bodyStaticAdmitted_eq_of_fields hPw hVer hArg hLoc hId hEmpty hSt
    constructor
    · intro hVerT
      refine ⟨hBS, by rw [hAdm]; exact hVerT.2.1, ?_⟩
      intro args hArgs hPre
      have hArgsT : ValidEntryArgs bTgt args := by
        unfold ValidEntryArgs; rw [← hArg, ← hLoc]; exact hArgs
      have hPreT : bTgt.isUnsafe = true → safetyPre args := by
        rw [← hUns]; exact hPre
      exact (hEntryQuery defId args).mp (hVerT.2.2 args hArgsT hPreT)
    · intro hVerS
      refine ⟨hBT, by rw [← hAdm]; exact hVerS.2.1, ?_⟩
      intro args hArgs hPre
      have hArgsS : ValidEntryArgs bSrc args := by
        unfold ValidEntryArgs; rw [hArg, hLoc]; exact hArgs
      have hPreS : bSrc.isUnsafe = true → safetyPre args := by
        rw [hUns]; exact hPre
      exact (hEntryQuery defId args).mpr (hVerS.2.2 args hArgsS hPreS)


private theorem fullSemanticEquiv_trans {p1 p2 p3 : Program}
    (hLen12 : p1.bodies.length = p2.bodies.length)
    (h12 : FullSemanticEquiv p1 p2)
    (h23 : FullSemanticEquiv p2 p3) :
    FullSemanticEquiv p1 p3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let ⟨hW12, hB12, hF12, hD12⟩ := h12.1 q
    let ⟨hW23, hB23, hF23, hD23⟩ := h23.1 q
    exact ⟨Iff.trans hW23 hW12,
           fun out => Iff.trans (hB23 out) (hB12 out),
           fun k => Iff.trans (hF23 k) (hF12 k),
           Iff.trans hD23 hD12⟩
  · intro q post
    exact Iff.trans (h23.2.1 q post) (h12.2.1 q post)
  · intro defId b1 b3 safetyPre hB1 hB3
    have hLt2 : defId < p2.bodies.length := by
      rw [← hLen12]; exact getElem?_some_lt hB1
    let ⟨b2, hB2⟩ := getElem?_some_of_lt p2.bodies defId hLt2
    exact Iff.trans (h23.2.2 defId b2 b3 safetyPre hB2 hB3)
      (h12.2.2 defId b1 b2 safetyPre hB1 hB2)

private theorem all_nonEmpty_id_eq_map (bs : List Body) :
    bs.all (fun b => !stringBeq b.identity "") =
      (bs.map (fun b => b.identity)).all (fun s => !stringBeq s "") := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    dsimp [List.map, List.all]
    rw [ih]

private theorem bodiesHaveUniqueIdentities_eq_of_map_id {bs1 bs2 : List Body}
    (hMap : bs1.map (fun b => b.identity) = bs2.map (fun b => b.identity)) :
    bodiesHaveUniqueIdentities bs1 = bodiesHaveUniqueIdentities bs2 := by
  unfold bodiesHaveUniqueIdentities
  rw [all_nonEmpty_id_eq_map bs1, all_nonEmpty_id_eq_map bs2, hMap]

private theorem programVerified_iff_of_equiv {pSrc pTgt : Program}
    (hEquiv : FullSemanticEquiv pSrc pTgt)
    (hPw : pSrc.pointerWidthBits = pTgt.pointerWidthBits)
    (hVer : pSrc.mirProfileVersion = pTgt.mirProfileVersion)
    (hEnt : pSrc.entryDefId = pTgt.entryDefId)
    (hSc : pSrc.scope = pTgt.scope)
    (hIds : pSrc.bodies.map (fun b => b.identity) =
      pTgt.bodies.map (fun b => b.identity))
    (safety : String → List Val → Prop) (prop : Program → Prop)
    (hProp : prop pTgt ↔ prop pSrc) :
    (CrateTheorem ⟨pTgt, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨pSrc, ⟨safety, prop⟩⟩) ∧
    (UnitTheorem ⟨pTgt, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨pSrc, ⟨safety, prop⟩⟩) := by
  have hLen : pSrc.bodies.length = pTgt.bodies.length := by
    rw [← map_length_eq (fun b : Body => b.identity) pSrc.bodies,
        ← map_length_eq (fun b : Body => b.identity) pTgt.bodies, hIds]
  have hIsEmpty : pSrc.bodies.isEmpty = pTgt.bodies.isEmpty :=
    list_isEmpty_eq_of_length hLen
  have hUniq : bodiesHaveUniqueIdentities pSrc.bodies =
      bodiesHaveUniqueIdentities pTgt.bodies :=
    bodiesHaveUniqueIdentities_eq_of_map_id hIds
  have hIdAt : ∀ defId bSrc bTgt,
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      bSrc.identity = bTgt.identity := by
    intro defId bSrc bTgt hBS hBT
    have hM1 := getElem?_map (fun b : Body => b.identity) pSrc.bodies defId
    have hM2 := getElem?_map (fun b : Body => b.identity) pTgt.bodies defId
    rw [hBS] at hM1; rw [hBT] at hM2; rw [hIds, hM2] at hM1
    dsimp [Option.map] at hM1
    injection hM1 with hEq; exact hEq.symm
  have hPV : ProgramVerified pTgt ⟨safety, prop⟩ ↔
      ProgramVerified pSrc ⟨safety, prop⟩ := by
    unfold ProgramVerified; dsimp
    rw [← hPw, ← hVer, ← hIsEmpty, ← hEnt, ← hLen, ← hUniq]
    constructor
    · intro ⟨h1, h2, h3, h4, h5, hBodiesT, hPr⟩
      refine ⟨h1, h2, h3, h4, h5, ?_, hProp.mp hPr⟩
      intro defId bSrc hBS
      have hLtT : defId < pTgt.bodies.length := by
        rw [← hLen]; exact getElem?_some_lt hBS
      let ⟨bTgt, hBT⟩ := getElem?_some_of_lt pTgt.bodies defId hLtT
      have hIdEq := hIdAt defId bSrc bTgt hBS hBT
      have hBVT := hBodiesT defId bTgt hBT
      rw [← hIdEq] at hBVT
      exact (hEquiv.2.2 defId bSrc bTgt (safety bSrc.identity) hBS hBT).mp hBVT
    · intro ⟨h1, h2, h3, h4, h5, hBodiesS, hPr⟩
      refine ⟨h1, h2, h3, h4, h5, ?_, hProp.mpr hPr⟩
      intro defId bTgt hBT
      have hLtS : defId < pSrc.bodies.length := by
        rw [hLen]; exact getElem?_some_lt hBT
      let ⟨bSrc, hBS⟩ := getElem?_some_of_lt pSrc.bodies defId hLtS
      have hIdEq := hIdAt defId bSrc bTgt hBS hBT
      have hBVS := hBodiesS defId bSrc hBS
      rw [hIdEq] at hBVS
      exact (hEquiv.2.2 defId bSrc bTgt (safety bTgt.identity) hBS hBT).mpr hBVS
  unfold CrateTheorem UnitTheorem; dsimp
  rw [← hSc]
  exact ⟨⟨fun h => ⟨h.1, hPV.mp h.2⟩, fun h => ⟨h.1, hPV.mpr h.2⟩⟩,
         ⟨fun h => ⟨h.1, hPV.mp h.2⟩, fun h => ⟨h.1, hPV.mpr h.2⟩⟩⟩

/-! #### Shared Storage-Marker Preservation Across `.assign`/`.nop` Rewrites -/

private noncomputable def stmtStorageBound (numLocals : Nat) : StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.blt id numLocals
  | _ => true

private noncomputable def NonStorageOrEqStmt : StatementKind → StatementKind → Prop
  | s₁, s₂ =>
    s₁ = s₂ ∨
    ((match s₁ with | .assign _ _ | .nop => True | _ => False) ∧
     (match s₂ with | .assign _ _ | .nop => True | _ => False))

private noncomputable def StmtListStoragePreserved :
    List StatementKind → List StatementKind → Prop
  | [], [] => True
  | s₁ :: r₁, s₂ :: r₂ =>
    NonStorageOrEqStmt s₁ s₂ ∧ StmtListStoragePreserved r₁ r₂
  | _, _ => False

private theorem nonStorageOrEqStmt_marker {s₁ s₂ : StatementKind} (id : LocalId)
    (h : NonStorageOrEqStmt s₁ s₂) :
    stmtHasStorageMarker id s₁ = stmtHasStorageMarker id s₂ := by
  cases h with
  | inl hEq => rw [hEq]
  | inr hPair =>
    let ⟨h1, h2⟩ := hPair
    cases s₁ with
    | storageLive _ | storageDead _ | unsupported => cases h1
    | assign _ _ | nop =>
      cases s₂ with
      | storageLive _ | storageDead _ | unsupported => cases h2
      | assign _ _ | nop => rfl

private theorem nonStorageOrEqStmt_fn {s₁ s₂ : StatementKind}
    (f : StatementKind → Bool)
    (hfAsg : ∀ d rv, f (.assign d rv) = true)
    (hfNop : f .nop = true)
    (h : NonStorageOrEqStmt s₁ s₂) :
    f s₁ = f s₂ := by
  cases h with
  | inl hEq => rw [hEq]
  | inr hPair =>
    let ⟨h1, h2⟩ := hPair
    cases s₁ with
    | storageLive _ | storageDead _ | unsupported => cases h1
    | assign d1 rv1 =>
      rw [hfAsg d1 rv1]
      cases s₂ with
      | storageLive _ | storageDead _ | unsupported => cases h2
      | assign d2 rv2 => rw [hfAsg d2 rv2]
      | nop => rw [hfNop]
    | nop =>
      rw [hfNop]
      cases s₂ with
      | storageLive _ | storageDead _ | unsupported => cases h2
      | assign d2 rv2 => rw [hfAsg d2 rv2]
      | nop => rw [hfNop]

private theorem stmtListStoragePreserved_props {ss₁ ss₂ : List StatementKind}
    (h : StmtListStoragePreserved ss₁ ss₂) :
    ss₁.length = ss₂.length ∧
    (∀ id, ss₁.any (stmtHasStorageMarker id) = ss₂.any (stmtHasStorageMarker id)) ∧
    (∀ f : StatementKind → Bool,
      (∀ d rv, f (.assign d rv) = true) →
      f .nop = true →
      ss₁.all f = ss₂.all f) := by
  induction ss₁ generalizing ss₂ with
  | nil =>
    cases ss₂ with
    | nil => exact ⟨rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    | cons _ _ => cases h
  | cons s₁ r₁ ih =>
    cases ss₂ with
    | nil => cases h
    | cons s₂ r₂ =>
      let ⟨hHead, hTail⟩ := h
      let ⟨hLen, hAny, hAll⟩ := ih hTail
      refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
      · intro id
        dsimp [List.any]
        rw [nonStorageOrEqStmt_marker id hHead, hAny id]
      · intro f hfAsg hfNop
        dsimp [List.all]
        rw [nonStorageOrEqStmt_fn f hfAsg hfNop hHead, hAll f hfAsg hfNop]

private theorem bodyStorage_eq_of_blocks {bbRel : BasicBlock → BasicBlock → Bool}
    {b₁ b₂ : Body}
    (hHdr : bodyHeaderEq b₁ b₂ = true)
    (hBBs : listRel bbRel b₁.basicBlocks b₂.basicBlocks = true)
    (hStmts : ∀ bb₁ bb₂, bbRel bb₁ bb₂ = true →
      StmtListStoragePreserved bb₁.statements bb₂.statements) :
    bodyHeaderEq b₁ b₂ = true ∧
    b₁.basicBlocks.length = b₂.basicBlocks.length ∧
    b₁.basicBlocks.isEmpty = b₂.basicBlocks.isEmpty ∧
    (∀ idx, hasStorageAnnotation b₁ idx = hasStorageAnnotation b₂ idx) ∧
    storageAnnotationsInBounds b₁ = storageAnnotationsInBounds b₂ ∧
    (∀ args, initLocalsLoop b₁ args 0 b₁.locals = initLocalsLoop b₂ args 0 b₂.locals) := by
  let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hHdr
  have hBBLen := listRel_length hBBs
  have hBBEmpty := list_isEmpty_eq_of_length hBBLen
  have hMarker : ∀ idx, hasStorageAnnotation b₁ idx = hasStorageAnnotation b₂ idx := by
    intro idx
    unfold hasStorageAnnotation
    apply list_any_eq_of_rel hBBs
    intro bb₁ bb₂ hBB
    exact (stmtListStoragePreserved_props (hStmts bb₁ bb₂ hBB)).2.1 idx
  have hBounds : storageAnnotationsInBounds b₁ = storageAnnotationsInBounds b₂ := by
    unfold storageAnnotationsInBounds; dsimp only
    rw [← hLoc]
    apply list_all_eq_of_rel hBBs
    intro bb₁ bb₂ hBB
    exact (stmtListStoragePreserved_props (hStmts bb₁ bb₂ hBB)).2.2
      (fun stmt => match stmt with | .storageLive id | .storageDead id => Nat.blt id b₁.locals.length | _ => true)
      (fun _ _ => rfl) rfl
  exact ⟨hHdr, hBBLen, hBBEmpty, hMarker, hBounds,
         fun args => initLocalsLoop_eq_of_storage_eq args hArg hLoc (fun idx _ _ => hMarker idx)⟩

/-! #### `checkVal`, `SlotWellTyped`, & `LocalsWellTyped` -/

private theorem isPrimitiveReadableTy_bool : isPrimitiveReadableTy .bool = true := rfl
private theorem isPrimitiveReadableTy_int (w : IntWidth) (s : Bool) :
    isPrimitiveReadableTy (.int w s) = true := rfl

private theorem isPrimitiveReadableTy_elim {ty : MirTy}
    (h : isPrimitiveReadableTy ty = true) :
    ty = .bool ∨ ∃ w s, ty = .int w s := by
  cases ty with
  | bool => exact Or.inl rfl
  | int w s => exact Or.inr ⟨w, s, rfl⟩
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases h

private theorem pow2_bitWidth_pos (w : IntWidth) : 0 < Nat.pow 2 w.bitWidth := by
  cases w <;> decide

private theorem toNat_truncateBits (w : IntWidth) (x : BitVec 128) :
    (truncateBits w x).toNat = Nat.mod x.toNat (Nat.pow 2 w.bitWidth) := by
  cases w
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 7 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 15 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 31 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 63 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt (bvExtractLsb 127 0 x).isLt
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 63 0 x).isLt (by decide))

private theorem truncateBits_idem (w : IntWidth) (x : BitVec 128) :
    truncateBits w (truncateBits w x) = truncateBits w x := by
  apply bitvec_eq_of_toNat_eq
  rw [toNat_truncateBits, toNat_truncateBits]
  exact Nat.mod_eq_of_lt (Nat.mod_lt x.toNat (pow2_bitWidth_pos w))

private theorem truncateBits_eq_iff {w : IntWidth} {x : BitVec 128} :
    truncateBits w x = x ↔ x.toNat < Nat.pow 2 w.bitWidth := by
  constructor
  · intro h
    rw [← h, toNat_truncateBits]
    exact Nat.mod_lt x.toNat (pow2_bitWidth_pos w)
  · intro h
    apply bitvec_eq_of_toNat_eq
    rw [toNat_truncateBits]
    exact Nat.mod_eq_of_lt h

private theorem truncateBits_zero (w : IntWidth) :
    truncateBits w (BitVec.ofNat 128 0) = BitVec.ofNat 128 0 := by
  cases w <;> decide

private theorem scalarWf_truncateBits (w : IntWidth) (s : Bool) (x : BitVec 128) :
    ScalarVal.wf ⟨w, s, truncateBits w x⟩ = true := by
  unfold ScalarVal.wf; dsimp only
  rw [truncateBits_idem]
  exact beq_self_eq_true (truncateBits w x)

private theorem checkVal_iff_ty? {v : Val} {ty : MirTy} :
    checkVal v ty = true ↔ v.ty? = some ty := by
  unfold checkVal
  cases hTy : v.ty? with
  | none => constructor <;> (intro h; cases h)
  | some vTy =>
    dsimp only
    constructor
    · intro h; rw [mirTy_beq_eq h]
    · intro h; injection h with hEq; subst hEq; exact mirTy_beq_refl vTy

private theorem checkVal_int_iff {v : Val} {w : IntWidth} {s : Bool} :
    checkVal v (.int w s) = true ↔
    ∃ bits : BitVec 128,
      v = .scalar ⟨w, s, bits⟩ ∧ truncateBits w bits = bits := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | scalar sv =>
      cases sv with
      | mk sw ss bits =>
        dsimp only [Val.ty?] at h
        cases hWf : ScalarVal.wf ⟨sw, ss, bits⟩ with
        | false => rw [hWf] at h; cases h
        | true =>
          rw [hWf] at h
          change some (MirTy.int sw ss) = some (MirTy.int w s) at h
          injection h with hTy; injection hTy with hw hs
          subst hw; subst hs
          exact ⟨bits, rfl, eq_of_beq hWf⟩
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | ptr _ | bool _ | unit | tuple _ | bytes _ => cases h
  · intro ⟨bits, hv, hTrunc⟩
    subst hv
    have hWf : ScalarVal.wf ⟨w, s, bits⟩ = true := by
      unfold ScalarVal.wf; dsimp only; rw [hTrunc]; exact beq_self_eq_true bits
    dsimp only [Val.ty?]
    rw [if_bool_true hWf]

private theorem checkVal_bool_iff {v : Val} :
    checkVal v .bool = true ↔ ∃ b : Bool, v = .bool b := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | bool b => exact ⟨b, rfl⟩
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | ptr _ | unit | tuple _ | bytes _ => cases h
  · intro ⟨b, hb⟩; subst hb; rfl

private theorem checkVal_unit_eq {v : Val} (h : checkVal v .unit = true) :
    v = .unit := by
  have hTy := checkVal_iff_ty?.mp h
  cases v with
  | unit => rfl
  | scalar sv =>
    dsimp only [Val.ty?] at hTy
    cases hWf : sv.wf <;> rw [hWf] at hTy <;> cases hTy
  | enumVal ety idx =>
    dsimp only [Val.ty?] at hTy
    cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
      <;> rw [hAdm] at hTy <;> cases hTy
  | ptr _ | bool _ | tuple _ | bytes _ => cases hTy

private theorem checkVal_enum_iff {v : Val} {ety : EnumTy} :
    checkVal v (.enum ety) = true ↔
    enumAdmitted ety = true ∧
    ∃ idx : Nat, idx < ety.discriminants.length ∧ v = .enumVal ety idx := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | enumVal ety' var =>
      dsimp only [Val.ty?] at h
      cases hAdm : enumAdmitted ety' with
      | false => rw [hAdm] at h; cases h
      | true =>
        rw [hAdm] at h
        cases hBlt : Nat.blt var ety'.discriminants.length with
        | false => rw [hBlt] at h; cases h
        | true =>
          rw [hBlt] at h
          change some (MirTy.enum ety') = some (MirTy.enum ety) at h
          injection h with hTy; injection hTy with hEty; subst hEty
          exact ⟨hAdm, var, nat_blt_lt hBlt, rfl⟩
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | ptr _ | bool _ | unit | tuple _ | bytes _ => cases h
  · intro ⟨hAdm, idx, hLt, hEq⟩
    subst hEq
    dsimp only [Val.ty?]
    rw [hAdm, nat_lt_blt hLt]
    rfl

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

private theorem checkVal_zstEnum_eq {ety : EnumTy} {v : Val}
    (hZst : isZstEnumTy ety = true) (h : checkVal v (.enum ety) = true) :
    v = .enumVal ety 0 := by
  let ⟨_, _, hLen1⟩ := isZstEnumTy_elim hZst
  let ⟨_, k, hLt, hEq⟩ := checkVal_enum_iff.mp h
  subst hEq
  rw [hLen1] at hLt
  cases k with
  | zero => rfl
  | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hLt))

private theorem findDiscrVariantAux_lt {idx : Nat} {discrBits : BitVec 128}
    {ds : List Nat} {v : Nat}
    (h : findDiscrVariantAux idx discrBits ds = some v) :
    v < idx + ds.length := by
  induction ds generalizing idx with
  | nil => cases h
  | cons d rest ih =>
    dsimp [findDiscrVariantAux] at h
    cases hEq : (BitVec.ofNat 128 d == discrBits) with
    | true =>
      rw [hEq] at h
      injection h with hV; subst hV
      dsimp [List.length]
      rw [Nat.add_succ]
      exact Nat.lt_succ_of_le (Nat.le_add_right idx rest.length)
    | false =>
      rw [hEq] at h
      have hSub := ih h
      dsimp [List.length]
      rw [Nat.add_assoc, Nat.add_comm 1 rest.length, ← Nat.add_assoc] at hSub
      exact hSub

private theorem evalConstLit_checkVal {ty : MirTy} {lit : ConstLit} {v : Val}
    (h : evalConstLit ty lit = .ok v) : checkVal v ty = true := by
  cases ty with
  | int w s =>
    cases lit with
    | zeroSized => cases h
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases hOvf : (truncateBits w bits != bits) with
      | true => rw [hOvf] at h; cases h
      | false =>
        rw [hOvf] at h; dsimp at h
        injection h with hEq; subst hEq
        exact checkVal_int_iff.mpr ⟨truncateBits w bits, rfl, truncateBits_idem w bits⟩
  | bool =>
    cases lit with
    | zeroSized => cases h
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases hOvf : (truncateBits .i8 bits != bits) with
      | true => rw [hOvf] at h; cases h
      | false =>
        rw [hOvf] at h; dsimp at h
        cases h0 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) with
        | true => rw [h0] at h; injection h with hEq; subst hEq; rfl
        | false =>
          rw [h0] at h; dsimp at h
          cases h1 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) with
          | true => rw [h1] at h; injection h with hEq; subst hEq; rfl
          | false => rw [h1] at h; cases h
  | unit =>
    cases lit with
    | scalar _ => cases h
    | zeroSized => injection h with hEq; subst hEq; rfl
  | enum ety =>
    cases lit with
    | zeroSized =>
      dsimp [evalConstLit] at h
      cases hZ : isZstEnumTy ety with
      | false => rw [hZ] at h; cases h
      | true =>
        rw [hZ] at h; injection h with hEq; subst hEq
        let ⟨_, hAdm, hLen1⟩ := isZstEnumTy_elim hZ
        exact checkVal_enum_iff.mpr ⟨hAdm, 0, by rw [hLen1]; exact Nat.zero_lt_one, rfl⟩
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases hTr : ety.tagRepr with
      | zeroSized => rw [hTr] at h; cases h
      | scalar tw ts =>
        rw [hTr] at h; dsimp at h
        cases hBad : (!enumAdmitted ety || (truncateBits tw bits != bits)) with
        | true => rw [hBad] at h; cases h
        | false =>
          rw [hBad] at h; dsimp at h
          have hAdm : enumAdmitted ety = true := by
            cases hA : enumAdmitted ety with
            | true => rfl
            | false => rw [hA] at hBad; cases hBad
          cases hFind : findDiscrVariant? (tagBitsToDiscrBits tw ts ety.discrWidth bits) ety.discriminants with
          | none => rw [hFind] at h; cases h
          | some idx =>
            rw [hFind] at h; injection h with hEq; subst hEq
            have hLt : idx < ety.discriminants.length := by
              have h0 := findDiscrVariantAux_lt hFind
              rw [Nat.zero_add] at h0; exact h0
            exact checkVal_enum_iff.mpr ⟨hAdm, idx, hLt, rfl⟩
  | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases lit <;> cases h

private noncomputable def SlotWellTyped (ty : MirTy) : LocalSlot → Prop
  | .dead => True
  | .live none => isAlwaysInhabitedZst ty = false
  | .live (some v) => checkVal v ty = true

private theorem liveUninitSlot_isLive (ty : MirTy) :
    ∃ opt, liveUninitSlot ty = .live opt := by
  cases ty with
  | unit => exact ⟨some .unit, rfl⟩
  | enum ety =>
    dsimp [liveUninitSlot]
    cases isZstEnumTy ety with
    | true => exact ⟨some (.enumVal ety 0), rfl⟩
    | false => exact ⟨none, rfl⟩
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    exact ⟨none, rfl⟩

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
      exact checkVal_enum_iff.mpr ⟨hAdm, 0, by rw [hLen1]; exact Nat.zero_lt_one, rfl⟩
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => rfl

private noncomputable def LocalsWellTyped (bodyLocals : List MirTy)
    (locals : List LocalSlot) : Prop :=
  locals.length = bodyLocals.length ∧
  ∀ i ty sl,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? locals i = some sl →
    SlotWellTyped ty sl

private theorem localsWellTyped_set {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {id : Nat} {ty : MirTy} {sl : LocalSlot}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSet : setElem? locals id sl = some locals')
    (hSlWt : SlotWellTyped ty sl) :
    LocalsWellTyped bodyLocals locals' := by
  let ⟨hLen, hAll⟩ := hWt
  refine ⟨by rw [setElem?_length hSet, hLen], ?_⟩
  intro i tyi sli hTyi hSli
  cases hEq : Nat.beq i id with
  | true =>
    have hi := nat_beq_eq hEq; subst hi
    rw [hTy] at hTyi; injection hTyi with hEqT; subst hEqT
    rw [setElem?_getElem?_same hSet] at hSli; injection hSli with hEqS; subst hEqS
    exact hSlWt
  | false =>
    rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hEq)] at hSli
    exact hAll i tyi sli hTyi hSli

private theorem initLocalsLoop_wellTyped {body : Body} {args : List Val}
    (hArgs : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true) :
    LocalsWellTyped body.locals (initLocalsLoop body args 0 body.locals) := by
  refine ⟨initLocalsLoop_length body args 0 body.locals, ?_⟩
  intro i ty sl hTy hSl
  have hGet := initLocalsLoop_getElem? body args 0 body.locals i ty hTy
  rw [Nat.zero_add] at hGet
  rw [hGet] at hSl; injection hSl with hEq; subst hEq
  cases i with
  | zero => exact liveUninitSlot_wellTyped ty
  | succ k =>
    dsimp [Nat.beq]
    cases hLe : Nat.ble (k + 1) body.argumentCount with
    | true =>
      have hKlt : k < body.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((body.locals.drop 1).take body.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 body.locals body.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]; exact hChk
    | false =>
      cases hasStorageAnnotation body (k + 1) with
      | true => exact True.intro
      | false => exact liveUninitSlot_wellTyped ty

private theorem evalOperandToSlot_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {op : Operand} {ty : MirTy}
    {optVal : Option Val}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hEv : evalOperandToSlot bodyLocals locals op = .ok (ty, optVal, locals')) :
    LocalsWellTyped bodyLocals locals' ∧
    (∀ v, optVal = some v → checkVal v ty = true) := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok val =>
      rw [hC] at hEv
      injection hEv with hEq
      injection hEq with hTy hR; injection hR with hOpt hLoc
      subst hTy; subst hOpt; subst hLoc
      refine ⟨hWt, ?_⟩
      intro v hv; injection hv with hveq; subst hveq
      exact evalConstLit_checkVal hC
  | copy p =>
    dsimp [evalOperandToSlot] at hEv
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hEv; cases hEv
    | true =>
      rw [hProj] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some t =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some slot =>
          rw [hSl] at hEv
          cases slot with
          | dead => cases hEv
          | live o =>
            injection hEv with hEq
            injection hEq with hTyE hR; injection hR with hOptE hLocE
            subst hTyE; subst hOptE; subst hLocE
            refine ⟨hWt, ?_⟩
            intro v hv; subst hv
            exact hWt.2 p.localId t (.live (some v)) hTy hSl
  | move p =>
    dsimp [evalOperandToSlot] at hEv
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hEv; cases hEv
    | true =>
      rw [hProj] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some t =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some slot =>
          rw [hSl] at hEv
          cases slot with
          | dead => cases hEv
          | live o =>
            dsimp at hEv
            cases hSet : setElem? locals p.localId (liveUninitSlot t) with
            | none => rw [hSet] at hEv; cases hEv
            | some locs1 =>
              rw [hSet] at hEv
              injection hEv with hEq
              injection hEq with hTyE hR; injection hR with hOptE hLocE
              subst hTyE; subst hOptE; subst hLocE
              refine ⟨localsWellTyped_set hWt hTy hSet (liveUninitSlot_wellTyped t), ?_⟩
              intro v hv; subst hv
              exact hWt.2 p.localId t (.live (some v)) hTy hSl

private theorem evalPrimitiveOperand_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {op : Operand} {v : Val}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hEv : evalPrimitiveOperand bodyLocals locals op = .ok (v, locals')) :
    LocalsWellTyped bodyLocals locals' := by
  dsimp [evalPrimitiveOperand] at hEv
  cases hS : evalOperandToSlot bodyLocals locals op with
  | error _ => rw [hS] at hEv; cases hEv
  | ok res =>
    let ⟨ty0, optVal, locs1⟩ := res
    rw [hS] at hEv; dsimp at hEv
    cases hPrim : isPrimitiveReadableTy ty0 with
    | false => rw [hPrim] at hEv; cases hEv
    | true =>
      rw [hPrim] at hEv; dsimp at hEv
      cases optVal with
      | none => cases hEv
      | some _ =>
        injection hEv with hEq; injection hEq with _ hl; subst hl
        exact (evalOperandToSlot_preserves_wt hWt hS).1

private theorem evalRvalue_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    LocalsWellTyped bodyLocals locals' := by
  cases rv with
  | use o =>
    dsimp [evalRvalue] at hEv
    cases hS : evalOperandToSlot bodyLocals locals o with
    | error _ => rw [hS] at hEv; cases hEv
    | ok res =>
      let ⟨srcTy, optVal, locs1⟩ := res
      rw [hS] at hEv; dsimp at hEv
      cases hEqTy : MirTy.beq srcTy dstTy with
      | false => rw [hEqTy] at hEv; cases hEv
      | true =>
        rw [hEqTy] at hEv; dsimp at hEv
        cases optVal with
        | none => cases hEv
        | some _ =>
          injection hEv with h1; injection h1 with _ hL; subst hL
          exact (evalOperandToSlot_preserves_wt hWt hS).1
  | binaryOp op l r =>
    dsimp [evalRvalue] at hEv
    cases hL : evalPrimitiveOperand bodyLocals locals l with
    | error _ => rw [hL] at hEv; cases hEv
    | ok resL =>
      let ⟨lv, locs1⟩ := resL
      rw [hL] at hEv; dsimp at hEv
      cases hR : evalPrimitiveOperand bodyLocals locs1 r with
      | error _ => rw [hR] at hEv; cases hEv
      | ok resR =>
        let ⟨rvv, locs2⟩ := resR
        rw [hR] at hEv; dsimp at hEv
        cases hB : evalBinOp op lv rvv with
        | error _ => rw [hB] at hEv; cases hEv
        | ok _ =>
          rw [hB] at hEv; injection hEv with h1; injection h1 with _ hLoc; subst hLoc
          exact evalPrimitiveOperand_preserves_wt
            (evalPrimitiveOperand_preserves_wt hWt hL) hR
  | unaryOp op o =>
    dsimp [evalRvalue] at hEv
    cases hO : evalPrimitiveOperand bodyLocals locals o with
    | error _ => rw [hO] at hEv; cases hEv
    | ok resO =>
      let ⟨ov, locs1⟩ := resO
      rw [hO] at hEv; dsimp at hEv
      cases hU : evalUnOp op ov with
      | error _ => rw [hU] at hEv; cases hEv
      | ok _ =>
        rw [hU] at hEv; injection hEv with h1; injection h1 with _ hLoc; subst hLoc
        exact evalPrimitiveOperand_preserves_wt hWt hO
  | discriminant p =>
    dsimp [evalRvalue] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases ty with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hSl] at hEv; cases hEv
          | some slot =>
            rw [hSl] at hEv; dsimp at hEv
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEv; cases hEv
            | true =>
              rw [hAdm] at hEv; dsimp at hEv
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp at hEv
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEv; cases hEv
                    | some _ =>
                      rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                      subst hL; exact hWt
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                          subst hL; exact hWt
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
              | scalar _ _ =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none => cases hEv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                          subst hL; exact hWt
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEv

private theorem writePlace_preserves_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dstId : LocalId} {dstTy : MirTy} {val : Val}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (hW : writePlace locals dstId dstTy val = .ok locals') :
    LocalsWellTyped bodyLocals locals' ∧ checkVal val dstTy = true := by
  dsimp [writePlace] at hW
  cases hChk : checkVal val dstTy with
  | false => rw [hChk] at hW; cases hW
  | true =>
    rw [hChk] at hW; dsimp at hW
    cases hSl : Trusted.MirSemantics.getElem? locals dstId with
    | none => rw [hSl] at hW; cases hW
    | some slot =>
      rw [hSl] at hW
      cases slot with
      | dead => cases hW
      | live _ =>
        cases hSet : setElem? locals dstId (.live (some val)) with
        | none => rw [hSet] at hW; cases hW
        | some locs1 =>
          rw [hSet] at hW; injection hW with hEq; subst hEq
          exact ⟨localsWellTyped_set hWt hTy hSet hChk, rfl⟩

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

/-! #### Shared 3-Point `AbsSlot` Soundness (`AbsSlotSound`, `AbsEnvSound`) -/

private noncomputable def AbsSlotSound (ty : MirTy) (abs : AbsSlot)
    (sl : LocalSlot) : Prop :=
  SlotWellTyped ty sl ∧
  match abs with
  | .dead => True
  | .liveUninit => ∃ o, sl = .live o
  | .liveInit => ∃ v, sl = .live (some v)

private noncomputable def AbsEnvSound (bodyLocals : List MirTy)
    (env : List AbsSlot) (locals : List LocalSlot) : Prop :=
  LocalsWellTyped bodyLocals locals ∧
  env.length = bodyLocals.length ∧
  ∀ i ty abs sl,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? env i = some abs →
    Trusted.MirSemantics.getElem? locals i = some sl →
    AbsSlotSound ty abs sl

private theorem absSlotImplies_sound {ty : MirTy} {a₁ a₂ : AbsSlot} {sl : LocalSlot}
    (hImp : absSlotImplies a₁ a₂ = true)
    (hSound : AbsSlotSound ty a₁ sl) :
    AbsSlotSound ty a₂ sl := by
  let ⟨hWt, hS⟩ := hSound
  cases a₂ with
  | dead => exact ⟨hWt, True.intro⟩
  | liveUninit =>
    cases a₁ with
    | dead => cases hImp
    | liveUninit => exact ⟨hWt, hS⟩
    | liveInit =>
      let ⟨v, hv⟩ := hS
      exact ⟨hWt, ⟨some v, hv⟩⟩
  | liveInit =>
    cases a₁ with
    | dead | liveUninit => cases hImp
    | liveInit => exact ⟨hWt, hS⟩

private theorem absEnvImplies_sound {bodyLocals : List MirTy}
    {env₁ env₂ : List AbsSlot} {locals : List LocalSlot}
    (hImp : absEnvImplies env₁ env₂ = true)
    (hSound : AbsEnvSound bodyLocals env₁ locals) :
    AbsEnvSound bodyLocals env₂ locals := by
  let ⟨hWt, hLen1, hAll⟩ := hSound
  have hLen12 : env₁.length = env₂.length := listRel_length hImp
  refine ⟨hWt, hLen12.symm.trans hLen1, ?_⟩
  intro i ty a₂ sl hTy hA2 hSl
  let ⟨a₁, hA1, hImpSlot⟩ := listRel_getElem?_right hImp hA2
  exact absSlotImplies_sound hImpSlot (hAll i ty a₁ sl hTy hA1 hSl)

private theorem absSlotSound_liveUninit (ty : MirTy) :
    AbsSlotSound ty
      (if isAlwaysInhabitedZst ty then .liveInit else .liveUninit)
      (liveUninitSlot ty) := by
  cases ty with
  | unit => exact ⟨liveUninitSlot_wellTyped .unit, ⟨.unit, rfl⟩⟩
  | enum ety =>
    cases hZ : isZstEnumTy ety with
    | true =>
      have h1 : isAlwaysInhabitedZst (.enum ety) = true := hZ
      have h2 : liveUninitSlot (.enum ety) = .live (some (.enumVal ety 0)) := by
        dsimp [liveUninitSlot]; rw [hZ]; rfl
      rw [h1, h2]; dsimp
      exact ⟨by rw [← h2]; exact liveUninitSlot_wellTyped (.enum ety), ⟨.enumVal ety 0, rfl⟩⟩
    | false =>
      have h1 : isAlwaysInhabitedZst (.enum ety) = false := hZ
      have h2 : liveUninitSlot (.enum ety) = .live none := by
        dsimp [liveUninitSlot]; rw [hZ]; rfl
      rw [h1, h2]; dsimp
      exact ⟨by rw [← h2]; exact liveUninitSlot_wellTyped (.enum ety), ⟨none, rfl⟩⟩
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    exact ⟨liveUninitSlot_wellTyped _, ⟨none, rfl⟩⟩

private theorem initAbsEnvLoop_length (body : Body) :
    ∀ idx tys, (initAbsEnvLoop body idx tys).length = tys.length := by
  intro idx tys
  induction tys generalizing idx with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [initAbsEnvLoop, List.length]
    rw [ih (idx + 1)]

private theorem initAbsEnvLoop_getElem? (body : Body) :
    ∀ base tys k ty,
      Trusted.MirSemantics.getElem? tys k = some ty →
      Trusted.MirSemantics.getElem? (initAbsEnvLoop body base tys) k =
        some (initAbsSlot body (base + k) ty) := by
  intro base tys
  induction tys generalizing base with
  | nil => intro _ _ h; cases h
  | cons _ rest ih =>
    intro k ty h
    cases k with
    | zero =>
      injection h with hEq; subst hEq
      dsimp [initAbsEnvLoop, Trusted.MirSemantics.getElem?]
    | succ m =>
      dsimp [Trusted.MirSemantics.getElem?] at h
      dsimp [initAbsEnvLoop, Trusted.MirSemantics.getElem?]
      rw [ih (base + 1) m ty h, Nat.add_assoc, Nat.add_comm 1 m]

private theorem initAbsEnvLoop_sound {body : Body} {args : List Val}
    (hArgs : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true) :
    AbsEnvSound body.locals
      (initAbsEnvLoop body 0 body.locals)
      (initLocalsLoop body args 0 body.locals) := by
  have hWt := initLocalsLoop_wellTyped hArgs
  refine ⟨hWt, initAbsEnvLoop_length body 0 body.locals, ?_⟩
  intro i ty abs sl hTy hAbs hSl
  have hGetAbs := initAbsEnvLoop_getElem? body 0 body.locals i ty hTy
  rw [Nat.zero_add] at hGetAbs
  rw [hGetAbs] at hAbs; injection hAbs with hEqA; subst hEqA
  have hGetSl := initLocalsLoop_getElem? body args 0 body.locals i ty hTy
  rw [Nat.zero_add] at hGetSl
  rw [hGetSl] at hSl; injection hSl with hEqS; subst hEqS
  cases i with
  | zero =>
    dsimp [initAbsSlot, Nat.beq]
    exact absSlotSound_liveUninit ty
  | succ k =>
    dsimp [initAbsSlot, Nat.beq]
    cases hLe : Nat.ble (k + 1) body.argumentCount with
    | true =>
      dsimp
      have hKlt : k < body.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((body.locals.drop 1).take body.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 body.locals body.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]
      exact ⟨hChk, ⟨v, rfl⟩⟩
    | false =>
      dsimp
      cases hasStorageAnnotation body (k + 1) with
      | true => dsimp; exact ⟨True.intro, True.intro⟩
      | false => dsimp; exact absSlotSound_liveUninit ty

private theorem absEnvSound_set {bodyLocals : List MirTy}
    {env env' : List AbsSlot} {locals locals' : List LocalSlot}
    {id : Nat} {ty : MirTy} {abs' : AbsSlot} {sl' : LocalSlot}
    (hEnv : AbsEnvSound bodyLocals env locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSetE : setElem? env id abs' = some env')
    (hSetL : setElem? locals id sl' = some locals')
    (hSlSound : AbsSlotSound ty abs' sl') :
    AbsEnvSound bodyLocals env' locals' := by
  let ⟨hWt, hLenE, hAll⟩ := hEnv
  refine ⟨localsWellTyped_set hWt hTy hSetL hSlSound.1,
          (setElem?_length hSetE).trans hLenE, ?_⟩
  intro i tyi absi sli hTyi hE hL
  cases hEq : Nat.beq i id with
  | true =>
    have hi := nat_beq_eq hEq; subst hi
    rw [hTy] at hTyi; injection hTyi with h1; subst h1
    rw [setElem?_getElem?_same hSetE] at hE; injection hE with h2; subst h2
    rw [setElem?_getElem?_same hSetL] at hL; injection hL with h3; subst h3
    exact hSlSound
  | false =>
    have hNe := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSetE hNe] at hE
    rw [setElem?_getElem?_ne hSetL hNe] at hL
    exact hAll i tyi absi sli hTyi hE hL

private theorem deinitMoveOperandAbs_sound {bodyLocals : List MirTy}
    {env : List AbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {srcTy : MirTy} {optVal : Option Val}
    (hEnv : AbsEnvSound bodyLocals env locals)
    (hEv : evalOperandToSlot bodyLocals locals opnd = .ok (srcTy, optVal, locals')) :
    AbsEnvSound bodyLocals (deinitMoveOperandAbs bodyLocals env opnd) locals' := by
  cases opnd with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok _ =>
      rw [hC] at hEv; injection hEv with h1; injection h1 with _ h2
      injection h2 with _ hL; subst hL; exact hEnv
  | copy p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some _ =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            injection hEv with h1; injection h1 with _ h2
            injection h2 with _ hL; subst hL; exact hEnv
  | move p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            dsimp at hEv
            cases hSetL : setElem? locals p.localId (liveUninitSlot ty) with
            | none => rw [hSetL] at hEv; cases hEv
            | some locs1 =>
              rw [hSetL] at hEv
              injection hEv with h1; injection h1 with _ h2
              injection h2 with _ hL; subst hL
              have hLtE : p.localId < env.length := by
                rw [hEnv.2.1]; exact getElem?_some_lt hTy
              let ⟨env', hSetE⟩ := setElem?_some_of_lt env p.localId
                (if isAlwaysInhabitedZst ty then .liveInit else .liveUninit) hLtE
              dsimp [deinitMoveOperandAbs]
              rw [hP]; dsimp; rw [hTy]; dsimp; rw [hSetE]
              exact absEnvSound_set hEnv hTy hSetE hSetL (absSlotSound_liveUninit ty)

private theorem deinitMovePrimAbs_sound {bodyLocals : List MirTy}
    {env : List AbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {v : Val}
    (hEnv : AbsEnvSound bodyLocals env locals)
    (hEv : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    AbsEnvSound bodyLocals (deinitMoveOperandAbs bodyLocals env opnd) locals' := by
  dsimp [evalPrimitiveOperand] at hEv
  cases hS : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [hS] at hEv; cases hEv
  | ok res =>
    let ⟨ty0, optVal, locs1⟩ := res
    rw [hS] at hEv; dsimp at hEv
    cases hPrim : isPrimitiveReadableTy ty0 with
    | false => rw [hPrim] at hEv; cases hEv
    | true =>
      rw [hPrim] at hEv; dsimp at hEv
      cases optVal with
      | none => cases hEv
      | some _ =>
        injection hEv with h1; injection h1 with _ hL; subst hL
        exact deinitMoveOperandAbs_sound hEnv hS

private theorem deinitMovesInRvalueAbs_sound {bodyLocals : List MirTy}
    {env : List AbsSlot} {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hEnv : AbsEnvSound bodyLocals env locals)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    AbsEnvSound bodyLocals (deinitMovesInRvalueAbs bodyLocals env rv) locals' := by
  cases rv with
  | use o =>
    dsimp [evalRvalue] at hEv
    cases hS : evalOperandToSlot bodyLocals locals o with
    | error _ => rw [hS] at hEv; cases hEv
    | ok res =>
      let ⟨srcTy, optVal, locs1⟩ := res
      rw [hS] at hEv; dsimp at hEv
      cases hEqTy : MirTy.beq srcTy dstTy with
      | false => rw [hEqTy] at hEv; cases hEv
      | true =>
        rw [hEqTy] at hEv; dsimp at hEv
        cases optVal with
        | none => cases hEv
        | some _ =>
          injection hEv with h1; injection h1 with _ hL; subst hL
          exact deinitMoveOperandAbs_sound hEnv hS
  | unaryOp op o =>
    dsimp [evalRvalue] at hEv
    cases hO : evalPrimitiveOperand bodyLocals locals o with
    | error _ => rw [hO] at hEv; cases hEv
    | ok res =>
      let ⟨ov, locs1⟩ := res
      rw [hO] at hEv; dsimp at hEv
      cases hU : evalUnOp op ov with
      | error _ => rw [hU] at hEv; cases hEv
      | ok _ =>
        rw [hU] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL
        exact deinitMovePrimAbs_sound hEnv hO
  | binaryOp op l r =>
    dsimp [evalRvalue] at hEv
    cases hL : evalPrimitiveOperand bodyLocals locals l with
    | error _ => rw [hL] at hEv; cases hEv
    | ok resL =>
      let ⟨lv, locs1⟩ := resL
      rw [hL] at hEv; dsimp at hEv
      cases hR : evalPrimitiveOperand bodyLocals locs1 r with
      | error _ => rw [hR] at hEv; cases hEv
      | ok resR =>
        let ⟨rvv, locs2⟩ := resR
        rw [hR] at hEv; dsimp at hEv
        cases hB : evalBinOp op lv rvv with
        | error _ => rw [hB] at hEv; cases hEv
        | ok _ =>
          rw [hB] at hEv; injection hEv with h1; injection h1 with _ hL2; subst hL2
          exact deinitMovePrimAbs_sound (deinitMovePrimAbs_sound hEnv hL) hR
  | discriminant p =>
    dsimp [deinitMovesInRvalueAbs]
    have hWt' := evalRvalue_preserves_wt hEnv.1 hEv
    dsimp [evalRvalue] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases ty with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hSl] at hEv; cases hEv
          | some slot =>
            rw [hSl] at hEv; dsimp at hEv
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEv; cases hEv
            | true =>
              rw [hAdm] at hEv; dsimp at hEv
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp at hEv
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEv; cases hEv
                    | some _ =>
                      rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                      subst hL; exact hEnv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                          subst hL; exact hEnv
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
              | scalar _ _ =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none => cases hEv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                          subst hL; exact hEnv
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEv

private theorem stepPlainStmtAbs_sound {body : Body} {frame : FrameState}
    {cm : CallerMemory} {env env' : List AbsSlot} {stmt : StatementKind}
    {s' : State}
    (hEnv : AbsEnvSound body.locals env frame.locals)
    (hStepAbs : stepPlainStmtAbs body.locals env stmt = some env')
    (hEv : evalStatement body frame cm stmt = .step s') :
    ∃ locs',
      s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
             callerMem := cm } ∧
      AbsEnvSound body.locals env' locs' := by
  cases stmt with
  | nop =>
    injection hStepAbs with hE; subst hE
    injection hEv with hS; subst hS
    exact ⟨frame.locals, rfl, hEnv⟩
  | unsupported => cases hEv
  | storageLive id =>
    dsimp [stepPlainStmtAbs] at hStepAbs
    dsimp [evalStatement] at hEv
    cases hTy : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [hTy] at hEv; cases hEv
    | some ty =>
      rw [hTy] at hStepAbs hEv; dsimp at hStepAbs hEv
      cases hSetL : setElem? frame.locals id (liveUninitSlot ty) with
      | none => rw [hSetL] at hEv; cases hEv
      | some locs' =>
        rw [hSetL] at hEv; injection hEv with hS; subst hS
        exact ⟨locs', rfl, absEnvSound_set hEnv hTy hStepAbs hSetL (absSlotSound_liveUninit ty)⟩
  | storageDead id =>
    dsimp [stepPlainStmtAbs] at hStepAbs
    dsimp [evalStatement] at hEv
    cases hZ : Nat.beq id 0 with
    | true => rw [hZ] at hEv; cases hEv
    | false =>
      rw [hZ] at hStepAbs hEv; dsimp at hStepAbs hEv
      cases hSetL : setElem? frame.locals id .dead with
      | none => rw [hSetL] at hEv; cases hEv
      | some locs' =>
        rw [hSetL] at hEv; injection hEv with hS; subst hS
        have hLt : id < body.locals.length := by
          cases Nat.lt_or_ge id body.locals.length with
          | inl h => exact h
          | inr hge =>
            have hNone := setElem?_none_of_ge frame.locals id .dead (by rw [hEnv.1.1]; exact hge)
            rw [hNone] at hSetL; cases hSetL
        let ⟨ty, hTy⟩ := getElem?_some_of_lt body.locals id hLt
        exact ⟨locs', rfl, absEnvSound_set hEnv hTy hStepAbs hSetL ⟨True.intro, True.intro⟩⟩
  | assign dst rv =>
    dsimp [stepPlainStmtAbs] at hStepAbs
    dsimp [evalStatement] at hEv
    cases hP : dst.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hStepAbs hEv; dsimp at hStepAbs hEv
      cases hTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some dstTy =>
        rw [hTy] at hStepAbs hEv; dsimp at hStepAbs hEv
        cases hR : evalRvalue body.locals frame.locals dstTy rv with
        | error _ => rw [hR] at hEv; cases hEv
        | ok res =>
          let ⟨val, locs1⟩ := res
          rw [hR] at hEv; dsimp at hEv
          have hEnv1 := deinitMovesInRvalueAbs_sound hEnv hR
          dsimp [writePlace] at hEv
          cases hChk : checkVal val dstTy with
          | false => rw [hChk] at hEv; cases hEv
          | true =>
            rw [hChk] at hEv; dsimp at hEv
            cases hSl : Trusted.MirSemantics.getElem? locs1 dst.localId with
            | none => rw [hSl] at hEv; cases hEv
            | some sl =>
              rw [hSl] at hEv
              cases sl with
              | dead => cases hEv
              | live _ =>
                cases hSetL : setElem? locs1 dst.localId (.live (some val)) with
                | none => rw [hSetL] at hEv; cases hEv
                | some locs' =>
                  rw [hSetL] at hEv; injection hEv with hS; subst hS
                  exact ⟨locs', rfl, absEnvSound_set hEnv1 hTy hStepAbs hSetL ⟨hChk, ⟨val, rfl⟩⟩⟩

private theorem evalSwitchBranches_cases {w : IntWidth} {discrBits : BitVec 128}
    {otherwise tgt : BasicBlockId} {branches : List (BitVec 128 × BasicBlockId)}
    (hEv : evalSwitchBranches w discrBits otherwise branches = .ok tgt) :
    (∃ caseBits, (caseBits, tgt) ∈ branches) ∨
    (tgt = otherwise ∧
      (hasValidZeroGuard w branches = true →
        truncateBits w discrBits ≠ BitVec.ofNat 128 0)) := by
  induction branches with
  | nil =>
    injection hEv with hTgt
    exact Or.inr ⟨hTgt.symm, fun hG => by cases hG⟩
  | cons br rest ih =>
    cases br with
    | mk caseBits bTgt =>
      dsimp [evalSwitchBranches] at hEv
      cases hOvf : (truncateBits w caseBits != caseBits) with
      | true => rw [hOvf] at hEv; cases hEv
      | false =>
        rw [hOvf] at hEv; dsimp at hEv
        cases hMatch : (truncateBits w discrBits == truncateBits w caseBits) with
        | true =>
          rw [hMatch] at hEv
          injection hEv with hEq; subst hEq
          exact Or.inl ⟨caseBits, List.Mem.head rest⟩
        | false =>
          rw [hMatch] at hEv; dsimp at hEv
          cases ih hEv with
          | inl hCase =>
            let ⟨cb, hMem⟩ := hCase
            exact Or.inl ⟨cb, List.Mem.tail (caseBits, bTgt) hMem⟩
          | inr hCase =>
            let ⟨hTgt, hGuardRest⟩ := hCase
            refine Or.inr ⟨hTgt, ?_⟩
            intro hG
            dsimp [hasValidZeroGuard] at hG
            rw [hOvf] at hG; dsimp at hG
            cases hCaseZero : (caseBits == BitVec.ofNat 128 0) with
            | true =>
              have hCEq := bitvec_beq_eq hCaseZero
              subst hCEq
              intro hDiscrZero
              rw [hDiscrZero, truncateBits_zero w, bitvec_beq_refl] at hMatch
              cases hMatch
            | false =>
              rw [hCaseZero] at hG; dsimp at hG
              exact hGuardRest hG

private theorem evalBoolSwitchBranches_cases {b : Bool} {otherwise tgt : BasicBlockId}
    {branches : List (BitVec 128 × BasicBlockId)}
    (hEv : evalBoolSwitchBranches b otherwise branches = .ok tgt) :
    (∃ caseBits, (caseBits, tgt) ∈ branches) ∨ tgt = otherwise := by
  induction branches with
  | nil =>
    injection hEv with hTgt
    exact Or.inr hTgt.symm
  | cons br rest ih =>
    cases br with
    | mk caseBits bTgt =>
      dsimp [evalBoolSwitchBranches] at hEv
      cases hLit : evalConstLit .bool (.scalar caseBits) with
      | error _ => rw [hLit] at hEv; cases hEv
      | ok val =>
        rw [hLit] at hEv
        cases val with
        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
        | bool bv =>
          cases bv with
          | false =>
            cases b with
            | false =>
              dsimp at hEv; injection hEv with hEq; subst hEq
              exact Or.inl ⟨caseBits, List.Mem.head rest⟩
            | true =>
              dsimp at hEv
              cases ih hEv with
              | inl hCase =>
                let ⟨cb, hMem⟩ := hCase
                exact Or.inl ⟨cb, List.Mem.tail (caseBits, bTgt) hMem⟩
              | inr hTgt => exact Or.inr hTgt
          | true =>
            cases b with
            | true =>
              dsimp at hEv; injection hEv with hEq; subst hEq
              exact Or.inl ⟨caseBits, List.Mem.head rest⟩
            | false =>
              dsimp at hEv
              cases ih hEv with
              | inl hCase =>
                let ⟨cb, hMem⟩ := hCase
                exact Or.inl ⟨cb, List.Mem.tail (caseBits, bTgt) hMem⟩
              | inr hTgt => exact Or.inr hTgt

private theorem checkAbsEdge_sound {bodyLocals : List MirTy} {numBlocks : Nat}
    {cert : BodyAbsCert} {exitEnv : List AbsSlot} {locals : List LocalSlot}
    {target : BasicBlockId}
    (hEdge : checkAbsEdge numBlocks cert exitEnv target = true)
    (hLt : target < numBlocks)
    (hEnv : AbsEnvSound bodyLocals exitEnv locals) :
    ∃ tgtEnv,
      Trusted.MirSemantics.getElem? cert target = some (some tgtEnv) ∧
      AbsEnvSound bodyLocals tgtEnv locals := by
  unfold checkAbsEdge at hEdge
  rw [nat_lt_blt hLt] at hEdge; dsimp at hEdge
  cases hC : Trusted.MirSemantics.getElem? cert target with
  | none => rw [hC] at hEdge; cases hEdge
  | some opt =>
    rw [hC] at hEdge
    cases opt with
    | none => cases hEdge
    | some tgtEnv =>
      exact ⟨tgtEnv, rfl, absEnvImplies_sound hEdge hEnv⟩

private theorem checkAbsTerminatorEdges_step_sound {body : Body} {bb : BasicBlock}
    {cert : BodyAbsCert} {exitEnv : List AbsSlot} {frame : FrameState}
    {cm : CallerMemory} {s' : State}
    (hEnv : AbsEnvSound body.locals exitEnv frame.locals)
    (hEdges : checkAbsTerminatorEdges body.locals body.basicBlocks.length cert
      exitEnv bb.terminator = true)
    (hEv : evalTerminator body bb frame cm = .step s') :
    ∃ tgt locs',
      s' = { frames := [{ frame with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
             callerMem := cm } ∧
      LocalsWellTyped body.locals locs' ∧
      (tgt < body.basicBlocks.length →
        ∃ tgtEnv,
          Trusted.MirSemantics.getElem? cert tgt = some (some tgtEnv) ∧
          AbsEnvSound body.locals tgtEnv locs') := by
  unfold evalTerminator at hEv
  cases hTm : bb.terminator with
  | goto tgt =>
    rw [hTm] at hEv hEdges
    injection hEv with hEq; subst hEq
    exact ⟨tgt, frame.locals, rfl, hEnv.1,
           fun hLt => checkAbsEdge_sound hEdges hLt hEnv⟩
  | return_ =>
    rw [hTm] at hEv; dsimp at hEv
    cases hC : bb.cleanup with
    | true => rw [hC] at hEv; cases hEv
    | false =>
      rw [hC] at hEv; dsimp at hEv
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at hEv; cases hEv
      | some sl => rw [h0] at hEv; cases sl with | dead => cases hEv | live o => cases o <;> cases hEv
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    rw [hTm] at hEv; cases hEv
  | switchInt discr targets =>
    rw [hTm] at hEv hEdges; dsimp [checkAbsTerminatorEdges] at hEv hEdges
    let ⟨hOwEdge, hBrEdges⟩ := bool_and_true hEdges
    cases hD : evalPrimitiveOperand body.locals frame.locals discr with
    | error _ => rw [hD] at hEv; cases hEv
    | ok res =>
      let ⟨dv, locsAfter⟩ := res
      rw [hD] at hEv; dsimp at hEv
      have hEnvAfter := deinitMovePrimAbs_sound hEnv hD
      cases dv with
      | scalar sv =>
        dsimp at hEv
        cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok tgt =>
          rw [hSw] at hEv; injection hEv with hEq; subst hEq
          refine ⟨tgt, locsAfter, rfl, hEnvAfter.1, fun hLt => ?_⟩
          cases evalSwitchBranches_cases hSw with
          | inl hCase =>
            let ⟨cb, hMem⟩ := hCase
            have hBr := list_all_mem_true hBrEdges hMem
            exact checkAbsEdge_sound hBr hLt hEnvAfter
          | inr hCase =>
            let ⟨hTgtEq, _⟩ := hCase
            subst hTgtEq
            exact checkAbsEdge_sound hOwEdge hLt hEnvAfter
      | bool b =>
        dsimp at hEv
        cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok tgt =>
          rw [hSw] at hEv; injection hEv with hEq; subst hEq
          refine ⟨tgt, locsAfter, rfl, hEnvAfter.1, fun hLt => ?_⟩
          cases evalBoolSwitchBranches_cases hSw with
          | inl hCase =>
            let ⟨cb, hMem⟩ := hCase
            have hBr := list_all_mem_true hBrEdges hMem
            exact checkAbsEdge_sound hBr hLt hEnvAfter
          | inr hTgtEq =>
            subst hTgtEq
            exact checkAbsEdge_sound hOwEdge hLt hEnvAfter
      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

/-! #### Shared `SameLiveness` & `DeadMaskedEq` Bisimulation Infrastructure -/

private noncomputable def SameLiveness : LocalSlot → LocalSlot → Prop
  | .dead, .dead => True
  | .live _, .live _ => True
  | _, _ => False

private theorem sameLiveness_refl (sl : LocalSlot) : SameLiveness sl sl := by
  cases sl <;> exact True.intro

private theorem sameLiveness_symm {s₁ s₂ : LocalSlot}
    (h : SameLiveness s₁ s₂) : SameLiveness s₂ s₁ := by
  cases s₁ <;> cases s₂ <;> exact h

private noncomputable def DeadMaskedEq (bodyLocals : List MirTy)
    (D : LocalId → Prop) (locs₁ locs₂ : List LocalSlot) : Prop :=
  LocalsWellTyped bodyLocals locs₁ ∧
  LocalsWellTyped bodyLocals locs₂ ∧
  ∀ i,
    (∀ sl₁ sl₂,
      Trusted.MirSemantics.getElem? locs₁ i = some sl₁ →
      Trusted.MirSemantics.getElem? locs₂ i = some sl₂ →
      SameLiveness sl₁ sl₂) ∧
    (¬ D i →
      Trusted.MirSemantics.getElem? locs₁ i =
        Trusted.MirSemantics.getElem? locs₂ i)

private theorem deadMaskedEq_refl {bodyLocals : List MirTy} {D : LocalId → Prop}
    {locs : List LocalSlot} (hWt : LocalsWellTyped bodyLocals locs) :
    DeadMaskedEq bodyLocals D locs locs := by
  refine ⟨hWt, hWt, fun i => ⟨?_, fun _ => rfl⟩⟩
  intro sl₁ sl₂ h1 h2
  rw [h1] at h2; injection h2 with hEq; subst hEq
  exact sameLiveness_refl sl₁

private theorem deadMaskedEq_mono {bodyLocals : List MirTy}
    {D₁ D₂ : LocalId → Prop} {locs₁ locs₂ : List LocalSlot}
    (hImp : ∀ d, D₁ d → D₂ d)
    (hMask : DeadMaskedEq bodyLocals D₁ locs₁ locs₂) :
    DeadMaskedEq bodyLocals D₂ locs₁ locs₂ := by
  let ⟨hWt1, hWt2, hAll⟩ := hMask
  exact ⟨hWt1, hWt2, fun i =>
    ⟨(hAll i).1, fun hNot2 => (hAll i).2 (fun h1 => hNot2 (hImp i h1))⟩⟩

private theorem deadMaskedEq_set_same {bodyLocals : List MirTy}
    {D : LocalId → Prop} {locs₁ locs₂ locs₁' locs₂' : List LocalSlot}
    {id : LocalId} {ty : MirTy} {sl : LocalSlot}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSet1 : setElem? locs₁ id sl = some locs₁')
    (hSet2 : setElem? locs₂ id sl = some locs₂')
    (hSlWt : SlotWellTyped ty sl) :
    DeadMaskedEq bodyLocals (fun d => D d ∧ d ≠ id) locs₁' locs₂' := by
  let ⟨hWt1, hWt2, hAll⟩ := hMask
  refine ⟨localsWellTyped_set hWt1 hTy hSet1 hSlWt,
          localsWellTyped_set hWt2 hTy hSet2 hSlWt, fun i => ?_⟩
  cases hEq : Nat.beq i id with
  | true =>
    have hi := nat_beq_eq hEq; subst hi
    rw [setElem?_getElem?_same hSet1, setElem?_getElem?_same hSet2]
    refine ⟨?_, fun _ => rfl⟩
    intro sl₁ sl₂ h1 h2
    injection h1 with e1; injection h2 with e2; subst e1; subst e2
    exact sameLiveness_refl sl
  | false =>
    have hNe := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSet1 hNe, setElem?_getElem?_ne hSet2 hNe]
    exact ⟨(hAll i).1, fun hNot => (hAll i).2 (fun hDi => hNot ⟨hDi, hNe⟩)⟩

private theorem deadMaskedEq_set_left_live {bodyLocals : List MirTy}
    {D : LocalId → Prop} {locs₁ locs₂ locs₁' : List LocalSlot}
    {id : LocalId} {ty : MirTy} {opt₁ opt₂ : Option Val}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hGet2 : Trusted.MirSemantics.getElem? locs₂ id = some (.live opt₂))
    (hSet1 : setElem? locs₁ id (.live opt₁) = some locs₁')
    (hSlWt : SlotWellTyped ty (.live opt₁)) :
    DeadMaskedEq bodyLocals (fun d => D d ∨ d = id) locs₁' locs₂ := by
  let ⟨hWt1, hWt2, hAll⟩ := hMask
  refine ⟨localsWellTyped_set hWt1 hTy hSet1 hSlWt, hWt2, fun i => ?_⟩
  cases hEq : Nat.beq i id with
  | true =>
    have hi := nat_beq_eq hEq; subst hi
    rw [setElem?_getElem?_same hSet1, hGet2]
    refine ⟨?_, fun hNot => False.elim (hNot (Or.inr rfl))⟩
    intro sl₁ sl₂ h1 h2
    injection h1 with e1; injection h2 with e2; subst e1; subst e2
    exact True.intro
  | false =>
    have hNe := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSet1 hNe]
    exact ⟨(hAll i).1, fun hNot => (hAll i).2 (fun hDi => hNot (Or.inl hDi))⟩

private theorem evalOperandToSlot_untouched_bisim {bodyLocals : List MirTy}
    {D : LocalId → Prop} {locs₁ locs₂ : List LocalSlot} {op : Operand}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hUntouched : ∀ d, D d → operandTouchesLocal d op = false) :
    (∃ fk,
      evalOperandToSlot bodyLocals locs₁ op = .error fk ∧
      evalOperandToSlot bodyLocals locs₂ op = .error fk) ∨
    (∃ ty optVal locs₁' locs₂',
      evalOperandToSlot bodyLocals locs₁ op = .ok (ty, optVal, locs₁') ∧
      evalOperandToSlot bodyLocals locs₂ op = .ok (ty, optVal, locs₂') ∧
      DeadMaskedEq bodyLocals D locs₁' locs₂') := by
  let ⟨hWt1, hWt2, hAll⟩ := hMask
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot]
    cases evalConstLit c.ty c.lit with
    | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
    | ok v => exact Or.inr ⟨c.ty, some v, locs₁, locs₂, rfl, rfl, hMask⟩
  | copy p =>
    dsimp [evalOperandToSlot]
    cases hProj : p.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      have hNotD : ¬ D p.localId := by
        intro hDp
        have hF := hUntouched p.localId hDp
        dsimp [operandTouchesLocal] at hF
        rw [nat_beq_refl] at hF; cases hF
      rw [← (hAll p.localId).2 hNotD]
      cases Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        cases Trusted.MirSemantics.getElem? locs₁ p.localId with
        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | some sl =>
          cases sl with
          | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
          | live optVal => exact Or.inr ⟨ty, optVal, locs₁, locs₂, rfl, rfl, hMask⟩
  | move p =>
    dsimp [evalOperandToSlot]
    cases hProj : p.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      have hNotD : ¬ D p.localId := by
        intro hDp
        have hF := hUntouched p.localId hDp
        dsimp [operandTouchesLocal] at hF
        rw [nat_beq_refl] at hF; cases hF
      have hEqAt := (hAll p.localId).2 hNotD
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        have hLtB : p.localId < bodyLocals.length := getElem?_some_lt hTy
        let ⟨sl₁, hG1⟩ := getElem?_some_of_lt locs₁ p.localId (by rw [hWt1.1]; exact hLtB)
        have hG2 : Trusted.MirSemantics.getElem? locs₂ p.localId = some sl₁ := by
          rw [← hEqAt]; exact hG1
        rw [hG1, hG2]
        cases sl₁ with
        | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
        | live optVal =>
          dsimp
          let ⟨locs₁', hSet1⟩ := setElem?_some_of_lt locs₁ p.localId (liveUninitSlot ty)
            (by rw [hWt1.1]; exact hLtB)
          let ⟨locs₂', hSet2⟩ := setElem?_some_of_lt locs₂ p.localId (liveUninitSlot ty)
            (by rw [hWt2.1]; exact hLtB)
          rw [hSet1, hSet2]
          have hMaskSub := deadMaskedEq_set_same hMask hTy hSet1 hSet2
            (liveUninitSlot_wellTyped ty)
          exact Or.inr ⟨ty, optVal, locs₁', locs₂', rfl, rfl,
            deadMaskedEq_mono (fun _ h => h.1) hMaskSub⟩

private theorem evalPrimitiveOperand_untouched_bisim {bodyLocals : List MirTy}
    {D : LocalId → Prop} {locs₁ locs₂ : List LocalSlot} {op : Operand}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hUntouched : ∀ d, D d → operandTouchesLocal d op = false) :
    (∃ fk,
      evalPrimitiveOperand bodyLocals locs₁ op = .error fk ∧
      evalPrimitiveOperand bodyLocals locs₂ op = .error fk) ∨
    (∃ v locs₁' locs₂',
      evalPrimitiveOperand bodyLocals locs₁ op = .ok (v, locs₁') ∧
      evalPrimitiveOperand bodyLocals locs₂ op = .ok (v, locs₂') ∧
      DeadMaskedEq bodyLocals D locs₁' locs₂') := by
  dsimp [evalPrimitiveOperand]
  cases evalOperandToSlot_untouched_bisim hMask hUntouched with
  | inl hCase =>
    let ⟨fk, hE1, hE2⟩ := hCase
    rw [hE1, hE2]; exact Or.inl ⟨fk, rfl, rfl⟩
  | inr hCase =>
    let ⟨ty, optVal, locs₁', locs₂', hO1, hO2, hMask'⟩ := hCase
    rw [hO1, hO2]; dsimp
    cases isPrimitiveReadableTy ty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      cases optVal with
      | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
      | some v => exact Or.inr ⟨v, locs₁', locs₂', rfl, rfl, hMask'⟩

private theorem evalRvalue_untouched_bisim {bodyLocals : List MirTy}
    {D : LocalId → Prop} {locs₁ locs₂ : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hUntouched : ∀ d, D d → rvalueTouchesLocal d rv = false) :
    (∃ fk,
      evalRvalue bodyLocals locs₁ dstTy rv = .error fk ∧
      evalRvalue bodyLocals locs₂ dstTy rv = .error fk) ∨
    (∃ v locs₁' locs₂',
      evalRvalue bodyLocals locs₁ dstTy rv = .ok (v, locs₁') ∧
      evalRvalue bodyLocals locs₂ dstTy rv = .ok (v, locs₂') ∧
      DeadMaskedEq bodyLocals D locs₁' locs₂') := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalue]
    cases evalOperandToSlot_untouched_bisim hMask hUntouched with
    | inl hCase =>
      let ⟨fk, hE1, hE2⟩ := hCase
      rw [hE1, hE2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hCase =>
      let ⟨srcTy, optVal, l1, l2, hO1, hO2, hM1⟩ := hCase
      rw [hO1, hO2]; dsimp
      cases MirTy.beq srcTy dstTy with
      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | true =>
        dsimp
        cases optVal with
        | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
        | some v => exact Or.inr ⟨v, l1, l2, rfl, rfl, hM1⟩
  | unaryOp op opnd =>
    dsimp [evalRvalue]
    cases evalPrimitiveOperand_untouched_bisim hMask hUntouched with
    | inl hCase =>
      let ⟨fk, hE1, hE2⟩ := hCase
      rw [hE1, hE2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hCase =>
      let ⟨v, l1, l2, hO1, hO2, hM1⟩ := hCase
      rw [hO1, hO2]; dsimp
      cases evalUnOp op v with
      | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
      | ok res => exact Or.inr ⟨res, l1, l2, rfl, rfl, hM1⟩
  | binaryOp op lhs rhs =>
    dsimp [evalRvalue]
    have hUL : ∀ d, D d → operandTouchesLocal d lhs = false :=
      fun d hD => (bool_or_false (hUntouched d hD)).1
    have hUR : ∀ d, D d → operandTouchesLocal d rhs = false :=
      fun d hD => (bool_or_false (hUntouched d hD)).2
    cases evalPrimitiveOperand_untouched_bisim hMask hUL with
    | inl hCase =>
      let ⟨fk, hE1, hE2⟩ := hCase
      rw [hE1, hE2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hCase =>
      let ⟨vl, l1, l2, hO1, hO2, hM1⟩ := hCase
      rw [hO1, hO2]; dsimp
      cases evalPrimitiveOperand_untouched_bisim hM1 hUR with
      | inl hCase =>
        let ⟨fk, hER1, hER2⟩ := hCase
        rw [hER1, hER2]; exact Or.inl ⟨fk, rfl, rfl⟩
      | inr hCase =>
        let ⟨vr, l1', l2', hOR1, hOR2, hM2⟩ := hCase
        rw [hOR1, hOR2]; dsimp
        cases evalBinOp op vl vr with
        | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
        | ok res => exact Or.inr ⟨res, l1', l2', rfl, rfl, hM2⟩
  | discriminant p =>
    dsimp [evalRvalue]
    cases hProj : p.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      have hNotD : ¬ D p.localId := by
        intro hDp
        have hF := hUntouched p.localId hDp
        dsimp [rvalueTouchesLocal] at hF
        rw [nat_beq_refl] at hF; cases hF
      rw [← (hMask.2.2 p.localId).2 hNotD]
      cases Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        cases ty with
        | enum ety =>
          cases Trusted.MirSemantics.getElem? locs₁ p.localId with
          | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
          | some slot =>
            dsimp
            cases enumAdmitted ety with
            | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
            | true =>
              dsimp
              cases ety.tagRepr with
              | zeroSized =>
                cases slot with
                | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                    | some disc =>
                      exact Or.inr ⟨_, locs₁, locs₂, rfl, rfl, hMask⟩
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                        | some _ => exact Or.inr ⟨_, locs₁, locs₂, rfl, rfl, hMask⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ =>
                      exact Or.inl ⟨.unsupported, rfl, rfl⟩
              | scalar _ _ =>
                cases slot with
                | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
                | live opt =>
                  cases opt with
                  | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                        | some _ => exact Or.inr ⟨_, locs₁, locs₂, rfl, rfl, hMask⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ =>
                      exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
          exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported =>
    exact Or.inl ⟨.unsupported, rfl, rfl⟩

private theorem writePlace_deadMasked_bisim {bodyLocals : List MirTy}
    {D : LocalId → Prop} {locs₁ locs₂ : List LocalSlot}
    {dstId : LocalId} {dstTy : MirTy} {val : Val}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals dstId = some dstTy) :
    (∃ fk,
      writePlace locs₁ dstId dstTy val = .error fk ∧
      writePlace locs₂ dstId dstTy val = .error fk) ∨
    (∃ locs₁' locs₂',
      writePlace locs₁ dstId dstTy val = .ok locs₁' ∧
      writePlace locs₂ dstId dstTy val = .ok locs₂' ∧
      DeadMaskedEq bodyLocals (fun d => D d ∧ d ≠ dstId) locs₁' locs₂') := by
  let ⟨hWt1, hWt2, hAll⟩ := hMask
  dsimp [writePlace]
  cases hChk : checkVal val dstTy with
  | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | true =>
    dsimp
    have hLtB : dstId < bodyLocals.length := getElem?_some_lt hTy
    let ⟨sl₁, hG1⟩ := getElem?_some_of_lt locs₁ dstId (by rw [hWt1.1]; exact hLtB)
    let ⟨sl₂, hG2⟩ := getElem?_some_of_lt locs₂ dstId (by rw [hWt2.1]; exact hLtB)
    have hLive := (hAll dstId).1 sl₁ sl₂ hG1 hG2
    rw [hG1, hG2]
    cases sl₁ with
    | dead =>
      cases sl₂ with
      | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
      | live _ => cases hLive
    | live _ =>
      cases sl₂ with
      | dead => cases hLive
      | live _ =>
        let ⟨locs₁', hSet1⟩ := setElem?_some_of_lt locs₁ dstId (.live (some val))
          (by rw [hWt1.1]; exact hLtB)
        let ⟨locs₂', hSet2⟩ := setElem?_some_of_lt locs₂ dstId (.live (some val))
          (by rw [hWt2.1]; exact hLtB)
        rw [hSet1, hSet2]
        exact Or.inr ⟨locs₁', locs₂', rfl, rfl,
          deadMaskedEq_set_same hMask hTy hSet1 hSet2 hChk⟩

private theorem evalStatement_kept_deadMasked_bisim {bSrc bTgt : Body}
    {D₁ D₂ : LocalId → Prop} {fSrc fTgt : FrameState}
    {cm : CallerMemory} {stmt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hMask : DeadMaskedEq bSrc.locals D₁ fSrc.locals fTgt.locals)
    (hNop : stmt = .nop → ∀ d, D₁ d → D₂ d)
    (hUnsup : stmt = .unsupported → False ∨ True)
    (hSLive : ∀ id, stmt = .storageLive id → ∀ d, D₁ d → d = id ∨ D₂ d)
    (hSDead : ∀ id, stmt = .storageDead id → ∀ d, D₁ d → d = id ∨ D₂ d)
    (hAsg : ∀ lhs rv, stmt = .assign lhs rv →
      ∀ d, D₁ d →
        rvalueTouchesLocal d rv = false ∧
        ((lhs.projection.isEmpty = true ∧ d = lhs.localId) ∨ D₂ d)) :
    (∃ fk,
      evalStatement bSrc fSrc cm stmt = .fault fk ∧
      evalStatement bTgt fTgt cm stmt = .fault fk) ∨
    (∃ locs₁' locs₂',
      evalStatement bSrc fSrc cm stmt =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs₁' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs₂' }],
                callerMem := cm } ∧
      DeadMaskedEq bSrc.locals D₂ locs₁' locs₂') := by
  let _ := hUnsup
  let ⟨hWt1, hWt2, _⟩ := hMask
  cases stmt with
  | nop =>
    exact Or.inr ⟨fSrc.locals, fTgt.locals, rfl, rfl,
      deadMaskedEq_mono (hNop rfl) hMask⟩
  | unsupported =>
    exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | storageLive id =>
    dsimp [evalStatement]
    rw [← hLocEq]
    cases hTy : Trusted.MirSemantics.getElem? bSrc.locals id with
    | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | some ty =>
      dsimp
      have hLtB : id < bSrc.locals.length := getElem?_some_lt hTy
      let ⟨locs₁', hSet1⟩ := setElem?_some_of_lt fSrc.locals id (liveUninitSlot ty)
        (by rw [hWt1.1]; exact hLtB)
      let ⟨locs₂', hSet2⟩ := setElem?_some_of_lt fTgt.locals id (liveUninitSlot ty)
        (by rw [hWt2.1]; exact hLtB)
      rw [hSet1, hSet2]
      have hSub := deadMaskedEq_set_same hMask hTy hSet1 hSet2
        (liveUninitSlot_wellTyped ty)
      refine Or.inr ⟨locs₁', locs₂', rfl, rfl, deadMaskedEq_mono ?_ hSub⟩
      intro d ⟨hD1, hNe⟩
      cases hSLive id rfl d hD1 with
      | inl hEq => exact False.elim (hNe hEq)
      | inr hD2 => exact hD2
  | storageDead id =>
    dsimp [evalStatement]
    cases Nat.beq id 0 with
    | true => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | false =>
      dsimp
      cases Nat.lt_or_ge id bSrc.locals.length with
      | inr hGe =>
        rw [setElem?_none_of_ge fSrc.locals id .dead (by rw [hWt1.1]; exact hGe),
            setElem?_none_of_ge fTgt.locals id .dead (by rw [hWt2.1]; exact hGe)]
        exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | inl hLtB =>
        let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals id hLtB
        let ⟨locs₁', hSet1⟩ := setElem?_some_of_lt fSrc.locals id .dead
          (by rw [hWt1.1]; exact hLtB)
        let ⟨locs₂', hSet2⟩ := setElem?_some_of_lt fTgt.locals id .dead
          (by rw [hWt2.1]; exact hLtB)
        rw [hSet1, hSet2]
        have hSub := deadMaskedEq_set_same hMask hTy hSet1 hSet2 True.intro
        refine Or.inr ⟨locs₁', locs₂', rfl, rfl, deadMaskedEq_mono ?_ hSub⟩
        intro d ⟨hD1, hNe⟩
        cases hSDead id rfl d hD1 with
        | inl hEq => exact False.elim (hNe hEq)
        | inr hD2 => exact hD2
  | assign lhs rv =>
    dsimp [evalStatement]
    cases hP : lhs.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      rw [← hLocEq]
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals lhs.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some dstTy =>
        dsimp
        have hUntouched : ∀ d, D₁ d → rvalueTouchesLocal d rv = false :=
          fun d hD1 => (hAsg lhs rv rfl d hD1).1
        cases evalRvalue_untouched_bisim (dstTy := dstTy) hMask hUntouched with
        | inl hCase =>
          let ⟨fk, hE1, hE2⟩ := hCase
          rw [hE1, hE2]; exact Or.inl ⟨fk, rfl, rfl⟩
        | inr hCase =>
          let ⟨val, l1, l2, hO1, hO2, hM1⟩ := hCase
          rw [hO1, hO2]; dsimp
          cases writePlace_deadMasked_bisim (val := val) hM1 hTy with
          | inl hCase =>
            let ⟨fk, hWE1, hWE2⟩ := hCase
            rw [hWE1, hWE2]; exact Or.inl ⟨fk, rfl, rfl⟩
          | inr hCase =>
            let ⟨locs₁', locs₂', hWO1, hWO2, hM2⟩ := hCase
            rw [hWO1, hWO2]
            refine Or.inr ⟨locs₁', locs₂', rfl, rfl, deadMaskedEq_mono ?_ hM2⟩
            intro d ⟨hD1, hNe⟩
            cases (hAsg lhs rv rfl d hD1).2 with
            | inl hCase =>
              let ⟨_, hEq⟩ := hCase
              exact False.elim (hNe hEq)
            | inr hD2 => exact hD2

private theorem evalTerminator_deadMasked_bisim {bSrc bTgt : Body}
    {bbSrc bbTgt : BasicBlock} {D : LocalId → Prop}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hTerm : bbSrc.terminator = bbTgt.terminator)
    (hMask : DeadMaskedEq bSrc.locals D fSrc.locals fTgt.locals)
    (hNonZero : ∀ d, D d → d ≠ 0)
    (hSwUntouched : ∀ discr targets,
      bbTgt.terminator = .switchInt discr targets →
      ∀ d, D d → operandTouchesLocal d discr = false) :
    (∃ tgt locs₁' locs₂',
      evalTerminator bSrc bbSrc fSrc cm =
        .step { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs₁' }],
                callerMem := cm } ∧
      evalTerminator bTgt bbTgt fTgt cm =
        .step { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs₂' }],
                callerMem := cm } ∧
      DeadMaskedEq bSrc.locals D locs₁' locs₂') ∨
    (∃ out,
      evalTerminator bSrc bbSrc fSrc cm = .done out ∧
      evalTerminator bTgt bbTgt fTgt cm = .done out) ∨
    (∃ fk,
      evalTerminator bSrc bbSrc fSrc cm = .fault fk ∧
      evalTerminator bTgt bbTgt fTgt cm = .fault fk) := by
  unfold evalTerminator
  rw [hTerm, ← hLocEq, hClean]
  cases hTm : bbTgt.terminator with
  | goto tgt =>
    exact Or.inl ⟨tgt, fSrc.locals, fTgt.locals, rfl, rfl, hMask⟩
  | return_ =>
    dsimp
    cases bbTgt.cleanup with
    | true => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
    | false =>
      dsimp
      have hNot0 : ¬ D 0 := fun hD0 => hNonZero 0 hD0 rfl
      rw [← (hMask.2.2 0).2 hNot0]
      cases Trusted.MirSemantics.getElem? fSrc.locals 0 with
      | none => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
      | some sl =>
        cases sl with
        | dead => exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
        | live opt =>
          cases opt with
          | none => exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
          | some retVal => exact Or.inr (Or.inl ⟨.returned ⟨retVal, cm⟩, rfl, rfl⟩)
  | unreachable =>
    exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
  | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
  | switchInt discr targets =>
    dsimp
    cases evalPrimitiveOperand_untouched_bisim hMask (hSwUntouched discr targets hTm) with
    | inl hCase =>
      let ⟨fk, hE1, hE2⟩ := hCase
      rw [hE1, hE2]; exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
    | inr hCase =>
      let ⟨dv, l1, l2, hO1, hO2, hM1⟩ := hCase
      rw [hO1, hO2]; dsimp
      cases dv with
      | scalar sv =>
        dsimp
        cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error fk => exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
        | ok tgt => exact Or.inl ⟨tgt, l1, l2, rfl, rfl, hM1⟩
      | bool b =>
        dsimp
        cases evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error fk => exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
        | ok tgt => exact Or.inl ⟨tgt, l1, l2, rfl, rfl, hM1⟩
      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ =>
        exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)


/-! #### Additional Slice A Helpers: `programEq`, `mapOption`, `take`/`drop`,
V2 `*Eq`, & `isDeadAcrossCfg` -/

private theorem blockEq_eq {a b : BasicBlock} (h : blockEq a b = true) : a = b := by
  cases a with
  | mk ss1 tm1 cl1 =>
    cases b with
    | mk ss2 tm2 cl2 =>
      dsimp [blockEq] at h
      let ⟨h12, hTm⟩ := bool_and_true h
      let ⟨hCl, hSs⟩ := bool_and_true h12
      rw [bool_beq_eq hCl, listRel_eq (fun _ _ => stmtEq_eq) hSs,
          terminatorEq_eq hTm]

private theorem bodyEq_eq {a b : Body} (h : bodyEq a b = true) : a = b := by
  cases a with
  | mk ac1 lc1 bb1 un1 id1 =>
    cases b with
    | mk ac2 lc2 bb2 un2 id2 =>
      unfold bodyEq at h
      let ⟨hHdr, hBBs⟩ := bool_and_true h
      let ⟨hAc, hLc, hUn, hId⟩ := bodyHeaderEq_elim hHdr
      dsimp at hAc hLc hUn hId hBBs
      rw [hAc, hLc, hUn, hId, listRel_eq (fun _ _ => blockEq_eq) hBBs]

private theorem programEq_eq {a b : Program} (h : programEq a b = true) : a = b := by
  cases a with
  | mk bs1 ed1 pw1 pv1 sc1 =>
    cases b with
    | mk bs2 ed2 pw2 pv2 sc2 =>
      unfold programEq at h
      let ⟨hHdr, hBs⟩ := bool_and_true h
      let ⟨hPw, hPv, hEd, hSc⟩ := programHeaderEq_elim hHdr
      dsimp at hPw hPv hEd hSc hBs
      rw [hPw, hPv, hEd, hSc, listRel_eq (fun _ _ => bodyEq_eq) hBs]

private theorem stringBeq_refl (s : String) : stringBeq s s = true := by
  unfold stringBeq
  have hList : ∀ (xs : List UInt8), List.beq xs xs = true := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      dsimp [List.beq]
      rw [beq_self_eq_true x, ih]
      rfl
  exact hList s.toByteArray.data.toList

private theorem bodyHeaderEq_refl (b : Body) : bodyHeaderEq b b = true := by
  unfold bodyHeaderEq
  rw [nat_beq_refl, mirTy_beqList_refl, bool_beq_refl, stringBeq_refl]
  rfl

private theorem programHeaderEq_refl (p : Program) : programHeaderEq p p = true := by
  unfold programHeaderEq
  rw [nat_beq_refl, nat_beq_refl, nat_beq_refl, scopeEq_refl]
  rfl

private theorem fullSemanticEquiv_refl (p : Program) : FullSemanticEquiv p p := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact ⟨Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, Iff.rfl⟩
  · intro _ _; exact Iff.rfl
  · intro defId bSrc bTgt _ hBS hBT
    rw [hBS] at hBT; injection hBT with hEq; subst hEq
    exact Iff.rfl

private theorem mapOption_length {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} (h : mapOption f xs = some ys) :
    ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    injection h with hEq; subst hEq; rfl
  | cons x rest ih =>
    dsimp [mapOption] at h
    cases hfx : f x with
    | none => rw [hfx] at h; cases h
    | some y =>
      rw [hfx] at h
      cases hmr : mapOption f rest with
      | none => rw [hmr] at h; cases h
      | some ys' =>
        rw [hmr] at h
        injection h with hEq; subst hEq
        dsimp [List.length]
        rw [ih hmr]

private theorem mapOption_getElem?_left {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} {i : Nat} {x : α}
    (h : mapOption f xs = some ys)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) :
    ∃ y, Trusted.MirSemantics.getElem? ys i = some y ∧ f x = some y := by
  induction xs generalizing ys i with
  | nil => cases hGet
  | cons a rest ih =>
    dsimp [mapOption] at h
    cases hfa : f a with
    | none => rw [hfa] at h; cases h
    | some b =>
      rw [hfa] at h
      cases hmr : mapOption f rest with
      | none => rw [hmr] at h; cases h
      | some bs =>
        rw [hmr] at h
        injection h with hEq; rw [← hEq]
        cases i with
        | zero =>
          injection hGet with hxa; subst hxa
          exact ⟨b, rfl, hfa⟩
        | succ k =>
          dsimp [Trusted.MirSemantics.getElem?]
          exact ih hmr hGet

private theorem mapOption_getElem?_right {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} {i : Nat} {y : β}
    (h : mapOption f xs = some ys)
    (hGet : Trusted.MirSemantics.getElem? ys i = some y) :
    ∃ x, Trusted.MirSemantics.getElem? xs i = some x ∧ f x = some y := by
  induction xs generalizing ys i with
  | nil =>
    injection h with hEq; rw [← hEq] at hGet; cases hGet
  | cons a rest ih =>
    dsimp [mapOption] at h
    cases hfa : f a with
    | none => rw [hfa] at h; cases h
    | some b =>
      rw [hfa] at h
      cases hmr : mapOption f rest with
      | none => rw [hmr] at h; cases h
      | some bs =>
        rw [hmr] at h
        injection h with hEq; rw [← hEq] at hGet
        cases i with
        | zero =>
          injection hGet with hyb; subst hyb
          exact ⟨a, rfl, hfa⟩
        | succ k =>
          dsimp [Trusted.MirSemantics.getElem?]
          exact ih hmr hGet

private theorem mapOption_getElem?_none_iff {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} (i : Nat) (h : mapOption f xs = some ys) :
    Trusted.MirSemantics.getElem? xs i = none ↔
      Trusted.MirSemantics.getElem? ys i = none := by
  have hLen := mapOption_length h
  constructor
  · intro hN
    cases hY : Trusted.MirSemantics.getElem? ys i with
    | none => rfl
    | some y =>
      let ⟨x, hX, _⟩ := mapOption_getElem?_right h hY
      rw [hN] at hX; cases hX
  · intro hN
    cases hX : Trusted.MirSemantics.getElem? xs i with
    | none => rfl
    | some x =>
      let ⟨y, hY, _⟩ := mapOption_getElem?_left h hX
      rw [hN] at hY; cases hY

private theorem zip_cons_cons {α β : Type} (c : α) (cs : List α) (x : β) (xs : List β) :
    List.zip (c :: cs) (x :: xs) = (c, x) :: List.zip cs xs :=
  rfl

private theorem zip_length_eq {α β : Type} {cs : List α} {xs : List β}
    (hLen : cs.length = xs.length) :
    (List.zip cs xs).length = xs.length := by
  induction xs generalizing cs with
  | nil =>
    cases cs with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons x rest ih =>
    cases cs with
    | nil => cases hLen
    | cons c cs' =>
      rw [zip_cons_cons]
      dsimp only [List.length]
      rw [ih (Nat.succ.inj hLen)]

private theorem mapOption_zip_getElem?_left {α β γ : Type} {f : (α × β) → Option γ}
    {cs : List α} {xs : List β} {ys : List γ}
    (hLenC : cs.length = xs.length)
    (hMap : mapOption f (List.zip cs xs) = some ys)
    {i : Nat} {x : β}
    (hX : Trusted.MirSemantics.getElem? xs i = some x) :
    ∃ c y,
      Trusted.MirSemantics.getElem? cs i = some c ∧
      Trusted.MirSemantics.getElem? ys i = some y ∧
      f (c, x) = some y := by
  induction xs generalizing cs ys i with
  | nil => cases hX
  | cons x₀ xs ih =>
    cases cs with
    | nil => cases hLenC
    | cons c₀ cs =>
      rw [zip_cons_cons] at hMap
      dsimp only [mapOption] at hMap
      cases hf0 : f (c₀, x₀) with
      | none => rw [hf0] at hMap; cases hMap
      | some y₀ =>
        rw [hf0] at hMap
        cases hmr : mapOption f (List.zip cs xs) with
        | none => rw [hmr] at hMap; cases hMap
        | some ys' =>
          rw [hmr] at hMap
          injection hMap with hEq; rw [← hEq]
          cases i with
          | zero =>
            injection hX with hxEq; subst hxEq
            exact ⟨c₀, y₀, rfl, rfl, hf0⟩
          | succ k =>
            exact ih (Nat.succ.inj hLenC) hmr hX

private theorem mapOption_zip_getElem?_right {α β γ : Type} {f : (α × β) → Option γ}
    {cs : List α} {xs : List β} {ys : List γ}
    (hLenC : cs.length = xs.length)
    (hMap : mapOption f (List.zip cs xs) = some ys)
    {i : Nat} {y : γ}
    (hY : Trusted.MirSemantics.getElem? ys i = some y) :
    ∃ c x,
      Trusted.MirSemantics.getElem? cs i = some c ∧
      Trusted.MirSemantics.getElem? xs i = some x ∧
      f (c, x) = some y := by
  have hLenY : ys.length = xs.length :=
    (mapOption_length hMap).trans (zip_length_eq hLenC)
  have hLtX : i < xs.length := by rw [← hLenY]; exact getElem?_some_lt hY
  let ⟨x, hX⟩ := getElem?_some_of_lt xs i hLtX
  let ⟨c, y', hC, hY', hF⟩ := mapOption_zip_getElem?_left hLenC hMap hX
  rw [hY] at hY'; injection hY' with hEq; subst hEq
  exact ⟨c, x, hC, hX, hF⟩

private theorem take_length_of_le {α : Type} {xs : List α} {n : Nat}
    (h : n ≤ xs.length) : (xs.take n).length = n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ k => exact False.elim (Nat.not_succ_le_zero k h)
  | cons _ rest ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp [List.take, List.length]
      rw [ih (Nat.le_of_succ_le_succ h)]

private theorem getElem?_take_of_lt {α : Type} (xs : List α) {n i : Nat}
    (h : i < n) :
    Trusted.MirSemantics.getElem? (xs.take n) i =
      Trusted.MirSemantics.getElem? xs i := by
  induction xs generalizing n i with
  | nil =>
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero i h)
    | succ _ => rfl
  | cons a rest ih =>
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero i h)
    | succ m =>
      cases i with
      | zero => rfl
      | succ k => exact ih (Nat.lt_of_succ_lt_succ h)

private theorem getElem?_take_of_ge {α : Type} (xs : List α) {n i : Nat}
    (h : n ≤ i) :
    Trusted.MirSemantics.getElem? (xs.take n) i = none := by
  induction xs generalizing n i with
  | nil => cases n <;> rfl
  | cons _ rest ih =>
    cases n with
    | zero => rfl
    | succ m =>
      cases i with
      | zero => exact False.elim (Nat.not_succ_le_zero m h)
      | succ k => exact ih (Nat.le_of_succ_le_succ h)

private theorem setElem?_take_comm {α : Type} {xs xs' : List α} {n i : Nat} {v : α}
    (hi : i < n) (hSet : setElem? xs i v = some xs') :
    setElem? (xs.take n) i v = some (xs'.take n) := by
  induction xs generalizing xs' n i with
  | nil => cases hSet
  | cons a rest ih =>
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero i hi)
    | succ m =>
      cases i with
      | zero =>
        injection hSet with hEq; subst hEq; rfl
      | succ k =>
        dsimp [setElem?] at hSet
        cases hSub : setElem? rest k v with
        | none => rw [hSub] at hSet; cases hSet
        | some sub =>
          rw [hSub] at hSet; injection hSet with hEq; subst hEq
          dsimp [List.take, setElem?]
          rw [ih (Nat.lt_of_succ_lt_succ hi) hSub]

private theorem list_all_eq_take_drop {α : Type} (p : α → Bool) (xs : List α) (n : Nat) :
    xs.all p = ((xs.take n).all p && (xs.drop n).all p) := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons x rest ih =>
    cases n with
    | zero =>
      dsimp [List.take, List.drop, List.all]
      rfl
    | succ m =>
      dsimp [List.take, List.drop, List.all]
      rw [ih m, Bool.and_assoc]

private theorem take_take_of_le {α : Type} (ys : List α) {ac m : Nat}
    (hLe : ac ≤ m) : (ys.take m).take ac = ys.take ac := by
  induction ys generalizing ac m with
  | nil => cases m <;> cases ac <;> rfl
  | cons r rs ih =>
    cases ac with
    | zero => rfl
    | succ ac' =>
      cases m with
      | zero => exact False.elim (Nat.not_succ_le_zero ac' hLe)
      | succ m' =>
        dsimp [List.take]
        rw [ih (Nat.le_of_succ_le_succ hLe)]

private theorem take_drop1_of_lt {α : Type} (xs : List α) {ac nc : Nat}
    (hLt : ac < nc) :
    ((xs.take nc).drop 1).take ac = (xs.drop 1).take ac := by
  cases nc with
  | zero => exact False.elim (Nat.not_lt_zero ac hLt)
  | succ m =>
    cases xs with
    | nil => rfl
    | cons _ rest =>
      dsimp [List.take, List.drop]
      exact take_take_of_le rest (Nat.le_of_succ_le_succ hLt)

/-! #### V2 Structural Equality & Storage Helpers -/

private theorem profileModeEq_eq {a b : ProfileModeV2}
    (h : profileModeEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem profileModeEq_refl (a : ProfileModeV2) : profileModeEq a a = true := by
  cases a <;> rfl

private theorem placeV2Eq_eq : ∀ {a b : PlaceV2}, placeV2Eq a b = true → a = b
  | .local i1, .local i2, h => by rw [nat_beq_eq h]
  | .rawDeref p1, .rawDeref p2, h => by rw [nat_beq_eq h]
  | .rawDerefFieldOffset p1 o1, .rawDerefFieldOffset p2 o2, h => by
    let ⟨h1, h2⟩ := bool_and_true h
    rw [nat_beq_eq h1, nat_beq_eq h2]
  | .local _, .rawDeref _, h
  | .local _, .rawDerefFieldOffset _ _, h
  | .rawDeref _, .local _, h
  | .rawDeref _, .rawDerefFieldOffset _ _, h
  | .rawDerefFieldOffset _ _, .local _, h
  | .rawDerefFieldOffset _ _, .rawDeref _, h => by
    cases h

private theorem stmtV2Eq_eq {a b : StatementKindV2}
    (h : stmtV2Eq a b = true) : a = b := by
  cases a with
  | v1 s1 =>
    cases b with
    | v1 s2 => rw [stmtEq_eq h]
    | _ => cases h
  | placeMention p1 =>
    cases b with
    | placeMention p2 => rw [placeV2Eq_eq h]
    | _ => cases h
  | assume c1 =>
    cases b with
    | assume c2 => rw [operandEq_eq h]
    | _ => cases h

private theorem blockV2Eq_eq {a b : BasicBlockV2}
    (h : blockV2Eq a b = true) : a = b := by
  cases a with
  | mk ss1 tm1 cl1 =>
    cases b with
    | mk ss2 tm2 cl2 =>
      dsimp [blockV2Eq] at h
      let ⟨h12, hTm⟩ := bool_and_true h
      let ⟨hCl, hSs⟩ := bool_and_true h12
      rw [bool_beq_eq hCl, listRel_eq (fun _ _ => stmtV2Eq_eq) hSs,
          terminatorEq_eq hTm]

private theorem bodyHeaderV2Eq_elim {b₁ b₂ : BodyV2}
    (h : bodyHeaderV2Eq b₁ b₂ = true) :
    b₁.argumentCount = b₂.argumentCount ∧
    b₁.locals = b₂.locals ∧
    b₁.isUnsafe = b₂.isUnsafe ∧
    b₁.identity = b₂.identity := by
  unfold bodyHeaderV2Eq at h
  let ⟨h123, hId⟩ := bool_and_true h
  let ⟨h12, hUns⟩ := bool_and_true h123
  let ⟨hArg, hLoc⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hArg, mirTy_beqList_eq hLoc, bool_beq_eq hUns,
         stringBeq_eq hId⟩

private theorem programHeaderV2Eq_elim {p₁ p₂ : ProgramV2}
    (h : programHeaderV2Eq p₁ p₂ = true) :
    p₁.pointerWidthBits = p₂.pointerWidthBits ∧
    p₁.mirProfileVersion = p₂.mirProfileVersion ∧
    p₁.entryDefId = p₂.entryDefId ∧
    p₁.scope = p₂.scope ∧
    p₁.profileMode = p₂.profileMode := by
  unfold programHeaderV2Eq at h
  let ⟨h1234, hPm⟩ := bool_and_true h
  let ⟨h123, hSc⟩ := bool_and_true h1234
  let ⟨h12, hEnt⟩ := bool_and_true h123
  let ⟨hPw, hVer⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hPw, nat_beq_eq hVer, nat_beq_eq hEnt,
         scopeEq_eq hSc, profileModeEq_eq hPm⟩

private theorem programHeaderV2Eq_entryProgV2 {p₁ p₂ : ProgramV2} (defId : DefId)
    (h : programHeaderV2Eq p₁ p₂ = true) :
    programHeaderV2Eq (entryProgForBodyV2 p₁ defId)
      (entryProgForBodyV2 p₂ defId) = true := by
  let ⟨hPw, hVer, _, hSc, hPm⟩ := programHeaderV2Eq_elim h
  unfold programHeaderV2Eq entryProgForBodyV2
  dsimp
  rw [hPw, hVer, hSc, hPm, nat_beq_refl, nat_beq_refl, nat_beq_refl,
      scopeEq_refl, profileModeEq_refl]
  rfl

private theorem preservesAllStorageAnnotationsLoopV2_get {b₁ b₂ : BodyV2} {n idx : Nat}
    (hLoop : preservesAllStorageAnnotationsLoopV2 b₁ b₂ n = true)
    (hLt : idx < n) :
    hasStorageAnnotationV2 b₁ idx = hasStorageAnnotationV2 b₂ idx := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero idx hLt)
  | succ m ih =>
    dsimp [preservesAllStorageAnnotationsLoopV2] at hLoop
    let ⟨hHere, hRest⟩ := bool_and_true hLoop
    cases Nat.lt_or_ge idx m with
    | inl hSub => exact ih hRest hSub
    | inr hGe =>
      have hEq : idx = m := Nat.le_antisymm (Nat.le_of_succ_le_succ hLt) hGe
      subst hEq
      exact bool_beq_eq hHere

private theorem preservesAllStorageAnnotationsV2_elim {b₁ b₂ : BodyV2}
    (h : preservesAllStorageAnnotationsV2 b₁ b₂ = true) :
    storageAnnotationsInBoundsV2 b₁ = storageAnnotationsInBoundsV2 b₂ ∧
    ∀ idx, idx < b₁.locals.length →
      hasStorageAnnotationV2 b₁ idx = hasStorageAnnotationV2 b₂ idx := by
  unfold preservesAllStorageAnnotationsV2 at h
  let ⟨hBnd, hLoop⟩ := bool_and_true h
  exact ⟨bool_beq_eq hBnd,
         fun _ hLt => preservesAllStorageAnnotationsLoopV2_get hLoop hLt⟩

/-! #### `stepPlainStmtsAbs` Multi-Step Soundness & `isDeadAcrossCfg` Lemmas -/

private theorem stepPlainStmtsAbs_cons_elim {bodyLocals : List MirTy}
    {env exitEnv : List AbsSlot} {s : StatementKind} {ss : List StatementKind}
    (h : stepPlainStmtsAbs bodyLocals env (s :: ss) = some exitEnv) :
    ∃ env',
      stepPlainStmtAbs bodyLocals env s = some env' ∧
      stepPlainStmtsAbs bodyLocals env' ss = some exitEnv := by
  dsimp [stepPlainStmtsAbs] at h
  cases h1 : stepPlainStmtAbs bodyLocals env s with
  | none => rw [h1] at h; cases h
  | some env' => rw [h1] at h; exact ⟨env', rfl, h⟩

private theorem checkDeadAtEntryLoop_getElem? {bTgt : Body}
    {deadAtEntry : BodyDeadCert} :
    ∀ {base dsList k ds},
      checkDeadAtEntryLoop bTgt deadAtEntry base dsList = true →
      Trusted.MirSemantics.getElem? dsList k = some ds →
      ∃ bbTgt,
        Trusted.MirSemantics.getElem? bTgt.basicBlocks (base + k) = some bbTgt ∧
        ∀ d, natElem d ds = true →
          d ≠ 0 ∧
          d < bTgt.locals.length ∧
          isDeadAcrossCfg bTgt.locals.length deadAtEntry
            bTgt.basicBlocks.length d bbTgt.statements bbTgt.terminator = true := by
  intro base dsList
  induction dsList generalizing base with
  | nil => intro _ _ _ hG; cases hG
  | cons ds₀ rest ih =>
    intro k ds hLoop hG
    dsimp [checkDeadAtEntryLoop] at hLoop
    let ⟨hHead, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hG with hEq; subst hEq
      rw [Nat.add_zero]
      cases hBB : Trusted.MirSemantics.getElem? bTgt.basicBlocks base with
      | none => rw [hBB] at hHead; cases hHead
      | some bbTgt =>
        rw [hBB] at hHead; dsimp at hHead
        refine ⟨bbTgt, rfl, fun d hElem => ?_⟩
        have hD := list_all_mem_true hHead (natElem_mem hElem)
        let ⟨h12, hDead⟩ := bool_and_true hD
        let ⟨hNe0B, hLtB⟩ := bool_and_true h12
        exact ⟨nat_ne_of_beq_false (bool_not_true hNe0B),
               nat_blt_lt hLtB, hDead⟩
    | succ m =>
      have hSub := ih hTail hG
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hSub
      exact hSub

private theorem isDeadAcrossCfg_kept_step {bSrc bTgt : Body}
    {deadAtEntry : BodyDeadCert} {numBlocks : Nat}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmt : StatementKind} {restTgt : List StatementKind}
    {termTgt : TerminatorKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks d
          (stmt :: restTgt) termTgt = true)
      fSrc.locals fTgt.locals) :
    (∃ fk,
      evalStatement bSrc fSrc cm stmt = .fault fk ∧
      evalStatement bTgt fTgt cm stmt = .fault fk) ∨
    (∃ locs₁' locs₂',
      evalStatement bSrc fSrc cm stmt =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs₁' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs₂' }],
                callerMem := cm } ∧
      DeadMaskedEq bSrc.locals
        (fun d => d ≠ 0 ∧
          isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks d
            restTgt termTgt = true)
        locs₁' locs₂') := by
  apply evalStatement_kept_deadMasked_bisim hLocEq hMask
  · intro hNop d ⟨hd0, hD⟩; subst hNop; exact ⟨hd0, hD⟩
  · intro _; exact Or.inr True.intro
  · intro id hSL d ⟨hd0, hD⟩
    subst hSL; dsimp [isDeadAcrossCfg] at hD
    cases hCond : (Nat.beq id d && Nat.blt id bTgt.locals.length) with
    | true =>
      exact Or.inl (nat_beq_eq (bool_and_true hCond).1).symm
    | false =>
      rw [if_bool_false hCond] at hD
      exact Or.inr ⟨hd0, hD⟩
  · intro id hSD d ⟨hd0, hD⟩
    subst hSD; dsimp [isDeadAcrossCfg] at hD
    cases hCond : (Nat.beq id d && Nat.blt id bTgt.locals.length) with
    | true =>
      exact Or.inl (nat_beq_eq (bool_and_true hCond).1).symm
    | false =>
      rw [if_bool_false hCond] at hD
      exact Or.inr ⟨hd0, hD⟩
  · intro lhs rv hAsg d ⟨hd0, hD⟩
    subst hAsg; dsimp [isDeadAcrossCfg] at hD
    let ⟨h123, hIf⟩ := bool_and_true hD
    let ⟨h12, hNoT⟩ := bool_and_true h123
    let ⟨hPE, _⟩ := bool_and_true h12
    refine ⟨bool_not_true hNoT, ?_⟩
    cases hEq : Nat.beq lhs.localId d with
    | true =>
      exact Or.inl ⟨hPE, (nat_beq_eq hEq).symm⟩
    | false =>
      rw [if_bool_false hEq] at hIf
      exact Or.inr ⟨hd0, hIf⟩

private theorem isDeadAtTarget_elim {bTgt : Body} {bbNextTgt : BasicBlock}
    {deadAtEntry : BodyDeadCert} {tgt : BasicBlockId} {d : LocalId}
    (hDeadLoop : checkDeadAtEntryLoop bTgt deadAtEntry 0 deadAtEntry = true)
    (hBBNext : Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbNextTgt)
    (hAt : isDeadAtTarget deadAtEntry bTgt.basicBlocks.length d tgt = true) :
    d ≠ 0 ∧
    d < bTgt.locals.length ∧
    isDeadAcrossCfg bTgt.locals.length deadAtEntry bTgt.basicBlocks.length d
      bbNextTgt.statements bbNextTgt.terminator = true := by
  unfold isDeadAtTarget at hAt
  let ⟨_, hMatchDs⟩ := bool_and_true hAt
  cases hDs : Trusted.MirSemantics.getElem? deadAtEntry tgt with
  | none => rw [hDs] at hMatchDs; cases hMatchDs
  | some ds =>
    rw [hDs] at hMatchDs
    let ⟨bbTgt', hBB', hAllDs⟩ := checkDeadAtEntryLoop_getElem? hDeadLoop hDs
    rw [Nat.zero_add, hBBNext] at hBB'
    injection hBB' with eBB; subst eBB
    exact hAllDs d hMatchDs

private theorem isDeadAcrossCfg_nil_step_target {bTgt : Body} {bbTgt bbNextTgt : BasicBlock}
    {deadAtEntry : BodyDeadCert} {fTgt : FrameState} {cm : CallerMemory}
    {tgt : BasicBlockId} {locs₂' : List LocalSlot} {d : LocalId}
    (hDeadLoop : checkDeadAtEntryLoop bTgt deadAtEntry 0 deadAtEntry = true)
    (hEvTT : evalTerminator bTgt bbTgt fTgt cm =
      .step { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs₂' }],
              callerMem := cm })
    (hBBNext : Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbNextTgt)
    (hDeadNil : isDeadAcrossCfg bTgt.locals.length deadAtEntry
      bTgt.basicBlocks.length d [] bbTgt.terminator = true) :
    isDeadAcrossCfg bTgt.locals.length deadAtEntry bTgt.basicBlocks.length d
      bbNextTgt.statements bbNextTgt.terminator = true := by
  unfold evalTerminator at hEvTT
  cases hTerm : bbTgt.terminator with
  | return_ =>
    rw [hTerm] at hEvTT; dsimp at hEvTT
    cases hCl : bbTgt.cleanup with
    | true => rw [hCl] at hEvTT; cases hEvTT
    | false =>
      rw [hCl] at hEvTT; dsimp at hEvTT
      cases h0 : Trusted.MirSemantics.getElem? fTgt.locals 0 with
      | none => rw [h0] at hEvTT; cases hEvTT
      | some sl =>
        rw [h0] at hEvTT
        cases sl with
        | dead => cases hEvTT
        | live o => cases o <;> cases hEvTT
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    rw [hTerm] at hEvTT; cases hEvTT
  | goto target =>
    rw [hTerm] at hEvTT hDeadNil
    dsimp [jumpToBlock, isDeadAcrossCfg] at hEvTT hDeadNil
    injection hEvTT with eSt; injection eSt with eFs _; injection eFs with eF _
    have hTgtEq : target = tgt := congrArg FrameState.blockIdx eF
    subst hTgtEq
    exact (isDeadAtTarget_elim hDeadLoop hBBNext hDeadNil).2.2
  | switchInt discr targets =>
    rw [hTerm] at hEvTT hDeadNil
    dsimp [isDeadAcrossCfg] at hEvTT hDeadNil
    let ⟨h12, hBrAll⟩ := bool_and_true hDeadNil
    let ⟨_, hOwDs⟩ := bool_and_true h12
    cases hEvD : evalPrimitiveOperand bTgt.locals fTgt.locals discr with
    | error _ => rw [hEvD] at hEvTT; cases hEvTT
    | ok resD =>
      let ⟨dv, locsAfter⟩ := resD
      rw [hEvD] at hEvTT; dsimp at hEvTT
      have hTargetInBranchesOrOw :
          (∃ cb, (cb, tgt) ∈ targets.branches) ∨ tgt = targets.otherwise := by
        cases dv with
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEvTT
        | bool bv =>
          dsimp at hEvTT
          cases hSwB : evalBoolSwitchBranches bv targets.otherwise targets.branches with
          | error _ => rw [hSwB] at hEvTT; cases hEvTT
          | ok t0 =>
            rw [hSwB] at hEvTT; dsimp [jumpToBlock] at hEvTT
            injection hEvTT with eSt; injection eSt with eFs _; injection eFs with eF _
            have hTEq : t0 = tgt := congrArg FrameState.blockIdx eF
            subst hTEq
            exact evalBoolSwitchBranches_cases hSwB
        | scalar sv =>
          dsimp at hEvTT
          cases hSwS : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
          | error _ => rw [hSwS] at hEvTT; cases hEvTT
          | ok t0 =>
            rw [hSwS] at hEvTT; dsimp [jumpToBlock] at hEvTT
            injection hEvTT with eSt; injection eSt with eFs _; injection eFs with eF _
            have hTEq : t0 = tgt := congrArg FrameState.blockIdx eF
            subst hTEq
            cases evalSwitchBranches_cases hSwS with
            | inl hBr => exact Or.inl hBr
            | inr hOw => exact Or.inr hOw.1
      cases hTargetInBranchesOrOw with
      | inr hOw =>
        subst hOw
        exact (isDeadAtTarget_elim hDeadLoop hBBNext hOwDs).2.2
      | inl hInBr =>
        let ⟨cb, hMem⟩ := hInBr
        have hBr := list_all_mem_true hBrAll hMem
        exact (isDeadAtTarget_elim hDeadLoop hBBNext hBr).2.2

private theorem isDeadAcrossCfg_nil_switch_untouched {numLocals : Nat}
    {deadAtEntry : BodyDeadCert} {numBlocks : Nat} {d : LocalId}
    {discr : Operand} {targets : SwitchTargets}
    (h : isDeadAcrossCfg numLocals deadAtEntry numBlocks d []
      (.switchInt discr targets) = true) :
    operandTouchesLocal d discr = false := by
  dsimp [isDeadAcrossCfg] at h
  exact bool_not_true (bool_and_true (bool_and_true h).1).1

/-! ### Stage 4 Private Helpers — Slice B: Pass Family 1 (`.moveToCopyDead`)
& Pass Family 5 (`.compactUnusedTrailingLocals`) -/

/-! #### Pass Family 1: `.moveToCopyDead` -/

private theorem programHeaderEq_with_bodies (p : Program) (bs : List Body) :
    programHeaderEq p { p with bodies := bs } = true :=
  programHeaderEq_refl p

private noncomputable def rewriteMoveToCopyDeadOp (canKill : LocalId → Bool) :
    Operand → Operand
  | .move p =>
    if p.projection.isEmpty && canKill p.localId then .copy p else .move p
  | o => o

private theorem rewriteMoveToCopyDeadOp_spec (canKill : LocalId → Bool) (opnd : Operand) :
    rewriteMoveToCopyDeadOp canKill opnd = opnd ∨
    ∃ p, opnd = .move p ∧
      rewriteMoveToCopyDeadOp canKill opnd = .copy p ∧
      p.projection.isEmpty = true ∧
      canKill p.localId = true := by
  cases opnd with
  | copy _ | constant _ => exact Or.inl rfl
  | move p =>
    dsimp [rewriteMoveToCopyDeadOp]
    cases hC : (p.projection.isEmpty && canKill p.localId) with
    | false => exact Or.inl rfl
    | true =>
      let ⟨hPE, hCK⟩ := bool_and_true hC
      exact Or.inr ⟨p, rfl, rfl, hPE, hCK⟩

private noncomputable def rewriteMoveToCopyDeadSingleStmt (numLocals : Nat)
    (deadAtEntry : BodyDeadCert) (numBlocks : Nat) (term : TerminatorKind)
    (rest : List StatementKind) (s : StatementKind) : StatementKind :=
  match s with
  | .assign dst rv =>
    if dst.projection.isEmpty && Nat.blt dst.localId numLocals then
      let canKill := fun l =>
        !Nat.beq l 0 &&
          (Nat.beq dst.localId l ||
            isDeadAcrossCfg numLocals deadAtEntry numBlocks l rest term)
      .assign dst (rewriteMoveToCopyDeadRvalue canKill rv)
    else s
  | _ => s

private noncomputable def rewriteMoveToCopyDeadBlock (numLocals : Nat)
    (deadAtEntry : BodyDeadCert) (numBlocks : Nat)
    (bb : BasicBlock) : BasicBlock := {
  statements := rewriteMoveToCopyDeadStmts numLocals deadAtEntry
    numBlocks bb.terminator bb.statements
  terminator := rewriteMoveToCopyDeadTerm deadAtEntry numBlocks bb.terminator
  cleanup := bb.cleanup
}

private theorem rewriteMoveToCopyDeadStmts_storage (numLocals : Nat)
    (deadAtEntry : BodyDeadCert) (numBlocks : Nat) (term : TerminatorKind) :
    ∀ ss : List StatementKind,
      StmtListStoragePreserved ss
        (rewriteMoveToCopyDeadStmts numLocals deadAtEntry numBlocks term ss)
  | [] => True.intro
  | s :: rest => by
    dsimp [rewriteMoveToCopyDeadStmts, rewriteMoveToCopyDeadSingleStmt]
    refine ⟨?_, rewriteMoveToCopyDeadStmts_storage numLocals deadAtEntry numBlocks term rest⟩
    cases s with
    | nop | storageLive _ | storageDead _ | unsupported => exact Or.inl rfl
    | assign dst rv =>
      dsimp only
      cases (dst.projection.isEmpty && Nat.blt dst.localId numLocals) with
      | false => exact Or.inl rfl
      | true => exact Or.inr ⟨True.intro, True.intro⟩

private theorem listRel_map_self {α : Type} (r : α → α → Bool) (f : α → α)
    (hRefl : ∀ x, r x (f x) = true) :
    ∀ xs : List α, listRel r xs (xs.map f) = true
  | [] => rfl
  | x :: xs => by
    dsimp [List.map, listRel]
    exact bool_and_intro (hRefl x) (listRel_map_self r f hRefl xs)

private theorem applyMoveToCopyDeadBody_props {deadAtEntry : BodyDeadCert}
    {bSrc bTgt : Body}
    (hApply : applyMoveToCopyDeadBody deadAtEntry bSrc = some bTgt) :
    checkBodyDeadCert bSrc deadAtEntry = true ∧
    bTgt = {
      bSrc with
      basicBlocks := bSrc.basicBlocks.map
        (rewriteMoveToCopyDeadBlock bSrc.locals.length deadAtEntry
          bSrc.basicBlocks.length)
    } ∧
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) := by
  unfold applyMoveToCopyDeadBody at hApply
  cases hCert : checkBodyDeadCert bSrc deadAtEntry with
  | false => rw [hCert] at hApply; cases hApply
  | true =>
    rw [hCert] at hApply; dsimp at hApply
    injection hApply with hEq
    subst hEq
    let fn := rewriteMoveToCopyDeadBlock bSrc.locals.length deadAtEntry
      bSrc.basicBlocks.length
    have hHdr : bodyHeaderEq bSrc { bSrc with basicBlocks := bSrc.basicBlocks.map fn } = true :=
      bodyHeaderEq_refl bSrc
    have hBBLen : bSrc.basicBlocks.length = (bSrc.basicBlocks.map fn).length :=
      (map_length_eq fn bSrc.basicBlocks).symm
    have hBBEmpty : bSrc.basicBlocks.isEmpty = (bSrc.basicBlocks.map fn).isEmpty :=
      list_isEmpty_eq_of_length hBBLen
    have hMarker : ∀ idx,
        hasStorageAnnotation bSrc idx =
          hasStorageAnnotation { bSrc with basicBlocks := bSrc.basicBlocks.map fn } idx := by
      intro idx
      unfold hasStorageAnnotation; dsimp only
      induction bSrc.basicBlocks with
      | nil => rfl
      | cons bb rest ih =>
        dsimp [List.map, List.any, fn, rewriteMoveToCopyDeadBlock]
        have hSt := (stmtListStoragePreserved_props
          (rewriteMoveToCopyDeadStmts_storage bSrc.locals.length deadAtEntry
            bSrc.basicBlocks.length bb.terminator bb.statements)).2.1 idx
        rw [hSt, ih]
    have hBounds :
        storageAnnotationsInBounds bSrc =
          storageAnnotationsInBounds { bSrc with basicBlocks := bSrc.basicBlocks.map fn } := by
      unfold storageAnnotationsInBounds; dsimp only
      induction bSrc.basicBlocks with
      | nil => rfl
      | cons bb rest ih =>
        dsimp only [List.map, List.all]
        have hAnd : ∀ {a b c d : Bool}, a = c → b = d → (a && b) = (c && d) := by
          intro _ _ _ _ e1 e2; rw [e1, e2]
        exact hAnd
          ((stmtListStoragePreserved_props
            (rewriteMoveToCopyDeadStmts_storage bSrc.locals.length deadAtEntry
              bSrc.basicBlocks.length bb.terminator bb.statements)).2.2
            _ (fun _ _ => rfl) rfl)
          ih
    exact ⟨rfl, rfl, hHdr, hBBLen, hBBEmpty, hBounds,
      fun args => initLocalsLoop_eq_of_storage_eq
        (b1 := bSrc) (b2 := { bSrc with basicBlocks := bSrc.basicBlocks.map fn })
        args rfl rfl (fun idx _ _ => hMarker idx)⟩

private theorem rewriteMoveToCopyDeadStmts_drop {numLocals : Nat}
    {deadAtEntry : BodyDeadCert} {numBlocks : Nat} {term : TerminatorKind} :
    ∀ (ss : List StatementKind) (idx : Nat),
      (rewriteMoveToCopyDeadStmts numLocals deadAtEntry numBlocks term ss).drop idx =
        rewriteMoveToCopyDeadStmts numLocals deadAtEntry numBlocks term (ss.drop idx)
  | [], idx => by cases idx <;> rfl
  | s :: rest, 0 => rfl
  | s :: rest, k + 1 => by
    dsimp [rewriteMoveToCopyDeadStmts, List.drop]
    exact rewriteMoveToCopyDeadStmts_drop rest k

private theorem rewriteMoveToCopyDeadStmts_length {numLocals : Nat}
    {deadAtEntry : BodyDeadCert} {numBlocks : Nat} {term : TerminatorKind} :
    ∀ ss : List StatementKind,
      (rewriteMoveToCopyDeadStmts numLocals deadAtEntry numBlocks term ss).length =
        ss.length
  | [] => rfl
  | _ :: rest => by
    dsimp [rewriteMoveToCopyDeadStmts, List.length]
    rw [rewriteMoveToCopyDeadStmts_length rest]

private theorem evalOperandToSlot_moveToCopy_bisim {bodyLocals : List MirTy}
    {D Q : LocalId → Prop} {locs₁ locs₂ : List LocalSlot}
    {opSrc opTgt : Operand}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hUntouched : ∀ d, D d → operandTouchesLocal d opSrc = false)
    (hRew : opTgt = opSrc ∨
      ∃ p, opSrc = .move p ∧ opTgt = .copy p ∧
        p.projection.isEmpty = true ∧ Q p.localId) :
    (∃ fk,
      evalOperandToSlot bodyLocals locs₁ opSrc = .error fk ∧
      evalOperandToSlot bodyLocals locs₂ opTgt = .error fk) ∨
    (∃ ty optVal locs₁' locs₂',
      evalOperandToSlot bodyLocals locs₁ opSrc = .ok (ty, optVal, locs₁') ∧
      evalOperandToSlot bodyLocals locs₂ opTgt = .ok (ty, optVal, locs₂') ∧
      DeadMaskedEq bodyLocals (fun d => D d ∨ Q d) locs₁' locs₂') := by
  cases hRew with
  | inl hSame =>
    subst hSame
    cases evalOperandToSlot_untouched_bisim hMask hUntouched with
    | inl hErr => exact Or.inl hErr
    | inr hOk =>
      let ⟨ty, optVal, l1, l2, e1, e2, hM⟩ := hOk
      exact Or.inr ⟨ty, optVal, l1, l2, e1, e2,
        deadMaskedEq_mono (fun _ h => Or.inl h) hM⟩
  | inr hMC =>
    let ⟨p, hOS, hOT, hPEmp, hQp⟩ := hMC
    subst hOS; subst hOT
    let ⟨hWt1, hWt2, hAll⟩ := hMask
    have hNotD : ¬ D p.localId := by
      intro hDp
      have hF := hUntouched p.localId hDp
      dsimp [operandTouchesLocal] at hF
      rw [nat_beq_refl] at hF; cases hF
    have hEqAt := (hAll p.localId).2 hNotD
    dsimp [evalOperandToSlot]
    rw [hPEmp]; dsimp
    cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
    | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | some ty =>
      have hLtB : p.localId < bodyLocals.length := getElem?_some_lt hTy
      let ⟨sl, hG1⟩ := getElem?_some_of_lt locs₁ p.localId
        (by rw [hWt1.1]; exact hLtB)
      have hG2 : Trusted.MirSemantics.getElem? locs₂ p.localId = some sl := by
        rw [← hEqAt]; exact hG1
      rw [hG1, hG2]
      cases sl with
      | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
      | live optVal =>
        dsimp
        let ⟨locs₁', hSet1⟩ := setElem?_some_of_lt locs₁ p.localId
          (liveUninitSlot ty) (by rw [hWt1.1]; exact hLtB)
        rw [hSet1]
        let ⟨optU, hLU⟩ := liveUninitSlot_isLive ty
        have hSet1Live : setElem? locs₁ p.localId (.live optU) = some locs₁' := by
          rw [← hLU]; exact hSet1
        have hWtLU : SlotWellTyped ty (.live optU) := by
          rw [← hLU]; exact liveUninitSlot_wellTyped ty
        have hSub := deadMaskedEq_set_left_live hMask hTy hG2 hSet1Live hWtLU
        refine Or.inr ⟨ty, optVal, locs₁', locs₂, rfl, rfl,
          deadMaskedEq_mono ?_ hSub⟩
        intro d hDisj
        cases hDisj with
        | inl hDd => exact Or.inl hDd
        | inr hEq => subst hEq; exact Or.inr hQp

private theorem evalPrimitiveOperand_moveToCopy_bisim {bodyLocals : List MirTy}
    {D Q : LocalId → Prop} {locs₁ locs₂ : List LocalSlot}
    {opSrc opTgt : Operand}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hUntouched : ∀ d, D d → operandTouchesLocal d opSrc = false)
    (hRew : opTgt = opSrc ∨
      ∃ p, opSrc = .move p ∧ opTgt = .copy p ∧
        p.projection.isEmpty = true ∧ Q p.localId) :
    (∃ fk,
      evalPrimitiveOperand bodyLocals locs₁ opSrc = .error fk ∧
      evalPrimitiveOperand bodyLocals locs₂ opTgt = .error fk) ∨
    (∃ v locs₁' locs₂',
      evalPrimitiveOperand bodyLocals locs₁ opSrc = .ok (v, locs₁') ∧
      evalPrimitiveOperand bodyLocals locs₂ opTgt = .ok (v, locs₂') ∧
      DeadMaskedEq bodyLocals (fun d => D d ∨ Q d) locs₁' locs₂') := by
  dsimp [evalPrimitiveOperand]
  cases evalOperandToSlot_moveToCopy_bisim hMask hUntouched hRew with
  | inl hErr =>
    let ⟨fk, e1, e2⟩ := hErr
    rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
  | inr hOk =>
    let ⟨ty, optVal, l1, l2, e1, e2, hM⟩ := hOk
    rw [e1, e2]; dsimp
    cases isPrimitiveReadableTy ty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      cases optVal with
      | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
      | some v => exact Or.inr ⟨v, l1, l2, rfl, rfl, hM⟩

private theorem evalRvalue_moveToCopy_bisim {bodyLocals : List MirTy}
    {D : LocalId → Prop} {canKill : LocalId → Bool}
    {locs₁ locs₂ : List LocalSlot} {dstTy : MirTy} {rv : Rvalue}
    (hMask : DeadMaskedEq bodyLocals D locs₁ locs₂)
    (hUntouched : ∀ d, D d → rvalueTouchesLocal d rv = false) :
    (∃ fk,
      evalRvalue bodyLocals locs₁ dstTy rv = .error fk ∧
      evalRvalue bodyLocals locs₂ dstTy
        (rewriteMoveToCopyDeadRvalue canKill rv) = .error fk) ∨
    (∃ v locs₁' locs₂',
      evalRvalue bodyLocals locs₁ dstTy rv = .ok (v, locs₁') ∧
      evalRvalue bodyLocals locs₂ dstTy
        (rewriteMoveToCopyDeadRvalue canKill rv) = .ok (v, locs₂') ∧
      DeadMaskedEq bodyLocals (fun d => D d ∨ canKill d = true) locs₁' locs₂') := by
  cases rv with
  | use opnd =>
    have hUseEq :
        rewriteMoveToCopyDeadRvalue canKill (.use opnd) =
          .use (rewriteMoveToCopyDeadOp canKill opnd) := by
      cases opnd with
      | copy _ | constant _ => rfl
      | move p =>
        dsimp [rewriteMoveToCopyDeadRvalue, rewriteMoveToCopyDeadOp]
        cases (p.projection.isEmpty && canKill p.localId) <;> rfl
    rw [hUseEq]
    dsimp [evalRvalue]
    cases evalOperandToSlot_moveToCopy_bisim (Q := fun d => canKill d = true)
        hMask hUntouched (rewriteMoveToCopyDeadOp_spec canKill opnd) with
    | inl hErr =>
      let ⟨fk, e1, e2⟩ := hErr
      rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hOk =>
      let ⟨sTy, optVal, l1, l2, e1, e2, hM⟩ := hOk
      rw [e1, e2]; dsimp
      cases MirTy.beq sTy dstTy with
      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | true =>
        dsimp
        cases optVal with
        | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
        | some v => exact Or.inr ⟨v, l1, l2, rfl, rfl, hM⟩
  | unaryOp uop opnd =>
    have hUnEq :
        rewriteMoveToCopyDeadRvalue canKill (.unaryOp uop opnd) =
          .unaryOp uop (rewriteMoveToCopyDeadOp canKill opnd) := by
      cases opnd with
      | copy _ | constant _ => rfl
      | move p =>
        dsimp [rewriteMoveToCopyDeadRvalue, rewriteMoveToCopyDeadOp]
        cases (p.projection.isEmpty && canKill p.localId) <;> rfl
    rw [hUnEq]
    dsimp [evalRvalue]
    cases evalPrimitiveOperand_moveToCopy_bisim (Q := fun d => canKill d = true)
        hMask hUntouched (rewriteMoveToCopyDeadOp_spec canKill opnd) with
    | inl hErr =>
      let ⟨fk, e1, e2⟩ := hErr
      rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hOk =>
      let ⟨ov, l1, l2, e1, e2, hM⟩ := hOk
      rw [e1, e2]; dsimp
      cases evalUnOp uop ov with
      | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
      | ok res => exact Or.inr ⟨res, l1, l2, rfl, rfl, hM⟩
  | binaryOp bop lhs rhs =>
    have hBinEq :
        rewriteMoveToCopyDeadRvalue canKill (.binaryOp bop lhs rhs) =
          .binaryOp bop
            (rewriteMoveToCopyDeadOp
              (fun id => !operandTouchesLocal id rhs && canKill id) lhs)
            (rewriteMoveToCopyDeadOp canKill rhs) := by
      cases lhs with
      | copy _ | constant _ =>
        cases rhs <;> rfl
      | move p =>
        cases rhs with
        | copy _ | constant _ =>
          dsimp [rewriteMoveToCopyDeadRvalue, rewriteMoveToCopyDeadOp]
          rw [Bool.and_assoc]
        | move p2 =>
          dsimp [rewriteMoveToCopyDeadRvalue, rewriteMoveToCopyDeadOp]
          rw [Bool.and_assoc]
    rw [hBinEq]
    dsimp [evalRvalue]
    have hUL : ∀ d, D d → operandTouchesLocal d lhs = false :=
      fun d hD => (bool_or_false (hUntouched d hD)).1
    have hUR0 : ∀ d, D d → operandTouchesLocal d rhs = false :=
      fun d hD => (bool_or_false (hUntouched d hD)).2
    cases evalPrimitiveOperand_moveToCopy_bisim
        (Q := fun d => (!operandTouchesLocal d rhs && canKill d) = true)
        hMask hUL
        (rewriteMoveToCopyDeadOp_spec
          (fun id => !operandTouchesLocal id rhs && canKill id) lhs) with
    | inl hErrL =>
      let ⟨fk, e1, e2⟩ := hErrL
      rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hOkL =>
      let ⟨vl, l1, l2, e1, e2, hM1⟩ := hOkL
      rw [e1, e2]; dsimp
      have hUR1 : ∀ d,
          (D d ∨ (!operandTouchesLocal d rhs && canKill d) = true) →
          operandTouchesLocal d rhs = false := by
        intro d hDisj
        cases hDisj with
        | inl hDd => exact hUR0 d hDd
        | inr hQ => exact bool_not_true (bool_and_true hQ).1
      cases evalPrimitiveOperand_moveToCopy_bisim
          (Q := fun d => canKill d = true) hM1 hUR1
          (rewriteMoveToCopyDeadOp_spec canKill rhs) with
      | inl hErrR =>
        let ⟨fk, er1, er2⟩ := hErrR
        rw [er1, er2]; exact Or.inl ⟨fk, rfl, rfl⟩
      | inr hOkR =>
        let ⟨vr, l1', l2', er1, er2, hM2⟩ := hOkR
        rw [er1, er2]; dsimp
        have hM2' : DeadMaskedEq bodyLocals (fun d => D d ∨ canKill d = true)
            l1' l2' := by
          refine deadMaskedEq_mono ?_ hM2
          intro d hDisj
          cases hDisj with
          | inl hSub =>
            cases hSub with
            | inl hDd => exact Or.inl hDd
            | inr hQL => exact Or.inr (bool_and_true hQL).2
          | inr hCK => exact Or.inr hCK
        cases evalBinOp bop vl vr with
        | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
        | ok res => exact Or.inr ⟨res, l1', l2', rfl, rfl, hM2'⟩
  | discriminant _ | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported =>
    dsimp [rewriteMoveToCopyDeadRvalue]
    cases evalRvalue_untouched_bisim (dstTy := dstTy) hMask hUntouched with
    | inl hErr => exact Or.inl hErr
    | inr hOk =>
      let ⟨v, l1, l2, e1, e2, hM⟩ := hOk
      exact Or.inr ⟨v, l1, l2, e1, e2,
        deadMaskedEq_mono (fun _ h => Or.inl h) hM⟩

private theorem evalStatement_moveToCopy_kept_helper {bSrc bTgt : Body}
    {deadAtEntry : BodyDeadCert} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {sSrc sTgt : StatementKind} {restSrc : List StatementKind}
    {termSrc : TerminatorKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEqS : sSrc = sTgt)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bSrc.locals.length deadAtEntry bSrc.basicBlocks.length
          d (sSrc :: restSrc) termSrc = true)
      fSrc.locals fTgt.locals) :
    (∃ fk,
      evalStatement bSrc fSrc cm sSrc = .fault fk ∧
      evalStatement bTgt fTgt cm sTgt = .fault fk) ∨
    (∃ locs₁' locs₂',
      evalStatement bSrc fSrc cm sSrc =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs₁' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm sTgt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs₂' }],
                callerMem := cm } ∧
      DeadMaskedEq bSrc.locals
        (fun d => d ≠ 0 ∧
          isDeadAcrossCfg bSrc.locals.length deadAtEntry bSrc.basicBlocks.length
            d restSrc termSrc = true)
        locs₁' locs₂') := by
  rw [← hEqS]
  have hMaskTgt : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bTgt.locals.length deadAtEntry bSrc.basicBlocks.length
          d (sSrc :: restSrc) termSrc = true)
      fSrc.locals fTgt.locals := by
    rw [← hLocEq]; exact hMask
  cases isDeadAcrossCfg_kept_step (fTgt := fTgt) (cm := cm) hLocEq hMaskTgt with
  | inl hF => exact Or.inl hF
  | inr hS =>
    let ⟨l1, l2, e1, e2, hM⟩ := hS
    rw [← hLocEq] at hM
    exact Or.inr ⟨l1, l2, e1, e2, hM⟩

private theorem evalStatement_moveToCopy_step {bSrc bTgt : Body}
    {deadAtEntry : BodyDeadCert} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {sSrc : StatementKind} {restSrc : List StatementKind}
    {termSrc : TerminatorKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bSrc.locals.length deadAtEntry bSrc.basicBlocks.length
          d (sSrc :: restSrc) termSrc = true)
      fSrc.locals fTgt.locals) :
    (∃ fk,
      evalStatement bSrc fSrc cm sSrc = .fault fk ∧
      evalStatement bTgt fTgt cm
        (rewriteMoveToCopyDeadSingleStmt bSrc.locals.length deadAtEntry
          bSrc.basicBlocks.length termSrc restSrc sSrc) = .fault fk) ∨
    (∃ locs₁' locs₂',
      evalStatement bSrc fSrc cm sSrc =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs₁' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm
        (rewriteMoveToCopyDeadSingleStmt bSrc.locals.length deadAtEntry
          bSrc.basicBlocks.length termSrc restSrc sSrc) =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs₂' }],
                callerMem := cm } ∧
      DeadMaskedEq bSrc.locals
        (fun d => d ≠ 0 ∧
          isDeadAcrossCfg bSrc.locals.length deadAtEntry bSrc.basicBlocks.length
            d restSrc termSrc = true)
        locs₁' locs₂') := by
  cases sSrc with
  | nop => exact evalStatement_moveToCopy_kept_helper hLocEq rfl hMask
  | storageLive _ => exact evalStatement_moveToCopy_kept_helper hLocEq rfl hMask
  | storageDead _ => exact evalStatement_moveToCopy_kept_helper hLocEq rfl hMask
  | unsupported => exact evalStatement_moveToCopy_kept_helper hLocEq rfl hMask
  | assign dst rv =>
    cases hGuard : (dst.projection.isEmpty && Nat.blt dst.localId bSrc.locals.length) with
    | false =>
      exact evalStatement_moveToCopy_kept_helper hLocEq
        (by dsimp [rewriteMoveToCopyDeadSingleStmt]; rw [if_bool_false hGuard]) hMask
    | true =>
      dsimp [rewriteMoveToCopyDeadSingleStmt]
      rw [if_bool_true hGuard]
      let ⟨hPE, hBlt⟩ := bool_and_true hGuard
      let ⟨dstTy, hDstTy⟩ := getElem?_some_of_lt bSrc.locals dst.localId (nat_blt_lt hBlt)
      have hDstTyTgt : Trusted.MirSemantics.getElem? bTgt.locals dst.localId = some dstTy := by
        rw [← hLocEq]; exact hDstTy
      dsimp [evalStatement]
      rw [hPE]; dsimp
      rw [hDstTy, hDstTyTgt]; dsimp
      rw [← hLocEq]
      have hUntouched : ∀ d,
          (d ≠ 0 ∧ isDeadAcrossCfg bSrc.locals.length deadAtEntry
            bSrc.basicBlocks.length d (.assign dst rv :: restSrc) termSrc = true) →
          rvalueTouchesLocal d rv = false := by
        intro d ⟨_, hD⟩
        dsimp [isDeadAcrossCfg] at hD
        exact bool_not_true (bool_and_true (bool_and_true hD).1).2
      cases evalRvalue_moveToCopy_bisim
          (canKill := fun l =>
            !Nat.beq l 0 &&
              (Nat.beq dst.localId l ||
                isDeadAcrossCfg bSrc.locals.length deadAtEntry
                  bSrc.basicBlocks.length l restSrc termSrc))
          (dstTy := dstTy) hMask hUntouched with
      | inl hErrRv =>
        let ⟨fk, e1, e2⟩ := hErrRv
        rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
      | inr hOkRv =>
        let ⟨val, l1, l2, e1, e2, hM1⟩ := hOkRv
        rw [e1, e2]; dsimp
        cases writePlace_deadMasked_bisim (val := val) hM1 hDstTy with
        | inl hErrW =>
          let ⟨fk, w1, w2⟩ := hErrW
          rw [w1, w2]; exact Or.inl ⟨fk, rfl, rfl⟩
        | inr hOkW =>
          let ⟨locs₁', locs₂', w1, w2, hM2⟩ := hOkW
          rw [w1, w2]
          refine Or.inr ⟨locs₁', locs₂', rfl, rfl, deadMaskedEq_mono ?_ hM2⟩
          intro d ⟨hDisj, hNeDst⟩
          cases hDisj with
          | inl hD1 =>
            let ⟨hd0, hD⟩ := hD1
            dsimp [isDeadAcrossCfg] at hD
            let ⟨_, hIf⟩ := bool_and_true hD
            rw [nat_beq_false_of_ne (Ne.symm hNeDst), if_bool_false rfl] at hIf
            exact ⟨hd0, hIf⟩
          | inr hCK =>
            let ⟨hNotZ, hOr⟩ := bool_and_true hCK
            have hd0 := nat_ne_of_beq_false (bool_not_true hNotZ)
            cases bool_or_true hOr with
            | inl hEqDst => exact False.elim (hNeDst (nat_beq_eq hEqDst).symm)
            | inr hDeadRest => exact ⟨hd0, hDeadRest⟩

private theorem evalTerminator_moveToCopy_unchanged_helper {bSrc bTgt : Body}
    {bbSrc : BasicBlock} {deadAtEntry : BodyDeadCert}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hDeadLoop : checkDeadAtEntryLoop bSrc deadAtEntry 0 deadAtEntry = true)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bSrc.locals.length deadAtEntry bSrc.basicBlocks.length
          d [] bbSrc.terminator = true)
      fSrc.locals fTgt.locals)
    (hTmEq : rewriteMoveToCopyDeadTerm deadAtEntry
      bSrc.basicBlocks.length bbSrc.terminator = bbSrc.terminator) :
    let bbTgt := rewriteMoveToCopyDeadBlock bSrc.locals.length deadAtEntry
      bSrc.basicBlocks.length bbSrc
    (∃ tgt locs₁' locs₂',
      evalTerminator bSrc bbSrc fSrc cm =
        .step { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs₁' }],
                callerMem := cm } ∧
      evalTerminator bTgt bbTgt fTgt cm =
        .step { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs₂' }],
                callerMem := cm } ∧
      (∀ bbNextSrc,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbNextSrc →
        DeadMaskedEq bSrc.locals
          (fun d => d ≠ 0 ∧
            isDeadAcrossCfg bSrc.locals.length deadAtEntry
              bSrc.basicBlocks.length d bbNextSrc.statements
              bbNextSrc.terminator = true)
          locs₁' locs₂') ∧
      LocalsWellTyped bSrc.locals locs₁' ∧
      LocalsWellTyped bSrc.locals locs₂') ∨
    (∃ out,
      evalTerminator bSrc bbSrc fSrc cm = .done out ∧
      evalTerminator bTgt bbTgt fTgt cm = .done out) ∨
    (∃ fk,
      evalTerminator bSrc bbSrc fSrc cm = .fault fk ∧
      evalTerminator bTgt bbTgt fTgt cm = .fault fk) := by
  let bbTgt := rewriteMoveToCopyDeadBlock bSrc.locals.length deadAtEntry
    bSrc.basicBlocks.length bbSrc
  have hTerm : bbSrc.terminator = bbTgt.terminator := hTmEq.symm
  have hSwU : ∀ discr targets,
      bbTgt.terminator = .switchInt discr targets →
      ∀ d, (d ≠ 0 ∧ isDeadAcrossCfg bSrc.locals.length deadAtEntry
        bSrc.basicBlocks.length d [] bbSrc.terminator = true) →
      operandTouchesLocal d discr = false := by
    intro discr targets hT d ⟨_, hD⟩
    rw [hTerm, hT] at hD
    exact isDeadAcrossCfg_nil_switch_untouched hD
  cases evalTerminator_deadMasked_bisim (bbSrc := bbSrc) (bbTgt := bbTgt)
      (fTgt := fTgt) (cm := cm) hLocEq rfl hTerm hMask (fun _ h => h.1) hSwU with
  | inr hDF => exact Or.inr hDF
  | inl hST =>
    let ⟨tgt, l1, l2, e1, e2, hM⟩ := hST
    refine Or.inl ⟨tgt, l1, l2, e1, e2, ?_, hM.1, hM.2.1⟩
    intro bbNextSrc hBBN
    refine deadMaskedEq_mono ?_ hM
    intro d ⟨hd0, hDnil⟩
    exact ⟨hd0, isDeadAcrossCfg_nil_step_target hDeadLoop e1 hBBN hDnil⟩

private theorem evalTerminator_moveToCopy_step {bSrc bTgt : Body}
    {bbSrc : BasicBlock} {deadAtEntry : BodyDeadCert}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hDeadLoop : checkDeadAtEntryLoop bSrc deadAtEntry 0 deadAtEntry = true)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bSrc.locals.length deadAtEntry bSrc.basicBlocks.length
          d [] bbSrc.terminator = true)
      fSrc.locals fTgt.locals) :
    let bbTgt := rewriteMoveToCopyDeadBlock bSrc.locals.length deadAtEntry
      bSrc.basicBlocks.length bbSrc
    (∃ tgt locs₁' locs₂',
      evalTerminator bSrc bbSrc fSrc cm =
        .step { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs₁' }],
                callerMem := cm } ∧
      evalTerminator bTgt bbTgt fTgt cm =
        .step { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs₂' }],
                callerMem := cm } ∧
      (∀ bbNextSrc,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbNextSrc →
        DeadMaskedEq bSrc.locals
          (fun d => d ≠ 0 ∧
            isDeadAcrossCfg bSrc.locals.length deadAtEntry
              bSrc.basicBlocks.length d bbNextSrc.statements
              bbNextSrc.terminator = true)
          locs₁' locs₂') ∧
      LocalsWellTyped bSrc.locals locs₁' ∧
      LocalsWellTyped bSrc.locals locs₂') ∨
    (∃ out,
      evalTerminator bSrc bbSrc fSrc cm = .done out ∧
      evalTerminator bTgt bbTgt fTgt cm = .done out) ∨
    (∃ fk,
      evalTerminator bSrc bbSrc fSrc cm = .fault fk ∧
      evalTerminator bTgt bbTgt fTgt cm = .fault fk) := by
  have hUnchanged := fun hTmEq =>
    evalTerminator_moveToCopy_unchanged_helper (bTgt := bTgt) (bbSrc := bbSrc)
      (fTgt := fTgt) (cm := cm) hLocEq hDeadLoop hMask hTmEq
  cases hTm : bbSrc.terminator with
  | goto _ => exact hUnchanged (by rw [hTm]; rfl)
  | return_ => exact hUnchanged (by rw [hTm]; rfl)
  | unreachable => exact hUnchanged (by rw [hTm]; rfl)
  | unwindResume => exact hUnchanged (by rw [hTm]; rfl)
  | assert _ _ _ _ _ => exact hUnchanged (by rw [hTm]; rfl)
  | call _ _ _ _ _ => exact hUnchanged (by rw [hTm]; rfl)
  | unsupported => exact hUnchanged (by rw [hTm]; rfl)
  | switchInt discr targets =>
    cases discr with
    | copy _ | constant _ => exact hUnchanged (by rw [hTm]; rfl)
    | move p =>
      cases hCond : (p.projection.isEmpty && !Nat.beq p.localId 0 &&
          isDeadAtTarget deadAtEntry bSrc.basicBlocks.length p.localId targets.otherwise &&
          targets.branches.all (fun br =>
            isDeadAtTarget deadAtEntry bSrc.basicBlocks.length p.localId br.2)) with
      | false =>
        exact hUnchanged (by
          rw [hTm]; dsimp [rewriteMoveToCopyDeadTerm]
          rw [if_bool_false hCond])
      | true =>
        let ⟨h123, hBrAllP⟩ := bool_and_true hCond
        let ⟨h12, hOwP⟩ := bool_and_true h123
        let ⟨hPE, hNotZ⟩ := bool_and_true h12
        have hp0 := nat_ne_of_beq_false (bool_not_true hNotZ)
        dsimp only [rewriteMoveToCopyDeadBlock]
        unfold evalTerminator
        dsimp only
        rw [hTm]
        dsimp [rewriteMoveToCopyDeadTerm]
        rw [if_bool_true hCond]; dsimp
        rw [← hLocEq]
        have hUntouched : ∀ d,
            (d ≠ 0 ∧ isDeadAcrossCfg bSrc.locals.length deadAtEntry
              bSrc.basicBlocks.length d [] bbSrc.terminator = true) →
            operandTouchesLocal d (.move p) = false := by
          intro d ⟨_, hD⟩
          rw [hTm] at hD
          exact isDeadAcrossCfg_nil_switch_untouched hD
        cases evalPrimitiveOperand_moveToCopy_bisim (Q := fun d => d = p.localId)
            hMask hUntouched (Or.inr ⟨p, rfl, rfl, hPE, rfl⟩) with
        | inl hErr =>
          let ⟨fk, e1, e2⟩ := hErr
          rw [e1, e2]; exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
        | inr hOk =>
          let ⟨dv, l1, l2, e1, e2, hM1⟩ := hOk
          rw [e1, e2]; dsimp
          have hFinish : ∀ tgt,
              ((∃ cb, (cb, tgt) ∈ targets.branches) ∨ tgt = targets.otherwise) →
              ∀ bbNextSrc,
                Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbNextSrc →
                DeadMaskedEq bSrc.locals
                  (fun d => d ≠ 0 ∧
                    isDeadAcrossCfg bSrc.locals.length deadAtEntry
                      bSrc.basicBlocks.length d bbNextSrc.statements
                      bbNextSrc.terminator = true)
                  l1 l2 := by
            intro tgt hOut bbNextSrc hBBN
            refine deadMaskedEq_mono ?_ hM1
            intro d hDisj
            cases hDisj with
            | inl hPre =>
              let ⟨hd0, hDnil⟩ := hPre
              rw [hTm] at hDnil
              dsimp [isDeadAcrossCfg] at hDnil
              let ⟨h12d, hBrD⟩ := bool_and_true hDnil
              let ⟨_, hOwD⟩ := bool_and_true h12d
              cases hOut with
              | inr hEqOw =>
                subst hEqOw
                exact ⟨hd0, (isDeadAtTarget_elim hDeadLoop hBBN hOwD).2.2⟩
              | inl hInBr =>
                let ⟨cb, hMem⟩ := hInBr
                have hAt := list_all_mem_true hBrD hMem
                exact ⟨hd0, (isDeadAtTarget_elim hDeadLoop hBBN hAt).2.2⟩
            | inr hEqP =>
              subst hEqP
              cases hOut with
              | inr hEqOw =>
                subst hEqOw
                exact ⟨hp0, (isDeadAtTarget_elim hDeadLoop hBBN hOwP).2.2⟩
              | inl hInBr =>
                let ⟨cb, hMem⟩ := hInBr
                have hAt := list_all_mem_true hBrAllP hMem
                exact ⟨hp0, (isDeadAtTarget_elim hDeadLoop hBBN hAt).2.2⟩
          cases dv with
          | scalar sv =>
            dsimp
            cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
            | error fk => exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
            | ok tgt =>
              have hOut : (∃ cb, (cb, tgt) ∈ targets.branches) ∨ tgt = targets.otherwise := by
                cases evalSwitchBranches_cases hSw with
                | inl hB => exact Or.inl hB
                | inr hO => exact Or.inr hO.1
              exact Or.inl ⟨tgt, l1, l2, rfl, rfl, hFinish tgt hOut, hM1.1, hM1.2.1⟩
          | bool bv =>
            dsimp
            cases hSw : evalBoolSwitchBranches bv targets.otherwise targets.branches with
            | error fk => exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
            | ok tgt =>
              have hOut := evalBoolSwitchBranches_cases hSw
              exact Or.inl ⟨tgt, l1, l2, rfl, rfl, hFinish tgt hOut, hM1.1, hM1.2.1⟩
          | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ =>
            exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)

private noncomputable def MoveToCopyBisimRel (cert : ProgramDeadCert)
    (pSrc pTgt : Program) (s t : State) : Prop :=
  ∃ fSrc fTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    ∀ bSrc,
      Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
      ∃ deadAtEntry bTgt,
        Trusted.MirSemantics.getElem? cert fSrc.defId = some deadAtEntry ∧
        Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
        applyMoveToCopyDeadBody deadAtEntry bSrc = some bTgt ∧
        LocalsWellTyped bSrc.locals fSrc.locals ∧
        LocalsWellTyped bSrc.locals fTgt.locals ∧
        ∀ bbSrc,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
          DeadMaskedEq bSrc.locals
            (fun d => d ≠ 0 ∧
              isDeadAcrossCfg bSrc.locals.length deadAtEntry
                bSrc.basicBlocks.length d
                (bbSrc.statements.drop fSrc.stmtIdx) bbSrc.terminator = true)
            fSrc.locals fTgt.locals

private theorem moveToCopyDead_initState_eq {cert : ProgramDeadCert}
    {pSrc : Program} {bodies' : List Body}
    (hLen : cert.length = pSrc.bodies.length)
    (hMap : mapOption (fun pr => applyMoveToCopyDeadBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some bodies')
    (q : Query) :
    initState pSrc q = initState { pSrc with bodies := bodies' } q := by
  apply initState_eq_of_matching_entry q (programHeaderEq_with_bodies pSrc bodies')
  · dsimp only
    cases hX : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId with
    | none =>
      constructor
      · intro _
        cases hY : Trusted.MirSemantics.getElem? bodies' pSrc.entryDefId with
        | none => rfl
        | some y =>
          let ⟨_, x, _, hX', _⟩ := mapOption_zip_getElem?_right hLen hMap hY
          rw [hX] at hX'; cases hX'
      · intro _; rfl
    | some x =>
      let ⟨_, y, _, hY, _⟩ := mapOption_zip_getElem?_left hLen hMap hX
      rw [hY]
      constructor <;> (intro h; cases h)
  · intro bSrc hBS
    let ⟨deadC, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLen hMap hBS
    let ⟨_, _, hBHdr, _, hEmpty, hBounds, hLoop⟩ := applyMoveToCopyDeadBody_props hAp
    exact ⟨bTgt, hBT, hBHdr, hEmpty, hBounds, hLoop q.args⟩

private theorem moveToCopyDead_query_iff {cert : ProgramDeadCert}
    {pSrc : Program} {bodies' : List Body}
    (hLen : cert.length = pSrc.bodies.length)
    (hMap : mapOption (fun pr => applyMoveToCopyDeadBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some bodies')
    (q : Query) :
    let pTgt : Program := { pSrc with bodies := bodies' }
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let pTgt : Program := { pSrc with bodies := bodies' }
  apply bisim_lockstep_query_iff (R := MoveToCopyBisimRel cert pSrc pTgt)
    (moveToCopyDead_initState_eq hLen hMap q)
  · intro s₀ hInitS
    let ⟨_, _, body, hBody, _, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hInitS
    subst hEqS
    have hWt0 := initLocalsLoop_wellTyped hArgs
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, fun bSrc hBS => ?_⟩
    dsimp at hBS; rw [hBody] at hBS; injection hBS with eB; subst eB
    let ⟨deadC, bTgt, hDC, hBT, hAp⟩ := mapOption_zip_getElem?_left hLen hMap hBody
    exact ⟨deadC, bTgt, hDC, hBT, hAp, hWt0, hWt0,
      fun _ _ => deadMaskedEq_refl hWt0⟩
  · intro s t hR
    let ⟨fSrc, fTgt, hFS, hFT, hCM, hDefEq, hBlkEq, hIdxEq, hBInv⟩ := hR
    cases s with
    | mk fsS cmS =>
      cases t with
      | mk fsT cmT =>
        dsimp at hFS hFT hCM; subst hFS; subst hFT; subst hCM
        cases hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId with
        | none =>
          have hBTgtNone : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = none := by
            rw [← hDefEq]
            dsimp [pTgt]
            cases hY : Trusted.MirSemantics.getElem? bodies' fSrc.defId with
            | none => rfl
            | some y =>
              let ⟨_, x, _, hX, _⟩ := mapOption_zip_getElem?_right hLen hMap hY
              rw [hBSrc] at hX; cases hX
          refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
          · unfold evalStep; dsimp; rw [hBSrc]
          · unfold evalStep; dsimp; rw [hBTgtNone]
        | some bSrc =>
          let ⟨deadAtEntry, bTgt, hDC, hBTgt, hAp, hWt1, hWt2, hBBInv⟩ :=
            hBInv bSrc hBSrc
          let ⟨hCert, hBTgtEq, hBHdr, _, _, _, _⟩ :=
            applyMoveToCopyDeadBody_props hAp
          let ⟨_, hDeadLoop⟩ := bool_and_true hCert
          let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
          have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
            rw [← hDefEq]; exact hBTgt
          cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
          | none =>
            have hBBTgtNone : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
              rw [← hBlkEq, hBTgtEq]; dsimp
              rw [getElem?_map, hBBSrc]; rfl
            refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
            · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]
            · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgtNone]
          | some bbSrc =>
            have hMask := hBBInv bbSrc hBBSrc
            let bbTgt := rewriteMoveToCopyDeadBlock bSrc.locals.length deadAtEntry
              bSrc.basicBlocks.length bbSrc
            have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
              rw [← hBlkEq, hBTgtEq]; dsimp
              rw [getElem?_map, hBBSrc]; rfl
            cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
            | some sSrc =>
              have hDropS := drop_eq_cons_of_getElem? hStSrc
              rw [hDropS] at hMask
              let restSrc := bbSrc.statements.drop (fSrc.stmtIdx + 1)
              let sTgt := rewriteMoveToCopyDeadSingleStmt bSrc.locals.length deadAtEntry
                bSrc.basicBlocks.length bbSrc.terminator restSrc sSrc
              have hDropT : bbTgt.statements.drop fSrc.stmtIdx =
                  sTgt :: rewriteMoveToCopyDeadStmts bSrc.locals.length deadAtEntry
                    bSrc.basicBlocks.length bbSrc.terminator restSrc := by
                dsimp [bbTgt, rewriteMoveToCopyDeadBlock]
                rw [rewriteMoveToCopyDeadStmts_drop, hDropS]
                rfl
              let ⟨hStTgt0, _⟩ := getElem?_of_drop_eq_cons hDropT
              have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some sTgt := by
                rw [← hIdxEq]; exact hStTgt0
              cases evalStatement_moveToCopy_step (fTgt := fTgt) (cm := cmS)
                  hLocEq hMask with
              | inl hFault =>
                let ⟨fk, e1, e2⟩ := hFault
                refine Or.inr (Or.inr ⟨fk, ?_, ?_⟩)
                · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                  rw [hStSrc]; exact e1
                · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                  rw [hStTgt2]; exact e2
              | inr hStep =>
                let ⟨l1, l2, e1, e2, hMaskNext⟩ := hStep
                refine Or.inl ⟨
                  { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1 }],
                    callerMem := cmS },
                  { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2 }],
                    callerMem := cmS },
                  ?_, ?_,
                  { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1 },
                  { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2 },
                  rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
                · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                  rw [hStSrc]; exact e1
                · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                  rw [hStTgt2]; exact e2
                · intro bS2 hBS2
                  dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                  refine ⟨deadAtEntry, bTgt, hDC, hBTgt, hAp,
                    hMaskNext.1, hMaskNext.2.1, ?_⟩
                  intro bbS2 hBBS2
                  dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                  exact hMaskNext
            | none =>
              have hGe : bbSrc.statements.length ≤ fSrc.stmtIdx := by
                cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
                | inr hge => exact hge
                | inl hlt =>
                  let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
                  rw [hStSrc] at hx; cases hx
              rw [drop_eq_nil_of_ge hGe] at hMask
              have hLenStEq : bbTgt.statements.length = bbSrc.statements.length :=
                rewriteMoveToCopyDeadStmts_length bbSrc.statements
              have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none :=
                getElem?_none_of_ge (by rw [← hIdxEq, hLenStEq]; exact hGe)
              cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
              | false =>
                have hEnd2 : Nat.beq fTgt.stmtIdx bbTgt.statements.length = false := by
                  rw [← hIdxEq, hLenStEq]; exact hEnd
                refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
                · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                  rw [hStSrc]; dsimp; rw [hEnd]; rfl
                · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                  rw [hStTgt2]; dsimp; rw [hEnd2]; rfl
              | true =>
                have hEnd2 : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
                  rw [← hIdxEq, hLenStEq]; exact hEnd
                cases evalTerminator_moveToCopy_step (bTgt := bTgt) (bbSrc := bbSrc)
                    (fTgt := fTgt) (cm := cmS) hLocEq hDeadLoop hMask with
                | inr hDF =>
                  cases hDF with
                  | inl hD =>
                    let ⟨out, d1, d2⟩ := hD
                    refine Or.inr (Or.inl ⟨out, ?_, ?_⟩)
                    · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                      rw [hStSrc]; dsimp; rw [hEnd]; dsimp; exact d1
                    · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                      rw [hStTgt2]; dsimp; rw [hEnd2]; dsimp; exact d2
                  | inr hF =>
                    let ⟨fk, d1, d2⟩ := hF
                    refine Or.inr (Or.inr ⟨fk, ?_, ?_⟩)
                    · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                      rw [hStSrc]; dsimp; rw [hEnd]; dsimp; exact d1
                    · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                      rw [hStTgt2]; dsimp; rw [hEnd2]; dsimp; exact d2
                | inl hST =>
                  let ⟨tgt, l1, l2, t1, t2, hNextFn, hWtL1, hWtL2⟩ := hST
                  refine Or.inl ⟨
                    { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1 }],
                      callerMem := cmS },
                    { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2 }],
                      callerMem := cmS },
                    ?_, ?_,
                    { fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1 },
                    { fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2 },
                    rfl, rfl, rfl, hDefEq, rfl, rfl, ?_⟩
                  · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                    rw [hStSrc]; dsimp; rw [hEnd]; dsimp; exact t1
                  · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                    rw [hStTgt2]; dsimp; rw [hEnd2]; dsimp; exact t2
                  · intro bS2 hBS2
                    dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                    exact ⟨deadAtEntry, bTgt, hDC, hBTgt, hAp, hWtL1, hWtL2,
                      fun bbNext hBBN => hNextFn bbNext hBBN⟩

private theorem applyMoveToCopyDeadProgram_equiv {cert : ProgramDeadCert}
    {pSrc pTgt : Program}
    (hApply : applyMoveToCopyDeadProgram cert pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  unfold applyMoveToCopyDeadProgram at hApply
  cases hLenB : Nat.beq cert.length pSrc.bodies.length with
  | false => rw [hLenB] at hApply; cases hApply
  | true =>
    rw [hLenB] at hApply; dsimp at hApply
    have hLen := nat_beq_eq hLenB
    cases hMap : mapOption (fun pr => applyMoveToCopyDeadBody pr.1 pr.2)
        (List.zip cert pSrc.bodies) with
    | none => rw [hMap] at hApply; cases hApply
    | some bodies' =>
      rw [hMap] at hApply
      injection hApply with hEqP; subst hEqP
      have hIds : pSrc.bodies.map Body.identity = bodies'.map Body.identity := by
        have hLenEq : pSrc.bodies.length = bodies'.length :=
          ((mapOption_length hMap).trans (zip_length_eq hLen)).symm
        apply list_eq_of_getElem?_eq
        · rw [map_length_eq, map_length_eq, hLenEq]
        · intro i
          rw [getElem?_map, getElem?_map]
          cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies i with
          | none =>
            have hBTNone : Trusted.MirSemantics.getElem? bodies' i = none := by
              cases hY : Trusted.MirSemantics.getElem? bodies' i with
              | none => rfl
              | some y =>
                let ⟨_, x, _, hX, _⟩ := mapOption_zip_getElem?_right hLen hMap hY
                rw [hBS] at hX; cases hX
            rw [hBTNone]
          | some bSrc =>
            let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLen hMap hBS
            rw [hBT]; dsimp [Option.map]
            let ⟨_, _, hBHdr, _, _, _, _⟩ := applyMoveToCopyDeadBody_props hAp
            rw [(bodyHeaderEq_elim hBHdr).2.2.2]
      refine ⟨?_, programHeaderEq_with_bodies pSrc bodies', hIds⟩
      apply fullSemanticEquiv_of_query_iff (programHeaderEq_with_bodies pSrc bodies')
      · intro defId bSrc bTgt hBS hBT
        let ⟨_, bTgt', _, hBT', hAp⟩ := mapOption_zip_getElem?_left hLen hMap hBS
        dsimp at hBT; rw [hBT] at hBT'; injection hBT' with eB; subst eB
        let ⟨_, _, hBHdr, _, hEmpty, hBounds, _⟩ := applyMoveToCopyDeadBody_props hAp
        exact ⟨hBHdr, hEmpty, hBounds⟩
      · exact moveToCopyDead_query_iff hLen hMap
      · intro defId args
        exact (moveToCopyDead_query_iff (pSrc := entryProgForBody pSrc defId)
          hLen hMap { args := args }).1

/-! #### Pass Family 5: `.compactUnusedTrailingLocals (newCount : Nat)` -/

private theorem initLocalsLoop_take_comm {bSrc : Body} {args : List Val}
    {newCount : Nat} :
    ∀ base tys k,
      initLocalsLoop { bSrc with locals := bSrc.locals.take newCount } args
        base (tys.take k) =
      (initLocalsLoop bSrc args base tys).take k := by
  intro base tys
  induction tys generalizing base with
  | nil => intro k; cases k <;> rfl
  | cons ty rest ih =>
    intro k
    cases k with
    | zero => rfl
    | succ m =>
      change _ :: initLocalsLoop { bSrc with locals := bSrc.locals.take newCount } args
        (base + 1) (rest.take m) =
        _ :: (initLocalsLoop bSrc args (base + 1) rest).take m
      rw [ih (base + 1) m]
      rfl

private theorem storageAnnotationsInBounds_of_allLocalsLt {b : Body} {bound : Nat}
    (hLe : bound ≤ b.locals.length)
    (hAll : b.basicBlocks.all (blockAllLocalsLt bound) = true) :
    storageAnnotationsInBounds b = true := by
  unfold storageAnnotationsInBounds
  dsimp only
  revert hAll
  induction b.basicBlocks with
  | nil => intro _; rfl
  | cons bb rest ih =>
    intro hAll
    dsimp [List.all] at hAll
    let ⟨hBB, hRest⟩ := bool_and_true hAll
    dsimp [blockAllLocalsLt] at hBB
    let ⟨hSts, _⟩ := bool_and_true hBB
    dsimp [List.all]
    refine bool_and_intro ?_ (ih hRest)
    revert hSts
    induction bb.statements with
    | nil => intro _; rfl
    | cons st srest ihs =>
      intro hSts
      dsimp [List.all] at hSts
      let ⟨hSt, hSRest⟩ := bool_and_true hSts
      dsimp [List.all]
      refine bool_and_intro ?_ (ihs hSRest)
      cases st with
      | nop | assign _ _ | unsupported => rfl
      | storageLive id | storageDead id =>
        dsimp [stmtLocalsLt] at hSt
        exact nat_lt_blt (Nat.lt_of_lt_of_le (nat_blt_lt hSt) hLe)

private theorem canCompactBodyLocals_props {newCount : Nat} {b : Body}
    (h : canCompactBodyLocals newCount b = true) :
    let bTgt : Body := { b with locals := b.locals.take newCount }
    b.argumentCount < newCount ∧
    newCount ≤ b.locals.length ∧
    bTgt.locals.length = newCount ∧
    Nat.blt b.argumentCount b.locals.length = true ∧
    Nat.blt bTgt.argumentCount bTgt.locals.length = true ∧
    storageAnnotationsInBounds b = true ∧
    storageAnnotationsInBounds bTgt = true ∧
    b.locals.all isSupportedScalarOrUnitTy =
      bTgt.locals.all isSupportedScalarOrUnitTy ∧
    (bTgt.locals.drop 1).take bTgt.argumentCount =
      (b.locals.drop 1).take b.argumentCount ∧
    b.basicBlocks.all (blockAllLocalsLt newCount) = true := by
  unfold canCompactBodyLocals at h
  let ⟨h123, hBBAll⟩ := bool_and_true h
  let ⟨h12, hDropSup⟩ := bool_and_true h123
  let ⟨hAcLtB, hNcLeB⟩ := bool_and_true h12
  have hAcLt := nat_blt_lt hAcLtB
  have hNcLe := nat_ble_le hNcLeB
  have hTakeLen : (b.locals.take newCount).length = newCount :=
    take_length_of_le hNcLe
  have hStSrc := storageAnnotationsInBounds_of_allLocalsLt hNcLe hBBAll
  have hStTgt : storageAnnotationsInBounds { b with locals := b.locals.take newCount } = true :=
    storageAnnotationsInBounds_of_allLocalsLt (b := { b with locals := b.locals.take newCount })
      (by rw [hTakeLen]; exact Nat.le_refl newCount) hBBAll
  have hSupEq : b.locals.all isSupportedScalarOrUnitTy =
      (b.locals.take newCount).all isSupportedScalarOrUnitTy := by
    rw [list_all_eq_take_drop isSupportedScalarOrUnitTy b.locals newCount,
        hDropSup, Bool.and_true]
  exact ⟨hAcLt, hNcLe, hTakeLen,
    nat_lt_blt (Nat.lt_of_lt_of_le hAcLt hNcLe),
    by dsimp; rw [hTakeLen]; exact hAcLtB,
    hStSrc, hStTgt, hSupEq, take_drop1_of_lt b.locals hAcLt, hBBAll⟩

private theorem evalOperandToSlot_take_comm {bodyLocals : List MirTy}
    {locals : List LocalSlot} {nc : Nat} {op : Operand}
    (hLen : locals.length = bodyLocals.length)
    (hOp : operandLocalsLt nc op = true) :
    (∃ fk,
      evalOperandToSlot bodyLocals locals op = .error fk ∧
      evalOperandToSlot (bodyLocals.take nc) (locals.take nc) op = .error fk) ∨
    (∃ ty optVal locals',
      evalOperandToSlot bodyLocals locals op = .ok (ty, optVal, locals') ∧
      evalOperandToSlot (bodyLocals.take nc) (locals.take nc) op =
        .ok (ty, optVal, locals'.take nc) ∧
      locals'.length = bodyLocals.length) := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot]
    cases evalConstLit c.ty c.lit with
    | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
    | ok v => exact Or.inr ⟨c.ty, some v, locals, rfl, rfl, hLen⟩
  | copy p =>
    dsimp [operandLocalsLt] at hOp
    have hLt := nat_blt_lt hOp
    dsimp [evalOperandToSlot]
    cases p.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      rw [getElem?_take_of_lt bodyLocals hLt, getElem?_take_of_lt locals hLt]
      cases Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        cases Trusted.MirSemantics.getElem? locals p.localId with
        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | some sl =>
          cases sl with
          | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
          | live opt => exact Or.inr ⟨ty, opt, locals, rfl, rfl, hLen⟩
  | move p =>
    dsimp [operandLocalsLt] at hOp
    have hLt := nat_blt_lt hOp
    dsimp [evalOperandToSlot]
    cases p.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      rw [getElem?_take_of_lt bodyLocals hLt, getElem?_take_of_lt locals hLt]
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | some sl =>
          cases sl with
          | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
          | live opt =>
            dsimp
            have hLtL : p.localId < locals.length := by
              rw [hLen]; exact getElem?_some_lt hTy
            let ⟨locals', hSet⟩ := setElem?_some_of_lt locals p.localId
              (liveUninitSlot ty) hLtL
            rw [hSet, setElem?_take_comm hLt hSet]
            exact Or.inr ⟨ty, opt, locals', rfl, rfl,
              (setElem?_length hSet).trans hLen⟩

private theorem evalPrimitiveOperand_take_comm {bodyLocals : List MirTy}
    {locals : List LocalSlot} {nc : Nat} {op : Operand}
    (hLen : locals.length = bodyLocals.length)
    (hOp : operandLocalsLt nc op = true) :
    (∃ fk,
      evalPrimitiveOperand bodyLocals locals op = .error fk ∧
      evalPrimitiveOperand (bodyLocals.take nc) (locals.take nc) op = .error fk) ∨
    (∃ v locals',
      evalPrimitiveOperand bodyLocals locals op = .ok (v, locals') ∧
      evalPrimitiveOperand (bodyLocals.take nc) (locals.take nc) op =
        .ok (v, locals'.take nc) ∧
      locals'.length = bodyLocals.length) := by
  dsimp [evalPrimitiveOperand]
  cases evalOperandToSlot_take_comm hLen hOp with
  | inl hErr =>
    let ⟨fk, e1, e2⟩ := hErr
    rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
  | inr hOk =>
    let ⟨ty, optVal, l1, e1, e2, hLen1⟩ := hOk
    rw [e1, e2]; dsimp
    cases isPrimitiveReadableTy ty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      cases optVal with
      | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
      | some v => exact Or.inr ⟨v, l1, rfl, rfl, hLen1⟩

private theorem evalRvalue_take_comm {bodyLocals : List MirTy}
    {locals : List LocalSlot} {nc : Nat} {dstTy : MirTy} {rv : Rvalue}
    (hLen : locals.length = bodyLocals.length)
    (hRv : rvalueLocalsLt nc rv = true) :
    (∃ fk,
      evalRvalue bodyLocals locals dstTy rv = .error fk ∧
      evalRvalue (bodyLocals.take nc) (locals.take nc) dstTy rv = .error fk) ∨
    (∃ v locals',
      evalRvalue bodyLocals locals dstTy rv = .ok (v, locals') ∧
      evalRvalue (bodyLocals.take nc) (locals.take nc) dstTy rv =
        .ok (v, locals'.take nc) ∧
      locals'.length = bodyLocals.length) := by
  cases rv with
  | use o =>
    dsimp [evalRvalue]
    cases evalOperandToSlot_take_comm hLen hRv with
    | inl hErr =>
      let ⟨fk, e1, e2⟩ := hErr
      rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hOk =>
      let ⟨sTy, optVal, l1, e1, e2, hLen1⟩ := hOk
      rw [e1, e2]; dsimp
      cases MirTy.beq sTy dstTy with
      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | true =>
        dsimp
        cases optVal with
        | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
        | some v => exact Or.inr ⟨v, l1, rfl, rfl, hLen1⟩
  | unaryOp uop o =>
    dsimp [evalRvalue]
    cases evalPrimitiveOperand_take_comm hLen hRv with
    | inl hErr =>
      let ⟨fk, e1, e2⟩ := hErr
      rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hOk =>
      let ⟨ov, l1, e1, e2, hLen1⟩ := hOk
      rw [e1, e2]; dsimp
      cases evalUnOp uop ov with
      | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
      | ok res => exact Or.inr ⟨res, l1, rfl, rfl, hLen1⟩
  | binaryOp bop l r =>
    let ⟨hL, hR⟩ := bool_and_true hRv
    dsimp [evalRvalue]
    cases evalPrimitiveOperand_take_comm hLen hL with
    | inl hErrL =>
      let ⟨fk, e1, e2⟩ := hErrL
      rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
    | inr hOkL =>
      let ⟨vl, l1, e1, e2, hLen1⟩ := hOkL
      rw [e1, e2]; dsimp
      cases evalPrimitiveOperand_take_comm hLen1 hR with
      | inl hErrR =>
        let ⟨fk, er1, er2⟩ := hErrR
        rw [er1, er2]; exact Or.inl ⟨fk, rfl, rfl⟩
      | inr hOkR =>
        let ⟨vr, l2, er1, er2, hLen2⟩ := hOkR
        rw [er1, er2]; dsimp
        cases evalBinOp bop vl vr with
        | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
        | ok res => exact Or.inr ⟨res, l2, rfl, rfl, hLen2⟩
  | discriminant p =>
    dsimp [rvalueLocalsLt] at hRv
    have hLt := nat_blt_lt hRv
    dsimp [evalRvalue]
    cases p.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      rw [getElem?_take_of_lt bodyLocals hLt, getElem?_take_of_lt locals hLt]
      cases Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        cases ty with
        | enum ety =>
          cases Trusted.MirSemantics.getElem? locals p.localId with
          | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
          | some slot =>
            dsimp
            cases enumAdmitted ety with
            | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
            | true =>
              dsimp
              cases ety.tagRepr with
              | zeroSized =>
                cases slot with
                | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                    | some _ => exact Or.inr ⟨_, locals, rfl, rfl, hLen⟩
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                        | some _ => exact Or.inr ⟨_, locals, rfl, rfl, hLen⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ =>
                      exact Or.inl ⟨.unsupported, rfl, rfl⟩
              | scalar _ _ =>
                cases slot with
                | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
                | live opt =>
                  cases opt with
                  | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                        | some _ => exact Or.inr ⟨_, locals, rfl, rfl, hLen⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ =>
                      exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
          exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported =>
    exact Or.inl ⟨.unsupported, rfl, rfl⟩

private theorem evalStatement_compact_bisim {bSrc : Body} {nc : Nat}
    {fSrc : FrameState} {cm : CallerMemory} {stmt : StatementKind}
    (hLen : fSrc.locals.length = bSrc.locals.length)
    (hSt : stmtLocalsLt nc stmt = true) :
    let bTgt : Body := { bSrc with locals := bSrc.locals.take nc }
    let fTgt : FrameState := { fSrc with locals := fSrc.locals.take nc }
    (∃ fk,
      evalStatement bSrc fSrc cm stmt = .fault fk ∧
      evalStatement bTgt fTgt cm stmt = .fault fk) ∨
    (∃ locs',
      evalStatement bSrc fSrc cm stmt =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmt =
        .step { frames := [{ fTgt with stmtIdx := fSrc.stmtIdx + 1, locals := locs'.take nc }],
                callerMem := cm } ∧
      locs'.length = bSrc.locals.length) := by
  dsimp only
  cases stmt with
  | nop => exact Or.inr ⟨fSrc.locals, rfl, rfl, hLen⟩
  | unsupported => exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | storageLive id =>
    dsimp [stmtLocalsLt] at hSt
    have hLt := nat_blt_lt hSt
    dsimp [evalStatement]
    rw [getElem?_take_of_lt bSrc.locals hLt]
    cases hTy : Trusted.MirSemantics.getElem? bSrc.locals id with
    | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | some ty =>
      dsimp
      have hLtL : id < fSrc.locals.length := by rw [hLen]; exact getElem?_some_lt hTy
      let ⟨locs', hSet⟩ := setElem?_some_of_lt fSrc.locals id (liveUninitSlot ty) hLtL
      rw [hSet, setElem?_take_comm hLt hSet]
      exact Or.inr ⟨locs', rfl, rfl, (setElem?_length hSet).trans hLen⟩
  | storageDead id =>
    dsimp [stmtLocalsLt] at hSt
    have hLt := nat_blt_lt hSt
    dsimp [evalStatement]
    cases Nat.beq id 0 with
    | true => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | false =>
      dsimp
      cases Nat.lt_or_ge id fSrc.locals.length with
      | inr hGe =>
        have hGeT : (fSrc.locals.take nc).length ≤ id := by
          cases Nat.lt_or_ge nc fSrc.locals.length with
          | inl hNcLt => exact False.elim (Nat.not_lt_of_ge hGe (Nat.lt_trans hLt hNcLt))
          | inr hNcGe =>
            have hTakeAll : ∀ (xs : List LocalSlot) (k : Nat),
                xs.length ≤ k → (xs.take k).length = xs.length := by
              intro xs
              induction xs with
              | nil => intro k _; cases k <;> rfl
              | cons _ rs ihr =>
                intro k hk
                cases k with
                | zero => exact False.elim (Nat.not_succ_le_zero rs.length hk)
                | succ m =>
                  dsimp [List.take, List.length]
                  rw [ihr m (Nat.le_of_succ_le_succ hk)]
            rw [hTakeAll fSrc.locals nc hNcGe]
            exact hGe
        rw [setElem?_none_of_ge fSrc.locals id .dead hGe,
            setElem?_none_of_ge (fSrc.locals.take nc) id .dead hGeT]
        exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | inl hLtL =>
        let ⟨locs', hSet⟩ := setElem?_some_of_lt fSrc.locals id .dead hLtL
        rw [hSet, setElem?_take_comm hLt hSet]
        exact Or.inr ⟨locs', rfl, rfl, (setElem?_length hSet).trans hLen⟩
  | assign dst rv =>
    dsimp [stmtLocalsLt] at hSt
    let ⟨hDstB, hRvB⟩ := bool_and_true hSt
    have hDstLt := nat_blt_lt hDstB
    dsimp [evalStatement]
    cases dst.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      dsimp
      rw [getElem?_take_of_lt bSrc.locals hDstLt]
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some dstTy =>
        dsimp
        cases evalRvalue_take_comm (dstTy := dstTy) hLen hRvB with
        | inl hErr =>
          let ⟨fk, e1, e2⟩ := hErr
          rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
        | inr hOk =>
          let ⟨val, l1, e1, e2, hLen1⟩ := hOk
          rw [e1, e2]; dsimp [writePlace]
          cases checkVal val dstTy with
          | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
          | true =>
            dsimp
            rw [getElem?_take_of_lt l1 hDstLt]
            cases hSl : Trusted.MirSemantics.getElem? l1 dst.localId with
            | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
            | some sl =>
              cases sl with
              | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
              | live _ =>
                have hLtL1 : dst.localId < l1.length := by
                  rw [hLen1]; exact getElem?_some_lt hTy
                let ⟨locs', hSet⟩ := setElem?_some_of_lt l1 dst.localId
                  (.live (some val)) hLtL1
                rw [hSet, setElem?_take_comm hDstLt hSet]
                exact Or.inr ⟨locs', rfl, rfl, (setElem?_length hSet).trans hLen1⟩

private noncomputable def CompactBisimRel (nc : Nat) (pSrc pTgt : Program)
    (s t : State) : Prop :=
  ∃ fSrc,
    s.frames = [fSrc] ∧
    t.frames = [{ fSrc with locals := fSrc.locals.take nc }] ∧
    s.callerMem = t.callerMem ∧
    ∀ bSrc,
      Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
      fSrc.locals.length = bSrc.locals.length ∧
      ∃ bTgt,
        Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
        applyCompactTrailingLocalsBody nc bSrc = some bTgt

private theorem list_all_getElem? {α : Type} {p : α → Bool} {xs : List α}
    {i : Nat} {x : α} (hAll : xs.all p = true)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) :
    p x = true := by
  induction xs generalizing i with
  | nil => cases hGet
  | cons a rest ih =>
    dsimp [List.all] at hAll
    let ⟨ha, hRest⟩ := bool_and_true hAll
    cases i with
    | zero => injection hGet with hEq; subst hEq; exact ha
    | succ k => exact ih hRest hGet

private theorem compactTrailingLocals_query_iff {nc : Nat} {pSrc : Program}
    {bodies' : List Body}
    (hMap : mapOption (applyCompactTrailingLocalsBody nc) pSrc.bodies = some bodies')
    (q : Query) :
    let pTgt : Program := { pSrc with bodies := bodies' }
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let pTgt : Program := { pSrc with bodies := bodies' }
  have hInit :
      (∀ fk, initState pSrc q = .error fk ↔ initState pTgt q = .error fk) ∧
      (∀ s₀, initState pSrc q = .ok s₀ →
        ∃ t₀, initState pTgt q = .ok t₀ ∧ CompactBisimRel nc pSrc pTgt s₀ t₀) ∧
      (∀ t₀, initState pTgt q = .ok t₀ →
        ∃ s₀, initState pSrc q = .ok s₀ ∧ CompactBisimRel nc pSrc pTgt s₀ t₀) := by
    unfold initState
    dsimp [pTgt]
    cases (!Nat.beq pSrc.pointerWidthBits 64 || !Nat.beq pSrc.mirProfileVersion 1) with
    | true =>
      exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | false =>
      rw [if_bool_false rfl, if_bool_false rfl]
      cases (!q.callerMem.allocations.isEmpty) with
      | true =>
        exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | false =>
        rw [if_bool_false rfl, if_bool_false rfl]
        cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId with
        | none =>
          rw [(mapOption_getElem?_none_iff pSrc.entryDefId hMap).mp hBS]
          exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h), fun _ h => (by cases h)⟩
        | some bSrc =>
          let ⟨bTgt, hBT, hAp⟩ := mapOption_getElem?_left hMap hBS
          rw [hBT]; dsimp
          unfold applyCompactTrailingLocalsBody at hAp
          cases hCan : canCompactBodyLocals nc bSrc with
          | false => rw [hCan] at hAp; cases hAp
          | true =>
            rw [hCan] at hAp; injection hAp with eBT; subst eBT
            let ⟨_, _, _, hBltS, hBltT, hStS, hStT, hSupEq, hParamEq, _⟩ :=
              canCompactBodyLocals_props hCan
            dsimp only
            rw [hBltS, hBltT, hStS, hStT, hSupEq, hParamEq,
                initLocalsLoop_take_comm 0 bSrc.locals nc]
            cases bSrc.basicBlocks.isEmpty with
            | true =>
              exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h), fun _ h => (by cases h)⟩
            | false =>
              dsimp
              cases (! (bSrc.locals.take nc).all isSupportedScalarOrUnitTy) with
              | true =>
                exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h), fun _ h => (by cases h)⟩
              | false =>
                dsimp
                cases (!checkArgsMatch q.args ((bSrc.locals.drop 1).take bSrc.argumentCount)) with
                | true =>
                  exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h), fun _ h => (by cases h)⟩
                | false =>
                  dsimp
                  have hRel0 : CompactBisimRel nc pSrc pTgt
                      { frames := [{ defId := pSrc.entryDefId, blockIdx := 0, stmtIdx := 0,
                                     locals := initLocalsLoop bSrc q.args 0 bSrc.locals }],
                        callerMem := q.callerMem }
                      { frames := [{ defId := pSrc.entryDefId, blockIdx := 0, stmtIdx := 0,
                                     locals := (initLocalsLoop bSrc q.args 0 bSrc.locals).take nc }],
                        callerMem := q.callerMem } := by
                    refine ⟨_, rfl, rfl, rfl, fun bS2 hBS2 => ?_⟩
                    dsimp at hBS2; rw [hBS] at hBS2; injection hBS2 with eB; subst eB
                    refine ⟨initLocalsLoop_length bSrc q.args 0 bSrc.locals,
                            { bSrc with locals := bSrc.locals.take nc }, hBT, ?_⟩
                    unfold applyCompactTrailingLocalsBody
                    rw [if_bool_true hCan]
                  exact ⟨fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩,
                    fun s₀ hS => (by injection hS with e; subst e; exact ⟨_, rfl, hRel0⟩),
                    fun t₀ hT => (by injection hT with e; subst e; exact ⟨_, rfl, hRel0⟩)⟩
  have hStep : ∀ s t, CompactBisimRel nc pSrc pTgt s t →
      StepOutcomeBisim pSrc pTgt (CompactBisimRel nc pSrc pTgt) s t := by
    intro s t ⟨fSrc, hFS, hFT, hCM, hBInv⟩
    cases s with
    | mk fsS cmS =>
      cases t with
      | mk fsT cmT =>
        dsimp at hFS hFT hCM; subst hFS; subst hFT; subst hCM
        cases hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId with
        | none =>
          have hBTNone : Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = none :=
            (mapOption_getElem?_none_iff fSrc.defId hMap).mp hBSrc
          refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
          · unfold evalStep; dsimp; rw [hBSrc]
          · unfold evalStep; dsimp; rw [hBTNone]
        | some bSrc =>
          let ⟨hLenL, bTgt, hBTgt, hAp⟩ := hBInv bSrc hBSrc
          unfold applyCompactTrailingLocalsBody at hAp
          cases hCan : canCompactBodyLocals nc bSrc with
          | false => rw [hCan] at hAp; cases hAp
          | true =>
            rw [hCan] at hAp; injection hAp with eBT; subst eBT
            let ⟨hAcLt, _, _, _, _, _, _, _, _, hBBAll⟩ :=
              canCompactBodyLocals_props hCan
            cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
            | none =>
              refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]
              · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBSrc]
            | some bb =>
              let ⟨hStsAll, hTmLt⟩ := bool_and_true
                (list_all_getElem? (p := blockAllLocalsLt nc) hBBAll hBBSrc)
              cases hSt : Trusted.MirSemantics.getElem? bb.statements fSrc.stmtIdx with
              | some stmt =>
                have hStLt := list_all_getElem? (p := stmtLocalsLt nc) hStsAll hSt
                cases evalStatement_compact_bisim (cm := cmS) hLenL hStLt with
                | inl hF =>
                  let ⟨fk, e1, e2⟩ := hF
                  refine Or.inr (Or.inr ⟨fk, ?_, ?_⟩)
                  · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                    rw [hSt]; exact e1
                  · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBSrc]; dsimp
                    rw [hSt]; exact e2
                | inr hS =>
                  let ⟨locs', e1, e2, hLen'⟩ := hS
                  refine Or.inl ⟨
                    { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs' }],
                      callerMem := cmS },
                    { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs'.take nc }],
                      callerMem := cmS },
                    ?_, ?_,
                    { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs' },
                    rfl, rfl, rfl, ?_⟩
                  · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                    rw [hSt]; exact e1
                  · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBSrc]; dsimp
                    rw [hSt]; exact e2
                  · intro bS2 hBS2
                    dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                    refine ⟨hLen', { bSrc with locals := bSrc.locals.take nc }, hBTgt, ?_⟩
                    unfold applyCompactTrailingLocalsBody
                    rw [if_bool_true hCan]
              | none =>
                cases hEnd : Nat.beq fSrc.stmtIdx bb.statements.length with
                | false =>
                  refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
                  · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                    rw [hSt]; dsimp; rw [hEnd]; rfl
                  · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBSrc]; dsimp
                    rw [hSt]; dsimp; rw [hEnd]; rfl
                | true =>
                  have hEvSEq : evalStep pSrc 0 { frames := [fSrc], callerMem := cmS } =
                      evalTerminator bSrc bb fSrc cmS := by
                    unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                    rw [hSt, if_bool_true hEnd]
                  have hEvTEq : evalStep pTgt 0
                      { frames := [{ fSrc with locals := fSrc.locals.take nc }], callerMem := cmS } =
                      evalTerminator { bSrc with locals := bSrc.locals.take nc } bb
                        { fSrc with locals := fSrc.locals.take nc } cmS := by
                    unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBSrc]; dsimp
                    rw [hSt, if_bool_true hEnd]
                  unfold StepOutcomeBisim
                  rw [hEvSEq, hEvTEq]
                  unfold evalTerminator
                  cases hTm : bb.terminator with
                  | goto tgt =>
                    refine Or.inl ⟨_, _, rfl, rfl,
                      { fSrc with blockIdx := tgt, stmtIdx := 0 }, rfl, rfl, rfl, ?_⟩
                    intro bS2 hBS2
                    dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                    refine ⟨hLenL, _, hBTgt, ?_⟩
                    unfold applyCompactTrailingLocalsBody; rw [if_bool_true hCan]
                  | return_ =>
                    dsimp
                    cases bb.cleanup with
                    | true => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
                    | false =>
                      dsimp
                      have h0Lt : 0 < nc := Nat.lt_of_le_of_lt (Nat.zero_le _) hAcLt
                      rw [getElem?_take_of_lt fSrc.locals h0Lt]
                      cases Trusted.MirSemantics.getElem? fSrc.locals 0 with
                      | none => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
                      | some sl =>
                        cases sl with
                        | dead => exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
                        | live opt =>
                          cases opt with
                          | none => exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
                          | some rv => exact Or.inr (Or.inl ⟨.returned ⟨rv, cmS⟩, rfl, rfl⟩)
                  | unreachable => exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
                  | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
                    exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
                  | switchInt discr targets =>
                    rw [hTm] at hTmLt
                    dsimp [terminatorLocalsLt] at hTmLt
                    dsimp
                    cases evalPrimitiveOperand_take_comm hLenL hTmLt with
                    | inl hErr =>
                      let ⟨fk, e1, e2⟩ := hErr
                      rw [e1, e2]; exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
                    | inr hOk =>
                      let ⟨dv, l1, e1, e2, hLen1⟩ := hOk
                      rw [e1, e2]; dsimp
                      cases dv with
                      | scalar sv =>
                        dsimp
                        cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                        | error fk => exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
                        | ok tgt =>
                          refine Or.inl ⟨_, _, rfl, rfl,
                            { fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1 },
                            rfl, rfl, rfl, ?_⟩
                          intro bS2 hBS2
                          dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                          refine ⟨hLen1, _, hBTgt, ?_⟩
                          unfold applyCompactTrailingLocalsBody; rw [if_bool_true hCan]
                      | bool bv =>
                        dsimp
                        cases evalBoolSwitchBranches bv targets.otherwise targets.branches with
                        | error fk => exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
                        | ok tgt =>
                          refine Or.inl ⟨_, _, rfl, rfl,
                            { fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1 },
                            rfl, rfl, rfl, ?_⟩
                          intro bS2 hBS2
                          dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                          refine ⟨hLen1, _, hBTgt, ?_⟩
                          unfold applyCompactTrailingLocalsBody; rw [if_bool_true hCan]
                      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ =>
                        exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
  -- Lift `hInit` + `hStep` to `(WellFormed, Behavior, ReachesResult (.fault k), Diverges)`
  cases hIS : initState pSrc q with
  | error fk =>
    have hIT : initState pTgt q = .error fk := (hInit.1 fk).mp hIS
    refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · intro ⟨⟨_, hOk, _⟩, _⟩; rw [hIT] at hOk; cases hOk
      · intro ⟨⟨_, hOk, _⟩, _⟩; rw [hIS] at hOk; cases hOk
    · intro out; unfold Behavior ReachesResult; rw [hIT, hIS]
    · intro k; unfold ReachesResult; rw [hIT, hIS]
    · constructor
      · intro ⟨_, hOk, _⟩; rw [hIT] at hOk; cases hOk
      · intro ⟨_, hOk, _⟩; rw [hIS] at hOk; cases hOk
  | ok s₀ =>
    let ⟨t₀, hIT, hR0⟩ := hInit.2.1 s₀ hIS
    have hStepSrc : ∀ s t s', CompactBisimRel nc pSrc pTgt s t →
        evalStep pSrc 0 s = .step s' →
        ∃ t', evalStep pTgt 0 t = .step t' ∧ CompactBisimRel nc pSrc pTgt s' t' := by
      intro s t s' hR hEvS
      cases hStep s t hR with
      | inl h1 =>
        let ⟨s1, t1, e1, e2, hR1⟩ := h1
        rw [hEvS] at e1; injection e1 with eq; subst eq
        exact ⟨t1, e2, hR1⟩
      | inr h23 =>
        cases h23 with
        | inl h2 => let ⟨_, e1, _⟩ := h2; rw [hEvS] at e1; cases e1
        | inr h3 => let ⟨_, e1, _⟩ := h3; rw [hEvS] at e1; cases e1
    have hStepTgt : ∀ s t t', CompactBisimRel nc pSrc pTgt s t →
        evalStep pTgt 0 t = .step t' →
        ∃ s', evalStep pSrc 0 s = .step s' ∧ CompactBisimRel nc pSrc pTgt s' t' := by
      intro s t t' hR hEvT
      cases hStep s t hR with
      | inl h1 =>
        let ⟨s1, t1, e1, e2, hR1⟩ := h1
        rw [hEvT] at e2; injection e2 with eq; subst eq
        exact ⟨s1, e1, hR1⟩
      | inr h23 =>
        cases h23 with
        | inl h2 => let ⟨_, _, e2⟩ := h2; rw [hEvT] at e2; cases e2
        | inr h3 => let ⟨_, _, e2⟩ := h3; rw [hEvT] at e2; cases e2
    have hReachSrc : ∀ s, Reaches pSrc s₀ s →
        ∃ t, Reaches pTgt t₀ t ∧ CompactBisimRel nc pSrc pTgt s t := by
      intro s hRs
      induction hRs with
      | refl => exact ⟨t₀, Reaches.refl t₀, hR0⟩
      | tail _ hSt ih =>
        let ⟨t, hRt, hRst⟩ := ih
        let ⟨t', hEvT, hR'⟩ := hStepSrc _ t _ hRst (step_iff_evalStep.mp hSt)
        exact ⟨t', Reaches.tail hRt (step_iff_evalStep.mpr hEvT), hR'⟩
    have hReachTgt : ∀ t, Reaches pTgt t₀ t →
        ∃ s, Reaches pSrc s₀ s ∧ CompactBisimRel nc pSrc pTgt s t := by
      intro t hRt
      induction hRt with
      | refl => exact ⟨s₀, Reaches.refl s₀, hR0⟩
      | tail _ hSt ih =>
        let ⟨s, hRs, hRst⟩ := ih
        let ⟨s', hEvS, hR'⟩ := hStepTgt s _ _ hRst (step_iff_evalStep.mp hSt)
        exact ⟨s', Reaches.tail hRs (step_iff_evalStep.mpr hEvS), hR'⟩
    have hDoneIff : ∀ out,
        ReachesResult pTgt q (.done out) ↔ ReachesResult pSrc q (.done out) := by
      intro out; unfold ReachesResult; rw [hIT, hIS]
      constructor
      · intro ⟨t, hRt, hStT⟩
        let ⟨s, hRs, hRst⟩ := hReachTgt t hRt
        have hEvT := step_iff_evalStep.mp hStT
        cases hStep s t hRst with
        | inl h1 => let ⟨_, _, _, e2, _⟩ := h1; rw [hEvT] at e2; cases e2
        | inr h23 =>
          cases h23 with
          | inl h2 =>
            let ⟨out', e1, e2⟩ := h2; rw [hEvT] at e2; injection e2 with eq; subst eq
            exact ⟨s, hRs, step_iff_evalStep.mpr e1⟩
          | inr h3 => let ⟨_, _, e2⟩ := h3; rw [hEvT] at e2; cases e2
      · intro ⟨s, hRs, hStS⟩
        let ⟨t, hRt, hRst⟩ := hReachSrc s hRs
        have hEvS := step_iff_evalStep.mp hStS
        cases hStep s t hRst with
        | inl h1 => let ⟨_, _, e1, _, _⟩ := h1; rw [hEvS] at e1; cases e1
        | inr h23 =>
          cases h23 with
          | inl h2 =>
            let ⟨out', e1, e2⟩ := h2; rw [hEvS] at e1; injection e1 with eq; subst eq
            exact ⟨t, hRt, step_iff_evalStep.mpr e2⟩
          | inr h3 => let ⟨_, e1, _⟩ := h3; rw [hEvS] at e1; cases e1
    have hFaultIff : ∀ fk,
        ReachesResult pTgt q (.fault fk) ↔ ReachesResult pSrc q (.fault fk) := by
      intro fk; unfold ReachesResult; rw [hIT, hIS]
      constructor
      · intro ⟨t, hRt, hStT⟩
        let ⟨s, hRs, hRst⟩ := hReachTgt t hRt
        have hEvT := step_iff_evalStep.mp hStT
        cases hStep s t hRst with
        | inl h1 => let ⟨_, _, _, e2, _⟩ := h1; rw [hEvT] at e2; cases e2
        | inr h23 =>
          cases h23 with
          | inl h2 => let ⟨_, _, e2⟩ := h2; rw [hEvT] at e2; cases e2
          | inr h3 =>
            let ⟨fk', e1, e2⟩ := h3; rw [hEvT] at e2; injection e2 with eq; subst eq
            exact ⟨s, hRs, step_iff_evalStep.mpr e1⟩
      · intro ⟨s, hRs, hStS⟩
        let ⟨t, hRt, hRst⟩ := hReachSrc s hRs
        have hEvS := step_iff_evalStep.mp hStS
        cases hStep s t hRst with
        | inl h1 => let ⟨_, _, e1, _, _⟩ := h1; rw [hEvS] at e1; cases e1
        | inr h23 =>
          cases h23 with
          | inl h2 => let ⟨_, e1, _⟩ := h2; rw [hEvS] at e1; cases e1
          | inr h3 =>
            let ⟨fk', e1, e2⟩ := h3; rw [hEvS] at e1; injection e1 with eq; subst eq
            exact ⟨t, hRt, step_iff_evalStep.mpr e2⟩
    refine ⟨?_, hDoneIff, hFaultIff, ?_⟩
    · constructor
      · intro hW
        exact ⟨⟨s₀, hIS, fun _ _ => ⟨0, rfl⟩⟩,
               fun fk hF => hW.2 fk ((hFaultIff fk).mpr hF)⟩
      · intro hW
        exact ⟨⟨t₀, hIT, fun _ _ => ⟨0, rfl⟩⟩,
               fun fk hF => hW.2 fk ((hFaultIff fk).mp hF)⟩
    · constructor
      · intro ⟨t₀', hOkT, trT, h0T, hStT⟩
        rw [hIT] at hOkT; injection hOkT with eq; subst eq
        have hInv : ∀ n, CompactBisimRel nc pSrc pTgt (iterState pSrc s₀ n) (trT n) := by
          intro n
          induction n with
          | zero => rw [h0T]; exact hR0
          | succ k ih =>
            let ⟨s', hEvS, hR'⟩ := hStepTgt _ _ _ ih (step_iff_evalStep.mp (hStT k))
            dsimp [iterState]; rw [hEvS]; exact hR'
        refine ⟨s₀, hIS, iterState pSrc s₀, rfl, fun n => ?_⟩
        let ⟨s', hEvS, _⟩ := hStepTgt _ _ _ (hInv n) (step_iff_evalStep.mp (hStT n))
        apply step_iff_evalStep.mpr; dsimp [iterState]; rw [hEvS]
      · exact diverges_fwd_sim hIS hIT hR0 hStepSrc

private theorem applyCompactTrailingLocalsProgram_equiv {nc : Nat}
    {pSrc pTgt : Program}
    (hApply : applyCompactTrailingLocalsProgram nc pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  unfold applyCompactTrailingLocalsProgram at hApply
  cases hMap : mapOption (applyCompactTrailingLocalsBody nc) pSrc.bodies with
  | none => rw [hMap] at hApply; cases hApply
  | some bodies' =>
    rw [hMap] at hApply; injection hApply with eP; subst eP
    have hIds : pSrc.bodies.map Body.identity = bodies'.map Body.identity := by
      have hLenEq := (mapOption_length hMap).symm
      apply list_eq_of_getElem?_eq
      · rw [map_length_eq, map_length_eq, hLenEq]
      · intro i
        rw [getElem?_map, getElem?_map]
        cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies i with
        | none =>
          rw [(mapOption_getElem?_none_iff i hMap).mp hBS]
        | some bSrc =>
          let ⟨bTgt, hBT, hAp⟩ := mapOption_getElem?_left hMap hBS
          rw [hBT]; dsimp [Option.map]
          unfold applyCompactTrailingLocalsBody at hAp
          cases hCan : canCompactBodyLocals nc bSrc with
          | false => rw [hCan] at hAp; cases hAp
          | true => rw [hCan] at hAp; injection hAp with eB; subst eB; rfl
    refine ⟨?_, programHeaderEq_with_bodies pSrc bodies', hIds⟩
    refine ⟨compactTrailingLocals_query_iff hMap, ?_, ?_⟩
    · intro q post
      let ⟨hWfIff, hBehIff, _, _⟩ := compactTrailingLocals_query_iff hMap q
      constructor
      · intro hSat
        exact ⟨hWfIff.mp hSat.1, fun out hB => hSat.2 out ((hBehIff out).mpr hB)⟩
      · intro hSat
        exact ⟨hWfIff.mpr hSat.1, fun out hB => hSat.2 out ((hBehIff out).mp hB)⟩
    · intro defId bSrc bTgt safetyPre hBS hBT
      let ⟨bTgt', hBT', hAp⟩ := mapOption_getElem?_left hMap hBS
      dsimp at hBT; rw [hBT] at hBT'; injection hBT' with eB; subst eB
      unfold applyCompactTrailingLocalsBody at hAp
      cases hCan : canCompactBodyLocals nc bSrc with
      | false => rw [hCan] at hAp; cases hAp
      | true =>
        rw [hCan] at hAp; injection hAp with eB; subst eB
        let ⟨_, _, _, hBltS, hBltT, hStS, hStT, hSupEq, hParamEq, _⟩ :=
          canCompactBodyLocals_props hCan
        have hAdmEq : BodyStaticAdmitted { pSrc with bodies := bodies' }
            { bSrc with locals := bSrc.locals.take nc } =
            BodyStaticAdmitted pSrc bSrc := by
          unfold BodyStaticAdmitted; dsimp
          rw [hBltS, hBltT, hStS, hStT, hSupEq]
        have hEntryWf := (compactTrailingLocals_query_iff
          (pSrc := entryProgForBody pSrc defId) hMap)
        constructor
        · intro ⟨_, hAdmT, hVerT⟩
          refine ⟨hBS, by rw [← hAdmEq]; exact hAdmT, ?_⟩
          intro args hArgsS hPre
          have hArgsT : ValidEntryArgs { bSrc with locals := bSrc.locals.take nc } args := by
            unfold ValidEntryArgs; rw [hParamEq]; exact hArgsS
          exact (hEntryWf { args := args }).1.mp (hVerT args hArgsT hPre)
        · intro ⟨_, hAdmS, hVerS⟩
          refine ⟨hBT, by rw [hAdmEq]; exact hAdmS, ?_⟩
          intro args hArgsT hPre
          have hArgsS : ValidEntryArgs bSrc args := by
            unfold ValidEntryArgs at hArgsT; unfold ValidEntryArgs
            rw [hParamEq] at hArgsT; exact hArgsT
          exact (hEntryWf { args := args }).1.mpr (hVerS args hArgsS hPre)

/-! ### Shared List / BitVec Helpers for Slice C -/

private theorem bitvec_eq_of_bne_false {n : Nat} {a b : BitVec n}
    (h : (a != b) = false) : a = b := by
  change (!(a == b)) = false at h
  exact bitvec_beq_eq (bool_not_false h)

private theorem nat_beq_succ_succ (a b : Nat) : Nat.beq (a + 1) (b + 1) = Nat.beq a b := rfl

private theorem getElem?_none_ge {α : Type} {xs : List α} {i : Nat}
    (h : Trusted.MirSemantics.getElem? xs i = none) : xs.length ≤ i := by
  induction xs generalizing i with
  | nil => exact Nat.zero_le i
  | cons _ rest ih =>
    cases i with
    | zero => cases h
    | succ k => exact Nat.succ_le_succ (ih h)

private theorem list_any_eq_of_getElem? {α β : Type} {f : α → Bool} {g : β → Bool}
    {xs : List α} {ys : List β}
    (hLen : xs.length = ys.length)
    (hAt : ∀ i x y,
      Trusted.MirSemantics.getElem? xs i = some x →
      Trusted.MirSemantics.getElem? ys i = some y →
      f x = g y) :
    xs.any f = ys.any g := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons x rest ih =>
    cases ys with
    | nil => cases hLen
    | cons y yrest =>
      dsimp [List.any]
      have h0 := hAt 0 x y rfl rfl
      have hTail := ih (Nat.succ.inj hLen) (fun i a b ha hb => hAt (i + 1) a b ha hb)
      rw [h0, hTail]

private theorem list_all_eq_of_getElem? {α β : Type} {f : α → Bool} {g : β → Bool}
    {xs : List α} {ys : List β}
    (hLen : xs.length = ys.length)
    (hAt : ∀ i x y,
      Trusted.MirSemantics.getElem? xs i = some x →
      Trusted.MirSemantics.getElem? ys i = some y →
      f x = g y) :
    xs.all f = ys.all g := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons x rest ih =>
    cases ys with
    | nil => cases hLen
    | cons y yrest =>
      dsimp [List.all]
      have h0 := hAt 0 x y rfl rfl
      have hTail := ih (Nat.succ.inj hLen) (fun i a b ha hb => hAt (i + 1) a b ha hb)
      rw [h0, hTail]

/-! ### Pass Family 2: `.simplifyCfgBranch` (`F1-5`) -/

private theorem pruneOtherwiseBranches_all {ow : BasicBlockId}
    {p : (BitVec 128 × BasicBlockId) → Bool} :
    ∀ bs : List (BitVec 128 × BasicBlockId),
      bs.all p = true → (pruneOtherwiseBranches ow bs).all p = true
  | [], _ => rfl
  | (c, tgt) :: rest, h => by
    dsimp [List.all] at h
    let ⟨hHead, hTail⟩ := bool_and_true h
    dsimp [pruneOtherwiseBranches]
    cases (Nat.beq tgt ow && !hasCaseBitsIn c rest) with
    | true => exact pruneOtherwiseBranches_all rest hTail
    | false =>
      dsimp [List.all]
      exact bool_and_intro hHead (pruneOtherwiseBranches_all rest hTail)

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
      | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

private theorem evalSwitchBranches_valid_total {w : IntWidth} {bits : BitVec 128}
    {ow : BasicBlockId} :
    ∀ bs : List (BitVec 128 × BasicBlockId),
      bs.all (fun br => truncateBits w br.1 == br.1) = true →
      ∃ tgt, evalSwitchBranches w bits ow bs = .ok tgt
  | [], _ => ⟨ow, rfl⟩
  | (cb, tb) :: rest, hAll => by
    dsimp [List.all] at hAll
    let ⟨hHead, hTail⟩ := bool_and_true hAll
    have hTrunc : truncateBits w cb = cb := bitvec_beq_eq hHead
    have hOvf : (truncateBits w cb != cb) = false := by
      rw [hTrunc]; change (!(cb == cb)) = false; rw [bitvec_beq_refl]; rfl
    dsimp [evalSwitchBranches]
    rw [hOvf]; dsimp
    cases (truncateBits w bits == truncateBits w cb) with
    | true => exact ⟨tb, rfl⟩
    | false => exact evalSwitchBranches_valid_total rest hTail

private theorem evalBoolSwitchBranches_valid_total {b : Bool} {ow : BasicBlockId} :
    ∀ bs : List (BitVec 128 × BasicBlockId),
      bs.all (fun br =>
        match evalConstLit .bool (.scalar br.1) with
        | .ok (.bool _) => true
        | _ => false) = true →
      ∃ tgt, evalBoolSwitchBranches b ow bs = .ok tgt
  | [], _ => ⟨ow, rfl⟩
  | (cb, tb) :: rest, hAll => by
    dsimp [List.all] at hAll
    let ⟨hHead, hTail⟩ := bool_and_true hAll
    dsimp [evalBoolSwitchBranches]
    cases hC : evalConstLit .bool (.scalar cb) with
    | error _ => rw [hC] at hHead; cases hHead
    | ok cv =>
      rw [hC] at hHead
      cases cv with
      | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hHead
      | bool cbv =>
        cases cbv <;> cases b <;>
          first | exact ⟨tb, rfl⟩ | exact evalBoolSwitchBranches_valid_total rest hTail

private theorem evalSwitchBranches_no_caseBits {w : IntWidth} {bits : BitVec 128}
    {ow : BasicBlockId} (hWfBits : truncateBits w bits = bits) :
    ∀ bs : List (BitVec 128 × BasicBlockId),
      bs.all (fun br => truncateBits w br.1 == br.1) = true →
      hasCaseBitsIn bits bs = false →
      evalSwitchBranches w bits ow bs = .ok ow
  | [], _, _ => rfl
  | (cb, tb) :: rest, hAll, hNo => by
    dsimp [List.all] at hAll
    let ⟨hHead, hTail⟩ := bool_and_true hAll
    dsimp [hasCaseBitsIn] at hNo
    let ⟨hNeq, hNoRest⟩ := bool_or_false hNo
    have hTruncC : truncateBits w cb = cb := bitvec_beq_eq hHead
    have hOvf : (truncateBits w cb != cb) = false := by
      rw [hTruncC]; change (!(cb == cb)) = false; rw [bitvec_beq_refl]; rfl
    dsimp [evalSwitchBranches]
    rw [hOvf]; dsimp
    rw [hWfBits, hTruncC, hNeq]; dsimp
    exact evalSwitchBranches_no_caseBits hWfBits rest hTail hNoRest

private theorem evalSwitchBranches_pruneOtherwise {w : IntWidth} (bits : BitVec 128)
    (ow : BasicBlockId) :
    ∀ bs : List (BitVec 128 × BasicBlockId),
      bs.all (fun br => truncateBits w br.1 == br.1) = true →
      evalSwitchBranches w bits ow (pruneOtherwiseBranches ow bs) =
        evalSwitchBranches w bits ow bs
  | [], _ => rfl
  | (cb, tb) :: rest, hAll => by
    dsimp [List.all] at hAll
    let ⟨hHead, hTail⟩ := bool_and_true hAll
    have hTruncC : truncateBits w cb = cb := bitvec_beq_eq hHead
    have hOvf : (truncateBits w cb != cb) = false := by
      rw [hTruncC]; change (!(cb == cb)) = false; rw [bitvec_beq_refl]; rfl
    have ih := evalSwitchBranches_pruneOtherwise bits ow rest hTail
    dsimp [pruneOtherwiseBranches]
    cases hDrop : (Nat.beq tb ow && !hasCaseBitsIn cb rest) with
    | false =>
      dsimp [evalSwitchBranches]
      rw [hOvf]; dsimp
      cases (truncateBits w bits == truncateBits w cb) with
      | true => rfl
      | false => exact ih
    | true =>
      let ⟨hTbOw, hNotIn⟩ := bool_and_true hDrop
      have hTbEq := nat_beq_eq hTbOw
      subst hTbEq
      have hNoIn := bool_not_true hNotIn
      dsimp
      rw [ih]
      dsimp [evalSwitchBranches]
      rw [hOvf]; dsimp
      cases hMatch : (truncateBits w bits == truncateBits w cb) with
      | false => rfl
      | true =>
        have hBitsEq : truncateBits w bits = cb := by
          rw [← hTruncC]; exact bitvec_beq_eq hMatch
        have hSub := evalSwitchBranches_no_caseBits (ow := tb)
          (truncateBits_idem w bits) rest hTail (by rw [hBitsEq]; exact hNoIn)
        have hCongr : ∀ rs : List (BitVec 128 × BasicBlockId),
            evalSwitchBranches w (truncateBits w bits) tb rs =
              evalSwitchBranches w bits tb rs := by
          intro rs
          induction rs with
          | nil => rfl
          | cons br rrest ihr =>
            cases br with
            | mk c2 t2 =>
              dsimp [evalSwitchBranches]
              rw [truncateBits_idem]
              cases (truncateBits w c2 != c2) with
              | true => rfl
              | false =>
                dsimp
                cases (truncateBits w bits == truncateBits w c2) with
                | true => rfl
                | false => exact ihr
        rw [← hCongr rest]
        exact hSub

private theorem evalConstLit_bool_scalar_bits {cb : BitVec 128} {b : Bool}
    (h : evalConstLit .bool (.scalar cb) = .ok (.bool b)) :
    cb = (if b then BitVec.ofNat 128 1 else BitVec.ofNat 128 0) := by
  dsimp [evalConstLit] at h
  cases hOvf : (truncateBits .i8 cb != cb) with
  | true => rw [hOvf] at h; cases h
  | false =>
    rw [hOvf] at h; dsimp at h
    have hTrunc : truncateBits .i8 cb = cb := bitvec_eq_of_bne_false hOvf
    have hLt256 : cb.toNat < 256 := truncateBits_eq_iff.mp hTrunc
    cases h0 : (UInt8.ofNat (truncateBits .i8 cb).toNat == 0) with
    | true =>
      rw [h0] at h; injection h with hB; injection hB with hbEq
      subst hbEq
      rw [hTrunc] at h0
      have hU0 : UInt8.ofNat cb.toNat = 0 := eq_of_beq h0
      have hN0 : Nat.mod cb.toNat 256 = 0 := congrArg UInt8.toNat hU0
      have hEq0 : cb.toNat = 0 := (Nat.mod_eq_of_lt hLt256).symm.trans hN0
      exact bitvec_eq_of_toNat_eq hEq0
    | false =>
      rw [h0] at h; dsimp at h
      cases h1 : (UInt8.ofNat (truncateBits .i8 cb).toNat == 1) with
      | false => rw [h1] at h; cases h
      | true =>
        rw [h1] at h; injection h with hB; injection hB with hbEq
        subst hbEq
        rw [hTrunc] at h1
        have hU1 : UInt8.ofNat cb.toNat = 1 := eq_of_beq h1
        have hN1 : Nat.mod cb.toNat 256 = 1 := congrArg UInt8.toNat hU1
        have hEq1 : cb.toNat = 1 := (Nat.mod_eq_of_lt hLt256).symm.trans hN1
        exact bitvec_eq_of_toNat_eq hEq1

private theorem evalBoolSwitchBranches_no_caseBits {b : Bool} {cb : BitVec 128}
    {ow : BasicBlockId}
    (hCb : evalConstLit .bool (.scalar cb) = .ok (.bool b)) :
    ∀ bs : List (BitVec 128 × BasicBlockId),
      bs.all (fun br =>
        match evalConstLit .bool (.scalar br.1) with
        | .ok (.bool _) => true
        | _ => false) = true →
      hasCaseBitsIn cb bs = false →
      evalBoolSwitchBranches b ow bs = .ok ow
  | [], _, _ => rfl
  | (c2, t2) :: rest, hAll, hNo => by
    dsimp [List.all] at hAll
    let ⟨hHead, hTail⟩ := bool_and_true hAll
    dsimp [hasCaseBitsIn] at hNo
    let ⟨hNeq, hNoRest⟩ := bool_or_false hNo
    dsimp [evalBoolSwitchBranches]
    cases hC2 : evalConstLit .bool (.scalar c2) with
    | error _ => rw [hC2] at hHead; cases hHead
    | ok cv =>
      rw [hC2] at hHead
      cases cv with
      | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hHead
      | bool b2 =>
        have hc1 := evalConstLit_bool_scalar_bits hCb
        have hc2 := evalConstLit_bool_scalar_bits hC2
        cases b2 with
        | false =>
          cases b with
          | false =>
            rw [hc1, hc2, bitvec_beq_refl] at hNeq; cases hNeq
          | true =>
            exact evalBoolSwitchBranches_no_caseBits hCb rest hTail hNoRest
        | true =>
          cases b with
          | true =>
            rw [hc1, hc2, bitvec_beq_refl] at hNeq; cases hNeq
          | false =>
            exact evalBoolSwitchBranches_no_caseBits hCb rest hTail hNoRest

private theorem evalBoolSwitchBranches_pruneOtherwise (b : Bool) (ow : BasicBlockId) :
    ∀ bs : List (BitVec 128 × BasicBlockId),
      bs.all (fun br =>
        match evalConstLit .bool (.scalar br.1) with
        | .ok (.bool _) => true
        | _ => false) = true →
      evalBoolSwitchBranches b ow (pruneOtherwiseBranches ow bs) =
        evalBoolSwitchBranches b ow bs
  | [], _ => rfl
  | (cb, tb) :: rest, hAll => by
    dsimp [List.all] at hAll
    let ⟨hHead, hTail⟩ := bool_and_true hAll
    have ih := evalBoolSwitchBranches_pruneOtherwise b ow rest hTail
    dsimp [pruneOtherwiseBranches]
    cases hDrop : (Nat.beq tb ow && !hasCaseBitsIn cb rest) with
    | false =>
      dsimp [evalBoolSwitchBranches]
      cases hC : evalConstLit .bool (.scalar cb) with
      | error _ => rfl
      | ok cv =>
        cases cv with
        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
        | bool cbv =>
          cases cbv <;> cases b <;> first | rfl | exact ih
    | true =>
      let ⟨hTbOw, hNotIn⟩ := bool_and_true hDrop
      have hTbEq := nat_beq_eq hTbOw
      subst hTbEq
      have hNoIn := bool_not_true hNotIn
      dsimp
      rw [ih]
      dsimp [evalBoolSwitchBranches]
      cases hC : evalConstLit .bool (.scalar cb) with
      | error _ => rw [hC] at hHead; cases hHead
      | ok cv =>
        rw [hC] at hHead
        cases cv with
        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hHead
        | bool cbv =>
          cases cbv with
          | false =>
            cases b with
            | true => rfl
            | false => exact evalBoolSwitchBranches_no_caseBits hC rest hTail hNoIn
          | true =>
            cases b with
            | false => rfl
            | true => exact evalBoolSwitchBranches_no_caseBits hC rest hTail hNoIn

private theorem operandStaticTy?_evalSlot_eq {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {opnd : Operand}
    {ty srcTy : MirTy} {optVal : Option Val}
    (hStatic : operandStaticTy? bodyLocals opnd = some ty)
    (hS : evalOperandToSlot bodyLocals locals opnd = .ok (srcTy, optVal, locals')) :
    srcTy = ty := by
  cases opnd with
  | constant c =>
    dsimp [operandStaticTy?] at hStatic
    injection hStatic with hC
    dsimp [evalOperandToSlot] at hS
    cases hCL : evalConstLit c.ty c.lit with
    | error _ => rw [hCL] at hS; cases hS
    | ok _ =>
      rw [hCL] at hS; injection hS with h2; injection h2 with hS2 _
      exact hS2.symm.trans hC
  | copy p =>
    dsimp [operandStaticTy?] at hStatic
    dsimp [evalOperandToSlot] at hS
    cases hPE : p.projection.isEmpty with
    | false => rw [hPE] at hStatic; cases hStatic
    | true =>
      rw [hPE] at hStatic hS; dsimp at hStatic hS
      rw [hStatic] at hS
      cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
      | none => rw [hSl] at hS; cases hS
      | some sl =>
        rw [hSl] at hS
        cases sl with
        | dead => cases hS
        | live _ =>
          injection hS with h2; injection h2 with hS2 _; exact hS2.symm
  | move p =>
    dsimp [operandStaticTy?] at hStatic
    dsimp [evalOperandToSlot] at hS
    cases hPE : p.projection.isEmpty with
    | false => rw [hPE] at hStatic; cases hStatic
    | true =>
      rw [hPE] at hStatic hS; dsimp at hStatic hS
      rw [hStatic] at hS
      cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
      | none => rw [hSl] at hS; cases hS
      | some sl =>
        rw [hSl] at hS
        cases sl with
        | dead => cases hS
        | live _ =>
          dsimp at hS
          cases hSet : setElem? locals p.localId (liveUninitSlot ty) with
          | none => rw [hSet] at hS; cases hS
          | some _ =>
            rw [hSet] at hS; injection hS with h2
            injection h2 with hS2 _; exact hS2.symm

private theorem operandStaticTy?_evalPrim_wt {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {opnd : Operand} {ty : MirTy} {dv : Val}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hStatic : operandStaticTy? bodyLocals opnd = some ty)
    (hEv : evalPrimitiveOperand bodyLocals locals opnd = .ok (dv, locals')) :
    checkVal dv ty = true := by
  dsimp [evalPrimitiveOperand] at hEv
  cases hS : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [hS] at hEv; cases hEv
  | ok res =>
    let ⟨srcTy, optVal, locs1⟩ := res
    rw [hS] at hEv; dsimp at hEv
    cases hP : isPrimitiveReadableTy srcTy with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases optVal with
      | none => cases hEv
      | some v0 =>
        injection hEv with h1; injection h1 with hv _; subst hv
        have hChkSrc := (evalOperandToSlot_preserves_wt hWt hS).2 v0 rfl
        have hTyEq := operandStaticTy?_evalSlot_eq hStatic hS
        rw [← hTyEq]; exact hChkSrc

private theorem simplifySwitchTerminator_eval_eq {bSrc bTgt : Body}
    {bbSrc : BasicBlock} {exitEnv : List AbsSlot}
    {frame : FrameState} {cm : CallerMemory}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEnv : AbsEnvSound bSrc.locals exitEnv frame.locals) :
    evalTerminator bSrc bbSrc frame cm =
      evalTerminator bTgt
        { bbSrc with terminator := simplifySwitchTerminator bSrc.locals exitEnv bbSrc.terminator }
        frame cm := by
  cases hTm : bbSrc.terminator with
  | goto _ | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    unfold evalTerminator; dsimp; rw [hTm]; rfl
  | return_ =>
    unfold evalTerminator; dsimp; rw [hTm]; rfl
  | switchInt discr targets =>
    let targets' : SwitchTargets :=
      match operandStaticTy? bSrc.locals discr with
      | some ty =>
        if isPrimitiveReadableTy ty &&
            validSwitchBranchesForTy ty targets.branches then
          { branches := pruneOtherwiseBranches targets.otherwise targets.branches
            otherwise := targets.otherwise }
        else targets
      | none => targets
    have hPruneEq :
        evalTerminator bSrc { bbSrc with terminator := .switchInt discr targets } frame cm =
          evalTerminator bSrc { bbSrc with terminator := .switchInt discr targets' } frame cm := by
      dsimp only [targets']
      cases hOpTy : operandStaticTy? bSrc.locals discr with
      | none => rfl
      | some ty =>
        dsimp only
        cases hCond : (isPrimitiveReadableTy ty && validSwitchBranchesForTy ty targets.branches) with
        | false => rw [if_bool_false rfl]
        | true =>
          rw [if_bool_true rfl]
          let ⟨hPrim, hValBr⟩ := bool_and_true hCond
          unfold evalTerminator; dsimp
          cases hEvD : evalPrimitiveOperand bSrc.locals frame.locals discr with
          | error _ => rfl
          | ok res =>
            let ⟨dv, locsAfter⟩ := res
            dsimp
            have hChk := operandStaticTy?_evalPrim_wt hEnv.1 hOpTy hEvD
            cases isPrimitiveReadableTy_elim hPrim with
            | inl hB =>
              subst hB
              let ⟨bv, hbv⟩ := checkVal_bool_iff.mp hChk
              subst hbv; dsimp
              rw [evalBoolSwitchBranches_pruneOtherwise bv targets.otherwise targets.branches hValBr]
            | inr hI =>
              let ⟨w, s, hIS⟩ := hI
              subst hIS
              let ⟨bits, hsc, _⟩ := checkVal_int_iff.mp hChk
              subst hsc; dsimp
              rw [evalSwitchBranches_pruneOtherwise bits targets.otherwise targets.branches hValBr]
    have hSrcEq : evalTerminator bSrc bbSrc frame cm =
        evalTerminator bSrc { bbSrc with terminator := .switchInt discr targets } frame cm := by
      unfold evalTerminator; dsimp; rw [hTm]
    rw [hSrcEq, hPruneEq]
    dsimp only [simplifySwitchTerminator]
    change evalTerminator bSrc { bbSrc with terminator := .switchInt discr targets' } frame cm =
      evalTerminator bTgt {
        bbSrc with
        terminator :=
          if allSwitchTargetsEq targets' targets'.otherwise &&
              canCollapseUniformSwitch bSrc.locals exitEnv discr targets' then
            .goto targets'.otherwise
          else
            .switchInt discr targets'
      } frame cm
    cases hCol : (allSwitchTargetsEq targets' targets'.otherwise &&
        canCollapseUniformSwitch bSrc.locals exitEnv discr targets') with
    | false =>
      rw [if_bool_false rfl]
      unfold evalTerminator; dsimp; rw [← hLocEq]
    | true =>
      rw [if_bool_true rfl]
      let ⟨hAllEq, hCan⟩ := bool_and_true hCol
      unfold allSwitchTargetsEq at hAllEq
      let ⟨hOwEq, hBsEq⟩ := bool_and_true hAllEq
      unfold evalTerminator; dsimp
      cases discr with
      | move _ => cases hCan
      | constant c =>
        dsimp [canCollapseUniformSwitch] at hCan
        cases hRes : resolveConstSwitchTarget c targets' with
        | none => rw [hRes] at hCan; cases hCan
        | some resTgt =>
          unfold resolveConstSwitchTarget at hRes
          cases hPrimC : isPrimitiveReadableTy c.ty with
          | false => rw [hPrimC] at hRes; cases hRes
          | true =>
            rw [hPrimC] at hRes; dsimp at hRes
            dsimp [evalPrimitiveOperand, evalOperandToSlot]
            cases hCL : evalConstLit c.ty c.lit with
            | error _ => rw [hCL] at hRes; cases hRes
            | ok dv =>
              rw [hCL] at hRes; dsimp
              rw [hPrimC]; dsimp
              cases dv with
              | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hRes
              | scalar sv =>
                dsimp at hRes; dsimp
                cases hSw : evalSwitchBranches sv.width sv.bits targets'.otherwise targets'.branches with
                | error _ => rw [hSw] at hRes; cases hRes
                | ok tgt =>
                  have hTgtEq := nat_beq_eq (evalSwitchBranches_target_ok
                    (P := fun b => Nat.beq b targets'.otherwise) hOwEq hBsEq hSw)
                  subst hTgtEq; rfl
              | bool bv =>
                dsimp at hRes; dsimp
                cases hSw : evalBoolSwitchBranches bv targets'.otherwise targets'.branches with
                | error _ => rw [hSw] at hRes; cases hRes
                | ok tgt =>
                  have hTgtEq := nat_beq_eq (evalBoolSwitchBranches_target_ok
                    (P := fun b => Nat.beq b targets'.otherwise) hOwEq hBsEq hSw)
                  subst hTgtEq; rfl
      | copy p =>
        dsimp [canCollapseUniformSwitch] at hCan
        cases hPE : p.projection.isEmpty with
        | false => rw [hPE] at hCan; cases hCan
        | true =>
          rw [hPE] at hCan
          cases hTy : Trusted.MirSemantics.getElem? bSrc.locals p.localId with
          | none => rw [hTy] at hCan; cases hCan
          | some ty =>
            rw [hTy] at hCan
            cases hAbs : Trusted.MirSemantics.getElem? exitEnv p.localId with
            | none => rw [hAbs] at hCan; cases hCan
            | some abs =>
              rw [hAbs] at hCan
              cases abs with
              | liveUninit | dead => cases hCan
              | liveInit =>
                dsimp at hCan
                let ⟨hPrim, hValBr⟩ := bool_and_true (bool_and_true hCan).2
                let ⟨sl, hSl⟩ := getElem?_some_of_lt frame.locals p.localId
                  (by rw [hEnv.1.1]; exact getElem?_some_lt hTy)
                let ⟨hWtSl, v, hvSl⟩ := hEnv.2.2 p.localId ty .liveInit sl hTy hAbs hSl
                subst hvSl
                have hChk : checkVal v ty = true := hWtSl
                dsimp [evalPrimitiveOperand, evalOperandToSlot]
                rw [hPE, hTy, hSl]; dsimp; rw [hPrim]; dsimp
                cases isPrimitiveReadableTy_elim hPrim with
                | inl hB =>
                  subst hB
                  let ⟨bv, hbv⟩ := checkVal_bool_iff.mp hChk
                  subst hbv; dsimp
                  let ⟨tgt, hSw⟩ := evalBoolSwitchBranches_valid_total
                    (b := bv) (ow := targets'.otherwise) targets'.branches hValBr
                  rw [hSw]; dsimp [jumpToBlock]
                  have hTgtEq := nat_beq_eq (evalBoolSwitchBranches_target_ok
                    (P := fun b => Nat.beq b targets'.otherwise) hOwEq hBsEq hSw)
                  subst hTgtEq; rfl
                | inr hI =>
                  let ⟨w, s, hIS⟩ := hI
                  subst hIS
                  let ⟨bits, hsc, _⟩ := checkVal_int_iff.mp hChk
                  subst hsc; dsimp
                  let ⟨tgt, hSw⟩ := evalSwitchBranches_valid_total
                    (w := w) (bits := bits) (ow := targets'.otherwise)
                    targets'.branches hValBr
                  rw [hSw]; dsimp [jumpToBlock]
                  have hTgtEq := nat_beq_eq (evalSwitchBranches_target_ok
                    (P := fun b => Nat.beq b targets'.otherwise) hOwEq hBsEq hSw)
                  subst hTgtEq; rfl

private theorem applySimplifyCfgBranchBlocks_props {b : Body} {cert : BodyAbsCert} :
    ∀ {base : Nat} {bbs bbs' : List BasicBlock},
      applySimplifyCfgBranchBlocks b cert base bbs = some bbs' →
      bbs.length = bbs'.length ∧
      (∀ i bb₁ bb₂,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? bbs' i = some bb₂ →
        bb₁.statements = bb₂.statements ∧ bb₁.cleanup = bb₂.cleanup) ∧
      (∀ i bb₁ entryEnv,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? cert (base + i) = some (some entryEnv) →
        ∃ bb₂ exitEnv,
          Trusted.MirSemantics.getElem? bbs' i = some bb₂ ∧
          entryEnv.length = b.locals.length ∧
          stepPlainStmtsAbs b.locals entryEnv bb₁.statements = some exitEnv ∧
          checkAbsTerminatorEdges b.locals b.basicBlocks.length cert exitEnv
            bb₁.terminator = true ∧
          bb₂ = { bb₁ with terminator := simplifySwitchTerminator b.locals exitEnv bb₁.terminator })
  | _, [], bbs', h => by
    injection h with e; subst e
    exact ⟨rfl, (fun _ _ _ hG _ => by cases hG), (fun _ _ _ hG _ => by cases hG)⟩
  | base, bb :: rest, bbs', h => by
    dsimp [applySimplifyCfgBranchBlocks] at h
    cases hC : Trusted.MirSemantics.getElem? cert base with
    | none => rw [hC] at h; cases h
    | some optE =>
      rw [hC] at h
      cases optE with
      | none =>
        dsimp at h
        cases hRec : applySimplifyCfgBranchBlocks b cert (base + 1) rest with
        | none => rw [hRec] at h; cases h
        | some rest' =>
          rw [hRec] at h; injection h with e; subst e
          let ⟨hLen, hStCl, hActive⟩ := applySimplifyCfgBranchBlocks_props hRec
          refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
          · intro i bb₁ bb₂ h1 h2
            cases i with
            | zero =>
              injection h1 with e1; injection h2 with e2; subst e1; subst e2
              exact ⟨rfl, rfl⟩
            | succ k => exact hStCl k bb₁ bb₂ h1 h2
          · intro i bb₁ entryEnv h1 hCE
            cases i with
            | zero =>
              rw [Nat.add_zero, hC] at hCE; cases hCE
            | succ k =>
              have hAdd : (base + 1) + k = base + (k + 1) := by
                rw [Nat.add_assoc, Nat.add_comm 1 k]
              rw [← hAdd] at hCE
              exact hActive k bb₁ entryEnv h1 hCE
      | some entryEnv =>
        dsimp at h
        cases hELen : Nat.beq entryEnv.length b.locals.length with
        | false => rw [hELen] at h; cases h
        | true =>
          rw [hELen] at h; dsimp at h
          cases hStp : stepPlainStmtsAbs b.locals entryEnv bb.statements with
          | none => rw [hStp] at h; cases h
          | some exitEnv =>
            rw [hStp] at h; dsimp at h
            cases hEdg : checkAbsTerminatorEdges b.locals b.basicBlocks.length cert exitEnv bb.terminator with
            | false => rw [hEdg] at h; cases h
            | true =>
              rw [hEdg] at h; dsimp at h
              cases hRec : applySimplifyCfgBranchBlocks b cert (base + 1) rest with
              | none => rw [hRec] at h; cases h
              | some rest' =>
                rw [hRec] at h; injection h with e; subst e
                let ⟨hLen, hStCl, hActive⟩ := applySimplifyCfgBranchBlocks_props hRec
                refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
                · intro i bb₁ bb₂ h1 h2
                  cases i with
                  | zero =>
                    injection h1 with e1; injection h2 with e2; subst e1; subst e2
                    exact ⟨rfl, rfl⟩
                  | succ k => exact hStCl k bb₁ bb₂ h1 h2
                · intro i bb₁ eEnv h1 hCE
                  cases i with
                  | zero =>
                    injection h1 with e1; subst e1
                    rw [Nat.add_zero, hC] at hCE; injection hCE with eE
                    injection eE with eE'; subst eE'
                    exact ⟨_, exitEnv, rfl, nat_beq_eq hELen, hStp, hEdg, rfl⟩
                  | succ k =>
                    have hAdd : (base + 1) + k = base + (k + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 k]
                    rw [← hAdd] at hCE
                    exact hActive k bb₁ eEnv h1 hCE

private theorem applySimplifyCfgBranchBody_props {cert : BodyAbsCert}
    {bSrc bTgt : Body}
    (hApply : applySimplifyCfgBranchBody cert bSrc = some bTgt) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) ∧
    (bSrc.basicBlocks.isEmpty = false →
      ∃ env₀, Trusted.MirSemantics.getElem? cert 0 = some (some env₀) ∧
        absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
    applySimplifyCfgBranchBlocks bSrc cert 0 bSrc.basicBlocks =
      some bTgt.basicBlocks := by
  unfold applySimplifyCfgBranchBody at hApply
  cases hCLen : Nat.beq cert.length bSrc.basicBlocks.length with
  | false => rw [hCLen] at hApply; cases hApply
  | true =>
    rw [hCLen] at hApply; dsimp at hApply
    have hProceed :
        ((bSrc.basicBlocks.isEmpty = false →
          ∃ env₀, Trusted.MirSemantics.getElem? cert 0 = some (some env₀) ∧
            absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
         ∃ bbs', applySimplifyCfgBranchBlocks bSrc cert 0 bSrc.basicBlocks = some bbs' ∧
           bTgt = { bSrc with basicBlocks := bbs' }) := by
      cases hEmp : bSrc.basicBlocks.isEmpty with
      | true =>
        rw [hEmp] at hApply; dsimp at hApply
        cases hBlk : applySimplifyCfgBranchBlocks bSrc cert 0 bSrc.basicBlocks with
        | none => rw [hBlk] at hApply; cases hApply
        | some bbs' =>
          rw [hBlk] at hApply; injection hApply with eB
          exact ⟨(fun hF => by cases hF), bbs', rfl, eB.symm⟩
      | false =>
        rw [hEmp] at hApply
        cases hC0 : Trusted.MirSemantics.getElem? cert 0 with
        | none => rw [hC0] at hApply; cases hApply
        | some opt0 =>
          rw [hC0] at hApply
          cases opt0 with
          | none => cases hApply
          | some env₀ =>
            cases hImp : absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ with
            | false =>
              have hCT : (!false && !(match (some (some env₀) : Option (Option (List AbsSlot))) with
                  | some (some e) => absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = true := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_true hCT] at hApply; cases hApply
            | true =>
              have hCF : (!false && !(match (some (some env₀) : Option (Option (List AbsSlot))) with
                  | some (some e) => absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = false := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_false hCF] at hApply
              cases hBlk : applySimplifyCfgBranchBlocks bSrc cert 0 bSrc.basicBlocks with
              | none => rw [hBlk] at hApply; cases hApply
              | some bbs' =>
                rw [hBlk] at hApply; injection hApply with eB
                exact ⟨fun _ => ⟨env₀, rfl, hImp⟩, bbs', rfl, eB.symm⟩
    let ⟨hCert0Fn, bbs', hBlk, eB⟩ := hProceed
    subst eB
    let ⟨hBBLen, hStCl, _⟩ := applySimplifyCfgBranchBlocks_props hBlk
    have hBBEmpty := list_isEmpty_eq_of_length hBBLen
    have hHdr : bodyHeaderEq bSrc { bSrc with basicBlocks := bbs' } = true :=
      bodyHeaderEq_refl bSrc
    have hMarker : ∀ idx,
        hasStorageAnnotation bSrc idx =
          hasStorageAnnotation { bSrc with basicBlocks := bbs' } idx := by
      intro idx
      unfold hasStorageAnnotation; dsimp only
      exact list_any_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 => by
        rw [(hStCl i bb₁ bb₂ h1 h2).1])
    have hBounds :
        storageAnnotationsInBounds bSrc =
          storageAnnotationsInBounds { bSrc with basicBlocks := bbs' } := by
      unfold storageAnnotationsInBounds; dsimp only
      exact list_all_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 => by
        rw [(hStCl i bb₁ bb₂ h1 h2).1])
    exact ⟨hHdr, hBBLen, hBBEmpty, hBounds,
      fun args => initLocalsLoop_eq_of_storage_eq args rfl rfl (fun idx _ _ => hMarker idx),
      hCert0Fn, hBlk⟩

private noncomputable def SimplifyCfgInv (cert : ProgramAbsCert)
    (pSrc pTgt : Program) (s : State) : Prop :=
  ∃ f bCert bSrc bTgt,
    s.frames = [f] ∧
    Trusted.MirSemantics.getElem? cert f.defId = some bCert ∧
    Trusted.MirSemantics.getElem? pSrc.bodies f.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies f.defId = some bTgt ∧
    applySimplifyCfgBranchBody bCert bSrc = some bTgt ∧
    (f.blockIdx < bSrc.basicBlocks.length →
      ∃ bbSrc entryEnv curEnv exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks f.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bCert f.blockIdx = some (some entryEnv) ∧
        stepPlainStmtsAbs bSrc.locals entryEnv bbSrc.statements = some exitEnv ∧
        f.stmtIdx ≤ bbSrc.statements.length ∧
        AbsEnvSound bSrc.locals curEnv f.locals ∧
        stepPlainStmtsAbs bSrc.locals curEnv (bbSrc.statements.drop f.stmtIdx) =
          some exitEnv)

private theorem simplifyCfgBranch_init_eq {cert : ProgramAbsCert}
    {pSrc pTgt : Program} (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applySimplifyCfgBranchBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    initState pSrc q = initState pTgt q := by
  let ⟨_, _, hEntEq, _⟩ := programHeaderEq_elim hHdr
  have hBBLen : pSrc.bodies.length = pTgt.bodies.length :=
    (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
  refine initState_eq_of_matching_entry q hHdr ?_ ?_
  · rw [← hEntEq]
    exact ⟨fun hN => getElem?_none_of_ge
              (by rw [← hBBLen]; exact getElem?_none_ge hN),
           fun hN => getElem?_none_of_ge
              (by rw [hBBLen]; exact getElem?_none_ge hN)⟩
  · intro bSrc hBS
    let ⟨bCert, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    rw [hEntEq] at hBT
    let ⟨hBHdr, _, hEmp, hBnd, hInitL, _, _⟩ := applySimplifyCfgBranchBody_props hAp
    exact ⟨bTgt, hBT, hBHdr, hEmp, hBnd, hInitL q.args⟩

private theorem simplifyCfgBranch_query_iff {cert : ProgramAbsCert}
    {pSrc pTgt : Program} (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applySimplifyCfgBranchBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := simplifyCfgBranch_init_eq q hLenC hHdr hMap
  apply lockstep_inv_query_iff (Inv := SimplifyCfgInv cert pSrc pTgt) hInitEq
  · intro s₀ hIS
    let ⟨_, _, bSrc, hBS, hNotEmp, _, _, _, hArgs, hS0⟩ := initState_ok_elim hIS
    let ⟨bCert, bTgt, hBC, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    let ⟨_, _, _, _, _, hCert0Fn, hBlks⟩ := applySimplifyCfgBranchBody_props hAp
    let ⟨env₀, hC0, hImp0⟩ := hCert0Fn hNotEmp
    subst hS0
    refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, ?_⟩
    intro h0Lt
    let ⟨bb0, hBB0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
    let ⟨_, _, hAct⟩ := applySimplifyCfgBranchBlocks_props hBlks
    let ⟨_, exitEnv, _, _, hStp0, _, _⟩ := hAct 0 bb0 env₀ hBB0 hC0
    have hEnvInit : AbsEnvSound bSrc.locals env₀ (initLocalsLoop bSrc q.args 0 bSrc.locals) :=
      absEnvImplies_sound hImp0 (initAbsEnvLoop_sound hArgs)
    exact ⟨bb0, env₀, env₀, exitEnv, hBB0, hC0, hStp0, Nat.zero_le _, hEnvInit, hStp0⟩
  · intro s hInv
    let ⟨f, bCert, bSrc, bTgt, hFs, hBC, hBS, hBT, hAp, hBlkInv⟩ := hInv
    let ⟨hBHdr, hBBLen, _, _, _, _, hBlks⟩ := applySimplifyCfgBranchBody_props hAp
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    let ⟨_, _, hAct⟩ := applySimplifyCfgBranchBlocks_props hBlks
    cases Nat.lt_or_ge f.blockIdx bSrc.basicBlocks.length with
    | inr hGe =>
      have hNoneS := getElem?_none_of_ge hGe
      have hNoneT : Trusted.MirSemantics.getElem? bTgt.basicBlocks f.blockIdx = none :=
        getElem?_none_of_ge (by rw [← hBBLen]; exact hGe)
      have hEvS : evalStep pSrc 0 s = .fault .unsupported := by
        unfold evalStep; rw [hFs]; dsimp; rw [hBS]; dsimp; rw [hNoneS]
      have hEvT : evalStep pTgt 0 s = .fault .unsupported := by
        unfold evalStep; rw [hFs]; dsimp; rw [hBT]; dsimp; rw [hNoneT]
      exact ⟨by rw [hEvS, hEvT], fun _ hSt => by rw [hEvS] at hSt; cases hSt⟩
    | inl hLt =>
      let ⟨bbSrc, entryEnv, curEnv, exitEnv, hBBS, hCE, hEntryStp, hIdxLe, hCurSound, hDropStp⟩ :=
        hBlkInv hLt
      have hCE0 : Trusted.MirSemantics.getElem? bCert (0 + f.blockIdx) = some (some entryEnv) := by
        rw [Nat.zero_add]; exact hCE
      let ⟨bbTgt, exitEnv', hBBT, _, hFullStp, hEdges, hBBTEq⟩ :=
        hAct f.blockIdx bbSrc entryEnv hBBS hCE0
      rw [hEntryStp] at hFullStp; injection hFullStp with eEx; subst eEx
      cases hSt : Trusted.MirSemantics.getElem? bbSrc.statements f.stmtIdx with
      | some stmt =>
        have hStT : Trusted.MirSemantics.getElem? bbTgt.statements f.stmtIdx = some stmt := by
          rw [hBBTEq]; exact hSt
        have hEvEq : evalStep pSrc 0 s = evalStep pTgt 0 s := by
          unfold evalStep; rw [hFs]; dsimp
          rw [hBS, hBT]; dsimp; rw [hBBS, hBBT]; dsimp; rw [hSt, hStT]
          cases stmt <;> first | rfl | (unfold evalStatement; dsimp; rw [hLocEq])
        refine ⟨hEvEq, fun s' hEvS => ?_⟩
        unfold evalStep at hEvS; rw [hFs] at hEvS; dsimp at hEvS
        rw [hBS] at hEvS; dsimp at hEvS; rw [hBBS] at hEvS; dsimp at hEvS
        rw [hSt] at hEvS
        have hDropCons := drop_eq_cons_of_getElem? hSt
        rw [hDropCons] at hDropStp
        let ⟨nextEnv, hStep1, hDropNext⟩ := stepPlainStmtsAbs_cons_elim hDropStp
        let ⟨locs', hs', hNextSound⟩ := stepPlainStmtAbs_sound hCurSound hStep1 hEvS
        subst hs'
        refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, ?_⟩
        intro _
        exact ⟨bbSrc, entryEnv, nextEnv, exitEnv, hBBS, hCE, hEntryStp,
          Nat.succ_le_of_lt (getElem?_some_lt hSt), hNextSound, hDropNext⟩
      | none =>
        have hGeLen := getElem?_none_ge hSt
        have hIdxEq : f.stmtIdx = bbSrc.statements.length :=
          Nat.le_antisymm hIdxLe hGeLen
        have hEndB : Nat.beq f.stmtIdx bbSrc.statements.length = true := by
          rw [hIdxEq]; exact nat_beq_refl _
        have hStT : Trusted.MirSemantics.getElem? bbTgt.statements f.stmtIdx = none := by
          rw [hBBTEq]; exact hSt
        have hEndBT : Nat.beq f.stmtIdx bbTgt.statements.length = true := by
          rw [hBBTEq]; exact hEndB
        have hDropNil : bbSrc.statements.drop f.stmtIdx = [] :=
          drop_eq_nil_of_ge hGeLen
        rw [hDropNil] at hDropStp
        dsimp [stepPlainStmtsAbs] at hDropStp
        injection hDropStp with eEx; subst eEx
        have hEvSEq : evalStep pSrc 0 s = evalTerminator bSrc bbSrc f s.callerMem := by
          unfold evalStep; rw [hFs]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
          rw [hSt, if_bool_true hEndB]
        have hEvTEq : evalStep pTgt 0 s = evalTerminator bTgt bbTgt f s.callerMem := by
          unfold evalStep; rw [hFs]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
          rw [hStT, if_bool_true hEndBT]
        have hTmEq : evalStep pSrc 0 s = evalStep pTgt 0 s := by
          rw [hEvSEq, hEvTEq, hBBTEq]
          exact simplifySwitchTerminator_eval_eq hLocEq hCurSound
        refine ⟨hTmEq, fun s' hEvS => ?_⟩
        rw [hEvSEq] at hEvS
        let ⟨tgt, locs', hs', _, hEdgeNext⟩ :=
          checkAbsTerminatorEdges_step_sound hCurSound hEdges hEvS
        subst hs'
        refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, ?_⟩
        intro hTgtLt
        let ⟨tgtEnv, hCTgt, hTgtSound⟩ := hEdgeNext hTgtLt
        let ⟨bbNext, hBBNext⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt hTgtLt
        have hCTgt0 : Trusted.MirSemantics.getElem? bCert (0 + tgt) = some (some tgtEnv) := by
          rw [Nat.zero_add]; exact hCTgt
        let ⟨_, nextExitEnv, _, _, hNextStp, _, _⟩ :=
          hAct tgt bbNext tgtEnv hBBNext hCTgt0
        exact ⟨bbNext, tgtEnv, tgtEnv, nextExitEnv, hBBNext, hCTgt, hNextStp,
          Nat.zero_le _, hTgtSound, hNextStp⟩

private theorem applySimplifyCfgBranchProgram_equiv {cert : ProgramAbsCert}
    {pSrc pTgt : Program}
    (hApply : applySimplifyCfgBranchProgram cert pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  unfold applySimplifyCfgBranchProgram at hApply
  cases hLenB : Nat.beq cert.length pSrc.bodies.length with
  | false => rw [hLenB] at hApply; cases hApply
  | true =>
    rw [hLenB] at hApply; dsimp at hApply
    have hLenC := nat_beq_eq hLenB
    cases hMap : mapOption (fun pr => applySimplifyCfgBranchBody pr.1 pr.2)
        (List.zip cert pSrc.bodies) with
    | none => rw [hMap] at hApply; cases hApply
    | some bodies' =>
      rw [hMap] at hApply; injection hApply with eP; subst eP
      have hHdr := programHeaderEq_with_bodies pSrc bodies'
      have hBodyLen : pSrc.bodies.length = bodies'.length :=
        (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
      have hIds : pSrc.bodies.map Body.identity = bodies'.map Body.identity := by
        apply list_eq_of_getElem?_eq
        · rw [map_length_eq, map_length_eq, hBodyLen]
        · intro i
          rw [getElem?_map, getElem?_map]
          cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies i with
          | none =>
            have hGe : bodies'.length ≤ i := by
              rw [← hBodyLen]; exact getElem?_none_ge hBS
            rw [getElem?_none_of_ge hGe]
          | some bSrc =>
            let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
            let ⟨hBHdr, _, _, _, _, _, _⟩ := applySimplifyCfgBranchBody_props hAp
            let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim hBHdr
            rw [hBT]; dsimp [Option.map]; rw [hIdEq]
      refine ⟨?_, hHdr, hIds⟩
      refine fullSemanticEquiv_of_query_iff hHdr ?_ ?_ ?_
      · intro defId bSrc bTgt hBS hBT
        let ⟨_, bTgt', _, hBT', hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
        dsimp at hBT; rw [hBT] at hBT'; injection hBT' with eB; subst eB
        let ⟨hBHdr, _, hEmp, hBnd, _, _, _⟩ := applySimplifyCfgBranchBody_props hAp
        exact ⟨hBHdr, hEmp, hBnd⟩
      · intro q
        exact simplifyCfgBranch_query_iff q hLenC hHdr hMap
      · intro defId args
        exact (simplifyCfgBranch_query_iff
          (pSrc := entryProgForBody pSrc defId)
          (pTgt := entryProgForBody { pSrc with bodies := bodies' } defId)
          { args := args } hLenC
          (programHeaderEq_entryProg defId hHdr) hMap).1

/-! ### Pass Family 3: `.instSimplifyAlgAndConst` (`F1-6` + `F1-8`) -/

/-! #### Part 3A: Scalar & Boolean Neutral Algebra -/

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_mod_lt (a : Nat) {b : Nat} (h : 0 < b) : Nat.mod a b < b :=
  Nat.mod_lt a h

private theorem nat_div_add_mod (a b : Nat) : b * Nat.div a b + Nat.mod a b = a :=
  Nat.div_add_mod a b

private theorem nat_mul_add_mod (a b c : Nat) : Nat.mod (a * b + c) a = Nat.mod c a := by
  rw [Nat.add_comm (a * b) c]
  exact Nat.add_mul_mod_self_left c a b

private theorem bv_isLt {n : Nat} (x : BitVec n) : x.toNat < Nat.pow 2 n := x.isLt

private theorem intEmod_ofNat (m p : Nat) :
    intEmod (Int.ofNat m) (Int.ofNat p) = Int.ofNat (Nat.mod m p) := rfl

private theorem intEmod_negSucc (m p : Nat) :
    intEmod (Int.negSucc m) (Int.ofNat p) =
      Int.subNatNat p (Nat.succ (Nat.mod m p)) := rfl

private theorem nat_two_mul (n : Nat) : 2 * n = n + n := by
  have h1 : 2 * n = 1 * n + n := Nat.succ_mul 1 n
  rw [h1, Nat.one_mul]

private theorem nat_lt_of_two_mul_lt {a b : Nat} (h : 2 * a < 2 * b) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hLt => exact hLt
  | inr hGe =>
    exact False.elim (Nat.not_le_of_gt h (Nat.mul_le_mul_left 2 hGe))

private theorem nat_le_of_two_mul_le {a b : Nat} (h : 2 * a ≤ 2 * b) : a ≤ b := by
  cases Nat.lt_or_ge b a with
  | inr hLe => exact hLe
  | inl hLt =>
    have hLt2 : 2 * b < 2 * a := by
      rw [nat_two_mul b, nat_two_mul a]
      exact Nat.add_lt_add hLt hLt
    exact False.elim (Nat.not_lt_of_ge h hLt2)

private theorem nat_sub_sub_self {m n : Nat} (h : n ≤ m) : m - (m - n) = n := by
  have hAdd : n + (m - n) = m := Nat.add_sub_of_le h
  have hSub : (n + (m - n)) - (m - n) = n := Nat.add_sub_cancel n (m - n)
  rw [hAdd] at hSub
  exact hSub

private theorem nat_sub_pos_eq_succ {m n : Nat} (hLt : n < m) :
    m - n = Nat.succ (m - 1 - n) := by
  cases m with
  | zero => exact False.elim (Nat.not_lt_zero n hLt)
  | succ k =>
    have hLe : n ≤ k := Nat.le_of_succ_le_succ hLt
    have h1 : Nat.succ k - 1 = k := rfl
    rw [h1]
    exact Nat.succ_sub hLe

private theorem nat_sub_lt_of_pos_le {m k : Nat} (hPos : 0 < k) (hLe : k ≤ m) :
    m - k < m :=
  Nat.sub_lt (Nat.lt_of_lt_of_le hPos hLe) hPos

private theorem nat_mod_mul_mod (n m k : Nat) :
    Nat.mod (Nat.mod n (m * k)) m = Nat.mod n m := by
  have hDivMod := nat_div_add_mod n (m * k)
  have hAssoc : (m * k) * Nat.div n (m * k) = m * (k * Nat.div n (m * k)) :=
    Nat.mul_assoc m k (Nat.div n (m * k))
  rw [hAssoc] at hDivMod
  have hMod := congrArg (fun z => Nat.mod z m) hDivMod
  rw [nat_mul_add_mod] at hMod
  exact hMod

private theorem int_ofNat_sub_eq_subNatNat (a b : Nat) (hPos : 0 < b) :
    Int.ofNat a - Int.ofNat b = Int.subNatNat a b := by
  cases b with
  | zero => exact False.elim (Nat.not_lt_zero 0 hPos)
  | succ _ => rfl

private theorem int_subNatNat_of_le {a b : Nat} (hLe : b ≤ a) :
    Int.subNatNat a b = Int.ofNat (a - b) := by
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le hLe]

private theorem int_subNatNat_of_lt {a b : Nat} (hLt : a < b) :
    Int.subNatNat a b = Int.negSucc (b - 1 - a) := by
  unfold Int.subNatNat
  rw [nat_sub_pos_eq_succ hLt]

private theorem int_beq_refl (x : Int) : (x == x) = true :=
  decide_eq_true rfl

private theorem int_zero_add (x : Int) : 0 + x = x := by
  cases x with
  | ofNat n =>
    change Int.ofNat (0 + n) = Int.ofNat n
    rw [Nat.zero_add]
  | negSucc _ => rfl

private theorem int_add_zero (x : Int) : x + 0 = x := by
  cases x <;> rfl

private theorem int_sub_zero (x : Int) : x - 0 = x := by
  cases x <;> rfl

private theorem int_one_mul (x : Int) : 1 * x = x := by
  cases x with
  | ofNat n =>
    change Int.ofNat (1 * n) = Int.ofNat n
    rw [Nat.one_mul]
  | negSucc n =>
    change Int.negOfNat (1 * Nat.succ n) = Int.negSucc n
    rw [Nat.one_mul]; rfl

private theorem int_mul_one (x : Int) : x * 1 = x := by
  cases x with
  | ofNat n =>
    change Int.ofNat (n * 1) = Int.ofNat n
    rw [Nat.mul_one]
  | negSucc n =>
    change Int.negOfNat (Nat.succ n * 1) = Int.negSucc n
    rw [Nat.mul_one]; rfl

private theorem bvToInt_in_i128_range (x : BitVec 128) :
    (decide (bvToInt x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (bvToInt x ≥ HPow.hPow (2 : Int) 127)) = false := by
  unfold bvToInt
  have hXlt : x.toNat < Nat.pow 2 128 := bv_isLt x
  have hPow128 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
  have hInt127 : HPow.hPow (2 : Int) 127 = Int.ofNat (Nat.pow 2 127) := by decide
  have hNeg127 : Neg.neg (Int.ofNat (Nat.pow 2 127)) =
      Int.negSucc (Nat.pow 2 127 - 1) := by decide
  rw [hInt127, hNeg127]
  cases Nat.lt_or_ge (2 * x.toNat) (Nat.pow 2 128) with
  | inl hCmp =>
    rw [ite_prop_true hCmp]
    have hLt2 : 2 * x.toNat < 2 * Nat.pow 2 127 := by rw [← hPow128]; exact hCmp
    have hLt : x.toNat < Nat.pow 2 127 := nat_lt_of_two_mul_lt hLt2
    have hNotNeg : ¬ (Int.ofNat x.toNat < Int.negSucc (Nat.pow 2 127 - 1)) :=
      fun h => nomatch h
    have hNotGe : ¬ (Int.ofNat x.toNat ≥ Int.ofNat (Nat.pow 2 127)) := by
      intro hGeI
      have hPos127 : Nat.pow 2 127 = Nat.succ (Nat.pow 2 127 - 1) := by decide
      rw [hPos127] at hGeI
      change Int.NonNeg (Int.subNatNat x.toNat (Nat.succ (Nat.pow 2 127 - 1))) at hGeI
      rw [← hPos127, int_subNatNat_of_lt hLt] at hGeI
      nomatch hGeI
    rw [decide_eq_false hNotNeg, decide_eq_false hNotGe]; rfl
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
    have hGe2 : 2 * Nat.pow 2 127 ≤ 2 * x.toNat := by rw [← hPow128]; exact hCmp
    have hGe : Nat.pow 2 127 ≤ x.toNat := nat_le_of_two_mul_le hGe2
    have hPos128 : 0 < Nat.pow 2 128 := by decide
    rw [int_ofNat_sub_eq_subNatNat x.toNat (Nat.pow 2 128) hPos128]
    rw [int_subNatNat_of_lt hXlt]
    let k := Nat.pow 2 128 - 1 - x.toNat
    have hDiff : Nat.pow 2 128 - x.toNat = k + 1 := nat_sub_pos_eq_succ hXlt
    have hKLt : k < Nat.pow 2 127 := by
      have hSum : x.toNat + (k + 1) = Nat.pow 2 127 + Nat.pow 2 127 := by
        have hAdd := Nat.add_sub_of_le (Nat.le_of_lt hXlt)
        have hHalfPow : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
        rw [hDiff, hHalfPow] at hAdd; exact hAdd
      have hLeAdd : Nat.pow 2 127 + (k + 1) ≤ Nat.pow 2 127 + Nat.pow 2 127 := by
        rw [← hSum]; exact Nat.add_le_add_right hGe (k + 1)
      exact Nat.le_of_add_le_add_left hLeAdd
    have hNotGe : ¬ (Int.negSucc k ≥ Int.ofNat (Nat.pow 2 127)) := by
      intro hGeI
      have hPos127 : Nat.pow 2 127 = Nat.succ (Nat.pow 2 127 - 1) := by decide
      rw [hPos127] at hGeI; nomatch hGeI
    have hNotLt : ¬ (Int.negSucc k < Int.negSucc (Nat.pow 2 127 - 1)) := by
      intro hLtI
      cases hK : k with
      | zero =>
        rw [hK] at hLtI
        have hZ : Int.negSucc 0 + 1 = Int.ofNat 0 := by decide
        change Int.NonNeg (Int.negSucc (Nat.pow 2 127 - 1) - (Int.negSucc 0 + 1)) at hLtI
        rw [hZ] at hLtI; nomatch hLtI
      | succ k' =>
        rw [hK] at hLtI hKLt
        have hSucc127 : Nat.succ (Nat.pow 2 127 - 1) = Nat.pow 2 127 := by decide
        change Int.NonNeg (Int.subNatNat (Nat.succ k') (Nat.succ (Nat.pow 2 127 - 1))) at hLtI
        rw [hSucc127, int_subNatNat_of_lt hKLt] at hLtI; nomatch hLtI
    rw [decide_eq_false hNotLt, decide_eq_false hNotGe]; rfl

private theorem bvOfInt_bvToInt_128 (x : BitVec 128) :
    bvOfInt 128 (bvToInt x) = x := by
  have hXlt : x.toNat < Nat.pow 2 128 := bv_isLt x
  apply bitvec_eq_of_toNat_eq
  unfold bvToInt bvOfInt
  cases Nat.lt_or_ge (2 * x.toNat) (Nat.pow 2 128) with
  | inl hCmp =>
    rw [ite_prop_true hCmp, intEmod_ofNat]
    change Nat.mod (Nat.mod x.toNat (Nat.pow 2 128)) (Nat.pow 2 128) = x.toNat
    rw [nat_mod_eq_of_lt hXlt, nat_mod_eq_of_lt hXlt]
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
    have hPos128 : 0 < Nat.pow 2 128 := by decide
    rw [int_ofNat_sub_eq_subNatNat x.toNat (Nat.pow 2 128) hPos128]
    rw [int_subNatNat_of_lt hXlt]
    let k := Nat.pow 2 128 - 1 - x.toNat
    have hDiff : Nat.pow 2 128 - x.toNat = k + 1 := nat_sub_pos_eq_succ hXlt
    have hSum : x.toNat + (k + 1) = Nat.pow 2 128 := by
      have hAdd := Nat.add_sub_of_le (Nat.le_of_lt hXlt)
      rw [hDiff] at hAdd; exact hAdd
    have hKLt : k < Nat.pow 2 128 := by
      have h1 : k + 1 ≤ Nat.pow 2 128 := by
        rw [← hSum]; exact Nat.le_add_left (k + 1) x.toNat
      exact Nat.lt_of_succ_le h1
    have hKSuccLe : k + 1 ≤ Nat.pow 2 128 := hKLt
    change (BitVec.ofNat 128 (intEmod (Int.negSucc k) (Int.ofNat (Nat.pow 2 128))).toNat).toNat = x.toNat
    rw [intEmod_negSucc, nat_mod_eq_of_lt hKLt, int_subNatNat_of_le hKSuccLe]
    have hSubK : Nat.pow 2 128 - (k + 1) = x.toNat := by
      rw [← hSum]; exact Nat.add_sub_cancel x.toNat (k + 1)
    rw [hSubK]
    change Nat.mod x.toNat (Nat.pow 2 128) = x.toNat
    exact nat_mod_eq_of_lt hXlt

private theorem bvToInt_bvOfInt_128_ofNat {k : Nat} (hLt : k < Nat.pow 2 127) :
    bvToInt (bvOfInt 128 (Int.ofNat k)) = Int.ofNat k := by
  have hLt128 : k < Nat.pow 2 128 :=
    Nat.lt_trans hLt (by decide : Nat.pow 2 127 < Nat.pow 2 128)
  have hToNat : (bvOfInt 128 (Int.ofNat k)).toNat = k := by
    unfold bvOfInt; rw [intEmod_ofNat]
    change Nat.mod (Nat.mod k (Nat.pow 2 128)) (Nat.pow 2 128) = k
    rw [nat_mod_eq_of_lt hLt128, nat_mod_eq_of_lt hLt128]
  unfold bvToInt; rw [hToNat]
  have hPow128 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
  have h2Lt : 2 * k < Nat.pow 2 128 := by
    rw [hPow128, nat_two_mul k, nat_two_mul (Nat.pow 2 127)]
    exact Nat.add_lt_add hLt hLt
  exact ite_prop_true h2Lt

private theorem bvToInt_bvOfInt_128_negSucc {k : Nat} (hLt : k < Nat.pow 2 127) :
    bvToInt (bvOfInt 128 (Int.negSucc k)) = Int.negSucc k := by
  have hLt128 : k < Nat.pow 2 128 :=
    Nat.lt_trans hLt (by decide : Nat.pow 2 127 < Nat.pow 2 128)
  have hSuccLe127 : k + 1 ≤ Nat.pow 2 127 := hLt
  have hSuccLe128 : k + 1 ≤ Nat.pow 2 128 := hLt128
  have hSubLt128 : Nat.pow 2 128 - (k + 1) < Nat.pow 2 128 :=
    nat_sub_lt_of_pos_le (Nat.zero_lt_succ k) hSuccLe128
  have hToNat : (bvOfInt 128 (Int.negSucc k)).toNat = Nat.pow 2 128 - (k + 1) := by
    unfold bvOfInt
    rw [intEmod_negSucc, nat_mod_eq_of_lt hLt128, int_subNatNat_of_le hSuccLe128]
    change Nat.mod (Nat.pow 2 128 - (k + 1)) (Nat.pow 2 128) = _
    exact nat_mod_eq_of_lt hSubLt128
  unfold bvToInt; rw [hToNat]
  have hGe127 : Nat.pow 2 127 ≤ Nat.pow 2 128 - (k + 1) := by
    have hHalf : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
    have hAddLe : Nat.pow 2 127 + (k + 1) ≤ Nat.pow 2 128 := by
      rw [hHalf]; exact Nat.add_le_add_left hSuccLe127 (Nat.pow 2 127)
    have hSub := Nat.sub_le_sub_right hAddLe (k + 1)
    rw [Nat.add_sub_cancel] at hSub; exact hSub
  have hNot2Lt : ¬ (2 * (Nat.pow 2 128 - (k + 1)) < Nat.pow 2 128) := by
    have hPow128 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
    rw [hPow128]
    exact Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 hGe127)
  rw [ite_prop_false hNot2Lt]
  have hPos128 : 0 < Nat.pow 2 128 := by decide
  rw [int_ofNat_sub_eq_subNatNat _ (Nat.pow 2 128) hPos128]
  rw [int_subNatNat_of_lt hSubLt128]
  have hCancel : Nat.pow 2 128 - 1 - (Nat.pow 2 128 - (k + 1)) = k := by
    have h1 : Nat.pow 2 128 - (Nat.pow 2 128 - (k + 1)) = k + 1 :=
      nat_sub_sub_self hSuccLe128
    have h2 : Nat.succ (Nat.pow 2 128 - 1 - (Nat.pow 2 128 - (k + 1))) = k + 1 := by
      rw [← nat_sub_pos_eq_succ hSubLt128]; exact h1
    exact Nat.succ.inj h2
  rw [hCancel]

private noncomputable def intWidthCofactor : IntWidth → Nat
  | .i8 => Nat.pow 2 120
  | .i16 => Nat.pow 2 112
  | .i32 => Nat.pow 2 96
  | .i64 | .isize => Nat.pow 2 64
  | .i128 => 1

private theorem pow128_eq_mul_cofactor (w : IntWidth) :
    Nat.pow 2 128 = Nat.pow 2 w.bitWidth * intWidthCofactor w := by
  cases w <;> decide

private theorem toNat_truncateBits_bvOfInt (w : IntWidth) (v : Int) :
    (truncateBits w (bvOfInt 128 v)).toNat =
      (intEmod v (Int.ofNat (Nat.pow 2 w.bitWidth))).toNat := by
  let M := Nat.pow 2 w.bitWidth
  let K := intWidthCofactor w
  have hM : 0 < M := pow2_bitWidth_pos w
  have hP128 : 0 < Nat.pow 2 128 := by decide
  have hFac : Nat.pow 2 128 = M * K := pow128_eq_mul_cofactor w
  rw [toNat_truncateBits]
  cases v with
  | ofNat n =>
    unfold bvOfInt; rw [intEmod_ofNat, intEmod_ofNat]
    have hModLt128 : Nat.mod n (Nat.pow 2 128) < Nat.pow 2 128 := nat_mod_lt n hP128
    change Nat.mod (Nat.mod (Nat.mod n (Nat.pow 2 128)) (Nat.pow 2 128)) M = Nat.mod n M
    rw [nat_mod_eq_of_lt hModLt128, hFac]
    exact nat_mod_mul_mod n M K
  | negSucc n =>
    unfold bvOfInt; rw [intEmod_negSucc, intEmod_negSucc]
    have hModP_lt : Nat.mod n (Nat.pow 2 128) < Nat.pow 2 128 := nat_mod_lt n hP128
    have hModM_lt : Nat.mod n M < M := nat_mod_lt n hM
    have hSuccP_le : Nat.succ (Nat.mod n (Nat.pow 2 128)) ≤ Nat.pow 2 128 := hModP_lt
    have hSuccM_le : Nat.succ (Nat.mod n M) ≤ M := hModM_lt
    rw [int_subNatNat_of_le hSuccP_le, int_subNatNat_of_le hSuccM_le]
    have hSubP_lt : Nat.pow 2 128 - Nat.succ (Nat.mod n (Nat.pow 2 128)) < Nat.pow 2 128 :=
      nat_sub_lt_of_pos_le (Nat.zero_lt_succ _) hSuccP_le
    change Nat.mod (Nat.mod (Nat.pow 2 128 - Nat.succ (Nat.mod n (Nat.pow 2 128))) (Nat.pow 2 128)) M =
      M - Nat.succ (Nat.mod n M)
    rw [nat_mod_eq_of_lt hSubP_lt]
    let remP := Nat.mod n (Nat.pow 2 128)
    let q := Nat.div remP M
    let r := Nat.mod remP M
    have hREq : r = Nat.mod n M := by
      dsimp [r, remP]; rw [hFac]; exact nat_mod_mul_mod n M K
    have hDecomp : M * q + r = remP := nat_div_add_mod remP M
    have hQLtK : q < K := by
      cases Nat.lt_or_ge q K with
      | inl hlt => exact hlt
      | inr hge =>
        have h1 : M * K ≤ M * q := Nat.mul_le_mul_left M hge
        have h2 : M * K ≤ M * q + r := Nat.le_trans h1 (Nat.le_add_right (M * q) r)
        rw [hDecomp, ← hFac] at h2
        exact False.elim (Nat.not_lt_of_ge h2 hModP_lt)
    have hKDecomp : K = (K - (q + 1)) + (q + 1) := by
      rw [Nat.add_comm]; exact (Nat.add_sub_of_le hQLtK).symm
    have hRLtM : r < M := by rw [hREq]; exact hModM_lt
    have hRSuccLe : r + 1 ≤ M := hRLtM
    have hRewriteSub :
        Nat.pow 2 128 - Nat.succ remP = M * (K - (q + 1)) + (M - (r + 1)) := by
      have hMSub : (M - (r + 1)) + (r + 1) = M := by
        rw [Nat.add_comm]; exact Nat.add_sub_of_le hRSuccLe
      have hSumEq :
          (M * (K - (q + 1)) + (M - (r + 1))) + (M * q + r + 1) = Nat.pow 2 128 := by
        have s1 : (M * (K - (q + 1)) + (M - (r + 1))) + (M * q + r + 1) =
            M * (K - (q + 1)) + ((M - (r + 1)) + ((r + 1) + M * q)) := by
          rw [Nat.add_assoc (M * q) r 1, Nat.add_comm (M * q) (r + 1),
              Nat.add_assoc, Nat.add_assoc]
        have s2 : M * (K - (q + 1)) + ((M - (r + 1)) + ((r + 1) + M * q)) =
            M * (K - (q + 1)) + (((M - (r + 1)) + (r + 1)) + M * q) := by
          rw [Nat.add_assoc (M - (r + 1)) (r + 1) (M * q)]
        have s3 : M * (K - (q + 1)) + (((M - (r + 1)) + (r + 1)) + M * q) =
            M * (K - (q + 1)) + M * (q + 1) := by
          rw [hMSub, Nat.mul_succ M q, Nat.add_comm (M * q) M]
        have s4 : M * (K - (q + 1)) + M * (q + 1) = Nat.pow 2 128 := by
          rw [← Nat.left_distrib M (K - (q + 1)) (q + 1), ← hKDecomp, ← hFac]
        exact s1.trans (s2.trans (s3.trans s4))
      rw [← hDecomp, ← hSumEq]
      exact Nat.add_sub_cancel _ (M * q + r + 1)
    rw [hRewriteSub, nat_mul_add_mod]
    have hSubMLt : M - (r + 1) < M := nat_sub_lt_of_pos_le (Nat.zero_lt_succ r) hRSuccLe
    rw [nat_mod_eq_of_lt hSubMLt, hREq]

private theorem truncateScalar_eq (w : IntWidth) (s : Bool) (value : Int) :
    ∃ lossy : Bool,
      truncateScalar w s value =
        .ok (⟨w, s, truncateBits w (bvOfInt 128 value)⟩, lossy) ∧
      (s = false → lossy = (truncateBits w (bvOfInt 128 value) != bvOfInt 128 value)) ∧
      (s = true →
        lossy = (signExtendBits w (truncateBits w (bvOfInt 128 value)) !=
          bvToInt (bvOfInt 128 value))) := by
  unfold truncateScalar
  cases s with
  | false => exact ⟨_, rfl, (fun _ => rfl), (fun h => nomatch h)⟩
  | true =>
    dsimp only
    rw [bvToInt_in_i128_range (bvOfInt 128 value)]
    rw [if_bool_false rfl]
    rw [bvOfInt_bvToInt_128 (bvOfInt 128 value)]
    exact ⟨_, rfl, (fun h => nomatch h), (fun _ => rfl)⟩

private theorem signExtendBits_concrete_width {W H : Nat} {low : BitVec W}
    (hPow : Nat.pow 2 W = 2 * H)
    (hHPos : 0 < H)
    (hHLe127 : H ≤ Nat.pow 2 127) :
    bvToInt (bvSignExtend 128 low) =
      if 2 * low.toNat < Nat.pow 2 W then
        Int.ofNat low.toNat
      else
        Int.negSucc (Nat.pow 2 W - 1 - low.toNat) := by
  unfold bvSignExtend
  have hLowLt : low.toNat < Nat.pow 2 W := bv_isLt low
  have hWPos : 0 < Nat.pow 2 W := by
    rw [hPow, nat_two_mul H]
    exact Nat.lt_of_lt_of_le hHPos (Nat.le_add_right H H)
  cases Nat.lt_or_ge (2 * low.toNat) (Nat.pow 2 W) with
  | inl hCmp =>
    rw [ite_prop_true hCmp]
    have hBv : bvToInt low = Int.ofNat low.toNat := by
      unfold bvToInt; exact ite_prop_true hCmp
    rw [hBv]
    have hLtH : low.toNat < H := by
      apply nat_lt_of_two_mul_lt; rw [← hPow]; exact hCmp
    exact bvToInt_bvOfInt_128_ofNat (Nat.lt_of_lt_of_le hLtH hHLe127)
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
    have hGeH : H ≤ low.toNat := by
      apply nat_le_of_two_mul_le; rw [← hPow]; exact hCmp
    have hBv : bvToInt low = Int.negSucc (Nat.pow 2 W - 1 - low.toNat) := by
      unfold bvToInt
      rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
      rw [int_ofNat_sub_eq_subNatNat low.toNat (Nat.pow 2 W) hWPos]
      exact int_subNatNat_of_lt hLowLt
    rw [hBv]
    let k := Nat.pow 2 W - 1 - low.toNat
    have hDiff : Nat.pow 2 W - low.toNat = k + 1 := nat_sub_pos_eq_succ hLowLt
    have hKLtH : k < H := by
      have hSum : low.toNat + (k + 1) = H + H := by
        have hAdd := Nat.add_sub_of_le (Nat.le_of_lt hLowLt)
        rw [hDiff, hPow, nat_two_mul H] at hAdd; exact hAdd
      have hLeAdd : H + (k + 1) ≤ H + H := by
        rw [← hSum]; exact Nat.add_le_add_right hGeH (k + 1)
      exact Nat.le_of_add_le_add_left hLeAdd
    exact bvToInt_bvOfInt_128_negSucc (Nat.lt_of_lt_of_le hKLtH hHLe127)

private theorem signExtendBits_eq {w : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < Nat.pow 2 w.bitWidth) :
    signExtendBits w b =
      if 2 * b.toNat < Nat.pow 2 w.bitWidth then
        Int.ofNat b.toNat
      else
        Int.negSucc (Nat.pow 2 w.bitWidth - 1 - b.toNat) := by
  unfold signExtendBits
  cases w
  · have hLow : (bvExtractLsb 7 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width (H := Nat.pow 2 7) (low := bvExtractLsb 7 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 15 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width (H := Nat.pow 2 15) (low := bvExtractLsb 15 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 31 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width (H := Nat.pow 2 31) (low := bvExtractLsb 31 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 63 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width (H := Nat.pow 2 63) (low := bvExtractLsb 63 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 127 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width (H := Nat.pow 2 127) (low := bvExtractLsb 127 0 b)
      (by decide) (by decide) (Nat.le_refl _)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 63 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width (H := Nat.pow 2 63) (low := bvExtractLsb 63 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq

private theorem decodeScalar_unsigned {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    decodeScalar ⟨w, false, b⟩ = Int.ofNat b.toNat := by
  unfold decodeScalar; dsimp; rw [hWf]

private theorem decodeScalar_signed {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    decodeScalar ⟨w, true, b⟩ = signExtendBits w b := by
  unfold decodeScalar; dsimp; rw [hWf]

private theorem decodeScalar_in_host_range {sv : ScalarVal} :
    (if sv.signed then
       decide (decodeScalar sv < Neg.neg (HPow.hPow (2 : Int) 127)) ||
         decide (decodeScalar sv ≥ HPow.hPow (2 : Int) 127)
     else
       decide (decodeScalar sv < 0) ||
         decide (decodeScalar sv ≥ HPow.hPow (2 : Int) 128)) = false := by
  unfold decodeScalar
  cases sv.signed with
  | true =>
    dsimp; unfold signExtendBits
    exact bvToInt_in_i128_range _
  | false =>
    change (decide (Int.ofNat (truncateBits sv.width sv.bits).toNat < 0) ||
      decide (Int.ofNat (truncateBits sv.width sv.bits).toNat ≥ HPow.hPow (2 : Int) 128)) = false
    have hLt128 : (truncateBits sv.width sv.bits).toNat < Nat.pow 2 128 :=
      bv_isLt (truncateBits sv.width sv.bits)
    have hNotNeg : ¬ (Int.ofNat (truncateBits sv.width sv.bits).toNat < 0) :=
      fun h => nomatch h
    have hInt128 : HPow.hPow (2 : Int) 128 = Int.ofNat (Nat.pow 2 128) := by decide
    have hNotGe : ¬ (Int.ofNat (truncateBits sv.width sv.bits).toNat ≥ HPow.hPow (2 : Int) 128) := by
      intro hGeI
      rw [hInt128] at hGeI
      have hPos128 : Nat.pow 2 128 = Nat.succ (Nat.pow 2 128 - 1) := by decide
      rw [hPos128] at hGeI
      change Int.NonNeg (Int.subNatNat (truncateBits sv.width sv.bits).toNat (Nat.succ (Nat.pow 2 128 - 1))) at hGeI
      rw [← hPos128, int_subNatNat_of_lt hLt128] at hGeI
      nomatch hGeI
    rw [decide_eq_false hNotNeg, decide_eq_false hNotGe]; rfl

private theorem truncateBits_bvOfInt_decodeScalar {w : IntWidth} {s : Bool} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvOfInt 128 (decodeScalar ⟨w, s, b⟩)) = b := by
  have hLt : b.toNat < Nat.pow 2 w.bitWidth := truncateBits_eq_iff.mp hWf
  apply bitvec_eq_of_toNat_eq
  rw [toNat_truncateBits_bvOfInt]
  cases s with
  | false =>
    rw [decodeScalar_unsigned hWf, intEmod_ofNat]
    exact nat_mod_eq_of_lt hLt
  | true =>
    rw [decodeScalar_signed hWf, signExtendBits_eq hLt]
    cases Nat.lt_or_ge (2 * b.toNat) (Nat.pow 2 w.bitWidth) with
    | inl hCmp =>
      rw [ite_prop_true hCmp, intEmod_ofNat]
      exact nat_mod_eq_of_lt hLt
    | inr hCmp =>
      rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
      let M := Nat.pow 2 w.bitWidth
      let k := M - 1 - b.toNat
      have hDiff : M - b.toNat = k + 1 := nat_sub_pos_eq_succ hLt
      have hSum : b.toNat + (k + 1) = M := by
        have hAdd := Nat.add_sub_of_le (Nat.le_of_lt hLt)
        rw [hDiff] at hAdd; exact hAdd
      have hKLtM : k < M := by
        have hLe : k + 1 ≤ M := by rw [← hSum]; exact Nat.le_add_left (k + 1) b.toNat
        exact Nat.lt_of_succ_le hLe
      rw [intEmod_negSucc, nat_mod_eq_of_lt hKLtM, int_subNatNat_of_le hKLtM]
      change M - (k + 1) = b.toNat
      rw [← hSum]; exact Nat.add_sub_cancel b.toNat (k + 1)

private theorem truncateScalar_decodeScalar {w : IntWidth} {s : Bool} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateScalar w s (decodeScalar ⟨w, s, b⟩) = .ok (⟨w, s, b⟩, false) := by
  let ⟨lossy, hTr, hFalse, hTrue⟩ := truncateScalar_eq w s (decodeScalar ⟨w, s, b⟩)
  have hBits := truncateBits_bvOfInt_decodeScalar (s := s) hWf
  rw [hBits] at hTr
  cases s with
  | false =>
    have hL := hFalse rfl
    rw [hBits] at hL
    have hBvEq : bvOfInt 128 (decodeScalar ⟨w, false, b⟩) = b := by
      rw [decodeScalar_unsigned hWf]; unfold bvOfInt; rw [intEmod_ofNat]
      apply bitvec_eq_of_toNat_eq
      change Nat.mod (Nat.mod b.toNat (Nat.pow 2 128)) (Nat.pow 2 128) = b.toNat
      rw [nat_mod_eq_of_lt (bv_isLt b), nat_mod_eq_of_lt (bv_isLt b)]
    rw [hBvEq] at hL
    have hLossyFalse : (b != b) = false := by
      change (!(b == b)) = false; rw [bitvec_beq_refl b]; rfl
    rw [hLossyFalse] at hL; subst hL; exact hTr
  | true =>
    have hL := hTrue rfl
    rw [hBits] at hL
    have hDecEq : bvToInt (bvOfInt 128 (decodeScalar ⟨w, true, b⟩)) = signExtendBits w b := by
      rw [decodeScalar_signed hWf]; unfold signExtendBits
      let x := bvSignExtend 128 (bvExtractLsb (w.bitWidth - 1) 0 b)
      change bvToInt (bvOfInt 128 (bvToInt x)) = bvToInt x
      rw [bvOfInt_bvToInt_128 x]
    rw [hDecEq] at hL
    have hLossyFalse : (signExtendBits w b != signExtendBits w b) = false := by
      change (!(signExtendBits w b == signExtendBits w b)) = false
      rw [int_beq_refl]; rfl
    rw [hLossyFalse] at hL; subst hL; exact hTr

private theorem truncateBits_one (w : IntWidth) :
    truncateBits w (BitVec.ofNat 128 1) = BitVec.ofNat 128 1 := by
  cases w <;> decide

private theorem decodeScalar_zero (w : IntWidth) (s : Bool) :
    decodeScalar ⟨w, s, BitVec.ofNat 128 0⟩ = 0 := by
  cases w <;> cases s <;> decide

private theorem decodeScalar_one (w : IntWidth) (s : Bool) :
    decodeScalar ⟨w, s, BitVec.ofNat 128 1⟩ = 1 := by
  cases w <;> cases s <;> decide

private theorem isFalseBoolConst_elim {c : ConstOperand} (h : isFalseBoolConst c = true) :
    c = ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩ ∧
    evalConstLit c.ty c.lit = .ok (.bool false) := by
  cases c with
  | mk ty lit =>
    unfold isFalseBoolConst at h; dsimp at h
    let ⟨h1, h2⟩ := bool_and_true h
    have hTy := mirTy_beq_eq h1
    have hLit := constLitEq_eq h2
    subst hTy; subst hLit
    exact ⟨rfl, rfl⟩

private theorem isIntZeroConst_elim {w : IntWidth} {s : Bool} {c : ConstOperand}
    (h : isIntZeroConst w s c = true) :
    c = ⟨.int w s, .scalar (BitVec.ofNat 128 0)⟩ ∧
    evalConstLit c.ty c.lit = .ok (.scalar ⟨w, s, BitVec.ofNat 128 0⟩) := by
  cases c with
  | mk ty lit =>
    unfold isIntZeroConst at h; dsimp at h
    let ⟨h1, h2⟩ := bool_and_true h
    have hTy := mirTy_beq_eq h1
    have hLit := constLitEq_eq h2
    subst hTy; subst hLit
    refine ⟨rfl, ?_⟩
    dsimp only; unfold evalConstLit; dsimp only
    rw [truncateBits_zero w]; rfl

private theorem isIntOneConst_elim {w : IntWidth} {s : Bool} {c : ConstOperand}
    (h : isIntOneConst w s c = true) :
    c = ⟨.int w s, .scalar (BitVec.ofNat 128 1)⟩ ∧
    evalConstLit c.ty c.lit = .ok (.scalar ⟨w, s, BitVec.ofNat 128 1⟩) := by
  cases c with
  | mk ty lit =>
    unfold isIntOneConst at h; dsimp at h
    let ⟨h1, h2⟩ := bool_and_true h
    have hTy := mirTy_beq_eq h1
    have hLit := constLitEq_eq h2
    subst hTy; subst hLit
    refine ⟨rfl, ?_⟩
    dsimp only; unfold evalConstLit; dsimp only
    rw [truncateBits_one w]; rfl

private theorem nat_xor_zero_left (m : Nat) : Nat.xor 0 m = m := by
  unfold Nat.xor; rw [Nat.bitwise.eq_1]; rfl

private theorem nat_xor_zero_right (n : Nat) : Nat.xor n 0 = n := by
  unfold Nat.xor; rw [Nat.bitwise.eq_1]; cases n <;> rfl

private theorem truncateBits_bvXor_zero_left {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvXor (BitVec.ofNat 128 0) b) = b := by
  have h0 : (BitVec.ofNat 128 0).toNat = 0 := rfl
  have hEq : bvXor (BitVec.ofNat 128 0) b = b := by
    apply bitvec_eq_of_toNat_eq
    unfold bvXor; rw [h0, nat_xor_zero_left]
    exact nat_mod_eq_of_lt (bv_isLt b)
  rw [hEq, hWf]

private theorem truncateBits_bvXor_zero_right {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvXor b (BitVec.ofNat 128 0)) = b := by
  have h0 : (BitVec.ofNat 128 0).toNat = 0 := rfl
  have hEq : bvXor b (BitVec.ofNat 128 0) = b := by
    apply bitvec_eq_of_toNat_eq
    unfold bvXor; rw [h0, nat_xor_zero_right]
    exact nat_mod_eq_of_lt (bv_isLt b)
  rw [hEq, hWf]

private theorem evalBinOp_scalar_nonShift {op : BinOp} {w : IntWidth} {s : Bool}
    {b₁ b₂ : BitVec 128} (hShift : op.isShift = false) :
    evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      match op with
      | .eq => .ok (.bool (decodeScalar ⟨w, s, b₁⟩ == decodeScalar ⟨w, s, b₂⟩))
      | .ne => .ok (.bool (decodeScalar ⟨w, s, b₁⟩ != decodeScalar ⟨w, s, b₂⟩))
      | .lt => .ok (.bool (decide (decodeScalar ⟨w, s, b₁⟩ < decodeScalar ⟨w, s, b₂⟩)))
      | .le => .ok (.bool (decide (decodeScalar ⟨w, s, b₁⟩ ≤ decodeScalar ⟨w, s, b₂⟩)))
      | .gt => .ok (.bool (decide (decodeScalar ⟨w, s, b₁⟩ > decodeScalar ⟨w, s, b₂⟩)))
      | .ge => .ok (.bool (decide (decodeScalar ⟨w, s, b₁⟩ ≥ decodeScalar ⟨w, s, b₂⟩)))
      | .bitAnd => .ok (.scalar ⟨w, s, truncateBits w (bvAnd (truncateBits w b₁) (truncateBits w b₂))⟩)
      | .bitOr => .ok (.scalar ⟨w, s, truncateBits w (bvOr (truncateBits w b₁) (truncateBits w b₂))⟩)
      | .bitXor => .ok (.scalar ⟨w, s, truncateBits w (bvXor (truncateBits w b₁) (truncateBits w b₂))⟩)
      | .add | .sub | .mul | .div | .rem
      | .addUnchecked | .subUnchecked | .mulUnchecked =>
        evalArithOp op w s (decodeScalar ⟨w, s, b₁⟩) (decodeScalar ⟨w, s, b₂⟩)
      | _ => .error .unsupported := by
  unfold evalBinOp; dsimp only
  rw [intWidth_beq_refl w, bool_beq_refl s]
  cases op <;> cases hShift <;> rfl

private noncomputable def binOpIsDivOrRem : BinOp → Bool
  | .div | .rem => true
  | _ => false

private noncomputable def evalArithMath (op : BinOp) (l r : Int) : Option Int :=
  match op with
  | .add | .addUnchecked => some (l + r)
  | .sub | .subUnchecked => some (l - r)
  | .mul | .mulUnchecked => some (l * r)
  | .div => some (intTdiv l r)
  | .rem => some (intTmod l r)
  | _ => none

private theorem evalArithOp_preserves_scalar {op : BinOp} {w : IntWidth} {s : Bool}
    {b : BitVec 128} {l r : Int}
    (hWf : truncateBits w b = b)
    (hNotDivZero : (binOpIsDivOrRem op && (r == 0)) = false)
    (hNotMinNeg1 : (s && binOpIsDivOrRem op && (l == signedMinInt w && r == Neg.neg 1)) = false)
    (hRes : evalArithMath op l r = some (decodeScalar ⟨w, s, b⟩)) :
    evalArithOp op w s l r = .ok (.scalar ⟨w, s, b⟩) := by
  have hHost := decodeScalar_in_host_range (sv := ⟨w, s, b⟩)
  dsimp only at hHost
  have hTrunc := truncateScalar_decodeScalar (w := w) (s := s) hWf
  unfold evalArithOp
  cases op with
  | add | addUnchecked | sub | subUnchecked | mul | mulUnchecked | div | rem =>
    dsimp only [binOpIsDivOrRem, evalArithMath] at hNotDivZero hNotMinNeg1 hRes
    dsimp only [binOpIsDivOrRem, evalArithMath]
    injection hRes with hValEq
    rw [if_bool_false hNotDivZero, if_bool_false hNotMinNeg1, hValEq]
    rw [hHost, hTrunc]; dsimp
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | bitXor | bitAnd | bitOr | shl | shlUnchecked | shr | shrUnchecked
  | eq | lt | le | ne | ge | gt | offset =>
    cases hRes

private theorem isAlgLeftNeutral_const_ok {dstTy : MirTy} {op : BinOp} {c : ConstOperand}
    (h : isAlgLeftNeutral dstTy op c = true) :
    isPrimitiveReadableTy dstTy = true ∧
    isPrimitiveReadableTy c.ty = true ∧
    ∃ vc, evalConstLit c.ty c.lit = .ok vc ∧
      (∀ v, checkVal v dstTy = true → evalBinOp op vc v = .ok v) := by
  cases dstTy with
  | int w s =>
    unfold isAlgLeftNeutral at h
    cases op with
    | add =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_zero_add]
    | addUnchecked =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_zero_add]
    | mul =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_one w s, int_one_mul]
    | mulUnchecked =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_one w s, int_one_mul]
    | bitXor =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_zero w, hWf, truncateBits_bvXor_zero_left hWf]
    | addWithOverflow | sub | subUnchecked | subWithOverflow | mulWithOverflow
    | div | rem | bitAnd | bitOr | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset =>
      cases h
  | bool =>
    unfold isAlgLeftNeutral at h
    cases op with
    | bitXor =>
      let ⟨hc, hEvC⟩ := isFalseBoolConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
      cases b <;> rfl
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mul | mulUnchecked | mulWithOverflow | div | rem | bitAnd | bitOr
    | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset =>
      cases h
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases h

private theorem isAlgRightNeutral_const_ok {dstTy : MirTy} {op : BinOp} {c : ConstOperand}
    (h : isAlgRightNeutral dstTy op c = true) :
    isPrimitiveReadableTy dstTy = true ∧
    isPrimitiveReadableTy c.ty = true ∧
    ∃ vc, evalConstLit c.ty c.lit = .ok vc ∧
      (∀ v, checkVal v dstTy = true → evalBinOp op v vc = .ok v) := by
  cases dstTy with
  | int w s =>
    unfold isAlgRightNeutral at h
    cases op with
    | add =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_add_zero]
    | addUnchecked =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_add_zero]
    | sub =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_sub_zero]
    | subUnchecked =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_sub_zero]
    | mul =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_one w s, int_mul_one]
    | mulUnchecked =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_one w s, int_mul_one]
    | bitXor =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_zero w, hWf, truncateBits_bvXor_zero_right hWf]
    | addWithOverflow | subWithOverflow | mulWithOverflow
    | div | rem | bitAnd | bitOr | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset =>
      cases h
  | bool =>
    unfold isAlgRightNeutral at h
    cases op with
    | bitXor =>
      let ⟨hc, hEvC⟩ := isFalseBoolConst_elim h
      refine ⟨rfl, by rw [hc]; rfl, _, hEvC, fun v hChk => ?_⟩
      let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
      cases b <;> rfl
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mul | mulUnchecked | mulWithOverflow | div | rem | bitAnd | bitOr
    | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset =>
      cases h
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases h

private theorem foldAlgNeutralRvalue_eval_eq {bodyLocals : List MirTy}
    {locals : List LocalSlot} {dstTy : MirTy} {rv : Rvalue}
    (hWt : LocalsWellTyped bodyLocals locals) :
    evalRvalue bodyLocals locals dstTy (foldAlgNeutralRvalue bodyLocals dstTy rv) =
      evalRvalue bodyLocals locals dstTy rv := by
  have hLeftFold : ∀ op c rhs rhsTy,
      operandStaticTy? bodyLocals rhs = some rhsTy →
      MirTy.beq rhsTy dstTy = true →
      isAlgLeftNeutral dstTy op c = true →
      evalRvalue bodyLocals locals dstTy (.use rhs) =
        evalRvalue bodyLocals locals dstTy (.binaryOp op (.constant c) rhs) := by
    intro op c rhs rhsTy hRTy hEqB hLNeut
    have hREq := mirTy_beq_eq hEqB; subst hREq
    let ⟨hPrimDst, hPrimC, vc, hEvC, hBinId⟩ := isAlgLeftNeutral_const_ok hLNeut
    have hConstPrim : evalPrimitiveOperand bodyLocals locals (.constant c) =
        .ok (vc, locals) := by
      dsimp [evalPrimitiveOperand, evalOperandToSlot]
      rw [hEvC]; dsimp; rw [hPrimC]; rfl
    dsimp [evalRvalue]
    rw [hConstPrim]; dsimp
    unfold evalPrimitiveOperand
    cases hSR : evalOperandToSlot bodyLocals locals rhs with
    | error _ => rfl
    | ok resR =>
      let ⟨srcTy, optVal, locs1⟩ := resR
      dsimp only
      have hSrcEq := operandStaticTy?_evalSlot_eq hRTy hSR
      subst hSrcEq
      rw [mirTy_beq_refl srcTy, hPrimDst]; dsimp
      cases optVal with
      | none => rfl
      | some vr =>
        dsimp
        have hChkR := (evalOperandToSlot_preserves_wt hWt hSR).2 vr rfl
        rw [hBinId vr hChkR]
  have hRightFold : ∀ op lhs cR lhsTy,
      operandStaticTy? bodyLocals lhs = some lhsTy →
      MirTy.beq lhsTy dstTy = true →
      isAlgRightNeutral dstTy op cR = true →
      evalRvalue bodyLocals locals dstTy (.use lhs) =
        evalRvalue bodyLocals locals dstTy (.binaryOp op lhs (.constant cR)) := by
    intro op lhs cR lhsTy hLTy hEqB hRNeut
    have hLEq := mirTy_beq_eq hEqB; subst hLEq
    let ⟨hPrimDst, hPrimC, vcR, hEvC, hBinId⟩ := isAlgRightNeutral_const_ok hRNeut
    dsimp [evalRvalue, evalPrimitiveOperand]
    cases hSL : evalOperandToSlot bodyLocals locals lhs with
    | error _ => rfl
    | ok resL =>
      let ⟨srcTy, optVal, locs1⟩ := resL
      dsimp only
      have hSrcEq := operandStaticTy?_evalSlot_eq hLTy hSL
      subst hSrcEq
      rw [mirTy_beq_refl srcTy, hPrimDst]; dsimp
      cases optVal with
      | none => rfl
      | some vl =>
        dsimp [evalOperandToSlot]
        rw [hEvC]; dsimp; rw [hPrimC]; dsimp
        have hChkL := (evalOperandToSlot_preserves_wt hWt hSL).2 vl rfl
        rw [hBinId vl hChkL]
  cases rv with
  | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
  | aggregateTuple _ | unsupported => rfl
  | binaryOp op lhs rhs =>
    dsimp [foldAlgNeutralRvalue]
    cases lhs with
    | constant c =>
      cases hRTy : operandStaticTy? bodyLocals rhs with
      | some rhsTy =>
        dsimp only
        cases hC1 : (MirTy.beq rhsTy dstTy && isAlgLeftNeutral dstTy op c) with
        | true =>
          rw [if_bool_true rfl]
          let ⟨hEqB, hLN⟩ := bool_and_true hC1
          exact hLeftFold op c rhs rhsTy hRTy hEqB hLN
        | false =>
          rw [if_bool_false rfl]
          cases rhs with
          | copy _ | move _ => rfl
          | constant cR =>
            cases hLTy : operandStaticTy? bodyLocals (.constant c) with
            | none => rfl
            | some lhsTy =>
              dsimp only
              cases hC2 : (MirTy.beq lhsTy dstTy && isAlgRightNeutral dstTy op cR) with
              | false => rw [if_bool_false rfl]
              | true =>
                rw [if_bool_true rfl]
                let ⟨hEqB, hRN⟩ := bool_and_true hC2
                exact hRightFold op (.constant c) cR lhsTy hLTy hEqB hRN
      | none =>
        dsimp only
        cases rhs with
        | copy _ | move _ => rfl
        | constant cR =>
          cases hLTy : operandStaticTy? bodyLocals (.constant c) with
          | none => rfl
          | some lhsTy =>
            dsimp only
            cases hC2 : (MirTy.beq lhsTy dstTy && isAlgRightNeutral dstTy op cR) with
            | false => rw [if_bool_false rfl]
            | true =>
              rw [if_bool_true rfl]
              let ⟨hEqB, hRN⟩ := bool_and_true hC2
              exact hRightFold op (.constant c) cR lhsTy hLTy hEqB hRN
    | copy pL =>
      dsimp only
      cases rhs with
      | copy _ | move _ => rfl
      | constant cR =>
        cases hLTy : operandStaticTy? bodyLocals (.copy pL) with
        | none => rfl
        | some lhsTy =>
          dsimp only
          cases hC2 : (MirTy.beq lhsTy dstTy && isAlgRightNeutral dstTy op cR) with
          | false => rw [if_bool_false rfl]
          | true =>
            rw [if_bool_true rfl]
            let ⟨hEqB, hRN⟩ := bool_and_true hC2
            exact hRightFold op (.copy pL) cR lhsTy hLTy hEqB hRN
    | move pL =>
      dsimp only
      cases rhs with
      | copy _ | move _ => rfl
      | constant cR =>
        cases hLTy : operandStaticTy? bodyLocals (.move pL) with
        | none => rfl
        | some lhsTy =>
          dsimp only
          cases hC2 : (MirTy.beq lhsTy dstTy && isAlgRightNeutral dstTy op cR) with
          | false => rw [if_bool_false rfl]
          | true =>
            rw [if_bool_true rfl]
            let ⟨hEqB, hRN⟩ := bool_and_true hC2
            exact hRightFold op (.move pL) cR lhsTy hLTy hEqB hRN

/-! #### Part 3B: `ConstAbsSlot` Domain Soundness -/

private noncomputable def SlotMatchesConst (ty : MirTy) : ConstAbsSlot → LocalSlot → Prop
  | .bottom, _ => False
  | .knownConst cTy cLit, sl =>
    cTy = ty ∧
    ∃ v, sl = .live (some v) ∧
      evalConstLit ty cLit = .ok v ∧
      checkVal v ty = true
  | .liveUnknown, sl =>
    ∃ v, sl = .live (some v) ∧ checkVal v ty = true
  | .liveUninit, sl =>
    ∃ opt, sl = .live opt ∧ SlotWellTyped ty (.live opt)
  | .dead, sl =>
    SlotWellTyped ty sl

private theorem slotMatchesConst_wt {ty : MirTy} {abs : ConstAbsSlot} {sl : LocalSlot}
    (h : SlotMatchesConst ty abs sl) : SlotWellTyped ty sl := by
  cases abs with
  | bottom => exact False.elim h
  | knownConst _ _ =>
    let ⟨_, v, hsl, _, hchk⟩ := h; subst hsl; exact hchk
  | liveUnknown =>
    let ⟨v, hsl, hchk⟩ := h; subst hsl; exact hchk
  | liveUninit =>
    let ⟨opt, hsl, hwt⟩ := h; subst hsl; exact hwt
  | dead => exact h

private theorem slotMatchesConst_mono {ty : MirTy} {abs₁ abs₂ : ConstAbsSlot} {sl : LocalSlot}
    (hImp : constSlotImplies abs₁ abs₂ = true)
    (hMatch : SlotMatchesConst ty abs₁ sl) :
    SlotMatchesConst ty abs₂ sl := by
  cases abs₁ with
  | bottom => exact False.elim hMatch
  | knownConst t1 l1 =>
    let ⟨ht1, v, hsl, hev, hchk⟩ := hMatch
    subst ht1
    cases abs₂ with
    | bottom => cases hImp
    | knownConst t2 l2 =>
      dsimp [constSlotImplies] at hImp
      let ⟨ht, hl⟩ := bool_and_true hImp
      have htEq := mirTy_beq_eq ht
      have hlEq := constLitEq_eq hl
      subst htEq; subst hlEq
      exact ⟨rfl, v, hsl, hev, hchk⟩
    | liveUnknown => exact ⟨v, hsl, hchk⟩
    | liveUninit => exact ⟨some v, hsl, hchk⟩
    | dead => subst hsl; exact hchk
  | liveUnknown =>
    let ⟨v, hsl, hchk⟩ := hMatch
    cases abs₂ with
    | bottom | knownConst _ _ => cases hImp
    | liveUnknown => exact ⟨v, hsl, hchk⟩
    | liveUninit => exact ⟨some v, hsl, hchk⟩
    | dead => subst hsl; exact hchk
  | liveUninit =>
    let ⟨opt, hsl, hwt⟩ := hMatch
    cases abs₂ with
    | bottom | knownConst _ _ | liveUnknown => cases hImp
    | liveUninit => exact ⟨opt, hsl, hwt⟩
    | dead => subst hsl; exact hwt
  | dead =>
    cases abs₂ with
    | bottom | knownConst _ _ | liveUnknown | liveUninit => cases hImp
    | dead => exact hMatch

private theorem slotMatchesConst_liveUninit (ty : MirTy) :
    SlotMatchesConst ty (liveUninitConstSlot ty) (liveUninitSlot ty) := by
  unfold liveUninitConstSlot
  cases hZ : isAlwaysInhabitedZst ty with
  | false =>
    rw [if_bool_false rfl]
    let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
    refine ⟨opt, hOpt, ?_⟩
    rw [← hOpt]; exact liveUninitSlot_wellTyped ty
  | true =>
    rw [if_bool_true rfl]
    cases ty with
    | unit => exact ⟨.unit, rfl, rfl⟩
    | enum ety =>
      dsimp [isAlwaysInhabitedZst] at hZ
      dsimp [liveUninitSlot]
      rw [if_bool_true hZ]
      let ⟨_, hAdm, hLen1⟩ := isZstEnumTy_elim hZ
      exact ⟨.enumVal ety 0, rfl,
        checkVal_enum_iff.mpr ⟨hAdm, 0, by rw [hLen1]; exact Nat.zero_lt_one, rfl⟩⟩
    | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
      cases hZ

private noncomputable def LocalsMatchConstEnv (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (locals : List LocalSlot) : Prop :=
  env.length = bodyLocals.length ∧
  locals.length = bodyLocals.length ∧
  ∀ i ty abs sl,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? env i = some abs →
    Trusted.MirSemantics.getElem? locals i = some sl →
    SlotMatchesConst ty abs sl

private theorem localsMatchConstEnv_wt {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals : List LocalSlot}
    (h : LocalsMatchConstEnv bodyLocals env locals) :
    LocalsWellTyped bodyLocals locals := by
  let ⟨hLenE, hLenL, hAll⟩ := h
  refine ⟨hLenL, ?_⟩
  intro i ty sl hTy hSl
  let ⟨abs, hAbs⟩ := getElem?_some_of_lt env i (by rw [hLenE]; exact getElem?_some_lt hTy)
  exact slotMatchesConst_wt (hAll i ty abs sl hTy hAbs hSl)

private theorem localsMatchConstEnv_mono {bodyLocals : List MirTy}
    {env₁ env₂ : List ConstAbsSlot} {locals : List LocalSlot}
    (hImp : constEnvImplies env₁ env₂ = true)
    (hMatch : LocalsMatchConstEnv bodyLocals env₁ locals) :
    LocalsMatchConstEnv bodyLocals env₂ locals := by
  let ⟨hLen1, hLenL, hAll1⟩ := hMatch
  have hLen12 : env₁.length = env₂.length := listRel_length hImp
  refine ⟨by rw [← hLen12]; exact hLen1, hLenL, ?_⟩
  intro i ty abs₂ sl hTy hAbs₂ hSl
  let ⟨abs₁, hAbs₁, hSlotImp⟩ := listRel_getElem?_right hImp hAbs₂
  exact slotMatchesConst_mono hSlotImp (hAll1 i ty abs₁ sl hTy hAbs₁ hSl)

private theorem localsMatchConstEnv_set {bodyLocals : List MirTy}
    {env env' : List ConstAbsSlot} {locals locals' : List LocalSlot}
    {id : Nat} {ty : MirTy} {abs' : ConstAbsSlot} {sl' : LocalSlot}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSetE : setElem? env id abs' = some env')
    (hSetL : setElem? locals id sl' = some locals')
    (hSlot : SlotMatchesConst ty abs' sl') :
    LocalsMatchConstEnv bodyLocals env' locals' := by
  let ⟨hLenE, hLenL, hAll⟩ := hMatch
  refine ⟨by rw [setElem?_length hSetE, hLenE],
          by rw [setElem?_length hSetL, hLenL], ?_⟩
  intro i tyi absi sli hTyi hAbsi hSli
  cases hEq : Nat.beq i id with
  | true =>
    have hi : i = id := nat_beq_eq hEq; subst hi
    rw [hTy] at hTyi; injection hTyi with hEqT; subst hEqT
    rw [setElem?_getElem?_same hSetE] at hAbsi; injection hAbsi with hEqA; subst hEqA
    rw [setElem?_getElem?_same hSetL] at hSli; injection hSli with hEqS; subst hEqS
    exact hSlot
  | false =>
    have hNe : i ≠ id := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSetE hNe] at hAbsi
    rw [setElem?_getElem?_ne hSetL hNe] at hSli
    exact hAll i tyi absi sli hTyi hAbsi hSli

private theorem initConstEnvLoop_length (body : Body) (base : Nat) (tys : List MirTy) :
    (initConstEnvLoop body base tys).length = tys.length := by
  induction tys generalizing base with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [initConstEnvLoop, List.length]; rw [ih (base + 1)]

private theorem initConstEnvLoop_getElem? (body : Body) (base : Nat) (tys : List MirTy)
    (i : Nat) (ty : MirTy)
    (hTy : Trusted.MirSemantics.getElem? tys i = some ty) :
    Trusted.MirSemantics.getElem? (initConstEnvLoop body base tys) i =
      some (initConstSlot body (base + i) ty) := by
  induction tys generalizing base i with
  | nil => cases hTy
  | cons _ rest ih =>
    cases i with
    | zero => injection hTy with hEq; subst hEq; rfl
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTy
      rw [hAdd] at hRec; exact hRec

private theorem initConstEnvLoop_matches {body : Body} {args : List Val}
    (hArgs : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true) :
    LocalsMatchConstEnv body.locals
      (initConstEnvLoop body 0 body.locals)
      (initLocalsLoop body args 0 body.locals) := by
  refine ⟨initConstEnvLoop_length body 0 body.locals,
          initLocalsLoop_length body args 0 body.locals, ?_⟩
  intro i ty abs sl hTy hAbs hSl
  have hGE := initConstEnvLoop_getElem? body 0 body.locals i ty hTy
  have hGL := initLocalsLoop_getElem? body args 0 body.locals i ty hTy
  rw [Nat.zero_add] at hGE hGL
  rw [hGE] at hAbs; injection hAbs with hEqA; subst hEqA
  rw [hGL] at hSl; injection hSl with hEqS; subst hEqS
  unfold initConstSlot
  cases i with
  | zero =>
    dsimp [Nat.beq]; exact slotMatchesConst_liveUninit ty
  | succ k =>
    dsimp [Nat.beq]
    cases hLe : Nat.ble (k + 1) body.argumentCount with
    | true =>
      rw [if_bool_true rfl]
      have hKlt : k < body.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((body.locals.drop 1).take body.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 body.locals body.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]; exact ⟨v, rfl, hChk⟩
    | false =>
      rw [if_bool_false rfl]
      cases hasStorageAnnotation body (k + 1) with
      | true => exact True.intro
      | false => exact slotMatchesConst_liveUninit ty

private theorem validTypedConstOperand_elim {ty : MirTy} {c : ConstOperand}
    (h : validTypedConstOperand ty c = true) :
    c.ty = ty ∧
    isSupportedScalarOrUnitTy ty = true ∧
    ∃ v, evalConstLit ty c.lit = .ok v ∧ checkVal v ty = true := by
  unfold validTypedConstOperand at h
  let ⟨h12, hEv⟩ := bool_and_true h
  let ⟨hTyEq, hSup⟩ := bool_and_true h12
  cases hC : evalConstLit ty c.lit with
  | error _ => rw [hC] at hEv; cases hEv
  | ok v =>
    rw [hC] at hEv
    exact ⟨mirTy_beq_eq hTyEq, hSup, v, rfl, hEv⟩

private theorem evalOperandConst?_sound {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {opTy srcTy : MirTy} {lit : ConstLit} {optVal : Option Val}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hConst : evalOperandConst? bodyLocals env opnd = some (opTy, lit))
    (hEval : evalOperandToSlot bodyLocals locals opnd = .ok (srcTy, optVal, locals')) :
    srcTy = opTy ∧
    ∃ v, optVal = some v ∧ evalConstLit opTy lit = .ok v ∧ checkVal v opTy = true := by
  let ⟨_, _, hAll⟩ := hMatch
  cases opnd with
  | constant c =>
    dsimp [evalOperandConst?] at hConst
    cases hVal : validTypedConstOperand c.ty c with
    | false => rw [hVal] at hConst; cases hConst
    | true =>
      rw [hVal, if_bool_true rfl] at hConst
      injection hConst with hPr
      injection hPr with hTyEq hLitEq; subst hTyEq; subst hLitEq
      let ⟨_, _, v, hEvC, hChk⟩ := validTypedConstOperand_elim hVal
      dsimp [evalOperandToSlot] at hEval
      rw [hEvC] at hEval
      injection hEval with hEq
      injection hEq with hSrc hR; injection hR with hOpt _
      subst hSrc; subst hOpt
      exact ⟨rfl, v, rfl, hEvC, hChk⟩
  | copy p =>
    dsimp [evalOperandConst?] at hConst
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hConst; cases hConst
    | true =>
      rw [hProj] at hConst; dsimp at hConst
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hConst; cases hConst
      | some ty =>
        rw [hTy] at hConst
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hConst; cases hConst
        | some abs =>
          rw [hAbs] at hConst
          cases abs with
          | bottom | liveUnknown | liveUninit | dead => cases hConst
          | knownConst cTy cLit =>
            dsimp at hConst
            cases hVal : validTypedConstOperand ty ⟨cTy, cLit⟩ with
            | false => rw [hVal] at hConst; cases hConst
            | true =>
              rw [hVal, if_bool_true rfl] at hConst
              injection hConst with hPr
              injection hPr with hOpTy hLitEq; subst hOpTy; subst hLitEq
              dsimp [evalOperandToSlot] at hEval
              rw [hProj, hTy] at hEval; dsimp at hEval
              cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
              | none => rw [hSl] at hEval; cases hEval
              | some sl =>
                rw [hSl] at hEval
                let ⟨_, v, hsl, hEvL, hChk⟩ := hAll p.localId ty (.knownConst cTy cLit) sl hTy hAbs hSl
                subst hsl
                injection hEval with hEq
                injection hEq with hSrc hR; injection hR with hOpt _
                subst hSrc; subst hOpt
                exact ⟨rfl, v, rfl, hEvL, hChk⟩
  | move p =>
    dsimp [evalOperandConst?] at hConst
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hConst; cases hConst
    | true =>
      rw [hProj] at hConst; dsimp at hConst
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hConst; cases hConst
      | some ty =>
        rw [hTy] at hConst
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hConst; cases hConst
        | some abs =>
          rw [hAbs] at hConst
          cases abs with
          | bottom | liveUnknown | liveUninit | dead => cases hConst
          | knownConst cTy cLit =>
            dsimp at hConst
            cases hVal : validTypedConstOperand ty ⟨cTy, cLit⟩ with
            | false => rw [hVal] at hConst; cases hConst
            | true =>
              rw [hVal, if_bool_true rfl] at hConst
              injection hConst with hPr
              injection hPr with hOpTy hLitEq; subst hOpTy; subst hLitEq
              dsimp [evalOperandToSlot] at hEval
              rw [hProj, hTy] at hEval; dsimp at hEval
              cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
              | none => rw [hSl] at hEval; cases hEval
              | some sl =>
                rw [hSl] at hEval
                let ⟨_, v, hsl, hEvL, hChk⟩ := hAll p.localId ty (.knownConst cTy cLit) sl hTy hAbs hSl
                subst hsl; dsimp at hEval
                cases hSet : setElem? locals p.localId (liveUninitSlot ty) with
                | none => rw [hSet] at hEval; cases hEval
                | some _ =>
                  rw [hSet] at hEval
                  injection hEval with hEq
                  injection hEq with hSrc hR; injection hR with hOpt _
                  subst hSrc; subst hOpt
                  exact ⟨rfl, v, rfl, hEvL, hChk⟩

private theorem deinitMoveOperandConst_sound {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {ty : MirTy} {optVal : Option Val}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hEval : evalOperandToSlot bodyLocals locals opnd = .ok (ty, optVal, locals')) :
    LocalsMatchConstEnv bodyLocals (deinitMoveOperandConst bodyLocals env opnd) locals' := by
  cases opnd with
  | constant c =>
    dsimp [evalOperandToSlot] at hEval
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEval; cases hEval
    | ok _ =>
      rw [hC] at hEval
      injection hEval with h1; injection h1 with _ h2; injection h2 with _ hLoc
      subst hLoc; exact hMatch
  | copy p =>
    dsimp [evalOperandToSlot] at hEval
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEval; cases hEval
    | true =>
      rw [hP] at hEval; dsimp at hEval
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some _ =>
        rw [hTy] at hEval
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEval; cases hEval
        | some sl =>
          rw [hSl] at hEval
          cases sl with
          | dead => cases hEval
          | live _ =>
            injection hEval with h1; injection h1 with _ h2; injection h2 with _ hLoc
            subst hLoc; exact hMatch
  | move p =>
    dsimp [evalOperandToSlot] at hEval
    dsimp [deinitMoveOperandConst]
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEval; cases hEval
    | true =>
      rw [hP] at hEval; dsimp at hEval; dsimp
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some t =>
        rw [hTy] at hEval; dsimp
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEval; cases hEval
        | some sl =>
          rw [hSl] at hEval
          cases sl with
          | dead => cases hEval
          | live _ =>
            dsimp at hEval
            cases hSetL : setElem? locals p.localId (liveUninitSlot t) with
            | none => rw [hSetL] at hEval; cases hEval
            | some locs1 =>
              rw [hSetL] at hEval
              injection hEval with h1; injection h1 with _ h2; injection h2 with _ hLoc
              subst hLoc
              let ⟨env1, hSetE⟩ := setElem?_some_of_lt env p.localId (liveUninitConstSlot t)
                (by rw [hMatch.1]; exact getElem?_some_lt hTy)
              rw [hSetE]
              exact localsMatchConstEnv_set hMatch hTy hSetE hSetL
                (slotMatchesConst_liveUninit t)

private theorem deinitMovePrimitiveOperand_sound {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {v : Val}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hEval : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    LocalsMatchConstEnv bodyLocals (deinitMoveOperandConst bodyLocals env opnd) locals' := by
  dsimp [evalPrimitiveOperand] at hEval
  cases hS : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [hS] at hEval; cases hEval
  | ok res =>
    let ⟨ty0, optVal, _⟩ := res
    rw [hS] at hEval; dsimp at hEval
    cases hP : isPrimitiveReadableTy ty0 with
    | false => rw [hP] at hEval; cases hEval
    | true =>
      rw [hP] at hEval; dsimp at hEval
      cases optVal with
      | none => cases hEval
      | some _ =>
        injection hEval with h1; injection h1 with _ hL; subst hL
        exact deinitMoveOperandConst_sound hMatch hS

private theorem rvalueConstSlot_and_deinit_sound {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {val : Val}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hEval : evalRvalue bodyLocals locals dstTy rv = .ok (val, locals'))
    (hChk : checkVal val dstTy = true) :
    LocalsMatchConstEnv bodyLocals (deinitMovesInRvalueConst bodyLocals env rv) locals' ∧
    SlotMatchesConst dstTy (rvalueConstSlot bodyLocals env dstTy rv) (.live (some val)) := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalue] at hEval
    cases hS : evalOperandToSlot bodyLocals locals opnd with
    | error _ => rw [hS] at hEval; cases hEval
    | ok res =>
      let ⟨srcTy, optVal, _⟩ := res
      rw [hS] at hEval; dsimp at hEval
      cases hEqTy : MirTy.beq srcTy dstTy with
      | false => rw [hEqTy] at hEval; cases hEval
      | true =>
        rw [hEqTy] at hEval; dsimp at hEval
        cases optVal with
        | none => cases hEval
        | some v0 =>
          injection hEval with h1; injection h1 with hv hl
          rw [← hv] at hChk; rw [← hv]; subst hl
          refine ⟨deinitMoveOperandConst_sound hMatch hS, ?_⟩
          dsimp [rvalueConstSlot]
          cases hC : evalOperandConst? bodyLocals env opnd with
          | none => exact ⟨v0, rfl, hChk⟩
          | some pr =>
            let ⟨opTy, lit⟩ := pr
            dsimp only
            let ⟨hSrcEq, v', hOptEq, hEvL, _⟩ := evalOperandConst?_sound hMatch hC hS
            rw [hSrcEq] at hEqTy
            injection hOptEq with hvEq; subst hvEq
            rw [hEqTy, if_bool_true rfl]
            have hOpDst := mirTy_beq_eq hEqTy
            rw [← hOpDst] at hChk; rw [← hOpDst]
            exact ⟨rfl, v0, rfl, hEvL, hChk⟩
  | unaryOp uop opnd =>
    dsimp [evalRvalue] at hEval
    cases hEO : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [hEO] at hEval; cases hEval
    | ok resO =>
      let ⟨ov, _⟩ := resO
      rw [hEO] at hEval; dsimp at hEval
      cases hUn : evalUnOp uop ov with
      | error _ => rw [hUn] at hEval; cases hEval
      | ok resV =>
        rw [hUn] at hEval
        injection hEval with h1; injection h1 with hv hl
        rw [← hv] at hChk; rw [← hv]; subst hl
        exact ⟨deinitMovePrimitiveOperand_sound hMatch hEO, resV, rfl, hChk⟩
  | binaryOp bop lhs rhs =>
    dsimp [evalRvalue] at hEval
    cases hEL : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [hEL] at hEval; cases hEval
    | ok resL =>
      let ⟨lv, locs1⟩ := resL
      rw [hEL] at hEval; dsimp at hEval
      have hMatch1 := deinitMovePrimitiveOperand_sound hMatch hEL
      cases hER : evalPrimitiveOperand bodyLocals locs1 rhs with
      | error _ => rw [hER] at hEval; cases hEval
      | ok resR =>
        let ⟨rvv, _⟩ := resR
        rw [hER] at hEval; dsimp at hEval
        have hMatch2 := deinitMovePrimitiveOperand_sound hMatch1 hER
        cases hBin : evalBinOp bop lv rvv with
        | error _ => rw [hBin] at hEval; cases hEval
        | ok resV =>
          rw [hBin] at hEval
          injection hEval with h1; injection h1 with hv hl
          rw [← hv] at hChk; rw [← hv]; subst hl
          exact ⟨hMatch2, resV, rfl, hChk⟩
  | discriminant p =>
    dsimp [evalRvalue] at hEval
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEval; cases hEval
    | true =>
      rw [hP] at hEval; dsimp at hEval
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some ty =>
        rw [hTy] at hEval
        cases ty with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hSl] at hEval; cases hEval
          | some sl =>
            rw [hSl] at hEval; dsimp at hEval
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEval; cases hEval
            | true =>
              rw [hAdm] at hEval; dsimp at hEval
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEval
                cases sl with
                | dead => cases hEval
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp at hEval
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEval; cases hEval
                    | some _ =>
                      rw [hD] at hEval; injection hEval with h1; injection h1 with _ hl
                      subst hl; exact ⟨hMatch, val, rfl, hChk⟩
                  | some v0 =>
                    cases v0 with
                    | enumVal ety' k =>
                      dsimp at hEval
                      cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => rw [hC] at hEval; cases hEval
                      | true =>
                        rw [hC] at hEval; dsimp at hEval
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEval; cases hEval
                        | some _ =>
                          rw [hD] at hEval; injection hEval with h1; injection h1 with _ hl
                          subst hl; exact ⟨hMatch, val, rfl, hChk⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEval
              | scalar _ _ =>
                rw [hTr] at hEval
                cases sl with
                | dead => cases hEval
                | live opt =>
                  cases opt with
                  | none => cases hEval
                  | some v0 =>
                    cases v0 with
                    | enumVal ety' k =>
                      dsimp at hEval
                      cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => rw [hC] at hEval; cases hEval
                      | true =>
                        rw [hC] at hEval; dsimp at hEval
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => rw [hD] at hEval; cases hEval
                        | some _ =>
                          rw [hD] at hEval; injection hEval with h1; injection h1 with _ hl
                          subst hl; exact ⟨hMatch, val, rfl, hChk⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEval
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEval
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEval

private theorem stepPlainStmtConst_sound {body : Body} {frame : FrameState}
    {cm : CallerMemory} {env env' : List ConstAbsSlot}
    {stmt : StatementKind} {s' : State}
    (hMatch : LocalsMatchConstEnv body.locals env frame.locals)
    (hAbs : stepPlainStmtConst body.locals env stmt = some env')
    (hEv : evalStatement body frame cm stmt = .step s') :
    ∃ locs',
      s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
             callerMem := cm } ∧
      LocalsMatchConstEnv body.locals env' locs' := by
  cases stmt with
  | nop =>
    injection hAbs with hEqE; subst hEqE
    injection hEv with hEqS; subst hEqS
    exact ⟨frame.locals, rfl, hMatch⟩
  | unsupported => cases hEv
  | storageLive id =>
    dsimp [stepPlainStmtConst] at hAbs
    dsimp [evalStatement] at hEv
    cases hTy : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [hTy] at hAbs; cases hAbs
    | some ty =>
      rw [hTy] at hAbs hEv; dsimp at hEv
      cases hSetL : setElem? frame.locals id (liveUninitSlot ty) with
      | none => rw [hSetL] at hEv; cases hEv
      | some locs' =>
        rw [hSetL] at hEv; injection hEv with hEqS; subst hEqS
        exact ⟨locs', rfl, localsMatchConstEnv_set hMatch hTy hAbs hSetL
          (slotMatchesConst_liveUninit ty)⟩
  | storageDead id =>
    dsimp [stepPlainStmtConst] at hAbs
    dsimp [evalStatement] at hEv
    cases hZ : Nat.beq id 0 with
    | true => rw [hZ] at hEv; cases hEv
    | false =>
      rw [hZ] at hAbs hEv; dsimp at hAbs hEv
      cases hSetL : setElem? frame.locals id .dead with
      | none => rw [hSetL] at hEv; cases hEv
      | some locs' =>
        rw [hSetL] at hEv; injection hEv with hEqS; subst hEqS
        have hLt : id < body.locals.length := by
          cases Nat.lt_or_ge id body.locals.length with
          | inl h => exact h
          | inr hge =>
            have hNone := setElem?_none_of_ge frame.locals id .dead (by rw [hMatch.2.1]; exact hge)
            rw [hNone] at hSetL; cases hSetL
        let ⟨ty, hTy⟩ := getElem?_some_of_lt body.locals id hLt
        exact ⟨locs', rfl, localsMatchConstEnv_set hMatch hTy hAbs hSetL True.intro⟩
  | assign dst rv =>
    dsimp [stepPlainStmtConst] at hAbs
    dsimp [evalStatement] at hEv
    cases hP : dst.projection.isEmpty with
    | false => rw [hP] at hAbs; cases hAbs
    | true =>
      rw [hP] at hAbs hEv; dsimp at hAbs hEv
      cases hTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hTy] at hAbs; cases hAbs
      | some dstTy =>
        rw [hTy] at hAbs hEv; dsimp at hAbs hEv
        cases hR : evalRvalue body.locals frame.locals dstTy rv with
        | error _ => rw [hR] at hEv; cases hEv
        | ok res =>
          let ⟨val, locs1⟩ := res
          rw [hR] at hEv; dsimp at hEv
          unfold writePlace at hEv
          cases hChk : checkVal val dstTy with
          | false => rw [hChk] at hEv; cases hEv
          | true =>
            rw [hChk] at hEv; dsimp at hEv
            cases hSlD : Trusted.MirSemantics.getElem? locs1 dst.localId with
            | none => rw [hSlD] at hEv; cases hEv
            | some slD =>
              rw [hSlD] at hEv
              cases slD with
              | dead => cases hEv
              | live _ =>
                cases hSetL : setElem? locs1 dst.localId (.live (some val)) with
                | none => rw [hSetL] at hEv; cases hEv
                | some locs' =>
                  rw [hSetL] at hEv; injection hEv with hEqS; subst hEqS
                  let ⟨hMatch1, hDstSlot⟩ := rvalueConstSlot_and_deinit_sound hMatch hR hChk
                  exact ⟨locs', rfl, localsMatchConstEnv_set hMatch1 hTy hAbs hSetL hDstSlot⟩

private theorem evalSwitchBranches_outcome {w : IntWidth} {discrBits : BitVec 128}
    {otherwise : BasicBlockId} {branches : List (BitVec 128 × BasicBlockId)}
    {target : BasicBlockId}
    (h : evalSwitchBranches w discrBits otherwise branches = .ok target) :
    target = otherwise ∨
    ∃ i caseBits,
      Trusted.MirSemantics.getElem? branches i = some (caseBits, target) ∧
      truncateBits w caseBits = caseBits ∧
      truncateBits w discrBits = truncateBits w caseBits := by
  induction branches with
  | nil =>
    injection h with hEq; exact Or.inl hEq.symm
  | cons br rest ih =>
    cases br with
    | mk caseBits brTgt =>
      dsimp [evalSwitchBranches] at h
      cases hOvf : (truncateBits w caseBits != caseBits) with
      | true => rw [hOvf] at h; cases h
      | false =>
        rw [hOvf] at h; dsimp at h
        have hTruncC := bitvec_eq_of_bne_false hOvf
        cases hEqB : (truncateBits w discrBits == truncateBits w caseBits) with
        | true =>
          rw [hEqB] at h; injection h with hTgt; subst hTgt
          exact Or.inr ⟨0, caseBits, rfl, hTruncC, bitvec_beq_eq hEqB⟩
        | false =>
          rw [hEqB] at h; dsimp at h
          cases ih h with
          | inl hOw => exact Or.inl hOw
          | inr hSub =>
            let ⟨i, cb, hGet, hTC, hTD⟩ := hSub
            exact Or.inr ⟨i + 1, cb, hGet, hTC, hTD⟩

private theorem evalBoolSwitchBranches_outcome {b : Bool}
    {otherwise : BasicBlockId} {branches : List (BitVec 128 × BasicBlockId)}
    {target : BasicBlockId}
    (h : evalBoolSwitchBranches b otherwise branches = .ok target) :
    target = otherwise ∨
    ∃ i caseBits,
      Trusted.MirSemantics.getElem? branches i = some (caseBits, target) ∧
      evalConstLit .bool (.scalar caseBits) = .ok (.bool b) := by
  induction branches with
  | nil =>
    injection h with hEq; exact Or.inl hEq.symm
  | cons br rest ih =>
    cases br with
    | mk caseBits brTgt =>
      dsimp [evalBoolSwitchBranches] at h
      cases hCL : evalConstLit .bool (.scalar caseBits) with
      | error _ => rw [hCL] at h; cases h
      | ok cv =>
        rw [hCL] at h
        cases cv with
        | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases h
        | bool cb =>
          cases cb with
          | false =>
            dsimp at h
            cases b with
            | false =>
              dsimp at h; injection h with hTgt; subst hTgt
              exact Or.inr ⟨0, caseBits, rfl, hCL⟩
            | true =>
              dsimp at h
              cases ih h with
              | inl hOw => exact Or.inl hOw
              | inr hSub =>
                let ⟨i, cb', hGet, hEv⟩ := hSub
                exact Or.inr ⟨i + 1, cb', hGet, hEv⟩
          | true =>
            dsimp at h
            cases b with
            | true =>
              dsimp at h; injection h with hTgt; subst hTgt
              exact Or.inr ⟨0, caseBits, rfl, hCL⟩
            | false =>
              dsimp at h
              cases ih h with
              | inl hOw => exact Or.inl hOw
              | inr hSub =>
                let ⟨i, cb', hGet, hEv⟩ := hSub
                exact Or.inr ⟨i + 1, cb', hGet, hEv⟩

private theorem refineSwitchBranchEnv_scalar_sound {bodyLocals : List MirTy}
    {exitEnv : List ConstAbsSlot} {locals locsAfter : List LocalSlot}
    {discr : Operand} {sv : ScalarVal} {caseBits : BitVec 128}
    (hMatch : LocalsMatchConstEnv bodyLocals exitEnv locals)
    (hEval : evalPrimitiveOperand bodyLocals locals discr = .ok (.scalar sv, locsAfter))
    (hTruncC : truncateBits sv.width caseBits = caseBits)
    (hTruncEq : truncateBits sv.width sv.bits = truncateBits sv.width caseBits) :
    LocalsMatchConstEnv bodyLocals
      (refineSwitchBranchEnv bodyLocals (deinitMoveOperandConst bodyLocals exitEnv discr) discr caseBits)
      locsAfter := by
  have hAfter := deinitMovePrimitiveOperand_sound hMatch hEval
  cases discr with
  | move _ | constant _ => exact hAfter
  | copy p =>
    dsimp [refineSwitchBranchEnv]
    cases hP : p.projection.isEmpty with
    | false => exact hAfter
    | true =>
      dsimp
      dsimp [evalPrimitiveOperand, evalOperandToSlot] at hEval
      rw [hP] at hEval; dsimp at hEval
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some ty =>
        rw [hTy] at hEval
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEval; cases hEval
        | some sl =>
          rw [hSl] at hEval
          cases sl with
          | dead => cases hEval
          | live opt =>
            dsimp at hEval
            cases hPrim : isPrimitiveReadableTy ty with
            | false => rw [hPrim] at hEval; cases hEval
            | true =>
              rw [hPrim] at hEval; dsimp at hEval
              cases opt with
              | none => cases hEval
              | some dv =>
                injection hEval with h1; injection h1 with hdv hLocs
                subst hdv; subst hLocs
                have hWt := localsMatchConstEnv_wt hMatch
                have hChk : checkVal (.scalar sv) ty = true :=
                  hWt.2 p.localId ty (.live (some (.scalar sv))) hTy hSl
                have hTyEq : ty = .int sv.width sv.signed := by
                  cases isPrimitiveReadableTy_elim hPrim with
                  | inl hB =>
                    subst hB
                    let ⟨_, hb⟩ := checkVal_bool_iff.mp hChk; cases hb
                  | inr hI =>
                    let ⟨w, s, hIS⟩ := hI; subst hIS
                    let ⟨_, hsc, _⟩ := checkVal_int_iff.mp hChk
                    injection hsc with hsc'
                    cases sv with
                    | mk sw ss sbits =>
                      injection hsc' with hw hs _
                      subst hw; subst hs; rfl
                subst hTyEq
                let ⟨wBits, hsc, hTruncSv⟩ := checkVal_int_iff.mp hChk
                have hBitsEq : sv.bits = caseBits := by
                  have hSb : sv.bits = wBits := congrArg ScalarVal.bits (Val.scalar.inj hsc)
                  rw [← hSb] at hTruncSv
                  rw [← hTruncSv, hTruncEq, hTruncC]
                dsimp [deinitMoveOperandConst] at hAfter
                dsimp [deinitMoveOperandConst]
                cases hAbs : Trusted.MirSemantics.getElem? exitEnv p.localId with
                | none => exact hAfter
                | some curSlot =>
                  dsimp only
                  cases (isPrimitiveReadableTy (.int sv.width sv.signed) &&
                      constSlotImplies curSlot .liveUnknown &&
                      validTypedConstOperand (.int sv.width sv.signed) ⟨.int sv.width sv.signed, .scalar caseBits⟩) with
                  | false => rw [if_bool_false rfl]; exact hAfter
                  | true =>
                    rw [if_bool_true rfl]
                    cases hSetE : setElem? exitEnv p.localId (.knownConst (.int sv.width sv.signed) (.scalar caseBits)) with
                    | none => exact hAfter
                    | some refined =>
                      have hEvC : evalConstLit (.int sv.width sv.signed) (.scalar caseBits) = .ok (.scalar sv) := by
                        dsimp [evalConstLit]
                        have hBneF : (truncateBits sv.width caseBits != caseBits) = false := by
                          rw [hTruncC]; change (!(caseBits == caseBits)) = false
                          rw [bitvec_beq_refl]; rfl
                        rw [hBneF, if_bool_false rfl, hTruncC]
                        cases sv with
                        | mk sw ss sb => dsimp at hBitsEq; subst hBitsEq; rfl
                      refine ⟨by rw [setElem?_length hSetE, hMatch.1], hMatch.2.1, ?_⟩
                      intro i tyi absi sli hTyi hAbsi hSli
                      cases hEqI : Nat.beq i p.localId with
                      | true =>
                        have hi := nat_beq_eq hEqI; subst hi
                        rw [hTy] at hTyi; injection hTyi with hEqT; subst hEqT
                        rw [setElem?_getElem?_same hSetE] at hAbsi; injection hAbsi with hEqA; subst hEqA
                        rw [hSl] at hSli; injection hSli with hEqS; subst hEqS
                        exact ⟨rfl, .scalar sv, rfl, hEvC, hChk⟩
                      | false =>
                        have hNe := nat_ne_of_beq_false hEqI
                        rw [setElem?_getElem?_ne hSetE hNe] at hAbsi
                        exact hMatch.2.2 i tyi absi sli hTyi hAbsi hSli

private theorem refineSwitchBranchEnv_bool_sound {bodyLocals : List MirTy}
    {exitEnv : List ConstAbsSlot} {locals locsAfter : List LocalSlot}
    {discr : Operand} {b : Bool} {caseBits : BitVec 128}
    (hMatch : LocalsMatchConstEnv bodyLocals exitEnv locals)
    (hEval : evalPrimitiveOperand bodyLocals locals discr = .ok (.bool b, locsAfter))
    (hEvC : evalConstLit .bool (.scalar caseBits) = .ok (.bool b)) :
    LocalsMatchConstEnv bodyLocals
      (refineSwitchBranchEnv bodyLocals (deinitMoveOperandConst bodyLocals exitEnv discr) discr caseBits)
      locsAfter := by
  have hAfter := deinitMovePrimitiveOperand_sound hMatch hEval
  cases discr with
  | move _ | constant _ => exact hAfter
  | copy p =>
    dsimp [refineSwitchBranchEnv]
    cases hP : p.projection.isEmpty with
    | false => exact hAfter
    | true =>
      dsimp
      dsimp [evalPrimitiveOperand, evalOperandToSlot] at hEval
      rw [hP] at hEval; dsimp at hEval
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some ty =>
        rw [hTy] at hEval
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEval; cases hEval
        | some sl =>
          rw [hSl] at hEval
          cases sl with
          | dead => cases hEval
          | live opt =>
            dsimp at hEval
            cases hPrim : isPrimitiveReadableTy ty with
            | false => rw [hPrim] at hEval; cases hEval
            | true =>
              rw [hPrim] at hEval; dsimp at hEval
              cases opt with
              | none => cases hEval
              | some dv =>
                injection hEval with h1; injection h1 with hdv hLocs
                subst hdv; subst hLocs
                have hWt := localsMatchConstEnv_wt hMatch
                have hChk : checkVal (.bool b) ty = true :=
                  hWt.2 p.localId ty (.live (some (.bool b))) hTy hSl
                have hTyEq : ty = .bool := by
                  cases isPrimitiveReadableTy_elim hPrim with
                  | inl hB => exact hB
                  | inr hI =>
                    let ⟨_, _, hIS⟩ := hI; subst hIS
                    let ⟨_, hsc, _⟩ := checkVal_int_iff.mp hChk; cases hsc
                subst hTyEq
                dsimp [deinitMoveOperandConst] at hAfter
                dsimp [deinitMoveOperandConst]
                cases hAbs : Trusted.MirSemantics.getElem? exitEnv p.localId with
                | none => exact hAfter
                | some curSlot =>
                  dsimp only
                  cases (isPrimitiveReadableTy .bool &&
                      constSlotImplies curSlot .liveUnknown &&
                      validTypedConstOperand .bool ⟨.bool, .scalar caseBits⟩) with
                  | false => rw [if_bool_false rfl]; exact hAfter
                  | true =>
                    rw [if_bool_true rfl]
                    cases hSetE : setElem? exitEnv p.localId (.knownConst .bool (.scalar caseBits)) with
                    | none => exact hAfter
                    | some refined =>
                      refine ⟨by rw [setElem?_length hSetE, hMatch.1], hMatch.2.1, ?_⟩
                      intro i tyi absi sli hTyi hAbsi hSli
                      cases hEqI : Nat.beq i p.localId with
                      | true =>
                        have hi := nat_beq_eq hEqI; subst hi
                        rw [hTy] at hTyi; injection hTyi with hEqT; subst hEqT
                        rw [setElem?_getElem?_same hSetE] at hAbsi; injection hAbsi with hEqA; subst hEqA
                        rw [hSl] at hSli; injection hSli with hEqS; subst hEqS
                        exact ⟨rfl, .bool b, rfl, hEvC, hChk⟩
                      | false =>
                        have hNe := nat_ne_of_beq_false hEqI
                        rw [setElem?_getElem?_ne hSetE hNe] at hAbsi
                        exact hMatch.2.2 i tyi absi sli hTyi hAbsi hSli

private theorem checkConstEdge_sound {bodyLocals : List MirTy} {numBlocks : Nat}
    {cert : BodyConstCert} {edgeEnv : List ConstAbsSlot}
    {locals : List LocalSlot} {target : BasicBlockId}
    (hMatch : LocalsMatchConstEnv bodyLocals edgeEnv locals)
    (hEdge : checkConstEdge numBlocks cert edgeEnv target = true)
    (hLt : target < numBlocks) :
    ∃ tgtEnv,
      Trusted.MirSemantics.getElem? cert target = some (some tgtEnv) ∧
      LocalsMatchConstEnv bodyLocals tgtEnv locals := by
  unfold checkConstEdge at hEdge
  rw [nat_lt_blt hLt] at hEdge; dsimp at hEdge
  cases hC : Trusted.MirSemantics.getElem? cert target with
  | none => rw [hC] at hEdge; cases hEdge
  | some optE =>
    rw [hC] at hEdge
    cases optE with
    | none => cases hEdge
    | some tgtEnv =>
      exact ⟨tgtEnv, rfl, localsMatchConstEnv_mono hEdge hMatch⟩

private theorem evalTerminator_constEdges_sound {body : Body} {bb : BasicBlock}
    {cert : BodyConstCert} {exitEnv : List ConstAbsSlot}
    {frame : FrameState} {cm : CallerMemory} {s' : State}
    (hMatch : LocalsMatchConstEnv body.locals exitEnv frame.locals)
    (hEdges : checkConstTerminatorEdges body.locals body.basicBlocks.length
      cert exitEnv bb.terminator = true)
    (hEv : evalTerminator body bb frame cm = .step s') :
    ∃ target locs',
      s' = { frames := [{ frame with blockIdx := target, stmtIdx := 0, locals := locs' }],
             callerMem := cm } ∧
      LocalsWellTyped body.locals locs' ∧
      (target < body.basicBlocks.length →
        ∃ tgtEnv,
          Trusted.MirSemantics.getElem? cert target = some (some tgtEnv) ∧
          LocalsMatchConstEnv body.locals tgtEnv locs') := by
  unfold evalTerminator at hEv
  cases hTm : bb.terminator with
  | goto target =>
    rw [hTm] at hEv hEdges
    injection hEv with hEq; subst hEq
    exact ⟨target, frame.locals, rfl, localsMatchConstEnv_wt hMatch,
           fun hLt => checkConstEdge_sound hMatch hEdges hLt⟩
  | return_ =>
    rw [hTm] at hEv; dsimp at hEv
    cases hC : bb.cleanup with
    | true => rw [hC] at hEv; cases hEv
    | false =>
      rw [hC] at hEv; dsimp at hEv
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at hEv; cases hEv
      | some sl =>
        rw [h0] at hEv
        cases sl with
        | dead => cases hEv
        | live o => cases o <;> cases hEv
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    rw [hTm] at hEv; cases hEv
  | switchInt discr targets =>
    rw [hTm] at hEv hEdges; dsimp [checkConstTerminatorEdges] at hEv hEdges
    let ⟨hOwEdge, hBrAll⟩ := bool_and_true hEdges
    cases hD : evalPrimitiveOperand body.locals frame.locals discr with
    | error _ => rw [hD] at hEv; cases hEv
    | ok res =>
      let ⟨dv, locsAfter⟩ := res
      rw [hD] at hEv; dsimp at hEv
      have hAfter := deinitMovePrimitiveOperand_sound hMatch hD
      cases dv with
      | scalar sv =>
        dsimp at hEv
        cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok target =>
          rw [hSw] at hEv; injection hEv with hEq; subst hEq
          refine ⟨target, locsAfter, rfl, localsMatchConstEnv_wt hAfter, ?_⟩
          intro hLt
          cases evalSwitchBranches_outcome hSw with
          | inl hOw =>
            subst hOw; exact checkConstEdge_sound hAfter hOwEdge hLt
          | inr hBr =>
            let ⟨i, caseBits, hGetBr, hTC, hTEq⟩ := hBr
            have hBrEdge := list_all_getElem? hBrAll hGetBr
            dsimp only at hBrEdge
            have hRefMatch := refineSwitchBranchEnv_scalar_sound hMatch hD hTC hTEq
            exact checkConstEdge_sound hRefMatch hBrEdge hLt
      | bool b =>
        dsimp at hEv
        cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok target =>
          rw [hSw] at hEv; injection hEv with hEq; subst hEq
          refine ⟨target, locsAfter, rfl, localsMatchConstEnv_wt hAfter, ?_⟩
          intro hLt
          cases evalBoolSwitchBranches_outcome hSw with
          | inl hOw =>
            subst hOw; exact checkConstEdge_sound hAfter hOwEdge hLt
          | inr hBr =>
            let ⟨i, caseBits, hGetBr, hEvC⟩ := hBr
            have hBrEdge := list_all_getElem? hBrAll hGetBr
            dsimp only at hBrEdge
            have hRefMatch := refineSwitchBranchEnv_bool_sound hMatch hD hEvC
            exact checkConstEdge_sound hRefMatch hBrEdge hLt
      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

/-! #### Part 3C: `constPropOperand`, `rewriteInstSimplifySingleStmt`,
`matchBoolDoubleNotSecond?`, and `InstSimplifyAt` -/

private theorem constPropOperand_evalSlot_eq {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals : List LocalSlot} (opnd : Operand)
    (hMatch : LocalsMatchConstEnv bodyLocals env locals) :
    evalOperandToSlot bodyLocals locals (constPropOperand bodyLocals env opnd) =
      evalOperandToSlot bodyLocals locals opnd := by
  cases opnd with
  | move _ | constant _ => rfl
  | copy p =>
    dsimp [constPropOperand]
    cases hPE : p.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rfl
      | some ty =>
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rfl
        | some abs =>
          cases abs with
          | bottom | liveUnknown | liveUninit | dead => rfl
          | knownConst cTy cLit =>
            dsimp only
            cases hVal : validTypedConstOperand ty ⟨cTy, cLit⟩ with
            | false => rw [if_bool_false rfl]
            | true =>
              rw [if_bool_true rfl]
              let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId
                (by rw [hMatch.2.1]; exact getElem?_some_lt hTy)
              let ⟨_, v, hsl, hEvC, _⟩ :=
                hMatch.2.2 p.localId ty (.knownConst cTy cLit) sl hTy hAbs hSl
              subst hsl
              dsimp [evalOperandToSlot]
              rw [hPE, hTy, hSl, hEvC]; rfl

private theorem constPropOperand_evalPrim_eq {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals : List LocalSlot} (opnd : Operand)
    (hMatch : LocalsMatchConstEnv bodyLocals env locals) :
    evalPrimitiveOperand bodyLocals locals (constPropOperand bodyLocals env opnd) =
      evalPrimitiveOperand bodyLocals locals opnd := by
  unfold evalPrimitiveOperand
  rw [constPropOperand_evalSlot_eq opnd hMatch]

private theorem constPropRvalue_eval_eq {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals : List LocalSlot}
    (dstTy : MirTy) (rv : Rvalue)
    (hMatch : LocalsMatchConstEnv bodyLocals env locals) :
    evalRvalue bodyLocals locals dstTy (constPropRvalue bodyLocals env rv) =
      evalRvalue bodyLocals locals dstTy rv := by
  cases rv with
  | use o =>
    dsimp [constPropRvalue, evalRvalue]
    rw [constPropOperand_evalSlot_eq o hMatch]
  | unaryOp uop o =>
    dsimp [constPropRvalue, evalRvalue]
    rw [constPropOperand_evalPrim_eq o hMatch]
  | binaryOp bop lhs rhs =>
    dsimp [constPropRvalue, evalRvalue]
    rw [constPropOperand_evalPrim_eq lhs hMatch]
    cases hEL : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rfl
    | ok resL =>
      let ⟨lv, locs1⟩ := resL
      dsimp
      have hMatch1 := deinitMovePrimitiveOperand_sound hMatch hEL
      rw [constPropOperand_evalPrim_eq rhs hMatch1]
  | discriminant _ | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => rfl

private theorem rewriteInstSimplifySingleStmt_eval_eq {bSrc bTgt : Body}
    {env : List ConstAbsSlot} {frame : FrameState} {cm : CallerMemory}
    (s : StatementKind)
    (hLocEq : bSrc.locals = bTgt.locals)
    (hMatch : LocalsMatchConstEnv bSrc.locals env frame.locals) :
    evalStatement bSrc frame cm s =
      evalStatement bTgt frame cm (rewriteInstSimplifySingleStmt bSrc.locals env s) := by
  cases s with
  | nop | unsupported | storageDead _ => rfl
  | storageLive id =>
    dsimp [rewriteInstSimplifySingleStmt, evalStatement]
    rw [← hLocEq]
  | assign dst rv =>
    dsimp [rewriteInstSimplifySingleStmt]
    cases hPE : dst.projection.isEmpty with
    | false =>
      dsimp [evalStatement]; rw [hPE]; rfl
    | true =>
      dsimp
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
      | none =>
        dsimp [evalStatement]; rw [hPE, ← hLocEq, hTy]
      | some dstTy =>
        dsimp [evalStatement]
        rw [hPE, ← hLocEq, hTy]; dsimp
        rw [foldAlgNeutralRvalue_eval_eq (localsMatchConstEnv_wt hMatch),
            constPropRvalue_eval_eq dstTy rv hMatch]

private theorem rewriteInstSimplifyTerm_eval_eq {bSrc bTgt : Body}
    {bbSrc : BasicBlock} {stmts' : List StatementKind}
    {exitEnv : List ConstAbsSlot} {frame : FrameState} {cm : CallerMemory}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hMatch : LocalsMatchConstEnv bSrc.locals exitEnv frame.locals) :
    evalTerminator bSrc bbSrc frame cm =
      evalTerminator bTgt
        { statements := stmts'
          terminator := rewriteInstSimplifyTerm bSrc.locals exitEnv bbSrc.terminator
          cleanup := bbSrc.cleanup }
        frame cm := by
  cases hTm : bbSrc.terminator with
  | goto _ | return_ | unreachable | unwindResume
  | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    unfold evalTerminator; dsimp; rw [hTm]; rfl
  | switchInt discr targets =>
    unfold evalTerminator; dsimp; rw [hTm]; dsimp [rewriteInstSimplifyTerm]
    rw [← hLocEq, constPropOperand_evalPrim_eq discr hMatch]

private theorem matchBoolDoubleNotSecond?_elim {bodyLocals : List MirTy}
    {s₁ s₂ t₂ : StatementKind}
    (h : matchBoolDoubleNotSecond? bodyLocals s₁ s₂ = some t₂) :
    ∃ tmp bPlace dst tmp',
      s₁ = .assign tmp (.unaryOp .not (.copy bPlace)) ∧
      s₂ = .assign dst (.unaryOp .not (.copy tmp')) ∧
      t₂ = .assign dst (.use (.copy bPlace)) ∧
      bPlace.projection.isEmpty = true ∧
      tmp.projection.isEmpty = true ∧
      tmp'.projection.isEmpty = true ∧
      dst.projection.isEmpty = true ∧
      tmp.localId = tmp'.localId ∧
      tmp.localId ≠ bPlace.localId ∧
      Trusted.MirSemantics.getElem? bodyLocals bPlace.localId = some .bool ∧
      Trusted.MirSemantics.getElem? bodyLocals tmp.localId = some .bool ∧
      Trusted.MirSemantics.getElem? bodyLocals dst.localId = some .bool := by
  cases s₁ with
  | nop | storageLive _ | storageDead _ | unsupported => cases h
  | assign tmp rv₁ =>
    cases rv₁ with
    | use _ | binaryOp _ _ _ | discriminant _ | ref _ _ | addressOf _ _
    | aggregateTuple _ | unsupported => cases h
    | unaryOp uop₁ op₁ =>
      cases uop₁ with
      | neg | ptrMetadata => cases h
      | not =>
        cases op₁ with
        | move _ | constant _ => cases h
        | copy bPlace =>
          cases s₂ with
          | nop | storageLive _ | storageDead _ | unsupported => cases h
          | assign dst rv₂ =>
            cases rv₂ with
            | use _ | binaryOp _ _ _ | discriminant _ | ref _ _ | addressOf _ _
            | aggregateTuple _ | unsupported => cases h
            | unaryOp uop₂ op₂ =>
              cases uop₂ with
              | neg | ptrMetadata => cases h
              | not =>
                cases op₂ with
                | move _ | constant _ => cases h
                | copy tmp' =>
                  dsimp [matchBoolDoubleNotSecond?] at h
                  cases hG : (bPlace.projection.isEmpty &&
                      tmp.projection.isEmpty &&
                      tmp'.projection.isEmpty &&
                      dst.projection.isEmpty &&
                      Nat.beq tmp.localId tmp'.localId &&
                      !Nat.beq tmp.localId bPlace.localId) with
                  | false => rw [hG] at h; cases h
                  | true =>
                    rw [hG, if_bool_true rfl] at h
                    let ⟨g15, g6⟩ := bool_and_true hG
                    let ⟨g14, g5⟩ := bool_and_true g15
                    let ⟨g13, g4⟩ := bool_and_true g14
                    let ⟨g12, g3⟩ := bool_and_true g13
                    let ⟨g1, g2⟩ := bool_and_true g12
                    cases hTb : Trusted.MirSemantics.getElem? bodyLocals bPlace.localId with
                    | none => rw [hTb] at h; cases h
                    | some tyB =>
                      rw [hTb] at h
                      cases tyB with
                      | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h
                      | bool =>
                        cases hTt : Trusted.MirSemantics.getElem? bodyLocals tmp.localId with
                        | none => rw [hTt] at h; cases h
                        | some tyT =>
                          rw [hTt] at h
                          cases tyT with
                          | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h
                          | bool =>
                            cases hTd : Trusted.MirSemantics.getElem? bodyLocals dst.localId with
                            | none => rw [hTd] at h; cases h
                            | some tyD =>
                              rw [hTd] at h
                              cases tyD with
                              | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h
                              | bool =>
                                injection h with eT2
                                exact ⟨tmp, bPlace, dst, tmp', rfl, rfl, eT2.symm,
                                  g1, g2, g3, g4, nat_beq_eq g5,
                                  nat_ne_of_beq_false (bool_not_true g6),
                                  hTb, hTt, hTd⟩

private theorem rewriteInstSimplifySingleStmt_storage (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (s : StatementKind) :
    NonStorageOrEqStmt s (rewriteInstSimplifySingleStmt bodyLocals env s) := by
  cases s with
  | nop | storageLive _ | storageDead _ | unsupported => exact Or.inl rfl
  | assign dst rv =>
    dsimp [rewriteInstSimplifySingleStmt]
    cases dst.projection.isEmpty with
    | false => exact Or.inl rfl
    | true =>
      dsimp
      cases Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => exact Or.inl rfl
      | some _ => exact Or.inr ⟨True.intro, True.intro⟩

private theorem rewriteInstSimplifyStmts_storage {bodyLocals : List MirTy} :
    ∀ {ss : List StatementKind} {env exitEnv : List ConstAbsSlot}
      {ss' : List StatementKind},
      rewriteInstSimplifyStmts bodyLocals env ss = some (ss', exitEnv) →
      StmtListStoragePreserved ss ss'
  | [], env, exitEnv, ss', h => by
    injection h with e; injection e with e1 _; subst e1; exact True.intro
  | [s₁], env, exitEnv, ss', h => by
    dsimp [rewriteInstSimplifyStmts] at h
    cases hStp : stepPlainStmtConst bodyLocals env s₁ with
    | none => rw [hStp] at h; cases h
    | some ex =>
      rw [hStp] at h; injection h with e; injection e with e1 _; subst e1
      exact ⟨rewriteInstSimplifySingleStmt_storage bodyLocals env s₁, True.intro⟩
  | s₁ :: s₂ :: rest, env, exitEnv, ss', h => by
    dsimp [rewriteInstSimplifyStmts] at h
    cases hDN : matchBoolDoubleNotSecond? bodyLocals s₁ s₂ with
    | none =>
      rw [hDN] at h; dsimp at h
      cases hStp1 : stepPlainStmtConst bodyLocals env s₁ with
      | none => rw [hStp1] at h; cases h
      | some env₁ =>
        rw [hStp1] at h; dsimp at h
        cases hRec : rewriteInstSimplifyStmts bodyLocals env₁ (s₂ :: rest) with
        | none => rw [hRec] at h; cases h
        | some pr =>
          let ⟨rest', ex⟩ := pr
          rw [hRec] at h; injection h with e; injection e with e1 e2
          subst e1; subst e2
          exact ⟨rewriteInstSimplifySingleStmt_storage bodyLocals env s₁,
                 rewriteInstSimplifyStmts_storage hRec⟩
    | some t₂ =>
      rw [hDN] at h; dsimp at h
      let ⟨tmp, bPlace, dst, tmp', hs1, hs2, ht2, _, _, _, _, _, _, _, _, _⟩ :=
        matchBoolDoubleNotSecond?_elim hDN
      cases hStp1 : stepPlainStmtConst bodyLocals env s₁ with
      | none => rw [hStp1] at h; cases h
      | some env₁ =>
        rw [hStp1] at h; dsimp at h
        cases hStp2 : stepPlainStmtConst bodyLocals env₁ s₂ with
        | none => rw [hStp2] at h; cases h
        | some env₂ =>
          rw [hStp2] at h; dsimp at h
          cases hRec : rewriteInstSimplifyStmts bodyLocals env₂ rest with
          | none => rw [hRec] at h; cases h
          | some pr =>
            let ⟨rest', ex⟩ := pr
            rw [hRec] at h; injection h with e; injection e with e1 e2
            subst e1; subst e2
            have hS2 : NonStorageOrEqStmt s₂ t₂ := by
              rw [hs2, ht2]; exact Or.inr ⟨True.intro, True.intro⟩
            exact ⟨rewriteInstSimplifySingleStmt_storage bodyLocals env s₁,
                   hS2, rewriteInstSimplifyStmts_storage hRec⟩

private noncomputable def DoubleNotAfterFirst (locals : List LocalSlot)
    (bId tmpId : LocalId) : Prop :=
  ∃ b : Bool,
    Trusted.MirSemantics.getElem? locals bId = some (.live (some (.bool b))) ∧
    Trusted.MirSemantics.getElem? locals tmpId = some (.live (some (.bool (!b))))

private inductive InstSimplifyAt (bodyLocals : List MirTy) :
    List StatementKind → List StatementKind → List ConstAbsSlot →
    Nat → List LocalSlot → Prop where
  | atEnd {exitEnv locals}
      (hMatch : LocalsMatchConstEnv bodyLocals exitEnv locals) :
      InstSimplifyAt bodyLocals [] [] exitEnv 0 locals
  | atSingle0 {env exitEnv s₁ locals}
      (hStepC : stepPlainStmtConst bodyLocals env s₁ = some exitEnv)
      (hMatch : LocalsMatchConstEnv bodyLocals env locals) :
      InstSimplifyAt bodyLocals [s₁]
        [rewriteInstSimplifySingleStmt bodyLocals env s₁] exitEnv 0 locals
  | atCons0 {env env₁ exitEnv s₁ rest rest' locals}
      (hStepC : stepPlainStmtConst bodyLocals env s₁ = some env₁)
      (hRest : rewriteInstSimplifyStmts bodyLocals env₁ rest = some (rest', exitEnv))
      (hMatch : LocalsMatchConstEnv bodyLocals env locals) :
      InstSimplifyAt bodyLocals (s₁ :: rest)
        (rewriteInstSimplifySingleStmt bodyLocals env s₁ :: rest') exitEnv 0 locals
  | atDoubleNot0 {env env₁ env₂ exitEnv s₁ s₂ t₂ rest rest' locals}
      (hDN : matchBoolDoubleNotSecond? bodyLocals s₁ s₂ = some t₂)
      (hStepC1 : stepPlainStmtConst bodyLocals env s₁ = some env₁)
      (hStepC2 : stepPlainStmtConst bodyLocals env₁ s₂ = some env₂)
      (hRest : rewriteInstSimplifyStmts bodyLocals env₂ rest = some (rest', exitEnv))
      (hMatch : LocalsMatchConstEnv bodyLocals env locals) :
      InstSimplifyAt bodyLocals (s₁ :: s₂ :: rest)
        (rewriteInstSimplifySingleStmt bodyLocals env s₁ :: t₂ :: rest')
        exitEnv 0 locals
  | atDoubleNot1 {env₁ env₂ exitEnv s₁ t₁ s₂ t₂ rest rest' locals}
      (hDN : matchBoolDoubleNotSecond? bodyLocals s₁ s₂ = some t₂)
      (hStepC2 : stepPlainStmtConst bodyLocals env₁ s₂ = some env₂)
      (hRest : rewriteInstSimplifyStmts bodyLocals env₂ rest = some (rest', exitEnv))
      (hMatch : LocalsMatchConstEnv bodyLocals env₁ locals)
      (hMid : ∀ tmp bPlace,
        s₁ = .assign tmp (.unaryOp .not (.copy bPlace)) →
        DoubleNotAfterFirst locals bPlace.localId tmp.localId) :
      InstSimplifyAt bodyLocals (s₁ :: s₂ :: rest) (t₁ :: t₂ :: rest')
        exitEnv 1 locals
  | atShift1 {s₁ t₁ rest rest' exitEnv k locals}
      (hSub : InstSimplifyAt bodyLocals rest rest' exitEnv k locals) :
      InstSimplifyAt bodyLocals (s₁ :: rest) (t₁ :: rest') exitEnv (k + 1) locals

private theorem instSimplifyAt_entry {bodyLocals : List MirTy} :
    ∀ {ss : List StatementKind} {env exitEnv : List ConstAbsSlot}
      {ss' : List StatementKind} {locals : List LocalSlot},
      rewriteInstSimplifyStmts bodyLocals env ss = some (ss', exitEnv) →
      LocalsMatchConstEnv bodyLocals env locals →
      InstSimplifyAt bodyLocals ss ss' exitEnv 0 locals
  | [], env, exitEnv, ss', locals, h, hM => by
    injection h with e; injection e with e1 e2; subst e1; subst e2
    exact .atEnd hM
  | [s₁], env, exitEnv, ss', locals, h, hM => by
    dsimp [rewriteInstSimplifyStmts] at h
    cases hStp : stepPlainStmtConst bodyLocals env s₁ with
    | none => rw [hStp] at h; cases h
    | some ex =>
      rw [hStp] at h; injection h with e; injection e with e1 e2
      subst e1; subst e2
      exact .atSingle0 hStp hM
  | s₁ :: s₂ :: rest, env, exitEnv, ss', locals, h, hM => by
    dsimp [rewriteInstSimplifyStmts] at h
    cases hDN : matchBoolDoubleNotSecond? bodyLocals s₁ s₂ with
    | none =>
      rw [hDN] at h; dsimp at h
      cases hStp1 : stepPlainStmtConst bodyLocals env s₁ with
      | none => rw [hStp1] at h; cases h
      | some env₁ =>
        rw [hStp1] at h; dsimp at h
        cases hRec : rewriteInstSimplifyStmts bodyLocals env₁ (s₂ :: rest) with
        | none => rw [hRec] at h; cases h
        | some pr =>
          let ⟨rest', ex⟩ := pr
          rw [hRec] at h; injection h with e; injection e with e1 e2
          subst e1; subst e2
          exact .atCons0 hStp1 hRec hM
    | some t₂ =>
      rw [hDN] at h; dsimp at h
      cases hStp1 : stepPlainStmtConst bodyLocals env s₁ with
      | none => rw [hStp1] at h; cases h
      | some env₁ =>
        rw [hStp1] at h; dsimp at h
        cases hStp2 : stepPlainStmtConst bodyLocals env₁ s₂ with
        | none => rw [hStp2] at h; cases h
        | some env₂ =>
          rw [hStp2] at h; dsimp at h
          cases hRec : rewriteInstSimplifyStmts bodyLocals env₂ rest with
          | none => rw [hRec] at h; cases h
          | some pr =>
            let ⟨rest', ex⟩ := pr
            rw [hRec] at h; injection h with e; injection e with e1 e2
            subst e1; subst e2
            exact .atDoubleNot0 hDN hStp1 hStp2 hRec hM

private theorem doubleNot_first_step_establish {bSrc : Body} {frame : FrameState}
    {cm : CallerMemory} {tmp bPlace : Place} {locs' : List LocalSlot}
    (hWt : LocalsWellTyped bSrc.locals frame.locals)
    (hPEb : bPlace.projection.isEmpty = true)
    (hPEt : tmp.projection.isEmpty = true)
    (hNe : tmp.localId ≠ bPlace.localId)
    (hTb : Trusted.MirSemantics.getElem? bSrc.locals bPlace.localId = some .bool)
    (hTt : Trusted.MirSemantics.getElem? bSrc.locals tmp.localId = some .bool)
    (hEv : evalStatement bSrc frame cm (.assign tmp (.unaryOp .not (.copy bPlace))) =
      .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
              callerMem := cm }) :
    DoubleNotAfterFirst locs' bPlace.localId tmp.localId := by
  dsimp [evalStatement] at hEv
  rw [hPEt, hTt] at hEv; dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot] at hEv
  rw [hPEb, hTb] at hEv; dsimp at hEv
  cases hSlB : Trusted.MirSemantics.getElem? frame.locals bPlace.localId with
  | none => rw [hSlB] at hEv; cases hEv
  | some slB =>
    rw [hSlB] at hEv
    cases slB with
    | dead => cases hEv
    | live optB =>
      dsimp at hEv
      cases optB with
      | none => cases hEv
      | some vb =>
        have hChkB : checkVal vb .bool = true :=
          hWt.2 bPlace.localId .bool (.live (some vb)) hTb hSlB
        let ⟨b, hvb⟩ := checkVal_bool_iff.mp hChkB
        subst hvb
        have hChkNotB : checkVal (.bool (!b)) .bool = true := rfl
        rw [isPrimitiveReadableTy_bool] at hEv
        unfold evalUnOp writePlace at hEv
        dsimp at hEv
        rw [hChkNotB] at hEv
        dsimp at hEv
        cases hSlT : Trusted.MirSemantics.getElem? frame.locals tmp.localId with
        | none => rw [hSlT] at hEv; cases hEv
        | some slT =>
          rw [hSlT] at hEv
          cases slT with
          | dead => cases hEv
          | live _ =>
            cases hSet : setElem? frame.locals tmp.localId (.live (some (.bool (!b)))) with
            | none => rw [hSet] at hEv; cases hEv
            | some l1 =>
              rw [hSet] at hEv
              injection hEv with eSt; injection eSt with eFs _
              injection eFs with eF _
              have hLocsEq : l1 = locs' := congrArg FrameState.locals eF
              subst hLocsEq
              refine ⟨b, ?_, setElem?_getElem?_same hSet⟩
              rw [setElem?_getElem?_ne hSet (Ne.symm hNe)]
              exact hSlB

private theorem doubleNot_second_eval_eq {bSrc bTgt : Body}
    {frame : FrameState} {cm : CallerMemory}
    {s₁ s₂ t₂ : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hDN : matchBoolDoubleNotSecond? bSrc.locals s₁ s₂ = some t₂)
    (hMid : ∀ tmp bPlace,
      s₁ = .assign tmp (.unaryOp .not (.copy bPlace)) →
      DoubleNotAfterFirst frame.locals bPlace.localId tmp.localId) :
    evalStatement bSrc frame cm s₂ = evalStatement bTgt frame cm t₂ := by
  let ⟨tmp, bPlace, dst, tmp', hs1, hs2, ht2, hPEb, _, hPEt', hPEd,
       hTmpEq, _, hTb, hTt, hTd⟩ := matchBoolDoubleNotSecond?_elim hDN
  let ⟨b, hGetB, hGetT⟩ := hMid tmp bPlace hs1
  subst hs2; subst ht2
  dsimp [evalStatement]
  rw [hPEd, ← hLocEq, hTd]; dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
  rw [hPEt', ← hTmpEq, hTt, hGetT, hPEb, hTb, hGetB]
  dsimp
  rw [isPrimitiveReadableTy_bool, mirTy_beq_refl .bool]
  unfold evalUnOp
  dsimp
  have hNotNot : (!(!b)) = b := by cases b <;> rfl
  rw [hNotNot]

private theorem instSimplifyAt_step_aux {bSrc bTgt : Body}
    {ss ss' : List StatementKind} {exitEnv : List ConstAbsSlot}
    {idx : Nat} {locs0 : List LocalSlot}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hAt : InstSimplifyAt bSrc.locals ss ss' exitEnv idx locs0) :
    ∀ (frame : FrameState) (cm : CallerMemory),
      frame.stmtIdx = idx →
      frame.locals = locs0 →
      (Trusted.MirSemantics.getElem? ss frame.stmtIdx = none ∧
       Trusted.MirSemantics.getElem? ss' frame.stmtIdx = none ∧
       Nat.beq frame.stmtIdx ss.length = true ∧
       Nat.beq frame.stmtIdx ss'.length = true ∧
       LocalsMatchConstEnv bSrc.locals exitEnv frame.locals) ∨
      (∃ sSrc sTgt,
        Trusted.MirSemantics.getElem? ss frame.stmtIdx = some sSrc ∧
        Trusted.MirSemantics.getElem? ss' frame.stmtIdx = some sTgt ∧
        evalStatement bSrc frame cm sSrc = evalStatement bTgt frame cm sTgt ∧
        ∀ s', evalStatement bSrc frame cm sSrc = .step s' →
          ∃ locs',
            s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
                   callerMem := cm } ∧
            InstSimplifyAt bSrc.locals ss ss' exitEnv (frame.stmtIdx + 1) locs') := by
  induction hAt with
  | atEnd hM =>
    intro frame cm hIdx hLocs
    exact Or.inl ⟨by rw [hIdx]; rfl, by rw [hIdx]; rfl,
                  by rw [hIdx]; rfl, by rw [hIdx]; rfl,
                  by rw [hLocs]; exact hM⟩
  | @atSingle0 env ex s₁ locs hStepC hM =>
    intro frame cm hIdx hLocs
    have hMF : LocalsMatchConstEnv bSrc.locals env frame.locals := by
      rw [hLocs]; exact hM
    right
    refine ⟨s₁, rewriteInstSimplifySingleStmt bSrc.locals env s₁,
      by rw [hIdx]; rfl, by rw [hIdx]; rfl,
      rewriteInstSimplifySingleStmt_eval_eq s₁ hLocEq hMF, ?_⟩
    intro s' hEv
    let ⟨locs', hs', hM'⟩ := stepPlainStmtConst_sound hMF hStepC hEv
    exact ⟨locs', hs', by rw [hIdx]; exact .atShift1 (.atEnd hM')⟩
  | @atCons0 env env₁ ex s₁ rest rest' locs hStepC hRest hM =>
    intro frame cm hIdx hLocs
    have hMF : LocalsMatchConstEnv bSrc.locals env frame.locals := by
      rw [hLocs]; exact hM
    right
    refine ⟨s₁, rewriteInstSimplifySingleStmt bSrc.locals env s₁,
      by rw [hIdx]; rfl, by rw [hIdx]; rfl,
      rewriteInstSimplifySingleStmt_eval_eq s₁ hLocEq hMF, ?_⟩
    intro s' hEv
    let ⟨locs', hs', hM'⟩ := stepPlainStmtConst_sound hMF hStepC hEv
    exact ⟨locs', hs', by rw [hIdx]; exact .atShift1 (instSimplifyAt_entry hRest hM')⟩
  | @atDoubleNot0 env env₁ env₂ ex s₁ s₂ t₂ rest rest' locs hDN hStepC1 hStepC2 hRest hM =>
    intro frame cm hIdx hLocs
    have hMF : LocalsMatchConstEnv bSrc.locals env frame.locals := by
      rw [hLocs]; exact hM
    right
    refine ⟨s₁, rewriteInstSimplifySingleStmt bSrc.locals env s₁,
      by rw [hIdx]; rfl, by rw [hIdx]; rfl,
      rewriteInstSimplifySingleStmt_eval_eq s₁ hLocEq hMF, ?_⟩
    intro s' hEv
    let ⟨locs', hs', hM1⟩ := stepPlainStmtConst_sound hMF hStepC1 hEv
    refine ⟨locs', hs', ?_⟩
    rw [hIdx]
    refine .atDoubleNot1 hDN hStepC2 hRest hM1 ?_
    intro tmp bPlace hs1Eq
    let ⟨tmp0, bPlace0, _, _, hs1_0, _, _, hPEb, hPEt, _, _, _, hNe, hTb, hTt, _⟩ :=
      matchBoolDoubleNotSecond?_elim hDN
    rw [hs1Eq] at hs1_0
    injection hs1_0 with eTmp eRv
    injection eRv with _ eOp
    injection eOp with eBP
    subst eTmp; subst eBP
    have hEv' : evalStatement bSrc frame cm (.assign tmp (.unaryOp .not (.copy bPlace))) =
        .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
                callerMem := cm } := by
      rw [← hs1Eq, ← hs']; exact hEv
    exact doubleNot_first_step_establish (localsMatchConstEnv_wt hMF)
      hPEb hPEt hNe hTb hTt hEv'
  | @atDoubleNot1 env₁ env₂ ex s₁ t₁ s₂ t₂ rest rest' locs hDN hStepC2 hRest hM1 hMid =>
    intro frame cm hIdx hLocs
    have hMF1 : LocalsMatchConstEnv bSrc.locals env₁ frame.locals := by
      rw [hLocs]; exact hM1
    have hMidF : ∀ tmp bPlace,
        s₁ = .assign tmp (.unaryOp .not (.copy bPlace)) →
        DoubleNotAfterFirst frame.locals bPlace.localId tmp.localId := by
      rw [hLocs]; exact hMid
    right
    refine ⟨s₂, t₂,
      by rw [hIdx]; rfl, by rw [hIdx]; rfl,
      doubleNot_second_eval_eq hLocEq hDN hMidF, ?_⟩
    intro s' hEv
    let ⟨locs', hs', hM2⟩ := stepPlainStmtConst_sound hMF1 hStepC2 hEv
    exact ⟨locs', hs', by rw [hIdx]; exact .atShift1 (.atShift1 (instSimplifyAt_entry hRest hM2))⟩
  | @atShift1 s₁ t₁ rest rest' ex k locs hSub ih =>
    intro frame cm hIdx hLocs
    let fSub : FrameState := { frame with stmtIdx := k }
    cases ih fSub cm rfl hLocs with
    | inl hEnd =>
      let ⟨hN1, hN2, hB1, hB2, hM⟩ := hEnd
      left
      refine ⟨?_, ?_, ?_, ?_, hM⟩
      · rw [hIdx]; exact hN1
      · rw [hIdx]; exact hN2
      · rw [hIdx]; dsimp [List.length]; rw [nat_beq_succ_succ]; exact hB1
      · rw [hIdx]; dsimp [List.length]; rw [nat_beq_succ_succ]; exact hB2
    | inr hMid =>
      let ⟨sSrc, sTgt, hG1, hG2, hEvEq, hNext⟩ := hMid
      right
      have hEvShift : ∀ (b : Body) (st : StatementKind),
          evalStatement b frame cm st =
            match evalStatement b fSub cm st with
            | .step { frames := [f'], callerMem := c' } =>
              .step { frames := [{ f' with stmtIdx := frame.stmtIdx + 1 }], callerMem := c' }
            | r => r := by
        intro b st
        cases st with
        | nop => rfl
        | unsupported => rfl
        | storageLive id =>
          dsimp [evalStatement]
          cases Trusted.MirSemantics.getElem? b.locals id with
          | none => rfl
          | some ty =>
            dsimp
            cases setElem? frame.locals id (liveUninitSlot ty) <;> rfl
        | storageDead id =>
          dsimp [evalStatement]
          cases Nat.beq id 0 with
          | true => rfl
          | false =>
            dsimp
            cases setElem? frame.locals id .dead <;> rfl
        | assign dst rv =>
          dsimp [evalStatement]
          cases dst.projection.isEmpty with
          | false => rfl
          | true =>
            dsimp
            cases Trusted.MirSemantics.getElem? b.locals dst.localId with
            | none => rfl
            | some ty =>
              dsimp
              cases evalRvalue b.locals frame.locals ty rv with
              | error _ => rfl
              | ok res =>
                let ⟨val, l1⟩ := res
                dsimp
                cases writePlace l1 dst.localId ty val <;> rfl
      refine ⟨sSrc, sTgt, by rw [hIdx]; exact hG1, by rw [hIdx]; exact hG2, ?_, ?_⟩
      · rw [hEvShift bSrc sSrc, hEvShift bTgt sTgt, hEvEq]
      · intro s' hEvF
        rw [hEvShift bSrc sSrc] at hEvF
        cases hEvSub : evalStatement bSrc fSub cm sSrc with
        | done _ | fault _ => rw [hEvSub] at hEvF; cases hEvF
        | step sSub =>
          let ⟨locs', hsSub, hAtNext⟩ := hNext sSub hEvSub
          rw [hEvSub, hsSub] at hEvF
          dsimp at hEvF
          injection hEvF with eS'
          exact ⟨locs', eS'.symm, by rw [hIdx]; exact .atShift1 hAtNext⟩

private theorem instSimplifyAt_step {bSrc bTgt : Body}
    {ss ss' : List StatementKind} {exitEnv : List ConstAbsSlot}
    {frame : FrameState} {cm : CallerMemory}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hAt : InstSimplifyAt bSrc.locals ss ss' exitEnv frame.stmtIdx frame.locals) :
    (Trusted.MirSemantics.getElem? ss frame.stmtIdx = none ∧
     Trusted.MirSemantics.getElem? ss' frame.stmtIdx = none ∧
     Nat.beq frame.stmtIdx ss.length = true ∧
     Nat.beq frame.stmtIdx ss'.length = true ∧
     LocalsMatchConstEnv bSrc.locals exitEnv frame.locals) ∨
    (∃ sSrc sTgt,
      Trusted.MirSemantics.getElem? ss frame.stmtIdx = some sSrc ∧
      Trusted.MirSemantics.getElem? ss' frame.stmtIdx = some sTgt ∧
      evalStatement bSrc frame cm sSrc = evalStatement bTgt frame cm sTgt ∧
      ∀ s', evalStatement bSrc frame cm sSrc = .step s' →
        ∃ locs',
          s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
                 callerMem := cm } ∧
          InstSimplifyAt bSrc.locals ss ss' exitEnv (frame.stmtIdx + 1) locs') :=
  instSimplifyAt_step_aux hLocEq hAt frame cm rfl rfl

/-! #### Part 3D: Block & Program Lifting for `.instSimplifyAlgAndConst` -/

private theorem applyInstSimplifyBlocks_props {b : Body} {cert : BodyConstCert} :
    ∀ {base : Nat} {bbs bbs' : List BasicBlock},
      applyInstSimplifyBlocks b cert base bbs = some bbs' →
      bbs.length = bbs'.length ∧
      (∀ i bb₁ bb₂,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? bbs' i = some bb₂ →
        StmtListStoragePreserved bb₁.statements bb₂.statements ∧
        bb₁.cleanup = bb₂.cleanup) ∧
      (∀ i bb₁ entryEnv,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? cert (base + i) = some (some entryEnv) →
        ∃ bb₂ stmts' exitEnv,
          Trusted.MirSemantics.getElem? bbs' i = some bb₂ ∧
          entryEnv.length = b.locals.length ∧
          rewriteInstSimplifyStmts b.locals entryEnv bb₁.statements =
            some (stmts', exitEnv) ∧
          checkConstTerminatorEdges b.locals b.basicBlocks.length cert exitEnv
            bb₁.terminator = true ∧
          bb₂ = {
            statements := stmts'
            terminator := rewriteInstSimplifyTerm b.locals exitEnv bb₁.terminator
            cleanup := bb₁.cleanup
          })
  | _, [], bbs', h => by
    injection h with e; subst e
    exact ⟨rfl, (fun _ _ _ hG _ => by cases hG), (fun _ _ _ hG _ => by cases hG)⟩
  | base, bb :: rest, bbs', h => by
    dsimp [applyInstSimplifyBlocks] at h
    cases hC : Trusted.MirSemantics.getElem? cert base with
    | none => rw [hC] at h; cases h
    | some optE =>
      rw [hC] at h
      cases optE with
      | none =>
        dsimp at h
        cases hRec : applyInstSimplifyBlocks b cert (base + 1) rest with
        | none => rw [hRec] at h; cases h
        | some rest' =>
          rw [hRec] at h; injection h with e; subst e
          let ⟨hLen, hStCl, hAct⟩ := applyInstSimplifyBlocks_props hRec
          refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
          · intro i bb₁ bb₂ h1 h2
            cases i with
            | zero =>
              injection h1 with e1; injection h2 with e2; subst e1; subst e2
              have hSelf : ∀ ss : List StatementKind, StmtListStoragePreserved ss ss := by
                intro ss; induction ss with
                | nil => exact True.intro
                | cons _ rs ihr => exact ⟨Or.inl rfl, ihr⟩
              exact ⟨hSelf bb.statements, rfl⟩
            | succ k => exact hStCl k bb₁ bb₂ h1 h2
          · intro i bb₁ entryEnv h1 hCE
            cases i with
            | zero => rw [Nat.add_zero, hC] at hCE; cases hCE
            | succ k =>
              have hAdd : (base + 1) + k = base + (k + 1) := by
                rw [Nat.add_assoc, Nat.add_comm 1 k]
              rw [← hAdd] at hCE
              exact hAct k bb₁ entryEnv h1 hCE
      | some entryEnv =>
        dsimp at h
        cases hELen : Nat.beq entryEnv.length b.locals.length with
        | false => rw [hELen] at h; cases h
        | true =>
          rw [hELen] at h; dsimp at h
          cases hRew : rewriteInstSimplifyStmts b.locals entryEnv bb.statements with
          | none => rw [hRew] at h; cases h
          | some pr =>
            let ⟨stmts', exitEnv⟩ := pr
            rw [hRew] at h; dsimp at h
            cases hEdg : checkConstTerminatorEdges b.locals b.basicBlocks.length cert exitEnv bb.terminator with
            | false => rw [hEdg] at h; cases h
            | true =>
              rw [hEdg] at h; dsimp at h
              cases hRec : applyInstSimplifyBlocks b cert (base + 1) rest with
              | none => rw [hRec] at h; cases h
              | some rest' =>
                rw [hRec] at h; injection h with e; subst e
                let ⟨hLen, hStCl, hAct⟩ := applyInstSimplifyBlocks_props hRec
                refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
                · intro i bb₁ bb₂ h1 h2
                  cases i with
                  | zero =>
                    injection h1 with e1; injection h2 with e2; subst e1; subst e2
                    exact ⟨rewriteInstSimplifyStmts_storage hRew, rfl⟩
                  | succ k => exact hStCl k bb₁ bb₂ h1 h2
                · intro i bb₁ eEnv h1 hCE
                  cases i with
                  | zero =>
                    injection h1 with e1; subst e1
                    rw [Nat.add_zero, hC] at hCE; injection hCE with eE
                    injection eE with eE'; subst eE'
                    exact ⟨_, stmts', exitEnv, rfl, nat_beq_eq hELen, hRew, hEdg, rfl⟩
                  | succ k =>
                    have hAdd : (base + 1) + k = base + (k + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 k]
                    rw [← hAdd] at hCE
                    exact hAct k bb₁ eEnv h1 hCE

private theorem applyInstSimplifyAlgAndConstBody_props {cert : BodyConstCert}
    {bSrc bTgt : Body}
    (hApply : applyInstSimplifyAlgAndConstBody cert bSrc = some bTgt) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) ∧
    (bSrc.basicBlocks.isEmpty = false →
      ∃ env₀, Trusted.MirSemantics.getElem? cert 0 = some (some env₀) ∧
        constEnvImplies (initConstEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
    applyInstSimplifyBlocks bSrc cert 0 bSrc.basicBlocks =
      some bTgt.basicBlocks := by
  unfold applyInstSimplifyAlgAndConstBody at hApply
  cases hCLen : Nat.beq cert.length bSrc.basicBlocks.length with
  | false => rw [hCLen] at hApply; cases hApply
  | true =>
    rw [hCLen] at hApply; dsimp at hApply
    have hProceed :
        ((bSrc.basicBlocks.isEmpty = false →
          ∃ env₀, Trusted.MirSemantics.getElem? cert 0 = some (some env₀) ∧
            constEnvImplies (initConstEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
         ∃ bbs', applyInstSimplifyBlocks bSrc cert 0 bSrc.basicBlocks = some bbs' ∧
           bTgt = { bSrc with basicBlocks := bbs' }) := by
      cases hEmp : bSrc.basicBlocks.isEmpty with
      | true =>
        rw [hEmp] at hApply; dsimp at hApply
        cases hBlk : applyInstSimplifyBlocks bSrc cert 0 bSrc.basicBlocks with
        | none => rw [hBlk] at hApply; cases hApply
        | some bbs' =>
          rw [hBlk] at hApply; injection hApply with eB
          exact ⟨(fun hF => by cases hF), bbs', rfl, eB.symm⟩
      | false =>
        rw [hEmp] at hApply
        cases hC0 : Trusted.MirSemantics.getElem? cert 0 with
        | none => rw [hC0] at hApply; cases hApply
        | some opt0 =>
          rw [hC0] at hApply
          cases opt0 with
          | none => cases hApply
          | some env₀ =>
            cases hImp : constEnvImplies (initConstEnvLoop bSrc 0 bSrc.locals) env₀ with
            | false =>
              have hCT : (!false && !(match (some (some env₀) : Option (Option (List ConstAbsSlot))) with
                  | some (some e) => constEnvImplies (initConstEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = true := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_true hCT] at hApply; cases hApply
            | true =>
              have hCF : (!false && !(match (some (some env₀) : Option (Option (List ConstAbsSlot))) with
                  | some (some e) => constEnvImplies (initConstEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = false := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_false hCF] at hApply
              cases hBlk : applyInstSimplifyBlocks bSrc cert 0 bSrc.basicBlocks with
              | none => rw [hBlk] at hApply; cases hApply
              | some bbs' =>
                rw [hBlk] at hApply; injection hApply with eB
                exact ⟨fun _ => ⟨env₀, rfl, hImp⟩, bbs', rfl, eB.symm⟩
    let ⟨hCert0Fn, bbs', hBlk, eB⟩ := hProceed
    subst eB
    let ⟨hBBLen, hStCl, _⟩ := applyInstSimplifyBlocks_props hBlk
    have hBBEmpty := list_isEmpty_eq_of_length hBBLen
    have hHdr : bodyHeaderEq bSrc { bSrc with basicBlocks := bbs' } = true :=
      bodyHeaderEq_refl bSrc
    have hMarker : ∀ idx,
        hasStorageAnnotation bSrc idx =
          hasStorageAnnotation { bSrc with basicBlocks := bbs' } idx := by
      intro idx
      unfold hasStorageAnnotation; dsimp only
      exact list_any_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 =>
        (stmtListStoragePreserved_props (hStCl i bb₁ bb₂ h1 h2).1).2.1 idx)
    have hBounds :
        storageAnnotationsInBounds bSrc =
          storageAnnotationsInBounds { bSrc with basicBlocks := bbs' } := by
      unfold storageAnnotationsInBounds; dsimp only
      exact list_all_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 =>
        (stmtListStoragePreserved_props (hStCl i bb₁ bb₂ h1 h2).1).2.2
          _ (fun _ _ => rfl) rfl)
    exact ⟨hHdr, hBBLen, hBBEmpty, hBounds,
      fun args => initLocalsLoop_eq_of_storage_eq args rfl rfl (fun idx _ _ => hMarker idx),
      hCert0Fn, hBlk⟩

private noncomputable def InstSimplifyInv (cert : ProgramConstCert)
    (pSrc pTgt : Program) (s : State) : Prop :=
  ∃ f bCert bSrc bTgt,
    s.frames = [f] ∧
    Trusted.MirSemantics.getElem? cert f.defId = some bCert ∧
    Trusted.MirSemantics.getElem? pSrc.bodies f.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies f.defId = some bTgt ∧
    applyInstSimplifyAlgAndConstBody bCert bSrc = some bTgt ∧
    (f.blockIdx < bSrc.basicBlocks.length →
      ∃ bbSrc entryEnv stmts' exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks f.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bCert f.blockIdx = some (some entryEnv) ∧
        rewriteInstSimplifyStmts bSrc.locals entryEnv bbSrc.statements =
          some (stmts', exitEnv) ∧
        InstSimplifyAt bSrc.locals bbSrc.statements stmts' exitEnv
          f.stmtIdx f.locals)

private theorem instSimplify_init_eq {cert : ProgramConstCert}
    {pSrc pTgt : Program} (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applyInstSimplifyAlgAndConstBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    initState pSrc q = initState pTgt q := by
  let ⟨_, _, hEntEq, _⟩ := programHeaderEq_elim hHdr
  have hBBLen : pSrc.bodies.length = pTgt.bodies.length :=
    (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
  refine initState_eq_of_matching_entry q hHdr ?_ ?_
  · rw [← hEntEq]
    exact ⟨fun hN => getElem?_none_of_ge
              (by rw [← hBBLen]; exact getElem?_none_ge hN),
           fun hN => getElem?_none_of_ge
              (by rw [hBBLen]; exact getElem?_none_ge hN)⟩
  · intro bSrc hBS
    let ⟨bCert, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    rw [hEntEq] at hBT
    let ⟨hBHdr, _, hEmp, hBnd, hInitL, _, _⟩ := applyInstSimplifyAlgAndConstBody_props hAp
    exact ⟨bTgt, hBT, hBHdr, hEmp, hBnd, hInitL q.args⟩

private theorem instSimplify_query_iff {cert : ProgramConstCert}
    {pSrc pTgt : Program} (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applyInstSimplifyAlgAndConstBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := instSimplify_init_eq q hLenC hHdr hMap
  apply lockstep_inv_query_iff (Inv := InstSimplifyInv cert pSrc pTgt) hInitEq
  · intro s₀ hIS
    let ⟨_, _, bSrc, hBS, hNotEmp, _, _, _, hArgs, hS0⟩ := initState_ok_elim hIS
    let ⟨bCert, bTgt, hBC, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    let ⟨_, _, _, _, _, hCert0Fn, hBlks⟩ := applyInstSimplifyAlgAndConstBody_props hAp
    let ⟨env₀, hC0, hImp0⟩ := hCert0Fn hNotEmp
    subst hS0
    refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, ?_⟩
    intro h0Lt
    let ⟨bb0, hBB0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
    let ⟨_, _, hAct⟩ := applyInstSimplifyBlocks_props hBlks
    let ⟨_, stmts', exitEnv, _, _, hRew0, _, _⟩ := hAct 0 bb0 env₀ hBB0 hC0
    have hM0 : LocalsMatchConstEnv bSrc.locals env₀ (initLocalsLoop bSrc q.args 0 bSrc.locals) :=
      localsMatchConstEnv_mono hImp0 (initConstEnvLoop_matches hArgs)
    exact ⟨bb0, env₀, stmts', exitEnv, hBB0, hC0, hRew0, instSimplifyAt_entry hRew0 hM0⟩
  · intro s hInv
    let ⟨f, bCert, bSrc, bTgt, hFs, hBC, hBS, hBT, hAp, hBlkInv⟩ := hInv
    let ⟨hBHdr, hBBLen, _, _, _, _, hBlks⟩ := applyInstSimplifyAlgAndConstBody_props hAp
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    let ⟨_, _, hAct⟩ := applyInstSimplifyBlocks_props hBlks
    cases Nat.lt_or_ge f.blockIdx bSrc.basicBlocks.length with
    | inr hGe =>
      have hNoneS := getElem?_none_of_ge hGe
      have hNoneT : Trusted.MirSemantics.getElem? bTgt.basicBlocks f.blockIdx = none :=
        getElem?_none_of_ge (by rw [← hBBLen]; exact hGe)
      have hEvS : evalStep pSrc 0 s = .fault .unsupported := by
        unfold evalStep; rw [hFs]; dsimp; rw [hBS]; dsimp; rw [hNoneS]
      have hEvT : evalStep pTgt 0 s = .fault .unsupported := by
        unfold evalStep; rw [hFs]; dsimp; rw [hBT]; dsimp; rw [hNoneT]
      exact ⟨by rw [hEvS, hEvT], fun _ hSt => by rw [hEvS] at hSt; cases hSt⟩
    | inl hLt =>
      let ⟨bbSrc, entryEnv, stmts', exitEnv, hBBS, hCE, hEntryRew, hAt⟩ := hBlkInv hLt
      have hCE0 : Trusted.MirSemantics.getElem? bCert (0 + f.blockIdx) = some (some entryEnv) := by
        rw [Nat.zero_add]; exact hCE
      let ⟨bbTgt, stmts2, exitEnv2, hBBT, _, hFullRew, hEdges, hBBTEq⟩ :=
        hAct f.blockIdx bbSrc entryEnv hBBS hCE0
      rw [hEntryRew] at hFullRew
      injection hFullRew with ePr; injection ePr with eSts eEx
      subst eSts; subst eEx
      cases instSimplifyAt_step (bSrc := bSrc) (bTgt := bTgt) (cm := s.callerMem) hLocEq hAt with
      | inr hStmtCase =>
        let ⟨sSrc, sTgt, hGS, hGT, hEvStEq, hNextFn⟩ := hStmtCase
        have hGT' : Trusted.MirSemantics.getElem? bbTgt.statements f.stmtIdx = some sTgt := by
          rw [hBBTEq]; exact hGT
        have hEvEq : evalStep pSrc 0 s = evalStep pTgt 0 s := by
          unfold evalStep; rw [hFs]; dsimp; rw [hBS, hBT]; dsimp
          rw [hBBS, hBBT]; dsimp; rw [hGS, hGT']; exact hEvStEq
        refine ⟨hEvEq, fun s' hEvS => ?_⟩
        unfold evalStep at hEvS; rw [hFs] at hEvS; dsimp at hEvS
        rw [hBS] at hEvS; dsimp at hEvS; rw [hBBS] at hEvS; dsimp at hEvS
        rw [hGS] at hEvS
        let ⟨locs', hs', hAtNext⟩ := hNextFn s' hEvS
        subst hs'
        refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, ?_⟩
        intro _
        exact ⟨bbSrc, entryEnv, stmts', exitEnv, hBBS, hCE, hEntryRew, hAtNext⟩
      | inl hTermCase =>
        let ⟨hNS, hNT, hEndS, hEndT, hExitMatch⟩ := hTermCase
        have hNT' : Trusted.MirSemantics.getElem? bbTgt.statements f.stmtIdx = none := by
          rw [hBBTEq]; exact hNT
        have hEndT' : Nat.beq f.stmtIdx bbTgt.statements.length = true := by
          rw [hBBTEq]; exact hEndT
        have hEvSEq : evalStep pSrc 0 s = evalTerminator bSrc bbSrc f s.callerMem := by
          unfold evalStep; rw [hFs]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
          rw [hNS, if_bool_true hEndS]
        have hEvTEq : evalStep pTgt 0 s = evalTerminator bTgt bbTgt f s.callerMem := by
          unfold evalStep; rw [hFs]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
          rw [hNT', if_bool_true hEndT']
        have hTmEq : evalStep pSrc 0 s = evalStep pTgt 0 s := by
          rw [hEvSEq, hEvTEq, hBBTEq]
          exact rewriteInstSimplifyTerm_eval_eq hLocEq hExitMatch
        refine ⟨hTmEq, fun s' hEvS => ?_⟩
        rw [hEvSEq] at hEvS
        let ⟨tgt, locs', hs', _, hEdgeNext⟩ :=
          evalTerminator_constEdges_sound hExitMatch hEdges hEvS
        subst hs'
        refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, ?_⟩
        intro hTgtLt
        let ⟨tgtEnv, hCTgt, hTgtMatch⟩ := hEdgeNext hTgtLt
        let ⟨bbNext, hBBNext⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt hTgtLt
        have hCTgt0 : Trusted.MirSemantics.getElem? bCert (0 + tgt) = some (some tgtEnv) := by
          rw [Nat.zero_add]; exact hCTgt
        let ⟨_, nextStmts, nextExitEnv, _, _, hNextRew, _, _⟩ :=
          hAct tgt bbNext tgtEnv hBBNext hCTgt0
        exact ⟨bbNext, tgtEnv, nextStmts, nextExitEnv, hBBNext, hCTgt, hNextRew,
          instSimplifyAt_entry hNextRew hTgtMatch⟩

private theorem applyInstSimplifyAlgAndConstProgram_equiv {cert : ProgramConstCert}
    {pSrc pTgt : Program}
    (hApply : applyInstSimplifyAlgAndConstProgram cert pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  unfold applyInstSimplifyAlgAndConstProgram at hApply
  cases hLenB : Nat.beq cert.length pSrc.bodies.length with
  | false => rw [hLenB] at hApply; cases hApply
  | true =>
    rw [hLenB] at hApply; dsimp at hApply
    have hLenC := nat_beq_eq hLenB
    cases hMap : mapOption (fun pr => applyInstSimplifyAlgAndConstBody pr.1 pr.2)
        (List.zip cert pSrc.bodies) with
    | none => rw [hMap] at hApply; cases hApply
    | some bodies' =>
      rw [hMap] at hApply; injection hApply with eP; subst eP
      have hHdr := programHeaderEq_with_bodies pSrc bodies'
      have hBodyLen : pSrc.bodies.length = bodies'.length :=
        (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
      have hIds : pSrc.bodies.map Body.identity = bodies'.map Body.identity := by
        apply list_eq_of_getElem?_eq
        · rw [map_length_eq, map_length_eq, hBodyLen]
        · intro i
          rw [getElem?_map, getElem?_map]
          cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies i with
          | none =>
            have hGe : bodies'.length ≤ i := by
              rw [← hBodyLen]; exact getElem?_none_ge hBS
            rw [getElem?_none_of_ge hGe]
          | some bSrc =>
            let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
            let ⟨hBHdr, _, _, _, _, _, _⟩ := applyInstSimplifyAlgAndConstBody_props hAp
            let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim hBHdr
            rw [hBT]; dsimp [Option.map]; rw [hIdEq]
      refine ⟨?_, hHdr, hIds⟩
      refine fullSemanticEquiv_of_query_iff hHdr ?_ ?_ ?_
      · intro defId bSrc bTgt hBS hBT
        let ⟨_, bTgt', _, hBT', hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
        dsimp at hBT; rw [hBT] at hBT'; injection hBT' with eB; subst eB
        let ⟨hBHdr, _, hEmp, hBnd, _, _, _⟩ := applyInstSimplifyAlgAndConstBody_props hAp
        exact ⟨hBHdr, hEmp, hBnd⟩
      · intro q
        exact instSimplify_query_iff q hLenC hHdr hMap
      · intro defId args
        exact (instSimplify_query_iff
          (pSrc := entryProgForBody pSrc defId)
          (pTgt := entryProgForBody { pSrc with bodies := bodies' } defId)
          { args := args } hLenC
          (programHeaderEq_entryProg defId hHdr) hMap).1

/-! ### Stage 4 Private Helpers — Slice D: Pass Family 4 (`CopyProp` +
`DestProp` + `CertifiedDse`) & Half A Theorems -/

/-! #### Part D.1: `CopyProp` (`applyCopyPropProgram_equiv`) -/

private theorem stmtListStoragePreserved_refl :
    ∀ ss : List StatementKind, StmtListStoragePreserved ss ss
  | [] => True.intro
  | _ :: rest => ⟨Or.inl rfl, stmtListStoragePreserved_refl rest⟩

private noncomputable def AliasPairSound (bodyLocals : List MirTy)
    (locals : List LocalSlot) (dst src : LocalId) : Prop :=
  ∃ ty v,
    Trusted.MirSemantics.getElem? bodyLocals dst = some ty ∧
    Trusted.MirSemantics.getElem? bodyLocals src = some ty ∧
    Trusted.MirSemantics.getElem? locals dst = some (.live (some v)) ∧
    Trusted.MirSemantics.getElem? locals src = some (.live (some v)) ∧
    checkVal v ty = true

private noncomputable def AllAliasesSound (bodyLocals : List MirTy)
    (locals : List LocalSlot) : CopyAliases → Prop
  | [] => True
  | (dst, src) :: rest =>
    AliasPairSound bodyLocals locals dst src ∧
    AllAliasesSound bodyLocals locals rest

private noncomputable def AliasesNotMutatedBy (rv : Rvalue) : CopyAliases → Prop
  | [] => True
  | (dst, src) :: rest =>
    rvalueMutatesOrBorrowsLocal dst rv = false ∧
    rvalueMutatesOrBorrowsLocal src rv = false ∧
    AliasesNotMutatedBy rv rest

private theorem lookupCopyAlias_sound {bodyLocals : List MirTy}
    {locals : List LocalSlot} {aliases : CopyAliases} {d s : LocalId}
    (hAll : AllAliasesSound bodyLocals locals aliases)
    (hLook : lookupCopyAlias d aliases = some s) :
    AliasPairSound bodyLocals locals d s := by
  induction aliases with
  | nil => cases hLook
  | cons pr rest ih =>
    cases pr with
    | mk dst src =>
      dsimp [lookupCopyAlias] at hLook
      let ⟨hHead, hTail⟩ := hAll
      cases hEq : Nat.beq d dst with
      | true =>
        rw [hEq] at hLook; dsimp at hLook
        injection hLook with hsEq; subst hsEq
        rw [nat_beq_eq hEq]
        exact hHead
      | false =>
        rw [hEq] at hLook; dsimp at hLook
        exact ih hTail hLook

private theorem filterAliasesForRvalue_props {bodyLocals : List MirTy}
    {locals : List LocalSlot} {rv : Rvalue} {aliases : CopyAliases}
    (hAll : AllAliasesSound bodyLocals locals aliases) :
    AllAliasesSound bodyLocals locals (filterAliasesForRvalue rv aliases) ∧
    AliasesNotMutatedBy rv (filterAliasesForRvalue rv aliases) := by
  induction aliases with
  | nil => exact ⟨True.intro, True.intro⟩
  | cons pr rest ih =>
    cases pr with
    | mk dst src =>
      let ⟨hHead, hTail⟩ := hAll
      let ⟨ihSound, ihNoMut⟩ := ih hTail
      dsimp [filterAliasesForRvalue]
      cases hMut : (rvalueMutatesOrBorrowsLocal dst rv ||
          rvalueMutatesOrBorrowsLocal src rv) with
      | true => exact ⟨ihSound, ihNoMut⟩
      | false =>
        let ⟨hD, hS⟩ := bool_or_false hMut
        exact ⟨⟨hHead, ihSound⟩, ⟨hD, hS, ihNoMut⟩⟩

private theorem allAliasesSound_preserve_not_moved {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {aliases : CopyAliases}
    (hAll : AllAliasesSound bodyLocals locals aliases)
    (hSame : ∀ id, (∀ d s, (d, s) ∈ aliases → id ≠ d ∧ id ≠ s) ∨
      Trusted.MirSemantics.getElem? locals' id =
        Trusted.MirSemantics.getElem? locals id) :
    AllAliasesSound bodyLocals locals' aliases := by
  have hAt : ∀ id,
      (∃ s, (id, s) ∈ aliases) ∨ (∃ d, (d, id) ∈ aliases) →
      Trusted.MirSemantics.getElem? locals' id =
        Trusted.MirSemantics.getElem? locals id := by
    intro id hIn
    cases hSame id with
    | inr hEq => exact hEq
    | inl hNe =>
      cases hIn with
      | inl h1 =>
        let ⟨s, hMem⟩ := h1
        exact False.elim ((hNe id s hMem).1 rfl)
      | inr h2 =>
        let ⟨d, hMem⟩ := h2
        exact False.elim ((hNe d id hMem).2 rfl)
  induction aliases with
  | nil => exact True.intro
  | cons pr rest ih =>
    cases pr with
    | mk dst src =>
      let ⟨hHead, hTail⟩ := hAll
      let ⟨ty, v, hTyD, hTyS, hLD, hLS, hChk⟩ := hHead
      have hEqD : Trusted.MirSemantics.getElem? locals' dst =
          Trusted.MirSemantics.getElem? locals dst :=
        hAt dst (Or.inl ⟨src, List.Mem.head rest⟩)
      have hEqS : Trusted.MirSemantics.getElem? locals' src =
          Trusted.MirSemantics.getElem? locals src :=
        hAt src (Or.inr ⟨dst, List.Mem.head rest⟩)
      refine ⟨⟨ty, v, hTyD, hTyS, by rw [hEqD]; exact hLD,
               by rw [hEqS]; exact hLS, hChk⟩, ?_⟩
      apply ih hTail
      · intro id
        cases hSame id with
        | inr hEq => exact Or.inr hEq
        | inl hNe =>
          exact Or.inl (fun d s hMem => hNe d s (List.Mem.tail (dst, src) hMem))
      · intro id hIn
        cases hIn with
        | inl h1 =>
          let ⟨s, hMem⟩ := h1
          exact hAt id (Or.inl ⟨s, List.Mem.tail (dst, src) hMem⟩)
        | inr h2 =>
          let ⟨d, hMem⟩ := h2
          exact hAt id (Or.inr ⟨d, List.Mem.tail (dst, src) hMem⟩)

private theorem killCopyAliasesTouching_set_sound {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {id : LocalId} {sl : LocalSlot}
    {aliases : CopyAliases}
    (hAll : AllAliasesSound bodyLocals locals aliases)
    (hSet : setElem? locals id sl = some locals') :
    AllAliasesSound bodyLocals locals' (killCopyAliasesTouching id aliases) := by
  induction aliases with
  | nil => exact True.intro
  | cons pr rest ih =>
    cases pr with
    | mk dst src =>
      let ⟨hHead, hTail⟩ := hAll
      dsimp [killCopyAliasesTouching]
      cases hTouch : (Nat.beq dst id || Nat.beq src id) with
      | true => exact ih hTail
      | false =>
        let ⟨hD, hS⟩ := bool_or_false hTouch
        let ⟨ty, v, hTyD, hTyS, hLD, hLS, hChk⟩ := hHead
        refine ⟨⟨ty, v, hTyD, hTyS,
          by rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hD)]; exact hLD,
          by rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hS)]; exact hLS,
          hChk⟩, ih hTail⟩

private theorem rewriteCopyPropOperand_evalSlot_eq {bodyLocals : List MirTy}
    {locals : List LocalSlot} {aliases : CopyAliases} (op : Operand)
    (hSound : AllAliasesSound bodyLocals locals aliases) :
    evalOperandToSlot bodyLocals locals op =
      evalOperandToSlot bodyLocals locals (rewriteCopyPropOperand aliases op) := by
  cases op with
  | move _ | constant _ => rfl
  | copy p =>
    dsimp [rewriteCopyPropOperand]
    cases hPE : p.projection.isEmpty with
    | false => dsimp
    | true =>
      dsimp
      cases hLook : lookupCopyAlias p.localId aliases with
      | none => rfl
      | some src =>
        let ⟨ty, v, hTyD, hTyS, hLD, hLS, _⟩ := lookupCopyAlias_sound hSound hLook
        dsimp [evalOperandToSlot]
        rw [hPE]; dsimp
        rw [hTyD, hTyS, hLD, hLS]

private theorem rewriteCopyPropOperand_evalPrim_eq {bodyLocals : List MirTy}
    {locals : List LocalSlot} {aliases : CopyAliases} (op : Operand)
    (hSound : AllAliasesSound bodyLocals locals aliases) :
    evalPrimitiveOperand bodyLocals locals op =
      evalPrimitiveOperand bodyLocals locals (rewriteCopyPropOperand aliases op) := by
  unfold evalPrimitiveOperand
  rw [rewriteCopyPropOperand_evalSlot_eq op hSound]

private theorem evalOperandToSlot_noMove_aliases {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {op : Operand}
    {ty : MirTy} {optVal : Option Val} {aliases : CopyAliases}
    (hSound : AllAliasesSound bodyLocals locals aliases)
    (hNoMove : ∀ d s, (d, s) ∈ aliases →
      operandMovesLocal d op = false ∧ operandMovesLocal s op = false)
    (hEv : evalOperandToSlot bodyLocals locals op = .ok (ty, optVal, locals')) :
    AllAliasesSound bodyLocals locals' aliases := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok _ =>
      rw [hC] at hEv; injection hEv with h1; injection h1 with _ h2
      injection h2 with _ hL; subst hL; exact hSound
  | copy p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some _ =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            injection hEv with h1; injection h1 with _ h2
            injection h2 with _ hL; subst hL; exact hSound
  | move p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some t =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            dsimp at hEv
            cases hSet : setElem? locals p.localId (liveUninitSlot t) with
            | none => rw [hSet] at hEv; cases hEv
            | some locs1 =>
              rw [hSet] at hEv
              injection hEv with h1; injection h1 with _ h2
              injection h2 with _ hL; subst hL
              apply allAliasesSound_preserve_not_moved hSound
              intro id
              cases hEq : Nat.beq id p.localId with
              | false =>
                exact Or.inr (setElem?_getElem?_ne hSet (nat_ne_of_beq_false hEq))
              | true =>
                have hid := nat_beq_eq hEq; subst hid
                refine Or.inl (fun d s hMem => ?_)
                let ⟨hD, hS⟩ := hNoMove d s hMem
                dsimp [operandMovesLocal] at hD hS
                exact ⟨nat_ne_of_beq_false hD, nat_ne_of_beq_false hS⟩

private theorem aliasesNotMutatedBy_mem {rv : Rvalue} {aliases : CopyAliases}
    (h : AliasesNotMutatedBy rv aliases) :
    ∀ d s, (d, s) ∈ aliases →
      rvalueMutatesOrBorrowsLocal d rv = false ∧
      rvalueMutatesOrBorrowsLocal s rv = false := by
  induction aliases with
  | nil => intro _ _ hMem; cases hMem
  | cons pr rest ih =>
    cases pr with
    | mk dst src =>
      let ⟨hD, hS, hRest⟩ := h
      intro d s hMem
      cases hMem with
      | head _ => exact ⟨hD, hS⟩
      | tail _ hM => exact ih hRest d s hM

private theorem rewriteCopyPropRvalue_eval_eq_and_preserve {bodyLocals : List MirTy}
    {locals : List LocalSlot} {dstTy : MirTy}
    {aliases : CopyAliases} (rvSrc : Rvalue)
    (hSound : AllAliasesSound bodyLocals locals aliases) :
    evalRvalue bodyLocals locals dstTy rvSrc =
      evalRvalue bodyLocals locals dstTy (rewriteCopyPropRvalue aliases rvSrc) ∧
    (∀ v locals₁,
      evalRvalue bodyLocals locals dstTy rvSrc = .ok (v, locals₁) →
      AllAliasesSound bodyLocals locals₁ (filterAliasesForRvalue rvSrc aliases)) := by
  let safeAliases := filterAliasesForRvalue rvSrc aliases
  let ⟨hSafeSound, hSafeNoMut⟩ := filterAliasesForRvalue_props (rv := rvSrc) hSound
  have hSafeMem := aliasesNotMutatedBy_mem hSafeNoMut
  have hPreserve : ∀ v locals₁,
      evalRvalue bodyLocals locals dstTy rvSrc = .ok (v, locals₁) →
      AllAliasesSound bodyLocals locals₁ safeAliases := by
    intro v locals₁ hEv
    cases rvSrc with
    | use opnd =>
      dsimp [evalRvalue] at hEv
      cases hS : evalOperandToSlot bodyLocals locals opnd with
      | error _ => rw [hS] at hEv; cases hEv
      | ok res =>
        let ⟨sTy, optV, l1⟩ := res
        rw [hS] at hEv; dsimp at hEv
        cases hEqTy : MirTy.beq sTy dstTy with
        | false => rw [hEqTy] at hEv; cases hEv
        | true =>
          rw [hEqTy] at hEv; dsimp at hEv
          cases optV with
          | none => cases hEv
          | some _ =>
            injection hEv with h1; injection h1 with _ hL; subst hL
            exact evalOperandToSlot_noMove_aliases hSafeSound hSafeMem hS
    | unaryOp op opnd =>
      dsimp [evalRvalue, evalPrimitiveOperand] at hEv
      cases hS : evalOperandToSlot bodyLocals locals opnd with
      | error _ => rw [hS] at hEv; cases hEv
      | ok res =>
        let ⟨sTy, optV, l1⟩ := res
        rw [hS] at hEv; dsimp at hEv
        cases hPrim : isPrimitiveReadableTy sTy with
        | false => rw [hPrim] at hEv; cases hEv
        | true =>
          rw [hPrim] at hEv; dsimp at hEv
          cases optV with
          | none => cases hEv
          | some v0 =>
            dsimp at hEv
            cases hU : evalUnOp op v0 with
            | error _ => rw [hU] at hEv; cases hEv
            | ok _ =>
              rw [hU] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL
              exact evalOperandToSlot_noMove_aliases hSafeSound hSafeMem hS
    | binaryOp op lhs rhs =>
      have hNoL : ∀ d s, (d, s) ∈ safeAliases →
          operandMovesLocal d lhs = false ∧ operandMovesLocal s lhs = false := by
        intro d s hM
        let ⟨hD, hS⟩ := hSafeMem d s hM
        exact ⟨(bool_or_false hD).1, (bool_or_false hS).1⟩
      have hNoR : ∀ d s, (d, s) ∈ safeAliases →
          operandMovesLocal d rhs = false ∧ operandMovesLocal s rhs = false := by
        intro d s hM
        let ⟨hD, hS⟩ := hSafeMem d s hM
        exact ⟨(bool_or_false hD).2, (bool_or_false hS).2⟩
      dsimp [evalRvalue, evalPrimitiveOperand] at hEv
      cases hSL : evalOperandToSlot bodyLocals locals lhs with
      | error _ => rw [hSL] at hEv; cases hEv
      | ok resL =>
        let ⟨lTy, optL, l1⟩ := resL
        rw [hSL] at hEv; dsimp at hEv
        cases hPL : isPrimitiveReadableTy lTy with
        | false => rw [hPL] at hEv; cases hEv
        | true =>
          rw [hPL] at hEv; dsimp at hEv
          cases optL with
          | none => cases hEv
          | some lv =>
            dsimp at hEv
            have hS1 := evalOperandToSlot_noMove_aliases hSafeSound hNoL hSL
            cases hSR : evalOperandToSlot bodyLocals l1 rhs with
            | error _ => rw [hSR] at hEv; cases hEv
            | ok resR =>
              let ⟨rTy, optR, l2⟩ := resR
              rw [hSR] at hEv; dsimp at hEv
              cases hPR : isPrimitiveReadableTy rTy with
              | false => rw [hPR] at hEv; cases hEv
              | true =>
                rw [hPR] at hEv; dsimp at hEv
                cases optR with
                | none => cases hEv
                | some rvVal =>
                  dsimp at hEv
                  cases hB : evalBinOp op lv rvVal with
                  | error _ => rw [hB] at hEv; cases hEv
                  | ok _ =>
                    rw [hB] at hEv; injection hEv with h1; injection h1 with _ hL2; subst hL2
                    exact evalOperandToSlot_noMove_aliases hS1 hNoR hSR
    | discriminant p =>
      dsimp [evalRvalue] at hEv
      cases hP : p.projection.isEmpty with
      | false => rw [hP] at hEv; cases hEv
      | true =>
        rw [hP] at hEv; dsimp at hEv
        cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
        | none => rw [hTy] at hEv; cases hEv
        | some ty =>
          rw [hTy] at hEv
          cases ty with
          | enum ety =>
            cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
            | none => rw [hSl] at hEv; cases hEv
            | some slot =>
              rw [hSl] at hEv; dsimp at hEv
              cases hAdm : enumAdmitted ety with
              | false => rw [hAdm] at hEv; cases hEv
              | true =>
                rw [hAdm] at hEv; dsimp at hEv
                cases hTr : ety.tagRepr with
                | zeroSized =>
                  rw [hTr] at hEv
                  cases slot with
                  | dead => cases hEv
                  | live opt =>
                    cases opt with
                    | none =>
                      dsimp at hEv
                      cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                      | none => rw [hD] at hEv; cases hEv
                      | some _ =>
                        rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                        subst hL; exact hSafeSound
                    | some val =>
                      cases val with
                      | enumVal ety' k =>
                        dsimp at hEv
                        cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                        | false => rw [hC] at hEv; cases hEv
                        | true =>
                          rw [hC] at hEv; dsimp at hEv
                          cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                          | none => rw [hD] at hEv; cases hEv
                          | some _ =>
                            rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                            subst hL; exact hSafeSound
                      | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
                | scalar _ _ =>
                  rw [hTr] at hEv
                  cases slot with
                  | dead => cases hEv
                  | live opt =>
                    cases opt with
                    | none => cases hEv
                    | some val =>
                      cases val with
                      | enumVal ety' k =>
                        dsimp at hEv
                        cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                        | false => rw [hC] at hEv; cases hEv
                        | true =>
                          rw [hC] at hEv; dsimp at hEv
                          cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                          | none => rw [hD] at hEv; cases hEv
                          | some _ =>
                            rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL
                            subst hL; exact hSafeSound
                      | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
          | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
    | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEv
  refine ⟨?_, hPreserve⟩
  cases rvSrc with
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => rfl
  | use o =>
    dsimp [rewriteCopyPropRvalue, evalRvalue]
    rw [rewriteCopyPropOperand_evalSlot_eq o hSafeSound]
  | unaryOp op o =>
    dsimp [rewriteCopyPropRvalue, evalRvalue]
    rw [rewriteCopyPropOperand_evalPrim_eq o hSafeSound]
  | binaryOp op l r =>
    have hNoL : ∀ d s, (d, s) ∈ safeAliases →
        operandMovesLocal d l = false ∧ operandMovesLocal s l = false := by
      intro d s hM
      let ⟨hD, hS⟩ := hSafeMem d s hM
      exact ⟨(bool_or_false hD).1, (bool_or_false hS).1⟩
    dsimp [rewriteCopyPropRvalue, evalRvalue]
    rw [← rewriteCopyPropOperand_evalPrim_eq l hSafeSound]
    cases hEvL : evalPrimitiveOperand bodyLocals locals l with
    | error _ => rfl
    | ok resL =>
      let ⟨lv, locs1⟩ := resL
      dsimp
      have hS1 : AllAliasesSound bodyLocals locs1 safeAliases := by
        dsimp [evalPrimitiveOperand] at hEvL
        cases hSL : evalOperandToSlot bodyLocals locals l with
        | error _ => rw [hSL] at hEvL; cases hEvL
        | ok r0 =>
          let ⟨t0, o0, l0⟩ := r0
          rw [hSL] at hEvL; dsimp at hEvL
          cases hP0 : isPrimitiveReadableTy t0 with
          | false => rw [hP0] at hEvL; cases hEvL
          | true =>
            rw [hP0] at hEvL; dsimp at hEvL
            cases o0 with
            | none => cases hEvL
            | some _ =>
              injection hEvL with e1; injection e1 with _ eL; subst eL
              exact evalOperandToSlot_noMove_aliases hSafeSound hNoL hSL
      rw [rewriteCopyPropOperand_evalPrim_eq r hS1]
  | discriminant p =>
    dsimp [rewriteCopyPropRvalue]
    cases hP : p.projection.isEmpty with
    | false => dsimp
    | true =>
      dsimp
      cases hLook : lookupCopyAlias p.localId safeAliases with
      | none => rfl
      | some src =>
        let ⟨ty, v, hTy1, hTy2, hL1, hL2, _⟩ := lookupCopyAlias_sound hSafeSound hLook
        dsimp [evalRvalue]
        rw [hP]; dsimp
        rw [hTy1, hTy2, hL1, hL2]

private theorem rewriteCopyPropTerm_eval_eq {bSrc bTgt : Body}
    {bbSrc bbTgt : BasicBlock} {frame : FrameState} {cm : CallerMemory}
    {aliases : CopyAliases}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hTerm : bbTgt.terminator = rewriteCopyPropTerm aliases bbSrc.terminator)
    (hAliases : AllAliasesSound bSrc.locals frame.locals aliases) :
    evalTerminator bSrc bbSrc frame cm = evalTerminator bTgt bbTgt frame cm := by
  unfold evalTerminator
  rw [hTerm, ← hLocEq, hClean]
  cases bbSrc.terminator with
  | goto _ | return_ | unreachable | unwindResume | assert _ _ _ _ _
  | call _ _ _ _ _ | unsupported => rfl
  | switchInt discr targets =>
    dsimp [rewriteCopyPropTerm]
    rw [rewriteCopyPropOperand_evalPrim_eq discr hAliases]

private theorem rewriteCopyPropStmts_storage {bodyLocals : List MirTy} :
    ∀ {aliases env ss ss' exitAliases exitEnv},
      rewriteCopyPropStmts bodyLocals aliases env ss =
        some (ss', exitAliases, exitEnv) →
      StmtListStoragePreserved ss ss' := by
  intro aliases env ss
  induction ss generalizing aliases env with
  | nil =>
    intro ss' _ _ h
    injection h with e; injection e with e1 _
    subst e1; exact True.intro
  | cons s rest ih =>
    intro ss' exitA exitE h
    cases s with
    | nop =>
      dsimp [rewriteCopyPropStmts] at h
      cases hR : rewriteCopyPropStmts bodyLocals aliases env rest with
      | none => rw [hR] at h; cases h
      | some pr =>
        let ⟨rest', ea, ee⟩ := pr
        rw [hR] at h; injection h with e; injection e with e1 _
        subst e1
        exact ⟨Or.inl rfl, ih hR⟩
    | unsupported =>
      dsimp [rewriteCopyPropStmts] at h
      cases hR : rewriteCopyPropStmts bodyLocals [] env rest with
      | none => rw [hR] at h; cases h
      | some pr =>
        let ⟨rest', ea, ee⟩ := pr
        rw [hR] at h; injection h with e; injection e with e1 _
        subst e1
        exact ⟨Or.inl rfl, ih hR⟩
    | storageLive id =>
      dsimp [rewriteCopyPropStmts] at h
      cases hSt : stepPlainStmtAbs bodyLocals env (.storageLive id) with
      | none => rw [hSt] at h; cases h
      | some env' =>
        rw [hSt] at h; dsimp at h
        cases hR : rewriteCopyPropStmts bodyLocals
            (killCopyAliasesTouching id aliases) env' rest with
        | none => rw [hR] at h; cases h
        | some pr =>
          let ⟨rest', ea, ee⟩ := pr
          rw [hR] at h; injection h with e; injection e with e1 _
          subst e1
          exact ⟨Or.inl rfl, ih hR⟩
    | storageDead id =>
      dsimp [rewriteCopyPropStmts] at h
      cases hSt : stepPlainStmtAbs bodyLocals env (.storageDead id) with
      | none => rw [hSt] at h; cases h
      | some env' =>
        rw [hSt] at h; dsimp at h
        cases hR : rewriteCopyPropStmts bodyLocals
            (killCopyAliasesTouching id aliases) env' rest with
        | none => rw [hR] at h; cases h
        | some pr =>
          let ⟨rest', ea, ee⟩ := pr
          rw [hR] at h; injection h with e; injection e with e1 _
          subst e1
          exact ⟨Or.inl rfl, ih hR⟩
    | assign dst rvSrc =>
      dsimp [rewriteCopyPropStmts] at h
      cases hPE : dst.projection.isEmpty with
      | false => rw [hPE] at h; cases h
      | true =>
        rw [hPE] at h; dsimp at h
        cases hSt : stepPlainStmtAbs bodyLocals env (.assign dst rvSrc) with
        | none => rw [hSt] at h; cases h
        | some env' =>
          rw [hSt] at h; dsimp only at h
          let aliasesNext :=
            match rewriteCopyPropRvalue aliases rvSrc with
            | .use (.copy pHead) =>
              if pHead.projection.isEmpty && !Nat.beq dst.localId pHead.localId then
                match Trusted.MirSemantics.getElem? bodyLocals dst.localId,
                    Trusted.MirSemantics.getElem? bodyLocals pHead.localId,
                    Trusted.MirSemantics.getElem? env dst.localId,
                    Trusted.MirSemantics.getElem? env pHead.localId with
                | some dstTy, some srcTy, some dstSlot, some .liveInit =>
                  if MirTy.beq dstTy srcTy && isSupportedScalarOrUnitTy dstTy &&
                      absSlotImplies dstSlot .liveUninit then
                    (dst.localId, pHead.localId) ::
                      killCopyAliasesTouching dst.localId (filterAliasesForRvalue rvSrc aliases)
                  else
                    killCopyAliasesTouching dst.localId (filterAliasesForRvalue rvSrc aliases)
                | _, _, _, _ =>
                  killCopyAliasesTouching dst.localId (filterAliasesForRvalue rvSrc aliases)
              else
                killCopyAliasesTouching dst.localId (filterAliasesForRvalue rvSrc aliases)
            | _ =>
              killCopyAliasesTouching dst.localId (filterAliasesForRvalue rvSrc aliases)
          change (match rewriteCopyPropStmts bodyLocals aliasesNext env' rest with
            | some (rest', exitAliases, exitEnv) =>
              some (.assign dst (rewriteCopyPropRvalue aliases rvSrc) :: rest',
                    exitAliases, exitEnv)
            | none => none) = some (ss', exitA, exitE) at h
          cases hR : rewriteCopyPropStmts bodyLocals aliasesNext env' rest with
          | none => rw [hR] at h; cases h
          | some pr =>
            let ⟨rest', ea, ee⟩ := pr
            rw [hR] at h; injection h with e; injection e with e1 _
            subst e1
            exact ⟨Or.inr ⟨True.intro, True.intro⟩, ih hR⟩

private theorem rewriteCopyPropStmts_step {bSrc bTgt : Body}
    {frame : FrameState} {cm : CallerMemory}
    {aliases exitAliases : CopyAliases} {env exitEnv : List AbsSlot}
    {sSrc : StatementKind} {restSrc ssTgt : List StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEnv : AbsEnvSound bSrc.locals env frame.locals)
    (hAliases : AllAliasesSound bSrc.locals frame.locals aliases)
    (hRew : rewriteCopyPropStmts bSrc.locals aliases env (sSrc :: restSrc) =
      some (ssTgt, exitAliases, exitEnv)) :
    ∃ sTgt restTgt aliases' env',
      ssTgt = sTgt :: restTgt ∧
      rewriteCopyPropStmts bSrc.locals aliases' env' restSrc =
        some (restTgt, exitAliases, exitEnv) ∧
      evalStatement bSrc frame cm sSrc = evalStatement bTgt frame cm sTgt ∧
      (∀ s', evalStatement bSrc frame cm sSrc = .step s' →
        ∃ locs',
          s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
                 callerMem := cm } ∧
          AbsEnvSound bSrc.locals env' locs' ∧
          AllAliasesSound bSrc.locals locs' aliases') := by
  cases sSrc with
  | nop =>
    dsimp [rewriteCopyPropStmts] at hRew
    cases hR : rewriteCopyPropStmts bSrc.locals aliases env restSrc with
    | none => rw [hR] at hRew; cases hRew
    | some pr =>
      let ⟨restTgt, ea, ee⟩ := pr
      rw [hR] at hRew; injection hRew with e
      injection e with e1 e2; injection e2 with e3 e4
      subst e1; subst e3; subst e4
      refine ⟨.nop, restTgt, aliases, env, rfl, hR, rfl, ?_⟩
      intro s' hEv; injection hEv with eS; subst eS
      exact ⟨frame.locals, rfl, hEnv, hAliases⟩
  | unsupported =>
    dsimp [rewriteCopyPropStmts] at hRew
    cases hR : rewriteCopyPropStmts bSrc.locals [] env restSrc with
    | none => rw [hR] at hRew; cases hRew
    | some pr =>
      let ⟨restTgt, ea, ee⟩ := pr
      rw [hR] at hRew; injection hRew with e
      injection e with e1 e2; injection e2 with e3 e4
      subst e1; subst e3; subst e4
      exact ⟨.unsupported, restTgt, [], env, rfl, hR, rfl, fun _ hEv => by cases hEv⟩
  | storageLive id =>
    dsimp [rewriteCopyPropStmts] at hRew
    cases hSt : stepPlainStmtAbs bSrc.locals env (.storageLive id) with
    | none => rw [hSt] at hRew; cases hRew
    | some env' =>
      rw [hSt] at hRew; dsimp at hRew
      cases hR : rewriteCopyPropStmts bSrc.locals
          (killCopyAliasesTouching id aliases) env' restSrc with
      | none => rw [hR] at hRew; cases hRew
      | some pr =>
        let ⟨restTgt, ea, ee⟩ := pr
        rw [hR] at hRew; injection hRew with e
        injection e with e1 e2; injection e2 with e3 e4
        subst e1; subst e3; subst e4
        refine ⟨.storageLive id, restTgt, killCopyAliasesTouching id aliases,
          env', rfl, hR, by dsimp [evalStatement]; rw [hLocEq], ?_⟩
        intro s' hEv
        let ⟨locs', hSEq, hEnv'⟩ := stepPlainStmtAbs_sound hEnv hSt hEv
        dsimp [evalStatement] at hEv
        cases hTy : Trusted.MirSemantics.getElem? bSrc.locals id with
        | none => rw [hTy] at hEv; cases hEv
        | some ty =>
          rw [hTy] at hEv; dsimp at hEv
          cases hSet : setElem? frame.locals id (liveUninitSlot ty) with
          | none => rw [hSet] at hEv; cases hEv
          | some l' =>
            rw [hSet] at hEv; injection hEv with hS1
            rw [hSEq] at hS1
            injection hS1 with hFs _; injection hFs with hF _
            have hLEq : locs' = l' := (congrArg FrameState.locals hF).symm
            subst hLEq
            exact ⟨locs', hSEq, hEnv', killCopyAliasesTouching_set_sound hAliases hSet⟩
  | storageDead id =>
    dsimp [rewriteCopyPropStmts] at hRew
    cases hSt : stepPlainStmtAbs bSrc.locals env (.storageDead id) with
    | none => rw [hSt] at hRew; cases hRew
    | some env' =>
      rw [hSt] at hRew; dsimp at hRew
      cases hR : rewriteCopyPropStmts bSrc.locals
          (killCopyAliasesTouching id aliases) env' restSrc with
      | none => rw [hR] at hRew; cases hRew
      | some pr =>
        let ⟨restTgt, ea, ee⟩ := pr
        rw [hR] at hRew; injection hRew with e
        injection e with e1 e2; injection e2 with e3 e4
        subst e1; subst e3; subst e4
        refine ⟨.storageDead id, restTgt, killCopyAliasesTouching id aliases,
          env', rfl, hR, rfl, ?_⟩
        intro s' hEv
        let ⟨locs', hSEq, hEnv'⟩ := stepPlainStmtAbs_sound hEnv hSt hEv
        dsimp [evalStatement] at hEv
        cases hZ : Nat.beq id 0 with
        | true => rw [hZ] at hEv; cases hEv
        | false =>
          rw [hZ] at hEv; dsimp at hEv
          cases hSet : setElem? frame.locals id .dead with
          | none => rw [hSet] at hEv; cases hEv
          | some l' =>
            rw [hSet] at hEv; injection hEv with hS1
            rw [hSEq] at hS1
            injection hS1 with hFs _; injection hFs with hF _
            have hLEq : locs' = l' := (congrArg FrameState.locals hF).symm
            subst hLEq
            exact ⟨locs', hSEq, hEnv', killCopyAliasesTouching_set_sound hAliases hSet⟩
  | assign dst rvSrc =>
    dsimp [rewriteCopyPropStmts] at hRew
    cases hPE : dst.projection.isEmpty with
    | false => rw [hPE] at hRew; cases hRew
    | true =>
      rw [hPE] at hRew; dsimp at hRew
      cases hSt : stepPlainStmtAbs bSrc.locals env (.assign dst rvSrc) with
      | none => rw [hSt] at hRew; cases hRew
      | some env' =>
        rw [hSt] at hRew; dsimp only at hRew
        let rvTgt := rewriteCopyPropRvalue aliases rvSrc
        let afterKill :=
          killCopyAliasesTouching dst.localId (filterAliasesForRvalue rvSrc aliases)
        let aliases' :=
          match rvTgt with
          | .use (.copy pHead) =>
            if pHead.projection.isEmpty && !Nat.beq dst.localId pHead.localId then
              match Trusted.MirSemantics.getElem? bSrc.locals dst.localId,
                  Trusted.MirSemantics.getElem? bSrc.locals pHead.localId,
                  Trusted.MirSemantics.getElem? env dst.localId,
                  Trusted.MirSemantics.getElem? env pHead.localId with
              | some dstTy, some srcTy, some dstSlot, some .liveInit =>
                if MirTy.beq dstTy srcTy && isSupportedScalarOrUnitTy dstTy &&
                    absSlotImplies dstSlot .liveUninit then
                  (dst.localId, pHead.localId) :: afterKill
                else
                  afterKill
              | _, _, _, _ => afterKill
            else
              afterKill
          | _ => afterKill
        change (match rewriteCopyPropStmts bSrc.locals aliases' env' restSrc with
          | some (rest', exitAliases, exitEnv) =>
            some (.assign dst rvTgt :: rest', exitAliases, exitEnv)
          | none => none) = some (ssTgt, exitAliases, exitEnv) at hRew
        cases hR : rewriteCopyPropStmts bSrc.locals aliases' env' restSrc with
        | none => rw [hR] at hRew; cases hRew
        | some pr =>
          let ⟨restTgt, ea, ee⟩ := pr
          rw [hR] at hRew; injection hRew with e
          injection e with e1 e2; injection e2 with e3 e4
          subst e1; subst e3; subst e4
          have hEvEq : evalStatement bSrc frame cm (.assign dst rvSrc) =
              evalStatement bTgt frame cm (.assign dst rvTgt) := by
            dsimp [evalStatement]
            rw [hPE, ← hLocEq]; dsimp
            cases Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
            | none => rfl
            | some dstTy =>
              dsimp
              rw [(rewriteCopyPropRvalue_eval_eq_and_preserve (dstTy := dstTy) rvSrc hAliases).1]
          refine ⟨.assign dst rvTgt, restTgt, aliases', env', rfl, hR, hEvEq, ?_⟩
          intro s' hEv
          let ⟨locs', hSEq, hEnv'⟩ := stepPlainStmtAbs_sound hEnv hSt hEv
          dsimp [evalStatement] at hEv
          rw [hPE] at hEv; dsimp at hEv
          cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
          | none => rw [hDstTy] at hEv; cases hEv
          | some dstTy =>
            rw [hDstTy] at hEv; dsimp at hEv
            let ⟨hRvEq, hRvPres⟩ :=
              rewriteCopyPropRvalue_eval_eq_and_preserve (dstTy := dstTy) rvSrc hAliases
            cases hEvR : evalRvalue bSrc.locals frame.locals dstTy rvSrc with
            | error _ => rw [hEvR] at hEv; cases hEv
            | ok resR =>
              let ⟨val, locsAfterR⟩ := resR
              rw [hEvR] at hEv; dsimp at hEv
              have hAfterR := hRvPres val locsAfterR hEvR
              unfold writePlace at hEv
              cases hChk : checkVal val dstTy with
              | false => rw [hChk] at hEv; cases hEv
              | true =>
                rw [hChk] at hEv; dsimp at hEv
                cases hSlDst : Trusted.MirSemantics.getElem? locsAfterR dst.localId with
                | none => rw [hSlDst] at hEv; cases hEv
                | some slDst =>
                  rw [hSlDst] at hEv
                  cases slDst with
                  | dead => cases hEv
                  | live _ =>
                    cases hSetW : setElem? locsAfterR dst.localId (.live (some val)) with
                    | none => rw [hSetW] at hEv; cases hEv
                    | some locsW =>
                      rw [hSetW] at hEv; injection hEv with hS1
                      rw [hSEq] at hS1
                      injection hS1 with hFs _; injection hFs with hF _
                      have hLEq : locs' = locsW := (congrArg FrameState.locals hF).symm
                      subst hLEq
                      have hAfterKill : AllAliasesSound bSrc.locals locs' afterKill :=
                        killCopyAliasesTouching_set_sound hAfterR hSetW
                      refine ⟨locs', hSEq, hEnv', ?_⟩
                      dsimp [aliases']
                      cases hRvTgt : rvTgt with
                      | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
                      | addressOf _ _ | aggregateTuple _ | unsupported =>
                        exact hAfterKill
                      | use opTgt =>
                        cases opTgt with
                        | move _ | constant _ => exact hAfterKill
                        | copy pHead =>
                          dsimp
                          cases hHeadCond : (pHead.projection.isEmpty &&
                              !Nat.beq dst.localId pHead.localId) with
                          | false => dsimp; exact hAfterKill
                          | true =>
                            dsimp
                            rw [hDstTy]
                            let ⟨hHeadEmp, hDstNeHeadB⟩ := bool_and_true hHeadCond
                            have hDstNeHead := nat_ne_of_beq_false (bool_not_true hDstNeHeadB)
                            cases hSrcTy : Trusted.MirSemantics.getElem? bSrc.locals pHead.localId with
                            | none => exact hAfterKill
                            | some srcTy =>
                              cases hEDst : Trusted.MirSemantics.getElem? env dst.localId with
                              | none => exact hAfterKill
                              | some dstAbs =>
                                cases hESrc : Trusted.MirSemantics.getElem? env pHead.localId with
                                | none => exact hAfterKill
                                | some srcAbs =>
                                  cases srcAbs with
                                  | dead | liveUninit => exact hAfterKill
                                  | liveInit =>
                                    dsimp
                                    cases hAdmit : (MirTy.beq dstTy srcTy &&
                                        isSupportedScalarOrUnitTy dstTy &&
                                        absSlotImplies dstAbs .liveUninit) with
                                    | false => dsimp; exact hAfterKill
                                    | true =>
                                      dsimp
                                      let ⟨h12A, _⟩ := bool_and_true hAdmit
                                      let ⟨hTyEqB, _⟩ := bool_and_true h12A
                                      have hTyEq := mirTy_beq_eq hTyEqB; subst hTyEq
                                      have hEvRTgt : evalRvalue bSrc.locals frame.locals dstTy
                                          (.use (.copy pHead)) = .ok (val, locsAfterR) := by
                                        rw [← hRvTgt, ← hRvEq]; exact hEvR
                                      dsimp [evalRvalue, evalOperandToSlot] at hEvRTgt
                                      rw [hHeadEmp, hSrcTy] at hEvRTgt; dsimp at hEvRTgt
                                      cases hSlHead : Trusted.MirSemantics.getElem?
                                          frame.locals pHead.localId with
                                      | none => rw [hSlHead] at hEvRTgt; cases hEvRTgt
                                      | some slHead =>
                                        rw [hSlHead] at hEvRTgt
                                        cases slHead with
                                        | dead => cases hEvRTgt
                                        | live optHead =>
                                          dsimp at hEvRTgt
                                          rw [mirTy_beq_refl dstTy] at hEvRTgt; dsimp at hEvRTgt
                                          cases optHead with
                                          | none => cases hEvRTgt
                                          | some vHead =>
                                            injection hEvRTgt with q1
                                            injection q1 with hvEq hL
                                            subst hvEq; subst hL
                                            have hW_dst := setElem?_getElem?_same hSetW
                                            have hW_head : Trusted.MirSemantics.getElem? locs'
                                                pHead.localId = some (.live (some vHead)) := by
                                              rw [setElem?_getElem?_ne hSetW hDstNeHead.symm]
                                              exact hSlHead
                                            exact ⟨⟨dstTy, vHead, hDstTy, hSrcTy, hW_dst,
                                                    hW_head, hChk⟩, hAfterKill⟩

private theorem applyCopyPropBlocks_props {b : Body} {cert : BodyAbsCert} :
    ∀ {base bbs bbs'},
      applyCopyPropBlocks b cert base bbs = some bbs' →
      bbs.length = bbs'.length ∧
      (∀ i bb₁ bb₂,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? bbs' i = some bb₂ →
        StmtListStoragePreserved bb₁.statements bb₂.statements ∧
        bb₁.cleanup = bb₂.cleanup) ∧
      (∀ i bb₁ entryEnv,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? cert (base + i) = some (some entryEnv) →
        ∃ bb₂ stmts' exitAliases exitEnv,
          Trusted.MirSemantics.getElem? bbs' i = some bb₂ ∧
          entryEnv.length = b.locals.length ∧
          rewriteCopyPropStmts b.locals [] entryEnv bb₁.statements =
            some (stmts', exitAliases, exitEnv) ∧
          checkAbsTerminatorEdges b.locals b.basicBlocks.length cert exitEnv
            bb₁.terminator = true ∧
          bb₂ = { statements := stmts',
                  terminator := rewriteCopyPropTerm exitAliases bb₁.terminator,
                  cleanup := bb₁.cleanup }) := by
  intro base bbs
  induction bbs generalizing base with
  | nil =>
    intro bbs' h; injection h with e; subst e
    exact ⟨rfl, (fun _ _ _ h1 => by cases h1), (fun _ _ _ h1 => by cases h1)⟩
  | cons bb rest ih =>
    intro bbs' h
    dsimp [applyCopyPropBlocks] at h
    cases hC : Trusted.MirSemantics.getElem? cert base with
    | none => rw [hC] at h; cases h
    | some optE =>
      rw [hC] at h
      cases optE with
      | none =>
        dsimp at h
        cases hRec : applyCopyPropBlocks b cert (base + 1) rest with
        | none => rw [hRec] at h; cases h
        | some rest' =>
          rw [hRec] at h; injection h with e; subst e
          let ⟨hLen, hStCl, hAct⟩ := ih hRec
          refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
          · intro i bb₁ bb₂ h1 h2
            cases i with
            | zero =>
              injection h1 with e1; injection h2 with e2; subst e1; subst e2
              exact ⟨stmtListStoragePreserved_refl _, rfl⟩
            | succ k => exact hStCl k bb₁ bb₂ h1 h2
          · intro i bb₁ eEnv h1 hCE
            cases i with
            | zero => rw [Nat.add_zero, hC] at hCE; cases hCE
            | succ k =>
              have hAdd : (base + 1) + k = base + (k + 1) := by
                rw [Nat.add_assoc, Nat.add_comm 1 k]
              rw [← hAdd] at hCE
              exact hAct k bb₁ eEnv h1 hCE
      | some entryEnv =>
        dsimp at h
        cases hELen : Nat.beq entryEnv.length b.locals.length with
        | false => rw [hELen] at h; cases h
        | true =>
          rw [hELen] at h; dsimp at h
          cases hRew : rewriteCopyPropStmts b.locals [] entryEnv bb.statements with
          | none => rw [hRew] at h; cases h
          | some pr =>
            let ⟨stmts', exitAliases, exitEnv⟩ := pr
            rw [hRew] at h; dsimp at h
            cases hEdg : checkAbsTerminatorEdges b.locals b.basicBlocks.length cert
                exitEnv bb.terminator with
            | false => rw [hEdg] at h; cases h
            | true =>
              rw [hEdg] at h; dsimp at h
              cases hRec : applyCopyPropBlocks b cert (base + 1) rest with
              | none => rw [hRec] at h; cases h
              | some rest' =>
                rw [hRec] at h; injection h with e; subst e
                let ⟨hLen, hStCl, hAct⟩ := ih hRec
                refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
                · intro i bb₁ bb₂ h1 h2
                  cases i with
                  | zero =>
                    injection h1 with e1; injection h2 with e2; subst e1; subst e2
                    exact ⟨rewriteCopyPropStmts_storage hRew, rfl⟩
                  | succ k => exact hStCl k bb₁ bb₂ h1 h2
                · intro i bb₁ eEnv h1 hCE
                  cases i with
                  | zero =>
                    injection h1 with e1; subst e1
                    rw [Nat.add_zero, hC] at hCE; injection hCE with eE
                    injection eE with eE'; subst eE'
                    exact ⟨_, stmts', exitAliases, exitEnv, rfl,
                           nat_beq_eq hELen, hRew, hEdg, rfl⟩
                  | succ k =>
                    have hAdd : (base + 1) + k = base + (k + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 k]
                    rw [← hAdd] at hCE
                    exact hAct k bb₁ eEnv h1 hCE

private theorem applyCopyPropBody_props {cert : BodyAbsCert} {bSrc bTgt : Body}
    (hApply : applyCopyPropBody cert bSrc = some bTgt) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) ∧
    (bSrc.basicBlocks.isEmpty = false →
      ∃ env₀, Trusted.MirSemantics.getElem? cert 0 = some (some env₀) ∧
        absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
    applyCopyPropBlocks bSrc cert 0 bSrc.basicBlocks = some bTgt.basicBlocks := by
  unfold applyCopyPropBody at hApply
  cases hCLen : Nat.beq cert.length bSrc.basicBlocks.length with
  | false => rw [hCLen] at hApply; cases hApply
  | true =>
    rw [hCLen] at hApply; dsimp at hApply
    have hProceed :
        ((bSrc.basicBlocks.isEmpty = false →
          ∃ env₀, Trusted.MirSemantics.getElem? cert 0 = some (some env₀) ∧
            absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
         ∃ bbs', applyCopyPropBlocks bSrc cert 0 bSrc.basicBlocks = some bbs' ∧
           bTgt = { bSrc with basicBlocks := bbs' }) := by
      cases hEmp : bSrc.basicBlocks.isEmpty with
      | true =>
        rw [hEmp] at hApply; dsimp at hApply
        cases hBlk : applyCopyPropBlocks bSrc cert 0 bSrc.basicBlocks with
        | none => rw [hBlk] at hApply; cases hApply
        | some bbs' =>
          rw [hBlk] at hApply; injection hApply with eB
          exact ⟨(fun hF => by cases hF), bbs', rfl, eB.symm⟩
      | false =>
        rw [hEmp] at hApply
        cases hC0 : Trusted.MirSemantics.getElem? cert 0 with
        | none => rw [hC0] at hApply; cases hApply
        | some opt0 =>
          rw [hC0] at hApply
          cases opt0 with
          | none => cases hApply
          | some env₀ =>
            cases hImp : absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ with
            | false =>
              have hCT : (!false && !(match (some (some env₀) : Option (Option (List AbsSlot))) with
                  | some (some e) => absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = true := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_true hCT] at hApply; cases hApply
            | true =>
              have hCF : (!false && !(match (some (some env₀) : Option (Option (List AbsSlot))) with
                  | some (some e) => absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = false := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_false hCF] at hApply
              cases hBlk : applyCopyPropBlocks bSrc cert 0 bSrc.basicBlocks with
              | none => rw [hBlk] at hApply; cases hApply
              | some bbs' =>
                rw [hBlk] at hApply; injection hApply with eB
                exact ⟨fun _ => ⟨env₀, rfl, hImp⟩, bbs', rfl, eB.symm⟩
    let ⟨hCert0Fn, bbs', hBlk, eB⟩ := hProceed
    subst eB
    let ⟨hBBLen, hStCl, _⟩ := applyCopyPropBlocks_props hBlk
    have hBBEmpty := list_isEmpty_eq_of_length hBBLen
    have hHdr : bodyHeaderEq bSrc { bSrc with basicBlocks := bbs' } = true :=
      bodyHeaderEq_refl bSrc
    have hMarker : ∀ idx,
        hasStorageAnnotation bSrc idx =
          hasStorageAnnotation { bSrc with basicBlocks := bbs' } idx := by
      intro idx
      unfold hasStorageAnnotation; dsimp only
      exact list_any_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 =>
        (stmtListStoragePreserved_props (hStCl i bb₁ bb₂ h1 h2).1).2.1 idx)
    have hBounds :
        storageAnnotationsInBounds bSrc =
          storageAnnotationsInBounds { bSrc with basicBlocks := bbs' } := by
      unfold storageAnnotationsInBounds; dsimp only
      exact list_all_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 =>
        (stmtListStoragePreserved_props (hStCl i bb₁ bb₂ h1 h2).1).2.2
          (fun stmt => match stmt with
            | .storageLive id | .storageDead id => Nat.blt id bSrc.locals.length
            | _ => true)
          (fun _ _ => rfl) rfl)
    exact ⟨hHdr, hBBLen, hBBEmpty, hBounds,
      fun args => initLocalsLoop_eq_of_storage_eq args rfl rfl (fun idx _ _ => hMarker idx),
      hCert0Fn, hBlk⟩

private noncomputable def CopyPropInv (cert : ProgramAbsCert)
    (pSrc pTgt : Program) (s : State) : Prop :=
  ∃ f bCert bSrc bTgt,
    s.frames = [f] ∧
    Trusted.MirSemantics.getElem? cert f.defId = some bCert ∧
    Trusted.MirSemantics.getElem? pSrc.bodies f.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies f.defId = some bTgt ∧
    applyCopyPropBody bCert bSrc = some bTgt ∧
    (f.blockIdx < bSrc.basicBlocks.length →
      ∃ bbSrc bbTgt aliases env exitAliases exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks f.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks f.blockIdx = some bbTgt ∧
        rewriteCopyPropStmts bSrc.locals aliases env
          (bbSrc.statements.drop f.stmtIdx) =
          some (bbTgt.statements.drop f.stmtIdx, exitAliases, exitEnv) ∧
        bbTgt.terminator = rewriteCopyPropTerm exitAliases bbSrc.terminator ∧
        bbSrc.cleanup = bbTgt.cleanup ∧
        checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length bCert
          exitEnv bbSrc.terminator = true ∧
        AbsEnvSound bSrc.locals env f.locals ∧
        AllAliasesSound bSrc.locals f.locals aliases)

private theorem copyProp_init_eq {cert : ProgramAbsCert} {pSrc pTgt : Program}
    (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applyCopyPropBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    initState pSrc q = initState pTgt q := by
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  have hBodyLen : pSrc.bodies.length = pTgt.bodies.length :=
    (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
  apply initState_eq_of_matching_entry q hHdr
  · constructor
    · intro hN
      have hGe : pTgt.bodies.length ≤ pTgt.entryDefId := by
        rw [← hBodyLen, ← hEnt]; exact getElem?_none_ge hN
      exact getElem?_none_of_ge hGe
    · intro hN
      have hGe : pSrc.bodies.length ≤ pSrc.entryDefId := by
        rw [hBodyLen, hEnt]; exact getElem?_none_ge hN
      exact getElem?_none_of_ge hGe
  · intro bSrc hBS
    let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    rw [hEnt] at hBT
    let ⟨hBHdr, _, hEmp, hBnd, hInitL, _, _⟩ := applyCopyPropBody_props hAp
    exact ⟨bTgt, hBT, hBHdr, hEmp, hBnd, hInitL q.args⟩

private theorem copyProp_query_iff {cert : ProgramAbsCert} {pSrc pTgt : Program}
    (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applyCopyPropBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  apply lockstep_inv_query_iff (Inv := CopyPropInv cert pSrc pTgt)
    (copyProp_init_eq q hLenC hHdr hMap)
  · intro s₀ hInitS
    let ⟨_, _, bSrc, hBS, hNotEmp, _, _, _, hArgs, hs0⟩ := initState_ok_elim hInitS
    subst hs0
    let ⟨bCert, bTgt, hBC, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    let ⟨_, _, _, _, _, hCert0Fn, hBlk⟩ := applyCopyPropBody_props hAp
    let ⟨_, _, hAct⟩ := applyCopyPropBlocks_props hBlk
    let ⟨env₀, hC0, hImp0⟩ := hCert0Fn hNotEmp
    have hSound0 : AbsEnvSound bSrc.locals env₀ (initLocalsLoop bSrc q.args 0 bSrc.locals) :=
      absEnvImplies_sound hImp0 (initAbsEnvLoop_sound hArgs)
    refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, ?_⟩
    intro h0Lt
    let ⟨bbSrc0, hBBS0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
    let ⟨bbTgt0, stmts0', exitA0, exitE0, hBBT0, _, hRew0, hEdg0, eBB0⟩ :=
      hAct 0 bbSrc0 env₀ hBBS0 hC0
    subst eBB0
    exact ⟨bbSrc0, _, [], env₀, exitA0, exitE0, hBBS0, hBBT0,
           hRew0, rfl, rfl, hEdg0, hSound0, True.intro⟩
  · intro s hInv
    let ⟨f, bCert, bSrc, bTgt, hFr, hBC, hBS, hBT, hAp, hBlkInv⟩ := hInv
    let ⟨hBHdr, hBBLen, _, _, _, _, hBlk⟩ := applyCopyPropBody_props hAp
    let ⟨_, _, hAct⟩ := applyCopyPropBlocks_props hBlk
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    cases s with
    | mk frames cm =>
      dsimp at hFr; subst hFr
      cases Nat.lt_or_ge f.blockIdx bSrc.basicBlocks.length with
      | inr hGe =>
        have hGeT : bTgt.basicBlocks.length ≤ f.blockIdx := by rw [← hBBLen]; exact hGe
        have hStepEq : evalStep pSrc 0 { frames := [f], callerMem := cm } =
            evalStep pTgt 0 { frames := [f], callerMem := cm } := by
          unfold evalStep; dsimp
          rw [hBS, hBT]; dsimp
          rw [getElem?_none_of_ge hGe, getElem?_none_of_ge hGeT]
        refine ⟨hStepEq, fun s' hSt => ?_⟩
        unfold evalStep at hSt; dsimp at hSt
        rw [hBS] at hSt; dsimp at hSt
        rw [getElem?_none_of_ge hGe] at hSt; cases hSt
      | inl hLt =>
        let ⟨bbSrc, bbTgt, aliases, env, exitA, exitE, hBBS, hBBT,
             hRewRem, hTermEq, hCleanEq, hEdg, hEnvS, hAliasesS⟩ := hBlkInv hLt
        cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements f.stmtIdx with
        | some sSrc =>
          have hDropS := drop_eq_cons_of_getElem? hStS
          rw [hDropS] at hRewRem
          let ⟨sTgt, restTgt, aliases', env', hDropTEq, hRewNext, hEvStmtEq, hNextFn⟩ :=
            rewriteCopyPropStmts_step (bTgt := bTgt) (frame := f) (cm := cm)
              hLocEq hEnvS hAliasesS hRewRem
          let ⟨hStT, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropTEq
          have hStepEq : evalStep pSrc 0 { frames := [f], callerMem := cm } =
              evalStep pTgt 0 { frames := [f], callerMem := cm } := by
            unfold evalStep; dsimp
            rw [hBS, hBT]; dsimp
            rw [hBBS, hBBT]; dsimp
            rw [hStS, hStT]; dsimp
            exact hEvStmtEq
          refine ⟨hStepEq, fun s' hStepS => ?_⟩
          unfold evalStep at hStepS; dsimp at hStepS
          rw [hBS] at hStepS; dsimp at hStepS
          rw [hBBS] at hStepS; dsimp at hStepS
          rw [hStS] at hStepS; dsimp at hStepS
          let ⟨locs', hs', hEnv', hAliases'⟩ := hNextFn s' hStepS
          subst hs'
          refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, fun _ => ?_⟩
          refine ⟨bbSrc, bbTgt, aliases', env', exitA, exitE, hBBS, hBBT, ?_,
            hTermEq, hCleanEq, hEdg, hEnv', hAliases'⟩
          dsimp
          rw [(getElem?_of_drop_eq_cons hDropS).2, hDropTNext]
          exact hRewNext
        | none =>
          have hGeS := getElem?_none_ge hStS
          have hDropSNil := drop_eq_nil_of_ge hGeS
          rw [hDropSNil] at hRewRem
          dsimp [rewriteCopyPropStmts] at hRewRem
          injection hRewRem with eP
          injection eP with hDropTNilSym eAE
          injection eAE with eA eE
          subst eA; subst eE
          have hDropTNil := hDropTNilSym.symm
          have hStmtsLenEq : bbSrc.statements.length = bbTgt.statements.length := by
            let ⟨_, hStCl, _⟩ := applyCopyPropBlocks_props hBlk
            exact (stmtListStoragePreserved_props (hStCl f.blockIdx bbSrc bbTgt hBBS hBBT).1).1
          have hStTNone : Trusted.MirSemantics.getElem? bbTgt.statements f.stmtIdx = none :=
            getElem?_none_of_ge (by rw [← hStmtsLenEq]; exact hGeS)
          have hStepEq : evalStep pSrc 0 { frames := [f], callerMem := cm } =
              evalStep pTgt 0 { frames := [f], callerMem := cm } := by
            unfold evalStep; dsimp
            rw [hBS, hBT]; dsimp
            rw [hBBS, hBBT]; dsimp
            rw [hStS, hStTNone]; dsimp
            rw [hStmtsLenEq]
            cases Nat.beq f.stmtIdx bbTgt.statements.length with
            | false => rfl
            | true =>
              dsimp
              exact rewriteCopyPropTerm_eval_eq hLocEq hCleanEq hTermEq hAliasesS
          refine ⟨hStepEq, fun s' hStepS => ?_⟩
          unfold evalStep at hStepS; dsimp at hStepS
          rw [hBS] at hStepS; dsimp at hStepS
          rw [hBBS] at hStepS; dsimp at hStepS
          rw [hStS] at hStepS; dsimp at hStepS
          cases hEnd : Nat.beq f.stmtIdx bbSrc.statements.length with
          | false => rw [hEnd] at hStepS; cases hStepS
          | true =>
            rw [hEnd] at hStepS; dsimp at hStepS
            let ⟨tgt, locs', hs', _, hTgtCert⟩ :=
              checkAbsTerminatorEdges_step_sound hEnvS hEdg hStepS
            subst hs'
            refine ⟨_, bCert, bSrc, bTgt, rfl, hBC, hBS, hBT, hAp, ?_⟩
            intro hTgtLt
            let ⟨tgtEnv, hCTgt, hTgtEnvS⟩ := hTgtCert hTgtLt
            let ⟨bbNextS, hBBNS⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt hTgtLt
            have hCTgt0 : Trusted.MirSemantics.getElem? bCert (0 + tgt) = some (some tgtEnv) := by
              rw [Nat.zero_add]; exact hCTgt
            let ⟨bbNextT, nextStmts', nextExitA, nextExitE, hBBNT, _, hRewN, hEdgN, eBBN⟩ :=
              hAct tgt bbNextS tgtEnv hBBNS hCTgt0
            subst eBBN
            exact ⟨bbNextS, _, [], tgtEnv, nextExitA, nextExitE, hBBNS, hBBNT,
                   hRewN, rfl, rfl, hEdgN, hTgtEnvS, True.intro⟩

private theorem applyCopyPropProgram_equiv {cert : ProgramAbsCert}
    {pSrc pTgt : Program}
    (hApply : applyCopyPropProgram cert pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  unfold applyCopyPropProgram at hApply
  cases hLenB : Nat.beq cert.length pSrc.bodies.length with
  | false => rw [hLenB] at hApply; cases hApply
  | true =>
    rw [hLenB] at hApply; dsimp at hApply
    have hLenC := nat_beq_eq hLenB
    cases hMap : mapOption (fun pr => applyCopyPropBody pr.1 pr.2)
        (List.zip cert pSrc.bodies) with
    | none => rw [hMap] at hApply; cases hApply
    | some bodies' =>
      rw [hMap] at hApply; injection hApply with eP; subst eP
      have hHdr := programHeaderEq_with_bodies pSrc bodies'
      have hBodyLen : pSrc.bodies.length = bodies'.length :=
        (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
      have hIds : pSrc.bodies.map Body.identity = bodies'.map Body.identity := by
        apply list_eq_of_getElem?_eq
        · rw [map_length_eq, map_length_eq, hBodyLen]
        · intro i
          rw [getElem?_map, getElem?_map]
          cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies i with
          | none =>
            have hGe : bodies'.length ≤ i := by
              rw [← hBodyLen]; exact getElem?_none_ge hBS
            rw [getElem?_none_of_ge hGe]
          | some bSrc =>
            let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
            let ⟨hBHdr, _, _, _, _, _, _⟩ := applyCopyPropBody_props hAp
            let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim hBHdr
            rw [hBT]; dsimp [Option.map]; rw [hIdEq]
      refine ⟨?_, hHdr, hIds⟩
      refine fullSemanticEquiv_of_query_iff hHdr ?_ ?_ ?_
      · intro defId bSrc bTgt hBS hBT
        let ⟨_, bTgt', _, hBT', hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
        dsimp at hBT; rw [hBT] at hBT'; injection hBT' with eB; subst eB
        let ⟨hBHdr, _, hEmp, hBnd, _, _, _⟩ := applyCopyPropBody_props hAp
        exact ⟨hBHdr, hEmp, hBnd⟩
      · intro q
        exact copyProp_query_iff q hLenC hHdr hMap
      · intro defId args
        exact (copyProp_query_iff
          (pSrc := entryProgForBody pSrc defId)
          (pTgt := entryProgForBody { pSrc with bodies := bodies' } defId)
          { args := args } hLenC
          (programHeaderEq_entryProg defId hHdr) hMap).1

/-! #### Part D.2: `DestinationPropagation` (`applyDestPropProgram_equiv`) -/

private theorem matchDestPropCandidate?_elim {bodyLocals : List MirTy}
    {env : List AbsSlot} {s₁ s₂ : StatementKind}
    {tmp : LocalId} {dstPlace : Place} {rv₁ : Rvalue}
    (hM : matchDestPropCandidate? bodyLocals env s₁ s₂ = some (tmp, dstPlace, rv₁)) :
    ∃ tmpPlace rvUse dstTy tmpSlot dstSlot,
      s₁ = .assign tmpPlace rv₁ ∧
      s₂ = .assign dstPlace rvUse ∧
      tmp = tmpPlace.localId ∧
      tmpPlace.projection.isEmpty = true ∧
      dstPlace.projection.isEmpty = true ∧
      tmp ≠ 0 ∧
      tmp ≠ dstPlace.localId ∧
      rvalueTouchesLocal tmp rv₁ = false ∧
      isDestPropCopyOrMoveTmp tmp rvUse = true ∧
      Trusted.MirSemantics.getElem? bodyLocals tmp = some dstTy ∧
      Trusted.MirSemantics.getElem? bodyLocals dstPlace.localId = some dstTy ∧
      Trusted.MirSemantics.getElem? env tmp = some tmpSlot ∧
      Trusted.MirSemantics.getElem? env dstPlace.localId = some dstSlot ∧
      isSupportedScalarOrUnitTy dstTy = true ∧
      absSlotImplies tmpSlot .liveUninit = true ∧
      absSlotImplies dstSlot .liveUninit = true := by
  cases s₁ with
  | nop | storageLive _ | storageDead _ | unsupported => cases hM
  | assign tmpPlace rvA =>
    cases s₂ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hM
    | assign dstPlace' rvUse =>
      dsimp [matchDestPropCandidate?] at hM
      cases hEmp : (tmpPlace.projection.isEmpty && dstPlace'.projection.isEmpty) with
      | false => rw [hEmp] at hM; cases hM
      | true =>
        rw [hEmp] at hM; dsimp at hM
        let ⟨hTEmp, hDEmp⟩ := bool_and_true hEmp
        cases hMid : (!Nat.beq tmpPlace.localId 0 &&
            !Nat.beq tmpPlace.localId dstPlace'.localId &&
            !rvalueTouchesLocal tmpPlace.localId rvA &&
            isDestPropCopyOrMoveTmp tmpPlace.localId rvUse) with
        | false => rw [if_bool_false hMid] at hM; cases hM
        | true =>
          rw [if_bool_true hMid] at hM
          let ⟨hM123, hUseTmp⟩ := bool_and_true hMid
          let ⟨hM12, hNoTouchB⟩ := bool_and_true hM123
          let ⟨hNe0B, hNeDstB⟩ := bool_and_true hM12
          cases hTTy : Trusted.MirSemantics.getElem? bodyLocals tmpPlace.localId with
          | none => rw [hTTy] at hM; cases hM
          | some tmpTy =>
            rw [hTTy] at hM
            cases hDTy : Trusted.MirSemantics.getElem? bodyLocals dstPlace'.localId with
            | none => rw [hDTy] at hM; cases hM
            | some dstTy =>
              rw [hDTy] at hM
              cases hET : Trusted.MirSemantics.getElem? env tmpPlace.localId with
              | none => rw [hET] at hM; cases hM
              | some tmpSlot =>
                rw [hET] at hM
                cases hED : Trusted.MirSemantics.getElem? env dstPlace'.localId with
                | none => rw [hED] at hM; cases hM
                | some dstSlot =>
                  rw [hED] at hM; dsimp at hM
                  cases hG : (MirTy.beq tmpTy dstTy &&
                      isSupportedScalarOrUnitTy dstTy &&
                      absSlotImplies tmpSlot .liveUninit &&
                      absSlotImplies dstSlot .liveUninit) with
                  | false => rw [if_bool_false hG] at hM; cases hM
                  | true =>
                    rw [if_bool_true hG] at hM
                    injection hM with eTuple
                    injection eTuple with eTmp ePair
                    injection ePair with eDst eRv
                    subst eTmp; subst eDst; subst eRv
                    let ⟨hG123, hDstImp⟩ := bool_and_true hG
                    let ⟨hG12, hTmpImp⟩ := bool_and_true hG123
                    let ⟨hTyEqB, hSup⟩ := bool_and_true hG12
                    have hTyEq := mirTy_beq_eq hTyEqB; subst hTyEq
                    exact ⟨tmpPlace, rvUse, tmpTy, tmpSlot, dstSlot,
                      rfl, rfl, rfl, hTEmp, hDEmp,
                      nat_ne_of_beq_false (bool_not_true hNe0B),
                      nat_ne_of_beq_false (bool_not_true hNeDstB),
                      bool_not_true hNoTouchB, hUseTmp,
                      hTTy, hDTy, hET, hED, hSup, hTmpImp, hDstImp⟩

private theorem evalOperandToSlot_untouched_preserves {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {x : LocalId} {op : Operand}
    {ty : MirTy} {optVal : Option Val}
    (hNoT : operandTouchesLocal x op = false)
    (hEv : evalOperandToSlot bodyLocals locals op = .ok (ty, optVal, locals')) :
    Trusted.MirSemantics.getElem? locals' x = Trusted.MirSemantics.getElem? locals x := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok _ =>
      rw [hC] at hEv; injection hEv with q1; injection q1 with _ q2
      injection q2 with _ qL; subst qL; rfl
  | copy p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some _ =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            injection hEv with q1; injection q1 with _ q2
            injection q2 with _ qL; subst qL; rfl
  | move p =>
    dsimp [operandTouchesLocal] at hNoT
    have hNe : x ≠ p.localId := (nat_ne_of_beq_false hNoT).symm
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some t =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            dsimp at hEv
            cases hSet : setElem? locals p.localId (liveUninitSlot t) with
            | none => rw [hSet] at hEv; cases hEv
            | some l1 =>
              rw [hSet] at hEv; injection hEv with q1; injection q1 with _ q2
              injection q2 with _ qL; subst qL
              exact setElem?_getElem?_ne hSet hNe

private theorem evalPrimitiveOperand_untouched_preserves {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {x : LocalId} {op : Operand} {v : Val}
    (hNoT : operandTouchesLocal x op = false)
    (hEv : evalPrimitiveOperand bodyLocals locals op = .ok (v, locals')) :
    Trusted.MirSemantics.getElem? locals' x = Trusted.MirSemantics.getElem? locals x := by
  dsimp [evalPrimitiveOperand] at hEv
  cases hS : evalOperandToSlot bodyLocals locals op with
  | error _ => rw [hS] at hEv; cases hEv
  | ok res =>
    let ⟨ty0, optV, l1⟩ := res
    rw [hS] at hEv; dsimp at hEv
    cases hPr : isPrimitiveReadableTy ty0 with
    | false => rw [hPr] at hEv; cases hEv
    | true =>
      rw [hPr] at hEv; dsimp at hEv
      cases optV with
      | none => cases hEv
      | some _ =>
        injection hEv with q1; injection q1 with _ qL; subst qL
        exact evalOperandToSlot_untouched_preserves hNoT hS

private theorem evalRvalue_untouched_preserves {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {x : LocalId} {dstTy : MirTy}
    {rv : Rvalue} {v : Val}
    (hNoT : rvalueTouchesLocal x rv = false)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    Trusted.MirSemantics.getElem? locals' x = Trusted.MirSemantics.getElem? locals x := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalue] at hEv
    cases hS : evalOperandToSlot bodyLocals locals opnd with
    | error _ => rw [hS] at hEv; cases hEv
    | ok res =>
      let ⟨sTy, optV, l1⟩ := res
      rw [hS] at hEv; dsimp at hEv
      cases hEqTy : MirTy.beq sTy dstTy with
      | false => rw [hEqTy] at hEv; cases hEv
      | true =>
        rw [hEqTy] at hEv; dsimp at hEv
        cases optV with
        | none => cases hEv
        | some _ =>
          injection hEv with q1; injection q1 with _ qL; subst qL
          exact evalOperandToSlot_untouched_preserves hNoT hS
  | unaryOp op opnd =>
    dsimp [evalRvalue] at hEv
    cases hO : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [hO] at hEv; cases hEv
    | ok res =>
      let ⟨ov, l1⟩ := res
      rw [hO] at hEv; dsimp at hEv
      cases hU : evalUnOp op ov with
      | error _ => rw [hU] at hEv; cases hEv
      | ok _ =>
        rw [hU] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
        exact evalPrimitiveOperand_untouched_preserves hNoT hO
  | binaryOp op lhs rhs =>
    let ⟨hNoL, hNoR⟩ := bool_or_false hNoT
    dsimp [evalRvalue] at hEv
    cases hL : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [hL] at hEv; cases hEv
    | ok resL =>
      let ⟨lv, l1⟩ := resL
      rw [hL] at hEv; dsimp at hEv
      cases hR : evalPrimitiveOperand bodyLocals l1 rhs with
      | error _ => rw [hR] at hEv; cases hEv
      | ok resR =>
        let ⟨rvv, l2⟩ := resR
        rw [hR] at hEv; dsimp at hEv
        cases hB : evalBinOp op lv rvv with
        | error _ => rw [hB] at hEv; cases hEv
        | ok _ =>
          rw [hB] at hEv; injection hEv with q1; injection q1 with _ qL2; subst qL2
          exact (evalPrimitiveOperand_untouched_preserves hNoR hR).trans
            (evalPrimitiveOperand_untouched_preserves hNoL hL)
  | discriminant p =>
    dsimp [evalRvalue] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases ty with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hSl] at hEv; cases hEv
          | some slot =>
            rw [hSl] at hEv; dsimp at hEv
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEv; cases hEv
            | true =>
              rw [hAdm] at hEv; dsimp at hEv
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp at hEv
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEv; cases hEv
                    | some _ =>
                      rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL; rfl
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL; rfl
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
              | scalar _ _ =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none => cases hEv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL; rfl
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEv

private theorem evalOperandToSlot_preserves_live {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {op : Operand}
    {ty : MirTy} {optVal : Option Val} {i : LocalId} {opt : Option Val}
    (hEv : evalOperandToSlot bodyLocals locals op = .ok (ty, optVal, locals'))
    (hLive : Trusted.MirSemantics.getElem? locals i = some (.live opt)) :
    ∃ opt', Trusted.MirSemantics.getElem? locals' i = some (.live opt') := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok _ =>
      rw [hC] at hEv; injection hEv with q1; injection q1 with _ q2
      injection q2 with _ qL; subst qL; exact ⟨opt, hLive⟩
  | copy p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some _ =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            injection hEv with q1; injection q1 with _ q2
            injection q2 with _ qL; subst qL; exact ⟨opt, hLive⟩
  | move p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some t =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            dsimp at hEv
            cases hSet : setElem? locals p.localId (liveUninitSlot t) with
            | none => rw [hSet] at hEv; cases hEv
            | some l1 =>
              rw [hSet] at hEv; injection hEv with q1; injection q1 with _ q2
              injection q2 with _ qL; subst qL
              cases hEq : Nat.beq i p.localId with
              | true =>
                have hi := nat_beq_eq hEq; subst hi
                let ⟨optU, hOptU⟩ := liveUninitSlot_isLive t
                exact ⟨optU, by rw [setElem?_getElem?_same hSet, hOptU]⟩
              | false =>
                exact ⟨opt, by rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hEq)]; exact hLive⟩

private theorem evalPrimitiveOperand_preserves_live {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {op : Operand} {v : Val}
    {i : LocalId} {opt : Option Val}
    (hEv : evalPrimitiveOperand bodyLocals locals op = .ok (v, locals'))
    (hLive : Trusted.MirSemantics.getElem? locals i = some (.live opt)) :
    ∃ opt', Trusted.MirSemantics.getElem? locals' i = some (.live opt') := by
  dsimp [evalPrimitiveOperand] at hEv
  cases hS : evalOperandToSlot bodyLocals locals op with
  | error _ => rw [hS] at hEv; cases hEv
  | ok res =>
    let ⟨ty0, optV, l1⟩ := res
    rw [hS] at hEv; dsimp at hEv
    cases hPr : isPrimitiveReadableTy ty0 with
    | false => rw [hPr] at hEv; cases hEv
    | true =>
      rw [hPr] at hEv; dsimp at hEv
      cases optV with
      | none => cases hEv
      | some _ =>
        injection hEv with q1; injection q1 with _ qL; subst qL
        exact evalOperandToSlot_preserves_live hS hLive

private theorem evalRvalue_preserves_live {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dstTy : MirTy} {rv : Rvalue} {v : Val}
    {i : LocalId} {opt : Option Val}
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals'))
    (hLive : Trusted.MirSemantics.getElem? locals i = some (.live opt)) :
    ∃ opt', Trusted.MirSemantics.getElem? locals' i = some (.live opt') := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalue] at hEv
    cases hS : evalOperandToSlot bodyLocals locals opnd with
    | error _ => rw [hS] at hEv; cases hEv
    | ok res =>
      let ⟨sTy, optV, l1⟩ := res
      rw [hS] at hEv; dsimp at hEv
      cases hEqTy : MirTy.beq sTy dstTy with
      | false => rw [hEqTy] at hEv; cases hEv
      | true =>
        rw [hEqTy] at hEv; dsimp at hEv
        cases optV with
        | none => cases hEv
        | some _ =>
          injection hEv with q1; injection q1 with _ qL; subst qL
          exact evalOperandToSlot_preserves_live hS hLive
  | unaryOp op opnd =>
    dsimp [evalRvalue] at hEv
    cases hO : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [hO] at hEv; cases hEv
    | ok res =>
      let ⟨ov, l1⟩ := res
      rw [hO] at hEv; dsimp at hEv
      cases hU : evalUnOp op ov with
      | error _ => rw [hU] at hEv; cases hEv
      | ok _ =>
        rw [hU] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
        exact evalPrimitiveOperand_preserves_live hO hLive
  | binaryOp op lhs rhs =>
    dsimp [evalRvalue] at hEv
    cases hL : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [hL] at hEv; cases hEv
    | ok resL =>
      let ⟨lv, l1⟩ := resL
      rw [hL] at hEv; dsimp at hEv
      cases hR : evalPrimitiveOperand bodyLocals l1 rhs with
      | error _ => rw [hR] at hEv; cases hEv
      | ok resR =>
        let ⟨rvv, l2⟩ := resR
        rw [hR] at hEv; dsimp at hEv
        cases hB : evalBinOp op lv rvv with
        | error _ => rw [hB] at hEv; cases hEv
        | ok _ =>
          rw [hB] at hEv; injection hEv with q1; injection q1 with _ qL2; subst qL2
          let ⟨opt1, h1⟩ := evalPrimitiveOperand_preserves_live hL hLive
          exact evalPrimitiveOperand_preserves_live hR h1
  | discriminant p =>
    dsimp [evalRvalue] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases ty with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hSl] at hEv; cases hEv
          | some slot =>
            rw [hSl] at hEv; dsimp at hEv
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEv; cases hEv
            | true =>
              rw [hAdm] at hEv; dsimp at hEv
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt0 =>
                  cases opt0 with
                  | none =>
                    dsimp at hEv
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEv; cases hEv
                    | some _ =>
                      rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                      exact ⟨opt, hLive⟩
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                          exact ⟨opt, hLive⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
              | scalar _ _ =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt0 =>
                  cases opt0 with
                  | none => cases hEv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                          exact ⟨opt, hLive⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEv

private inductive DestPropTail (bodyLocals : List MirTy) (deadAtEntry : BodyDeadCert)
    (numBlocks : Nat) (term : TerminatorKind) :
    List AbsSlot → List StatementKind → List StatementKind → List AbsSlot → Prop where
  | nil (env : List AbsSlot) :
      DestPropTail bodyLocals deadAtEntry numBlocks term env [] [] env
  | kept {env env₁ exitEnv : List AbsSlot} {s : StatementKind}
      {restSrc restTgt : List StatementKind} :
      stepPlainStmtAbs bodyLocals env s = some env₁ →
      DestPropTail bodyLocals deadAtEntry numBlocks term env₁ restSrc restTgt exitEnv →
      DestPropTail bodyLocals deadAtEntry numBlocks term env
        (s :: restSrc) (s :: restTgt) exitEnv
  | pair {env env₁ env₂ exitEnv : List AbsSlot}
      {s₁ s₂ : StatementKind} {tmp : LocalId} {dstPlace : Place} {rv₁ : Rvalue}
      {restSrc restTgt : List StatementKind} :
      matchDestPropCandidate? bodyLocals env s₁ s₂ = some (tmp, dstPlace, rv₁) →
      stepPlainStmtAbs bodyLocals env s₁ = some env₁ →
      stepPlainStmtAbs bodyLocals env₁ s₂ = some env₂ →
      isDeadAcrossCfg bodyLocals.length deadAtEntry numBlocks tmp restTgt term = true →
      DestPropTail bodyLocals deadAtEntry numBlocks term env₂ restSrc restTgt exitEnv →
      DestPropTail bodyLocals deadAtEntry numBlocks term env
        (s₁ :: s₂ :: restSrc) ((.assign dstPlace rv₁) :: .nop :: restTgt) exitEnv

private theorem rewriteDestPropStmts_sound_aux {bodyLocals : List MirTy}
    {deadAtEntry : BodyDeadCert} {numBlocks : Nat} {term : TerminatorKind} :
    ∀ n {env ss ss' exitEnv},
      ss.length ≤ n →
      rewriteDestPropStmts bodyLocals deadAtEntry numBlocks term env ss =
        some (ss', exitEnv) →
      DestPropTail bodyLocals deadAtEntry numBlocks term env ss ss' exitEnv ∧
      StmtListStoragePreserved ss ss' := by
  intro n
  induction n with
  | zero =>
    intro env ss ss' exitEnv hLen hRew
    cases ss with
    | nil =>
      injection hRew with e; injection e with e1 e2; subst e1; subst e2
      exact ⟨.nil env, True.intro⟩
    | cons _ _ => exact False.elim (Nat.not_succ_le_zero _ hLen)
  | succ k ih =>
    intro env ss ss' exitEnv hLen hRew
    cases ss with
    | nil =>
      injection hRew with e; injection e with e1 e2; subst e1; subst e2
      exact ⟨.nil env, True.intro⟩
    | cons s₁ tail =>
      cases tail with
      | nil =>
        dsimp [rewriteDestPropStmts] at hRew
        cases hSt1 : stepPlainStmtAbs bodyLocals env s₁ with
        | none => rw [hSt1] at hRew; cases hRew
        | some e1 =>
          rw [hSt1] at hRew; injection hRew with e; injection e with eS eE
          subst eS; subst eE
          exact ⟨.kept hSt1 (.nil e1), ⟨Or.inl rfl, True.intro⟩⟩
      | cons s₂ rest =>
        dsimp [rewriteDestPropStmts] at hRew
        have hLe1 : (s₂ :: rest).length ≤ k := Nat.le_of_succ_le_succ hLen
        have hLe2 : rest.length ≤ k := Nat.le_trans (Nat.le_succ rest.length) hLe1
        cases hCand : matchDestPropCandidate? bodyLocals env s₁ s₂ with
        | none =>
          rw [hCand] at hRew; dsimp at hRew
          cases hSt1 : stepPlainStmtAbs bodyLocals env s₁ with
          | none => rw [hSt1] at hRew; cases hRew
          | some env₁ =>
            rw [hSt1] at hRew; dsimp at hRew
            cases hRec : rewriteDestPropStmts bodyLocals deadAtEntry numBlocks term
                env₁ (s₂ :: rest) with
            | none => rw [hRec] at hRew; cases hRew
            | some pr =>
              let ⟨tailTgt, exE⟩ := pr
              rw [hRec] at hRew; injection hRew with e; injection e with e1 e2
              subst e1; subst e2
              let ⟨hTail, hSt⟩ := ih hLe1 hRec
              exact ⟨.kept hSt1 hTail, ⟨Or.inl rfl, hSt⟩⟩
        | some cand =>
          let ⟨tmp, dstPlace, rv₁⟩ := cand
          rw [hCand] at hRew; dsimp at hRew
          cases hSt1 : stepPlainStmtAbs bodyLocals env s₁ with
          | none => rw [hSt1] at hRew; cases hRew
          | some env₁ =>
            rw [hSt1] at hRew; dsimp at hRew
            cases hSt2 : stepPlainStmtAbs bodyLocals env₁ s₂ with
            | none => rw [hSt2] at hRew; cases hRew
            | some env₂ =>
              rw [hSt2] at hRew; dsimp at hRew
              cases hRec2 : rewriteDestPropStmts bodyLocals deadAtEntry numBlocks term
                  env₂ rest with
              | none => rw [hRec2] at hRew; cases hRew
              | some pr2 =>
                let ⟨restTgt, exE2⟩ := pr2
                rw [hRec2] at hRew; dsimp only at hRew
                cases hDead : isDeadAcrossCfg bodyLocals.length deadAtEntry numBlocks
                    tmp restTgt term with
                | true =>
                  rw [if_bool_true hDead] at hRew
                  injection hRew with e; injection e with e1 e2
                  subst e1; subst e2
                  let ⟨hTail2, hSt2P⟩ := ih hLe2 hRec2
                  let ⟨_, _, _, _, _, hs1, hs2, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
                    matchDestPropCandidate?_elim hCand
                  subst hs1; subst hs2
                  exact ⟨.pair hCand hSt1 hSt2 hDead hTail2,
                         ⟨Or.inr ⟨True.intro, True.intro⟩,
                          ⟨Or.inr ⟨True.intro, True.intro⟩, hSt2P⟩⟩⟩
                | false =>
                  rw [if_bool_false hDead] at hRew
                  cases hRec1 : rewriteDestPropStmts bodyLocals deadAtEntry numBlocks term
                      env₁ (s₂ :: rest) with
                  | none => rw [hRec1] at hRew; cases hRew
                  | some pr1 =>
                    let ⟨tailTgt, exE1⟩ := pr1
                    rw [hRec1] at hRew; injection hRew with e; injection e with e1 e2
                    subst e1; subst e2
                    let ⟨hTail1, hSt1P⟩ := ih hLe1 hRec1
                    exact ⟨.kept hSt1 hTail1, ⟨Or.inl rfl, hSt1P⟩⟩

private noncomputable def DestPropMidLocals (bodyLocals : List MirTy)
    (D_after : LocalId → Prop) (tmp dst : LocalId) (dstTy : MirTy) (val : Val)
    (locs₁ locs₂ : List LocalSlot) : Prop :=
  LocalsWellTyped bodyLocals locs₁ ∧
  LocalsWellTyped bodyLocals locs₂ ∧
  tmp ≠ 0 ∧
  tmp ≠ dst ∧
  D_after tmp ∧
  Trusted.MirSemantics.getElem? bodyLocals tmp = some dstTy ∧
  Trusted.MirSemantics.getElem? bodyLocals dst = some dstTy ∧
  checkVal val dstTy = true ∧
  Trusted.MirSemantics.getElem? locs₁ tmp = some (.live (some val)) ∧
  Trusted.MirSemantics.getElem? locs₂ dst = some (.live (some val)) ∧
  (∃ optD1, Trusted.MirSemantics.getElem? locs₁ dst = some (.live optD1)) ∧
  (∃ optT2, Trusted.MirSemantics.getElem? locs₂ tmp = some (.live optT2)) ∧
  (∀ i,
    (∀ sl₁ sl₂,
      Trusted.MirSemantics.getElem? locs₁ i = some sl₁ →
      Trusted.MirSemantics.getElem? locs₂ i = some sl₂ →
      SameLiveness sl₁ sl₂) ∧
    (i ≠ tmp → i ≠ dst → ¬ D_after i →
      Trusted.MirSemantics.getElem? locs₁ i =
        Trusted.MirSemantics.getElem? locs₂ i))

private theorem destProp_pair_step1_bisim {bSrc bTgt : Body}
    {deadAtEntry : BodyDeadCert} {numBlocks : Nat}
    {env : List AbsSlot} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {tmpPlace dstPlace : Place} {rv₁ : Rvalue}
    {restTgt : List StatementKind} {termTgt : TerminatorKind}
    {dstTy : MirTy} {tmpSlot dstSlot : AbsSlot}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEnvS : AbsEnvSound bSrc.locals env fSrc.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks d
          ((.assign dstPlace rv₁) :: .nop :: restTgt) termTgt = true)
      fSrc.locals fTgt.locals)
    (hTEmp : tmpPlace.projection.isEmpty = true)
    (hDEmp : dstPlace.projection.isEmpty = true)
    (hTmpNe0 : tmpPlace.localId ≠ 0)
    (hTmpNeDst : tmpPlace.localId ≠ dstPlace.localId)
    (hNoTouchTmp : rvalueTouchesLocal tmpPlace.localId rv₁ = false)
    (hTTy : Trusted.MirSemantics.getElem? bSrc.locals tmpPlace.localId = some dstTy)
    (hDTy : Trusted.MirSemantics.getElem? bSrc.locals dstPlace.localId = some dstTy)
    (hETmp : Trusted.MirSemantics.getElem? env tmpPlace.localId = some tmpSlot)
    (hEDst : Trusted.MirSemantics.getElem? env dstPlace.localId = some dstSlot)
    (hTmpImp : absSlotImplies tmpSlot .liveUninit = true)
    (hDstImp : absSlotImplies dstSlot .liveUninit = true)
    (hTmpDeadRest : isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks
      tmpPlace.localId restTgt termTgt = true) :
    (∃ fk,
      evalStatement bSrc fSrc cm (.assign tmpPlace rv₁) = .fault fk ∧
      evalStatement bTgt fTgt cm (.assign dstPlace rv₁) = .fault fk) ∨
    (∃ val l1' l2',
      evalStatement bSrc fSrc cm (.assign tmpPlace rv₁) =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm (.assign dstPlace rv₁) =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                callerMem := cm } ∧
      DestPropMidLocals bSrc.locals
        (fun d => d ≠ 0 ∧
          isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks d restTgt termTgt = true)
        tmpPlace.localId dstPlace.localId dstTy val l1' l2') := by
  have hDTyTgt : Trusted.MirSemantics.getElem? bTgt.locals dstPlace.localId = some dstTy := by
    rw [← hLocEq]; exact hDTy
  have hUntouchedRv1 : ∀ d,
      (d ≠ 0 ∧ isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks d
        ((.assign dstPlace rv₁) :: .nop :: restTgt) termTgt = true) →
      rvalueTouchesLocal d rv₁ = false := by
    intro d ⟨_, hD⟩
    dsimp [isDeadAcrossCfg] at hD
    exact bool_not_true (bool_and_true (bool_and_true hD).1).2
  cases evalRvalue_untouched_bisim (dstTy := dstTy) hMask hUntouchedRv1 with
  | inl hErr =>
    let ⟨fk, hER1, hER2⟩ := hErr
    refine Or.inl ⟨fk, ?_, ?_⟩
    · dsimp [evalStatement]; rw [hTEmp]; dsimp; rw [hTTy]; dsimp; rw [hER1]
    · dsimp [evalStatement]; rw [hDEmp]; dsimp; rw [hDTyTgt]; dsimp
      rw [← hLocEq, hER2]
  | inr hOk =>
    let ⟨val, la1, la2, hOR1, hOR2, hMaskAfterR⟩ := hOk
    cases hChk : checkVal val dstTy with
    | false =>
      refine Or.inl ⟨.unsupported, ?_, ?_⟩
      · dsimp [evalStatement]; rw [hTEmp]; dsimp; rw [hTTy]; dsimp; rw [hOR1]; dsimp
        unfold writePlace; rw [hChk]; rfl
      · dsimp [evalStatement]; rw [hDEmp]; dsimp; rw [hDTyTgt]; dsimp
        rw [← hLocEq, hOR2]; dsimp; unfold writePlace; rw [hChk]; rfl
    | true =>
      have hLtTmp : tmpPlace.localId < bSrc.locals.length := getElem?_some_lt hTTy
      have hLtDst : dstPlace.localId < bSrc.locals.length := getElem?_some_lt hDTy
      let ⟨slT0, hG1T0⟩ := getElem?_some_of_lt fSrc.locals tmpPlace.localId
        (by rw [hEnvS.1.1]; exact hLtTmp)
      let ⟨_, optT0, hSlT0Eq⟩ := absSlotImplies_sound hTmpImp
        (hEnvS.2.2 tmpPlace.localId dstTy tmpSlot slT0 hTTy hETmp hG1T0)
      subst hSlT0Eq
      let ⟨slD0, hG1D0⟩ := getElem?_some_of_lt fSrc.locals dstPlace.localId
        (by rw [hEnvS.1.1]; exact hLtDst)
      let ⟨_, optD0, hSlD0Eq⟩ := absSlotImplies_sound hDstImp
        (hEnvS.2.2 dstPlace.localId dstTy dstSlot slD0 hDTy hEDst hG1D0)
      subst hSlD0Eq
      let ⟨slT2_0, hG2T0⟩ := getElem?_some_of_lt fTgt.locals tmpPlace.localId
        (by rw [hMask.2.1.1]; exact hLtTmp)
      have hSameT0 := (hMask.2.2 tmpPlace.localId).1 _ _ hG1T0 hG2T0
      cases slT2_0 with
      | dead => cases hSameT0
      | live optT2_0 =>
        let ⟨slD2_0, hG2D0⟩ := getElem?_some_of_lt fTgt.locals dstPlace.localId
          (by rw [hMask.2.1.1]; exact hLtDst)
        have hSameD0 := (hMask.2.2 dstPlace.localId).1 _ _ hG1D0 hG2D0
        cases slD2_0 with
        | dead => cases hSameD0
        | live optD2_0 =>
          have hLa1Tmp : Trusted.MirSemantics.getElem? la1 tmpPlace.localId =
              some (.live optT0) := by
            rw [evalRvalue_untouched_preserves hNoTouchTmp hOR1]; exact hG1T0
          let ⟨optD1_after, hLa1Dst⟩ := evalRvalue_preserves_live hOR1 hG1D0
          let ⟨optT2_after, hLa2Tmp⟩ := evalRvalue_preserves_live hOR2 hG2T0
          let ⟨optD2_after, hLa2Dst⟩ := evalRvalue_preserves_live hOR2 hG2D0
          let ⟨l1', hSet1⟩ := setElem?_some_of_lt la1 tmpPlace.localId (.live (some val))
            (by rw [hMaskAfterR.1.1]; exact hLtTmp)
          let ⟨l2', hSet2⟩ := setElem?_some_of_lt la2 dstPlace.localId (.live (some val))
            (by rw [hMaskAfterR.2.1.1]; exact hLtDst)
          have hWt1' := localsWellTyped_set hMaskAfterR.1 hTTy hSet1 hChk
          have hWt2' := localsWellTyped_set hMaskAfterR.2.1 hDTy hSet2 hChk
          refine Or.inr ⟨val, l1', l2', ?_, ?_, ?_⟩
          · dsimp [evalStatement]; rw [hTEmp]; dsimp; rw [hTTy]; dsimp; rw [hOR1]; dsimp
            unfold writePlace; rw [hChk]; dsimp; rw [hLa1Tmp]; dsimp; rw [hSet1]
          · dsimp [evalStatement]; rw [hDEmp]; dsimp; rw [hDTyTgt]; dsimp
            rw [← hLocEq, hOR2]; dsimp
            unfold writePlace; rw [hChk]; dsimp; rw [hLa2Dst]; dsimp; rw [hSet2]
          · refine ⟨hWt1', hWt2', hTmpNe0, hTmpNeDst, ⟨hTmpNe0, hTmpDeadRest⟩,
                    hTTy, hDTy, hChk,
                    setElem?_getElem?_same hSet1,
                    setElem?_getElem?_same hSet2,
                    ⟨optD1_after, by rw [setElem?_getElem?_ne hSet1 hTmpNeDst.symm]; exact hLa1Dst⟩,
                    ⟨optT2_after, by rw [setElem?_getElem?_ne hSet2 hTmpNeDst]; exact hLa2Tmp⟩,
                    fun i => ⟨?_, ?_⟩⟩
            · intro sl1 sl2 hG1 hG2
              cases hEqT : Nat.beq i tmpPlace.localId with
              | true =>
                have hi := nat_beq_eq hEqT; subst hi
                rw [setElem?_getElem?_same hSet1] at hG1
                rw [setElem?_getElem?_ne hSet2 hTmpNeDst, hLa2Tmp] at hG2
                injection hG1 with e1; injection hG2 with e2; subst e1; subst e2
                exact True.intro
              | false =>
                have hiNeT := nat_ne_of_beq_false hEqT
                rw [setElem?_getElem?_ne hSet1 hiNeT] at hG1
                cases hEqD : Nat.beq i dstPlace.localId with
                | true =>
                  have hi := nat_beq_eq hEqD; subst hi
                  rw [hLa1Dst] at hG1
                  rw [setElem?_getElem?_same hSet2] at hG2
                  injection hG1 with e1; injection hG2 with e2; subst e1; subst e2
                  exact True.intro
                | false =>
                  have hiNeD := nat_ne_of_beq_false hEqD
                  rw [setElem?_getElem?_ne hSet2 hiNeD] at hG2
                  exact (hMaskAfterR.2.2 i).1 sl1 sl2 hG1 hG2
            · intro hiNeT hiNeD hNotDAfter
              rw [setElem?_getElem?_ne hSet1 hiNeT, setElem?_getElem?_ne hSet2 hiNeD]
              apply (hMaskAfterR.2.2 i).2
              intro ⟨hiNe0, hDBefore⟩
              dsimp [isDeadAcrossCfg] at hDBefore
              let ⟨_, hIfDst⟩ := bool_and_true hDBefore
              have hBeqDstF : Nat.beq dstPlace.localId i = false :=
                nat_beq_false_of_ne hiNeD.symm
              rw [if_bool_false hBeqDstF] at hIfDst
              exact hNotDAfter ⟨hiNe0, hIfDst⟩

private theorem destProp_pair_step2_bisim {bSrc bTgt : Body}
    {D_after : LocalId → Prop} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {tmp : LocalId} {dstPlace : Place} {rvUse : Rvalue}
    {dstTy : MirTy} {val : Val}
    (hMid : DestPropMidLocals bSrc.locals D_after tmp dstPlace.localId dstTy val
      fSrc.locals fTgt.locals)
    (hDEmp : dstPlace.projection.isEmpty = true)
    (hUseTmp : isDestPropCopyOrMoveTmp tmp rvUse = true) :
    ∃ l1'',
      evalStatement bSrc fSrc cm (.assign dstPlace rvUse) =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1'' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm .nop =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals }],
                callerMem := cm } ∧
      DeadMaskedEq bSrc.locals D_after l1'' fTgt.locals := by
  let ⟨hWt1, hWt2, _, hTmpNeDst, hDTmp, hTTy, hDTy, hChk,
       hG1Tmp, hG2Dst, ⟨optD1, hG1Dst⟩, ⟨optT2, hG2Tmp⟩, hRestLocs⟩ := hMid
  have hLtTmp : tmp < bSrc.locals.length := getElem?_some_lt hTTy
  have hLtDst : dstPlace.localId < bSrc.locals.length := getElem?_some_lt hDTy
  cases rvUse with
  | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
  | addressOf _ _ | aggregateTuple _ | unsupported => cases hUseTmp
  | use opnd =>
    cases opnd with
    | constant _ => cases hUseTmp
    | copy p =>
      dsimp [isDestPropCopyOrMoveTmp] at hUseTmp
      let ⟨hPE, hPIdB⟩ := bool_and_true hUseTmp
      have hPId := nat_beq_eq hPIdB; subst hPId
      let ⟨l1'', hSetW⟩ := setElem?_some_of_lt fSrc.locals dstPlace.localId
        (.live (some val)) (by rw [hWt1.1]; exact hLtDst)
      refine ⟨l1'', ?_, rfl, ⟨localsWellTyped_set hWt1 hDTy hSetW hChk, hWt2, fun i => ?_⟩⟩
      · dsimp [evalStatement]; rw [hDEmp]; dsimp; rw [hDTy]; dsimp
        dsimp [evalRvalue, evalOperandToSlot]
        rw [hPE]; dsimp; rw [hTTy, hG1Tmp]; dsimp; rw [mirTy_beq_refl dstTy]; dsimp
        unfold writePlace; rw [hChk]; dsimp; rw [hG1Dst]; dsimp; rw [hSetW]
      · cases hEqD : Nat.beq i dstPlace.localId with
        | true =>
          have hi := nat_beq_eq hEqD; subst hi
          rw [setElem?_getElem?_same hSetW, hG2Dst]
          refine ⟨?_, fun _ => rfl⟩
          intro a b ea eb; injection ea with qa; injection eb with qb
          subst qa; subst qb; exact True.intro
        | false =>
          have hiNeD := nat_ne_of_beq_false hEqD
          rw [setElem?_getElem?_ne hSetW hiNeD]
          cases hEqT : Nat.beq i p.localId with
          | true =>
            have hi := nat_beq_eq hEqT; subst hi
            exact ⟨(hRestLocs p.localId).1, fun hNot => False.elim (hNot hDTmp)⟩
          | false =>
            have hiNeT := nat_ne_of_beq_false hEqT
            exact ⟨(hRestLocs i).1, fun hNot => (hRestLocs i).2 hiNeT hiNeD hNot⟩
    | move p =>
      dsimp [isDestPropCopyOrMoveTmp] at hUseTmp
      let ⟨hPE, hPIdB⟩ := bool_and_true hUseTmp
      have hPId := nat_beq_eq hPIdB; subst hPId
      let ⟨lMove, hSetM⟩ := setElem?_some_of_lt fSrc.locals p.localId
        (liveUninitSlot dstTy) (by rw [hWt1.1]; exact hLtTmp)
      have hWtMove := localsWellTyped_set hWt1 hTTy hSetM (liveUninitSlot_wellTyped dstTy)
      have hMoveDst : Trusted.MirSemantics.getElem? lMove dstPlace.localId =
          some (.live optD1) := by
        rw [setElem?_getElem?_ne hSetM hTmpNeDst.symm]; exact hG1Dst
      let ⟨l1'', hSetW⟩ := setElem?_some_of_lt lMove dstPlace.localId
        (.live (some val)) (by rw [hWtMove.1]; exact hLtDst)
      refine ⟨l1'', ?_, rfl, ⟨localsWellTyped_set hWtMove hDTy hSetW hChk, hWt2, fun i => ?_⟩⟩
      · dsimp [evalStatement]; rw [hDEmp]; dsimp; rw [hDTy]; dsimp
        dsimp [evalRvalue, evalOperandToSlot]
        rw [hPE]; dsimp; rw [hTTy, hG1Tmp]; dsimp; rw [hSetM]; dsimp
        rw [mirTy_beq_refl dstTy]; dsimp
        unfold writePlace; rw [hChk]; dsimp; rw [hMoveDst]; dsimp; rw [hSetW]
      · cases hEqD : Nat.beq i dstPlace.localId with
        | true =>
          have hi := nat_beq_eq hEqD; subst hi
          rw [setElem?_getElem?_same hSetW, hG2Dst]
          refine ⟨?_, fun _ => rfl⟩
          intro a b ea eb; injection ea with qa; injection eb with qb
          subst qa; subst qb; exact True.intro
        | false =>
          have hiNeD := nat_ne_of_beq_false hEqD
          rw [setElem?_getElem?_ne hSetW hiNeD]
          cases hEqT : Nat.beq i p.localId with
          | true =>
            have hi := nat_beq_eq hEqT; subst hi
            let ⟨optU, hOptU⟩ := liveUninitSlot_isLive dstTy
            rw [setElem?_getElem?_same hSetM, hOptU, hG2Tmp]
            refine ⟨?_, fun hNot => False.elim (hNot hDTmp)⟩
            intro a b ea eb; injection ea with qa; injection eb with qb
            subst qa; subst qb; exact True.intro
          | false =>
            have hiNeT := nat_ne_of_beq_false hEqT
            rw [setElem?_getElem?_ne hSetM hiNeT]
            exact ⟨(hRestLocs i).1, fun hNot => (hRestLocs i).2 hiNeT hiNeD hNot⟩

private theorem applyDestPropBlocks_props {b : Body} {cert : BodyDestPropCert} :
    ∀ {base bbs bbs'},
      applyDestPropBlocks b cert base bbs = some bbs' →
      bbs.length = bbs'.length ∧
      (∀ i bb₁ bb₂,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? bbs' i = some bb₂ →
        StmtListStoragePreserved bb₁.statements bb₂.statements ∧
        bb₁.cleanup = bb₂.cleanup ∧
        bb₁.terminator = bb₂.terminator) ∧
      (∀ i bb₁ entryEnv,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? cert.liveCert (base + i) = some (some entryEnv) →
        ∃ bb₂ exitEnv,
          Trusted.MirSemantics.getElem? bbs' i = some bb₂ ∧
          entryEnv.length = b.locals.length ∧
          DestPropTail b.locals cert.deadAtEntry b.basicBlocks.length
            bb₂.terminator entryEnv bb₁.statements bb₂.statements exitEnv ∧
          checkAbsTerminatorEdges b.locals b.basicBlocks.length cert.liveCert
            exitEnv bb₁.terminator = true) := by
  intro base bbs
  induction bbs generalizing base with
  | nil =>
    intro bbs' h; injection h with e; subst e
    exact ⟨rfl, (fun _ _ _ h1 => by cases h1), (fun _ _ _ h1 => by cases h1)⟩
  | cons bb rest ih =>
    intro bbs' h
    dsimp [applyDestPropBlocks] at h
    cases hC : Trusted.MirSemantics.getElem? cert.liveCert base with
    | none => rw [hC] at h; cases h
    | some optE =>
      rw [hC] at h
      cases optE with
      | none =>
        dsimp at h
        cases hRec : applyDestPropBlocks b cert (base + 1) rest with
        | none => rw [hRec] at h; cases h
        | some rest' =>
          rw [hRec] at h; injection h with e; subst e
          let ⟨hLen, hStCl, hAct⟩ := ih hRec
          refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
          · intro i bb₁ bb₂ h1 h2
            cases i with
            | zero =>
              injection h1 with e1; injection h2 with e2; subst e1; subst e2
              exact ⟨stmtListStoragePreserved_refl _, rfl, rfl⟩
            | succ k => exact hStCl k bb₁ bb₂ h1 h2
          · intro i bb₁ eEnv h1 hCE
            cases i with
            | zero => rw [Nat.add_zero, hC] at hCE; cases hCE
            | succ k =>
              have hAdd : (base + 1) + k = base + (k + 1) := by
                rw [Nat.add_assoc, Nat.add_comm 1 k]
              rw [← hAdd] at hCE
              exact hAct k bb₁ eEnv h1 hCE
      | some entryEnv =>
        dsimp at h
        cases hELen : Nat.beq entryEnv.length b.locals.length with
        | false => rw [hELen] at h; cases h
        | true =>
          rw [hELen] at h; dsimp at h
          cases hRew : rewriteDestPropStmts b.locals cert.deadAtEntry
              b.basicBlocks.length bb.terminator entryEnv bb.statements with
          | none => rw [hRew] at h; cases h
          | some pr =>
            let ⟨stmts', exitEnv⟩ := pr
            rw [hRew] at h; dsimp at h
            cases hEdg : checkAbsTerminatorEdges b.locals b.basicBlocks.length
                cert.liveCert exitEnv bb.terminator with
            | false => rw [hEdg] at h; cases h
            | true =>
              rw [hEdg] at h; dsimp at h
              cases hRec : applyDestPropBlocks b cert (base + 1) rest with
              | none => rw [hRec] at h; cases h
              | some rest' =>
                rw [hRec] at h; injection h with e; subst e
                let ⟨hTail, hStP⟩ :=
                  rewriteDestPropStmts_sound_aux bb.statements.length (Nat.le_refl _) hRew
                let ⟨hLen, hStCl, hAct⟩ := ih hRec
                refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
                · intro i bb₁ bb₂ h1 h2
                  cases i with
                  | zero =>
                    injection h1 with e1; injection h2 with e2; subst e1; subst e2
                    exact ⟨hStP, rfl, rfl⟩
                  | succ k => exact hStCl k bb₁ bb₂ h1 h2
                · intro i bb₁ eEnv h1 hCE
                  cases i with
                  | zero =>
                    injection h1 with e1; subst e1
                    rw [Nat.add_zero, hC] at hCE; injection hCE with eE
                    injection eE with eE'; subst eE'
                    exact ⟨_, exitEnv, rfl, nat_beq_eq hELen, hTail, hEdg⟩
                  | succ k =>
                    have hAdd : (base + 1) + k = base + (k + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 k]
                    rw [← hAdd] at hCE
                    exact hAct k bb₁ eEnv h1 hCE

private theorem applyDestPropBody_props {cert : BodyDestPropCert} {bSrc bTgt : Body}
    (hApply : applyDestPropBody cert bSrc = some bTgt) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) ∧
    (bSrc.basicBlocks.isEmpty = false →
      ∃ env₀, Trusted.MirSemantics.getElem? cert.liveCert 0 = some (some env₀) ∧
        absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
    checkBodyDeadCert bTgt cert.deadAtEntry = true ∧
    applyDestPropBlocks bSrc cert 0 bSrc.basicBlocks = some bTgt.basicBlocks ∧
    bSrc.locals = bTgt.locals := by
  unfold applyDestPropBody at hApply
  cases hCLen : Nat.beq cert.liveCert.length bSrc.basicBlocks.length with
  | false => rw [hCLen] at hApply; cases hApply
  | true =>
    rw [hCLen] at hApply; dsimp at hApply
    have hProceed :
        ((bSrc.basicBlocks.isEmpty = false →
          ∃ env₀, Trusted.MirSemantics.getElem? cert.liveCert 0 = some (some env₀) ∧
            absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
         ∃ bbs', applyDestPropBlocks bSrc cert 0 bSrc.basicBlocks = some bbs' ∧
           checkBodyDeadCert { bSrc with basicBlocks := bbs' } cert.deadAtEntry = true ∧
           bTgt = { bSrc with basicBlocks := bbs' }) := by
      cases hEmp : bSrc.basicBlocks.isEmpty with
      | true =>
        rw [hEmp] at hApply; dsimp at hApply
        cases hBlk : applyDestPropBlocks bSrc cert 0 bSrc.basicBlocks with
        | none => rw [hBlk] at hApply; cases hApply
        | some bbs' =>
          rw [hBlk] at hApply; dsimp at hApply
          cases hDC : checkBodyDeadCert { bSrc with basicBlocks := bbs' } cert.deadAtEntry with
          | false => rw [hDC] at hApply; cases hApply
          | true =>
            rw [hDC] at hApply; injection hApply with eB
            exact ⟨(fun hF => by cases hF), bbs', rfl, hDC, eB.symm⟩
      | false =>
        rw [hEmp] at hApply
        cases hC0 : Trusted.MirSemantics.getElem? cert.liveCert 0 with
        | none => rw [hC0] at hApply; cases hApply
        | some opt0 =>
          rw [hC0] at hApply
          cases opt0 with
          | none => cases hApply
          | some env₀ =>
            cases hImp : absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀ with
            | false =>
              have hCT : (!false && !(match (some (some env₀) : Option (Option (List AbsSlot))) with
                  | some (some e) => absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = true := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_true hCT] at hApply; cases hApply
            | true =>
              have hCF : (!false && !(match (some (some env₀) : Option (Option (List AbsSlot))) with
                  | some (some e) => absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = false := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_false hCF] at hApply
              cases hBlk : applyDestPropBlocks bSrc cert 0 bSrc.basicBlocks with
              | none => rw [hBlk] at hApply; cases hApply
              | some bbs' =>
                rw [hBlk] at hApply; dsimp at hApply
                cases hDC : checkBodyDeadCert { bSrc with basicBlocks := bbs' } cert.deadAtEntry with
                | false => rw [hDC] at hApply; cases hApply
                | true =>
                  rw [hDC] at hApply; injection hApply with eB
                  exact ⟨fun _ => ⟨env₀, rfl, hImp⟩, bbs', rfl, hDC, eB.symm⟩
    let ⟨hCert0Fn, bbs', hBlk, hDC, eB⟩ := hProceed
    subst eB
    let ⟨hBBLen, hStCl, _⟩ := applyDestPropBlocks_props hBlk
    have hBBEmpty := list_isEmpty_eq_of_length hBBLen
    have hHdr : bodyHeaderEq bSrc { bSrc with basicBlocks := bbs' } = true :=
      bodyHeaderEq_refl bSrc
    have hMarker : ∀ idx,
        hasStorageAnnotation bSrc idx =
          hasStorageAnnotation { bSrc with basicBlocks := bbs' } idx := by
      intro idx
      unfold hasStorageAnnotation; dsimp only
      exact list_any_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 =>
        (stmtListStoragePreserved_props (hStCl i bb₁ bb₂ h1 h2).1).2.1 idx)
    have hBounds :
        storageAnnotationsInBounds bSrc =
          storageAnnotationsInBounds { bSrc with basicBlocks := bbs' } := by
      unfold storageAnnotationsInBounds; dsimp only
      exact list_all_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 =>
        (stmtListStoragePreserved_props (hStCl i bb₁ bb₂ h1 h2).1).2.2
          (fun stmt => match stmt with
            | .storageLive id | .storageDead id => Nat.blt id bSrc.locals.length
            | _ => true)
          (fun _ _ => rfl) rfl)
    exact ⟨hHdr, hBBLen, hBBEmpty, hBounds,
      fun args => initLocalsLoop_eq_of_storage_eq args rfl rfl (fun idx _ _ => hMarker idx),
      hCert0Fn, hDC, hBlk, rfl⟩

private noncomputable def DestPropBlockMode (bSrc bTgt : Body) (bCert : BodyDestPropCert)
    (bbSrc bbTgt : BasicBlock) (fSrc fTgt : FrameState) : Prop :=
  (∃ env exitEnv,
    DestPropTail bSrc.locals bCert.deadAtEntry bSrc.basicBlocks.length
      bbTgt.terminator env
      (bbSrc.statements.drop fSrc.stmtIdx)
      (bbTgt.statements.drop fSrc.stmtIdx) exitEnv ∧
    checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      bCert.liveCert exitEnv bbSrc.terminator = true ∧
    AbsEnvSound bSrc.locals env fSrc.locals ∧
    DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bTgt.locals.length bCert.deadAtEntry bTgt.basicBlocks.length d
          (bbTgt.statements.drop fSrc.stmtIdx) bbTgt.terminator = true)
      fSrc.locals fTgt.locals) ∨
  (∃ dstPlace rvUse restSrc restTgt tmp dstTy val env₁ env₂ exitEnv,
    bbSrc.statements.drop fSrc.stmtIdx = (.assign dstPlace rvUse) :: restSrc ∧
    bbTgt.statements.drop fSrc.stmtIdx = .nop :: restTgt ∧
    dstPlace.projection.isEmpty = true ∧
    isDestPropCopyOrMoveTmp tmp rvUse = true ∧
    DestPropMidLocals bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bTgt.locals.length bCert.deadAtEntry bTgt.basicBlocks.length d
          restTgt bbTgt.terminator = true)
      tmp dstPlace.localId dstTy val fSrc.locals fTgt.locals ∧
    AbsEnvSound bSrc.locals env₁ fSrc.locals ∧
    stepPlainStmtAbs bSrc.locals env₁ (.assign dstPlace rvUse) = some env₂ ∧
    DestPropTail bSrc.locals bCert.deadAtEntry bSrc.basicBlocks.length
      bbTgt.terminator env₂ restSrc restTgt exitEnv ∧
    checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      bCert.liveCert exitEnv bbSrc.terminator = true)

private noncomputable def DestPropBisimRel (cert : ProgramDestPropCert)
    (pSrc pTgt : Program) (s t : State) : Prop :=
  ∃ fSrc fTgt bCert bSrc bTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    Trusted.MirSemantics.getElem? cert fSrc.defId = some bCert ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
    applyDestPropBody bCert bSrc = some bTgt ∧
    (fSrc.blockIdx < bSrc.basicBlocks.length →
      ∃ bbSrc bbTgt,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt ∧
        DestPropBlockMode bSrc bTgt bCert bbSrc bbTgt fSrc fTgt)

private theorem destProp_init_eq {cert : ProgramDestPropCert} {pSrc pTgt : Program}
    (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applyDestPropBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    initState pSrc q = initState pTgt q := by
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  have hBodyLen : pSrc.bodies.length = pTgt.bodies.length :=
    (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
  apply initState_eq_of_matching_entry q hHdr
  · constructor
    · intro hN
      have hGe : pTgt.bodies.length ≤ pTgt.entryDefId := by
        rw [← hBodyLen, ← hEnt]; exact getElem?_none_ge hN
      exact getElem?_none_of_ge hGe
    · intro hN
      have hGe : pSrc.bodies.length ≤ pSrc.entryDefId := by
        rw [hBodyLen, hEnt]; exact getElem?_none_ge hN
      exact getElem?_none_of_ge hGe
  · intro bSrc hBS
    let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    rw [hEnt] at hBT
    let ⟨hBHdr, _, hEmp, hBnd, hInitL, _, _, _, _⟩ := applyDestPropBody_props hAp
    exact ⟨bTgt, hBT, hBHdr, hEmp, hBnd, hInitL q.args⟩

private theorem destProp_query_iff {cert : ProgramDestPropCert} {pSrc pTgt : Program}
    (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applyDestPropBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  apply bisim_lockstep_query_iff (R := DestPropBisimRel cert pSrc pTgt)
    (destProp_init_eq q hLenC hHdr hMap)
  · intro s₀ hOk
    let ⟨_, _, bSrc, hBS, hNotEmp, _, _, _, hArgs, hs0⟩ := initState_ok_elim hOk
    subst hs0
    let ⟨bCert, bTgt, hBC, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    let ⟨_, hBBLen, _, _, _, hCert0Fn, _, hBlk, _⟩ := applyDestPropBody_props hAp
    let ⟨_, _, hAct⟩ := applyDestPropBlocks_props hBlk
    let ⟨env₀, hC0, hImp0⟩ := hCert0Fn hNotEmp
    have hEnv0 := absEnvImplies_sound hImp0 (initAbsEnvLoop_sound hArgs)
    refine ⟨_, _, bCert, bSrc, bTgt, rfl, rfl, rfl, rfl, rfl, rfl,
            hBC, hBS, hBT, hAp, ?_⟩
    intro h0Lt
    let ⟨bbSrc0, hBBS0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
    let ⟨bbTgt0, exitE0, hBBT0, _, hTail0, hEdg0⟩ := hAct 0 bbSrc0 env₀ hBBS0 hC0
    exact ⟨bbSrc0, bbTgt0, hBBS0, hBBT0,
      Or.inl ⟨env₀, exitE0, hTail0, hEdg0, hEnv0, deadMaskedEq_refl hEnv0.1⟩⟩
  · intro s t hR
    let ⟨fSrc, fTgt, bCert, bSrc, bTgt, hFS, hFT, hCM, hDefEq, hBlkEq, hIdxEq,
         hBC, hBS, hBT, hAp, hBlkInv⟩ := hR
    let ⟨_, hBBLen, _, _, _, _, hDC, hBlk, hLocEq⟩ := applyDestPropBody_props hAp
    let ⟨_, hStCl, hAct⟩ := applyDestPropBlocks_props hBlk
    cases s with
    | mk fsS cmS =>
      cases t with
      | mk fsT cmT =>
        dsimp at hFS hFT hCM; subst hFS; subst hFT; subst hCM
        have hBT2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
          rw [← hDefEq]; exact hBT
        cases Nat.lt_or_ge fSrc.blockIdx bSrc.basicBlocks.length with
        | inr hGe =>
          have hGeT : bTgt.basicBlocks.length ≤ fTgt.blockIdx := by
            rw [← hBlkEq, ← hBBLen]; exact hGe
          unfold StepOutcomeBisim evalStep; dsimp
          rw [hBS, hBT2]; dsimp
          rw [getElem?_none_of_ge hGe, getElem?_none_of_ge hGeT]
          exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
        | inl hLt =>
          let ⟨bbSrc, bbTgt, hBBS, hBBT, hMode⟩ := hBlkInv hLt
          have hBBT2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx =
              some bbTgt := by
            rw [← hBlkEq]; exact hBBT
          let ⟨hStP, hCleanEq, hTermEq⟩ := hStCl fSrc.blockIdx bbSrc bbTgt hBBS hBBT
          have hStmtsLenEq := (stmtListStoragePreserved_props hStP).1
          cases hMode with
          | inr hMidMode =>
            let ⟨dstPlace, rvUse, restSrc, restTgt, tmp, dstTy, val,
                 env₁, env₂, exitEnv, hDropS, hDropT, hDEmp, hUseTmp,
                 hMidLocs, hEnv1S, hStep2Abs, hTailRest, hEdges⟩ := hMidMode
            let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
            let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
            have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx =
                some .nop := by
              rw [← hIdxEq]; exact hStTgt0
            let ⟨l1'', hEvS2, hEvT2, hMaskNext⟩ :=
              destProp_pair_step2_bisim (bTgt := bTgt) (cm := cmS) hMidLocs hDEmp hUseTmp
            let ⟨l1''', hEqS2, hEnv2S⟩ := stepPlainStmtAbs_sound hEnv1S hStep2Abs hEvS2
            injection hEqS2 with eFs _; injection eFs with eF _
            have hLEq : l1'' = l1''' := congrArg FrameState.locals eF
            subst hLEq
            unfold StepOutcomeBisim evalStep; dsimp
            rw [hBS, hBT2]; dsimp
            rw [hBBS, hBBT2]; dsimp
            rw [hStSrc, hStTgt2]; dsimp
            rw [hEvS2, hEvT2]
            refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1'' }],
                             callerMem := cmS },
              { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals }],
                callerMem := cmS }, rfl, rfl,
              { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1'' },
              { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals },
              bCert, bSrc, bTgt,
              rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq],
              hBC, hBS, hBT, hAp, fun _ => ?_⟩
            refine ⟨bbSrc, bbTgt, hBBS, hBBT, Or.inl ⟨env₂, exitEnv, ?_, hEdges, hEnv2S, ?_⟩⟩
            · dsimp; rw [hDropSNext, hDropTNext]; exact hTailRest
            · dsimp; rw [hDropTNext]; exact hMaskNext
          | inl hAligned =>
            let ⟨env, exitEnv, hTail, hEdges, hEnvS, hMask⟩ := hAligned
            cases hDropS : bbSrc.statements.drop fSrc.stmtIdx with
            | nil =>
              rw [hDropS] at hTail
              cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
              | cons _ _ => rw [hDropT] at hTail; cases hTail
              | nil =>
                rw [hDropT] at hTail hMask
                cases hTail with
                | nil =>
                  cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
                  | some x =>
                    rw [drop_eq_cons_of_getElem? hStSrc] at hDropS; cases hDropS
                  | none =>
                    have hGeS := getElem?_none_ge hStSrc
                    have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx =
                        none :=
                      getElem?_none_of_ge (by rw [← hIdxEq, ← hStmtsLenEq]; exact hGeS)
                    unfold StepOutcomeBisim evalStep; dsimp
                    rw [hBS, hBT2]; dsimp
                    rw [hBBS, hBBT2]; dsimp
                    rw [hStSrc, hStTgt2]; dsimp
                    rw [← hIdxEq, ← hStmtsLenEq]
                    cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
                    | false => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
                    | true =>
                      dsimp
                      have hSwUntouched : ∀ discr targets,
                          bbTgt.terminator = .switchInt discr targets →
                          ∀ d, (d ≠ 0 ∧ isDeadAcrossCfg bTgt.locals.length bCert.deadAtEntry
                            bTgt.basicBlocks.length d [] bbTgt.terminator = true) →
                          operandTouchesLocal d discr = false := by
                        intro discr targets hTm d ⟨_, hDnil⟩
                        rw [hTm] at hDnil
                        exact isDeadAcrossCfg_nil_switch_untouched hDnil
                      cases evalTerminator_deadMasked_bisim (cm := cmS)
                          hLocEq hCleanEq hTermEq hMask (fun _ h => h.1) hSwUntouched with
                      | inr hDoneOrFault => exact Or.inr hDoneOrFault
                      | inl hStepTerm =>
                        let ⟨tgt, l1', l2', hEvTS, hEvTT, hMaskAfterTerm⟩ := hStepTerm
                        let ⟨tgt', l1'', hEqS', _, hCertNext⟩ :=
                          checkAbsTerminatorEdges_step_sound hEnvS hEdges hEvTS
                        injection hEqS' with eFs _; injection eFs with eF _
                        have hTgtEq : tgt = tgt' := congrArg FrameState.blockIdx eF
                        have hL1Eq : l1' = l1'' := congrArg FrameState.locals eF
                        subst hTgtEq; subst hL1Eq
                        rw [hEvTS, hEvTT]
                        refine Or.inl ⟨{ frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1' }],
                                         callerMem := cmS },
                          { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2' }],
                            callerMem := cmS }, rfl, rfl,
                          { fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1' },
                          { fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2' },
                          bCert, bSrc, bTgt,
                          rfl, rfl, rfl, hDefEq, rfl, rfl,
                          hBC, hBS, hBT, hAp, ?_⟩
                        intro hTgtLt
                        let ⟨tgtEnv, hCNext, hTgtEnvS⟩ := hCertNext hTgtLt
                        let ⟨bbNextS, hBBNS⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt hTgtLt
                        have hCNext0 : Trusted.MirSemantics.getElem? bCert.liveCert (0 + tgt) =
                            some (some tgtEnv) := by
                          rw [Nat.zero_add]; exact hCNext
                        let ⟨bbNextT, exitEN, hBBNT, _, hTailN, hEdgN⟩ :=
                          hAct tgt bbNextS tgtEnv hBBNS hCNext0
                        have hDeadLoop : checkDeadAtEntryLoop bTgt bCert.deadAtEntry 0
                            bCert.deadAtEntry = true := (bool_and_true hDC).2
                        have hMaskEntry : DeadMaskedEq bSrc.locals
                            (fun d => d ≠ 0 ∧ isDeadAcrossCfg bTgt.locals.length bCert.deadAtEntry
                              bTgt.basicBlocks.length d
                              bbNextT.statements bbNextT.terminator = true)
                            l1' l2' := by
                          apply deadMaskedEq_mono ?_ hMaskAfterTerm
                          intro d ⟨hd0, hDnil⟩
                          exact ⟨hd0, isDeadAcrossCfg_nil_step_target hDeadLoop
                            hEvTT hBBNT hDnil⟩
                        exact ⟨bbNextS, bbNextT, hBBNS, hBBNT,
                          Or.inl ⟨tgtEnv, exitEN, hTailN, hEdgN, hTgtEnvS, hMaskEntry⟩⟩
            | cons s₀ restSrc0 =>
              rw [hDropS] at hTail
              cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
              | nil => rw [hDropT] at hTail; cases hTail
              | cons t₀ restTgt0 =>
                rw [hDropT] at hTail hMask
                cases hTail with
                | kept hStep1 hTailRest =>
                  let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
                  let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
                  have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx =
                      some s₀ := by
                    rw [← hIdxEq]; exact hStTgt0
                  unfold StepOutcomeBisim evalStep; dsimp
                  rw [hBS, hBT2]; dsimp
                  rw [hBBS, hBBT2]; dsimp
                  rw [hStSrc, hStTgt2]; dsimp
                  cases isDeadAcrossCfg_kept_step (cm := cmS) hLocEq hMask with
                  | inl hCase =>
                    let ⟨fk, hF1, hF2⟩ := hCase
                    rw [hF1, hF2]
                    exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
                  | inr hCase =>
                    let ⟨l1', l2', hS1, hS2, hMask'⟩ := hCase
                    let ⟨l1'', hEqS', hEnv1⟩ := stepPlainStmtAbs_sound hEnvS hStep1 hS1
                    injection hEqS' with eFs _; injection eFs with eF _
                    have eL : l1' = l1'' := congrArg FrameState.locals eF
                    subst eL
                    rw [hS1, hS2]
                    refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                                     callerMem := cmS },
                      { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                        callerMem := cmS }, rfl, rfl,
                      { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' },
                      bCert, bSrc, bTgt,
                      rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq],
                      hBC, hBS, hBT, hAp, fun _ => ?_⟩
                    refine ⟨bbSrc, bbTgt, hBBS, hBBT,
                      Or.inl ⟨_, exitEnv, ?_, hEdges, hEnv1, ?_⟩⟩
                    · dsimp; rw [hDropSNext, hDropTNext]; exact hTailRest
                    · dsimp; rw [hDropTNext]; exact hMask'
                | pair hCand hStep1 hStep2 hDeadTmp hTailRest =>
                  let ⟨tmpPlace, rvUse, dstTy, tmpSlot, dstSlot,
                       hs1, hs2, hTmpId, hTEmp, hDEmp, hTmpNe0, hTmpNeDst,
                       hNoTouchTmp, hUseTmp, hTTy, hDTy, hETmp, hEDst,
                       _, hTmpImp, hDstImp⟩ := matchDestPropCandidate?_elim hCand
                  subst hs1; subst hs2; subst hTmpId
                  let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
                  let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
                  have hStTgt2 := hStTgt0
                  rw [hIdxEq] at hStTgt2
                  unfold StepOutcomeBisim evalStep; dsimp
                  rw [hBS, hBT2]; dsimp
                  rw [hBBS, hBBT2]; dsimp
                  rw [hStSrc, hStTgt2]; dsimp
                  have hDeadTmpTgt := hDeadTmp
                  rw [hLocEq, hBBLen] at hDeadTmpTgt
                  cases destProp_pair_step1_bisim (cm := cmS)
                      hLocEq hEnvS hMask hTEmp hDEmp hTmpNe0 hTmpNeDst
                      hNoTouchTmp hTTy hDTy hETmp hEDst hTmpImp hDstImp
                      hDeadTmpTgt with
                  | inl hFault =>
                    let ⟨fk, hF1, hF2⟩ := hFault
                    rw [hF1, hF2]
                    exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
                  | inr hStepPair =>
                    let ⟨val, l1', l2', hEvS1, hEvT1, hMidNext⟩ := hStepPair
                    let ⟨l1'', hEqS1, hEnv1S⟩ := stepPlainStmtAbs_sound hEnvS hStep1 hEvS1
                    injection hEqS1 with eFs _; injection eFs with eF _
                    have hL1Eq : l1' = l1'' := congrArg FrameState.locals eF
                    subst hL1Eq
                    rw [hEvS1, hEvT1]
                    refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                                     callerMem := cmS },
                      { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                        callerMem := cmS }, rfl, rfl,
                      { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' },
                      bCert, bSrc, bTgt,
                      rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq],
                      hBC, hBS, hBT, hAp, fun _ => ?_⟩
                    refine ⟨bbSrc, bbTgt, hBBS, hBBT,
                      Or.inr ⟨_, rvUse, _, _, tmpPlace.localId, dstTy, val,
                              _, _, exitEnv, ?_, ?_, hDEmp, hUseTmp,
                              hMidNext, hEnv1S, hStep2, hTailRest, hEdges⟩⟩
                    · dsimp; exact hDropSNext
                    · dsimp; exact hDropTNext

private theorem applyDestPropProgram_equiv {cert : ProgramDestPropCert}
    {pSrc pTgt : Program}
    (hApply : applyDestPropProgram cert pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  unfold applyDestPropProgram at hApply
  cases hLenB : Nat.beq cert.length pSrc.bodies.length with
  | false => rw [hLenB] at hApply; cases hApply
  | true =>
    rw [hLenB] at hApply; dsimp at hApply
    have hLenC := nat_beq_eq hLenB
    cases hMap : mapOption (fun pr => applyDestPropBody pr.1 pr.2)
        (List.zip cert pSrc.bodies) with
    | none => rw [hMap] at hApply; cases hApply
    | some bodies' =>
      rw [hMap] at hApply; injection hApply with eP; subst eP
      have hHdr := programHeaderEq_with_bodies pSrc bodies'
      have hBodyLen : pSrc.bodies.length = bodies'.length :=
        (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
      have hIds : pSrc.bodies.map Body.identity = bodies'.map Body.identity := by
        apply list_eq_of_getElem?_eq
        · rw [map_length_eq, map_length_eq, hBodyLen]
        · intro i
          rw [getElem?_map, getElem?_map]
          cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies i with
          | none =>
            have hGe : bodies'.length ≤ i := by
              rw [← hBodyLen]; exact getElem?_none_ge hBS
            rw [getElem?_none_of_ge hGe]
          | some bSrc =>
            let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
            let ⟨hBHdr, _, _, _, _, _, _, _, _⟩ := applyDestPropBody_props hAp
            let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim hBHdr
            rw [hBT]; dsimp [Option.map]; rw [hIdEq]
      refine ⟨?_, hHdr, hIds⟩
      refine fullSemanticEquiv_of_query_iff hHdr ?_ ?_ ?_
      · intro defId bSrc bTgt hBS hBT
        let ⟨_, bTgt', _, hBT', hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
        dsimp at hBT; rw [hBT] at hBT'; injection hBT' with eB; subst eB
        let ⟨hBHdr, _, hEmp, hBnd, _, _, _, _, _⟩ := applyDestPropBody_props hAp
        exact ⟨hBHdr, hEmp, hBnd⟩
      · intro q
        exact destProp_query_iff q hLenC hHdr hMap
      · intro defId args
        exact (destProp_query_iff
          (pSrc := entryProgForBody pSrc defId)
          (pTgt := entryProgForBody { pSrc with bodies := bodies' } defId)
          { args := args } hLenC
          (programHeaderEq_entryProg defId hHdr) hMap).1

/-! #### Part D.3: Totality-Certified `DeadStoreElimination`
(`applyCertifiedDseProgram_equiv`) -/

private theorem decide_prop_false {P : Prop} {inst : Decidable P} (h : ¬ P) :
    @decide P inst = false := by
  cases inst with
  | isFalse _ => rfl
  | isTrue hp => exact False.elim (h hp)

private theorem bool_and_false (b : Bool) : (b && false) = false := by
  cases b <;> rfl

private theorem truncateScalar_ok (w : IntWidth) (s : Bool) (value : Int) :
    ∃ lossy : Bool,
      truncateScalar w s value =
        .ok (⟨w, s, truncateBits w (bvOfInt 128 value)⟩, lossy) ∧
      checkVal (.scalar ⟨w, s, truncateBits w (bvOfInt 128 value)⟩) (.int w s) = true := by
  let ⟨lossy, hTr, _, _⟩ := truncateScalar_eq w s value
  exact ⟨lossy, hTr, checkVal_int_iff.mpr ⟨_, rfl, truncateBits_idem w _⟩⟩

private theorem decodeScalar_ne_zero_of_bits_ne_zero {w : IntWidth} {s : Bool} {b : BitVec 128}
    (hWf : truncateBits w b = b) (hNe : b ≠ BitVec.ofNat 128 0) :
    decodeScalar ⟨w, s, b⟩ ≠ 0 := by
  have hToNatNe : b.toNat ≠ 0 := by
    intro hZ
    apply hNe
    apply bitvec_eq_of_toNat_eq
    exact hZ
  have hLt : b.toNat < Nat.pow 2 w.bitWidth := truncateBits_eq_iff.mp hWf
  cases s with
  | false =>
    rw [decodeScalar_unsigned hWf]
    intro hEq
    injection hEq with hN
    exact hToNatNe hN
  | true =>
    rw [decodeScalar_signed hWf, signExtendBits_eq hLt]
    cases Nat.lt_or_ge (2 * b.toNat) (Nat.pow 2 w.bitWidth) with
    | inl hCmp =>
      rw [ite_prop_true hCmp]
      intro hEq; injection hEq with hN; exact hToNatNe hN
    | inr hCmp =>
      rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
      intro hEq; nomatch hEq

private noncomputable def NonZeroSlotSound (ty : MirTy) (abs : NonZeroAbsSlot)
    (sl : LocalSlot) : Prop :=
  SlotWellTyped ty sl ∧
  match abs with
  | .dead => True
  | .liveUninit => ∃ o, sl = .live o
  | .liveInit => ∃ v, sl = .live (some v)
  | .liveNonZero =>
    ∃ w s b,
      ty = .int w s ∧
      sl = .live (some (.scalar ⟨w, s, b⟩)) ∧
      truncateBits w b = b ∧
      decodeScalar ⟨w, s, b⟩ ≠ 0

private noncomputable def NonZeroEnvSound (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) (locals : List LocalSlot) : Prop :=
  LocalsWellTyped bodyLocals locals ∧
  env.length = bodyLocals.length ∧
  ∀ i ty abs sl,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? env i = some abs →
    Trusted.MirSemantics.getElem? locals i = some sl →
    NonZeroSlotSound ty abs sl

private theorem nonZeroSlotImplies_sound {ty : MirTy} {a₁ a₂ : NonZeroAbsSlot} {sl : LocalSlot}
    (hImp : nonZeroSlotImplies a₁ a₂ = true)
    (hSound : NonZeroSlotSound ty a₁ sl) :
    NonZeroSlotSound ty a₂ sl := by
  let ⟨hWt, hS⟩ := hSound
  cases a₂ with
  | dead => exact ⟨hWt, True.intro⟩
  | liveUninit =>
    cases a₁ with
    | dead => cases hImp
    | liveUninit => exact ⟨hWt, hS⟩
    | liveInit =>
      let ⟨v, hv⟩ := hS
      exact ⟨hWt, ⟨some v, hv⟩⟩
    | liveNonZero =>
      let ⟨_, _, _, _, hsl, _, _⟩ := hS
      exact ⟨hWt, ⟨some _, hsl⟩⟩
  | liveInit =>
    cases a₁ with
    | dead | liveUninit => cases hImp
    | liveInit => exact ⟨hWt, hS⟩
    | liveNonZero =>
      let ⟨_, _, _, _, hsl, _, _⟩ := hS
      exact ⟨hWt, ⟨_, hsl⟩⟩
  | liveNonZero =>
    cases a₁ with
    | dead | liveUninit | liveInit => cases hImp
    | liveNonZero => exact ⟨hWt, hS⟩

private theorem nonZeroEnvImplies_sound {bodyLocals : List MirTy}
    {env₁ env₂ : List NonZeroAbsSlot} {locals : List LocalSlot}
    (hImp : nonZeroEnvImplies env₁ env₂ = true)
    (hSound : NonZeroEnvSound bodyLocals env₁ locals) :
    NonZeroEnvSound bodyLocals env₂ locals := by
  let ⟨hWt, hLen1, hAll⟩ := hSound
  have hLen12 : env₁.length = env₂.length := listRel_length hImp
  refine ⟨hWt, hLen12.symm.trans hLen1, ?_⟩
  intro i ty a₂ sl hTy hA2 hSl
  let ⟨a₁, hA1, hImpSlot⟩ := listRel_getElem?_right hImp hA2
  exact nonZeroSlotImplies_sound hImpSlot (hAll i ty a₁ sl hTy hA1 hSl)

private theorem nonZeroSlotSound_liveUninit (ty : MirTy) :
    NonZeroSlotSound ty
      (if isAlwaysInhabitedZst ty then .liveInit else .liveUninit)
      (liveUninitSlot ty) := by
  cases ty with
  | unit =>
    exact ⟨liveUninitSlot_wellTyped .unit, ⟨.unit, rfl⟩⟩
  | enum ety =>
    cases hZ : isZstEnumTy ety with
    | true =>
      have h1 : isAlwaysInhabitedZst (.enum ety) = true := hZ
      have h2 : liveUninitSlot (.enum ety) = .live (some (.enumVal ety 0)) := by
        unfold liveUninitSlot; dsimp; rw [hZ]; rfl
      rw [h1, h2]; dsimp
      exact ⟨by rw [← h2]; exact liveUninitSlot_wellTyped (.enum ety), ⟨.enumVal ety 0, rfl⟩⟩
    | false =>
      have h1 : isAlwaysInhabitedZst (.enum ety) = false := hZ
      have h2 : liveUninitSlot (.enum ety) = .live none := by
        unfold liveUninitSlot; dsimp; rw [hZ]; rfl
      rw [h1, h2]; dsimp
      exact ⟨by rw [← h2]; exact liveUninitSlot_wellTyped (.enum ety), ⟨none, rfl⟩⟩
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    exact ⟨liveUninitSlot_wellTyped _, ⟨none, rfl⟩⟩

private theorem initNonZeroEnvLoop_length (body : Body) :
    ∀ idx tys, (initNonZeroEnvLoop body idx tys).length = tys.length := by
  intro idx tys
  induction tys generalizing idx with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [initNonZeroEnvLoop, List.length]
    rw [ih (idx + 1)]

private theorem initNonZeroEnvLoop_getElem? (body : Body) :
    ∀ base tys k ty,
      Trusted.MirSemantics.getElem? tys k = some ty →
      Trusted.MirSemantics.getElem? (initNonZeroEnvLoop body base tys) k =
        some (initNonZeroSlot body (base + k) ty) := by
  intro base tys
  induction tys generalizing base with
  | nil => intro _ _ h; cases h
  | cons t₀ rest ih =>
    intro k ty h
    cases k with
    | zero =>
      injection h with hEq; subst hEq
      dsimp [initNonZeroEnvLoop, Trusted.MirSemantics.getElem?]
    | succ m =>
      dsimp [Trusted.MirSemantics.getElem?] at h
      dsimp [initNonZeroEnvLoop, Trusted.MirSemantics.getElem?]
      rw [ih (base + 1) m ty h]
      rw [Nat.add_assoc, Nat.add_comm 1 m]

private theorem initNonZeroEnvLoop_sound {body : Body} {args : List Val}
    (hArgs : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true) :
    NonZeroEnvSound body.locals
      (initNonZeroEnvLoop body 0 body.locals)
      (initLocalsLoop body args 0 body.locals) := by
  have hWt := initLocalsLoop_wellTyped hArgs
  refine ⟨hWt, initNonZeroEnvLoop_length body 0 body.locals, ?_⟩
  intro i ty abs sl hTy hAbs hSl
  have hGetAbs := initNonZeroEnvLoop_getElem? body 0 body.locals i ty hTy
  rw [Nat.zero_add] at hGetAbs
  rw [hGetAbs] at hAbs; injection hAbs with hEqA; subst hEqA
  have hGetSl := initLocalsLoop_getElem? body args 0 body.locals i ty hTy
  rw [Nat.zero_add] at hGetSl
  rw [hGetSl] at hSl; injection hSl with hEqS; subst hEqS
  cases i with
  | zero =>
    dsimp [initNonZeroSlot, Nat.beq]
    exact nonZeroSlotSound_liveUninit ty
  | succ k =>
    dsimp [initNonZeroSlot, Nat.beq]
    cases hLe : Nat.ble (k + 1) body.argumentCount with
    | true =>
      dsimp
      have hKlt : k < body.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((body.locals.drop 1).take body.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 body.locals body.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]
      exact ⟨hChk, ⟨v, rfl⟩⟩
    | false =>
      dsimp
      cases hasStorageAnnotation body (k + 1) with
      | true => dsimp; exact ⟨True.intro, True.intro⟩
      | false => dsimp; exact nonZeroSlotSound_liveUninit ty

private theorem nonZeroEnvSound_set {bodyLocals : List MirTy}
    {env env' : List NonZeroAbsSlot} {locals locals' : List LocalSlot}
    {id : Nat} {ty : MirTy} {abs' : NonZeroAbsSlot} {sl' : LocalSlot}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSetE : setElem? env id abs' = some env')
    (hSetL : setElem? locals id sl' = some locals')
    (hSlSound : NonZeroSlotSound ty abs' sl') :
    NonZeroEnvSound bodyLocals env' locals' := by
  let ⟨hWt, hLenE, hAll⟩ := hEnv
  refine ⟨localsWellTyped_set hWt hTy hSetL hSlSound.1,
          (setElem?_length hSetE).trans hLenE, ?_⟩
  intro i tyi absi sli hTyi hE hL
  cases hEq : Nat.beq i id with
  | true =>
    have hi := nat_beq_eq hEq; subst hi
    rw [hTy] at hTyi; injection hTyi with h1; subst h1
    rw [setElem?_getElem?_same hSetE] at hE; injection hE with h2; subst h2
    rw [setElem?_getElem?_same hSetL] at hL; injection hL with h3; subst h3
    exact hSlSound
  | false =>
    have hNe := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSetE hNe] at hE
    rw [setElem?_getElem?_ne hSetL hNe] at hL
    exact hAll i tyi absi sli hTyi hE hL

private theorem nonZeroEnvSound_refine_existing {bodyLocals : List MirTy}
    {env env' : List NonZeroAbsSlot} {locals : List LocalSlot}
    {id : Nat} {ty : MirTy} {abs' : NonZeroAbsSlot} {sl : LocalSlot}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hGetL : Trusted.MirSemantics.getElem? locals id = some sl)
    (hSetE : setElem? env id abs' = some env')
    (hSlSound : NonZeroSlotSound ty abs' sl) :
    NonZeroEnvSound bodyLocals env' locals := by
  let ⟨hWt, hLenE, hAll⟩ := hEnv
  refine ⟨hWt, (setElem?_length hSetE).trans hLenE, ?_⟩
  intro i tyi absi sli hTyi hE hL
  cases hEq : Nat.beq i id with
  | true =>
    have hi := nat_beq_eq hEq; subst hi
    rw [hTy] at hTyi; injection hTyi with h1; subst h1
    rw [setElem?_getElem?_same hSetE] at hE; injection hE with h2; subst h2
    rw [hGetL] at hL; injection hL with h3; subst h3
    exact hSlSound
  | false =>
    have hNe := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSetE hNe] at hE
    exact hAll i tyi absi sli hTyi hE hL

private theorem deinitMoveOperandNonZero_sound {bodyLocals : List MirTy}
    {env : List NonZeroAbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {srcTy : MirTy} {optVal : Option Val}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hEv : evalOperandToSlot bodyLocals locals opnd = .ok (srcTy, optVal, locals')) :
    NonZeroEnvSound bodyLocals (deinitMoveOperandNonZero bodyLocals env opnd) locals' := by
  cases opnd with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok _ =>
      rw [hC] at hEv; injection hEv with h1; injection h1 with _ h2
      injection h2 with _ hL; subst hL
      exact hEnv
  | copy p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some _ =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            injection hEv with h1; injection h1 with _ h2
            injection h2 with _ hL; subst hL
            exact hEnv
  | move p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            dsimp at hEv
            cases hSetL : setElem? locals p.localId (liveUninitSlot ty) with
            | none => rw [hSetL] at hEv; cases hEv
            | some locs1 =>
              rw [hSetL] at hEv
              injection hEv with h1; injection h1 with _ h2
              injection h2 with _ hL; subst hL
              have hLtE : p.localId < env.length := by
                rw [hEnv.2.1]; exact getElem?_some_lt hTy
              let ⟨env', hSetE⟩ := setElem?_some_of_lt env p.localId
                (if isAlwaysInhabitedZst ty then .liveInit else .liveUninit) hLtE
              dsimp [deinitMoveOperandNonZero]
              rw [hP]; dsimp; rw [hTy]; dsimp; rw [hSetE]
              exact nonZeroEnvSound_set hEnv hTy hSetE hSetL (nonZeroSlotSound_liveUninit ty)

private theorem deinitMovePrimNonZero_sound {bodyLocals : List MirTy}
    {env : List NonZeroAbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {v : Val}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hEv : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    NonZeroEnvSound bodyLocals (deinitMoveOperandNonZero bodyLocals env opnd) locals' := by
  dsimp [evalPrimitiveOperand] at hEv
  cases hS : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [hS] at hEv; cases hEv
  | ok res =>
    let ⟨ty0, optVal, locs1⟩ := res
    rw [hS] at hEv; dsimp at hEv
    cases hPrim : isPrimitiveReadableTy ty0 with
    | false => rw [hPrim] at hEv; cases hEv
    | true =>
      rw [hPrim] at hEv; dsimp at hEv
      cases optVal with
      | none => cases hEv
      | some _ =>
        injection hEv with h1; injection h1 with _ hL; subst hL
        exact deinitMoveOperandNonZero_sound hEnv hS

private theorem deinitMovesInRvalueNonZero_sound {bodyLocals : List MirTy}
    {env : List NonZeroAbsSlot} {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    NonZeroEnvSound bodyLocals (deinitMovesInRvalueNonZero bodyLocals env rv) locals' := by
  cases rv with
  | use o =>
    dsimp [evalRvalue] at hEv
    cases hS : evalOperandToSlot bodyLocals locals o with
    | error _ => rw [hS] at hEv; cases hEv
    | ok res =>
      let ⟨srcTy, optVal, locs1⟩ := res
      rw [hS] at hEv; dsimp at hEv
      cases hEqTy : MirTy.beq srcTy dstTy with
      | false => rw [hEqTy] at hEv; cases hEv
      | true =>
        rw [hEqTy] at hEv; dsimp at hEv
        cases optVal with
        | none => cases hEv
        | some _ =>
          injection hEv with h1; injection h1 with _ hL; subst hL
          exact deinitMoveOperandNonZero_sound hEnv hS
  | unaryOp op o =>
    dsimp [evalRvalue] at hEv
    cases hO : evalPrimitiveOperand bodyLocals locals o with
    | error _ => rw [hO] at hEv; cases hEv
    | ok res =>
      let ⟨ov, locs1⟩ := res
      rw [hO] at hEv; dsimp at hEv
      cases hU : evalUnOp op ov with
      | error _ => rw [hU] at hEv; cases hEv
      | ok _ =>
        rw [hU] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL
        exact deinitMovePrimNonZero_sound hEnv hO
  | binaryOp op l r =>
    dsimp [evalRvalue] at hEv
    cases hL : evalPrimitiveOperand bodyLocals locals l with
    | error _ => rw [hL] at hEv; cases hEv
    | ok resL =>
      let ⟨lv, locs1⟩ := resL
      rw [hL] at hEv; dsimp at hEv
      cases hR : evalPrimitiveOperand bodyLocals locs1 r with
      | error _ => rw [hR] at hEv; cases hEv
      | ok resR =>
        let ⟨rvv, locs2⟩ := resR
        rw [hR] at hEv; dsimp at hEv
        cases hB : evalBinOp op lv rvv with
        | error _ => rw [hB] at hEv; cases hEv
        | ok _ =>
          rw [hB] at hEv; injection hEv with h1; injection h1 with _ hL2; subst hL2
          exact deinitMovePrimNonZero_sound (deinitMovePrimNonZero_sound hEnv hL) hR
  | discriminant p =>
    dsimp [deinitMovesInRvalueNonZero]
    dsimp [evalRvalue] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases ty with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hSl] at hEv; cases hEv
          | some slot =>
            rw [hSl] at hEv; dsimp at hEv
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEv; cases hEv
            | true =>
              rw [hAdm] at hEv; dsimp at hEv
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp at hEv
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEv; cases hEv
                    | some _ =>
                      rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL
                      exact hEnv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL
                          exact hEnv
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
              | scalar _ _ =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none => cases hEv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL
                          exact hEnv
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEv

private theorem isValidNonZeroIntConst_elim {w : IntWidth} {s : Bool} {c : ConstOperand}
    (h : isValidNonZeroIntConst w s c = true) :
    ∃ b : BitVec 128,
      c.ty = .int w s ∧
      evalConstLit c.ty c.lit = .ok (.scalar ⟨w, s, b⟩) ∧
      truncateBits w b = b ∧
      decodeScalar ⟨w, s, b⟩ ≠ 0 := by
  unfold isValidNonZeroIntConst at h
  let ⟨hTyB, hRest⟩ := bool_and_true h
  have hTyEq := mirTy_beq_eq hTyB
  cases hLit : evalConstLit (.int w s) c.lit with
  | error _ => rw [hLit] at hRest; cases hRest
  | ok val =>
    rw [hLit] at hRest
    cases val with
    | ptr _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hRest
    | scalar sv =>
      have hChk := evalConstLit_checkVal hLit
      let ⟨b, hsv, hWf⟩ := checkVal_int_iff.mp hChk
      injection hsv with hsvEq; subst hsvEq
      dsimp at hRest
      have hNe0 : decodeScalar ⟨w, s, b⟩ ≠ 0 := by
        intro hEq0
        rw [hEq0] at hRest
        cases hRest
      refine ⟨b, hTyEq, ?_, hWf, hNe0⟩
      rw [hTyEq]; exact hLit

private theorem rvalueProducesNonZero_sound {bodyLocals : List MirTy}
    {env : List NonZeroAbsSlot} {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hProd : rvalueProducesNonZero bodyLocals env dstTy rv = true)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals'))
    (hChk : checkVal v dstTy = true) :
    NonZeroSlotSound dstTy .liveNonZero (.live (some v)) := by
  cases rv with
  | unaryOp _ _ | binaryOp _ _ _ | discriminant _ | ref _ _
  | addressOf _ _ | aggregateTuple _ | unsupported => cases hProd
  | use opnd =>
    cases opnd with
    | constant c =>
      dsimp [rvalueProducesNonZero, constProducesNonZeroScalar] at hProd
      cases dstTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
        cases hProd
      | int w s =>
        let ⟨b, hCTy, hEvC, hWf, hNe0⟩ := isValidNonZeroIntConst_elim hProd
        dsimp [evalRvalue, evalOperandToSlot] at hEv
        rw [hEvC] at hEv; dsimp at hEv
        rw [hCTy, mirTy_beq_refl (.int w s)] at hEv; dsimp at hEv
        injection hEv with h1; injection h1 with hvEq _; subst hvEq
        exact ⟨hChk, ⟨w, s, b, rfl, rfl, hWf, hNe0⟩⟩
    | copy p =>
      dsimp [rvalueProducesNonZero] at hProd
      let ⟨hPEmp, hMatch⟩ := bool_and_true hProd
      cases hSrcTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hSrcTy] at hMatch; cases hMatch
      | some srcTy =>
        rw [hSrcTy] at hMatch
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hMatch; cases hMatch
        | some abs =>
          rw [hAbs] at hMatch
          cases abs with
          | dead | liveUninit | liveInit => cases hMatch
          | liveNonZero =>
            have hTyEq := mirTy_beq_eq hMatch; subst hTyEq
            dsimp [evalRvalue, evalOperandToSlot] at hEv
            rw [hPEmp] at hEv; dsimp at hEv
            rw [hSrcTy] at hEv
            cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
            | none => rw [hSl] at hEv; cases hEv
            | some sl =>
              rw [hSl] at hEv
              have hSlS := hEnv.2.2 p.localId srcTy .liveNonZero sl hSrcTy hAbs hSl
              let ⟨_, w, s, b, hIntEq, hSlEq, hWf, hNe0⟩ := hSlS
              rw [hSlEq] at hEv; dsimp at hEv
              rw [mirTy_beq_refl srcTy] at hEv; dsimp at hEv
              injection hEv with h1; injection h1 with hvEq _; subst hvEq
              exact ⟨hChk, ⟨w, s, b, hIntEq, rfl, hWf, hNe0⟩⟩
    | move p =>
      dsimp [rvalueProducesNonZero] at hProd
      let ⟨hPEmp, hMatch⟩ := bool_and_true hProd
      cases hSrcTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hSrcTy] at hMatch; cases hMatch
      | some srcTy =>
        rw [hSrcTy] at hMatch
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hMatch; cases hMatch
        | some abs =>
          rw [hAbs] at hMatch
          cases abs with
          | dead | liveUninit | liveInit => cases hMatch
          | liveNonZero =>
            have hTyEq := mirTy_beq_eq hMatch; subst hTyEq
            dsimp [evalRvalue, evalOperandToSlot] at hEv
            rw [hPEmp] at hEv; dsimp at hEv
            rw [hSrcTy] at hEv
            cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
            | none => rw [hSl] at hEv; cases hEv
            | some sl =>
              rw [hSl] at hEv
              have hSlS := hEnv.2.2 p.localId srcTy .liveNonZero sl hSrcTy hAbs hSl
              let ⟨_, w, s, b, hIntEq, hSlEq, hWf, hNe0⟩ := hSlS
              rw [hSlEq] at hEv; dsimp at hEv
              cases hSet : setElem? locals p.localId (liveUninitSlot srcTy) with
              | none => rw [hSet] at hEv; cases hEv
              | some locs1 =>
                rw [hSet] at hEv; dsimp at hEv
                rw [mirTy_beq_refl srcTy] at hEv; dsimp at hEv
                injection hEv with h1; injection h1 with hvEq _; subst hvEq
                exact ⟨hChk, ⟨w, s, b, hIntEq, rfl, hWf, hNe0⟩⟩

private theorem isCertifiedNonZeroDivisor_sound {bodyLocals : List MirTy}
    {env : List NonZeroAbsSlot} {locals : List LocalSlot}
    {w : IntWidth} {s : Bool} {rhs : Operand}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hDiv : isCertifiedNonZeroDivisor bodyLocals env w s rhs = true) :
    ∃ b : BitVec 128,
      evalPrimitiveOperand bodyLocals locals rhs = .ok (.scalar ⟨w, s, b⟩, locals) ∧
      truncateBits w b = b ∧
      decodeScalar ⟨w, s, b⟩ ≠ 0 := by
  cases rhs with
  | move _ => cases hDiv
  | constant c =>
    let ⟨b, hCTy, hEvC, hWf, hNe0⟩ := isValidNonZeroIntConst_elim hDiv
    refine ⟨b, ?_, hWf, hNe0⟩
    dsimp [evalPrimitiveOperand, evalOperandToSlot]
    rw [hEvC]; dsimp; rw [hCTy]; rfl
  | copy p =>
    dsimp [isCertifiedNonZeroDivisor] at hDiv
    let ⟨hPEmp, hMatch⟩ := bool_and_true hDiv
    cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
    | none => rw [hTy] at hMatch; cases hMatch
    | some ty =>
      rw [hTy] at hMatch
      cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
      | none => rw [hAbs] at hMatch; cases hMatch
      | some abs =>
        rw [hAbs] at hMatch
        cases abs with
        | dead | liveUninit | liveInit => cases hMatch
        | liveNonZero =>
          have hTyEq := mirTy_beq_eq hMatch; subst hTyEq
          have hLtL : p.localId < locals.length := by
            rw [hEnv.1.1]; exact getElem?_some_lt hTy
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
          let ⟨_, w', s', b, hIntEq, hSlEq, hWf, hNe0⟩ :=
            hEnv.2.2 p.localId (.int w s) .liveNonZero sl hTy hAbs hSl
          injection hIntEq with hw hs; subst hw; subst hs
          refine ⟨b, ?_, hWf, hNe0⟩
          dsimp [evalPrimitiveOperand, evalOperandToSlot]
          rw [hPEmp]; dsimp; rw [hTy, hSl, hSlEq]; rfl

private theorem isCertifiedSignedSafeDivisor_sound {bodyLocals : List MirTy}
    {locals : List LocalSlot} {w : IntWidth} {rhs : Operand}
    (hDiv : isCertifiedSignedSafeDivisor w rhs = true) :
    ∃ b : BitVec 128,
      evalPrimitiveOperand bodyLocals locals rhs = .ok (.scalar ⟨w, true, b⟩, locals) ∧
      (decodeScalar ⟨w, true, b⟩ == 0) = false ∧
      (decodeScalar ⟨w, true, b⟩ == Neg.neg 1) = false := by
  cases rhs with
  | copy _ | move _ => cases hDiv
  | constant c =>
    unfold isCertifiedSignedSafeDivisor at hDiv
    let ⟨hTyB, hRest⟩ := bool_and_true hDiv
    have hTyEq := mirTy_beq_eq hTyB
    cases hLit : evalConstLit (.int w true) c.lit with
    | error _ => rw [hLit] at hRest; cases hRest
    | ok val =>
      rw [hLit] at hRest
      cases val with
      | ptr _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hRest
      | scalar sv =>
        have hChk := evalConstLit_checkVal hLit
        let ⟨b, hsv, _⟩ := checkVal_int_iff.mp hChk
        injection hsv with hsvEq; subst hsvEq
        dsimp at hRest
        let ⟨hNe0B, hNeNeg1B⟩ := bool_and_true hRest
        refine ⟨b, ?_, bool_not_true hNe0B, bool_not_true hNeNeg1B⟩
        dsimp [evalPrimitiveOperand, evalOperandToSlot]
        rw [hTyEq, hLit]; rfl

private theorem operandCertifiedPrimitiveTy?_total {bodyLocals : List MirTy}
    {env : List NonZeroAbsSlot} {locals : List LocalSlot}
    {dst : LocalId} {opnd : Operand} {opTy : MirTy}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hCert : operandCertifiedPrimitiveTy? bodyLocals env dst opnd = some opTy) :
    ∃ v locals',
      evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals') ∧
      checkVal v opTy = true ∧
      NonZeroEnvSound bodyLocals (deinitMoveOperandNonZero bodyLocals env opnd) locals' := by
  cases opnd with
  | constant c =>
    dsimp [operandCertifiedPrimitiveTy?] at hCert
    cases hPr : isPrimitiveReadableTy c.ty with
    | false => rw [hPr] at hCert; cases hCert
    | true =>
      rw [hPr] at hCert; dsimp at hCert
      cases hLit : evalConstLit c.ty c.lit with
      | error _ => rw [hLit] at hCert; cases hCert
      | ok v =>
        rw [hLit] at hCert; dsimp at hCert
        cases hChk : checkVal v c.ty with
        | false => rw [hChk] at hCert; cases hCert
        | true =>
          rw [hChk] at hCert; dsimp at hCert
          injection hCert with hTyEq; subst hTyEq
          refine ⟨v, locals, ?_, hChk, hEnv⟩
          dsimp [evalPrimitiveOperand, evalOperandToSlot]
          rw [hLit]; dsimp; rw [hPr]; rfl
  | copy p =>
    dsimp [operandCertifiedPrimitiveTy?] at hCert
    cases hPE : p.projection.isEmpty with
    | false => rw [hPE] at hCert; cases hCert
    | true =>
      rw [hPE] at hCert; dsimp at hCert
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hCert; cases hCert
      | some ty =>
        rw [hTy] at hCert
        cases hSlE : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hSlE] at hCert; cases hCert
        | some slot =>
          rw [hSlE] at hCert; dsimp at hCert
          cases hCond : (isPrimitiveReadableTy ty && nonZeroSlotImplies slot .liveInit) with
          | false => rw [hCond] at hCert; cases hCert
          | true =>
            rw [hCond] at hCert; dsimp at hCert
            injection hCert with hTyEq; subst hTyEq
            let ⟨hPr, hImp⟩ := bool_and_true hCond
            have hLtL : p.localId < locals.length := by
              rw [hEnv.1.1]; exact getElem?_some_lt hTy
            let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
            have hInitS := nonZeroSlotImplies_sound hImp (hEnv.2.2 p.localId ty slot sl hTy hSlE hSl)
            let ⟨hWtSl, v, hSlEq⟩ := hInitS
            subst hSlEq
            refine ⟨v, locals, ?_, hWtSl, hEnv⟩
            dsimp [evalPrimitiveOperand, evalOperandToSlot]
            rw [hPE]; dsimp; rw [hTy, hSl]; dsimp; rw [hPr]; rfl
  | move p =>
    dsimp [operandCertifiedPrimitiveTy?] at hCert
    cases hG : (p.projection.isEmpty && Nat.beq p.localId dst) with
    | false => rw [hG] at hCert; cases hCert
    | true =>
      rw [hG] at hCert; dsimp at hCert
      let ⟨hPE, _⟩ := bool_and_true hG
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hCert; cases hCert
      | some ty =>
        rw [hTy] at hCert
        cases hSlE : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hSlE] at hCert; cases hCert
        | some slot =>
          rw [hSlE] at hCert; dsimp at hCert
          cases hCond : (isPrimitiveReadableTy ty && nonZeroSlotImplies slot .liveInit) with
          | false => rw [hCond] at hCert; cases hCert
          | true =>
            rw [hCond] at hCert; dsimp at hCert
            injection hCert with hTyEq; subst hTyEq
            let ⟨hPr, hImp⟩ := bool_and_true hCond
            have hLtL : p.localId < locals.length := by
              rw [hEnv.1.1]; exact getElem?_some_lt hTy
            let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
            let ⟨locs', hSetL⟩ := setElem?_some_of_lt locals p.localId (liveUninitSlot ty) hLtL
            have hInitS := nonZeroSlotImplies_sound hImp (hEnv.2.2 p.localId ty slot sl hTy hSlE hSl)
            let ⟨hWtSl, v, hSlEq⟩ := hInitS
            subst hSlEq
            have hEvP : evalPrimitiveOperand bodyLocals locals (.move p) = .ok (v, locs') := by
              dsimp [evalPrimitiveOperand, evalOperandToSlot]
              rw [hPE]; dsimp; rw [hTy, hSl]; dsimp; rw [hSetL]; dsimp; rw [hPr]; rfl
            exact ⟨v, locs', hEvP, hWtSl, deinitMovePrimNonZero_sound hEnv hEvP⟩

private theorem evalArithOp_add_ok (w : IntWidth) (s : Bool) (l r : Int) :
    ∃ sv : ScalarVal,
      evalArithOp .add w s l r = .ok (.scalar sv) ∧
      checkVal (.scalar sv) (.int w s) = true := by
  cases s with
  | false =>
    let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w false (l + r)
    refine ⟨_, ?_, hChk⟩
    unfold evalArithOp
    change (match truncateScalar w false (l + r) with
      | Except.error k => Except.error k
      | Except.ok (val, lossy) =>
        if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
        else Except.ok (Val.scalar val)) = _
    rw [hTr]
    change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
    rw [if_bool_false (bool_and_false _)]
  | true =>
    let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w true (l + r)
    refine ⟨_, ?_, hChk⟩
    unfold evalArithOp
    change (match truncateScalar w true (l + r) with
      | Except.error k => Except.error k
      | Except.ok (val, lossy) =>
        if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
        else Except.ok (Val.scalar val)) = _
    rw [hTr]
    change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
    rw [if_bool_false (bool_and_false _)]

private theorem evalArithOp_sub_ok (w : IntWidth) (s : Bool) (l r : Int) :
    ∃ sv : ScalarVal,
      evalArithOp .sub w s l r = .ok (.scalar sv) ∧
      checkVal (.scalar sv) (.int w s) = true := by
  cases s with
  | false =>
    let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w false (l - r)
    refine ⟨_, ?_, hChk⟩
    unfold evalArithOp
    change (match truncateScalar w false (l - r) with
      | Except.error k => Except.error k
      | Except.ok (val, lossy) =>
        if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
        else Except.ok (Val.scalar val)) = _
    rw [hTr]
    change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
    rw [if_bool_false (bool_and_false _)]
  | true =>
    let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w true (l - r)
    refine ⟨_, ?_, hChk⟩
    unfold evalArithOp
    change (match truncateScalar w true (l - r) with
      | Except.error k => Except.error k
      | Except.ok (val, lossy) =>
        if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
        else Except.ok (Val.scalar val)) = _
    rw [hTr]
    change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
    rw [if_bool_false (bool_and_false _)]

private theorem evalArithOp_mul_ok (w : IntWidth) (s : Bool) (l r : Int) :
    ∃ sv : ScalarVal,
      evalArithOp .mul w s l r = .ok (.scalar sv) ∧
      checkVal (.scalar sv) (.int w s) = true := by
  cases s with
  | false =>
    let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w false (l * r)
    refine ⟨_, ?_, hChk⟩
    unfold evalArithOp
    change (match truncateScalar w false (l * r) with
      | Except.error k => Except.error k
      | Except.ok (val, lossy) =>
        if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
        else Except.ok (Val.scalar val)) = _
    rw [hTr]
    change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
    rw [if_bool_false (bool_and_false _)]
  | true =>
    let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w true (l * r)
    refine ⟨_, ?_, hChk⟩
    unfold evalArithOp
    change (match truncateScalar w true (l * r) with
      | Except.error k => Except.error k
      | Except.ok (val, lossy) =>
        if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
        else Except.ok (Val.scalar val)) = _
    rw [hTr]
    change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
    rw [if_bool_false (bool_and_false _)]

private theorem binOpCertifiedTotal_total {bodyLocals : List MirTy}
    {env₁ : List NonZeroAbsSlot} {locals₁ locals₂ : List LocalSlot}
    {op : BinOp} {lhsTy rhsTy dstTy : MirTy} {rhs : Operand}
    {lVal rVal : Val}
    (hEnv1 : NonZeroEnvSound bodyLocals env₁ locals₁)
    (hCert : binOpCertifiedTotal bodyLocals env₁ op lhsTy rhsTy dstTy rhs = true)
    (hChkL : checkVal lVal lhsTy = true)
    (hEvR : evalPrimitiveOperand bodyLocals locals₁ rhs = .ok (rVal, locals₂))
    (hChkR : checkVal rVal rhsTy = true) :
    ∃ res, evalBinOp op lVal rVal = .ok res ∧ checkVal res dstTy = true := by
  cases op with
  | addUnchecked | subUnchecked | mulUnchecked
  | shlUnchecked | shrUnchecked | offset
  | addWithOverflow | subWithOverflow | mulWithOverflow =>
    cases hCert
  | add =>
    dsimp [binOpCertifiedTotal] at hCert
    cases lhsTy with
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
    | int w s =>
      let ⟨hRTyB, hDTyB⟩ := bool_and_true hCert
      rw [mirTy_beq_eq hRTyB] at hChkR; rw [mirTy_beq_eq hDTyB]
      let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
      let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
      unfold evalBinOp BinOp.isShift; dsimp
      rw [intWidth_beq_refl w, bool_beq_refl s]; dsimp
      let ⟨sv, hOk, hChk⟩ := evalArithOp_add_ok w s
        (decodeScalar ⟨w, s, lb⟩) (decodeScalar ⟨w, s, rb⟩)
      exact ⟨.scalar sv, hOk, hChk⟩
  | sub =>
    dsimp [binOpCertifiedTotal] at hCert
    cases lhsTy with
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
    | int w s =>
      let ⟨hRTyB, hDTyB⟩ := bool_and_true hCert
      rw [mirTy_beq_eq hRTyB] at hChkR; rw [mirTy_beq_eq hDTyB]
      let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
      let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
      unfold evalBinOp BinOp.isShift; dsimp
      rw [intWidth_beq_refl w, bool_beq_refl s]; dsimp
      let ⟨sv, hOk, hChk⟩ := evalArithOp_sub_ok w s
        (decodeScalar ⟨w, s, lb⟩) (decodeScalar ⟨w, s, rb⟩)
      exact ⟨.scalar sv, hOk, hChk⟩
  | mul =>
    dsimp [binOpCertifiedTotal] at hCert
    cases lhsTy with
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
    | int w s =>
      let ⟨hRTyB, hDTyB⟩ := bool_and_true hCert
      rw [mirTy_beq_eq hRTyB] at hChkR; rw [mirTy_beq_eq hDTyB]
      let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
      let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
      unfold evalBinOp BinOp.isShift; dsimp
      rw [intWidth_beq_refl w, bool_beq_refl s]; dsimp
      let ⟨sv, hOk, hChk⟩ := evalArithOp_mul_ok w s
        (decodeScalar ⟨w, s, lb⟩) (decodeScalar ⟨w, s, rb⟩)
      exact ⟨.scalar sv, hOk, hChk⟩
  | bitAnd =>
    dsimp [binOpCertifiedTotal] at hCert
    cases bool_or_true hCert with
    | inl hB =>
      let ⟨h12, hDT⟩ := bool_and_true hB; let ⟨hLT, hRT⟩ := bool_and_true h12
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨.bool (lb && rb), rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        let ⟨hRT, hDT⟩ := bool_and_true hI
        rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp
        rw [intWidth_beq_refl w, bool_beq_refl s]; dsimp
        exact ⟨_, rfl, checkVal_int_iff.mpr ⟨_, rfl, truncateBits_idem w _⟩⟩
  | bitOr =>
    dsimp [binOpCertifiedTotal] at hCert
    cases bool_or_true hCert with
    | inl hB =>
      let ⟨h12, hDT⟩ := bool_and_true hB; let ⟨hLT, hRT⟩ := bool_and_true h12
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨.bool (lb || rb), rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        let ⟨hRT, hDT⟩ := bool_and_true hI
        rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp
        rw [intWidth_beq_refl w, bool_beq_refl s]; dsimp
        exact ⟨_, rfl, checkVal_int_iff.mpr ⟨_, rfl, truncateBits_idem w _⟩⟩
  | bitXor =>
    dsimp [binOpCertifiedTotal] at hCert
    cases bool_or_true hCert with
    | inl hB =>
      let ⟨h12, hDT⟩ := bool_and_true hB; let ⟨hLT, hRT⟩ := bool_and_true h12
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨.bool (bne lb rb), rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        let ⟨hRT, hDT⟩ := bool_and_true hI
        rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp
        rw [intWidth_beq_refl w, bool_beq_refl s]; dsimp
        exact ⟨_, rfl, checkVal_int_iff.mpr ⟨_, rfl, truncateBits_idem w _⟩⟩
  | eq =>
    dsimp [binOpCertifiedTotal] at hCert
    let ⟨hDT, hDisj⟩ := bool_and_true hCert; rw [mirTy_beq_eq hDT]
    cases bool_or_true hDisj with
    | inl hB =>
      let ⟨hLT, hRT⟩ := bool_and_true hB
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨_, rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        rw [mirTy_beq_eq hI] at hChkR
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp; rw [intWidth_beq_refl w, bool_beq_refl s]
        exact ⟨_, rfl, rfl⟩
  | ne =>
    dsimp [binOpCertifiedTotal] at hCert
    let ⟨hDT, hDisj⟩ := bool_and_true hCert; rw [mirTy_beq_eq hDT]
    cases bool_or_true hDisj with
    | inl hB =>
      let ⟨hLT, hRT⟩ := bool_and_true hB
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨_, rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        rw [mirTy_beq_eq hI] at hChkR
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp; rw [intWidth_beq_refl w, bool_beq_refl s]
        exact ⟨_, rfl, rfl⟩
  | lt =>
    dsimp [binOpCertifiedTotal] at hCert
    let ⟨hDT, hDisj⟩ := bool_and_true hCert; rw [mirTy_beq_eq hDT]
    cases bool_or_true hDisj with
    | inl hB =>
      let ⟨hLT, hRT⟩ := bool_and_true hB
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨_, rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        rw [mirTy_beq_eq hI] at hChkR
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp; rw [intWidth_beq_refl w, bool_beq_refl s]
        exact ⟨_, rfl, rfl⟩
  | le =>
    dsimp [binOpCertifiedTotal] at hCert
    let ⟨hDT, hDisj⟩ := bool_and_true hCert; rw [mirTy_beq_eq hDT]
    cases bool_or_true hDisj with
    | inl hB =>
      let ⟨hLT, hRT⟩ := bool_and_true hB
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨_, rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        rw [mirTy_beq_eq hI] at hChkR
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp; rw [intWidth_beq_refl w, bool_beq_refl s]
        exact ⟨_, rfl, rfl⟩
  | gt =>
    dsimp [binOpCertifiedTotal] at hCert
    let ⟨hDT, hDisj⟩ := bool_and_true hCert; rw [mirTy_beq_eq hDT]
    cases bool_or_true hDisj with
    | inl hB =>
      let ⟨hLT, hRT⟩ := bool_and_true hB
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨_, rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        rw [mirTy_beq_eq hI] at hChkR
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp; rw [intWidth_beq_refl w, bool_beq_refl s]
        exact ⟨_, rfl, rfl⟩
  | ge =>
    dsimp [binOpCertifiedTotal] at hCert
    let ⟨hDT, hDisj⟩ := bool_and_true hCert; rw [mirTy_beq_eq hDT]
    cases bool_or_true hDisj with
    | inl hB =>
      let ⟨hLT, hRT⟩ := bool_and_true hB
      rw [mirTy_beq_eq hLT] at hChkL; rw [mirTy_beq_eq hRT] at hChkR
      let ⟨lb, hL⟩ := checkVal_bool_iff.mp hChkL; subst hL
      let ⟨rb, hR⟩ := checkVal_bool_iff.mp hChkR; subst hR
      exact ⟨_, rfl, rfl⟩
    | inr hI =>
      cases lhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hI
      | int w s =>
        rw [mirTy_beq_eq hI] at hChkR
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        unfold evalBinOp BinOp.isShift; dsimp; rw [intWidth_beq_refl w, bool_beq_refl s]
        exact ⟨_, rfl, rfl⟩
  | shl =>
    dsimp [binOpCertifiedTotal] at hCert
    cases lhsTy with
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
    | int w s =>
      cases rhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
      | int rw rs =>
        rw [mirTy_beq_eq hCert]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        let shRes := intShiftLeft (decodeScalar ⟨w, s, lb⟩)
          (intEmod (decodeScalar ⟨rw, rs, rb⟩) (Int.ofNat w.bitWidth)).toNat
        let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w s shRes
        refine ⟨_, ?_, hChk⟩
        unfold evalBinOp evalShiftOp
        change (match truncateScalar w s shRes with
          | Except.error k => Except.error k
          | Except.ok (res, _) =>
            if (_ && false) = true then Except.error FaultKind.undefined
            else Except.ok (Val.scalar res)) = _
        rw [hTr]
        change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
        rw [if_bool_false (bool_and_false _)]
  | shr =>
    dsimp [binOpCertifiedTotal] at hCert
    cases lhsTy with
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
    | int w s =>
      cases rhsTy with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
      | int rw rs =>
        rw [mirTy_beq_eq hCert]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hR, _⟩ := checkVal_int_iff.mp hChkR; subst hR
        let shRes := intShiftRight (decodeScalar ⟨w, s, lb⟩)
          (intEmod (decodeScalar ⟨rw, rs, rb⟩) (Int.ofNat w.bitWidth)).toNat
        let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w s shRes
        refine ⟨_, ?_, hChk⟩
        unfold evalBinOp evalShiftOp
        change (match truncateScalar w s shRes with
          | Except.error k => Except.error k
          | Except.ok (res, _) =>
            if (_ && false) = true then Except.error FaultKind.undefined
            else Except.ok (Val.scalar res)) = _
        rw [hTr]
        change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
        rw [if_bool_false (bool_and_false _)]
  | div =>
    dsimp [binOpCertifiedTotal] at hCert
    cases lhsTy with
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
    | int w s =>
      cases s with
      | false =>
        let ⟨h12, hDivC⟩ := bool_and_true hCert
        let ⟨hRT, hDT⟩ := bool_and_true h12
        rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hEvR2, _, hNe0⟩ := isCertifiedNonZeroDivisor_sound hEnv1 hDivC
        rw [hEvR] at hEvR2; injection hEvR2 with q1; injection q1 with hREq _; subst hREq
        let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w false
          (intTdiv (decodeScalar ⟨w, false, lb⟩) (decodeScalar ⟨w, false, rb⟩))
        refine ⟨_, ?_, hChk⟩
        unfold evalBinOp BinOp.isShift; dsimp
        rw [intWidth_beq_refl w]; dsimp
        unfold evalArithOp
        change (if (decodeScalar ⟨w, false, rb⟩ == 0) = true then Except.error FaultKind.undefined
          else match truncateScalar w false
            (intTdiv (decodeScalar ⟨w, false, lb⟩) (decodeScalar ⟨w, false, rb⟩)) with
          | Except.error k => Except.error k
          | Except.ok (val, lossy) =>
            if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
            else Except.ok (Val.scalar val)) = _
        have hBeq0 : (decodeScalar ⟨w, false, rb⟩ == 0) = false := decide_prop_false hNe0
        rw [if_bool_false hBeq0, hTr]
        change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
        rw [if_bool_false (bool_and_false _)]
      | true =>
        let ⟨h12, hDivC⟩ := bool_and_true hCert
        let ⟨hRT, hDT⟩ := bool_and_true h12
        rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hEvR2, hNe0, hNeNeg1⟩ :=
          isCertifiedSignedSafeDivisor_sound (bodyLocals := bodyLocals) (locals := locals₁) hDivC
        rw [hEvR] at hEvR2; injection hEvR2 with q1; injection q1 with hREq _; subst hREq
        let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w true
          (intTdiv (decodeScalar ⟨w, true, lb⟩) (decodeScalar ⟨w, true, rb⟩))
        refine ⟨_, ?_, hChk⟩
        unfold evalBinOp BinOp.isShift; dsimp
        rw [intWidth_beq_refl w]; dsimp
        unfold evalArithOp
        have hC2 : ((decodeScalar ⟨w, true, lb⟩ == signedMinInt w) &&
            (decodeScalar ⟨w, true, rb⟩ == Neg.neg 1)) = false := by
          rw [hNeNeg1]; exact bool_and_false _
        change (if (decodeScalar ⟨w, true, rb⟩ == 0) = true then Except.error FaultKind.undefined
          else if ((decodeScalar ⟨w, true, lb⟩ == signedMinInt w) &&
            (decodeScalar ⟨w, true, rb⟩ == Neg.neg 1)) = true then Except.error FaultKind.undefined
          else match truncateScalar w true
            (intTdiv (decodeScalar ⟨w, true, lb⟩) (decodeScalar ⟨w, true, rb⟩)) with
          | Except.error k => Except.error k
          | Except.ok (val, lossy) =>
            if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
            else Except.ok (Val.scalar val)) = _
        rw [if_bool_false hNe0, if_bool_false hC2, hTr]
        change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
        rw [if_bool_false (bool_and_false _)]
  | rem =>
    dsimp [binOpCertifiedTotal] at hCert
    cases lhsTy with
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hCert
    | int w s =>
      cases s with
      | false =>
        let ⟨h12, hDivC⟩ := bool_and_true hCert
        let ⟨hRT, hDT⟩ := bool_and_true h12
        rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hEvR2, _, hNe0⟩ := isCertifiedNonZeroDivisor_sound hEnv1 hDivC
        rw [hEvR] at hEvR2; injection hEvR2 with q1; injection q1 with hREq _; subst hREq
        let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w false
          (intTmod (decodeScalar ⟨w, false, lb⟩) (decodeScalar ⟨w, false, rb⟩))
        refine ⟨_, ?_, hChk⟩
        unfold evalBinOp BinOp.isShift; dsimp
        rw [intWidth_beq_refl w]; dsimp
        unfold evalArithOp
        change (if (decodeScalar ⟨w, false, rb⟩ == 0) = true then Except.error FaultKind.undefined
          else match truncateScalar w false
            (intTmod (decodeScalar ⟨w, false, lb⟩) (decodeScalar ⟨w, false, rb⟩)) with
          | Except.error k => Except.error k
          | Except.ok (val, lossy) =>
            if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
            else Except.ok (Val.scalar val)) = _
        have hBeq0 : (decodeScalar ⟨w, false, rb⟩ == 0) = false := decide_prop_false hNe0
        rw [if_bool_false hBeq0, hTr]
        change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
        rw [if_bool_false (bool_and_false _)]
      | true =>
        let ⟨h12, hDivC⟩ := bool_and_true hCert
        let ⟨hRT, hDT⟩ := bool_and_true h12
        rw [mirTy_beq_eq hRT] at hChkR; rw [mirTy_beq_eq hDT]
        let ⟨lb, hL, _⟩ := checkVal_int_iff.mp hChkL; subst hL
        let ⟨rb, hEvR2, hNe0, hNeNeg1⟩ :=
          isCertifiedSignedSafeDivisor_sound (bodyLocals := bodyLocals) (locals := locals₁) hDivC
        rw [hEvR] at hEvR2; injection hEvR2 with q1; injection q1 with hREq _; subst hREq
        let ⟨lossy, hTr, hChk⟩ := truncateScalar_ok w true
          (intTmod (decodeScalar ⟨w, true, lb⟩) (decodeScalar ⟨w, true, rb⟩))
        refine ⟨_, ?_, hChk⟩
        unfold evalBinOp BinOp.isShift; dsimp
        rw [intWidth_beq_refl w]; dsimp
        unfold evalArithOp
        have hC2 : ((decodeScalar ⟨w, true, lb⟩ == signedMinInt w) &&
            (decodeScalar ⟨w, true, rb⟩ == Neg.neg 1)) = false := by
          rw [hNeNeg1]; exact bool_and_false _
        change (if (decodeScalar ⟨w, true, rb⟩ == 0) = true then Except.error FaultKind.undefined
          else if ((decodeScalar ⟨w, true, lb⟩ == signedMinInt w) &&
            (decodeScalar ⟨w, true, rb⟩ == Neg.neg 1)) = true then Except.error FaultKind.undefined
          else match truncateScalar w true
            (intTmod (decodeScalar ⟨w, true, lb⟩) (decodeScalar ⟨w, true, rb⟩)) with
          | Except.error k => Except.error k
          | Except.ok (val, lossy) =>
            if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
            else Except.ok (Val.scalar val)) = _
        rw [if_bool_false hNe0, if_bool_false hC2, hTr]
        change (if (_ && false) = true then Except.error FaultKind.undefined else Except.ok _) = _
        rw [if_bool_false (bool_and_false _)]

private theorem rvalueCertifiedTotal_binOp_general {bodyLocals : List MirTy}
    {env : List NonZeroAbsSlot} {locals : List LocalSlot}
    {dst : LocalId} {dstTy : MirTy} {op : BinOp} {lhs rhs : Operand}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hArm : (match operandCertifiedPrimitiveTy? bodyLocals env dst lhs with
      | none => false
      | some lhsTy =>
        let env₁ := deinitMoveOperandNonZero bodyLocals env lhs
        match operandCertifiedPrimitiveTy? bodyLocals env₁ dst rhs with
        | none => false
        | some rhsTy =>
          binOpCertifiedTotal bodyLocals env₁ op lhsTy rhsTy dstTy rhs) = true) :
    ∃ val locals',
      evalRvalue bodyLocals locals dstTy (.binaryOp op lhs rhs) = .ok (val, locals') ∧
      checkVal val dstTy = true := by
  cases hCL : operandCertifiedPrimitiveTy? bodyLocals env dst lhs with
  | none => rw [hCL] at hArm; cases hArm
  | some lhsTy =>
    rw [hCL] at hArm; dsimp only at hArm
    let ⟨lVal, locs1, hEvL, hChkL, hEnv1⟩ := operandCertifiedPrimitiveTy?_total hEnv hCL
    cases hCR : operandCertifiedPrimitiveTy? bodyLocals
        (deinitMoveOperandNonZero bodyLocals env lhs) dst rhs with
    | none => rw [hCR] at hArm; cases hArm
    | some rhsTy =>
      rw [hCR] at hArm; dsimp only at hArm
      let ⟨rVal, locs2, hEvR, hChkR, _⟩ := operandCertifiedPrimitiveTy?_total hEnv1 hCR
      let ⟨res, hEvB, hChkRes⟩ := binOpCertifiedTotal_total hEnv1 hArm hChkL hEvR hChkR
      refine ⟨res, locs2, ?_, hChkRes⟩
      dsimp [evalRvalue]; rw [hEvL]; dsimp; rw [hEvR]; dsimp; rw [hEvB]

private theorem rvalueCertifiedTotal_total {bodyLocals : List MirTy}
    {env : List NonZeroAbsSlot} {locals : List LocalSlot}
    {dst : LocalId} {dstTy : MirTy} {rv : Rvalue}
    (hEnv : NonZeroEnvSound bodyLocals env locals)
    (hCert : rvalueCertifiedTotal bodyLocals env dst dstTy rv = true) :
    ∃ val locals',
      evalRvalue bodyLocals locals dstTy rv = .ok (val, locals') ∧
      checkVal val dstTy = true := by
  unfold rvalueCertifiedTotal at hCert
  let ⟨_, hMatch⟩ := bool_and_true hCert
  cases rv with
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hMatch
  | use opnd =>
    cases opnd with
    | constant c =>
      dsimp only at hMatch
      let ⟨hCTyB, hLitOk⟩ := bool_and_true hMatch
      have hCTy := mirTy_beq_eq hCTyB
      cases hLit : evalConstLit dstTy c.lit with
      | error _ => rw [hLit] at hLitOk; cases hLitOk
      | ok v =>
        rw [hLit] at hLitOk
        refine ⟨v, locals, ?_, hLitOk⟩
        dsimp [evalRvalue, evalOperandToSlot]
        rw [hCTy, hLit]; dsimp; rw [mirTy_beq_refl dstTy]; rfl
    | copy p =>
      dsimp only at hMatch
      let ⟨hPE, hInner⟩ := bool_and_true hMatch
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hInner; cases hInner
      | some srcTy =>
        rw [hTy] at hInner
        cases hSlE : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hSlE] at hInner; cases hInner
        | some slot =>
          rw [hSlE] at hInner; dsimp only at hInner
          let ⟨hTyEqB, hImp⟩ := bool_and_true hInner
          have hTyEq := mirTy_beq_eq hTyEqB; subst hTyEq
          have hLtL : p.localId < locals.length := by
            rw [hEnv.1.1]; exact getElem?_some_lt hTy
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
          let ⟨hWtSl, v, hSlEq⟩ :=
            nonZeroSlotImplies_sound hImp (hEnv.2.2 p.localId srcTy slot sl hTy hSlE hSl)
          subst hSlEq
          refine ⟨v, locals, ?_, hWtSl⟩
          dsimp [evalRvalue, evalOperandToSlot]
          rw [hPE]; dsimp; rw [hTy, hSl]; dsimp; rw [mirTy_beq_refl srcTy]; rfl
    | move p =>
      dsimp only at hMatch
      let ⟨hPE, hInner⟩ := bool_and_true hMatch
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hInner; cases hInner
      | some srcTy =>
        rw [hTy] at hInner
        cases hSlE : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hSlE] at hInner; cases hInner
        | some slot =>
          rw [hSlE] at hInner; dsimp only at hInner
          let ⟨hTyEqB, hImp⟩ := bool_and_true hInner
          have hTyEq := mirTy_beq_eq hTyEqB; subst hTyEq
          have hLtL : p.localId < locals.length := by
            rw [hEnv.1.1]; exact getElem?_some_lt hTy
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
          let ⟨locs1, hSetL⟩ := setElem?_some_of_lt locals p.localId (liveUninitSlot srcTy) hLtL
          let ⟨hWtSl, v, hSlEq⟩ :=
            nonZeroSlotImplies_sound hImp (hEnv.2.2 p.localId srcTy slot sl hTy hSlE hSl)
          subst hSlEq
          refine ⟨v, locs1, ?_, hWtSl⟩
          dsimp [evalRvalue, evalOperandToSlot]
          rw [hPE]; dsimp; rw [hTy, hSl]; dsimp; rw [hSetL]; dsimp
          rw [mirTy_beq_refl srcTy]; rfl
  | unaryOp op opnd =>
    dsimp only at hMatch
    cases hCOp : operandCertifiedPrimitiveTy? bodyLocals env dst opnd with
    | none => rw [hCOp] at hMatch; cases hMatch
    | some opTy =>
      rw [hCOp] at hMatch; dsimp only at hMatch
      let ⟨hTyEqB, hOpMatch⟩ := bool_and_true hMatch
      have hTyEq := mirTy_beq_eq hTyEqB; subst hTyEq
      let ⟨ov, locs1, hEvO, hChkO, _⟩ := operandCertifiedPrimitiveTy?_total hEnv hCOp
      cases op with
      | ptrMetadata => cases hOpMatch
      | not =>
        cases opTy with
        | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
          cases hOpMatch
        | bool =>
          let ⟨b, hb⟩ := checkVal_bool_iff.mp hChkO; subst hb
          refine ⟨.bool (!b), locs1, ?_, rfl⟩
          dsimp [evalRvalue]; rw [hEvO]; rfl
        | int w s =>
          let ⟨bits, hb, _⟩ := checkVal_int_iff.mp hChkO; subst hb
          let ⟨lossy, hTr, hChkRes⟩ :=
            truncateScalar_ok w s (intNot (decodeScalar ⟨w, s, bits⟩))
          refine ⟨.scalar ⟨w, s, truncateBits w (bvOfInt 128 (intNot (decodeScalar ⟨w, s, bits⟩)))⟩,
                  locs1, ?_, hChkRes⟩
          dsimp [evalRvalue]; rw [hEvO]; dsimp; unfold evalUnOp; dsimp; rw [hTr]
      | neg =>
        cases opTy with
        | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
          cases hOpMatch
        | int w s =>
          cases s with
          | false => cases hOpMatch
          | true =>
            let ⟨bits, hb, _⟩ := checkVal_int_iff.mp hChkO; subst hb
            let ⟨lossy, hTr, hChkRes⟩ :=
              truncateScalar_ok w true (Neg.neg (decodeScalar ⟨w, true, bits⟩))
            refine ⟨.scalar ⟨w, true, truncateBits w (bvOfInt 128 (Neg.neg (decodeScalar ⟨w, true, bits⟩)))⟩,
                    locs1, ?_, hChkRes⟩
            dsimp [evalRvalue]; rw [hEvO]; dsimp; unfold evalUnOp; dsimp; rw [hTr]
  | binaryOp op lhs rhs =>
    cases lhs with
    | copy pL => exact rvalueCertifiedTotal_binOp_general hEnv hMatch
    | move pL => exact rvalueCertifiedTotal_binOp_general hEnv hMatch
    | constant c₁ =>
      cases rhs with
      | copy pR => exact rvalueCertifiedTotal_binOp_general hEnv hMatch
      | move pR => exact rvalueCertifiedTotal_binOp_general hEnv hMatch
      | constant c₂ =>
        dsimp only at hMatch
        let ⟨hPr12, hLitB⟩ := bool_and_true hMatch
        let ⟨hPr1, hPr2⟩ := bool_and_true hPr12
        cases hL1 : evalConstLit c₁.ty c₁.lit with
        | error _ => rw [hL1] at hLitB; cases hLitB
        | ok v₁ =>
          rw [hL1] at hLitB
          cases hL2 : evalConstLit c₂.ty c₂.lit with
          | error _ => rw [hL2] at hLitB; cases hLitB
          | ok v₂ =>
            rw [hL2] at hLitB; dsimp only at hLitB
            cases hB : evalBinOp op v₁ v₂ with
            | error _ => rw [hB] at hLitB; cases hLitB
            | ok res =>
              rw [hB] at hLitB
              refine ⟨res, locals, ?_, hLitB⟩
              dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
              rw [hL1]; dsimp; rw [hPr1]; dsimp
              rw [hL2]; dsimp; rw [hPr2]; dsimp
              rw [hB]
  | discriminant p =>
    dsimp only at hMatch
    let ⟨hPE, hInner⟩ := bool_and_true hMatch
    cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
    | none => rw [hTy] at hInner; cases hInner
    | some pTy =>
      rw [hTy] at hInner
      cases pTy with
      | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
        cases hInner
      | enum ety =>
        cases hSlE : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hSlE] at hInner; cases hInner
        | some slot =>
          rw [hSlE] at hInner; dsimp only at hInner
          let ⟨hAdmDst, hSlotImp⟩ := bool_and_true hInner
          let ⟨hAdm, hDstEqB⟩ := bool_and_true hAdmDst
          rw [mirTy_beq_eq hDstEqB]
          have hDiscPos : 0 < ety.discriminants.length := by
            have hAdmC := hAdm
            unfold enumAdmitted at hAdmC
            let ⟨h1234, _⟩ := bool_and_true hAdmC
            let ⟨h123, _⟩ := bool_and_true h1234
            let ⟨h12, _⟩ := bool_and_true h123
            let ⟨hNotEmp, _⟩ := bool_and_true h12
            exact list_pos_of_isEmpty_false (bool_not_true hNotEmp)
          have hLtL : p.localId < locals.length := by
            rw [hEnv.1.1]; exact getElem?_some_lt hTy
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
          have hSlSound := hEnv.2.2 p.localId (.enum ety) slot sl hTy hSlE hSl
          cases hTr : ety.tagRepr with
          | zeroSized =>
            have hZst : isZstEnumTy ety = true := by
              unfold isZstEnumTy; rw [hTr]; exact hAdm
            rw [if_bool_true hZst] at hSlotImp
            let ⟨hWtSl, opt, hSlEq⟩ := nonZeroSlotImplies_sound hSlotImp hSlSound
            subst hSlEq
            let ⟨disc₀, hDisc0⟩ := getElem?_some_of_lt ety.discriminants 0 hDiscPos
            have hChkRes : checkVal
                (.scalar ⟨ety.discrWidth, ety.discrSigned,
                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc₀)⟩)
                (.int ety.discrWidth ety.discrSigned) = true :=
              checkVal_int_iff.mpr ⟨_, rfl, truncateBits_idem _ _⟩
            cases opt with
            | none =>
              refine ⟨_, locals, ?_, hChkRes⟩
              dsimp [evalRvalue]; rw [hPE]; dsimp; rw [hTy, hSl]; dsimp
              rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hDisc0]
            | some val =>
              have hVEq : val = .enumVal ety 0 := checkVal_zstEnum_eq hZst hWtSl
              subst hVEq
              refine ⟨_, locals, ?_, hChkRes⟩
              dsimp [evalRvalue]; rw [hPE]; dsimp; rw [hTy, hSl]; dsimp
              rw [hAdm]; dsimp; rw [hTr]; dsimp
              rw [enumTy_beq_refl ety]; dsimp; rw [hDisc0]
          | scalar tw ts =>
            have hZstF : isZstEnumTy ety = false := by
              unfold isZstEnumTy; rw [hTr]
            rw [if_bool_false hZstF] at hSlotImp
            let ⟨hWtSl, val, hSlEq⟩ := nonZeroSlotImplies_sound hSlotImp hSlSound
            subst hSlEq
            let ⟨_, idx, hIdxLt, hVEq⟩ := checkVal_enum_iff.mp hWtSl
            subst hVEq
            let ⟨disc, hDisc⟩ := getElem?_some_of_lt ety.discriminants idx hIdxLt
            have hChkRes : checkVal
                (.scalar ⟨ety.discrWidth, ety.discrSigned,
                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                (.int ety.discrWidth ety.discrSigned) = true :=
              checkVal_int_iff.mpr ⟨_, rfl, truncateBits_idem _ _⟩
            refine ⟨_, locals, ?_, hChkRes⟩
            dsimp [evalRvalue]; rw [hPE]; dsimp; rw [hTy, hSl]; dsimp
            rw [hAdm]; dsimp; rw [hTr]; dsimp
            rw [enumTy_beq_refl ety, nat_lt_blt hIdxLt]; dsimp; rw [hDisc]

private theorem stepPlainStmtNonZero_sound {body : Body}
    {env env' : List NonZeroAbsSlot} {frame : FrameState}
    {cm : CallerMemory} {stmt : StatementKind} {s' : State}
    (hEnv : NonZeroEnvSound body.locals env frame.locals)
    (hStep : stepPlainStmtNonZero body.locals env stmt = some env')
    (hEv : evalStatement body frame cm stmt = .step s') :
    ∃ locs',
      s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
             callerMem := cm } ∧
      NonZeroEnvSound body.locals env' locs' := by
  cases stmt with
  | nop =>
    injection hStep with hE; subst hE
    injection hEv with hS; subst hS
    exact ⟨frame.locals, rfl, hEnv⟩
  | unsupported => cases hEv
  | storageLive id =>
    dsimp [stepPlainStmtNonZero] at hStep
    dsimp [evalStatement] at hEv
    cases hTy : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [hTy] at hStep; cases hStep
    | some ty =>
      rw [hTy] at hStep hEv; dsimp at hStep hEv
      cases hSetL : setElem? frame.locals id (liveUninitSlot ty) with
      | none => rw [hSetL] at hEv; cases hEv
      | some locs' =>
        rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
        exact ⟨locs', rfl, nonZeroEnvSound_set hEnv hTy hStep hSetL (nonZeroSlotSound_liveUninit ty)⟩
  | storageDead id =>
    dsimp [stepPlainStmtNonZero] at hStep
    dsimp [evalStatement] at hEv
    cases hZ : Nat.beq id 0 with
    | true => rw [hZ] at hStep; cases hStep
    | false =>
      rw [hZ] at hStep hEv; dsimp at hStep hEv
      cases hSetL : setElem? frame.locals id .dead with
      | none => rw [hSetL] at hEv; cases hEv
      | some locs' =>
        rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
        have hLt : id < body.locals.length := by
          rw [← hEnv.2.1]
          cases Nat.lt_or_ge id env.length with
          | inl hlt => exact hlt
          | inr hge =>
            rw [setElem?_none_of_ge env id .dead hge] at hStep; cases hStep
        let ⟨ty, hTy⟩ := getElem?_some_of_lt body.locals id hLt
        exact ⟨locs', rfl, nonZeroEnvSound_set hEnv hTy hStep hSetL ⟨True.intro, True.intro⟩⟩
  | assign dst rv =>
    dsimp [stepPlainStmtNonZero] at hStep
    dsimp [evalStatement] at hEv
    cases hPEmp : dst.projection.isEmpty with
    | false => rw [hPEmp] at hStep; cases hStep
    | true =>
      rw [hPEmp] at hStep hEv; dsimp at hStep hEv
      cases hDstTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hDstTy] at hStep; cases hStep
      | some dstTy =>
        rw [hDstTy] at hStep hEv; dsimp at hStep hEv
        cases hRv : evalRvalue body.locals frame.locals dstTy rv with
        | error _ => rw [hRv] at hEv; cases hEv
        | ok res =>
          let ⟨val, locs1⟩ := res
          rw [hRv] at hEv; dsimp at hEv
          have hEnv1 := deinitMovesInRvalueNonZero_sound hEnv hRv
          unfold writePlace at hEv
          cases hChk : checkVal val dstTy with
          | false => rw [hChk] at hEv; cases hEv
          | true =>
            rw [hChk] at hEv; dsimp at hEv
            cases hSl1 : Trusted.MirSemantics.getElem? locs1 dst.localId with
            | none => rw [hSl1] at hEv; cases hEv
            | some sl1 =>
              rw [hSl1] at hEv
              cases sl1 with
              | dead => cases hEv
              | live _ =>
                cases hSetL : setElem? locs1 dst.localId (.live (some val)) with
                | none => rw [hSetL] at hEv; cases hEv
                | some locsW =>
                  rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
                  refine ⟨locsW, rfl, nonZeroEnvSound_set hEnv1 hDstTy hStep hSetL ?_⟩
                  cases hProd : rvalueProducesNonZero body.locals env dstTy rv with
                  | true => exact rvalueProducesNonZero_sound hEnv hProd hRv hChk
                  | false => exact ⟨hChk, ⟨val, rfl⟩⟩

private theorem evalOperandToSlot_noMoveExcept {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dst : LocalId} {op : Operand}
    {ty : MirTy} {optVal : Option Val}
    (hNoMove : operandNoMoveExcept dst op = true)
    (hEv : evalOperandToSlot bodyLocals locals op = .ok (ty, optVal, locals')) :
    (∀ i, i ≠ dst →
      Trusted.MirSemantics.getElem? locals' i =
        Trusted.MirSemantics.getElem? locals i) ∧
    (∀ sl, Trusted.MirSemantics.getElem? locals dst = some (.live sl) →
      ∃ sl', Trusted.MirSemantics.getElem? locals' dst = some (.live sl')) ∧
    (∀ sl', Trusted.MirSemantics.getElem? locals' dst = some (.live sl') →
      ∃ sl, Trusted.MirSemantics.getElem? locals dst = some (.live sl)) := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok _ =>
      rw [hC] at hEv; injection hEv with q1; injection q1 with _ q2
      injection q2 with _ qL; subst qL
      exact ⟨fun _ _ => rfl, fun sl h => ⟨sl, h⟩, fun sl' h => ⟨sl', h⟩⟩
  | copy p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some _ =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some slot =>
          rw [hSl] at hEv
          cases slot with
          | dead => cases hEv
          | live _ =>
            injection hEv with q1; injection q1 with _ q2
            injection q2 with _ qL; subst qL
            exact ⟨fun _ _ => rfl, fun sl h => ⟨sl, h⟩, fun sl' h => ⟨sl', h⟩⟩
  | move p =>
    dsimp [operandNoMoveExcept] at hNoMove
    let ⟨hPEmp, hIdEqB⟩ := bool_and_true hNoMove
    have hpEq : p.localId = dst := nat_beq_eq hIdEqB
    dsimp [evalOperandToSlot] at hEv
    rw [hPEmp, hpEq] at hEv; dsimp at hEv
    cases hTy : Trusted.MirSemantics.getElem? bodyLocals dst with
    | none => rw [hTy] at hEv; cases hEv
    | some t =>
      rw [hTy] at hEv
      cases hSl : Trusted.MirSemantics.getElem? locals dst with
      | none => rw [hSl] at hEv; cases hEv
      | some slot =>
        rw [hSl] at hEv
        cases slot with
        | dead => cases hEv
        | live opt0 =>
          dsimp at hEv
          cases hSet : setElem? locals dst (liveUninitSlot t) with
          | none => rw [hSet] at hEv; cases hEv
          | some l1 =>
            rw [hSet] at hEv
            injection hEv with q1; injection q1 with _ q2
            injection q2 with _ qL; subst qL
            let ⟨optU, hOptU⟩ := liveUninitSlot_isLive t
            refine ⟨fun i hiNe => setElem?_getElem?_ne hSet hiNe,
                    fun _ _ => ⟨optU, by rw [setElem?_getElem?_same hSet, hOptU]⟩,
                    fun _ _ => ⟨opt0, rfl⟩⟩

private theorem evalPrimitiveOperand_noMoveExcept {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dst : LocalId} {op : Operand} {v : Val}
    (hNoMove : operandNoMoveExcept dst op = true)
    (hEv : evalPrimitiveOperand bodyLocals locals op = .ok (v, locals')) :
    (∀ i, i ≠ dst →
      Trusted.MirSemantics.getElem? locals' i =
        Trusted.MirSemantics.getElem? locals i) ∧
    (∀ sl, Trusted.MirSemantics.getElem? locals dst = some (.live sl) →
      ∃ sl', Trusted.MirSemantics.getElem? locals' dst = some (.live sl')) ∧
    (∀ sl', Trusted.MirSemantics.getElem? locals' dst = some (.live sl') →
      ∃ sl, Trusted.MirSemantics.getElem? locals dst = some (.live sl)) := by
  dsimp [evalPrimitiveOperand] at hEv
  cases hS : evalOperandToSlot bodyLocals locals op with
  | error _ => rw [hS] at hEv; cases hEv
  | ok res =>
    let ⟨ty0, optV, l1⟩ := res
    rw [hS] at hEv; dsimp at hEv
    cases hPr : isPrimitiveReadableTy ty0 with
    | false => rw [hPr] at hEv; cases hEv
    | true =>
      rw [hPr] at hEv; dsimp at hEv
      cases optV with
      | none => cases hEv
      | some _ =>
        injection hEv with q1; injection q1 with _ qL; subst qL
        exact evalOperandToSlot_noMoveExcept hNoMove hS

private theorem evalRvalue_noMoveExcept {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dst : LocalId}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hNoMove : rvalueNoMoveExcept dst rv = true)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    (∀ i, i ≠ dst →
      Trusted.MirSemantics.getElem? locals' i =
        Trusted.MirSemantics.getElem? locals i) ∧
    (∀ sl, Trusted.MirSemantics.getElem? locals dst = some (.live sl) →
      ∃ sl', Trusted.MirSemantics.getElem? locals' dst = some (.live sl')) ∧
    (∀ sl', Trusted.MirSemantics.getElem? locals' dst = some (.live sl') →
      ∃ sl, Trusted.MirSemantics.getElem? locals dst = some (.live sl)) := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalue] at hEv
    cases hS : evalOperandToSlot bodyLocals locals opnd with
    | error _ => rw [hS] at hEv; cases hEv
    | ok res =>
      let ⟨sTy, optV, l1⟩ := res
      rw [hS] at hEv; dsimp at hEv
      cases hEqTy : MirTy.beq sTy dstTy with
      | false => rw [hEqTy] at hEv; cases hEv
      | true =>
        rw [hEqTy] at hEv; dsimp at hEv
        cases optV with
        | none => cases hEv
        | some _ =>
          injection hEv with q1; injection q1 with _ qL; subst qL
          exact evalOperandToSlot_noMoveExcept hNoMove hS
  | unaryOp op opnd =>
    dsimp [evalRvalue] at hEv
    cases hO : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [hO] at hEv; cases hEv
    | ok res =>
      let ⟨ov, l1⟩ := res
      rw [hO] at hEv; dsimp at hEv
      cases hU : evalUnOp op ov with
      | error _ => rw [hU] at hEv; cases hEv
      | ok _ =>
        rw [hU] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
        exact evalPrimitiveOperand_noMoveExcept hNoMove hO
  | binaryOp op lhs rhs =>
    let ⟨hNoL, hNoR⟩ := bool_and_true hNoMove
    dsimp [evalRvalue] at hEv
    cases hL : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [hL] at hEv; cases hEv
    | ok resL =>
      let ⟨lv, l1⟩ := resL
      rw [hL] at hEv; dsimp at hEv
      cases hR : evalPrimitiveOperand bodyLocals l1 rhs with
      | error _ => rw [hR] at hEv; cases hEv
      | ok resR =>
        let ⟨rvv, l2⟩ := resR
        rw [hR] at hEv; dsimp at hEv
        cases hB : evalBinOp op lv rvv with
        | error _ => rw [hB] at hEv; cases hEv
        | ok _ =>
          rw [hB] at hEv; injection hEv with q1; injection q1 with _ qL2; subst qL2
          let ⟨hEq1, hF1, hB1⟩ := evalPrimitiveOperand_noMoveExcept hNoL hL
          let ⟨hEq2, hF2, hB2⟩ := evalPrimitiveOperand_noMoveExcept hNoR hR
          exact ⟨fun i hiNe => (hEq2 i hiNe).trans (hEq1 i hiNe),
                 fun sl h0 => let ⟨s1, hs1⟩ := hF1 sl h0; hF2 s1 hs1,
                 fun sl2 h2 => let ⟨s1, hs1⟩ := hB2 sl2 h2; hB1 s1 hs1⟩
  | discriminant p =>
    dsimp [evalRvalue] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases ty with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hSl] at hEv; cases hEv
          | some slot =>
            rw [hSl] at hEv; dsimp at hEv
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEv; cases hEv
            | true =>
              rw [hAdm] at hEv; dsimp at hEv
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp at hEv
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEv; cases hEv
                    | some _ =>
                      rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                      exact ⟨fun _ _ => rfl, fun sl h => ⟨sl, h⟩, fun sl' h => ⟨sl', h⟩⟩
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                          exact ⟨fun _ _ => rfl, fun sl h => ⟨sl, h⟩, fun sl' h => ⟨sl', h⟩⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
              | scalar _ _ =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none => cases hEv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                          exact ⟨fun _ _ => rfl, fun sl h => ⟨sl, h⟩, fun sl' h => ⟨sl', h⟩⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEv

private inductive DseTail (bodyLocals : List MirTy) (deadAtEntry : BodyDeadCert)
    (numBlocks : Nat) (term : TerminatorKind) :
    List NonZeroAbsSlot → List StatementKind → List StatementKind →
    List NonZeroAbsSlot → Prop where
  | nil (env : List NonZeroAbsSlot) :
      DseTail bodyLocals deadAtEntry numBlocks term env [] [] env
  | kept {env env' exitEnv : List NonZeroAbsSlot} {s : StatementKind}
      {restSrc restTgt : List StatementKind} :
      stepPlainStmtNonZero bodyLocals env s = some env' →
      DseTail bodyLocals deadAtEntry numBlocks term env' restSrc restTgt exitEnv →
      DseTail bodyLocals deadAtEntry numBlocks term env
        (s :: restSrc) (s :: restTgt) exitEnv
  | elim {env env' exitEnv : List NonZeroAbsSlot}
      {dstPlace : Place} {rval : Rvalue} {dstTy : MirTy} {dstSlot : NonZeroAbsSlot}
      {restSrc restTgt : List StatementKind} :
      dstPlace.projection.isEmpty = true →
      dstPlace.localId ≠ 0 →
      isDeadAcrossCfg bodyLocals.length deadAtEntry numBlocks dstPlace.localId
        restTgt term = true →
      Trusted.MirSemantics.getElem? bodyLocals dstPlace.localId = some dstTy →
      Trusted.MirSemantics.getElem? env dstPlace.localId = some dstSlot →
      nonZeroSlotImplies dstSlot .liveUninit = true →
      rvalueCertifiedTotal bodyLocals env dstPlace.localId dstTy rval = true →
      stepPlainStmtNonZero bodyLocals env (.assign dstPlace rval) = some env' →
      DseTail bodyLocals deadAtEntry numBlocks term env' restSrc restTgt exitEnv →
      DseTail bodyLocals deadAtEntry numBlocks term env
        ((.assign dstPlace rval) :: restSrc) (.nop :: restTgt) exitEnv

private theorem rewriteCertifiedDseStmts_sound {bodyLocals : List MirTy}
    {deadAtEntry : BodyDeadCert} {numBlocks : Nat} {term : TerminatorKind} :
    ∀ {env ss ss' exitEnv},
      rewriteCertifiedDseStmts bodyLocals deadAtEntry numBlocks term env ss =
        some (ss', exitEnv) →
      DseTail bodyLocals deadAtEntry numBlocks term env ss ss' exitEnv ∧
      StmtListStoragePreserved ss ss' := by
  intro env ss
  induction ss generalizing env with
  | nil =>
    intro ss' exitEnv h
    injection h with e; injection e with e1 e2; subst e1; subst e2
    exact ⟨.nil env, True.intro⟩
  | cons sSrc restSrc ih =>
    intro ss' exitEnv h
    dsimp [rewriteCertifiedDseStmts] at h
    cases hSt : stepPlainStmtNonZero bodyLocals env sSrc with
    | none => rw [hSt] at h; cases h
    | some env' =>
      rw [hSt] at h; dsimp at h
      cases hRec : rewriteCertifiedDseStmts bodyLocals deadAtEntry numBlocks term
          env' restSrc with
      | none => rw [hRec] at h; cases h
      | some pr =>
        let ⟨restTgt, exE⟩ := pr
        rw [hRec] at h; dsimp only at h
        let ⟨hTail, hStP⟩ := ih hRec
        cases sSrc with
        | nop =>
          dsimp at h; injection h with e; injection e with e1 e2; subst e1; subst e2
          exact ⟨.kept hSt hTail, ⟨Or.inl rfl, hStP⟩⟩
        | storageLive id =>
          dsimp at h; injection h with e; injection e with e1 e2; subst e1; subst e2
          exact ⟨.kept hSt hTail, ⟨Or.inl rfl, hStP⟩⟩
        | storageDead id =>
          dsimp at h; injection h with e; injection e with e1 e2; subst e1; subst e2
          exact ⟨.kept hSt hTail, ⟨Or.inl rfl, hStP⟩⟩
        | unsupported =>
          dsimp at h; injection h with e; injection e with e1 e2; subst e1; subst e2
          exact ⟨.kept hSt hTail, ⟨Or.inl rfl, hStP⟩⟩
        | assign dstPlace rval =>
          dsimp at h
          cases hP4 : (dstPlace.projection.isEmpty &&
              !Nat.beq dstPlace.localId 0 &&
              Nat.blt dstPlace.localId bodyLocals.length &&
              isDeadAcrossCfg bodyLocals.length deadAtEntry numBlocks
                dstPlace.localId restTgt term) with
          | false =>
            rw [ite_prop_false (fun hT => by rw [hP4] at hT; cases hT)] at h
            injection h with e; injection e with e1 e2; subst e1; subst e2
            exact ⟨.kept hSt hTail, ⟨Or.inl rfl, hStP⟩⟩
          | true =>
            let ⟨h123, hDead⟩ := bool_and_true hP4
            let ⟨h12, _⟩ := bool_and_true h123
            let ⟨hPE, hNe0B⟩ := bool_and_true h12
            cases hDTy : Trusted.MirSemantics.getElem? bodyLocals dstPlace.localId with
            | none =>
              rw [ite_prop_false (fun hT => by rw [hP4, hDTy] at hT; dsimp at hT; cases hT)] at h
              injection h with e; injection e with e1 e2; subst e1; subst e2
              exact ⟨.kept hSt hTail, ⟨Or.inl rfl, hStP⟩⟩
            | some dstTy =>
              cases hDSl : Trusted.MirSemantics.getElem? env dstPlace.localId with
              | none =>
                rw [ite_prop_false (fun hT => by rw [hP4, hDTy, hDSl] at hT; dsimp at hT; cases hT)] at h
                injection h with e; injection e with e1 e2; subst e1; subst e2
                exact ⟨.kept hSt hTail, ⟨Or.inl rfl, hStP⟩⟩
              | some dstSlot =>
                cases hM : (nonZeroSlotImplies dstSlot .liveUninit &&
                    rvalueCertifiedTotal bodyLocals env dstPlace.localId dstTy rval) with
                | false =>
                  rw [ite_prop_false (fun hT => by rw [hP4, hDTy, hDSl] at hT; dsimp at hT; rw [hM] at hT; cases hT)] at h
                  injection h with e; injection e with e1 e2; subst e1; subst e2
                  exact ⟨.kept hSt hTail, ⟨Or.inl rfl, hStP⟩⟩
                | true =>
                  rw [ite_prop_true (by rw [hP4, hDTy, hDSl]; dsimp; exact hM)] at h
                  injection h with e; injection e with e1 e2; subst e1; subst e2
                  let ⟨hImp, hTot⟩ := bool_and_true hM
                  exact ⟨.elim hPE (nat_ne_of_beq_false (bool_not_true hNe0B))
                               hDead hDTy hDSl hImp hTot hSt hTail,
                         ⟨Or.inr ⟨True.intro, True.intro⟩, hStP⟩⟩

private theorem dse_certified_elim_succeeds_and_effects {bSrc bTgt : Body}
    {deadAtEntry : BodyDeadCert} {numBlocks : Nat}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    {env : List NonZeroAbsSlot}
    {dstPlace : Place} {rval : Rvalue}
    {restTgt : List StatementKind} {termTgt : TerminatorKind}
    {dstTy : MirTy} {dstSlot : NonZeroAbsSlot}
    (hEnv : NonZeroEnvSound bSrc.locals env fSrc.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks d
          (.nop :: restTgt) termTgt = true)
      fSrc.locals fTgt.locals)
    (hDstEmp : dstPlace.projection.isEmpty = true)
    (hDstNe0 : dstPlace.localId ≠ 0)
    (hDeadDst : isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks
      dstPlace.localId restTgt termTgt = true)
    (hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dstPlace.localId = some dstTy)
    (hDstSlE : Trusted.MirSemantics.getElem? env dstPlace.localId = some dstSlot)
    (hLiveDst : nonZeroSlotImplies dstSlot .liveUninit = true)
    (hTot : rvalueCertifiedTotal bSrc.locals env dstPlace.localId dstTy rval = true) :
    ∃ locsW,
      evalStatement bSrc fSrc cm (.assign dstPlace rval) =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locsW }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm .nop =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals }],
                callerMem := cm } ∧
      DeadMaskedEq bSrc.locals
        (fun d => d ≠ 0 ∧
          isDeadAcrossCfg bTgt.locals.length deadAtEntry numBlocks d restTgt termTgt = true)
        locsW fTgt.locals := by
  have hNoMove : rvalueNoMoveExcept dstPlace.localId rval = true := by
    have hT := hTot
    unfold rvalueCertifiedTotal at hT
    exact (bool_and_true (bool_and_true hT).1).2
  let ⟨val, locsAfterR, hEvR, hChk⟩ := rvalueCertifiedTotal_total hEnv hTot
  have hLtDst : dstPlace.localId < bSrc.locals.length := getElem?_some_lt hDstTy
  let ⟨sl0, hSl0⟩ := getElem?_some_of_lt fSrc.locals dstPlace.localId
    (by rw [hEnv.1.1]; exact hLtDst)
  let ⟨_, opt0, hSl0Eq⟩ :=
    nonZeroSlotImplies_sound hLiveDst
      (hEnv.2.2 dstPlace.localId dstTy dstSlot sl0 hDstTy hDstSlE hSl0)
  subst hSl0Eq
  let ⟨hOtherEq, hFwdLive, _⟩ := evalRvalue_noMoveExcept hNoMove hEvR
  let ⟨optA, hSlAfter⟩ := hFwdLive opt0 hSl0
  have hWtAfterR := evalRvalue_preserves_wt hEnv.1 hEvR
  let ⟨locsW, hSetW⟩ := setElem?_some_of_lt locsAfterR dstPlace.localId (.live (some val))
    (by rw [hWtAfterR.1]; exact hLtDst)
  have hWtW := localsWellTyped_set hWtAfterR hDstTy hSetW hChk
  let ⟨sl2Dst, hG2Dst⟩ := getElem?_some_of_lt fTgt.locals dstPlace.localId
    (by rw [hMask.2.1.1]; exact hLtDst)
  have hSameLiveDst := (hMask.2.2 dstPlace.localId).1 _ _ hSl0 hG2Dst
  cases sl2Dst with
  | dead => cases hSameLiveDst
  | live opt2Dst =>
    refine ⟨locsW, ?_, rfl, ⟨hWtW, hMask.2.1, fun i => ?_⟩⟩
    · dsimp [evalStatement]
      rw [hDstEmp]; dsimp; rw [hDstTy]; dsimp; rw [hEvR]; dsimp
      unfold writePlace; rw [hChk]; dsimp; rw [hSlAfter]; dsimp; rw [hSetW]
    · cases hEqI : Nat.beq i dstPlace.localId with
      | true =>
        have hi := nat_beq_eq hEqI; subst hi
        rw [setElem?_getElem?_same hSetW, hG2Dst]
        refine ⟨?_, fun hNotD => False.elim (hNotD ⟨hDstNe0, hDeadDst⟩)⟩
        intro a b ea eb; injection ea with qa; injection eb with qb
        subst qa; subst qb; exact True.intro
      | false =>
        have hiNe := nat_ne_of_beq_false hEqI
        rw [setElem?_getElem?_ne hSetW hiNe, hOtherEq i hiNe]
        exact (hMask.2.2 i)

private noncomputable def refineSwitchNonZeroEnv (bodyLocals : List MirTy)
    (afterDiscrEnv : List NonZeroAbsSlot) (discr : Operand)
    (branches : List (BitVec 128 × BasicBlockId)) : List NonZeroAbsSlot :=
  match discr with
  | .copy p =>
    if !p.projection.isEmpty then afterDiscrEnv
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? afterDiscrEnv p.localId with
      | some (.int w _), some curSlot =>
        if nonZeroSlotImplies curSlot .liveInit &&
            hasValidZeroGuard w branches then
          match setElem? afterDiscrEnv p.localId .liveNonZero with
          | some refined => refined
          | none => afterDiscrEnv
        else
          afterDiscrEnv
      | _, _ => afterDiscrEnv
  | _ => afterDiscrEnv

private theorem refineSwitchNonZeroEnv_bool {bodyLocals : List MirTy}
    {curEnv : List NonZeroAbsSlot} {locals locsAfter : List LocalSlot}
    {discr : Operand} {bv : Bool}
    {branches : List (BitVec 128 × BasicBlockId)}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hEvD : evalPrimitiveOperand bodyLocals locals discr = .ok (.bool bv, locsAfter)) :
    refineSwitchNonZeroEnv bodyLocals
      (deinitMoveOperandNonZero bodyLocals curEnv discr) discr branches =
    deinitMoveOperandNonZero bodyLocals curEnv discr := by
  cases discr with
  | constant _ | move _ => rfl
  | copy p =>
    dsimp [refineSwitchNonZeroEnv]
    dsimp [evalPrimitiveOperand, evalOperandToSlot] at hEvD
    cases hPE : p.projection.isEmpty with
    | false => rw [hPE] at hEvD; cases hEvD
    | true =>
      rw [hPE] at hEvD; dsimp at hEvD
      dsimp
      cases hPTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rfl
      | some pTy =>
        rw [hPTy] at hEvD
        cases hPSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hPSl] at hEvD; cases hEvD
        | some pSl =>
          rw [hPSl] at hEvD
          cases pSl with
          | dead => cases hEvD
          | live pOpt =>
            dsimp at hEvD
            cases hPrP : isPrimitiveReadableTy pTy with
            | false => rw [hPrP] at hEvD; cases hEvD
            | true =>
              rw [hPrP] at hEvD; dsimp at hEvD
              cases pOpt with
              | none => cases hEvD
              | some pv =>
                injection hEvD with hEqP
                injection hEqP with hPvEq _; subst hPvEq
                have hChkB : checkVal (.bool bv) pTy = true :=
                  hWt.2 p.localId pTy (.live (some (.bool bv))) hPTy hPSl
                have hPTyBool : pTy = .bool := by
                  cases pTy <;> first | rfl | cases hChkB
                rw [hPTyBool]

private theorem refineSwitchNonZeroEnv_scalar {bodyLocals : List MirTy}
    {curEnv : List NonZeroAbsSlot} {locals locsAfter : List LocalSlot}
    {discr : Operand} {sv : ScalarVal}
    {branches : List (BitVec 128 × BasicBlockId)}
    (hCurSound : NonZeroEnvSound bodyLocals curEnv locals)
    (hAfterSound : NonZeroEnvSound bodyLocals
      (deinitMoveOperandNonZero bodyLocals curEnv discr) locsAfter)
    (hEvD : evalPrimitiveOperand bodyLocals locals discr = .ok (.scalar sv, locsAfter))
    (hGuardFn : hasValidZeroGuard sv.width branches = true →
      truncateBits sv.width sv.bits ≠ BitVec.ofNat 128 0) :
    NonZeroEnvSound bodyLocals
      (refineSwitchNonZeroEnv bodyLocals
        (deinitMoveOperandNonZero bodyLocals curEnv discr) discr branches)
      locsAfter := by
  cases discr with
  | constant _ | move _ => exact hAfterSound
  | copy p =>
    dsimp [refineSwitchNonZeroEnv]
    dsimp [evalPrimitiveOperand, evalOperandToSlot] at hEvD
    cases hPE : p.projection.isEmpty with
    | false => rw [hPE] at hEvD; cases hEvD
    | true =>
      rw [hPE] at hEvD; dsimp at hEvD
      dsimp
      cases hPTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact hAfterSound
      | some pTy =>
        rw [hPTy] at hEvD
        cases hPSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hPSl] at hEvD; cases hEvD
        | some pSl =>
          rw [hPSl] at hEvD
          cases pSl with
          | dead => cases hEvD
          | live pOpt =>
            dsimp at hEvD
            cases hPrP : isPrimitiveReadableTy pTy with
            | false => rw [hPrP] at hEvD; cases hEvD
            | true =>
              rw [hPrP] at hEvD; dsimp at hEvD
              cases pOpt with
              | none => cases hEvD
              | some pv =>
                injection hEvD with hEqP
                injection hEqP with hPvEq hLocsEq
                subst hPvEq; subst hLocsEq
                cases pTy with
                | bool | unit | never | enum _ | tuple _
                | ref _ _ | rawPtr _ _ | unsupported =>
                  exact hAfterSound
                | int w s =>
                  cases hCurP : Trusted.MirSemantics.getElem?
                      (deinitMoveOperandNonZero bodyLocals curEnv (.copy p))
                      p.localId with
                  | none => exact hAfterSound
                  | some curSlot =>
                    dsimp
                    cases hCond : (nonZeroSlotImplies curSlot .liveInit &&
                        hasValidZeroGuard w branches) with
                    | false => dsimp; exact hAfterSound
                    | true =>
                      dsimp
                      let ⟨_, hHasGuard⟩ := bool_and_true hCond
                      have hChkSv : checkVal (.scalar sv) (.int w s) = true :=
                        hCurSound.1.2 p.localId (.int w s)
                          (.live (some (.scalar sv))) hPTy hPSl
                      let ⟨b, hsvEq, hWfB⟩ := checkVal_int_iff.mp hChkSv
                      injection hsvEq with hSvStruct; subst hSvStruct
                      have hTrNe0 : truncateBits w b ≠ BitVec.ofNat 128 0 :=
                        hGuardFn hHasGuard
                      have hBitsNe0 : b ≠ BitVec.ofNat 128 0 := by
                        rw [← hWfB]; exact hTrNe0
                      have hDecNe0 :=
                        decodeScalar_ne_zero_of_bits_ne_zero (s := s) hWfB hBitsNe0
                      cases hSetRef : setElem?
                          (deinitMoveOperandNonZero bodyLocals curEnv (.copy p))
                          p.localId .liveNonZero with
                      | none => exact hAfterSound
                      | some refined =>
                        exact nonZeroEnvSound_refine_existing hAfterSound hPTy hPSl
                          hSetRef ⟨hChkSv, ⟨w, s, b, rfl, rfl, hWfB, hDecNe0⟩⟩

private theorem checkNonZeroEdge_sound {bodyLocals : List MirTy}
    {numBlocks : Nat} {nzCert : List (Option (List NonZeroAbsSlot))}
    {edgeEnv : List NonZeroAbsSlot} {locs' : List LocalSlot} {tgt : BasicBlockId}
    (hEdge : checkNonZeroEdge numBlocks nzCert edgeEnv tgt = true)
    (hSound : NonZeroEnvSound bodyLocals edgeEnv locs')
    (hLt : tgt < numBlocks) :
    ∃ entryEnv,
      Trusted.MirSemantics.getElem? nzCert tgt = some (some entryEnv) ∧
      NonZeroEnvSound bodyLocals entryEnv locs' := by
  unfold checkNonZeroEdge at hEdge
  rw [nat_lt_blt hLt] at hEdge; dsimp at hEdge
  cases hCertTgt : Trusted.MirSemantics.getElem? nzCert tgt with
  | none => rw [hCertTgt] at hEdge; cases hEdge
  | some optEnv =>
    rw [hCertTgt] at hEdge
    cases optEnv with
    | none => cases hEdge
    | some entryEnv =>
      exact ⟨entryEnv, rfl, nonZeroEnvImplies_sound hEdge hSound⟩

private theorem checkNonZeroTerminatorEdges_step_sound {bSrc : Body} {bbSrc : BasicBlock}
    {nzCert : List (Option (List NonZeroAbsSlot))}
    {exitEnv : List NonZeroAbsSlot} {fSrc : FrameState}
    {cm : CallerMemory} {s' : State}
    (hExitSound : NonZeroEnvSound bSrc.locals exitEnv fSrc.locals)
    (hEdges : checkNonZeroTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      nzCert exitEnv bbSrc.terminator = true)
    (hEvT : evalTerminator bSrc bbSrc fSrc cm = .step s') :
    ∃ tgt locs',
      s' = { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
             callerMem := cm } ∧
      (tgt < bSrc.basicBlocks.length →
        ∃ nextEntry,
          Trusted.MirSemantics.getElem? nzCert tgt = some (some nextEntry) ∧
          NonZeroEnvSound bSrc.locals nextEntry locs') := by
  unfold evalTerminator at hEvT
  cases hTerm : bbSrc.terminator with
  | return_ =>
    rw [hTerm] at hEvT; dsimp at hEvT
    cases hCl : bbSrc.cleanup with
    | true => rw [hCl] at hEvT; cases hEvT
    | false =>
      rw [hCl] at hEvT; dsimp at hEvT
      cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
      | none => rw [h0] at hEvT; cases hEvT
      | some sl => rw [h0] at hEvT; cases sl with | dead => cases hEvT | live o => cases o <;> cases hEvT
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    rw [hTerm] at hEvT; cases hEvT
  | goto target =>
    rw [hTerm] at hEvT hEdges; dsimp at hEvT hEdges
    injection hEvT with hSEq; subst hSEq
    exact ⟨target, fSrc.locals, rfl, fun hLt => checkNonZeroEdge_sound hEdges hExitSound hLt⟩
  | switchInt discr targets =>
    rw [hTerm] at hEvT hEdges; dsimp only [checkNonZeroTerminatorEdges] at hEdges
    dsimp at hEvT
    let ⟨hOtherEdge, hBrEdges⟩ := bool_and_true hEdges
    cases hEvD : evalPrimitiveOperand bSrc.locals fSrc.locals discr with
    | error _ => rw [hEvD] at hEvT; cases hEvT
    | ok resD =>
      let ⟨dv, locsAfter⟩ := resD
      rw [hEvD] at hEvT; dsimp at hEvT
      have hAfterSound := deinitMovePrimNonZero_sound hExitSound hEvD
      cases dv with
      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEvT
      | bool bv =>
        dsimp at hEvT
        cases hSwB : evalBoolSwitchBranches bv targets.otherwise targets.branches with
        | error _ => rw [hSwB] at hEvT; cases hEvT
        | ok tgt =>
          rw [hSwB] at hEvT; injection hEvT with hSEq; subst hSEq
          refine ⟨tgt, locsAfter, rfl, fun hLt => ?_⟩
          cases evalBoolSwitchBranches_cases hSwB with
          | inl hInBr =>
            let ⟨cb, hMem⟩ := hInBr
            have hBr := list_all_mem_true hBrEdges hMem
            exact checkNonZeroEdge_sound hBr hAfterSound hLt
          | inr hOth =>
            subst hOth
            have hRefEq := refineSwitchNonZeroEnv_bool (curEnv := exitEnv)
              (branches := targets.branches) hExitSound.1 hEvD
            change checkNonZeroEdge bSrc.basicBlocks.length nzCert
              (refineSwitchNonZeroEnv bSrc.locals
                (deinitMoveOperandNonZero bSrc.locals exitEnv discr) discr targets.branches)
              targets.otherwise = true at hOtherEdge
            rw [hRefEq] at hOtherEdge
            exact checkNonZeroEdge_sound hOtherEdge hAfterSound hLt
      | scalar sv =>
        dsimp at hEvT
        cases hSwS : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error _ => rw [hSwS] at hEvT; cases hEvT
        | ok tgt =>
          rw [hSwS] at hEvT; injection hEvT with hSEq; subst hSEq
          refine ⟨tgt, locsAfter, rfl, fun hLt => ?_⟩
          cases evalSwitchBranches_cases hSwS with
          | inl hInBr =>
            let ⟨cb, hMem⟩ := hInBr
            have hBr := list_all_mem_true hBrEdges hMem
            exact checkNonZeroEdge_sound hBr hAfterSound hLt
          | inr hOth =>
            let ⟨hTgtEq, hGuardFn⟩ := hOth
            subst hTgtEq
            have hRefSound := refineSwitchNonZeroEnv_scalar
              hExitSound hAfterSound hEvD hGuardFn
            exact checkNonZeroEdge_sound hOtherEdge hRefSound hLt

private theorem applyCertifiedDseBlocks_props {b : Body} {cert : BodyDseCert} :
    ∀ {base bbs bbs'},
      applyCertifiedDseBlocks b cert base bbs = some bbs' →
      bbs.length = bbs'.length ∧
      (∀ i bb₁ bb₂,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? bbs' i = some bb₂ →
        StmtListStoragePreserved bb₁.statements bb₂.statements ∧
        bb₁.cleanup = bb₂.cleanup ∧
        bb₁.terminator = bb₂.terminator) ∧
      (∀ i bb₁ entryEnv,
        Trusted.MirSemantics.getElem? bbs i = some bb₁ →
        Trusted.MirSemantics.getElem? cert.nzCert (base + i) = some (some entryEnv) →
        ∃ bb₂ exitEnv,
          Trusted.MirSemantics.getElem? bbs' i = some bb₂ ∧
          entryEnv.length = b.locals.length ∧
          DseTail b.locals cert.deadAtEntry b.basicBlocks.length
            bb₂.terminator entryEnv bb₁.statements bb₂.statements exitEnv ∧
          checkNonZeroTerminatorEdges b.locals b.basicBlocks.length cert.nzCert
            exitEnv bb₁.terminator = true) := by
  intro base bbs
  induction bbs generalizing base with
  | nil =>
    intro bbs' h; injection h with e; subst e
    exact ⟨rfl, (fun _ _ _ h1 => by cases h1), (fun _ _ _ h1 => by cases h1)⟩
  | cons bb rest ih =>
    intro bbs' h
    dsimp [applyCertifiedDseBlocks] at h
    cases hC : Trusted.MirSemantics.getElem? cert.nzCert base with
    | none => rw [hC] at h; cases h
    | some optE =>
      rw [hC] at h
      cases optE with
      | none =>
        dsimp at h
        cases hRec : applyCertifiedDseBlocks b cert (base + 1) rest with
        | none => rw [hRec] at h; cases h
        | some rest' =>
          rw [hRec] at h; injection h with e; subst e
          let ⟨hLen, hStCl, hAct⟩ := ih hRec
          refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
          · intro i bb₁ bb₂ h1 h2
            cases i with
            | zero =>
              injection h1 with e1; injection h2 with e2; subst e1; subst e2
              exact ⟨stmtListStoragePreserved_refl _, rfl, rfl⟩
            | succ k => exact hStCl k bb₁ bb₂ h1 h2
          · intro i bb₁ eEnv h1 hCE
            cases i with
            | zero => rw [Nat.add_zero, hC] at hCE; cases hCE
            | succ k =>
              have hAdd : (base + 1) + k = base + (k + 1) := by
                rw [Nat.add_assoc, Nat.add_comm 1 k]
              rw [← hAdd] at hCE
              exact hAct k bb₁ eEnv h1 hCE
      | some entryEnv =>
        dsimp at h
        cases hELen : Nat.beq entryEnv.length b.locals.length with
        | false => rw [hELen] at h; cases h
        | true =>
          rw [hELen] at h; dsimp at h
          cases hRew : rewriteCertifiedDseStmts b.locals cert.deadAtEntry
              b.basicBlocks.length bb.terminator entryEnv bb.statements with
          | none => rw [hRew] at h; cases h
          | some pr =>
            let ⟨stmts', exitEnv⟩ := pr
            rw [hRew] at h; dsimp at h
            cases hEdg : checkNonZeroTerminatorEdges b.locals b.basicBlocks.length
                cert.nzCert exitEnv bb.terminator with
            | false => rw [hEdg] at h; cases h
            | true =>
              rw [hEdg] at h; dsimp at h
              cases hRec : applyCertifiedDseBlocks b cert (base + 1) rest with
              | none => rw [hRec] at h; cases h
              | some rest' =>
                rw [hRec] at h; injection h with e; subst e
                let ⟨hTail, hStP⟩ := rewriteCertifiedDseStmts_sound hRew
                let ⟨hLen, hStCl, hAct⟩ := ih hRec
                refine ⟨by dsimp [List.length]; rw [hLen], ?_, ?_⟩
                · intro i bb₁ bb₂ h1 h2
                  cases i with
                  | zero =>
                    injection h1 with e1; injection h2 with e2; subst e1; subst e2
                    exact ⟨hStP, rfl, rfl⟩
                  | succ k => exact hStCl k bb₁ bb₂ h1 h2
                · intro i bb₁ eEnv h1 hCE
                  cases i with
                  | zero =>
                    injection h1 with e1; subst e1
                    rw [Nat.add_zero, hC] at hCE; injection hCE with eE
                    injection eE with eE'; subst eE'
                    exact ⟨_, exitEnv, rfl, nat_beq_eq hELen, hTail, hEdg⟩
                  | succ k =>
                    have hAdd : (base + 1) + k = base + (k + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 k]
                    rw [← hAdd] at hCE
                    exact hAct k bb₁ eEnv h1 hCE

private theorem applyCertifiedDseBody_props {cert : BodyDseCert} {bSrc bTgt : Body}
    (hApply : applyCertifiedDseBody cert bSrc = some bTgt) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) ∧
    (bSrc.basicBlocks.isEmpty = false →
      ∃ env₀, Trusted.MirSemantics.getElem? cert.nzCert 0 = some (some env₀) ∧
        nonZeroEnvImplies (initNonZeroEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
    checkBodyDeadCert bTgt cert.deadAtEntry = true ∧
    applyCertifiedDseBlocks bSrc cert 0 bSrc.basicBlocks = some bTgt.basicBlocks ∧
    bSrc.locals = bTgt.locals := by
  unfold applyCertifiedDseBody at hApply
  cases hCLen : Nat.beq cert.nzCert.length bSrc.basicBlocks.length with
  | false => rw [hCLen] at hApply; cases hApply
  | true =>
    rw [hCLen] at hApply; dsimp at hApply
    have hProceed :
        ((bSrc.basicBlocks.isEmpty = false →
          ∃ env₀, Trusted.MirSemantics.getElem? cert.nzCert 0 = some (some env₀) ∧
            nonZeroEnvImplies (initNonZeroEnvLoop bSrc 0 bSrc.locals) env₀ = true) ∧
         ∃ bbs', applyCertifiedDseBlocks bSrc cert 0 bSrc.basicBlocks = some bbs' ∧
           checkBodyDeadCert { bSrc with basicBlocks := bbs' } cert.deadAtEntry = true ∧
           bTgt = { bSrc with basicBlocks := bbs' }) := by
      cases hEmp : bSrc.basicBlocks.isEmpty with
      | true =>
        rw [hEmp] at hApply; dsimp at hApply
        cases hBlk : applyCertifiedDseBlocks bSrc cert 0 bSrc.basicBlocks with
        | none => rw [hBlk] at hApply; cases hApply
        | some bbs' =>
          rw [hBlk] at hApply; dsimp at hApply
          cases hDC : checkBodyDeadCert { bSrc with basicBlocks := bbs' } cert.deadAtEntry with
          | false => rw [hDC] at hApply; cases hApply
          | true =>
            rw [hDC] at hApply; injection hApply with eB
            exact ⟨(fun hF => by cases hF), bbs', rfl, hDC, eB.symm⟩
      | false =>
        rw [hEmp] at hApply
        cases hC0 : Trusted.MirSemantics.getElem? cert.nzCert 0 with
        | none => rw [hC0] at hApply; cases hApply
        | some opt0 =>
          rw [hC0] at hApply
          cases opt0 with
          | none => cases hApply
          | some env₀ =>
            cases hImp : nonZeroEnvImplies (initNonZeroEnvLoop bSrc 0 bSrc.locals) env₀ with
            | false =>
              have hCT : (!false && !(match (some (some env₀) : Option (Option (List NonZeroAbsSlot))) with
                  | some (some e) => nonZeroEnvImplies (initNonZeroEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = true := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_true hCT] at hApply; cases hApply
            | true =>
              have hCF : (!false && !(match (some (some env₀) : Option (Option (List NonZeroAbsSlot))) with
                  | some (some e) => nonZeroEnvImplies (initNonZeroEnvLoop bSrc 0 bSrc.locals) e
                  | _ => false)) = false := by
                dsimp; rw [hImp]; rfl
              rw [if_bool_false hCF] at hApply
              cases hBlk : applyCertifiedDseBlocks bSrc cert 0 bSrc.basicBlocks with
              | none => rw [hBlk] at hApply; cases hApply
              | some bbs' =>
                rw [hBlk] at hApply; dsimp at hApply
                cases hDC : checkBodyDeadCert { bSrc with basicBlocks := bbs' } cert.deadAtEntry with
                | false => rw [hDC] at hApply; cases hApply
                | true =>
                  rw [hDC] at hApply; injection hApply with eB
                  exact ⟨fun _ => ⟨env₀, rfl, hImp⟩, bbs', rfl, hDC, eB.symm⟩
    let ⟨hCert0Fn, bbs', hBlk, hDC, eB⟩ := hProceed
    subst eB
    let ⟨hBBLen, hStCl, _⟩ := applyCertifiedDseBlocks_props hBlk
    have hBBEmpty := list_isEmpty_eq_of_length hBBLen
    have hHdr : bodyHeaderEq bSrc { bSrc with basicBlocks := bbs' } = true :=
      bodyHeaderEq_refl bSrc
    have hMarker : ∀ idx,
        hasStorageAnnotation bSrc idx =
          hasStorageAnnotation { bSrc with basicBlocks := bbs' } idx := by
      intro idx
      unfold hasStorageAnnotation; dsimp only
      exact list_any_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 =>
        (stmtListStoragePreserved_props (hStCl i bb₁ bb₂ h1 h2).1).2.1 idx)
    have hBounds :
        storageAnnotationsInBounds bSrc =
          storageAnnotationsInBounds { bSrc with basicBlocks := bbs' } := by
      unfold storageAnnotationsInBounds; dsimp only
      exact list_all_eq_of_getElem? hBBLen (fun i bb₁ bb₂ h1 h2 =>
        (stmtListStoragePreserved_props (hStCl i bb₁ bb₂ h1 h2).1).2.2
          (fun stmt => match stmt with
            | .storageLive id | .storageDead id => Nat.blt id bSrc.locals.length
            | _ => true)
          (fun _ _ => rfl) rfl)
    exact ⟨hHdr, hBBLen, hBBEmpty, hBounds,
      fun args => initLocalsLoop_eq_of_storage_eq args rfl rfl (fun idx _ _ => hMarker idx),
      hCert0Fn, hDC, hBlk, rfl⟩

private noncomputable def DseCertBisimRel (cert : ProgramDseCert)
    (pSrc pTgt : Program) (s t : State) : Prop :=
  ∃ fSrc fTgt bCert bSrc bTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    Trusted.MirSemantics.getElem? cert fSrc.defId = some bCert ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
    applyCertifiedDseBody bCert bSrc = some bTgt ∧
    (fSrc.blockIdx < bSrc.basicBlocks.length →
      ∃ bbSrc bbTgt curEnv exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt ∧
        DseTail bSrc.locals bCert.deadAtEntry bSrc.basicBlocks.length
          bbTgt.terminator curEnv
          (bbSrc.statements.drop fSrc.stmtIdx)
          (bbTgt.statements.drop fSrc.stmtIdx) exitEnv ∧
        checkNonZeroTerminatorEdges bSrc.locals bSrc.basicBlocks.length
          bCert.nzCert exitEnv bbSrc.terminator = true ∧
        NonZeroEnvSound bSrc.locals curEnv fSrc.locals ∧
        DeadMaskedEq bSrc.locals
          (fun d => d ≠ 0 ∧
            isDeadAcrossCfg bTgt.locals.length bCert.deadAtEntry bTgt.basicBlocks.length d
              (bbTgt.statements.drop fSrc.stmtIdx) bbTgt.terminator = true)
          fSrc.locals fTgt.locals)

private theorem dse_init_eq {cert : ProgramDseCert} {pSrc pTgt : Program}
    (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applyCertifiedDseBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    initState pSrc q = initState pTgt q := by
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  have hBodyLen : pSrc.bodies.length = pTgt.bodies.length :=
    (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
  apply initState_eq_of_matching_entry q hHdr
  · constructor
    · intro hN
      have hGe : pTgt.bodies.length ≤ pTgt.entryDefId := by
        rw [← hBodyLen, ← hEnt]; exact getElem?_none_ge hN
      exact getElem?_none_of_ge hGe
    · intro hN
      have hGe : pSrc.bodies.length ≤ pSrc.entryDefId := by
        rw [hBodyLen, hEnt]; exact getElem?_none_ge hN
      exact getElem?_none_of_ge hGe
  · intro bSrc hBS
    let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    rw [hEnt] at hBT
    let ⟨hBHdr, _, hEmp, hBnd, hInitL, _, _, _, _⟩ := applyCertifiedDseBody_props hAp
    exact ⟨bTgt, hBT, hBHdr, hEmp, hBnd, hInitL q.args⟩

private theorem dse_query_iff {cert : ProgramDseCert} {pSrc pTgt : Program}
    (q : Query)
    (hLenC : cert.length = pSrc.bodies.length)
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hMap : mapOption (fun pr => applyCertifiedDseBody pr.1 pr.2)
      (List.zip cert pSrc.bodies) = some pTgt.bodies) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  apply bisim_lockstep_query_iff (R := DseCertBisimRel cert pSrc pTgt)
    (dse_init_eq q hLenC hHdr hMap)
  · intro s₀ hOk
    let ⟨_, _, bSrc, hBS, hNotEmp, _, _, _, hArgs, hs0⟩ := initState_ok_elim hOk
    subst hs0
    let ⟨bCert, bTgt, hBC, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
    let ⟨_, _, _, _, _, hCert0Fn, _, hBlk, _⟩ := applyCertifiedDseBody_props hAp
    let ⟨_, _, hAct⟩ := applyCertifiedDseBlocks_props hBlk
    let ⟨env₀, hC0, hImp0⟩ := hCert0Fn hNotEmp
    have hEnv0 := nonZeroEnvImplies_sound hImp0 (initNonZeroEnvLoop_sound hArgs)
    refine ⟨_, _, bCert, bSrc, bTgt, rfl, rfl, rfl, rfl, rfl, rfl,
            hBC, hBS, hBT, hAp, ?_⟩
    intro h0Lt
    let ⟨bbSrc0, hBBS0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
    let ⟨bbTgt0, exitE0, hBBT0, _, hTail0, hEdg0⟩ := hAct 0 bbSrc0 env₀ hBBS0 hC0
    exact ⟨bbSrc0, bbTgt0, env₀, exitE0, hBBS0, hBBT0, hTail0, hEdg0,
           hEnv0, deadMaskedEq_refl hEnv0.1⟩
  · intro s t hR
    let ⟨fSrc, fTgt, bCert, bSrc, bTgt, hFS, hFT, hCM, hDefEq, hBlkEq, hIdxEq,
         hBC, hBS, hBT, hAp, hBlkInv⟩ := hR
    let ⟨_, hBBLen, _, _, _, _, hDC, hBlk, hLocEq⟩ := applyCertifiedDseBody_props hAp
    let ⟨_, hStCl, hAct⟩ := applyCertifiedDseBlocks_props hBlk
    cases s with
    | mk fsS cmS =>
      cases t with
      | mk fsT cmT =>
        dsimp at hFS hFT hCM; subst hFS; subst hFT; subst hCM
        have hBT2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
          rw [← hDefEq]; exact hBT
        cases Nat.lt_or_ge fSrc.blockIdx bSrc.basicBlocks.length with
        | inr hGe =>
          have hGeT : bTgt.basicBlocks.length ≤ fTgt.blockIdx := by
            rw [← hBlkEq, ← hBBLen]; exact hGe
          unfold StepOutcomeBisim evalStep; dsimp
          rw [hBS, hBT2]; dsimp
          rw [getElem?_none_of_ge hGe, getElem?_none_of_ge hGeT]
          exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
        | inl hLt =>
          let ⟨bbSrc, bbTgt, curEnv, exitEnv, hBBS, hBBT, hTail,
               hEdges, hCurSound, hMask⟩ := hBlkInv hLt
          have hBBT2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx =
              some bbTgt := by
            rw [← hBlkEq]; exact hBBT
          let ⟨hStP, hCleanEq, hTermEq⟩ := hStCl fSrc.blockIdx bbSrc bbTgt hBBS hBBT
          have hStmtsLenEq := (stmtListStoragePreserved_props hStP).1
          cases hDropS : bbSrc.statements.drop fSrc.stmtIdx with
          | nil =>
            rw [hDropS] at hTail
            cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
            | cons _ _ => rw [hDropT] at hTail; cases hTail
            | nil =>
              rw [hDropT] at hTail hMask
              cases hTail with
              | nil =>
                cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
                | some x =>
                  rw [drop_eq_cons_of_getElem? hStSrc] at hDropS; cases hDropS
                | none =>
                  have hGeS := getElem?_none_ge hStSrc
                  have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx =
                      none :=
                    getElem?_none_of_ge (by rw [← hIdxEq, ← hStmtsLenEq]; exact hGeS)
                  unfold StepOutcomeBisim evalStep; dsimp
                  rw [hBS, hBT2]; dsimp
                  rw [hBBS, hBBT2]; dsimp
                  rw [hStSrc, hStTgt2]; dsimp
                  rw [← hIdxEq, ← hStmtsLenEq]
                  cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
                  | false => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
                  | true =>
                    dsimp
                    have hSwUntouched : ∀ discr targets,
                        bbTgt.terminator = .switchInt discr targets →
                        ∀ d, (d ≠ 0 ∧ isDeadAcrossCfg bTgt.locals.length bCert.deadAtEntry
                          bTgt.basicBlocks.length d [] bbTgt.terminator = true) →
                        operandTouchesLocal d discr = false := by
                      intro discr targets hTm d ⟨_, hDnil⟩
                      rw [hTm] at hDnil
                      exact isDeadAcrossCfg_nil_switch_untouched hDnil
                    cases evalTerminator_deadMasked_bisim (cm := cmS)
                        hLocEq hCleanEq hTermEq hMask (fun _ h => h.1) hSwUntouched with
                    | inr hDoneOrFault => exact Or.inr hDoneOrFault
                    | inl hStepTerm =>
                      let ⟨tgt, l1', l2', hEvTS, hEvTT, hMaskAfterTerm⟩ := hStepTerm
                      let ⟨tgt', l1'', hEqS', hCertNext⟩ :=
                        checkNonZeroTerminatorEdges_step_sound hCurSound hEdges hEvTS
                      injection hEqS' with eFs _; injection eFs with eF _
                      have hTgtEq : tgt = tgt' := congrArg FrameState.blockIdx eF
                      have hL1Eq : l1' = l1'' := congrArg FrameState.locals eF
                      subst hTgtEq; subst hL1Eq
                      rw [hEvTS, hEvTT]
                      refine Or.inl ⟨{ frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1' }],
                                       callerMem := cmS },
                        { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2' }],
                          callerMem := cmS }, rfl, rfl,
                        { fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1' },
                        { fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2' },
                        bCert, bSrc, bTgt,
                        rfl, rfl, rfl, hDefEq, rfl, rfl,
                        hBC, hBS, hBT, hAp, ?_⟩
                      intro hTgtLt
                      let ⟨nextEntry, hCNext, hNextSound⟩ := hCertNext hTgtLt
                      let ⟨bbNextS, hBBNS⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt hTgtLt
                      have hCNext0 : Trusted.MirSemantics.getElem? bCert.nzCert (0 + tgt) =
                          some (some nextEntry) := by
                        rw [Nat.zero_add]; exact hCNext
                      let ⟨bbNextT, exitEN, hBBNT, _, hTailN, hEdgN⟩ :=
                        hAct tgt bbNextS nextEntry hBBNS hCNext0
                      have hDeadLoop : checkDeadAtEntryLoop bTgt bCert.deadAtEntry 0
                          bCert.deadAtEntry = true := (bool_and_true hDC).2
                      have hMaskEntry : DeadMaskedEq bSrc.locals
                          (fun d => d ≠ 0 ∧ isDeadAcrossCfg bTgt.locals.length bCert.deadAtEntry
                            bTgt.basicBlocks.length d
                            bbNextT.statements bbNextT.terminator = true)
                          l1' l2' := by
                        apply deadMaskedEq_mono ?_ hMaskAfterTerm
                        intro d ⟨hd0, hDnil⟩
                        exact ⟨hd0, isDeadAcrossCfg_nil_step_target hDeadLoop
                          hEvTT hBBNT hDnil⟩
                      exact ⟨bbNextS, bbNextT, nextEntry, exitEN, hBBNS, hBBNT,
                        hTailN, hEdgN, hNextSound, hMaskEntry⟩
          | cons s₀ restSrc0 =>
            rw [hDropS] at hTail
            cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
            | nil => rw [hDropT] at hTail; cases hTail
            | cons t₀ restTgt0 =>
              rw [hDropT] at hTail hMask
              cases hTail with
              | kept hStepPlain hTailRest =>
                let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
                let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
                have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx =
                    some s₀ := by
                  rw [← hIdxEq]; exact hStTgt0
                unfold StepOutcomeBisim evalStep; dsimp
                rw [hBS, hBT2]; dsimp
                rw [hBBS, hBBT2]; dsimp
                rw [hStSrc, hStTgt2]; dsimp
                cases isDeadAcrossCfg_kept_step (cm := cmS) hLocEq hMask with
                | inl hFault =>
                  let ⟨fk, hF1, hF2⟩ := hFault
                  rw [hF1, hF2]
                  exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
                | inr hStepBoth =>
                  let ⟨l1', l2', hEvS, hEvT, hMaskNext⟩ := hStepBoth
                  let ⟨l1'', hEqS'', hNextSound⟩ :=
                    stepPlainStmtNonZero_sound hCurSound hStepPlain hEvS
                  injection hEqS'' with eFs _; injection eFs with eF _
                  have hL1Eq : l1' = l1'' := congrArg FrameState.locals eF
                  subst hL1Eq
                  rw [hEvS, hEvT]
                  refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                                   callerMem := cmS },
                    { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                      callerMem := cmS }, rfl, rfl,
                    { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                    { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' },
                    bCert, bSrc, bTgt,
                    rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq],
                    hBC, hBS, hBT, hAp, fun _ => ?_⟩
                  refine ⟨bbSrc, bbTgt, _, exitEnv, hBBS, hBBT, ?_, hEdges, hNextSound, ?_⟩
                  · dsimp; rw [hDropSNext, hDropTNext]; exact hTailRest
                  · dsimp; rw [hDropTNext]; exact hMaskNext
              | elim hDstEmp hDstNe0 hDeadDst hDstTy hDstSlE hLiveDst hTotRv
                     hStepPlain hTailRest =>
                let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
                let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
                have hStTgt2 := hStTgt0
                rw [hIdxEq] at hStTgt2
                have hDeadDstTgt := hDeadDst
                rw [hLocEq, hBBLen] at hDeadDstTgt
                let ⟨l1', hEvS, hEvT, hMaskNext⟩ :=
                  dse_certified_elim_succeeds_and_effects
                    (bTgt := bTgt) (fSrc := fSrc) (fTgt := fTgt) (cm := cmS)
                    hCurSound hMask hDstEmp hDstNe0 hDeadDstTgt hDstTy hDstSlE
                    hLiveDst hTotRv
                let ⟨l1'', hEqS'', hNextSound⟩ :=
                  stepPlainStmtNonZero_sound hCurSound hStepPlain hEvS
                injection hEqS'' with eFs _; injection eFs with eF _
                have hL1Eq : l1' = l1'' := congrArg FrameState.locals eF
                subst hL1Eq
                unfold StepOutcomeBisim evalStep; dsimp
                rw [hBS, hBT2]; dsimp
                rw [hBBS, hBBT2]; dsimp
                rw [hStSrc, hStTgt2]; dsimp
                rw [hEvS, hEvT]
                refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                                 callerMem := cmS },
                  { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals }],
                    callerMem := cmS }, rfl, rfl,
                  { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                  { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals },
                  bCert, bSrc, bTgt,
                  rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq],
                  hBC, hBS, hBT, hAp, fun _ => ?_⟩
                refine ⟨bbSrc, bbTgt, _, exitEnv, hBBS, hBBT, ?_, hEdges, hNextSound, ?_⟩
                · dsimp; rw [hDropSNext, hDropTNext]; exact hTailRest
                · dsimp; rw [hDropTNext]; exact hMaskNext

private theorem applyCertifiedDseProgram_equiv {cert : ProgramDseCert}
    {pSrc pTgt : Program}
    (hApply : applyCertifiedDseProgram cert pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  unfold applyCertifiedDseProgram at hApply
  cases hLenB : Nat.beq cert.length pSrc.bodies.length with
  | false => rw [hLenB] at hApply; cases hApply
  | true =>
    rw [hLenB] at hApply; dsimp at hApply
    have hLenC := nat_beq_eq hLenB
    cases hMap : mapOption (fun pr => applyCertifiedDseBody pr.1 pr.2)
        (List.zip cert pSrc.bodies) with
    | none => rw [hMap] at hApply; cases hApply
    | some bodies' =>
      rw [hMap] at hApply; injection hApply with eP; subst eP
      have hHdr := programHeaderEq_with_bodies pSrc bodies'
      have hBodyLen : pSrc.bodies.length = bodies'.length :=
        (zip_length_eq hLenC).symm.trans (mapOption_length hMap).symm
      have hIds : pSrc.bodies.map Body.identity = bodies'.map Body.identity := by
        apply list_eq_of_getElem?_eq
        · rw [map_length_eq, map_length_eq, hBodyLen]
        · intro i
          rw [getElem?_map, getElem?_map]
          cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies i with
          | none =>
            have hGe : bodies'.length ≤ i := by
              rw [← hBodyLen]; exact getElem?_none_ge hBS
            rw [getElem?_none_of_ge hGe]
          | some bSrc =>
            let ⟨_, bTgt, _, hBT, hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
            let ⟨hBHdr, _, _, _, _, _, _, _, _⟩ := applyCertifiedDseBody_props hAp
            let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim hBHdr
            rw [hBT]; dsimp [Option.map]; rw [hIdEq]
      refine ⟨?_, hHdr, hIds⟩
      refine fullSemanticEquiv_of_query_iff hHdr ?_ ?_ ?_
      · intro defId bSrc bTgt hBS hBT
        let ⟨_, bTgt', _, hBT', hAp⟩ := mapOption_zip_getElem?_left hLenC hMap hBS
        dsimp at hBT; rw [hBT] at hBT'; injection hBT' with eB; subst eB
        let ⟨hBHdr, _, hEmp, hBnd, _, _, _, _, _⟩ := applyCertifiedDseBody_props hAp
        exact ⟨hBHdr, hEmp, hBnd⟩
      · intro q
        exact dse_query_iff q hLenC hHdr hMap
      · intro defId args
        exact (dse_query_iff
          (pSrc := entryProgForBody pSrc defId)
          (pTgt := entryProgForBody { pSrc with bodies := bodies' } defId)
          { args := args } hLenC
          (programHeaderEq_entryProg defId hHdr) hMap).1

private theorem programHeaderEq_trans {p₁ p₂ p₃ : Program}
    (h12 : programHeaderEq p₁ p₂ = true)
    (h23 : programHeaderEq p₂ p₃ = true) :
    programHeaderEq p₁ p₃ = true := by
  let ⟨pw12, ver12, ent12, sc12⟩ := programHeaderEq_elim h12
  let ⟨pw23, ver23, ent23, sc23⟩ := programHeaderEq_elim h23
  unfold programHeaderEq
  rw [pw12, pw23, ver12, ver23, ent12, ent23, sc12, sc23]
  rw [nat_beq_refl, nat_beq_refl, nat_beq_refl, scopeEq_refl]
  rfl

private theorem bodies_length_of_map_identity {p₁ p₂ : Program}
    (hIds : p₁.bodies.map Body.identity = p₂.bodies.map Body.identity) :
    p₁.bodies.length = p₂.bodies.length := by
  rw [← map_length_eq Body.identity p₁.bodies,
      ← map_length_eq Body.identity p₂.bodies, hIds]

private theorem applyCopyAndDestPropAndDseProgram_equiv {cert : CopyDestDseCert}
    {pSrc pTgt : Program}
    (hApply : applyCopyAndDestPropAndDseProgram cert pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  unfold applyCopyAndDestPropAndDseProgram at hApply
  cases h1 : applyCopyPropProgram cert.copyCert pSrc with
  | none => rw [h1] at hApply; cases hApply
  | some p₁ =>
    rw [h1] at hApply; dsimp at hApply
    cases h2 : applyDestPropProgram cert.destCert p₁ with
    | none => rw [h2] at hApply; cases hApply
    | some p₂ =>
      rw [h2] at hApply; dsimp at hApply
      let ⟨hEq01, hHdr01, hIds01⟩ := applyCopyPropProgram_equiv h1
      let ⟨hEq12, hHdr12, hIds12⟩ := applyDestPropProgram_equiv h2
      let ⟨hEq23, hHdr23, hIds23⟩ := applyCertifiedDseProgram_equiv hApply
      have hLen01 := bodies_length_of_map_identity hIds01
      have hLen12 := bodies_length_of_map_identity hIds12
      have hEq02 := fullSemanticEquiv_trans hLen01 hEq01 hEq12
      have hEq03 := fullSemanticEquiv_trans (hLen01.trans hLen12) hEq02 hEq23
      exact ⟨hEq03,
             programHeaderEq_trans hHdr01 (programHeaderEq_trans hHdr12 hHdr23),
             hIds01.trans (hIds12.trans hIds23)⟩

/-! #### Part D.4: Unified Half A Target Theorems (Theorems 1a, 1b, 1c) -/

private theorem applyMirOptStep_props {step : MirOptStep} {pSrc pTgt : Program}
    (hApply : applyMirOptStep step pSrc = some pTgt) :
    FullSemanticEquiv pSrc pTgt ∧
    programHeaderEq pSrc pTgt = true ∧
    pSrc.bodies.map Body.identity = pTgt.bodies.map Body.identity := by
  cases step with
  | moveToCopyDead cert => exact applyMoveToCopyDeadProgram_equiv hApply
  | simplifyCfgBranch cert => exact applySimplifyCfgBranchProgram_equiv hApply
  | instSimplifyAlgAndConst cert =>
    exact applyInstSimplifyAlgAndConstProgram_equiv hApply
  | copyAndDestPropAndDse cert =>
    exact applyCopyAndDestPropAndDseProgram_equiv hApply
  | compactUnusedTrailingLocals nc =>
    exact applyCompactTrailingLocalsProgram_equiv hApply

private theorem applyCopyPropProgram_unit_comm (cert : ProgramAbsCert) (p : Program) (u : DefId) :
    applyCopyPropProgram cert (unitProgForDef p u) =
      Option.map (fun p' => unitProgForDef p' u) (applyCopyPropProgram cert p) := by
  cases p with
  | mk bodies entry pw ver sc =>
    unfold applyCopyPropProgram unitProgForDef; dsimp
    cases Nat.beq cert.length bodies.length with
    | false => rfl
    | true =>
      dsimp
      cases mapOption (fun pr => applyCopyPropBody pr.1 pr.2) (List.zip cert bodies) <;> rfl

private theorem applyDestPropProgram_unit_comm (cert : ProgramDestPropCert) (p : Program) (u : DefId) :
    applyDestPropProgram cert (unitProgForDef p u) =
      Option.map (fun p' => unitProgForDef p' u) (applyDestPropProgram cert p) := by
  cases p with
  | mk bodies entry pw ver sc =>
    unfold applyDestPropProgram unitProgForDef; dsimp
    cases Nat.beq cert.length bodies.length with
    | false => rfl
    | true =>
      dsimp
      cases mapOption (fun pr => applyDestPropBody pr.1 pr.2) (List.zip cert bodies) <;> rfl

private theorem applyCertifiedDseProgram_unit_comm (cert : ProgramDseCert) (p : Program) (u : DefId) :
    applyCertifiedDseProgram cert (unitProgForDef p u) =
      Option.map (fun p' => unitProgForDef p' u) (applyCertifiedDseProgram cert p) := by
  cases p with
  | mk bodies entry pw ver sc =>
    unfold applyCertifiedDseProgram unitProgForDef; dsimp
    cases Nat.beq cert.length bodies.length with
    | false => rfl
    | true =>
      dsimp
      cases mapOption (fun pr => applyCertifiedDseBody pr.1 pr.2) (List.zip cert bodies) <;> rfl

private theorem applyMirOptStep_unit_comm (step : MirOptStep) (p : Program) (u : DefId) :
    applyMirOptStep step (unitProgForDef p u) =
      Option.map (fun p' => unitProgForDef p' u) (applyMirOptStep step p) := by
  cases step with
  | moveToCopyDead cert =>
    cases p with
    | mk bodies entry pw ver sc =>
      unfold applyMirOptStep applyMoveToCopyDeadProgram unitProgForDef; dsimp
      cases Nat.beq cert.length bodies.length with
      | false => rfl
      | true =>
        dsimp
        cases mapOption (fun pr => applyMoveToCopyDeadBody pr.1 pr.2) (List.zip cert bodies) <;> rfl
  | simplifyCfgBranch cert =>
    cases p with
    | mk bodies entry pw ver sc =>
      unfold applyMirOptStep applySimplifyCfgBranchProgram unitProgForDef; dsimp
      cases Nat.beq cert.length bodies.length with
      | false => rfl
      | true =>
        dsimp
        cases mapOption (fun pr => applySimplifyCfgBranchBody pr.1 pr.2) (List.zip cert bodies) <;> rfl
  | instSimplifyAlgAndConst cert =>
    cases p with
    | mk bodies entry pw ver sc =>
      unfold applyMirOptStep applyInstSimplifyAlgAndConstProgram unitProgForDef; dsimp
      cases Nat.beq cert.length bodies.length with
      | false => rfl
      | true =>
        dsimp
        cases mapOption (fun pr => applyInstSimplifyAlgAndConstBody pr.1 pr.2)
          (List.zip cert bodies) <;> rfl
  | copyAndDestPropAndDse cert =>
    unfold applyMirOptStep applyCopyAndDestPropAndDseProgram; dsimp
    rw [applyCopyPropProgram_unit_comm]
    cases applyCopyPropProgram cert.copyCert p with
    | none => rfl
    | some p₁ =>
      dsimp [Option.map]
      rw [applyDestPropProgram_unit_comm]
      cases applyDestPropProgram cert.destCert p₁ with
      | none => rfl
      | some p₂ =>
        dsimp [Option.map]
        exact applyCertifiedDseProgram_unit_comm cert.dseCert p₂ u
  | compactUnusedTrailingLocals nc =>
    cases p with
    | mk bodies entry pw ver sc =>
      unfold applyMirOptStep applyCompactTrailingLocalsProgram unitProgForDef; dsimp
      cases mapOption (applyCompactTrailingLocalsBody nc) bodies <;> rfl

private theorem applyMirOptTrace_unit_comm (trace : MirOptTrace) (p : Program) (u : DefId) :
    applyMirOptTrace trace (unitProgForDef p u) =
      Option.map (fun p' => unitProgForDef p' u) (applyMirOptTrace trace p) := by
  induction trace generalizing p with
  | nil => rfl
  | cons step rest ih =>
    dsimp [applyMirOptTrace]
    rw [applyMirOptStep_unit_comm]
    cases applyMirOptStep step p with
    | none => rfl
    | some pMid =>
      dsimp [Option.map]
      exact ih pMid

private theorem applyMirOptTrace_props {trace : MirOptTrace} {p₁ p₂ : Program}
    (hApply : applyMirOptTrace trace p₁ = some p₂) :
    FullSemanticEquiv p₁ p₂ ∧
    programHeaderEq p₁ p₂ = true ∧
    p₁.bodies.map Body.identity = p₂.bodies.map Body.identity := by
  induction trace generalizing p₁ with
  | nil =>
    injection hApply with e; subst e
    exact ⟨fullSemanticEquiv_refl p₁, programHeaderEq_refl p₁, rfl⟩
  | cons step rest ih =>
    dsimp [applyMirOptTrace] at hApply
    cases hSt : applyMirOptStep step p₁ with
    | none => rw [hSt] at hApply; cases hApply
    | some pMid =>
      rw [hSt] at hApply
      let ⟨hEq1, hHdr1, hIds1⟩ := applyMirOptStep_props hSt
      let ⟨hEq2, hHdr2, hIds2⟩ := ih hApply
      exact ⟨fullSemanticEquiv_trans (bodies_length_of_map_identity hIds1) hEq1 hEq2,
             programHeaderEq_trans hHdr1 hHdr2,
             hIds1.trans hIds2⟩

private theorem mirOptStep_sound_bidirectional_iff_priv
    (step : MirOptStep) (pSrc pTgt : Program)
    (hStep : checkMirOptStep step pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  unfold checkMirOptStep at hStep
  cases hAp : applyMirOptStep step pSrc with
  | none => rw [hAp] at hStep; cases hStep
  | some pOut =>
    rw [hAp] at hStep
    rw [← programEq_eq hStep]
    exact (applyMirOptStep_props hAp).1

private theorem mirOptTrace_sound_bidirectional_iff_priv
    (trace : MirOptTrace) (pPostCleanup pOptimized : Program)
    (hTrace : checkMirOptTrace trace pPostCleanup pOptimized = true) :
    FullSemanticEquiv pPostCleanup pOptimized := by
  unfold checkMirOptTrace at hTrace
  cases hAp : applyMirOptTrace trace pPostCleanup with
  | none => rw [hAp] at hTrace; cases hTrace
  | some pOut =>
    rw [hAp] at hTrace
    rw [← programEq_eq hTrace]
    exact (applyMirOptTrace_props hAp).1

private theorem mirOptTrace_crate_and_unit_vc_transport_iff_priv
    (trace : MirOptTrace) (pPostCleanup pOptimized : Program) (specs : Specs)
    (hTrace : checkMirOptTrace trace pPostCleanup pOptimized = true)
    (hSpec : SpecsPropertyInvariant specs) :
    (CrateTheorem ⟨pOptimized, specs⟩ ↔ CrateTheorem ⟨pPostCleanup, specs⟩) ∧
    (UnitTheorem ⟨pOptimized, specs⟩ ↔ UnitTheorem ⟨pPostCleanup, specs⟩) ∧
    (∀ u : DefId,
      UnitTheorem ⟨unitProgForDef pOptimized u, specs⟩ ↔
        UnitTheorem ⟨unitProgForDef pPostCleanup u, specs⟩) := by
  unfold checkMirOptTrace at hTrace
  cases hAp : applyMirOptTrace trace pPostCleanup with
  | none => rw [hAp] at hTrace; cases hTrace
  | some pOut =>
    rw [hAp] at hTrace
    have hEqOut := programEq_eq hTrace
    subst hEqOut
    cases specs with
    | mk safety prop =>
      let ⟨hEquiv, hHdr, hIds⟩ := applyMirOptTrace_props hAp
      let ⟨hPw, hVer, hEnt, hSc⟩ := programHeaderEq_elim hHdr
      let ⟨hCrate, hUnit⟩ :=
        programVerified_iff_of_equiv hEquiv hPw hVer hEnt hSc hIds
          safety prop (hSpec pPostCleanup pOut hEquiv).symm
      refine ⟨hCrate, hUnit, fun u => ?_⟩
      have hApU : applyMirOptTrace trace (unitProgForDef pPostCleanup u) =
          some (unitProgForDef pOut u) := by
        rw [applyMirOptTrace_unit_comm, hAp]; rfl
      let ⟨hEquivU, hHdrU, hIdsU⟩ := applyMirOptTrace_props hApU
      let ⟨hPwU, hVerU, hEntU, hScU⟩ := programHeaderEq_elim hHdrU
      exact (programVerified_iff_of_equiv hEquivU hPwU hVerU hEntU hScU hIdsU
        safety prop (hSpec _ _ hEquivU).symm).2

/-! ### Stage 4 Private Helpers — Slice E: `MirProfileV2` Conservative
Extension, `RemovePlaceMention`, & `UnreachablePropagation` -/

/-! #### Part E.1: Theorem 2a — Exact Conservative Extension
(`embedProgramV1`) -/

private theorem faultKindV2_ofV1_toV1 (k : FaultKind) :
    (FaultKindV2.ofV1 k).toV1 = k := by
  cases k <;> rfl

private theorem writePlaceV2_v1Embedded_eq (locals : List LocalSlot)
    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    writePlaceV2 .v1Embedded locals dstLocalId dstTy val =
      match writePlace locals dstLocalId dstTy val with
      | .ok l' => .ok l'
      | .error k => .error (FaultKindV2.ofV1 k) := by
  unfold writePlaceV2 writePlace checkValForMode
  dsimp
  cases checkVal val dstTy with
  | false => rfl
  | true =>
    dsimp
    cases Trusted.MirSemantics.getElem? locals dstLocalId with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | live _ =>
        cases setElem? locals dstLocalId (.live (some val)) <;> rfl

private theorem evalStatementV2_embed_toV1 (b : Body) (frame : FrameState)
    (cm : CallerMemory) (stmt : StatementKind) :
    mapStepResultV2ToV1
      (evalStatementV2 .v1Embedded (embedBodyV1 b) frame cm (.v1 stmt)) =
      evalStatement b frame cm stmt := by
  cases stmt with
  | nop => rfl
  | unsupported => rfl
  | storageLive id =>
    unfold evalStatementV2 evalV1StatementInV2 evalStatement embedBodyV1
    dsimp
    cases Trusted.MirSemantics.getElem? b.locals id with
    | none => rfl
    | some ty =>
      dsimp
      cases setElem? frame.locals id (liveUninitSlot ty) <;> rfl
  | storageDead id =>
    unfold evalStatementV2 evalV1StatementInV2 evalStatement embedBodyV1
    dsimp
    cases Nat.beq id 0 with
    | true => rfl
    | false =>
      dsimp
      cases setElem? frame.locals id .dead <;> rfl
  | assign dst rv =>
    unfold evalStatementV2 evalV1StatementInV2 evalStatement embedBodyV1
    dsimp
    cases dst.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      cases Trusted.MirSemantics.getElem? b.locals dst.localId with
      | none => rfl
      | some dstTy =>
        dsimp
        cases evalRvalue b.locals frame.locals dstTy rv with
        | error k => dsimp [mapStepResultV2ToV1]; rw [faultKindV2_ofV1_toV1]
        | ok pr =>
          let ⟨val, la⟩ := pr
          dsimp
          rw [writePlaceV2_v1Embedded_eq]
          cases writePlace la dst.localId dstTy val with
          | error k => dsimp [mapStepResultV2ToV1]; rw [faultKindV2_ofV1_toV1]
          | ok lw => rfl

private theorem evalTerminatorV2_embed_toV1 (b : Body) (bb : BasicBlock)
    (frame : FrameState) (cm : CallerMemory) :
    mapStepResultV2ToV1
      (evalTerminatorV2 (embedBodyV1 b) (embedBlockV1 bb) frame cm) =
      evalTerminator b bb frame cm := by
  cases bb with
  | mk stmts term cleanup =>
    cases term with
    | goto target => rfl
    | unreachable => rfl
    | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported => rfl
    | return_ =>
      unfold evalTerminatorV2 evalTerminator embedBodyV1 embedBlockV1
      dsimp
      cases cleanup with
      | true => rfl
      | false =>
        dsimp
        cases Trusted.MirSemantics.getElem? frame.locals 0 with
        | none => rfl
        | some sl =>
          cases sl with
          | dead => rfl
          | live o => cases o <;> rfl
    | switchInt discr targets =>
      unfold evalTerminatorV2 evalTerminator embedBodyV1 embedBlockV1
      dsimp
      cases evalPrimitiveOperand b.locals frame.locals discr with
      | error k => dsimp [mapStepResultV2ToV1]; rw [faultKindV2_ofV1_toV1]
      | ok pr =>
        let ⟨dv, la⟩ := pr
        dsimp
        cases dv with
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
        | bool bv =>
          dsimp
          cases evalBoolSwitchBranches bv targets.otherwise targets.branches with
          | error k => dsimp [mapStepResultV2ToV1]; rw [faultKindV2_ofV1_toV1]
          | ok tgt => rfl
        | scalar sv =>
          dsimp
          cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
          | error k => dsimp [mapStepResultV2ToV1]; rw [faultKindV2_ofV1_toV1]
          | ok tgt => rfl

private theorem mapStepResultV2ToV1_evalStepV2 (p : Program) (c : Choice) (s : State) :
    mapStepResultV2ToV1 (evalStepV2 (embedProgramV1 p) c s) =
      evalStep p c s := by
  cases s with
  | mk frames cm =>
    unfold evalStepV2 evalStep embedProgramV1
    dsimp
    cases frames with
    | nil => rfl
    | cons f rest =>
      cases rest with
      | cons _ _ => rfl
      | nil =>
        dsimp
        rw [getElem?_map]
        cases Trusted.MirSemantics.getElem? p.bodies f.defId with
        | none => rfl
        | some b =>
          dsimp [Option.map, embedBodyV1]
          rw [getElem?_map]
          cases Trusted.MirSemantics.getElem? b.basicBlocks f.blockIdx with
          | none => rfl
          | some bb =>
            dsimp [Option.map]
            have hStG : Trusted.MirSemantics.getElem? (embedBlockV1 bb).statements f.stmtIdx =
                (Trusted.MirSemantics.getElem? bb.statements f.stmtIdx).map StatementKindV2.v1 := by
              unfold embedBlockV1; dsimp; exact getElem?_map StatementKindV2.v1 bb.statements f.stmtIdx
            have hStL : (embedBlockV1 bb).statements.length = bb.statements.length := by
              unfold embedBlockV1; dsimp; exact map_length_eq StatementKindV2.v1 bb.statements
            rw [hStG, hStL]
            cases Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
            | some stmt =>
              dsimp [Option.map]
              exact evalStatementV2_embed_toV1 b f cm stmt
            | none =>
              dsimp [Option.map]
              cases Nat.beq f.stmtIdx bb.statements.length with
              | false => rfl
              | true =>
                dsimp
                exact evalTerminatorV2_embed_toV1 b bb f cm

private theorem evalStepV2_embed_step_iff (p : Program) (c : Choice) (s s' : State) :
    evalStepV2 (embedProgramV1 p) c s = .step s' ↔
      evalStep p c s = .step s' := by
  rw [← mapStepResultV2ToV1_evalStepV2 p c s]
  cases evalStepV2 (embedProgramV1 p) c s with
  | step s₂ =>
    dsimp [mapStepResultV2ToV1]
    constructor <;> (intro h; injection h with e; subst e; rfl)
  | done _ =>
    dsimp [mapStepResultV2ToV1]
    constructor <;> (intro h; cases h)
  | fault _ =>
    dsimp [mapStepResultV2ToV1]
    constructor <;> (intro h; cases h)

private theorem evalStepV2_embed_done_iff (p : Program) (c : Choice) (s : State)
    (out : TerminalOut) :
    evalStepV2 (embedProgramV1 p) c s = .done out ↔
      evalStep p c s = .done out := by
  rw [← mapStepResultV2ToV1_evalStepV2 p c s]
  cases evalStepV2 (embedProgramV1 p) c s with
  | done o₂ =>
    dsimp [mapStepResultV2ToV1]
    constructor <;> (intro h; injection h with e; subst e; rfl)
  | step _ =>
    dsimp [mapStepResultV2ToV1]
    constructor <;> (intro h; cases h)
  | fault _ =>
    dsimp [mapStepResultV2ToV1]
    constructor <;> (intro h; cases h)

private theorem evalStepV2_embed_fault_iff (p : Program) (c : Choice) (s : State)
    (k : FaultKind) :
    (∃ k₂ : FaultKindV2, k₂.toV1 = k ∧
      evalStepV2 (embedProgramV1 p) c s = .fault k₂) ↔
      evalStep p c s = .fault k := by
  rw [← mapStepResultV2ToV1_evalStepV2 p c s]
  cases evalStepV2 (embedProgramV1 p) c s with
  | fault k₂ =>
    dsimp [mapStepResultV2ToV1]
    constructor
    · intro ⟨k', hk, hEq⟩
      injection hEq with ek; subst ek
      rw [hk]
    · intro hEq
      injection hEq with ek
      exact ⟨k₂, ek, rfl⟩
  | step _ =>
    dsimp [mapStepResultV2ToV1]
    constructor
    · intro ⟨_, _, hEq⟩; cases hEq
    · intro hEq; cases hEq
  | done _ =>
    dsimp [mapStepResultV2ToV1]
    constructor
    · intro ⟨_, _, hEq⟩; cases hEq
    · intro hEq; cases hEq

private theorem list_any_map {α β : Type} (f : α → β) (p : β → Bool) (xs : List α) :
    (xs.map f).any p = xs.any (fun x => p (f x)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp [List.map, List.any]
    rw [ih]

private theorem list_all_map {α β : Type} (f : α → β) (p : β → Bool) (xs : List α) :
    (xs.map f).all p = xs.all (fun x => p (f x)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp [List.map, List.all]
    rw [ih]

private theorem hasStorageAnnotationV2_embed (b : Body) (idx : LocalId) :
    hasStorageAnnotationV2 (embedBodyV1 b) idx = hasStorageAnnotation b idx := by
  unfold hasStorageAnnotationV2 hasStorageAnnotation embedBodyV1
  dsimp
  rw [list_any_map]
  exact list_any_eq_of_getElem? rfl (fun i bb₁ bb₂ h1 h2 => by
    rw [h1] at h2; injection h2 with e; subst e
    unfold embedBlockV1; dsimp
    rw [list_any_map]; rfl)

private theorem storageAnnotationsInBoundsV2_embed (b : Body) :
    storageAnnotationsInBoundsV2 (embedBodyV1 b) = storageAnnotationsInBounds b := by
  unfold storageAnnotationsInBoundsV2 storageAnnotationsInBounds embedBodyV1
  dsimp
  rw [list_all_map]
  exact list_all_eq_of_getElem? rfl (fun i bb₁ bb₂ h1 h2 => by
    rw [h1] at h2; injection h2 with e; subst e
    unfold embedBlockV1; dsimp
    rw [list_all_map]
    exact list_all_eq_of_getElem? rfl (fun j s₁ s₂ hs1 hs2 => by
      rw [hs1] at hs2; injection hs2 with es; subst es
      cases s₁ <;> rfl))

private theorem checkArgsMatchForMode_v1Embedded (args : List Val) (tys : List MirTy) :
    checkArgsMatchForMode .v1Embedded args tys = checkArgsMatch args tys := by
  induction args generalizing tys with
  | nil =>
    cases tys <;> rfl
  | cons v vs ih =>
    cases tys with
    | nil => rfl
    | cons ty rest =>
      dsimp [checkArgsMatchForMode, checkValForMode, checkArgsMatch]
      rw [ih rest]

private theorem initLocalsLoopV2_embed (b : Body) (args : List Val) :
    ∀ idx tys,
      initLocalsLoopV2 (embedBodyV1 b) args idx tys =
        initLocalsLoop b args idx tys := by
  intro idx tys
  induction tys generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    dsimp [initLocalsLoopV2, initLocalsLoop]
    rw [hasStorageAnnotationV2_embed b idx, ih (idx + 1)]
    rfl

private theorem list_isEmpty_map {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).isEmpty = xs.isEmpty := by
  cases xs <;> rfl

private theorem except_ofV1_ite {c₁ c₂ : Bool} {e₂ : Except FaultKindV2 State}
    {e₁ : Except FaultKind State}
    (hc : c₁ = c₂)
    (he : e₂ = match e₁ with
      | .ok s₀ => .ok s₀
      | .error k => .error (FaultKindV2.ofV1 k)) :
    (if c₁ then Except.error FaultKindV2.unsupported else e₂) =
      match (if c₂ then Except.error FaultKind.unsupported else e₁) with
      | .ok s₀ => .ok s₀
      | .error k => .error (FaultKindV2.ofV1 k) := by
  subst hc
  cases c₁ with
  | true => rfl
  | false => exact he

private theorem initStateV2_embedProgramV1 (p : Program) (q : Query) :
    initStateV2 (embedProgramV1 p) q =
      match initState p q with
      | .ok s₀ => .ok s₀
      | .error k => .error (FaultKindV2.ofV1 k) := by
  unfold initStateV2 initState embedProgramV1
  dsimp
  cases Nat.beq p.pointerWidthBits 64 with
  | false => rfl
  | true =>
    cases Nat.beq p.mirProfileVersion 1 with
    | false => rfl
    | true =>
      cases q.callerMem.allocations.isEmpty with
      | false => rfl
      | true =>
        dsimp
        rw [getElem?_map]
        cases Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
        | none => rfl
        | some b =>
          dsimp [Option.map]
          refine except_ofV1_ite (list_isEmpty_map embedBlockV1 b.basicBlocks) ?_
          refine except_ofV1_ite rfl ?_
          refine except_ofV1_ite (congrArg Bool.not (storageAnnotationsInBoundsV2_embed b)) ?_
          refine except_ofV1_ite rfl ?_
          refine except_ofV1_ite (congrArg Bool.not (checkArgsMatchForMode_v1Embedded _ _)) ?_
          rw [initLocalsLoopV2_embed b]
          rfl

private theorem stepV2_iff_evalStepV2 {p : ProgramV2} {s : State}
    {res : StepResultV2 State TerminalOut} :
    StepV2 p s res ↔ evalStepV2 p 0 s = res := by
  constructor
  · intro ⟨c, hc, hEv⟩
    have hc0 : c = 0 := hc
    subst hc0; exact hEv
  · intro hEv
    exact ⟨0, rfl, hEv⟩

private theorem reachesV2_embed_iff (p : Program) (s₁ s₂ : State) :
    ReachesV2 (embedProgramV1 p) s₁ s₂ ↔ Reaches p s₁ s₂ := by
  constructor
  · intro hR
    induction hR with
    | refl => exact Reaches.refl _
    | tail _ hSt ih =>
      have hEv2 := stepV2_iff_evalStepV2.mp hSt
      have hEv1 := (evalStepV2_embed_step_iff p 0 _ _).mp hEv2
      exact Reaches.tail ih (step_iff_evalStep.mpr hEv1)
  · intro hR
    induction hR with
    | refl => exact ReachesV2.refl _
    | tail _ hSt ih =>
      have hEv1 := step_iff_evalStep.mp hSt
      have hEv2 := (evalStepV2_embed_step_iff p 0 _ _).mpr hEv1
      exact ReachesV2.tail ih (stepV2_iff_evalStepV2.mpr hEv2)

private theorem profileV2_conservative_extension_exact_priv (p : Program) :
    (∀ (c : Choice) (s : State),
      mapStepResultV2ToV1 (evalStepV2 (embedProgramV1 p) c s) =
        evalStep p c s) ∧
    (∀ q : Query,
      (WellFormedV2 (embedProgramV1 p) q ↔ WellFormed p q) ∧
      (∀ out : TerminalOut,
        BehaviorV2 (embedProgramV1 p) q out ↔ Behavior p q out) ∧
      (∀ k : FaultKind,
        (∃ k₂ : FaultKindV2,
          k₂.toV1 = k ∧
          ReachesResultV2 (embedProgramV1 p) q (.fault k₂)) ↔
          ReachesResult p q (.fault k)) ∧
      (DivergesV2 (embedProgramV1 p) q ↔ Diverges p q)) := by
  refine ⟨mapStepResultV2ToV1_evalStepV2 p, fun q => ?_⟩
  have hInit := initStateV2_embedProgramV1 p q
  have hFaultIff : ∀ k : FaultKind,
      (∃ k₂ : FaultKindV2, k₂.toV1 = k ∧
        ReachesResultV2 (embedProgramV1 p) q (.fault k₂)) ↔
        ReachesResult p q (.fault k) := by
    intro k
    unfold ReachesResultV2 ReachesResult
    rw [hInit]
    cases initState p q with
    | error k₀ =>
      dsimp
      constructor
      · intro ⟨k₂, hk, hEq⟩
        injection hEq with ek; subst ek
        rw [faultKindV2_ofV1_toV1] at hk
        rw [hk]
      · intro hEq
        injection hEq with ek; subst ek
        exact ⟨FaultKindV2.ofV1 k, faultKindV2_ofV1_toV1 k, rfl⟩
    | ok s₀ =>
      dsimp
      constructor
      · intro ⟨k₂, hk, s, hR2, hSt2⟩
        have hEv1 := (evalStepV2_embed_fault_iff p 0 s k).mp
          ⟨k₂, hk, stepV2_iff_evalStepV2.mp hSt2⟩
        exact ⟨s, (reachesV2_embed_iff p s₀ s).mp hR2, step_iff_evalStep.mpr hEv1⟩
      · intro ⟨s, hR1, hSt1⟩
        let ⟨k₂, hk, hEv2⟩ :=
          (evalStepV2_embed_fault_iff p 0 s k).mpr (step_iff_evalStep.mp hSt1)
        exact ⟨k₂, hk, s, (reachesV2_embed_iff p s₀ s).mpr hR1,
               stepV2_iff_evalStepV2.mpr hEv2⟩
  have hBehIff : ∀ out : TerminalOut,
      BehaviorV2 (embedProgramV1 p) q out ↔ Behavior p q out := by
    intro out
    unfold BehaviorV2 Behavior ReachesResultV2 ReachesResult
    rw [hInit]
    cases initState p q with
    | error _ =>
      dsimp
      constructor <;> (intro h; cases h)
    | ok s₀ =>
      dsimp
      constructor
      · intro ⟨s, hR2, hSt2⟩
        have hEv1 := (evalStepV2_embed_done_iff p 0 s out).mp
          (stepV2_iff_evalStepV2.mp hSt2)
        exact ⟨s, (reachesV2_embed_iff p s₀ s).mp hR2, step_iff_evalStep.mpr hEv1⟩
      · intro ⟨s, hR1, hSt1⟩
        have hEv2 := (evalStepV2_embed_done_iff p 0 s out).mpr
          (step_iff_evalStep.mp hSt1)
        exact ⟨s, (reachesV2_embed_iff p s₀ s).mpr hR1,
               stepV2_iff_evalStepV2.mpr hEv2⟩
  have hWfIff : WellFormedV2 (embedProgramV1 p) q ↔ WellFormed p q := by
    unfold WellFormedV2 WellFormed
    constructor
    · intro ⟨⟨s₀, hOk2, _⟩, hNoF2⟩
      rw [hInit] at hOk2
      cases hInit1 : initState p q with
      | error _ => rw [hInit1] at hOk2; cases hOk2
      | ok s₁ =>
        rw [hInit1] at hOk2; injection hOk2 with es; subst es
        refine ⟨⟨s₁, rfl, fun _ _ => ⟨0, rfl⟩⟩, fun k hF1 => ?_⟩
        let ⟨k₂, _, hF2⟩ := (hFaultIff k).mpr hF1
        exact hNoF2 k₂ hF2
    · intro ⟨⟨s₀, hOk1, _⟩, hNoF1⟩
      have hOk2 : initStateV2 (embedProgramV1 p) q = .ok s₀ := by
        rw [hInit, hOk1]
      refine ⟨⟨s₀, hOk2, fun _ _ => ⟨0, rfl⟩⟩, fun k₂ hF2 => ?_⟩
      exact hNoF1 k₂.toV1 ((hFaultIff k₂.toV1).mp ⟨k₂, rfl, hF2⟩)
  have hDivIff : DivergesV2 (embedProgramV1 p) q ↔ Diverges p q := by
    unfold DivergesV2 Diverges
    rw [hInit]
    cases initState p q with
    | error _ =>
      constructor <;> (intro ⟨_, hOk, _⟩; cases hOk)
    | ok s₀ =>
      constructor
      · intro ⟨s', hOk, tr, h0, hSt⟩
        injection hOk with es; subst es
        refine ⟨s₀, rfl, tr, h0, fun n => ?_⟩
        exact step_iff_evalStep.mpr
          ((evalStepV2_embed_step_iff p 0 _ _).mp (stepV2_iff_evalStepV2.mp (hSt n)))
      · intro ⟨s', hOk, tr, h0, hSt⟩
        injection hOk with es; subst es
        refine ⟨s₀, rfl, tr, h0, fun n => ?_⟩
        exact stepV2_iff_evalStepV2.mpr
          ((evalStepV2_embed_step_iff p 0 _ _).mpr (step_iff_evalStep.mp (hSt n)))
  exact ⟨hWfIff, hBehIff, hFaultIff, hDivIff⟩

/-! #### Part E.2: Shared `MirProfileV2` Simulation, `iterStateV2`, &
`AbsEnvSoundV2` -/

private noncomputable def iterStateV2 (p : ProgramV2) (s₀ : State) : Nat → State
  | 0 => s₀
  | n + 1 =>
    match evalStepV2 p 0 (iterStateV2 p s₀ n) with
    | .step next => next
    | .done _ => iterStateV2 p s₀ n
    | .fault _ => iterStateV2 p s₀ n

private theorem iterStateV2_eq_of_trace {p : ProgramV2} {s₀ : State}
    {trace : Nat → State} (h0 : trace 0 = s₀)
    (hStep : ∀ n, StepV2 p (trace n) (.step (trace (n + 1)))) :
    ∀ n, iterStateV2 p s₀ n = trace n := by
  intro n
  induction n with
  | zero => exact h0.symm
  | succ k ih =>
    dsimp [iterStateV2]
    rw [ih, stepV2_iff_evalStepV2.mp (hStep k)]

private theorem reachesV2_trans {p : ProgramV2} {s₁ s₂ s₃ : State}
    (h12 : ReachesV2 p s₁ s₂) (h23 : ReachesV2 p s₂ s₃) :
    ReachesV2 p s₁ s₃ := by
  induction h23 with
  | refl => exact h12
  | tail _ hSt ih => exact ReachesV2.tail ih hSt

private theorem lockstep_inv_v2_query_iff {pSrc pTgt : ProgramV2} {q : Query}
    {Inv : State → Prop}
    (hInit : initStateV2 pSrc q = initStateV2 pTgt q)
    (hInv0 : ∀ s₀, initStateV2 pSrc q = .ok s₀ → Inv s₀)
    (hStep : ∀ s, Inv s →
      evalStepV2 pSrc 0 s = evalStepV2 pTgt 0 s ∧
      ∀ s', evalStepV2 pSrc 0 s = .step s' → Inv s') :
    (WellFormedV2 pTgt q ↔ WellFormedV2 pSrc q) ∧
    (∀ out : TerminalOut, BehaviorV2 pTgt q out ↔ BehaviorV2 pSrc q out) ∧
    (∀ k : FaultKindV2,
      ReachesResultV2 pTgt q (.fault k) ↔ ReachesResultV2 pSrc q (.fault k)) ∧
    (DivergesV2 pTgt q ↔ DivergesV2 pSrc q) := by
  cases hInitS : initStateV2 pSrc q with
  | error k₀ =>
    have hInitT : initStateV2 pTgt q = .error k₀ := by rw [← hInit]; exact hInitS
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold WellFormedV2; rw [hInitS, hInitT]
      constructor <;> (intro ⟨⟨_, h, _⟩, _⟩; cases h)
    · intro out; unfold BehaviorV2 ReachesResultV2; rw [hInitS, hInitT]
    · intro k; unfold ReachesResultV2; rw [hInitS, hInitT]
    · unfold DivergesV2; rw [hInitS, hInitT]
      constructor <;> (intro ⟨_, h, _⟩; cases h)
  | ok s₀ =>
    have hInitT : initStateV2 pTgt q = .ok s₀ := by rw [← hInit]; exact hInitS
    have hI0 := hInv0 s₀ hInitS
    have hReachIff : ∀ s,
        (ReachesV2 pSrc s₀ s → Inv s ∧ ReachesV2 pTgt s₀ s) ∧
        (ReachesV2 pTgt s₀ s → Inv s ∧ ReachesV2 pSrc s₀ s) := by
      intro s
      constructor
      · intro hRS
        induction hRS with
        | refl => exact ⟨hI0, ReachesV2.refl s₀⟩
        | @tail s₂ s₃ _ hSt ih =>
          let ⟨hIs, hRT⟩ := ih
          have hEvS := stepV2_iff_evalStepV2.mp hSt
          let ⟨hEqEv, hNextI⟩ := hStep s₂ hIs
          have hEvT : evalStepV2 pTgt 0 s₂ = .step s₃ := by rw [← hEqEv]; exact hEvS
          exact ⟨hNextI s₃ hEvS, ReachesV2.tail hRT (stepV2_iff_evalStepV2.mpr hEvT)⟩
      · intro hRT
        induction hRT with
        | refl => exact ⟨hI0, ReachesV2.refl s₀⟩
        | @tail s₂ s₃ _ hSt ih =>
          let ⟨hIs, hRS⟩ := ih
          have hEvT := stepV2_iff_evalStepV2.mp hSt
          let ⟨hEqEv, hNextI⟩ := hStep s₂ hIs
          have hEvS : evalStepV2 pSrc 0 s₂ = .step s₃ := by rw [hEqEv]; exact hEvT
          exact ⟨hNextI s₃ hEvS, ReachesV2.tail hRS (stepV2_iff_evalStepV2.mpr hEvS)⟩
    have hResIff : ∀ res, ReachesResultV2 pTgt q res ↔ ReachesResultV2 pSrc q res := by
      intro res
      unfold ReachesResultV2; rw [hInitS, hInitT]
      constructor
      · intro ⟨s, hRT, hStT⟩
        let ⟨hIs, hRS⟩ := (hReachIff s).2 hRT
        have hEvT := stepV2_iff_evalStepV2.mp hStT
        rw [← (hStep s hIs).1] at hEvT
        exact ⟨s, hRS, stepV2_iff_evalStepV2.mpr hEvT⟩
      · intro ⟨s, hRS, hStS⟩
        let ⟨hIs, hRT⟩ := (hReachIff s).1 hRS
        have hEvS := stepV2_iff_evalStepV2.mp hStS
        rw [(hStep s hIs).1] at hEvS
        exact ⟨s, hRT, stepV2_iff_evalStepV2.mpr hEvS⟩
    refine ⟨?_, fun out => hResIff (.done out), fun k => hResIff (.fault k), ?_⟩
    · unfold WellFormedV2; rw [hInitS, hInitT]
      constructor
      · intro ⟨_, hNF⟩
        exact ⟨⟨s₀, rfl, fun _ _ => ⟨0, rfl⟩⟩, fun k hFS => hNF k ((hResIff (.fault k)).mpr hFS)⟩
      · intro ⟨_, hNF⟩
        exact ⟨⟨s₀, rfl, fun _ _ => ⟨0, rfl⟩⟩, fun k hFT => hNF k ((hResIff (.fault k)).mp hFT)⟩
    · unfold DivergesV2; rw [hInitS, hInitT]
      constructor
      · intro ⟨t₀, hOkT, tr, h0, hTrSt⟩
        injection hOkT with eT; subst eT
        have hTrInv : ∀ n, Inv (tr n) := by
          intro n
          induction n with
          | zero => rw [h0]; exact hI0
          | succ m ih =>
            have hEvT := stepV2_iff_evalStepV2.mp (hTrSt m)
            rw [← (hStep (tr m) ih).1] at hEvT
            exact (hStep (tr m) ih).2 (tr (m + 1)) hEvT
        refine ⟨s₀, rfl, tr, h0, fun n => ?_⟩
        have hEvT := stepV2_iff_evalStepV2.mp (hTrSt n)
        rw [← (hStep (tr n) (hTrInv n)).1] at hEvT
        exact stepV2_iff_evalStepV2.mpr hEvT
      · intro ⟨s₀', hOkS, tr, h0, hTrSt⟩
        injection hOkS with eS; subst eS
        have hTrInv : ∀ n, Inv (tr n) := by
          intro n
          induction n with
          | zero => rw [h0]; exact hI0
          | succ m ih =>
            exact (hStep (tr m) ih).2 (tr (m + 1)) (stepV2_iff_evalStepV2.mp (hTrSt m))
        refine ⟨s₀, rfl, tr, h0, fun n => ?_⟩
        have hEvS := stepV2_iff_evalStepV2.mp (hTrSt n)
        rw [(hStep (tr n) (hTrInv n)).1] at hEvS
        exact stepV2_iff_evalStepV2.mpr hEvS

private theorem fullSemanticEquivV2_of_query_iff {pSrc pTgt : ProgramV2}
    (hHdr : programHeaderV2Eq pSrc pTgt = true)
    (hBodyFields : ∀ defId bSrc bTgt,
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      bodyHeaderV2Eq bSrc bTgt = true ∧
      bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
      storageAnnotationsInBoundsV2 bSrc = storageAnnotationsInBoundsV2 bTgt)
    (hQuery : ∀ q,
      (WellFormedV2 pTgt q ↔ WellFormedV2 pSrc q) ∧
      (∀ out : TerminalOut, BehaviorV2 pTgt q out ↔ BehaviorV2 pSrc q out) ∧
      (∀ k : FaultKindV2,
        ReachesResultV2 pTgt q (.fault k) ↔ ReachesResultV2 pSrc q (.fault k)) ∧
      (DivergesV2 pTgt q ↔ DivergesV2 pSrc q))
    (hEntryWf : ∀ defId args,
      WellFormedV2 (entryProgForBodyV2 pTgt defId) { args := args } ↔
        WellFormedV2 (entryProgForBodyV2 pSrc defId) { args := args }) :
    FullSemanticEquivV2 pSrc pTgt := by
  let ⟨hPw, hVer, _, _, hPm⟩ := programHeaderV2Eq_elim hHdr
  refine ⟨hQuery, ?_, ?_⟩
  · intro q post
    let ⟨hWf, hBeh, _, _⟩ := hQuery q
    constructor
    · intro ⟨hW, hP⟩
      exact ⟨hWf.mp hW, fun out hB => hP out ((hBeh out).mpr hB)⟩
    · intro ⟨hW, hP⟩
      exact ⟨hWf.mpr hW, fun out hB => hP out ((hBeh out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hBS hBT
    let ⟨hBHdr, hEmp, hStBnd⟩ := hBodyFields defId bSrc bTgt hBS hBT
    let ⟨hArg, hLoc, hUns, hId⟩ := bodyHeaderV2Eq_elim hBHdr
    have hAdmEq : BodyStaticAdmittedV2 pSrc bSrc = BodyStaticAdmittedV2 pTgt bTgt := by
      unfold BodyStaticAdmittedV2
      rw [hPw, hVer, hPm, hId, hEmp, hArg, hLoc, hStBnd]
    have hArgsEq : ∀ args, ValidEntryArgsV2 pSrc.profileMode bSrc args ↔
        ValidEntryArgsV2 pTgt.profileMode bTgt args := by
      intro args
      unfold ValidEntryArgsV2
      rw [hPm, hLoc, hArg]
    constructor
    · intro ⟨_, hAdmT, hVerT⟩
      refine ⟨hBS, by rw [hAdmEq]; exact hAdmT, ?_⟩
      intro args hVA hPre
      rw [hUns] at hPre
      exact (hEntryWf defId args).mp (hVerT args ((hArgsEq args).mp hVA) hPre)
    · intro ⟨_, hAdmS, hVerS⟩
      refine ⟨hBT, by rw [← hAdmEq]; exact hAdmS, ?_⟩
      intro args hVA hPre
      rw [← hUns] at hPre
      exact (hEntryWf defId args).mpr (hVerS args ((hArgsEq args).mpr hVA) hPre)

private noncomputable def SlotWellTypedV2 (mode : ProfileModeV2) (ty : MirTy) :
    LocalSlot → Prop
  | .dead => True
  | .live none => True
  | .live (some v) => checkValForMode mode v ty = true

private noncomputable def LocalsWellTypedV2 (mode : ProfileModeV2)
    (bodyLocals : List MirTy) (locals : List LocalSlot) : Prop :=
  locals.length = bodyLocals.length ∧
  ∀ i ty sl,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? locals i = some sl →
    SlotWellTypedV2 mode ty sl

private noncomputable def AbsSlotSoundV2 (mode : ProfileModeV2) (ty : MirTy)
    (abs : AbsSlot) (sl : LocalSlot) : Prop :=
  SlotWellTypedV2 mode ty sl ∧
  match abs with
  | .dead => True
  | .liveUninit => ∃ o, sl = .live o
  | .liveInit => ∃ v, sl = .live (some v)

private noncomputable def AbsEnvSoundV2 (mode : ProfileModeV2) (bodyLocals : List MirTy)
    (env : List AbsSlot) (locals : List LocalSlot) : Prop :=
  LocalsWellTypedV2 mode bodyLocals locals ∧
  env.length = bodyLocals.length ∧
  ∀ i ty abs sl,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? env i = some abs →
    Trusted.MirSemantics.getElem? locals i = some sl →
    AbsSlotSoundV2 mode ty abs sl

private theorem absSlotImplies_soundV2 {mode : ProfileModeV2} {ty : MirTy}
    {a₁ a₂ : AbsSlot} {sl : LocalSlot}
    (hImp : absSlotImplies a₁ a₂ = true)
    (hSound : AbsSlotSoundV2 mode ty a₁ sl) :
    AbsSlotSoundV2 mode ty a₂ sl := by
  let ⟨hWt, hS⟩ := hSound
  cases a₂ with
  | dead => exact ⟨hWt, True.intro⟩
  | liveUninit =>
    cases a₁ with
    | dead => cases hImp
    | liveUninit => exact ⟨hWt, hS⟩
    | liveInit =>
      let ⟨v, hv⟩ := hS
      exact ⟨hWt, ⟨some v, hv⟩⟩
  | liveInit =>
    cases a₁ with
    | dead | liveUninit => cases hImp
    | liveInit => exact ⟨hWt, hS⟩

private theorem absEnvImplies_soundV2 {mode : ProfileModeV2} {bodyLocals : List MirTy}
    {env₁ env₂ : List AbsSlot} {locals : List LocalSlot}
    (hImp : absEnvImplies env₁ env₂ = true)
    (hSound : AbsEnvSoundV2 mode bodyLocals env₁ locals) :
    AbsEnvSoundV2 mode bodyLocals env₂ locals := by
  let ⟨hWt, hLen1, hAll⟩ := hSound
  have hLen12 : env₁.length = env₂.length := listRel_length hImp
  refine ⟨hWt, hLen12.symm.trans hLen1, ?_⟩
  intro i ty a₂ sl hTy hA2 hSl
  let ⟨a₁, hA1, hImpSlot⟩ := listRel_getElem?_right hImp hA2
  exact absSlotImplies_soundV2 hImpSlot (hAll i ty a₁ sl hTy hA1 hSl)

private theorem checkVal_implies_checkValForMode (mode : ProfileModeV2) {v : Val}
    {ty : MirTy} (h : checkVal v ty = true) :
    checkValForMode mode v ty = true := by
  cases mode with
  | v1Embedded => exact h
  | v2Extended =>
    unfold checkValForMode checkValV2
    cases v with
    | ptr pv =>
      cases ty with
      | rawPtr _ _ => cases h
      | bool | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | unsupported =>
        exact h
    | scalar _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ => exact h

private theorem liveUninitSlot_absSoundV2 (mode : ProfileModeV2) (ty : MirTy) :
    AbsSlotSoundV2 mode ty
      (if isAlwaysInhabitedZst ty then .liveInit else .liveUninit)
      (liveUninitSlot ty) := by
  cases ty with
  | unit =>
    exact ⟨checkVal_implies_checkValForMode mode (liveUninitSlot_wellTyped .unit),
           ⟨.unit, rfl⟩⟩
  | enum ety =>
    cases hZ : isZstEnumTy ety with
    | true =>
      have h1 : isAlwaysInhabitedZst (.enum ety) = true := hZ
      have h2 : liveUninitSlot (.enum ety) = .live (some (.enumVal ety 0)) := by
        unfold liveUninitSlot; dsimp; rw [hZ]; rfl
      rw [h1, h2]; dsimp
      have hWt1 := liveUninitSlot_wellTyped (.enum ety)
      rw [h2] at hWt1
      exact ⟨checkVal_implies_checkValForMode mode hWt1, ⟨.enumVal ety 0, rfl⟩⟩
    | false =>
      have h1 : isAlwaysInhabitedZst (.enum ety) = false := hZ
      have h2 : liveUninitSlot (.enum ety) = .live none := by
        unfold liveUninitSlot; dsimp; rw [hZ]; rfl
      rw [h1, h2]; dsimp
      exact ⟨True.intro, ⟨none, rfl⟩⟩
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    exact ⟨True.intro, ⟨none, rfl⟩⟩

private theorem localsWellTypedV2_set {mode : ProfileModeV2} {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {id : Nat} {ty : MirTy} {sl : LocalSlot}
    (hWt : LocalsWellTypedV2 mode bodyLocals locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSet : setElem? locals id sl = some locals')
    (hSl : SlotWellTypedV2 mode ty sl) :
    LocalsWellTypedV2 mode bodyLocals locals' := by
  refine ⟨(setElem?_length hSet).trans hWt.1, ?_⟩
  intro i tyi sli hTyi hGeti
  cases hEq : Nat.beq i id with
  | true =>
    have hi := nat_beq_eq hEq; subst hi
    rw [hTy] at hTyi; injection hTyi with e1; subst e1
    rw [setElem?_getElem?_same hSet] at hGeti; injection hGeti with e2; subst e2
    exact hSl
  | false =>
    rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hEq)] at hGeti
    exact hWt.2 i tyi sli hTyi hGeti

private theorem absEnvSoundV2_set {mode : ProfileModeV2} {bodyLocals : List MirTy}
    {env env' : List AbsSlot} {locals locals' : List LocalSlot}
    {id : Nat} {ty : MirTy} {abs' : AbsSlot} {sl' : LocalSlot}
    (hEnv : AbsEnvSoundV2 mode bodyLocals env locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSetE : setElem? env id abs' = some env')
    (hSetL : setElem? locals id sl' = some locals')
    (hSlSound : AbsSlotSoundV2 mode ty abs' sl') :
    AbsEnvSoundV2 mode bodyLocals env' locals' := by
  let ⟨hWt, hLenE, hAll⟩ := hEnv
  refine ⟨localsWellTypedV2_set hWt hTy hSetL hSlSound.1,
          (setElem?_length hSetE).trans hLenE, ?_⟩
  intro i tyi absi sli hTyi hE hL
  cases hEq : Nat.beq i id with
  | true =>
    have hi := nat_beq_eq hEq; subst hi
    rw [hTy] at hTyi; injection hTyi with e1; subst e1
    rw [setElem?_getElem?_same hSetE] at hE; injection hE with e2; subst e2
    rw [setElem?_getElem?_same hSetL] at hL; injection hL with e3; subst e3
    exact hSlSound
  | false =>
    have hNe := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSetE hNe] at hE
    rw [setElem?_getElem?_ne hSetL hNe] at hL
    exact hAll i tyi absi sli hTyi hE hL

private theorem checkArgsMatchForMode_getElem? {mode : ProfileModeV2} :
    ∀ {args : List Val} {tys : List MirTy} {k : Nat} {ty : MirTy},
      checkArgsMatchForMode mode args tys = true →
      Trusted.MirSemantics.getElem? tys k = some ty →
      ∃ v, Trusted.MirSemantics.getElem? args k = some v ∧
        checkValForMode mode v ty = true := by
  intro args
  induction args with
  | nil =>
    intro tys k ty hM hG
    cases tys with
    | nil => cases hG
    | cons _ _ => cases hM
  | cons v vs ih =>
    intro tys k ty hM hG
    cases tys with
    | nil => cases hM
    | cons t₀ rest =>
      let ⟨hHere, hTail⟩ := bool_and_true hM
      cases k with
      | zero =>
        injection hG with e; subst e
        exact ⟨v, rfl, hHere⟩
      | succ m =>
        exact ih hTail hG

private theorem initLocalsLoopV2_length (body : BodyV2) (args : List Val) :
    ∀ idx tys, (initLocalsLoopV2 body args idx tys).length = tys.length := by
  intro idx tys
  induction tys generalizing idx with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [initLocalsLoopV2, List.length]; rw [ih (idx + 1)]

private theorem initLocalsLoopV2_getElem? (body : BodyV2) (args : List Val) :
    ∀ base tys k ty,
      Trusted.MirSemantics.getElem? tys k = some ty →
      Trusted.MirSemantics.getElem? (initLocalsLoopV2 body args base tys) k =
        some (if Nat.beq (base + k) 0 then
                liveUninitSlot ty
              else if Nat.ble (base + k) body.argumentCount then
                match Trusted.MirSemantics.getElem? args ((base + k) - 1) with
                | some v => .live (some v)
                | none => .dead
              else if hasStorageAnnotationV2 body (base + k) then
                .dead
              else
                liveUninitSlot ty) := by
  intro base tys
  induction tys generalizing base with
  | nil => intro _ _ h; cases h
  | cons _ rest ih =>
    intro k ty h
    cases k with
    | zero => injection h with e; subst e; rfl
    | succ m =>
      have hSub := ih (base + 1) m ty h
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hSub
      exact hSub

private theorem initAbsEnvLoopV2_length (body : BodyV2) :
    ∀ idx tys, (initAbsEnvLoopV2 body idx tys).length = tys.length := by
  intro idx tys
  induction tys generalizing idx with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [initAbsEnvLoopV2, List.length]; rw [ih (idx + 1)]

private theorem initAbsEnvLoopV2_getElem? (body : BodyV2) :
    ∀ base tys k ty,
      Trusted.MirSemantics.getElem? tys k = some ty →
      Trusted.MirSemantics.getElem? (initAbsEnvLoopV2 body base tys) k =
        some (initAbsSlotV2 body (base + k) ty) := by
  intro base tys
  induction tys generalizing base with
  | nil => intro _ _ h; cases h
  | cons _ rest ih =>
    intro k ty h
    cases k with
    | zero => injection h with e; subst e; rfl
    | succ m =>
      have hSub := ih (base + 1) m ty h
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hSub
      exact hSub

private theorem initAbsEnvLoopV2_sound {mode : ProfileModeV2} {body : BodyV2}
    {args : List Val}
    (hArgs : checkArgsMatchForMode mode args
      ((body.locals.drop 1).take body.argumentCount) = true) :
    AbsEnvSoundV2 mode body.locals
      (initAbsEnvLoopV2 body 0 body.locals)
      (initLocalsLoopV2 body args 0 body.locals) := by
  have hEach : ∀ i ty,
      Trusted.MirSemantics.getElem? body.locals i = some ty →
      ∃ abs sl,
        Trusted.MirSemantics.getElem? (initAbsEnvLoopV2 body 0 body.locals) i = some abs ∧
        Trusted.MirSemantics.getElem? (initLocalsLoopV2 body args 0 body.locals) i = some sl ∧
        AbsSlotSoundV2 mode ty abs sl := by
    intro i ty hTy
    have hGA := initAbsEnvLoopV2_getElem? body 0 body.locals i ty hTy
    have hGL := initLocalsLoopV2_getElem? body args 0 body.locals i ty hTy
    rw [Nat.zero_add] at hGA hGL
    refine ⟨_, _, hGA, hGL, ?_⟩
    cases i with
    | zero =>
      dsimp [initAbsSlotV2, Nat.beq]
      exact liveUninitSlot_absSoundV2 mode ty
    | succ k =>
      dsimp [initAbsSlotV2, Nat.beq]
      cases hLe : Nat.ble (k + 1) body.argumentCount with
      | true =>
        dsimp
        have hKlt : k < body.argumentCount := nat_ble_le hLe
        have hDrop : Trusted.MirSemantics.getElem?
            ((body.locals.drop 1).take body.argumentCount) k = some ty := by
          rw [getElem?_take_drop1 body.locals body.argumentCount k hKlt]
          exact hTy
        let ⟨v, hV, hChk⟩ := checkArgsMatchForMode_getElem? hArgs hDrop
        rw [hV]
        exact ⟨hChk, ⟨v, rfl⟩⟩
      | false =>
        dsimp
        cases hasStorageAnnotationV2 body (k + 1) with
        | true => dsimp; exact ⟨True.intro, True.intro⟩
        | false => dsimp; exact liveUninitSlot_absSoundV2 mode ty
  refine ⟨⟨initLocalsLoopV2_length body args 0 body.locals, ?_⟩,
          initAbsEnvLoopV2_length body 0 body.locals, ?_⟩
  · intro i ty sl hTy hSl
    let ⟨_, sl', _, hSl', hS⟩ := hEach i ty hTy
    rw [hSl] at hSl'; injection hSl' with e; subst e
    exact hS.1
  · intro i ty abs sl hTy hAbs hSl
    let ⟨abs', sl', hAbs', hSl', hS⟩ := hEach i ty hTy
    rw [hAbs] at hAbs'; injection hAbs' with ea; subst ea
    rw [hSl] at hSl'; injection hSl' with es; subst es
    exact hS

private theorem except_ite_err_ok {ε α : Type} {c : Bool} {err : ε}
    {mx : Except ε α} {v : α}
    (h : (if c then .error err else mx) = .ok v) :
    c = false ∧ mx = .ok v := by
  cases c with
  | true => cases h
  | false => exact ⟨rfl, h⟩

private theorem option_ite_none_some {α : Type} {c : Bool}
    {mx : Option α} {v : α}
    (h : (if c then none else mx) = some v) :
    c = false ∧ mx = some v := by
  cases c with
  | true => cases h
  | false => exact ⟨rfl, h⟩

private theorem initStateV2_ok_elim {p : ProgramV2} {q : Query} {s₀ : State}
    (hOk : initStateV2 p q = .ok s₀) :
    ∃ body,
      Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body ∧
      body.basicBlocks.isEmpty = false ∧
      Nat.blt body.argumentCount body.locals.length = true ∧
      storageAnnotationsInBoundsV2 body = true ∧
      checkArgsMatchForMode p.profileMode q.args
        ((body.locals.drop 1).take body.argumentCount) = true ∧
      s₀ = {
        frames := [{
          defId := p.entryDefId
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoopV2 body q.args 0 body.locals
        }]
        callerMem := q.callerMem
      } := by
  unfold initStateV2 at hOk
  dsimp only at hOk
  let ⟨_, hOk1⟩ := except_ite_err_ok hOk
  cases hB : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
  | none => rw [hB] at hOk1; cases hOk1
  | some body =>
    rw [hB] at hOk1; dsimp only at hOk1
    let ⟨hEmp, hOk2⟩ := except_ite_err_ok hOk1
    let ⟨hAL, hOk3⟩ := except_ite_err_ok hOk2
    let ⟨hSB, hOk4⟩ := except_ite_err_ok hOk3
    let ⟨_, hOk5⟩ := except_ite_err_ok hOk4
    let ⟨hArgs, hOk6⟩ := except_ite_err_ok hOk5
    injection hOk6 with eS
    exact ⟨body, rfl, hEmp, bool_not_false hAL, bool_not_false hSB,
           bool_not_false hArgs, eS.symm⟩

private theorem initLocalsLoopV2_eq_of_preservesStorage {b₁ b₂ : BodyV2}
    (args : List Val)
    (hBHdr : bodyHeaderV2Eq b₁ b₂ = true)
    (hPres : preservesAllStorageAnnotationsV2 b₁ b₂ = true) :
    initLocalsLoopV2 b₁ args 0 b₁.locals =
      initLocalsLoopV2 b₂ args 0 b₂.locals := by
  let ⟨hArg, hLoc, _, _⟩ := bodyHeaderV2Eq_elim hBHdr
  let ⟨_, hAt⟩ := preservesAllStorageAnnotationsV2_elim hPres
  rw [← hLoc]
  have hLoop : ∀ base tys,
      base + tys.length = b₁.locals.length →
      initLocalsLoopV2 b₁ args base tys = initLocalsLoopV2 b₂ args base tys := by
    intro base tys hSum
    induction tys generalizing base with
    | nil => rfl
    | cons ty rest ih =>
      dsimp [List.length] at hSum
      have hBaseLt : base < b₁.locals.length := by
        rw [← hSum]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self base)
          (by rw [Nat.add_succ]; exact Nat.succ_le_succ (Nat.le_add_right base rest.length))
      have hSumNext : (base + 1) + rest.length = b₁.locals.length := by
        rw [Nat.add_assoc, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
        exact hSum
      dsimp [initLocalsLoopV2]
      rw [ih (base + 1) hSumNext, ← hArg, hAt base hBaseLt]
  exact hLoop 0 b₁.locals (Nat.zero_add b₁.locals.length)

private theorem ite_else_congr {α : Type} {P : Prop} [Decidable P] {t e₁ e₂ : α}
    (h : e₁ = e₂) :
    (if P then t else e₁) = (if P then t else e₂) := by
  rw [h]

private theorem initStateV2_eq_of_matching_entry {p₁ p₂ : ProgramV2} (q : Query)
    (hHdr : programHeaderV2Eq p₁ p₂ = true)
    (hNone : Trusted.MirSemantics.getElem? p₁.bodies p₁.entryDefId = none ↔
      Trusted.MirSemantics.getElem? p₂.bodies p₂.entryDefId = none)
    (hSome : ∀ b₁, Trusted.MirSemantics.getElem? p₁.bodies p₁.entryDefId = some b₁ →
      ∃ b₂, Trusted.MirSemantics.getElem? p₂.bodies p₂.entryDefId = some b₂ ∧
        bodyHeaderV2Eq b₁ b₂ = true ∧
        b₁.basicBlocks.isEmpty = b₂.basicBlocks.isEmpty ∧
        preservesAllStorageAnnotationsV2 b₁ b₂ = true) :
    initStateV2 p₁ q = initStateV2 p₂ q := by
  let ⟨hPw, hVer, hEnt, _, hPm⟩ := programHeaderV2Eq_elim hHdr
  unfold initStateV2
  rw [hPw, hVer, hPm]
  dsimp only
  apply ite_else_congr
  cases hB₁ : Trusted.MirSemantics.getElem? p₁.bodies p₁.entryDefId with
  | none => rw [hNone.mp hB₁]
  | some b₁ =>
    let ⟨b₂, hB₂, hBHdr, hEmp, hPres⟩ := hSome b₁ hB₁
    let ⟨hArg, hLoc, _, _⟩ := bodyHeaderV2Eq_elim hBHdr
    let ⟨hBnd, _⟩ := preservesAllStorageAnnotationsV2_elim hPres
    have hLoop := initLocalsLoopV2_eq_of_preservesStorage q.args hBHdr hPres
    rw [hB₂]; dsimp only
    rw [hLoop, hEmp, hArg, hLoc, hBnd, hEnt]

private theorem deinitMoveOperandAbsV2_sound {mode : ProfileModeV2} {bodyLocals : List MirTy}
    {env : List AbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {srcTy : MirTy} {optVal : Option Val}
    (hEnv : AbsEnvSoundV2 mode bodyLocals env locals)
    (hEv : evalOperandToSlot bodyLocals locals opnd = .ok (srcTy, optVal, locals')) :
    AbsEnvSoundV2 mode bodyLocals (deinitMoveOperandAbs bodyLocals env opnd) locals' := by
  cases opnd with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEv; cases hEv
    | ok _ =>
      rw [hC] at hEv; injection hEv with q1; injection q1 with _ q2
      injection q2 with _ qL; subst qL; exact hEnv
  | copy p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some _ =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            injection hEv with q1; injection q1 with _ q2
            injection q2 with _ qL; subst qL; exact hEnv
  | move p =>
    dsimp [evalOperandToSlot] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            dsimp at hEv
            cases hSetL : setElem? locals p.localId (liveUninitSlot ty) with
            | none => rw [hSetL] at hEv; cases hEv
            | some locs1 =>
              rw [hSetL] at hEv; injection hEv with q1; injection q1 with _ q2
              injection q2 with _ qL; subst qL
              have hLtE : p.localId < env.length := by
                rw [hEnv.2.1]; exact getElem?_some_lt hTy
              let ⟨env', hSetE⟩ := setElem?_some_of_lt env p.localId
                (if isAlwaysInhabitedZst ty then .liveInit else .liveUninit) hLtE
              dsimp [deinitMoveOperandAbs]
              rw [hP]; dsimp; rw [hTy]; dsimp; rw [hSetE]
              exact absEnvSoundV2_set hEnv hTy hSetE hSetL (liveUninitSlot_absSoundV2 mode ty)

private theorem deinitMovePrimAbsV2_sound {mode : ProfileModeV2} {bodyLocals : List MirTy}
    {env : List AbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {v : Val}
    (hEnv : AbsEnvSoundV2 mode bodyLocals env locals)
    (hEv : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    AbsEnvSoundV2 mode bodyLocals (deinitMoveOperandAbs bodyLocals env opnd) locals' := by
  dsimp [evalPrimitiveOperand] at hEv
  cases hS : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [hS] at hEv; cases hEv
  | ok res =>
    let ⟨ty0, optVal, _⟩ := res
    rw [hS] at hEv; dsimp at hEv
    cases hPr : isPrimitiveReadableTy ty0 with
    | false => rw [hPr] at hEv; cases hEv
    | true =>
      rw [hPr] at hEv; dsimp at hEv
      cases optVal with
      | none => cases hEv
      | some _ =>
        injection hEv with q1; injection q1 with _ qL; subst qL
        exact deinitMoveOperandAbsV2_sound hEnv hS

private theorem deinitMovesInRvalueAbsV2_sound {mode : ProfileModeV2} {bodyLocals : List MirTy}
    {env : List AbsSlot} {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hEnv : AbsEnvSoundV2 mode bodyLocals env locals)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    AbsEnvSoundV2 mode bodyLocals (deinitMovesInRvalueAbs bodyLocals env rv) locals' := by
  cases rv with
  | use o =>
    dsimp [evalRvalue] at hEv
    cases hS : evalOperandToSlot bodyLocals locals o with
    | error _ => rw [hS] at hEv; cases hEv
    | ok res =>
      let ⟨srcTy, optVal, _⟩ := res
      rw [hS] at hEv; dsimp at hEv
      cases hEqTy : MirTy.beq srcTy dstTy with
      | false => rw [hEqTy] at hEv; cases hEv
      | true =>
        rw [hEqTy] at hEv; dsimp at hEv
        cases optVal with
        | none => cases hEv
        | some _ =>
          injection hEv with q1; injection q1 with _ qL; subst qL
          exact deinitMoveOperandAbsV2_sound hEnv hS
  | unaryOp op o =>
    dsimp [evalRvalue] at hEv
    cases hO : evalPrimitiveOperand bodyLocals locals o with
    | error _ => rw [hO] at hEv; cases hEv
    | ok res =>
      let ⟨ov, _⟩ := res
      rw [hO] at hEv; dsimp at hEv
      cases hU : evalUnOp op ov with
      | error _ => rw [hU] at hEv; cases hEv
      | ok _ =>
        rw [hU] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
        exact deinitMovePrimAbsV2_sound hEnv hO
  | binaryOp op l r =>
    dsimp [evalRvalue] at hEv
    cases hL : evalPrimitiveOperand bodyLocals locals l with
    | error _ => rw [hL] at hEv; cases hEv
    | ok resL =>
      let ⟨lv, locs1⟩ := resL
      rw [hL] at hEv; dsimp at hEv
      cases hR : evalPrimitiveOperand bodyLocals locs1 r with
      | error _ => rw [hR] at hEv; cases hEv
      | ok resR =>
        let ⟨rvv, _⟩ := resR
        rw [hR] at hEv; dsimp at hEv
        cases hB : evalBinOp op lv rvv with
        | error _ => rw [hB] at hEv; cases hEv
        | ok _ =>
          rw [hB] at hEv; injection hEv with q1; injection q1 with _ qL2; subst qL2
          exact deinitMovePrimAbsV2_sound (deinitMovePrimAbsV2_sound hEnv hL) hR
  | discriminant p =>
    dsimp [deinitMovesInRvalueAbs]
    dsimp [evalRvalue] at hEv
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases ty with
        | enum ety =>
          cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hSl] at hEv; cases hEv
          | some slot =>
            rw [hSl] at hEv; dsimp at hEv
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEv; cases hEv
            | true =>
              rw [hAdm] at hEv; dsimp at hEv
              cases hTr : ety.tagRepr with
              | zeroSized =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp at hEv
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at hEv; cases hEv
                    | some _ =>
                      rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                      exact hEnv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                          exact hEnv
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
              | scalar _ _ =>
                rw [hTr] at hEv
                cases slot with
                | dead => cases hEv
                | live opt =>
                  cases opt with
                  | none => cases hEv
                  | some val =>
                    cases val with
                    | enumVal ety' k =>
                      dsimp at hEv
                      cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => rw [hC] at hEv; cases hEv
                      | true =>
                        rw [hC] at hEv; dsimp at hEv
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => rw [hD] at hEv; cases hEv
                        | some _ =>
                          rw [hD] at hEv; injection hEv with q1; injection q1 with _ qL; subst qL
                          exact hEnv
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEv

private theorem stepPlainStmtAbsV2_sound {mode : ProfileModeV2} {body : BodyV2}
    {env env' : List AbsSlot} {frame : FrameState}
    {cm : CallerMemory} {stmt : StatementKindV2} {s' : State}
    (hEnv : AbsEnvSoundV2 mode body.locals env frame.locals)
    (hStep : stepPlainStmtAbsV2 body.locals env stmt = some env')
    (hEv : evalStatementV2 mode body frame cm stmt = .step s') :
    ∃ locs',
      s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
             callerMem := cm } ∧
      AbsEnvSoundV2 mode body.locals env' locs' := by
  cases stmt with
  | placeMention p =>
    dsimp [stepPlainStmtAbsV2] at hStep
    injection hStep with eE; subst eE
    dsimp [evalStatementV2] at hEv
    cases hPM : evalPlaceMentionV2 body frame cm p with
    | error _ => rw [hPM] at hEv; cases hEv
    | ok _ =>
      rw [hPM] at hEv; injection hEv with eS; subst eS
      exact ⟨frame.locals, rfl, hEnv⟩
  | assume cond =>
    dsimp [stepPlainStmtAbsV2] at hStep
    injection hStep with eE; subst eE
    dsimp [evalStatementV2] at hEv
    cases hC : evalPrimitiveOperand body.locals frame.locals cond with
    | error _ => rw [hC] at hEv; cases hEv
    | ok pr =>
      let ⟨cv, locs'⟩ := pr
      rw [hC] at hEv
      cases cv with
      | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
      | bool b =>
        cases b with
        | false => cases hEv
        | true =>
          injection hEv with eS; subst eS
          exact ⟨locs', rfl, deinitMovePrimAbsV2_sound hEnv hC⟩
  | v1 s =>
    dsimp [stepPlainStmtAbsV2] at hStep
    unfold evalStatementV2 evalV1StatementInV2 at hEv
    cases s with
    | nop =>
      injection hStep with eE; subst eE
      injection hEv with eS; subst eS
      exact ⟨frame.locals, rfl, hEnv⟩
    | unsupported => cases hEv
    | storageLive id =>
      dsimp [stepPlainStmtAbs] at hStep hEv
      cases hTy : Trusted.MirSemantics.getElem? body.locals id with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep hEv; dsimp at hStep hEv
        cases hSetL : setElem? frame.locals id (liveUninitSlot ty) with
        | none => rw [hSetL] at hEv; cases hEv
        | some locs' =>
          rw [hSetL] at hEv; injection hEv with eS; subst eS
          exact ⟨locs', rfl,
                 absEnvSoundV2_set hEnv hTy hStep hSetL (liveUninitSlot_absSoundV2 mode ty)⟩
    | storageDead id =>
      dsimp [stepPlainStmtAbs] at hStep hEv
      cases hZ : Nat.beq id 0 with
      | true => rw [hZ] at hStep; cases hStep
      | false =>
        rw [hZ] at hStep hEv; dsimp at hStep hEv
        cases hSetL : setElem? frame.locals id .dead with
        | none => rw [hSetL] at hEv; cases hEv
        | some locs' =>
          rw [hSetL] at hEv; injection hEv with eS; subst eS
          have hLt : id < body.locals.length := by
            rw [← hEnv.2.1]
            cases Nat.lt_or_ge id env.length with
            | inl hlt => exact hlt
            | inr hge =>
              rw [setElem?_none_of_ge env id .dead hge] at hStep; cases hStep
          let ⟨ty, hTy⟩ := getElem?_some_of_lt body.locals id hLt
          exact ⟨locs', rfl, absEnvSoundV2_set hEnv hTy hStep hSetL ⟨True.intro, True.intro⟩⟩
    | assign dst rv =>
      dsimp [stepPlainStmtAbs] at hStep hEv
      cases hPE : dst.projection.isEmpty with
      | false => rw [hPE] at hStep; cases hStep
      | true =>
        rw [hPE] at hStep hEv; dsimp at hStep hEv
        cases hDstTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
        | none => rw [hDstTy] at hStep; cases hStep
        | some dstTy =>
          rw [hDstTy] at hStep hEv; dsimp at hEv
          cases hRv : evalRvalue body.locals frame.locals dstTy rv with
          | error _ => rw [hRv] at hEv; cases hEv
          | ok res =>
            let ⟨val, locs1⟩ := res
            rw [hRv] at hEv; dsimp at hEv
            have hEnv1 := deinitMovesInRvalueAbsV2_sound hEnv hRv
            unfold writePlaceV2 at hEv
            cases hChk : checkValForMode mode val dstTy with
            | false => rw [hChk] at hEv; cases hEv
            | true =>
              rw [hChk] at hEv; dsimp at hEv
              cases hSl1 : Trusted.MirSemantics.getElem? locs1 dst.localId with
              | none => rw [hSl1] at hEv; cases hEv
              | some sl1 =>
                rw [hSl1] at hEv
                cases sl1 with
                | dead => cases hEv
                | live _ =>
                  cases hSetL : setElem? locs1 dst.localId (.live (some val)) with
                  | none => rw [hSetL] at hEv; cases hEv
                  | some locsW =>
                    rw [hSetL] at hEv; injection hEv with eS; subst eS
                    exact ⟨locsW, rfl,
                           absEnvSoundV2_set hEnv1 hDstTy hStep hSetL ⟨hChk, ⟨val, rfl⟩⟩⟩

private theorem checkAbsEdge_v2_sound {mode : ProfileModeV2} {bodyLocals : List MirTy}
    {numBlocks : Nat} {cert : BodyAbsCert}
    {edgeEnv : List AbsSlot} {locs' : List LocalSlot} {tgt : BasicBlockId}
    (hEdge : checkAbsEdge numBlocks cert edgeEnv tgt = true)
    (hSound : AbsEnvSoundV2 mode bodyLocals edgeEnv locs')
    (hLt : tgt < numBlocks) :
    ∃ tgtEnv,
      Trusted.MirSemantics.getElem? cert tgt = some (some tgtEnv) ∧
      AbsEnvSoundV2 mode bodyLocals tgtEnv locs' := by
  unfold checkAbsEdge at hEdge
  rw [nat_lt_blt hLt] at hEdge; dsimp at hEdge
  cases hC : Trusted.MirSemantics.getElem? cert tgt with
  | none => rw [hC] at hEdge; cases hEdge
  | some optE =>
    rw [hC] at hEdge
    cases optE with
    | none => cases hEdge
    | some tgtEnv =>
      exact ⟨tgtEnv, rfl, absEnvImplies_soundV2 hEdge hSound⟩

private theorem checkAbsTerminatorEdges_v2_step_sound {mode : ProfileModeV2}
    {bSrc : BodyV2} {bbSrc : BasicBlockV2} {cert : BodyAbsCert}
    {exitEnv : List AbsSlot} {frame : FrameState} {cm : CallerMemory} {s' : State}
    (hEnv : AbsEnvSoundV2 mode bSrc.locals exitEnv frame.locals)
    (hEdges : checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length cert
      exitEnv bbSrc.terminator = true)
    (hEv : evalTerminatorV2 bSrc bbSrc frame cm = .step s') :
    ∃ tgt locs',
      s' = { frames := [{ frame with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
             callerMem := cm } ∧
      (tgt < bSrc.basicBlocks.length →
        ∃ tgtEnv,
          Trusted.MirSemantics.getElem? cert tgt = some (some tgtEnv) ∧
          AbsEnvSoundV2 mode bSrc.locals tgtEnv locs') := by
  unfold evalTerminatorV2 at hEv
  cases hTm : bbSrc.terminator with
  | return_ =>
    rw [hTm] at hEv; dsimp at hEv
    cases hCl : bbSrc.cleanup with
    | true => rw [hCl] at hEv; cases hEv
    | false =>
      rw [hCl] at hEv; dsimp at hEv
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at hEv; cases hEv
      | some sl => rw [h0] at hEv; cases sl with | dead => cases hEv | live o => cases o <;> cases hEv
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    rw [hTm] at hEv; cases hEv
  | goto target =>
    rw [hTm] at hEv hEdges; dsimp [checkAbsTerminatorEdges] at hEv hEdges
    injection hEv with eS; subst eS
    exact ⟨target, frame.locals, rfl, fun hLt => checkAbsEdge_v2_sound hEdges hEnv hLt⟩
  | switchInt discr targets =>
    rw [hTm] at hEv hEdges; dsimp [checkAbsTerminatorEdges] at hEv hEdges
    let ⟨hOw, hBrs⟩ := bool_and_true hEdges
    cases hEvD : evalPrimitiveOperand bSrc.locals frame.locals discr with
    | error _ => rw [hEvD] at hEv; cases hEv
    | ok pr =>
      let ⟨dv, locs'⟩ := pr
      rw [hEvD] at hEv; dsimp at hEv
      have hAfter := deinitMovePrimAbsV2_sound hEnv hEvD
      cases dv with
      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
      | bool bv =>
        dsimp at hEv
        cases hSw : evalBoolSwitchBranches bv targets.otherwise targets.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok tgt =>
          rw [hSw] at hEv; injection hEv with eS; subst eS
          refine ⟨tgt, locs', rfl, fun hLt => ?_⟩
          cases evalBoolSwitchBranches_cases hSw with
          | inr hO => subst hO; exact checkAbsEdge_v2_sound hOw hAfter hLt
          | inl hB =>
            let ⟨cb, hMem⟩ := hB
            have hBr := list_all_mem_true hBrs hMem
            dsimp only at hBr
            exact checkAbsEdge_v2_sound hBr hAfter hLt
      | scalar sv =>
        dsimp at hEv
        cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok tgt =>
          rw [hSw] at hEv; injection hEv with eS; subst eS
          refine ⟨tgt, locs', rfl, fun hLt => ?_⟩
          cases evalSwitchBranches_cases hSw with
          | inr hO =>
            let ⟨hTgtEq, _⟩ := hO
            subst hTgtEq
            exact checkAbsEdge_v2_sound hOw hAfter hLt
          | inl hB =>
            let ⟨cb, hMem⟩ := hB
            have hBr := list_all_mem_true hBrs hMem
            dsimp only at hBr
            exact checkAbsEdge_v2_sound hBr hAfter hLt

/-! #### Part E.3: Theorem 2b — Certified `RemovePlaceMention`
(`removePlaceMention_certified_bidirectional_iff_priv`) -/

private theorem checkVal_rawPtr_not_true {v : Val} {mutbl : Mutability} {pointee : MirTy}
    (h : checkVal v (.rawPtr mutbl pointee) = true) : False := by
  have hTy := checkVal_iff_ty?.mp h
  cases v with
  | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hTy
  | scalar sv =>
    unfold Val.ty? at hTy; dsimp only at hTy
    cases hWf : sv.wf <;> rw [hWf] at hTy <;> cases hTy
  | enumVal ety idx =>
    unfold Val.ty? at hTy; dsimp only at hTy
    cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
      <;> rw [hAdm] at hTy <;> cases hTy

private theorem checkValV2_rawPtr_elim {v : Val} {mutbl : Mutability} {pointee : MirTy}
    (h : checkValForMode .v2Extended v (.rawPtr mutbl pointee) = true) :
    ∃ pv, v = .ptr pv ∧
      IntWidth.beq pv.width .isize = true ∧
      isSupportedProfileV2Ty pointee = true := by
  cases v with
  | ptr pv =>
    unfold checkValForMode checkValV2 at h
    dsimp only at h
    let ⟨h1, h2⟩ := bool_and_true h
    exact ⟨pv, rfl, h1, h2⟩
  | scalar _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ =>
    unfold checkValForMode checkValV2 at h
    dsimp only at h
    exact False.elim (checkVal_rawPtr_not_true h)

private theorem placeMentionCertifiedInEnv_eval_ok {bSrc : BodyV2} {frame : FrameState}
    {cm : CallerMemory} {env : List AbsSlot} {p : PlaceV2}
    (hEnv : AbsEnvSoundV2 .v2Extended bSrc.locals env frame.locals)
    (hCert : placeMentionCertifiedInEnv bSrc.locals env p = true) :
    evalPlaceMentionV2 bSrc frame cm p = .ok () :=
  match p, hCert with
  | .local localId, hCert => by
    unfold placeMentionCertifiedInEnv at hCert
    let ⟨_, hM⟩ := bool_and_true hCert
    dsimp only at hM
    cases hTy : Trusted.MirSemantics.getElem? bSrc.locals localId with
    | none => rw [hTy] at hM; cases hM
    | some ty =>
      rw [hTy] at hM
      cases hAbs : Trusted.MirSemantics.getElem? env localId with
      | none => rw [hAbs] at hM; cases hM
      | some slot =>
        rw [hAbs] at hM
        have hLtL : localId < frame.locals.length := by
          rw [hEnv.1.1]; exact getElem?_some_lt hTy
        let ⟨sl, hSl⟩ := getElem?_some_of_lt frame.locals localId hLtL
        let ⟨_, opt, hSlEq⟩ := absSlotImplies_soundV2 hM
          (hEnv.2.2 localId ty slot sl hTy hAbs hSl)
        subst hSlEq
        unfold evalPlaceMentionV2; dsimp only
        rw [hTy, hSl]
  | .rawDeref ptrLocal, hCert => by
    unfold placeMentionCertifiedInEnv at hCert
    let ⟨_, hM⟩ := bool_and_true hCert
    dsimp only at hM
    cases hTy : Trusted.MirSemantics.getElem? bSrc.locals ptrLocal with
    | none => rw [hTy] at hM; cases hM
    | some ty =>
      rw [hTy] at hM
      cases ty with
      | bool | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | unsupported =>
        cases hM
      | rawPtr mutbl pointee =>
        cases hAbs : Trusted.MirSemantics.getElem? env ptrLocal with
        | none => rw [hAbs] at hM; cases hM
        | some slot =>
          rw [hAbs] at hM
          cases slot with
          | dead | liveUninit => cases hM
          | liveInit =>
            have hLtL : ptrLocal < frame.locals.length := by
              rw [hEnv.1.1]; exact getElem?_some_lt hTy
            let ⟨sl, hSl⟩ := getElem?_some_of_lt frame.locals ptrLocal hLtL
            let ⟨hWtSl, v, hSlEq⟩ :=
              hEnv.2.2 ptrLocal (.rawPtr mutbl pointee) .liveInit sl hTy hAbs hSl
            subst hSlEq
            let ⟨pv, hvEq, hW, hSup⟩ := checkValV2_rawPtr_elim hWtSl
            subst hvEq
            unfold evalPlaceMentionV2; dsimp only
            rw [hTy, hSl]; dsimp
            rw [hW, hSup]; rfl
  | .rawDerefFieldOffset ptrLocal byteOffset, hCert => by
    unfold placeMentionCertifiedInEnv at hCert
    let ⟨hSafe, hM⟩ := bool_and_true hCert
    dsimp [isSafePlaceMention] at hSafe
    dsimp only at hM
    cases hTy : Trusted.MirSemantics.getElem? bSrc.locals ptrLocal with
    | none => rw [hTy] at hM; cases hM
    | some ty =>
      rw [hTy] at hM
      cases ty with
      | bool | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | unsupported =>
        cases hM
      | rawPtr mutbl pointee =>
        cases hAbs : Trusted.MirSemantics.getElem? env ptrLocal with
        | none => rw [hAbs] at hM; cases hM
        | some slot =>
          rw [hAbs] at hM
          cases slot with
          | dead | liveUninit => cases hM
          | liveInit =>
            have hLtL : ptrLocal < frame.locals.length := by
              rw [hEnv.1.1]; exact getElem?_some_lt hTy
            let ⟨sl, hSl⟩ := getElem?_some_of_lt frame.locals ptrLocal hLtL
            let ⟨hWtSl, v, hSlEq⟩ :=
              hEnv.2.2 ptrLocal (.rawPtr mutbl pointee) .liveInit sl hTy hAbs hSl
            subst hSlEq
            let ⟨pv, hvEq, hW, hSup⟩ := checkValV2_rawPtr_elim hWtSl
            subst hvEq
            unfold evalPlaceMentionV2; dsimp only
            rw [hTy, hSl]; dsimp
            rw [hW, hSup, hSafe]; rfl

private theorem evalStatementV2_eq_of_locals_eq {mode : ProfileModeV2}
    {b₁ b₂ : BodyV2} {frame : FrameState} {cm : CallerMemory}
    (stmt : StatementKindV2) (hLoc : b₁.locals = b₂.locals) :
    evalStatementV2 mode b₁ frame cm stmt =
      evalStatementV2 mode b₂ frame cm stmt := by
  cases stmt with
  | v1 s =>
    unfold evalStatementV2 evalV1StatementInV2
    cases s <;> dsimp <;> rw [hLoc]
  | placeMention p =>
    refine match p with
      | .local _ => by unfold evalStatementV2 evalPlaceMentionV2; dsimp; rw [hLoc]
      | .rawDeref _ => by unfold evalStatementV2 evalPlaceMentionV2; dsimp; rw [hLoc]
      | .rawDerefFieldOffset _ _ => by unfold evalStatementV2 evalPlaceMentionV2; dsimp; rw [hLoc]
  | assume cond =>
    unfold evalStatementV2; dsimp; rw [hLoc]

private theorem evalTerminatorV2_eq_of_eq {b₁ b₂ : BodyV2} {bb₁ bb₂ : BasicBlockV2}
    {frame : FrameState} {cm : CallerMemory}
    (hLoc : b₁.locals = b₂.locals)
    (hCl : bb₁.cleanup = bb₂.cleanup)
    (hTm : bb₁.terminator = bb₂.terminator) :
    evalTerminatorV2 b₁ bb₁ frame cm = evalTerminatorV2 b₂ bb₂ frame cm := by
  unfold evalTerminatorV2
  rw [hLoc, hCl, hTm]

private theorem stepRemovePlaceMentionCertStmts_length {bodyLocals : List MirTy} :
    ∀ {env exitEnv : List AbsSlot} {ss₁ ss₂ : List StatementKindV2},
      stepRemovePlaceMentionCertStmts bodyLocals env ss₁ ss₂ = some exitEnv →
      ss₁.length = ss₂.length := by
  intro env exitEnv ss₁
  induction ss₁ generalizing env with
  | nil =>
    intro ss₂ h
    cases ss₂ with
    | nil => rfl
    | cons _ _ => cases h
  | cons s₁ r₁ ih =>
    intro ss₂ h
    cases ss₂ with
    | nil => cases h
    | cons s₂ r₂ =>
      dsimp [stepRemovePlaceMentionCertStmts] at h
      let ⟨_, hRem⟩ := option_ite_none_some h
      cases hSt : stepPlainStmtAbsV2 bodyLocals env s₁ with
      | none => rw [hSt] at hRem; cases hRem
      | some env' =>
        rw [hSt] at hRem
        dsimp [List.length]; rw [ih hRem]

private theorem checkRemovePlaceMentionBlocks_get {bSrc bTgt : BodyV2}
    {cert : BodyAbsCert} :
    ∀ {base k : Nat} {bbs : List BasicBlockV2} {bbSrc : BasicBlockV2}
      {entryEnv : List AbsSlot},
      checkRemovePlaceMentionBlocks bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      Trusted.MirSemantics.getElem? cert (base + k) = some (some entryEnv) →
      ∃ bbTgt exitEnv,
        Trusted.MirSemantics.getElem? bTgt.basicBlocks (base + k) = some bbTgt ∧
        bbSrc.cleanup = bbTgt.cleanup ∧
        bbSrc.terminator = bbTgt.terminator ∧
        stepRemovePlaceMentionCertStmts bSrc.locals entryEnv
          bbSrc.statements bbTgt.statements = some exitEnv ∧
        checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length cert
          exitEnv bbSrc.terminator = true := by
  intro base k bbs
  induction bbs generalizing base k with
  | nil => intro _ _ _ hG _; cases hG
  | cons bb₀ rest ih =>
    intro bbSrc entryEnv hLoop hG hC
    dsimp [checkRemovePlaceMentionBlocks] at hLoop
    let ⟨hHere, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hG with e; subst e
      rw [Nat.add_zero] at hC
      rw [Nat.add_zero]
      rw [hC] at hHere
      cases hBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks base with
      | none => rw [hBT] at hHere; cases hHere
      | some bbTgt =>
        rw [hBT] at hHere; dsimp only at hHere
        let ⟨h123, hStM⟩ := bool_and_true hHere
        let ⟨h12, hTmB⟩ := bool_and_true h123
        let ⟨_, hClB⟩ := bool_and_true h12
        cases hSt : stepRemovePlaceMentionCertStmts bSrc.locals entryEnv
            bb₀.statements bbTgt.statements with
        | none => rw [hSt] at hStM; cases hStM
        | some exitEnv =>
          rw [hSt] at hStM
          exact ⟨bbTgt, exitEnv, rfl, bool_beq_eq hClB, terminatorEq_eq hTmB,
                 hSt, hStM⟩
    | succ m =>
      have hAdd : (base + 1) + m = base + (m + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 m]
      rw [← hAdd] at hC
      have hSub := ih hTail hG hC
      rw [hAdd] at hSub
      exact hSub

private noncomputable def RemovePlaceMentionInv (cert : ProgramAbsCert)
    (pSrc pTgt : ProgramV2) (s : State) : Prop :=
  ∃ f bCert bSrc bTgt,
    s.frames = [f] ∧
    pSrc.profileMode = .v2Extended ∧
    pTgt.profileMode = .v2Extended ∧
    Trusted.MirSemantics.getElem? cert f.defId = some bCert ∧
    Trusted.MirSemantics.getElem? pSrc.bodies f.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies f.defId = some bTgt ∧
    checkRemovePlaceMentionBody bCert bSrc bTgt = true ∧
    (f.blockIdx < bSrc.basicBlocks.length →
      ∃ bbSrc bbTgt env exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks f.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks f.blockIdx = some bbTgt ∧
        bbSrc.cleanup = bbTgt.cleanup ∧
        bbSrc.terminator = bbTgt.terminator ∧
        bbSrc.statements.length = bbTgt.statements.length ∧
        stepRemovePlaceMentionCertStmts bSrc.locals env
          (bbSrc.statements.drop f.stmtIdx)
          (bbTgt.statements.drop f.stmtIdx) = some exitEnv ∧
        checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length bCert
          exitEnv bbSrc.terminator = true ∧
        AbsEnvSoundV2 .v2Extended bSrc.locals env f.locals)

private theorem removePlaceMention_query_iff {cert : ProgramAbsCert}
    {pSrc pTgt : ProgramV2}
    (hCert : checkRemovePlaceMentionProgram cert pSrc pTgt = true)
    (q : Query) :
    (WellFormedV2 pTgt q ↔ WellFormedV2 pSrc q) ∧
    (∀ out : TerminalOut, BehaviorV2 pTgt q out ↔ BehaviorV2 pSrc q out) ∧
    (∀ k : FaultKindV2,
      ReachesResultV2 pTgt q (.fault k) ↔ ReachesResultV2 pSrc q (.fault k)) ∧
    (DivergesV2 pTgt q ↔ DivergesV2 pSrc q) := by
  let ⟨h12P, hZipC⟩ := bool_and_true hCert
  let ⟨hRel, hCLenB⟩ := bool_and_true h12P
  have hCLen := nat_beq_eq hCLenB
  let ⟨h12R, hBodiesR⟩ := bool_and_true hRel
  let ⟨hHdr, hPmB⟩ := bool_and_true h12R
  have hPmS := profileModeEq_eq hPmB
  let ⟨_, _, hEnt, _, hPmEq⟩ := programHeaderV2Eq_elim hHdr
  have hPmT : pTgt.profileMode = .v2Extended := hPmEq.symm.trans hPmS
  have hInitEq : initStateV2 pSrc q = initStateV2 pTgt q := by
    apply initStateV2_eq_of_matching_entry q hHdr
    · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodiesR
    · intro b₁ hB₁
      let ⟨_, b₂, _, hB₂, hChkB⟩ := listRel_zip_getElem? hCLen hZipC hB₁
      rw [hEnt] at hB₂
      let ⟨h12345, _⟩ := bool_and_true hChkB
      let ⟨h1234, _⟩ := bool_and_true h12345
      let ⟨h123, hBBLenB⟩ := bool_and_true h1234
      let ⟨h12, _⟩ := bool_and_true h123
      let ⟨hBHdr, hPres⟩ := bool_and_true h12
      exact ⟨b₂, hB₂, hBHdr, list_isEmpty_eq_of_length (nat_beq_eq hBBLenB), hPres⟩
  apply lockstep_inv_v2_query_iff (Inv := RemovePlaceMentionInv cert pSrc pTgt) hInitEq
  · intro s₀ hOk
    let ⟨bSrc, hBS, hNotEmp, _, _, hArgs, hs0⟩ := initStateV2_ok_elim hOk
    subst hs0
    rw [hPmS] at hArgs
    let ⟨bCert, bTgt, hBC, hBT, hChkB⟩ := listRel_zip_getElem? hCLen hZipC hBS
    let ⟨h12345, hBlkLoop⟩ := bool_and_true hChkB
    let ⟨_, hEntry0⟩ := bool_and_true h12345
    rw [if_bool_false hNotEmp] at hEntry0
    cases hC0 : Trusted.MirSemantics.getElem? bCert 0 with
    | none => rw [hC0] at hEntry0; cases hEntry0
    | some opt0 =>
      rw [hC0] at hEntry0
      cases opt0 with
      | none => cases hEntry0
      | some env₀ =>
        have hEnv0 := absEnvImplies_soundV2 hEntry0 (initAbsEnvLoopV2_sound hArgs)
        refine ⟨_, bCert, bSrc, bTgt, rfl, hPmS, hPmT, hBC, hBS, hBT, hChkB, ?_⟩
        intro h0Lt
        let ⟨bbSrc0, hBBS0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
        let ⟨bbTgt0, exitE0, hBBT0, hCl0, hTm0, hSt0, hEdg0⟩ :=
          checkRemovePlaceMentionBlocks_get hBlkLoop hBBS0 hC0
        exact ⟨bbSrc0, bbTgt0, env₀, exitE0, hBBS0, hBBT0, hCl0, hTm0,
               stepRemovePlaceMentionCertStmts_length hSt0, hSt0, hEdg0, hEnv0⟩
  · intro s hInv
    let ⟨f, bCert, bSrc, bTgt, hFr, _, _, hBC, hBS, hBT, hChkB, hBlkInv⟩ := hInv
    let ⟨h12345, hBlkLoop⟩ := bool_and_true hChkB
    let ⟨h1234, _⟩ := bool_and_true h12345
    let ⟨h123, hBBLenB⟩ := bool_and_true h1234
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hBHdr, _⟩ := bool_and_true h12
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderV2Eq_elim hBHdr
    have hBBLen := nat_beq_eq hBBLenB
    cases s with
    | mk frames cm =>
      dsimp at hFr; subst hFr
      cases Nat.lt_or_ge f.blockIdx bSrc.basicBlocks.length with
      | inr hGe =>
        have hGeT : bTgt.basicBlocks.length ≤ f.blockIdx := by rw [← hBBLen]; exact hGe
        refine ⟨?_, fun s' hSt => ?_⟩
        · unfold evalStepV2; dsimp
          rw [hBS, hBT]; dsimp
          rw [getElem?_none_of_ge hGe, getElem?_none_of_ge hGeT]
        · unfold evalStepV2 at hSt; dsimp at hSt
          rw [hBS] at hSt; dsimp at hSt
          rw [getElem?_none_of_ge hGe] at hSt; cases hSt
      | inl hLt =>
        let ⟨bbSrc, bbTgt, env, exitEnv, hBBS, hBBT, hClEq, hTmEq,
             hStLenEq, hStRem, hEdg, hEnvS⟩ := hBlkInv hLt
        cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements f.stmtIdx with
        | some sSrc =>
          have hDropS := drop_eq_cons_of_getElem? hStS
          rw [hDropS] at hStRem
          cases hDropT : bbTgt.statements.drop f.stmtIdx with
          | nil => rw [hDropT] at hStRem; cases hStRem
          | cons sTgt restTgt =>
            rw [hDropT] at hStRem
            let ⟨hStT, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
            dsimp [stepRemovePlaceMentionCertStmts] at hStRem
            let ⟨hNotOkF, hStRem2⟩ := option_ite_none_some hStRem
            have hOkH := bool_not_false hNotOkF
            cases hSt1 : stepPlainStmtAbsV2 bSrc.locals env sSrc with
            | none => rw [hSt1] at hStRem2; cases hStRem2
            | some env' =>
              rw [hSt1] at hStRem2
              have hEvStmtEq : evalStatementV2 .v2Extended bSrc f cm sSrc =
                  evalStatementV2 .v2Extended bTgt f cm sTgt := by
                cases sSrc with
                | v1 sv1 =>
                  dsimp at hOkH
                  have hEq := stmtV2Eq_eq hOkH
                  rw [← hEq]
                  exact evalStatementV2_eq_of_locals_eq (.v1 sv1) hLocEq
                | assume cond =>
                  dsimp at hOkH
                  have hEq := stmtV2Eq_eq hOkH
                  rw [← hEq]
                  exact evalStatementV2_eq_of_locals_eq (.assume cond) hLocEq
                | placeMention pm =>
                  cases sTgt with
                  | placeMention pm2 =>
                    dsimp at hOkH
                    have hEq := stmtV2Eq_eq hOkH
                    rw [← hEq]
                    exact evalStatementV2_eq_of_locals_eq (.placeMention pm) hLocEq
                  | assume _ => dsimp at hOkH; cases hOkH
                  | v1 sv2 =>
                    cases sv2 with
                    | assign _ _ | storageLive _ | storageDead _ | unsupported =>
                      dsimp at hOkH; cases hOkH
                    | nop =>
                      dsimp at hOkH
                      dsimp [evalStatementV2, evalV1StatementInV2]
                      rw [placeMentionCertifiedInEnv_eval_ok hEnvS hOkH]
              have hStepEq : evalStepV2 pSrc 0 { frames := [f], callerMem := cm } =
                  evalStepV2 pTgt 0 { frames := [f], callerMem := cm } := by
                unfold evalStepV2; dsimp
                rw [hBS, hBT]; dsimp
                rw [hBBS, hBBT]; dsimp
                rw [hStS, hStT]; dsimp
                rw [hPmS, hPmT]
                exact hEvStmtEq
              refine ⟨hStepEq, fun s' hStepS => ?_⟩
              unfold evalStepV2 at hStepS; dsimp at hStepS
              rw [hBS] at hStepS; dsimp at hStepS
              rw [hBBS] at hStepS; dsimp at hStepS
              rw [hStS] at hStepS; dsimp at hStepS
              rw [hPmS] at hStepS
              let ⟨locs', hs', hEnv'⟩ := stepPlainStmtAbsV2_sound hEnvS hSt1 hStepS
              subst hs'
              refine ⟨_, bCert, bSrc, bTgt, rfl, hPmS, hPmT, hBC, hBS, hBT, hChkB,
                      fun _ => ?_⟩
              refine ⟨bbSrc, bbTgt, env', exitEnv, hBBS, hBBT, hClEq, hTmEq,
                      hStLenEq, ?_, hEdg, hEnv'⟩
              dsimp
              rw [(getElem?_of_drop_eq_cons hDropS).2, hDropTNext]
              exact hStRem2
        | none =>
          have hGeS := getElem?_none_ge hStS
          have hDropSNil := drop_eq_nil_of_ge hGeS
          have hDropTNil := drop_eq_nil_of_ge (by rw [← hStLenEq]; exact hGeS)
          rw [hDropSNil, hDropTNil] at hStRem
          injection hStRem with eEnv; subst eEnv
          have hStTNone := getElem?_none_of_ge (by rw [← hStLenEq]; exact hGeS)
          have hStepEq : evalStepV2 pSrc 0 { frames := [f], callerMem := cm } =
              evalStepV2 pTgt 0 { frames := [f], callerMem := cm } := by
            unfold evalStepV2; dsimp
            rw [hBS, hBT]; dsimp
            rw [hBBS, hBBT]; dsimp
            rw [hStS, hStTNone]; dsimp
            rw [hStLenEq]
            cases Nat.beq f.stmtIdx bbTgt.statements.length with
            | false => rfl
            | true =>
              dsimp
              exact evalTerminatorV2_eq_of_eq hLocEq hClEq hTmEq
          refine ⟨hStepEq, fun s' hStepS => ?_⟩
          unfold evalStepV2 at hStepS; dsimp at hStepS
          rw [hBS] at hStepS; dsimp at hStepS
          rw [hBBS] at hStepS; dsimp at hStepS
          rw [hStS] at hStepS; dsimp at hStepS
          cases hEnd : Nat.beq f.stmtIdx bbSrc.statements.length with
          | false => rw [hEnd] at hStepS; cases hStepS
          | true =>
            rw [hEnd] at hStepS; dsimp at hStepS
            let ⟨tgt, locs', hs', hTgtCert⟩ :=
              checkAbsTerminatorEdges_v2_step_sound hEnvS hEdg hStepS
            subst hs'
            refine ⟨_, bCert, bSrc, bTgt, rfl, hPmS, hPmT, hBC, hBS, hBT, hChkB, ?_⟩
            intro hTgtLt
            let ⟨tgtEnv, hCTgt, hTgtEnvS⟩ := hTgtCert hTgtLt
            let ⟨bbNextS, hBBNS⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt hTgtLt
            have hCTgt0 : Trusted.MirSemantics.getElem? bCert (0 + tgt) =
                some (some tgtEnv) := by
              rw [Nat.zero_add]; exact hCTgt
            let ⟨bbNextT, nextExit, hBBNT, hClN, hTmN, hStN, hEdgN⟩ :=
              checkRemovePlaceMentionBlocks_get hBlkLoop hBBNS hCTgt0
            rw [Nat.zero_add] at hBBNT
            exact ⟨bbNextS, bbNextT, tgtEnv, nextExit, hBBNS, hBBNT, hClN, hTmN,
                   stepRemovePlaceMentionCertStmts_length hStN, hStN, hEdgN, hTgtEnvS⟩

private theorem removePlaceMention_certified_bidirectional_iff_priv
    (pSrc pTgt : ProgramV2) (cert : ProgramAbsCert)
    (hCert : checkRemovePlaceMentionProgram cert pSrc pTgt = true) :
    FullSemanticEquivV2 pSrc pTgt := by
  let ⟨h12P, hZipC⟩ := bool_and_true hCert
  let ⟨hRel, hCLenB⟩ := bool_and_true h12P
  have hCLen := nat_beq_eq hCLenB
  let ⟨h12R, hBodiesR⟩ := bool_and_true hRel
  let ⟨hHdr, hPmB⟩ := bool_and_true h12R
  apply fullSemanticEquivV2_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨_, bTgt', _, hBT', hChkB⟩ := listRel_zip_getElem? hCLen hZipC hBS
    rw [hBT] at hBT'; injection hBT' with eB; subst eB
    let ⟨h12345, _⟩ := bool_and_true hChkB
    let ⟨h1234, _⟩ := bool_and_true h12345
    let ⟨h123, hBBLenB⟩ := bool_and_true h1234
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hBHdr, hPres⟩ := bool_and_true h12
    exact ⟨hBHdr, list_isEmpty_eq_of_length (nat_beq_eq hBBLenB),
           (preservesAllStorageAnnotationsV2_elim hPres).1⟩
  · exact removePlaceMention_query_iff hCert
  · intro defId args
    have hHdrE := programHeaderV2Eq_entryProgV2 defId hHdr
    have hRelE : isRemovePlaceMentionProgram
        (entryProgForBodyV2 pSrc defId) (entryProgForBodyV2 pTgt defId) = true :=
      bool_and_intro (bool_and_intro hHdrE hPmB) hBodiesR
    have hCertE : checkRemovePlaceMentionProgram cert
        (entryProgForBodyV2 pSrc defId) (entryProgForBodyV2 pTgt defId) = true :=
      bool_and_intro (bool_and_intro hRelE hCLenB) hZipC
    exact (removePlaceMention_query_iff hCertE { args := args }).1

/-! #### Part E.4: Theorem 2c — Certified `UnreachablePropagation` `SwitchInt
-> .assume` (`unreachableProp_switchBoolToAssume_bidirectional_iff_priv`) -/

private inductive MacroStepOutcome (pSrc pTgt : ProgramV2) (Inv : State → Prop)
    (s : State) : Prop where
  | step11 (s' : State) :
      evalStepV2 pSrc 0 s = .step s' →
      evalStepV2 pTgt 0 s = .step s' →
      Inv s' →
      MacroStepOutcome pSrc pTgt Inv s
  | step12 (tMid s' : State) :
      evalStepV2 pSrc 0 s = .step s' →
      evalStepV2 pTgt 0 s = .step tMid →
      evalStepV2 pTgt 0 tMid = .step s' →
      Inv s' →
      MacroStepOutcome pSrc pTgt Inv s
  | done11 (out : TerminalOut) :
      evalStepV2 pSrc 0 s = .done out →
      evalStepV2 pTgt 0 s = .done out →
      MacroStepOutcome pSrc pTgt Inv s
  | fault11 (k : FaultKindV2) :
      evalStepV2 pSrc 0 s = .fault k →
      evalStepV2 pTgt 0 s = .fault k →
      MacroStepOutcome pSrc pTgt Inv s
  | fault21 (sMid : State) (k : FaultKindV2) :
      evalStepV2 pSrc 0 s = .step sMid →
      evalStepV2 pSrc 0 sMid = .fault k →
      evalStepV2 pTgt 0 s = .fault k →
      MacroStepOutcome pSrc pTgt Inv s

private theorem macroStep_same {pSrc pTgt : ProgramV2} {Inv : State → Prop} {s : State}
    (hEq : evalStepV2 pSrc 0 s = evalStepV2 pTgt 0 s)
    (hNext : ∀ s', evalStepV2 pSrc 0 s = .step s' → Inv s') :
    MacroStepOutcome pSrc pTgt Inv s := by
  cases hEv : evalStepV2 pSrc 0 s with
  | step s' =>
    exact .step11 s' hEv (hEq.symm.trans hEv) (hNext s' hEv)
  | done out =>
    exact .done11 out hEv (hEq.symm.trans hEv)
  | fault k =>
    exact .fault11 k hEv (hEq.symm.trans hEv)

private theorem macro_step_v2_query_iff {pSrc pTgt : ProgramV2} {q : Query}
    {Inv : State → Prop}
    (hInit : initStateV2 pSrc q = initStateV2 pTgt q)
    (hInv0 : ∀ s₀, initStateV2 pSrc q = .ok s₀ → Inv s₀)
    (hStep : ∀ s, Inv s → MacroStepOutcome pSrc pTgt Inv s) :
    (WellFormedV2 pTgt q ↔ WellFormedV2 pSrc q) ∧
    (∀ out : TerminalOut, BehaviorV2 pTgt q out ↔ BehaviorV2 pSrc q out) ∧
    (∀ k : FaultKindV2,
      ReachesResultV2 pTgt q (.fault k) ↔ ReachesResultV2 pSrc q (.fault k)) ∧
    (DivergesV2 pTgt q ↔ DivergesV2 pSrc q) := by
  cases hInitS : initStateV2 pSrc q with
  | error k₀ =>
    have hInitT : initStateV2 pTgt q = .error k₀ := by rw [← hInit]; exact hInitS
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold WellFormedV2; rw [hInitS, hInitT]
      constructor <;> (intro ⟨⟨_, h, _⟩, _⟩; cases h)
    · intro out; unfold BehaviorV2 ReachesResultV2; rw [hInitS, hInitT]
    · intro k; unfold ReachesResultV2; rw [hInitS, hInitT]
    · unfold DivergesV2; rw [hInitS, hInitT]
      constructor <;> (intro ⟨_, h, _⟩; cases h)
  | ok s₀ =>
    have hInitT : initStateV2 pTgt q = .ok s₀ := by rw [← hInit]; exact hInitS
    have hI0 := hInv0 s₀ hInitS
    have hReachSrc : ∀ s, ReachesV2 pSrc s₀ s →
        (Inv s ∧ ReachesV2 pTgt s₀ s) ∨
        (∃ t k, ReachesV2 pTgt s₀ t ∧
          evalStepV2 pTgt 0 t = .fault k ∧
          evalStepV2 pSrc 0 s = .fault k) := by
      intro s hRS
      induction hRS with
      | refl => exact Or.inl ⟨hI0, ReachesV2.refl s₀⟩
      | tail _ hSt ih =>
        have hEvS := stepV2_iff_evalStepV2.mp hSt
        cases ih with
        | inr hF =>
          let ⟨_, _, _, _, hFS⟩ := hF
          rw [hFS] at hEvS; cases hEvS
        | inl hOk =>
          let ⟨hIs, hRT⟩ := hOk
          cases hStep _ hIs with
          | step11 s' hS hT hI' =>
            rw [hS] at hEvS; injection hEvS with e; subst e
            exact Or.inl ⟨hI', ReachesV2.tail hRT (stepV2_iff_evalStepV2.mpr hT)⟩
          | step12 tMid s' hS hT1 hT2 hI' =>
            rw [hS] at hEvS; injection hEvS with e; subst e
            have hRT1 := ReachesV2.tail hRT (stepV2_iff_evalStepV2.mpr hT1)
            exact Or.inl ⟨hI', ReachesV2.tail hRT1 (stepV2_iff_evalStepV2.mpr hT2)⟩
          | done11 _ hS _ =>
            rw [hS] at hEvS; cases hEvS
          | fault11 _ hS _ =>
            rw [hS] at hEvS; cases hEvS
          | fault21 sMid k hS1 hS2 hT =>
            rw [hS1] at hEvS; injection hEvS with e; subst e
            exact Or.inr ⟨_, k, hRT, hT, hS2⟩
    have hReachTgt : ∀ t, ReachesV2 pTgt s₀ t →
        (Inv t ∧ ReachesV2 pSrc s₀ t) ∨
        (∃ s', evalStepV2 pTgt 0 t = .step s' ∧ Inv s' ∧ ReachesV2 pSrc s₀ s') := by
      intro t hRT
      induction hRT with
      | refl => exact Or.inl ⟨hI0, ReachesV2.refl s₀⟩
      | tail _ hSt ih =>
        have hEvT := stepV2_iff_evalStepV2.mp hSt
        cases ih with
        | inr hMid =>
          let ⟨s', hTMid, hIs', hRS'⟩ := hMid
          rw [hTMid] at hEvT; injection hEvT with e; subst e
          exact Or.inl ⟨hIs', hRS'⟩
        | inl hOk =>
          let ⟨hIt, hRS⟩ := hOk
          cases hStep _ hIt with
          | step11 s' hS hT hI' =>
            rw [hT] at hEvT; injection hEvT with e; subst e
            exact Or.inl ⟨hI', ReachesV2.tail hRS (stepV2_iff_evalStepV2.mpr hS)⟩
          | step12 tMid s' hS hT1 hT2 hI' =>
            rw [hT1] at hEvT; injection hEvT with e; subst e
            exact Or.inr ⟨s', hT2, hI', ReachesV2.tail hRS (stepV2_iff_evalStepV2.mpr hS)⟩
          | done11 _ _ hT =>
            rw [hT] at hEvT; cases hEvT
          | fault11 _ _ hT =>
            rw [hT] at hEvT; cases hEvT
          | fault21 _ _ _ _ hT =>
            rw [hT] at hEvT; cases hEvT
    have hBehIff : ∀ out : TerminalOut,
        BehaviorV2 pTgt q out ↔ BehaviorV2 pSrc q out := by
      intro out
      unfold BehaviorV2 ReachesResultV2; rw [hInitS, hInitT]
      constructor
      · intro ⟨t, hRT, hStT⟩
        have hEvT := stepV2_iff_evalStepV2.mp hStT
        cases hReachTgt t hRT with
        | inr hMid =>
          let ⟨_, hTMid, _, _⟩ := hMid
          rw [hTMid] at hEvT; cases hEvT
        | inl hOk =>
          let ⟨hIt, hRS⟩ := hOk
          cases hStep t hIt with
          | step11 _ _ hT _ => rw [hT] at hEvT; cases hEvT
          | step12 _ _ _ hT1 _ _ => rw [hT1] at hEvT; cases hEvT
          | done11 o hS hT =>
            rw [hT] at hEvT; injection hEvT with e; subst e
            exact ⟨t, hRS, stepV2_iff_evalStepV2.mpr hS⟩
          | fault11 _ _ hT => rw [hT] at hEvT; cases hEvT
          | fault21 _ _ _ _ hT => rw [hT] at hEvT; cases hEvT
      · intro ⟨s, hRS, hStS⟩
        have hEvS := stepV2_iff_evalStepV2.mp hStS
        cases hReachSrc s hRS with
        | inr hF =>
          let ⟨_, _, _, _, hFS⟩ := hF
          rw [hFS] at hEvS; cases hEvS
        | inl hOk =>
          let ⟨hIs, hRT⟩ := hOk
          cases hStep s hIs with
          | step11 _ hS _ _ => rw [hS] at hEvS; cases hEvS
          | step12 _ _ hS _ _ _ => rw [hS] at hEvS; cases hEvS
          | done11 o hS hT =>
            rw [hS] at hEvS; injection hEvS with e; subst e
            exact ⟨s, hRT, stepV2_iff_evalStepV2.mpr hT⟩
          | fault11 _ hS _ => rw [hS] at hEvS; cases hEvS
          | fault21 _ _ hS1 _ _ => rw [hS1] at hEvS; cases hEvS
    have hFaultIff : ∀ k : FaultKindV2,
        ReachesResultV2 pTgt q (.fault k) ↔ ReachesResultV2 pSrc q (.fault k) := by
      intro k
      unfold ReachesResultV2; rw [hInitS, hInitT]
      constructor
      · intro ⟨t, hRT, hStT⟩
        have hEvT := stepV2_iff_evalStepV2.mp hStT
        cases hReachTgt t hRT with
        | inr hMid =>
          let ⟨_, hTMid, _, _⟩ := hMid
          rw [hTMid] at hEvT; cases hEvT
        | inl hOk =>
          let ⟨hIt, hRS⟩ := hOk
          cases hStep t hIt with
          | step11 _ _ hT _ => rw [hT] at hEvT; cases hEvT
          | step12 _ _ _ hT1 _ _ => rw [hT1] at hEvT; cases hEvT
          | done11 _ _ hT => rw [hT] at hEvT; cases hEvT
          | fault11 kf hS hT =>
            rw [hT] at hEvT; injection hEvT with e; subst e
            exact ⟨t, hRS, stepV2_iff_evalStepV2.mpr hS⟩
          | fault21 sMid kf hS1 hS2 hT =>
            rw [hT] at hEvT; injection hEvT with e; subst e
            exact ⟨sMid, ReachesV2.tail hRS (stepV2_iff_evalStepV2.mpr hS1),
                   stepV2_iff_evalStepV2.mpr hS2⟩
      · intro ⟨s, hRS, hStS⟩
        have hEvS := stepV2_iff_evalStepV2.mp hStS
        cases hReachSrc s hRS with
        | inr hF =>
          let ⟨t, kf, hRT, hFT, hFS⟩ := hF
          rw [hFS] at hEvS; injection hEvS with e; subst e
          exact ⟨t, hRT, stepV2_iff_evalStepV2.mpr hFT⟩
        | inl hOk =>
          let ⟨hIs, hRT⟩ := hOk
          cases hStep s hIs with
          | step11 _ hS _ _ => rw [hS] at hEvS; cases hEvS
          | step12 _ _ hS _ _ _ => rw [hS] at hEvS; cases hEvS
          | done11 _ hS _ => rw [hS] at hEvS; cases hEvS
          | fault11 kf hS hT =>
            rw [hS] at hEvS; injection hEvS with e; subst e
            exact ⟨s, hRT, stepV2_iff_evalStepV2.mpr hT⟩
          | fault21 _ _ hS1 _ _ => rw [hS1] at hEvS; cases hEvS
    refine ⟨?_, hBehIff, hFaultIff, ?_⟩
    · unfold WellFormedV2; rw [hInitS, hInitT]
      constructor
      · intro ⟨_, hNF⟩
        exact ⟨⟨s₀, rfl, fun _ _ => ⟨0, rfl⟩⟩, fun k hFS => hNF k ((hFaultIff k).mpr hFS)⟩
      · intro ⟨_, hNF⟩
        exact ⟨⟨s₀, rfl, fun _ _ => ⟨0, rfl⟩⟩, fun k hFT => hNF k ((hFaultIff k).mp hFT)⟩
    · unfold DivergesV2; rw [hInitS, hInitT]
      constructor
      · intro ⟨t₀, hOkT, trT, h0T, hTrT⟩
        injection hOkT with eT; subst eT
        have hEvTrT : ∀ j, evalStepV2 pTgt 0 (trT j) = .step (trT (j + 1)) :=
          fun j => stepV2_iff_evalStepV2.mp (hTrT j)
        have hSync : ∀ m, ∃ j, Inv (iterStateV2 pSrc s₀ m) ∧
            iterStateV2 pSrc s₀ m = trT j := by
          intro m
          induction m with
          | zero => exact ⟨0, hI0, h0T.symm⟩
          | succ m' ih =>
            let ⟨j, hIm, hEqJ⟩ := ih
            cases hStep (iterStateV2 pSrc s₀ m') hIm with
            | step11 s' hS hT hI' =>
              have hNextS : iterStateV2 pSrc s₀ (m' + 1) = s' := by
                dsimp [iterStateV2]; rw [hS]
              rw [hEqJ, hEvTrT j] at hT; injection hT with e1
              rw [hNextS]
              exact ⟨j + 1, hI', e1.symm⟩
            | step12 tMid s' hS hT1 hT2 hI' =>
              have hNextS : iterStateV2 pSrc s₀ (m' + 1) = s' := by
                dsimp [iterStateV2]; rw [hS]
              rw [hEqJ, hEvTrT j] at hT1; injection hT1 with eMid
              rw [← eMid, hEvTrT (j + 1)] at hT2; injection hT2 with e2
              rw [hNextS]
              exact ⟨j + 2, hI', e2.symm⟩
            | done11 _ _ hT =>
              rw [hEqJ, hEvTrT j] at hT; cases hT
            | fault11 _ _ hT =>
              rw [hEqJ, hEvTrT j] at hT; cases hT
            | fault21 _ _ _ _ hT =>
              rw [hEqJ, hEvTrT j] at hT; cases hT
        refine ⟨s₀, rfl, iterStateV2 pSrc s₀, rfl, fun m => ?_⟩
        let ⟨j, hIm, hEqJ⟩ := hSync m
        apply stepV2_iff_evalStepV2.mpr
        cases hStep (iterStateV2 pSrc s₀ m) hIm with
        | step11 s' hS _ _ =>
          dsimp [iterStateV2]; rw [hS]
        | step12 _ s' hS _ _ _ =>
          dsimp [iterStateV2]; rw [hS]
        | done11 _ _ hT =>
          rw [hEqJ, hEvTrT j] at hT; cases hT
        | fault11 _ _ hT =>
          rw [hEqJ, hEvTrT j] at hT; cases hT
        | fault21 _ _ _ _ hT =>
          rw [hEqJ, hEvTrT j] at hT; cases hT
      · intro ⟨s₀', hOkS, trS, h0S, hTrS⟩
        injection hOkS with eS; subst eS
        have hEvTrS : ∀ i, evalStepV2 pSrc 0 (trS i) = .step (trS (i + 1)) :=
          fun i => stepV2_iff_evalStepV2.mp (hTrS i)
        have hSyncT : ∀ n,
            (∃ i, Inv (trS i) ∧ iterStateV2 pTgt s₀ n = trS i) ∨
            (∃ i, Inv (trS i) ∧
              evalStepV2 pTgt 0 (iterStateV2 pTgt s₀ n) = .step (trS i)) := by
          intro n
          induction n with
          | zero =>
            refine Or.inl ⟨0, ?_, h0S.symm⟩
            rw [h0S]; exact hI0
          | succ n' ih =>
            cases ih with
            | inr hPend =>
              let ⟨i, hIi, hStepN⟩ := hPend
              refine Or.inl ⟨i, hIi, ?_⟩
              dsimp [iterStateV2]; rw [hStepN]
            | inl hAl =>
              let ⟨i, hIi, hEqN⟩ := hAl
              cases hStep (trS i) hIi with
              | step11 s' hS hT hI' =>
                rw [hEvTrS i] at hS; injection hS with e'; subst e'
                refine Or.inl ⟨i + 1, hI', ?_⟩
                dsimp [iterStateV2]; rw [hEqN, hT]
              | step12 tMid s' hS hT1 hT2 hI' =>
                rw [hEvTrS i] at hS; injection hS with e'; subst e'
                refine Or.inr ⟨i + 1, hI', ?_⟩
                dsimp [iterStateV2]; rw [hEqN, hT1]; exact hT2
              | done11 _ hS _ =>
                rw [hEvTrS i] at hS; cases hS
              | fault11 _ hS _ =>
                rw [hEvTrS i] at hS; cases hS
              | fault21 sMid _ hS1 hS2 _ =>
                rw [hEvTrS i] at hS1; injection hS1 with eMid; subst eMid
                rw [hEvTrS (i + 1)] at hS2; cases hS2
        refine ⟨s₀, rfl, iterStateV2 pTgt s₀, rfl, fun n => ?_⟩
        apply stepV2_iff_evalStepV2.mpr
        cases hSyncT n with
        | inr hPend =>
          let ⟨i, _, hStepN⟩ := hPend
          dsimp [iterStateV2]; rw [hStepN]
        | inl hAl =>
          let ⟨i, hIi, hEqN⟩ := hAl
          cases hStep (trS i) hIi with
          | step11 s' _ hT _ =>
            dsimp [iterStateV2]; rw [hEqN, hT]
          | step12 tMid _ _ hT1 _ _ =>
            dsimp [iterStateV2]; rw [hEqN, hT1]
          | done11 _ hS _ =>
            rw [hEvTrS i] at hS; cases hS
          | fault11 _ hS _ =>
            rw [hEvTrS i] at hS; cases hS
          | fault21 sMid _ hS1 hS2 _ =>
            rw [hEvTrS i] at hS1; injection hS1 with eMid; subst eMid
            rw [hEvTrS (i + 1)] at hS2; cases hS2

private theorem v2_list_isEmpty_eq_nil {α : Type} {xs : List α}
    (h : xs.isEmpty = true) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons _ _ => cases h

private theorem v2_getElem?_append_lt {α : Type} :
    ∀ {xs : List α} {a : α} {i : Nat} {x : α},
      Trusted.MirSemantics.getElem? xs i = some x →
      Trusted.MirSemantics.getElem? (xs ++ [a]) i = some x := by
  intro xs
  induction xs with
  | nil => intro _ _ _ h; cases h
  | cons _ rest ih =>
    intro a i x h
    cases i with
    | zero => exact h
    | succ m => exact ih h

private theorem v2_getElem?_append_len {α : Type} (xs : List α) (a : α) :
    Trusted.MirSemantics.getElem? (xs ++ [a]) xs.length = some a := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [List.length, Trusted.MirSemantics.getElem?]
    exact ih

private theorem v2_length_append_one {α : Type} (xs : List α) (a : α) :
    (xs ++ [a]).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [List.length]; rw [ih]

private theorem checkValForMode_bool_elim {mode : ProfileModeV2} {v : Val}
    (h : checkValForMode mode v .bool = true) :
    ∃ bv : Bool, v = .bool bv := by
  cases mode with
  | v1Embedded =>
    exact checkVal_bool_iff.mp h
  | v2Extended =>
    unfold checkValForMode checkValV2 at h
    cases v with
    | ptr _ => exact checkVal_bool_iff.mp h
    | scalar _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ =>
      exact checkVal_bool_iff.mp h

private theorem operandCertifiedBoolInEnv_eval_cases {mode : ProfileModeV2}
    {bodyLocals : List MirTy} {env : List AbsSlot} {locals : List LocalSlot}
    {op : Operand}
    (hEnv : AbsEnvSoundV2 mode bodyLocals env locals)
    (hCert : operandCertifiedBoolInEnv bodyLocals env op = true) :
    (∃ fk, evalPrimitiveOperand bodyLocals locals op = .error fk) ∨
    (∃ bv locs', evalPrimitiveOperand bodyLocals locals op = .ok (.bool bv, locs')) := by
  cases op with
  | constant c =>
    dsimp [operandCertifiedBoolInEnv] at hCert
    have hCTy := mirTy_beq_eq hCert
    unfold evalPrimitiveOperand evalOperandToSlot
    dsimp
    rw [hCTy]
    cases hCL : evalConstLit .bool c.lit with
    | error fk => exact Or.inl ⟨fk, rfl⟩
    | ok v =>
      let ⟨bv, hv⟩ := checkVal_bool_iff.mp (evalConstLit_checkVal hCL)
      subst hv
      dsimp
      rw [isPrimitiveReadableTy_bool]; dsimp
      exact Or.inr ⟨bv, locals, rfl⟩
  | copy p =>
    dsimp [operandCertifiedBoolInEnv] at hCert
    let ⟨hPE, hM⟩ := bool_and_true hCert
    cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
    | none => rw [hTy] at hM; cases hM
    | some ty =>
      rw [hTy] at hM
      cases ty with
      | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
        cases hM
      | bool =>
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hM; cases hM
        | some slot =>
          rw [hAbs] at hM
          have hLtL : p.localId < locals.length := by
            rw [hEnv.1.1]; exact getElem?_some_lt hTy
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
          let ⟨hWt, opt, hSlEq⟩ := absSlotImplies_soundV2 hM
            (hEnv.2.2 p.localId .bool slot sl hTy hAbs hSl)
          subst hSlEq
          unfold evalPrimitiveOperand evalOperandToSlot
          dsimp; rw [hPE]; dsimp; rw [hTy, hSl]; dsimp
          rw [isPrimitiveReadableTy_bool]; dsimp
          cases opt with
          | none => exact Or.inl ⟨.undefined, rfl⟩
          | some v =>
            let ⟨bv, hv⟩ := checkValForMode_bool_elim hWt
            subst hv
            exact Or.inr ⟨bv, locals, rfl⟩
  | move p =>
    dsimp [operandCertifiedBoolInEnv] at hCert
    let ⟨hPE, hM⟩ := bool_and_true hCert
    cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
    | none => rw [hTy] at hM; cases hM
    | some ty =>
      rw [hTy] at hM
      cases ty with
      | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
        cases hM
      | bool =>
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hM; cases hM
        | some slot =>
          rw [hAbs] at hM
          have hLtL : p.localId < locals.length := by
            rw [hEnv.1.1]; exact getElem?_some_lt hTy
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
          let ⟨locs1, hSetL⟩ := setElem?_some_of_lt locals p.localId (liveUninitSlot .bool) hLtL
          let ⟨hWt, opt, hSlEq⟩ := absSlotImplies_soundV2 hM
            (hEnv.2.2 p.localId .bool slot sl hTy hAbs hSl)
          subst hSlEq
          unfold evalPrimitiveOperand evalOperandToSlot
          dsimp; rw [hPE]; dsimp; rw [hTy, hSl]; dsimp
          rw [hSetL]; dsimp
          rw [isPrimitiveReadableTy_bool]; dsimp
          cases opt with
          | none => exact Or.inl ⟨.undefined, rfl⟩
          | some v =>
            let ⟨bv, hv⟩ := checkValForMode_bool_elim hWt
            subst hv
            exact Or.inr ⟨bv, locs1, rfl⟩

private theorem evalBoolSwitchBranches_zero_false (bbNext bbUnreach : BasicBlockId) :
    evalBoolSwitchBranches false bbNext [(BitVec.ofNat 128 0, bbUnreach)] =
      .ok bbUnreach := rfl

private theorem evalBoolSwitchBranches_zero_true (bbNext bbUnreach : BasicBlockId) :
    evalBoolSwitchBranches true bbNext [(BitVec.ofNat 128 0, bbUnreach)] =
      .ok bbNext := rfl

private theorem matchSwitchBoolToAssumeAt?_elim {bSrc : BodyV2} {bbIdx : BasicBlockId}
    {bbSrc bbTgt : BasicBlockV2} {op : Operand}
    (h : matchSwitchBoolToAssumeAt? bSrc bbIdx bbSrc bbTgt = some op) :
    ∃ bbUnreach bbNext blkUnreach,
      bbSrc.cleanup = bbTgt.cleanup ∧
      bbSrc.terminator = .switchInt op
        { branches := [(BitVec.ofNat 128 0, bbUnreach)], otherwise := bbNext } ∧
      bbTgt.terminator = .goto bbNext ∧
      Trusted.MirSemantics.getElem? bSrc.basicBlocks bbUnreach = some blkUnreach ∧
      blkUnreach.statements = [] ∧
      blkUnreach.terminator = .unreachable ∧
      bbTgt.statements = bbSrc.statements ++ [.assume op] := by
  unfold matchSwitchBoolToAssumeAt? at h
  let ⟨hNotCl, h1⟩ := option_ite_none_some h
  have hClEq : bbSrc.cleanup = bbTgt.cleanup := bool_beq_eq (bool_not_false hNotCl)
  cases hTmS : bbSrc.terminator with
  | goto _ | return_ | unreachable | unwindResume | assert _ _ _ _ _
  | call _ _ _ _ _ | unsupported =>
    rw [hTmS] at h1; cases h1
  | switchInt op' targets =>
    rw [hTmS] at h1
    cases targets with
    | mk branches bbNext =>
      cases branches with
      | nil => cases h1
      | cons br rest =>
        cases br with
        | mk caseBits bbUnreach =>
          cases rest with
          | cons _ _ => cases h1
          | nil =>
            cases hTmT : bbTgt.terminator with
            | return_ | unreachable | switchInt _ _ | unwindResume
            | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
              rw [hTmT] at h1; cases h1
            | goto gotoNext =>
              rw [hTmT] at h1; dsimp only at h1
              let ⟨hNotG, h2⟩ := option_ite_none_some h1
              have hG := bool_not_false hNotG
              let ⟨hG12, _⟩ := bool_and_true hG
              let ⟨hCaseB, hNextB⟩ := bool_and_true hG12
              have hCaseEq := bitvec_beq_eq hCaseB
              have hNextEq := nat_beq_eq hNextB
              subst hCaseEq; subst hNextEq
              cases hBU : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbUnreach with
              | none => rw [hBU] at h2; cases h2
              | some blkUnreach =>
                rw [hBU] at h2; dsimp only at h2
                cases hIn : (blkUnreach.statements.isEmpty &&
                    terminatorEq blkUnreach.terminator .unreachable &&
                    listRel stmtV2Eq (bbSrc.statements ++ [.assume op']) bbTgt.statements) with
                | false => rw [if_bool_false hIn] at h2; cases h2
                | true =>
                  rw [if_bool_true hIn] at h2
                  injection h2 with eOp; subst eOp
                  let ⟨hIn12, hRelS⟩ := bool_and_true hIn
                  let ⟨hEmpU, hTmU⟩ := bool_and_true hIn12
                  exact ⟨bbUnreach, bbNext, blkUnreach, hClEq, rfl, rfl, hBU,
                         v2_list_isEmpty_eq_nil hEmpU, terminatorEq_eq hTmU,
                         (listRel_eq (fun _ _ => stmtV2Eq_eq) hRelS).symm⟩

private theorem checkUnreachablePropAssumeBlocks_get {bSrc bTgt : BodyV2}
    {cert : BodyAbsCert} :
    ∀ {base k : Nat} {bbs : List BasicBlockV2} {bbSrc : BasicBlockV2}
      {entryEnv : List AbsSlot},
      checkUnreachablePropAssumeBlocks bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      Trusted.MirSemantics.getElem? cert (base + k) = some (some entryEnv) →
      ∃ bbTgt exitEnv,
        Trusted.MirSemantics.getElem? bTgt.basicBlocks (base + k) = some bbTgt ∧
        stepPlainStmtsAbsV2 bSrc.locals entryEnv bbSrc.statements = some exitEnv ∧
        checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length cert
          exitEnv bbSrc.terminator = true ∧
        (bbSrc = bbTgt ∨
          ∃ op, matchSwitchBoolToAssumeAt? bSrc (base + k) bbSrc bbTgt = some op ∧
            operandCertifiedBoolInEnv bSrc.locals exitEnv op = true) := by
  intro base k bbs
  induction bbs generalizing base k with
  | nil => intro _ _ _ hG _; cases hG
  | cons bb₀ rest ih =>
    intro bbSrc entryEnv hLoop hG hC
    dsimp [checkUnreachablePropAssumeBlocks] at hLoop
    let ⟨hHere, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hG with e; subst e
      rw [Nat.add_zero] at hC
      rw [Nat.add_zero]
      rw [hC] at hHere
      cases hBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks base with
      | none => rw [hBT] at hHere; cases hHere
      | some bbTgt =>
        rw [hBT] at hHere; dsimp only at hHere
        let ⟨_, hStM⟩ := bool_and_true hHere
        cases hSt : stepPlainStmtsAbsV2 bSrc.locals entryEnv bb₀.statements with
        | none => rw [hSt] at hStM; cases hStM
        | some exitEnv =>
          rw [hSt] at hStM
          let ⟨hEdg, hDisj⟩ := bool_and_true hStM
          refine ⟨bbTgt, exitEnv, rfl, rfl, hEdg, ?_⟩
          cases bool_or_true hDisj with
          | inl hEqB => exact Or.inl (blockV2Eq_eq hEqB)
          | inr hM =>
            cases hMat : matchSwitchBoolToAssumeAt? bSrc base bb₀ bbTgt with
            | none => rw [hMat] at hM; cases hM
            | some op =>
              rw [hMat] at hM
              exact Or.inr ⟨op, rfl, hM⟩
    | succ m =>
      have hAdd : (base + 1) + m = base + (m + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 m]
      rw [← hAdd] at hC
      have hSub := ih hTail hG hC
      rw [hAdd] at hSub
      exact hSub

private noncomputable def UnreachablePropInv (cert : ProgramAbsCert)
    (pSrc pTgt : ProgramV2) (s : State) : Prop :=
  ∃ f bCert bSrc bTgt,
    s.frames = [f] ∧
    pSrc.profileMode = pTgt.profileMode ∧
    Trusted.MirSemantics.getElem? cert f.defId = some bCert ∧
    Trusted.MirSemantics.getElem? pSrc.bodies f.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies f.defId = some bTgt ∧
    checkUnreachablePropAssumeBody bCert bSrc bTgt = true ∧
    (f.blockIdx < bSrc.basicBlocks.length →
      ∃ bbSrc bbTgt env exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks f.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks f.blockIdx = some bbTgt ∧
        f.stmtIdx ≤ bbSrc.statements.length ∧
        stepPlainStmtsAbsV2 bSrc.locals env
          (bbSrc.statements.drop f.stmtIdx) = some exitEnv ∧
        checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length bCert
          exitEnv bbSrc.terminator = true ∧
        AbsEnvSoundV2 pSrc.profileMode bSrc.locals env f.locals ∧
        (bbSrc = bbTgt ∨
          ∃ op, matchSwitchBoolToAssumeAt? bSrc f.blockIdx bbSrc bbTgt = some op ∧
            operandCertifiedBoolInEnv bSrc.locals exitEnv op = true))

private theorem unreachableProp_query_iff {cert : ProgramAbsCert}
    {pSrc pTgt : ProgramV2}
    (hCert : checkUnreachablePropAssumeProgram cert pSrc pTgt = true)
    (q : Query) :
    (WellFormedV2 pTgt q ↔ WellFormedV2 pSrc q) ∧
    (∀ out : TerminalOut, BehaviorV2 pTgt q out ↔ BehaviorV2 pSrc q out) ∧
    (∀ k : FaultKindV2,
      ReachesResultV2 pTgt q (.fault k) ↔ ReachesResultV2 pSrc q (.fault k)) ∧
    (DivergesV2 pTgt q ↔ DivergesV2 pSrc q) := by
  let ⟨h12P, hZipC⟩ := bool_and_true hCert
  let ⟨hRel, hCLenB⟩ := bool_and_true h12P
  have hCLen := nat_beq_eq hCLenB
  let ⟨hHdr, hBodiesR⟩ := bool_and_true hRel
  let ⟨_, _, hEnt, _, hPmEq⟩ := programHeaderV2Eq_elim hHdr
  have hInitEq : initStateV2 pSrc q = initStateV2 pTgt q := by
    apply initStateV2_eq_of_matching_entry q hHdr
    · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodiesR
    · intro b₁ hB₁
      let ⟨_, b₂, _, hB₂, hChkB⟩ := listRel_zip_getElem? hCLen hZipC hB₁
      rw [hEnt] at hB₂
      let ⟨h12345, _⟩ := bool_and_true hChkB
      let ⟨h1234, _⟩ := bool_and_true h12345
      let ⟨h123, hBBLenB⟩ := bool_and_true h1234
      let ⟨h12, _⟩ := bool_and_true h123
      let ⟨hBHdr, hPres⟩ := bool_and_true h12
      exact ⟨b₂, hB₂, hBHdr, list_isEmpty_eq_of_length (nat_beq_eq hBBLenB), hPres⟩
  apply macro_step_v2_query_iff (Inv := UnreachablePropInv cert pSrc pTgt) hInitEq
  · intro s₀ hOk
    let ⟨bSrc, hBS, hNotEmp, _, _, hArgs, hs0⟩ := initStateV2_ok_elim hOk
    subst hs0
    let ⟨bCert, bTgt, hBC, hBT, hChkB⟩ := listRel_zip_getElem? hCLen hZipC hBS
    let ⟨h12345, hBlkLoop⟩ := bool_and_true hChkB
    let ⟨_, hEntry0⟩ := bool_and_true h12345
    rw [if_bool_false hNotEmp] at hEntry0
    cases hC0 : Trusted.MirSemantics.getElem? bCert 0 with
    | none => rw [hC0] at hEntry0; cases hEntry0
    | some opt0 =>
      rw [hC0] at hEntry0
      cases opt0 with
      | none => cases hEntry0
      | some env₀ =>
        have hEnv0 := absEnvImplies_soundV2 hEntry0 (initAbsEnvLoopV2_sound hArgs)
        refine ⟨_, bCert, bSrc, bTgt, rfl, hPmEq, hBC, hBS, hBT, hChkB, ?_⟩
        intro h0Lt
        let ⟨bbSrc0, hBBS0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
        let ⟨bbTgt0, exitE0, hBBT0, hSt0, hEdg0, hDisj0⟩ :=
          checkUnreachablePropAssumeBlocks_get hBlkLoop hBBS0 hC0
        exact ⟨bbSrc0, bbTgt0, env₀, exitE0, hBBS0, hBBT0,
               Nat.zero_le bbSrc0.statements.length, hSt0, hEdg0, hEnv0, hDisj0⟩
  · intro s hInv
    let ⟨f, bCert, bSrc, bTgt, hFr, _, hBC, hBS, hBT, hChkB, hBlkInv⟩ := hInv
    let ⟨h12345, hBlkLoop⟩ := bool_and_true hChkB
    let ⟨h1234, _⟩ := bool_and_true h12345
    let ⟨h123, hBBLenB⟩ := bool_and_true h1234
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hBHdr, _⟩ := bool_and_true h12
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderV2Eq_elim hBHdr
    have hBBLen := nat_beq_eq hBBLenB
    cases s with
    | mk frames cm =>
      dsimp at hFr; subst hFr
      cases Nat.lt_or_ge f.blockIdx bSrc.basicBlocks.length with
      | inr hGe =>
        have hGeT : bTgt.basicBlocks.length ≤ f.blockIdx := by rw [← hBBLen]; exact hGe
        apply macroStep_same
        · unfold evalStepV2; dsimp
          rw [hBS, hBT]; dsimp
          rw [getElem?_none_of_ge hGe, getElem?_none_of_ge hGeT]
        · intro s' hSt
          unfold evalStepV2 at hSt; dsimp at hSt
          rw [hBS] at hSt; dsimp at hSt
          rw [getElem?_none_of_ge hGe] at hSt; cases hSt
      | inl hLt =>
        let ⟨bbSrc, bbTgt, env, exitEnv, hBBS, hBBT, hIdxLe, hStAbs, hEdg,
             hEnvS, hDisj⟩ := hBlkInv hLt
        cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements f.stmtIdx with
        | some stmt =>
          have hIdxLt := getElem?_some_lt hStS
          have hDropS := drop_eq_cons_of_getElem? hStS
          rw [hDropS] at hStAbs
          dsimp [stepPlainStmtsAbsV2] at hStAbs
          cases hSt1 : stepPlainStmtAbsV2 bSrc.locals env stmt with
          | none => rw [hSt1] at hStAbs; cases hStAbs
          | some env' =>
            rw [hSt1] at hStAbs
            have hStT : Trusted.MirSemantics.getElem? bbTgt.statements f.stmtIdx =
                some stmt := by
              cases hDisj with
              | inl hEqB => rw [← hEqB]; exact hStS
              | inr hRew =>
                let ⟨op, hMat, _⟩ := hRew
                let ⟨_, _, _, _, _, _, _, _, _, hStmtsT⟩ :=
                  matchSwitchBoolToAssumeAt?_elim hMat
                rw [hStmtsT]
                exact v2_getElem?_append_lt hStS
            apply macroStep_same
            · unfold evalStepV2; dsimp
              rw [hBS, hBT]; dsimp
              rw [hBBS, hBBT]; dsimp
              rw [hStS, hStT]; dsimp
              rw [← hPmEq]
              exact evalStatementV2_eq_of_locals_eq stmt hLocEq
            · intro s' hStepS
              unfold evalStepV2 at hStepS; dsimp at hStepS
              rw [hBS] at hStepS; dsimp at hStepS
              rw [hBBS] at hStepS; dsimp at hStepS
              rw [hStS] at hStepS; dsimp at hStepS
              let ⟨locs', hs', hEnv'⟩ := stepPlainStmtAbsV2_sound hEnvS hSt1 hStepS
              subst hs'
              refine ⟨_, bCert, bSrc, bTgt, rfl, hPmEq, hBC, hBS, hBT, hChkB,
                      fun _ => ?_⟩
              refine ⟨bbSrc, bbTgt, env', exitEnv, hBBS, hBBT, hIdxLt, ?_, hEdg,
                      hEnv', hDisj⟩
              dsimp
              rw [(getElem?_of_drop_eq_cons hDropS).2]
              exact hStAbs
        | none =>
          have hGeIdx := getElem?_none_ge hStS
          have hIdxEq : f.stmtIdx = bbSrc.statements.length :=
            Nat.le_antisymm hIdxLe hGeIdx
          rw [drop_eq_nil_of_ge hGeIdx] at hStAbs
          dsimp [stepPlainStmtsAbsV2] at hStAbs
          injection hStAbs with eEnv; subst eEnv
          cases hDisj with
          | inl hEqB =>
            apply macroStep_same
            · unfold evalStepV2; dsimp
              rw [hBS, hBT]; dsimp
              rw [hBBS, hBBT]; dsimp
              rw [← hEqB, hStS]; dsimp
              rw [hIdxEq, nat_beq_refl]
              dsimp
              exact evalTerminatorV2_eq_of_eq hLocEq rfl rfl
            · intro s' hStepS
              unfold evalStepV2 at hStepS; dsimp at hStepS
              rw [hBS] at hStepS; dsimp at hStepS
              rw [hBBS] at hStepS; dsimp at hStepS
              rw [hStS, hIdxEq, nat_beq_refl] at hStepS; dsimp at hStepS
              let ⟨tgt, locs', hs', hTgtCert⟩ :=
                checkAbsTerminatorEdges_v2_step_sound hEnvS hEdg hStepS
              subst hs'
              refine ⟨_, bCert, bSrc, bTgt, rfl, hPmEq, hBC, hBS, hBT, hChkB, ?_⟩
              intro hTgtLt
              let ⟨tgtEnv, hCTgt, hTgtEnvS⟩ := hTgtCert hTgtLt
              let ⟨bbNextS, hBBNS⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt hTgtLt
              have hCTgt0 : Trusted.MirSemantics.getElem? bCert (0 + tgt) =
                  some (some tgtEnv) := by
                rw [Nat.zero_add]; exact hCTgt
              let ⟨bbNextT, nextExit, hBBNT, hStN, hEdgN, hDisjN⟩ :=
                checkUnreachablePropAssumeBlocks_get hBlkLoop hBBNS hCTgt0
              rw [Nat.zero_add] at hBBNT
              rw [Nat.zero_add] at hDisjN
              exact ⟨bbNextS, bbNextT, tgtEnv, nextExit, hBBNS, hBBNT,
                     Nat.zero_le bbNextS.statements.length, hStN, hEdgN,
                     hTgtEnvS, hDisjN⟩
          | inr hRew =>
            let ⟨op, hMat, hOpBool⟩ := hRew
            let ⟨bbUnreach, bbNext, blkUnreach, _, hTmSrc, hTmTgt, hBlkU,
                 hStmtsU, hTmU, hStmtsT⟩ :=
              matchSwitchBoolToAssumeAt?_elim hMat
            have hGetAssume : Trusted.MirSemantics.getElem? bbTgt.statements f.stmtIdx =
                some (.assume op) := by
              rw [hStmtsT, hIdxEq]
              exact v2_getElem?_append_len bbSrc.statements (.assume op)
            cases operandCertifiedBoolInEnv_eval_cases hEnvS hOpBool with
            | inl hErr =>
              let ⟨fk, hEvOp⟩ := hErr
              refine .fault11 (FaultKindV2.ofV1 fk) ?_ ?_
              · unfold evalStepV2; dsimp
                rw [hBS]; dsimp; rw [hBBS]; dsimp
                rw [hStS, hIdxEq, nat_beq_refl]; dsimp
                unfold evalTerminatorV2; rw [hTmSrc]; dsimp
                rw [hEvOp]
              · unfold evalStepV2; dsimp
                rw [hBT]; dsimp; rw [hBBT]; dsimp
                rw [hGetAssume]; dsimp
                unfold evalStatementV2; dsimp
                rw [← hLocEq, hEvOp]
            | inr hOkOp =>
              let ⟨bv, locs', hEvOp⟩ := hOkOp
              cases bv with
              | false =>
                refine .fault21
                  { frames := [{ f with blockIdx := bbUnreach, stmtIdx := 0, locals := locs' }],
                    callerMem := cm }
                  .unreachableExecuted ?_ ?_ ?_
                · unfold evalStepV2; dsimp
                  rw [hBS]; dsimp; rw [hBBS]; dsimp
                  rw [hStS, hIdxEq, nat_beq_refl]; dsimp
                  unfold evalTerminatorV2; rw [hTmSrc]; dsimp
                  rw [hEvOp]; dsimp
                  rw [evalBoolSwitchBranches_zero_false]
                · unfold evalStepV2; dsimp
                  rw [hBS]; dsimp; rw [hBlkU]; dsimp
                  rw [hStmtsU]; dsimp [Trusted.MirSemantics.getElem?, List.length]
                  unfold evalTerminatorV2; rw [hTmU]
                · unfold evalStepV2; dsimp
                  rw [hBT]; dsimp; rw [hBBT]; dsimp
                  rw [hGetAssume]; dsimp
                  unfold evalStatementV2; dsimp
                  rw [← hLocEq, hEvOp]
              | true =>
                have hEvSrcStep : evalTerminatorV2 bSrc bbSrc f cm =
                    .step { frames := [{ f with blockIdx := bbNext, stmtIdx := 0, locals := locs' }],
                            callerMem := cm } := by
                  unfold evalTerminatorV2; rw [hTmSrc]; dsimp
                  rw [hEvOp]; dsimp
                  rw [evalBoolSwitchBranches_zero_true]
                let ⟨tgt, locs2, hs', hTgtCert⟩ :=
                  checkAbsTerminatorEdges_v2_step_sound hEnvS hEdg hEvSrcStep
                injection hs' with eFr _
                injection eFr with eF _
                have hTgtEq : bbNext = tgt := congrArg FrameState.blockIdx eF
                have hLocs2Eq : locs' = locs2 := congrArg FrameState.locals eF
                subst hTgtEq; subst hLocs2Eq
                refine .step12
                  { frames := [{ f with stmtIdx := f.stmtIdx + 1, locals := locs' }],
                    callerMem := cm }
                  { frames := [{ f with blockIdx := bbNext, stmtIdx := 0, locals := locs' }],
                    callerMem := cm }
                  ?_ ?_ ?_ ?_
                · unfold evalStepV2; dsimp
                  rw [hBS]; dsimp; rw [hBBS]; dsimp
                  rw [hStS, hIdxEq, nat_beq_refl]; dsimp
                  exact hEvSrcStep
                · unfold evalStepV2; dsimp
                  rw [hBT]; dsimp; rw [hBBT]; dsimp
                  rw [hGetAssume]; dsimp
                  unfold evalStatementV2; dsimp
                  rw [← hLocEq, hEvOp]
                · unfold evalStepV2; dsimp
                  rw [hBT]; dsimp; rw [hBBT]; dsimp
                  have hLenT : bbTgt.statements.length = f.stmtIdx + 1 := by
                    rw [hStmtsT, hIdxEq, v2_length_append_one]
                  have hNoneNext : Trusted.MirSemantics.getElem? bbTgt.statements (f.stmtIdx + 1) =
                      none :=
                    getElem?_none_of_ge (by rw [hLenT]; exact Nat.le_refl _)
                  rw [hNoneNext, hLenT, nat_beq_refl]; dsimp
                  unfold evalTerminatorV2; rw [hTmTgt]
                · refine ⟨_, bCert, bSrc, bTgt, rfl, hPmEq, hBC, hBS, hBT, hChkB, ?_⟩
                  intro hNextLt
                  let ⟨tgtEnv, hCTgt, hTgtEnvS⟩ := hTgtCert hNextLt
                  let ⟨bbNextS, hBBNS⟩ := getElem?_some_of_lt bSrc.basicBlocks bbNext hNextLt
                  have hCTgt0 : Trusted.MirSemantics.getElem? bCert (0 + bbNext) =
                      some (some tgtEnv) := by
                    rw [Nat.zero_add]; exact hCTgt
                  let ⟨bbNextT, nextExit, hBBNT, hStN, hEdgN, hDisjN⟩ :=
                    checkUnreachablePropAssumeBlocks_get hBlkLoop hBBNS hCTgt0
                  rw [Nat.zero_add] at hBBNT
                  rw [Nat.zero_add] at hDisjN
                  exact ⟨bbNextS, bbNextT, tgtEnv, nextExit, hBBNS, hBBNT,
                         Nat.zero_le bbNextS.statements.length, hStN, hEdgN,
                         hTgtEnvS, hDisjN⟩

private theorem unreachableProp_switchBoolToAssume_bidirectional_iff_priv
    (pSrc pTgt : ProgramV2) (cert : ProgramAbsCert)
    (hCert : checkUnreachablePropAssumeProgram cert pSrc pTgt = true) :
    FullSemanticEquivV2 pSrc pTgt := by
  let ⟨h12P, hZipC⟩ := bool_and_true hCert
  let ⟨hRel, hCLenB⟩ := bool_and_true h12P
  have hCLen := nat_beq_eq hCLenB
  let ⟨hHdr, hBodiesR⟩ := bool_and_true hRel
  apply fullSemanticEquivV2_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨_, bTgt', _, hBT', hChkB⟩ := listRel_zip_getElem? hCLen hZipC hBS
    rw [hBT] at hBT'; injection hBT' with eB; subst eB
    let ⟨h12345, _⟩ := bool_and_true hChkB
    let ⟨h1234, _⟩ := bool_and_true h12345
    let ⟨h123, hBBLenB⟩ := bool_and_true h1234
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hBHdr, hPres⟩ := bool_and_true h12
    exact ⟨hBHdr, list_isEmpty_eq_of_length (nat_beq_eq hBBLenB),
           (preservesAllStorageAnnotationsV2_elim hPres).1⟩
  · exact unreachableProp_query_iff hCert
  · intro defId args
    have hHdrE := programHeaderV2Eq_entryProgV2 defId hHdr
    have hRelE : isUnreachablePropAssumeProgram
        (entryProgForBodyV2 pSrc defId) (entryProgForBodyV2 pTgt defId) = true :=
      bool_and_intro hHdrE hBodiesR
    have hCertE : checkUnreachablePropAssumeProgram cert
        (entryProgForBodyV2 pSrc defId) (entryProgForBodyV2 pTgt defId) = true :=
      bool_and_intro (bool_and_intro hRelE hCLenB) hZipC
    exact (unreachableProp_query_iff hCertE { args := args }).1

/-! ## Part III: Core Target Theorems Directly Over `Trusted.MirSemantics` & `MirProfileV2` -/

/-- **Theorem 1a (Single-Step Multi-Family `MirOptStep` Bidirectional Soundness):**
Every certified pass family in `MirOptStep` (`.moveToCopyDead`,
`.simplifyCfgBranch`, `.instSimplifyAlgAndConst`, `.copyAndDestPropAndDse`, and
`.compactUnusedTrailingLocals`) preserves `FullSemanticEquiv` (`WellFormed`,
`Behavior`, `ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and
`BodyVerified` bidirectionally `↔`) directly on unmodified `Trusted.MirSemantics`. -/
theorem mirOptStep_sound_bidirectional_iff
    (step : MirOptStep) (pSrc pTgt : Program)
    (hStep : checkMirOptStep step pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact mirOptStep_sound_bidirectional_iff_priv step pSrc pTgt hStep

/-- **Theorem 1b (Arbitrary-Length Multi-Pass `MirOptTrace` Composition):**
For any finite optimization trace `trace : MirOptTrace`, `checkMirOptTrace trace
pPostCleanup pOptimized = true` implies `FullSemanticEquiv pPostCleanup
pOptimized` (`WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`,
`SatisfiesPost`, and `BodyVerified` `↔`). -/
theorem mirOptTrace_sound_bidirectional_iff
    (trace : MirOptTrace) (pPostCleanup pOptimized : Program)
    (hTrace : checkMirOptTrace trace pPostCleanup pOptimized = true) :
    FullSemanticEquiv pPostCleanup pOptimized := by
  exact mirOptTrace_sound_bidirectional_iff_priv trace pPostCleanup pOptimized hTrace

/-- **Theorem 1c (Whole-Pipeline `CrateTheorem` & `UnitTheorem` Bidirectional
VC Transport):**
Whenever `checkMirOptTrace trace pPostCleanup pOptimized = true` and `specs`
satisfies `SpecsPropertyInvariant specs`, `CrateTheorem` and `UnitTheorem`
transport bidirectionally (`↔`) between `pOptimized` and `pPostCleanup` across
both whole-crate subjects and arbitrary per-item proof units `u : DefId`. -/
theorem mirOptTrace_crate_and_unit_vc_transport_iff
    (trace : MirOptTrace) (pPostCleanup pOptimized : Program) (specs : Specs)
    (hTrace : checkMirOptTrace trace pPostCleanup pOptimized = true)
    (hSpec : SpecsPropertyInvariant specs) :
    (CrateTheorem ⟨pOptimized, specs⟩ ↔ CrateTheorem ⟨pPostCleanup, specs⟩) ∧
    (UnitTheorem ⟨pOptimized, specs⟩ ↔ UnitTheorem ⟨pPostCleanup, specs⟩) ∧
    (∀ u : DefId,
      UnitTheorem ⟨unitProgForDef pOptimized u, specs⟩ ↔
        UnitTheorem ⟨unitProgForDef pPostCleanup u, specs⟩) := by
  exact mirOptTrace_crate_and_unit_vc_transport_iff_priv trace pPostCleanup pOptimized specs hTrace hSpec

/-- **Theorem 2a (Exact Conservative Extension of `MirProfileV2` Over
`Trusted.MirSemantics`):**
For every `p : Trusted.MirAst.Program`, `embedProgramV1 p` steps in exact
1-to-1 lockstep with `Trusted.MirSemantics.evalStep` and preserves `WellFormed`,
`Behavior`, `ReachesResult (.fault _)`, and `Diverges` identically (`↔`). -/
theorem profileV2_conservative_extension_exact
    (p : Program) :
    (∀ (c : Choice) (s : State),
      mapStepResultV2ToV1 (evalStepV2 (embedProgramV1 p) c s) =
        evalStep p c s) ∧
    (∀ q : Query,
      (WellFormedV2 (embedProgramV1 p) q ↔ WellFormed p q) ∧
      (∀ out : TerminalOut,
        BehaviorV2 (embedProgramV1 p) q out ↔ Behavior p q out) ∧
      (∀ k : FaultKind,
        (∃ k₂ : FaultKindV2,
          k₂.toV1 = k ∧
          ReachesResultV2 (embedProgramV1 p) q (.fault k₂)) ↔
          ReachesResult p q (.fault k)) ∧
      (DivergesV2 (embedProgramV1 p) q ↔ Diverges p q)) := by
  exact profileV2_conservative_extension_exact_priv p

/-- **Theorem 2b (Certified `RemovePlaceMention` Bidirectional Equivalence,
`E3-22` / `remove_place_mention.rs:13`):**
Erasing certified `StatementKindV2.placeMention p` (`isSafePlaceMention p =
true` under `checkRemovePlaceMentionProgram`) to `.v1 .nop` preserves
`FullSemanticEquivV2` (`↔`), covering both live local mentions and RFC 2582
zero-offset raw-pointer dereferences while rejecting uncertified non-zero
`inbounds` field-offset projections. -/
theorem removePlaceMention_certified_bidirectional_iff
    (pSrc pTgt : ProgramV2) (cert : ProgramAbsCert)
    (hCert : checkRemovePlaceMentionProgram cert pSrc pTgt = true) :
    FullSemanticEquivV2 pSrc pTgt := by
  exact removePlaceMention_certified_bidirectional_iff_priv pSrc pTgt cert hCert

/-- **Theorem 2c (Certified `UnreachablePropagation` `SwitchInt -> .assume`
Bidirectional Equivalence, `E3-16` / `unreachable_prop.rs`):**
Rewriting `bb: stmts; SwitchInt(op) -> [0: bb_empty_unreachable, otherwise:
bb_next]` into `bb: stmts ++ [.assume op]; Goto bb_next` under
`checkUnreachablePropAssumeProgram` preserves `FullSemanticEquivV2` (`↔`,
including `DivergesV2` and `.fault .unreachableExecuted`). -/
theorem unreachableProp_switchBoolToAssume_bidirectional_iff
    (pSrc pTgt : ProgramV2) (cert : ProgramAbsCert)
    (hCert : checkUnreachablePropAssumeProgram cert pSrc pTgt = true) :
    FullSemanticEquivV2 pSrc pTgt := by
  exact unreachableProp_switchBoolToAssume_bidirectional_iff_priv pSrc pTgt cert hCert

/-! ## Part IV: Deterministic Adequacy & Constructive Sharpness / Non-Vacuity Witnesses (`0` `sorry`) -/

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

/-! ### Deterministic Fuel-Indexed Adequacy for `MirProfileV2` (`evalBodyV2`) -/

noncomputable def PositiveCanaryClaimV2 (p : ProgramV2) (q : Query)
    (expectedRet : Val) : Prop :=
  WellFormedV2 p q ∧ BehaviorV2 p q (.returned ⟨expectedRet, q.callerMem⟩)

noncomputable def NegativeCanaryClaimV2 (p : ProgramV2) (q : Query)
    (expectedFault otherFault : FaultKindV2) : Prop :=
  ReachesResultV2 p q (.fault expectedFault) ∧
  ¬ ReachesResultV2 p q (.fault otherFault) ∧
  ¬ WellFormedV2 p q

noncomputable def execReturnsV2 (p : ProgramV2) (fuel : Nat) (q : Query)
    (expected : Val) : Prop :=
  match initStateV2 p q with
  | .error _ => False
  | .ok s₀ => evalBodyV2 p fuel s₀ = .done (.returned ⟨expected, q.callerMem⟩)

noncomputable def execFaultsV2 (p : ProgramV2) (fuel : Nat) (q : Query)
    (expected : FaultKindV2) : Prop :=
  match initStateV2 p q with
  | .error k => k = expected
  | .ok s₀ => evalBodyV2 p fuel s₀ = .fault expected

theorem reachesV2_head_det {p : ProgramV2} {s₁ s₂ s₃ : State}
    (hFirst : StepV2 p s₁ (.step s₂)) (hRest : ReachesV2 p s₂ s₃) :
    ReachesV2 p s₁ s₃ := by
  induction hRest with
  | refl => exact ReachesV2.tail (ReachesV2.refl s₁) hFirst
  | tail _ hLast ih => exact ReachesV2.tail ih hLast

theorem evalBodyV2_reaches_inv {p : ProgramV2}
    {res : StepResultV2 State TerminalOut}
    {s₁ s₂ : State} {fuel : Nat}
    (hNotStep : match res with | .step _ => False | _ => True)
    (hExec : evalBodyV2 p fuel s₁ = res)
    (hReach : ReachesV2 p s₁ s₂) :
    ∃ fuel', evalBodyV2 p fuel' s₂ = res := by
  induction hReach with
  | refl => exact ⟨fuel, hExec⟩
  | tail _ hStep ih =>
    let ⟨f, hf⟩ := ih
    cases f with
    | zero =>
      dsimp [evalBodyV2] at hf
      subst hf
      exact False.elim hNotStep
    | succ f' =>
      let ⟨c, hc, hEval⟩ := hStep
      have hc0 : c = 0 := hc
      subst hc0
      dsimp [evalBodyV2] at hf
      rw [hEval] at hf
      exact ⟨f', hf⟩

theorem evalBodyV2_terminal {p : ProgramV2}
    {res : StepResultV2 State TerminalOut}
    {fuel : Nat} {s : State}
    (hNotStep : match res with | .step _ => False | _ => True)
    (hExec : evalBodyV2 p fuel s = res) :
    ∃ sEnd, ReachesV2 p s sEnd ∧ StepV2 p sEnd res := by
  induction fuel generalizing s with
  | zero =>
    dsimp [evalBodyV2] at hExec
    subst hExec
    exact False.elim hNotStep
  | succ f ih =>
    dsimp [evalBodyV2] at hExec
    cases hEval : evalStepV2 p 0 s with
    | step s' =>
      rw [hEval] at hExec
      let ⟨sEnd, hR, hT⟩ := ih hExec
      exact ⟨sEnd, reachesV2_head_det ⟨0, rfl, hEval⟩ hR, hT⟩
    | done out =>
      rw [hEval] at hExec
      subst hExec
      exact ⟨s, ReachesV2.refl s, ⟨0, rfl, hEval⟩⟩
    | fault k =>
      rw [hEval] at hExec
      subst hExec
      exact ⟨s, ReachesV2.refl s, ⟨0, rfl, hEval⟩⟩

theorem positiveCanaryV2_of_execReturnsV2 {p : ProgramV2} {fuel : Nat}
    {q : Query} {expected : Val}
    (h : execReturnsV2 p fuel q expected) :
    PositiveCanaryClaimV2 p q expected := by
  unfold execReturnsV2 at h
  cases hInit : initStateV2 p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_⟩
    · intro k hFault
      unfold ReachesResultV2 at hFault
      rw [hInit] at hFault
      let ⟨sF, hReach, c, hc, hEval⟩ := hFault
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalBodyV2_reaches_inv True.intro h hReach
      cases f' with
      | zero =>
        dsimp [evalBodyV2] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalBodyV2] at hf'
        rw [hEval] at hf'
        cases hf'
    · unfold BehaviorV2 ReachesResultV2
      rw [hInit]
      exact evalBodyV2_terminal True.intro h

theorem negativeCanaryV2_of_execFaultsV2 {p : ProgramV2} {fuel : Nat}
    {q : Query} {expectedFault otherFault : FaultKindV2}
    (hNe : otherFault ≠ expectedFault)
    (h : execFaultsV2 p fuel q expectedFault) :
    NegativeCanaryClaimV2 p q expectedFault otherFault := by
  unfold execFaultsV2 at h
  cases hInit : initStateV2 p q with
  | error k =>
    rw [hInit] at h
    subst h
    refine ⟨?_, ?_, ?_⟩
    · unfold ReachesResultV2; rw [hInit]
    · intro hOther
      unfold ReachesResultV2 at hOther
      rw [hInit] at hOther
      cases hOther
      exact hNe rfl
    · intro hWf
      let ⟨⟨_, hOk, _⟩, _⟩ := hWf
      rw [hInit] at hOk
      cases hOk
  | ok s₀ =>
    rw [hInit] at h
    have hReachExp : ReachesResultV2 p q (.fault expectedFault) := by
      unfold ReachesResultV2
      rw [hInit]
      exact evalBodyV2_terminal True.intro h
    refine ⟨hReachExp, ?_, ?_⟩
    · intro hOther
      unfold ReachesResultV2 at hOther
      rw [hInit] at hOther
      let ⟨sF, hReach, c, hc, hEval⟩ := hOther
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalBodyV2_reaches_inv True.intro h hReach
      cases f' with
      | zero =>
        dsimp [evalBodyV2] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalBodyV2] at hf'
        rw [hEval] at hf'
        injection hf' with hEq
        exact hNe hEq
    · intro hWf
      exact hWf.2 expectedFault hReachExp

/-! ### Sharpness Counterexample 1 (`E3-22` / `F1-5`): Collapsing Equal-Target `SwitchInt` on Uninitialized Discriminant Erases UB -/

noncomputable def progCe1UninitSwitchSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u8Ty]
    identity := "ce1::uninit_switch_branch"
    basicBlocks := [
      {
        statements := [.storageLive 1]
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 1
        }
      },
      {
        statements := [
          .storageDead 1,
          .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def progCe1UninitSwitchBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u8Ty]
    identity := "ce1::uninit_switch_branch"
    basicBlocks := [
      {
        statements := [.storageLive 1]
        terminator := .goto 1
      },
      {
        statements := [
          .storageDead 1,
          .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def ce1AbsCert : ProgramAbsCert := [[
  some [.liveUninit, .dead],
  some [.liveUninit, .liveUninit]
]]

/-- **Sharpness Theorem CE1 (`E3-22` `equal_target_unit_switch_uninit_u8`):**
Collapsing equal-target `SwitchInt(copy _1) -> [0: bb1, otherwise: bb1]` into
`Goto bb1` when `_1 : u8` is uninitialized erases `FaultKind.undefined` in
`pSrc` (returning `42_u32` in `pBadTgt`) and is rejected by `checkMirOptStep`. -/
theorem ce1_uninit_switchBranch_erases_ub :
    checkMirOptStep (.simplifyCfgBranch ce1AbsCert)
      progCe1UninitSwitchSrc progCe1UninitSwitchBadTgt = false ∧
    NegativeCanaryClaim progCe1UninitSwitchSrc queryEmpty
      .undefined .unsupported ∧
    PositiveCanaryClaim progCe1UninitSwitchBadTgt queryEmpty (u32Val 42) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact negativeCanary_of_execFaults (fuel := 6) (by intro h; cases h) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Sharpness Counterexample 2 (`E3-22`): `RemovePlaceMention` on Null Non-Zero `inbounds` Field Offset Erases UB -/

noncomputable def u64Ty : MirTy := .int .i64 false
noncomputable def rawConstU64Ty : MirTy := .rawPtr .shared u64Ty

noncomputable def nullPtrVal : Val :=
  .ptr { allocId := none, offsetBytes := 0, width := .isize }

noncomputable def misalignedPtrVal : Val :=
  .ptr { allocId := some 1, offsetBytes := 1, width := .isize }

noncomputable def queryNullPtr : Query := { args := [nullPtrVal] }
noncomputable def queryMisalignedPtr : Query := { args := [misalignedPtrVal] }

noncomputable def progCe2NullFieldOffsetSrc : ProgramV2 where
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, rawConstU64Ty]
    isUnsafe := true
    identity := "ce2::place_mention_null_nonzero_offset"
    basicBlocks := [{
      statements := [
        .placeMention (.rawDerefFieldOffset 1 8),
        .v1 (.assign ⟨0, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩)))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progCe2NullFieldOffsetBadTgt : ProgramV2 where
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, rawConstU64Ty]
    isUnsafe := true
    identity := "ce2::place_mention_null_nonzero_offset"
    basicBlocks := [{
      statements := [
        .v1 .nop,
        .v1 (.assign ⟨0, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩)))
      ]
      terminator := .return_
    }]
  }]

noncomputable def singleBlockPtrCert : ProgramAbsCert := [[
  some [.liveUninit, .liveInit]
]]

/-- **Sharpness Theorem CE2 (`E3-22` `place_mention_null_nonzero_field_offset`):**
Erasing `PlaceMention(((*_1).1: u64))` at byte offset `8` to `.nop` erases
`FaultKindV2.invalidPointerOffset` when `_1` is a null pointer, and is rejected
by both `isSafePlaceMention` and `checkRemovePlaceMentionProgram`. -/
theorem ce2_removePlaceMention_null_nonzero_offset_erases_ub :
    isSafePlaceMention (.rawDerefFieldOffset 1 8) = false ∧
    checkRemovePlaceMentionProgram singleBlockPtrCert
      progCe2NullFieldOffsetSrc progCe2NullFieldOffsetBadTgt = false ∧
    NegativeCanaryClaimV2 progCe2NullFieldOffsetSrc queryNullPtr
      .invalidPointerOffset .unsupported ∧
    PositiveCanaryClaimV2 progCe2NullFieldOffsetBadTgt queryNullPtr
      (u32Val 42) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact negativeCanaryV2_of_execFaultsV2 (fuel := 4)
      (by intro h; cases h) rfl
  · exact positiveCanaryV2_of_execReturnsV2 (fuel := 4) rfl

/-! ### Sharpness & RFC 2582 Witness 3 (`E3-22`): Zero-Offset Raw-Pointer `PlaceMention(*_1)` Is Defined on Both Misaligned and Null Pointers -/

noncomputable def progCe3Rfc2582RawDerefSrc : ProgramV2 where
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, rawConstU64Ty]
    isUnsafe := true
    identity := "ce3::rfc2582_raw_deref_place_mention"
    basicBlocks := [{
      statements := [
        .placeMention (.rawDeref 1),
        .v1 (.assign ⟨0, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩)))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progCe3Rfc2582RawDerefTgt : ProgramV2 where
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, rawConstU64Ty]
    isUnsafe := true
    identity := "ce3::rfc2582_raw_deref_place_mention"
    basicBlocks := [{
      statements := [
        .v1 .nop,
        .v1 (.assign ⟨0, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩)))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE3 (`E3-22` `place_mention_raw_deref_misaligned_u64`):**
Per RFC 2582, `PlaceMention(*_1)` on an initialized raw pointer `_1 : *const u64`
is well-formed and returns `42_u32` even when `_1` is misaligned (`offset = 1`)
or null (`allocId = none`), and its erasure to `.nop` passes
`checkRemovePlaceMentionProgram`. -/
theorem ce3_rfc2582_zero_offset_raw_deref_placeMention_defined :
    isSafePlaceMention (.rawDeref 1) = true ∧
    checkRemovePlaceMentionProgram singleBlockPtrCert
      progCe3Rfc2582RawDerefSrc progCe3Rfc2582RawDerefTgt = true ∧
    PositiveCanaryClaimV2 progCe3Rfc2582RawDerefSrc queryMisalignedPtr
      (u32Val 42) ∧
    PositiveCanaryClaimV2 progCe3Rfc2582RawDerefSrc queryNullPtr
      (u32Val 42) ∧
    PositiveCanaryClaimV2 progCe3Rfc2582RawDerefTgt queryMisalignedPtr
      (u32Val 42) ∧
    PositiveCanaryClaimV2 progCe3Rfc2582RawDerefTgt queryNullPtr
      (u32Val 42) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact positiveCanaryV2_of_execReturnsV2 (fuel := 4) rfl
  · exact positiveCanaryV2_of_execReturnsV2 (fuel := 4) rfl
  · exact positiveCanaryV2_of_execReturnsV2 (fuel := 4) rfl
  · exact positiveCanaryV2_of_execReturnsV2 (fuel := 4) rfl

/-! ### Sharpness Counterexample 4 (`E3-16`): `StatementKindV2.assume` Faults with `.unreachableExecuted` on `false` and Rejects Non-`bool` Operands -/

noncomputable def progCe4AssumeBool : ProgramV2 where
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, .bool]
    isUnsafe := true
    identity := "ce4::assume_bool"
    basicBlocks := [{
      statements := [
        .assume (.copy ⟨1, []⟩),
        .v1 (.assign ⟨0, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩)))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progCe4SwitchU32Src : ProgramV2 where
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce4::non_bool_switch_to_assume"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        }
      },
      { statements := [], terminator := .unreachable },
      {
        statements := [
          .v1 (.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def progCe4SwitchU32BadTgt : ProgramV2 where
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce4::non_bool_switch_to_assume"
    basicBlocks := [
      {
        statements := [.assume (.copy ⟨1, []⟩)]
        terminator := .goto 2
      },
      { statements := [], terminator := .unreachable },
      {
        statements := [
          .v1 (.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def ce4ThreeBlockCert : ProgramAbsCert := [[
  some [.liveUninit, .liveInit],
  some [.liveUninit, .liveInit],
  some [.liveUninit, .liveInit]
]]

/-- **Sharpness Theorem CE4 (`E3-16` `NonDivergingIntrinsic::Assume`):**
`StatementKindV2.assume (.copy ⟨1, []⟩)` faults with
`FaultKindV2.unreachableExecuted` on `.bool false`, returns `42_u32` on
`.bool true`, and `checkUnreachablePropAssumeProgram` rejects rewriting a
non-`.bool` `u32` `SwitchInt` into `.assume`. -/
theorem ce4_assume_false_faults_unreachableExecuted :
    NegativeCanaryClaimV2 progCe4AssumeBool { args := [.bool false] }
      .unreachableExecuted .unsupported ∧
    PositiveCanaryClaimV2 progCe4AssumeBool { args := [.bool true] }
      (u32Val 42) ∧
    checkUnreachablePropAssumeProgram ce4ThreeBlockCert
      progCe4SwitchU32Src progCe4SwitchU32BadTgt = false := by
  refine ⟨?_, ?_, rfl⟩
  · exact negativeCanaryV2_of_execFaultsV2 (fuel := 4)
      (by intro h; cases h) rfl
  · exact positiveCanaryV2_of_execReturnsV2 (fuel := 4) rfl

/-! ### Sharpness Counterexample 5 (`R3` / `E3-7`): Truncating a Referenced Trailing Local Slot Breaks `WellFormed` -/

noncomputable def progCe5CompactSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce5::compact_referenced_slot"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progCe5CompactBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce5::compact_referenced_slot"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE5 (`R3` `SimplifyLocals` Trailing-Slot Guard):**
Truncating `locals` from `3` to `2` while local `_2` is still referenced in
statements turns a well-formed execution returning `19_u32` into
`FaultKind.unsupported` and is rejected by `.compactUnusedTrailingLocals 2`. -/
theorem ce5_compactTrailingLocals_referenced_slot_unsound :
    checkMirOptStep (.compactUnusedTrailingLocals 2)
      progCe5CompactSrc progCe5CompactBadTgt = false ∧
    PositiveCanaryClaim progCe5CompactSrc
      { args := [u32Val 19] } (u32Val 19) ∧
    NegativeCanaryClaim progCe5CompactBadTgt
      { args := [u32Val 19] } .unsupported .undefined := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 5) rfl
  · exact negativeCanary_of_execFaults (fuel := 5) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 6 (`F1-7`): Propagating Copy Alias Across Clobber Is Rejected by `MirOptTrace` -/

noncomputable def progCe6ClobberSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce6::clobbered_copyprop"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨1, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progCe6ClobberBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce6::clobbered_copyprop"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨1, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def ce6CddCert : CopyDestDseCert where
  copyCert := [[some [.liveUninit, .liveInit, .liveUninit]]]
  destCert := [{
    liveCert := [some [.liveUninit, .liveInit, .liveUninit]]
    deadAtEntry := [[]]
  }]
  dseCert := [{
    nzCert := [some [.liveUninit, .liveInit, .liveUninit]]
    deadAtEntry := [[]]
  }]

/-- **Sharpness Theorem CE6:** Propagating `.copy ⟨2, []⟩ ↦ .copy ⟨1, []⟩`
across `_1 = const 99_u32` alters the return value from `10_u32` to `99_u32`
and is rejected by both `checkMirOptStep` and `checkMirOptTrace`. -/
theorem ce6_pipeline_clobbered_copyprop_unsound :
    checkMirOptStep (.copyAndDestPropAndDse ce6CddCert)
      progCe6ClobberSrc progCe6ClobberBadTgt = false ∧
    checkMirOptTrace [.copyAndDestPropAndDse ce6CddCert]
      progCe6ClobberSrc progCe6ClobberBadTgt = false ∧
    PositiveCanaryClaim progCe6ClobberSrc
      { args := [u32Val 10] } (u32Val 10) ∧
    PositiveCanaryClaim progCe6ClobberBadTgt
      { args := [u32Val 10] } (u32Val 99) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 6) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Multi-Step Non-Vacuous Witness 1: 5-Family End-to-End `MirOptTrace` (`pRaw -> p1 -> p2 -> p3 -> p4 -> p5`) -/

noncomputable def pipeLocals8 : List MirTy := [
  u32Ty, u32Ty, .bool, .bool, .bool, u32Ty, u32Ty, u32Ty
]

noncomputable def pipeLocals3 : List MirTy := [
  u32Ty, u32Ty, .bool
]

noncomputable def mkPipeProg (decls : List MirTy)
    (bb0Term bb1Term : TerminatorKind)
    (bb1Stmts : List StatementKind) : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := decls
    identity := "witness::five_family_whole_pipeline"
    basicBlocks := [
      {
        statements := []
        terminator := bb0Term
      },
      {
        statements := bb1Stmts
        terminator := bb1Term
      },
      {
        statements := []
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def bb0TermRaw : TerminatorKind :=
  .switchInt (.copy ⟨2, []⟩) {
    branches := [(BitVec.ofNat 128 0, 3), (BitVec.ofNat 128 1, 1)]
    otherwise := 3
  }

noncomputable def bb0TermPruned : TerminatorKind :=
  .switchInt (.copy ⟨2, []⟩) {
    branches := [(BitVec.ofNat 128 1, 1)]
    otherwise := 3
  }

noncomputable def bb1TermRaw : TerminatorKind :=
  .switchInt (.copy ⟨4, []⟩) {
    branches := [(BitVec.ofNat 128 0, 2)]
    otherwise := 2
  }

noncomputable def stmtsRawAndP1 : List StatementKind := [
  .assign ⟨3, []⟩ (.unaryOp .not (.copy ⟨2, []⟩)),
  .assign ⟨4, []⟩ (.unaryOp .not (.copy ⟨3, []⟩)),
  .assign ⟨5, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
  .assign ⟨6, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩)),
  .assign ⟨7, []⟩ (.binaryOp .add (.move ⟨6, []⟩) (.copy ⟨5, []⟩)),
  .assign ⟨0, []⟩ (.use (.move ⟨7, []⟩))
]

noncomputable def stmtsP2 : List StatementKind := [
  .assign ⟨3, []⟩ (.unaryOp .not (.copy ⟨2, []⟩)),
  .assign ⟨4, []⟩ (.use (.copy ⟨2, []⟩)),
  .assign ⟨5, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
  .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
  .assign ⟨7, []⟩ (.binaryOp .add (.move ⟨6, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
  .assign ⟨0, []⟩ (.use (.move ⟨7, []⟩))
]

noncomputable def stmtsP3 : List StatementKind := [
  .assign ⟨3, []⟩ (.unaryOp .not (.copy ⟨2, []⟩)),
  .assign ⟨4, []⟩ (.use (.copy ⟨2, []⟩)),
  .assign ⟨5, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
  .assign ⟨6, []⟩ (.use (.copy ⟨1, []⟩)),
  .assign ⟨7, []⟩ (.binaryOp .add (.copy ⟨6, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
  .assign ⟨0, []⟩ (.use (.move ⟨7, []⟩))
]

noncomputable def stmtsP4AndP5 : List StatementKind := [
  .nop,
  .nop,
  .nop,
  .nop,
  .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
  .nop
]

noncomputable def pRaw : Program :=
  mkPipeProg pipeLocals8 bb0TermRaw bb1TermRaw stmtsRawAndP1

noncomputable def p1 : Program :=
  mkPipeProg pipeLocals8 bb0TermPruned (.goto 2) stmtsRawAndP1

noncomputable def p2 : Program :=
  mkPipeProg pipeLocals8 bb0TermPruned (.goto 2) stmtsP2

noncomputable def p3 : Program :=
  mkPipeProg pipeLocals8 bb0TermPruned (.goto 2) stmtsP3

noncomputable def p4 : Program :=
  mkPipeProg pipeLocals8 bb0TermPruned (.goto 2) stmtsP4AndP5

noncomputable def p5 : Program :=
  mkPipeProg pipeLocals3 bb0TermPruned (.goto 2) stmtsP4AndP5

noncomputable def pipeAbsEnv8 : List AbsSlot := [
  .liveUninit, .liveInit, .liveInit, .liveUninit,
  .liveUninit, .liveUninit, .liveUninit, .liveUninit
]

noncomputable def pipeAbsCert4Blocks : ProgramAbsCert := [[
  some pipeAbsEnv8,
  some pipeAbsEnv8,
  some pipeAbsEnv8,
  some pipeAbsEnv8
]]

noncomputable def pipeConstEnv8 : List ConstAbsSlot := [
  .liveUninit, .liveUnknown, .liveUnknown, .liveUninit,
  .liveUninit, .liveUninit, .liveUninit, .liveUninit
]

noncomputable def pipeConstCert4Blocks : ProgramConstCert := [[
  some pipeConstEnv8,
  some pipeConstEnv8,
  some pipeConstEnv8,
  some pipeConstEnv8
]]

noncomputable def pipeDeadCertStep3 : ProgramDeadCert := [[
  [], [], [6], []
]]

noncomputable def pipeNzEnv8 : List NonZeroAbsSlot := [
  .liveUninit, .liveInit, .liveInit, .liveUninit,
  .liveUninit, .liveUninit, .liveUninit, .liveUninit
]

noncomputable def pipeCddCertStep4 : CopyDestDseCert where
  copyCert := pipeAbsCert4Blocks
  destCert := [{
    liveCert := pipeAbsCert4Blocks.headD []
    deadAtEntry := [[], [], [7], []]
  }]
  dseCert := [{
    nzCert := [
      some pipeNzEnv8,
      some pipeNzEnv8,
      some pipeNzEnv8,
      some pipeNzEnv8
    ]
    deadAtEntry := [[], [], [3, 4, 5, 6], []]
  }]

noncomputable def step1SimplifyCfg : MirOptStep :=
  .simplifyCfgBranch pipeAbsCert4Blocks

noncomputable def step2InstSimplify : MirOptStep :=
  .instSimplifyAlgAndConst pipeConstCert4Blocks

noncomputable def step3MoveToCopy : MirOptStep :=
  .moveToCopyDead pipeDeadCertStep3

noncomputable def step4CopyDestDse : MirOptStep :=
  .copyAndDestPropAndDse pipeCddCertStep4

noncomputable def step5CompactLocals : MirOptStep :=
  .compactUnusedTrailingLocals 3

noncomputable def fiveFamilyWholeTrace : MirOptTrace := [
  step1SimplifyCfg,
  step2InstSimplify,
  step3MoveToCopy,
  step4CopyDestDse,
  step5CompactLocals
]

noncomputable def body0LocalCount (p : Program) : Nat :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | some b => b.locals.length
  | none => 0

/-- **Constructive Witness 1 (`witness_five_family_whole_pipeline_nonvacuous`):**
Concrete 5-step `MirOptTrace` (`pRaw -> p1 -> p2 -> p3 -> p4 -> p5`) exercising
all 5 pass families in sequence (`.simplifyCfgBranch`,
`.instSimplifyAlgAndConst`, `.moveToCopyDead`, `.copyAndDestPropAndDse`, and
`.compactUnusedTrailingLocals 3`), compacting `locals` from `8` slots down to
`3` with `pRaw ≠ p5`, `checkMirOptTrace fiveFamilyWholeTrace pRaw p5 = true`,
and `PositiveCanaryClaim` proved on both `pRaw` and `p5`. -/
theorem witness_five_family_whole_pipeline_nonvacuous :
    checkMirOptStep step1SimplifyCfg pRaw p1 = true ∧
    checkMirOptStep step2InstSimplify p1 p2 = true ∧
    checkMirOptStep step3MoveToCopy p2 p3 = true ∧
    checkMirOptStep step4CopyDestDse p3 p4 = true ∧
    checkMirOptStep step5CompactLocals p4 p5 = true ∧
    checkMirOptTrace fiveFamilyWholeTrace pRaw p5 = true ∧
    pRaw ≠ p5 ∧
    Nat.blt (body0LocalCount p5) (body0LocalCount pRaw) = true ∧
    PositiveCanaryClaim pRaw { args := [u32Val 32, .bool true] } (u32Val 42) ∧
    PositiveCanaryClaim p5 { args := [u32Val 32, .bool true] } (u32Val 42) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · intro hEq
    have hLen : body0LocalCount pRaw = body0LocalCount p5 := by
      rw [hEq]
    cases hLen
  · exact positiveCanary_of_execReturns (fuel := 14) rfl
  · exact positiveCanary_of_execReturns (fuel := 14) rfl

/-! ### Multi-Step Non-Vacuous Witness 2: `MirProfileV2` `RemovePlaceMention` + `UnreachablePropagation` (`pV2_0 -> pV2_1 -> pV2_2`) -/

noncomputable def pV2_0 : ProgramV2 where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 3
    locals := [u32Ty, rawConstU64Ty, .bool, u32Ty]
    isUnsafe := true
    identity := "witness::profile_v2_place_mention_and_assume"
    basicBlocks := [
      {
        statements := [
          .placeMention (.local 3),
          .placeMention (.rawDeref 1),
          .placeMention (.rawDerefFieldOffset 1 0)
        ]
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        }
      },
      {
        statements := []
        terminator := .unreachable
      },
      {
        statements := [
          .v1 (.assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩)))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def pV2_1 : ProgramV2 where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 3
    locals := [u32Ty, rawConstU64Ty, .bool, u32Ty]
    isUnsafe := true
    identity := "witness::profile_v2_place_mention_and_assume"
    basicBlocks := [
      {
        statements := [
          .v1 .nop,
          .v1 .nop,
          .v1 .nop
        ]
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        }
      },
      {
        statements := []
        terminator := .unreachable
      },
      {
        statements := [
          .v1 (.assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩)))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def pV2_2 : ProgramV2 where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 2
  profileMode := .v2Extended
  bodies := [{
    argumentCount := 3
    locals := [u32Ty, rawConstU64Ty, .bool, u32Ty]
    isUnsafe := true
    identity := "witness::profile_v2_place_mention_and_assume"
    basicBlocks := [
      {
        statements := [
          .v1 .nop,
          .v1 .nop,
          .v1 .nop,
          .assume (.copy ⟨2, []⟩)
        ]
        terminator := .goto 2
      },
      {
        statements := []
        terminator := .unreachable
      },
      {
        statements := [
          .v1 (.assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩)))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def pipeV2Env : List AbsSlot := [
  .liveUninit, .liveInit, .liveInit, .liveInit
]

noncomputable def pipeV2Cert : ProgramAbsCert := [[
  some pipeV2Env,
  some pipeV2Env,
  some pipeV2Env
]]

noncomputable def body0Bb0StmtCountV2 (p : ProgramV2) : Nat :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | some b =>
    match Trusted.MirSemantics.getElem? b.basicBlocks 0 with
    | some bb => bb.statements.length
    | none => 0
  | none => 0

/-- **Constructive Witness 2 (`witness_profileV2_placeMention_and_assume_pipeline`):**
Concrete 2-stage `MirProfileV2` pipeline (`pV2_0 -> pV2_1 -> pV2_2`) erasing
local and RFC 2582 zero-offset raw-pointer `PlaceMention`s (`E3-22`) and
lowering `SwitchInt(copy _2) -> [0: bb1_unreachable, otherwise: bb2]` into
`.assume (copy _2); Goto bb2` (`E3-16`), preserving `42_u32` on a misaligned
pointer with `true` guard and `.fault .unreachableExecuted` on a null pointer
with `false` guard. -/
theorem witness_profileV2_placeMention_and_assume_pipeline :
    checkRemovePlaceMentionProgram pipeV2Cert pV2_0 pV2_1 = true ∧
    checkUnreachablePropAssumeProgram pipeV2Cert pV2_1 pV2_2 = true ∧
    pV2_0 ≠ pV2_2 ∧
    PositiveCanaryClaimV2 pV2_0
      { args := [misalignedPtrVal, .bool true, u32Val 40] } (u32Val 42) ∧
    PositiveCanaryClaimV2 pV2_2
      { args := [misalignedPtrVal, .bool true, u32Val 40] } (u32Val 42) ∧
    NegativeCanaryClaimV2 pV2_0
      { args := [nullPtrVal, .bool false, u32Val 40] }
      .unreachableExecuted .unsupported ∧
    NegativeCanaryClaimV2 pV2_2
      { args := [nullPtrVal, .bool false, u32Val 40] }
      .unreachableExecuted .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hLen : body0Bb0StmtCountV2 pV2_0 = body0Bb0StmtCountV2 pV2_2 := by
      rw [hEq]
    cases hLen
  · exact positiveCanaryV2_of_execReturnsV2 (fuel := 10) rfl
  · exact positiveCanaryV2_of_execReturnsV2 (fuel := 10) rfl
  · exact negativeCanaryV2_of_execFaultsV2 (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanaryV2_of_execFaultsV2 (fuel := 10)
      (by intro h; cases h) rfl

end VrustcFormal.F1_9
