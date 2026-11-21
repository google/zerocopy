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

namespace VrustcFormal.F1_7

open Trusted.MirAst Trusted.MirSemantics

/-!
# Direct `Trusted.MirSemantics` Bridge: Post-`SimplifyCfg` `CopyProp`, `DeadStoreElimination`, and `DestinationPropagation` (`VrustcFormal.F1_7`)

This module formalizes the three post-`SimplifyCfg-final` MIR optimization
passes scheduled at the tail of `optimized_mir` in
`compiler/rustc_mir_transform/src/lib.rs:760-762` (`copy_prop.rs`,
`dead_store_elimination.rs`, and `dest_prop.rs`, together with
`Rvalue::is_safe_to_remove` in
`compiler/rustc_middle/src/mir/statement.rs:774-810`, grounded in `rustc`
commits `8144389c895da997dbdecaa635e41d6a50be6ffd` and `E3-10` empirical census
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) directly over Anneal's unmodified
TCB syntax (`Trusted.MirAst`) and small-step operational semantics
(`Trusted.MirSemantics`).

All public theorem statements reference strictly `Init.*`, `Trusted.MirAst.*`,
`Trusted.MirSemantics.*`, and pure definitions in `VrustcFormal.F1_7` (zero
surrogate MIR AST, zero `Anneal.*` references).

## Ground-Truth Semantic Findings (`E3-10`) Mechanized Directly on $M_{\text{anneal}}$

1. **Certified `CopyProp` & `Move`-Head Unification (`copy_prop.rs:12-194`,
   `zerocopy` census `-138` assigns / `-133` copy-move assigns):**
   - Straight-line copy propagation after `_dst = Use(Copy(_src))` (`dst ≠ src`,
     matching `MirTy`) rewrites subsequent `.copy ⟨dst, []⟩` -> `.copy ⟨src, []⟩`
     (in `Rvalue` and `TerminatorKind.switchInt`) and
     `.discriminant ⟨dst, []⟩` -> `.discriminant ⟨src, []⟩` up until any
     write, `Operand.move`, borrow, `StorageLive`, or `StorageDead` touching
     `dst` or `src`. Paired with a flow-sensitive liveness/initialization
     certificate, `CopyProp` satisfies `FullSemanticEquiv pSrc pTgt` (`↔`).
   - Propagating across a clobber of `src` (`ce_copyprop_clobbered_src_unsound`),
     propagating a `.move` head without eliminating the move itself under
     `deinitMovedPlace = true`
     (`ce_copyprop_move_deinit_without_head_elim_unsound`), or propagating past
     `StorageDead(src)` (`ce_copyprop_storage_dead_src_unsound`) is unsound.
   - Adjacent `Move`-head single-use unification (`_dst = Use(Move(_src));
     _out = rval[move _dst]` -> `.nop; _out = rval[move _src]` when `dst ≠ 0`,
     `dst ≠ src`, `src` is `.liveInit`, `dst` is `.live` and dead afterward)
     restores exact 2-step bidirectional equivalence (`↔`).

2. **`DeadStoreElimination` (`dead_store_elimination.rs:34-155`) & Live `E3-10`
   `Rvalue::is_safe_to_remove()` UB-Erasure Asymmetry (`statement.rs:774-810`):**
   - Upstream `Rvalue::is_safe_to_remove()` marks `Rvalue::BinaryOp`, `Use`,
     `UnaryOp`, and `Discriminant` unconditionally removable when the assigned
     local is dead—silently erasing `DivisionByZero` UB (`custom_mir_div_zero_dead_local`
     in `E3-10`, mechanized by `ce_dse_is_safe_to_remove_div_zero_erases_ub`),
     uninitialized-read UB (`ce_dse_is_safe_to_remove_uninit_read_erases_ub`),
     and `DeadLocal` write-time UB (`ce_dse_dead_dst_slot_erases_write_deadlocal_ub`),
     even under `-Zmir-preserve-ub=yes`!
   - On $M_{\text{anneal}}$, eliminating a dead assignment `_dst = rval` -> `.nop`
     with no `Operand.move` of any `l ≠ dst` (`ce_dse_move_live_src_reverse_unsound`)
     satisfies **`ForwardCodegenRefines pSrc pTgt` unconditionally** (`Theorem 2a`),
     while **`FullSemanticEquiv pSrc pTgt` (`↔`)** (`Theorem 2b`) holds under a
     flow-sensitive initialization + non-zero/total-rvalue certificate.

3. **Certified `DestinationPropagation` (`dest_prop.rs:16-160`, `zerocopy`
   census `-58` copy-move assigns):**
   - Fusing `_tmp = rval; _dst = Use(Move(_tmp) | Copy(_tmp))` into
     `_dst = rval; .nop` when `tmp ≠ 0`, `tmp ≠ dst`, `MirTy.beq`, both `tmp`
     and `dst` are certified `.live`, and `tmp` is dead on all paths afterward
     satisfies **`FullSemanticEquiv pSrc pTgt` (`↔`)**—including self-updates
     `_tmp = _dst + 1; _dst = move _tmp -> _dst = _dst + 1; .nop` because
     `evalStatement` evaluates `rval` before `writePlace`
     (`witness_destprop_self_update_exact`), whereas hoisting `_dst = rval` past
     an intervening reader is unsound (`ce_destprop_hoist_past_reader_unsound`).
-/

/-! ## Part I: Structural Equality & Executable Post-`SimplifyCfg` Pass Predicates -/

/-- Pairwise boolean relation over two lists of equal length. -/
noncomputable def listRel {α β : Type} (r : α → β → Bool) :
    List α → List β → Bool
  | [], [] => true
  | x :: xs, y :: ys => r x y && listRel r xs ys
  | _, _ => false

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

/-- Structural equality on `VerificationScope`. -/
noncomputable def scopeEq : VerificationScope → VerificationScope → Bool
  | .unit, .unit | .crate, .crate => true
  | _, _ => false

/-- Shared body-metadata equality (`argumentCount`, `locals`, `isUnsafe`, `identity`). -/
noncomputable def bodyHeaderEq (b₁ b₂ : Body) : Bool :=
  Nat.beq b₁.argumentCount b₂.argumentCount &&
    MirTy.beqList b₁.locals b₂.locals &&
    (b₁.isUnsafe == b₂.isUnsafe) &&
    stringBeq b₁.identity b₂.identity

/-- Shared program-header equality (`pointerWidthBits`, `mirProfileVersion`, `entryDefId`, `scope`). -/
noncomputable def programHeaderEq (p₁ p₂ : Program) : Bool :=
  Nat.beq p₁.pointerWidthBits p₂.pointerWidthBits &&
    Nat.beq p₁.mirProfileVersion p₂.mirProfileVersion &&
    Nat.beq p₁.entryDefId p₂.entryDefId &&
    scopeEq p₁.scope p₂.scope

/-! ### Local-Use, Move, and Intra-Block Deadness Helpers -/

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

/-- Intra-block deadness check (`isDeadInBlockFrom d stmts term`): returns `true`
iff `d` (`d ≠ 0` checked by callers) is never read or touched in `stmts` before
being completely overwritten by an unprojected `.assign ⟨d, []⟩`,
`StorageLive(d)`, `StorageDead(d)`, or reaching `TerminatorKind.return_` /
`TerminatorKind.unreachable`. -/
noncomputable def isDeadInBlockFrom (d : LocalId) :
    List StatementKind → TerminatorKind → Bool
  | [], .return_ => true
  | [], .unreachable => true
  | [], _ => false
  | .nop :: rest, term => isDeadInBlockFrom d rest term
  | .storageLive id :: rest, term =>
    if Nat.beq id d then true else isDeadInBlockFrom d rest term
  | .storageDead id :: rest, term =>
    if Nat.beq id d then true else isDeadInBlockFrom d rest term
  | .assign lhs rv :: rest, term =>
    !rvalueTouchesLocal d rv &&
      if lhs.projection.isEmpty && Nat.beq lhs.localId d then
        true
      else
        isDeadInBlockFrom d rest term
  | .unsupported :: _, _ => false

/-! ### Pass 1a: Block-Local `CopyProp` (`copy_prop.rs:12-194`) -/

/-- Active copy-alias list `[(dst, src), ...]` inside a basic block, recording
that `dst` currently holds a live copy of `src` with identical `MirTy`. -/
abbrev CopyAliases := List (LocalId × LocalId)

/-- Lookup the canonical source local for `d` in `aliases`, if any. -/
noncomputable def lookupCopyAlias (d : LocalId) : CopyAliases → Option LocalId
  | [] => none
  | (dst, src) :: rest =>
    if Nat.beq d dst then some src else lookupCopyAlias d rest

/-- Kill every alias `(dst, src)` in `aliases` that mentions `id`. -/
noncomputable def killCopyAliasesTouching (id : LocalId) :
    CopyAliases → CopyAliases
  | [] => []
  | (dst, src) :: rest =>
    if Nat.beq dst id || Nat.beq src id then
      killCopyAliasesTouching id rest
    else
      (dst, src) :: killCopyAliasesTouching id rest

/-- Retain only aliases `(dst, src)` where neither `dst` nor `src` is mutated or
borrowed by `rv`. Preventing propagation across an `Rvalue` that moves `src` or
`dst` closes intra-statement move-before-copy hazards such as
`BinaryOp(.add, .move ⟨src, []⟩, .copy ⟨dst, []⟩)`. -/
noncomputable def filterAliasesForRvalue (rv : Rvalue) :
    CopyAliases → CopyAliases
  | [] => []
  | (dst, src) :: rest =>
    if rvalueMutatesOrBorrowsLocal dst rv ||
        rvalueMutatesOrBorrowsLocal src rv then
      filterAliasesForRvalue rv rest
    else
      (dst, src) :: filterAliasesForRvalue rv rest

/-- Check whether `opTgt` is either equal to `opSrc` or rewrites
`.copy ⟨dst, []⟩` to `.copy ⟨src, []⟩` for `(dst, src)` in `aliases`. -/
noncomputable def isCopyPropOperand (aliases : CopyAliases)
    (opSrc opTgt : Operand) : Bool :=
  operandEq opSrc opTgt ||
    match opSrc, opTgt with
    | .copy pSrc, .copy pTgt =>
      pSrc.projection.isEmpty && pTgt.projection.isEmpty &&
        match lookupCopyAlias pSrc.localId aliases with
        | some src => Nat.beq pTgt.localId src
        | none => false
    | _, _ => false

/-- Check whether `rvTgt` is obtained from `rvSrc` by optional `.copy` and
`.discriminant` propagation under `aliases` (filtered for `rvSrc` moves). -/
noncomputable def isCopyPropRvalue (aliases : CopyAliases)
    (rvSrc rvTgt : Rvalue) : Bool :=
  let safeAliases := filterAliasesForRvalue rvSrc aliases
  rvalueEq rvSrc rvTgt ||
    match rvSrc, rvTgt with
    | .use o₁, .use o₂ => isCopyPropOperand safeAliases o₁ o₂
    | .unaryOp op₁ o₁, .unaryOp op₂ o₂ =>
      unOpEq op₁ op₂ && isCopyPropOperand safeAliases o₁ o₂
    | .binaryOp op₁ l₁ r₁, .binaryOp op₂ l₂ r₂ =>
      binOpEq op₁ op₂ &&
        isCopyPropOperand safeAliases l₁ l₂ &&
        isCopyPropOperand safeAliases r₁ r₂
    | .discriminant p₁, .discriminant p₂ =>
      p₁.projection.isEmpty && p₂.projection.isEmpty &&
        match lookupCopyAlias p₁.localId safeAliases with
        | some src => Nat.beq p₂.localId src
        | none => false
    | _, _ => false

/-- Advance block-local `CopyProp` across one `(sSrc, sTgt)` statement pair. -/
noncomputable def stepCopyPropSyntactic (bodyLocals : List MirTy)
    (aliases : CopyAliases) (sSrc sTgt : StatementKind) : Option CopyAliases :=
  match sSrc, sTgt with
  | .nop, .nop => some aliases
  | .unsupported, .unsupported => some []
  | .storageLive i₁, .storageLive i₂ =>
    if Nat.beq i₁ i₂ then some (killCopyAliasesTouching i₁ aliases) else none
  | .storageDead i₁, .storageDead i₂ =>
    if Nat.beq i₁ i₂ then some (killCopyAliasesTouching i₁ aliases) else none
  | .assign dst rvSrc, .assign dst' rvTgt =>
    if !(placeEq dst dst' && isCopyPropRvalue aliases rvSrc rvTgt) then
      none
    else
      let afterRval := filterAliasesForRvalue rvSrc aliases
      let afterKill := killCopyAliasesTouching dst.localId afterRval
      if !dst.projection.isEmpty then
        some afterKill
      else
        match rvTgt with
        | .use (.copy pHead) =>
          if pHead.projection.isEmpty && !Nat.beq dst.localId pHead.localId then
            match Trusted.MirSemantics.getElem? bodyLocals dst.localId,
                Trusted.MirSemantics.getElem? bodyLocals pHead.localId with
            | some dstTy, some srcTy =>
              if MirTy.beq dstTy srcTy then
                some ((dst.localId, pHead.localId) :: afterKill)
              else
                some afterKill
            | _, _ => some afterKill
          else
            some afterKill
        | _ => some afterKill
  | _, _ => none

noncomputable def stepCopyPropStmtsSyntactic (bodyLocals : List MirTy) :
    CopyAliases → List StatementKind → List StatementKind → Option CopyAliases
  | aliases, [], [] => some aliases
  | aliases, sSrc :: restSrc, sTgt :: restTgt =>
    match stepCopyPropSyntactic bodyLocals aliases sSrc sTgt with
    | none => none
    | some aliases' =>
      stepCopyPropStmtsSyntactic bodyLocals aliases' restSrc restTgt
  | _, _, _ => none

noncomputable def isCopyPropTerminator (aliases : CopyAliases)
    (tSrc tTgt : TerminatorKind) : Bool :=
  terminatorEq tSrc tTgt ||
    match tSrc, tTgt with
    | .switchInt d₁ ts₁, .switchInt d₂ ts₂ =>
      isCopyPropOperand aliases d₁ d₂ && switchTargetsEq ts₁ ts₂
    | _, _ => false

noncomputable def isCopyPropBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    match stepCopyPropStmtsSyntactic bodyLocals []
        b₁.statements b₂.statements with
    | none => false
    | some exitAliases =>
      isCopyPropTerminator exitAliases b₁.terminator b₂.terminator

noncomputable def isCopyPropBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isCopyPropBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isCopyPropProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isCopyPropBody pSrc.bodies pTgt.bodies

/-! ### Pass 1b: Single-Use `Move`-Head Unification (`copy_prop.rs:14-21, 127-156`) -/

/-- Match `rvSrc` against `rvTgt` where `rvSrc` moves `dst` (`⟨dst, []⟩`)
exactly once, `rvTgt` replaces that move with `.move ⟨src, []⟩`, and neither
`dst` nor `src` is touched elsewhere in the rvalue. -/
noncomputable def isMoveHeadRvaluePair (dst src : LocalId) :
    Rvalue → Rvalue → Bool
  | .use (.move p₁), .use (.move p₂) =>
    p₁.projection.isEmpty && p₂.projection.isEmpty &&
      Nat.beq p₁.localId dst && Nat.beq p₂.localId src
  | .unaryOp op₁ (.move p₁), .unaryOp op₂ (.move p₂) =>
    unOpEq op₁ op₂ &&
      p₁.projection.isEmpty && p₂.projection.isEmpty &&
      Nat.beq p₁.localId dst && Nat.beq p₂.localId src
  | .binaryOp op₁ (.move p₁) r₁, .binaryOp op₂ (.move p₂) r₂ =>
    binOpEq op₁ op₂ &&
      p₁.projection.isEmpty && p₂.projection.isEmpty &&
      Nat.beq p₁.localId dst && Nat.beq p₂.localId src &&
      operandEq r₁ r₂ &&
      !operandTouchesLocal dst r₁ && !operandTouchesLocal src r₁
  | .binaryOp op₁ l₁ (.move p₁), .binaryOp op₂ l₂ (.move p₂) =>
    binOpEq op₁ op₂ &&
      p₁.projection.isEmpty && p₂.projection.isEmpty &&
      Nat.beq p₁.localId dst && Nat.beq p₂.localId src &&
      operandEq l₁ l₂ &&
      !operandTouchesLocal dst l₁ && !operandTouchesLocal src l₁
  | _, _ => false

/-- Match an adjacent `Move`-head unification pair:
`s₁ = (_dst = Use(Move(_src))); s₂ = (_out = rv[move _dst])` rewritten to
`t₁ = .nop; t₂ = (_out = rv[move _src])`. -/
noncomputable def isMoveHeadUnifyPair (bodyLocals : List MirTy)
    (s₁ s₂ t₁ t₂ : StatementKind) (restTgt : List StatementKind)
    (termTgt : TerminatorKind) : Bool :=
  match s₁, s₂, t₁, t₂ with
  | .assign dPlace (.use (.move sPlace)), .assign out₁ rvSrc,
      .nop, .assign out₂ rvTgt =>
    dPlace.projection.isEmpty &&
      sPlace.projection.isEmpty &&
      out₁.projection.isEmpty &&
      placeEq out₁ out₂ &&
      (let dst := dPlace.localId
       let src := sPlace.localId
       let out := out₁.localId
       !Nat.beq dst 0 &&
         !Nat.beq dst src &&
         Nat.blt out bodyLocals.length &&
         (match Trusted.MirSemantics.getElem? bodyLocals dst,
              Trusted.MirSemantics.getElem? bodyLocals src with
          | some dstTy, some srcTy => MirTy.beq dstTy srcTy
          | _, _ => false) &&
         isMoveHeadRvaluePair dst src rvSrc rvTgt &&
         (Nat.beq out dst || isDeadInBlockFrom dst restTgt termTgt))
  | _, _, _, _ => false

noncomputable def isMoveHeadUnifyStmts (bodyLocals : List MirTy)
    (termTgt : TerminatorKind) :
    List StatementKind → List StatementKind → Bool
  | [], [] => true
  | s₁ :: s₂ :: restSrc, t₁ :: t₂ :: restTgt =>
    if isMoveHeadUnifyPair bodyLocals s₁ s₂ t₁ t₂ restTgt termTgt then
      isMoveHeadUnifyStmts bodyLocals termTgt restSrc restTgt
    else
      stmtEq s₁ t₁ &&
        isMoveHeadUnifyStmts bodyLocals termTgt (s₂ :: restSrc) (t₂ :: restTgt)
  | [s₁], [t₁] => stmtEq s₁ t₁
  | _, _ => false

noncomputable def isMoveHeadUnifyBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    terminatorEq b₁.terminator b₂.terminator &&
    isMoveHeadUnifyStmts bodyLocals b₂.terminator b₁.statements b₂.statements

noncomputable def isMoveHeadUnifyBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isMoveHeadUnifyBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isMoveHeadUnifyProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isMoveHeadUnifyBody pSrc.bodies pTgt.bodies

/-! ### Pass 2: `DeadStoreElimination` (`dead_store_elimination.rs:34-155`) -/

/-- Match a single dead-store elimination rewrite `.assign ⟨dst, []⟩ rval ↦ .nop`
where `dst ≠ 0`, `dst < bodyLocals.length`, `rval` moves no local `l ≠ dst`,
and `dst` is dead in the remaining block (`restTgt`, `termTgt`). -/
noncomputable def isDseMoveFreeElim (bodyLocals : List MirTy)
    (sSrc sTgt : StatementKind) (restTgt : List StatementKind)
    (termTgt : TerminatorKind) : Bool :=
  match sSrc, sTgt with
  | .assign dstPlace rval, .nop =>
    dstPlace.projection.isEmpty &&
      !Nat.beq dstPlace.localId 0 &&
      Nat.blt dstPlace.localId bodyLocals.length &&
      rvalueNoMoveExcept dstPlace.localId rval &&
      isDeadInBlockFrom dstPlace.localId restTgt termTgt
  | _, _ => false

noncomputable def isDseMoveFreeStmts (bodyLocals : List MirTy)
    (termTgt : TerminatorKind) :
    List StatementKind → List StatementKind → Bool
  | [], [] => true
  | sSrc :: restSrc, sTgt :: restTgt =>
    (isDseMoveFreeElim bodyLocals sSrc sTgt restTgt termTgt ||
      stmtEq sSrc sTgt) &&
      isDseMoveFreeStmts bodyLocals termTgt restSrc restTgt
  | _, _ => false

noncomputable def isDseMoveFreeBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    terminatorEq b₁.terminator b₂.terminator &&
    isDseMoveFreeStmts bodyLocals b₂.terminator b₁.statements b₂.statements

noncomputable def isDseMoveFreeBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isDseMoveFreeBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isDseMoveFreeProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isDseMoveFreeBody pSrc.bodies pTgt.bodies

/-! ### Pass 3: Adjacent `DestinationPropagation` (`dest_prop.rs:16-160`) -/

/-- Match `.use (.move ⟨tmp, []⟩)` or `.use (.copy ⟨tmp, []⟩)`. -/
noncomputable def isDestPropCopyOrMoveTmp (tmp : LocalId) : Rvalue → Bool
  | .use (.move p) | .use (.copy p) =>
    p.projection.isEmpty && Nat.beq p.localId tmp
  | _ => false

/-- Structural match for an adjacent destination-propagation fusion pair:
`s₁ = (_tmp = rval); s₂ = (_dst = Use(Move(_tmp) | Copy(_tmp)))` fused into
`t₁ = (_dst = rval); t₂ = .nop` with `tmp ≠ 0`, `tmp ≠ dst`, `!rvalueTouchesLocal
tmp rval`, and `MirTy.beq bodyLocals[tmp] bodyLocals[dst]`. -/
noncomputable def isDestPropPairCore (bodyLocals : List MirTy)
    (s₁ s₂ t₁ t₂ : StatementKind) : Option LocalId :=
  match s₁, s₂, t₁, t₂ with
  | .assign tmpPlace rv₁, .assign dstPlace rvUse,
      .assign dstPlace' rv₂, .nop =>
    if !(tmpPlace.projection.isEmpty &&
          dstPlace.projection.isEmpty &&
          placeEq dstPlace dstPlace' &&
          rvalueEq rv₁ rv₂) then
      none
    else
      let tmp := tmpPlace.localId
      let dst := dstPlace.localId
      if !Nat.beq tmp 0 &&
          !Nat.beq tmp dst &&
          !rvalueTouchesLocal tmp rv₁ &&
          isDestPropCopyOrMoveTmp tmp rvUse then
        match Trusted.MirSemantics.getElem? bodyLocals tmp,
            Trusted.MirSemantics.getElem? bodyLocals dst with
        | some tmpTy, some dstTy =>
          if MirTy.beq tmpTy dstTy then some tmp else none
        | _, _ => none
      else
        none
  | _, _, _, _ => none

noncomputable def isDestPropStmts (bodyLocals : List MirTy) :
    List StatementKind → List StatementKind → Bool
  | [], [] => true
  | s₁ :: s₂ :: restSrc, t₁ :: t₂ :: restTgt =>
    match isDestPropPairCore bodyLocals s₁ s₂ t₁ t₂ with
    | some _ => isDestPropStmts bodyLocals restSrc restTgt
    | none =>
      stmtEq s₁ t₁ && isDestPropStmts bodyLocals (s₂ :: restSrc) (t₂ :: restTgt)
  | [s₁], [t₁] => stmtEq s₁ t₁
  | _, _ => false

noncomputable def isDestPropBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    terminatorEq b₁.terminator b₂.terminator &&
    isDestPropStmts bodyLocals b₁.statements b₂.statements

noncomputable def isDestPropBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isDestPropBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isDestPropProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isDestPropBody pSrc.bodies pTgt.bodies

/-! ## Part II: Semantic Relations & Decidable Flow-Sensitive Certificates -/

/-- Whether `ty` is an inhabited 0-byte ZST whose `liveUninitSlot` is already
initialized (`MirTy.unit` or an admitted 1-variant `.zeroSized` enum). -/
noncomputable def isAlwaysInhabitedZst (ty : MirTy) : Bool :=
  match ty with
  | .unit => true
  | .enum ety => isZstEnumTy ety
  | _ => false

/-- Check that `bSrc` and `bTgt` have identical `storageAnnotationsInBounds` and
per-local `hasStorageAnnotation` bits across all locals. -/
noncomputable def preservesAllStorageAnnotationsLoop (bSrc bTgt : Body) :
    Nat → Bool
  | 0 => true
  | idx + 1 =>
    (hasStorageAnnotation bSrc idx == hasStorageAnnotation bTgt idx) &&
      preservesAllStorageAnnotationsLoop bSrc bTgt idx

noncomputable def preservesAllStorageAnnotations (bSrc bTgt : Body) : Bool :=
  (storageAnnotationsInBounds bSrc == storageAnnotationsInBounds bTgt) &&
    preservesAllStorageAnnotationsLoop bSrc bTgt bSrc.locals.length

/-! ### Shared 3-Point Liveness & Initialization Lattice (`AbsSlot`) -/

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

/-! ### Certificate 1a (`checkCopyPropProgram`): Liveness & Init Certificate for `CopyProp` -/

/-- Step `(aliases, env)` across a `CopyProp` statement pair, admitting a new
copy alias `(dst, pHead)` only when `pHead` is certified `.liveInit` and `dst`
is certified `.live` (`absSlotImplies dstSlot .liveUninit`) at the copy point so
`writePlace` cannot fault on a `.dead` `dst`. -/
noncomputable def stepCopyPropCertStmt (bodyLocals : List MirTy)
    (aliases : CopyAliases) (env : List AbsSlot)
    (sSrc sTgt : StatementKind) : Option (CopyAliases × List AbsSlot) :=
  match sSrc, sTgt with
  | .nop, .nop => some (aliases, env)
  | .unsupported, .unsupported => some ([], env)
  | .storageLive i₁, .storageLive i₂ =>
    if !Nat.beq i₁ i₂ then none
    else
      match stepPlainStmtAbs bodyLocals env sSrc with
      | none => none
      | some env' => some (killCopyAliasesTouching i₁ aliases, env')
  | .storageDead i₁, .storageDead i₂ =>
    if !Nat.beq i₁ i₂ then none
    else
      match stepPlainStmtAbs bodyLocals env sSrc with
      | none => none
      | some env' => some (killCopyAliasesTouching i₁ aliases, env')
  | .assign dst rvSrc, .assign dst' rvTgt =>
    if !(placeEq dst dst' && dst.projection.isEmpty &&
          isCopyPropRvalue aliases rvSrc rvTgt) then
      none
    else
      match stepPlainStmtAbs bodyLocals env sSrc with
      | none => none
      | some env' =>
        let afterRval := filterAliasesForRvalue rvSrc aliases
        let afterKill := killCopyAliasesTouching dst.localId afterRval
        match rvTgt with
        | .use (.copy pHead) =>
          if pHead.projection.isEmpty && !Nat.beq dst.localId pHead.localId then
            match Trusted.MirSemantics.getElem? bodyLocals dst.localId,
                Trusted.MirSemantics.getElem? bodyLocals pHead.localId,
                Trusted.MirSemantics.getElem? env dst.localId,
                Trusted.MirSemantics.getElem? env pHead.localId with
            | some dstTy, some srcTy, some dstSlot, some .liveInit =>
              if MirTy.beq dstTy srcTy &&
                  isSupportedScalarOrUnitTy dstTy &&
                  absSlotImplies dstSlot .liveUninit then
                some ((dst.localId, pHead.localId) :: afterKill, env')
              else
                some (afterKill, env')
            | _, _, _, _ => some (afterKill, env')
          else
            some (afterKill, env')
        | _ => some (afterKill, env')
  | _, _ => none

noncomputable def stepCopyPropCertStmts (bodyLocals : List MirTy) :
    CopyAliases → List AbsSlot → List StatementKind → List StatementKind →
    Option (CopyAliases × List AbsSlot)
  | aliases, env, [], [] => some (aliases, env)
  | aliases, env, sSrc :: restSrc, sTgt :: restTgt =>
    match stepCopyPropCertStmt bodyLocals aliases env sSrc sTgt with
    | none => none
    | some (aliases', env') =>
      stepCopyPropCertStmts bodyLocals aliases' env' restSrc restTgt
  | _, _, _, _ => none

noncomputable def checkCopyPropBlock (bSrc bTgt : Body) (cert : BodyAbsCert)
    (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      match stepCopyPropCertStmts bSrc.locals [] entryEnv
          bbSrc.statements bbTgt.statements with
      | none => false
      | some (exitAliases, exitEnv) =>
        isCopyPropTerminator exitAliases bbSrc.terminator bbTgt.terminator &&
          checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
            cert exitEnv bbSrc.terminator

noncomputable def checkCopyPropBlocksLoop (bSrc bTgt : Body)
    (cert : BodyAbsCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkCopyPropBlock bSrc bTgt cert idx bbSrc &&
      checkCopyPropBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkCopyPropBody (cert : BodyAbsCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkCopyPropBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkCopyPropProgram (cert : ProgramAbsCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkCopyPropBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Certificate 1b (`checkMoveHeadUnifyProgram`): Liveness & Init Certificate for `Move`-Head Unification -/

noncomputable def stepMoveHeadCertStmts (bodyLocals : List MirTy)
    (termTgt : TerminatorKind) :
    List AbsSlot → List StatementKind → List StatementKind →
    Option (List AbsSlot)
  | env, [], [] => some env
  | env, s₁ :: s₂ :: restSrc, t₁ :: t₂ :: restTgt =>
    if isMoveHeadUnifyPair bodyLocals s₁ s₂ t₁ t₂ restTgt termTgt then
      match s₁, s₂ with
      | .assign dPlace (.use (.move sPlace)), _ =>
        match Trusted.MirSemantics.getElem? env dPlace.localId,
            Trusted.MirSemantics.getElem? env sPlace.localId with
        | some dstSlot, some .liveInit =>
          if !absSlotImplies dstSlot .liveUninit then none
          else
            match stepPlainStmtAbs bodyLocals env s₁ with
            | none => none
            | some env₁ =>
              match stepPlainStmtAbs bodyLocals env₁ s₂ with
              | none => none
              | some env₂ =>
                stepMoveHeadCertStmts bodyLocals termTgt env₂ restSrc restTgt
        | _, _ => none
      | _, _ => none
    else if !stmtEq s₁ t₁ then
      none
    else
      match stepPlainStmtAbs bodyLocals env s₁ with
      | none => none
      | some env₁ =>
        stepMoveHeadCertStmts bodyLocals termTgt env₁
          (s₂ :: restSrc) (t₂ :: restTgt)
  | env, [s₁], [t₁] =>
    if stmtEq s₁ t₁ then stepPlainStmtAbs bodyLocals env s₁ else none
  | _, _, _ => none

noncomputable def checkMoveHeadBlock (bSrc bTgt : Body) (cert : BodyAbsCert)
    (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      match stepMoveHeadCertStmts bSrc.locals bbTgt.terminator entryEnv
          bbSrc.statements bbTgt.statements with
      | none => false
      | some exitEnv =>
        checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
          cert exitEnv bbSrc.terminator

noncomputable def checkMoveHeadBlocksLoop (bSrc bTgt : Body)
    (cert : BodyAbsCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkMoveHeadBlock bSrc bTgt cert idx bbSrc &&
      checkMoveHeadBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkMoveHeadUnifyBody (cert : BodyAbsCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkMoveHeadBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkMoveHeadUnifyProgram (cert : ProgramAbsCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkMoveHeadUnifyBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Certificate 2 (`checkCertifiedDseProgram`): 4-Point Non-Zero & Total-Rvalue Certificate for `DeadStoreElimination` -/

/-- 4-point abstract local domain for certified `DeadStoreElimination`:
`.liveNonZero ⊑ .liveInit ⊑ .liveUninit ⊑ .dead`. -/
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

abbrev BodyDseCert := List (Option (List NonZeroAbsSlot))
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

/-- True iff `c` is a well-formed integer constant of `(w, s)` whose decoded
scalar value is non-zero (`decodeScalar sv != 0`). -/
noncomputable def isValidNonZeroIntConst (w : IntWidth) (s : Bool)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty (.int w s) &&
    match evalConstLit (.int w s) c.lit with
    | .ok (.scalar sv) => decodeScalar sv != 0
    | _ => false

/-- True iff `rhs` is a signed integer constant of width `w` whose decoded value
is neither `0` nor `-1` (ruling out both `DivisionByZero` and `INT_MIN / -1` UB). -/
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

/-- Return `some ty` iff `evalPrimitiveOperand` on `opnd` is guaranteed to
succeed with a well-typed primitive value of type `ty` (allowing `.move` only on
`allowedMoveLocal`). -/
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

/-- Check that `evalBinOp op lVal rVal` is guaranteed to succeed with a value of
type `dstTy` whenever `lVal : lhsTy` and `rVal : rhsTy`. -/
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

/-- Check that `evalRvalue bodyLocals locals dstTy rv` is guaranteed to succeed
without faulting and yield `val` satisfying `checkVal val dstTy = true`. -/
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

noncomputable def stepCertifiedDseStmts (bodyLocals : List MirTy)
    (termTgt : TerminatorKind) :
    List NonZeroAbsSlot → List StatementKind → List StatementKind →
    Option (List NonZeroAbsSlot)
  | env, [], [] => some env
  | env, sSrc :: restSrc, sTgt :: restTgt =>
    if isDseMoveFreeElim bodyLocals sSrc sTgt restTgt termTgt then
      match sSrc with
      | .assign dstPlace rval =>
        match Trusted.MirSemantics.getElem? bodyLocals dstPlace.localId,
            Trusted.MirSemantics.getElem? env dstPlace.localId with
        | some dstTy, some dstSlot =>
          if nonZeroSlotImplies dstSlot .liveUninit &&
              rvalueCertifiedTotal bodyLocals env dstPlace.localId dstTy rval then
            match stepPlainStmtNonZero bodyLocals env sSrc with
            | none => none
            | some env' =>
              stepCertifiedDseStmts bodyLocals termTgt env' restSrc restTgt
          else
            none
        | _, _ => none
      | _ => none
    else if stmtEq sSrc sTgt then
      match stepPlainStmtNonZero bodyLocals env sSrc with
      | none => none
      | some env' =>
        stepCertifiedDseStmts bodyLocals termTgt env' restSrc restTgt
    else
      none
  | _, _, _ => none

/-- Check whether `branches` contains a valid width-`w` `0` guard with no
preceding overflowing `caseBits` (so falling through to `otherwise` guarantees
`decodeScalar sv != 0`). -/
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

noncomputable def checkNonZeroEdge (numBlocks : Nat) (cert : BodyDseCert)
    (exitEnv : List NonZeroAbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? cert target with
    | some (some tgtEnv) => nonZeroEnvImplies exitEnv tgtEnv
    | _ => false

noncomputable def checkCertifiedDseBlock (bSrc bTgt : Body)
    (cert : BodyDseCert) (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      terminatorEq bbSrc.terminator bbTgt.terminator &&
      match stepCertifiedDseStmts bSrc.locals bbTgt.terminator entryEnv
          bbSrc.statements bbTgt.statements with
      | none => false
      | some exitEnv =>
        let numBlocks := bSrc.basicBlocks.length
        match bbSrc.terminator with
        | .goto target => checkNonZeroEdge numBlocks cert exitEnv target
        | .switchInt discr targets =>
          let afterDiscrEnv := deinitMoveOperandNonZero bSrc.locals exitEnv discr
          let otherwiseEnv :=
            match discr with
            | .copy p =>
              if !p.projection.isEmpty then afterDiscrEnv
              else
                match Trusted.MirSemantics.getElem? bSrc.locals p.localId,
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
          checkNonZeroEdge numBlocks cert otherwiseEnv targets.otherwise &&
            targets.branches.all (fun br =>
              checkNonZeroEdge numBlocks cert afterDiscrEnv br.2)
        | _ => true

noncomputable def checkCertifiedDseBlocksLoop (bSrc bTgt : Body)
    (cert : BodyDseCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkCertifiedDseBlock bSrc bTgt cert idx bbSrc &&
      checkCertifiedDseBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkCertifiedDseBody (cert : BodyDseCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         nonZeroEnvImplies (initNonZeroEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkCertifiedDseBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkCertifiedDseProgram (cert : ProgramDseCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkCertifiedDseBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Certificate 3 (`checkDestPropProgram`): Liveness & All-Paths Deadness Certificate for `DestinationPropagation` -/

/-- Per-body certificate for `DestinationPropagation`, pairing forward slot
liveness (`liveCert`) with optional cross-block dead-on-entry sets
(`deadAtEntry`, defaulting to `[]` when `tmp` dies intra-block). -/
structure BodyDestPropCert where
  liveCert : BodyAbsCert
  deadAtEntry : List (List LocalId) := []

abbrev ProgramDestPropCert := List BodyDestPropCert

/-- Check whether local `d` (`d ≠ 0`) is dead along all CFG paths starting at
`(stmts, term)` given validated block-entry dead sets `deadAtEntry`. -/
noncomputable def isDeadAcrossCfg (deadAtEntry : List (List LocalId))
    (numBlocks : Nat) (d : LocalId) :
    List StatementKind → TerminatorKind → Bool
  | [], .return_ => true
  | [], .unreachable => true
  | [], .goto target =>
    Nat.blt target numBlocks &&
      match Trusted.MirSemantics.getElem? deadAtEntry target with
      | some ds => natElem d ds
      | none => false
  | [], .switchInt discr targets =>
    !operandTouchesLocal d discr &&
      Nat.blt targets.otherwise numBlocks &&
      (match Trusted.MirSemantics.getElem? deadAtEntry targets.otherwise with
       | some ds => natElem d ds
       | none => false) &&
      targets.branches.all (fun br =>
        Nat.blt br.2 numBlocks &&
          match Trusted.MirSemantics.getElem? deadAtEntry br.2 with
          | some ds => natElem d ds
          | none => false)
  | [], _ => false
  | .nop :: rest, term => isDeadAcrossCfg deadAtEntry numBlocks d rest term
  | .storageLive id :: rest, term =>
    if Nat.beq id d then true
    else isDeadAcrossCfg deadAtEntry numBlocks d rest term
  | .storageDead id :: rest, term =>
    if Nat.beq id d then true
    else isDeadAcrossCfg deadAtEntry numBlocks d rest term
  | .assign lhs rv :: rest, term =>
    !rvalueTouchesLocal d rv &&
      if lhs.projection.isEmpty && Nat.beq lhs.localId d then
        true
      else
        isDeadAcrossCfg deadAtEntry numBlocks d rest term
  | .unsupported :: _, _ => false

noncomputable def checkDeadAtEntryLoop (bTgt : Body)
    (deadAtEntry : List (List LocalId)) : Nat → List (List LocalId) → Bool
  | _, [] => true
  | bbIdx, ds :: rest =>
    (match Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
     | none => false
     | some bbTgt =>
       ds.all (fun d =>
         !Nat.beq d 0 &&
           isDeadAcrossCfg deadAtEntry bTgt.basicBlocks.length d
             bbTgt.statements bbTgt.terminator)) &&
      checkDeadAtEntryLoop bTgt deadAtEntry (bbIdx + 1) rest

noncomputable def stepDestPropCertStmts (bodyLocals : List MirTy)
    (deadAtEntry : List (List LocalId)) (numBlocks : Nat)
    (termTgt : TerminatorKind) :
    List AbsSlot → List StatementKind → List StatementKind →
    Option (List AbsSlot)
  | env, [], [] => some env
  | env, s₁ :: s₂ :: restSrc, t₁ :: t₂ :: restTgt =>
    match isDestPropPairCore bodyLocals s₁ s₂ t₁ t₂ with
    | some tmp =>
      match s₁, s₂ with
      | .assign _ _, .assign dstPlace _ =>
        match Trusted.MirSemantics.getElem? bodyLocals dstPlace.localId,
            Trusted.MirSemantics.getElem? env tmp,
            Trusted.MirSemantics.getElem? env dstPlace.localId with
        | some dstTy, some tmpSlot, some dstSlot =>
          if isSupportedScalarOrUnitTy dstTy &&
              absSlotImplies tmpSlot .liveUninit &&
              absSlotImplies dstSlot .liveUninit &&
              isDeadAcrossCfg deadAtEntry numBlocks tmp restTgt termTgt then
            match stepPlainStmtAbs bodyLocals env s₁ with
            | none => none
            | some env₁ =>
              match stepPlainStmtAbs bodyLocals env₁ s₂ with
              | none => none
              | some env₂ =>
                stepDestPropCertStmts bodyLocals deadAtEntry numBlocks termTgt
                  env₂ restSrc restTgt
          else
            none
        | _, _, _ => none
      | _, _ => none
    | none =>
      if !stmtEq s₁ t₁ then none
      else
        match stepPlainStmtAbs bodyLocals env s₁ with
        | none => none
        | some env₁ =>
          stepDestPropCertStmts bodyLocals deadAtEntry numBlocks termTgt
            env₁ (s₂ :: restSrc) (t₂ :: restTgt)
  | env, [s₁], [t₁] =>
    if stmtEq s₁ t₁ then stepPlainStmtAbs bodyLocals env s₁ else none
  | _, _, _ => none

noncomputable def checkDestPropBlock (bSrc bTgt : Body)
    (cert : BodyDestPropCert) (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert.liveCert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      terminatorEq bbSrc.terminator bbTgt.terminator &&
      match stepDestPropCertStmts bSrc.locals cert.deadAtEntry
          bTgt.basicBlocks.length bbTgt.terminator entryEnv
          bbSrc.statements bbTgt.statements with
      | none => false
      | some exitEnv =>
        checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
          cert.liveCert exitEnv bbSrc.terminator

noncomputable def checkDestPropBlocksLoop (bSrc bTgt : Body)
    (cert : BodyDestPropCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkDestPropBlock bSrc bTgt cert idx bbSrc &&
      checkDestPropBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkDestPropBody (cert : BodyDestPropCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.liveCert.length bSrc.basicBlocks.length &&
    checkDeadAtEntryLoop bTgt cert.deadAtEntry 0 cert.deadAtEntry &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert.liveCert 0 with
       | some (some env₀) =>
         absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkDestPropBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkDestPropProgram (cert : ProgramDestPropCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkDestPropBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Top-Level Semantic Equivalence & Forward Refinement Relations -/

/-- Bundled bidirectional operational and verification equivalence between
`pSrc` and `pTgt` across all $M_{\text{anneal}}$ execution and verification
predicates (`WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`,
`SatisfiesPost`, and `BodyVerified`). -/
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

/-- Bundled unconditional forward codegen refinement from `pSrc` to `pTgt`
whenever `pSrc` is `WellFormed`. -/
noncomputable def ForwardCodegenRefines (pSrc pTgt : Program) : Prop :=
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
    BodyVerified pTgt defId bTgt safetyPre)

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

private theorem forwardCodegenRefines_of_query_fwd {pSrc pTgt : Program}
    (hHdr : programHeaderEq pSrc pTgt = true)
    (hBodyFields : ∀ defId bSrc bTgt,
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      bodyHeaderEq bSrc bTgt = true ∧
      bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
      storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt)
    (hQuery : ∀ q,
      WellFormed pSrc q →
      WellFormed pTgt q ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (Diverges pTgt q ↔ Diverges pSrc q))
    (hEntryQuery : ∀ defId args,
      WellFormed (entryProgForBody pSrc defId) { args := args } →
      WellFormed (entryProgForBody pTgt defId) { args := args }) :
    ForwardCodegenRefines pSrc pTgt := by
  let ⟨hPw, hVer, _, _⟩ := programHeaderEq_elim hHdr
  refine ⟨hQuery, ?_, ?_⟩
  · intro q post hSat
    let ⟨hWfT, hBehIff, _⟩ := hQuery q hSat.1
    exact ⟨hWfT, fun out hB => hSat.2 out ((hBehIff out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hBS hBT hVerS
    let ⟨hBHdr, hEmpty, hStEq⟩ := hBodyFields defId bSrc bTgt hBS hBT
    let ⟨hArg, hLoc, hUns, hId⟩ := bodyHeaderEq_elim hBHdr
    have hAdm := bodyStaticAdmitted_eq_of_fields hPw hVer hArg hLoc hId hEmpty hStEq
    refine ⟨hBT, by rw [← hAdm]; exact hVerS.2.1, ?_⟩
    intro args hArgs hPre
    have hArgsS : ValidEntryArgs bSrc args := by
      unfold ValidEntryArgs; rw [hArg, hLoc]; exact hArgs
    have hPreS : bSrc.isUnsafe = true → safetyPre args := by
      rw [hUns]; exact hPre
    exact hEntryQuery defId args (hVerS.2.2 args hArgsS hPreS)

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

/-! #### `isDeadInBlockFrom` Step Inversion Lemmas -/

private theorem isDeadInBlockFrom_kept_step {bSrc bTgt : Body}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmt : StatementKind} {restTgt : List StatementKind}
    {termTgt : TerminatorKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧ isDeadInBlockFrom d (stmt :: restTgt) termTgt = true)
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
        (fun d => d ≠ 0 ∧ isDeadInBlockFrom d restTgt termTgt = true)
        locs₁' locs₂') := by
  apply evalStatement_kept_deadMasked_bisim hLocEq hMask
  · intro hS d ⟨hNe0, hDead⟩
    subst hS; exact ⟨hNe0, hDead⟩
  · intro _; exact Or.inr True.intro
  · intro id hS d ⟨hNe0, hDead⟩
    subst hS
    dsimp [isDeadInBlockFrom] at hDead
    cases hEq : Nat.beq id d with
    | true => exact Or.inl (nat_beq_eq hEq).symm
    | false => rw [hEq] at hDead; exact Or.inr ⟨hNe0, hDead⟩
  · intro id hS d ⟨hNe0, hDead⟩
    subst hS
    dsimp [isDeadInBlockFrom] at hDead
    cases hEq : Nat.beq id d with
    | true => exact Or.inl (nat_beq_eq hEq).symm
    | false => rw [hEq] at hDead; exact Or.inr ⟨hNe0, hDead⟩
  · intro lhs rv hS d ⟨hNe0, hDead⟩
    subst hS
    dsimp [isDeadInBlockFrom] at hDead
    let ⟨hNoTouch, hRest⟩ := bool_and_true hDead
    refine ⟨bool_not_true hNoTouch, ?_⟩
    cases hOver : (lhs.projection.isEmpty && Nat.beq lhs.localId d) with
    | true =>
      let ⟨hEmp, hBeq⟩ := bool_and_true hOver
      exact Or.inl ⟨hEmp, (nat_beq_eq hBeq).symm⟩
    | false =>
      rw [hOver] at hRest; dsimp at hRest
      exact Or.inr ⟨hNe0, hRest⟩

private theorem isDeadInBlockFrom_nil_term {d : LocalId} {term : TerminatorKind}
    (h : isDeadInBlockFrom d [] term = true) :
    term = .return_ ∨ term = .unreachable := by
  cases term with
  | return_ => exact Or.inl rfl
  | unreachable => exact Or.inr rfl
  | goto _ | switchInt _ _ | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    cases h

/-! ### Stage 4 Private Helpers — Layer C: Certified `CopyProp` (Theorem 1a) -/

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

private theorem evalOperandToSlot_copyProp_eq {bodyLocals : List MirTy}
    {locals : List LocalSlot} {aliases : CopyAliases}
    {opSrc opTgt : Operand}
    (hSound : AllAliasesSound bodyLocals locals aliases)
    (hOp : isCopyPropOperand aliases opSrc opTgt = true) :
    evalOperandToSlot bodyLocals locals opSrc =
      evalOperandToSlot bodyLocals locals opTgt := by
  unfold isCopyPropOperand at hOp
  cases bool_or_true hOp with
  | inl hEq => rw [operandEq_eq hEq]
  | inr hProp =>
    cases opSrc with
    | move _ | constant _ => cases hProp
    | copy pSrc =>
      cases opTgt with
      | move _ | constant _ => cases hProp
      | copy pTgt =>
        dsimp at hProp
        let ⟨h12, hLookM⟩ := bool_and_true hProp
        let ⟨hEmp1, hEmp2⟩ := bool_and_true h12
        cases hLook : lookupCopyAlias pSrc.localId aliases with
        | none => rw [hLook] at hLookM; cases hLookM
        | some src =>
          rw [hLook] at hLookM
          have hTgtId := nat_beq_eq hLookM
          let ⟨ty, v, hTyD, hTyS, hLD, hLS, _⟩ := lookupCopyAlias_sound hSound hLook
          dsimp [evalOperandToSlot]
          rw [hEmp1, hEmp2]; dsimp
          rw [hTgtId, hTyD, hTyS, hLD, hLS]

private theorem evalPrimitiveOperand_copyProp_eq {bodyLocals : List MirTy}
    {locals : List LocalSlot} {aliases : CopyAliases}
    {opSrc opTgt : Operand}
    (hSound : AllAliasesSound bodyLocals locals aliases)
    (hOp : isCopyPropOperand aliases opSrc opTgt = true) :
    evalPrimitiveOperand bodyLocals locals opSrc =
      evalPrimitiveOperand bodyLocals locals opTgt := by
  unfold evalPrimitiveOperand
  rw [evalOperandToSlot_copyProp_eq hSound hOp]

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

private theorem evalRvalue_copyProp_eq_and_preserve {bodyLocals : List MirTy}
    {locals : List LocalSlot} {dstTy : MirTy}
    {aliases : CopyAliases} {rvSrc rvTgt : Rvalue}
    (hSound : AllAliasesSound bodyLocals locals aliases)
    (hRv : isCopyPropRvalue aliases rvSrc rvTgt = true) :
    evalRvalue bodyLocals locals dstTy rvSrc =
      evalRvalue bodyLocals locals dstTy rvTgt ∧
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
  unfold isCopyPropRvalue at hRv
  cases bool_or_true hRv with
  | inl hEq => rw [rvalueEq_eq hEq]
  | inr hProp =>
    cases rvSrc with
    | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hProp
    | use o₁ =>
      cases rvTgt with
      | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
      | addressOf _ _ | aggregateTuple _ | unsupported => cases hProp
      | use o₂ =>
        dsimp [evalRvalue]
        rw [evalOperandToSlot_copyProp_eq hSafeSound hProp]
    | unaryOp op₁ o₁ =>
      cases rvTgt with
      | use _ | binaryOp _ _ _ | discriminant _ | ref _ _
      | addressOf _ _ | aggregateTuple _ | unsupported => cases hProp
      | unaryOp op₂ o₂ =>
        let ⟨hOpEq, hO⟩ := bool_and_true hProp
        dsimp [evalRvalue]
        rw [unOpEq_eq hOpEq, evalPrimitiveOperand_copyProp_eq hSafeSound hO]
    | binaryOp op₁ l₁ r₁ =>
      cases rvTgt with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _
      | addressOf _ _ | aggregateTuple _ | unsupported => cases hProp
      | binaryOp op₂ l₂ r₂ =>
        let ⟨h12, hR⟩ := bool_and_true hProp
        let ⟨hOpEq, hL⟩ := bool_and_true h12
        have hNoL : ∀ d s, (d, s) ∈ safeAliases →
            operandMovesLocal d l₁ = false ∧ operandMovesLocal s l₁ = false := by
          intro d s hM
          let ⟨hD, hS⟩ := hSafeMem d s hM
          exact ⟨(bool_or_false hD).1, (bool_or_false hS).1⟩
        dsimp [evalRvalue]
        rw [binOpEq_eq hOpEq, ← evalPrimitiveOperand_copyProp_eq hSafeSound hL]
        cases hEvL : evalPrimitiveOperand bodyLocals locals l₁ with
        | error _ => rfl
        | ok resL =>
          let ⟨lv, locs1⟩ := resL
          dsimp
          have hS1 : AllAliasesSound bodyLocals locs1 safeAliases := by
            dsimp [evalPrimitiveOperand] at hEvL
            cases hSL : evalOperandToSlot bodyLocals locals l₁ with
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
          rw [evalPrimitiveOperand_copyProp_eq hS1 hR]
    | discriminant p₁ =>
      cases rvTgt with
      | use _ | binaryOp _ _ _ | unaryOp _ _ | ref _ _
      | addressOf _ _ | aggregateTuple _ | unsupported => cases hProp
      | discriminant p₂ =>
        let ⟨h12, hLookM⟩ := bool_and_true hProp
        let ⟨hEmp1, hEmp2⟩ := bool_and_true h12
        cases hLook : lookupCopyAlias p₁.localId safeAliases with
        | none => rw [hLook] at hLookM; cases hLookM
        | some src =>
          rw [hLook] at hLookM
          have hP2Id := nat_beq_eq hLookM
          let ⟨ty, v, hTy1, hTy2, hL1, hL2, _⟩ :=
            lookupCopyAlias_sound hSafeSound hLook
          dsimp [evalRvalue]
          rw [hEmp1, hEmp2]; dsimp
          rw [hP2Id, hTy1, hTy2, hL1, hL2]

private theorem stepCopyPropCertStmt_step_eq_and_sound {bSrc bTgt : Body}
    {frame : FrameState} {cm : CallerMemory}
    {aliases aliases' : CopyAliases} {env env' : List AbsSlot}
    {sSrc sTgt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEnv : AbsEnvSound bSrc.locals env frame.locals)
    (hAliases : AllAliasesSound bSrc.locals frame.locals aliases)
    (hCertStmt : stepCopyPropCertStmt bSrc.locals aliases env sSrc sTgt =
      some (aliases', env')) :
    evalStatement bSrc frame cm sSrc = evalStatement bTgt frame cm sTgt ∧
    (∀ s', evalStatement bSrc frame cm sSrc = .step s' →
      ∃ locs',
        s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
               callerMem := cm } ∧
        AbsEnvSound bSrc.locals env' locs' ∧
        AllAliasesSound bSrc.locals locs' aliases') := by
  cases sSrc with
  | nop =>
    cases sTgt with
    | assign _ _ | storageLive _ | storageDead _ | unsupported => cases hCertStmt
    | nop =>
      dsimp [stepCopyPropCertStmt] at hCertStmt
      injection hCertStmt with hPair; injection hPair with hA hE
      subst hA; subst hE
      refine ⟨rfl, ?_⟩
      intro s' hEv; injection hEv with hS; subst hS
      exact ⟨frame.locals, rfl, hEnv, hAliases⟩
  | unsupported =>
    cases sTgt with
    | assign _ _ | storageLive _ | storageDead _ | nop => cases hCertStmt
    | unsupported =>
      exact ⟨rfl, fun _ hEv => by cases hEv⟩
  | storageLive i₁ =>
    cases sTgt with
    | assign _ _ | storageDead _ | nop | unsupported => cases hCertStmt
    | storageLive i₂ =>
      dsimp [stepCopyPropCertStmt] at hCertStmt
      cases hNeq : (!Nat.beq i₁ i₂) with
      | true => rw [hNeq] at hCertStmt; cases hCertStmt
      | false =>
        rw [hNeq] at hCertStmt; dsimp at hCertStmt
        have hiEq := nat_beq_eq (bool_not_false hNeq)
        subst hiEq
        cases hStepA : stepPlainStmtAbs bSrc.locals env (.storageLive i₁) with
        | none => rw [hStepA] at hCertStmt; cases hCertStmt
        | some e' =>
          rw [hStepA] at hCertStmt
          injection hCertStmt with hPair; injection hPair with hA hE
          subst hA; subst hE
          refine ⟨by dsimp [evalStatement]; rw [hLocEq], ?_⟩
          intro s' hEv
          let ⟨locs', hSEq, hEnv'⟩ := stepPlainStmtAbs_sound hEnv hStepA hEv
          dsimp [evalStatement] at hEv
          cases hTy : Trusted.MirSemantics.getElem? bSrc.locals i₁ with
          | none => rw [hTy] at hEv; cases hEv
          | some ty =>
            rw [hTy] at hEv; dsimp at hEv
            cases hSet : setElem? frame.locals i₁ (liveUninitSlot ty) with
            | none => rw [hSet] at hEv; cases hEv
            | some l' =>
              rw [hSet] at hEv; injection hEv with hS1
              rw [hSEq] at hS1
              injection hS1 with hFs _; injection hFs with hF _; injection hF with _ _ _ hLEq
              subst hLEq
              exact ⟨l', hSEq, hEnv', killCopyAliasesTouching_set_sound hAliases hSet⟩
  | storageDead i₁ =>
    cases sTgt with
    | assign _ _ | storageLive _ | nop | unsupported => cases hCertStmt
    | storageDead i₂ =>
      dsimp [stepCopyPropCertStmt] at hCertStmt
      cases hNeq : (!Nat.beq i₁ i₂) with
      | true => rw [hNeq] at hCertStmt; cases hCertStmt
      | false =>
        rw [hNeq] at hCertStmt; dsimp at hCertStmt
        have hiEq := nat_beq_eq (bool_not_false hNeq)
        subst hiEq
        cases hStepA : stepPlainStmtAbs bSrc.locals env (.storageDead i₁) with
        | none => rw [hStepA] at hCertStmt; cases hCertStmt
        | some e' =>
          rw [hStepA] at hCertStmt
          injection hCertStmt with hPair; injection hPair with hA hE
          subst hA; subst hE
          refine ⟨rfl, ?_⟩
          intro s' hEv
          let ⟨locs', hSEq, hEnv'⟩ := stepPlainStmtAbs_sound hEnv hStepA hEv
          dsimp [evalStatement] at hEv
          cases hZ : Nat.beq i₁ 0 with
          | true => rw [hZ] at hEv; cases hEv
          | false =>
            rw [hZ] at hEv; dsimp at hEv
            cases hSet : setElem? frame.locals i₁ .dead with
            | none => rw [hSet] at hEv; cases hEv
            | some l' =>
              rw [hSet] at hEv; injection hEv with hS1
              rw [hSEq] at hS1
              injection hS1 with hFs _; injection hFs with hF _; injection hF with _ _ _ hLEq
              subst hLEq
              exact ⟨l', hSEq, hEnv', killCopyAliasesTouching_set_sound hAliases hSet⟩
  | assign dst rvSrc =>
    cases sTgt with
    | storageLive _ | storageDead _ | nop | unsupported => cases hCertStmt
    | assign dst' rvTgt =>
      dsimp [stepCopyPropCertStmt] at hCertStmt
      cases hGuard : (!(placeEq dst dst' && dst.projection.isEmpty &&
          isCopyPropRvalue aliases rvSrc rvTgt)) with
      | true => rw [hGuard] at hCertStmt; cases hCertStmt
      | false =>
        rw [hGuard] at hCertStmt; dsimp at hCertStmt
        have hG := bool_not_false hGuard
        let ⟨h12, hRvProp⟩ := bool_and_true hG
        let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12
        have hDEq := placeEq_eq hDstEq; subst hDEq
        cases hStepA : stepPlainStmtAbs bSrc.locals env (.assign dst rvSrc) with
        | none => rw [hStepA] at hCertStmt; cases hCertStmt
        | some e' =>
          rw [hStepA] at hCertStmt; dsimp at hCertStmt
          have hEvStmtEq : evalStatement bSrc frame cm (.assign dst rvSrc) =
              evalStatement bTgt frame cm (.assign dst rvTgt) := by
            dsimp [evalStatement]
            rw [hDstEmp]; dsimp
            rw [← hLocEq]
            cases Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
            | none => rfl
            | some dstTy =>
              dsimp
              rw [(evalRvalue_copyProp_eq_and_preserve (dstTy := dstTy) hAliases hRvProp).1]
          refine ⟨hEvStmtEq, ?_⟩
          intro s' hEv
          let ⟨locs', hSEq, hEnv'⟩ := stepPlainStmtAbs_sound hEnv hStepA hEv
          dsimp [evalStatement] at hEv
          rw [hDstEmp] at hEv; dsimp at hEv
          cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
          | none => rw [hDstTy] at hEv; cases hEv
          | some dstTy =>
            rw [hDstTy] at hEv; dsimp at hEv
            let ⟨hRvEq, hRvPres⟩ :=
              evalRvalue_copyProp_eq_and_preserve (dstTy := dstTy) hAliases hRvProp
            cases hEvR : evalRvalue bSrc.locals frame.locals dstTy rvSrc with
            | error _ => rw [hEvR] at hEv; cases hEv
            | ok resR =>
              let ⟨val, locsAfterR⟩ := resR
              rw [hEvR] at hEv; dsimp at hEv
              have hAfterR := hRvPres val locsAfterR hEvR
              dsimp [writePlace] at hEv
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
                      injection hS1 with hFs _; injection hFs with hF _; injection hF with _ _ _ hLEq
                      subst hLEq
                      have hAfterKill : AllAliasesSound bSrc.locals locsW
                          (killCopyAliasesTouching dst.localId (filterAliasesForRvalue rvSrc aliases)) :=
                        killCopyAliasesTouching_set_sound hAfterR hSetW
                      cases rvTgt with
                      | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
                      | addressOf _ _ | aggregateTuple _ | unsupported =>
                        dsimp at hCertStmt
                        injection hCertStmt with hPair; injection hPair with hA hE
                        subst hA; subst hE
                        exact ⟨locsW, hSEq, hEnv', hAfterKill⟩
                      | use opTgt =>
                        cases opTgt with
                        | move _ | constant _ =>
                          dsimp at hCertStmt
                          injection hCertStmt with hPair; injection hPair with hA hE
                          subst hA; subst hE
                          exact ⟨locsW, hSEq, hEnv', hAfterKill⟩
                        | copy pHead =>
                          dsimp at hCertStmt
                          cases hHeadCond : (pHead.projection.isEmpty &&
                              !Nat.beq dst.localId pHead.localId) with
                          | false =>
                            rw [hHeadCond] at hCertStmt; dsimp at hCertStmt
                            injection hCertStmt with hPair; injection hPair with hA hE
                            subst hA; subst hE
                            exact ⟨locsW, hSEq, hEnv', hAfterKill⟩
                          | true =>
                            rw [hHeadCond] at hCertStmt; dsimp at hCertStmt
                            rw [hDstTy] at hCertStmt
                            let ⟨hHeadEmp, hDstNeHeadB⟩ := bool_and_true hHeadCond
                            have hDstNeHead := nat_ne_of_beq_false (bool_not_true hDstNeHeadB)
                            cases hSrcTy : Trusted.MirSemantics.getElem? bSrc.locals pHead.localId with
                            | none =>
                              rw [hSrcTy] at hCertStmt; dsimp at hCertStmt
                              injection hCertStmt with hPair; injection hPair with hA hE
                              subst hA; subst hE
                              exact ⟨locsW, hSEq, hEnv', hAfterKill⟩
                            | some srcTy =>
                              rw [hSrcTy] at hCertStmt
                              cases hEDst : Trusted.MirSemantics.getElem? env dst.localId with
                              | none =>
                                rw [hEDst] at hCertStmt; dsimp at hCertStmt
                                injection hCertStmt with hPair; injection hPair with hA hE
                                subst hA; subst hE
                                exact ⟨locsW, hSEq, hEnv', hAfterKill⟩
                              | some dstAbs =>
                                rw [hEDst] at hCertStmt
                                cases hESrc : Trusted.MirSemantics.getElem? env pHead.localId with
                                | none =>
                                  rw [hESrc] at hCertStmt; dsimp at hCertStmt
                                  injection hCertStmt with hPair; injection hPair with hA hE
                                  subst hA; subst hE
                                  exact ⟨locsW, hSEq, hEnv', hAfterKill⟩
                                | some srcAbs =>
                                  rw [hESrc] at hCertStmt
                                  cases srcAbs with
                                  | dead | liveUninit =>
                                    dsimp at hCertStmt
                                    injection hCertStmt with hPair; injection hPair with hA hE
                                    subst hA; subst hE
                                    exact ⟨locsW, hSEq, hEnv', hAfterKill⟩
                                  | liveInit =>
                                    dsimp at hCertStmt
                                    cases hAdmit : (MirTy.beq dstTy srcTy &&
                                        isSupportedScalarOrUnitTy dstTy &&
                                        absSlotImplies dstAbs .liveUninit) with
                                    | false =>
                                      rw [hAdmit] at hCertStmt; dsimp at hCertStmt
                                      injection hCertStmt with hPair; injection hPair with hA hE
                                      subst hA; subst hE
                                      exact ⟨locsW, hSEq, hEnv', hAfterKill⟩
                                    | true =>
                                      rw [hAdmit] at hCertStmt; dsimp at hCertStmt
                                      injection hCertStmt with hPair; injection hPair with hA hE
                                      subst hA; subst hE
                                      let ⟨h12A, _⟩ := bool_and_true hAdmit
                                      let ⟨hTyEqB, _⟩ := bool_and_true h12A
                                      have hTyEq := mirTy_beq_eq hTyEqB; subst hTyEq
                                      have hEvRTgt : evalRvalue bSrc.locals frame.locals dstTy
                                          (.use (.copy pHead)) = .ok (val, locsAfterR) := by
                                        rw [← hRvEq]; exact hEvR
                                      dsimp [evalRvalue, evalOperandToSlot] at hEvRTgt
                                      rw [hHeadEmp, hSrcTy] at hEvRTgt; dsimp at hEvRTgt
                                      cases hSlHead : Trusted.MirSemantics.getElem? frame.locals pHead.localId with
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
                                            injection hEvRTgt with h1; injection h1 with hvEq hL
                                            subst hvEq; subst hL
                                            have hW_dst := setElem?_getElem?_same hSetW
                                            have hW_head : Trusted.MirSemantics.getElem? locsW pHead.localId =
                                                some (.live (some vHead)) := by
                                              rw [setElem?_getElem?_ne hSetW hDstNeHead.symm]
                                              exact hSlHead
                                            exact ⟨locsW, hSEq, hEnv',
                                              ⟨⟨dstTy, vHead, hDstTy, hSrcTy, hW_dst, hW_head, hChk⟩,
                                               hAfterKill⟩⟩

private theorem evalTerminator_copyProp_eq {bSrc bTgt : Body}
    {bbSrc bbTgt : BasicBlock} {frame : FrameState} {cm : CallerMemory}
    {aliases : CopyAliases}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hAliases : AllAliasesSound bSrc.locals frame.locals aliases)
    (hTerm : isCopyPropTerminator aliases bbSrc.terminator bbTgt.terminator = true) :
    evalTerminator bSrc bbSrc frame cm = evalTerminator bTgt bbTgt frame cm := by
  unfold isCopyPropTerminator at hTerm
  cases bool_or_true hTerm with
  | inl hEq =>
    unfold evalTerminator
    rw [terminatorEq_eq hEq, hLocEq, hClean]
  | inr hSw =>
    cases hTmS : bbSrc.terminator with
    | goto _ | return_ | unreachable | unwindResume | assert _ _ _ _ _
    | call _ _ _ _ _ | unsupported =>
      rw [hTmS] at hSw; cases hSw
    | switchInt d₁ ts₁ =>
      rw [hTmS] at hSw
      cases hTmT : bbTgt.terminator with
      | goto _ | return_ | unreachable | unwindResume | assert _ _ _ _ _
      | call _ _ _ _ _ | unsupported =>
        rw [hTmT] at hSw; cases hSw
      | switchInt d₂ ts₂ =>
        rw [hTmT] at hSw; dsimp at hSw
        let ⟨hOp, hTs⟩ := bool_and_true hSw
        unfold evalTerminator
        rw [hTmS, hTmT]; dsimp
        rw [← hLocEq, switchTargetsEq_eq hTs,
            evalPrimitiveOperand_copyProp_eq hAliases hOp]

private theorem stepCopyPropStmtsSyntactic_storage {bodyLocals : List MirTy} :
    ∀ {aliases res ss₁ ss₂},
      stepCopyPropStmtsSyntactic bodyLocals aliases ss₁ ss₂ = some res →
      StmtListStoragePreserved ss₁ ss₂ := by
  intro aliases res ss₁
  induction ss₁ generalizing aliases with
  | nil =>
    intro ss₂ h
    cases ss₂ with
    | nil => exact True.intro
    | cons _ _ => cases h
  | cons s₁ r₁ ih =>
    intro ss₂ h
    cases ss₂ with
    | nil => cases h
    | cons s₂ r₂ =>
      dsimp [stepCopyPropStmtsSyntactic] at h
      cases hSt : stepCopyPropSyntactic bodyLocals aliases s₁ s₂ with
      | none => rw [hSt] at h; cases h
      | some a' =>
        rw [hSt] at h; dsimp at h
        refine ⟨?_, ih h⟩
        cases s₁ with
        | nop =>
          cases s₂ <;> first | exact Or.inl rfl | cases hSt
        | unsupported =>
          cases s₂ <;> first | exact Or.inl rfl | cases hSt
        | storageLive i₁ =>
          cases s₂ with
          | nop | unsupported | storageDead _ | assign _ _ => cases hSt
          | storageLive i₂ =>
            dsimp [stepCopyPropSyntactic] at hSt
            cases hEq : Nat.beq i₁ i₂ with
            | false => rw [hEq] at hSt; cases hSt
            | true => exact Or.inl (by rw [nat_beq_eq hEq])
        | storageDead i₁ =>
          cases s₂ with
          | nop | unsupported | storageLive _ | assign _ _ => cases hSt
          | storageDead i₂ =>
            dsimp [stepCopyPropSyntactic] at hSt
            cases hEq : Nat.beq i₁ i₂ with
            | false => rw [hEq] at hSt; cases hSt
            | true => exact Or.inl (by rw [nat_beq_eq hEq])
        | assign _ _ =>
          cases s₂ with
          | nop | unsupported | storageLive _ | storageDead _ => cases hSt
          | assign _ _ => exact Or.inr ⟨True.intro, True.intro⟩

private theorem stepCopyPropCertStmts_length {bodyLocals : List MirTy} :
    ∀ {aliases env res ss₁ ss₂},
      stepCopyPropCertStmts bodyLocals aliases env ss₁ ss₂ = some res →
      ss₁.length = ss₂.length := by
  intro aliases env res ss₁
  induction ss₁ generalizing aliases env with
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
      dsimp [stepCopyPropCertStmts] at h
      cases hSt : stepCopyPropCertStmt bodyLocals aliases env s₁ s₂ with
      | none => rw [hSt] at h; cases h
      | some pr =>
        let ⟨a', e'⟩ := pr
        rw [hSt] at h; dsimp at h
        dsimp [List.length]; rw [ih h]

private theorem checkCopyPropBlocksLoop_getElem? {bSrc bTgt : Body}
    {cert : BodyAbsCert} :
    ∀ {base bbs k bbSrc},
      checkCopyPropBlocksLoop bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      checkCopyPropBlock bSrc bTgt cert (base + k) bbSrc = true := by
  intro base bbs
  induction bbs generalizing base with
  | nil => intro _ _ _ hG; cases hG
  | cons bb₀ rest ih =>
    intro k bbSrc hLoop hG
    let ⟨hHead, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hG with hEq; subst hEq
      rw [Nat.add_zero]; exact hHead
    | succ m =>
      have hSub := ih hTail hG
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hSub
      exact hSub

private theorem isCopyPropBody_storage {bSrc bTgt : Body}
    (hBody : isCopyPropBody bSrc bTgt = true) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    (∀ idx, hasStorageAnnotation bSrc idx = hasStorageAnnotation bTgt idx) ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨hBHdr, hBBs⟩ := bool_and_true hBody
  apply bodyStorage_eq_of_blocks hBHdr hBBs
  intro bb₁ bb₂ hBB
  let ⟨_, hRest⟩ := bool_and_true hBB
  cases hSt : stepCopyPropStmtsSyntactic bSrc.locals [] bb₁.statements bb₂.statements with
  | none => rw [hSt] at hRest; cases hRest
  | some _ => exact stepCopyPropStmtsSyntactic_storage hSt

private theorem copyProp_initState_eq {pSrc pTgt : Program}
    (hRel : isCopyPropProgram pSrc pTgt = true) (q : Query) :
    initState pSrc q = initState pTgt q := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodies
  · intro b₁ hB₁
    let ⟨b₂, hB₂, hBRel⟩ := listRel_getElem?_left hBodies hB₁
    rw [hEnt] at hB₂
    let ⟨hBHdr, _, hEmpty, _, hBounds, hLoop⟩ := isCopyPropBody_storage hBRel
    exact ⟨b₂, hB₂, hBHdr, hEmpty, hBounds, hLoop q.args⟩

private noncomputable def CopyPropStateInv (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (s : State) : Prop :=
  ∃ frame,
    s.frames = [frame] ∧
    ∀ bSrc,
      Trusted.MirSemantics.getElem? pSrc.bodies frame.defId = some bSrc →
      ∃ bTgt bCert,
        Trusted.MirSemantics.getElem? pTgt.bodies frame.defId = some bTgt ∧
        Trusted.MirSemantics.getElem? cert frame.defId = some bCert ∧
        isCopyPropBody bSrc bTgt = true ∧
        checkCopyPropBody bCert bSrc bTgt = true ∧
        ∀ bbSrc,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx = some bbSrc →
          ∃ bbTgt aliases env exitAliases exitEnv,
            Trusted.MirSemantics.getElem? bTgt.basicBlocks frame.blockIdx = some bbTgt ∧
            stepCopyPropCertStmts bSrc.locals aliases env
              (bbSrc.statements.drop frame.stmtIdx)
              (bbTgt.statements.drop frame.stmtIdx) =
              some (exitAliases, exitEnv) ∧
            isCopyPropTerminator exitAliases bbSrc.terminator bbTgt.terminator = true ∧
            checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
              bCert exitEnv bbSrc.terminator = true ∧
            AbsEnvSound bSrc.locals env frame.locals ∧
            AllAliasesSound bSrc.locals frame.locals aliases

private theorem copyProp_query_iff {pSrc pTgt : Program} {cert : ProgramAbsCert}
    (hRel : isCopyPropProgram pSrc pTgt = true)
    (hCert : checkCopyPropProgram cert pSrc pTgt = true) (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLenB, hCertZip⟩ := bool_and_true hCert
  have hCertLen := nat_beq_eq hCertLenB
  apply lockstep_inv_query_iff (Inv := CopyPropStateInv pSrc pTgt cert)
    (copyProp_initState_eq hRel q)
  · intro s₀ hOk
    let ⟨_, _, body, hBody, hNotEmp, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    refine ⟨_, rfl, fun bSrc hBS => ?_⟩
    rw [hBody] at hBS; injection hBS with hBEq; subst hBEq
    let ⟨bCert, bTgt, hBCert, hBTgt, hChkBody⟩ :=
      listRel_zip_getElem? hCertLen hCertZip hBody
    let ⟨bTgt', hBTgt', hBRel⟩ := listRel_getElem?_left hBodiesRel hBody
    rw [hBTgt] at hBTgt'; injection hBTgt' with hTEq; subst hTEq
    refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
    intro bbSrc hBB0
    dsimp at hBB0
    let ⟨h123, hLoop⟩ := bool_and_true hChkBody
    let ⟨_, hEntry0⟩ := bool_and_true h123
    rw [hNotEmp] at hEntry0; dsimp at hEntry0
    cases hC0 : Trusted.MirSemantics.getElem? bCert 0 with
    | none => rw [hC0] at hEntry0; cases hEntry0
    | some opt0 =>
      rw [hC0] at hEntry0
      cases opt0 with
      | none => cases hEntry0
      | some env₀ =>
        have hEnv0Sound : AbsEnvSound body.locals env₀
            (initLocalsLoop body q.args 0 body.locals) :=
          absEnvImplies_sound hEntry0 (initAbsEnvLoop_sound hArgs)
        have hChkBB0 := checkCopyPropBlocksLoop_getElem? (k := 0) hLoop hBB0
        rw [Nat.zero_add] at hChkBB0
        unfold checkCopyPropBlock at hChkBB0
        rw [hC0] at hChkBB0
        cases hBBTgt0 : Trusted.MirSemantics.getElem? bTgt.basicBlocks 0 with
        | none => rw [hBBTgt0] at hChkBB0; cases hChkBB0
        | some bbTgt =>
          rw [hBBTgt0] at hChkBB0; dsimp at hChkBB0
          let ⟨_, hRest0⟩ := bool_and_true hChkBB0
          cases hSt0 : stepCopyPropCertStmts body.locals [] env₀
              bbSrc.statements bbTgt.statements with
          | none => rw [hSt0] at hRest0; cases hRest0
          | some pr =>
            let ⟨exitA, exitE⟩ := pr
            rw [hSt0] at hRest0; dsimp at hRest0
            let ⟨hTerm0, hEdges0⟩ := bool_and_true hRest0
            exact ⟨bbTgt, [], env₀, exitA, exitE, rfl, hSt0,
                   hTerm0, hEdges0, hEnv0Sound, True.intro⟩
  · intro s hInv
    let ⟨frame, hFs, hBInv⟩ := hInv
    cases s with
    | mk fs cm =>
      dsimp at hFs; subst hFs
      cases hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies frame.defId with
      | none =>
        have hBTgtNone := (listRel_getElem?_none_iff frame.defId hBodiesRel).mp hBSrc
        refine ⟨by unfold evalStep; dsimp; rw [hBSrc, hBTgtNone], ?_⟩
        intro s' hStepS
        unfold evalStep at hStepS; dsimp at hStepS; rw [hBSrc] at hStepS; cases hStepS
      | some bSrc =>
        let ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, hBBInv⟩ :=
          hBInv bSrc hBSrc
        let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
        let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
        cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
        | none =>
          have hBBTgtNone := (listRel_getElem?_none_iff frame.blockIdx hBBsRel).mp hBBSrc
          refine ⟨by unfold evalStep; dsimp; rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgtNone], ?_⟩
          intro s' hStepS
          unfold evalStep at hStepS; dsimp at hStepS
          rw [hBSrc] at hStepS; dsimp at hStepS
          rw [hBBSrc] at hStepS; cases hStepS
        | some bbSrc =>
          let ⟨bbTgt, aliases, env, exitA, exitE, hBBTgt, hStepStmts,
               hTermProp, hEdges, hEnvS, hAliasesS⟩ := hBBInv bbSrc hBBSrc
          let ⟨bbTgt', hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBsRel hBBSrc
          rw [hBBTgt] at hBBTgt'; injection hBBTgt' with hBBEq; subst hBBEq
          let ⟨hCleanEqB, _⟩ := bool_and_true hBBRel
          have hCleanEq := bool_beq_eq hCleanEqB
          cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements frame.stmtIdx with
          | some sSrc =>
            have hDropSrc := drop_eq_cons_of_getElem? hStSrc
            rw [hDropSrc] at hStepStmts
            cases hDropTgt : bbTgt.statements.drop frame.stmtIdx with
            | nil => rw [hDropTgt] at hStepStmts; cases hStepStmts
            | cons sTgt restTgt =>
              rw [hDropTgt] at hStepStmts
              let ⟨hStTgt, hDropTgtNext⟩ := getElem?_of_drop_eq_cons hDropTgt
              dsimp [stepCopyPropCertStmts] at hStepStmts
              cases hOne : stepCopyPropCertStmt bSrc.locals aliases env sSrc sTgt with
              | none => rw [hOne] at hStepStmts; cases hStepStmts
              | some pr =>
                let ⟨aliases', env'⟩ := pr
                rw [hOne] at hStepStmts; dsimp at hStepStmts
                let ⟨hEvStmtEq, hOneNext⟩ :=
                  stepCopyPropCertStmt_step_eq_and_sound (cm := cm)
                    hLocEq hEnvS hAliasesS hOne
                have hStepEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                    evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                  unfold evalStep; dsimp
                  rw [hBSrc, hBTgt]; dsimp
                  rw [hBBSrc, hBBTgt]; dsimp
                  rw [hStSrc, hStTgt]; dsimp
                  exact hEvStmtEq
                refine ⟨hStepEq, ?_⟩
                intro s' hStepS
                unfold evalStep at hStepS; dsimp at hStepS
                rw [hBSrc] at hStepS; dsimp at hStepS
                rw [hBBSrc] at hStepS; dsimp at hStepS
                rw [hStSrc] at hStepS; dsimp at hStepS
                let ⟨locs', hSEq, hEnv', hAliases'⟩ := hOneNext s' hStepS
                subst hSEq
                refine ⟨_, rfl, fun bS2 hBS2 => ?_⟩
                dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                intro bbS2 hBBS2
                dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                refine ⟨bbTgt, aliases', env', exitA, exitE, hBBTgt, ?_,
                  hTermProp, hEdges, hEnv', hAliases'⟩
                dsimp; rw [hDropTgtNext]; exact hStepStmts
          | none =>
            have hGeSrc : bbSrc.statements.length ≤ frame.stmtIdx := by
              cases Nat.lt_or_ge frame.stmtIdx bbSrc.statements.length with
              | inr hge => exact hge
              | inl hlt =>
                let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements frame.stmtIdx hlt
                rw [hStSrc] at hx; cases hx
            have hDropSrcNil := drop_eq_nil_of_ge hGeSrc
            rw [hDropSrcNil] at hStepStmts
            cases hDropTgt : bbTgt.statements.drop frame.stmtIdx with
            | cons _ _ => rw [hDropTgt] at hStepStmts; cases hStepStmts
            | nil =>
              rw [hDropTgt] at hStepStmts
              dsimp [stepCopyPropCertStmts] at hStepStmts
              injection hStepStmts with hPair; injection hPair with hAEq hEEq
              subst hAEq; subst hEEq
              let ⟨_, hRestBB⟩ := bool_and_true hBBRel
              have hStmtsLenEq : bbSrc.statements.length = bbTgt.statements.length := by
                cases hSynt : stepCopyPropStmtsSyntactic bSrc.locals []
                    bbSrc.statements bbTgt.statements with
                | none => rw [hSynt] at hRestBB; cases hRestBB
                | some _ =>
                  exact (stmtListStoragePreserved_props
                    (stepCopyPropStmtsSyntactic_storage hSynt)).1
              have hStTgtNone : Trusted.MirSemantics.getElem? bbTgt.statements frame.stmtIdx = none :=
                getElem?_none_of_ge (by rw [← hStmtsLenEq]; exact hGeSrc)
              have hStepEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                  evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                unfold evalStep; dsimp
                rw [hBSrc, hBTgt]; dsimp
                rw [hBBSrc, hBBTgt]; dsimp
                rw [hStSrc, hStTgtNone]; dsimp
                rw [hStmtsLenEq]
                cases Nat.beq frame.stmtIdx bbTgt.statements.length with
                | false => rfl
                | true =>
                  rw [if_bool_true rfl, if_bool_true rfl]
                  exact evalTerminator_copyProp_eq hLocEq hCleanEq hAliasesS hTermProp
              refine ⟨hStepEq, ?_⟩
              intro s' hStepS
              unfold evalStep at hStepS; dsimp at hStepS
              rw [hBSrc] at hStepS; dsimp at hStepS
              rw [hBBSrc] at hStepS; dsimp at hStepS
              rw [hStSrc] at hStepS; dsimp at hStepS
              cases hEnd : Nat.beq frame.stmtIdx bbSrc.statements.length with
              | false => rw [hEnd] at hStepS; cases hStepS
              | true =>
                rw [hEnd] at hStepS; dsimp at hStepS
                let ⟨tgt, locs', hSEq, _, hTgtCert⟩ :=
                  checkAbsTerminatorEdges_step_sound hEnvS hEdges hStepS
                subst hSEq
                refine ⟨_, rfl, fun bS2 hBS2 => ?_⟩
                dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                intro bbNext hBBNext
                dsimp at hBBNext
                have hTgtLt := getElem?_some_lt hBBNext
                let ⟨tgtEnv, hCertTgt, hTgtEnvS⟩ := hTgtCert hTgtLt
                let ⟨_, hLoop⟩ := bool_and_true hChkBody
                have hChkTgt := checkCopyPropBlocksLoop_getElem? hLoop hBBNext
                rw [Nat.zero_add] at hChkTgt
                unfold checkCopyPropBlock at hChkTgt
                rw [hCertTgt] at hChkTgt
                cases hBBTgtNext : Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt with
                | none => rw [hBBTgtNext] at hChkTgt; cases hChkTgt
                | some bbNextTgt =>
                  rw [hBBTgtNext] at hChkTgt; dsimp at hChkTgt
                  let ⟨_, hRestNext⟩ := bool_and_true hChkTgt
                  cases hStNext : stepCopyPropCertStmts bSrc.locals [] tgtEnv
                      bbNext.statements bbNextTgt.statements with
                  | none => rw [hStNext] at hRestNext; cases hRestNext
                  | some prN =>
                    let ⟨exitAN, exitEN⟩ := prN
                    rw [hStNext] at hRestNext; dsimp at hRestNext
                    let ⟨hTermN, hEdgesN⟩ := bool_and_true hRestNext
                    exact ⟨bbNextTgt, [], tgtEnv, exitAN, exitEN, rfl,
                      hStNext, hTermN, hEdgesN, hTgtEnvS, True.intro⟩

private theorem copyProp_certified_bidirectional_iff_priv
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isCopyPropProgram pSrc pTgt = true)
    (hCert : checkCopyPropProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
    let ⟨hBHdr, _, hEmpty, _, hBounds, _⟩ := isCopyPropBody_storage hBRel
    exact ⟨hBHdr, hEmpty, hBounds⟩
  · exact copyProp_query_iff hRel hCert
  · intro defId args
    have hRelEntry : isCopyPropProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies
    exact (copyProp_query_iff hRelEntry hCert { args := args }).1


/-! ### Stage 4 Private Helpers — Layer C2: Certified `MoveHeadUnify`
(Theorem 1b) -/

private theorem isMoveHeadRvaluePair_elim {dst src : LocalId} {rvSrc rvTgt : Rvalue}
    (h : isMoveHeadRvaluePair dst src rvSrc rvTgt = true) :
    (∃ p₁ p₂,
      rvSrc = .use (.move p₁) ∧ rvTgt = .use (.move p₂) ∧
      p₁.projection.isEmpty = true ∧ p₂.projection.isEmpty = true ∧
      p₁.localId = dst ∧ p₂.localId = src) ∨
    (∃ op p₁ p₂,
      rvSrc = .unaryOp op (.move p₁) ∧ rvTgt = .unaryOp op (.move p₂) ∧
      p₁.projection.isEmpty = true ∧ p₂.projection.isEmpty = true ∧
      p₁.localId = dst ∧ p₂.localId = src) ∨
    (∃ op p₁ p₂ r,
      rvSrc = .binaryOp op (.move p₁) r ∧ rvTgt = .binaryOp op (.move p₂) r ∧
      p₁.projection.isEmpty = true ∧ p₂.projection.isEmpty = true ∧
      p₁.localId = dst ∧ p₂.localId = src ∧
      operandTouchesLocal dst r = false ∧ operandTouchesLocal src r = false) ∨
    (∃ op l p₁ p₂,
      rvSrc = .binaryOp op l (.move p₁) ∧ rvTgt = .binaryOp op l (.move p₂) ∧
      p₁.projection.isEmpty = true ∧ p₂.projection.isEmpty = true ∧
      p₁.localId = dst ∧ p₂.localId = src ∧
      operandTouchesLocal dst l = false ∧ operandTouchesLocal src l = false) := by
  unfold isMoveHeadRvaluePair at h
  cases rvSrc with
  | discriminant _ | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases h
  | use o₁ =>
    cases o₁ with
    | copy _ | constant _ => cases h
    | move p₁ =>
      cases rvTgt with
      | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
      | addressOf _ _ | aggregateTuple _ | unsupported => cases h
      | use o₂ =>
        cases o₂ with
        | copy _ | constant _ => cases h
        | move p₂ =>
          dsimp at h
          let ⟨h123, h4⟩ := bool_and_true h
          let ⟨h12, h3⟩ := bool_and_true h123
          let ⟨h1, h2⟩ := bool_and_true h12
          exact Or.inl ⟨p₁, p₂, rfl, rfl, h1, h2, nat_beq_eq h3, nat_beq_eq h4⟩
  | unaryOp op₁ o₁ =>
    cases o₁ with
    | copy _ | constant _ => cases h
    | move p₁ =>
      cases rvTgt with
      | use _ | binaryOp _ _ _ | discriminant _ | ref _ _
      | addressOf _ _ | aggregateTuple _ | unsupported => cases h
      | unaryOp op₂ o₂ =>
        cases o₂ with
        | copy _ | constant _ => cases h
        | move p₂ =>
          dsimp at h
          let ⟨h1234, h5⟩ := bool_and_true h
          let ⟨h123, h4⟩ := bool_and_true h1234
          let ⟨h12, h3⟩ := bool_and_true h123
          let ⟨h1, h2⟩ := bool_and_true h12
          rw [unOpEq_eq h1]
          exact Or.inr (Or.inl ⟨op₂, p₁, p₂, rfl, rfl, h2, h3, nat_beq_eq h4, nat_beq_eq h5⟩)
  | binaryOp op₁ l₁ r₁ =>
    have hLhsArm : ∀ op₂ r₂ (p₁ p₂ : Place),
        (binOpEq op₁ op₂ && p₁.projection.isEmpty && p₂.projection.isEmpty &&
         Nat.beq p₁.localId dst && Nat.beq p₂.localId src &&
         operandEq r₁ r₂ && !operandTouchesLocal dst r₁ &&
         !operandTouchesLocal src r₁) = true →
        l₁ = .move p₁ →
        rvTgt = .binaryOp op₂ (.move p₂) r₂ →
        ∃ (op : BinOp) (q₁ q₂ : Place) (r : Operand),
          Rvalue.binaryOp op₁ l₁ r₁ = .binaryOp op (.move q₁) r ∧
          rvTgt = .binaryOp op (.move q₂) r ∧
          q₁.projection.isEmpty = true ∧ q₂.projection.isEmpty = true ∧
          q₁.localId = dst ∧ q₂.localId = src ∧
          operandTouchesLocal dst r = false ∧ operandTouchesLocal src r = false := by
      intro op₂ r₂ p₁ p₂ hc hl ht
      let ⟨c1, c8⟩ := bool_and_true hc
      let ⟨c2, c7⟩ := bool_and_true c1
      let ⟨c3, c6⟩ := bool_and_true c2
      let ⟨c4, c5⟩ := bool_and_true c3
      let ⟨c5a, c4b⟩ := bool_and_true c4
      let ⟨c6a, c3b⟩ := bool_and_true c5a
      let ⟨c1b, c2b⟩ := bool_and_true c6a
      subst hl
      exact ⟨op₂, p₁, p₂, r₂,
             by rw [binOpEq_eq c1b, operandEq_eq c6],
             ht, c2b, c3b, nat_beq_eq c4b, nat_beq_eq c5,
             by rw [← operandEq_eq c6]; exact bool_not_true c7,
             by rw [← operandEq_eq c6]; exact bool_not_true c8⟩
    have hRhsArm : ∀ op₂ l₂ (p₁ p₂ : Place),
        (binOpEq op₁ op₂ && p₁.projection.isEmpty && p₂.projection.isEmpty &&
         Nat.beq p₁.localId dst && Nat.beq p₂.localId src &&
         operandEq l₁ l₂ && !operandTouchesLocal dst l₁ &&
         !operandTouchesLocal src l₁) = true →
        r₁ = .move p₁ →
        rvTgt = .binaryOp op₂ l₂ (.move p₂) →
        ∃ (op : BinOp) (l : Operand) (q₁ q₂ : Place),
          Rvalue.binaryOp op₁ l₁ r₁ = .binaryOp op l (.move q₁) ∧
          rvTgt = .binaryOp op l (.move q₂) ∧
          q₁.projection.isEmpty = true ∧ q₂.projection.isEmpty = true ∧
          q₁.localId = dst ∧ q₂.localId = src ∧
          operandTouchesLocal dst l = false ∧ operandTouchesLocal src l = false := by
      intro op₂ l₂ p₁ p₂ hc hr ht
      let ⟨c1, c8⟩ := bool_and_true hc
      let ⟨c2, c7⟩ := bool_and_true c1
      let ⟨c3, c6⟩ := bool_and_true c2
      let ⟨c4, c5⟩ := bool_and_true c3
      let ⟨c5a, c4b⟩ := bool_and_true c4
      let ⟨c6a, c3b⟩ := bool_and_true c5a
      let ⟨c1b, c2b⟩ := bool_and_true c6a
      subst hr
      exact ⟨op₂, l₂, p₁, p₂,
             by rw [binOpEq_eq c1b, operandEq_eq c6],
             ht, c2b, c3b, nat_beq_eq c4b, nat_beq_eq c5,
             by rw [← operandEq_eq c6]; exact bool_not_true c7,
             by rw [← operandEq_eq c6]; exact bool_not_true c8⟩
    cases l₁ with
    | copy _ | constant _ =>
      cases r₁ with
      | copy _ | constant _ => cases h
      | move pr1 =>
        cases rvTgt with
        | use _ | unaryOp _ _ | discriminant _ | ref _ _
        | addressOf _ _ | aggregateTuple _ | unsupported => cases h
        | binaryOp op₂ l₂ r₂ =>
          cases r₂ with
          | copy _ | constant _ => cases h
          | move pr2 => exact Or.inr (Or.inr (Or.inr (hRhsArm op₂ l₂ pr1 pr2 h rfl rfl)))
    | move pl1 =>
      cases rvTgt with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _
      | addressOf _ _ | aggregateTuple _ | unsupported =>
        cases r₁ <;> cases h
      | binaryOp op₂ l₂ r₂ =>
        cases l₂ with
        | copy _ | constant _ =>
          cases r₁ with
          | copy _ | constant _ => cases r₂ <;> cases h
          | move pr1 =>
            cases r₂ with
            | copy _ | constant _ => cases h
            | move pr2 => exact Or.inr (Or.inr (Or.inr (hRhsArm op₂ _ pr1 pr2 h rfl rfl)))
        | move pl2 =>
          exact Or.inr (Or.inr (Or.inl (hLhsArm op₂ r₂ pl1 pl2 h rfl rfl)))

private theorem isMoveHeadRvaluePair_touches_src {dst src : LocalId} {rvSrc rvTgt : Rvalue}
    (h : isMoveHeadRvaluePair dst src rvSrc rvTgt = true) :
    rvalueTouchesLocal src rvTgt = true := by
  cases isMoveHeadRvaluePair_elim h with
  | inl hCase =>
    let ⟨_, p₂, _, ht, _, _, _, hId2⟩ := hCase
    subst ht; dsimp [rvalueTouchesLocal, operandTouchesLocal]
    rw [hId2]; exact nat_beq_refl src
  | inr hRest =>
    cases hRest with
    | inl hCase =>
      let ⟨_, _, p₂, _, ht, _, _, _, hId2⟩ := hCase
      subst ht; dsimp [rvalueTouchesLocal, operandTouchesLocal]
      rw [hId2]; exact nat_beq_refl src
    | inr hRest2 =>
      cases hRest2 with
      | inl hCase =>
        let ⟨_, _, p₂, _, _, ht, _, _, _, hId2, _, _⟩ := hCase
        subst ht; dsimp [rvalueTouchesLocal, operandTouchesLocal]
        rw [hId2, nat_beq_refl src]; rfl
      | inr hCase =>
        let ⟨_, l, _, p₂, _, ht, _, _, _, hId2, _, _⟩ := hCase
        subst ht
        change (operandTouchesLocal src l || Nat.beq p₂.localId src) = true
        rw [hId2, nat_beq_refl src]
        cases operandTouchesLocal src l <;> rfl

private noncomputable def MoveHeadMidLocals (bodyLocals : List MirTy)
    (D_rest : LocalId → Prop) (dst src : LocalId) (dstTy : MirTy) (v : Val)
    (locs₁ locs₂ : List LocalSlot) : Prop :=
  dst ≠ src ∧
  Trusted.MirSemantics.getElem? bodyLocals dst = some dstTy ∧
  Trusted.MirSemantics.getElem? bodyLocals src = some dstTy ∧
  checkVal v dstTy = true ∧
  Trusted.MirSemantics.getElem? locs₁ src = some (liveUninitSlot dstTy) ∧
  Trusted.MirSemantics.getElem? locs₂ src = some (.live (some v)) ∧
  Trusted.MirSemantics.getElem? locs₁ dst = some (.live (some v)) ∧
  (∃ optT, Trusted.MirSemantics.getElem? locs₂ dst = some (.live optT)) ∧
  DeadMaskedEq bodyLocals (fun d => D_rest d ∨ d = dst ∨ d = src) locs₁ locs₂

private theorem moveHead_consume_pair {bodyLocals : List MirTy}
    {D_rest : LocalId → Prop} {dst src : LocalId} {dstTy : MirTy} {v : Val}
    {locs₁ locs₂ : List LocalSlot} {p₁ p₂ : Place}
    (hMid : MoveHeadMidLocals bodyLocals D_rest dst src dstTy v locs₁ locs₂)
    (hEmp1 : p₁.projection.isEmpty = true)
    (hEmp2 : p₂.projection.isEmpty = true)
    (hId1 : p₁.localId = dst)
    (hId2 : p₂.localId = src) :
    ∃ locs₁' locs₂',
      evalOperandToSlot bodyLocals locs₁ (.move p₁) = .ok (dstTy, some v, locs₁') ∧
      evalOperandToSlot bodyLocals locs₂ (.move p₂) = .ok (dstTy, some v, locs₂') ∧
      DeadMaskedEq bodyLocals (fun d => D_rest d ∨ d = dst) locs₁' locs₂' := by
  let ⟨hNe, hTyD, hTyS, _, hL1S, hL2S, hL1D, hOptT, hMask⟩ := hMid
  let ⟨optT, hL2D⟩ := hOptT
  let ⟨hWt1, hWt2, hAll⟩ := hMask
  have hLtD : dst < bodyLocals.length := getElem?_some_lt hTyD
  have hLtS : src < bodyLocals.length := getElem?_some_lt hTyS
  let ⟨locs₁', hSet1⟩ := setElem?_some_of_lt locs₁ dst (liveUninitSlot dstTy)
    (by rw [hWt1.1]; exact hLtD)
  let ⟨locs₂', hSet2⟩ := setElem?_some_of_lt locs₂ src (liveUninitSlot dstTy)
    (by rw [hWt2.1]; exact hLtS)
  refine ⟨locs₁', locs₂', ?_, ?_, ?_⟩
  · dsimp [evalOperandToSlot]
    rw [hEmp1, hId1]; dsimp
    rw [hTyD, hL1D]; dsimp; rw [hSet1]
  · dsimp [evalOperandToSlot]
    rw [hEmp2, hId2]; dsimp
    rw [hTyS, hL2S]; dsimp; rw [hSet2]
  · refine ⟨localsWellTyped_set hWt1 hTyD hSet1 (liveUninitSlot_wellTyped dstTy),
            localsWellTyped_set hWt2 hTyS hSet2 (liveUninitSlot_wellTyped dstTy),
            fun i => ?_⟩
    cases hEqD : Nat.beq i dst with
    | true =>
      have hiD := nat_beq_eq hEqD; subst hiD
      rw [setElem?_getElem?_same hSet1, setElem?_getElem?_ne hSet2 hNe, hL2D]
      let ⟨optU, hOptU⟩ := liveUninitSlot_isLive dstTy
      rw [hOptU]
      refine ⟨?_, fun hNot => False.elim (hNot (Or.inr rfl))⟩
      intro sl₁ sl₂ e1 e2; injection e1 with q1; injection e2 with q2; subst q1; subst q2
      exact True.intro
    | false =>
      have hiNeD := nat_ne_of_beq_false hEqD
      rw [setElem?_getElem?_ne hSet1 hiNeD]
      cases hEqS : Nat.beq i src with
      | true =>
        have hiS := nat_beq_eq hEqS; subst hiS
        rw [setElem?_getElem?_same hSet2, hL1S]
        refine ⟨?_, fun _ => rfl⟩
        intro sl₁ sl₂ e1 e2; injection e1 with q1; injection e2 with q2; subst q1; subst q2
        exact sameLiveness_refl (liveUninitSlot dstTy)
      | false =>
        have hiNeS := nat_ne_of_beq_false hEqS
        rw [setElem?_getElem?_ne hSet2 hiNeS]
        exact ⟨(hAll i).1, fun hNot =>
          (hAll i).2 (fun hOr =>
            match hOr with
            | Or.inl hDr => hNot (Or.inl hDr)
            | Or.inr (Or.inl hId) => hiNeD hId
            | Or.inr (Or.inr hIs) => hiNeS hIs)⟩

private theorem moveHeadMid_untouched_op {bodyLocals : List MirTy}
    {D_rest : LocalId → Prop} {dst src : LocalId} {dstTy : MirTy} {v : Val}
    {locs₁ locs₂ : List LocalSlot} {op : Operand}
    (hMid : MoveHeadMidLocals bodyLocals D_rest dst src dstTy v locs₁ locs₂)
    (hNoD : operandTouchesLocal dst op = false)
    (hNoS : operandTouchesLocal src op = false)
    (hNoRest : ∀ d, D_rest d → operandTouchesLocal d op = false) :
    (∃ fk,
      evalPrimitiveOperand bodyLocals locs₁ op = .error fk ∧
      evalPrimitiveOperand bodyLocals locs₂ op = .error fk) ∨
    (∃ vo locs₁' locs₂',
      evalPrimitiveOperand bodyLocals locs₁ op = .ok (vo, locs₁') ∧
      evalPrimitiveOperand bodyLocals locs₂ op = .ok (vo, locs₂') ∧
      MoveHeadMidLocals bodyLocals D_rest dst src dstTy v locs₁' locs₂') := by
  let ⟨hNe, hTyD, hTyS, hChkV, hL1S, hL2S, hL1D, hOptT, hMask⟩ := hMid
  have hUntouchedAll : ∀ d, (D_rest d ∨ d = dst ∨ d = src) →
      operandTouchesLocal d op = false := by
    intro d hOr
    cases hOr with
    | inl hDr => exact hNoRest d hDr
    | inr hDS =>
      cases hDS with
      | inl hEqD => subst hEqD; exact hNoD
      | inr hEqS => subst hEqS; exact hNoS
  cases op with
  | constant c =>
    dsimp [evalPrimitiveOperand, evalOperandToSlot]
    cases evalConstLit c.ty c.lit with
    | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
    | ok vc =>
      dsimp
      cases isPrimitiveReadableTy c.ty with
      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | true => exact Or.inr ⟨vc, locs₁, locs₂, rfl, rfl, hMid⟩
  | copy p =>
    cases evalPrimitiveOperand_untouched_bisim hMask hUntouchedAll with
    | inl hCase =>
      let ⟨fk, hE1, hE2⟩ := hCase
      exact Or.inl ⟨fk, hE1, hE2⟩
    | inr hCase =>
      let ⟨vo, l1, l2, hO1, hO2, _⟩ := hCase
      have hSame1 : l1 = locs₁ := by
        dsimp [evalPrimitiveOperand, evalOperandToSlot] at hO1
        cases hP : p.projection.isEmpty with
        | false => rw [hP] at hO1; cases hO1
        | true =>
          rw [hP] at hO1; dsimp at hO1
          cases hT : Trusted.MirSemantics.getElem? bodyLocals p.localId with
          | none => rw [hT] at hO1; cases hO1
          | some pt =>
            rw [hT] at hO1
            cases hG : Trusted.MirSemantics.getElem? locs₁ p.localId with
            | none => rw [hG] at hO1; cases hO1
            | some sl =>
              rw [hG] at hO1
              cases sl with
              | dead => cases hO1
              | live po =>
                dsimp at hO1
                cases hPr : isPrimitiveReadableTy pt with
                | false => rw [hPr] at hO1; cases hO1
                | true =>
                  rw [hPr] at hO1; dsimp at hO1
                  cases po with
                  | none => cases hO1
                  | some _ => injection hO1 with q1; injection q1 with _ qL; exact qL.symm
      have hSame2 : l2 = locs₂ := by
        dsimp [evalPrimitiveOperand, evalOperandToSlot] at hO2
        cases hP : p.projection.isEmpty with
        | false => rw [hP] at hO2; cases hO2
        | true =>
          rw [hP] at hO2; dsimp at hO2
          cases hT : Trusted.MirSemantics.getElem? bodyLocals p.localId with
          | none => rw [hT] at hO2; cases hO2
          | some pt =>
            rw [hT] at hO2
            cases hG : Trusted.MirSemantics.getElem? locs₂ p.localId with
            | none => rw [hG] at hO2; cases hO2
            | some sl =>
              rw [hG] at hO2
              cases sl with
              | dead => cases hO2
              | live po =>
                dsimp at hO2
                cases hPr : isPrimitiveReadableTy pt with
                | false => rw [hPr] at hO2; cases hO2
                | true =>
                  rw [hPr] at hO2; dsimp at hO2
                  cases po with
                  | none => cases hO2
                  | some _ => injection hO2 with q1; injection q1 with _ qL; exact qL.symm
      subst hSame1; subst hSame2
      exact Or.inr ⟨vo, l1, l2, hO1, hO2, hMid⟩
  | move p =>
    dsimp [operandTouchesLocal] at hNoD hNoS
    have hpNeD : dst ≠ p.localId := (nat_ne_of_beq_false hNoD).symm
    have hpNeS : src ≠ p.localId := (nat_ne_of_beq_false hNoS).symm
    cases evalPrimitiveOperand_untouched_bisim hMask hUntouchedAll with
    | inl hCase =>
      let ⟨fk, hE1, hE2⟩ := hCase
      exact Or.inl ⟨fk, hE1, hE2⟩
    | inr hCase =>
      let ⟨vo, l1, l2, hO1, hO2, hM'⟩ := hCase
      have hKeep1 : ∀ k, k ≠ p.localId →
          Trusted.MirSemantics.getElem? l1 k = Trusted.MirSemantics.getElem? locs₁ k := by
        intro k hkNe
        dsimp [evalPrimitiveOperand, evalOperandToSlot] at hO1
        cases hP : p.projection.isEmpty with
        | false => rw [hP] at hO1; cases hO1
        | true =>
          rw [hP] at hO1; dsimp at hO1
          cases hT : Trusted.MirSemantics.getElem? bodyLocals p.localId with
          | none => rw [hT] at hO1; cases hO1
          | some pt =>
            rw [hT] at hO1
            cases hG : Trusted.MirSemantics.getElem? locs₁ p.localId with
            | none => rw [hG] at hO1; cases hO1
            | some sl =>
              rw [hG] at hO1
              cases sl with
              | dead => cases hO1
              | live po =>
                dsimp at hO1
                cases hSet : setElem? locs₁ p.localId (liveUninitSlot pt) with
                | none => rw [hSet] at hO1; cases hO1
                | some lm =>
                  rw [hSet] at hO1; dsimp at hO1
                  cases hPr : isPrimitiveReadableTy pt with
                  | false => rw [hPr] at hO1; cases hO1
                  | true =>
                    rw [hPr] at hO1; dsimp at hO1
                    cases po with
                    | none => cases hO1
                    | some _ =>
                      injection hO1 with q1; injection q1 with _ qL; subst qL
                      exact setElem?_getElem?_ne hSet hkNe
      have hKeep2 : ∀ k, k ≠ p.localId →
          Trusted.MirSemantics.getElem? l2 k = Trusted.MirSemantics.getElem? locs₂ k := by
        intro k hkNe
        dsimp [evalPrimitiveOperand, evalOperandToSlot] at hO2
        cases hP : p.projection.isEmpty with
        | false => rw [hP] at hO2; cases hO2
        | true =>
          rw [hP] at hO2; dsimp at hO2
          cases hT : Trusted.MirSemantics.getElem? bodyLocals p.localId with
          | none => rw [hT] at hO2; cases hO2
          | some pt =>
            rw [hT] at hO2
            cases hG : Trusted.MirSemantics.getElem? locs₂ p.localId with
            | none => rw [hG] at hO2; cases hO2
            | some sl =>
              rw [hG] at hO2
              cases sl with
              | dead => cases hO2
              | live po =>
                dsimp at hO2
                cases hSet : setElem? locs₂ p.localId (liveUninitSlot pt) with
                | none => rw [hSet] at hO2; cases hO2
                | some lm =>
                  rw [hSet] at hO2; dsimp at hO2
                  cases hPr : isPrimitiveReadableTy pt with
                  | false => rw [hPr] at hO2; cases hO2
                  | true =>
                    rw [hPr] at hO2; dsimp at hO2
                    cases po with
                    | none => cases hO2
                    | some _ =>
                      injection hO2 with q1; injection q1 with _ qL; subst qL
                      exact setElem?_getElem?_ne hSet hkNe
      let ⟨optT, hL2D⟩ := hOptT
      exact Or.inr ⟨vo, l1, l2, hO1, hO2,
        ⟨hNe, hTyD, hTyS, hChkV,
         by rw [hKeep1 src hpNeS]; exact hL1S,
         by rw [hKeep2 src hpNeS]; exact hL2S,
         by rw [hKeep1 dst hpNeD]; exact hL1D,
         ⟨optT, by rw [hKeep2 dst hpNeD]; exact hL2D⟩,
         hM'⟩⟩

private theorem evalRvalue_moveHead_mid_bisim {bodyLocals : List MirTy}
    {D_rest : LocalId → Prop} {dst src : LocalId} {dstTy outTy : MirTy}
    {v : Val} {locs₁ locs₂ : List LocalSlot} {rvSrc rvTgt : Rvalue}
    (hMid : MoveHeadMidLocals bodyLocals D_rest dst src dstTy v locs₁ locs₂)
    (hPair : isMoveHeadRvaluePair dst src rvSrc rvTgt = true)
    (hNoTouchTgt : ∀ d, D_rest d → rvalueTouchesLocal d rvTgt = false) :
    (∃ fk,
      evalRvalue bodyLocals locs₁ outTy rvSrc = .error fk ∧
      evalRvalue bodyLocals locs₂ outTy rvTgt = .error fk) ∨
    (∃ res locs₁' locs₂',
      evalRvalue bodyLocals locs₁ outTy rvSrc = .ok (res, locs₁') ∧
      evalRvalue bodyLocals locs₂ outTy rvTgt = .ok (res, locs₂') ∧
      DeadMaskedEq bodyLocals (fun d => D_rest d ∨ d = dst) locs₁' locs₂') := by
  cases isMoveHeadRvaluePair_elim hPair with
  | inl hCase =>
    let ⟨p₁, p₂, hs, ht, hEmp1, hEmp2, hId1, hId2⟩ := hCase
    subst hs; subst ht
    let ⟨l1, l2, hO1, hO2, hMask'⟩ := moveHead_consume_pair hMid hEmp1 hEmp2 hId1 hId2
    dsimp [evalRvalue]; rw [hO1, hO2]; dsimp
    cases MirTy.beq dstTy outTy with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true => exact Or.inr ⟨v, l1, l2, rfl, rfl, hMask'⟩
  | inr hRest =>
    cases hRest with
    | inl hCase =>
      let ⟨op, p₁, p₂, hs, ht, hEmp1, hEmp2, hId1, hId2⟩ := hCase
      subst hs; subst ht
      let ⟨l1, l2, hO1, hO2, hMask'⟩ := moveHead_consume_pair hMid hEmp1 hEmp2 hId1 hId2
      dsimp [evalRvalue, evalPrimitiveOperand]; rw [hO1, hO2]; dsimp
      cases isPrimitiveReadableTy dstTy with
      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | true =>
        dsimp
        cases evalUnOp op v with
        | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
        | ok res => exact Or.inr ⟨res, l1, l2, rfl, rfl, hMask'⟩
    | inr hRest2 =>
      cases hRest2 with
      | inl hCase =>
        let ⟨op, p₁, p₂, r, hs, ht, hEmp1, hEmp2, hId1, hId2, hNoDR, _⟩ := hCase
        subst hs; subst ht
        have hNoRestR : ∀ d, (D_rest d ∨ d = dst) → operandTouchesLocal d r = false := by
          intro d hOr
          cases hOr with
          | inl hDr => exact (bool_or_false (hNoTouchTgt d hDr)).2
          | inr hEqD => subst hEqD; exact hNoDR
        dsimp [evalRvalue, evalPrimitiveOperand]
        let ⟨la1, la2, hOL1, hOL2, hMask1⟩ :=
          moveHead_consume_pair hMid hEmp1 hEmp2 hId1 hId2
        rw [hOL1, hOL2]; dsimp
        cases isPrimitiveReadableTy dstTy with
        | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | true =>
          dsimp
          cases evalPrimitiveOperand_untouched_bisim hMask1 hNoRestR with
          | inl hC =>
            let ⟨fk, hER1, hER2⟩ := hC
            dsimp [evalPrimitiveOperand] at hER1 hER2
            rw [hER1, hER2]; exact Or.inl ⟨fk, rfl, rfl⟩
          | inr hC =>
            let ⟨vr, l1', l2', hOR1, hOR2, hMask2⟩ := hC
            dsimp [evalPrimitiveOperand] at hOR1 hOR2
            rw [hOR1, hOR2]; dsimp
            cases evalBinOp op v vr with
            | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
            | ok res => exact Or.inr ⟨res, l1', l2', rfl, rfl, hMask2⟩
      | inr hCase =>
        let ⟨op, l, p₁, p₂, hs, ht, hEmp1, hEmp2, hId1, hId2, hNoDL, hNoSL⟩ := hCase
        subst hs; subst ht
        have hNoRestL : ∀ d, D_rest d → operandTouchesLocal d l = false :=
          fun d hDr => (bool_or_false (hNoTouchTgt d hDr)).1
        dsimp [evalRvalue]
        cases moveHeadMid_untouched_op hMid hNoDL hNoSL hNoRestL with
        | inl hC =>
          let ⟨fk, hE1, hE2⟩ := hC
          rw [hE1, hE2]; exact Or.inl ⟨fk, rfl, rfl⟩
        | inr hC =>
          let ⟨vl, la1, la2, hOL1, hOL2, hMid'⟩ := hC
          rw [hOL1, hOL2]; dsimp
          let ⟨l1', l2', hOR1, hOR2, hMask'⟩ :=
            moveHead_consume_pair hMid' hEmp1 hEmp2 hId1 hId2
          dsimp [evalPrimitiveOperand]; rw [hOR1, hOR2]; dsimp
          cases isPrimitiveReadableTy dstTy with
          | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
          | true =>
            dsimp
            cases evalBinOp op vl v with
            | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
            | ok res => exact Or.inr ⟨res, l1', l2', rfl, rfl, hMask'⟩

private theorem isMoveHeadUnifyStmts_storage_aux {bodyLocals : List MirTy}
    {termTgt : TerminatorKind} :
    ∀ (n : Nat) {ss₁ ss₂ : List StatementKind},
      ss₁.length ≤ n →
      isMoveHeadUnifyStmts bodyLocals termTgt ss₁ ss₂ = true →
      StmtListStoragePreserved ss₁ ss₂ := by
  intro n
  induction n with
  | zero =>
    intro ss₁ ss₂ hLe hRel
    cases ss₁ with
    | cons _ r => exact False.elim (Nat.not_succ_le_zero r.length hLe)
    | nil =>
      cases ss₂ with
      | nil => exact True.intro
      | cons _ _ => cases hRel
  | succ k ih =>
    intro ss₁ ss₂ hLe hRel
    cases ss₁ with
    | nil =>
      cases ss₂ with
      | nil => exact True.intro
      | cons _ _ => cases hRel
    | cons s₁ tail₁ =>
      cases tail₁ with
      | nil =>
        cases ss₂ with
        | nil => cases hRel
        | cons t₁ tail₂ =>
          cases tail₂ with
          | cons _ _ => cases hRel
          | nil =>
            dsimp [isMoveHeadUnifyStmts] at hRel
            exact ⟨Or.inl (stmtEq_eq hRel), True.intro⟩
      | cons s₂ r₁ =>
        cases ss₂ with
        | nil => cases hRel
        | cons t₁ tail₂ =>
          cases tail₂ with
          | nil => cases hRel
          | cons t₂ r₂ =>
            dsimp [isMoveHeadUnifyStmts] at hRel
            have hLe1 : (s₂ :: r₁).length ≤ k := Nat.le_of_succ_le_succ hLe
            have hLe2 : r₁.length ≤ k :=
              Nat.le_trans (Nat.le_succ r₁.length) hLe1
            cases hPair : isMoveHeadUnifyPair bodyLocals s₁ s₂ t₁ t₂ r₂ termTgt with
            | true =>
              rw [hPair] at hRel; dsimp at hRel
              have hS12 : NonStorageOrEqStmt s₁ t₁ ∧ NonStorageOrEqStmt s₂ t₂ := by
                cases s₁ with
                | nop | storageLive _ | storageDead _ | unsupported => cases hPair
                | assign _ rv1 =>
                  cases rv1 with
                  | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
                  | addressOf _ _ | aggregateTuple _ | unsupported => cases hPair
                  | use o1 =>
                    cases o1 with
                    | copy _ | constant _ => cases hPair
                    | move _ =>
                      cases s₂ with
                      | nop | storageLive _ | storageDead _ | unsupported => cases hPair
                      | assign _ _ =>
                        cases t₁ with
                        | assign _ _ | storageLive _ | storageDead _ | unsupported => cases hPair
                        | nop =>
                          cases t₂ with
                          | nop | storageLive _ | storageDead _ | unsupported => cases hPair
                          | assign _ _ =>
                            exact ⟨Or.inr ⟨True.intro, True.intro⟩,
                                   Or.inr ⟨True.intro, True.intro⟩⟩
              exact ⟨hS12.1, ⟨hS12.2, ih hLe2 hRel⟩⟩
            | false =>
              rw [hPair] at hRel; dsimp at hRel
              let ⟨hEq1, hRest⟩ := bool_and_true hRel
              exact ⟨Or.inl (stmtEq_eq hEq1), ih hLe1 hRest⟩

private theorem isMoveHeadUnifyBody_storage {bSrc bTgt : Body}
    (hBody : isMoveHeadUnifyBody bSrc bTgt = true) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    (∀ idx, hasStorageAnnotation bSrc idx = hasStorageAnnotation bTgt idx) ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨hBHdr, hBBs⟩ := bool_and_true hBody
  apply bodyStorage_eq_of_blocks hBHdr hBBs
  intro bb₁ bb₂ hBB
  let ⟨_, hStmts⟩ := bool_and_true hBB
  exact isMoveHeadUnifyStmts_storage_aux bb₁.statements.length
    (Nat.le_refl _) hStmts

private theorem moveHead_initState_eq {pSrc pTgt : Program}
    (hRel : isMoveHeadUnifyProgram pSrc pTgt = true) (q : Query) :
    initState pSrc q = initState pTgt q := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodies
  · intro b₁ hB₁
    let ⟨b₂, hB₂, hBRel⟩ := listRel_getElem?_left hBodies hB₁
    rw [hEnt] at hB₂
    let ⟨hBHdr, _, hEmpty, _, hBounds, hLoop⟩ := isMoveHeadUnifyBody_storage hBRel
    exact ⟨b₂, hB₂, hBHdr, hEmpty, hBounds, hLoop q.args⟩

private theorem checkMoveHeadBlocksLoop_getElem? {bSrc bTgt : Body}
    {cert : BodyAbsCert} :
    ∀ {base bbs k bbSrc},
      checkMoveHeadBlocksLoop bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      checkMoveHeadBlock bSrc bTgt cert (base + k) bbSrc = true := by
  intro base bbs
  induction bbs generalizing base with
  | nil => intro _ _ _ hG; cases hG
  | cons _ _ ih =>
    intro k bbSrc hLoop hG
    let ⟨hHead, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hG with hEq; subst hEq
      rw [Nat.add_zero]; exact hHead
    | succ m =>
      have hSub := ih hTail hG
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hSub
      exact hSub

private noncomputable def MoveHeadBlockMode (bSrc _bTgt : Body) (bCert : BodyAbsCert)
    (bbSrc bbTgt : BasicBlock) (fSrc fTgt : FrameState) : Prop :=
  (∃ env exitEnv,
    stepMoveHeadCertStmts bSrc.locals bbTgt.terminator env
      (bbSrc.statements.drop fSrc.stmtIdx)
      (bbTgt.statements.drop fSrc.stmtIdx) = some exitEnv ∧
    checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      bCert exitEnv bbSrc.terminator = true ∧
    AbsEnvSound bSrc.locals env fSrc.locals ∧
    DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadInBlockFrom d (bbTgt.statements.drop fSrc.stmtIdx) bbTgt.terminator = true)
      fSrc.locals fTgt.locals) ∨
  (∃ outPlace rvSrc rvTgt restSrc restTgt dst src dstTy v env₁ env₂ exitEnv,
    bbSrc.statements.drop fSrc.stmtIdx = (.assign outPlace rvSrc) :: restSrc ∧
    bbTgt.statements.drop fSrc.stmtIdx = (.assign outPlace rvTgt) :: restTgt ∧
    outPlace.projection.isEmpty = true ∧
    dst ≠ 0 ∧
    isMoveHeadRvaluePair dst src rvSrc rvTgt = true ∧
    (Nat.beq outPlace.localId dst = true ∨
      isDeadInBlockFrom dst restTgt bbTgt.terminator = true) ∧
    MoveHeadMidLocals bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadInBlockFrom d ((.assign outPlace rvTgt) :: restTgt) bbTgt.terminator = true)
      dst src dstTy v fSrc.locals fTgt.locals ∧
    AbsEnvSound bSrc.locals env₁ fSrc.locals ∧
    stepPlainStmtAbs bSrc.locals env₁ (.assign outPlace rvSrc) = some env₂ ∧
    stepMoveHeadCertStmts bSrc.locals bbTgt.terminator env₂ restSrc restTgt =
      some exitEnv ∧
    checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      bCert exitEnv bbSrc.terminator = true)

private noncomputable def MoveHeadBisimRel (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (s t : State) : Prop :=
  ∃ fSrc fTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    ∀ bSrc,
      Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
      ∃ bTgt bCert,
        Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
        Trusted.MirSemantics.getElem? cert fSrc.defId = some bCert ∧
        isMoveHeadUnifyBody bSrc bTgt = true ∧
        checkMoveHeadUnifyBody bCert bSrc bTgt = true ∧
        ∀ bbSrc,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
          ∃ bbTgt,
            Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt ∧
            MoveHeadBlockMode bSrc bTgt bCert bbSrc bbTgt fSrc fTgt

private theorem moveHead_kept_step_helper {pSrc pTgt : Program} {cert : ProgramAbsCert}
    {bSrc bTgt : Body} {bCert : BodyAbsCert} {bbSrc bbTgt : BasicBlock}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmt : StatementKind} {restSrc restTgt : List StatementKind}
    {env env₁ exitEnv : List AbsSlot}
    (hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc)
    (hBTgt : Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt)
    (hBCert : Trusted.MirSemantics.getElem? cert fSrc.defId = some bCert)
    (hBRel : isMoveHeadUnifyBody bSrc bTgt = true)
    (hChkBody : checkMoveHeadUnifyBody bCert bSrc bTgt = true)
    (hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc)
    (hBBTgt : Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt)
    (hDefEq : fSrc.defId = fTgt.defId)
    (hBlkEq : fSrc.blockIdx = fTgt.blockIdx)
    (hIdxEq : fSrc.stmtIdx = fTgt.stmtIdx)
    (hLocEq : bSrc.locals = bTgt.locals)
    (hDropS : bbSrc.statements.drop fSrc.stmtIdx = stmt :: restSrc)
    (hDropT : bbTgt.statements.drop fSrc.stmtIdx = stmt :: restTgt)
    (hEnvS : AbsEnvSound bSrc.locals env fSrc.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧ isDeadInBlockFrom d (stmt :: restTgt) bbTgt.terminator = true)
      fSrc.locals fTgt.locals)
    (hStep1 : stepPlainStmtAbs bSrc.locals env stmt = some env₁)
    (hStepRest : stepMoveHeadCertStmts bSrc.locals bbTgt.terminator env₁
      restSrc restTgt = some exitEnv)
    (hEdges : checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      bCert exitEnv bbSrc.terminator = true) :
    StepOutcomeBisim pSrc pTgt (MoveHeadBisimRel pSrc pTgt cert)
      { frames := [fSrc], callerMem := cm }
      { frames := [fTgt], callerMem := cm } := by
  let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
  let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
  have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
    rw [← hDefEq]; exact hBTgt
  have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
    rw [← hBlkEq]; exact hBBTgt
  have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some stmt := by
    rw [← hIdxEq]; exact hStTgt0
  unfold StepOutcomeBisim evalStep; dsimp
  rw [hBSrc, hBTgt2]; dsimp
  rw [hBBSrc, hBBTgt2]; dsimp
  rw [hStSrc, hStTgt2]; dsimp
  cases isDeadInBlockFrom_kept_step (cm := cm) hLocEq hMask with
  | inl hCase =>
    let ⟨fk, hF1, hF2⟩ := hCase
    rw [hF1, hF2]
    exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
  | inr hCase =>
    let ⟨l1', l2', hS1, hS2, hMask'⟩ := hCase
    let ⟨l1'', hEqS', hEnv1⟩ := stepPlainStmtAbs_sound hEnvS hStep1 hS1
    injection hEqS' with eFs _; injection eFs with eF _; injection eF with _ _ _ eL
    subst eL
    rw [hS1, hS2]
    refine Or.inl ⟨_, _, rfl, rfl,
      { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' },
      rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
    intro bS2 hBS2
    dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
    refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
    intro bbS2 hBBS2
    dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
    refine ⟨bbTgt, hBBTgt, Or.inl ⟨env₁, exitEnv, ?_, hEdges, hEnv1, ?_⟩⟩
    · dsimp; rw [hDropSNext, hDropTNext]; exact hStepRest
    · dsimp; rw [hDropTNext]; exact hMask'

private theorem moveHead_query_iff {pSrc pTgt : Program} {cert : ProgramAbsCert}
    (hRel : isMoveHeadUnifyProgram pSrc pTgt = true)
    (hCert : checkMoveHeadUnifyProgram cert pSrc pTgt = true) (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLenB, hCertZip⟩ := bool_and_true hCert
  have hCertLen := nat_beq_eq hCertLenB
  apply bisim_lockstep_query_iff (R := MoveHeadBisimRel pSrc pTgt cert)
    (moveHead_initState_eq hRel q)
  · intro s₀ hOk
    let ⟨_, _, body, hBody, hNotEmp, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    have hInitSound := initAbsEnvLoop_sound hArgs
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, fun bSrc hBS => ?_⟩
    rw [hBody] at hBS; injection hBS with eB; subst eB
    let ⟨bCert, bTgt, hBCert, hBTgt, hChkBody⟩ :=
      listRel_zip_getElem? hCertLen hCertZip hBody
    let ⟨bTgt', hBTgt', hBRel⟩ := listRel_getElem?_left hBodiesRel hBody
    rw [hBTgt] at hBTgt'; injection hBTgt' with eT; subst eT
    refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
    intro bbSrc hBB0
    dsimp at hBB0
    let ⟨h123, hLoop⟩ := bool_and_true hChkBody
    let ⟨_, hEntry0⟩ := bool_and_true h123
    rw [hNotEmp] at hEntry0; dsimp at hEntry0
    cases hC0 : Trusted.MirSemantics.getElem? bCert 0 with
    | none => rw [hC0] at hEntry0; cases hEntry0
    | some opt0 =>
      rw [hC0] at hEntry0
      cases opt0 with
      | none => cases hEntry0
      | some env₀ =>
        have hEnv0 := absEnvImplies_sound hEntry0 hInitSound
        have hChk0 := checkMoveHeadBlocksLoop_getElem? (k := 0) hLoop hBB0
        rw [Nat.zero_add] at hChk0
        unfold checkMoveHeadBlock at hChk0
        rw [hC0] at hChk0
        cases hBBTgt0 : Trusted.MirSemantics.getElem? bTgt.basicBlocks 0 with
        | none => rw [hBBTgt0] at hChk0; cases hChk0
        | some bbTgt =>
          rw [hBBTgt0] at hChk0; dsimp at hChk0
          let ⟨_, hRest0⟩ := bool_and_true hChk0
          cases hSt0 : stepMoveHeadCertStmts body.locals bbTgt.terminator env₀
              bbSrc.statements bbTgt.statements with
          | none => rw [hSt0] at hRest0; cases hRest0
          | some exitE =>
            rw [hSt0] at hRest0; dsimp at hRest0
            exact ⟨bbTgt, rfl, Or.inl ⟨env₀, exitE, hSt0, hRest0, hEnv0,
              deadMaskedEq_refl hEnv0.1⟩⟩
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
            rw [← hDefEq]; exact (listRel_getElem?_none_iff fSrc.defId hBodiesRel).mp hBSrc
          unfold StepOutcomeBisim evalStep; dsimp
          rw [hBSrc, hBTgtNone]
          exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
        | some bSrc =>
          let ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, hBBInv⟩ := hBInv bSrc hBSrc
          let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
          let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
          cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
          | none =>
            have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
              rw [← hDefEq]; exact hBTgt
            have hBBTgtNone : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
              rw [← hBlkEq]; exact (listRel_getElem?_none_iff fSrc.blockIdx hBBsRel).mp hBBSrc
            unfold StepOutcomeBisim evalStep; dsimp
            rw [hBSrc, hBTgt2]; dsimp; rw [hBBSrc, hBBTgtNone]
            exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
          | some bbSrc =>
            let ⟨bbTgt, hBBTgt, hMode⟩ := hBBInv bbSrc hBBSrc
            let ⟨bbTgt', hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBsRel hBBSrc
            rw [hBBTgt] at hBBTgt'; injection hBBTgt' with eBB; subst eBB
            let ⟨h12BB, hStmtsSynt⟩ := bool_and_true hBBRel
            let ⟨hCleanEqB, hTermEqB⟩ := bool_and_true h12BB
            have hCleanEq := bool_beq_eq hCleanEqB
            have hTermEq := terminatorEq_eq hTermEqB
            have hStmtsLenEq : bbSrc.statements.length = bbTgt.statements.length :=
              (stmtListStoragePreserved_props
                (isMoveHeadUnifyStmts_storage_aux bbSrc.statements.length
                  (Nat.le_refl _) hStmtsSynt)).1
            cases hMode with
            | inr hMidMode =>
              -- Mode 2 (`MidPair`): execute `(s₂, t₂)` and return to Mode 1 (`Aligned`)
              let ⟨outPlace, rvSrc, rvTgt, restSrc, restTgt, dst, src, dstTy, v,
                   env₁, env₂, exitEnv, hDropS, hDropT, hOutEmp, hDstNe0, hRvPair,
                   hDstDeadOrOut, hMidLocs, hEnv1S, hStep2Abs, hStepRest, hEdges⟩ := hMidMode
              let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
              let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
              have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                rw [← hDefEq]; exact hBTgt
              have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                rw [← hBlkEq]; exact hBBTgt
              have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx =
                  some (.assign outPlace rvTgt) := by
                rw [← hIdxEq]; exact hStTgt0
              unfold StepOutcomeBisim evalStep; dsimp
              rw [hBSrc, hBTgt2]; dsimp
              rw [hBBSrc, hBBTgt2]; dsimp
              rw [hStSrc, hStTgt2]; dsimp
              dsimp [evalStatement]
              rw [hOutEmp]; dsimp
              rw [← hLocEq]
              have hStep2Full := hStep2Abs
              dsimp [stepPlainStmtAbs] at hStep2Abs
              rw [hOutEmp] at hStep2Abs; dsimp at hStep2Abs
              cases hOutTy : Trusted.MirSemantics.getElem? bSrc.locals outPlace.localId with
              | none => rw [hOutTy] at hStep2Abs; cases hStep2Abs
              | some outTy =>
                dsimp
                have hNoTouchTgt : ∀ d,
                    (d ≠ 0 ∧ isDeadInBlockFrom d ((.assign outPlace rvTgt) :: restTgt) bbTgt.terminator = true) →
                    rvalueTouchesLocal d rvTgt = false := by
                  intro d ⟨_, hDd⟩
                  dsimp [isDeadInBlockFrom] at hDd
                  exact bool_not_true (bool_and_true hDd).1
                cases evalRvalue_moveHead_mid_bisim (outTy := outTy) hMidLocs hRvPair hNoTouchTgt with
                | inl hCase =>
                  let ⟨fk, hER1, hER2⟩ := hCase
                  rw [hER1, hER2]; exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
                | inr hCase =>
                  let ⟨resVal, la1, la2, hOR1, hOR2, hMaskAfterR⟩ := hCase
                  rw [hOR1, hOR2]; dsimp
                  cases writePlace_deadMasked_bisim (val := resVal) hMaskAfterR hOutTy with
                  | inl hCase =>
                    let ⟨fk, hEW1, hEW2⟩ := hCase
                    rw [hEW1, hEW2]; exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
                  | inr hCase =>
                    let ⟨l1', l2', hOW1, hOW2, hMaskAfterW⟩ := hCase
                    have hEvS2 : evalStatement bSrc fSrc cmS (.assign outPlace rvSrc) =
                        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                                callerMem := cmS } := by
                      dsimp [evalStatement]; rw [hOutEmp]; dsimp
                      rw [hOutTy]; dsimp; rw [hOR1]; dsimp; rw [hOW1]
                    let ⟨l1'', hEqS2, hEnv2S⟩ :=
                      stepPlainStmtAbs_sound hEnv1S hStep2Full hEvS2
                    injection hEqS2 with eFs _; injection eFs with eF _; injection eF with _ _ _ eL
                    subst eL
                    rw [hOW1, hOW2]
                    have hMaskNext : DeadMaskedEq bSrc.locals
                        (fun d => d ≠ 0 ∧ isDeadInBlockFrom d restTgt bbTgt.terminator = true)
                        l1' l2' := by
                      apply deadMaskedEq_mono ?_ hMaskAfterW
                      intro d ⟨hOr, hNeOut⟩
                      cases hOr with
                      | inl hDprev =>
                        let ⟨hdNe0, hdDead⟩ := hDprev
                        dsimp [isDeadInBlockFrom] at hdDead
                        let ⟨_, hdRest⟩ := bool_and_true hdDead
                        have hOutBeqFalse : Nat.beq outPlace.localId d = false :=
                          nat_beq_false_of_ne hNeOut.symm
                        rw [hOutEmp, hOutBeqFalse] at hdRest; dsimp at hdRest
                        exact ⟨hdNe0, hdRest⟩
                      | inr hEqDst =>
                        subst hEqDst
                        cases hDstDeadOrOut with
                        | inl hBeqOut =>
                          exact False.elim (hNeOut (nat_beq_eq hBeqOut).symm)
                        | inr hDeadRest => exact ⟨hDstNe0, hDeadRest⟩
                    refine Or.inl ⟨_, _, rfl, rfl,
                      { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' },
                      rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
                    intro bS2 hBS2
                    dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                    refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                    intro bbS2 hBBS2
                    dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                    refine ⟨bbTgt, hBBTgt, Or.inl ⟨env₂, exitEnv, ?_, hEdges, hEnv2S, ?_⟩⟩
                    · dsimp; rw [hDropSNext, hDropTNext]; exact hStepRest
                    · dsimp; rw [hDropTNext]; exact hMaskNext
            | inl hAligned =>
              let ⟨env, exitEnv, hStepStmts, hEdges, hEnvS, hMask⟩ := hAligned
              cases hDropS : bbSrc.statements.drop fSrc.stmtIdx with
              | nil =>
                rw [hDropS] at hStepStmts
                cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
                | cons _ _ => rw [hDropT] at hStepStmts; cases hStepStmts
                | nil =>
                  rw [hDropT] at hStepStmts hMask
                  dsimp [stepMoveHeadCertStmts] at hStepStmts
                  injection hStepStmts with eEnv; subst eEnv
                  have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                    rw [← hDefEq]; exact hBTgt
                  have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                    rw [← hBlkEq]; exact hBBTgt
                  cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
                  | some x =>
                    rw [drop_eq_cons_of_getElem? hStSrc] at hDropS; cases hDropS
                  | none =>
                    have hGeSrc : bbSrc.statements.length ≤ fSrc.stmtIdx := by
                      cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
                      | inr hge => exact hge
                      | inl hlt =>
                        let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
                        rw [hStSrc] at hx; cases hx
                    have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none :=
                      getElem?_none_of_ge (by rw [← hIdxEq, ← hStmtsLenEq]; exact hGeSrc)
                    unfold StepOutcomeBisim evalStep; dsimp
                    rw [hBSrc, hBTgt2]; dsimp
                    rw [hBBSrc, hBBTgt2]; dsimp
                    rw [hStSrc, hStTgt2]; dsimp
                    rw [← hIdxEq, ← hStmtsLenEq]
                    cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
                    | false => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
                    | true =>
                      dsimp
                      have hSwUntouched : ∀ discr targets,
                          bbTgt.terminator = .switchInt discr targets →
                          ∀ d, (d ≠ 0 ∧ isDeadInBlockFrom d [] bbTgt.terminator = true) →
                            operandTouchesLocal d discr = false := by
                        intro discr targets hTm d ⟨_, hDnil⟩
                        rw [hTm] at hDnil; cases hDnil
                      cases evalTerminator_deadMasked_bisim (cm := cmS)
                          hLocEq hCleanEq hTermEq hMask (fun _ h => h.1) hSwUntouched with
                      | inr hDoneOrFault => exact Or.inr hDoneOrFault
                      | inl hStepTerm =>
                        let ⟨tgt, l1', l2', hEvTS, hEvTT, hMaskAfterTerm⟩ := hStepTerm
                        -- Notice: since evalTerminator stepped, bbTgt.terminator is .goto or .switchInt,
                        -- so `isDeadInBlockFrom d [] bbTgt.terminator = false` for all d, hence l1' = l2'!
                        have hTermNotRetUnreach : bbTgt.terminator ≠ .return_ ∧ bbTgt.terminator ≠ .unreachable := by
                          constructor
                          · intro hRet
                            unfold evalTerminator at hEvTT
                            rw [hRet] at hEvTT; dsimp at hEvTT
                            cases hCl : bbTgt.cleanup with
                            | true => rw [hCl] at hEvTT; cases hEvTT
                            | false =>
                              rw [hCl] at hEvTT; dsimp at hEvTT
                              cases h0 : Trusted.MirSemantics.getElem? fTgt.locals 0 with
                              | none => rw [h0] at hEvTT; cases hEvTT
                              | some sl =>
                                rw [h0] at hEvTT
                                cases sl with | dead => cases hEvTT | live o => cases o <;> cases hEvTT
                          · intro hUn
                            unfold evalTerminator at hEvTT; rw [hUn] at hEvTT; cases hEvTT
                        have hLocsEqAfter : l1' = l2' := by
                          apply list_eq_of_getElem?_eq (hMaskAfterTerm.1.1.trans hMaskAfterTerm.2.1.1.symm)
                          intro i
                          apply (hMaskAfterTerm.2.2 i).2
                          intro ⟨_, hDnil⟩
                          cases isDeadInBlockFrom_nil_term hDnil with
                          | inl hR => exact hTermNotRetUnreach.1 hR
                          | inr hU => exact hTermNotRetUnreach.2 hU
                        subst hLocsEqAfter
                        let ⟨tgt', l1'', hEqS', _, hCertNext⟩ :=
                          checkAbsTerminatorEdges_step_sound hEnvS hEdges hEvTS
                        injection hEqS' with eFs _; injection eFs with eF _
                        injection eF with _ eTgt _ eL; subst eTgt; subst eL
                        rw [hEvTS, hEvTT]
                        refine Or.inl ⟨_, _, rfl, rfl,
                          { fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1' },
                          { fTgt with blockIdx := tgt, stmtIdx := 0, locals := l1' },
                          rfl, rfl, rfl, hDefEq, rfl, rfl, ?_⟩
                        intro bS2 hBS2
                        dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                        refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                        intro bbNext hBBNext
                        dsimp at hBBNext
                        let ⟨tgtEnv, hCNext, hTgtEnvS⟩ := hCertNext (getElem?_some_lt hBBNext)
                        let ⟨_, hLoop⟩ := bool_and_true hChkBody
                        have hChkNext := checkMoveHeadBlocksLoop_getElem? hLoop hBBNext
                        rw [Nat.zero_add] at hChkNext
                        unfold checkMoveHeadBlock at hChkNext
                        rw [hCNext] at hChkNext
                        cases hBBTgtNext : Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt with
                        | none => rw [hBBTgtNext] at hChkNext; cases hChkNext
                        | some bbNextTgt =>
                          rw [hBBTgtNext] at hChkNext; dsimp at hChkNext
                          let ⟨_, hRestNext⟩ := bool_and_true hChkNext
                          cases hStNext : stepMoveHeadCertStmts bSrc.locals bbNextTgt.terminator
                              tgtEnv bbNext.statements bbNextTgt.statements with
                          | none => rw [hStNext] at hRestNext; cases hRestNext
                          | some exitEN =>
                            rw [hStNext] at hRestNext; dsimp at hRestNext
                            exact ⟨bbNextTgt, rfl, Or.inl ⟨tgtEnv, exitEN, hStNext, hRestNext,
                              hTgtEnvS, deadMaskedEq_refl hTgtEnvS.1⟩⟩
              | cons s₁ tailSrc =>
                rw [hDropS] at hStepStmts
                cases tailSrc with
                | nil =>
                  cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
                  | nil => rw [hDropT] at hStepStmts; cases hStepStmts
                  | cons t₁ tailTgt =>
                    rw [hDropT] at hStepStmts hMask
                    cases tailTgt with
                    | cons _ _ => cases hStepStmts
                    | nil =>
                      dsimp [stepMoveHeadCertStmts] at hStepStmts
                      cases hEq1 : stmtEq s₁ t₁ with
                      | false => rw [hEq1] at hStepStmts; cases hStepStmts
                      | true =>
                        rw [hEq1] at hStepStmts; dsimp at hStepStmts
                        have hsEq := stmtEq_eq hEq1; subst hsEq
                        exact moveHead_kept_step_helper hBSrc hBTgt hBCert hBRel hChkBody
                          hBBSrc hBBTgt hDefEq hBlkEq hIdxEq hLocEq hDropS hDropT
                          hEnvS hMask hStepStmts rfl hEdges
                | cons s₂ restSrc =>
                  cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
                  | nil => rw [hDropT] at hStepStmts; cases hStepStmts
                  | cons t₁ tailTgt =>
                    rw [hDropT] at hStepStmts hMask
                    cases tailTgt with
                    | nil => cases hStepStmts
                    | cons t₂ restTgt =>
                      dsimp [stepMoveHeadCertStmts] at hStepStmts
                      cases hPair : isMoveHeadUnifyPair bSrc.locals s₁ s₂ t₁ t₂ restTgt bbTgt.terminator with
                      | false =>
                        rw [hPair] at hStepStmts; dsimp at hStepStmts
                        cases hNeq1 : (!stmtEq s₁ t₁) with
                        | true => rw [hNeq1] at hStepStmts; cases hStepStmts
                        | false =>
                          rw [hNeq1] at hStepStmts; dsimp at hStepStmts
                          have hsEq := stmtEq_eq (bool_not_false hNeq1); subst hsEq
                          cases hStep1 : stepPlainStmtAbs bSrc.locals env s₁ with
                          | none => rw [hStep1] at hStepStmts; cases hStepStmts
                          | some env₁ =>
                            rw [hStep1] at hStepStmts; dsimp at hStepStmts
                            exact moveHead_kept_step_helper hBSrc hBTgt hBCert hBRel hChkBody
                              hBBSrc hBBTgt hDefEq hBlkEq hIdxEq hLocEq hDropS hDropT
                              hEnvS hMask hStep1 hStepStmts hEdges
                      | true =>
                        -- Fused pair `(s₁, s₂)` vs `(.nop, t₂)` -> step to `MidPair`!
                        rw [hPair] at hStepStmts; dsimp at hStepStmts
                        cases s₁ with
                        | nop | storageLive _ | storageDead _ | unsupported => cases hPair
                        | assign dPlace rv1 =>
                          cases rv1 with
                          | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
                          | addressOf _ _ | aggregateTuple _ | unsupported => cases hPair
                          | use o1 =>
                            cases o1 with
                            | copy _ | constant _ => cases hPair
                            | move sPlace =>
                              cases s₂ with
                              | nop | storageLive _ | storageDead _ | unsupported => cases hPair
                              | assign out₁ rvSrc =>
                                cases t₁ with
                                | assign _ _ | storageLive _ | storageDead _ | unsupported => cases hPair
                                | nop =>
                                  cases t₂ with
                                  | nop | storageLive _ | storageDead _ | unsupported => cases hPair
                                  | assign out₂ rvTgt =>
                                    dsimp [isMoveHeadUnifyPair] at hPair
                                    let ⟨hLeft, hRight⟩ := bool_and_true hPair
                                    let ⟨hL123, hOutEqB⟩ := bool_and_true hLeft
                                    let ⟨hL12, hOutEmp⟩ := bool_and_true hL123
                                    let ⟨hDEmp, hSEmp⟩ := bool_and_true hL12
                                    let ⟨hR1, hDstDeadOrOutB⟩ := bool_and_true hRight
                                    let ⟨hR2, hRvPair⟩ := bool_and_true hR1
                                    let ⟨hR3, hTyMatch⟩ := bool_and_true hR2
                                    let ⟨hR4, hOutLtB⟩ := bool_and_true hR3
                                    let ⟨hDstNe0B, hDstNeSrcB⟩ := bool_and_true hR4
                                    let _ := hOutLtB
                                    have hOutEq := placeEq_eq hOutEqB; subst hOutEq
                                    have hDstNe0 := nat_ne_of_beq_false (bool_not_true hDstNe0B)
                                    have hDstNeSrc := nat_ne_of_beq_false (bool_not_true hDstNeSrcB)
                                    cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId with
                                    | none => rw [hDstTy] at hTyMatch; cases hTyMatch
                                    | some dstTy =>
                                      rw [hDstTy] at hTyMatch
                                      cases hSrcTy : Trusted.MirSemantics.getElem? bSrc.locals sPlace.localId with
                                      | none => rw [hSrcTy] at hTyMatch; cases hTyMatch
                                      | some srcTy =>
                                        rw [hSrcTy] at hTyMatch
                                        have hTyEq := mirTy_beq_eq hTyMatch; subst hTyEq
                                        dsimp at hStepStmts
                                        cases hEDst : Trusted.MirSemantics.getElem? env dPlace.localId with
                                        | none => rw [hEDst] at hStepStmts; cases hStepStmts
                                        | some dstSlot =>
                                          rw [hEDst] at hStepStmts
                                          cases hESrc : Trusted.MirSemantics.getElem? env sPlace.localId with
                                          | none => rw [hESrc] at hStepStmts; cases hStepStmts
                                          | some srcSlot =>
                                            rw [hESrc] at hStepStmts
                                            cases srcSlot with
                                            | dead | liveUninit => cases hStepStmts
                                            | liveInit =>
                                              dsimp at hStepStmts
                                              cases hImpNeg : (!absSlotImplies dstSlot .liveUninit) with
                                              | true => rw [hImpNeg] at hStepStmts; cases hStepStmts
                                              | false =>
                                                rw [hImpNeg] at hStepStmts; dsimp at hStepStmts
                                                have hDstImp := bool_not_false hImpNeg
                                                cases hStep1 : stepPlainStmtAbs bSrc.locals env
                                                    (.assign dPlace (.use (.move sPlace))) with
                                                | none => rw [hStep1] at hStepStmts; cases hStepStmts
                                                | some env₁ =>
                                                  rw [hStep1] at hStepStmts; dsimp at hStepStmts
                                                  cases hStep2 : stepPlainStmtAbs bSrc.locals env₁
                                                      (.assign out₁ rvSrc) with
                                                  | none => rw [hStep2] at hStepStmts; cases hStepStmts
                                                  | some env₂ =>
                                                    rw [hStep2] at hStepStmts; dsimp at hStepStmts
                                                    -- Evaluate s₁ in pSrc and .nop in pTgt!
                                                    have hLtSrc : sPlace.localId < bSrc.locals.length :=
                                                      getElem?_some_lt hSrcTy
                                                    have hLtDst : dPlace.localId < bSrc.locals.length :=
                                                      getElem?_some_lt hDstTy
                                                    let ⟨slSrc1, hG1S⟩ := getElem?_some_of_lt fSrc.locals sPlace.localId
                                                      (by rw [hEnvS.1.1]; exact hLtSrc)
                                                    have hSrcS := hEnvS.2.2 sPlace.localId dstTy .liveInit slSrc1
                                                      hSrcTy hESrc hG1S
                                                    let ⟨hChkSlS, v, hvSl⟩ := hSrcS
                                                    subst hvSl
                                                    have hChkV : checkVal v dstTy = true := hChkSlS
                                                    -- src cannot be in D_before because rvTgt touches src!
                                                    have hSrcNotD : ¬ (sPlace.localId ≠ 0 ∧
                                                        isDeadInBlockFrom sPlace.localId
                                                          (.nop :: (.assign out₁ rvTgt) :: restTgt) bbTgt.terminator = true) := by
                                                      intro ⟨_, hDeadS⟩
                                                      dsimp [isDeadInBlockFrom] at hDeadS
                                                      let ⟨hNoTS, _⟩ := bool_and_true hDeadS
                                                      rw [isMoveHeadRvaluePair_touches_src hRvPair] at hNoTS
                                                      cases hNoTS
                                                    have hG2S : Trusted.MirSemantics.getElem? fTgt.locals sPlace.localId =
                                                        some (.live (some v)) := by
                                                      rw [← (hMask.2.2 sPlace.localId).2 hSrcNotD]
                                                      exact hG1S
                                                    let ⟨slDst1, hG1D⟩ := getElem?_some_of_lt fSrc.locals dPlace.localId
                                                      (by rw [hEnvS.1.1]; exact hLtDst)
                                                    have hDstLive1 := absSlotImplies_sound hDstImp
                                                      (hEnvS.2.2 dPlace.localId dstTy dstSlot slDst1 hDstTy hEDst hG1D)
                                                    let ⟨_, optD1, hSlDst1⟩ := hDstLive1
                                                    subst hSlDst1
                                                    let ⟨slDst2, hG2D⟩ := getElem?_some_of_lt fTgt.locals dPlace.localId
                                                      (by rw [hMask.2.1.1]; exact hLtDst)
                                                    have hSameLiveD := (hMask.2.2 dPlace.localId).1 _ _ hG1D hG2D
                                                    cases slDst2 with
                                                    | dead => cases hSameLiveD
                                                    | live optD2 =>
                                                      let ⟨lMove, hSetMove⟩ := setElem?_some_of_lt fSrc.locals
                                                        sPlace.localId (liveUninitSlot dstTy)
                                                        (by rw [hEnvS.1.1]; exact hLtSrc)
                                                      have hMoveDst : Trusted.MirSemantics.getElem? lMove dPlace.localId =
                                                          some (.live optD1) := by
                                                        rw [setElem?_getElem?_ne hSetMove hDstNeSrc]; exact hG1D
                                                      let ⟨l1', hSetDst⟩ := setElem?_some_of_lt lMove
                                                        dPlace.localId (.live (some v))
                                                        (by rw [setElem?_length hSetMove, hEnvS.1.1]; exact hLtDst)
                                                      have hEvS1 : evalStatement bSrc fSrc cmS
                                                          (.assign dPlace (.use (.move sPlace))) =
                                                          .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                                                                  callerMem := cmS } := by
                                                        dsimp [evalStatement]
                                                        rw [hDEmp]; dsimp; rw [hDstTy]; dsimp
                                                        dsimp [evalRvalue, evalOperandToSlot]
                                                        rw [hSEmp]; dsimp; rw [hSrcTy, hG1S]; dsimp
                                                        rw [hSetMove]; dsimp
                                                        rw [mirTy_beq_refl dstTy]; dsimp
                                                        dsimp [writePlace]; rw [hChkV]; dsimp
                                                        rw [hMoveDst]; dsimp; rw [hSetDst]
                                                      let ⟨l1'', hEqS1, hEnv1S⟩ := stepPlainStmtAbs_sound hEnvS hStep1 hEvS1
                                                      injection hEqS1 with eFs _; injection eFs with eF _
                                                      injection eF with _ _ _ eL; subst eL
                                                      let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
                                                      let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
                                                      have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                                                        rw [← hDefEq]; exact hBTgt
                                                      have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                                                        rw [← hBlkEq]; exact hBBTgt
                                                      have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some .nop := by
                                                        rw [← hIdxEq]; exact hStTgt0
                                                      unfold StepOutcomeBisim evalStep; dsimp
                                                      rw [hBSrc, hBTgt2]; dsimp
                                                      rw [hBBSrc, hBBTgt2]; dsimp
                                                      rw [hStSrc, hStTgt2]; dsimp
                                                      rw [hEvS1]
                                                      -- Construct MoveHeadMidLocals on (l1', fTgt.locals):
                                                      have hMidNext : MoveHeadMidLocals bSrc.locals
                                                          (fun d => d ≠ 0 ∧
                                                            isDeadInBlockFrom d ((.assign out₁ rvTgt) :: restTgt) bbTgt.terminator = true)
                                                          dPlace.localId sPlace.localId dstTy v l1' fTgt.locals := by
                                                        refine ⟨hDstNeSrc, hDstTy, hSrcTy, hChkV,
                                                          by rw [setElem?_getElem?_ne hSetDst hDstNeSrc.symm,
                                                                 setElem?_getElem?_same hSetMove],
                                                          hG2S,
                                                          setElem?_getElem?_same hSetDst,
                                                          ⟨optD2, hG2D⟩, ?_⟩
                                                        let ⟨optU, hOptU⟩ := liveUninitSlot_isLive dstTy
                                                        have hM1 : DeadMaskedEq bSrc.locals
                                                            (fun d => (d ≠ 0 ∧ isDeadInBlockFrom d ((.assign out₁ rvTgt) :: restTgt) bbTgt.terminator = true) ∨ d = sPlace.localId)
                                                            lMove fTgt.locals := by
                                                          have hSetMoveOpt : setElem? fSrc.locals sPlace.localId (.live optU) = some lMove := by
                                                            rw [← hOptU]; exact hSetMove
                                                          have hWtU : SlotWellTyped dstTy (.live optU) := by
                                                            rw [← hOptU]; exact liveUninitSlot_wellTyped dstTy
                                                          exact deadMaskedEq_set_left_live hMask hSrcTy hG2S hSetMoveOpt hWtU
                                                        have hM2 := deadMaskedEq_set_left_live hM1 hDstTy hG2D hSetDst hChkV
                                                        apply deadMaskedEq_mono ?_ hM2
                                                        intro d hOr
                                                        cases hOr with
                                                        | inr hEqD => exact Or.inr (Or.inl hEqD)
                                                        | inl hOr2 =>
                                                          cases hOr2 with
                                                          | inl hDr => exact Or.inl hDr
                                                          | inr hEqS => exact Or.inr (Or.inr hEqS)
                                                      refine Or.inl ⟨_, _, rfl, rfl,
                                                        { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                                                        { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals },
                                                        rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
                                                      intro bS2 hBS2
                                                      dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                                                      refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                                                      intro bbS2 hBBS2
                                                      dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                                                      refine ⟨bbTgt, hBBTgt, Or.inr
                                                        ⟨out₁, rvSrc, rvTgt, restSrc, restTgt,
                                                         dPlace.localId, sPlace.localId, dstTy, v,
                                                         env₁, env₂, exitEnv,
                                                         by dsimp; exact hDropSNext,
                                                         by dsimp; exact hDropTNext,
                                                         hOutEmp, hDstNe0, hRvPair,
                                                         bool_or_true hDstDeadOrOutB,
                                                         hMidNext, hEnv1S, hStep2, hStepStmts, hEdges⟩⟩

private theorem moveHeadUnify_certified_bidirectional_iff_priv
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isMoveHeadUnifyProgram pSrc pTgt = true)
    (hCert : checkMoveHeadUnifyProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
    let ⟨hBHdr, _, hEmpty, _, hBounds, _⟩ := isMoveHeadUnifyBody_storage hBRel
    exact ⟨hBHdr, hEmpty, hBounds⟩
  · exact moveHead_query_iff hRel hCert
  · intro defId args
    have hRelEntry : isMoveHeadUnifyProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies
    exact (moveHead_query_iff hRelEntry hCert { args := args }).1

/-! ### Stage 4 Private Helpers — Layer D: `DeadStoreElimination` (Theorems
2a & 2b) -/

/-! #### Shared DSE Storage, Move-Free Locality, & Theorem 2a
(`codegen_dse_moveFree_refines_unconditional`) -/

private theorem isDseMoveFreeStmts_storage {bodyLocals : List MirTy}
    {termTgt : TerminatorKind} :
    ∀ {ss₁ ss₂},
      isDseMoveFreeStmts bodyLocals termTgt ss₁ ss₂ = true →
      StmtListStoragePreserved ss₁ ss₂ := by
  intro ss₁
  induction ss₁ with
  | nil =>
    intro ss₂ h
    cases ss₂ with
    | nil => exact True.intro
    | cons _ _ => cases h
  | cons s₁ r₁ ih =>
    intro ss₂ h
    cases ss₂ with
    | nil => cases h
    | cons s₂ r₂ =>
      dsimp [isDseMoveFreeStmts] at h
      let ⟨hHead, hTail⟩ := bool_and_true h
      refine ⟨?_, ih hTail⟩
      cases bool_or_true hHead with
      | inr hEq => exact Or.inl (stmtEq_eq hEq)
      | inl hElim =>
        cases s₁ with
        | nop | storageLive _ | storageDead _ | unsupported => cases hElim
        | assign _ _ =>
          cases s₂ with
          | assign _ _ | storageLive _ | storageDead _ | unsupported => cases hElim
          | nop => exact Or.inr ⟨True.intro, True.intro⟩

private theorem isDseMoveFreeBody_storage {bSrc bTgt : Body}
    (hBody : isDseMoveFreeBody bSrc bTgt = true) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    (∀ idx, hasStorageAnnotation bSrc idx = hasStorageAnnotation bTgt idx) ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨hBHdr, hBBs⟩ := bool_and_true hBody
  apply bodyStorage_eq_of_blocks hBHdr hBBs
  intro bb₁ bb₂ hBB
  let ⟨_, hStmts⟩ := bool_and_true hBB
  exact isDseMoveFreeStmts_storage hStmts

private theorem dse_initState_eq {pSrc pTgt : Program}
    (hRel : isDseMoveFreeProgram pSrc pTgt = true) (q : Query) :
    initState pSrc q = initState pTgt q := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodies
  · intro b₁ hB₁
    let ⟨b₂, hB₂, hBRel⟩ := listRel_getElem?_left hBodies hB₁
    rw [hEnt] at hB₂
    let ⟨hBHdr, _, hEmpty, _, hBounds, hLoop⟩ := isDseMoveFreeBody_storage hBRel
    exact ⟨b₂, hB₂, hBHdr, hEmpty, hBounds, hLoop q.args⟩

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

private theorem dse_elim_step_effect {bSrc bTgt : Body}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    {sSrc sTgt : StatementKind} {restTgt : List StatementKind}
    {termTgt : TerminatorKind} {s' : State}
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧ isDeadInBlockFrom d (sTgt :: restTgt) termTgt = true)
      fSrc.locals fTgt.locals)
    (hElim : isDseMoveFreeElim bSrc.locals sSrc sTgt restTgt termTgt = true)
    (hEvS : evalStatement bSrc fSrc cm sSrc = .step s') :
    ∃ locs₁',
      s' = { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs₁' }],
             callerMem := cm } ∧
      evalStatement bTgt fTgt cm sTgt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals }],
                callerMem := cm } ∧
      DeadMaskedEq bSrc.locals
        (fun d => d ≠ 0 ∧ isDeadInBlockFrom d restTgt termTgt = true)
        locs₁' fTgt.locals := by
  cases sSrc with
  | nop | storageLive _ | storageDead _ | unsupported => cases hElim
  | assign dstPlace rval =>
    cases sTgt with
    | assign _ _ | storageLive _ | storageDead _ | unsupported => cases hElim
    | nop =>
      dsimp [isDseMoveFreeElim] at hElim
      let ⟨h1234, hDeadDst⟩ := bool_and_true hElim
      let ⟨h123, hNoMove⟩ := bool_and_true h1234
      let ⟨h12, _⟩ := bool_and_true h123
      let ⟨hDstEmp, hDstNe0B⟩ := bool_and_true h12
      have hDstNe0 := nat_ne_of_beq_false (bool_not_true hDstNe0B)
      dsimp [evalStatement] at hEvS
      rw [hDstEmp] at hEvS; dsimp at hEvS
      cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dstPlace.localId with
      | none => rw [hDstTy] at hEvS; cases hEvS
      | some dstTy =>
        rw [hDstTy] at hEvS; dsimp at hEvS
        cases hEvR : evalRvalue bSrc.locals fSrc.locals dstTy rval with
        | error _ => rw [hEvR] at hEvS; cases hEvS
        | ok resR =>
          let ⟨val, locsAfterR⟩ := resR
          rw [hEvR] at hEvS; dsimp at hEvS
          let ⟨hOtherEq, _, hBackLive⟩ := evalRvalue_noMoveExcept hNoMove hEvR
          have hWtAfterR := evalRvalue_preserves_wt hMask.1 hEvR
          dsimp [writePlace] at hEvS
          cases hChk : checkVal val dstTy with
          | false => rw [hChk] at hEvS; cases hEvS
          | true =>
            rw [hChk] at hEvS; dsimp at hEvS
            cases hSlAfter : Trusted.MirSemantics.getElem? locsAfterR dstPlace.localId with
            | none => rw [hSlAfter] at hEvS; cases hEvS
            | some slA =>
              rw [hSlAfter] at hEvS
              cases slA with
              | dead => cases hEvS
              | live optA =>
                cases hSetW : setElem? locsAfterR dstPlace.localId (.live (some val)) with
                | none => rw [hSetW] at hEvS; cases hEvS
                | some locsW =>
                  rw [hSetW] at hEvS
                  injection hEvS with hSEq; subst hSEq
                  have hWtW := localsWellTyped_set hWtAfterR hDstTy hSetW hChk
                  let ⟨optOrig1, hG1Orig⟩ := hBackLive optA hSlAfter
                  have hLtDst : dstPlace.localId < bSrc.locals.length := getElem?_some_lt hDstTy
                  let ⟨sl2Dst, hG2Dst⟩ := getElem?_some_of_lt fTgt.locals dstPlace.localId
                    (by rw [hMask.2.1.1]; exact hLtDst)
                  have hSameLiveDst := (hMask.2.2 dstPlace.localId).1 _ _ hG1Orig hG2Dst
                  cases sl2Dst with
                  | dead => cases hSameLiveDst
                  | live opt2Dst =>
                    refine ⟨locsW, rfl, rfl, ⟨hWtW, hMask.2.1, fun i => ?_⟩⟩
                    cases hEqI : Nat.beq i dstPlace.localId with
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

private noncomputable def DseFwdRel (pSrc pTgt : Program) (s t : State) : Prop :=
  ∃ fSrc fTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    ∀ bSrc,
      Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
      ∃ bTgt,
        Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
        isDseMoveFreeBody bSrc bTgt = true ∧
        ∀ bbSrc,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
          ∃ bbTgt,
            Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt ∧
            isDseMoveFreeStmts bSrc.locals bbTgt.terminator
              (bbSrc.statements.drop fSrc.stmtIdx)
              (bbTgt.statements.drop fSrc.stmtIdx) = true ∧
            DeadMaskedEq bSrc.locals
              (fun d => d ≠ 0 ∧
                isDeadInBlockFrom d (bbTgt.statements.drop fSrc.stmtIdx) bbTgt.terminator = true)
              fSrc.locals fTgt.locals

private theorem dse_uncond_query_fwd {pSrc pTgt : Program}
    (hRel : isDseMoveFreeProgram pSrc pTgt = true)
    (q : Query) (hWfSrc : WellFormed pSrc q) :
    WellFormed pTgt q ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  apply fwd_sim_lift (R := DseFwdRel pSrc pTgt) ?_ ?_ hWfSrc
  · intro s₀ hInitS
    have hInitT : initState pTgt q = .ok s₀ := by
      rw [← dse_initState_eq hRel q]; exact hInitS
    let ⟨_, _, body, hBody, _, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hInitS
    subst hEqS
    have hWt0 := initLocalsLoop_wellTyped hArgs
    refine ⟨_, hInitT, _, _, rfl, rfl, rfl, rfl, rfl, rfl, fun bSrc hBS => ?_⟩
    rw [hBody] at hBS; injection hBS with eB; subst eB
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodiesRel hBody
    refine ⟨bTgt, hBTgt, hBRel, ?_⟩
    intro bbSrc hBB0
    dsimp at hBB0
    let ⟨_, hBBsRel⟩ := bool_and_true hBRel
    let ⟨bbTgt, hBBTgt0, hBBRel⟩ := listRel_getElem?_left hBBsRel hBB0
    let ⟨_, hStmts0⟩ := bool_and_true hBBRel
    exact ⟨bbTgt, hBBTgt0, hStmts0, deadMaskedEq_refl hWt0⟩
  · intro s t hR
    let ⟨fSrc, fTgt, hFS, hFT, hCM, hDefEq, hBlkEq, hIdxEq, hBInv⟩ := hR
    cases s with
    | mk fsS cmS =>
      cases t with
      | mk fsT cmT =>
        dsimp at hFS hFT hCM; subst hFS; subst hFT; subst hCM
        refine ⟨?_, ?_⟩
        · intro s' hEvS
          unfold evalStep at hEvS; dsimp at hEvS
          cases hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId with
          | none => rw [hBSrc] at hEvS; cases hEvS
          | some bSrc =>
            rw [hBSrc] at hEvS; dsimp at hEvS
            let ⟨bTgt, hBTgt, hBRel, hBBInv⟩ := hBInv bSrc hBSrc
            let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
            let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
            cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
            | none => rw [hBBSrc] at hEvS; cases hEvS
            | some bbSrc =>
              rw [hBBSrc] at hEvS; dsimp at hEvS
              let ⟨bbTgt, hBBTgt, hStmtsRel, hMask⟩ := hBBInv bbSrc hBBSrc
              let ⟨bbTgt', hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBsRel hBBSrc
              rw [hBBTgt] at hBBTgt'; injection hBBTgt' with eBB; subst eBB
              let ⟨h12BB, hFullStmts⟩ := bool_and_true hBBRel
              let ⟨hCleanEqB, hTermEqB⟩ := bool_and_true h12BB
              have hCleanEq := bool_beq_eq hCleanEqB
              have hTermEq := terminatorEq_eq hTermEqB
              have hStmtsLenEq :=
                (stmtListStoragePreserved_props (isDseMoveFreeStmts_storage hFullStmts)).1
              have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                rw [← hDefEq]; exact hBTgt
              have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                rw [← hBlkEq]; exact hBBTgt
              cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
              | some sSrc =>
                rw [hStSrc] at hEvS; dsimp at hEvS
                have hDropS := drop_eq_cons_of_getElem? hStSrc
                rw [hDropS] at hStmtsRel
                cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
                | nil => rw [hDropT] at hStmtsRel; cases hStmtsRel
                | cons sTgt restTgt =>
                  rw [hDropT] at hStmtsRel hMask
                  let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
                  have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some sTgt := by
                    rw [← hIdxEq]; exact hStTgt0
                  dsimp [isDseMoveFreeStmts] at hStmtsRel
                  let ⟨hHeadRel, hTailRel⟩ := bool_and_true hStmtsRel
                  cases bool_or_true hHeadRel with
                  | inl hElim =>
                    let ⟨l1', hEqS', hEvT, hMaskNext⟩ :=
                      dse_elim_step_effect (bTgt := bTgt) (fTgt := fTgt) hMask hElim hEvS
                    subst hEqS'
                    refine ⟨{ frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals }],
                              callerMem := cmS }, ?_,
                      { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals },
                      rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
                    · unfold evalStep; dsimp
                      rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp; rw [hStTgt2]; dsimp
                      exact hEvT
                    · intro bS2 hBS2
                      dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                      refine ⟨bTgt, hBTgt, hBRel, ?_⟩
                      intro bbS2 hBBS2
                      dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                      refine ⟨bbTgt, hBBTgt, ?_, ?_⟩
                      · dsimp; rw [hDropTNext]; exact hTailRel
                      · dsimp; rw [hDropTNext]; exact hMaskNext
                  | inr hEqSt =>
                    have hsEq := stmtEq_eq hEqSt; subst hsEq
                    cases isDeadInBlockFrom_kept_step (fTgt := fTgt) (cm := cmS) hLocEq hMask with
                    | inl hC =>
                      let ⟨_, hF1, _⟩ := hC; rw [hF1] at hEvS; cases hEvS
                    | inr hC =>
                      let ⟨l1', l2', hS1, hS2, hMaskNext⟩ := hC
                      rw [hS1] at hEvS; injection hEvS with eS; subst eS
                      refine ⟨{ frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                                callerMem := cmS }, ?_,
                        { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                        { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' },
                        rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
                      · unfold evalStep; dsimp
                        rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp; rw [hStTgt2]; dsimp
                        exact hS2
                      · intro bS2 hBS2
                        dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                        refine ⟨bTgt, hBTgt, hBRel, ?_⟩
                        intro bbS2 hBBS2
                        dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                        refine ⟨bbTgt, hBBTgt, ?_, ?_⟩
                        · dsimp; rw [hDropTNext]; exact hTailRel
                        · dsimp; rw [hDropTNext]; exact hMaskNext
              | none =>
                rw [hStSrc] at hEvS; dsimp at hEvS
                have hGeSrc : bbSrc.statements.length ≤ fSrc.stmtIdx := by
                  cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
                  | inr hge => exact hge
                  | inl hlt =>
                    let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
                    rw [hStSrc] at hx; cases hx
                have hDropSNil := drop_eq_nil_of_ge hGeSrc
                have hDropTNil : bbTgt.statements.drop fSrc.stmtIdx = [] :=
                  drop_eq_nil_of_ge (by rw [← hStmtsLenEq]; exact hGeSrc)
                rw [hDropTNil] at hMask
                cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
                | false => rw [hEnd] at hEvS; cases hEvS
                | true =>
                  rw [hEnd] at hEvS; dsimp at hEvS
                  have hSwUntouched : ∀ discr targets,
                      bbTgt.terminator = .switchInt discr targets →
                      ∀ d, (d ≠ 0 ∧ isDeadInBlockFrom d [] bbTgt.terminator = true) →
                        operandTouchesLocal d discr = false := by
                    intro discr targets hTm d ⟨_, hDnil⟩
                    rw [hTm] at hDnil; cases hDnil
                  cases evalTerminator_deadMasked_bisim (fTgt := fTgt) (cm := cmS)
                      hLocEq hCleanEq hTermEq hMask (fun _ h => h.1) hSwUntouched with
                  | inr hDF =>
                    cases hDF with
                    | inl hD => let ⟨_, hDS, _⟩ := hD; rw [hDS] at hEvS; cases hEvS
                    | inr hF => let ⟨_, hFS', _⟩ := hF; rw [hFS'] at hEvS; cases hEvS
                  | inl hST =>
                    let ⟨tgt, l1', l2', hTS, hTT, hMaskAfter⟩ := hST
                    rw [hTS] at hEvS; injection hEvS with eS; subst eS
                    have hTermNotRetUnreach : bbTgt.terminator ≠ .return_ ∧ bbTgt.terminator ≠ .unreachable := by
                      constructor
                      · intro hRet
                        unfold evalTerminator at hTT; rw [hRet] at hTT; dsimp at hTT
                        cases hCl : bbTgt.cleanup with
                        | true => rw [hCl] at hTT; cases hTT
                        | false =>
                          rw [hCl] at hTT; dsimp at hTT
                          cases h0 : Trusted.MirSemantics.getElem? fTgt.locals 0 with
                          | none => rw [h0] at hTT; cases hTT
                          | some sl => rw [h0] at hTT; cases sl with | dead => cases hTT | live o => cases o <;> cases hTT
                      · intro hUn
                        unfold evalTerminator at hTT; rw [hUn] at hTT; cases hTT
                    have hLocsEq : l1' = l2' := by
                      apply list_eq_of_getElem?_eq (hMaskAfter.1.1.trans hMaskAfter.2.1.1.symm)
                      intro i
                      apply (hMaskAfter.2.2 i).2
                      intro ⟨_, hDnil⟩
                      cases isDeadInBlockFrom_nil_term hDnil with
                      | inl hR => exact hTermNotRetUnreach.1 hR
                      | inr hU => exact hTermNotRetUnreach.2 hU
                    subst hLocsEq
                    have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none :=
                      getElem?_none_of_ge (by rw [← hIdxEq, ← hStmtsLenEq]; exact hGeSrc)
                    have hEnd2 : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
                      rw [← hIdxEq, ← hStmtsLenEq]; exact hEnd
                    refine ⟨{ frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l1' }],
                              callerMem := cmS }, ?_,
                      { fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1' },
                      { fTgt with blockIdx := tgt, stmtIdx := 0, locals := l1' },
                      rfl, rfl, rfl, hDefEq, rfl, rfl, ?_⟩
                    · unfold evalStep; dsimp
                      rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp; rw [hStTgt2]; dsimp
                      rw [hEnd2]; dsimp; exact hTT
                    · intro bS2 hBS2
                      dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                      refine ⟨bTgt, hBTgt, hBRel, ?_⟩
                      intro bbNext hBBNext
                      dsimp at hBBNext
                      let ⟨bbNextTgt, hBBNextTgt, hBBNextRel⟩ := listRel_getElem?_left hBBsRel hBBNext
                      let ⟨_, hNextStmts⟩ := bool_and_true hBBNextRel
                      exact ⟨bbNextTgt, hBBNextTgt, hNextStmts, deadMaskedEq_refl hMaskAfter.1⟩
        · intro out hDoneS
          unfold evalStep at hDoneS; dsimp at hDoneS
          cases hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId with
          | none => rw [hBSrc] at hDoneS; cases hDoneS
          | some bSrc =>
            rw [hBSrc] at hDoneS; dsimp at hDoneS
            let ⟨bTgt, hBTgt, hBRel, hBBInv⟩ := hBInv bSrc hBSrc
            let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
            let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
            cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
            | none => rw [hBBSrc] at hDoneS; cases hDoneS
            | some bbSrc =>
              rw [hBBSrc] at hDoneS; dsimp at hDoneS
              let ⟨bbTgt, hBBTgt, _, hMask⟩ := hBBInv bbSrc hBBSrc
              let ⟨bbTgt', hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBsRel hBBSrc
              rw [hBBTgt] at hBBTgt'; injection hBBTgt' with eBB; subst eBB
              let ⟨h12BB, hFullStmts⟩ := bool_and_true hBBRel
              let ⟨hCleanEqB, hTermEqB⟩ := bool_and_true h12BB
              have hStmtsLenEq :=
                (stmtListStoragePreserved_props (isDseMoveFreeStmts_storage hFullStmts)).1
              cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
              | some sSrc =>
                rw [hStSrc] at hDoneS; dsimp at hDoneS
                exact False.elim (evalStatement_never_done bSrc fSrc cmS sSrc out hDoneS)
              | none =>
                rw [hStSrc] at hDoneS; dsimp at hDoneS
                have hGeSrc : bbSrc.statements.length ≤ fSrc.stmtIdx := by
                  cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
                  | inr hge => exact hge
                  | inl hlt =>
                    let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
                    rw [hStSrc] at hx; cases hx
                have hDropTNil : bbTgt.statements.drop fSrc.stmtIdx = [] :=
                  drop_eq_nil_of_ge (by rw [← hStmtsLenEq]; exact hGeSrc)
                rw [hDropTNil] at hMask
                cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
                | false => rw [hEnd] at hDoneS; cases hDoneS
                | true =>
                  rw [hEnd] at hDoneS; dsimp at hDoneS
                  have hSwUntouched : ∀ discr targets,
                      bbTgt.terminator = .switchInt discr targets →
                      ∀ d, (d ≠ 0 ∧ isDeadInBlockFrom d [] bbTgt.terminator = true) →
                        operandTouchesLocal d discr = false := by
                    intro discr targets hTm d ⟨_, hDnil⟩
                    rw [hTm] at hDnil; cases hDnil
                  cases evalTerminator_deadMasked_bisim (fTgt := fTgt) (cm := cmS)
                      hLocEq (bool_beq_eq hCleanEqB) (terminatorEq_eq hTermEqB)
                      hMask (fun _ h => h.1) hSwUntouched with
                  | inl hST =>
                    let ⟨_, _, _, hTS, _, _⟩ := hST; rw [hTS] at hDoneS; cases hDoneS
                  | inr hDF =>
                    cases hDF with
                    | inr hF =>
                      let ⟨_, hFS', _⟩ := hF; rw [hFS'] at hDoneS; cases hDoneS
                    | inl hD =>
                      let ⟨out', hDS, hDT⟩ := hD
                      rw [hDS] at hDoneS; injection hDoneS with eO; subst eO
                      unfold evalStep; dsimp
                      rw [← hDefEq, hBTgt]; dsimp
                      rw [← hBlkEq, hBBTgt]; dsimp
                      have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none :=
                        getElem?_none_of_ge (by rw [← hIdxEq, ← hStmtsLenEq]; exact hGeSrc)
                      rw [hStTgt2]; dsimp
                      rw [← hIdxEq, ← hStmtsLenEq, hEnd]; dsimp
                      exact hDT

private theorem codegen_dse_moveFree_refines_unconditional_priv
    (pSrc pTgt : Program)
    (hRel : isDseMoveFreeProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  apply forwardCodegenRefines_of_query_fwd hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
    let ⟨hBHdr, _, hEmpty, _, hBounds, _⟩ := isDseMoveFreeBody_storage hBRel
    exact ⟨hBHdr, hEmpty, hBounds⟩
  · exact dse_uncond_query_fwd hRel
  · intro defId args hWf
    have hRelEntry : isDseMoveFreeProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies
    exact (dse_uncond_query_fwd hRelEntry { args := args } hWf).1


/-! #### Two's-Complement `truncateScalar` & `decodeScalar` Helpers for
Certified DSE -/

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

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
      rw [← hPos127] at hGeI
      rw [int_subNatNat_of_lt hLt] at hGeI
      nomatch hGeI
    rw [decide_eq_false hNotNeg, decide_eq_false hNotGe]
    rfl
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
        rw [hDiff, hHalfPow] at hAdd
        exact hAdd
      have hLeAdd : Nat.pow 2 127 + (k + 1) ≤ Nat.pow 2 127 + Nat.pow 2 127 := by
        rw [← hSum]
        exact Nat.add_le_add_right hGe (k + 1)
      exact Nat.le_of_add_le_add_left hLeAdd
    have hNotGe : ¬ (Int.negSucc k ≥ Int.ofNat (Nat.pow 2 127)) := by
      intro hGeI
      have hPos127 : Nat.pow 2 127 = Nat.succ (Nat.pow 2 127 - 1) := by decide
      rw [hPos127] at hGeI
      nomatch hGeI
    have hNotLt : ¬ (Int.negSucc k < Int.negSucc (Nat.pow 2 127 - 1)) := by
      intro hLtI
      cases hK : k with
      | zero =>
        rw [hK] at hLtI
        have hZ : Int.negSucc 0 + 1 = Int.ofNat 0 := by decide
        change Int.NonNeg (Int.negSucc (Nat.pow 2 127 - 1) - (Int.negSucc 0 + 1)) at hLtI
        rw [hZ] at hLtI
        nomatch hLtI
      | succ k' =>
        rw [hK] at hLtI hKLt
        have hSucc127 : Nat.succ (Nat.pow 2 127 - 1) = Nat.pow 2 127 := by decide
        change Int.NonNeg (Int.subNatNat (Nat.succ k') (Nat.succ (Nat.pow 2 127 - 1))) at hLtI
        rw [hSucc127, int_subNatNat_of_lt hKLt] at hLtI
        nomatch hLtI
    rw [decide_eq_false hNotLt, decide_eq_false hNotGe]
    rfl

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
      rw [hDiff] at hAdd
      exact hAdd
    have hKLt : k < Nat.pow 2 128 := by
      have h1 : k + 1 ≤ Nat.pow 2 128 := by
        rw [← hSum]
        exact Nat.le_add_left (k + 1) x.toNat
      exact Nat.lt_of_succ_le h1
    have hKSuccLe : k + 1 ≤ Nat.pow 2 128 := hKLt
    change (BitVec.ofNat 128 (intEmod (Int.negSucc k) (Int.ofNat (Nat.pow 2 128))).toNat).toNat = x.toNat
    rw [intEmod_negSucc, nat_mod_eq_of_lt hKLt, int_subNatNat_of_le hKSuccLe]
    have hSubK : Nat.pow 2 128 - (k + 1) = x.toNat := by
      rw [← hSum]
      exact Nat.add_sub_cancel x.toNat (k + 1)
    rw [hSubK]
    change Nat.mod x.toNat (Nat.pow 2 128) = x.toNat
    exact nat_mod_eq_of_lt hXlt

private theorem bvToInt_bvOfInt_128_ofNat {k : Nat} (hLt : k < Nat.pow 2 127) :
    bvToInt (bvOfInt 128 (Int.ofNat k)) = Int.ofNat k := by
  have hLt128 : k < Nat.pow 2 128 :=
    Nat.lt_trans hLt (by decide : Nat.pow 2 127 < Nat.pow 2 128)
  have hToNat : (bvOfInt 128 (Int.ofNat k)).toNat = k := by
    unfold bvOfInt
    rw [intEmod_ofNat]
    change Nat.mod (Nat.mod k (Nat.pow 2 128)) (Nat.pow 2 128) = k
    rw [nat_mod_eq_of_lt hLt128, nat_mod_eq_of_lt hLt128]
  unfold bvToInt
  rw [hToNat]
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
  unfold bvToInt
  rw [hToNat]
  have hGe127 : Nat.pow 2 127 ≤ Nat.pow 2 128 - (k + 1) := by
    have hHalf : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
    have hAddLe : Nat.pow 2 127 + (k + 1) ≤ Nat.pow 2 128 := by
      rw [hHalf]
      exact Nat.add_le_add_left hSuccLe127 (Nat.pow 2 127)
    have hSub := Nat.sub_le_sub_right hAddLe (k + 1)
    rw [Nat.add_sub_cancel] at hSub
    exact hSub
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
      rw [← nat_sub_pos_eq_succ hSubLt128]
      exact h1
    exact Nat.succ.inj h2
  rw [hCancel]

private theorem truncateScalar_ok (w : IntWidth) (s : Bool) (value : Int) :
    ∃ lossy : Bool,
      truncateScalar w s value =
        .ok (⟨w, s, truncateBits w (bvOfInt 128 value)⟩, lossy) ∧
      checkVal (.scalar ⟨w, s, truncateBits w (bvOfInt 128 value)⟩) (.int w s) = true := by
  have hChk : checkVal (.scalar ⟨w, s, truncateBits w (bvOfInt 128 value)⟩) (.int w s) = true :=
    checkVal_int_iff.mpr ⟨_, rfl, truncateBits_idem w (bvOfInt 128 value)⟩
  unfold truncateScalar
  cases s with
  | false => exact ⟨_, rfl, hChk⟩
  | true =>
    dsimp only
    rw [bvToInt_in_i128_range (bvOfInt 128 value)]
    rw [if_bool_false rfl]
    rw [bvOfInt_bvToInt_128 (bvOfInt 128 value)]
    exact ⟨_, rfl, hChk⟩

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
      apply nat_lt_of_two_mul_lt
      rw [← hPow]; exact hCmp
    exact bvToInt_bvOfInt_128_ofNat (Nat.lt_of_lt_of_le hLtH hHLe127)
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
    have hGeH : H ≤ low.toNat := by
      apply nat_le_of_two_mul_le
      rw [← hPow]; exact hCmp
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
        rw [hDiff, hPow, nat_two_mul H] at hAdd
        exact hAdd
      have hLeAdd : H + (k + 1) ≤ H + H := by
        rw [← hSum]
        exact Nat.add_le_add_right hGeH (k + 1)
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

/-! #### 4-Point `NonZeroAbsSlot` Abstract Domain Soundness -/

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


/-! #### Totality of `rvalueCertifiedTotal`, `stepPlainStmtNonZero`, & Switch
Refinement -/

private theorem bool_and_false (b : Bool) : (b && false) = false := by
  cases b <;> rfl

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
      unfold evalBinOp; dsimp [BinOp.isShift]
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
      unfold evalBinOp; dsimp [BinOp.isShift]
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
      unfold evalBinOp; dsimp [BinOp.isShift]
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
        unfold evalBinOp; dsimp [BinOp.isShift]
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
        unfold evalBinOp; dsimp [BinOp.isShift]
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
        unfold evalBinOp; dsimp [BinOp.isShift]
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
        unfold evalBinOp; dsimp [BinOp.isShift]; rw [intWidth_beq_refl w, bool_beq_refl s]
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
        unfold evalBinOp; dsimp [BinOp.isShift]; rw [intWidth_beq_refl w, bool_beq_refl s]
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
        unfold evalBinOp; dsimp [BinOp.isShift]; rw [intWidth_beq_refl w, bool_beq_refl s]
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
        unfold evalBinOp; dsimp [BinOp.isShift]; rw [intWidth_beq_refl w, bool_beq_refl s]
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
        unfold evalBinOp; dsimp [BinOp.isShift]; rw [intWidth_beq_refl w, bool_beq_refl s]
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
        unfold evalBinOp; dsimp [BinOp.isShift]; rw [intWidth_beq_refl w, bool_beq_refl s]
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
        unfold evalBinOp; dsimp [BinOp.isShift]
        rw [intWidth_beq_refl w]; dsimp
        unfold evalArithOp
        change (if (decodeScalar ⟨w, false, rb⟩ == 0) = true then Except.error FaultKind.undefined
          else match truncateScalar w false
            (intTdiv (decodeScalar ⟨w, false, lb⟩) (decodeScalar ⟨w, false, rb⟩)) with
          | Except.error k => Except.error k
          | Except.ok (val, lossy) =>
            if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
            else Except.ok (Val.scalar val)) = _
        have hBeq0 : (decodeScalar ⟨w, false, rb⟩ == 0) = false := decide_eq_false hNe0
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
        unfold evalBinOp; dsimp [BinOp.isShift]
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
        unfold evalBinOp; dsimp [BinOp.isShift]
        rw [intWidth_beq_refl w]; dsimp
        unfold evalArithOp
        change (if (decodeScalar ⟨w, false, rb⟩ == 0) = true then Except.error FaultKind.undefined
          else match truncateScalar w false
            (intTmod (decodeScalar ⟨w, false, lb⟩) (decodeScalar ⟨w, false, rb⟩)) with
          | Except.error k => Except.error k
          | Except.ok (val, lossy) =>
            if ((_ || lossy) && false) = true then Except.error FaultKind.undefined
            else Except.ok (Val.scalar val)) = _
        have hBeq0 : (decodeScalar ⟨w, false, rb⟩ == 0) = false := decide_eq_false hNe0
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
        unfold evalBinOp; dsimp [BinOp.isShift]
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
          dsimp [evalRvalue, evalUnOp]; rw [hEvO]; dsimp; rw [hTr]
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
            dsimp [evalRvalue, evalUnOp]; rw [hEvO]; dsimp; rw [hTr]
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
          dsimp [writePlace] at hEv
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

private theorem dse_certified_elim_succeeds {bSrc : Body} {fSrc : FrameState}
    {cm : CallerMemory} {env : List NonZeroAbsSlot}
    {dstPlace : Place} {rval : Rvalue} {sTgt : StatementKind}
    {restTgt : List StatementKind} {termTgt : TerminatorKind}
    {dstTy : MirTy} {dstSlot : NonZeroAbsSlot}
    (hEnv : NonZeroEnvSound bSrc.locals env fSrc.locals)
    (hElim : isDseMoveFreeElim bSrc.locals (.assign dstPlace rval) sTgt restTgt termTgt = true)
    (hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dstPlace.localId = some dstTy)
    (hDstSlE : Trusted.MirSemantics.getElem? env dstPlace.localId = some dstSlot)
    (hLiveDst : nonZeroSlotImplies dstSlot .liveUninit = true)
    (hTot : rvalueCertifiedTotal bSrc.locals env dstPlace.localId dstTy rval = true) :
    ∃ s', evalStatement bSrc fSrc cm (.assign dstPlace rval) = .step s' := by
  cases sTgt with
  | assign _ _ | storageLive _ | storageDead _ | unsupported => cases hElim
  | nop =>
    dsimp [isDseMoveFreeElim] at hElim
    let ⟨h1234, _⟩ := bool_and_true hElim
    let ⟨h123, hNoMove⟩ := bool_and_true h1234
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hDstEmp, _⟩ := bool_and_true h12
    let ⟨val, locsAfterR, hEvR, hChk⟩ := rvalueCertifiedTotal_total hEnv hTot
    have hLtDst : dstPlace.localId < fSrc.locals.length := by
      rw [hEnv.1.1]; exact getElem?_some_lt hDstTy
    let ⟨sl0, hSl0⟩ := getElem?_some_of_lt fSrc.locals dstPlace.localId hLtDst
    let ⟨_, opt0, hSl0Eq⟩ :=
      nonZeroSlotImplies_sound hLiveDst
        (hEnv.2.2 dstPlace.localId dstTy dstSlot sl0 hDstTy hDstSlE hSl0)
    subst hSl0Eq
    let ⟨_, hFwdLive, _⟩ := evalRvalue_noMoveExcept hNoMove hEvR
    let ⟨optA, hSlAfter⟩ := hFwdLive opt0 hSl0
    have hWtAfterR := evalRvalue_preserves_wt hEnv.1 hEvR
    have hLtAfter : dstPlace.localId < locsAfterR.length := by
      rw [hWtAfterR.1]; exact getElem?_some_lt hDstTy
    let ⟨locsW, hSetW⟩ := setElem?_some_of_lt locsAfterR dstPlace.localId (.live (some val)) hLtAfter
    refine ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locsW }],
              callerMem := cm }, ?_⟩
    dsimp [evalStatement]
    rw [hDstEmp]; dsimp; rw [hDstTy]; dsimp; rw [hEvR]; dsimp
    dsimp [writePlace]; rw [hChk]; dsimp; rw [hSlAfter]; dsimp; rw [hSetW]

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
                have hPTyBool : MirTy.bool = pTy :=
                  mirTy_beq_eq (by dsimp [checkVal, Val.ty?] at hChkB; exact hChkB)
                rw [← hPTyBool]

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

private theorem checkCertifiedDseBlocksLoop_getElem? (bSrc bTgt : Body)
    (cert : BodyDseCert) :
    ∀ base bbs k bbSrc,
      checkCertifiedDseBlocksLoop bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      checkCertifiedDseBlock bSrc bTgt cert (base + k) bbSrc = true := by
  intro base bbs
  induction bbs generalizing base with
  | nil => intro _ _ _ h; cases h
  | cons bb₀ rest ih =>
    intro k bbSrc hLoop hGet
    let ⟨hHead, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hGet with hEq; subst hEq
      rw [Nat.add_zero]; exact hHead
    | succ m =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      have hSub := ih (base + 1) m bbSrc hTail hGet
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hSub
      exact hSub

private theorem checkNonZeroEdge_dse_sound {bSrc bTgt : Body} {cert : BodyDseCert}
    {edgeEnv : List NonZeroAbsSlot} {locs' : List LocalSlot} {tgt : BasicBlockId}
    (hBBLen : bSrc.basicBlocks.length = bTgt.basicBlocks.length)
    (hLoops : checkCertifiedDseBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks = true)
    (hEdge : checkNonZeroEdge bSrc.basicBlocks.length cert edgeEnv tgt = true)
    (hSound : NonZeroEnvSound bSrc.locals edgeEnv locs')
    (hLt : tgt < bSrc.basicBlocks.length) :
    ∃ bbSrc bbTgt entryEnv exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbTgt ∧
      Trusted.MirSemantics.getElem? cert tgt = some (some entryEnv) ∧
      NonZeroEnvSound bSrc.locals entryEnv locs' ∧
      stepCertifiedDseStmts bSrc.locals bbTgt.terminator entryEnv
        bbSrc.statements bbTgt.statements = some exitEnv ∧
      checkCertifiedDseBlock bSrc bTgt cert tgt bbSrc = true := by
  unfold checkNonZeroEdge at hEdge
  rw [nat_lt_blt hLt] at hEdge; dsimp at hEdge
  cases hCertTgt : Trusted.MirSemantics.getElem? cert tgt with
  | none => rw [hCertTgt] at hEdge; cases hEdge
  | some optEnv =>
    rw [hCertTgt] at hEdge
    cases optEnv with
    | none => cases hEdge
    | some entryEnv =>
      let ⟨bbSrc, hBBSrc⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt hLt
      let ⟨bbTgt, hBBTgt⟩ := getElem?_some_of_lt bTgt.basicBlocks tgt
        (by rw [← hBBLen]; exact hLt)
      have hChkBlk := checkCertifiedDseBlocksLoop_getElem? bSrc bTgt cert 0
        bSrc.basicBlocks tgt bbSrc hLoops hBBSrc
      rw [Nat.zero_add] at hChkBlk
      have hChkCopy := hChkBlk
      unfold checkCertifiedDseBlock at hChkCopy
      rw [hCertTgt, hBBTgt] at hChkCopy; dsimp at hChkCopy
      let ⟨_, hStmtsMatch⟩ := bool_and_true hChkCopy
      cases hPair : stepCertifiedDseStmts bSrc.locals bbTgt.terminator entryEnv
          bbSrc.statements bbTgt.statements with
      | none => rw [hPair] at hStmtsMatch; cases hStmtsMatch
      | some exitEnv =>
        exact ⟨bbSrc, bbTgt, entryEnv, exitEnv, hBBSrc, hBBTgt, rfl,
               nonZeroEnvImplies_sound hEdge hSound, hPair, hChkBlk⟩

private theorem checkCertifiedDseTerminator_step_sound {bSrc bTgt : Body}
    {bbSrc bbTgt : BasicBlock} {cert : BodyDseCert}
    {entryEnv exitEnv : List NonZeroAbsSlot} {fSrc : FrameState}
    {cm : CallerMemory} {s' : State}
    (hBBLen : bSrc.basicBlocks.length = bTgt.basicBlocks.length)
    (hLoops : checkCertifiedDseBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks = true)
    (hCertBlk : Trusted.MirSemantics.getElem? cert fSrc.blockIdx = some (some entryEnv))
    (hBBTgt : Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt)
    (hChkBlk : checkCertifiedDseBlock bSrc bTgt cert fSrc.blockIdx bbSrc = true)
    (hStepAll : stepCertifiedDseStmts bSrc.locals bbTgt.terminator entryEnv
      bbSrc.statements bbTgt.statements = some exitEnv)
    (hExitSound : NonZeroEnvSound bSrc.locals exitEnv fSrc.locals)
    (hEvT : evalTerminator bSrc bbSrc fSrc cm = .step s') :
    ∃ tgt locs',
      s' = { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
             callerMem := cm } ∧
      (tgt < bSrc.basicBlocks.length →
        ∃ bbNextS bbNextT nextEntry nextExit,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbNextS ∧
          Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbNextT ∧
          Trusted.MirSemantics.getElem? cert tgt = some (some nextEntry) ∧
          NonZeroEnvSound bSrc.locals nextEntry locs' ∧
          stepCertifiedDseStmts bSrc.locals bbNextT.terminator nextEntry
            bbNextS.statements bbNextT.statements = some nextExit ∧
          checkCertifiedDseBlock bSrc bTgt cert tgt bbNextS = true) := by
  unfold checkCertifiedDseBlock at hChkBlk
  rw [hCertBlk, hBBTgt] at hChkBlk; dsimp at hChkBlk
  let ⟨_, hEdgesMatch⟩ := bool_and_true hChkBlk
  rw [hStepAll] at hEdgesMatch; dsimp only at hEdgesMatch
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
    rw [hTerm] at hEvT hEdgesMatch; dsimp at hEvT hEdgesMatch
    injection hEvT with hSEq; subst hSEq
    refine ⟨target, fSrc.locals, rfl, fun hLt => ?_⟩
    exact checkNonZeroEdge_dse_sound hBBLen hLoops hEdgesMatch hExitSound hLt
  | switchInt discr targets =>
    rw [hTerm] at hEvT hEdgesMatch; dsimp only at hEvT hEdgesMatch
    let ⟨hOtherEdge, hBrEdges⟩ := bool_and_true hEdgesMatch
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
            exact checkNonZeroEdge_dse_sound hBBLen hLoops hBr hAfterSound hLt
          | inr hOth =>
            subst hOth
            have hRefEq := refineSwitchNonZeroEnv_bool (curEnv := exitEnv)
              (branches := targets.branches) hExitSound.1 hEvD
            change checkNonZeroEdge bSrc.basicBlocks.length cert
              (refineSwitchNonZeroEnv bSrc.locals
                (deinitMoveOperandNonZero bSrc.locals exitEnv discr) discr targets.branches)
              targets.otherwise = true at hOtherEdge
            rw [hRefEq] at hOtherEdge
            exact checkNonZeroEdge_dse_sound hBBLen hLoops hOtherEdge hAfterSound hLt
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
            exact checkNonZeroEdge_dse_sound hBBLen hLoops hBr hAfterSound hLt
          | inr hOth =>
            let ⟨hTgtEq, hGuardFn⟩ := hOth
            subst hTgtEq
            have hRefSound := refineSwitchNonZeroEnv_scalar
              hExitSound hAfterSound hEvD hGuardFn
            exact checkNonZeroEdge_dse_sound hBBLen hLoops hOtherEdge hRefSound hLt

private noncomputable def DseCertBisimRel (pSrc pTgt : Program) (cert : ProgramDseCert)
    (s t : State) : Prop :=
  ∃ fSrc fTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    ∀ bSrc,
      Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
      ∃ bTgt bodyCert,
        Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
        Trusted.MirSemantics.getElem? cert fSrc.defId = some bodyCert ∧
        isDseMoveFreeBody bSrc bTgt = true ∧
        checkCertifiedDseBody bodyCert bSrc bTgt = true ∧
        ∀ bbSrc,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
          ∃ bbTgt entryEnv curEnv exitEnv,
            Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt ∧
            Trusted.MirSemantics.getElem? bodyCert fSrc.blockIdx = some (some entryEnv) ∧
            checkCertifiedDseBlock bSrc bTgt bodyCert fSrc.blockIdx bbSrc = true ∧
            stepCertifiedDseStmts bSrc.locals bbTgt.terminator entryEnv
              bbSrc.statements bbTgt.statements = some exitEnv ∧
            stepCertifiedDseStmts bSrc.locals bbTgt.terminator curEnv
              (bbSrc.statements.drop fSrc.stmtIdx)
              (bbTgt.statements.drop fSrc.stmtIdx) = some exitEnv ∧
            NonZeroEnvSound bSrc.locals curEnv fSrc.locals ∧
            DeadMaskedEq bSrc.locals
              (fun d => d ≠ 0 ∧
                isDeadInBlockFrom d (bbTgt.statements.drop fSrc.stmtIdx) bbTgt.terminator = true)
              fSrc.locals fTgt.locals

private theorem dse_certified_query_bisim {pSrc pTgt : Program} {cert : ProgramDseCert}
    (hRel : isDseMoveFreeProgram pSrc pTgt = true)
    (hCert : checkCertifiedDseProgram cert pSrc pTgt = true)
    (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLenB, hCertZip⟩ := bool_and_true hCert
  have hCertLen := nat_beq_eq hCertLenB
  apply bisim_lockstep_query_iff (R := DseCertBisimRel pSrc pTgt cert)
    (dse_initState_eq hRel q)
  · intro s₀ hInitS
    let ⟨_, _, body, hBody, hNotEmpty, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hInitS
    subst hEqS
    have hInitNZ := initNonZeroEnvLoop_sound hArgs
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, fun bSrc hBS => ?_⟩
    dsimp at hBS; rw [hBody] at hBS; injection hBS with eB; subst eB
    let ⟨bodyCert, bTgt, hBCert, hBTgt, hChkBody⟩ :=
      listRel_zip_getElem? hCertLen hCertZip hBody
    let ⟨bTgt', hBTgt', hBRel⟩ := listRel_getElem?_left hBodiesRel hBody
    rw [hBTgt] at hBTgt'; injection hBTgt' with eBT; subst eBT
    refine ⟨bTgt, bodyCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
    intro bbSrc0 hBB0
    dsimp at hBB0
    have hChkBodyCopy := hChkBody
    unfold checkCertifiedDseBody at hChkBodyCopy
    let ⟨h123, hLoops⟩ := bool_and_true hChkBodyCopy
    let ⟨_, hEntry0⟩ := bool_and_true h123
    rw [if_bool_false hNotEmpty] at hEntry0
    cases hC0 : Trusted.MirSemantics.getElem? bodyCert 0 with
    | none => rw [hC0] at hEntry0; cases hEntry0
    | some opt0 =>
      rw [hC0] at hEntry0
      cases opt0 with
      | none => cases hEntry0
      | some env₀ =>
        have hEnv0Sound := nonZeroEnvImplies_sound hEntry0 hInitNZ
        have hChk0 := checkCertifiedDseBlocksLoop_getElem? body bTgt bodyCert 0
          body.basicBlocks 0 bbSrc0 hLoops hBB0
        rw [Nat.zero_add] at hChk0
        have hChk0Copy := hChk0
        unfold checkCertifiedDseBlock at hChk0Copy
        let ⟨bbTgt0, hBBTgt0, _⟩ := listRel_getElem?_left (bool_and_true hBRel).2 hBB0
        rw [hC0, hBBTgt0] at hChk0Copy; dsimp at hChk0Copy
        let ⟨_, hStMatch⟩ := bool_and_true hChk0Copy
        cases hStep0 : stepCertifiedDseStmts body.locals bbTgt0.terminator env₀
            bbSrc0.statements bbTgt0.statements with
        | none => rw [hStep0] at hStMatch; cases hStMatch
        | some exitEnv =>
          exact ⟨bbTgt0, env₀, env₀, exitEnv, hBBTgt0, rfl, hChk0, hStep0, hStep0,
                 hEnv0Sound, deadMaskedEq_refl hEnv0Sound.1⟩
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
            exact (listRel_getElem?_none_iff fSrc.defId hBodiesRel).mp hBSrc
          refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
          · unfold evalStep; dsimp; rw [hBSrc]
          · unfold evalStep; dsimp; rw [hBTgtNone]
        | some bSrc =>
          let ⟨bTgt, bodyCert, hBTgt, hBCert, hBRel, hChkBody, hBBInv⟩ := hBInv bSrc hBSrc
          let ⟨hBHdr, _, _, _, _, _⟩ := isDseMoveFreeBody_storage hBRel
          let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
          have hBBLenEq := listRel_length (bool_and_true hBRel).2
          have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
            rw [← hDefEq]; exact hBTgt
          cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
          | none =>
            have hBBTgtNone : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
              rw [← hBlkEq]
              exact (listRel_getElem?_none_iff fSrc.blockIdx (bool_and_true hBRel).2).mp hBBSrc
            refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
            · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]
            · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgtNone]
          | some bbSrc =>
            let ⟨bbTgt, entryEnv, curEnv, exitEnv, hBBTgt, hCertBlk, hChkBlk,
                 hStepAll, hStepRem, hCurSound, hMask⟩ := hBBInv bbSrc hBBSrc
            let ⟨bbTgt', hBBTgt', hBBRel⟩ :=
              listRel_getElem?_left (bool_and_true hBRel).2 hBBSrc
            rw [hBBTgt] at hBBTgt'; injection hBBTgt' with eBB; subst eBB
            let ⟨h12BB, hFullStmts⟩ := bool_and_true hBBRel
            let ⟨hCleanEqB, hTermEqB⟩ := bool_and_true h12BB
            have hCleanEq := bool_beq_eq hCleanEqB
            have hTermEq := terminatorEq_eq hTermEqB
            have hStmtsLenEq :=
              (stmtListStoragePreserved_props (isDseMoveFreeStmts_storage hFullStmts)).1
            have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
              rw [← hBlkEq]; exact hBBTgt
            cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
            | some sSrc =>
              have hDropS := drop_eq_cons_of_getElem? hStSrc
              rw [hDropS] at hStepRem
              cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
              | nil => rw [hDropT] at hStepRem; cases hStepRem
              | cons sTgt restTgt =>
                rw [hDropT] at hStepRem hMask
                let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
                have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some sTgt := by
                  rw [← hIdxEq]; exact hStTgt0
                dsimp [stepCertifiedDseStmts] at hStepRem
                cases hElim : isDseMoveFreeElim bSrc.locals sSrc sTgt restTgt bbTgt.terminator with
                | true =>
                  rw [if_bool_true hElim] at hStepRem
                  cases sSrc with
                  | nop | storageLive _ | storageDead _ | unsupported => cases hStepRem
                  | assign dstPlace rval =>
                    dsimp only at hStepRem
                    cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dstPlace.localId with
                    | none => rw [hDstTy] at hStepRem; cases hStepRem
                    | some dstTy =>
                      rw [hDstTy] at hStepRem
                      cases hDstSlE : Trusted.MirSemantics.getElem? curEnv dstPlace.localId with
                      | none => rw [hDstSlE] at hStepRem; cases hStepRem
                      | some dstSlot =>
                        rw [hDstSlE] at hStepRem; dsimp only at hStepRem
                        cases hTotCond : (nonZeroSlotImplies dstSlot .liveUninit &&
                            rvalueCertifiedTotal bSrc.locals curEnv dstPlace.localId dstTy rval) with
                        | false => rw [hTotCond] at hStepRem; cases hStepRem
                        | true =>
                          rw [if_bool_true hTotCond] at hStepRem
                          let ⟨hLiveDst, hTotRv⟩ := bool_and_true hTotCond
                          cases hStepPlain : stepPlainStmtNonZero bSrc.locals curEnv
                              (.assign dstPlace rval) with
                          | none => rw [hStepPlain] at hStepRem; cases hStepRem
                          | some nextEnv =>
                            rw [hStepPlain] at hStepRem; dsimp only at hStepRem
                            let ⟨s', hEvS⟩ := dse_certified_elim_succeeds (fSrc := fSrc) (cm := cmS)
                              hCurSound hElim hDstTy hDstSlE hLiveDst hTotRv
                            let ⟨l1', hEqS', hEvT, hMaskNext⟩ :=
                              dse_elim_step_effect (bTgt := bTgt) (fTgt := fTgt) hMask hElim hEvS
                            let ⟨l1'', hEqS'', hNextSound⟩ :=
                              stepPlainStmtNonZero_sound hCurSound hStepPlain hEvS
                            rw [hEqS'] at hEqS''
                            injection hEqS'' with eFr _
                            injection eFr with eF0 _
                            have hL1Eq : l1' = l1'' := by
                              have h := congrArg FrameState.locals eF0; exact h
                            subst hL1Eq; subst hEqS'
                            refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                                             callerMem := cmS },
                              { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals }],
                                callerMem := cmS }, ?_, ?_,
                              { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                              { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals },
                              rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
                            · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                              rw [hStSrc]; exact hEvS
                            · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                              rw [hStTgt2]; exact hEvT
                            · intro bS2 hBS2
                              dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                              refine ⟨bTgt, bodyCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                              intro bbS2 hBBS2
                              dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                              refine ⟨bbTgt, entryEnv, nextEnv, exitEnv, hBBTgt, hCertBlk,
                                      hChkBlk, hStepAll, ?_, hNextSound, ?_⟩
                              · dsimp; rw [hDropTNext]; exact hStepRem
                              · dsimp; rw [hDropTNext]; exact hMaskNext
                | false =>
                  rw [if_bool_false hElim] at hStepRem
                  cases hStEq : stmtEq sSrc sTgt with
                  | false => rw [if_bool_false hStEq] at hStepRem; cases hStepRem
                  | true =>
                    rw [if_bool_true hStEq] at hStepRem
                    have hsEq := stmtEq_eq hStEq; subst hsEq
                    cases hStepPlain : stepPlainStmtNonZero bSrc.locals curEnv sSrc with
                    | none => rw [hStepPlain] at hStepRem; cases hStepRem
                    | some nextEnv =>
                      rw [hStepPlain] at hStepRem; dsimp only at hStepRem
                      cases isDeadInBlockFrom_kept_step (fTgt := fTgt) (cm := cmS) hLocEq hMask with
                      | inl hFault =>
                        let ⟨fk, hFS', hFT'⟩ := hFault
                        refine Or.inr (Or.inr ⟨fk, ?_, ?_⟩)
                        · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                          rw [hStSrc]; exact hFS'
                        · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                          rw [hStTgt2]; exact hFT'
                      | inr hStepBoth =>
                        let ⟨l1', l2', hEvS, hEvT, hMaskNext⟩ := hStepBoth
                        let ⟨l1'', hEqS'', hNextSound⟩ :=
                          stepPlainStmtNonZero_sound hCurSound hStepPlain hEvS
                        injection hEqS'' with eFr _
                        injection eFr with eF0 _
                        have hL1Eq : l1' = l1'' := congrArg FrameState.locals eF0
                        subst hL1Eq
                        refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                                         callerMem := cmS },
                          { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                            callerMem := cmS }, ?_, ?_,
                          { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
                          { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' },
                          rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
                        · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                          rw [hStSrc]; exact hEvS
                        · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                          rw [hStTgt2]; exact hEvT
                        · intro bS2 hBS2
                          dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                          refine ⟨bTgt, bodyCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                          intro bbS2 hBBS2
                          dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                          refine ⟨bbTgt, entryEnv, nextEnv, exitEnv, hBBTgt, hCertBlk,
                                  hChkBlk, hStepAll, ?_, hNextSound, ?_⟩
                          · dsimp; rw [hDropTNext]; exact hStepRem
                          · dsimp; rw [hDropTNext]; exact hMaskNext
            | none =>
              have hGeSrc : bbSrc.statements.length ≤ fSrc.stmtIdx := by
                cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
                | inr hge => exact hge
                | inl hlt =>
                  let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
                  rw [hStSrc] at hx; cases hx
              have hDropSNil := drop_eq_nil_of_ge hGeSrc
              have hDropTNil : bbTgt.statements.drop fSrc.stmtIdx = [] :=
                drop_eq_nil_of_ge (by rw [← hStmtsLenEq]; exact hGeSrc)
              rw [hDropSNil, hDropTNil] at hStepRem
              rw [hDropTNil] at hMask
              injection hStepRem with hExitEq; subst hExitEq
              have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none :=
                getElem?_none_of_ge (by rw [← hIdxEq, ← hStmtsLenEq]; exact hGeSrc)
              cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
              | false =>
                have hEnd2 : Nat.beq fTgt.stmtIdx bbTgt.statements.length = false := by
                  rw [← hIdxEq, ← hStmtsLenEq]; exact hEnd
                refine Or.inr (Or.inr ⟨.unsupported, ?_, ?_⟩)
                · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                  rw [hStSrc]; dsimp; rw [hEnd]; rfl
                · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                  rw [hStTgt2]; dsimp; rw [hEnd2]; rfl
              | true =>
                have hEnd2 : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
                  rw [← hIdxEq, ← hStmtsLenEq]; exact hEnd
                have hSwUntouched : ∀ discr targets,
                    bbTgt.terminator = .switchInt discr targets →
                    ∀ d, (d ≠ 0 ∧ isDeadInBlockFrom d [] bbTgt.terminator = true) →
                      operandTouchesLocal d discr = false := by
                  intro discr targets hTm d ⟨_, hDnil⟩
                  rw [hTm] at hDnil; cases hDnil
                cases evalTerminator_deadMasked_bisim (fTgt := fTgt) (cm := cmS)
                    hLocEq hCleanEq hTermEq hMask (fun _ h => h.1) hSwUntouched with
                | inr hDF =>
                  cases hDF with
                  | inl hD =>
                    let ⟨out, hDS, hDT⟩ := hD
                    refine Or.inr (Or.inl ⟨out, ?_, ?_⟩)
                    · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                      rw [hStSrc]; dsimp; rw [hEnd]; dsimp; exact hDS
                    · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                      rw [hStTgt2]; dsimp; rw [hEnd2]; dsimp; exact hDT
                  | inr hF =>
                    let ⟨fk, hFS', hFT'⟩ := hF
                    refine Or.inr (Or.inr ⟨fk, ?_, ?_⟩)
                    · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                      rw [hStSrc]; dsimp; rw [hEnd]; dsimp; exact hFS'
                    · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                      rw [hStTgt2]; dsimp; rw [hEnd2]; dsimp; exact hFT'
                | inl hST =>
                  let ⟨tgt, l1', l2', hTS, hTT, hMaskAfter⟩ := hST
                  have hTermNotRetUnreach : bbTgt.terminator ≠ .return_ ∧ bbTgt.terminator ≠ .unreachable := by
                    constructor
                    · intro hRet
                      unfold evalTerminator at hTT; rw [hRet] at hTT; dsimp at hTT
                      cases hCl : bbTgt.cleanup with
                      | true => rw [hCl] at hTT; cases hTT
                      | false =>
                        rw [hCl] at hTT; dsimp at hTT
                        cases h0 : Trusted.MirSemantics.getElem? fTgt.locals 0 with
                        | none => rw [h0] at hTT; cases hTT
                        | some sl => rw [h0] at hTT; cases sl with | dead => cases hTT | live o => cases o <;> cases hTT
                    · intro hUn
                      unfold evalTerminator at hTT; rw [hUn] at hTT; cases hTT
                  have hLocsEq : l1' = l2' := by
                    apply list_eq_of_getElem?_eq (hMaskAfter.1.1.trans hMaskAfter.2.1.1.symm)
                    intro i
                    apply (hMaskAfter.2.2 i).2
                    intro ⟨_, hDnil⟩
                    cases isDeadInBlockFrom_nil_term hDnil with
                    | inl hR => exact hTermNotRetUnreach.1 hR
                    | inr hU => exact hTermNotRetUnreach.2 hU
                  subst hLocsEq
                  have hLoops : checkCertifiedDseBlocksLoop bSrc bTgt bodyCert 0 bSrc.basicBlocks = true :=
                    (bool_and_true hChkBody).2
                  let ⟨tgt', l1'', hTgtStEq, hNextBlkFn⟩ :=
                    checkCertifiedDseTerminator_step_sound hBBLenEq hLoops hCertBlk
                      hBBTgt hChkBlk hStepAll hCurSound hTS
                  injection hTgtStEq with eFr _
                  injection eFr with eF0 _
                  have hTgtEq : tgt = tgt' := congrArg FrameState.blockIdx eF0
                  have hL1Eq : l1' = l1'' := congrArg FrameState.locals eF0
                  subst hTgtEq; subst hL1Eq
                  refine Or.inl ⟨{ frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1' }],
                                   callerMem := cmS },
                    { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l1' }],
                      callerMem := cmS }, ?_, ?_,
                    { fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1' },
                    { fTgt with blockIdx := tgt, stmtIdx := 0, locals := l1' },
                    rfl, rfl, rfl, hDefEq, rfl, rfl, ?_⟩
                  · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBSrc]; dsimp
                    rw [hStSrc]; dsimp; rw [hEnd]; dsimp; exact hTS
                  · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp
                    rw [hStTgt2]; dsimp; rw [hEnd2]; dsimp; exact hTT
                  · intro bS2 hBS2
                    dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                    refine ⟨bTgt, bodyCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                    intro bbNext hBBNext
                    dsimp at hBBNext
                    have hLtTgt : tgt < bSrc.basicBlocks.length := getElem?_some_lt hBBNext
                    let ⟨bbNextS, bbNextT, nextEntry, nextExit, hBBNS, hBBNT,
                         hCertNext, hNextSound, hStepNext, hChkNext⟩ := hNextBlkFn hLtTgt
                    rw [hBBNext] at hBBNS; injection hBBNS with eN; subst eN
                    exact ⟨bbNextT, nextEntry, nextEntry, nextExit, hBBNT, hCertNext,
                           hChkNext, hStepNext, hStepNext, hNextSound,
                           deadMaskedEq_refl hNextSound.1⟩

private theorem vc_transport_dse_certified_iff_priv
    (pSrc pTgt : Program) (cert : ProgramDseCert)
    (hRel : isDseMoveFreeProgram pSrc pTgt = true)
    (hCert : checkCertifiedDseProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
    let ⟨hBHdr, _, hEmpty, _, hBounds, _⟩ := isDseMoveFreeBody_storage hBRel
    exact ⟨hBHdr, hEmpty, hBounds⟩
  · exact dse_certified_query_bisim hRel hCert
  · intro defId args
    have hRelEntry : isDseMoveFreeProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies
    exact (dse_certified_query_bisim hRelEntry hCert { args := args }).1

/-! ### Stage 4 Private Helpers — Layer E: `DestinationPropagation` & Tail
Pipeline (Theorems 3 & 4) -/

/-! #### `DestinationPropagation` Storage Preservation, Cross-Block Deadness,
& Pair Lemmas -/

private theorem isDestPropPairCore_elim {bodyLocals : List MirTy}
    {s₁ s₂ t₁ t₂ : StatementKind} {tmp : LocalId}
    (hCore : isDestPropPairCore bodyLocals s₁ s₂ t₁ t₂ = some tmp) :
    ∃ tmpPlace dstPlace rv₁ rvUse dstTy,
      s₁ = .assign tmpPlace rv₁ ∧
      s₂ = .assign dstPlace rvUse ∧
      t₁ = .assign dstPlace rv₁ ∧
      t₂ = .nop ∧
      tmpPlace.projection.isEmpty = true ∧
      dstPlace.projection.isEmpty = true ∧
      tmp = tmpPlace.localId ∧
      tmp ≠ 0 ∧
      tmp ≠ dstPlace.localId ∧
      rvalueTouchesLocal tmp rv₁ = false ∧
      isDestPropCopyOrMoveTmp tmp rvUse = true ∧
      Trusted.MirSemantics.getElem? bodyLocals tmp = some dstTy ∧
      Trusted.MirSemantics.getElem? bodyLocals dstPlace.localId = some dstTy := by
  cases s₁ with
  | nop | storageLive _ | storageDead _ | unsupported => cases hCore
  | assign tmpPlace rv₁ =>
    cases s₂ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hCore
    | assign dstPlace rvUse =>
      cases t₁ with
      | nop | storageLive _ | storageDead _ | unsupported => cases hCore
      | assign dstPlace' rv₂ =>
        cases t₂ with
        | assign _ _ | storageLive _ | storageDead _ | unsupported => cases hCore
        | nop =>
          dsimp [isDestPropPairCore] at hCore
          cases hHdr : (tmpPlace.projection.isEmpty && dstPlace.projection.isEmpty &&
              placeEq dstPlace dstPlace' && rvalueEq rv₁ rv₂) with
          | false => rw [hHdr] at hCore; cases hCore
          | true =>
            rw [hHdr] at hCore; dsimp at hCore
            let ⟨h123, hRvEqB⟩ := bool_and_true hHdr
            let ⟨h12, hPlEqB⟩ := bool_and_true h123
            let ⟨hTEmp, hDEmp⟩ := bool_and_true h12
            have hPlEq := placeEq_eq hPlEqB; subst hPlEq
            have hRvEq := rvalueEq_eq hRvEqB; subst hRvEq
            cases hMid : (!Nat.beq tmpPlace.localId 0 &&
                !Nat.beq tmpPlace.localId dstPlace.localId &&
                !rvalueTouchesLocal tmpPlace.localId rv₁ &&
                isDestPropCopyOrMoveTmp tmpPlace.localId rvUse) with
            | false => rw [hMid] at hCore; cases hCore
            | true =>
              rw [hMid] at hCore; dsimp at hCore
              let ⟨hM123, hUseTmp⟩ := bool_and_true hMid
              let ⟨hM12, hNoTouchB⟩ := bool_and_true hM123
              let ⟨hNe0B, hNeDstB⟩ := bool_and_true hM12
              cases hTTy : Trusted.MirSemantics.getElem? bodyLocals tmpPlace.localId with
              | none => rw [hTTy] at hCore; cases hCore
              | some tmpTy =>
                rw [hTTy] at hCore
                cases hDTy : Trusted.MirSemantics.getElem? bodyLocals dstPlace.localId with
                | none => rw [hDTy] at hCore; cases hCore
                | some dstTy =>
                  rw [hDTy] at hCore; dsimp at hCore
                  cases hTyEqB : MirTy.beq tmpTy dstTy with
                  | false => rw [hTyEqB] at hCore; cases hCore
                  | true =>
                    rw [hTyEqB] at hCore
                    injection hCore with hTmpId
                    have hTyEq := mirTy_beq_eq hTyEqB; subst hTyEq
                    subst hTmpId
                    exact ⟨tmpPlace, dstPlace, rv₁, rvUse, tmpTy,
                      rfl, rfl, rfl, rfl, hTEmp, hDEmp, rfl,
                      nat_ne_of_beq_false (bool_not_true hNe0B),
                      nat_ne_of_beq_false (bool_not_true hNeDstB),
                      bool_not_true hNoTouchB, hUseTmp, hTTy, hDTy⟩

private theorem isDestPropStmts_storage_aux {bodyLocals : List MirTy} :
    ∀ n {ss₁ ss₂},
      ss₁.length ≤ n →
      isDestPropStmts bodyLocals ss₁ ss₂ = true →
      StmtListStoragePreserved ss₁ ss₂ := by
  intro n
  induction n with
  | zero =>
    intro ss₁ ss₂ hLen hRel
    cases ss₁ with
    | nil =>
      cases ss₂ with
      | nil => exact True.intro
      | cons t ts => cases ts <;> cases hRel
    | cons _ _ => exact False.elim (Nat.not_succ_le_zero _ hLen)
  | succ k ih =>
    intro ss₁ ss₂ hLen hRel
    cases ss₁ with
    | nil =>
      cases ss₂ with
      | nil => exact True.intro
      | cons t ts => cases ts <;> cases hRel
    | cons s₁ tail₁ =>
      cases tail₁ with
      | nil =>
        cases ss₂ with
        | nil => cases hRel
        | cons t₁ tail₂ =>
          cases tail₂ with
          | nil =>
            dsimp [isDestPropStmts] at hRel
            exact ⟨Or.inl (stmtEq_eq hRel), True.intro⟩
          | cons _ _ => cases hRel
      | cons s₂ r₁ =>
        cases ss₂ with
        | nil => cases hRel
        | cons t₁ tail₂ =>
          cases tail₂ with
          | nil => cases hRel
          | cons t₂ r₂ =>
            dsimp [isDestPropStmts] at hRel
            have hLe1 : (s₂ :: r₁).length ≤ k := Nat.le_of_succ_le_succ hLen
            have hLe2 : r₁.length ≤ k :=
              Nat.le_trans (Nat.le_succ r₁.length) hLe1
            cases hCore : isDestPropPairCore bodyLocals s₁ s₂ t₁ t₂ with
            | some tmp =>
              rw [hCore] at hRel; dsimp at hRel
              let ⟨_, _, _, _, _, hs1, hs2, ht1, ht2, _, _, _, _, _, _, _, _, _⟩ :=
                isDestPropPairCore_elim hCore
              subst hs1; subst hs2; subst ht1; subst ht2
              exact ⟨Or.inr ⟨True.intro, True.intro⟩,
                     ⟨Or.inr ⟨True.intro, True.intro⟩, ih hLe2 hRel⟩⟩
            | none =>
              rw [hCore] at hRel; dsimp at hRel
              let ⟨hEq1, hRest⟩ := bool_and_true hRel
              exact ⟨Or.inl (stmtEq_eq hEq1), ih hLe1 hRest⟩

private theorem isDestPropBody_storage {bSrc bTgt : Body}
    (hBody : isDestPropBody bSrc bTgt = true) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.length = bTgt.basicBlocks.length ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    (∀ idx, hasStorageAnnotation bSrc idx = hasStorageAnnotation bTgt idx) ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨hBHdr, hBBs⟩ := bool_and_true hBody
  apply bodyStorage_eq_of_blocks hBHdr hBBs
  intro bb₁ bb₂ hBB
  let ⟨_, hStmts⟩ := bool_and_true hBB
  exact isDestPropStmts_storage_aux bb₁.statements.length (Nat.le_refl _) hStmts

private theorem destProp_initState_eq {pSrc pTgt : Program}
    (hRel : isDestPropProgram pSrc pTgt = true) (q : Query) :
    initState pSrc q = initState pTgt q := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodies
  · intro b₁ hB₁
    let ⟨b₂, hB₂, hBRel⟩ := listRel_getElem?_left hBodies hB₁
    rw [hEnt] at hB₂
    let ⟨hBHdr, _, hEmpty, _, hBounds, hLoop⟩ := isDestPropBody_storage hBRel
    exact ⟨b₂, hB₂, hBHdr, hEmpty, hBounds, hLoop q.args⟩

private theorem checkDeadAtEntryLoop_getElem? {bTgt : Body}
    {deadAtEntry : List (List LocalId)} :
    ∀ {base dsList k ds},
      checkDeadAtEntryLoop bTgt deadAtEntry base dsList = true →
      Trusted.MirSemantics.getElem? dsList k = some ds →
      ∃ bbTgt,
        Trusted.MirSemantics.getElem? bTgt.basicBlocks (base + k) = some bbTgt ∧
        ∀ d, natElem d ds = true →
          d ≠ 0 ∧
          isDeadAcrossCfg deadAtEntry bTgt.basicBlocks.length d
            bbTgt.statements bbTgt.terminator = true := by
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
        let ⟨hNe0B, hDead⟩ := bool_and_true hD
        exact ⟨nat_ne_of_beq_false (bool_not_true hNe0B), hDead⟩
    | succ m =>
      have hSub := ih hTail hG
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hSub
      exact hSub

private theorem checkDestPropBlocksLoop_getElem? {bSrc bTgt : Body}
    {cert : BodyDestPropCert} :
    ∀ {base bbs k bbSrc},
      checkDestPropBlocksLoop bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      checkDestPropBlock bSrc bTgt cert (base + k) bbSrc = true := by
  intro base bbs
  induction bbs generalizing base with
  | nil => intro _ _ _ hG; cases hG
  | cons _ _ ih =>
    intro k bbSrc hLoop hG
    let ⟨hHead, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hG with hEq; subst hEq
      rw [Nat.add_zero]; exact hHead
    | succ m =>
      have hSub := ih hTail hG
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hSub
      exact hSub

private theorem isDeadAcrossCfg_kept_step {bSrc bTgt : Body}
    {deadAtEntry : List (List LocalId)} {numBlocks : Nat}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmt : StatementKind} {restTgt : List StatementKind}
    {termTgt : TerminatorKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg deadAtEntry numBlocks d (stmt :: restTgt) termTgt = true)
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
        (fun d => d ≠ 0 ∧ isDeadAcrossCfg deadAtEntry numBlocks d restTgt termTgt = true)
        locs₁' locs₂') := by
  apply evalStatement_kept_deadMasked_bisim hLocEq hMask
  · intro hNop d ⟨hd0, hD⟩; subst hNop; exact ⟨hd0, hD⟩
  · intro _; exact Or.inr True.intro
  · intro id hSL d ⟨hd0, hD⟩
    subst hSL; dsimp [isDeadAcrossCfg] at hD
    cases hEq : Nat.beq id d with
    | true => exact Or.inl (nat_beq_eq hEq).symm
    | false => rw [hEq] at hD; dsimp at hD; exact Or.inr ⟨hd0, hD⟩
  · intro id hSD d ⟨hd0, hD⟩
    subst hSD; dsimp [isDeadAcrossCfg] at hD
    cases hEq : Nat.beq id d with
    | true => exact Or.inl (nat_beq_eq hEq).symm
    | false => rw [hEq] at hD; dsimp at hD; exact Or.inr ⟨hd0, hD⟩
  · intro lhs rv hAsg d ⟨hd0, hD⟩
    subst hAsg; dsimp [isDeadAcrossCfg] at hD
    let ⟨hNoT, hRest⟩ := bool_and_true hD
    refine ⟨bool_not_true hNoT, ?_⟩
    cases hOvr : (lhs.projection.isEmpty && Nat.beq lhs.localId d) with
    | true =>
      let ⟨hPE, hId⟩ := bool_and_true hOvr
      exact Or.inl ⟨hPE, (nat_beq_eq hId).symm⟩
    | false =>
      rw [hOvr] at hRest; dsimp at hRest
      exact Or.inr ⟨hd0, hRest⟩

private theorem isDeadAcrossCfg_nil_step_target {bTgt : Body} {bbTgt bbNextTgt : BasicBlock}
    {deadAtEntry : List (List LocalId)} {fTgt : FrameState} {cm : CallerMemory}
    {tgt : BasicBlockId} {locs₂' : List LocalSlot} {d : LocalId}
    (hDeadLoop : checkDeadAtEntryLoop bTgt deadAtEntry 0 deadAtEntry = true)
    (hEvTT : evalTerminator bTgt bbTgt fTgt cm =
      .step { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs₂' }],
              callerMem := cm })
    (hBBNext : Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbNextTgt)
    (hDeadNil : isDeadAcrossCfg deadAtEntry bTgt.basicBlocks.length d [] bbTgt.terminator = true) :
    isDeadAcrossCfg deadAtEntry bTgt.basicBlocks.length d
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
      | some sl => rw [h0] at hEvTT; cases sl with | dead => cases hEvTT | live o => cases o <;> cases hEvTT
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    rw [hTerm] at hEvTT; cases hEvTT
  | goto target =>
    rw [hTerm] at hEvTT hDeadNil; dsimp [jumpToBlock, isDeadAcrossCfg] at hEvTT hDeadNil
    injection hEvTT with eSt; injection eSt with eFs _; injection eFs with eF _
    have hTgtEq : target = tgt := congrArg FrameState.blockIdx eF
    subst hTgtEq
    let ⟨_, hMatchDs⟩ := bool_and_true hDeadNil
    cases hDs : Trusted.MirSemantics.getElem? deadAtEntry target with
    | none => rw [hDs] at hMatchDs; cases hMatchDs
    | some ds =>
      rw [hDs] at hMatchDs
      let ⟨bbTgt', hBB', hAllDs⟩ := checkDeadAtEntryLoop_getElem? hDeadLoop hDs
      rw [Nat.zero_add, hBBNext] at hBB'
      injection hBB' with eBB; subst eBB
      exact (hAllDs d hMatchDs).2
  | switchInt discr targets =>
    rw [hTerm] at hEvTT hDeadNil; dsimp [isDeadAcrossCfg] at hEvTT hDeadNil
    let ⟨h123, hBrAll⟩ := bool_and_true hDeadNil
    let ⟨_, hOwDs⟩ := bool_and_true h123
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
        cases hDs : Trusted.MirSemantics.getElem? deadAtEntry targets.otherwise with
        | none => rw [hDs] at hOwDs; cases hOwDs
        | some ds =>
          rw [hDs] at hOwDs
          let ⟨bbTgt', hBB', hAllDs⟩ := checkDeadAtEntryLoop_getElem? hDeadLoop hDs
          rw [Nat.zero_add, hBBNext] at hBB'
          injection hBB' with eBB; subst eBB
          exact (hAllDs d hOwDs).2
      | inl hInBr =>
        let ⟨cb, hMem⟩ := hInBr
        have hBr := list_all_mem_true hBrAll hMem
        let ⟨_, hBrDs⟩ := bool_and_true hBr
        cases hDs : Trusted.MirSemantics.getElem? deadAtEntry tgt with
        | none => rw [hDs] at hBrDs; cases hBrDs
        | some ds =>
          rw [hDs] at hBrDs
          let ⟨bbTgt', hBB', hAllDs⟩ := checkDeadAtEntryLoop_getElem? hDeadLoop hDs
          rw [Nat.zero_add, hBBNext] at hBB'
          injection hBB' with eBB; subst eBB
          exact (hAllDs d hBrDs).2

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
    {deadAtEntry : List (List LocalId)} {numBlocks : Nat}
    {env : List AbsSlot} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {tmpPlace dstPlace : Place} {rv₁ : Rvalue}
    {restTgt : List StatementKind} {termTgt : TerminatorKind}
    {dstTy : MirTy} {tmpSlot dstSlot : AbsSlot}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEnvS : AbsEnvSound bSrc.locals env fSrc.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg deadAtEntry numBlocks d
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
    (hTmpDeadRest : isDeadAcrossCfg deadAtEntry numBlocks tmpPlace.localId restTgt termTgt = true) :
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
        (fun d => d ≠ 0 ∧ isDeadAcrossCfg deadAtEntry numBlocks d restTgt termTgt = true)
        tmpPlace.localId dstPlace.localId dstTy val l1' l2') := by
  have hDTyTgt : Trusted.MirSemantics.getElem? bTgt.locals dstPlace.localId = some dstTy := by
    rw [← hLocEq]; exact hDTy
  have hUntouchedRv1 : ∀ d,
      (d ≠ 0 ∧ isDeadAcrossCfg deadAtEntry numBlocks d
        ((.assign dstPlace rv₁) :: .nop :: restTgt) termTgt = true) →
      rvalueTouchesLocal d rv₁ = false := by
    intro d ⟨_, hD⟩
    dsimp [isDeadAcrossCfg] at hD
    exact bool_not_true (bool_and_true hD).1
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
        dsimp [writePlace]; rw [hChk]; rfl
      · dsimp [evalStatement]; rw [hDEmp]; dsimp; rw [hDTyTgt]; dsimp
        rw [← hLocEq, hOR2]; dsimp; dsimp [writePlace]; rw [hChk]; rfl
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
      -- In bTgt, both tmp and dst are .live in fTgt.locals via hMask.2.2
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
          have hLa1Tmp : Trusted.MirSemantics.getElem? la1 tmpPlace.localId = some (.live optT0) := by
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
            dsimp [writePlace]; rw [hChk]; dsimp; rw [hLa1Tmp]; dsimp; rw [hSet1]
          · dsimp [evalStatement]; rw [hDEmp]; dsimp; rw [hDTyTgt]; dsimp
            rw [← hLocEq, hOR2]; dsimp
            dsimp [writePlace]; rw [hChk]; dsimp; rw [hLa2Dst]; dsimp; rw [hSet2]
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
              rw [hDEmp, hBeqDstF] at hIfDst; dsimp at hIfDst
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
        dsimp [writePlace]; rw [hChk]; dsimp; rw [hG1Dst]; dsimp; rw [hSetW]
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
      have hMoveDst : Trusted.MirSemantics.getElem? lMove dstPlace.localId = some (.live optD1) := by
        rw [setElem?_getElem?_ne hSetM hTmpNeDst.symm]; exact hG1Dst
      let ⟨l1'', hSetW⟩ := setElem?_some_of_lt lMove dstPlace.localId
        (.live (some val)) (by rw [hWtMove.1]; exact hLtDst)
      refine ⟨l1'', ?_, rfl, ⟨localsWellTyped_set hWtMove hDTy hSetW hChk, hWt2, fun i => ?_⟩⟩
      · dsimp [evalStatement]; rw [hDEmp]; dsimp; rw [hDTy]; dsimp
        dsimp [evalRvalue, evalOperandToSlot]
        rw [hPE]; dsimp; rw [hTTy, hG1Tmp]; dsimp; rw [hSetM]; dsimp
        rw [mirTy_beq_refl dstTy]; dsimp
        dsimp [writePlace]; rw [hChk]; dsimp; rw [hMoveDst]; dsimp; rw [hSetW]
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

private noncomputable def DestPropBlockMode (bSrc bTgt : Body) (bCert : BodyDestPropCert)
    (bbSrc bbTgt : BasicBlock) (fSrc fTgt : FrameState) : Prop :=
  (∃ env exitEnv,
    stepDestPropCertStmts bSrc.locals bCert.deadAtEntry bTgt.basicBlocks.length
      bbTgt.terminator env
      (bbSrc.statements.drop fSrc.stmtIdx)
      (bbTgt.statements.drop fSrc.stmtIdx) = some exitEnv ∧
    checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      bCert.liveCert exitEnv bbSrc.terminator = true ∧
    AbsEnvSound bSrc.locals env fSrc.locals ∧
    DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bCert.deadAtEntry bTgt.basicBlocks.length d
          (bbTgt.statements.drop fSrc.stmtIdx) bbTgt.terminator = true)
      fSrc.locals fTgt.locals) ∨
  (∃ dstPlace rvUse restSrc restTgt tmp dstTy val env₁ env₂ exitEnv,
    bbSrc.statements.drop fSrc.stmtIdx = (.assign dstPlace rvUse) :: restSrc ∧
    bbTgt.statements.drop fSrc.stmtIdx = .nop :: restTgt ∧
    dstPlace.projection.isEmpty = true ∧
    isDestPropCopyOrMoveTmp tmp rvUse = true ∧
    DestPropMidLocals bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bCert.deadAtEntry bTgt.basicBlocks.length d
          restTgt bbTgt.terminator = true)
      tmp dstPlace.localId dstTy val fSrc.locals fTgt.locals ∧
    AbsEnvSound bSrc.locals env₁ fSrc.locals ∧
    stepPlainStmtAbs bSrc.locals env₁ (.assign dstPlace rvUse) = some env₂ ∧
    stepDestPropCertStmts bSrc.locals bCert.deadAtEntry bTgt.basicBlocks.length
      bbTgt.terminator env₂ restSrc restTgt = some exitEnv ∧
    checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      bCert.liveCert exitEnv bbSrc.terminator = true)

private noncomputable def DestPropBisimRel (pSrc pTgt : Program) (cert : ProgramDestPropCert)
    (s t : State) : Prop :=
  ∃ fSrc fTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    ∀ bSrc,
      Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
      ∃ bTgt bCert,
        Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
        Trusted.MirSemantics.getElem? cert fSrc.defId = some bCert ∧
        isDestPropBody bSrc bTgt = true ∧
        checkDestPropBody bCert bSrc bTgt = true ∧
        ∀ bbSrc,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
          ∃ bbTgt,
            Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt ∧
            DestPropBlockMode bSrc bTgt bCert bbSrc bbTgt fSrc fTgt

private theorem destProp_kept_step_helper {pSrc pTgt : Program} {cert : ProgramDestPropCert}
    {bSrc bTgt : Body} {bCert : BodyDestPropCert} {bbSrc bbTgt : BasicBlock}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmt : StatementKind} {restSrc restTgt : List StatementKind}
    {env env₁ exitEnv : List AbsSlot}
    (hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc)
    (hBTgt : Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt)
    (hBCert : Trusted.MirSemantics.getElem? cert fSrc.defId = some bCert)
    (hBRel : isDestPropBody bSrc bTgt = true)
    (hChkBody : checkDestPropBody bCert bSrc bTgt = true)
    (hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc)
    (hBBTgt : Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt)
    (hDefEq : fSrc.defId = fTgt.defId)
    (hBlkEq : fSrc.blockIdx = fTgt.blockIdx)
    (hIdxEq : fSrc.stmtIdx = fTgt.stmtIdx)
    (hLocEq : bSrc.locals = bTgt.locals)
    (hDropS : bbSrc.statements.drop fSrc.stmtIdx = stmt :: restSrc)
    (hDropT : bbTgt.statements.drop fSrc.stmtIdx = stmt :: restTgt)
    (hEnvS : AbsEnvSound bSrc.locals env fSrc.locals)
    (hMask : DeadMaskedEq bSrc.locals
      (fun d => d ≠ 0 ∧
        isDeadAcrossCfg bCert.deadAtEntry bTgt.basicBlocks.length d
          (stmt :: restTgt) bbTgt.terminator = true)
      fSrc.locals fTgt.locals)
    (hStep1 : stepPlainStmtAbs bSrc.locals env stmt = some env₁)
    (hStepRest : stepDestPropCertStmts bSrc.locals bCert.deadAtEntry
      bTgt.basicBlocks.length bbTgt.terminator env₁ restSrc restTgt = some exitEnv)
    (hEdges : checkAbsTerminatorEdges bSrc.locals bSrc.basicBlocks.length
      bCert.liveCert exitEnv bbSrc.terminator = true) :
    StepOutcomeBisim pSrc pTgt (DestPropBisimRel pSrc pTgt cert)
      { frames := [fSrc], callerMem := cm }
      { frames := [fTgt], callerMem := cm } := by
  let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
  let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
  have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
    rw [← hDefEq]; exact hBTgt
  have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
    rw [← hBlkEq]; exact hBBTgt
  have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some stmt := by
    rw [← hIdxEq]; exact hStTgt0
  unfold StepOutcomeBisim evalStep; dsimp
  rw [hBSrc, hBTgt2]; dsimp
  rw [hBBSrc, hBBTgt2]; dsimp
  rw [hStSrc, hStTgt2]; dsimp
  cases isDeadAcrossCfg_kept_step (cm := cm) hLocEq hMask with
  | inl hCase =>
    let ⟨fk, hF1, hF2⟩ := hCase
    rw [hF1, hF2]
    exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
  | inr hCase =>
    let ⟨l1', l2', hS1, hS2, hMask'⟩ := hCase
    let ⟨l1'', hEqS', hEnv1⟩ := stepPlainStmtAbs_sound hEnvS hStep1 hS1
    injection hEqS' with eFs _; injection eFs with eF _; injection eF with _ _ _ eL
    subst eL
    rw [hS1, hS2]
    refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                     callerMem := cm },
      { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
        callerMem := cm }, rfl, rfl,
      { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' },
      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' },
      rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
    intro bS2 hBS2
    dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
    refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
    intro bbS2 hBBS2
    dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
    refine ⟨bbTgt, hBBTgt, Or.inl ⟨env₁, exitEnv, ?_, hEdges, hEnv1, ?_⟩⟩
    · dsimp; rw [hDropSNext, hDropTNext]; exact hStepRest
    · dsimp; rw [hDropTNext]; exact hMask'

private theorem destProp_query_iff {pSrc pTgt : Program} {cert : ProgramDestPropCert}
    (hRel : isDestPropProgram pSrc pTgt = true)
    (hCert : checkDestPropProgram cert pSrc pTgt = true) (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLenB, hCertZip⟩ := bool_and_true hCert
  have hCertLen := nat_beq_eq hCertLenB
  apply bisim_lockstep_query_iff (R := DestPropBisimRel pSrc pTgt cert)
    (destProp_initState_eq hRel q)
  · intro s₀ hOk
    let ⟨_, _, body, hBody, hNotEmp, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    have hInitSound := initAbsEnvLoop_sound hArgs
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, fun bSrc hBS => ?_⟩
    rw [hBody] at hBS; injection hBS with eB; subst eB
    let ⟨bCert, bTgt, hBCert, hBTgt, hChkBody⟩ :=
      listRel_zip_getElem? hCertLen hCertZip hBody
    let ⟨bTgt', hBTgt', hBRel⟩ := listRel_getElem?_left hBodiesRel hBody
    rw [hBTgt] at hBTgt'; injection hBTgt' with eT; subst eT
    refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
    intro bbSrc hBB0
    dsimp at hBB0
    let ⟨h1234, hLoop⟩ := bool_and_true hChkBody
    let ⟨_, hEntry0⟩ := bool_and_true h1234
    rw [hNotEmp] at hEntry0; dsimp at hEntry0
    cases hC0 : Trusted.MirSemantics.getElem? bCert.liveCert 0 with
    | none => rw [hC0] at hEntry0; cases hEntry0
    | some opt0 =>
      rw [hC0] at hEntry0
      cases opt0 with
      | none => cases hEntry0
      | some env₀ =>
        have hEnv0 := absEnvImplies_sound hEntry0 hInitSound
        have hChk0 := checkDestPropBlocksLoop_getElem? (k := 0) hLoop hBB0
        rw [Nat.zero_add] at hChk0
        unfold checkDestPropBlock at hChk0
        rw [hC0] at hChk0
        cases hBBTgt0 : Trusted.MirSemantics.getElem? bTgt.basicBlocks 0 with
        | none => rw [hBBTgt0] at hChk0; cases hChk0
        | some bbTgt =>
          rw [hBBTgt0] at hChk0; dsimp at hChk0
          let ⟨_, hRest0⟩ := bool_and_true hChk0
          cases hSt0 : stepDestPropCertStmts body.locals bCert.deadAtEntry
              bTgt.basicBlocks.length bbTgt.terminator env₀
              bbSrc.statements bbTgt.statements with
          | none => rw [hSt0] at hRest0; cases hRest0
          | some exitE =>
            rw [hSt0] at hRest0; dsimp at hRest0
            exact ⟨bbTgt, rfl, Or.inl ⟨env₀, exitE, hSt0, hRest0, hEnv0,
              deadMaskedEq_refl hEnv0.1⟩⟩
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
            rw [← hDefEq]; exact (listRel_getElem?_none_iff fSrc.defId hBodiesRel).mp hBSrc
          unfold StepOutcomeBisim evalStep; dsimp
          rw [hBSrc, hBTgtNone]
          exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
        | some bSrc =>
          let ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, hBBInv⟩ := hBInv bSrc hBSrc
          let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
          let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
          cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
          | none =>
            have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
              rw [← hDefEq]; exact hBTgt
            have hBBTgtNone : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
              rw [← hBlkEq]; exact (listRel_getElem?_none_iff fSrc.blockIdx hBBsRel).mp hBBSrc
            unfold StepOutcomeBisim evalStep; dsimp
            rw [hBSrc, hBTgt2]; dsimp; rw [hBBSrc, hBBTgtNone]
            exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
          | some bbSrc =>
            let ⟨bbTgt, hBBTgt, hMode⟩ := hBBInv bbSrc hBBSrc
            let ⟨bbTgt', hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBsRel hBBSrc
            rw [hBBTgt] at hBBTgt'; injection hBBTgt' with eBB; subst eBB
            let ⟨h12BB, hStmtsSynt⟩ := bool_and_true hBBRel
            let ⟨hCleanEqB, hTermEqB⟩ := bool_and_true h12BB
            have hCleanEq := bool_beq_eq hCleanEqB
            have hTermEq := terminatorEq_eq hTermEqB
            have hStmtsLenEq : bbSrc.statements.length = bbTgt.statements.length :=
              (stmtListStoragePreserved_props
                (isDestPropStmts_storage_aux bbSrc.statements.length
                  (Nat.le_refl _) hStmtsSynt)).1
            cases hMode with
            | inr hMidMode =>
              let ⟨dstPlace, rvUse, restSrc, restTgt, tmp, dstTy, val,
                   env₁, env₂, exitEnv, hDropS, hDropT, hDEmp, hUseTmp,
                   hMidLocs, hEnv1S, hStep2Abs, hStepRest, hEdges⟩ := hMidMode
              let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
              let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
              have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                rw [← hDefEq]; exact hBTgt
              have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                rw [← hBlkEq]; exact hBBTgt
              have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some .nop := by
                rw [← hIdxEq]; exact hStTgt0
              let ⟨l1'', hEvS2, hEvT2, hMaskNext⟩ :=
                destProp_pair_step2_bisim (bTgt := bTgt) (cm := cmS) hMidLocs hDEmp hUseTmp
              let ⟨l1''', hEqS2, hEnv2S⟩ := stepPlainStmtAbs_sound hEnv1S hStep2Abs hEvS2
              injection hEqS2 with eFs _; injection eFs with eF _
              have hLEq : l1'' = l1''' := congrArg FrameState.locals eF
              subst hLEq
              unfold StepOutcomeBisim evalStep; dsimp
              rw [hBSrc, hBTgt2]; dsimp
              rw [hBBSrc, hBBTgt2]; dsimp
              rw [hStSrc, hStTgt2]; dsimp
              rw [hEvS2, hEvT2]
              refine Or.inl ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1'' }],
                               callerMem := cmS },
                { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals }],
                  callerMem := cmS }, rfl, rfl,
                { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1'' },
                { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := fTgt.locals },
                rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
              intro bS2 hBS2
              dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
              refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
              intro bbS2 hBBS2
              dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
              refine ⟨bbTgt, hBBTgt, Or.inl ⟨env₂, exitEnv, ?_, hEdges, hEnv2S, ?_⟩⟩
              · dsimp; rw [hDropSNext, hDropTNext]; exact hStepRest
              · dsimp; rw [hDropTNext]; exact hMaskNext
            | inl hAligned =>
              let ⟨env, exitEnv, hStepStmts, hEdges, hEnvS, hMask⟩ := hAligned
              cases hDropS : bbSrc.statements.drop fSrc.stmtIdx with
              | nil =>
                rw [hDropS] at hStepStmts
                cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
                | cons _ _ => rw [hDropT] at hStepStmts; cases hStepStmts
                | nil =>
                  rw [hDropT] at hStepStmts hMask
                  dsimp [stepDestPropCertStmts] at hStepStmts
                  injection hStepStmts with eEnv; subst eEnv
                  have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                    rw [← hDefEq]; exact hBTgt
                  have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                    rw [← hBlkEq]; exact hBBTgt
                  cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
                  | some x =>
                    rw [drop_eq_cons_of_getElem? hStSrc] at hDropS; cases hDropS
                  | none =>
                    have hGeSrc : bbSrc.statements.length ≤ fSrc.stmtIdx := by
                      cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
                      | inr hge => exact hge
                      | inl hlt =>
                        let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
                        rw [hStSrc] at hx; cases hx
                    have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none :=
                      getElem?_none_of_ge (by rw [← hIdxEq, ← hStmtsLenEq]; exact hGeSrc)
                    unfold StepOutcomeBisim evalStep; dsimp
                    rw [hBSrc, hBTgt2]; dsimp
                    rw [hBBSrc, hBBTgt2]; dsimp
                    rw [hStSrc, hStTgt2]; dsimp
                    rw [← hIdxEq, ← hStmtsLenEq]
                    cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
                    | false => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
                    | true =>
                      dsimp
                      have hSwUntouched : ∀ discr targets,
                          bbTgt.terminator = .switchInt discr targets →
                          ∀ d, (d ≠ 0 ∧ isDeadAcrossCfg bCert.deadAtEntry
                            bTgt.basicBlocks.length d [] bbTgt.terminator = true) →
                          operandTouchesLocal d discr = false := by
                        intro discr targets hTm d ⟨_, hDnil⟩
                        rw [hTm] at hDnil
                        dsimp [isDeadAcrossCfg] at hDnil
                        let ⟨h123, _⟩ := bool_and_true hDnil
                        let ⟨h12, _⟩ := bool_and_true h123
                        let ⟨hNoTD, _⟩ := bool_and_true h12
                        exact bool_not_true hNoTD
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
                          rfl, rfl, rfl, hDefEq, rfl, rfl, ?_⟩
                        intro bS2 hBS2
                        dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                        refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                        intro bbNext hBBNext
                        dsimp at hBBNext
                        let ⟨tgtEnv, hCNext, hTgtEnvS⟩ := hCertNext (getElem?_some_lt hBBNext)
                        let ⟨h1234, hLoop⟩ := bool_and_true hChkBody
                        let ⟨h123, _⟩ := bool_and_true h1234
                        let ⟨_, hDeadLoop⟩ := bool_and_true h123
                        have hChkNext := checkDestPropBlocksLoop_getElem? hLoop hBBNext
                        rw [Nat.zero_add] at hChkNext
                        unfold checkDestPropBlock at hChkNext
                        rw [hCNext] at hChkNext
                        cases hBBTgtNext : Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt with
                        | none => rw [hBBTgtNext] at hChkNext; cases hChkNext
                        | some bbNextTgt =>
                          rw [hBBTgtNext] at hChkNext; dsimp at hChkNext
                          let ⟨_, hRestNext⟩ := bool_and_true hChkNext
                          cases hStNext : stepDestPropCertStmts bSrc.locals bCert.deadAtEntry
                              bTgt.basicBlocks.length bbNextTgt.terminator
                              tgtEnv bbNext.statements bbNextTgt.statements with
                          | none => rw [hStNext] at hRestNext; cases hRestNext
                          | some exitEN =>
                            rw [hStNext] at hRestNext; dsimp at hRestNext
                            have hMaskEntry : DeadMaskedEq bSrc.locals
                                (fun d => d ≠ 0 ∧ isDeadAcrossCfg bCert.deadAtEntry
                                  bTgt.basicBlocks.length d
                                  bbNextTgt.statements bbNextTgt.terminator = true)
                                l1' l2' := by
                              apply deadMaskedEq_mono ?_ hMaskAfterTerm
                              intro d ⟨hd0, hDnil⟩
                              exact ⟨hd0, isDeadAcrossCfg_nil_step_target hDeadLoop
                                hEvTT hBBTgtNext hDnil⟩
                            exact ⟨bbNextTgt, rfl, Or.inl ⟨tgtEnv, exitEN, hStNext, hRestNext,
                              hTgtEnvS, hMaskEntry⟩⟩
              | cons s₁ tailSrc =>
                rw [hDropS] at hStepStmts
                cases tailSrc with
                | nil =>
                  cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
                  | nil => rw [hDropT] at hStepStmts; cases hStepStmts
                  | cons t₁ tailTgt =>
                    rw [hDropT] at hStepStmts hMask
                    cases tailTgt with
                    | cons _ _ => cases hStepStmts
                    | nil =>
                      dsimp [stepDestPropCertStmts] at hStepStmts
                      cases hEq1 : stmtEq s₁ t₁ with
                      | false => rw [hEq1] at hStepStmts; cases hStepStmts
                      | true =>
                        rw [hEq1] at hStepStmts; dsimp at hStepStmts
                        have hsEq := stmtEq_eq hEq1; subst hsEq
                        exact destProp_kept_step_helper hBSrc hBTgt hBCert hBRel hChkBody
                          hBBSrc hBBTgt hDefEq hBlkEq hIdxEq hLocEq hDropS hDropT
                          hEnvS hMask hStepStmts rfl hEdges
                | cons s₂ restSrc =>
                  cases hDropT : bbTgt.statements.drop fSrc.stmtIdx with
                  | nil => rw [hDropT] at hStepStmts; cases hStepStmts
                  | cons t₁ tailTgt =>
                    rw [hDropT] at hStepStmts hMask
                    cases tailTgt with
                    | nil => cases hStepStmts
                    | cons t₂ restTgt =>
                      dsimp [stepDestPropCertStmts] at hStepStmts
                      cases hCore : isDestPropPairCore bSrc.locals s₁ s₂ t₁ t₂ with
                      | none =>
                        rw [hCore] at hStepStmts; dsimp at hStepStmts
                        cases hNeq1 : (!stmtEq s₁ t₁) with
                        | true => rw [hNeq1] at hStepStmts; cases hStepStmts
                        | false =>
                          rw [hNeq1] at hStepStmts; dsimp at hStepStmts
                          have hsEq := stmtEq_eq (bool_not_false hNeq1); subst hsEq
                          cases hStep1 : stepPlainStmtAbs bSrc.locals env s₁ with
                          | none => rw [hStep1] at hStepStmts; cases hStepStmts
                          | some env₁ =>
                            rw [hStep1] at hStepStmts; dsimp at hStepStmts
                            exact destProp_kept_step_helper hBSrc hBTgt hBCert hBRel hChkBody
                              hBBSrc hBBTgt hDefEq hBlkEq hIdxEq hLocEq hDropS hDropT
                              hEnvS hMask hStep1 hStepStmts hEdges
                      | some tmp =>
                        rw [hCore] at hStepStmts; dsimp only at hStepStmts
                        let ⟨tmpPlace, dstPlace, rv₁, rvUse, dstTy,
                             hs1, hs2, ht1, ht2, hTEmp, hDEmp, hTmpId,
                             hTmpNe0, hTmpNeDst, hNoTouchTmp, hUseTmp,
                             hTTy, hDTy⟩ := isDestPropPairCore_elim hCore
                        subst hs1; subst hs2; subst ht1; subst ht2; subst hTmpId
                        dsimp only at hStepStmts
                        rw [hDTy] at hStepStmts
                        cases hETmp : Trusted.MirSemantics.getElem? env tmpPlace.localId with
                        | none => rw [hETmp] at hStepStmts; cases hStepStmts
                        | some tmpSlot =>
                          rw [hETmp] at hStepStmts
                          cases hEDst : Trusted.MirSemantics.getElem? env dstPlace.localId with
                          | none => rw [hEDst] at hStepStmts; cases hStepStmts
                          | some dstSlot =>
                            rw [hEDst] at hStepStmts; dsimp only at hStepStmts
                            cases hGuard : (isSupportedScalarOrUnitTy dstTy &&
                                absSlotImplies tmpSlot .liveUninit &&
                                absSlotImplies dstSlot .liveUninit &&
                                isDeadAcrossCfg bCert.deadAtEntry bTgt.basicBlocks.length
                                  tmpPlace.localId restTgt bbTgt.terminator) with
                            | false => rw [if_bool_false hGuard] at hStepStmts; cases hStepStmts
                            | true =>
                              rw [if_bool_true hGuard] at hStepStmts
                              let ⟨hG123, hTmpDeadRest⟩ := bool_and_true hGuard
                              let ⟨hG12, hDstImp⟩ := bool_and_true hG123
                              let ⟨_, hTmpImp⟩ := bool_and_true hG12
                              cases hStep1 : stepPlainStmtAbs bSrc.locals env
                                  (.assign tmpPlace rv₁) with
                              | none => rw [hStep1] at hStepStmts; cases hStepStmts
                              | some env₁ =>
                                rw [hStep1] at hStepStmts; dsimp only at hStepStmts
                                cases hStep2 : stepPlainStmtAbs bSrc.locals env₁
                                    (.assign dstPlace rvUse) with
                                | none => rw [hStep2] at hStepStmts; cases hStepStmts
                                | some env₂ =>
                                  rw [hStep2] at hStepStmts; dsimp only at hStepStmts
                                  let ⟨hStSrc, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
                                  let ⟨hStTgt0, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
                                  have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                                    rw [← hDefEq]; exact hBTgt
                                  have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                                    rw [← hBlkEq]; exact hBBTgt
                                  have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx =
                                      some (.assign dstPlace rv₁) := by
                                    rw [← hIdxEq]; exact hStTgt0
                                  unfold StepOutcomeBisim evalStep; dsimp
                                  rw [hBSrc, hBTgt2]; dsimp
                                  rw [hBBSrc, hBBTgt2]; dsimp
                                  rw [hStSrc, hStTgt2]; dsimp
                                  cases destProp_pair_step1_bisim (cm := cmS)
                                      hLocEq hEnvS hMask hTEmp hDEmp hTmpNe0 hTmpNeDst
                                      hNoTouchTmp hTTy hDTy hETmp hEDst hTmpImp hDstImp
                                      hTmpDeadRest with
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
                                      rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq], ?_⟩
                                    intro bS2 hBS2
                                    dsimp at hBS2; rw [hBSrc] at hBS2; injection hBS2 with eB; subst eB
                                    refine ⟨bTgt, bCert, hBTgt, hBCert, hBRel, hChkBody, ?_⟩
                                    intro bbS2 hBBS2
                                    dsimp at hBBS2; rw [hBBSrc] at hBBS2; injection hBBS2 with eBB; subst eBB
                                    refine ⟨bbTgt, hBBTgt, Or.inr
                                      ⟨dstPlace, rvUse, restSrc, restTgt, tmpPlace.localId,
                                       dstTy, val, env₁, env₂, exitEnv, ?_, ?_, hDEmp, hUseTmp,
                                       hMidNext, hEnv1S, hStep2, hStepStmts, hEdges⟩⟩
                                    · dsimp; exact hDropSNext
                                    · dsimp; exact hDropTNext

private theorem destProp_certified_bidirectional_iff_priv
    (pSrc pTgt : Program) (cert : ProgramDestPropCert)
    (hRel : isDestPropProgram pSrc pTgt = true)
    (hCert : checkDestPropProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
    let ⟨hBHdr, _, hEmpty, _, hBounds, _⟩ := isDestPropBody_storage hBRel
    exact ⟨hBHdr, hEmpty, hBounds⟩
  · exact destProp_query_iff hRel hCert
  · intro defId args
    have hRelEntry : isDestPropProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies
    exact (destProp_query_iff hRelEntry hCert { args := args }).1

/-! #### Theorem 4: End-to-End Post-`SimplifyCfg` Tail Pipeline Composition -/

private theorem relProgram_header_and_ids {p₁ p₂ : Program} {r : Body → Body → Bool}
    (hHdr : programHeaderEq p₁ p₂ = true)
    (hBodies : listRel r p₁.bodies p₂.bodies = true)
    (hBHdr : ∀ b₁ b₂, r b₁ b₂ = true → bodyHeaderEq b₁ b₂ = true) :
    p₁.pointerWidthBits = p₂.pointerWidthBits ∧
    p₁.mirProfileVersion = p₂.mirProfileVersion ∧
    p₁.entryDefId = p₂.entryDefId ∧
    p₁.scope = p₂.scope ∧
    p₁.bodies.length = p₂.bodies.length ∧
    p₁.bodies.map (fun b => b.identity) = p₂.bodies.map (fun b => b.identity) := by
  let ⟨hPw, hVer, hEnt, hSc⟩ := programHeaderEq_elim hHdr
  refine ⟨hPw, hVer, hEnt, hSc, listRel_length hBodies, ?_⟩
  apply list_map_eq_of_rel hBodies
  intro b₁ b₂ hR
  exact (bodyHeaderEq_elim (hBHdr b₁ b₂ hR)).2.2.2

private theorem postSimplifyCfg_tail_crate_and_unit_iff_priv
    (p₀ p₁ p₂ p₃ p₄ : Program)
    (cpCert mhCert : ProgramAbsCert)
    (dseCert : ProgramDseCert)
    (dpCert : ProgramDestPropCert)
    (hCopy : isCopyPropProgram p₀ p₁ = true)
    (hCopyCert : checkCopyPropProgram cpCert p₀ p₁ = true)
    (hMove : isMoveHeadUnifyProgram p₁ p₂ = true)
    (hMoveCert : checkMoveHeadUnifyProgram mhCert p₁ p₂ = true)
    (hDse : isDseMoveFreeProgram p₂ p₃ = true)
    (hDseCert : checkCertifiedDseProgram dseCert p₂ p₃ = true)
    (hDest : isDestPropProgram p₃ p₄ = true)
    (hDestCert : checkDestPropProgram dpCert p₃ p₄ = true) :
    FullSemanticEquiv p₀ p₄ ∧
    (∀ (safety : String → List Val → Prop) (prop : Program → Prop),
      (prop p₄ ↔ prop p₀) →
      (CrateTheorem ⟨p₄, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨p₀, ⟨safety, prop⟩⟩) ∧
      (UnitTheorem ⟨p₄, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨p₀, ⟨safety, prop⟩⟩)) := by
  have e01 := copyProp_certified_bidirectional_iff_priv p₀ p₁ cpCert hCopy hCopyCert
  have e12 := moveHeadUnify_certified_bidirectional_iff_priv p₁ p₂ mhCert hMove hMoveCert
  have e23 := vc_transport_dse_certified_iff_priv p₂ p₃ dseCert hDse hDseCert
  have e34 := destProp_certified_bidirectional_iff_priv p₃ p₄ dpCert hDest hDestCert
  let ⟨hPw01, hVer01, hEnt01, hSc01, hLen01, hIds01⟩ :=
    relProgram_header_and_ids (bool_and_true hCopy).1 (bool_and_true hCopy).2
      (fun _ _ h => (bool_and_true h).1)
  let ⟨hPw12, hVer12, hEnt12, hSc12, hLen12, hIds12⟩ :=
    relProgram_header_and_ids (bool_and_true hMove).1 (bool_and_true hMove).2
      (fun _ _ h => (bool_and_true h).1)
  let ⟨hPw23, hVer23, hEnt23, hSc23, hLen23, hIds23⟩ :=
    relProgram_header_and_ids (bool_and_true hDse).1 (bool_and_true hDse).2
      (fun _ _ h => (bool_and_true h).1)
  let ⟨hPw34, hVer34, hEnt34, hSc34, _, hIds34⟩ :=
    relProgram_header_and_ids (bool_and_true hDest).1 (bool_and_true hDest).2
      (fun _ _ h => (bool_and_true h).1)
  have e02 := fullSemanticEquiv_trans hLen01 e01 e12
  have e03 := fullSemanticEquiv_trans (hLen01.trans hLen12) e02 e23
  have e04 := fullSemanticEquiv_trans ((hLen01.trans hLen12).trans hLen23) e03 e34
  refine ⟨e04, ?_⟩
  intro safety prop hProp
  exact programVerified_iff_of_equiv e04
    (((hPw01.trans hPw12).trans hPw23).trans hPw34)
    (((hVer01.trans hVer12).trans hVer23).trans hVer34)
    (((hEnt01.trans hEnt12).trans hEnt23).trans hEnt34)
    (((hSc01.trans hSc12).trans hSc23).trans hSc34)
    (((hIds01.trans hIds12).trans hIds23).trans hIds34)
    safety prop hProp

/-! ## Part III: Core Target Theorems Directly Over `Trusted.MirSemantics` -/

/-- **Theorem 1a (Certified `CopyProp` Bidirectional Equivalence,
`copy_prop.rs:12-194`):**
Block-local copy propagation after `_dst = Use(Copy(_src))` (`isCopyPropProgram`)
paired with flow-sensitive liveness/initialization certification
(`checkCopyPropProgram`) preserves `WellFormed`, `Behavior`,
`ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and `BodyVerified`
bidirectionally (`↔`). -/
theorem copyProp_certified_bidirectional_iff
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isCopyPropProgram pSrc pTgt = true)
    (hCert : checkCopyPropProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact copyProp_certified_bidirectional_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 1b (Certified `Move`-Head Single-Use Unification Bidirectional
Equivalence, `copy_prop.rs:14-21, 127-156`):**
Rewriting adjacent `_dst = Use(Move(_src)); _out = rval[move _dst]` into
`.nop; _out = rval[move _src]` (`isMoveHeadUnifyProgram`) under
`checkMoveHeadUnifyProgram` preserves full bidirectional equivalence (`↔`). -/
theorem moveHeadUnify_certified_bidirectional_iff
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isMoveHeadUnifyProgram pSrc pTgt = true)
    (hCert : checkMoveHeadUnifyProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact moveHeadUnify_certified_bidirectional_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 2a (Unconditional Forward Codegen Refinement for Move-Free
`DeadStoreElimination`, `dead_store_elimination.rs:34-155`):**
Replacing a dead assignment `StatementKind.assign ⟨dst, []⟩ rval` (`dst ≠ 0`,
no `Operand.move` of any `l ≠ dst`) with `.nop` (`isDseMoveFreeProgram`)
unconditionally refines well-formed executions (`pSrc → pTgt`), even when `rval`
can fault on ill-formed inputs. -/
theorem codegen_dse_moveFree_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isDseMoveFreeProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  exact codegen_dse_moveFree_refines_unconditional_priv pSrc pTgt hRel

/-- **Theorem 2b (Certified Bidirectional VC Transport for
`DeadStoreElimination`):**
Pairing `isDseMoveFreeProgram` with `checkCertifiedDseProgram` (guaranteeing
that at every eliminated store `dst` is `.live` and `evalRvalue` + `writePlace`
succeed without faulting) restores full bidirectional equivalence (`↔`). -/
theorem vc_transport_dse_certified_iff
    (pSrc pTgt : Program) (cert : ProgramDseCert)
    (hRel : isDseMoveFreeProgram pSrc pTgt = true)
    (hCert : checkCertifiedDseProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact vc_transport_dse_certified_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 3 (Certified `DestinationPropagation` Bidirectional Equivalence,
`dest_prop.rs:16-160`):**
Fusing `_tmp = rval; _dst = Use(Move(_tmp) | Copy(_tmp))` into `_dst = rval;
.nop` (`isDestPropProgram`) under `checkDestPropProgram` preserves full
bidirectional equivalence (`↔`)—including self-updates where `rval` reads
`Operand.copy ⟨dst, []⟩`. -/
theorem destProp_certified_bidirectional_iff
    (pSrc pTgt : Program) (cert : ProgramDestPropCert)
    (hRel : isDestPropProgram pSrc pTgt = true)
    (hCert : checkDestPropProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact destProp_certified_bidirectional_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 4 (End-to-End Post-`SimplifyCfg` Optimization Tail Bidirectional
`CrateTheorem` & `UnitTheorem` Transport, `lib.rs:760-762`):**
Composing certified `CopyProp`, certified `MoveHeadUnify`, certified
`DeadStoreElimination`, and certified `DestinationPropagation` preserves
`FullSemanticEquiv` and transports `CrateTheorem` and `UnitTheorem`
bidirectionally (`↔`) whenever `specs.property` respects the pipeline endpoints. -/
theorem postSimplifyCfg_tail_crate_and_unit_iff
    (p₀ p₁ p₂ p₃ p₄ : Program)
    (cpCert mhCert : ProgramAbsCert)
    (dseCert : ProgramDseCert)
    (dpCert : ProgramDestPropCert)
    (hCopy : isCopyPropProgram p₀ p₁ = true)
    (hCopyCert : checkCopyPropProgram cpCert p₀ p₁ = true)
    (hMove : isMoveHeadUnifyProgram p₁ p₂ = true)
    (hMoveCert : checkMoveHeadUnifyProgram mhCert p₁ p₂ = true)
    (hDse : isDseMoveFreeProgram p₂ p₃ = true)
    (hDseCert : checkCertifiedDseProgram dseCert p₂ p₃ = true)
    (hDest : isDestPropProgram p₃ p₄ = true)
    (hDestCert : checkDestPropProgram dpCert p₃ p₄ = true) :
    FullSemanticEquiv p₀ p₄ ∧
    (∀ (safety : String → List Val → Prop) (prop : Program → Prop),
      (prop p₄ ↔ prop p₀) →
      (CrateTheorem ⟨p₄, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨p₀, ⟨safety, prop⟩⟩) ∧
      (UnitTheorem ⟨p₄, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨p₀, ⟨safety, prop⟩⟩)) := by
  exact postSimplifyCfg_tail_crate_and_unit_iff_priv p₀ p₁ p₂ p₃ p₄ cpCert mhCert dseCert dpCert hCopy hCopyCert hMove hMoveCert hDse hDseCert hDest hDestCert

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

/-! ### Sharpness Counterexample 1: `CopyProp` Past Clobbered `src` Is Unsound -/

noncomputable def progCopyClobberSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::copyprop_clobbered_src"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progCopyClobberTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::copyprop_clobbered_src"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE1:** Propagating `.copy ⟨2, []⟩ ↦ .copy ⟨1, []⟩` past
an intervening write `_1 = const 99_u32` changes the return value from `10_u32`
to `99_u32`, and is rejected by `isCopyPropProgram`. -/
theorem ce_copyprop_clobbered_src_unsound :
    isCopyPropProgram progCopyClobberSrc progCopyClobberTgt = false ∧
    PositiveCanaryClaim progCopyClobberSrc { args := [u32Val 10] } (u32Val 10) ∧
    PositiveCanaryClaim progCopyClobberTgt { args := [u32Val 10] } (u32Val 99) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 6) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Sharpness Counterexample 2: Propagating a `Move` Head Without Eliminating the Head Move Faults Under `deinitMovedPlace = true` -/

noncomputable def progMoveNoHeadElimSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::copyprop_move_no_head_elim"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progMoveNoHeadElimTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::copyprop_move_no_head_elim"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE2:** Keeping `_2 = move _1` while rewriting
`_0 = copy _2 ↦ _0 = copy _1` introduces use-after-move UB (`.undefined`) in
$M_{\text{anneal}}$ (`deinitMovedPlace = true`), and is rejected by both
`isCopyPropProgram` and `isMoveHeadUnifyProgram`. -/
theorem ce_copyprop_move_deinit_without_head_elim_unsound :
    isCopyPropProgram progMoveNoHeadElimSrc progMoveNoHeadElimTgt = false ∧
    isMoveHeadUnifyProgram progMoveNoHeadElimSrc progMoveNoHeadElimTgt = false ∧
    PositiveCanaryClaim progMoveNoHeadElimSrc
      { args := [u32Val 10] } (u32Val 10) ∧
    NegativeCanaryClaim progMoveNoHeadElimTgt
      { args := [u32Val 10] } .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 5) rfl
  · exact negativeCanary_of_execFaults (fuel := 5) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 3: `CopyProp` Past `StorageDead(src)` Introduces `DeadLocal` UB -/

noncomputable def progCopyStorageDeadSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::copyprop_storage_dead_src"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .storageDead 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progCopyStorageDeadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::copyprop_storage_dead_src"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .storageDead 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE3 (`copy_prop.rs:55-92` `StorageChecker` Hazard):**
Propagating `_2 ↦ _1` past `StorageDead(_1)` without removing `_1`'s storage
markers turns a well-formed execution returning `7_u32` into `DeadLocal` UB
(`.undefined`), and is rejected by `isCopyPropProgram`. -/
theorem ce_copyprop_storage_dead_src_unsound :
    isCopyPropProgram progCopyStorageDeadSrc progCopyStorageDeadTgt = false ∧
    PositiveCanaryClaim progCopyStorageDeadSrc queryEmpty (u32Val 7) ∧
    NegativeCanaryClaim progCopyStorageDeadTgt queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 8) rfl
  · exact negativeCanary_of_execFaults (fuel := 8) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 4: `DeadStoreElimination` via `Rvalue::is_safe_to_remove()` Erases `DivisionByZero` UB (`E3-10` Live Miri Finding) -/

noncomputable def progDseDivZeroSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, u32Ty, u32Ty]
    identity := "ce::dse_div_zero_erases_ub"
    basicBlocks := [{
      statements := [
        .assign ⟨3, []⟩ (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)),
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progDseDivZeroTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, u32Ty, u32Ty]
    identity := "ce::dse_div_zero_erases_ub"
    basicBlocks := [{
      statements := [
        .nop,
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE4 (`E3-10` `custom_mir_div_zero_dead_local` Live
`-Zmir-preserve-ub=yes` Bug):**
Eliminating dead `_3 = _1 / _2` satisfies `isDseMoveFreeProgram` (forward-sound
for codegen) and returns `42_u32` in `pTgt` at `(10_u32, 0_u32)`, yet `pSrc`
faults with `FaultKind.undefined` (`DivisionByZero`) and is rejected by
`checkCertifiedDseProgram`. -/
theorem ce_dse_is_safe_to_remove_div_zero_erases_ub :
    isDseMoveFreeProgram progDseDivZeroSrc progDseDivZeroTgt = true ∧
    checkCertifiedDseProgram
      [[some [.liveUninit, .liveInit, .liveInit, .liveUninit]]]
      progDseDivZeroSrc progDseDivZeroTgt = false ∧
    PositiveCanaryClaim progDseDivZeroTgt
      { args := [u32Val 10, u32Val 0] } (u32Val 42) ∧
    NegativeCanaryClaim progDseDivZeroSrc
      { args := [u32Val 10, u32Val 0] } .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 5) rfl
  · exact negativeCanary_of_execFaults (fuel := 5) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 5: `DeadStoreElimination` Erases Uninitialized-Read UB -/

noncomputable def progDseUninitReadSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::dse_uninit_read_erases_ub"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

noncomputable def progDseUninitReadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::dse_uninit_read_erases_ub"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .nop,
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE5:** Eliminating `_2 = copy _1` when `_1` is
uninitialized (`StorageLive(_1)`) satisfies `isDseMoveFreeProgram` and returns
`7_u32` in `pTgt`, yet faults `.undefined` in `pSrc` and is rejected by
`checkCertifiedDseProgram`. -/
theorem ce_dse_is_safe_to_remove_uninit_read_erases_ub :
    isDseMoveFreeProgram progDseUninitReadSrc progDseUninitReadTgt = true ∧
    checkCertifiedDseProgram [[some [.liveUninit, .dead, .liveUninit]]]
      progDseUninitReadSrc progDseUninitReadTgt = false ∧
    PositiveCanaryClaim progDseUninitReadTgt queryEmpty (u32Val 7) ∧
    NegativeCanaryClaim progDseUninitReadSrc queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 7) rfl
  · exact negativeCanary_of_execFaults (fuel := 7) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 6: `DeadStoreElimination` on a `.dead` Destination Slot Erases Write-Time `DeadLocal` UB -/

noncomputable def progDseDeadDstSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::dse_dead_dst_erases_ub"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .storageDead 1,
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩)),
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progDseDeadDstTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::dse_dead_dst_erases_ub"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .storageDead 1,
        .nop,
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE6:** Even when `rval` is a pure valid constant
(`const 5_u32`), eliminating `_1 = const 5_u32` after `StorageDead(_1)` erases
`writePlace`'s `DeadLocal` UB (`.undefined`) in `pSrc`, and is rejected by
`checkCertifiedDseProgram`. -/
theorem ce_dse_dead_dst_slot_erases_write_deadlocal_ub :
    isDseMoveFreeProgram progDseDeadDstSrc progDseDeadDstTgt = true ∧
    checkCertifiedDseProgram [[some [.liveUninit, .dead]]]
      progDseDeadDstSrc progDseDeadDstTgt = false ∧
    PositiveCanaryClaim progDseDeadDstTgt queryEmpty (u32Val 7) ∧
    NegativeCanaryClaim progDseDeadDstSrc queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 7) rfl
  · exact negativeCanary_of_execFaults (fuel := 7) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 7: Eliminating `_2 = move _1` When `_1` Is Read Later Erases Use-After-Move UB in Reverse Transport -/

noncomputable def progDseMoveLiveSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::dse_move_live_src"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progDseMoveLiveTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::dse_move_live_src"
    basicBlocks := [{
      statements := [
        .nop,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE7:** Eliminating a dead store `_2 = move _1` whose RHS
moves a live local `_1 ≠ _2` erases `deinitMovedPlace = true` use-after-move UB
at `_0 = copy _1` (`WellFormed pTgt ∧ ¬ WellFormed pSrc`), and is excluded by
`rvalueNoMoveExcept` in `isDseMoveFreeProgram`. -/
theorem ce_dse_move_live_src_reverse_unsound :
    isDseMoveFreeProgram progDseMoveLiveSrc progDseMoveLiveTgt = false ∧
    PositiveCanaryClaim progDseMoveLiveTgt
      { args := [u32Val 11] } (u32Val 11) ∧
    NegativeCanaryClaim progDseMoveLiveSrc
      { args := [u32Val 11] } .undefined .unsupported := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 5) rfl
  · exact negativeCanary_of_execFaults (fuel := 5) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 8: Non-Adjacent `DestinationPropagation` Hoisting Past an Intervening Reader Is Unsound -/

noncomputable def progDestHoistSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::destprop_hoist_past_reader"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨1, []⟩ (.use (.move ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progDestHoistTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::destprop_hoist_past_reader"
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)),
        .nop
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE8 (`dest_prop.rs:49-65` Live-Range Conflict):**
Propagating destination `_1` backwards into `_2 = _1 + 1` across an intervening
read `_0 = copy _1` changes the return value from `10_u32` to `11_u32`, and is
rejected by `isDestPropProgram`. -/
theorem ce_destprop_hoist_past_reader_unsound :
    isDestPropProgram progDestHoistSrc progDestHoistTgt = false ∧
    PositiveCanaryClaim progDestHoistSrc { args := [u32Val 10] } (u32Val 10) ∧
    PositiveCanaryClaim progDestHoistTgt { args := [u32Val 10] } (u32Val 11) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 6) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Constructive Witness 1: Self-Updating `DestinationPropagation` (`_tmp = _dst + 1; _dst = move _tmp ↦ _dst = _dst + 1; .nop`) -/

noncomputable def progDestSelfUpdateSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "witness::destprop_self_update"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨1, []⟩ (.use (.move ⟨2, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progDestSelfUpdateTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "witness::destprop_self_update"
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .nop,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def destSelfUpdateCert : ProgramDestPropCert := [{
  liveCert := [some [.liveUninit, .liveInit, .liveUninit]]
}]

/-- **Constructive Witness 1:** Because `evalStatement` evaluates `evalRvalue`
before `writePlace`, fusing `_2 = copy _1 + 1_u32; _1 = move _2` into the
in-place self-update `_1 = copy _1 + 1_u32; .nop` passes both `isDestPropProgram`
and `checkDestPropProgram` and returns `42_u32` on input `41_u32`. -/
theorem witness_destprop_self_update_exact :
    isDestPropProgram progDestSelfUpdateSrc progDestSelfUpdateTgt = true ∧
    checkDestPropProgram destSelfUpdateCert
      progDestSelfUpdateSrc progDestSelfUpdateTgt = true ∧
    PositiveCanaryClaim progDestSelfUpdateSrc
      { args := [u32Val 41] } (u32Val 42) ∧
    PositiveCanaryClaim progDestSelfUpdateTgt
      { args := [u32Val 41] } (u32Val 42) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 6) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Constructive Witness 2: End-to-End Post-`SimplifyCfg` Tail Pipeline (`CopyProp` -> `MoveHeadUnify` -> `DeadStoreElimination` -> `DestinationPropagation`) -/

/-- Two-variant `#[repr(u8)]` enum `enum TailTag { Two = 2, Five = 5 }`. -/
noncomputable def tailEnumU8Ty : EnumTy := {
  id := 17
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [2, 5]
}

/-- Parameterized multi-block program exercising all 4 post-`SimplifyCfg` stages
in sequence on `(x = 40_u32, tag = TailTag::Five)`:
- `bb0`: `SwitchInt(copy _1) [0 -> bb2, otherwise -> bb1]` (refining `_1` to
  `.liveNonZero` along `bb1`)
- `bb1`:
  1. `sCopyInt`: `_3 = copy _1` -> `.nop` (propagated by `CopyProp`, then
     eliminated by certified `DeadStoreElimination`)
  2. `sCopyEnum`: `_4 = copy _2` -> `.nop` (propagated into `Discriminant` by
     `CopyProp`, then eliminated by certified `DeadStoreElimination`)
  3. `sDiscr`: `_5 = Discriminant(_4)` -> `_5 = Discriminant(_2)` -> `.nop`
  4. `sDeadDiv`: `_7 = Div(100_u32, copy _3)` -> `_7 = Div(100_u32, copy _1)` ->
     `.nop` (certified non-zero unsigned division dead store!)
  5. `sMove₁; sMove₂`: `_6 = move _1; _8 = move _6 + 1_u32` ->
     `.nop; _8 = move _1 + 1_u32` (`MoveHeadUnify`)
  6. `sDest₁; sDest₂`: `_9 = copy _8 + 1_u32; _8 = move _9` ->
     `_8 = copy _8 + 1_u32; .nop` (`DestinationPropagation` self-update)
  7. `_0 = copy _8; Return`
- `bb2`: `_0 = const 0_u32; Return` -/
noncomputable def mkTailPipeProg (sCopyInt sCopyEnum sDiscr sDeadDiv
    sMove₁ sMove₂ sDest₁ sDest₂ : StatementKind) : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [
      u32Ty, u32Ty, .enum tailEnumU8Ty, u32Ty, .enum tailEnumU8Ty,
      u8Ty, u32Ty, u32Ty, u32Ty, u32Ty
    ]
    identity := "witness::post_simplifycfg_tail"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0, 2)]
          otherwise := 1
        }
      },
      {
        statements := [
          sCopyInt,
          sCopyEnum,
          sDiscr,
          sDeadDiv,
          sMove₁,
          sMove₂,
          sDest₁,
          sDest₂,
          .assign ⟨0, []⟩ (.use (.copy ⟨8, []⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def sTailCopyIntSrc : StatementKind :=
  .assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩))

noncomputable def sTailCopyEnumSrc : StatementKind :=
  .assign ⟨4, []⟩ (.use (.copy ⟨2, []⟩))

noncomputable def sTailDiscr₀ : StatementKind :=
  .assign ⟨5, []⟩ (.discriminant ⟨4, []⟩)
noncomputable def sTailDiscr₁ : StatementKind :=
  .assign ⟨5, []⟩ (.discriminant ⟨2, []⟩)

noncomputable def sTailDiv₀ : StatementKind :=
  .assign ⟨7, []⟩ (.binaryOp .div
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩) (.copy ⟨3, []⟩))
noncomputable def sTailDiv₁ : StatementKind :=
  .assign ⟨7, []⟩ (.binaryOp .div
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩) (.copy ⟨1, []⟩))

noncomputable def sTailMove₁Src : StatementKind :=
  .assign ⟨6, []⟩ (.use (.move ⟨1, []⟩))
noncomputable def sTailMove₂Src : StatementKind :=
  .assign ⟨8, []⟩ (.binaryOp .add (.move ⟨6, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
noncomputable def sTailMove₂Tgt : StatementKind :=
  .assign ⟨8, []⟩ (.binaryOp .add (.move ⟨1, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))

noncomputable def sTailDest₁Src : StatementKind :=
  .assign ⟨9, []⟩ (.binaryOp .add (.copy ⟨8, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
noncomputable def sTailDest₂Src : StatementKind :=
  .assign ⟨8, []⟩ (.use (.move ⟨9, []⟩))
noncomputable def sTailDest₁Tgt : StatementKind :=
  .assign ⟨8, []⟩ (.binaryOp .add (.copy ⟨8, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))

noncomputable def pTail₀ : Program :=
  mkTailPipeProg sTailCopyIntSrc sTailCopyEnumSrc sTailDiscr₀ sTailDiv₀
    sTailMove₁Src sTailMove₂Src sTailDest₁Src sTailDest₂Src

noncomputable def pTail₁ : Program :=
  mkTailPipeProg sTailCopyIntSrc sTailCopyEnumSrc sTailDiscr₁ sTailDiv₁
    sTailMove₁Src sTailMove₂Src sTailDest₁Src sTailDest₂Src

noncomputable def pTail₂ : Program :=
  mkTailPipeProg sTailCopyIntSrc sTailCopyEnumSrc sTailDiscr₁ sTailDiv₁
    .nop sTailMove₂Tgt sTailDest₁Src sTailDest₂Src

noncomputable def pTail₃ : Program :=
  mkTailPipeProg .nop .nop .nop .nop
    .nop sTailMove₂Tgt sTailDest₁Src sTailDest₂Src

noncomputable def pTail₄ : Program :=
  mkTailPipeProg .nop .nop .nop .nop
    .nop sTailMove₂Tgt sTailDest₁Tgt .nop

noncomputable def tailBlockAbsEnv : List AbsSlot := [
  .liveUninit, .liveInit, .liveInit, .liveUninit, .liveUninit,
  .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
]

noncomputable def tailAbsCert : ProgramAbsCert := [[
  some tailBlockAbsEnv,
  some tailBlockAbsEnv,
  some tailBlockAbsEnv
]]

noncomputable def tailDseCert : ProgramDseCert := [[
  some [
    .liveUninit, .liveInit, .liveInit, .liveUninit, .liveUninit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ],
  some [
    .liveUninit, .liveNonZero, .liveInit, .liveUninit, .liveUninit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ],
  some [
    .liveUninit, .liveInit, .liveInit, .liveUninit, .liveUninit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ]
]]

noncomputable def tailDestCert : ProgramDestPropCert := [{
  liveCert := [
    some tailBlockAbsEnv,
    some tailBlockAbsEnv,
    some tailBlockAbsEnv
  ]
}]

theorem witness_postSimplifyCfg_tail_pipeline_nonvacuous :
    isCopyPropProgram pTail₀ pTail₁ = true ∧
    checkCopyPropProgram tailAbsCert pTail₀ pTail₁ = true ∧
    isMoveHeadUnifyProgram pTail₁ pTail₂ = true ∧
    checkMoveHeadUnifyProgram tailAbsCert pTail₁ pTail₂ = true ∧
    isDseMoveFreeProgram pTail₂ pTail₃ = true ∧
    checkCertifiedDseProgram tailDseCert pTail₂ pTail₃ = true ∧
    isDestPropProgram pTail₃ pTail₄ = true ∧
    checkDestPropProgram tailDestCert pTail₃ pTail₄ = true ∧
    PositiveCanaryClaim pTail₀
      { args := [u32Val 40, .enumVal tailEnumU8Ty 1] } (u32Val 42) ∧
    PositiveCanaryClaim pTail₄
      { args := [u32Val 40, .enumVal tailEnumU8Ty 1] } (u32Val 42) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 16) rfl
  · exact positiveCanary_of_execReturns (fuel := 16) rfl

end VrustcFormal.F1_7
