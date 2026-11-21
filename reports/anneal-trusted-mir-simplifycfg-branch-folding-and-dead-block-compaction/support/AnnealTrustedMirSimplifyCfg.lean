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

namespace VrustcFormal.F1_5

open Trusted.MirAst Trusted.MirSemantics

/-!
# Direct `Trusted.MirSemantics` Bridge: `SimplifyCfg`, Constant & Uniform `SwitchInt` Folding, Acyclic `Goto` Threading, and Dead-Block Compaction (`VrustcFormal.F1_5`)

This module formalizes the control-flow simplification passes of
`compiler/rustc_mir_transform/src/simplify.rs` and constant `SwitchInt` branch
folding (`rust-lang/rust` commit `8144389c895da997dbdecaa635e41d6a50be6ffd`)
directly over Anneal's live TCB syntax (`Trusted.MirAst`) and small-step
operational semantics (`Trusted.MirSemantics` at `joshlf/anneal` commit
`c131b320eeeb26ef692e5afd5ec8db49ee518613`).

All public theorem statements reference strictly `Init.*`, `Trusted.MirAst.*`,
`Trusted.MirSemantics.*`, and pure definitions in `VrustcFormal.F1_5` (zero
surrogate MIR AST, zero `Anneal.*` references).

## Four Ground-Truth Semantic Findings Mechanized Directly on $M_{\text{anneal}}$

1. **Exact Bidirectional Stuttering Equivalence of `StripNops` and Ranked
   Acyclic `Goto`-Chain Threading (`↔` including `Diverges`):**
   - `SimplifyCfg::strip_nops` (`simplify.rs:321`) and rank-certified empty-block
     `Goto` forwarding (`SimplifyCfg::collapse_goto_chain`, `simplify.rs:235`,
     guarded by `ranks[next] < ranks[mid]` so pure empty `Goto` cycles cannot
     collapse to zero steps) alter execution step counts yet preserve
     `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, infinite `Diverges`,
     `SatisfiesPost`, `BodyVerified`, `ProgramVerified`, `CrateTheorem`, and
     `UnitTheorem` unconditionally in **both** directions (`↔`).

2. **Exact Unconditional Bidirectional Equivalence of Validated Constant
   `SwitchInt` Branch Folding (`↔`):**
   - Rewriting `TerminatorKind.switchInt (.constant c) targets` to
     `TerminatorKind.goto target` whenever `resolveConstSwitchTarget c targets =
     some target` (evaluating `evalConstLit` and sequential branch matching up to
     the first hit) is unconditionally bidirectionally equivalent (`↔`) across
     all $M_{\text{anneal}}$ judgments without any dataflow certificate. Naive
     constant folding that skips `evalConstLit` (e.g., on an invalid `bool` bit
     pattern `2`) erases `FaultKind.undefined` (`ce_const_switch_invalid_bool_unsound`).

3. **The `SimplifyCfg::simplify_branch` (`simplify.rs:126, 298`) Asymmetry on
   Uniform-Target `SwitchInt(discr, targets) ↦ Goto(t)`:**
   - Upstream `simplify.rs:299` explicitly warns: *"Removing a `SwitchInt`
     terminator may remove reads that result in UB, so we must not apply this
     optimization before borrowck or when `-Zmir-preserve-ub` is set."*
   - On $M_{\text{anneal}}$, collapsing `SwitchInt(discr, targets)` when all
     arm targets and `otherwise` equal `t` is **unconditionally forward-sound**
     for codegen (`WellFormed pSrc q → WellFormed pTgt q`), but **unsound for
     reverse VC transport** (`WellFormed pTgt q ↛ WellFormed pSrc q`) via three
     independent mechanisms:
     * uninitialized/dead `discr` read (`ce_uniform_switch_uninit_discr_unsound`),
     * `Operand.move` deinitialization (`deinitMovedPlace = true`) observed by a
       subsequent read (`ce_uniform_switch_move_deinit_unsound`), and
     * overflowing `caseBits` in `targets.branches`
       (`ce_uniform_switch_overflow_case_unsound`).
   - Pairing uniform-branch collapse with `checkUniformBranchCert` restores full
     bidirectional equivalence (`↔`).

4. **The Surprising Dead-Block Elimination Hazard (`SimplifyCfg::remove_dead_blocks`
   vs. `always_storage_live_locals` / `hasStorageAnnotation`):**
   - In `rustc_const_eval/src/interpret/stack.rs` and
     `Trusted.MirSemantics.initLocalsLoop`, a non-argument local `idx >
     argumentCount` starts `.dead` at function entry iff `hasStorageAnnotation
     body idx = true` across **all** blocks in `body.basicBlocks`—including
     CFG-unreachable blocks!
   - Deleting an unreachable block that held the sole `StorageLive(idx)` or
     `StorageDead(idx)` marker flips `hasStorageAnnotation` from `true` to
     `false`, silently promoting `idx` from entry-`.dead` to entry-`.live none`
     in reachable code (`ce_dead_block_elim_flips_always_storage_live_unsound`),
     and deleting an unreachable block with out-of-bounds `StorageLive(99)` flips
     `storageAnnotationsInBounds` (`ce_dead_block_elim_hides_oob_storage_marker_unsound`).
   - Dead-block compaction is **unconditionally forward-sound** (`pSrc → pTgt`),
     and pairing it with `checkDeadBlockStorageSafeProgram` (preserving
     `storageAnnotationsInBounds` and per-local `hasStorageAnnotation` for
     `idx > argumentCount`) restores full bidirectional equivalence (`↔`).
-/

/-! ## Part I: Structural Equality & Decidable CFG Transformation Relations -/

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
  | .continue_, .continue_ | .unreachable, .unreachable | .terminate, .terminate => true
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
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ => operandEq d₁ d₂ && switchTargetsEq ts₁ ts₂
  | .return_, .return_ => true
  | .unreachable, .unreachable => true
  | .unwindResume, .unwindResume => true
  | .assert c₁ e₁ m₁ t₁ u₁, .assert c₂ e₂ m₂ t₂ u₂ =>
    operandEq c₁ c₂ && (e₁ == e₂) && assertKindEq m₁ m₂ && Nat.beq t₁ t₂ && unwindActionEq u₁ u₂
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

/-! ### Pass 1: `StripNops` (`SimplifyCfg::strip_nops`, `simplify.rs:321`) -/

/-- Strip any subset (or all) of `StatementKind.nop` statements from a statement list. -/
noncomputable def isStripNopsStmts : List StatementKind → List StatementKind → Bool
  | [], [] => true
  | .nop :: ss₁, .nop :: ss₂ => isStripNopsStmts ss₁ ss₂
  | .nop :: ss₁, ss₂ => isStripNopsStmts ss₁ ss₂
  | s₁ :: ss₁, s₂ :: ss₂ => stmtEq s₁ s₂ && isStripNopsStmts ss₁ ss₂
  | _, _ => false

noncomputable def isStripNopsBlock (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    isStripNopsStmts b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isStripNopsBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ && listRel isStripNopsBlock b₁.basicBlocks b₂.basicBlocks

noncomputable def isStripNopsProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt && listRel isStripNopsBody pSrc.bodies pTgt.bodies

/-! ### Pass 2: Validated Constant `SwitchInt` Branch Folding -/

/-- Compile-time constant `SwitchInt` target resolver mirroring
`Trusted.MirSemantics.evalPrimitiveOperand` + `evalSwitchBranches` /
`evalBoolSwitchBranches`. Returns `some target` iff `c` is a valid primitive
scalar or `bool` constant and branch resolution succeeds without faulting. -/
noncomputable def resolveConstSwitchTarget (c : ConstOperand)
    (targets : SwitchTargets) : Option BasicBlockId :=
  if !isPrimitiveReadableTy c.ty then
    none
  else
    match evalConstLit c.ty c.lit with
    | .error _ => none
    | .ok (.scalar sv) =>
      match evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
      | .ok target => some target
      | .error _ => none
    | .ok (.bool b) =>
      match evalBoolSwitchBranches b targets.otherwise targets.branches with
      | .ok target => some target
      | .error _ => none
    | .ok _ => none

noncomputable def isConstBranchFoldTerm : TerminatorKind → TerminatorKind → Bool
  | .switchInt (.constant c) targets, .goto target =>
    match resolveConstSwitchTarget c targets with
    | some resolved => Nat.beq resolved target
    | none => false
  | t₁, t₂ => terminatorEq t₁ t₂

noncomputable def isConstBranchFoldBlock (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel stmtEq b₁.statements b₂.statements &&
    isConstBranchFoldTerm b₁.terminator b₂.terminator

noncomputable def isConstBranchFoldBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ && listRel isConstBranchFoldBlock b₁.basicBlocks b₂.basicBlocks

noncomputable def isConstBranchFoldProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt && listRel isConstBranchFoldBody pSrc.bodies pTgt.bodies

/-! ### Pass 3: Uniform-Target `SwitchInt -> Goto` Collapse (`SimplifyCfg::simplify_branch`, `simplify.rs:298`) -/

/-- True iff `targets.otherwise == target` and every `(val, brTarget)` in
`targets.branches` has `brTarget == target`. -/
noncomputable def allSwitchTargetsEq (targets : SwitchTargets)
    (target : BasicBlockId) : Bool :=
  Nat.beq targets.otherwise target &&
    targets.branches.all (fun br => Nat.beq br.2 target)

noncomputable def isUniformBranchCollapseTerm : TerminatorKind → TerminatorKind → Bool
  | .switchInt _ targets, .goto target => allSwitchTargetsEq targets target
  | t₁, t₂ => terminatorEq t₁ t₂

noncomputable def isUniformBranchCollapseBlock (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel stmtEq b₁.statements b₂.statements &&
    isUniformBranchCollapseTerm b₁.terminator b₂.terminator

noncomputable def isUniformBranchCollapseBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ && listRel isUniformBranchCollapseBlock b₁.basicBlocks b₂.basicBlocks

noncomputable def isUniformBranchCollapseProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt && listRel isUniformBranchCollapseBody pSrc.bodies pTgt.bodies

/-! ### Pass 4: Ranked Acyclic `Goto`-Chain Threading (`SimplifyCfg::collapse_goto_chain`, `simplify.rs:235`) -/

/-- Check whether `srcIdx` can step along zero or more strictly rank-decreasing
empty non-cleanup `Goto` blocks in `bSrc` to `dstIdx` within `fuel` hops.
Strict rank decrease (`ranks[next] < ranks[cur]`) statically rules out infinite
forwarding cycles while allowing arbitrary multi-hop DAG `Goto` chains. -/
noncomputable def reachesRankedEmptyGoto (bSrc : Body) (ranks : List Nat) :
    Nat → BasicBlockId → BasicBlockId → Bool
  | 0, cur, dst => Nat.beq cur dst
  | fuel + 1, cur, dst =>
    if Nat.beq cur dst then
      true
    else
      match Trusted.MirSemantics.getElem? bSrc.basicBlocks cur,
          Trusted.MirSemantics.getElem? ranks cur with
      | some bb, some rCur =>
        if !bb.cleanup && bb.statements.isEmpty then
          match bb.terminator with
          | .goto next =>
            match Trusted.MirSemantics.getElem? ranks next with
            | some rNext =>
              Nat.blt rNext rCur && reachesRankedEmptyGoto bSrc ranks fuel next dst
            | none => false
          | _ => false
        else
          false
      | _, _ => false

noncomputable def canThreadEdge (bSrc : Body) (ranks : List Nat)
    (srcTarget dstTarget : BasicBlockId) : Bool :=
  reachesRankedEmptyGoto bSrc ranks bSrc.basicBlocks.length srcTarget dstTarget

noncomputable def isAcyclicGotoThreadTerm (bSrc : Body) (ranks : List Nat) :
    TerminatorKind → TerminatorKind → Bool
  | .goto t₁, .goto t₂ => canThreadEdge bSrc ranks t₁ t₂
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ =>
    operandEq d₁ d₂ &&
      canThreadEdge bSrc ranks ts₁.otherwise ts₂.otherwise &&
      listRel (fun a b => (a.1 == b.1) && canThreadEdge bSrc ranks a.2 b.2)
        ts₁.branches ts₂.branches
  | t₁, t₂ => terminatorEq t₁ t₂

noncomputable def isAcyclicGotoThreadBlocks (bSrc : Body) (ranks : List Nat) :
    List BasicBlock → List BasicBlock → Bool :=
  listRel (fun b₁ b₂ =>
    (b₁.cleanup == b₂.cleanup) &&
      listRel stmtEq b₁.statements b₂.statements &&
      isAcyclicGotoThreadTerm bSrc ranks b₁.terminator b₂.terminator)

noncomputable def isAcyclicGotoThreadBody (ranks : List Nat) (bSrc bTgt : Body) : Bool :=
  bodyHeaderEq bSrc bTgt &&
    Nat.beq ranks.length bSrc.basicBlocks.length &&
    isAcyclicGotoThreadBlocks bSrc ranks bSrc.basicBlocks bTgt.basicBlocks

noncomputable def isAcyclicGotoThreadProgram (ranksList : List (List Nat))
    (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    Nat.beq ranksList.length pSrc.bodies.length &&
    listRel (fun rkPr bTgt => isAcyclicGotoThreadBody rkPr.1 rkPr.2 bTgt)
      (List.zip ranksList pSrc.bodies) pTgt.bodies

/-! ### Pass 5: Dead-Block Elimination & Bijective Reachable-Block Compaction (`SimplifyCfg::remove_dead_blocks`) -/

/-- Partial block-index map for one `Body`: `remap[srcIdx] = some tgtIdx` maps
reachable block `srcIdx` to `tgtIdx`; `none` deletes an unreachable block. -/
abbrev BlockRemap := List (Option BasicBlockId)

/-- Remap a live `BasicBlockId` via `remap`. Notice that if `srcTarget ≥
numSrcBlocks` (an out-of-bounds jump in `bSrc` that faults `.unsupported` at the
next step), mapping it to any out-of-bounds `tgtTarget ≥ numTgtBlocks` preserves
exact `.fault .unsupported` behavior, while in-bounds jumps must land in `remap`. -/
noncomputable def remapEdge (numSrcBlocks numTgtBlocks : Nat) (remap : BlockRemap)
    (srcTarget tgtTarget : BasicBlockId) : Bool :=
  if Nat.blt srcTarget numSrcBlocks then
    match Trusted.MirSemantics.getElem? remap srcTarget with
    | some (some mapped) => Nat.beq mapped tgtTarget && Nat.blt mapped numTgtBlocks
    | _ => false
  else
    !Nat.blt tgtTarget numTgtBlocks

noncomputable def remapOptEdge (numSrcBlocks numTgtBlocks : Nat) (remap : BlockRemap) :
    Option BasicBlockId → Option BasicBlockId → Bool
  | none, none => true
  | some s, some t => remapEdge numSrcBlocks numTgtBlocks remap s t
  | _, _ => false

noncomputable def remapUnwind (numSrcBlocks numTgtBlocks : Nat) (remap : BlockRemap) :
    UnwindAction → UnwindAction → Bool
  | .continue_, .continue_ | .unreachable, .unreachable | .terminate, .terminate => true
  | .cleanup s, .cleanup t => remapEdge numSrcBlocks numTgtBlocks remap s t
  | _, _ => false

noncomputable def remapTerminator (numSrcBlocks numTgtBlocks : Nat)
    (remap : BlockRemap) : TerminatorKind → TerminatorKind → Bool
  | .goto s, .goto t => remapEdge numSrcBlocks numTgtBlocks remap s t
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ =>
    operandEq d₁ d₂ &&
      remapEdge numSrcBlocks numTgtBlocks remap ts₁.otherwise ts₂.otherwise &&
      listRel (fun a b =>
        (a.1 == b.1) && remapEdge numSrcBlocks numTgtBlocks remap a.2 b.2)
        ts₁.branches ts₂.branches
  | .return_, .return_ => true
  | .unreachable, .unreachable => true
  | .unwindResume, .unwindResume => true
  | .assert c₁ e₁ m₁ s₁ u₁, .assert c₂ e₂ m₂ t₂ u₂ =>
    operandEq c₁ c₂ && (e₁ == e₂) && assertKindEq m₁ m₂ &&
      remapEdge numSrcBlocks numTgtBlocks remap s₁ t₂ &&
      remapUnwind numSrcBlocks numTgtBlocks remap u₁ u₂
  | .call f₁ as₁ d₁ s₁ u₁, .call f₂ as₂ d₂ t₂ u₂ =>
    Nat.beq f₁ f₂ && listRel operandEq as₁ as₂ && placeEq d₁ d₂ &&
      remapOptEdge numSrcBlocks numTgtBlocks remap s₁ t₂ &&
      remapUnwind numSrcBlocks numTgtBlocks remap u₁ u₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Check that `remap` maps `j` at most once (`countMappedTo remap j == 1` for
every `j < numTgtBlocks`, establishing a bijection between mapped source blocks
and `0 .. numTgtBlocks - 1`). -/
noncomputable def countMappedTo (j : BasicBlockId) : BlockRemap → Nat
  | [] => 0
  | some m :: rest => (if Nat.beq m j then 1 else 0) + countMappedTo j rest
  | none :: rest => countMappedTo j rest

noncomputable def allTgtBlocksCoveredOnce (remap : BlockRemap) : Nat → Bool
  | 0 => true
  | k + 1 => Nat.beq (countMappedTo k remap) 1 && allTgtBlocksCoveredOnce remap k

noncomputable def checkMappedBlocksLoop (bSrc bTgt : Body) (remap : BlockRemap) :
    Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    let okHere : Bool :=
      match Trusted.MirSemantics.getElem? remap idx with
      | none => false
      | some none => true
      | some (some j) =>
        match Trusted.MirSemantics.getElem? bTgt.basicBlocks j with
        | none => false
        | some bbTgt =>
          (bbSrc.cleanup == bbTgt.cleanup) &&
            listRel stmtEq bbSrc.statements bbTgt.statements &&
            remapTerminator bSrc.basicBlocks.length bTgt.basicBlocks.length
              remap bbSrc.terminator bbTgt.terminator
    okHere && checkMappedBlocksLoop bSrc bTgt remap (idx + 1) rest

noncomputable def isDeadBlockCompactionBody (remap : BlockRemap)
    (bSrc bTgt : Body) : Bool :=
  bodyHeaderEq bSrc bTgt &&
    Nat.beq remap.length bSrc.basicBlocks.length &&
    allTgtBlocksCoveredOnce remap bTgt.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then
       bTgt.basicBlocks.isEmpty
     else
       !bTgt.basicBlocks.isEmpty &&
         (match Trusted.MirSemantics.getElem? remap 0 with
          | some (some j₀) => Nat.beq j₀ 0
          | _ => false)) &&
    checkMappedBlocksLoop bSrc bTgt remap 0 bSrc.basicBlocks

noncomputable def isDeadBlockCompactionProgram (remapList : List BlockRemap)
    (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    Nat.beq remapList.length pSrc.bodies.length &&
    listRel (fun rmPr bTgt => isDeadBlockCompactionBody rmPr.1 rmPr.2 bTgt)
      (List.zip remapList pSrc.bodies) pTgt.bodies

/-! ## Part II: Decidable Certificates for Reverse VC-Transport (`pTgt → pSrc`) -/

/-! ### Certificate A: Dead-Block Storage-Annotation Preservation -/

/-- Check that `bSrc` and `bTgt` have identical `hasStorageAnnotation` bits for
all non-parameter locals `idx > bSrc.argumentCount` (`idx < bSrc.locals.length`). -/
noncomputable def preservesStorageAnnotationsLoop (bSrc bTgt : Body) : Nat → Bool
  | 0 => true
  | idx + 1 =>
    let okHere :=
      if Nat.ble idx bSrc.argumentCount then true
      else hasStorageAnnotation bSrc idx == hasStorageAnnotation bTgt idx
    okHere && preservesStorageAnnotationsLoop bSrc bTgt idx

noncomputable def checkDeadBlockStorageSafeBody (bSrc bTgt : Body) : Bool :=
  storageAnnotationsInBounds bSrc &&
    preservesStorageAnnotationsLoop bSrc bTgt bSrc.locals.length

noncomputable def checkDeadBlockStorageSafeProgram (pSrc pTgt : Program) : Bool :=
  listRel checkDeadBlockStorageSafeBody pSrc.bodies pTgt.bodies

/-! ### Certificate B: Uniform-Branch Read-Validity & No-Use-After-Move Certificate -/

noncomputable def isAlwaysInhabitedZst (ty : MirTy) : Bool :=
  match ty with
  | .unit => true
  | .enum ety => isZstEnumTy ety
  | _ => false

inductive AbsSlot where
  | liveInit
  | liveUninit
  | dead

noncomputable def absSlotImplies : AbsSlot → AbsSlot → Bool
  | _, .dead => true
  | .liveInit, .liveUninit => true
  | .liveUninit, .liveUninit => true
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

noncomputable def initAbsEnvLoop (body : Body) : Nat → List MirTy → List AbsSlot
  | _, [] => []
  | idx, ty :: rest => initAbsSlot body idx ty :: initAbsEnvLoop body (idx + 1) rest

/-- Validate that every branch literal in `branches` is well-formed for a
primitive `SwitchInt` discriminant of type `ty` (ruling out overflowing integer
case literals and non-`0`/`1` boolean case literals). -/
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

/-- Abstract check for a primitive `SwitchInt` discriminant that is being
collapsed to `Goto`: requires `isPrimitiveReadableTy ty` AND valid constant/liveInit
operand AND valid `targets.branches` literals. -/
noncomputable def stepCollapsedSwitchOperand (bodyLocals : List MirTy)
    (env : List AbsSlot) (discr : Operand) (targets : SwitchTargets) :
    Option (List AbsSlot) :=
  match discr with
  | .constant c =>
    match resolveConstSwitchTarget c targets with
    | some _ => some env
    | none => none
  | .copy p =>
    if !p.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some .liveInit =>
        if isPrimitiveReadableTy ty && validSwitchBranchesForTy ty targets.branches then
          some env
        else
          none
      | _, _ => none
  | .move p =>
    if !p.projection.isEmpty then none
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some .liveInit =>
        if isPrimitiveReadableTy ty && validSwitchBranchesForTy ty targets.branches then
          setElem? env p.localId .liveUninit
        else
          none
      | _, _ => none

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

noncomputable def stepAbsStmt (bodyLocals : List MirTy) (env : List AbsSlot) :
    StatementKind → Option (List AbsSlot)
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
        | some env₁ => setElem? env₁ dst.localId .liveInit
  | .unsupported => none

noncomputable def stepAbsStmts (bodyLocals : List MirTy) :
    List AbsSlot → List StatementKind → Option (List AbsSlot)
  | env, [] => some env
  | env, s :: ss =>
    match stepAbsStmt bodyLocals env s with
    | none => none
    | some env' => stepAbsStmts bodyLocals env' ss

noncomputable def checkEdgeTarget (numBlocks : Nat) (cert : BodyAbsCert)
    (exitEnv : List AbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? cert target with
    | some (some tgtEnv) => absEnvImplies exitEnv tgtEnv
    | _ => false

noncomputable def checkUniformBranchBlock (bSrc bTgt : Body) (cert : BodyAbsCert)
    (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      match stepAbsStmts bSrc.locals entryEnv bbSrc.statements with
      | none => false
      | some exitEnv =>
        let numBlocks := bSrc.basicBlocks.length
        match bbSrc.terminator, bbTgt.terminator with
        | .switchInt discr targets, .goto target =>
          match stepCollapsedSwitchOperand bSrc.locals exitEnv discr targets with
          | none => false
          | some afterDiscrEnv => checkEdgeTarget numBlocks cert afterDiscrEnv target
        | .goto target, .goto _ => checkEdgeTarget numBlocks cert exitEnv target
        | .return_, .return_ =>
          if bbSrc.cleanup then true
          else
            match Trusted.MirSemantics.getElem? exitEnv 0 with
            | some .liveInit => true
            | _ => false
        | .switchInt discr targets, .switchInt _ _ =>
          match stepAbsOperand bSrc.locals exitEnv discr with
          | none => false
          | some afterDiscrEnv =>
            checkEdgeTarget numBlocks cert afterDiscrEnv targets.otherwise &&
              targets.branches.all (fun br =>
                checkEdgeTarget numBlocks cert afterDiscrEnv br.2)
        | .unreachable, .unreachable
        | .unwindResume, .unwindResume
        | .assert _ _ _ _ _, .assert _ _ _ _ _
        | .call _ _ _ _ _, .call _ _ _ _ _
        | .unsupported, .unsupported => true
        | _, _ => false

noncomputable def checkUniformBranchBlocksLoop (bSrc bTgt : Body)
    (cert : BodyAbsCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkUniformBranchBlock bSrc bTgt cert idx bbSrc &&
      checkUniformBranchBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkUniformBranchBody (bSrc bTgt : Body)
    (cert : BodyAbsCert) : Bool :=
  Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) => absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkUniformBranchBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkUniformBranchProgram (pSrc pTgt : Program)
    (cert : ProgramAbsCert) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun bPr c => checkUniformBranchBody bPr.1 bPr.2 c)
      (List.zip pSrc.bodies pTgt.bodies) cert

/-! ### Stage 4 Private Helpers — Layer A: Reflection, List, & AST Equality -/

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

private theorem nat_beq_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact nat_beq_refl a

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

private theorem nat_sub_succ_lt {i n : Nat} (h : i < n) :
    n - i = (n - (i + 1)) + 1 := by
  induction n generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero i h)
  | succ m ih =>
    cases i with
    | zero => rfl
    | succ k =>
      have h1 : (m + 1) - (k + 1) = m - k := Nat.succ_sub_succ m k
      have h2 : (m + 1) - (k + 1 + 1) = m - (k + 1) := Nat.succ_sub_succ m (k + 1)
      rw [h1, h2]
      exact ih (Nat.lt_of_succ_lt_succ h)

private theorem bitvec_beq_eq {n : Nat} {a b : BitVec n}
    (h : (a == b) = true) : a = b :=
  eq_of_beq h

private theorem bitvec_bne_false_of_beq {n : Nat} {a b : BitVec n}
    (h : (a == b) = true) : (a != b) = false := by
  change (!(a == b)) = false
  rw [h]; rfl

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
  have hL : a.toByteArray.data.toList = b.toByteArray.data.toList := uint8_list_beq_eq h
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

private theorem getElem?_of_drop_eq_cons {α : Type} {xs rest : List α} {n : Nat} {x : α}
    (h : xs.drop n = x :: rest) :
    Trusted.MirSemantics.getElem? xs n = some x ∧ xs.drop (n + 1) = rest := by
  induction xs generalizing n with
  | nil =>
    cases n <;> cases h
  | cons a xs ih =>
    cases n with
    | zero =>
      injection h with h1 h2
      subst h1; subst h2
      exact ⟨rfl, rfl⟩
    | succ k =>
      exact ih h

private theorem le_of_drop_eq_nil {α : Type} {xs : List α} {n : Nat}
    (h : xs.drop n = []) : xs.length ≤ n := by
  induction xs generalizing n with
  | nil => exact Nat.zero_le n
  | cons _ xs ih =>
    cases n with
    | zero => cases h
    | succ k => exact Nat.succ_le_succ (ih h)

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

private theorem list_all_of_forall_getElem? {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = true) :
    xs.all p = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    dsimp [List.all]
    exact bool_and_intro (h 0 a rfl) (ih (fun i x hi => h (i + 1) x hi))

private theorem list_any_getElem? {α : Type} {p : α → Bool} {xs : List α}
    (hAny : xs.any p = true) :
    ∃ i x, Trusted.MirSemantics.getElem? xs i = some x ∧ p x = true := by
  induction xs with
  | nil => cases hAny
  | cons a xs ih =>
    dsimp [List.any] at hAny
    cases bool_or_true hAny with
    | inl ha => exact ⟨0, a, rfl, ha⟩
    | inr hxs =>
      let ⟨i, x, hi, hx⟩ := ih hxs
      exact ⟨i + 1, x, hi, hx⟩

private theorem list_any_of_getElem? {α : Type} {p : α → Bool} {xs : List α}
    {i : Nat} {x : α} (hGet : Trusted.MirSemantics.getElem? xs i = some x)
    (hp : p x = true) : xs.any p = true := by
  induction xs generalizing i with
  | nil => cases hGet
  | cons a xs ih =>
    dsimp [List.any]
    cases i with
    | zero =>
      injection hGet with hxa
      subst hxa
      rw [hp]; rfl
    | succ k =>
      rw [ih hGet]
      cases p a <;> rfl

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
      | succ k => exact ih h2 hTy

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
  | cons a xs ih =>
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

private theorem zip_length_eq {α β : Type} {xs : List α} {ys : List β}
    (h : xs.length = ys.length) :
    (List.zip xs ys).length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons a xs ih =>
    cases ys with
    | nil => cases h
    | cons b ys =>
      have hLen : xs.length = ys.length := Nat.succ.inj h
      change (List.zip xs ys).length + 1 = ys.length + 1
      rw [ih hLen]

private theorem getElem?_zip {α β : Type} {xs : List α} {ys : List β}
    {i : Nat} {x : α} {y : β}
    (hX : Trusted.MirSemantics.getElem? xs i = some x)
    (hY : Trusted.MirSemantics.getElem? ys i = some y) :
    Trusted.MirSemantics.getElem? (List.zip xs ys) i = some (x, y) := by
  induction xs generalizing ys i with
  | nil => cases hX
  | cons a xs ih =>
    cases ys with
    | nil => cases hY
    | cons b ys =>
      cases i with
      | zero =>
        injection hX with hxa
        injection hY with hyb
        subst hxa; subst hyb
        rfl
      | succ k =>
        dsimp [List.zip, List.zipWith, Trusted.MirSemantics.getElem?]
        exact ih hX hY

private theorem getElem?_of_getElem?_zip {α β : Type} {xs : List α} {ys : List β}
    {i : Nat} {x : α} {y : β}
    (hZ : Trusted.MirSemantics.getElem? (List.zip xs ys) i = some (x, y)) :
    Trusted.MirSemantics.getElem? xs i = some x ∧
      Trusted.MirSemantics.getElem? ys i = some y := by
  induction xs generalizing ys i with
  | nil =>
    dsimp [List.zip, List.zipWith] at hZ
    cases hZ
  | cons a xs ih =>
    cases ys with
    | nil =>
      dsimp [List.zip, List.zipWith] at hZ
      cases hZ
    | cons b ys =>
      dsimp [List.zip, List.zipWith] at hZ
      cases i with
      | zero =>
        injection hZ with hEq
        injection hEq with hxa hyb
        subst hxa; subst hyb
        exact ⟨rfl, rfl⟩
      | succ k =>
        exact ih hZ

private theorem listRel_zip_left_rel {α β γ : Type}
    {rel : α → β → γ → Bool} {auxs : List α} {xs : List β} {ys : List γ}
    (hLen : auxs.length = xs.length)
    (hRel : listRel (fun pr y => rel pr.1 pr.2 y) (List.zip auxs xs) ys = true) :
    xs.length = ys.length ∧
    (∀ i x, Trusted.MirSemantics.getElem? xs i = some x →
      ∃ a y, Trusted.MirSemantics.getElem? auxs i = some a ∧
        Trusted.MirSemantics.getElem? ys i = some y ∧
        rel a x y = true) ∧
    (∀ i, Trusted.MirSemantics.getElem? xs i = none ↔
      Trusted.MirSemantics.getElem? ys i = none) := by
  have hZLen : (List.zip auxs xs).length = ys.length := listRel_length hRel
  rw [zip_length_eq hLen] at hZLen
  refine ⟨hZLen, ?_, ?_⟩
  · intro i x hX
    have hiAux : i < auxs.length := by
      rw [hLen]
      exact getElem?_some_lt hX
    let ⟨a, hA⟩ := getElem?_some_of_lt auxs i hiAux
    have hZ := getElem?_zip hA hX
    let ⟨y, hY, hR⟩ := listRel_getElem?_left hRel hZ
    exact ⟨a, y, hA, hY, hR⟩
  · intro i
    constructor
    · intro hN
      have hGe : ys.length ≤ i := by
        rw [← hZLen]
        cases Nat.lt_or_ge i xs.length with
        | inr hge => exact hge
        | inl hlt =>
          let ⟨x, hx⟩ := getElem?_some_of_lt xs i hlt
          rw [hN] at hx; cases hx
      exact getElem?_none_of_ge hGe
    · intro hN
      have hGe : xs.length ≤ i := by
        rw [hZLen]
        cases Nat.lt_or_ge i ys.length with
        | inr hge => exact hge
        | inl hlt =>
          let ⟨y, hy⟩ := getElem?_some_of_lt ys i hlt
          rw [hN] at hy; cases hy
      exact getElem?_none_of_ge hGe

private theorem intWidth_beq_eq {a b : IntWidth}
    (h : IntWidth.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem intWidth_beq_refl (a : IntWidth) : IntWidth.beq a a = true := by
  cases a <;> rfl

private theorem mutability_beq_eq {a b : Mutability}
    (h : Mutability.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

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

/-! ### Stage 4 Private Helpers — Layer B: Simulation & Stuttering Lifting -/

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

private theorem reaches_trans {p : Program} {s₁ s₂ s₃ : State}
    (h1 : Reaches p s₁ s₂) (h2 : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction h2 with
  | refl => exact h1
  | tail _ hSt ih => exact Reaches.tail ih hSt

private theorem iterState_eq_of_trace {p : Program} {s₀ : State}
    {trace : Nat → State} (h0 : trace 0 = s₀)
    (hStep : ∀ n, Step p (trace n) (.step (trace (n + 1)))) :
    ∀ n, iterState p s₀ n = trace n := by
  intro n
  induction n with
  | zero => rw [h0]; rfl
  | succ k ih =>
    dsimp [iterState]
    rw [ih, step_iff_evalStep.mp (hStep k)]

private theorem reaches_eq_of_evalStep_eq {p1 p2 : Program}
    (hStep : ∀ s, evalStep p1 0 s = evalStep p2 0 s)
    {s1 s2 : State} :
    Reaches p1 s1 s2 ↔ Reaches p2 s1 s2 := by
  constructor
  · intro hR
    induction hR with
    | refl => exact Reaches.refl s1
    | tail _ hSt ih =>
      have hE := step_iff_evalStep.mp hSt
      rw [hStep] at hE
      exact Reaches.tail ih (step_iff_evalStep.mpr hE)
  · intro hR
    induction hR with
    | refl => exact Reaches.refl s1
    | tail _ hSt ih =>
      have hE := step_iff_evalStep.mp hSt
      rw [← hStep] at hE
      exact Reaches.tail ih (step_iff_evalStep.mpr hE)

private theorem exact_step_eq_query_iff {pSrc pTgt : Program} {q : Query}
    (hInit : initState pSrc q = initState pTgt q)
    (hStep : ∀ s, evalStep pSrc 0 s = evalStep pTgt 0 s) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hResIff : ∀ res, ReachesResult pTgt q res ↔ ReachesResult pSrc q res := by
    intro res
    unfold ReachesResult
    rw [hInit]
    cases initState pTgt q with
    | error _ => exact ⟨fun h => h, fun h => h⟩
    | ok s₀ =>
      constructor
      · intro h
        let ⟨s, hR, hSt⟩ := h
        have hE : evalStep pSrc 0 s = res := by
          rw [hStep]; exact step_iff_evalStep.mp hSt
        exact ⟨s, (reaches_eq_of_evalStep_eq hStep).mpr hR, step_iff_evalStep.mpr hE⟩
      · intro h
        let ⟨s, hR, hSt⟩ := h
        have hE : evalStep pTgt 0 s = res := by
          rw [← hStep]; exact step_iff_evalStep.mp hSt
        exact ⟨s, (reaches_eq_of_evalStep_eq hStep).mp hR, step_iff_evalStep.mpr hE⟩
  refine ⟨?_, fun out => hResIff (.done out), fun k => hResIff (.fault k), ?_⟩
  · constructor
    · intro hW
      let ⟨⟨s₀, hOk, _⟩, hNF⟩ := hW
      rw [← hInit] at hOk
      exact ⟨⟨s₀, hOk, fun _ _ => ⟨0, rfl⟩⟩, fun k hF => hNF k ((hResIff (.fault k)).mpr hF)⟩
    · intro hW
      let ⟨⟨s₀, hOk, _⟩, hNF⟩ := hW
      rw [hInit] at hOk
      exact ⟨⟨s₀, hOk, fun _ _ => ⟨0, rfl⟩⟩, fun k hF => hNF k ((hResIff (.fault k)).mp hF)⟩
  · constructor
    · intro hD
      let ⟨s₀, hOk, tr, h0, hSt⟩ := hD
      rw [← hInit] at hOk
      refine ⟨s₀, hOk, tr, h0, fun n => step_iff_evalStep.mpr ?_⟩
      rw [hStep]
      exact step_iff_evalStep.mp (hSt n)
    · intro hD
      let ⟨s₀, hOk, tr, h0, hSt⟩ := hD
      rw [hInit] at hOk
      refine ⟨s₀, hOk, tr, h0, fun n => step_iff_evalStep.mpr ?_⟩
      rw [← hStep]
      exact step_iff_evalStep.mp (hSt n)

private noncomputable def SyncStepOutcome (pSrc pTgt : Program)
    (R : Nat → State → State → Prop) (s t : State) : Prop :=
  (∃ k' s' t', evalStep pSrc 0 s = .step s' ∧ evalStep pTgt 0 t = .step t' ∧ R k' s' t') ∨
  (∃ out, evalStep pSrc 0 s = .done out ∧ evalStep pTgt 0 t = .done out) ∨
  (∃ fk, evalStep pSrc 0 s = .fault fk ∧ evalStep pTgt 0 t = .fault fk)

private noncomputable def StutterStepOutcome (pSrc pTgt : Program)
    (R : Nat → State → State → Prop) (k : Nat) (s t : State) : Prop :=
  (∃ k' s', k = k' + 1 ∧ evalStep pSrc 0 s = .step s' ∧ R k' s' t) ∨
  SyncStepOutcome pSrc pTgt R s t

private theorem unstutter_src {pSrc pTgt : Program}
    {R : Nat → State → State → Prop}
    (hStep : ∀ k s t, R k s t → StutterStepOutcome pSrc pTgt R k s t) :
    ∀ k s t, R k s t →
      ∃ sSync, Reaches pSrc s sSync ∧ SyncStepOutcome pSrc pTgt R sSync t := by
  intro k
  induction k with
  | zero =>
    intro s t hR
    cases hStep 0 s t hR with
    | inl hSil =>
      let ⟨_, _, hEqK, _, _⟩ := hSil
      cases hEqK
    | inr hSync =>
      exact ⟨s, Reaches.refl s, hSync⟩
  | succ k1 ih =>
    intro s t hR
    cases hStep (k1 + 1) s t hR with
    | inl hSil =>
      let ⟨k', s', hEqK, hEv, hRk'⟩ := hSil
      injection hEqK with hK
      subst hK
      let ⟨sSync, hRch, hSync⟩ := ih s' t hRk'
      exact ⟨sSync,
        reaches_trans (Reaches.tail (Reaches.refl s) (step_iff_evalStep.mpr hEv)) hRch,
        hSync⟩
    | inr hSync =>
      exact ⟨s, Reaches.refl s, hSync⟩

private theorem stutter_bisim_lift {pSrc pTgt : Program} {q : Query}
    {R : Nat → State → State → Prop}
    (hInitErr : ∀ k, initState pSrc q = .error k ↔ initState pTgt q = .error k)
    (hInitOk : ∀ s₀ t₀, initState pSrc q = .ok s₀ → initState pTgt q = .ok t₀ →
      ∃ k₀, R k₀ s₀ t₀)
    (hStep : ∀ k s t, R k s t → StutterStepOutcome pSrc pTgt R k s t) :
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
    · intro out; unfold Behavior ReachesResult; rw [hInitTgt, hInitSrc]
    · intro k; unfold ReachesResult; rw [hInitTgt, hInitSrc]
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
      let ⟨k₀, hRel0⟩ := hInitOk s₀ t₀ hInitSrc hInitTgt
      have hSrcToTgtReach : ∀ s, Reaches pSrc s₀ s →
          ∃ k t, Reaches pTgt t₀ t ∧ R k s t := by
        intro s hRs
        induction hRs with
        | refl => exact ⟨k₀, t₀, Reaches.refl t₀, hRel0⟩
        | tail _ hSt ih =>
          let ⟨k2, t2, hRt2, hR2⟩ := ih
          have hEvSrc : evalStep pSrc 0 _ = .step _ := step_iff_evalStep.mp hSt
          cases hStep k2 _ t2 hR2 with
          | inl hSil =>
            let ⟨k', s', _, hEvS, hRk'⟩ := hSil
            rw [hEvSrc] at hEvS
            injection hEvS with hEqS; subst hEqS
            exact ⟨k', t2, hRt2, hRk'⟩
          | inr hSync =>
            cases hSync with
            | inl hBoth =>
              let ⟨k', s', t', hEvS, hEvT, hRk'⟩ := hBoth
              rw [hEvSrc] at hEvS
              injection hEvS with hEqS; subst hEqS
              exact ⟨k', t', Reaches.tail hRt2 (step_iff_evalStep.mpr hEvT), hRk'⟩
            | inr hTerm =>
              cases hTerm with
              | inl hDone =>
                let ⟨_, hEvS, _⟩ := hDone
                rw [hEvSrc] at hEvS; cases hEvS
              | inr hFlt =>
                let ⟨_, hEvS, _⟩ := hFlt
                rw [hEvSrc] at hEvS; cases hEvS
      have hTgtToSrcReach : ∀ t, Reaches pTgt t₀ t →
          ∃ k s, Reaches pSrc s₀ s ∧ R k s t := by
        intro t hRt
        induction hRt with
        | refl => exact ⟨k₀, s₀, Reaches.refl s₀, hRel0⟩
        | tail _ hSt ih =>
          let ⟨k2, s2, hRs2, hR2⟩ := ih
          have hEvTgt : evalStep pTgt 0 _ = .step _ := step_iff_evalStep.mp hSt
          let ⟨sSync, hRsSync, hSync⟩ := unstutter_src hStep k2 s2 _ hR2
          have hRsFull : Reaches pSrc s₀ sSync := reaches_trans hRs2 hRsSync
          cases hSync with
          | inl hBoth =>
            let ⟨k', s', t', hEvS, hEvT, hRk'⟩ := hBoth
            rw [hEvTgt] at hEvT
            injection hEvT with hEqT; subst hEqT
            exact ⟨k', s', Reaches.tail hRsFull (step_iff_evalStep.mpr hEvS), hRk'⟩
          | inr hTerm =>
            cases hTerm with
            | inl hDone =>
              let ⟨_, _, hEvT⟩ := hDone
              rw [hEvTgt] at hEvT; cases hEvT
            | inr hFlt =>
              let ⟨_, _, hEvT⟩ := hFlt
              rw [hEvTgt] at hEvT; cases hEvT
      have hBehIff : ∀ out, Behavior pTgt q out ↔ Behavior pSrc q out := by
        intro out
        unfold Behavior ReachesResult
        rw [hInitTgt, hInitSrc]
        constructor
        · intro h
          let ⟨t, hRt, hStT⟩ := h
          have hEvTgt : evalStep pTgt 0 t = .done out := step_iff_evalStep.mp hStT
          let ⟨k2, s2, hRs2, hR2⟩ := hTgtToSrcReach t hRt
          let ⟨sSync, hRsSync, hSync⟩ := unstutter_src hStep k2 s2 t hR2
          cases hSync with
          | inl hBoth =>
            let ⟨_, _, _, _, hEvT, _⟩ := hBoth
            rw [hEvTgt] at hEvT; cases hEvT
          | inr hTerm =>
            cases hTerm with
            | inl hDone =>
              let ⟨out', hEvS, hEvT⟩ := hDone
              rw [hEvTgt] at hEvT; injection hEvT with hEq; subst hEq
              exact ⟨sSync, reaches_trans hRs2 hRsSync, step_iff_evalStep.mpr hEvS⟩
            | inr hFlt =>
              let ⟨_, _, hEvT⟩ := hFlt
              rw [hEvTgt] at hEvT; cases hEvT
        · intro h
          let ⟨s, hRs, hStS⟩ := h
          have hEvSrc : evalStep pSrc 0 s = .done out := step_iff_evalStep.mp hStS
          let ⟨k2, t2, hRt2, hR2⟩ := hSrcToTgtReach s hRs
          cases hStep k2 s t2 hR2 with
          | inl hSil =>
            let ⟨_, _, _, hEvS, _⟩ := hSil
            rw [hEvSrc] at hEvS; cases hEvS
          | inr hSync =>
            cases hSync with
            | inl hBoth =>
              let ⟨_, _, _, hEvS, _, _⟩ := hBoth
              rw [hEvSrc] at hEvS; cases hEvS
            | inr hTerm =>
              cases hTerm with
              | inl hDone =>
                let ⟨out', hEvS, hEvT⟩ := hDone
                rw [hEvSrc] at hEvS; injection hEvS with hEq; subst hEq
                exact ⟨t2, hRt2, step_iff_evalStep.mpr hEvT⟩
              | inr hFlt =>
                let ⟨_, hEvS, _⟩ := hFlt
                rw [hEvSrc] at hEvS; cases hEvS
      have hFaultIff : ∀ fk, ReachesResult pTgt q (.fault fk) ↔
          ReachesResult pSrc q (.fault fk) := by
        intro fk
        unfold ReachesResult
        rw [hInitTgt, hInitSrc]
        constructor
        · intro h
          let ⟨t, hRt, hStT⟩ := h
          have hEvTgt : evalStep pTgt 0 t = .fault fk := step_iff_evalStep.mp hStT
          let ⟨k2, s2, hRs2, hR2⟩ := hTgtToSrcReach t hRt
          let ⟨sSync, hRsSync, hSync⟩ := unstutter_src hStep k2 s2 t hR2
          cases hSync with
          | inl hBoth =>
            let ⟨_, _, _, _, hEvT, _⟩ := hBoth
            rw [hEvTgt] at hEvT; cases hEvT
          | inr hTerm =>
            cases hTerm with
            | inl hDone =>
              let ⟨_, _, hEvT⟩ := hDone
              rw [hEvTgt] at hEvT; cases hEvT
            | inr hFlt =>
              let ⟨fk', hEvS, hEvT⟩ := hFlt
              rw [hEvTgt] at hEvT; injection hEvT with hEq; subst hEq
              exact ⟨sSync, reaches_trans hRs2 hRsSync, step_iff_evalStep.mpr hEvS⟩
        · intro h
          let ⟨s, hRs, hStS⟩ := h
          have hEvSrc : evalStep pSrc 0 s = .fault fk := step_iff_evalStep.mp hStS
          let ⟨k2, t2, hRt2, hR2⟩ := hSrcToTgtReach s hRs
          cases hStep k2 s t2 hR2 with
          | inl hSil =>
            let ⟨_, _, _, hEvS, _⟩ := hSil
            rw [hEvSrc] at hEvS; cases hEvS
          | inr hSync =>
            cases hSync with
            | inl hBoth =>
              let ⟨_, _, _, hEvS, _, _⟩ := hBoth
              rw [hEvSrc] at hEvS; cases hEvS
            | inr hTerm =>
              cases hTerm with
              | inl hDone =>
                let ⟨_, hEvS, _⟩ := hDone
                rw [hEvSrc] at hEvS; cases hEvS
              | inr hFlt =>
                let ⟨fk', hEvS, hEvT⟩ := hFlt
                rw [hEvSrc] at hEvS; injection hEvS with hEq; subst hEq
                exact ⟨t2, hRt2, step_iff_evalStep.mpr hEvT⟩
      refine ⟨?_, hBehIff, hFaultIff, ?_⟩
      · constructor
        · intro hW
          exact ⟨⟨s₀, hInitSrc, fun _ _ => ⟨0, rfl⟩⟩, fun fk hF => hW.2 fk ((hFaultIff fk).mpr hF)⟩
        · intro hW
          exact ⟨⟨t₀, hInitTgt, fun _ _ => ⟨0, rfl⟩⟩, fun fk hF => hW.2 fk ((hFaultIff fk).mp hF)⟩
      · constructor
        · -- Diverges pTgt q → Diverges pSrc q via canonical `iterState`.
          intro hDivTgt
          let ⟨t₀', hOkT, trTgt, hT0, hTStep⟩ := hDivTgt
          rw [hInitTgt] at hOkT; injection hOkT with hEqT; subst hEqT
          have hIterTgtEq := iterState_eq_of_trace hT0 hTStep
          have hTgtAlwaysSteps : ∀ j,
              evalStep pTgt 0 (iterState pTgt t₀ j) = .step (iterState pTgt t₀ (j + 1)) := by
            intro j
            rw [hIterTgtEq j, hIterTgtEq (j + 1)]
            exact step_iff_evalStep.mp (hTStep j)
          have hInvSrc : ∀ m, ∃ j k, R k (iterState pSrc s₀ m) (iterState pTgt t₀ j) := by
            intro m
            induction m with
            | zero => exact ⟨0, k₀, hRel0⟩
            | succ m1 ih =>
              let ⟨j, k, hR⟩ := ih
              cases hStep k (iterState pSrc s₀ m1) (iterState pTgt t₀ j) hR with
              | inl hSil =>
                let ⟨k', s', _, hEvS, hRk'⟩ := hSil
                dsimp [iterState]
                rw [hEvS]
                exact ⟨j, k', hRk'⟩
              | inr hSync =>
                have hEvTgtJ := hTgtAlwaysSteps j
                cases hSync with
                | inl hBoth =>
                  let ⟨k', s', t', hEvS, hEvT, hRk'⟩ := hBoth
                  rw [hEvTgtJ] at hEvT; injection hEvT with hEqT'; subst hEqT'
                  dsimp [iterState]
                  rw [hEvS]
                  exact ⟨j + 1, k', hRk'⟩
                | inr hTerm =>
                  cases hTerm with
                  | inl hDone =>
                    let ⟨_, _, hEvT⟩ := hDone
                    rw [hEvTgtJ] at hEvT; cases hEvT
                  | inr hFlt =>
                    let ⟨_, _, hEvT⟩ := hFlt
                    rw [hEvTgtJ] at hEvT; cases hEvT
          refine ⟨s₀, hInitSrc, iterState pSrc s₀, rfl, ?_⟩
          intro m
          let ⟨j, k, hR⟩ := hInvSrc m
          have hEvTgtJ := hTgtAlwaysSteps j
          cases hStep k (iterState pSrc s₀ m) (iterState pTgt t₀ j) hR with
          | inl hSil =>
            let ⟨_, s', _, hEvS, _⟩ := hSil
            apply step_iff_evalStep.mpr
            dsimp [iterState]
            rw [hEvS]
          | inr hSync =>
            cases hSync with
            | inl hBoth =>
              let ⟨_, s', _, hEvS, _, _⟩ := hBoth
              apply step_iff_evalStep.mpr
              dsimp [iterState]
              rw [hEvS]
            | inr hTerm =>
              cases hTerm with
              | inl hDone =>
                let ⟨_, _, hEvT⟩ := hDone
                rw [hEvTgtJ] at hEvT; cases hEvT
              | inr hFlt =>
                let ⟨_, _, hEvT⟩ := hFlt
                rw [hEvTgtJ] at hEvT; cases hEvT
        · -- Diverges pSrc q → Diverges pTgt q via canonical `iterState`.
          intro hDivSrc
          let ⟨s₀', hOkS, trSrc, hS0, hSStep⟩ := hDivSrc
          rw [hInitSrc] at hOkS; injection hOkS with hEqS; subst hEqS
          have hIterSrcEq := iterState_eq_of_trace hS0 hSStep
          have hSrcAlwaysSteps : ∀ i,
              evalStep pSrc 0 (iterState pSrc s₀ i) = .step (iterState pSrc s₀ (i + 1)) := by
            intro i
            rw [hIterSrcEq i, hIterSrcEq (i + 1)]
            exact step_iff_evalStep.mp (hSStep i)
          have hAdvance : ∀ k i t, R k (iterState pSrc s₀ i) t →
              ∃ i' k' t', evalStep pTgt 0 t = .step t' ∧ R k' (iterState pSrc s₀ i') t' := by
            intro k
            induction k with
            | zero =>
              intro i t hR
              have hEvSrcI := hSrcAlwaysSteps i
              cases hStep 0 (iterState pSrc s₀ i) t hR with
              | inl hSil =>
                let ⟨_, _, hEqK, _, _⟩ := hSil
                cases hEqK
              | inr hSync =>
                cases hSync with
                | inl hBoth =>
                  let ⟨k', s', t', hEvS, hEvT, hRk'⟩ := hBoth
                  rw [hEvSrcI] at hEvS; injection hEvS with hEqS'; subst hEqS'
                  exact ⟨i + 1, k', t', hEvT, hRk'⟩
                | inr hTerm =>
                  cases hTerm with
                  | inl hDone =>
                    let ⟨_, hEvS, _⟩ := hDone
                    rw [hEvSrcI] at hEvS; cases hEvS
                  | inr hFlt =>
                    let ⟨_, hEvS, _⟩ := hFlt
                    rw [hEvSrcI] at hEvS; cases hEvS
            | succ k1 ih =>
              intro i t hR
              have hEvSrcI := hSrcAlwaysSteps i
              cases hStep (k1 + 1) (iterState pSrc s₀ i) t hR with
              | inl hSil =>
                let ⟨k', s', hEqK, hEvS, hRk'⟩ := hSil
                injection hEqK with hK; subst hK
                rw [hEvSrcI] at hEvS; injection hEvS with hEqS'; subst hEqS'
                exact ih (i + 1) t hRk'
              | inr hSync =>
                cases hSync with
                | inl hBoth =>
                  let ⟨k', s', t', hEvS, hEvT, hRk'⟩ := hBoth
                  rw [hEvSrcI] at hEvS; injection hEvS with hEqS'; subst hEqS'
                  exact ⟨i + 1, k', t', hEvT, hRk'⟩
                | inr hTerm =>
                  cases hTerm with
                  | inl hDone =>
                    let ⟨_, hEvS, _⟩ := hDone
                    rw [hEvSrcI] at hEvS; cases hEvS
                  | inr hFlt =>
                    let ⟨_, hEvS, _⟩ := hFlt
                    rw [hEvSrcI] at hEvS; cases hEvS
          have hInvTgt : ∀ n, ∃ i k, R k (iterState pSrc s₀ i) (iterState pTgt t₀ n) := by
            intro n
            induction n with
            | zero => exact ⟨0, k₀, hRel0⟩
            | succ n1 ih =>
              let ⟨i, k, hR⟩ := ih
              let ⟨i', k', t', hEvT, hRk'⟩ := hAdvance k i (iterState pTgt t₀ n1) hR
              dsimp [iterState]
              rw [hEvT]
              exact ⟨i', k', hRk'⟩
          refine ⟨t₀, hInitTgt, iterState pTgt t₀, rfl, ?_⟩
          intro n
          let ⟨i, k, hR⟩ := hInvTgt n
          let ⟨_, _, t', hEvT, _⟩ := hAdvance k i (iterState pTgt t₀ n) hR
          apply step_iff_evalStep.mpr
          dsimp [iterState]
          rw [hEvT]

private theorem bisim_lift_disj {pSrc pTgt : Program} {q : Query}
    {R : State → State → Prop}
    (hInitErr : ∀ k, initState pSrc q = .error k ↔ initState pTgt q = .error k)
    (hInitOk : ∀ s₀ t₀, initState pSrc q = .ok s₀ → initState pTgt q = .ok t₀ →
      R s₀ t₀)
    (hStep : ∀ s t, R s t →
      (∃ s' t', evalStep pSrc 0 s = .step s' ∧ evalStep pTgt 0 t = .step t' ∧ R s' t') ∨
      (∃ out, evalStep pSrc 0 s = .done out ∧ evalStep pTgt 0 t = .done out) ∨
      (∃ fk, evalStep pSrc 0 s = .fault fk ∧ evalStep pTgt 0 t = .fault fk)) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  apply stutter_bisim_lift (R := fun _ s t => R s t) hInitErr
    (fun s₀ t₀ h1 h2 => ⟨0, hInitOk s₀ t₀ h1 h2⟩)
  intro _ s t hR
  right
  cases hStep s t hR with
  | inl hSt =>
    let ⟨s', t', h1, h2, hR'⟩ := hSt
    left; exact ⟨0, s', t', h1, h2, hR'⟩
  | inr hRest => right; exact hRest

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
  let ⟨_, hEval2, _⟩ := hStep _ _ _ (hInv n) hEval1
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
      let ⟨_, hST, _⟩ := (hStep s t hRel).1 s' hEvalSrc
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
        let ⟨_, hST, _⟩ := (hStep s t hRel).1 s' hEvalSrc
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
      | step _ =>
        apply step_iff_evalStep.mpr
        dsimp [iterState]
        rw [hEvalSrc]
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
      injection hTy with hEq
      subst hEq
      rfl
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
      cases hZero : Nat.beq base 0 with
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
      | none =>
        rw [hNone.mp hB1]
      | some b1 =>
        let ⟨b2, hB2, hBHdr, hEmpty, hSt, hLocsLoop⟩ := hSome b1 hB1
        let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
        rw [hB2]
        dsimp
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

private noncomputable def PrivFullSemanticEquiv (pSrc pTgt : Program) : Prop :=
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

private noncomputable def PrivForwardCodegenRefines (pSrc pTgt : Program) : Prop :=
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
    PrivFullSemanticEquiv pSrc pTgt := by
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
      (storageAnnotationsInBounds bSrc = true → storageAnnotationsInBounds bTgt = true))
    (hQuery : ∀ q,
      WellFormed pSrc q →
      WellFormed pTgt q ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (Diverges pTgt q ↔ Diverges pSrc q))
    (hEntryQuery : ∀ defId args,
      WellFormed (entryProgForBody pSrc defId) { args := args } →
      WellFormed (entryProgForBody pTgt defId) { args := args }) :
    PrivForwardCodegenRefines pSrc pTgt := by
  let ⟨hPw, hVer, _, _⟩ := programHeaderEq_elim hHdr
  refine ⟨hQuery, ?_, ?_⟩
  · intro q post hSat
    let ⟨hWfT, hBehIff, _⟩ := hQuery q hSat.1
    exact ⟨hWfT, fun out hB => hSat.2 out ((hBehIff out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hBS hBT hVerS
    let ⟨hBHdr, hEmpty, hStImp⟩ := hBodyFields defId bSrc bTgt hBS hBT
    let ⟨hArg, hLoc, hUns, hId⟩ := bodyHeaderEq_elim hBHdr
    have hAdmS : BodyStaticAdmitted pSrc bSrc = true := hVerS.2.1
    have hStSrc : storageAnnotationsInBounds bSrc = true := by
      unfold BodyStaticAdmitted at hAdmS
      let ⟨h123456, _⟩ := bool_and_true hAdmS
      let ⟨_, hStS⟩ := bool_and_true h123456
      exact hStS
    have hStEq : storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt := by
      rw [hStSrc, hStImp hStSrc]
    have hAdm := bodyStaticAdmitted_eq_of_fields hPw hVer hArg hLoc hId hEmpty hStEq
    refine ⟨hBT, by rw [← hAdm]; exact hAdmS, ?_⟩
    intro args hArgs hPre
    have hArgsS : ValidEntryArgs bSrc args := by
      unfold ValidEntryArgs; rw [hArg, hLoc]; exact hArgs
    have hPreS : bSrc.isUnsafe = true → safetyPre args := by
      rw [hUns]; exact hPre
    exact hEntryQuery defId args (hVerS.2.2 args hArgsS hPreS)

private theorem fullSemanticEquiv_trans {p1 p2 p3 : Program}
    (hLen12 : p1.bodies.length = p2.bodies.length)
    (h12 : PrivFullSemanticEquiv p1 p2)
    (h23 : PrivFullSemanticEquiv p2 p3) :
    PrivFullSemanticEquiv p1 p3 := by
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
    (hEquiv : PrivFullSemanticEquiv pSrc pTgt)
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
    rw [hBS] at hM1
    rw [hBT] at hM2
    rw [hIds, hM2] at hM1
    dsimp [Option.map] at hM1
    injection hM1 with hEq
    exact hEq.symm
  have hPV : ProgramVerified pTgt ⟨safety, prop⟩ ↔
      ProgramVerified pSrc ⟨safety, prop⟩ := by
    unfold ProgramVerified
    dsimp
    rw [← hPw, ← hVer, ← hIsEmpty, ← hEnt, ← hLen, ← hUniq]
    constructor
    · intro h
      let ⟨h1, h2, h3, h4, h5, hBodiesT, hPr⟩ := h
      refine ⟨h1, h2, h3, h4, h5, ?_, hProp.mp hPr⟩
      intro defId bSrc hBS
      have hLtT : defId < pTgt.bodies.length := by
        rw [← hLen]; exact getElem?_some_lt hBS
      let ⟨bTgt, hBT⟩ := getElem?_some_of_lt pTgt.bodies defId hLtT
      have hIdEq := hIdAt defId bSrc bTgt hBS hBT
      have hBVT := hBodiesT defId bTgt hBT
      rw [← hIdEq] at hBVT
      exact (hEquiv.2.2 defId bSrc bTgt (safety bSrc.identity) hBS hBT).mp hBVT
    · intro h
      let ⟨h1, h2, h3, h4, h5, hBodiesS, hPr⟩ := h
      refine ⟨h1, h2, h3, h4, h5, ?_, hProp.mpr hPr⟩
      intro defId bTgt hBT
      have hLtS : defId < pSrc.bodies.length := by
        rw [hLen]; exact getElem?_some_lt hBT
      let ⟨bSrc, hBS⟩ := getElem?_some_of_lt pSrc.bodies defId hLtS
      have hIdEq := hIdAt defId bSrc bTgt hBS hBT
      have hBVS := hBodiesS defId bSrc hBS
      rw [hIdEq] at hBVS
      exact (hEquiv.2.2 defId bSrc bTgt (safety bTgt.identity) hBS hBT).mpr hBVS
  unfold CrateTheorem UnitTheorem
  dsimp
  rw [← hSc]
  exact ⟨⟨fun h => ⟨h.1, hPV.mp h.2⟩, fun h => ⟨h.1, hPV.mpr h.2⟩⟩,
         ⟨fun h => ⟨h.1, hPV.mp h.2⟩, fun h => ⟨h.1, hPV.mpr h.2⟩⟩⟩

/-! ### Stage 4 Private Helpers — Layer C: Congruence & Passes 1, 2, and 4 -/

private theorem frame_with_locals_self (f : FrameState) :
    { f with locals := f.locals } = f := by
  cases f; rfl

private theorem evalStatement_congr_locals
    {bSrc bTgt : Body} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmt : StatementKind}
    (hBodyLocs : bSrc.locals = bTgt.locals)
    (hFrameLocs : fSrc.locals = fTgt.locals) :
    (∃ fk,
      evalStatement bSrc fSrc cm stmt = .fault fk ∧
      evalStatement bTgt fTgt cm stmt = .fault fk) ∨
    (∃ locs',
      evalStatement bSrc fSrc cm stmt =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs' }],
                callerMem := cm }) := by
  cases stmt with
  | nop =>
    right
    refine ⟨fSrc.locals, rfl, ?_⟩
    dsimp [evalStatement]
    rw [← hFrameLocs]
  | unsupported =>
    left
    exact ⟨.unsupported, rfl, rfl⟩
  | storageLive localId =>
    dsimp [evalStatement]
    rw [← hBodyLocs, ← hFrameLocs]
    cases Trusted.MirSemantics.getElem? bSrc.locals localId with
    | none => left; exact ⟨.unsupported, rfl, rfl⟩
    | some localTy =>
      dsimp
      cases setElem? fSrc.locals localId (liveUninitSlot localTy) with
      | none => left; exact ⟨.unsupported, rfl, rfl⟩
      | some locs' => right; exact ⟨locs', rfl, rfl⟩
  | storageDead localId =>
    dsimp [evalStatement]
    rw [← hFrameLocs]
    cases Nat.beq localId 0 with
    | true => left; exact ⟨.unsupported, rfl, rfl⟩
    | false =>
      rw [if_bool_false rfl, if_bool_false rfl]
      cases setElem? fSrc.locals localId .dead with
      | none => left; exact ⟨.unsupported, rfl, rfl⟩
      | some locs' => right; exact ⟨locs', rfl, rfl⟩
  | assign dst rv =>
    dsimp [evalStatement]
    rw [← hBodyLocs, ← hFrameLocs]
    cases (!dst.projection.isEmpty) with
    | true => left; exact ⟨.unsupported, rfl, rfl⟩
    | false =>
      rw [if_bool_false rfl, if_bool_false rfl]
      cases Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
      | none => left; exact ⟨.unsupported, rfl, rfl⟩
      | some dstTy =>
        dsimp
        cases evalRvalue bSrc.locals fSrc.locals dstTy rv with
        | error fk => left; exact ⟨fk, rfl, rfl⟩
        | ok res =>
          let ⟨val, locsAfter⟩ := res
          dsimp
          cases writePlace locsAfter dst.localId dstTy val with
          | error fk => left; exact ⟨fk, rfl, rfl⟩
          | ok locsWrite => right; exact ⟨locsWrite, rfl, rfl⟩

private theorem evalTerminator_eq_congr
    {bSrc bTgt : Body} {bbSrc bbTgt : BasicBlock}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hBodyLocs : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hTerm : bbSrc.terminator = bbTgt.terminator)
    (hFrameLocs : fSrc.locals = fTgt.locals) :
    (∃ fk,
      evalTerminator bSrc bbSrc fSrc cm = .fault fk ∧
      evalTerminator bTgt bbTgt fTgt cm = .fault fk) ∨
    (∃ out,
      evalTerminator bSrc bbSrc fSrc cm = .done out ∧
      evalTerminator bTgt bbTgt fTgt cm = .done out) ∨
    (∃ tgt locs',
      evalTerminator bSrc bbSrc fSrc cm =
        .step { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
                callerMem := cm } ∧
      evalTerminator bTgt bbTgt fTgt cm =
        .step { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
                callerMem := cm }) := by
  unfold evalTerminator
  rw [← hTerm, ← hBodyLocs]
  cases bbSrc.terminator with
  | goto tgt =>
    right; right
    refine ⟨tgt, fSrc.locals, rfl, ?_⟩
    dsimp [jumpToBlock]; rw [← hFrameLocs]
  | return_ =>
    dsimp
    rw [← hClean, ← hFrameLocs]
    cases bbSrc.cleanup with
    | true => left; exact ⟨.unsupported, rfl, rfl⟩
    | false =>
      cases Trusted.MirSemantics.getElem? fSrc.locals 0 with
      | none => left; exact ⟨.unsupported, rfl, rfl⟩
      | some sl =>
        cases sl with
        | dead => left; exact ⟨.undefined, rfl, rfl⟩
        | live opt =>
          cases opt with
          | none => left; exact ⟨.undefined, rfl, rfl⟩
          | some rv => right; left; exact ⟨.returned ⟨rv, cm⟩, rfl, rfl⟩
  | unreachable => left; exact ⟨.undefined, rfl, rfl⟩
  | unwindResume => left; exact ⟨.unsupported, rfl, rfl⟩
  | assert _ _ _ _ _ => left; exact ⟨.unsupported, rfl, rfl⟩
  | call _ _ _ _ _ => left; exact ⟨.unsupported, rfl, rfl⟩
  | unsupported => left; exact ⟨.unsupported, rfl, rfl⟩
  | switchInt discr targets =>
    dsimp
    rw [← hFrameLocs]
    cases evalPrimitiveOperand bSrc.locals fSrc.locals discr with
    | error fk => left; exact ⟨fk, rfl, rfl⟩
    | ok res =>
      let ⟨dv, locsAfter⟩ := res
      dsimp
      cases dv with
      | scalar sv =>
        dsimp
        cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error fk => left; exact ⟨fk, rfl, rfl⟩
        | ok tgt => right; right; exact ⟨tgt, locsAfter, rfl, rfl⟩
      | bool b =>
        dsimp
        cases evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error fk => left; exact ⟨fk, rfl, rfl⟩
        | ok tgt => right; right; exact ⟨tgt, locsAfter, rfl, rfl⟩
      | ptr _ => left; exact ⟨.unsupported, rfl, rfl⟩
      | unit => left; exact ⟨.unsupported, rfl, rfl⟩
      | enumVal _ _ => left; exact ⟨.unsupported, rfl, rfl⟩
      | tuple _ => left; exact ⟨.unsupported, rfl, rfl⟩
      | bytes _ => left; exact ⟨.unsupported, rfl, rfl⟩

private theorem evalSwitchBranches_rel {edgeRel : BasicBlockId → BasicBlockId → Bool}
    {w : IntWidth} {discrBits : BitVec 128}
    {ow₁ ow₂ : BasicBlockId}
    {bs₁ bs₂ : List (BitVec 128 × BasicBlockId)}
    (hOw : edgeRel ow₁ ow₂ = true)
    (hBs : listRel (fun a b => (a.1 == b.1) && edgeRel a.2 b.2) bs₁ bs₂ = true) :
    (∃ fk,
      evalSwitchBranches w discrBits ow₁ bs₁ = .error fk ∧
      evalSwitchBranches w discrBits ow₂ bs₂ = .error fk) ∨
    (∃ tgt₁ tgt₂,
      evalSwitchBranches w discrBits ow₁ bs₁ = .ok tgt₁ ∧
      evalSwitchBranches w discrBits ow₂ bs₂ = .ok tgt₂ ∧
      edgeRel tgt₁ tgt₂ = true) := by
  induction bs₁ generalizing bs₂ with
  | nil =>
    cases bs₂ with
    | nil =>
      right
      exact ⟨ow₁, ow₂, rfl, rfl, hOw⟩
    | cons _ _ => cases hBs
  | cons br₁ rest₁ ih =>
    cases bs₂ with
    | nil => cases hBs
    | cons br₂ rest₂ =>
      let ⟨cb₁, tb₁⟩ := br₁
      let ⟨cb₂, tb₂⟩ := br₂
      dsimp [listRel] at hBs
      let ⟨hHead, hTail⟩ := bool_and_true hBs
      let ⟨hCb, hTb⟩ := bool_and_true hHead
      have hCbEq : cb₁ = cb₂ := bitvec_beq_eq hCb
      subst hCbEq
      dsimp [evalSwitchBranches]
      cases hOvf : (truncateBits w cb₁ != cb₁) with
      | true => left; exact ⟨.unsupported, rfl, rfl⟩
      | false =>
        rw [if_bool_false rfl, if_bool_false rfl]
        cases hMatch : (truncateBits w discrBits == truncateBits w cb₁) with
        | true =>
          right
          exact ⟨tb₁, tb₂, rfl, rfl, hTb⟩
        | false =>
          rw [if_bool_false rfl, if_bool_false rfl]
          exact ih hTail

private theorem evalBoolSwitchBranches_rel {edgeRel : BasicBlockId → BasicBlockId → Bool}
    {discr : Bool} {ow₁ ow₂ : BasicBlockId}
    {bs₁ bs₂ : List (BitVec 128 × BasicBlockId)}
    (hOw : edgeRel ow₁ ow₂ = true)
    (hBs : listRel (fun a b => (a.1 == b.1) && edgeRel a.2 b.2) bs₁ bs₂ = true) :
    (∃ fk,
      evalBoolSwitchBranches discr ow₁ bs₁ = .error fk ∧
      evalBoolSwitchBranches discr ow₂ bs₂ = .error fk) ∨
    (∃ tgt₁ tgt₂,
      evalBoolSwitchBranches discr ow₁ bs₁ = .ok tgt₁ ∧
      evalBoolSwitchBranches discr ow₂ bs₂ = .ok tgt₂ ∧
      edgeRel tgt₁ tgt₂ = true) := by
  induction bs₁ generalizing bs₂ with
  | nil =>
    cases bs₂ with
    | nil => right; exact ⟨ow₁, ow₂, rfl, rfl, hOw⟩
    | cons _ _ => cases hBs
  | cons br₁ rest₁ ih =>
    cases bs₂ with
    | nil => cases hBs
    | cons br₂ rest₂ =>
      let ⟨cb₁, tb₁⟩ := br₁
      let ⟨cb₂, tb₂⟩ := br₂
      dsimp [listRel] at hBs
      let ⟨hHead, hTail⟩ := bool_and_true hBs
      let ⟨hCb, hTb⟩ := bool_and_true hHead
      have hCbEq : cb₁ = cb₂ := bitvec_beq_eq hCb
      subst hCbEq
      dsimp [evalBoolSwitchBranches]
      cases evalConstLit .bool (.scalar cb₁) with
      | error fk => left; exact ⟨fk, rfl, rfl⟩
      | ok cv =>
        cases cv with
        | bool b =>
          cases b with
          | false =>
            cases discr with
            | false => right; exact ⟨tb₁, tb₂, rfl, rfl, hTb⟩
            | true => exact ih hTail
          | true =>
            cases discr with
            | true => right; exact ⟨tb₁, tb₂, rfl, rfl, hTb⟩
            | false => exact ih hTail
        | scalar _ => left; exact ⟨.unsupported, rfl, rfl⟩
        | ptr _ => left; exact ⟨.unsupported, rfl, rfl⟩
        | unit => left; exact ⟨.unsupported, rfl, rfl⟩
        | enumVal _ _ => left; exact ⟨.unsupported, rfl, rfl⟩
        | tuple _ => left; exact ⟨.unsupported, rfl, rfl⟩
        | bytes _ => left; exact ⟨.unsupported, rfl, rfl⟩

private theorem stmtMarker_eq_of_stmtEq {s1 s2 : StatementKind} (idx : LocalId)
    (h : stmtEq s1 s2 = true) :
    stmtHasStorageMarker idx s1 = stmtHasStorageMarker idx s2 := by
  rw [stmtEq_eq h]

/-! #### Pass 1 (`StripNops`, Theorem 1) -/

private theorem isStripNopsStmts_elim {xs ys : List StatementKind}
    (h : isStripNopsStmts xs ys = true) :
    (xs = [] ∧ ys = []) ∨
    (∃ rest₁, xs = .nop :: rest₁ ∧ isStripNopsStmts rest₁ ys = true) ∨
    (∃ s₁ rest₁ s₂ rest₂,
      xs = s₁ :: rest₁ ∧ ys = s₂ :: rest₂ ∧
      stmtEq s₁ s₂ = true ∧ isStripNopsStmts rest₁ rest₂ = true) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => left; exact ⟨rfl, rfl⟩
    | cons _ _ => cases h
  | cons s₁ rest₁ =>
    cases s₁ with
    | nop =>
      cases ys with
      | nil =>
        right; left; exact ⟨rest₁, rfl, h⟩
      | cons s₂ rest₂ =>
        cases s₂ with
        | nop =>
          right; right; exact ⟨.nop, rest₁, .nop, rest₂, rfl, rfl, rfl, h⟩
        | assign _ _ =>
          right; left; exact ⟨rest₁, rfl, h⟩
        | storageLive _ =>
          right; left; exact ⟨rest₁, rfl, h⟩
        | storageDead _ =>
          right; left; exact ⟨rest₁, rfl, h⟩
        | unsupported =>
          right; left; exact ⟨rest₁, rfl, h⟩
    | assign d rv =>
      cases ys with
      | nil => cases h
      | cons s₂ rest₂ =>
        let ⟨h1, h2⟩ := bool_and_true h
        right; right; exact ⟨.assign d rv, rest₁, s₂, rest₂, rfl, rfl, h1, h2⟩
    | storageLive id =>
      cases ys with
      | nil => cases h
      | cons s₂ rest₂ =>
        let ⟨h1, h2⟩ := bool_and_true h
        right; right; exact ⟨.storageLive id, rest₁, s₂, rest₂, rfl, rfl, h1, h2⟩
    | storageDead id =>
      cases ys with
      | nil => cases h
      | cons s₂ rest₂ =>
        let ⟨h1, h2⟩ := bool_and_true h
        right; right; exact ⟨.storageDead id, rest₁, s₂, rest₂, rfl, rfl, h1, h2⟩
    | unsupported =>
      cases ys with
      | nil => cases h
      | cons s₂ rest₂ =>
        let ⟨h1, h2⟩ := bool_and_true h
        right; right; exact ⟨.unsupported, rest₁, s₂, rest₂, rfl, rfl, h1, h2⟩

private theorem stripNopsStmts_any_marker {xs ys : List StatementKind} (idx : LocalId)
    (h : isStripNopsStmts xs ys = true) :
    xs.any (stmtHasStorageMarker idx) = ys.any (stmtHasStorageMarker idx) := by
  induction xs generalizing ys with
  | nil =>
    cases isStripNopsStmts_elim h with
    | inl hNil => rw [hNil.2]
    | inr hRest =>
      cases hRest with
      | inl hNop => let ⟨_, hEq, _⟩ := hNop; cases hEq
      | inr hCons => let ⟨_, _, _, _, hEq, _, _, _⟩ := hCons; cases hEq
  | cons a rest₁ ih =>
    cases isStripNopsStmts_elim h with
    | inl hNil => cases hNil.1
    | inr hRest =>
      cases hRest with
      | inl hNop =>
        let ⟨r₁, hEqX, hTail⟩ := hNop
        injection hEqX with ha hr
        subst ha; subst hr
        dsimp [List.any, stmtHasStorageMarker]
        exact ih hTail
      | inr hCons =>
        let ⟨s₁, r₁, s₂, r₂, hEqX, hEqY, hS, hTail⟩ := hCons
        injection hEqX with ha hr
        subst ha; subst hr; subst hEqY
        dsimp [List.any]
        rw [stmtMarker_eq_of_stmtEq idx hS, ih hTail]

private theorem stripNopsStmts_all_inBounds {xs ys : List StatementKind} (numLocals : Nat)
    (h : isStripNopsStmts xs ys = true) :
    xs.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id numLocals
      | _ => true) =
    ys.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id numLocals
      | _ => true) := by
  induction xs generalizing ys with
  | nil =>
    cases isStripNopsStmts_elim h with
    | inl hNil => rw [hNil.2]
    | inr hRest =>
      cases hRest with
      | inl hNop => let ⟨_, hEq, _⟩ := hNop; cases hEq
      | inr hCons => let ⟨_, _, _, _, hEq, _, _, _⟩ := hCons; cases hEq
  | cons a rest₁ ih =>
    cases isStripNopsStmts_elim h with
    | inl hNil => cases hNil.1
    | inr hRest =>
      cases hRest with
      | inl hNop =>
        let ⟨r₁, hEqX, hTail⟩ := hNop
        injection hEqX with ha hr
        subst ha; subst hr
        dsimp [List.all]
        exact ih hTail
      | inr hCons =>
        let ⟨s₁, r₁, s₂, r₂, hEqX, hEqY, hS, hTail⟩ := hCons
        injection hEqX with ha hr
        subst ha; subst hr; subst hEqY
        have hEqS : a = s₂ := stmtEq_eq hS
        subst hEqS
        dsimp [List.all]
        rw [ih hTail]

private theorem stripNopsBody_storage_eq {b1 b2 : Body}
    (h : isStripNopsBody b1 b2 = true) :
    bodyHeaderEq b1 b2 = true ∧
    b1.basicBlocks.length = b2.basicBlocks.length ∧
    storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 ∧
    (∀ idx, hasStorageAnnotation b1 idx = hasStorageAnnotation b2 idx) := by
  unfold isStripNopsBody at h
  let ⟨hBHdr, hBlocks⟩ := bool_and_true h
  let ⟨_, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  refine ⟨hBHdr, listRel_length hBlocks, ?_, ?_⟩
  · unfold storageAnnotationsInBounds
    rw [hLoc]
    exact list_all_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
      unfold isStripNopsBlock at hbb
      let ⟨h12, _⟩ := bool_and_true hbb
      let ⟨_, hStmts⟩ := bool_and_true h12
      exact stripNopsStmts_all_inBounds b2.locals.length hStmts)
  · intro idx
    unfold hasStorageAnnotation
    exact list_any_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
      unfold isStripNopsBlock at hbb
      let ⟨h12, _⟩ := bool_and_true hbb
      let ⟨_, hStmts⟩ := bool_and_true h12
      exact stripNopsStmts_any_marker idx hStmts)

private theorem stripNops_entryProg {pSrc pTgt : Program} (defId : DefId)
    (h : isStripNopsProgram pSrc pTgt = true) :
    isStripNopsProgram (entryProgForBody pSrc defId)
      (entryProgForBody pTgt defId) = true := by
  unfold isStripNopsProgram at h
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  unfold isStripNopsProgram
  exact bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies

private theorem stripNops_initState_eq {pSrc pTgt : Program} (q : Query)
    (h : isStripNopsProgram pSrc pTgt = true) :
    initState pSrc q = initState pTgt q := by
  unfold isStripNopsProgram at h
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]
    exact listRel_getElem?_none_iff pSrc.entryDefId hBodies
  · intro b1 hB1
    let ⟨b2, hB20, hRelB⟩ := listRel_getElem?_left hBodies hB1
    have hB2 : Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some b2 := by
      rw [← hEnt]; exact hB20
    let ⟨hBHdr, hBLen, hSt, hHasAnn⟩ := stripNopsBody_storage_eq hRelB
    let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
    exact ⟨b2, hB2, hBHdr, list_isEmpty_eq_of_length hBLen, hSt,
      initLocalsLoop_eq_of_storage_eq q.args hArg hLoc (fun idx _ _ => hHasAnn idx)⟩

private noncomputable def StateStripNopsRel (pSrc pTgt : Program)
    (k : Nat) (s t : State) : Prop :=
  s.callerMem = t.callerMem ∧
  ∃ fSrc fTgt bSrc bTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.locals = fTgt.locals ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt ∧
    isStripNopsBody bSrc bTgt = true ∧
    ((Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = none ∧ k = 0) ∨
      ∃ bbSrc bbTgt,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt ∧
        fSrc.stmtIdx ≤ bbSrc.statements.length ∧
        fTgt.stmtIdx ≤ bbTgt.statements.length ∧
        isStripNopsStmts (bbSrc.statements.drop fSrc.stmtIdx)
          (bbTgt.statements.drop fTgt.stmtIdx) = true ∧
        k = bbSrc.statements.length - fSrc.stmtIdx)

private theorem stripNops_jump_rel {pSrc pTgt : Program}
    {bSrc bTgt : Body} {fSrc fTgt : FrameState} {cm1 cm2 : CallerMemory}
    {tgt : BasicBlockId} {locs' : List LocalSlot}
    (hCm : cm1 = cm2)
    (hDef : fSrc.defId = fTgt.defId)
    (hBS : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc)
    (hBT : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt)
    (hBody : isStripNopsBody bSrc bTgt = true) :
    ∃ k', StateStripNopsRel pSrc pTgt k'
      { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
        callerMem := cm1 }
      { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
        callerMem := cm2 } := by
  have hBodyCopy := hBody
  unfold isStripNopsBody at hBodyCopy
  let ⟨_, hBlocks⟩ := bool_and_true hBodyCopy
  cases hBB : Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt with
  | none =>
    exact ⟨0, hCm, _, _, bSrc, bTgt, rfl, rfl, hDef, rfl, rfl,
      hBS, hBT, hBody, Or.inl ⟨hBB, rfl⟩⟩
  | some bbNextSrc =>
    let ⟨bbNextTgt, hBBT, hRelBB⟩ := listRel_getElem?_left hBlocks hBB
    unfold isStripNopsBlock at hRelBB
    let ⟨h12, _⟩ := bool_and_true hRelBB
    let ⟨_, hStmts⟩ := bool_and_true h12
    exact ⟨bbNextSrc.statements.length - 0, hCm, _, _, bSrc, bTgt, rfl, rfl,
      hDef, rfl, rfl, hBS, hBT, hBody,
      Or.inr ⟨bbNextSrc, bbNextTgt, hBB, hBBT,
        Nat.zero_le _, Nat.zero_le _, hStmts, rfl⟩⟩

private theorem stripNops_stutter_step {pSrc pTgt : Program} {k : Nat} {s t : State}
    (hRel : StateStripNopsRel pSrc pTgt k s t) :
    StutterStepOutcome pSrc pTgt (StateStripNopsRel pSrc pTgt) k s t := by
  let ⟨hCm, fSrc, fTgt, bSrc, bTgt, hFS, hFT, hDef, hBlk, hLocs,
       hBS, hBT, hBody, hBlkState⟩ := hRel
  have hBodyCopy := hBody
  unfold isStripNopsBody at hBodyCopy
  let ⟨hBHdr, hBlocks⟩ := bool_and_true hBodyCopy
  let ⟨_, hBodyLocs, _, _⟩ := bodyHeaderEq_elim hBHdr
  cases hBlkState with
  | inl hNoBB =>
    have hNoBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
      rw [← hBlk]
      exact (listRel_getElem?_none_iff fSrc.blockIdx hBlocks).mp hNoBB.1
    right; right; right
    refine ⟨.unsupported, ?_, ?_⟩
    · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hNoBB.1]
    · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hNoBBT]
  | inr hInBB =>
    let ⟨bbSrc, bbTgt, hBBS, hBBT, hLeS, hLeT, hDropRel, hK⟩ := hInBB
    let ⟨bbTgt', hBBT', hRelBB⟩ := listRel_getElem?_left hBlocks hBBS
    rw [← hBlk] at hBBT
    rw [hBBT] at hBBT'; injection hBBT' with hEqBB; subst hEqBB
    unfold isStripNopsBlock at hRelBB
    let ⟨h12, hTermEq⟩ := bool_and_true hRelBB
    let ⟨hCleanB, _⟩ := bool_and_true h12
    have hClean : bbSrc.cleanup = bbTgt.cleanup := bool_beq_eq hCleanB
    have hTerm : bbSrc.terminator = bbTgt.terminator := terminatorEq_eq hTermEq
    cases isStripNopsStmts_elim hDropRel with
    | inl hBothNil =>
      have hIdxS : fSrc.stmtIdx = bbSrc.statements.length :=
        Nat.le_antisymm hLeS (le_of_drop_eq_nil hBothNil.1)
      have hIdxT : fTgt.stmtIdx = bbTgt.statements.length :=
        Nat.le_antisymm hLeT (le_of_drop_eq_nil hBothNil.2)
      have hNoS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx = none :=
        getElem?_none_of_ge (by rw [hIdxS]; exact Nat.le_refl _)
      have hNoT : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none :=
        getElem?_none_of_ge (by rw [hIdxT]; exact Nat.le_refl _)
      have hEndS : Nat.beq fSrc.stmtIdx bbSrc.statements.length = true :=
        nat_beq_of_eq hIdxS
      have hEndT : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true :=
        nat_beq_of_eq hIdxT
      have hEvS : evalStep pSrc 0 s = evalTerminator bSrc bbSrc fSrc s.callerMem := by
        unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
        rw [hNoS, if_bool_true hEndS]
      have hEvT : evalStep pTgt 0 t = evalTerminator bTgt bbTgt fTgt t.callerMem := by
        unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [← hBlk, hBBT]; dsimp
        rw [hNoT, if_bool_true hEndT]
      right
      rw [← hCm] at hEvT
      cases evalTerminator_eq_congr (cm := s.callerMem) hBodyLocs hClean hTerm hLocs with
      | inl hFlt =>
        let ⟨fk, h1, h2⟩ := hFlt
        right; right; exact ⟨fk, by rw [hEvS, h1], by rw [hEvT, h2]⟩
      | inr hRest =>
        cases hRest with
        | inl hDone =>
          let ⟨out, h1, h2⟩ := hDone
          right; left; exact ⟨out, by rw [hEvS, h1], by rw [hEvT, h2]⟩
        | inr hJmp =>
          let ⟨tgt, locs', h1, h2⟩ := hJmp
          let ⟨k', hNextRel⟩ := stripNops_jump_rel (pSrc := pSrc) (pTgt := pTgt)
            (tgt := tgt) (locs' := locs') hCm hDef hBS hBT hBody
          rw [← hCm] at hNextRel
          left
          exact ⟨k', _, _, by rw [hEvS, h1], by rw [hEvT, h2], hNextRel⟩
    | inr hNonNil =>
      cases hNonNil with
      | inl hSilentNop =>
        let ⟨rest₁, hDropS, hTailRel⟩ := hSilentNop
        let ⟨hGetS, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
        have hLtS : fSrc.stmtIdx < bbSrc.statements.length := getElem?_some_lt hGetS
        have hKSucc : k = (bbSrc.statements.length - (fSrc.stmtIdx + 1)) + 1 := by
          rw [hK]
          exact nat_sub_succ_lt hLtS
        left
        refine ⟨bbSrc.statements.length - (fSrc.stmtIdx + 1),
          { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1 }], callerMem := s.callerMem },
          hKSucc, ?_, ?_⟩
        · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
          rw [hGetS]; rfl
        · refine ⟨hCm, _, fTgt, bSrc, bTgt, rfl, hFT, hDef, hBlk, hLocs,
            hBS, hBT, hBody, Or.inr ⟨bbSrc, bbTgt, hBBS, ?_, hLtS, hLeT, ?_, rfl⟩⟩
          · rw [← hBlk]; exact hBBT
          · rw [hDropSNext]; exact hTailRel
      | inr hSyncStmt =>
        let ⟨st₁, rest₁, st₂, rest₂, hDropS, hDropT, hStEq, hTailRel⟩ := hSyncStmt
        have hEqSt : st₁ = st₂ := stmtEq_eq hStEq
        subst hEqSt
        let ⟨hGetS, hDropSNext⟩ := getElem?_of_drop_eq_cons hDropS
        let ⟨hGetT, hDropTNext⟩ := getElem?_of_drop_eq_cons hDropT
        have hLtS : fSrc.stmtIdx < bbSrc.statements.length := getElem?_some_lt hGetS
        have hLtT : fTgt.stmtIdx < bbTgt.statements.length := getElem?_some_lt hGetT
        have hEvS : evalStep pSrc 0 s = evalStatement bSrc fSrc s.callerMem st₁ := by
          unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp; rw [hGetS]
        have hEvT : evalStep pTgt 0 t = evalStatement bTgt fTgt s.callerMem st₁ := by
          unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [← hBlk, hBBT]; dsimp
          rw [hGetT, ← hCm]
        right
        cases evalStatement_congr_locals (cm := s.callerMem) (stmt := st₁) hBodyLocs hLocs with
        | inl hFlt =>
          let ⟨fk, h1, h2⟩ := hFlt
          right; right; exact ⟨fk, by rw [hEvS, h1], by rw [hEvT, h2]⟩
        | inr hStp =>
          let ⟨locs', h1, h2⟩ := hStp
          left
          refine ⟨bbSrc.statements.length - (fSrc.stmtIdx + 1), _,
            { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs' }],
              callerMem := t.callerMem },
            by rw [hEvS, h1], by rw [hEvT, h2, hCm], ?_⟩
          refine ⟨hCm, _, _, bSrc, bTgt, rfl, rfl, hDef, hBlk, rfl,
            hBS, hBT, hBody, Or.inr ⟨bbSrc, bbTgt, hBBS, ?_, hLtS, hLtT, ?_, rfl⟩⟩
          · rw [← hBlk]; exact hBBT
          · rw [hDropSNext, hDropTNext]; exact hTailRel

private theorem stripNops_query_iff {pSrc pTgt : Program} (q : Query)
    (hRel : isStripNopsProgram pSrc pTgt = true) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := stripNops_initState_eq q hRel
  apply stutter_bisim_lift (R := StateStripNopsRel pSrc pTgt)
  · intro k; rw [hInitEq]
  · intro s₀ t₀ hIS hIT
    rw [hInitEq] at hIS
    have hEqST : s₀ = t₀ := by rw [hIS] at hIT; injection hIT
    subst hEqST
    let ⟨_, _, bTgt, hBT, hNE, _, _, _, _, hS0⟩ := initState_ok_elim hIT
    unfold isStripNopsProgram at hRel
    let ⟨hHdr, hBodies⟩ := bool_and_true hRel
    let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
    have hBT' : Trusted.MirSemantics.getElem? pTgt.bodies pSrc.entryDefId = some bTgt := by
      rw [hEnt]; exact hBT
    let ⟨bSrc, hBS, hBody⟩ := listRel_getElem?_right hBodies hBT'
    let ⟨_, hBLen, _, _⟩ := stripNopsBody_storage_eq hBody
    have hPosT : 0 < bTgt.basicBlocks.length := list_pos_of_isEmpty_false hNE
    let ⟨bbSrc0, hBBS0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 (by rw [hBLen]; exact hPosT)
    have hBodyCopy := hBody
    unfold isStripNopsBody at hBodyCopy
    let ⟨_, hBlocks⟩ := bool_and_true hBodyCopy
    let ⟨bbTgt0, hBBT0, hRelBB0⟩ := listRel_getElem?_left hBlocks hBBS0
    unfold isStripNopsBlock at hRelBB0
    let ⟨h12, _⟩ := bool_and_true hRelBB0
    let ⟨_, hStmts0⟩ := bool_and_true h12
    subst hS0
    refine ⟨bbSrc0.statements.length - 0, rfl, _, _, bSrc, bTgt, rfl, rfl, rfl, rfl, rfl,
      ?_, hBT, hBody, Or.inr ⟨bbSrc0, bbTgt0, hBBS0, hBBT0, Nat.zero_le _, Nat.zero_le _, hStmts0, rfl⟩⟩
    rw [← hEnt]; exact hBS
  · intro k s t hR
    exact stripNops_stutter_step hR

private theorem stripNops_bidirectional_iff_priv
    (pSrc pTgt : Program)
    (hRel : isStripNopsProgram pSrc pTgt = true) :
    PrivFullSemanticEquiv pSrc pTgt := by
  have hRelCopy := hRel
  unfold isStripNopsProgram at hRelCopy
  let ⟨hHdr, hBodies⟩ := bool_and_true hRelCopy
  refine fullSemanticEquiv_of_query_iff hHdr ?_
    (fun q => stripNops_query_iff q hRel)
    (fun defId args => (stripNops_query_iff { args := args } (stripNops_entryProg defId hRel)).1)
  intro defId bSrc bTgt hBS hBT
  let ⟨bTgt', hBT', hBody⟩ := listRel_getElem?_left hBodies hBS
  rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
  let ⟨hBHdr, hBLen, hSt, _⟩ := stripNopsBody_storage_eq hBody
  exact ⟨hBHdr, list_isEmpty_eq_of_length hBLen, hSt⟩

/-! #### Pass 2 (`ConstBranchFold`, Theorem 2) -/

private theorem resolveConstSwitchTarget_evalTerminator
    {bSrc : Body} {bbSrc : BasicBlock} {f : FrameState} {cm : CallerMemory}
    {c : ConstOperand} {targets : SwitchTargets} {target : BasicBlockId}
    (hTerm : bbSrc.terminator = .switchInt (.constant c) targets)
    (hRes : resolveConstSwitchTarget c targets = some target) :
    evalTerminator bSrc bbSrc f cm = jumpToBlock f cm target := by
  unfold resolveConstSwitchTarget at hRes
  cases hPrim : (!isPrimitiveReadableTy c.ty) with
  | true => rw [if_bool_true hPrim] at hRes; cases hRes
  | false =>
    rw [if_bool_false hPrim] at hRes
    cases hLit : evalConstLit c.ty c.lit with
    | error _ => rw [hLit] at hRes; cases hRes
    | ok dv =>
      rw [hLit] at hRes
      cases dv with
      | scalar sv =>
        dsimp at hRes
        cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error _ => rw [hSw] at hRes; cases hRes
        | ok resolved =>
          rw [hSw] at hRes
          injection hRes with hEqT; subst hEqT
          unfold evalTerminator
          rw [hTerm]; dsimp [evalPrimitiveOperand, evalOperandToSlot]
          rw [hLit]; dsimp
          rw [if_bool_false hPrim]; dsimp
          rw [hSw]
      | bool b =>
        dsimp at hRes
        cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error _ => rw [hSw] at hRes; cases hRes
        | ok resolved =>
          rw [hSw] at hRes
          injection hRes with hEqT; subst hEqT
          unfold evalTerminator
          rw [hTerm]; dsimp [evalPrimitiveOperand, evalOperandToSlot]
          rw [hLit]; dsimp
          rw [if_bool_false hPrim]; dsimp
          rw [hSw]
      | ptr _ => cases hRes
      | unit => cases hRes
      | enumVal _ _ => cases hRes
      | tuple _ => cases hRes
      | bytes _ => cases hRes

private theorem isConstBranchFoldTerm_elim {t₁ t₂ : TerminatorKind}
    (h : isConstBranchFoldTerm t₁ t₂ = true) :
    t₁ = t₂ ∨
    ∃ c targets target,
      t₁ = .switchInt (.constant c) targets ∧
      t₂ = .goto target ∧
      resolveConstSwitchTarget c targets = some target := by
  cases t₁ with
  | switchInt d₁ ts₁ =>
    cases d₁ with
    | constant c =>
      cases t₂ with
      | goto target =>
        dsimp [isConstBranchFoldTerm] at h
        cases hR : resolveConstSwitchTarget c ts₁ with
        | none => rw [hR] at h; cases h
        | some resolved =>
          rw [hR] at h
          have hEq : resolved = target := nat_beq_eq h
          subst hEq
          right; exact ⟨c, ts₁, resolved, rfl, rfl, hR⟩
      | switchInt _ _ => left; exact terminatorEq_eq h
      | return_ => cases h
      | unreachable => cases h
      | unwindResume => cases h
      | assert _ _ _ _ _ => cases h
      | call _ _ _ _ _ => cases h
      | unsupported => cases h
    | copy _ => left; exact terminatorEq_eq h
    | move _ => left; exact terminatorEq_eq h
  | goto _ => left; exact terminatorEq_eq h
  | return_ => left; exact terminatorEq_eq h
  | unreachable => left; exact terminatorEq_eq h
  | unwindResume => left; exact terminatorEq_eq h
  | assert _ _ _ _ _ => left; exact terminatorEq_eq h
  | call _ _ _ _ _ => left; exact terminatorEq_eq h
  | unsupported => left; exact terminatorEq_eq h

private theorem constBranchFoldBody_storage_eq {b1 b2 : Body}
    (h : isConstBranchFoldBody b1 b2 = true) :
    bodyHeaderEq b1 b2 = true ∧
    b1.basicBlocks.length = b2.basicBlocks.length ∧
    storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 ∧
    (∀ idx, hasStorageAnnotation b1 idx = hasStorageAnnotation b2 idx) := by
  unfold isConstBranchFoldBody at h
  let ⟨hBHdr, hBlocks⟩ := bool_and_true h
  let ⟨_, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  refine ⟨hBHdr, listRel_length hBlocks, ?_, ?_⟩
  · unfold storageAnnotationsInBounds
    rw [hLoc]
    exact list_all_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
      unfold isConstBranchFoldBlock at hbb
      let ⟨h12, _⟩ := bool_and_true hbb
      let ⟨_, hStmts⟩ := bool_and_true h12
      rw [listRel_eq (fun _ _ => stmtEq_eq) hStmts])
  · intro idx
    unfold hasStorageAnnotation
    exact list_any_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
      unfold isConstBranchFoldBlock at hbb
      let ⟨h12, _⟩ := bool_and_true hbb
      let ⟨_, hStmts⟩ := bool_and_true h12
      rw [listRel_eq (fun _ _ => stmtEq_eq) hStmts])

private theorem constBranchFold_entryProg {pSrc pTgt : Program} (defId : DefId)
    (h : isConstBranchFoldProgram pSrc pTgt = true) :
    isConstBranchFoldProgram (entryProgForBody pSrc defId)
      (entryProgForBody pTgt defId) = true := by
  unfold isConstBranchFoldProgram at h
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  unfold isConstBranchFoldProgram
  exact bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies

private theorem constBranchFold_initState_eq {pSrc pTgt : Program} (q : Query)
    (h : isConstBranchFoldProgram pSrc pTgt = true) :
    initState pSrc q = initState pTgt q := by
  unfold isConstBranchFoldProgram at h
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]
    exact listRel_getElem?_none_iff pSrc.entryDefId hBodies
  · intro b1 hB1
    let ⟨b2, hB20, hRelB⟩ := listRel_getElem?_left hBodies hB1
    have hB2 : Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some b2 := by
      rw [← hEnt]; exact hB20
    let ⟨hBHdr, hBLen, hSt, hHasAnn⟩ := constBranchFoldBody_storage_eq hRelB
    let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
    exact ⟨b2, hB2, hBHdr, list_isEmpty_eq_of_length hBLen, hSt,
      initLocalsLoop_eq_of_storage_eq q.args hArg hLoc (fun idx _ _ => hHasAnn idx)⟩

private theorem constBranchFold_evalStep_eq {pSrc pTgt : Program}
    (h : isConstBranchFoldProgram pSrc pTgt = true) (s : State) :
    evalStep pSrc 0 s = evalStep pTgt 0 s := by
  unfold isConstBranchFoldProgram at h
  let ⟨_, hBodies⟩ := bool_and_true h
  unfold evalStep
  cases s.frames with
  | nil => rfl
  | cons frame restFrames =>
    cases restFrames with
    | cons _ _ => rfl
    | nil =>
      dsimp
      cases hBS : Trusted.MirSemantics.getElem? pSrc.bodies frame.defId with
      | none =>
        rw [(listRel_getElem?_none_iff frame.defId hBodies).mp hBS]
      | some bSrc =>
        let ⟨bTgt, hBT, hBody⟩ := listRel_getElem?_left hBodies hBS
        rw [hBT]; dsimp
        unfold isConstBranchFoldBody at hBody
        let ⟨hBHdr, hBlocks⟩ := bool_and_true hBody
        let ⟨_, hLocsEq, _, _⟩ := bodyHeaderEq_elim hBHdr
        cases hBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
        | none =>
          rw [(listRel_getElem?_none_iff frame.blockIdx hBlocks).mp hBBS]
        | some bbSrc =>
          let ⟨bbTgt, hBBT, hBB⟩ := listRel_getElem?_left hBlocks hBBS
          rw [hBBT]; dsimp
          unfold isConstBranchFoldBlock at hBB
          let ⟨h12, hTermRel⟩ := bool_and_true hBB
          let ⟨hCleanB, hStmtsRel⟩ := bool_and_true h12
          have hClean : bbSrc.cleanup = bbTgt.cleanup := bool_beq_eq hCleanB
          have hStmtsEq : bbSrc.statements = bbTgt.statements :=
            listRel_eq (fun _ _ => stmtEq_eq) hStmtsRel
          rw [← hStmtsEq]
          cases Trusted.MirSemantics.getElem? bbSrc.statements frame.stmtIdx with
          | some stmt =>
            dsimp
            cases evalStatement_congr_locals (fSrc := frame) (fTgt := frame)
                (cm := s.callerMem) (stmt := stmt) hLocsEq rfl with
            | inl hFlt =>
              let ⟨fk, h1, h2⟩ := hFlt
              rw [h1, h2]
            | inr hStp =>
              let ⟨locs', h1, h2⟩ := hStp
              rw [h1, h2]
          | none =>
            dsimp
            cases Nat.beq frame.stmtIdx bbSrc.statements.length with
            | false => rfl
            | true =>
              rw [if_bool_true rfl, if_bool_true rfl]
              cases isConstBranchFoldTerm_elim hTermRel with
              | inl hTermEq =>
                cases evalTerminator_eq_congr (fSrc := frame) (fTgt := frame)
                    (cm := s.callerMem) hLocsEq hClean hTermEq rfl with
                | inl hFlt => let ⟨_, h1, h2⟩ := hFlt; rw [h1, h2]
                | inr hR =>
                  cases hR with
                  | inl hDone => let ⟨_, h1, h2⟩ := hDone; rw [h1, h2]
                  | inr hJmp => let ⟨_, _, h1, h2⟩ := hJmp; rw [h1, h2]
              | inr hFold =>
                let ⟨c, targets, target, hTS, hTT, hRes⟩ := hFold
                rw [resolveConstSwitchTarget_evalTerminator hTS hRes]
                unfold evalTerminator
                rw [hTT]

private theorem constBranchFold_bidirectional_iff_priv
    (pSrc pTgt : Program)
    (hRel : isConstBranchFoldProgram pSrc pTgt = true) :
    PrivFullSemanticEquiv pSrc pTgt := by
  have hRelCopy := hRel
  unfold isConstBranchFoldProgram at hRelCopy
  let ⟨hHdr, hBodies⟩ := bool_and_true hRelCopy
  refine fullSemanticEquiv_of_query_iff hHdr ?_
    (fun q => exact_step_eq_query_iff (constBranchFold_initState_eq q hRel)
      (constBranchFold_evalStep_eq hRel))
    (fun defId args =>
      let hSub := constBranchFold_entryProg defId hRel
      (exact_step_eq_query_iff (constBranchFold_initState_eq { args := args } hSub)
        (constBranchFold_evalStep_eq hSub)).1)
  intro defId bSrc bTgt hBS hBT
  let ⟨bTgt', hBT', hBody⟩ := listRel_getElem?_left hBodies hBS
  rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
  let ⟨hBHdr, hBLen, hSt, _⟩ := constBranchFoldBody_storage_eq hBody
  exact ⟨hBHdr, list_isEmpty_eq_of_length hBLen, hSt⟩

/-! #### Pass 4 (`AcyclicGotoThread`, Theorem 4) -/

private theorem reachesRankedEmptyGoto_step_elim {bSrc : Body} {ranks : List Nat}
    {k : Nat} {cur dst : BasicBlockId}
    (hReach : reachesRankedEmptyGoto bSrc ranks k cur dst = true)
    (hNe : Nat.beq cur dst = false) :
    ∃ k' bb next,
      k = k' + 1 ∧
      Trusted.MirSemantics.getElem? bSrc.basicBlocks cur = some bb ∧
      bb.cleanup = false ∧
      bb.statements = [] ∧
      bb.terminator = .goto next ∧
      reachesRankedEmptyGoto bSrc ranks k' next dst = true := by
  cases k with
  | zero =>
    dsimp [reachesRankedEmptyGoto] at hReach
    rw [hNe] at hReach; cases hReach
  | succ k' =>
    dsimp [reachesRankedEmptyGoto] at hReach
    rw [if_bool_false hNe] at hReach
    cases hBB : Trusted.MirSemantics.getElem? bSrc.basicBlocks cur with
    | none => rw [hBB] at hReach; cases hReach
    | some bb =>
      rw [hBB] at hReach
      cases hRk : Trusted.MirSemantics.getElem? ranks cur with
      | none => rw [hRk] at hReach; cases hReach
      | some rCur =>
        rw [hRk] at hReach; dsimp at hReach
        cases hEmptyGuard : (!bb.cleanup && bb.statements.isEmpty) with
        | false => rw [if_bool_false hEmptyGuard] at hReach; cases hReach
        | true =>
          rw [if_bool_true hEmptyGuard] at hReach
          let ⟨hNotClean, hEmptyB⟩ := bool_and_true hEmptyGuard
          cases hT : bb.terminator with
          | goto next =>
            rw [hT] at hReach; dsimp at hReach
            cases hRNext : Trusted.MirSemantics.getElem? ranks next with
            | none => rw [hRNext] at hReach; cases hReach
            | some rNext =>
              rw [hRNext] at hReach; dsimp at hReach
              let ⟨_, hNextReach⟩ := bool_and_true hReach
              exact ⟨k', bb, next, rfl, rfl, bool_not_true hNotClean,
                list_eq_nil_of_isEmpty hEmptyB, hT, hNextReach⟩
          | switchInt _ _ => rw [hT] at hReach; cases hReach
          | return_ => rw [hT] at hReach; cases hReach
          | unreachable => rw [hT] at hReach; cases hReach
          | unwindResume => rw [hT] at hReach; cases hReach
          | assert _ _ _ _ _ => rw [hT] at hReach; cases hReach
          | call _ _ _ _ _ => rw [hT] at hReach; cases hReach
          | unsupported => rw [hT] at hReach; cases hReach

private theorem isAcyclicGotoThreadTerm_elim {bSrc : Body} {ranks : List Nat}
    {t₁ t₂ : TerminatorKind}
    (h : isAcyclicGotoThreadTerm bSrc ranks t₁ t₂ = true) :
    (∃ g₁ g₂, t₁ = .goto g₁ ∧ t₂ = .goto g₂ ∧
      canThreadEdge bSrc ranks g₁ g₂ = true) ∨
    (∃ d ts₁ ts₂, t₁ = .switchInt d ts₁ ∧ t₂ = .switchInt d ts₂ ∧
      canThreadEdge bSrc ranks ts₁.otherwise ts₂.otherwise = true ∧
      listRel (fun a b => (a.1 == b.1) && canThreadEdge bSrc ranks a.2 b.2)
        ts₁.branches ts₂.branches = true) ∨
    (t₁ = t₂ ∧
      (∀ g, t₁ ≠ .goto g) ∧
      (∀ d ts, t₁ ≠ .switchInt d ts)) := by
  cases t₁ with
  | goto g₁ =>
    cases t₂ with
    | goto g₂ => left; exact ⟨g₁, g₂, rfl, rfl, h⟩
    | _ => cases h
  | switchInt d₁ ts₁ =>
    cases t₂ with
    | switchInt d₂ ts₂ =>
      dsimp [isAcyclicGotoThreadTerm] at h
      let ⟨h12, hBs⟩ := bool_and_true h
      let ⟨hD, hOw⟩ := bool_and_true h12
      have hDEq : d₁ = d₂ := operandEq_eq hD
      subst hDEq
      right; left; exact ⟨d₁, ts₁, ts₂, rfl, rfl, hOw, hBs⟩
    | _ => cases h
  | return_ =>
    right; right
    exact ⟨terminatorEq_eq h, (fun _ hC => by cases hC), (fun _ _ hC => by cases hC)⟩
  | unreachable =>
    right; right
    exact ⟨terminatorEq_eq h, (fun _ hC => by cases hC), (fun _ _ hC => by cases hC)⟩
  | unwindResume =>
    right; right
    exact ⟨terminatorEq_eq h, (fun _ hC => by cases hC), (fun _ _ hC => by cases hC)⟩
  | assert _ _ _ _ _ =>
    right; right
    exact ⟨terminatorEq_eq h, (fun _ hC => by cases hC), (fun _ _ hC => by cases hC)⟩
  | call _ _ _ _ _ =>
    right; right
    exact ⟨terminatorEq_eq h, (fun _ hC => by cases hC), (fun _ _ hC => by cases hC)⟩
  | unsupported =>
    right; right
    exact ⟨terminatorEq_eq h, (fun _ hC => by cases hC), (fun _ _ hC => by cases hC)⟩

private theorem acyclicGotoBody_storage_eq {ranks : List Nat} {b1 b2 : Body}
    (h : isAcyclicGotoThreadBody ranks b1 b2 = true) :
    bodyHeaderEq b1 b2 = true ∧
    b1.basicBlocks.length = b2.basicBlocks.length ∧
    storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 ∧
    (∀ idx, hasStorageAnnotation b1 idx = hasStorageAnnotation b2 idx) := by
  unfold isAcyclicGotoThreadBody isAcyclicGotoThreadBlocks at h
  let ⟨h12, hBlocks⟩ := bool_and_true h
  let ⟨hBHdr, _⟩ := bool_and_true h12
  let ⟨_, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  refine ⟨hBHdr, listRel_length hBlocks, ?_, ?_⟩
  · unfold storageAnnotationsInBounds
    rw [hLoc]
    exact list_all_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
      let ⟨h12b, _⟩ := bool_and_true hbb
      let ⟨_, hStmts⟩ := bool_and_true h12b
      rw [listRel_eq (fun _ _ => stmtEq_eq) hStmts])
  · intro idx
    unfold hasStorageAnnotation
    exact list_any_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
      let ⟨h12b, _⟩ := bool_and_true hbb
      let ⟨_, hStmts⟩ := bool_and_true h12b
      rw [listRel_eq (fun _ _ => stmtEq_eq) hStmts])

private theorem acyclicGoto_entryProg {ranksList : List (List Nat)}
    {pSrc pTgt : Program} (defId : DefId)
    (h : isAcyclicGotoThreadProgram ranksList pSrc pTgt = true) :
    isAcyclicGotoThreadProgram ranksList
      (entryProgForBody pSrc defId) (entryProgForBody pTgt defId) = true := by
  unfold isAcyclicGotoThreadProgram at h
  let ⟨h12, hZip⟩ := bool_and_true h
  let ⟨hHdr, hRkLen⟩ := bool_and_true h12
  unfold isAcyclicGotoThreadProgram
  exact bool_and_intro (bool_and_intro (programHeaderEq_entryProg defId hHdr) hRkLen) hZip

private theorem acyclicGoto_initState_eq {ranksList : List (List Nat)}
    {pSrc pTgt : Program} (q : Query)
    (h : isAcyclicGotoThreadProgram ranksList pSrc pTgt = true) :
    initState pSrc q = initState pTgt q := by
  unfold isAcyclicGotoThreadProgram at h
  let ⟨h12, hZip⟩ := bool_and_true h
  let ⟨hHdr, hRkLenB⟩ := bool_and_true h12
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  let ⟨_, hSomeZip, hNoneZip⟩ := listRel_zip_left_rel (nat_beq_eq hRkLenB) hZip
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact hNoneZip pSrc.entryDefId
  · intro b1 hB1
    let ⟨ranks, b2, _, hB20, hBody⟩ := hSomeZip pSrc.entryDefId b1 hB1
    have hB2 : Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some b2 := by
      rw [← hEnt]; exact hB20
    let ⟨hBHdr, hBLen, hSt, hHasAnn⟩ := acyclicGotoBody_storage_eq hBody
    let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
    exact ⟨b2, hB2, hBHdr, list_isEmpty_eq_of_length hBLen, hSt,
      initLocalsLoop_eq_of_storage_eq q.args hArg hLoc (fun idx _ _ => hHasAnn idx)⟩

private noncomputable def StateGotoThreadRel (ranksList : List (List Nat))
    (pSrc pTgt : Program) (k : Nat) (s t : State) : Prop :=
  s.callerMem = t.callerMem ∧
  ∃ fSrc fTgt bSrc bTgt ranks,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.locals = fTgt.locals ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt ∧
    Trusted.MirSemantics.getElem? ranksList fSrc.defId = some ranks ∧
    isAcyclicGotoThreadBody ranks bSrc bTgt = true ∧
    ((k = 0 ∧ fSrc.blockIdx = fTgt.blockIdx ∧ fSrc.stmtIdx = fTgt.stmtIdx) ∨
      (fSrc.stmtIdx = 0 ∧ fTgt.stmtIdx = 0 ∧
        reachesRankedEmptyGoto bSrc ranks k fSrc.blockIdx fTgt.blockIdx = true))

private theorem acyclicGoto_sameBlock_sync_step
    {ranksList : List (List Nat)} {pSrc pTgt : Program}
    {s t : State} {fSrc fTgt : FrameState} {bSrc bTgt : Body} {ranks : List Nat}
    (hCm : s.callerMem = t.callerMem)
    (hFS : s.frames = [fSrc]) (hFT : t.frames = [fTgt])
    (hDef : fSrc.defId = fTgt.defId)
    (hLocs : fSrc.locals = fTgt.locals)
    (hBS : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc)
    (hBT : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt)
    (hRk : Trusted.MirSemantics.getElem? ranksList fSrc.defId = some ranks)
    (hBody : isAcyclicGotoThreadBody ranks bSrc bTgt = true)
    (hBlk : fSrc.blockIdx = fTgt.blockIdx)
    (hStmt : fSrc.stmtIdx = fTgt.stmtIdx) :
    SyncStepOutcome pSrc pTgt (StateGotoThreadRel ranksList pSrc pTgt) s t := by
  have hBodyCopy := hBody
  unfold isAcyclicGotoThreadBody isAcyclicGotoThreadBlocks at hBodyCopy
  let ⟨h12, hBlocks⟩ := bool_and_true hBodyCopy
  let ⟨hBHdr, _⟩ := bool_and_true h12
  let ⟨_, hBodyLocs, _, _⟩ := bodyHeaderEq_elim hBHdr
  cases hBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
  | none =>
    have hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
      rw [← hBlk]; exact (listRel_getElem?_none_iff fSrc.blockIdx hBlocks).mp hBBS
    right; right
    refine ⟨.unsupported, ?_, ?_⟩
    · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]
    · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]
  | some bbSrc =>
    let ⟨bbTgt, hBBT0, hRelBB⟩ := listRel_getElem?_left hBlocks hBBS
    have hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
      rw [← hBlk]; exact hBBT0
    let ⟨h12b, hTermRel⟩ := bool_and_true hRelBB
    let ⟨hCleanB, hStmtsRel⟩ := bool_and_true h12b
    have hClean : bbSrc.cleanup = bbTgt.cleanup := bool_beq_eq hCleanB
    have hStmtsEq : bbSrc.statements = bbTgt.statements :=
      listRel_eq (fun _ _ => stmtEq_eq) hStmtsRel
    cases hSS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
    | some st =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some st := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      have hEvS : evalStep pSrc 0 s = evalStatement bSrc fSrc s.callerMem st := by
        unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp; rw [hSS]
      have hEvT : evalStep pTgt 0 t = evalStatement bTgt fTgt s.callerMem st := by
        unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp; rw [hST, ← hCm]
      cases evalStatement_congr_locals (cm := s.callerMem) (stmt := st) hBodyLocs hLocs with
      | inl hFlt =>
        let ⟨fk, h1, h2⟩ := hFlt
        right; right; exact ⟨fk, by rw [hEvS, h1], by rw [hEvT, h2]⟩
      | inr hStp =>
        let ⟨locs', h1, h2⟩ := hStp
        left
        refine ⟨0,
          { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs' }],
            callerMem := s.callerMem },
          { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs' }],
            callerMem := t.callerMem },
          by rw [hEvS, h1], by rw [hEvT, h2, hCm],
          hCm, _, _, bSrc, bTgt, ranks, rfl, rfl, hDef, rfl, hBS, hBT, hRk, hBody,
          Or.inl ⟨rfl, hBlk, by dsimp; rw [hStmt]⟩⟩
    | none =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
      | false =>
        have hEndT : Nat.beq fTgt.stmtIdx bbTgt.statements.length = false := by
          rw [← hStmtsEq, ← hStmt]; exact hEnd
        right; right
        refine ⟨.unsupported, ?_, ?_⟩
        · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
          rw [hSS, if_bool_false hEnd]
        · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
          rw [hST, if_bool_false hEndT]
      | true =>
        have hEndT : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
          rw [← hStmtsEq, ← hStmt]; exact hEnd
        have hEvS : evalStep pSrc 0 s = evalTerminator bSrc bbSrc fSrc s.callerMem := by
          unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
          rw [hSS, if_bool_true hEnd]
        have hEvT : evalStep pTgt 0 t = evalTerminator bTgt bbTgt fTgt s.callerMem := by
          unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
          rw [hST, if_bool_true hEndT, ← hCm]
        cases isAcyclicGotoThreadTerm_elim hTermRel with
        | inl hGoto =>
          let ⟨g₁, g₂, hTS, hTT, hEdge⟩ := hGoto
          left
          refine ⟨bSrc.basicBlocks.length,
            { frames := [{ fSrc with blockIdx := g₁, stmtIdx := 0 }], callerMem := s.callerMem },
            { frames := [{ fTgt with blockIdx := g₂, stmtIdx := 0 }], callerMem := t.callerMem },
            ?_, ?_,
            hCm, _, _, bSrc, bTgt, ranks, rfl, rfl, hDef, hLocs, hBS, hBT, hRk, hBody,
            Or.inr ⟨rfl, rfl, hEdge⟩⟩
          · rw [hEvS]; unfold evalTerminator; rw [hTS]; rfl
          · rw [hEvT]; unfold evalTerminator; rw [hTT, hCm]; rfl
        | inr hRestTerm =>
          cases hRestTerm with
          | inl hSw =>
            let ⟨discr, ts₁, ts₂, hTS, hTT, hOw, hBs⟩ := hSw
            cases hPrim : evalPrimitiveOperand bSrc.locals fSrc.locals discr with
            | error fk =>
              right; right
              refine ⟨fk, ?_, ?_⟩
              · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
              · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                rw [← hBodyLocs, ← hLocs, hPrim]
            | ok res =>
              let ⟨dv, locsAfter⟩ := res
              cases dv with
              | scalar sv =>
                cases evalSwitchBranches_rel (w := sv.width) (discrBits := sv.bits) hOw hBs with
                | inl hFlt =>
                  let ⟨fk, hSw1, hSw2⟩ := hFlt
                  right; right
                  refine ⟨fk, ?_, ?_⟩
                  · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]; dsimp; rw [hSw1]
                  · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hBodyLocs, ← hLocs, hPrim]; dsimp; rw [hSw2]
                | inr hJmp =>
                  let ⟨tgt₁, tgt₂, hSw1, hSw2, hEdge⟩ := hJmp
                  left
                  refine ⟨bSrc.basicBlocks.length,
                    { frames := [{ fSrc with blockIdx := tgt₁, stmtIdx := 0, locals := locsAfter }],
                      callerMem := s.callerMem },
                    { frames := [{ fTgt with blockIdx := tgt₂, stmtIdx := 0, locals := locsAfter }],
                      callerMem := t.callerMem },
                    ?_, ?_,
                    hCm, _, _, bSrc, bTgt, ranks, rfl, rfl, hDef, rfl, hBS, hBT, hRk, hBody,
                    Or.inr ⟨rfl, rfl, hEdge⟩⟩
                  · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]; dsimp; rw [hSw1]; rfl
                  · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hBodyLocs, ← hLocs, hPrim]; dsimp; rw [hSw2, hCm]; rfl
              | bool b =>
                cases evalBoolSwitchBranches_rel (discr := b) hOw hBs with
                | inl hFlt =>
                  let ⟨fk, hSw1, hSw2⟩ := hFlt
                  right; right
                  refine ⟨fk, ?_, ?_⟩
                  · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]; dsimp; rw [hSw1]
                  · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hBodyLocs, ← hLocs, hPrim]; dsimp; rw [hSw2]
                | inr hJmp =>
                  let ⟨tgt₁, tgt₂, hSw1, hSw2, hEdge⟩ := hJmp
                  left
                  refine ⟨bSrc.basicBlocks.length,
                    { frames := [{ fSrc with blockIdx := tgt₁, stmtIdx := 0, locals := locsAfter }],
                      callerMem := s.callerMem },
                    { frames := [{ fTgt with blockIdx := tgt₂, stmtIdx := 0, locals := locsAfter }],
                      callerMem := t.callerMem },
                    ?_, ?_,
                    hCm, _, _, bSrc, bTgt, ranks, rfl, rfl, hDef, rfl, hBS, hBT, hRk, hBody,
                    Or.inr ⟨rfl, rfl, hEdge⟩⟩
                  · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]; dsimp; rw [hSw1]; rfl
                  · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hBodyLocs, ← hLocs, hPrim]; dsimp; rw [hSw2, hCm]; rfl
              | ptr _ =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
              | unit =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
              | enumVal _ _ =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
              | tuple _ =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
              | bytes _ =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
          | inr hOther =>
            let ⟨hTermEq, hNotGoto, hNotSw⟩ := hOther
            cases evalTerminator_eq_congr (cm := s.callerMem) hBodyLocs hClean hTermEq hLocs with
            | inl hFlt =>
              let ⟨fk, h1, h2⟩ := hFlt
              right; right; exact ⟨fk, by rw [hEvS, h1], by rw [hEvT, h2]⟩
            | inr hR =>
              cases hR with
              | inl hDone =>
                let ⟨out, h1, h2⟩ := hDone
                right; left; exact ⟨out, by rw [hEvS, h1], by rw [hEvT, h2]⟩
              | inr hJmp =>
                let ⟨tgt, locs', h1, _⟩ := hJmp
                cases hTS : bbSrc.terminator with
                | goto g => exact False.elim (hNotGoto g hTS)
                | switchInt d ts => exact False.elim (hNotSw d ts hTS)
                | return_ =>
                  unfold evalTerminator at h1; rw [hTS] at h1; dsimp at h1
                  cases hCl : bbSrc.cleanup with
                  | true => rw [if_bool_true hCl] at h1; cases h1
                  | false =>
                    rw [if_bool_false hCl] at h1
                    cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
                    | none => rw [h0] at h1; cases h1
                    | some sl =>
                      rw [h0] at h1
                      cases sl with
                      | dead => cases h1
                      | live opt => cases opt <;> cases h1
                | unreachable => unfold evalTerminator at h1; rw [hTS] at h1; cases h1
                | unwindResume => unfold evalTerminator at h1; rw [hTS] at h1; cases h1
                | assert _ _ _ _ _ => unfold evalTerminator at h1; rw [hTS] at h1; cases h1
                | call _ _ _ _ _ => unfold evalTerminator at h1; rw [hTS] at h1; cases h1
                | unsupported => unfold evalTerminator at h1; rw [hTS] at h1; cases h1

private theorem acyclicGoto_stutter_step {ranksList : List (List Nat)}
    {pSrc pTgt : Program} {k : Nat} {s t : State}
    (hRel : StateGotoThreadRel ranksList pSrc pTgt k s t) :
    StutterStepOutcome pSrc pTgt (StateGotoThreadRel ranksList pSrc pTgt) k s t := by
  let ⟨hCm, fSrc, fTgt, bSrc, bTgt, ranks, hFS, hFT, hDef, hLocs,
       hBS, hBT, hRk, hBody, hMode⟩ := hRel
  cases hMode with
  | inl hSame =>
    right
    exact acyclicGoto_sameBlock_sync_step hCm hFS hFT hDef hLocs hBS hBT hRk hBody
      hSame.2.1 hSame.2.2
  | inr hChain =>
    let ⟨hStmtS, hStmtT, hReach⟩ := hChain
    cases hEqBlk : Nat.beq fSrc.blockIdx fTgt.blockIdx with
    | true =>
      right
      exact acyclicGoto_sameBlock_sync_step hCm hFS hFT hDef hLocs hBS hBT hRk hBody
        (nat_beq_eq hEqBlk) (by rw [hStmtS, hStmtT])
    | false =>
      let ⟨k', bb, next, hKEq, hBBS, _, hStmtsNil, hTermGoto, hReachNext⟩ :=
        reachesRankedEmptyGoto_step_elim hReach hEqBlk
      left
      refine ⟨k',
        { frames := [{ fSrc with blockIdx := next, stmtIdx := 0 }], callerMem := s.callerMem },
        hKEq, ?_,
        hCm, _, fTgt, bSrc, bTgt, ranks, rfl, hFT, hDef, hLocs, hBS, hBT, hRk, hBody,
        Or.inr ⟨rfl, hStmtT, hReachNext⟩⟩
      unfold evalStep
      rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
      rw [hStmtsNil, hStmtS]; dsimp [Trusted.MirSemantics.getElem?, List.length, Nat.beq]
      unfold evalTerminator
      rw [hTermGoto]
      rfl

private theorem acyclicGoto_query_iff {ranksList : List (List Nat)}
    {pSrc pTgt : Program} (q : Query)
    (hRel : isAcyclicGotoThreadProgram ranksList pSrc pTgt = true) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := acyclicGoto_initState_eq q hRel
  apply stutter_bisim_lift (R := StateGotoThreadRel ranksList pSrc pTgt)
  · intro k; rw [hInitEq]
  · intro s₀ t₀ hIS hIT
    have hISCopy := hIS
    rw [hInitEq] at hIS
    have hEqST : s₀ = t₀ := by rw [hIS] at hIT; injection hIT
    subst hEqST
    let ⟨_, _, bSrc, hBS, _, _, _, _, _, hS0⟩ := initState_ok_elim hISCopy
    unfold isAcyclicGotoThreadProgram at hRel
    let ⟨h12, hZip⟩ := bool_and_true hRel
    let ⟨hHdr, hRkLenB⟩ := bool_and_true h12
    let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
    let ⟨_, hSomeZip, _⟩ := listRel_zip_left_rel (nat_beq_eq hRkLenB) hZip
    let ⟨ranks, bTgt, hRk, hBT0, hBody⟩ := hSomeZip pSrc.entryDefId bSrc hBS
    subst hS0
    exact ⟨0, rfl, _, _, bSrc, bTgt, ranks, rfl, rfl, rfl, rfl, hBS, hBT0, hRk, hBody,
      Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro k s t hR
    exact acyclicGoto_stutter_step hR

private theorem acyclicGotoThread_bidirectional_iff_priv
    (pSrc pTgt : Program) (ranksList : List (List Nat))
    (hRel : isAcyclicGotoThreadProgram ranksList pSrc pTgt = true) :
    PrivFullSemanticEquiv pSrc pTgt := by
  have hRelCopy := hRel
  unfold isAcyclicGotoThreadProgram at hRelCopy
  let ⟨h12, hZip⟩ := bool_and_true hRelCopy
  let ⟨hHdr, hRkLenB⟩ := bool_and_true h12
  let ⟨_, hSomeZip, _⟩ := listRel_zip_left_rel (nat_beq_eq hRkLenB) hZip
  refine fullSemanticEquiv_of_query_iff hHdr ?_
    (fun q => acyclicGoto_query_iff q hRel)
    (fun defId args => (acyclicGoto_query_iff { args := args } (acyclicGoto_entryProg defId hRel)).1)
  intro defId bSrc bTgt hBS hBT
  let ⟨ranks, bTgt', _, hBT', hBody⟩ := hSomeZip defId bSrc hBS
  rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
  let ⟨hBHdr, hBLen, hSt, _⟩ := acyclicGotoBody_storage_eq hBody
  exact ⟨hBHdr, list_isEmpty_eq_of_length hBLen, hSt⟩

/-! ### Stage 4 Private Helpers — Layer D: Slot Refinement & Pass 3 (3a/3b) -/

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
    rw [h]; rfl
  | bool => rfl
  | int _ _ => rfl
  | never => rfl
  | tuple _ => rfl
  | ref _ _ => rfl
  | rawPtr _ _ => rfl
  | unsupported => rfl

private theorem not_zst_of_primitiveReadable {ty : MirTy}
    (h : isPrimitiveReadableTy ty = true) :
    isAlwaysInhabitedZst ty = false := by
  cases ty <;> first | rfl | cases h

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
      rw [hZst]; rfl
    | bool => cases hZst
    | int _ _ => cases hZst
    | never => cases hZst
    | tuple _ => cases hZst
    | ref _ _ => cases hZst
    | rawPtr _ _ => cases hZst
    | unsupported => cases hZst

private noncomputable def SlotFwdRefines : LocalSlot → LocalSlot → Prop
  | .dead, _ => True
  | .live none, .live _ => True
  | .live (some v1), .live (some v2) => v1 = v2
  | _, _ => False

private theorem slotFwdRefines_refl_live (opt : Option Val) :
    SlotFwdRefines (.live opt) (.live opt) := by
  cases opt with
  | none => exact True.intro
  | some _ => rfl

private theorem slotFwdRefines_liveUninit_left {ty : MirTy}
    {optTgt : Option Val} (hWt : SlotWellTyped ty (.live optTgt)) :
    SlotFwdRefines (liveUninitSlot ty) (.live optTgt) := by
  cases hZ : isAlwaysInhabitedZst ty with
  | false =>
    rw [liveUninitSlot_of_not_zst hZ]
    exact True.intro
  | true =>
    rw [slot_eq_liveUninit_of_zst hZ hWt]
    let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
    rw [hOpt]
    exact slotFwdRefines_refl_live opt

private noncomputable def LocalsFwdRefines (bodyLocals : List MirTy)
    (localsSrc localsTgt : List LocalSlot) : Prop :=
  localsSrc.length = bodyLocals.length ∧
  localsTgt.length = bodyLocals.length ∧
  ∀ i ty s1 s2,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? localsSrc i = some s1 →
    Trusted.MirSemantics.getElem? localsTgt i = some s2 →
    SlotFwdRefines s1 s2 ∧ SlotWellTyped ty s2

private theorem localsFwdRefines_set_both
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' localsTgt' : List LocalSlot}
    {id : Nat} {ty : MirTy} {s1' s2' : LocalSlot}
    (hInv : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSet1 : setElem? localsSrc id s1' = some localsSrc')
    (hSet2 : setElem? localsTgt id s2' = some localsTgt')
    (hSlot : SlotFwdRefines s1' s2')
    (hWt : SlotWellTyped ty s2') :
    LocalsFwdRefines bodyLocals localsSrc' localsTgt' := by
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

private theorem localsFwdRefines_set_left
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {id : Nat} {ty : MirTy} {s1' s2 : LocalSlot}
    (hInv : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hGet2 : Trusted.MirSemantics.getElem? localsTgt id = some s2)
    (hSet1 : setElem? localsSrc id s1' = some localsSrc')
    (hSlot : SlotFwdRefines s1' s2) :
    LocalsFwdRefines bodyLocals localsSrc' localsTgt := by
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

private theorem evalOperandToSlot_fwd_eq
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {op : Operand} {ty : MirTy} {v : Val}
    (hInv : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hEval : evalOperandToSlot bodyLocals localsSrc op =
      .ok (ty, some v, localsSrc')) :
    ∃ localsTgt',
      evalOperandToSlot bodyLocals localsTgt op =
        .ok (ty, some v, localsTgt') ∧
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' := by
  let ⟨_, hLen2, hAll⟩ := hInv
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot] at hEval
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at hEval; cases hEval
    | ok val =>
      rw [hC] at hEval
      injection hEval with hEq
      injection hEq with hTyEq hRest
      injection hRest with hVEq hLocEq
      injection hVEq with hV
      subst hTyEq; subst hV; subst hLocEq
      refine ⟨localsTgt, ?_, hInv⟩
      dsimp [evalOperandToSlot]; rw [hC]
  | copy p =>
    dsimp [evalOperandToSlot] at hEval
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hEval; cases hEval
    | true =>
      rw [hProj] at hEval; dsimp at hEval
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some t =>
        rw [hTy] at hEval
        cases hS1 : Trusted.MirSemantics.getElem? localsSrc p.localId with
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
            let ⟨slot2, hS2⟩ := getElem?_some_of_lt localsTgt p.localId
              (by rw [hLen2]; exact getElem?_some_lt hTy)
            let ⟨hRef, _⟩ := hAll p.localId t (.live (some v)) slot2 hTy hS1 hS2
            cases slot2 with
            | dead => cases hRef
            | live opt2 =>
              cases opt2 with
              | none => cases hRef
              | some v2 =>
                have hv : v = v2 := hRef
                subst hv
                refine ⟨localsTgt, ?_, hInv⟩
                dsimp [evalOperandToSlot]; rw [hProj, hTy, hS2]; rfl
  | move p =>
    dsimp [evalOperandToSlot] at hEval
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hEval; cases hEval
    | true =>
      rw [hProj] at hEval; dsimp at hEval
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some t =>
        rw [hTy] at hEval
        cases hS1 : Trusted.MirSemantics.getElem? localsSrc p.localId with
        | none => rw [hS1] at hEval; cases hEval
        | some slot1 =>
          rw [hS1] at hEval
          cases slot1 with
          | dead => cases hEval
          | live opt1 =>
            dsimp at hEval
            cases hSet1 : setElem? localsSrc p.localId (liveUninitSlot t) with
            | none => rw [hSet1] at hEval; cases hEval
            | some locs1' =>
              rw [hSet1] at hEval
              injection hEval with hEq
              injection hEq with hTyEq hRest
              injection hRest with hOptEq hLocEq
              subst hTyEq; subst hOptEq; subst hLocEq
              let ⟨slot2, hS2⟩ := getElem?_some_of_lt localsTgt p.localId
                (by rw [hLen2]; exact getElem?_some_lt hTy)
              let ⟨hRef, _⟩ := hAll p.localId t (.live (some v)) slot2 hTy hS1 hS2
              cases slot2 with
              | dead => cases hRef
              | live opt2 =>
                cases opt2 with
                | none => cases hRef
                | some v2 =>
                  have hv : v = v2 := hRef
                  subst hv
                  let ⟨locs2', hSet2⟩ := setElem?_some_of_lt localsTgt p.localId
                    (liveUninitSlot t) (by rw [hLen2]; exact getElem?_some_lt hTy)
                  let ⟨optU, hOptU⟩ := liveUninitSlot_isLive t
                  refine ⟨locs2', ?_, localsFwdRefines_set_both hInv hTy hSet1 hSet2
                    (by rw [hOptU]; exact slotFwdRefines_refl_live optU)
                    (liveUninitSlot_wellTyped t)⟩
                  dsimp [evalOperandToSlot]
                  rw [hProj, hTy, hS2]; dsimp; rw [hSet2]

private theorem evalPrimitiveOperand_fwd_eq
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {op : Operand} {v : Val}
    (hInv : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hEval : evalPrimitiveOperand bodyLocals localsSrc op = .ok (v, localsSrc')) :
    ∃ localsTgt',
      evalPrimitiveOperand bodyLocals localsTgt op = .ok (v, localsTgt') ∧
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' := by
  dsimp [evalPrimitiveOperand] at hEval
  cases hS : evalOperandToSlot bodyLocals localsSrc op with
  | error _ => rw [hS] at hEval; cases hEval
  | ok res =>
    let ⟨ty, optVal, locs1⟩ := res
    rw [hS] at hEval; dsimp at hEval
    cases hPrim : isPrimitiveReadableTy ty with
    | false => rw [hPrim] at hEval; cases hEval
    | true =>
      rw [hPrim] at hEval; dsimp at hEval
      cases optVal with
      | none => cases hEval
      | some v0 =>
        injection hEval with hEq
        injection hEq with hV hL
        subst hV; subst hL
        let ⟨locs2, hT, hInv'⟩ := evalOperandToSlot_fwd_eq hInv hS
        refine ⟨locs2, ?_, hInv'⟩
        dsimp [evalPrimitiveOperand]; rw [hT]; dsimp; rw [hPrim]; rfl

private theorem evalPrimitiveOperand_collapsed_fwd
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {discr : Operand} {dv : Val}
    (hInv : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hEval : evalPrimitiveOperand bodyLocals localsSrc discr = .ok (dv, localsSrc')) :
    LocalsFwdRefines bodyLocals localsSrc' localsTgt := by
  let ⟨_, hLen2, hAll⟩ := hInv
  dsimp [evalPrimitiveOperand] at hEval
  cases hS : evalOperandToSlot bodyLocals localsSrc discr with
  | error _ => rw [hS] at hEval; cases hEval
  | ok res =>
    let ⟨ty, optVal, locs1⟩ := res
    rw [hS] at hEval; dsimp at hEval
    cases hPrim : isPrimitiveReadableTy ty with
    | false => rw [hPrim] at hEval; cases hEval
    | true =>
      rw [hPrim] at hEval; dsimp at hEval
      cases optVal with
      | none => cases hEval
      | some v0 =>
        injection hEval with hEq
        injection hEq with hV hL
        subst hV; subst hL
        cases discr with
        | constant c =>
          dsimp [evalOperandToSlot] at hS
          cases hC : evalConstLit c.ty c.lit with
          | error _ => rw [hC] at hS; cases hS
          | ok cv =>
            rw [hC] at hS; injection hS with hEq2
            injection hEq2 with _ hR2; injection hR2 with _ hLEq
            subst hLEq; exact hInv
        | copy p =>
          dsimp [evalOperandToSlot] at hS
          cases hProj : p.projection.isEmpty with
          | false => rw [hProj] at hS; cases hS
          | true =>
            rw [hProj] at hS; dsimp at hS
            cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
            | none => rw [hTy] at hS; cases hS
            | some t =>
              rw [hTy] at hS
              cases hG1 : Trusted.MirSemantics.getElem? localsSrc p.localId with
              | none => rw [hG1] at hS; cases hS
              | some sl1 =>
                rw [hG1] at hS
                cases sl1 with
                | dead => cases hS
                | live o1 =>
                  dsimp at hS; injection hS with hEq2
                  injection hEq2 with _ hR2; injection hR2 with _ hLEq
                  subst hLEq; exact hInv
        | move p =>
          dsimp [evalOperandToSlot] at hS
          cases hProj : p.projection.isEmpty with
          | false => rw [hProj] at hS; cases hS
          | true =>
            rw [hProj] at hS; dsimp at hS
            cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
            | none => rw [hTy] at hS; cases hS
            | some t =>
              rw [hTy] at hS
              cases hG1 : Trusted.MirSemantics.getElem? localsSrc p.localId with
              | none => rw [hG1] at hS; cases hS
              | some sl1 =>
                rw [hG1] at hS
                cases sl1 with
                | dead => cases hS
                | live o1 =>
                  dsimp at hS
                  cases hSet1 : setElem? localsSrc p.localId (liveUninitSlot t) with
                  | none => rw [hSet1] at hS; cases hS
                  | some l1' =>
                    rw [hSet1] at hS; injection hS with hEq2
                    injection hEq2 with hTyEq hR2; injection hR2 with hOptEq hLEq
                    subst hTyEq; subst hOptEq; subst hLEq
                    let ⟨sl2, hG2⟩ := getElem?_some_of_lt localsTgt p.localId
                      (by rw [hLen2]; exact getElem?_some_lt hTy)
                    let ⟨hRef, hWt2⟩ := hAll p.localId _ _ sl2 hTy hG1 hG2
                    cases sl2 with
                    | dead => cases hRef
                    | live o2 =>
                      exact localsFwdRefines_set_left hInv hTy hG2 hSet1
                        (slotFwdRefines_liveUninit_left hWt2)

private theorem evalRvalue_fwd_eq
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hInv : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hEval : evalRvalue bodyLocals localsSrc dstTy rv = .ok (v, localsSrc')) :
    ∃ localsTgt',
      evalRvalue bodyLocals localsTgt dstTy rv = .ok (v, localsTgt') ∧
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' := by
  cases rv with
  | use o =>
    dsimp [evalRvalue] at hEval
    cases hS : evalOperandToSlot bodyLocals localsSrc o with
    | error _ => rw [hS] at hEval; cases hEval
    | ok res =>
      let ⟨srcTy, optVal, locs1⟩ := res
      rw [hS] at hEval; dsimp at hEval
      cases hEqTy : MirTy.beq srcTy dstTy with
      | false => rw [hEqTy] at hEval; cases hEval
      | true =>
        rw [hEqTy] at hEval; dsimp at hEval
        cases optVal with
        | none => cases hEval
        | some v0 =>
          injection hEval with hEq
          injection hEq with hV hL
          subst hV; subst hL
          let ⟨locs2, hT, hInv'⟩ := evalOperandToSlot_fwd_eq hInv hS
          refine ⟨locs2, ?_, hInv'⟩
          dsimp [evalRvalue]; rw [hT]; dsimp; rw [hEqTy]; rfl
  | binaryOp op l r =>
    dsimp [evalRvalue] at hEval
    cases hEL : evalPrimitiveOperand bodyLocals localsSrc l with
    | error _ => rw [hEL] at hEval; cases hEval
    | ok resL =>
      let ⟨lv, locs1⟩ := resL
      rw [hEL] at hEval; dsimp at hEval
      cases hER : evalPrimitiveOperand bodyLocals locs1 r with
      | error _ => rw [hER] at hEval; cases hEval
      | ok resR =>
        let ⟨rvVal, locs2⟩ := resR
        rw [hER] at hEval; dsimp at hEval
        cases hBin : evalBinOp op lv rvVal with
        | error _ => rw [hBin] at hEval; cases hEval
        | ok resV =>
          rw [hBin] at hEval
          injection hEval with hEq
          injection hEq with hV hLoc
          subst hV; subst hLoc
          let ⟨tLocs1, hTL, hInv1⟩ := evalPrimitiveOperand_fwd_eq hInv hEL
          let ⟨tLocs2, hTR, hInv2⟩ := evalPrimitiveOperand_fwd_eq hInv1 hER
          refine ⟨tLocs2, ?_, hInv2⟩
          dsimp [evalRvalue]; rw [hTL]; dsimp; rw [hTR]; dsimp; rw [hBin]
  | unaryOp op o =>
    dsimp [evalRvalue] at hEval
    cases hEO : evalPrimitiveOperand bodyLocals localsSrc o with
    | error _ => rw [hEO] at hEval; cases hEval
    | ok resO =>
      let ⟨ov, locs1⟩ := resO
      rw [hEO] at hEval; dsimp at hEval
      cases hUn : evalUnOp op ov with
      | error _ => rw [hUn] at hEval; cases hEval
      | ok resV =>
        rw [hUn] at hEval
        injection hEval with hEq
        injection hEq with hV hLoc
        subst hV; subst hLoc
        let ⟨tLocs1, hTO, hInv1⟩ := evalPrimitiveOperand_fwd_eq hInv hEO
        refine ⟨tLocs1, ?_, hInv1⟩
        dsimp [evalRvalue]; rw [hTO]; dsimp; rw [hUn]
  | discriminant p =>
    let ⟨_, hLen2, hAll⟩ := hInv
    dsimp [evalRvalue] at hEval
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hEval; cases hEval
    | true =>
      rw [hProj] at hEval; dsimp at hEval
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some ty =>
        rw [hTy] at hEval
        cases ty with
        | enum ety =>
          cases hS1 : Trusted.MirSemantics.getElem? localsSrc p.localId with
          | none => rw [hS1] at hEval; cases hEval
          | some slot1 =>
            rw [hS1] at hEval; dsimp at hEval
            cases hAdm : enumAdmitted ety with
            | false => rw [hAdm] at hEval; cases hEval
            | true =>
              rw [hAdm] at hEval; dsimp at hEval
              let ⟨slot2, hS2⟩ := getElem?_some_of_lt localsTgt p.localId
                (by rw [hLen2]; exact getElem?_some_lt hTy)
              let ⟨hRef, hWt2⟩ := hAll p.localId (.enum ety) slot1 slot2 hTy hS1 hS2
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
                      unfold isZstEnumTy; rw [hTr]; exact hAdm
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
                        rw [hProj, hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp
                        rw [enumTy_beq_refl ety]; dsimp [Nat.beq]; rw [hD]
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
                        rw [hProj, hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp
                        rw [enumTy_beq_refl ety]; dsimp [Nat.beq]; rw [hD]
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
                            rw [hC] at hEval; dsimp at hEval
                            cases hD : Trusted.MirSemantics.getElem? ety.discriminants k with
                            | none => rw [hD] at hEval; cases hEval
                            | some disc =>
                              rw [hD] at hEval
                              injection hEval with hEq
                              injection hEq with hV hL
                              subst hV; subst hL
                              refine ⟨localsTgt, ?_, hInv⟩
                              dsimp [evalRvalue]
                              rw [hProj, hTy, hS2]; dsimp; rw [hAdm]; dsimp
                              rw [hTr]; dsimp; rw [hC]; dsimp; rw [hD]
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
  | ref _ _ => cases hEval
  | addressOf _ _ => cases hEval
  | aggregateTuple _ => cases hEval
  | unsupported => cases hEval

private theorem writePlace_fwd
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {dstId : LocalId} {dstTy : MirTy} {val : Val}
    (hInv : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (hWrite : writePlace localsSrc dstId dstTy val = .ok localsSrc') :
    ∃ localsTgt',
      writePlace localsTgt dstId dstTy val = .ok localsTgt' ∧
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' := by
  let ⟨_, hLen2, hAll⟩ := hInv
  dsimp [writePlace] at hWrite
  cases hChk : checkVal val dstTy with
  | false => rw [hChk] at hWrite; cases hWrite
  | true =>
    rw [hChk] at hWrite; dsimp at hWrite
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
          | live _ =>
            let ⟨locs2', hSet2⟩ := setElem?_some_of_lt localsTgt dstId
              (.live (some val)) (by rw [hLen2]; exact getElem?_some_lt hTy)
            refine ⟨locs2', ?_, localsFwdRefines_set_both hInv hTy hSet1 hSet2 rfl hChk⟩
            dsimp [writePlace]; rw [hChk]; dsimp; rw [hS2]; dsimp; rw [hSet2]

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

private theorem evalStatement_fwd_eq
    {bSrc bTgt : Body} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {stmt : StatementKind} {s' : State}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hInv : LocalsFwdRefines bSrc.locals fSrc.locals fTgt.locals)
    (hEv : evalStatement bSrc fSrc cm stmt = .step s') :
    ∃ locs1' locs2',
      s' = { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' }],
             callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' }],
                callerMem := cm } ∧
      LocalsFwdRefines bSrc.locals locs1' locs2' := by
  let ⟨hLen1, hLen2, _⟩ := hInv
  cases stmt with
  | nop =>
    injection hEv with hEq; subst hEq
    exact ⟨fSrc.locals, fTgt.locals, rfl, rfl, hInv⟩
  | unsupported => cases hEv
  | storageLive i1 =>
    dsimp [evalStatement] at hEv
    cases hTy : Trusted.MirSemantics.getElem? bSrc.locals i1 with
    | none => rw [hTy] at hEv; cases hEv
    | some ty =>
      rw [hTy] at hEv; dsimp at hEv
      cases hSet1 : setElem? fSrc.locals i1 (liveUninitSlot ty) with
      | none => rw [hSet1] at hEv; cases hEv
      | some locs1' =>
        rw [hSet1] at hEv; injection hEv with hEq; subst hEq
        let ⟨locs2', hSet2⟩ := setElem?_some_of_lt fTgt.locals i1
          (liveUninitSlot ty) (by rw [hLen2]; exact getElem?_some_lt hTy)
        let ⟨optU, hOptU⟩ := liveUninitSlot_isLive ty
        refine ⟨locs1', locs2', rfl, ?_,
          localsFwdRefines_set_both hInv hTy hSet1 hSet2
            (by rw [hOptU]; exact slotFwdRefines_refl_live optU)
            (liveUninitSlot_wellTyped ty)⟩
        dsimp [evalStatement]; rw [← hLocEq, hTy]; dsimp; rw [hSet2]
  | storageDead i1 =>
    dsimp [evalStatement] at hEv
    cases hZ : Nat.beq i1 0 with
    | true => rw [hZ] at hEv; cases hEv
    | false =>
      rw [hZ] at hEv; dsimp at hEv
      cases hSet1 : setElem? fSrc.locals i1 .dead with
      | none => rw [hSet1] at hEv; cases hEv
      | some locs1' =>
        rw [hSet1] at hEv; injection hEv with hEq; subst hEq
        have hLt1 : i1 < bSrc.locals.length := by
          cases Nat.lt_or_ge i1 bSrc.locals.length with
          | inl hlt => exact hlt
          | inr hge =>
            have hNone := setElem?_none_of_ge fSrc.locals i1 .dead
              (by rw [hLen1]; exact hge)
            rw [hNone] at hSet1; cases hSet1
        let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals i1 hLt1
        let ⟨locs2', hSet2⟩ := setElem?_some_of_lt fTgt.locals i1 .dead
          (by rw [hLen2]; exact hLt1)
        refine ⟨locs1', locs2', rfl, ?_,
          localsFwdRefines_set_both hInv hTy hSet1 hSet2 True.intro True.intro⟩
        dsimp [evalStatement]; rw [hZ]; dsimp; rw [hSet2]
  | assign d1 rv1 =>
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
            rw [hW] at hEv; injection hEv with hEq; subst hEq
            let ⟨locs2, hR2, hInv1⟩ := evalRvalue_fwd_eq hInv hR
            let ⟨locs2', hW2, hInv2⟩ := writePlace_fwd hInv1 hTy hW
            refine ⟨locs1', locs2', rfl, ?_, hInv2⟩
            dsimp [evalStatement]; rw [hP]; dsimp
            rw [← hLocEq, hTy]; dsimp; rw [hR2]; dsimp; rw [hW2]

private theorem initLocalsLoop_fwd_of_ann_imp {bSrc bTgt : Body} {args : List Val}
    (hArgEq : bSrc.argumentCount = bTgt.argumentCount)
    (hLocEq : bSrc.locals = bTgt.locals)
    (hArgs : checkArgsMatch args ((bSrc.locals.drop 1).take bSrc.argumentCount) = true)
    (hAnnImp : ∀ idx, idx < bSrc.locals.length →
      Nat.ble idx bSrc.argumentCount = false →
      hasStorageAnnotation bTgt idx = true →
      hasStorageAnnotation bSrc idx = true) :
    LocalsFwdRefines bSrc.locals
      (initLocalsLoop bSrc args 0 bSrc.locals)
      (initLocalsLoop bTgt args 0 bTgt.locals) := by
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
    exact ⟨by rw [hOpt]; exact slotFwdRefines_refl_live opt,
           liveUninitSlot_wellTyped ty⟩
  | succ k =>
    dsimp [Nat.beq]
    rw [← hArgEq]
    cases hLe : Nat.ble (k + 1) bSrc.argumentCount with
    | true =>
      have hKlt : k < bSrc.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((bSrc.locals.drop 1).take bSrc.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 bSrc.locals bSrc.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]
      exact ⟨rfl, hChk⟩
    | false =>
      cases hAnnT : hasStorageAnnotation bTgt (k + 1) with
      | true =>
        have hAnnS : hasStorageAnnotation bSrc (k + 1) = true :=
          hAnnImp (k + 1) (getElem?_some_lt hTy) hLe hAnnT
        rw [hAnnS]
        exact ⟨True.intro, True.intro⟩
      | false =>
        let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
        cases hasStorageAnnotation bSrc (k + 1) with
        | true =>
          exact ⟨True.intro, liveUninitSlot_wellTyped ty⟩
        | false =>
          exact ⟨by rw [hOpt]; exact slotFwdRefines_refl_live opt,
                 liveUninitSlot_wellTyped ty⟩

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

/-! #### Theorem 3a: Forward Codegen Refinement (`UniformBranchCollapse`) -/

private theorem isUniformBranchCollapseTerm_elim {t₁ t₂ : TerminatorKind}
    (h : isUniformBranchCollapseTerm t₁ t₂ = true) :
    t₁ = t₂ ∨
    ∃ discr targets target,
      t₁ = .switchInt discr targets ∧
      t₂ = .goto target ∧
      allSwitchTargetsEq targets target = true := by
  cases t₁ with
  | switchInt discr targets =>
    cases t₂ with
    | goto target => right; exact ⟨discr, targets, target, rfl, rfl, h⟩
    | switchInt _ _ => left; exact terminatorEq_eq h
    | return_ => cases h
    | unreachable => cases h
    | unwindResume => cases h
    | assert _ _ _ _ _ => cases h
    | call _ _ _ _ _ => cases h
    | unsupported => cases h
  | goto _ => left; exact terminatorEq_eq h
  | return_ => left; exact terminatorEq_eq h
  | unreachable => left; exact terminatorEq_eq h
  | unwindResume => left; exact terminatorEq_eq h
  | assert _ _ _ _ _ => left; exact terminatorEq_eq h
  | call _ _ _ _ _ => left; exact terminatorEq_eq h
  | unsupported => left; exact terminatorEq_eq h

private theorem uniformBranchBody_storage_eq {b1 b2 : Body}
    (h : isUniformBranchCollapseBody b1 b2 = true) :
    bodyHeaderEq b1 b2 = true ∧
    b1.basicBlocks.length = b2.basicBlocks.length ∧
    storageAnnotationsInBounds b1 = storageAnnotationsInBounds b2 ∧
    (∀ idx, hasStorageAnnotation b1 idx = hasStorageAnnotation b2 idx) := by
  unfold isUniformBranchCollapseBody at h
  let ⟨hBHdr, hBlocks⟩ := bool_and_true h
  let ⟨_, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  refine ⟨hBHdr, listRel_length hBlocks, ?_, ?_⟩
  · unfold storageAnnotationsInBounds
    rw [hLoc]
    exact list_all_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
      unfold isUniformBranchCollapseBlock at hbb
      let ⟨h12, _⟩ := bool_and_true hbb
      let ⟨_, hStmts⟩ := bool_and_true h12
      rw [listRel_eq (fun _ _ => stmtEq_eq) hStmts])
  · intro idx
    unfold hasStorageAnnotation
    exact list_any_eq_of_rel hBlocks (fun bb1 bb2 hbb => by
      unfold isUniformBranchCollapseBlock at hbb
      let ⟨h12, _⟩ := bool_and_true hbb
      let ⟨_, hStmts⟩ := bool_and_true h12
      rw [listRel_eq (fun _ _ => stmtEq_eq) hStmts])

private theorem uniformBranch_entryProg {pSrc pTgt : Program} (defId : DefId)
    (h : isUniformBranchCollapseProgram pSrc pTgt = true) :
    isUniformBranchCollapseProgram (entryProgForBody pSrc defId)
      (entryProgForBody pTgt defId) = true := by
  unfold isUniformBranchCollapseProgram at h
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  unfold isUniformBranchCollapseProgram
  exact bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies

private theorem uniformBranch_initState_eq {pSrc pTgt : Program} (q : Query)
    (h : isUniformBranchCollapseProgram pSrc pTgt = true) :
    initState pSrc q = initState pTgt q := by
  unfold isUniformBranchCollapseProgram at h
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]
    exact listRel_getElem?_none_iff pSrc.entryDefId hBodies
  · intro b1 hB1
    let ⟨b2, hB20, hRelB⟩ := listRel_getElem?_left hBodies hB1
    have hB2 : Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some b2 := by
      rw [← hEnt]; exact hB20
    let ⟨hBHdr, hBLen, hSt, hHasAnn⟩ := uniformBranchBody_storage_eq hRelB
    let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
    exact ⟨b2, hB2, hBHdr, list_isEmpty_eq_of_length hBLen, hSt,
      initLocalsLoop_eq_of_storage_eq q.args hArg hLoc (fun idx _ _ => hHasAnn idx)⟩

private noncomputable def StateUniformFwdRel (pSrc pTgt : Program)
    (s t : State) : Prop :=
  s.callerMem = t.callerMem ∧
  ∃ fSrc fTgt bSrc bTgt,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt ∧
    isUniformBranchCollapseBody bSrc bTgt = true ∧
    LocalsFwdRefines bSrc.locals fSrc.locals fTgt.locals

private theorem evalTerminator_eq_fwd
    {bSrc bTgt : Body} {bbSrc bbTgt : BasicBlock}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hLocsEq : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hTermEq : bbSrc.terminator = bbTgt.terminator)
    (hInv : LocalsFwdRefines bSrc.locals fSrc.locals fTgt.locals) :
    (∀ s', evalTerminator bSrc bbSrc fSrc cm = .step s' →
      ∃ tgt locs1' locs2',
        s' = { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs1' }],
               callerMem := cm } ∧
        evalTerminator bTgt bbTgt fTgt cm =
          .step { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' }],
                  callerMem := cm } ∧
        LocalsFwdRefines bSrc.locals locs1' locs2') ∧
    (∀ out, evalTerminator bSrc bbSrc fSrc cm = .done out →
      evalTerminator bTgt bbTgt fTgt cm = .done out) := by
  cases hTS : bbSrc.terminator with
  | goto tgt =>
    constructor
    · intro s' hEv
      unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp [jumpToBlock] at hEv
      injection hEv with hEqS; subst hEqS
      refine ⟨tgt, fSrc.locals, fTgt.locals, rfl, ?_, hInv⟩
      unfold evalTerminator; rw [← hTermEq, hTS]; rfl
    · intro out hEv
      unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv
  | return_ =>
    constructor
    · intro s' hEv
      unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
      cases hC : bbSrc.cleanup with
      | true => rw [hC] at hEv; cases hEv
      | false =>
        rw [hC] at hEv; dsimp at hEv
        cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
        | none => rw [h0] at hEv; cases hEv
        | some sl =>
          rw [h0] at hEv
          cases sl with
          | dead => cases hEv
          | live opt => cases opt <;> cases hEv
    · intro out hEv
      unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
      cases hC : bbSrc.cleanup with
      | true => rw [hC] at hEv; cases hEv
      | false =>
        rw [hC] at hEv; dsimp at hEv
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
              dsimp at hEv; injection hEv with hEqO; subst hEqO
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
                  unfold evalTerminator; rw [← hTermEq, hTS]; dsimp
                  rw [← hClean, hC]; dsimp; rw [h02]
  | switchInt d1 ts1 =>
    constructor
    · intro s' hEv
      unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
      cases hP : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
      | error _ => rw [hP] at hEv; cases hEv
      | ok res =>
        let ⟨dv, locs1⟩ := res
        rw [hP] at hEv; dsimp at hEv
        let ⟨locs2, hPT, hInv'⟩ := evalPrimitiveOperand_fwd_eq hInv hP
        cases dv with
        | scalar sv =>
          dsimp at hEv
          cases hTR : evalSwitchBranches sv.width sv.bits ts1.otherwise ts1.branches with
          | error _ => rw [hTR] at hEv; cases hEv
          | ok tgt =>
            rw [hTR] at hEv; dsimp [jumpToBlock] at hEv
            injection hEv with hEqS; subst hEqS
            refine ⟨tgt, locs1, locs2, rfl, ?_, hInv'⟩
            unfold evalTerminator; rw [← hTermEq, hTS]; dsimp
            rw [← hLocsEq, hPT]; dsimp; rw [hTR]; rfl
        | bool b =>
          dsimp at hEv
          cases hTR : evalBoolSwitchBranches b ts1.otherwise ts1.branches with
          | error _ => rw [hTR] at hEv; cases hEv
          | ok tgt =>
            rw [hTR] at hEv; dsimp [jumpToBlock] at hEv
            injection hEv with hEqS; subst hEqS
            refine ⟨tgt, locs1, locs2, rfl, ?_, hInv'⟩
            unfold evalTerminator; rw [← hTermEq, hTS]; dsimp
            rw [← hLocsEq, hPT]; dsimp; rw [hTR]; rfl
        | ptr _ => cases hEv
        | unit => cases hEv
        | enumVal _ _ => cases hEv
        | tuple _ => cases hEv
        | bytes _ => cases hEv
    · intro out hEv
      unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
      cases hP : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
      | error _ => rw [hP] at hEv; cases hEv
      | ok res =>
        let ⟨dv, _⟩ := res
        rw [hP] at hEv; dsimp at hEv
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
  | unreachable =>
    constructor <;> (intro _ hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)
  | unwindResume =>
    constructor <;> (intro _ hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)
  | assert _ _ _ _ _ =>
    constructor <;> (intro _ hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)
  | call _ _ _ _ _ =>
    constructor <;> (intro _ hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)
  | unsupported =>
    constructor <;> (intro _ hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)

private theorem uniformBranch_fwd_step {pSrc pTgt : Program} {s t : State}
    (hRel : StateUniformFwdRel pSrc pTgt s t) :
    (∀ s', evalStep pSrc 0 s = .step s' →
      ∃ t', evalStep pTgt 0 t = .step t' ∧
        StateUniformFwdRel pSrc pTgt s' t') ∧
    (∀ out, evalStep pSrc 0 s = .done out →
      evalStep pTgt 0 t = .done out) := by
  let ⟨hCm, fSrc, fTgt, bSrc, bTgt, hFS, hFT, hDef, hBlk, hStmt,
       hBS, hBT, hBody, hInv⟩ := hRel
  have hBodyCopy := hBody
  unfold isUniformBranchCollapseBody at hBodyCopy
  let ⟨hBHdr, hBlocks⟩ := bool_and_true hBodyCopy
  let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
  cases hBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
  | none =>
    constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; cases hEv)
  | some bbSrc =>
    let ⟨bbTgt, hBBT0, hBBRel⟩ := listRel_getElem?_left hBlocks hBBS
    have hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
      rw [← hBlk]; exact hBBT0
    unfold isUniformBranchCollapseBlock at hBBRel
    let ⟨h12, hTermRel⟩ := bool_and_true hBBRel
    let ⟨hCleanB, hStmtsRel⟩ := bool_and_true h12
    have hClean : bbSrc.cleanup = bbTgt.cleanup := bool_beq_eq hCleanB
    have hStmtsEq : bbSrc.statements = bbTgt.statements :=
      listRel_eq (fun _ _ => stmtEq_eq) hStmtsRel
    cases hSS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
    | some st =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some st := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      constructor
      · intro s' hEv
        unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
        rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS] at hEv
        let ⟨locs1', locs2', hEqS, hEv2, hInv'⟩ := evalStatement_fwd_eq hLocEq hInv hEv
        subst hEqS
        refine ⟨{ frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' }],
                  callerMem := t.callerMem }, ?_,
          hCm, _, _, bSrc, bTgt, rfl, rfl, hDef, hBlk, by dsimp; rw [hStmt],
          hBS, hBT, hBody, hInv'⟩
        unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
        rw [hBBT]; dsimp; rw [hST]; dsimp; rw [← hCm]; exact hEv2
      · intro out hEv
        unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
        rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS] at hEv
        exact False.elim (evalStatement_never_done bSrc fSrc s.callerMem st out hEv)
    | none =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      cases hAtEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
      | false =>
        constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS, if_bool_false hAtEnd] at hEv; cases hEv)
      | true =>
        have hAtEndT : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
          rw [← hStmtsEq, ← hStmt]; exact hAtEnd
        cases isUniformBranchCollapseTerm_elim hTermRel with
        | inl hTermEq =>
          have hT := evalTerminator_eq_fwd (cm := s.callerMem) hLocEq hClean hTermEq hInv
          constructor
          · intro s' hEv
            unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
            rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
            rw [hSS, if_bool_true hAtEnd] at hEv
            let ⟨tgt, locs1', locs2', hEqS, hEv2, hInv'⟩ := hT.1 s' hEv
            subst hEqS
            refine ⟨{ frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' }],
                      callerMem := t.callerMem }, ?_,
              hCm, _, _, bSrc, bTgt, rfl, rfl, hDef, rfl, rfl, hBS, hBT, hBody, hInv'⟩
            unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
            rw [hBBT]; dsimp; rw [hST, if_bool_true hAtEndT, ← hCm]; exact hEv2
          · intro out hEv
            unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
            rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
            rw [hSS, if_bool_true hAtEnd] at hEv
            unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
            rw [hBBT]; dsimp; rw [hST, if_bool_true hAtEndT, ← hCm]
            exact hT.2 out hEv
        | inr hCol =>
          let ⟨discr, targets, target, hTS, hTT, hAllEq⟩ := hCol
          unfold allSwitchTargetsEq at hAllEq
          let ⟨hOwEq, hBsEq⟩ := bool_and_true hAllEq
          constructor
          · intro s' hEv
            unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
            rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
            rw [hSS, if_bool_true hAtEnd] at hEv
            unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
            cases hPrim : evalPrimitiveOperand bSrc.locals fSrc.locals discr with
            | error _ => rw [hPrim] at hEv; cases hEv
            | ok res =>
              let ⟨dv, locsAfter⟩ := res
              rw [hPrim] at hEv; dsimp at hEv
              have hInv' := evalPrimitiveOperand_collapsed_fwd hInv hPrim
              cases dv with
              | scalar sv =>
                dsimp at hEv
                cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                | error _ => rw [hSw] at hEv; cases hEv
                | ok tgt =>
                  rw [hSw] at hEv; dsimp [jumpToBlock] at hEv
                  injection hEv with hEqS; subst hEqS
                  have hTgtEq : tgt = target :=
                    nat_beq_eq (evalSwitchBranches_target_ok (P := fun b => Nat.beq b target) hOwEq hBsEq hSw)
                  subst hTgtEq
                  refine ⟨{ frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0 }],
                            callerMem := t.callerMem }, ?_,
                    hCm, _, _, bSrc, bTgt, rfl, rfl, hDef, rfl, rfl, hBS, hBT, hBody, hInv'⟩
                  unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
                  rw [hBBT]; dsimp; rw [hST, if_bool_true hAtEndT]
                  unfold evalTerminator; rw [hTT]; rfl
              | bool b =>
                dsimp at hEv
                cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
                | error _ => rw [hSw] at hEv; cases hEv
                | ok tgt =>
                  rw [hSw] at hEv; dsimp [jumpToBlock] at hEv
                  injection hEv with hEqS; subst hEqS
                  have hTgtEq : tgt = target :=
                    nat_beq_eq (evalBoolSwitchBranches_target_ok (P := fun b => Nat.beq b target) hOwEq hBsEq hSw)
                  subst hTgtEq
                  refine ⟨{ frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0 }],
                            callerMem := t.callerMem }, ?_,
                    hCm, _, _, bSrc, bTgt, rfl, rfl, hDef, rfl, rfl, hBS, hBT, hBody, hInv'⟩
                  unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
                  rw [hBBT]; dsimp; rw [hST, if_bool_true hAtEndT]
                  unfold evalTerminator; rw [hTT]; rfl
              | ptr _ => cases hEv
              | unit => cases hEv
              | enumVal _ _ => cases hEv
              | tuple _ => cases hEv
              | bytes _ => cases hEv
          · intro out hEv
            unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
            rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
            rw [hSS, if_bool_true hAtEnd] at hEv
            unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
            cases hPrim : evalPrimitiveOperand bSrc.locals fSrc.locals discr with
            | error _ => rw [hPrim] at hEv; cases hEv
            | ok res =>
              let ⟨dv, _⟩ := res
              rw [hPrim] at hEv; dsimp at hEv
              cases dv with
              | scalar sv =>
                dsimp at hEv
                cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;>
                  rw [hSw] at hEv <;> cases hEv
              | bool b =>
                dsimp at hEv
                cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches <;>
                  rw [hSw] at hEv <;> cases hEv
              | ptr _ => cases hEv
              | unit => cases hEv
              | enumVal _ _ => cases hEv
              | tuple _ => cases hEv
              | bytes _ => cases hEv

private theorem uniformBranch_fwd_query {pSrc pTgt : Program} (q : Query)
    (hRel : isUniformBranchCollapseProgram pSrc pTgt = true)
    (hWf : WellFormed pSrc q) :
    WellFormed pTgt q ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := uniformBranch_initState_eq q hRel
  apply fwd_sim_lift (R := StateUniformFwdRel pSrc pTgt)
  · intro s₀ hIS
    have hIT : initState pTgt q = .ok s₀ := by rw [← hInitEq]; exact hIS
    let ⟨_, _, bSrc, hBS, _, _, _, _, hArgs, hS0⟩ := initState_ok_elim hIS
    unfold isUniformBranchCollapseProgram at hRel
    let ⟨_, hBodies⟩ := bool_and_true hRel
    let ⟨bTgt, hBT0, hBody⟩ := listRel_getElem?_left hBodies hBS
    subst hS0
    refine ⟨_, hIT, rfl, _, _, bSrc, bTgt, rfl, rfl, rfl, rfl, rfl, hBS, hBT0, hBody, ?_⟩
    exact initLocalsLoop_fwd_of_ann_imp (bSrc := bSrc) (bTgt := bSrc) rfl rfl hArgs
      (fun _ _ _ h => h)
  · intro s t hR
    exact uniformBranch_fwd_step hR
  · exact hWf

private theorem codegen_uniformBranchCollapse_refines_unconditional_priv
    (pSrc pTgt : Program)
    (hRel : isUniformBranchCollapseProgram pSrc pTgt = true) :
    PrivForwardCodegenRefines pSrc pTgt := by
  have hRelCopy := hRel
  unfold isUniformBranchCollapseProgram at hRelCopy
  let ⟨hHdr, hBodies⟩ := bool_and_true hRelCopy
  refine forwardCodegenRefines_of_query_fwd hHdr ?_
    (fun q hWf => uniformBranch_fwd_query q hRel hWf)
    (fun defId args hWf =>
      (uniformBranch_fwd_query { args := args } (uniformBranch_entryProg defId hRel) hWf).1)
  intro defId bSrc bTgt hBS hBT
  let ⟨bTgt', hBT', hBody⟩ := listRel_getElem?_left hBodies hBS
  rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
  let ⟨hBHdr, hBLen, hSt, _⟩ := uniformBranchBody_storage_eq hBody
  exact ⟨hBHdr, list_isEmpty_eq_of_length hBLen, fun hS => by rw [← hSt]; exact hS⟩

/-! #### Theorem 3b: Certified VC Transport (`UniformBranchCollapse`) -/

private noncomputable def SlotCertBisim (ty : MirTy) :
    AbsSlot → LocalSlot → LocalSlot → Prop
  | .liveInit, s1, s2 =>
    ∃ v, s1 = .live (some v) ∧ s2 = .live (some v) ∧ checkVal v ty = true
  | .liveUninit, s1, s2 =>
    (∃ opt1, s1 = .live opt1) ∧ (∃ opt2, s2 = .live opt2) ∧
    SlotWellTyped ty s1 ∧ SlotWellTyped ty s2
  | .dead, s1, s2 =>
    (s1 = .dead ↔ s2 = .dead) ∧ SlotWellTyped ty s1 ∧ SlotWellTyped ty s2

private theorem slotCertBisim_mono {ty : MirTy}
    {a b : AbsSlot} {s1 s2 : LocalSlot}
    (hImp : absSlotImplies a b = true)
    (h : SlotCertBisim ty a s1 s2) :
    SlotCertBisim ty b s1 s2 := by
  cases a with
  | liveInit =>
    let ⟨v, h1, h2, hChk⟩ := h
    subst h1; subst h2
    cases b with
    | liveInit => exact ⟨v, rfl, rfl, hChk⟩
    | liveUninit => exact ⟨⟨some v, rfl⟩, ⟨some v, rfl⟩, hChk, hChk⟩
    | dead => exact ⟨⟨(fun hD => by cases hD), (fun hD => by cases hD)⟩, hChk, hChk⟩
  | liveUninit =>
    let ⟨⟨o1, h1⟩, ⟨o2, h2⟩, hW1, hW2⟩ := h
    subst h1; subst h2
    cases b with
    | liveInit => cases hImp
    | liveUninit => exact ⟨⟨o1, rfl⟩, ⟨o2, rfl⟩, hW1, hW2⟩
    | dead => exact ⟨⟨(fun hD => by cases hD), (fun hD => by cases hD)⟩, hW1, hW2⟩
  | dead =>
    cases b with
    | liveInit => cases hImp
    | liveUninit => cases hImp
    | dead => exact h

private noncomputable def LocalsCertBisim (bodyLocals : List MirTy)
    (env : List AbsSlot) (localsSrc localsTgt : List LocalSlot) : Prop :=
  env.length = bodyLocals.length ∧
  localsSrc.length = bodyLocals.length ∧
  localsTgt.length = bodyLocals.length ∧
  ∀ i ty a s1 s2,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? env i = some a →
    Trusted.MirSemantics.getElem? localsSrc i = some s1 →
    Trusted.MirSemantics.getElem? localsTgt i = some s2 →
    SlotCertBisim ty a s1 s2

private theorem localsCertBisim_mono {bodyLocals : List MirTy}
    {env1 env2 : List AbsSlot} {localsSrc localsTgt : List LocalSlot}
    (hImp : absEnvImplies env1 env2 = true)
    (h : LocalsCertBisim bodyLocals env1 localsSrc localsTgt) :
    LocalsCertBisim bodyLocals env2 localsSrc localsTgt := by
  let ⟨hELen, hLen1, hLen2, hAll⟩ := h
  refine ⟨by rw [← listRel_length hImp, hELen], hLen1, hLen2, ?_⟩
  intro i ty b s1 s2 hTy hB hS1 hS2
  let ⟨a, hA, hAB⟩ := listRel_getElem?_right hImp hB
  exact slotCertBisim_mono hAB (hAll i ty a s1 s2 hTy hA hS1 hS2)

private theorem localsCertBisim_set_all {bodyLocals : List MirTy}
    {env env' : List AbsSlot} {locs1 locs2 locs1' locs2' : List LocalSlot}
    {id : Nat} {ty : MirTy} {a' : AbsSlot} {s1' s2' : LocalSlot}
    (h : LocalsCertBisim bodyLocals env locs1 locs2)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSE : setElem? env id a' = some env')
    (hS1 : setElem? locs1 id s1' = some locs1')
    (hS2 : setElem? locs2 id s2' = some locs2')
    (hSlot : SlotCertBisim ty a' s1' s2') :
    LocalsCertBisim bodyLocals env' locs1' locs2' := by
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

private theorem localsCertBisim_set_env_left {bodyLocals : List MirTy}
    {env env' : List AbsSlot} {locs1 locs2 locs1' : List LocalSlot}
    {id : Nat} {ty : MirTy} {a' : AbsSlot} {s1' s2 : LocalSlot}
    (h : LocalsCertBisim bodyLocals env locs1 locs2)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hG2 : Trusted.MirSemantics.getElem? locs2 id = some s2)
    (hSE : setElem? env id a' = some env')
    (hS1 : setElem? locs1 id s1' = some locs1')
    (hSlot : SlotCertBisim ty a' s1' s2) :
    LocalsCertBisim bodyLocals env' locs1' locs2 := by
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

private theorem slotCertBisim_liveUninit_pair (ty : MirTy) :
    SlotCertBisim ty
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

private theorem evalOperandToSlot_cert_bisim_eq
    {bodyLocals : List MirTy} {env env' : List AbsSlot}
    {locs1 locs2 : List LocalSlot} {op : Operand}
    (hInv : LocalsCertBisim bodyLocals env locs1 locs2)
    (hStep : stepAbsOperand bodyLocals env op = some env') :
    (∃ k,
      evalOperandToSlot bodyLocals locs1 op = .error k ∧
      evalOperandToSlot bodyLocals locs2 op = .error k) ∨
    (∃ ty v locs1' locs2',
      evalOperandToSlot bodyLocals locs1 op = .ok (ty, some v, locs1') ∧
      evalOperandToSlot bodyLocals locs2 op = .ok (ty, some v, locs2') ∧
      LocalsCertBisim bodyLocals env' locs1' locs2') := by
  let ⟨_, hLen1, hLen2, hAll⟩ := hInv
  cases op with
  | constant c =>
    injection hStep with hEqE; subst hEqE
    cases hC : evalConstLit c.ty c.lit with
    | error k =>
      left; refine ⟨k, ?_, ?_⟩ <;> (dsimp [evalOperandToSlot]; rw [hC])
    | ok v =>
      right; refine ⟨c.ty, v, locs1, locs2, ?_, ?_, hInv⟩ <;>
        (dsimp [evalOperandToSlot]; rw [hC])
  | copy p =>
    dsimp [stepAbsOperand] at hStep
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hStep; cases hStep
    | true =>
      rw [hP] at hStep; dsimp at hStep
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep
        cases hA : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hA] at hStep; cases hStep
        | some a =>
          rw [hA] at hStep
          cases a with
          | liveUninit => cases hStep
          | dead => cases hStep
          | liveInit =>
            dsimp at hStep; injection hStep with hEqE; subst hEqE
            let ⟨s1, hS1⟩ := getElem?_some_of_lt locs1 p.localId
              (by rw [hLen1]; exact getElem?_some_lt hTy)
            let ⟨s2, hS2⟩ := getElem?_some_of_lt locs2 p.localId
              (by rw [hLen2]; exact getElem?_some_lt hTy)
            let ⟨v, h1, h2, _⟩ := hAll p.localId ty .liveInit s1 s2 hTy hA hS1 hS2
            subst h1; subst h2
            right
            refine ⟨ty, v, locs1, locs2, ?_, ?_, hInv⟩
            · dsimp [evalOperandToSlot]; rw [hP, hTy, hS1]; rfl
            · dsimp [evalOperandToSlot]; rw [hP, hTy, hS2]; rfl
  | move p =>
    dsimp [stepAbsOperand] at hStep
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hStep; cases hStep
    | true =>
      rw [hP] at hStep; dsimp at hStep
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep
        cases hA : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hA] at hStep; cases hStep
        | some a =>
          rw [hA] at hStep
          cases a with
          | liveUninit => cases hStep
          | dead => cases hStep
          | liveInit =>
            dsimp at hStep
            let ⟨s1, hS1⟩ := getElem?_some_of_lt locs1 p.localId
              (by rw [hLen1]; exact getElem?_some_lt hTy)
            let ⟨s2, hS2⟩ := getElem?_some_of_lt locs2 p.localId
              (by rw [hLen2]; exact getElem?_some_lt hTy)
            let ⟨v, h1, h2, _⟩ := hAll p.localId ty .liveInit s1 s2 hTy hA hS1 hS2
            subst h1; subst h2
            let ⟨locs1', hSet1⟩ := setElem?_some_of_lt locs1 p.localId
              (liveUninitSlot ty) (by rw [hLen1]; exact getElem?_some_lt hTy)
            let ⟨locs2', hSet2⟩ := setElem?_some_of_lt locs2 p.localId
              (liveUninitSlot ty) (by rw [hLen2]; exact getElem?_some_lt hTy)
            right
            refine ⟨ty, v, locs1', locs2', ?_, ?_,
              localsCertBisim_set_all hInv hTy hStep hSet1 hSet2
                (slotCertBisim_liveUninit_pair ty)⟩
            · dsimp [evalOperandToSlot]; rw [hP, hTy, hS1]; dsimp; rw [hSet1]
            · dsimp [evalOperandToSlot]; rw [hP, hTy, hS2]; dsimp; rw [hSet2]

private theorem evalPrimitiveOperand_cert_bisim_eq
    {bodyLocals : List MirTy} {env env' : List AbsSlot}
    {locs1 locs2 : List LocalSlot} {op : Operand}
    (hInv : LocalsCertBisim bodyLocals env locs1 locs2)
    (hStep : stepAbsOperand bodyLocals env op = some env') :
    (∃ k,
      evalPrimitiveOperand bodyLocals locs1 op = .error k ∧
      evalPrimitiveOperand bodyLocals locs2 op = .error k) ∨
    (∃ v locs1' locs2',
      evalPrimitiveOperand bodyLocals locs1 op = .ok (v, locs1') ∧
      evalPrimitiveOperand bodyLocals locs2 op = .ok (v, locs2') ∧
      LocalsCertBisim bodyLocals env' locs1' locs2') := by
  cases evalOperandToSlot_cert_bisim_eq hInv hStep with
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

private theorem evalRvalue_cert_bisim_eq
    {bodyLocals : List MirTy} {env env' : List AbsSlot}
    {locs1 locs2 : List LocalSlot} {dstTy : MirTy} {rv : Rvalue}
    (hInv : LocalsCertBisim bodyLocals env locs1 locs2)
    (hStep : stepAbsRvalue bodyLocals env rv = some env') :
    (∃ k,
      evalRvalue bodyLocals locs1 dstTy rv = .error k ∧
      evalRvalue bodyLocals locs2 dstTy rv = .error k) ∨
    (∃ v locs1' locs2',
      evalRvalue bodyLocals locs1 dstTy rv = .ok (v, locs1') ∧
      evalRvalue bodyLocals locs2 dstTy rv = .ok (v, locs2') ∧
      LocalsCertBisim bodyLocals env' locs1' locs2') := by
  cases rv with
  | use o =>
    cases evalOperandToSlot_cert_bisim_eq hInv hStep with
    | inl hErr =>
      let ⟨k, h1, h2⟩ := hErr
      left; refine ⟨k, ?_, ?_⟩
      · dsimp [evalRvalue]; rw [h1]
      · dsimp [evalRvalue]; rw [h2]
    | inr hOk =>
      let ⟨srcTy, v, l1, l2, h1, h2, hInv'⟩ := hOk
      cases hEqTy : MirTy.beq srcTy dstTy with
      | false =>
        left; refine ⟨.unsupported, ?_, ?_⟩
        · dsimp [evalRvalue]; rw [h1]; dsimp; rw [hEqTy]; rfl
        · dsimp [evalRvalue]; rw [h2]; dsimp; rw [hEqTy]; rfl
      | true =>
        right; refine ⟨v, l1, l2, ?_, ?_, hInv'⟩
        · dsimp [evalRvalue]; rw [h1]; dsimp; rw [hEqTy]; rfl
        · dsimp [evalRvalue]; rw [h2]; dsimp; rw [hEqTy]; rfl
  | binaryOp op l r =>
    dsimp [stepAbsRvalue] at hStep
    cases hSL : stepAbsOperand bodyLocals env l with
    | none => rw [hSL] at hStep; cases hStep
    | some env1 =>
      rw [hSL] at hStep; dsimp at hStep
      cases evalPrimitiveOperand_cert_bisim_eq hInv hSL with
      | inl hErr =>
        let ⟨k, h1, h2⟩ := hErr
        left; refine ⟨k, ?_, ?_⟩
        · dsimp [evalRvalue]; rw [h1]
        · dsimp [evalRvalue]; rw [h2]
      | inr hOkL =>
        let ⟨lv, locsL1, locsL2, hL1, hL2, hInv1⟩ := hOkL
        cases evalPrimitiveOperand_cert_bisim_eq hInv1 hStep with
        | inl hErr =>
          let ⟨k, h1, h2⟩ := hErr
          left; refine ⟨k, ?_, ?_⟩
          · dsimp [evalRvalue]; rw [hL1]; dsimp; rw [h1]
          · dsimp [evalRvalue]; rw [hL2]; dsimp; rw [h2]
        | inr hOkR =>
          let ⟨rvVal, locsR1, locsR2, hR1, hR2, hInv2⟩ := hOkR
          cases hBin : evalBinOp op lv rvVal with
          | error k =>
            left; refine ⟨k, ?_, ?_⟩
            · dsimp [evalRvalue]; rw [hL1]; dsimp; rw [hR1]; dsimp; rw [hBin]
            · dsimp [evalRvalue]; rw [hL2]; dsimp; rw [hR2]; dsimp; rw [hBin]
          | ok resV =>
            right; refine ⟨resV, locsR1, locsR2, ?_, ?_, hInv2⟩
            · dsimp [evalRvalue]; rw [hL1]; dsimp; rw [hR1]; dsimp; rw [hBin]
            · dsimp [evalRvalue]; rw [hL2]; dsimp; rw [hR2]; dsimp; rw [hBin]
  | unaryOp op o =>
    cases evalPrimitiveOperand_cert_bisim_eq hInv hStep with
    | inl hErr =>
      let ⟨k, h1, h2⟩ := hErr
      left; refine ⟨k, ?_, ?_⟩
      · dsimp [evalRvalue]; rw [h1]
      · dsimp [evalRvalue]; rw [h2]
    | inr hOk =>
      let ⟨ov, l1, l2, h1, h2, hInv1⟩ := hOk
      cases hUn : evalUnOp op ov with
      | error k =>
        left; refine ⟨k, ?_, ?_⟩
        · dsimp [evalRvalue]; rw [h1]; dsimp; rw [hUn]
        · dsimp [evalRvalue]; rw [h2]; dsimp; rw [hUn]
      | ok resV =>
        right; refine ⟨resV, l1, l2, ?_, ?_, hInv1⟩
        · dsimp [evalRvalue]; rw [h1]; dsimp; rw [hUn]
        · dsimp [evalRvalue]; rw [h2]; dsimp; rw [hUn]
  | discriminant p =>
    let ⟨_, hLen1, hLen2, hAll⟩ := hInv
    dsimp [stepAbsRvalue] at hStep
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hStep; cases hStep
    | true =>
      rw [hP] at hStep; dsimp at hStep
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep
        cases ty with
        | enum ety =>
          cases hA : Trusted.MirSemantics.getElem? env p.localId with
          | none => rw [hA] at hStep; cases hStep
          | some a =>
            rw [hA] at hStep
            let ⟨s1, hS1⟩ := getElem?_some_of_lt locs1 p.localId
              (by rw [hLen1]; exact getElem?_some_lt hTy)
            let ⟨s2, hS2⟩ := getElem?_some_of_lt locs2 p.localId
              (by rw [hLen2]; exact getElem?_some_lt hTy)
            have hSlot := hAll p.localId (.enum ety) a s1 s2 hTy hA hS1 hS2
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
              left; refine ⟨.unsupported, ?_, ?_⟩
              · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; rfl
              · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; rfl
            | true =>
              cases hTr : ety.tagRepr with
              | zeroSized =>
                cases s1 with
                | dead =>
                  left; refine ⟨.undefined, ?_, ?_⟩
                  · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; rfl
                  · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; rfl
                | live opt =>
                  cases opt with
                  | none =>
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none =>
                      left; refine ⟨.unsupported, ?_, ?_⟩
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
                        left; refine ⟨.unsupported, ?_, ?_⟩
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; rfl
                        · dsimp [evalRvalue]; rw [hP]; dsimp; rw [hTy, hS2]; dsimp; rw [hAdm]; dsimp; rw [hTr]; dsimp; rw [hC]; rfl
                      | true =>
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
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
  | ref _ _ => cases hStep
  | addressOf _ _ => cases hStep
  | aggregateTuple _ => cases hStep
  | unsupported => cases hStep

private theorem evalStatement_cert_bisim_eq
    {bSrc bTgt : Body} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {env env' : List AbsSlot} {stmt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hStep : stepAbsStmt bSrc.locals env stmt = some env')
    (hInv : LocalsCertBisim bSrc.locals env fSrc.locals fTgt.locals) :
    (∃ k,
      evalStatement bSrc fSrc cm stmt = .fault k ∧
      evalStatement bTgt fTgt cm stmt = .fault k) ∨
    (∃ l1' l2',
      evalStatement bSrc fSrc cm stmt =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm stmt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                callerMem := cm } ∧
      LocalsCertBisim bSrc.locals env' l1' l2') := by
  let ⟨hELen, hLen1, hLen2, _⟩ := hInv
  cases stmt with
  | nop =>
    injection hStep with hEqE; subst hEqE
    right; exact ⟨fSrc.locals, fTgt.locals, rfl, rfl, hInv⟩
  | unsupported => cases hStep
  | storageLive i1 =>
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
  | storageDead i1 =>
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
  | assign d1 rv1 =>
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
          cases evalRvalue_cert_bisim_eq (dstTy := dstTy) hInv hSR with
          | inl hErr =>
            let ⟨k, h1, h2⟩ := hErr
            left; refine ⟨k, ?_, ?_⟩
            · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [h1]
            · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [h2]
          | inr hOk =>
            let ⟨val, l1, l2, hR1, hR2, hInv1⟩ := hOk
            let ⟨hE1Len, hL1, hL2, hAll1⟩ := hInv1
            let ⟨a1, hA1⟩ := getElem?_some_of_lt env1 d1.localId
              (by rw [hE1Len]; exact getElem?_some_lt hTy)
            cases hChk : checkVal val dstTy with
            | false =>
              left; refine ⟨.unsupported, ?_, ?_⟩
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
                  rw [h1, h2]
                  exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
                | dead => exact hSlot.1
              cases s1 with
              | dead =>
                have hs2 : s2 = .dead := hDeadIff.mp rfl
                subst hs2
                left; refine ⟨.undefined, ?_, ?_⟩
                · dsimp [evalStatement]; rw [hP]; dsimp; rw [hTy]; dsimp; rw [hR1]; dsimp
                  dsimp [writePlace]; rw [hChk]; dsimp; rw [hG1]
                · dsimp [evalStatement]; rw [hP]; dsimp; rw [← hLocEq, hTy]; dsimp; rw [hR2]; dsimp
                  dsimp [writePlace]; rw [hChk]; dsimp; rw [hG2]
              | live _ =>
                cases s2 with
                | dead => exact False.elim (by cases hDeadIff.mpr rfl)
                | live _ =>
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

private theorem checkVal_int_elim {v : Val} {w : IntWidth} {s : Bool}
    (h : checkVal v (.int w s) = true) :
    ∃ sv : ScalarVal, v = .scalar sv ∧ sv.width = w ∧ sv.signed = s := by
  unfold checkVal at h
  cases v with
  | scalar sv =>
    dsimp [Val.ty?] at h
    cases hWf : sv.wf with
    | false => rw [hWf] at h; cases h
    | true =>
      rw [hWf] at h; dsimp [MirTy.beq] at h
      let ⟨hW, hS⟩ := bool_and_true h
      exact ⟨sv, rfl, intWidth_beq_eq hW, bool_beq_eq hS⟩
  | bool _ => cases h
  | unit => cases h
  | ptr _ => cases h
  | enumVal ety k =>
    dsimp [Val.ty?] at h
    cases hC : (enumAdmitted ety && Nat.blt k ety.discriminants.length) <;>
      rw [hC] at h <;> cases h
  | tuple _ => cases h
  | bytes _ => cases h

private theorem checkVal_bool_elim {v : Val}
    (h : checkVal v .bool = true) :
    ∃ b : Bool, v = .bool b := by
  unfold checkVal at h
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | unit => cases h
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

private theorem evalSwitchBranches_ok_of_valid {w : IntWidth} {discrBits : BitVec 128}
    {ow target : BasicBlockId} {bs : List (BitVec 128 × BasicBlockId)}
    (hValid : bs.all (fun br => truncateBits w br.1 == br.1) = true)
    (hOw : Nat.beq ow target = true)
    (hBs : bs.all (fun br => Nat.beq br.2 target) = true) :
    evalSwitchBranches w discrBits ow bs = .ok target := by
  induction bs with
  | nil =>
    dsimp [evalSwitchBranches]
    rw [nat_beq_eq hOw]
  | cons br rest ih =>
    let ⟨cb, tb⟩ := br
    dsimp [List.all] at hValid hBs
    let ⟨hVHead, hVTail⟩ := bool_and_true hValid
    let ⟨hTHead, hTTail⟩ := bool_and_true hBs
    dsimp [evalSwitchBranches]
    rw [bitvec_bne_false_of_beq hVHead, if_bool_false rfl]
    cases (truncateBits w discrBits == truncateBits w cb) with
    | true => rw [nat_beq_eq hTHead]; rfl
    | false =>
      rw [if_bool_false rfl]
      exact ih hVTail hTTail

private theorem evalBoolSwitchBranches_ok_of_valid {discr : Bool}
    {ow target : BasicBlockId} {bs : List (BitVec 128 × BasicBlockId)}
    (hValid : bs.all (fun br =>
      match evalConstLit .bool (.scalar br.1) with
      | .ok (.bool _) => true
      | _ => false) = true)
    (hOw : Nat.beq ow target = true)
    (hBs : bs.all (fun br => Nat.beq br.2 target) = true) :
    evalBoolSwitchBranches discr ow bs = .ok target := by
  induction bs with
  | nil =>
    dsimp [evalBoolSwitchBranches]
    rw [nat_beq_eq hOw]
  | cons br rest ih =>
    let ⟨cb, tb⟩ := br
    dsimp [List.all] at hValid hBs
    let ⟨hVHead, hVTail⟩ := bool_and_true hValid
    let ⟨hTHead, hTTail⟩ := bool_and_true hBs
    dsimp [evalBoolSwitchBranches]
    cases hC : evalConstLit .bool (.scalar cb) with
    | error _ => rw [hC] at hVHead; cases hVHead
    | ok cv =>
      rw [hC] at hVHead
      cases cv with
      | bool b =>
        cases b with
        | false =>
          dsimp
          cases discr with
          | false => rw [nat_beq_eq hTHead]; rfl
          | true => exact ih hVTail hTTail
        | true =>
          dsimp
          cases discr with
          | true => rw [nat_beq_eq hTHead]; rfl
          | false => exact ih hVTail hTTail
      | scalar _ => cases hVHead
      | ptr _ => cases hVHead
      | unit => cases hVHead
      | enumVal _ _ => cases hVHead
      | tuple _ => cases hVHead
      | bytes _ => cases hVHead

private theorem validSwitchBranchesForTy_eval_ok {ty : MirTy} {dv : Val}
    {targets : SwitchTargets} {target : BasicBlockId}
    (hPrim : isPrimitiveReadableTy ty = true)
    (hChk : checkVal dv ty = true)
    (hValid : validSwitchBranchesForTy ty targets.branches = true)
    (hAllEq : allSwitchTargetsEq targets target = true) :
    (match dv with
     | .scalar sv => evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches
     | .bool b => evalBoolSwitchBranches b targets.otherwise targets.branches
     | _ => .error .unsupported) = .ok target := by
  unfold allSwitchTargetsEq at hAllEq
  let ⟨hOw, hBs⟩ := bool_and_true hAllEq
  cases ty with
  | int w s =>
    let ⟨sv, hDv, hW, _⟩ := checkVal_int_elim hChk
    subst hDv; subst hW
    exact evalSwitchBranches_ok_of_valid hValid hOw hBs
  | bool =>
    let ⟨b, hDv⟩ := checkVal_bool_elim hChk
    subst hDv
    exact evalBoolSwitchBranches_ok_of_valid hValid hOw hBs
  | unit => cases hPrim
  | never => cases hPrim
  | enum _ => cases hPrim
  | tuple _ => cases hPrim
  | ref _ _ => cases hPrim
  | rawPtr _ _ => cases hPrim
  | unsupported => cases hPrim

private theorem resolveConstSwitchTarget_eq_of_allEq
    {c : ConstOperand} {targets : SwitchTargets} {resolved target : BasicBlockId}
    (hRes : resolveConstSwitchTarget c targets = some resolved)
    (hAllEq : allSwitchTargetsEq targets target = true) :
    resolved = target := by
  unfold allSwitchTargetsEq at hAllEq
  let ⟨hOw, hBs⟩ := bool_and_true hAllEq
  unfold resolveConstSwitchTarget at hRes
  cases hPrim : (!isPrimitiveReadableTy c.ty) with
  | true => rw [if_bool_true hPrim] at hRes; cases hRes
  | false =>
    rw [if_bool_false hPrim] at hRes
    cases hLit : evalConstLit c.ty c.lit with
    | error _ => rw [hLit] at hRes; cases hRes
    | ok dv =>
      rw [hLit] at hRes
      cases dv with
      | scalar sv =>
        dsimp at hRes
        cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error _ => rw [hSw] at hRes; cases hRes
        | ok tgt =>
          rw [hSw] at hRes; injection hRes with hEq; subst hEq
          exact nat_beq_eq (evalSwitchBranches_target_ok (P := fun b => Nat.beq b target) hOw hBs hSw)
      | bool b =>
        dsimp at hRes
        cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error _ => rw [hSw] at hRes; cases hRes
        | ok tgt =>
          rw [hSw] at hRes; injection hRes with hEq; subst hEq
          exact nat_beq_eq (evalBoolSwitchBranches_target_ok (P := fun b => Nat.beq b target) hOw hBs hSw)
      | ptr _ => cases hRes
      | unit => cases hRes
      | enumVal _ _ => cases hRes
      | tuple _ => cases hRes
      | bytes _ => cases hRes

private theorem stepCollapsedSwitchOperand_sound
    {bSrc : Body} {bbSrc : BasicBlock} {fSrc fTgt : FrameState} {cm : CallerMemory}
    {exitEnv afterEnv : List AbsSlot}
    {discr : Operand} {targets : SwitchTargets} {target : BasicBlockId}
    (hInv : LocalsCertBisim bSrc.locals exitEnv fSrc.locals fTgt.locals)
    (hTS : bbSrc.terminator = .switchInt discr targets)
    (hAllEq : allSwitchTargetsEq targets target = true)
    (hStep : stepCollapsedSwitchOperand bSrc.locals exitEnv discr targets = some afterEnv) :
    ∃ l1',
      evalTerminator bSrc bbSrc fSrc cm =
        .step { frames := [{ fSrc with blockIdx := target, stmtIdx := 0, locals := l1' }],
                callerMem := cm } ∧
      LocalsCertBisim bSrc.locals afterEnv l1' fTgt.locals := by
  let ⟨_, hLen1, hLen2, hAll⟩ := hInv
  cases discr with
  | constant c =>
    dsimp [stepCollapsedSwitchOperand] at hStep
    cases hRes : resolveConstSwitchTarget c targets with
    | none => rw [hRes] at hStep; cases hStep
    | some resolved =>
      rw [hRes] at hStep; injection hStep with hEqE; subst hEqE
      have hRT := resolveConstSwitchTarget_eq_of_allEq hRes hAllEq
      subst hRT
      refine ⟨fSrc.locals, ?_, hInv⟩
      rw [resolveConstSwitchTarget_evalTerminator hTS hRes]
      rfl
  | copy p =>
    dsimp [stepCollapsedSwitchOperand] at hStep
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hStep; cases hStep
    | true =>
      rw [hP] at hStep; dsimp at hStep
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals p.localId with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep
        cases hA : Trusted.MirSemantics.getElem? exitEnv p.localId with
        | none => rw [hA] at hStep; cases hStep
        | some a =>
          rw [hA] at hStep
          cases a with
          | liveUninit => cases hStep
          | dead => cases hStep
          | liveInit =>
            dsimp at hStep
            cases hPV : (isPrimitiveReadableTy ty && validSwitchBranchesForTy ty targets.branches) with
            | false => rw [if_bool_false hPV] at hStep; cases hStep
            | true =>
              rw [if_bool_true hPV] at hStep; injection hStep with hEqE; subst hEqE
              let ⟨hPrim, hValBr⟩ := bool_and_true hPV
              let ⟨s1, hS1⟩ := getElem?_some_of_lt fSrc.locals p.localId
                (by rw [hLen1]; exact getElem?_some_lt hTy)
              let ⟨s2, hS2⟩ := getElem?_some_of_lt fTgt.locals p.localId
                (by rw [hLen2]; exact getElem?_some_lt hTy)
              let ⟨dv, h1, _, hChk⟩ := hAll p.localId ty .liveInit s1 s2 hTy hA hS1 hS2
              subst h1
              have hSwOk := validSwitchBranchesForTy_eval_ok hPrim hChk hValBr hAllEq
              refine ⟨fSrc.locals, ?_, hInv⟩
              unfold evalTerminator; rw [hTS]; dsimp [evalPrimitiveOperand, evalOperandToSlot]
              rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hPrim]; dsimp
              cases dv <;> first | (dsimp at hSwOk; dsimp; rw [hSwOk]; rfl) | cases hSwOk
  | move p =>
    dsimp [stepCollapsedSwitchOperand] at hStep
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hStep; cases hStep
    | true =>
      rw [hP] at hStep; dsimp at hStep
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals p.localId with
      | none => rw [hTy] at hStep; cases hStep
      | some ty =>
        rw [hTy] at hStep
        cases hA : Trusted.MirSemantics.getElem? exitEnv p.localId with
        | none => rw [hA] at hStep; cases hStep
        | some a =>
          rw [hA] at hStep
          cases a with
          | liveUninit => cases hStep
          | dead => cases hStep
          | liveInit =>
            dsimp at hStep
            cases hPV : (isPrimitiveReadableTy ty && validSwitchBranchesForTy ty targets.branches) with
            | false => rw [if_bool_false hPV] at hStep; cases hStep
            | true =>
              rw [if_bool_true hPV] at hStep
              let ⟨hPrim, hValBr⟩ := bool_and_true hPV
              let ⟨s1, hS1⟩ := getElem?_some_of_lt fSrc.locals p.localId
                (by rw [hLen1]; exact getElem?_some_lt hTy)
              let ⟨s2, hS2⟩ := getElem?_some_of_lt fTgt.locals p.localId
                (by rw [hLen2]; exact getElem?_some_lt hTy)
              let ⟨dv, h1, h2, hChk⟩ := hAll p.localId ty .liveInit s1 s2 hTy hA hS1 hS2
              subst h1; subst h2
              let ⟨l1', hSet1⟩ := setElem?_some_of_lt fSrc.locals p.localId
                (liveUninitSlot ty) (by rw [hLen1]; exact getElem?_some_lt hTy)
              have hNotZst := not_zst_of_primitiveReadable hPrim
              have hSlotNew : SlotCertBisim ty .liveUninit (liveUninitSlot ty) (.live (some dv)) := by
                rw [liveUninitSlot_of_not_zst hNotZst]
                exact ⟨⟨none, rfl⟩, ⟨some dv, rfl⟩, hNotZst, hChk⟩
              have hSwOk := validSwitchBranchesForTy_eval_ok hPrim hChk hValBr hAllEq
              refine ⟨l1', ?_,
                localsCertBisim_set_env_left hInv hTy hS2 hStep hSet1 hSlotNew⟩
              unfold evalTerminator; rw [hTS]; dsimp [evalPrimitiveOperand, evalOperandToSlot]
              rw [hP]; dsimp; rw [hTy, hS1]; dsimp; rw [hSet1]; dsimp; rw [hPrim]; dsimp
              cases dv <;> first | (dsimp at hSwOk; dsimp; rw [hSwOk]; rfl) | cases hSwOk

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
  | cons _ rest ih =>
    cases i with
    | zero => injection hTy with hEq; subst hEq; rfl
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTy
      rw [hAdd] at hRec
      exact hRec

private theorem initLocals_cert_bisim_uniform {bSrc bTgt : Body} {args : List Val}
    (hRel : isUniformBranchCollapseBody bSrc bTgt = true)
    (hArgs : checkArgsMatch args ((bSrc.locals.drop 1).take bSrc.argumentCount) = true) :
    LocalsCertBisim bSrc.locals
      (initAbsEnvLoop bSrc 0 bSrc.locals)
      (initLocalsLoop bSrc args 0 bSrc.locals)
      (initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨hBHdr, _, _, hHasAnn⟩ := uniformBranchBody_storage_eq hRel
  let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  have hLoopEq := initLocalsLoop_eq_of_storage_eq args hArg hLoc (fun idx _ _ => hHasAnn idx)
  rw [← hLoopEq]
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
      have hKlt : k < bSrc.argumentCount := nat_ble_le hLe
      have hDrop : Trusted.MirSemantics.getElem?
          ((bSrc.locals.drop 1).take bSrc.argumentCount) k = some ty := by
        rw [getElem?_take_drop1 bSrc.locals bSrc.argumentCount k hKlt]
        exact hTy
      let ⟨v, hV, hChk⟩ := checkArgsMatch_getElem? hArgs hDrop
      rw [hV]
      exact ⟨v, rfl, rfl, hChk⟩
    | false =>
      cases hasStorageAnnotation bSrc (k + 1) with
      | true => exact ⟨⟨fun h => h, fun h => h⟩, True.intro, True.intro⟩
      | false => exact slotCertBisim_liveUninit_pair ty

private noncomputable def UniformBlockTermOk (bSrc : Body) (bCert : BodyAbsCert)
    (bbSrc bbTgt : BasicBlock) (exitEnv : List AbsSlot) : Prop :=
  let numBlocks := bSrc.basicBlocks.length
  match bbSrc.terminator, bbTgt.terminator with
  | .switchInt discr targets, .goto target =>
    ∃ afterDiscrEnv,
      stepCollapsedSwitchOperand bSrc.locals exitEnv discr targets = some afterDiscrEnv ∧
      checkEdgeTarget numBlocks bCert afterDiscrEnv target = true
  | .goto target, .goto _ => checkEdgeTarget numBlocks bCert exitEnv target = true
  | .return_, .return_ =>
    if bbSrc.cleanup then True
    else Trusted.MirSemantics.getElem? exitEnv 0 = some .liveInit
  | .switchInt discr targets, .switchInt _ _ =>
    ∃ afterDiscrEnv,
      stepAbsOperand bSrc.locals exitEnv discr = some afterDiscrEnv ∧
      checkEdgeTarget numBlocks bCert afterDiscrEnv targets.otherwise = true ∧
      targets.branches.all (fun br =>
        checkEdgeTarget numBlocks bCert afterDiscrEnv br.2) = true
  | .unreachable, .unreachable
  | .unwindResume, .unwindResume
  | .assert _ _ _ _ _, .assert _ _ _ _ _
  | .call _ _ _ _ _, .call _ _ _ _ _
  | .unsupported, .unsupported => True
  | _, _ => False

private theorem checkUniformBranchBlocksLoop_getElem? (bSrc bTgt : Body)
    (cert : BodyAbsCert) (base : Nat) (bbs : List BasicBlock)
    (i : Nat) (bb : BasicBlock)
    (hLoop : checkUniformBranchBlocksLoop bSrc bTgt cert base bbs = true)
    (hGet : Trusted.MirSemantics.getElem? bbs i = some bb) :
    checkUniformBranchBlock bSrc bTgt cert (base + i) bb = true := by
  induction bbs generalizing base i with
  | nil => cases hGet
  | cons _ rest ih =>
    dsimp [checkUniformBranchBlocksLoop] at hLoop
    let ⟨hHead, hTail⟩ := bool_and_true hLoop
    cases i with
    | zero => injection hGet with hEq; subst hEq; exact hHead
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTail hGet
      rw [hAdd] at hRec
      exact hRec

private theorem checkUniformBranchBlock_elim {bSrc bTgt : Body} {bCert : BodyAbsCert}
    {bbIdx : Nat} {bbSrc bbTgt : BasicBlock} {entryEnv : List AbsSlot}
    (hBlk : checkUniformBranchBlock bSrc bTgt bCert bbIdx bbSrc = true)
    (hEntry : Trusted.MirSemantics.getElem? bCert bbIdx = some (some entryEnv))
    (hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt) :
    entryEnv.length = bSrc.locals.length ∧
    ∃ exitEnv,
      stepAbsStmts bSrc.locals entryEnv bbSrc.statements = some exitEnv ∧
      UniformBlockTermOk bSrc bCert bbSrc bbTgt exitEnv := by
  unfold checkUniformBranchBlock at hBlk
  rw [hEntry, hBBT] at hBlk; dsimp at hBlk
  let ⟨hLen, hRest⟩ := bool_and_true hBlk
  refine ⟨nat_beq_eq hLen, ?_⟩
  cases hSt : stepAbsStmts bSrc.locals entryEnv bbSrc.statements with
  | none => rw [hSt] at hRest; cases hRest
  | some exitEnv =>
    rw [hSt] at hRest; dsimp at hRest
    refine ⟨exitEnv, rfl, ?_⟩
    unfold UniformBlockTermOk
    cases hTS : bbSrc.terminator with
    | goto target =>
      rw [hTS] at hRest
      cases hTT : bbTgt.terminator <;> rw [hTT] at hRest <;> first | exact hRest | cases hRest
    | return_ =>
      rw [hTS] at hRest
      cases hTT : bbTgt.terminator with
      | return_ =>
        rw [hTT] at hRest; dsimp at hRest
        cases hC : bbSrc.cleanup with
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
      | _ => rw [hTT] at hRest; cases hRest
    | switchInt discr targets =>
      rw [hTS] at hRest
      cases hTT : bbTgt.terminator with
      | goto target =>
        rw [hTT] at hRest; dsimp at hRest
        cases hOp : stepCollapsedSwitchOperand bSrc.locals exitEnv discr targets with
        | none => rw [hOp] at hRest; cases hRest
        | some afterEnv =>
          rw [hOp] at hRest; dsimp at hRest
          exact ⟨afterEnv, hOp, hRest⟩
      | switchInt d2 ts2 =>
        rw [hTT] at hRest; dsimp at hRest
        cases hOp : stepAbsOperand bSrc.locals exitEnv discr with
        | none => rw [hOp] at hRest; cases hRest
        | some afterEnv =>
          rw [hOp] at hRest; dsimp at hRest
          let ⟨hOw, hBs⟩ := bool_and_true hRest
          exact ⟨afterEnv, hOp, hOw, hBs⟩
      | _ => rw [hTT] at hRest; cases hRest
    | unreachable =>
      rw [hTS] at hRest
      cases hTT : bbTgt.terminator <;> rw [hTT] at hRest <;> first | exact True.intro | cases hRest
    | unwindResume =>
      rw [hTS] at hRest
      cases hTT : bbTgt.terminator <;> rw [hTT] at hRest <;> first | exact True.intro | cases hRest
    | assert _ _ _ _ _ =>
      rw [hTS] at hRest
      cases hTT : bbTgt.terminator <;> rw [hTT] at hRest <;> first | exact True.intro | cases hRest
    | call _ _ _ _ _ =>
      rw [hTS] at hRest
      cases hTT : bbTgt.terminator <;> rw [hTT] at hRest <;> first | exact True.intro | cases hRest
    | unsupported =>
      rw [hTS] at hRest
      cases hTT : bbTgt.terminator <;> rw [hTT] at hRest <;> first | exact True.intro | cases hRest

private noncomputable def StateUniformCertBisim
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
    isUniformBranchCollapseBody bSrc bTgt = true ∧
    checkUniformBranchBody bSrc bTgt bCert = true ∧
    (Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = none ∨
      ∃ bbSrc bbTgt curEnv exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt ∧
        fSrc.stmtIdx ≤ bbSrc.statements.length ∧
        stepAbsStmts bSrc.locals curEnv (bbSrc.statements.drop fSrc.stmtIdx) = some exitEnv ∧
        UniformBlockTermOk bSrc bCert bbSrc bbTgt exitEnv ∧
        LocalsCertBisim bSrc.locals curEnv fSrc.locals fTgt.locals)

private theorem jump_uniform_cert_bisim
    {bSrc bTgt : Body} {bCert : BodyAbsCert} {env : List AbsSlot}
    {l1 l2 : List LocalSlot} {tgt : BasicBlockId}
    (hBodyRel : isUniformBranchCollapseBody bSrc bTgt = true)
    (hBodyCert : checkUniformBranchBody bSrc bTgt bCert = true)
    (hEdge : checkEdgeTarget bSrc.basicBlocks.length bCert env tgt = true)
    (hInv : LocalsCertBisim bSrc.locals env l1 l2) :
    Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = none ∨
    ∃ bbNextSrc bbNextTgt entryEnv exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbNextSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbNextTgt ∧
      0 ≤ bbNextSrc.statements.length ∧
      stepAbsStmts bSrc.locals entryEnv (bbNextSrc.statements.drop 0) = some exitEnv ∧
      UniformBlockTermOk bSrc bCert bbNextSrc bbNextTgt exitEnv ∧
      LocalsCertBisim bSrc.locals entryEnv l1 l2 := by
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
        let ⟨bbNextSrc, hBBS⟩ := getElem?_some_of_lt bSrc.basicBlocks tgt (nat_blt_lt hLt)
        unfold isUniformBranchCollapseBody at hBodyRel
        let ⟨_, hBlocks⟩ := bool_and_true hBodyRel
        let ⟨bbNextTgt, hBBT, _⟩ := listRel_getElem?_left hBlocks hBBS
        unfold checkUniformBranchBody at hBodyCert
        let ⟨_, hLoop⟩ := bool_and_true hBodyCert
        have hBlkOk : checkUniformBranchBlock bSrc bTgt bCert tgt bbNextSrc = true := by
          have h0 := checkUniformBranchBlocksLoop_getElem? bSrc bTgt bCert 0 bSrc.basicBlocks tgt bbNextSrc hLoop hBBS
          rw [Nat.zero_add] at h0
          exact h0
        let ⟨_, exitEnv, hStmts, hTermOk⟩ := checkUniformBranchBlock_elim hBlkOk hC hBBT
        right
        exact ⟨bbNextSrc, bbNextTgt, tgtEnv, exitEnv, hBBS, hBBT, Nat.zero_le _,
          hStmts, hTermOk, localsCertBisim_mono hEdge hInv⟩

private theorem evalStep_uniform_cert_bisim
    {pSrc pTgt : Program} {cert : ProgramAbsCert} {s t : State}
    (hRel : StateUniformCertBisim pSrc pTgt cert s t) :
    (∃ s' t', evalStep pSrc 0 s = .step s' ∧ evalStep pTgt 0 t = .step t' ∧
      StateUniformCertBisim pSrc pTgt cert s' t') ∨
    (∃ out, evalStep pSrc 0 s = .done out ∧ evalStep pTgt 0 t = .done out) ∨
    (∃ fk, evalStep pSrc 0 s = .fault fk ∧ evalStep pTgt 0 t = .fault fk) := by
  let ⟨hCm, fSrc, fTgt, bSrc, bTgt, bCert, hFS, hFT, hDef, hBlk, hStmt,
       hBS, hBT, hBC, hBody, hCertB, hBlkState⟩ := hRel
  have hBodyCopy := hBody
  unfold isUniformBranchCollapseBody at hBodyCopy
  let ⟨hBHdr, hBlocks⟩ := bool_and_true hBodyCopy
  let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
  cases hBlkState with
  | inl hNoBB =>
    have hNoBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
      rw [← hBlk]; exact (listRel_getElem?_none_iff fSrc.blockIdx hBlocks).mp hNoBB
    right; right
    refine ⟨.unsupported, ?_, ?_⟩
    · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hNoBB]
    · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hNoBBT]
  | inr hInBB =>
    let ⟨bbSrc, bbTgt, curEnv, exitEnv, hBBS, hBBT, hStmtLe, hDropStmts, hTermOk, hInv⟩ := hInBB
    let ⟨bbTgt', hBBT', hBBRel⟩ := listRel_getElem?_left hBlocks hBBS
    have hBBTF : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := hBBT
    rw [← hBlk] at hBBT
    rw [hBBT] at hBBT'; injection hBBT' with hEqBB; subst hEqBB
    unfold isUniformBranchCollapseBlock at hBBRel
    let ⟨h12, hTermRel⟩ := bool_and_true hBBRel
    let ⟨hCleanB, hStmtsRel⟩ := bool_and_true h12
    have hClean : bbSrc.cleanup = bbTgt.cleanup := bool_beq_eq hCleanB
    have hStmtsEq : bbSrc.statements = bbTgt.statements :=
      listRel_eq (fun _ _ => stmtEq_eq) hStmtsRel
    cases hSS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
    | some st =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some st := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      rw [drop_eq_cons_of_getElem? hSS] at hDropStmts
      dsimp [stepAbsStmts] at hDropStmts
      cases hStep1 : stepAbsStmt bSrc.locals curEnv st with
      | none => rw [hStep1] at hDropStmts; cases hDropStmts
      | some nextEnv =>
        rw [hStep1] at hDropStmts; dsimp at hDropStmts
        cases evalStatement_cert_bisim_eq (cm := s.callerMem) hLocEq hStep1 hInv with
        | inl hF =>
          let ⟨fk, hF1, hF2⟩ := hF
          right; right
          refine ⟨fk, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp; rw [hSS]; exact hF1
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBTF]; dsimp
            rw [hST]; dsimp; rw [← hCm]; exact hF2
        | inr hSt =>
          let ⟨l1', l2', hSt1, hSt2, hInv'⟩ := hSt
          left
          refine ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := l1' }],
                    callerMem := s.callerMem },
                  { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := l2' }],
                    callerMem := t.callerMem }, ?_, ?_, ?_⟩
          · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp; rw [hSS]; exact hSt1
          · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBTF]; dsimp
            rw [hST]; dsimp; rw [← hCm]; exact hSt2
          · refine ⟨hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, hBlk, by dsimp; rw [hStmt],
              hBS, hBT, hBC, hBody, hCertB, Or.inr ⟨bbSrc, bbTgt, nextEnv, exitEnv, hBBS, hBBTF,
              getElem?_some_lt hSS, hDropStmts, hTermOk, hInv'⟩⟩
    | none =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      have hGe : bbSrc.statements.length ≤ fSrc.stmtIdx := by
        cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
        | inr hge => exact hge
        | inl hlt =>
          let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
          rw [hSS] at hx; cases hx
      have hIdxEq : fSrc.stmtIdx = bbSrc.statements.length := Nat.le_antisymm hStmtLe hGe
      have hAtEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length = true := nat_beq_of_eq hIdxEq
      have hAtEndT : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
        rw [← hStmtsEq, ← hStmt]; exact hAtEnd
      rw [hIdxEq, drop_length_nil] at hDropStmts
      injection hDropStmts with hEnvEq; subst hEnvEq
      have hEvS : evalStep pSrc 0 s = evalTerminator bSrc bbSrc fSrc s.callerMem := by
        unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
        rw [hSS, if_bool_true hAtEnd]
      have hEvT : evalStep pTgt 0 t = evalTerminator bTgt bbTgt fTgt s.callerMem := by
        unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [← hBlk, hBBT]; dsimp
        rw [hST, if_bool_true hAtEndT, ← hCm]
      unfold UniformBlockTermOk at hTermOk
      cases hTS : bbSrc.terminator with
      | goto t1 =>
        rw [hTS] at hTermOk hTermRel
        cases hTT : bbTgt.terminator with
        | goto t2 =>
          rw [hTT] at hTermOk hTermRel
          have ht : t1 = t2 := nat_beq_eq hTermRel
          subst ht
          left
          refine ⟨{ frames := [{ fSrc with blockIdx := t1, stmtIdx := 0 }], callerMem := s.callerMem },
                  { frames := [{ fTgt with blockIdx := t1, stmtIdx := 0 }], callerMem := t.callerMem },
                  ?_, ?_,
                  hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, rfl, rfl,
                  hBS, hBT, hBC, hBody, hCertB,
                  jump_uniform_cert_bisim hBody hCertB hTermOk hInv⟩
          · rw [hEvS]; unfold evalTerminator; rw [hTS]; rfl
          · rw [hEvT]; unfold evalTerminator; rw [hTT, hCm]; rfl
        | _ => rw [hTT] at hTermOk; exact False.elim hTermOk
      | return_ =>
        rw [hTS] at hTermOk hTermRel
        cases hTT : bbTgt.terminator with
        | return_ =>
          rw [hTT] at hTermOk
          cases hC : bbSrc.cleanup with
          | true =>
            right; right
            refine ⟨.unsupported, ?_, ?_⟩
            · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hC]; rfl
            · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hClean, hC]; rfl
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
            · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hC]; dsimp; rw [hG1]
            · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hClean, hC]; dsimp; rw [hG2]
        | _ => rw [hTT] at hTermOk; exact False.elim hTermOk
      | switchInt discr targets =>
        rw [hTS] at hTermOk hTermRel
        cases hTT : bbTgt.terminator with
        | goto target =>
          rw [hTT] at hTermOk hTermRel; dsimp [isUniformBranchCollapseTerm] at hTermRel
          let ⟨afterEnv, hStepCol, hEdge⟩ := hTermOk
          let ⟨l1', hEvTermS, hInv1⟩ := stepCollapsedSwitchOperand_sound
            (cm := s.callerMem) hInv hTS hTermRel hStepCol
          left
          refine ⟨{ frames := [{ fSrc with blockIdx := target, stmtIdx := 0, locals := l1' }],
                    callerMem := s.callerMem },
                  { frames := [{ fTgt with blockIdx := target, stmtIdx := 0 }],
                    callerMem := t.callerMem }, ?_, ?_,
                  hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, rfl, rfl,
                  hBS, hBT, hBC, hBody, hCertB,
                  jump_uniform_cert_bisim hBody hCertB hEdge hInv1⟩
          · rw [hEvS]; exact hEvTermS
          · rw [hEvT]; unfold evalTerminator; rw [hTT, hCm]; rfl
        | switchInt d2 ts2 =>
          rw [hTT] at hTermOk hTermRel
          dsimp [isUniformBranchCollapseTerm, terminatorEq] at hTermRel
          let ⟨hDEqB, hTsEqB⟩ := bool_and_true hTermRel
          have hDEq : discr = d2 := operandEq_eq hDEqB
          have hTsEq : targets = ts2 := switchTargetsEq_eq hTsEqB
          subst hDEq; subst hTsEq
          let ⟨afterEnv, hStepOp, hOwOk, hBsOk⟩ := hTermOk
          cases evalPrimitiveOperand_cert_bisim_eq hInv hStepOp with
          | inl hErr =>
            let ⟨fk, h1, h2⟩ := hErr
            right; right
            refine ⟨fk, ?_, ?_⟩
            · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
            · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
          | inr hOk =>
            let ⟨dv, l1, l2, h1, h2, hInv1⟩ := hOk
            cases dv with
            | scalar sv =>
              cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
              | error fk =>
                right; right
                refine ⟨fk, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]; dsimp; rw [hSw]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]; dsimp; rw [hSw]
              | ok tgt =>
                have hTgtOk := evalSwitchBranches_target_ok hOwOk hBsOk hSw
                left
                refine ⟨{ frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1 }],
                          callerMem := s.callerMem },
                        { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2 }],
                          callerMem := t.callerMem }, ?_, ?_,
                        hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, rfl, rfl,
                        hBS, hBT, hBC, hBody, hCertB,
                        jump_uniform_cert_bisim hBody hCertB hTgtOk hInv1⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]; dsimp; rw [hSw]; rfl
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]; dsimp
                  rw [hSw, hCm]; rfl
            | bool b =>
              cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
              | error fk =>
                right; right
                refine ⟨fk, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]; dsimp; rw [hSw]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]; dsimp; rw [hSw]
              | ok tgt =>
                have hTgtOk := evalBoolSwitchBranches_target_ok hOwOk hBsOk hSw
                left
                refine ⟨{ frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := l1 }],
                          callerMem := s.callerMem },
                        { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := l2 }],
                          callerMem := t.callerMem }, ?_, ?_,
                        hCm, _, _, bSrc, bTgt, bCert, rfl, rfl, hDef, rfl, rfl,
                        hBS, hBT, hBC, hBody, hCertB,
                        jump_uniform_cert_bisim hBody hCertB hTgtOk hInv1⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]; dsimp; rw [hSw]; rfl
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]; dsimp
                  rw [hSw, hCm]; rfl
            | ptr _ =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
            | unit =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
            | enumVal _ _ =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
            | tuple _ =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
            | bytes _ =>
              right; right; refine ⟨.unsupported, ?_, ?_⟩
              · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [h1]
              · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hLocEq, h2]
        | _ => rw [hTT] at hTermOk; exact False.elim hTermOk
      | unreachable =>
        rw [hTS] at hTermOk
        cases hTT : bbTgt.terminator with
        | unreachable =>
          right; right; refine ⟨.undefined, ?_, ?_⟩
          · rw [hEvS]; unfold evalTerminator; rw [hTS]
          · rw [hEvT]; unfold evalTerminator; rw [hTT]
        | _ => rw [hTT] at hTermOk; exact False.elim hTermOk
      | unwindResume =>
        rw [hTS] at hTermOk
        cases hTT : bbTgt.terminator with
        | unwindResume =>
          right; right; refine ⟨.unsupported, ?_, ?_⟩
          · rw [hEvS]; unfold evalTerminator; rw [hTS]
          · rw [hEvT]; unfold evalTerminator; rw [hTT]
        | _ => rw [hTT] at hTermOk; exact False.elim hTermOk
      | assert _ _ _ _ _ =>
        rw [hTS] at hTermOk
        cases hTT : bbTgt.terminator with
        | assert _ _ _ _ _ =>
          right; right; refine ⟨.unsupported, ?_, ?_⟩
          · rw [hEvS]; unfold evalTerminator; rw [hTS]
          · rw [hEvT]; unfold evalTerminator; rw [hTT]
        | _ => rw [hTT] at hTermOk; exact False.elim hTermOk
      | call _ _ _ _ _ =>
        rw [hTS] at hTermOk
        cases hTT : bbTgt.terminator with
        | call _ _ _ _ _ =>
          right; right; refine ⟨.unsupported, ?_, ?_⟩
          · rw [hEvS]; unfold evalTerminator; rw [hTS]
          · rw [hEvT]; unfold evalTerminator; rw [hTT]
        | _ => rw [hTT] at hTermOk; exact False.elim hTermOk
      | unsupported =>
        rw [hTS] at hTermOk
        cases hTT : bbTgt.terminator with
        | unsupported =>
          right; right; refine ⟨.unsupported, ?_, ?_⟩
          · rw [hEvS]; unfold evalTerminator; rw [hTS]
          · rw [hEvT]; unfold evalTerminator; rw [hTT]
        | _ => rw [hTT] at hTermOk; exact False.elim hTermOk

private theorem entry_uniform_cert_bisim
    {bSrc bTgt : Body} {bCert : BodyAbsCert} {l1 l2 : List LocalSlot}
    (hBodyRel : isUniformBranchCollapseBody bSrc bTgt = true)
    (hBodyCert : checkUniformBranchBody bSrc bTgt bCert = true)
    (hNonEmpty : bSrc.basicBlocks.isEmpty = false)
    (hInitLocs : LocalsCertBisim bSrc.locals (initAbsEnvLoop bSrc 0 bSrc.locals) l1 l2) :
    ∃ bb0Src bb0Tgt env0 exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks 0 = some bb0Src ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks 0 = some bb0Tgt ∧
      0 ≤ bb0Src.statements.length ∧
      stepAbsStmts bSrc.locals env0 (bb0Src.statements.drop 0) = some exitEnv ∧
      UniformBlockTermOk bSrc bCert bb0Src bb0Tgt exitEnv ∧
      LocalsCertBisim bSrc.locals env0 l1 l2 := by
  have hCertCopy := hBodyCert
  unfold checkUniformBranchBody at hCertCopy
  let ⟨h12, hLoop⟩ := bool_and_true hCertCopy
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
      have h0Lt : 0 < bSrc.basicBlocks.length := list_pos_of_isEmpty_false hNonEmpty
      let ⟨bb0Src, hBBS0⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 h0Lt
      unfold isUniformBranchCollapseBody at hBodyRel
      let ⟨_, hBlocks⟩ := bool_and_true hBodyRel
      let ⟨bb0Tgt, hBBT0, _⟩ := listRel_getElem?_left hBlocks hBBS0
      have hBlk0 : checkUniformBranchBlock bSrc bTgt bCert 0 bb0Src = true :=
        checkUniformBranchBlocksLoop_getElem? bSrc bTgt bCert 0 bSrc.basicBlocks 0 bb0Src hLoop hBBS0
      let ⟨_, exitEnv, hStmts, hTermOk⟩ := checkUniformBranchBlock_elim hBlk0 hC0 hBBT0
      exact ⟨bb0Src, bb0Tgt, env0, exitEnv, hBBS0, hBBT0, Nat.zero_le _,
        hStmts, hTermOk, localsCertBisim_mono hEntry hInitLocs⟩

private theorem uniformBranch_cert_query_iff {pSrc pTgt : Program}
    {cert : ProgramAbsCert} (q : Query)
    (hRel : isUniformBranchCollapseProgram pSrc pTgt = true)
    (hCert : checkUniformBranchProgram pSrc pTgt cert = true) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := uniformBranch_initState_eq q hRel
  apply bisim_lift_disj (R := StateUniformCertBisim pSrc pTgt cert)
  · intro k; rw [hInitEq]
  · intro s₀ t₀ hIS hIT
    have hISCopy := hIS
    rw [hInitEq] at hIS
    have hEqST : s₀ = t₀ := by rw [hIS] at hIT; injection hIT
    subst hEqST
    let ⟨_, _, bSrc, hBS, hNE, _, _, _, hArgs, hS0⟩ := initState_ok_elim hISCopy
    unfold isUniformBranchCollapseProgram at hRel
    let ⟨hHdr, hBodies⟩ := bool_and_true hRel
    let ⟨bTgt, hBT0, hBody⟩ := listRel_getElem?_left hBodies hBS
    unfold checkUniformBranchProgram at hCert
    let ⟨_, hCertZip⟩ := bool_and_true hCert
    have hZ := getElem?_zip hBS hBT0
    let ⟨bCert, hBC, hCertB⟩ := listRel_getElem?_left hCertZip hZ
    let ⟨hBHdr, _, _, hHasAnn⟩ := uniformBranchBody_storage_eq hBody
    let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
    have hLoopEq := initLocalsLoop_eq_of_storage_eq q.args hArg hLoc (fun idx _ _ => hHasAnn idx)
    have hInitBisim := initLocals_cert_bisim_uniform (args := q.args) hBody hArgs
    rw [← hLoopEq] at hInitBisim
    let ⟨bb0Src, bb0Tgt, env0, exitEnv, hBBS0, hBBT0, hLe0, hStmts, hTermOk, hInv0⟩ :=
      entry_uniform_cert_bisim hBody hCertB hNE hInitBisim
    subst hS0
    exact ⟨rfl, _, _, bSrc, bTgt, bCert, rfl, rfl, rfl, rfl, rfl,
      hBS, hBT0, hBC, hBody, hCertB,
      Or.inr ⟨bb0Src, bb0Tgt, env0, exitEnv, hBBS0, hBBT0, hLe0, hStmts, hTermOk, hInv0⟩⟩
  · intro s t hSt
    exact evalStep_uniform_cert_bisim hSt

private theorem vc_transport_uniformBranchCollapse_certified_iff_priv
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isUniformBranchCollapseProgram pSrc pTgt = true)
    (hCert : checkUniformBranchProgram pSrc pTgt cert = true) :
    PrivFullSemanticEquiv pSrc pTgt := by
  have hRelCopy := hRel
  unfold isUniformBranchCollapseProgram at hRelCopy
  let ⟨hHdr, hBodies⟩ := bool_and_true hRelCopy
  refine fullSemanticEquiv_of_query_iff hHdr ?_
    (fun q => uniformBranch_cert_query_iff q hRel hCert)
    (fun defId args =>
      (uniformBranch_cert_query_iff { args := args }
        (uniformBranch_entryProg defId hRel) hCert).1)
  intro defId bSrc bTgt hBS hBT
  let ⟨bTgt', hBT', hBody⟩ := listRel_getElem?_left hBodies hBS
  rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
  let ⟨hBHdr, hBLen, hSt, _⟩ := uniformBranchBody_storage_eq hBody
  exact ⟨hBHdr, list_isEmpty_eq_of_length hBLen, hSt⟩

/-! ### Stage 4 Private Helpers — Layer E: Pass 5 (5a/5b) & Theorem 6 -/

private theorem allTgtBlocksCoveredOnce_eq_one {remap : BlockRemap} {k j : Nat}
    (hAll : allTgtBlocksCoveredOnce remap k = true)
    (hLt : j < k) :
    countMappedTo j remap = 1 := by
  induction k with
  | zero => exact False.elim (Nat.not_lt_zero j hLt)
  | succ m ih =>
    dsimp [allTgtBlocksCoveredOnce] at hAll
    let ⟨hM, hRest⟩ := bool_and_true hAll
    cases hEq : Nat.beq j m with
    | true =>
      have hJM : j = m := nat_beq_eq hEq
      subst hJM
      exact nat_beq_eq hM
    | false =>
      have hLe : j ≤ m := Nat.le_of_lt_succ hLt
      cases Nat.lt_or_ge j m with
      | inl hJltM => exact ih hRest hJltM
      | inr hMleJ =>
        have hJM : j = m := Nat.le_antisymm hLe hMleJ
        rw [hJM, nat_beq_refl] at hEq
        cases hEq

private theorem exists_mapped_of_countMappedTo_pos {j : BasicBlockId}
    {remap : BlockRemap}
    (hPos : 0 < countMappedTo j remap) :
    ∃ srcIdx, Trusted.MirSemantics.getElem? remap srcIdx = some (some j) := by
  induction remap with
  | nil => exact False.elim (Nat.not_lt_zero 0 hPos)
  | cons hd rest ih =>
    cases hd with
    | none =>
      dsimp [countMappedTo] at hPos
      let ⟨i, hi⟩ := ih hPos
      exact ⟨i + 1, hi⟩
    | some m =>
      dsimp [countMappedTo] at hPos
      cases hEq : Nat.beq m j with
      | true =>
        have hMJ : m = j := nat_beq_eq hEq
        subst hMJ
        exact ⟨0, rfl⟩
      | false =>
        rw [if_bool_false hEq, Nat.zero_add] at hPos
        let ⟨i, hi⟩ := ih hPos
        exact ⟨i + 1, hi⟩

private theorem checkMappedBlocksLoop_mapped_elim {bSrc bTgt : Body}
    {remap : BlockRemap} {base i j : Nat} {bbs : List BasicBlock} {bbSrc : BasicBlock}
    (hLoop : checkMappedBlocksLoop bSrc bTgt remap base bbs = true)
    (hGet : Trusted.MirSemantics.getElem? bbs i = some bbSrc)
    (hMap : Trusted.MirSemantics.getElem? remap (base + i) = some (some j)) :
    ∃ bbTgt,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks j = some bbTgt ∧
      bbSrc.cleanup = bbTgt.cleanup ∧
      bbSrc.statements = bbTgt.statements ∧
      remapTerminator bSrc.basicBlocks.length bTgt.basicBlocks.length
        remap bbSrc.terminator bbTgt.terminator = true := by
  induction bbs generalizing base i with
  | nil => cases hGet
  | cons b rest ih =>
    dsimp [checkMappedBlocksLoop] at hLoop
    let ⟨hHead, hTail⟩ := bool_and_true hLoop
    cases i with
    | zero =>
      injection hGet with hEqB; subst hEqB
      have hMap0 : Trusted.MirSemantics.getElem? remap base = some (some j) := by
        rw [Nat.add_zero] at hMap; exact hMap
      rw [hMap0] at hHead; dsimp at hHead
      cases hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks j with
      | none => rw [hBBT] at hHead; cases hHead
      | some bbTgt =>
        rw [hBBT] at hHead; dsimp at hHead
        let ⟨h12, hTerm⟩ := bool_and_true hHead
        let ⟨hClean, hStmts⟩ := bool_and_true h12
        exact ⟨bbTgt, rfl, bool_beq_eq hClean,
          listRel_eq (fun _ _ => stmtEq_eq) hStmts, hTerm⟩
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      rw [← hAdd] at hMap
      exact ih hTail hGet hMap

private theorem deadCompactionBody_parts {remap : BlockRemap} {bSrc bTgt : Body}
    (h : isDeadBlockCompactionBody remap bSrc bTgt = true) :
    bodyHeaderEq bSrc bTgt = true ∧
    remap.length = bSrc.basicBlocks.length ∧
    allTgtBlocksCoveredOnce remap bTgt.basicBlocks.length = true ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    (bSrc.basicBlocks.isEmpty = false →
      Trusted.MirSemantics.getElem? remap 0 = some (some 0)) ∧
    checkMappedBlocksLoop bSrc bTgt remap 0 bSrc.basicBlocks = true := by
  unfold isDeadBlockCompactionBody at h
  let ⟨h1234, hLoop⟩ := bool_and_true h
  let ⟨h123, hEntry⟩ := bool_and_true h1234
  let ⟨h12, hCov⟩ := bool_and_true h123
  let ⟨hBHdr, hRemLenB⟩ := bool_and_true h12
  refine ⟨hBHdr, nat_beq_eq hRemLenB, hCov, ?_, ?_, hLoop⟩
  · cases hES : bSrc.basicBlocks.isEmpty with
    | true =>
      rw [if_bool_true hES] at hEntry
      rw [hEntry]
    | false =>
      rw [if_bool_false hES] at hEntry
      let ⟨hNotEmptyT, _⟩ := bool_and_true hEntry
      rw [bool_not_true hNotEmptyT]
  · intro hES
    rw [if_bool_false hES] at hEntry
    let ⟨_, hR0⟩ := bool_and_true hEntry
    cases hG0 : Trusted.MirSemantics.getElem? remap 0 with
    | none => rw [hG0] at hR0; cases hR0
    | some opt0 =>
      rw [hG0] at hR0
      cases opt0 with
      | none => cases hR0
      | some j0 =>
        dsimp at hR0
        rw [nat_beq_eq hR0]

private theorem deadCompaction_tgt_block_has_src {remap : BlockRemap}
    {bSrc bTgt : Body} {j : Nat} {bbTgt : BasicBlock}
    (hBody : isDeadBlockCompactionBody remap bSrc bTgt = true)
    (hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks j = some bbTgt) :
    ∃ srcIdx bbSrc,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks srcIdx = some bbSrc ∧
      bbSrc.statements = bbTgt.statements := by
  let ⟨_, hRemLen, hCov, _, _, hLoop⟩ := deadCompactionBody_parts hBody
  have hJLt : j < bTgt.basicBlocks.length := getElem?_some_lt hBBT
  have hCnt1 : countMappedTo j remap = 1 := allTgtBlocksCoveredOnce_eq_one hCov hJLt
  have hPos : 0 < countMappedTo j remap := by
    rw [hCnt1]; exact Nat.zero_lt_succ 0
  let ⟨srcIdx, hMap⟩ := exists_mapped_of_countMappedTo_pos hPos
  have hSrcLt : srcIdx < bSrc.basicBlocks.length := by
    rw [← hRemLen]; exact getElem?_some_lt hMap
  let ⟨bbSrc, hBBS⟩ := getElem?_some_of_lt bSrc.basicBlocks srcIdx hSrcLt
  have hMap0 : Trusted.MirSemantics.getElem? remap (0 + srcIdx) = some (some j) := by
    rw [Nat.zero_add]; exact hMap
  let ⟨bbTgt', hBBT', _, hStmtsEq, _⟩ :=
    checkMappedBlocksLoop_mapped_elim hLoop hBBS hMap0
  rw [hBBT] at hBBT'; injection hBBT' with hEqBB; subst hEqBB
  exact ⟨srcIdx, bbSrc, hBBS, hStmtsEq⟩

private theorem deadCompaction_storageInBounds_imp {remap : BlockRemap}
    {bSrc bTgt : Body}
    (hBody : isDeadBlockCompactionBody remap bSrc bTgt = true)
    (hStSrc : storageAnnotationsInBounds bSrc = true) :
    storageAnnotationsInBounds bTgt = true := by
  let ⟨hBHdr, _, _, _, _, _⟩ := deadCompactionBody_parts hBody
  let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
  dsimp [storageAnnotationsInBounds] at hStSrc
  dsimp [storageAnnotationsInBounds]
  rw [← hLocEq]
  apply list_all_of_forall_getElem?
  intro j bbTgt hBBT
  let ⟨_, bbSrc, hBBS, hStmtsEq⟩ := deadCompaction_tgt_block_has_src hBody hBBT
  have hBBAll := list_all_getElem? hStSrc hBBS
  rw [← hStmtsEq]
  exact hBBAll

private theorem deadCompaction_hasStorageAnn_imp {remap : BlockRemap}
    {bSrc bTgt : Body} {idx : LocalId}
    (hBody : isDeadBlockCompactionBody remap bSrc bTgt = true)
    (hAnnTgt : hasStorageAnnotation bTgt idx = true) :
    hasStorageAnnotation bSrc idx = true := by
  unfold hasStorageAnnotation at hAnnTgt
  unfold hasStorageAnnotation
  let ⟨j, bbTgt, hBBT, hAnyTgt⟩ := list_any_getElem? hAnnTgt
  let ⟨_, bbSrc, hBBS, hStmtsEq⟩ := deadCompaction_tgt_block_has_src hBody hBBT
  rw [← hStmtsEq] at hAnyTgt
  exact list_any_of_getElem? hBBS hAnyTgt

private noncomputable def DeadBlockIdxRel (bSrc bTgt : Body) (remap : BlockRemap)
    (srcIdx tgtIdx : BasicBlockId) : Prop :=
  (srcIdx < bSrc.basicBlocks.length ∧
    Trusted.MirSemantics.getElem? remap srcIdx = some (some tgtIdx)) ∨
  (bSrc.basicBlocks.length ≤ srcIdx ∧ bTgt.basicBlocks.length ≤ tgtIdx)

private theorem remapEdge_elim {bSrc bTgt : Body} {remap : BlockRemap}
    {srcTarget tgtTarget : BasicBlockId}
    (hEdge : remapEdge bSrc.basicBlocks.length bTgt.basicBlocks.length
      remap srcTarget tgtTarget = true) :
    DeadBlockIdxRel bSrc bTgt remap srcTarget tgtTarget := by
  unfold remapEdge at hEdge
  cases hLt : Nat.blt srcTarget bSrc.basicBlocks.length with
  | true =>
    rw [if_bool_true hLt] at hEdge
    cases hM : Trusted.MirSemantics.getElem? remap srcTarget with
    | none => rw [hM] at hEdge; cases hEdge
    | some opt =>
      rw [hM] at hEdge
      cases opt with
      | none => cases hEdge
      | some mapped =>
        dsimp at hEdge
        let ⟨hEqB, _⟩ := bool_and_true hEdge
        rw [nat_beq_eq hEqB] at hM
        left
        exact ⟨nat_blt_lt hLt, hM⟩
  | false =>
    rw [if_bool_false hLt] at hEdge
    right
    exact ⟨nat_blt_false_ge hLt, nat_blt_false_ge (bool_not_true hEdge)⟩

private theorem deadCompaction_entryProg {remapList : List BlockRemap}
    {pSrc pTgt : Program} (defId : DefId)
    (h : isDeadBlockCompactionProgram remapList pSrc pTgt = true) :
    isDeadBlockCompactionProgram remapList
      (entryProgForBody pSrc defId) (entryProgForBody pTgt defId) = true := by
  unfold isDeadBlockCompactionProgram at h
  let ⟨h12, hZip⟩ := bool_and_true h
  let ⟨hHdr, hRemLen⟩ := bool_and_true h12
  unfold isDeadBlockCompactionProgram
  exact bool_and_intro (bool_and_intro (programHeaderEq_entryProg defId hHdr) hRemLen) hZip

/-! #### Theorem 5a: Forward Codegen Refinement (`DeadBlockCompaction`) -/

private noncomputable def StateDeadCompactionFwdRel (remapList : List BlockRemap)
    (pSrc pTgt : Program) (s t : State) : Prop :=
  s.callerMem = t.callerMem ∧
  ∃ fSrc fTgt bSrc bTgt remap,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt ∧
    Trusted.MirSemantics.getElem? remapList fSrc.defId = some remap ∧
    isDeadBlockCompactionBody remap bSrc bTgt = true ∧
    DeadBlockIdxRel bSrc bTgt remap fSrc.blockIdx fTgt.blockIdx ∧
    LocalsFwdRefines bSrc.locals fSrc.locals fTgt.locals

private theorem deadCompaction_fwd_step {remapList : List BlockRemap}
    {pSrc pTgt : Program} {s t : State}
    (hRel : StateDeadCompactionFwdRel remapList pSrc pTgt s t) :
    (∀ s', evalStep pSrc 0 s = .step s' →
      ∃ t', evalStep pTgt 0 t = .step t' ∧
        StateDeadCompactionFwdRel remapList pSrc pTgt s' t') ∧
    (∀ out, evalStep pSrc 0 s = .done out →
      evalStep pTgt 0 t = .done out) := by
  let ⟨hCm, fSrc, fTgt, bSrc, bTgt, remap, hFS, hFT, hDef, hStmt,
       hBS, hBT, hRM, hBody, hBlkRel, hInv⟩ := hRel
  let ⟨hBHdr, _, _, _, _, hLoop⟩ := deadCompactionBody_parts hBody
  let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
  cases hBlkRel with
  | inr hOob =>
    have hNoBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = none :=
      getElem?_none_of_ge hOob.1
    constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hNoBBS] at hEv; cases hEv)
  | inl hMapped =>
    let ⟨hLtS, hMapIdx⟩ := hMapped
    let ⟨bbSrc, hBBS⟩ := getElem?_some_of_lt bSrc.basicBlocks fSrc.blockIdx hLtS
    have hMap0 : Trusted.MirSemantics.getElem? remap (0 + fSrc.blockIdx) = some (some fTgt.blockIdx) := by
      rw [Nat.zero_add]; exact hMapIdx
    let ⟨bbTgt, hBBT, hClean, hStmtsEq, hTermRem⟩ :=
      checkMappedBlocksLoop_mapped_elim hLoop hBBS hMap0
    cases hSS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
    | some st =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some st := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      constructor
      · intro s' hEv
        unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
        rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS] at hEv
        let ⟨locs1', locs2', hEqS, hEv2, hInv'⟩ := evalStatement_fwd_eq hLocEq hInv hEv
        subst hEqS
        refine ⟨{ frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' }],
                  callerMem := t.callerMem }, ?_,
          hCm, _, _, bSrc, bTgt, remap, rfl, rfl, hDef, by dsimp; rw [hStmt],
          hBS, hBT, hRM, hBody, Or.inl ⟨hLtS, hMapIdx⟩, hInv'⟩
        unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
        rw [hBBT]; dsimp; rw [hST]; dsimp; rw [← hCm]; exact hEv2
      · intro out hEv
        unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
        rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS] at hEv
        exact False.elim (evalStatement_never_done bSrc fSrc s.callerMem st out hEv)
    | none =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      cases hAtEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
      | false =>
        constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS, if_bool_false hAtEnd] at hEv; cases hEv)
      | true =>
        have hAtEndT : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
          rw [← hStmtsEq, ← hStmt]; exact hAtEnd
        cases hTS : bbSrc.terminator with
        | goto gSrc =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | goto gTgt =>
            rw [hTT] at hTermRem
            have hNextRel := remapEdge_elim hTermRem
            constructor
            · intro s' hEv
              unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
              rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
              rw [hSS, if_bool_true hAtEnd] at hEv
              unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp [jumpToBlock] at hEv
              injection hEv with hEqS; subst hEqS
              refine ⟨{ frames := [{ fTgt with blockIdx := gTgt, stmtIdx := 0 }],
                        callerMem := t.callerMem }, ?_,
                hCm, _, _, bSrc, bTgt, remap, rfl, rfl, hDef, rfl,
                hBS, hBT, hRM, hBody, hNextRel, hInv⟩
              unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
              rw [hBBT]; dsimp; rw [hST, if_bool_true hAtEndT]
              unfold evalTerminator; rw [hTT]; rfl
            · intro out hEv
              unfold evalStep at hEv
              rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv
              rw [hBBS] at hEv; dsimp at hEv; rw [hSS, if_bool_true hAtEnd] at hEv
              unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | return_ =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | return_ =>
            have hRet := evalTerminator_eq_fwd (bSrc := bSrc) (bTgt := bTgt)
              (bbSrc := bbSrc) (bbTgt := bbTgt) (fSrc := fSrc) (fTgt := fTgt)
              (cm := s.callerMem) hLocEq hClean (by rw [hTS, hTT]) hInv
            constructor
            · intro s' hEv
              unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
              rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
              rw [hSS, if_bool_true hAtEnd] at hEv
              unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
              cases hCl : bbSrc.cleanup with
              | true => rw [hCl] at hEv; cases hEv
              | false =>
                rw [hCl] at hEv; dsimp at hEv
                cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
                | none => rw [h0] at hEv; cases hEv
                | some sl =>
                  rw [h0] at hEv
                  cases sl with
                  | dead => cases hEv
                  | live opt => cases opt <;> cases hEv
            · intro out hEv
              unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
              rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
              rw [hSS, if_bool_true hAtEnd] at hEv
              unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
              rw [hBBT]; dsimp; rw [hST, if_bool_true hAtEndT, ← hCm]
              exact hRet.2 out hEv
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | switchInt d1 ts1 =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | switchInt d2 ts2 =>
            rw [hTT] at hTermRem; dsimp [remapTerminator] at hTermRem
            let ⟨h12t, hBsRel⟩ := bool_and_true hTermRem
            let ⟨hDEqB, hOwRel⟩ := bool_and_true h12t
            have hDEq : d1 = d2 := operandEq_eq hDEqB
            subst hDEq
            constructor
            · intro s' hEv
              unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
              rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
              rw [hSS, if_bool_true hAtEnd] at hEv
              unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
              cases hP : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
              | error _ => rw [hP] at hEv; cases hEv
              | ok res =>
                let ⟨dv, locs1⟩ := res
                rw [hP] at hEv; dsimp at hEv
                let ⟨locs2, hPT, hInv'⟩ := evalPrimitiveOperand_fwd_eq hInv hP
                cases dv with
                | scalar sv =>
                  dsimp at hEv
                  cases evalSwitchBranches_rel (w := sv.width) (discrBits := sv.bits) hOwRel hBsRel with
                  | inl hFlt =>
                    let ⟨_, hSw1, _⟩ := hFlt
                    rw [hSw1] at hEv; cases hEv
                  | inr hJmp =>
                    let ⟨tgt1, tgt2, hSw1, hSw2, hEdge⟩ := hJmp
                    rw [hSw1] at hEv; dsimp [jumpToBlock] at hEv
                    injection hEv with hEqS; subst hEqS
                    refine ⟨{ frames := [{ fTgt with blockIdx := tgt2, stmtIdx := 0, locals := locs2 }],
                              callerMem := t.callerMem }, ?_,
                      hCm, _, _, bSrc, bTgt, remap, rfl, rfl, hDef, rfl,
                      hBS, hBT, hRM, hBody, remapEdge_elim hEdge, hInv'⟩
                    unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
                    rw [hBBT]; dsimp; rw [hST, if_bool_true hAtEndT]
                    unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hLocEq, hPT]; dsimp; rw [hSw2]; rfl
                | bool b =>
                  dsimp at hEv
                  cases evalBoolSwitchBranches_rel (discr := b) hOwRel hBsRel with
                  | inl hFlt =>
                    let ⟨_, hSw1, _⟩ := hFlt
                    rw [hSw1] at hEv; cases hEv
                  | inr hJmp =>
                    let ⟨tgt1, tgt2, hSw1, hSw2, hEdge⟩ := hJmp
                    rw [hSw1] at hEv; dsimp [jumpToBlock] at hEv
                    injection hEv with hEqS; subst hEqS
                    refine ⟨{ frames := [{ fTgt with blockIdx := tgt2, stmtIdx := 0, locals := locs2 }],
                              callerMem := t.callerMem }, ?_,
                      hCm, _, _, bSrc, bTgt, remap, rfl, rfl, hDef, rfl,
                      hBS, hBT, hRM, hBody, remapEdge_elim hEdge, hInv'⟩
                    unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp
                    rw [hBBT]; dsimp; rw [hST, if_bool_true hAtEndT]
                    unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hLocEq, hPT]; dsimp; rw [hSw2]; rfl
                | ptr _ => cases hEv
                | unit => cases hEv
                | enumVal _ _ => cases hEv
                | tuple _ => cases hEv
                | bytes _ => cases hEv
            · intro out hEv
              unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv
              rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv
              rw [hSS, if_bool_true hAtEnd] at hEv
              unfold evalTerminator at hEv; rw [hTS] at hEv; dsimp at hEv
              cases hP : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
              | error _ => rw [hP] at hEv; cases hEv
              | ok res =>
                let ⟨dv, _⟩ := res
                rw [hP] at hEv; dsimp at hEv
                cases dv with
                | scalar sv =>
                  dsimp at hEv
                  cases hSw : evalSwitchBranches sv.width sv.bits ts1.otherwise ts1.branches <;>
                    rw [hSw] at hEv <;> cases hEv
                | bool b =>
                  dsimp at hEv
                  cases hSw : evalBoolSwitchBranches b ts1.otherwise ts1.branches <;>
                    rw [hSw] at hEv <;> cases hEv
                | ptr _ => cases hEv
                | unit => cases hEv
                | enumVal _ _ => cases hEv
                | tuple _ => cases hEv
                | bytes _ => cases hEv
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | unreachable =>
          constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS, if_bool_true hAtEnd] at hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)
        | unwindResume =>
          constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS, if_bool_true hAtEnd] at hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)
        | assert _ _ _ _ _ =>
          constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS, if_bool_true hAtEnd] at hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)
        | call _ _ _ _ _ =>
          constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS, if_bool_true hAtEnd] at hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)
        | unsupported =>
          constructor <;> (intro _ hEv; unfold evalStep at hEv; rw [hFS] at hEv; dsimp at hEv; rw [hBS] at hEv; dsimp at hEv; rw [hBBS] at hEv; dsimp at hEv; rw [hSS, if_bool_true hAtEnd] at hEv; unfold evalTerminator at hEv; rw [hTS] at hEv; cases hEv)

private theorem deadCompaction_fwd_query {remapList : List BlockRemap}
    {pSrc pTgt : Program} (q : Query)
    (hRel : isDeadBlockCompactionProgram remapList pSrc pTgt = true)
    (hWf : WellFormed pSrc q) :
    WellFormed pTgt q ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  apply fwd_sim_lift (R := StateDeadCompactionFwdRel remapList pSrc pTgt)
  · intro s₀ hIS
    let ⟨hC1, hC2, bSrc, hBS, hNE, hAL, hSB, hSup, hArgs, hS0⟩ := initState_ok_elim hIS
    unfold isDeadBlockCompactionProgram at hRel
    let ⟨h12, hZip⟩ := bool_and_true hRel
    let ⟨hHdr, hRemLenB⟩ := bool_and_true h12
    let ⟨hPw, hVer, hEnt, _⟩ := programHeaderEq_elim hHdr
    let ⟨_, hSomeZip, _⟩ := listRel_zip_left_rel (nat_beq_eq hRemLenB) hZip
    let ⟨remap, bTgt, hRM, hBT0, hBody⟩ := hSomeZip pSrc.entryDefId bSrc hBS
    have hBT : Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some bTgt := by
      rw [← hEnt]; exact hBT0
    let ⟨hBHdr, _, _, hEmptyEq, hEntry0, _⟩ := deadCompactionBody_parts hBody
    let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
    have hNET : bTgt.basicBlocks.isEmpty = false := by rw [← hEmptyEq]; exact hNE
    have hALT : (!Nat.blt bTgt.argumentCount bTgt.locals.length) = false := by
      rw [← hArg, ← hLoc, hAL]; rfl
    have hSBT : (!storageAnnotationsInBounds bTgt) = false := by
      rw [deadCompaction_storageInBounds_imp hBody hSB]; rfl
    have hSupT : (!bTgt.locals.all isSupportedScalarOrUnitTy) = false := by
      rw [← hLoc, hSup]; rfl
    have hArgsT : (!checkArgsMatch q.args ((bTgt.locals.drop 1).take bTgt.argumentCount)) = false := by
      rw [← hArg, ← hLoc, hArgs]; rfl
    have hIT : initState pTgt q = .ok {
        frames := [{
          defId := pTgt.entryDefId
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop bTgt q.args 0 bTgt.locals
        }]
        callerMem := q.callerMem
      } := by
      unfold initState
      rw [← hPw, ← hVer, if_bool_false hC1, if_bool_false hC2, hBT]; dsimp
      rw [if_bool_false hNET, if_bool_false hALT, if_bool_false hSBT,
          if_bool_false hSupT, if_bool_false hArgsT]
    subst hS0
    refine ⟨_, hIT, rfl, _, _, bSrc, bTgt, remap, rfl, rfl, hEnt, rfl,
      hBS, hBT, hRM, hBody,
      Or.inl ⟨list_pos_of_isEmpty_false hNE, hEntry0 hNE⟩,
      initLocalsLoop_fwd_of_ann_imp hArg hLoc hArgs
        (fun _ _ _ hAnnT => deadCompaction_hasStorageAnn_imp hBody hAnnT)⟩
  · intro s t hR
    exact deadCompaction_fwd_step hR
  · exact hWf

private theorem codegen_deadBlockCompaction_refines_unconditional_priv
    (pSrc pTgt : Program) (remapList : List BlockRemap)
    (hRel : isDeadBlockCompactionProgram remapList pSrc pTgt = true) :
    PrivForwardCodegenRefines pSrc pTgt := by
  have hRelCopy := hRel
  unfold isDeadBlockCompactionProgram at hRelCopy
  let ⟨h12, hZip⟩ := bool_and_true hRelCopy
  let ⟨hHdr, hRemLenB⟩ := bool_and_true h12
  let ⟨_, hSomeZip, _⟩ := listRel_zip_left_rel (nat_beq_eq hRemLenB) hZip
  refine forwardCodegenRefines_of_query_fwd hHdr ?_
    (fun q hWf => deadCompaction_fwd_query q hRel hWf)
    (fun defId args hWf =>
      (deadCompaction_fwd_query { args := args }
        (deadCompaction_entryProg defId hRel) hWf).1)
  intro defId bSrc bTgt hBS hBT
  let ⟨remap, bTgt', _, hBT', hBody⟩ := hSomeZip defId bSrc hBS
  rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
  let ⟨hBHdr, _, _, hEmptyEq, _, _⟩ := deadCompactionBody_parts hBody
  exact ⟨hBHdr, hEmptyEq, deadCompaction_storageInBounds_imp hBody⟩

/-! #### Theorem 5b: Certified VC Transport (`DeadBlockCompaction`) -/

private theorem preservesStorageAnnotationsLoop_elim {bSrc bTgt : Body}
    {n idx : Nat}
    (hLoop : preservesStorageAnnotationsLoop bSrc bTgt n = true)
    (hLt : idx < n)
    (hNotArg : Nat.ble idx bSrc.argumentCount = false) :
    hasStorageAnnotation bSrc idx = hasStorageAnnotation bTgt idx := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero idx hLt)
  | succ m ih =>
    dsimp [preservesStorageAnnotationsLoop] at hLoop
    let ⟨hHere, hRest⟩ := bool_and_true hLoop
    cases hEq : Nat.beq idx m with
    | true =>
      have hIM : idx = m := nat_beq_eq hEq
      subst hIM
      rw [if_bool_false hNotArg] at hHere
      exact bool_beq_eq hHere
    | false =>
      have hLe : idx ≤ m := Nat.le_of_lt_succ hLt
      cases Nat.lt_or_ge idx m with
      | inl hIltM => exact ih hRest hIltM
      | inr hMleI =>
        have hIM : idx = m := Nat.le_antisymm hLe hMleI
        rw [hIM, nat_beq_refl] at hEq
        cases hEq

private theorem deadCompaction_cert_body_eq {remap : BlockRemap} {bSrc bTgt : Body}
    (hBody : isDeadBlockCompactionBody remap bSrc bTgt = true)
    (hCertB : checkDeadBlockStorageSafeBody bSrc bTgt = true) :
    bodyHeaderEq bSrc bTgt = true ∧
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty ∧
    storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt ∧
    (∀ args, initLocalsLoop bSrc args 0 bSrc.locals =
      initLocalsLoop bTgt args 0 bTgt.locals) := by
  let ⟨hBHdr, _, _, hEmptyEq, _, _⟩ := deadCompactionBody_parts hBody
  let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  unfold checkDeadBlockStorageSafeBody at hCertB
  let ⟨hStSrc, hPresLoop⟩ := bool_and_true hCertB
  have hStTgt := deadCompaction_storageInBounds_imp hBody hStSrc
  refine ⟨hBHdr, hEmptyEq, by rw [hStSrc, hStTgt], ?_⟩
  intro args
  exact initLocalsLoop_eq_of_storage_eq args hArg hLoc
    (fun idx hLt hNotArg => preservesStorageAnnotationsLoop_elim hPresLoop hLt hNotArg)

private theorem deadCompaction_cert_initState_eq {remapList : List BlockRemap}
    {pSrc pTgt : Program} (q : Query)
    (hRel : isDeadBlockCompactionProgram remapList pSrc pTgt = true)
    (hCert : checkDeadBlockStorageSafeProgram pSrc pTgt = true) :
    initState pSrc q = initState pTgt q := by
  unfold isDeadBlockCompactionProgram at hRel
  let ⟨h12, hZip⟩ := bool_and_true hRel
  let ⟨hHdr, hRemLenB⟩ := bool_and_true h12
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  let ⟨_, hSomeZip, hNoneZip⟩ := listRel_zip_left_rel (nat_beq_eq hRemLenB) hZip
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact hNoneZip pSrc.entryDefId
  · intro bSrc hBS
    let ⟨remap, bTgt, _, hBT0, hBody⟩ := hSomeZip pSrc.entryDefId bSrc hBS
    let ⟨bTgt', hBT', hCertB⟩ := listRel_getElem?_left hCert hBS
    rw [hBT0] at hBT'; injection hBT' with hEqB; subst hEqB
    have hBT : Trusted.MirSemantics.getElem? pTgt.bodies pTgt.entryDefId = some bTgt := by
      rw [← hEnt]; exact hBT0
    let ⟨hBHdr, hEmptyEq, hStEq, hLoopEq⟩ := deadCompaction_cert_body_eq hBody hCertB
    exact ⟨bTgt, hBT, hBHdr, hEmptyEq, hStEq, hLoopEq q.args⟩

private noncomputable def StateDeadCompactionBisim (remapList : List BlockRemap)
    (pSrc pTgt : Program) (s t : State) : Prop :=
  s.callerMem = t.callerMem ∧
  ∃ fSrc fTgt bSrc bTgt remap,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    fSrc.locals = fTgt.locals ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt ∧
    Trusted.MirSemantics.getElem? remapList fSrc.defId = some remap ∧
    isDeadBlockCompactionBody remap bSrc bTgt = true ∧
    DeadBlockIdxRel bSrc bTgt remap fSrc.blockIdx fTgt.blockIdx

private theorem deadCompaction_cert_step {remapList : List BlockRemap}
    {pSrc pTgt : Program} {s t : State}
    (hRel : StateDeadCompactionBisim remapList pSrc pTgt s t) :
    (∃ s' t', evalStep pSrc 0 s = .step s' ∧ evalStep pTgt 0 t = .step t' ∧
      StateDeadCompactionBisim remapList pSrc pTgt s' t') ∨
    (∃ out, evalStep pSrc 0 s = .done out ∧ evalStep pTgt 0 t = .done out) ∨
    (∃ fk, evalStep pSrc 0 s = .fault fk ∧ evalStep pTgt 0 t = .fault fk) := by
  let ⟨hCm, fSrc, fTgt, bSrc, bTgt, remap, hFS, hFT, hDef, hStmt, hLocs,
       hBS, hBT, hRM, hBody, hBlkRel⟩ := hRel
  let ⟨hBHdr, _, _, _, _, hLoop⟩ := deadCompactionBody_parts hBody
  let ⟨_, hBodyLocs, _, _⟩ := bodyHeaderEq_elim hBHdr
  cases hBlkRel with
  | inr hOob =>
    have hNoBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = none :=
      getElem?_none_of_ge hOob.1
    have hNoBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none :=
      getElem?_none_of_ge hOob.2
    right; right
    refine ⟨.unsupported, ?_, ?_⟩
    · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hNoBBS]
    · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hNoBBT]
  | inl hMapped =>
    let ⟨hLtS, hMapIdx⟩ := hMapped
    let ⟨bbSrc, hBBS⟩ := getElem?_some_of_lt bSrc.basicBlocks fSrc.blockIdx hLtS
    have hMap0 : Trusted.MirSemantics.getElem? remap (0 + fSrc.blockIdx) = some (some fTgt.blockIdx) := by
      rw [Nat.zero_add]; exact hMapIdx
    let ⟨bbTgt, hBBT, hClean, hStmtsEq, hTermRem⟩ :=
      checkMappedBlocksLoop_mapped_elim hLoop hBBS hMap0
    cases hSS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
    | some st =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some st := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      have hEvS : evalStep pSrc 0 s = evalStatement bSrc fSrc s.callerMem st := by
        unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp; rw [hSS]
      have hEvT : evalStep pTgt 0 t = evalStatement bTgt fTgt s.callerMem st := by
        unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp; rw [hST, ← hCm]
      cases evalStatement_congr_locals (cm := s.callerMem) (stmt := st) hBodyLocs hLocs with
      | inl hFlt =>
        let ⟨fk, h1, h2⟩ := hFlt
        right; right; exact ⟨fk, by rw [hEvS, h1], by rw [hEvT, h2]⟩
      | inr hStp =>
        let ⟨locs', h1, h2⟩ := hStp
        left
        refine ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs' }],
                  callerMem := s.callerMem },
                { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs' }],
                  callerMem := t.callerMem },
                by rw [hEvS, h1], by rw [hEvT, h2, hCm],
                hCm, _, _, bSrc, bTgt, remap, rfl, rfl, hDef, by dsimp; rw [hStmt], rfl,
                hBS, hBT, hRM, hBody, Or.inl ⟨hLtS, hMapIdx⟩⟩
    | none =>
      have hST : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
        rw [← hStmtsEq, ← hStmt]; exact hSS
      cases hAtEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
      | false =>
        have hAtEndT : Nat.beq fTgt.stmtIdx bbTgt.statements.length = false := by
          rw [← hStmtsEq, ← hStmt]; exact hAtEnd
        right; right
        refine ⟨.unsupported, ?_, ?_⟩
        · unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
          rw [hSS, if_bool_false hAtEnd]
        · unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
          rw [hST, if_bool_false hAtEndT]
      | true =>
        have hAtEndT : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
          rw [← hStmtsEq, ← hStmt]; exact hAtEnd
        have hEvS : evalStep pSrc 0 s = evalTerminator bSrc bbSrc fSrc s.callerMem := by
          unfold evalStep; rw [hFS]; dsimp; rw [hBS]; dsimp; rw [hBBS]; dsimp
          rw [hSS, if_bool_true hAtEnd]
        have hEvT : evalStep pTgt 0 t = evalTerminator bTgt bbTgt fTgt s.callerMem := by
          unfold evalStep; rw [hFT]; dsimp; rw [hBT]; dsimp; rw [hBBT]; dsimp
          rw [hST, if_bool_true hAtEndT, ← hCm]
        cases hTS : bbSrc.terminator with
        | goto gSrc =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | goto gTgt =>
            rw [hTT] at hTermRem
            left
            refine ⟨{ frames := [{ fSrc with blockIdx := gSrc, stmtIdx := 0 }], callerMem := s.callerMem },
                    { frames := [{ fTgt with blockIdx := gTgt, stmtIdx := 0 }], callerMem := t.callerMem },
                    ?_, ?_,
                    hCm, _, _, bSrc, bTgt, remap, rfl, rfl, hDef, rfl, hLocs,
                    hBS, hBT, hRM, hBody, remapEdge_elim hTermRem⟩
            · rw [hEvS]; unfold evalTerminator; rw [hTS]; rfl
            · rw [hEvT]; unfold evalTerminator; rw [hTT, hCm]; rfl
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | return_ =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | return_ =>
            cases evalTerminator_eq_congr (cm := s.callerMem) hBodyLocs hClean
                (by rw [hTS, hTT]) hLocs with
            | inl hFlt =>
              let ⟨fk, h1, h2⟩ := hFlt
              right; right; exact ⟨fk, by rw [hEvS, h1], by rw [hEvT, h2]⟩
            | inr hR =>
              cases hR with
              | inl hDone =>
                let ⟨out, h1, h2⟩ := hDone
                right; left; exact ⟨out, by rw [hEvS, h1], by rw [hEvT, h2]⟩
              | inr hJmp =>
                let ⟨_, _, h1, _⟩ := hJmp
                unfold evalTerminator at h1; rw [hTS] at h1; dsimp at h1
                cases hCl : bbSrc.cleanup with
                | true => rw [hCl] at h1; cases h1
                | false =>
                  rw [hCl] at h1; dsimp at h1
                  cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
                  | none => rw [h0] at h1; cases h1
                  | some sl =>
                    rw [h0] at h1
                    cases sl with
                    | dead => cases h1
                    | live opt => cases opt <;> cases h1
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | switchInt d1 ts1 =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | switchInt d2 ts2 =>
            rw [hTT] at hTermRem; dsimp [remapTerminator] at hTermRem
            let ⟨h12t, hBsRel⟩ := bool_and_true hTermRem
            let ⟨hDEqB, hOwRel⟩ := bool_and_true h12t
            have hDEq : d1 = d2 := operandEq_eq hDEqB
            subst hDEq
            cases hPrim : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
            | error fk =>
              right; right
              refine ⟨fk, ?_, ?_⟩
              · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
              · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                rw [← hBodyLocs, ← hLocs, hPrim]
            | ok res =>
              let ⟨dv, locsAfter⟩ := res
              cases dv with
              | scalar sv =>
                cases evalSwitchBranches_rel (w := sv.width) (discrBits := sv.bits) hOwRel hBsRel with
                | inl hFlt =>
                  let ⟨fk, hSw1, hSw2⟩ := hFlt
                  right; right
                  refine ⟨fk, ?_, ?_⟩
                  · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]; dsimp; rw [hSw1]
                  · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hBodyLocs, ← hLocs, hPrim]; dsimp; rw [hSw2]
                | inr hJmp =>
                  let ⟨tgt1, tgt2, hSw1, hSw2, hEdge⟩ := hJmp
                  left
                  refine ⟨{ frames := [{ fSrc with blockIdx := tgt1, stmtIdx := 0, locals := locsAfter }],
                            callerMem := s.callerMem },
                          { frames := [{ fTgt with blockIdx := tgt2, stmtIdx := 0, locals := locsAfter }],
                            callerMem := t.callerMem },
                          ?_, ?_,
                          hCm, _, _, bSrc, bTgt, remap, rfl, rfl, hDef, rfl, rfl,
                          hBS, hBT, hRM, hBody, remapEdge_elim hEdge⟩
                  · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]; dsimp; rw [hSw1]; rfl
                  · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hBodyLocs, ← hLocs, hPrim]; dsimp; rw [hSw2, hCm]; rfl
              | bool b =>
                cases evalBoolSwitchBranches_rel (discr := b) hOwRel hBsRel with
                | inl hFlt =>
                  let ⟨fk, hSw1, hSw2⟩ := hFlt
                  right; right
                  refine ⟨fk, ?_, ?_⟩
                  · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]; dsimp; rw [hSw1]
                  · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hBodyLocs, ← hLocs, hPrim]; dsimp; rw [hSw2]
                | inr hJmp =>
                  let ⟨tgt1, tgt2, hSw1, hSw2, hEdge⟩ := hJmp
                  left
                  refine ⟨{ frames := [{ fSrc with blockIdx := tgt1, stmtIdx := 0, locals := locsAfter }],
                            callerMem := s.callerMem },
                          { frames := [{ fTgt with blockIdx := tgt2, stmtIdx := 0, locals := locsAfter }],
                            callerMem := t.callerMem },
                          ?_, ?_,
                          hCm, _, _, bSrc, bTgt, remap, rfl, rfl, hDef, rfl, rfl,
                          hBS, hBT, hRM, hBody, remapEdge_elim hEdge⟩
                  · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]; dsimp; rw [hSw1]; rfl
                  · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp
                    rw [← hBodyLocs, ← hLocs, hPrim]; dsimp; rw [hSw2, hCm]; rfl
              | ptr _ =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
              | unit =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
              | enumVal _ _ =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
              | tuple _ =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
              | bytes _ =>
                right; right; refine ⟨.unsupported, ?_, ?_⟩
                · rw [hEvS]; unfold evalTerminator; rw [hTS]; dsimp; rw [hPrim]
                · rw [hEvT]; unfold evalTerminator; rw [hTT]; dsimp; rw [← hBodyLocs, ← hLocs, hPrim]
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | unreachable =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | unreachable =>
            right; right; refine ⟨.undefined, ?_, ?_⟩
            · rw [hEvS]; unfold evalTerminator; rw [hTS]
            · rw [hEvT]; unfold evalTerminator; rw [hTT]
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | unwindResume =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | unwindResume =>
            right; right; refine ⟨.unsupported, ?_, ?_⟩
            · rw [hEvS]; unfold evalTerminator; rw [hTS]
            · rw [hEvT]; unfold evalTerminator; rw [hTT]
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | assert _ _ _ _ _ =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | assert _ _ _ _ _ =>
            right; right; refine ⟨.unsupported, ?_, ?_⟩
            · rw [hEvS]; unfold evalTerminator; rw [hTS]
            · rw [hEvT]; unfold evalTerminator; rw [hTT]
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | call _ _ _ _ _ =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | call _ _ _ _ _ =>
            right; right; refine ⟨.unsupported, ?_, ?_⟩
            · rw [hEvS]; unfold evalTerminator; rw [hTS]
            · rw [hEvT]; unfold evalTerminator; rw [hTT]
          | _ => rw [hTT] at hTermRem; cases hTermRem
        | unsupported =>
          rw [hTS] at hTermRem
          cases hTT : bbTgt.terminator with
          | unsupported =>
            right; right; refine ⟨.unsupported, ?_, ?_⟩
            · rw [hEvS]; unfold evalTerminator; rw [hTS]
            · rw [hEvT]; unfold evalTerminator; rw [hTT]
          | _ => rw [hTT] at hTermRem; cases hTermRem

private theorem deadCompaction_cert_query_iff {remapList : List BlockRemap}
    {pSrc pTgt : Program} (q : Query)
    (hRel : isDeadBlockCompactionProgram remapList pSrc pTgt = true)
    (hCert : checkDeadBlockStorageSafeProgram pSrc pTgt = true) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := deadCompaction_cert_initState_eq q hRel hCert
  apply bisim_lift_disj (R := StateDeadCompactionBisim remapList pSrc pTgt)
  · intro k; rw [hInitEq]
  · intro s₀ t₀ hIS hIT
    have hISCopy := hIS
    rw [hInitEq] at hIS
    have hEqST : s₀ = t₀ := by rw [hIS] at hIT; injection hIT
    subst hEqST
    let ⟨_, _, bSrc, hBS, hNE, _, _, _, _, hS0⟩ := initState_ok_elim hISCopy
    unfold isDeadBlockCompactionProgram at hRel
    let ⟨h12, hZip⟩ := bool_and_true hRel
    let ⟨_, hRemLenB⟩ := bool_and_true h12
    let ⟨_, hSomeZip, _⟩ := listRel_zip_left_rel (nat_beq_eq hRemLenB) hZip
    let ⟨remap, bTgt, hRM, hBT0, hBody⟩ := hSomeZip pSrc.entryDefId bSrc hBS
    let ⟨_, _, _, _, hEntry0, _⟩ := deadCompactionBody_parts hBody
    subst hS0
    exact ⟨rfl, _, _, bSrc, bTgt, remap, rfl, rfl, rfl, rfl, rfl,
      hBS, hBT0, hRM, hBody, Or.inl ⟨list_pos_of_isEmpty_false hNE, hEntry0 hNE⟩⟩
  · intro s t hSt
    exact deadCompaction_cert_step hSt

private theorem vc_transport_deadBlockCompaction_certified_iff_priv
    (pSrc pTgt : Program) (remapList : List BlockRemap)
    (hRel : isDeadBlockCompactionProgram remapList pSrc pTgt = true)
    (hCert : checkDeadBlockStorageSafeProgram pSrc pTgt = true) :
    PrivFullSemanticEquiv pSrc pTgt := by
  have hRelCopy := hRel
  unfold isDeadBlockCompactionProgram at hRelCopy
  let ⟨h12, hZip⟩ := bool_and_true hRelCopy
  let ⟨hHdr, hRemLenB⟩ := bool_and_true h12
  let ⟨_, hSomeZip, _⟩ := listRel_zip_left_rel (nat_beq_eq hRemLenB) hZip
  refine fullSemanticEquiv_of_query_iff hHdr ?_
    (fun q => deadCompaction_cert_query_iff q hRel hCert)
    (fun defId args =>
      (deadCompaction_cert_query_iff { args := args }
        (deadCompaction_entryProg defId hRel) hCert).1)
  intro defId bSrc bTgt hBS hBT
  let ⟨remap, bTgt', _, hBT', hBody⟩ := hSomeZip defId bSrc hBS
  rw [hBT] at hBT'; injection hBT' with hEq; subst hEq
  let ⟨bTgt'', hBT'', hCertB⟩ := listRel_getElem?_left hCert hBS
  rw [hBT] at hBT''; injection hBT'' with hEq2; subst hEq2
  let ⟨hBHdr, hEmptyEq, hStEq, _⟩ := deadCompaction_cert_body_eq hBody hCertB
  exact ⟨hBHdr, hEmptyEq, hStEq⟩

/-! #### Theorem 6: 5-Stage `SimplifyCfg` `CrateTheorem` & `UnitTheorem` -/

private theorem map_id_eq_of_bodyRel {r : Body → Body → Bool} {bs1 bs2 : List Body}
    (hRel : listRel r bs1 bs2 = true)
    (hHdr : ∀ b1 b2, r b1 b2 = true → bodyHeaderEq b1 b2 = true) :
    bs1.map (fun b => b.identity) = bs2.map (fun b => b.identity) :=
  list_map_eq_of_rel hRel (fun b1 b2 hb => (bodyHeaderEq_elim (hHdr b1 b2 hb)).2.2.2)

private theorem map_id_eq_of_zipRel {α : Type} {rel : α → Body → Body → Bool}
    {auxs : List α} {bs1 bs2 : List Body}
    (hLen : auxs.length = bs1.length)
    (hRel : listRel (fun pr b2 => rel pr.1 pr.2 b2) (List.zip auxs bs1) bs2 = true)
    (hHdr : ∀ a b1 b2, rel a b1 b2 = true → bodyHeaderEq b1 b2 = true) :
    bs1.map (fun b => b.identity) = bs2.map (fun b => b.identity) := by
  induction auxs generalizing bs1 bs2 with
  | nil =>
    cases bs1 with
    | nil =>
      dsimp [List.zip, List.zipWith] at hRel
      cases bs2 with
      | nil => rfl
      | cons _ _ => cases hRel
    | cons _ _ => cases hLen
  | cons a auxRest ih =>
    cases bs1 with
    | nil => cases hLen
    | cons b1 bs1Rest =>
      dsimp [List.zip, List.zipWith] at hRel
      cases bs2 with
      | nil => cases hRel
      | cons b2 bs2Rest =>
        let ⟨hHead, hTail⟩ := bool_and_true hRel
        dsimp [List.map]
        rw [(bodyHeaderEq_elim (hHdr a b1 b2 hHead)).2.2.2,
            ih (Nat.succ.inj hLen) hTail]

private theorem simplifyCfg_pipeline_crate_and_unit_iff_priv
    (p₀ p₁ p₂ p₃ p₄ p₅ : Program)
    (uCert : ProgramAbsCert)
    (ranksList : List (List Nat))
    (remapList : List BlockRemap)
    (hConst : isConstBranchFoldProgram p₀ p₁ = true)
    (hUnif : isUniformBranchCollapseProgram p₁ p₂ = true)
    (hUnifCert : checkUniformBranchProgram p₁ p₂ uCert = true)
    (hGoto : isAcyclicGotoThreadProgram ranksList p₂ p₃ = true)
    (hNop : isStripNopsProgram p₃ p₄ = true)
    (hDead : isDeadBlockCompactionProgram remapList p₄ p₅ = true)
    (hDeadCert : checkDeadBlockStorageSafeProgram p₄ p₅ = true) :
    PrivFullSemanticEquiv p₀ p₅ ∧
    (∀ (safety : String → List Val → Prop) (prop : Program → Prop),
      (prop p₅ ↔ prop p₀) →
      (CrateTheorem ⟨p₅, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨p₀, ⟨safety, prop⟩⟩) ∧
      (UnitTheorem ⟨p₅, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨p₀, ⟨safety, prop⟩⟩)) := by
  have hEq01 := constBranchFold_bidirectional_iff_priv p₀ p₁ hConst
  have hEq12 := vc_transport_uniformBranchCollapse_certified_iff_priv p₁ p₂ uCert hUnif hUnifCert
  have hEq23 := acyclicGotoThread_bidirectional_iff_priv p₂ p₃ ranksList hGoto
  have hEq34 := stripNops_bidirectional_iff_priv p₃ p₄ hNop
  have hEq45 := vc_transport_deadBlockCompaction_certified_iff_priv p₄ p₅ remapList hDead hDeadCert
  let ⟨hHdr01, hB01⟩ := bool_and_true hConst
  let ⟨hHdr12, hB12⟩ := bool_and_true hUnif
  let ⟨h12G, hBG⟩ := bool_and_true hGoto
  let ⟨hHdr23, hRkLen⟩ := bool_and_true h12G
  let ⟨hHdr34, hB34⟩ := bool_and_true hNop
  let ⟨h12D, hBD⟩ := bool_and_true hDead
  let ⟨hHdr45, hRmLen⟩ := bool_and_true h12D
  have hIds01 : p₀.bodies.map (fun b => b.identity) = p₁.bodies.map (fun b => b.identity) :=
    map_id_eq_of_bodyRel hB01 (fun _ _ hb => (bool_and_true hb).1)
  have hIds12 : p₁.bodies.map (fun b => b.identity) = p₂.bodies.map (fun b => b.identity) :=
    map_id_eq_of_bodyRel hB12 (fun _ _ hb => (bool_and_true hb).1)
  have hIds23 : p₂.bodies.map (fun b => b.identity) = p₃.bodies.map (fun b => b.identity) :=
    map_id_eq_of_zipRel (nat_beq_eq hRkLen) hBG
      (fun _ _ _ hb => (bool_and_true (bool_and_true hb).1).1)
  have hIds34 : p₃.bodies.map (fun b => b.identity) = p₄.bodies.map (fun b => b.identity) :=
    map_id_eq_of_bodyRel hB34 (fun _ _ hb => (bool_and_true hb).1)
  have hIds45 : p₄.bodies.map (fun b => b.identity) = p₅.bodies.map (fun b => b.identity) :=
    map_id_eq_of_zipRel (nat_beq_eq hRmLen) hBD
      (fun _ _ _ hb => (deadCompactionBody_parts hb).1)
  have hIds05 : p₀.bodies.map (fun b => b.identity) = p₅.bodies.map (fun b => b.identity) := by
    rw [hIds01, hIds12, hIds23, hIds34, hIds45]
  have hLen01 : p₀.bodies.length = p₁.bodies.length := listRel_length hB01
  have hLen12 : p₁.bodies.length = p₂.bodies.length := listRel_length hB12
  have hLen23 : p₂.bodies.length = p₃.bodies.length :=
    (listRel_zip_left_rel (nat_beq_eq hRkLen) hBG).1
  have hLen34 : p₃.bodies.length = p₄.bodies.length := listRel_length hB34
  have hEq02 := fullSemanticEquiv_trans hLen01 hEq01 hEq12
  have hEq03 := fullSemanticEquiv_trans (by rw [hLen01, hLen12]) hEq02 hEq23
  have hEq04 := fullSemanticEquiv_trans (by rw [hLen01, hLen12, hLen23]) hEq03 hEq34
  have hEq05 := fullSemanticEquiv_trans (by rw [hLen01, hLen12, hLen23, hLen34]) hEq04 hEq45
  let ⟨hPw01, hV01, hE01, hS01⟩ := programHeaderEq_elim hHdr01
  let ⟨hPw12, hV12, hE12, hS12⟩ := programHeaderEq_elim hHdr12
  let ⟨hPw23, hV23, hE23, hS23⟩ := programHeaderEq_elim hHdr23
  let ⟨hPw34, hV34, hE34, hS34⟩ := programHeaderEq_elim hHdr34
  let ⟨hPw45, hV45, hE45, hS45⟩ := programHeaderEq_elim hHdr45
  refine ⟨hEq05, ?_⟩
  intro safety prop hProp
  exact programVerified_iff_of_equiv hEq05
    (by rw [hPw01, hPw12, hPw23, hPw34, hPw45])
    (by rw [hV01, hV12, hV23, hV34, hV45])
    (by rw [hE01, hE12, hE23, hE34, hE45])
    (by rw [hS01, hS12, hS23, hS34, hS45])
    hIds05 safety prop hProp

/-! ## Part III: Core Target Theorems Directly Over `Trusted.MirSemantics` -/

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

/-- **Theorem 1 (`StripNops` Unconditional Bidirectional Stuttering Equivalence):**
Stripping any subset or all `StatementKind.nop` statements (`isStripNopsProgram`)
preserves `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, infinite
`Diverges`, `SatisfiesPost`, and `BodyVerified` in both directions (`↔`). -/
theorem stripNops_bidirectional_iff
    (pSrc pTgt : Program)
    (hRel : isStripNopsProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact stripNops_bidirectional_iff_priv pSrc pTgt hRel

/-- **Theorem 2 (Validated Constant `SwitchInt` Branch Folding Bidirectional Equivalence):**
Folding any subset of `SwitchInt(.constant c, targets)` terminators with
`resolveConstSwitchTarget c targets = some target` to `Goto(target)` preserves
full bidirectional equivalence (`↔`) across all $M_{\text{anneal}}$ judgments. -/
theorem constBranchFold_bidirectional_iff
    (pSrc pTgt : Program)
    (hRel : isConstBranchFoldProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact constBranchFold_bidirectional_iff_priv pSrc pTgt hRel

/-- **Theorem 3a (Unconditional Forward Codegen Refinement for Uniform-Target
`SwitchInt -> Goto` Collapse, `SimplifyCfg::simplify_branch`):**
Collapsing any uniform-target `SwitchInt(discr, targets)` to `Goto(target)`
unconditionally refines well-formed executions (`pSrc → pTgt`). -/
theorem codegen_uniformBranchCollapse_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isUniformBranchCollapseProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  exact codegen_uniformBranchCollapse_refines_unconditional_priv pSrc pTgt hRel

/-- **Theorem 3b (Certified Bidirectional VC Transport for Uniform-Target
`SwitchInt -> Goto` Collapse):**
Pairing `isUniformBranchCollapseProgram` with `checkUniformBranchProgram`
restores full bidirectional equivalence (`↔`) across all queries. -/
theorem vc_transport_uniformBranchCollapse_certified_iff
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isUniformBranchCollapseProgram pSrc pTgt = true)
    (hCert : checkUniformBranchProgram pSrc pTgt cert = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact vc_transport_uniformBranchCollapse_certified_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 4 (Ranked Acyclic `Goto`-Chain Threading Bidirectional Stuttering
Equivalence, `SimplifyCfg::collapse_goto_chain`):**
Threading predecessor terminators along strictly rank-decreasing empty
non-cleanup `Goto` blocks preserves full bidirectional equivalence (`↔`),
including infinite execution traces (`Diverges pTgt q ↔ Diverges pSrc q`). -/
theorem acyclicGotoThread_bidirectional_iff
    (pSrc pTgt : Program) (ranksList : List (List Nat))
    (hRel : isAcyclicGotoThreadProgram ranksList pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact acyclicGotoThread_bidirectional_iff_priv pSrc pTgt ranksList hRel

/-- **Theorem 5a (Unconditional Forward Codegen Refinement for Dead-Block
Elimination & Bijective Reachable-Block Compaction, `SimplifyCfg::remove_dead_blocks`):**
Deleting unreachable basic blocks and bijectively compacting/permuting the
remaining blocks unconditionally refines well-formed executions (`pSrc → pTgt`),
even when deleted dead blocks carried storage annotations! -/
theorem codegen_deadBlockCompaction_refines_unconditional
    (pSrc pTgt : Program) (remapList : List BlockRemap)
    (hRel : isDeadBlockCompactionProgram remapList pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  exact codegen_deadBlockCompaction_refines_unconditional_priv pSrc pTgt remapList hRel

/-- **Theorem 5b (Certified Bidirectional VC Transport for Dead-Block
Elimination & Bijective Reachable-Block Compaction):**
Pairing `isDeadBlockCompactionProgram` with `checkDeadBlockStorageSafeProgram`
restores full bidirectional equivalence (`↔`) across all queries. -/
theorem vc_transport_deadBlockCompaction_certified_iff
    (pSrc pTgt : Program) (remapList : List BlockRemap)
    (hRel : isDeadBlockCompactionProgram remapList pSrc pTgt = true)
    (hCert : checkDeadBlockStorageSafeProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact vc_transport_deadBlockCompaction_certified_iff_priv pSrc pTgt remapList hRel hCert

/-- **Theorem 6 (End-to-End 5-Stage `SimplifyCfg` Pipeline Bidirectional
`CrateTheorem` & `UnitTheorem` Transport):**
Composing `ConstBranchFold`, certified `UniformBranchCollapse`, ranked
`AcyclicGotoThread`, `StripNops`, and certified `DeadBlockCompaction` preserves
full `FullSemanticEquiv` and transports `CrateTheorem` and `UnitTheorem`
bidirectionally (`↔`) whenever `specs.property` respects the pipeline pair. -/
theorem simplifyCfg_pipeline_crate_and_unit_iff
    (p₀ p₁ p₂ p₃ p₄ p₅ : Program)
    (uCert : ProgramAbsCert)
    (ranksList : List (List Nat))
    (remapList : List BlockRemap)
    (hConst : isConstBranchFoldProgram p₀ p₁ = true)
    (hUnif : isUniformBranchCollapseProgram p₁ p₂ = true)
    (hUnifCert : checkUniformBranchProgram p₁ p₂ uCert = true)
    (hGoto : isAcyclicGotoThreadProgram ranksList p₂ p₃ = true)
    (hNop : isStripNopsProgram p₃ p₄ = true)
    (hDead : isDeadBlockCompactionProgram remapList p₄ p₅ = true)
    (hDeadCert : checkDeadBlockStorageSafeProgram p₄ p₅ = true) :
    FullSemanticEquiv p₀ p₅ ∧
    (∀ (safety : String → List Val → Prop) (prop : Program → Prop),
      (prop p₅ ↔ prop p₀) →
      (CrateTheorem ⟨p₅, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨p₀, ⟨safety, prop⟩⟩) ∧
      (UnitTheorem ⟨p₅, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨p₀, ⟨safety, prop⟩⟩)) := by
  exact simplifyCfg_pipeline_crate_and_unit_iff_priv p₀ p₁ p₂ p₃ p₄ p₅ uCert ranksList remapList hConst hUnif hUnifCert hGoto hNop hDead hDeadCert

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

/-! ### Sharpness Counterexample 1: Dead-Block Elimination Flips `hasStorageAnnotation` (`always_storage_live_locals`) -/

/-- `pSrc` has reachable `bb0` writing `_1 = 42u32; _0 = copy _1; return`
without `StorageLive(_1)`, while **unreachable** `bb1` holds `.storageLive 1`.
Deleting unreachable `bb1` produces `pTgt`! -/
noncomputable def progDeadBlockStorageFlipSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::dead_block_storage_flip"
    basicBlocks := [
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩)),
          .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
        ]
        terminator := .return_
      },
      {
        statements := [.storageLive 1]
        terminator := .return_
      }
    ]
  }]

noncomputable def progDeadBlockStorageFlipTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::dead_block_storage_flip"
    basicBlocks := [
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩)),
          .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- **Sharpness Theorem CE1:** Deleting unreachable `bb1` satisfies
`isDeadBlockCompactionProgram [[some 0, none]]`, makes `pTgt` `WellFormed`
(returning `42u32`), yet `pSrc` faults with `FaultKind.undefined` (`DeadLocal`
on `_1`), and `checkDeadBlockStorageSafeProgram` rejects the uncertified pass! -/
theorem ce_dead_block_elim_flips_always_storage_live_unsound :
    isDeadBlockCompactionProgram [[some 0, none]]
      progDeadBlockStorageFlipSrc progDeadBlockStorageFlipTgt = true ∧
    checkDeadBlockStorageSafeProgram
      progDeadBlockStorageFlipSrc progDeadBlockStorageFlipTgt = false ∧
    PositiveCanaryClaim progDeadBlockStorageFlipTgt queryEmpty (u32Val 42) ∧
    NegativeCanaryClaim progDeadBlockStorageFlipSrc queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 4) rfl
  · exact negativeCanary_of_execFaults (fuel := 3) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 2: Dead-Block Elimination Hides Out-of-Bounds `StorageLive` -/

noncomputable def progDeadBlockOobStorageSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    identity := "ce::dead_block_oob_storage"
    basicBlocks := [
      { statements := [], terminator := .return_ },
      { statements := [.storageLive 99], terminator := .return_ }
    ]
  }]

noncomputable def progDeadBlockOobStorageTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    identity := "ce::dead_block_oob_storage"
    basicBlocks := [
      { statements := [], terminator := .return_ }
    ]
  }]

theorem ce_dead_block_elim_hides_oob_storage_marker_unsound :
    isDeadBlockCompactionProgram [[some 0, none]]
      progDeadBlockOobStorageSrc progDeadBlockOobStorageTgt = true ∧
    checkDeadBlockStorageSafeProgram
      progDeadBlockOobStorageSrc progDeadBlockOobStorageTgt = false ∧
    PositiveCanaryClaim progDeadBlockOobStorageTgt queryEmpty .unit ∧
    NegativeCanaryClaim progDeadBlockOobStorageSrc queryEmpty
      .unsupported .undefined := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 2) rfl
  · exact negativeCanary_of_execFaults (fuel := 1) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 3: Uniform `SwitchInt` Collapse Erases Uninitialized Discriminant UB (`simplify.rs:299`) -/

noncomputable def progUniformSwitchUninitSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit, u32Ty]
    identity := "ce::uniform_switch_uninit"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 1
        }
      },
      { statements := [], terminator := .return_ }
    ]
  }]

noncomputable def progUniformSwitchUninitTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit, u32Ty]
    identity := "ce::uniform_switch_uninit"
    basicBlocks := [
      { statements := [], terminator := .goto 1 },
      { statements := [], terminator := .return_ }
    ]
  }]

theorem ce_uniform_switch_uninit_discr_unsound :
    isUniformBranchCollapseProgram
      progUniformSwitchUninitSrc progUniformSwitchUninitTgt = true ∧
    PositiveCanaryClaim progUniformSwitchUninitTgt queryEmpty .unit ∧
    NegativeCanaryClaim progUniformSwitchUninitSrc queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 3) rfl
  · exact negativeCanary_of_execFaults (fuel := 2) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 4: Uniform `SwitchInt(move _1)` Collapse Erases `deinitMovedPlace = true` Use-After-Move UB -/

noncomputable def progUniformSwitchMoveDeinitSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce::uniform_switch_move"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.move ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 1
        }
      },
      {
        statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        terminator := .return_
      }
    ]
  }]

noncomputable def progUniformSwitchMoveDeinitTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce::uniform_switch_move"
    basicBlocks := [
      { statements := [], terminator := .goto 1 },
      {
        statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        terminator := .return_
      }
    ]
  }]

theorem ce_uniform_switch_move_deinit_unsound :
    isUniformBranchCollapseProgram
      progUniformSwitchMoveDeinitSrc progUniformSwitchMoveDeinitTgt = true ∧
    PositiveCanaryClaim progUniformSwitchMoveDeinitTgt
      { args := [u32Val 9] } (u32Val 9) ∧
    NegativeCanaryClaim progUniformSwitchMoveDeinitSrc
      { args := [u32Val 9] } .undefined .unsupported := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 4) rfl
  · exact negativeCanary_of_execFaults (fuel := 4) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 5: Uniform `SwitchInt` Collapse Erases Overflowing `caseBits` `.unsupported` Fault -/

noncomputable def progUniformSwitchOverflowCaseSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    identity := "ce::uniform_switch_overflow_case"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 0)⟩) {
          branches := [(BitVec.ofNat 128 256, 1)]
          otherwise := 1
        }
      },
      { statements := [], terminator := .return_ }
    ]
  }]

noncomputable def progUniformSwitchOverflowCaseTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    identity := "ce::uniform_switch_overflow_case"
    basicBlocks := [
      { statements := [], terminator := .goto 1 },
      { statements := [], terminator := .return_ }
    ]
  }]

theorem ce_uniform_switch_overflow_case_unsound :
    isUniformBranchCollapseProgram
      progUniformSwitchOverflowCaseSrc progUniformSwitchOverflowCaseTgt = true ∧
    PositiveCanaryClaim progUniformSwitchOverflowCaseTgt queryEmpty .unit ∧
    NegativeCanaryClaim progUniformSwitchOverflowCaseSrc queryEmpty
      .unsupported .undefined := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 3) rfl
  · exact negativeCanary_of_execFaults (fuel := 2) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 6: Invalid `bool` Constant (`2`) Rejected by `resolveConstSwitchTarget` -/

noncomputable def progInvalidBoolConstSwitch : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    identity := "ce::invalid_bool_const_switch"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.constant ⟨.bool, .scalar (BitVec.ofNat 128 2)⟩) {
          branches := []
          otherwise := 1
        }
      },
      { statements := [], terminator := .return_ }
    ]
  }]

theorem ce_const_switch_invalid_bool_unsound :
    isConstBranchFoldProgram
      progInvalidBoolConstSwitch progUniformSwitchOverflowCaseTgt = false ∧
    NegativeCanaryClaim progInvalidBoolConstSwitch queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, ?_⟩
  exact negativeCanary_of_execFaults (fuel := 2) (by intro h; cases h) rfl

/-! ### Non-Vacuity Witness: End-to-End 5-Stage `SimplifyCfg` Pipeline Compaction (`6` Blocks → `2` Blocks) -/

/-- `pPipe₀` (6 blocks):
- `bb0`: `.nop`, `_2 = copy _1 + const 1u32`, `.nop`, `SwitchInt(const true) [1 -> bb2, otherwise -> bb1]`
- `bb1` (dead cold branch after const-fold!): `TerminatorKind.unreachable`
- `bb2`: `SwitchInt(copy _2) [0 -> bb3, otherwise -> bb3]` (uniform branch!)
- `bb3`: empty forwarding `Goto(bb4)`
- `bb4`: empty forwarding `Goto(bb5)`
- `bb5`: `.nop`, `_0 = copy _2`, `Return`
Compacts via `pPipe₀ -> pPipe₁ -> pPipe₂ -> pPipe₃ -> pPipe₄ -> pPipe₅` down to
2 clean blocks (`bb0 -> bb1`)! -/
noncomputable def pPipe₀ : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "witness::pipeline"
    basicBlocks := [
      {
        statements := [
          .nop,
          .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
          .nop
        ]
        terminator := .switchInt (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩) {
          branches := [(BitVec.ofNat 128 1, 2)]
          otherwise := 1
        }
      },
      { statements := [], terminator := .unreachable },
      {
        statements := []
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 3)]
          otherwise := 3
        }
      },
      { statements := [], terminator := .goto 4 },
      { statements := [], terminator := .goto 5 },
      {
        statements := [.nop, .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
        terminator := .return_
      }
    ]
  }]

noncomputable def pPipe₁ : Program :=
  { pPipe₀ with bodies := [{
      argumentCount := 1
      locals := [u32Ty, u32Ty, u32Ty]
      identity := "witness::pipeline"
      basicBlocks := [
        {
          statements := [
            .nop,
            .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
              (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
            .nop
          ]
          terminator := .goto 2
        },
        { statements := [], terminator := .unreachable },
        {
          statements := []
          terminator := .switchInt (.copy ⟨2, []⟩) {
            branches := [(BitVec.ofNat 128 0, 3)]
            otherwise := 3
          }
        },
        { statements := [], terminator := .goto 4 },
        { statements := [], terminator := .goto 5 },
        {
          statements := [.nop, .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
          terminator := .return_
        }
      ]
    }] }

noncomputable def pPipe₂ : Program :=
  { pPipe₀ with bodies := [{
      argumentCount := 1
      locals := [u32Ty, u32Ty, u32Ty]
      identity := "witness::pipeline"
      basicBlocks := [
        {
          statements := [
            .nop,
            .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
              (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
            .nop
          ]
          terminator := .goto 2
        },
        { statements := [], terminator := .unreachable },
        { statements := [], terminator := .goto 3 },
        { statements := [], terminator := .goto 4 },
        { statements := [], terminator := .goto 5 },
        {
          statements := [.nop, .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
          terminator := .return_
        }
      ]
    }] }

noncomputable def pPipe₃ : Program :=
  { pPipe₀ with bodies := [{
      argumentCount := 1
      locals := [u32Ty, u32Ty, u32Ty]
      identity := "witness::pipeline"
      basicBlocks := [
        {
          statements := [
            .nop,
            .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
              (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
            .nop
          ]
          terminator := .goto 5
        },
        { statements := [], terminator := .unreachable },
        { statements := [], terminator := .goto 5 },
        { statements := [], terminator := .goto 5 },
        { statements := [], terminator := .goto 5 },
        {
          statements := [.nop, .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
          terminator := .return_
        }
      ]
    }] }

noncomputable def pPipe₄ : Program :=
  { pPipe₀ with bodies := [{
      argumentCount := 1
      locals := [u32Ty, u32Ty, u32Ty]
      identity := "witness::pipeline"
      basicBlocks := [
        {
          statements := [
            .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
              (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
          ]
          terminator := .goto 5
        },
        { statements := [], terminator := .unreachable },
        { statements := [], terminator := .goto 5 },
        { statements := [], terminator := .goto 5 },
        { statements := [], terminator := .goto 5 },
        {
          statements := [.assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
          terminator := .return_
        }
      ]
    }] }

noncomputable def pPipe₅ : Program :=
  { pPipe₀ with bodies := [{
      argumentCount := 1
      locals := [u32Ty, u32Ty, u32Ty]
      identity := "witness::pipeline"
      basicBlocks := [
        {
          statements := [
            .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
              (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
          ]
          terminator := .goto 1
        },
        {
          statements := [.assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
          terminator := .return_
        }
      ]
    }] }

noncomputable def pipeUniformCert : ProgramAbsCert :=
  [[
    some [.liveUninit, .liveInit, .liveUninit],
    none,
    some [.liveUninit, .liveInit, .liveInit],
    some [.liveUninit, .liveInit, .liveInit],
    some [.liveUninit, .liveInit, .liveInit],
    some [.liveUninit, .liveInit, .liveInit]
  ]]

noncomputable def pipeRanks : List (List Nat) :=
  [[5, 0, 4, 3, 2, 1]]

noncomputable def pipeRemap : List BlockRemap :=
  [[some 0, none, none, none, none, some 1]]

theorem witness_full_simplifyCfg_pipeline_nonvacuous :
    isConstBranchFoldProgram pPipe₀ pPipe₁ = true ∧
    isUniformBranchCollapseProgram pPipe₁ pPipe₂ = true ∧
    checkUniformBranchProgram pPipe₁ pPipe₂ pipeUniformCert = true ∧
    isAcyclicGotoThreadProgram pipeRanks pPipe₂ pPipe₃ = true ∧
    isStripNopsProgram pPipe₃ pPipe₄ = true ∧
    isDeadBlockCompactionProgram pipeRemap pPipe₄ pPipe₅ = true ∧
    checkDeadBlockStorageSafeProgram pPipe₄ pPipe₅ = true ∧
    PositiveCanaryClaim pPipe₀ { args := [u32Val 41] } (u32Val 42) ∧
    PositiveCanaryClaim pPipe₅ { args := [u32Val 41] } (u32Val 42) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 12) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

end VrustcFormal.F1_5
