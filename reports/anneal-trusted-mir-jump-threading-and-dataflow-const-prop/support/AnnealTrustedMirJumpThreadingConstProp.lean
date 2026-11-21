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

namespace VrustcFormal.F1_8

open Trusted.MirAst Trusted.MirSemantics

/-!
# Direct `Trusted.MirSemantics` Bridge: `DataflowConstProp` / `SingleUseConsts`, `MatchBranchSimplification`, and `JumpThreading` (`VrustcFormal.F1_8`)

This module formalizes the mid-pipeline constant-propagation, boolean
match-branch simplification, and block-duplicating jump-threading passes
scheduled in `compiler/rustc_mir_transform/src/lib.rs:762-766`
(`match_branches.rs`, `dataflow_const_prop.rs`, `single_use_consts.rs`, and
`jump_threading.rs`, grounded in `rust-lang/rust` commit
`412be32a6a189d9a28922beee178bc0abee9d492`, `Trusted.MirSemantics` baseline
`8144389c895da997dbdecaa635e41d6a50be6ffd`, and live `E3-14` empirical census
`e3_14_real_jump_threading_and_dataflow_const_prop.json`) directly over Anneal's
unmodified TCB syntax (`Trusted.MirAst`) and small-step operational semantics
(`Trusted.MirSemantics`).

All public theorem statements reference strictly `Init.*`, `Trusted.MirAst.*`,
`Trusted.MirSemantics.*`, and pure definitions in `VrustcFormal.F1_8` (zero
surrogate MIR AST, zero `Anneal.*` references).

## Ground-Truth Semantic Findings (`E3-14`) Mechanized Directly on $M_{\text{anneal}}$

1. **Certified `ConstPropCopy` vs. `ConstPropMove` Asymmetry
   (`dataflow_const_prop.rs:32-33, 931-1013` with `BLOCK_LIMIT = 100` and
   `PLACE_LIMIT = 100` at `mir_opt_level >= 3`, and `single_use_consts.rs:25-206`
   with `-1,027` assigns / `+243` const tokens across `zerocopy`):**
   - Over a 5-point flow-sensitive constant/liveness lattice (`ConstAbsSlot`:
     `.bottom ⊑ .knownConst ty lit ⊑ .liveUnknown ⊑ .liveUninit ⊑ .dead`) with
     `SwitchInt` equality-branch refinement (`discr == caseBits`), rewriting
     `Operand.copy ⟨x, []⟩ ↦ Operand.constant c` (`ConstPropCopy`) satisfies
     **`FullSemanticEquiv pSrc pTgt` (`↔`)** (`Theorem 1a`).
   - Rewriting `Operand.move ⟨x, []⟩ ↦ Operand.constant c` (`ConstPropMove`)
     under `deinitMovedPlace = true` (`Trusted.MirSemantics.evalOperandToSlot`)
     exhibits a sharp directional split matching `E3-14`'s live specimen
     `custom_read_after_move_scalar`:
     * Under `KnownConst` alone (without post-move deadness), `ConstPropMove`
       satisfies **`ForwardCodegenRefines pSrc pTgt` (`pSrc → pTgt`)**
       (`Theorem 1b`), whereas reverse VC transport fails because `pSrc`
       deinitializes `x` upon `Move(x)` and faults with `FaultKind.undefined` on
       a subsequent read while `pTgt` skips deinitialization and returns `14_u32`
       (`ce_constprop_move_without_deadness_reverse_unsound`).
     * Pairing `KnownConst` with co-inductive all-paths post-move deadness of
       `x` (`checkConstPropMoveDeadProgram`) restores
       **`FullSemanticEquiv pSrc pTgt` (`↔`)** (`Theorem 1c`).

2. **Certified `MatchBranchSimplification` (`match_branches.rs:116-148, 359-463`,
   `zerocopy` census `-66` BBs / `-19` `SwitchInt`s):**
   - Collapsing a diamond `SwitchInt (.copy ⟨discr, []⟩) [caseBits ↦ bbCase,
     otherwise ↦ bbOther]` where `bbCase` assigns `⟨dst, []⟩ = const bCase;
     Goto bbJoin` and `bbOther` assigns `⟨dst, []⟩ = const (!bCase);
     Goto bbJoin` into in-place `⟨dst, []⟩ = BinaryOp (.eq / .ne)
     (.copy ⟨discr, []⟩) (.constant caseConst); Goto bbJoin` (retaining existing
     blocks so `hasStorageAnnotation` and `storageAnnotationsInBounds` are
     unchanged) satisfies **`FullSemanticEquiv pSrc pTgt` (`↔`)** (`Theorem 2`)
     across all 6 integer widths (signed and unsigned) and `bool` whenever
     `caseConst`, `cCase`, and `cOther` pass `checkMatchBranchSimplifyProgram`.
   - Skipping `evalConstLit` validation on arm boolean literals (e.g. invalid
     `bool` bit pattern `2` in `bbCase`) erases `FaultKind.undefined`
     (`ce_match_branch_invalid_bool_or_uninit_discr_unsound`).

3. **Certified Block-Duplicating `JumpThreading` (`jump_threading.rs:73-148,
   985-1100`, `zerocopy` census `+296` duplicated BBs / `+288` `Goto`s / `+270`
   assigns):**
   - Appending specialized duplicate block(s)
     `bbDup = { statements := bbJoin.statements, terminator := .goto resolvedTarget }`
     at `bSrc.basicBlocks.length + d` and redirecting certified predecessor
     `Goto bbJoin` edge(s) to `Goto bbDup` (where `cert` proves `discr` holds a
     known switch constant resolving to `resolvedTarget` **after** executing
     `bbJoin.statements` along that incoming edge, and `bbJoin`'s `SwitchInt`
     uses `Operand.copy ⟨discr, []⟩`) preserves `initState` identically, aligns
     execution in exact **1-to-1 step lockstep** (preserving `Diverges` with
     zero stuttering), and satisfies **`FullSemanticEquiv pSrc pTgt` (`↔`)**
     (`Theorem 3`).
   - Skipping `bbJoin.statements` drops prefix side effects
     (`ce_jumpthread_skipping_join_prefix_stmts_unsound`, modeling `E3-14`'s
     `custom_jt_preserves_join_prefix`), threading a `Move(discr)` `SwitchInt`
     without deadness erases use-after-move UB
     (`ce_jumpthread_move_discr_without_deadness_reverse_unsound`), and using
     `bbPred`'s stale value when `bbJoin.statements` mutates `discr` misroutes
     control flow (`ce_jumpthread_mutated_discr_in_join_prefix_unsound`).
-/

/-! ## Part I: Structural Equality & Decidable Pass Relations -/

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

/-- Shared program-header equality (`pointerWidthBits`, `mirProfileVersion`,
`entryDefId`, `scope`). -/
noncomputable def programHeaderEq (p₁ p₂ : Program) : Bool :=
  Nat.beq p₁.pointerWidthBits p₂.pointerWidthBits &&
    Nat.beq p₁.mirProfileVersion p₂.mirProfileVersion &&
    Nat.beq p₁.entryDefId p₂.entryDefId &&
    scopeEq p₁.scope p₂.scope

/-! ### Pass 1a (`ConstPropCopy`) & Pass 1b (`ConstPropMove`): `SingleUseConsts` + `DataflowConstProp` -/

/-- Whether `opTgt` either equals `opSrc` or rewrites an unprojected
`Operand.copy ⟨x, []⟩` to `Operand.constant c`. -/
noncomputable def isConstPropCopyOperand (opSrc opTgt : Operand) : Bool :=
  match opSrc, opTgt with
  | .copy p, .constant _ => p.projection.isEmpty
  | _, _ => operandEq opSrc opTgt

/-- Whether `opTgt` either equals `opSrc` or rewrites an unprojected
`Operand.move ⟨x, []⟩` to `Operand.constant c`. -/
noncomputable def isConstPropMoveOperand (opSrc opTgt : Operand) : Bool :=
  match opSrc, opTgt with
  | .move p, .constant _ => p.projection.isEmpty
  | _, _ => operandEq opSrc opTgt

/-- Lift an operand-rewrite predicate across evaluated `Rvalue` forms (`.use`,
`.unaryOp`, `.binaryOp`), preserving all other `Rvalue` variants via `rvalueEq`. -/
noncomputable def liftOperandRewriteRvalue
    (opRel : Operand → Operand → Bool) : Rvalue → Rvalue → Bool
  | .use o₁, .use o₂ => opRel o₁ o₂
  | .unaryOp uop₁ o₁, .unaryOp uop₂ o₂ => unOpEq uop₁ uop₂ && opRel o₁ o₂
  | .binaryOp bop₁ l₁ r₁, .binaryOp bop₂ l₂ r₂ =>
    binOpEq bop₁ bop₂ && opRel l₁ l₂ && opRel r₁ r₂
  | rv₁, rv₂ => rvalueEq rv₁ rv₂

/-- Lift an operand-rewrite predicate across `StatementKind`. -/
noncomputable def liftOperandRewriteStmt
    (opRel : Operand → Operand → Bool) : StatementKind → StatementKind → Bool
  | .assign d₁ rv₁, .assign d₂ rv₂ =>
    placeEq d₁ d₂ && liftOperandRewriteRvalue opRel rv₁ rv₂
  | s₁, s₂ => stmtEq s₁ s₂

/-- Lift an operand-rewrite predicate across `TerminatorKind` (allowing
`SwitchInt` discriminant constant propagation). -/
noncomputable def liftOperandRewriteTerm
    (opRel : Operand → Operand → Bool) : TerminatorKind → TerminatorKind → Bool
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ =>
    opRel d₁ d₂ && switchTargetsEq ts₁ ts₂
  | t₁, t₂ => terminatorEq t₁ t₂

noncomputable def isConstPropCopyBlock (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (liftOperandRewriteStmt isConstPropCopyOperand)
      b₁.statements b₂.statements &&
    liftOperandRewriteTerm isConstPropCopyOperand b₁.terminator b₂.terminator

noncomputable def isConstPropCopyBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel isConstPropCopyBlock b₁.basicBlocks b₂.basicBlocks

noncomputable def isConstPropCopyProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isConstPropCopyBody pSrc.bodies pTgt.bodies

noncomputable def isConstPropMoveBlock (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (liftOperandRewriteStmt isConstPropMoveOperand)
      b₁.statements b₂.statements &&
    liftOperandRewriteTerm isConstPropMoveOperand b₁.terminator b₂.terminator

noncomputable def isConstPropMoveBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel isConstPropMoveBlock b₁.basicBlocks b₂.basicBlocks

noncomputable def isConstPropMoveProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isConstPropMoveBody pSrc.bodies pTgt.bodies

/-! ### Pass 2 (`MatchBranchSimplify`): `match_branches.rs` Boolean `SwitchInt` Diamond Collapse -/

/-- True iff `op` is `.eq` or `.ne` (the two comparison operators emitted by
`SimplifyMatch::unify_by_eq_op` in `match_branches.rs:139`). -/
noncomputable def isEqOrNeBinOp : BinOp → Bool
  | .eq | .ne => true
  | _ => false

/-- Check whether `(bbSrc, bbTgt)` at `bbIdx` in `bSrc` is a syntactic
`MatchBranchSimplification` collapse:
- `bbSrc` is a non-cleanup block ending in
  `SwitchInt (.copy ⟨discr, []⟩) { branches := [(caseBits, bbCase)], otherwise := bbOther }`;
- `bbCase` and `bbOther` are distinct, in-bounds, non-cleanup blocks in `bSrc`
  (neither equal to `bbIdx`), where `bbCase` is
  `[⟨dst, []⟩ = Use(Constant(cCase))]; Goto(bbJoin)` and `bbOther` is
  `[⟨dst, []⟩ = Use(Constant(cOther))]; Goto(bbJoin)`; and
- `bbTgt` is non-cleanup, appends
  `⟨dst, []⟩ = BinaryOp(cmpOp, .copy ⟨discr, []⟩, .constant caseConst)` (`cmpOp ∈ {.eq, .ne}`)
  to `bbSrc.statements`, and terminates with `Goto(bbJoin)`. -/
noncomputable def isMatchBranchRewriteAt (bSrc : Body) (bbIdx : BasicBlockId)
    (bbSrc bbTgt : BasicBlock) : Bool :=
  !bbSrc.cleanup && !bbTgt.cleanup &&
    match bbSrc.terminator, bbTgt.terminator with
    | .switchInt (.copy dPlace) { branches := [(_, bbCase)], otherwise := bbOther },
        .goto bbJoin =>
      dPlace.projection.isEmpty &&
        !Nat.beq bbCase bbIdx &&
        !Nat.beq bbOther bbIdx &&
        !Nat.beq bbCase bbOther &&
        match Trusted.MirSemantics.getElem? bSrc.basicBlocks bbCase,
            Trusted.MirSemantics.getElem? bSrc.basicBlocks bbOther with
        | some blkCase, some blkOther =>
          !blkCase.cleanup && !blkOther.cleanup &&
            match blkCase.statements, blkCase.terminator,
                blkOther.statements, blkOther.terminator with
            | [.assign dst₁ (.use (.constant _))], .goto join₁,
                [.assign dst₂ (.use (.constant _))], .goto join₂ =>
              dst₁.projection.isEmpty &&
                placeEq dst₁ dst₂ &&
                Nat.beq join₁ bbJoin &&
                Nat.beq join₂ bbJoin &&
                Nat.beq bbTgt.statements.length (bbSrc.statements.length + 1) &&
                listRel stmtEq bbSrc.statements
                  (bbTgt.statements.take bbSrc.statements.length) &&
                match Trusted.MirSemantics.getElem?
                    bbTgt.statements bbSrc.statements.length with
                | some (.assign dstTgt
                    (.binaryOp cmpOp (.copy dPlaceTgt) (.constant _))) =>
                  placeEq dst₁ dstTgt &&
                    isEqOrNeBinOp cmpOp &&
                    placeEq dPlace dPlaceTgt
                | _ => false
            | _, _, _, _ => false
        | _, _ => false
    | _, _ => false

noncomputable def isMatchBranchBlocksLoop (bSrc : Body) :
    Nat → List BasicBlock → List BasicBlock → Bool
  | _, [], [] => true
  | idx, bbSrc :: restSrc, bbTgt :: restTgt =>
    (isMatchBranchRewriteAt bSrc idx bbSrc bbTgt || blockEq bbSrc bbTgt) &&
      isMatchBranchBlocksLoop bSrc (idx + 1) restSrc restTgt
  | _, _, _ => false

noncomputable def isMatchBranchSimplifyBody (bSrc bTgt : Body) : Bool :=
  bodyHeaderEq bSrc bTgt &&
    isMatchBranchBlocksLoop bSrc 0 bSrc.basicBlocks bTgt.basicBlocks

noncomputable def isMatchBranchSimplifyProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isMatchBranchSimplifyBody pSrc.bodies pTgt.bodies

/-! ### Pass 3 (`JumpThreading`): `jump_threading.rs` Specialized Join-Block Duplication -/

/-- Descriptor for one appended jump-threaded duplicate block `bbDup` at index
`bSrc.basicBlocks.length + d`, specializing `bSrc.basicBlocks[joinBlock]`'s
`SwitchInt` terminator to `Goto resolvedTarget`. -/
structure JumpThreadDupSpec where
  joinBlock : BasicBlockId
  resolvedTarget : BasicBlockId

/-- Check whether `target` is one of `targets`'s outgoing destinations
(`targets.otherwise` or any `(caseBits, brTarget)` in `targets.branches`). -/
noncomputable def isSwitchTargetMember (targets : SwitchTargets)
    (target : BasicBlockId) : Bool :=
  Nat.beq target targets.otherwise ||
    targets.branches.any (fun br => Nat.beq target br.2)

/-- Validate that every appended duplicate block `bTgt.basicBlocks[numSrc + d]`
matches `dupSpecs[d]`: `joinBlock < numSrc`, `resolvedTarget < numSrc`,
`bSrc.basicBlocks[joinBlock]` is a non-cleanup block ending in
`SwitchInt (.copy ⟨discr, []⟩) targets` with `resolvedTarget` among `targets`,
and `bbDup` is a non-cleanup copy of `bbJoin.statements` ending in
`Goto resolvedTarget`. -/
noncomputable def checkAppendedDupBlocks (bSrc : Body) :
    List JumpThreadDupSpec → List BasicBlock → Bool
  | [], [] => true
  | spec :: restSpecs, bbDup :: restDups =>
    let numSrc := bSrc.basicBlocks.length
    Nat.blt spec.joinBlock numSrc &&
      Nat.blt spec.resolvedTarget numSrc &&
      !bbDup.cleanup &&
      (match Trusted.MirSemantics.getElem? bSrc.basicBlocks spec.joinBlock,
          bbDup.terminator with
       | some bbJoin, .goto dupTgt =>
         !bbJoin.cleanup &&
           Nat.beq dupTgt spec.resolvedTarget &&
           listRel stmtEq bbJoin.statements bbDup.statements &&
           match bbJoin.terminator with
           | .switchInt (.copy dPlace) targets =>
             dPlace.projection.isEmpty &&
               isSwitchTargetMember targets spec.resolvedTarget
           | _ => false
       | _, _ => false) &&
      checkAppendedDupBlocks bSrc restSpecs restDups
  | _, _ => false

/-- Check whether `(bbSrc, bbTgt)` at index `< numSrc` is either unchanged
(`blockEq`) or redirects a non-cleanup `Goto joinBlock` edge to `Goto (numSrc + d)`
for a valid `dupSpecs[d]` with `dupSpecs[d].joinBlock == joinBlock`. -/
noncomputable def isJumpThreadOrigBlock (numSrc : Nat)
    (dupSpecs : List JumpThreadDupSpec) (bbSrc bbTgt : BasicBlock) : Bool :=
  blockEq bbSrc bbTgt ||
    (!bbSrc.cleanup && !bbTgt.cleanup &&
      listRel stmtEq bbSrc.statements bbTgt.statements &&
      match bbSrc.terminator, bbTgt.terminator with
      | .goto joinIdx, .goto tgtIdx =>
        !Nat.blt tgtIdx numSrc &&
          let d := tgtIdx - numSrc
          match Trusted.MirSemantics.getElem? dupSpecs d with
          | some spec => Nat.beq spec.joinBlock joinIdx
          | none => false
      | _, _ => false)

noncomputable def isJumpThreadingBody (dupSpecs : List JumpThreadDupSpec)
    (bSrc bTgt : Body) : Bool :=
  let numSrc := bSrc.basicBlocks.length
  bodyHeaderEq bSrc bTgt &&
    Nat.beq bTgt.basicBlocks.length (numSrc + dupSpecs.length) &&
    listRel (isJumpThreadOrigBlock numSrc dupSpecs)
      bSrc.basicBlocks (bTgt.basicBlocks.take numSrc) &&
    checkAppendedDupBlocks bSrc dupSpecs (bTgt.basicBlocks.drop numSrc)

noncomputable def isJumpThreadingProgram
    (dupSpecsList : List (List JumpThreadDupSpec))
    (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    Nat.beq dupSpecsList.length pSrc.bodies.length &&
    listRel (fun spPr bTgt => isJumpThreadingBody spPr.1 spPr.2 bTgt)
      (List.zip dupSpecsList pSrc.bodies) pTgt.bodies

/-! ## Part II: Flow-Sensitive Constant/Branch Certificates & Semantic Contracts -/

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

/-! ### Local-Use & Co-Inductive All-Paths Deadness Helpers -/

/-- Whether `opnd` mentions `id` via `.copy` or `.move`. -/
noncomputable def operandTouchesLocal (id : LocalId) : Operand → Bool
  | .copy p | .move p => Nat.beq p.localId id
  | .constant _ => false

/-- Whether `rv` mentions `id` in any operand, discriminant, borrow, or
unsupported construct (conservatively returning `true` on `.unsupported`). -/
noncomputable def rvalueTouchesLocal (id : LocalId) : Rvalue → Bool
  | .use opnd | .unaryOp _ opnd => operandTouchesLocal id opnd
  | .binaryOp _ lhs rhs =>
    operandTouchesLocal id lhs || operandTouchesLocal id rhs
  | .discriminant p | .ref _ p | .addressOf _ p => Nat.beq p.localId id
  | .aggregateTuple fs => fs.any (operandTouchesLocal id)
  | .unsupported => true

/-- Check whether `d` is certified dead on entry to in-bounds block `target`. -/
noncomputable def isDeadAtTarget (deadAtEntry : List (List LocalId))
    (numBlocks : Nat) (d : LocalId) (target : BasicBlockId) : Bool :=
  Nat.blt target numBlocks &&
    match Trusted.MirSemantics.getElem? deadAtEntry target with
    | some ds => natElem d ds
    | none => false

/-- Check whether local `d` (`d ≠ 0` checked by callers) is never read or
touched along any CFG path starting at `(stmts, term)` before an unprojected
assignment `⟨d, []⟩ = ...`, `StorageLive(d)`, `StorageDead(d)`, or
`.return_` / `.unreachable`. -/
noncomputable def isDeadAcrossCfg (deadAtEntry : List (List LocalId))
    (numBlocks : Nat) (d : LocalId) :
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

noncomputable def checkDeadAtEntryLoop (bSrc : Body)
    (deadAtEntry : List (List LocalId)) : Nat → List (List LocalId) → Bool
  | _, [] => true
  | bbIdx, ds :: rest =>
    (match Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx with
     | none => false
     | some bbSrc =>
       ds.all (fun d =>
         !Nat.beq d 0 &&
           isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length d
             bbSrc.statements bbSrc.terminator)) &&
      checkDeadAtEntryLoop bSrc deadAtEntry (bbIdx + 1) rest

/-! ### 5-Point Flow-Sensitive Constant & Liveness Lattice (`ConstAbsSlot`) -/

/-- 5-point abstract local domain (`bottom ⊑ knownConst ty lit ⊑ liveUnknown ⊑
liveUninit ⊑ dead`), mirroring `State<FlatSet<Scalar>>` in
`compiler/rustc_mir_transform/src/dataflow_const_prop.rs:95-113` together with
local storage liveness and initialization. -/
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

/-- Structural equality on supported scalar/boolean/unit/enum `Val` payloads. -/
noncomputable def scalarValBeq (a b : ScalarVal) : Bool :=
  IntWidth.beq a.width b.width && (a.signed == b.signed) && (a.bits == b.bits)

noncomputable def valBeq : Val → Val → Bool
  | .scalar a, .scalar b => scalarValBeq a b
  | .bool a, .bool b => a == b
  | .unit, .unit => true
  | .enumVal ety₁ v₁, .enumVal ety₂ v₂ =>
    EnumTy.beq ety₁ ety₂ && Nat.beq v₁ v₂
  | _, _ => false

/-- Encode a runtime scalar, boolean, or unit `Val` back into a verified
`.knownConst dstTy lit` slot (falling back conservatively to `.liveUnknown` if
encoding is unavailable). Checking `valBeq vCheck resVal` against `evalConstLit`
guarantees by construction that `evalConstLit dstTy lit = .ok resVal`. -/
noncomputable def valToVerifiedConstSlot (dstTy : MirTy)
    (resVal : Val) : ConstAbsSlot :=
  if !(isSupportedScalarOrUnitTy dstTy && checkVal resVal dstTy) then
    .liveUnknown
  else
    let candLit? : Option ConstLit :=
      match resVal with
      | .scalar sv => if sv.wf then some (.scalar sv.bits) else none
      | .bool false => some (.scalar (BitVec.ofNat 128 0))
      | .bool true => some (.scalar (BitVec.ofNat 128 1))
      | .unit => some .zeroSized
      | _ => none
    match candLit? with
    | none => .liveUnknown
    | some lit =>
      match evalConstLit dstTy lit with
      | .ok vCheck =>
        if valBeq vCheck resVal then .knownConst dstTy lit else .liveUnknown
      | .error _ => .liveUnknown

/-- Check whether `c : ConstOperand` is a valid constant of supported type `ty`
decoding via `evalConstLit` to a well-typed `Val`. -/
noncomputable def validTypedConstOperand (ty : MirTy)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty ty &&
    isSupportedScalarOrUnitTy ty &&
    match evalConstLit ty c.lit with
    | .ok v => checkVal v ty
    | .error _ => false

/-- Resolve an `Operand` in `env` to a verified constant `(ty, lit)` whenever
known. -/
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

/-- Apply `Operand.move` deinitialization (`deinitMovedPlace = true`) in `env`. -/
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

/-- Compute the abstract constant slot produced by `rv` for destination type
`dstTy` (propagating `Rvalue.use` constants and constant-folding `Rvalue.unaryOp`
and `Rvalue.binaryOp` in left-to-right operand order, matching
`ConstAnalysis::handle_assign` in `dataflow_const_prop.rs:268-405`). -/
noncomputable def rvalueConstSlot (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (dstTy : MirTy) : Rvalue → ConstAbsSlot
  | .use opnd =>
    match evalOperandConst? bodyLocals env opnd with
    | some (opTy, lit) =>
      if MirTy.beq opTy dstTy then .knownConst dstTy lit else .liveUnknown
    | none => .liveUnknown
  | .unaryOp uop opnd =>
    match evalOperandConst? bodyLocals env opnd with
    | some (opTy, lit) =>
      if !isPrimitiveReadableTy opTy then .liveUnknown
      else
        match evalConstLit opTy lit with
        | .ok v =>
          match evalUnOp uop v with
          | .ok resVal => valToVerifiedConstSlot dstTy resVal
          | .error _ => .liveUnknown
        | .error _ => .liveUnknown
    | none => .liveUnknown
  | .binaryOp bop lhs rhs =>
    let env₁ := deinitMoveOperandConst bodyLocals env lhs
    match evalOperandConst? bodyLocals env lhs,
        evalOperandConst? bodyLocals env₁ rhs with
    | some (lTy, lLit), some (rTy, rLit) =>
      if !(isPrimitiveReadableTy lTy && isPrimitiveReadableTy rTy) then
        .liveUnknown
      else
        match evalConstLit lTy lLit, evalConstLit rTy rLit with
        | .ok lVal, .ok rVal =>
          match evalBinOp bop lVal rVal with
          | .ok resVal => valToVerifiedConstSlot dstTy resVal
          | .error _ => .liveUnknown
        | _, _ => .liveUnknown
    | _, _ => .liveUnknown
  | _ => .liveUnknown

/-- Abstract statement transfer function over `ConstAbsSlot`. -/
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

noncomputable def stepPlainStmtsConst (bodyLocals : List MirTy) :
    List ConstAbsSlot → List StatementKind → Option (List ConstAbsSlot)
  | env, [] => some env
  | env, s :: ss =>
    match stepPlainStmtConst bodyLocals env s with
    | none => none
    | some env' => stepPlainStmtsConst bodyLocals env' ss

/-- Refine `afterDiscrEnv` along a `SwitchInt (.copy ⟨x, []⟩)` equality arm
`(caseBits, brTarget)` whenever `x` has primitive scalar or `bool` type `ty`, is
certified initialized (`constSlotImplies curSlot .liveUnknown`), and `caseBits`
decodes cleanly via `evalConstLit ty (.scalar caseBits)`. -/
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
        let branchEnv := refineSwitchBranchEnv bodyLocals afterDiscrEnv discr br.1
        checkConstEdge numBlocks cert branchEnv br.2)
  | _ => true

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
      match evalSwitchBranches sv.width sv.bits
          targets.otherwise targets.branches with
      | .ok target => some target
      | .error _ => none
    | .ok (.bool b) =>
      match evalBoolSwitchBranches b targets.otherwise targets.branches with
      | .ok target => some target
      | .error _ => none
    | .ok _ => none

/-! ### Certificate 1a (`checkConstPropCopyProgram`): Certified `Operand.copy ↦ Operand.constant` -/

noncomputable def checkConstPropCopyOperand (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (opSrc opTgt : Operand) : Bool :=
  match opSrc, opTgt with
  | .copy p, .constant c =>
    p.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some slot =>
        validTypedConstOperand ty c &&
          constSlotImplies slot (.knownConst ty c.lit)
      | _, _ => false
  | _, _ => operandEq opSrc opTgt

noncomputable def checkConstPropCopyRvalue (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : Rvalue → Rvalue → Bool
  | .use o₁, .use o₂ => checkConstPropCopyOperand bodyLocals env o₁ o₂
  | .unaryOp uop₁ o₁, .unaryOp uop₂ o₂ =>
    unOpEq uop₁ uop₂ && checkConstPropCopyOperand bodyLocals env o₁ o₂
  | .binaryOp bop₁ l₁ r₁, .binaryOp bop₂ l₂ r₂ =>
    let env₁ := deinitMoveOperandConst bodyLocals env l₁
    binOpEq bop₁ bop₂ &&
      checkConstPropCopyOperand bodyLocals env l₁ l₂ &&
      checkConstPropCopyOperand bodyLocals env₁ r₁ r₂
  | rv₁, rv₂ => rvalueEq rv₁ rv₂

noncomputable def stepConstPropCopyCertStmts (bodyLocals : List MirTy) :
    List ConstAbsSlot → List StatementKind → List StatementKind →
    Option (List ConstAbsSlot)
  | env, [], [] => some env
  | env, sSrc :: restSrc, sTgt :: restTgt =>
    let stmtOk : Bool :=
      match sSrc, sTgt with
      | .assign d₁ rv₁, .assign d₂ rv₂ =>
        placeEq d₁ d₂ && d₁.projection.isEmpty &&
          checkConstPropCopyRvalue bodyLocals env rv₁ rv₂
      | _, _ => stmtEq sSrc sTgt
    if !stmtOk then none
    else
      match stepPlainStmtConst bodyLocals env sSrc with
      | none => none
      | some env' =>
        stepConstPropCopyCertStmts bodyLocals env' restSrc restTgt
  | _, _, _ => none

noncomputable def checkConstPropCopyTerminator (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : TerminatorKind → TerminatorKind → Bool
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ =>
    checkConstPropCopyOperand bodyLocals env d₁ d₂ && switchTargetsEq ts₁ ts₂
  | t₁, t₂ => terminatorEq t₁ t₂

noncomputable def checkConstPropCopyBlock (bSrc bTgt : Body)
    (cert : BodyConstCert) (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    (bbSrc.cleanup == bbTgt.cleanup) &&
      Nat.beq entryEnv.length bSrc.locals.length &&
      match stepConstPropCopyCertStmts bSrc.locals entryEnv
          bbSrc.statements bbTgt.statements with
      | none => false
      | some exitEnv =>
        checkConstPropCopyTerminator bSrc.locals exitEnv
            bbSrc.terminator bbTgt.terminator &&
          checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length
            cert exitEnv bbSrc.terminator

noncomputable def checkConstPropCopyBlocksLoop (bSrc bTgt : Body)
    (cert : BodyConstCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkConstPropCopyBlock bSrc bTgt cert idx bbSrc &&
      checkConstPropCopyBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkConstPropCopyBody (cert : BodyConstCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         constEnvImplies (initConstEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkConstPropCopyBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkConstPropCopyProgram (cert : ProgramConstCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkConstPropCopyBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Certificate 1b (`checkConstPropMoveProgram`): Certified `Operand.move ↦ Operand.constant` (Forward Codegen Refinement Without Deadness) -/

noncomputable def checkConstPropMoveOperand (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (opSrc opTgt : Operand) : Bool :=
  match opSrc, opTgt with
  | .move p, .constant c =>
    p.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some slot =>
        validTypedConstOperand ty c &&
          constSlotImplies slot (.knownConst ty c.lit)
      | _, _ => false
  | _, _ => operandEq opSrc opTgt

noncomputable def checkConstPropMoveRvalue (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : Rvalue → Rvalue → Bool
  | .use o₁, .use o₂ => checkConstPropMoveOperand bodyLocals env o₁ o₂
  | .unaryOp uop₁ o₁, .unaryOp uop₂ o₂ =>
    unOpEq uop₁ uop₂ && checkConstPropMoveOperand bodyLocals env o₁ o₂
  | .binaryOp bop₁ l₁ r₁, .binaryOp bop₂ l₂ r₂ =>
    let env₁ := deinitMoveOperandConst bodyLocals env l₁
    binOpEq bop₁ bop₂ &&
      checkConstPropMoveOperand bodyLocals env l₁ l₂ &&
      checkConstPropMoveOperand bodyLocals env₁ r₁ r₂
  | rv₁, rv₂ => rvalueEq rv₁ rv₂

noncomputable def stepConstPropMoveCertStmts (bodyLocals : List MirTy) :
    List ConstAbsSlot → List StatementKind → List StatementKind →
    Option (List ConstAbsSlot)
  | env, [], [] => some env
  | env, sSrc :: restSrc, sTgt :: restTgt =>
    let stmtOk : Bool :=
      match sSrc, sTgt with
      | .assign d₁ rv₁, .assign d₂ rv₂ =>
        placeEq d₁ d₂ && d₁.projection.isEmpty &&
          checkConstPropMoveRvalue bodyLocals env rv₁ rv₂
      | _, _ => stmtEq sSrc sTgt
    if !stmtOk then none
    else
      match stepPlainStmtConst bodyLocals env sSrc with
      | none => none
      | some env' =>
        stepConstPropMoveCertStmts bodyLocals env' restSrc restTgt
  | _, _, _ => none

noncomputable def checkConstPropMoveTerminator (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) : TerminatorKind → TerminatorKind → Bool
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ =>
    checkConstPropMoveOperand bodyLocals env d₁ d₂ && switchTargetsEq ts₁ ts₂
  | t₁, t₂ => terminatorEq t₁ t₂

noncomputable def checkConstPropMoveBlock (bSrc bTgt : Body)
    (cert : BodyConstCert) (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    (bbSrc.cleanup == bbTgt.cleanup) &&
      Nat.beq entryEnv.length bSrc.locals.length &&
      match stepConstPropMoveCertStmts bSrc.locals entryEnv
          bbSrc.statements bbTgt.statements with
      | none => false
      | some exitEnv =>
        checkConstPropMoveTerminator bSrc.locals exitEnv
            bbSrc.terminator bbTgt.terminator &&
          checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length
            cert exitEnv bbSrc.terminator

noncomputable def checkConstPropMoveBlocksLoop (bSrc bTgt : Body)
    (cert : BodyConstCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkConstPropMoveBlock bSrc bTgt cert idx bbSrc &&
      checkConstPropMoveBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkConstPropMoveBody (cert : BodyConstCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         constEnvImplies (initConstEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkConstPropMoveBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkConstPropMoveProgram (cert : ProgramConstCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkConstPropMoveBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Certificate 1c (`checkConstPropMoveDeadProgram`): Certified `Operand.move ↦ Operand.constant` + All-Paths Post-Move Deadness (`↔`) -/

/-- Per-body certificate for bidirectional `ConstPropMove`, pairing forward
constant certification (`constCert`) with co-inductive cross-block dead-on-entry
sets (`deadAtEntry`, defaulting to `[]` when moved locals die intra-block). -/
structure BodyConstMoveDeadCert where
  constCert : BodyConstCert
  deadAtEntry : List (List LocalId) := []

abbrev ProgramConstMoveDeadCert := List BodyConstMoveDeadCert

/-- Check that `x` (`x ≠ 0`) is either immediately overwritten by `dst` at the
current `.assign ⟨dst, []⟩` statement or dead along all CFG paths in
`(restSrc, termSrc)`. -/
noncomputable def isDeadAfterAssignMove (deadAtEntry : List (List LocalId))
    (numBlocks : Nat) (dst x : LocalId) (restSrc : List StatementKind)
    (termSrc : TerminatorKind) : Bool :=
  !Nat.beq x 0 &&
    (Nat.beq dst x || isDeadAcrossCfg deadAtEntry numBlocks x restSrc termSrc)

noncomputable def checkMoveRewriteDeadRvalue (deadAtEntry : List (List LocalId))
    (numBlocks : Nat) (dst : LocalId) (restSrc : List StatementKind)
    (termSrc : TerminatorKind) : Rvalue → Rvalue → Bool
  | .use (.move p), .use (.constant _) =>
    p.projection.isEmpty &&
      isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId restSrc termSrc
  | .unaryOp _ (.move p), .unaryOp _ (.constant _) =>
    p.projection.isEmpty &&
      isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId restSrc termSrc
  | .binaryOp _ l₁ r₁, .binaryOp _ l₂ r₂ =>
    let lhsDeadOk : Bool :=
      match l₁, l₂ with
      | .move p, .constant _ =>
        p.projection.isEmpty &&
          !operandTouchesLocal p.localId r₁ &&
          isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId
            restSrc termSrc
      | _, _ => true
    let rhsDeadOk : Bool :=
      match r₁, r₂ with
      | .move p, .constant _ =>
        p.projection.isEmpty &&
          isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId
            restSrc termSrc
      | _, _ => true
    lhsDeadOk && rhsDeadOk
  | _, _ => true

noncomputable def checkMoveRewriteDeadStmts (deadAtEntry : List (List LocalId))
    (numBlocks : Nat) (termSrc : TerminatorKind) :
    List StatementKind → List StatementKind → Bool
  | [], [] => true
  | sSrc :: restSrc, sTgt :: restTgt =>
    let okHere : Bool :=
      match sSrc, sTgt with
      | .assign dstPlace rvSrc, .assign _ rvTgt =>
        dstPlace.projection.isEmpty &&
          checkMoveRewriteDeadRvalue deadAtEntry numBlocks dstPlace.localId
            restSrc termSrc rvSrc rvTgt
      | _, _ => true
    okHere &&
      checkMoveRewriteDeadStmts deadAtEntry numBlocks termSrc restSrc restTgt
  | _, _ => false

noncomputable def checkMoveRewriteDeadTerm (deadAtEntry : List (List LocalId))
    (numBlocks : Nat) : TerminatorKind → TerminatorKind → Bool
  | .switchInt (.move p) targets, .switchInt (.constant _) _ =>
    p.projection.isEmpty &&
      !Nat.beq p.localId 0 &&
      isDeadAtTarget deadAtEntry numBlocks p.localId targets.otherwise &&
      targets.branches.all (fun br =>
        isDeadAtTarget deadAtEntry numBlocks p.localId br.2)
  | _, _ => true

noncomputable def checkMoveRewriteDeadBlocksLoop (bSrc bTgt : Body)
    (cert : BodyConstMoveDeadCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    let okHere : Bool :=
      match Trusted.MirSemantics.getElem? cert.constCert idx,
          Trusted.MirSemantics.getElem? bTgt.basicBlocks idx with
      | _, none => false
      | none, _ => false
      | some none, some _ => true
      | some (some _), some bbTgt =>
        let numBlocks := bSrc.basicBlocks.length
        checkMoveRewriteDeadStmts cert.deadAtEntry numBlocks bbSrc.terminator
            bbSrc.statements bbTgt.statements &&
          checkMoveRewriteDeadTerm cert.deadAtEntry numBlocks
            bbSrc.terminator bbTgt.terminator
    okHere && checkMoveRewriteDeadBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkConstPropMoveDeadBody (cert : BodyConstMoveDeadCert)
    (bSrc bTgt : Body) : Bool :=
  checkConstPropMoveBody cert.constCert bSrc bTgt &&
    checkDeadAtEntryLoop bSrc cert.deadAtEntry 0 cert.deadAtEntry &&
    checkMoveRewriteDeadBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkConstPropMoveDeadProgram
    (cert : ProgramConstMoveDeadCert) (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkConstPropMoveDeadBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Certificate 2 (`checkMatchBranchSimplifyProgram`): Validated Type, Width, & Polarity Certificate for `MatchBranchSimplify` -/

/-- Validate that a `MatchBranchSimplify` rewrite at `bbIdx` preserves exact
type, width, `evalConstLit` boolean/scalar validity, and `.eq`/`.ne` polarity
between `pSrc`'s `SwitchInt` + `bbCase`/`bbOther` diamond and `pTgt`'s in-place
`BinaryOp`. -/
noncomputable def checkMatchBranchRewriteAt (bSrc : Body) (bbIdx : BasicBlockId)
    (bbSrc bbTgt : BasicBlock) : Bool :=
  isMatchBranchRewriteAt bSrc bbIdx bbSrc bbTgt &&
    match bbSrc.terminator with
    | .switchInt (.copy dPlace) { branches := [(caseBits, bbCase)], otherwise := bbOther } =>
      match Trusted.MirSemantics.getElem? bSrc.basicBlocks bbCase,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks bbOther,
          Trusted.MirSemantics.getElem?
            bbTgt.statements bbSrc.statements.length with
      | some blkCase, some blkOther,
          some (.assign dstTgt
            (.binaryOp cmpOp (.copy _) (.constant caseConst))) =>
        match blkCase.statements, blkOther.statements,
            Trusted.MirSemantics.getElem? bSrc.locals dstTgt.localId,
            Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId with
        | [.assign _ (.use (.constant cCase))],
            [.assign _ (.use (.constant cOther))],
            some .bool, some discrTy =>
          isPrimitiveReadableTy discrTy &&
            constOpEq caseConst ⟨discrTy, .scalar caseBits⟩ &&
            validTypedConstOperand discrTy caseConst &&
            MirTy.beq cCase.ty .bool &&
            MirTy.beq cOther.ty .bool &&
            match evalConstLit .bool cCase.lit,
                evalConstLit .bool cOther.lit with
            | .ok (.bool bCase), .ok (.bool bOther) =>
              (bOther == !bCase) &&
                binOpEq cmpOp (if bCase then .eq else .ne)
            | _, _ => false
        | _, _, _, _ => false
      | _, _, _ => false
    | _ => false

noncomputable def checkMatchBranchBlocksLoop (bSrc : Body) :
    Nat → List BasicBlock → List BasicBlock → Bool
  | _, [], [] => true
  | idx, bbSrc :: restSrc, bbTgt :: restTgt =>
    (if isMatchBranchRewriteAt bSrc idx bbSrc bbTgt then
       checkMatchBranchRewriteAt bSrc idx bbSrc bbTgt
     else
       blockEq bbSrc bbTgt) &&
      checkMatchBranchBlocksLoop bSrc (idx + 1) restSrc restTgt
  | _, _, _ => false

noncomputable def checkMatchBranchSimplifyBody (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    checkMatchBranchBlocksLoop bSrc 0 bSrc.basicBlocks bTgt.basicBlocks

noncomputable def checkMatchBranchSimplifyProgram (pSrc pTgt : Program) : Bool :=
  listRel checkMatchBranchSimplifyBody pSrc.bodies pTgt.bodies

/-! ### Certificate 3 (`checkJumpThreadingProgram`): Flow-Sensitive Post-Prefix Switch Certificate for `JumpThreading` -/

/-- Check that every `.goto` and `.switchInt` destination in `bSrc` lies
strictly below `bSrc.basicBlocks.length` so appending `bbDup` blocks at
`>= bSrc.basicBlocks.length` cannot turn an out-of-bounds jump fault in `bSrc`
into an in-bounds jump to `bbDup` in `bTgt`. -/
noncomputable def allJumpTargetsInBounds (bSrc : Body) : Bool :=
  let numSrc := bSrc.basicBlocks.length
  bSrc.basicBlocks.all (fun bb =>
    match bb.terminator with
    | .goto target => Nat.blt target numSrc
    | .switchInt _ targets =>
      Nat.blt targets.otherwise numSrc &&
        targets.branches.all (fun br => Nat.blt br.2 numSrc)
    | _ => true)

/-- Validate a redirected predecessor `bbSrc` (`Goto joinIdx ↦ Goto (numSrc + d)`):
stepping `bbSrc`'s exit environment `predExitEnv` across `bbJoin.statements`
yields `dupExitEnv` in which `bbJoin`'s `SwitchInt (.copy ⟨discr, []⟩)`
discriminant is certified to hold a valid constant resolving via
`resolveConstSwitchTarget` to `dupSpecs[d].resolvedTarget`, and `dupExitEnv`
implies `cert[resolvedTarget]`. -/
noncomputable def checkJumpThreadRedirectedEdge (bSrc : Body)
    (cert : BodyConstCert) (dupSpecs : List JumpThreadDupSpec)
    (predExitEnv : List ConstAbsSlot) (tgtIdx : BasicBlockId) : Bool :=
  let numSrc := bSrc.basicBlocks.length
  !Nat.blt tgtIdx numSrc &&
    let d := tgtIdx - numSrc
    match Trusted.MirSemantics.getElem? dupSpecs d with
    | none => false
    | some spec =>
      match Trusted.MirSemantics.getElem? bSrc.basicBlocks spec.joinBlock with
      | none => false
      | some bbJoin =>
        match bbJoin.terminator,
            stepPlainStmtsConst bSrc.locals predExitEnv bbJoin.statements with
        | .switchInt (.copy dPlace) targets, some dupExitEnv =>
          dPlace.projection.isEmpty &&
            checkConstEdge numSrc cert dupExitEnv spec.resolvedTarget &&
            match Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId,
                Trusted.MirSemantics.getElem? dupExitEnv dPlace.localId with
            | some discrTy, some (.knownConst cTy cLit) =>
              MirTy.beq cTy discrTy &&
                match resolveConstSwitchTarget ⟨discrTy, cLit⟩ targets with
                | some res => Nat.beq res spec.resolvedTarget
                | none => false
            | some _, some .bottom => true
            | _, _ => false
        | _, _ => false

noncomputable def checkJumpThreadingBlock (bSrc bTgt : Body)
    (cert : BodyConstCert) (dupSpecs : List JumpThreadDupSpec)
    (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  let numSrc := bSrc.basicBlocks.length
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      match stepPlainStmtsConst bSrc.locals entryEnv bbSrc.statements with
      | none => false
      | some exitEnv =>
        checkConstTerminatorEdges bSrc.locals numSrc cert exitEnv
            bbSrc.terminator &&
          match bbSrc.terminator, bbTgt.terminator with
          | .goto _, .goto tgtIdx =>
            if Nat.blt tgtIdx numSrc then
              blockEq bbSrc bbTgt
            else
              checkJumpThreadRedirectedEdge bSrc cert dupSpecs exitEnv tgtIdx
          | _, _ => blockEq bbSrc bbTgt

noncomputable def checkJumpThreadingBlocksLoop (bSrc bTgt : Body)
    (cert : BodyConstCert) (dupSpecs : List JumpThreadDupSpec) :
    Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkJumpThreadingBlock bSrc bTgt cert dupSpecs idx bbSrc &&
      checkJumpThreadingBlocksLoop bSrc bTgt cert dupSpecs (idx + 1) rest

noncomputable def checkJumpThreadingBody (cert : BodyConstCert)
    (dupSpecs : List JumpThreadDupSpec) (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    allJumpTargetsInBounds bSrc &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         constEnvImplies (initConstEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkJumpThreadingBlocksLoop bSrc bTgt cert dupSpecs 0 bSrc.basicBlocks

noncomputable def checkJumpThreadingProgram (cert : ProgramConstCert)
    (dupSpecsList : List (List JumpThreadDupSpec))
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    Nat.beq dupSpecsList.length pSrc.bodies.length &&
    listRel
      (fun csPr bTgt =>
        checkJumpThreadingBody csPr.1 csPr.2.1 csPr.2.2 bTgt)
      (List.zip cert (List.zip dupSpecsList pSrc.bodies)) pTgt.bodies

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

private theorem nat_ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro hEq
  rw [hEq, nat_beq_refl] at h
  cases h

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
    (h : (a == b) = true) : a = b :=
  eq_of_beq h

private theorem bitvec_beq_refl {n : Nat} (x : BitVec n) : (x == x) = true :=
  decide_eq_true rfl

private theorem bitvec_eq_of_bne_false {n : Nat} {a b : BitVec n}
    (h : (a != b) = false) : a = b := by
  change (!(a == b)) = false at h
  exact eq_of_beq (bool_not_false h)

private theorem bitvec_ne_of_beq_false {n : Nat} {a b : BitVec n}
    (h : (a == b) = false) : a ≠ b := by
  intro hEq
  subst hEq
  rw [beq_self_eq_true a] at h
  cases h

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

private theorem natElem_all {p : Nat → Bool} {x : Nat} {xs : List Nat}
    (hAll : xs.all p = true) (hElem : natElem x xs = true) :
    p x = true := by
  induction xs with
  | nil => cases hElem
  | cons y ys ih =>
    dsimp [List.all] at hAll
    let ⟨hy, hys⟩ := bool_and_true hAll
    dsimp [natElem] at hElem
    cases bool_or_true hElem with
    | inl hEq =>
      rw [nat_beq_eq hEq]
      exact hy
    | inr hTail =>
      exact ih hys hTail

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

private theorem listRel_drop {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} (n : Nat)
    (hRel : listRel r xs ys = true) :
    listRel r (xs.drop n) (ys.drop n) = true := by
  induction xs generalizing ys n with
  | nil =>
    cases ys with
    | nil =>
      cases n <;> rfl
    | cons _ _ => cases hRel
  | cons a xs ih =>
    cases ys with
    | nil => cases hRel
    | cons b ys =>
      let ⟨_, hTail⟩ := bool_and_true hRel
      cases n with
      | zero => exact hRel
      | succ k => exact ih k hTail

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

private theorem drop_of_ge {α : Type} {xs : List α} {n : Nat}
    (h : xs.length ≤ n) : xs.drop n = [] := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons _ xs ih =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero xs.length h)
    | succ k => exact ih (Nat.le_of_succ_le_succ h)

private theorem getElem?_drop {α : Type} (xs : List α) (n d : Nat) :
    Trusted.MirSemantics.getElem? (xs.drop n) d =
      Trusted.MirSemantics.getElem? xs (n + d) := by
  induction xs generalizing n with
  | nil =>
    cases n <;> rfl
  | cons a xs ih =>
    cases n with
    | zero =>
      rw [Nat.zero_add]
      rfl
    | succ k =>
      rw [Nat.succ_add]
      exact ih k

private theorem getElem?_take_lt {α : Type} (xs : List α) (n i : Nat)
    (h : i < n) :
    Trusted.MirSemantics.getElem? (xs.take n) i =
      Trusted.MirSemantics.getElem? xs i := by
  induction xs generalizing n i with
  | nil =>
    cases n <;> rfl
  | cons a xs ih =>
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero i h)
    | succ m =>
      cases i with
      | zero => rfl
      | succ k => exact ih m k (Nat.lt_of_succ_lt_succ h)

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

private theorem constLitEq_refl (a : ConstLit) : constLitEq a a = true := by
  cases a with
  | scalar b => exact bitvec_beq_refl b
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

private theorem scopeEq_eq {a b : VerificationScope}
    (h : scopeEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem scopeEq_refl (a : VerificationScope) : scopeEq a a = true := by
  cases a <;> rfl

private theorem scalarValBeq_eq {a b : ScalarVal}
    (h : scalarValBeq a b = true) : a = b := by
  cases a with
  | mk w1 s1 b1 =>
    cases b with
    | mk w2 s2 b2 =>
      dsimp [scalarValBeq] at h
      let ⟨h12, h3⟩ := bool_and_true h
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [intWidth_beq_eq h1, bool_beq_eq h2, bitvec_beq_eq h3]

private theorem valBeq_eq {a b : Val} (h : valBeq a b = true) : a = b := by
  cases a with
  | scalar sa =>
    cases b with
    | scalar sb => rw [scalarValBeq_eq h]
    | _ => cases h
  | bool ba =>
    cases b with
    | bool bb => rw [bool_beq_eq h]
    | _ => cases h
  | unit =>
    cases b with
    | unit => rfl
    | _ => cases h
  | enumVal ea va =>
    cases b with
    | enumVal eb vb =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [enumTy_beq_eq h1, nat_beq_eq h2]
    | _ => cases h
  | ptr _ | tuple _ | bytes _ =>
    cases b <;> cases h

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

private theorem preservesAllStorageAnnotationsLoop_get {b₁ b₂ : Body} {n idx : Nat}
    (hLoop : preservesAllStorageAnnotationsLoop b₁ b₂ n = true)
    (hLt : idx < n) :
    hasStorageAnnotation b₁ idx = hasStorageAnnotation b₂ idx := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero idx hLt)
  | succ m ih =>
    dsimp [preservesAllStorageAnnotationsLoop] at hLoop
    let ⟨hHere, hRest⟩ := bool_and_true hLoop
    cases Nat.lt_or_ge idx m with
    | inl hSub => exact ih hRest hSub
    | inr hGe =>
      have hEq : idx = m := Nat.le_antisymm (Nat.le_of_succ_le_succ hLt) hGe
      subst hEq
      exact bool_beq_eq hHere

private theorem preservesAllStorageAnnotations_elim {b₁ b₂ : Body}
    (h : preservesAllStorageAnnotations b₁ b₂ = true) :
    storageAnnotationsInBounds b₁ = storageAnnotationsInBounds b₂ ∧
    ∀ idx, idx < b₁.locals.length →
      hasStorageAnnotation b₁ idx = hasStorageAnnotation b₂ idx := by
  unfold preservesAllStorageAnnotations at h
  let ⟨hBnd, hLoop⟩ := bool_and_true h
  exact ⟨bool_beq_eq hBnd, fun _ hLt => preservesAllStorageAnnotationsLoop_get hLoop hLt⟩

/-! ### Stage 4 Private Helpers — Layer B: Simulation & Program Lifters -/

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
        · intro hDivTgt
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
        · intro hDivSrc
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

private theorem initLocalsLoop_eq_of_preservesStorage {b1 b2 : Body} (args : List Val)
    (hBHdr : bodyHeaderEq b1 b2 = true)
    (hPres : preservesAllStorageAnnotations b1 b2 = true) :
    initLocalsLoop b1 args 0 b1.locals = initLocalsLoop b2 args 0 b2.locals := by
  let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  let ⟨_, hStAll⟩ := preservesAllStorageAnnotations_elim hPres
  exact initLocalsLoop_eq_of_storage_eq args hArg hLoc (fun idx hLt _ => hStAll idx hLt)

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

/-! ### Stage 4 Private Helpers — Layer B2: Well-Typed Locals, Slot
Refinement, & Scalar Injectivity -/

private theorem isPrimitiveReadableTy_bool : isPrimitiveReadableTy .bool = true := rfl

private theorem isPrimitiveReadableTy_int (w : IntWidth) (s : Bool) :
    isPrimitiveReadableTy (.int w s) = true := rfl

private theorem isPrimitiveReadableTy_elim {ty : MirTy}
    (h : isPrimitiveReadableTy ty = true) :
    ty = .bool ∨ ∃ w s, ty = .int w s := by
  cases ty with
  | bool => exact Or.inl rfl
  | int w s => exact Or.inr ⟨w, s, rfl⟩
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h

private theorem isSupportedScalarOrUnitTy_bool :
    isSupportedScalarOrUnitTy .bool = true := rfl

private theorem isSupportedScalarOrUnitTy_int (w : IntWidth) (s : Bool) :
    isSupportedScalarOrUnitTy (.int w s) = true := rfl

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

private theorem checkVal_iff_ty? {v : Val} {ty : MirTy} :
    checkVal v ty = true ↔ v.ty? = some ty := by
  unfold checkVal
  cases hTy : v.ty? with
  | none =>
    constructor <;> (intro h; cases h)
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
          injection h with hTy
          injection hTy with hw hs
          subst hw; subst hs
          exact ⟨bits, rfl, eq_of_beq hWf⟩
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | ptr _ | bool _ | unit | tuple _ | bytes _ => cases h
  · intro h
    let ⟨bits, hv, hTrunc⟩ := h
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
  · intro h
    let ⟨b, hb⟩ := h
    subst hb; rfl

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
          injection h with hTy
          injection hTy with hEty
          subst hEty
          exact ⟨hAdm, var, nat_blt_lt hBlt, rfl⟩
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | ptr _ | bool _ | unit | tuple _ | bytes _ => cases h
  · intro h
    let ⟨hAdm, idx, hLt, hEq⟩ := h
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
        | true =>
          rw [h0] at h; injection h with hEq; subst hEq; rfl
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
              rw [Nat.zero_add] at h0
              exact h0
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

private theorem liveUninitSlot_of_not_zst {ty : MirTy}
    (h : isAlwaysInhabitedZst ty = false) :
    liveUninitSlot ty = .live none := by
  cases ty with
  | unit => cases h
  | enum ety =>
    dsimp [isAlwaysInhabitedZst] at h
    dsimp [liveUninitSlot]
    rw [h]; rfl
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => rfl

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
    | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
      cases hZst

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
    have hi : i = id := nat_beq_eq hEq
    subst hi
    rw [hTy] at hTyi; injection hTyi with hEqT; subst hEqT
    rw [setElem?_getElem?_same hSet] at hSli; injection hSli with hEqS; subst hEqS
    exact hSlWt
  | false =>
    have hNe : i ≠ id := nat_ne_of_beq_false hEq
    rw [setElem?_getElem?_ne hSet hNe] at hSli
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
      rw [hV]
      exact hChk
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
        injection hEv with hEq
        injection hEq with _ hl; subst hl
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
          have hWt1 := evalPrimitiveOperand_preserves_wt hWt hL
          exact evalPrimitiveOperand_preserves_wt hWt1 hR
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
                      rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL; exact hWt
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
                          rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL; exact hWt
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
                          rw [hD] at hEv; injection hEv with h1; injection h1 with _ hL; subst hL; exact hWt
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

private theorem evalStatement_preserves_wt {body : Body} {frame : FrameState}
    {cm : CallerMemory} {stmt : StatementKind} {s' : State}
    (hWt : LocalsWellTyped body.locals frame.locals)
    (hEv : evalStatement body frame cm stmt = .step s') :
    ∃ locs',
      s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
             callerMem := cm } ∧
      LocalsWellTyped body.locals locs' := by
  cases stmt with
  | nop =>
    injection hEv with hEq; subst hEq
    exact ⟨frame.locals, rfl, hWt⟩
  | unsupported => cases hEv
  | storageLive id =>
    dsimp [evalStatement] at hEv
    cases hTy : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [hTy] at hEv; cases hEv
    | some ty =>
      rw [hTy] at hEv; dsimp at hEv
      cases hSet : setElem? frame.locals id (liveUninitSlot ty) with
      | none => rw [hSet] at hEv; cases hEv
      | some locs' =>
        rw [hSet] at hEv; injection hEv with hEq; subst hEq
        exact ⟨locs', rfl, localsWellTyped_set hWt hTy hSet (liveUninitSlot_wellTyped ty)⟩
  | storageDead id =>
    dsimp [evalStatement] at hEv
    cases hZ : Nat.beq id 0 with
    | true => rw [hZ] at hEv; cases hEv
    | false =>
      rw [hZ] at hEv; dsimp at hEv
      cases hSet : setElem? frame.locals id .dead with
      | none => rw [hSet] at hEv; cases hEv
      | some locs' =>
        rw [hSet] at hEv; injection hEv with hEq; subst hEq
        have hLt : id < body.locals.length := by
          cases Nat.lt_or_ge id body.locals.length with
          | inl h => exact h
          | inr hge =>
            have hNone := setElem?_none_of_ge frame.locals id .dead (by rw [hWt.1]; exact hge)
            rw [hNone] at hSet; cases hSet
        let ⟨ty, hTy⟩ := getElem?_some_of_lt body.locals id hLt
        exact ⟨locs', rfl, localsWellTyped_set hWt hTy hSet True.intro⟩
  | assign dst rv =>
    dsimp [evalStatement] at hEv
    cases hP : dst.projection.isEmpty with
    | false => rw [hP] at hEv; cases hEv
    | true =>
      rw [hP] at hEv; dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some dstTy =>
        rw [hTy] at hEv; dsimp at hEv
        cases hR : evalRvalue body.locals frame.locals dstTy rv with
        | error _ => rw [hR] at hEv; cases hEv
        | ok res =>
          let ⟨val, locs1⟩ := res
          rw [hR] at hEv; dsimp at hEv
          cases hW : writePlace locs1 dst.localId dstTy val with
          | error _ => rw [hW] at hEv; cases hEv
          | ok locs' =>
            rw [hW] at hEv; injection hEv with hEq; subst hEq
            have hWt1 := evalRvalue_preserves_wt hWt hR
            exact ⟨locs', rfl, (writePlace_preserves_wt hWt1 hTy hW).1⟩

private theorem evalTerminator_preserves_wt {body : Body} {bb : BasicBlock}
    {frame : FrameState} {cm : CallerMemory} {s' : State}
    (hWt : LocalsWellTyped body.locals frame.locals)
    (hEv : evalTerminator body bb frame cm = .step s') :
    ∃ tgt locs',
      s' = { frames := [{ frame with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
             callerMem := cm } ∧
      LocalsWellTyped body.locals locs' := by
  unfold evalTerminator at hEv
  cases hTm : bb.terminator with
  | goto tgt =>
    rw [hTm] at hEv
    injection hEv with hEq; subst hEq
    exact ⟨tgt, frame.locals, rfl, hWt⟩
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
    rw [hTm] at hEv; dsimp at hEv
    cases hD : evalPrimitiveOperand body.locals frame.locals discr with
    | error _ => rw [hD] at hEv; cases hEv
    | ok res =>
      let ⟨dv, locsAfter⟩ := res
      rw [hD] at hEv; dsimp at hEv
      have hWtAfter := evalPrimitiveOperand_preserves_wt hWt hD
      cases dv with
      | scalar sv =>
        dsimp at hEv
        cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok tgt =>
          rw [hSw] at hEv; injection hEv with hEq; subst hEq
          exact ⟨tgt, locsAfter, rfl, hWtAfter⟩
      | bool b =>
        dsimp at hEv
        cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok tgt =>
          rw [hSw] at hEv; injection hEv with hEq; subst hEq
          exact ⟨tgt, locsAfter, rfl, hWtAfter⟩
      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

private theorem evalStatement_eq_of_same {b₁ b₂ : Body} (frame : FrameState)
    (cm : CallerMemory) (stmt : StatementKind)
    (hLocs : b₁.locals = b₂.locals) :
    evalStatement b₁ frame cm stmt = evalStatement b₂ frame cm stmt := by
  unfold evalStatement
  rw [hLocs]

private theorem evalTerminator_eq_of_eq {b₁ b₂ : Body} {bb₁ bb₂ : BasicBlock}
    {frame : FrameState} {cm : CallerMemory}
    (hLocs : b₁.locals = b₂.locals)
    (hClean : bb₁.cleanup = bb₂.cleanup)
    (hTerm : bb₁.terminator = bb₂.terminator) :
    evalTerminator b₁ bb₁ frame cm = evalTerminator b₂ bb₂ frame cm := by
  unfold evalTerminator
  rw [hTerm, hLocs, hClean]

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

/-! #### Slot Forward Refinement (`SlotFwdRefines`, `LocalsFwdRefines`) -/

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

private theorem slotFwdRefines_refl (sl : LocalSlot) : SlotFwdRefines sl sl := by
  cases sl with
  | dead => exact True.intro
  | live opt => exact slotFwdRefines_refl_live opt

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

private theorem localsFwdRefines_refl_of_wt {bodyLocals : List MirTy}
    {locals : List LocalSlot} (hWt : LocalsWellTyped bodyLocals locals) :
    LocalsFwdRefines bodyLocals locals locals := by
  refine ⟨hWt.1, hWt.1, ?_⟩
  intro i ty s1 s2 hTy hS1 hS2
  rw [hS1] at hS2; injection hS2 with hEq; subst hEq
  exact ⟨slotFwdRefines_refl s1, hWt.2 i ty s1 hTy hS1⟩

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
    have hNe : i ≠ id := nat_ne_of_beq_false hEq
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
    have hNe : i ≠ id := nat_ne_of_beq_false hEq
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
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' ∧
      checkVal v ty = true := by
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
      refine ⟨localsTgt, ?_, hInv, evalConstLit_checkVal hC⟩
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
            let ⟨hRef, hWt2⟩ := hAll p.localId t (.live (some v)) slot2 hTy hS1 hS2
            cases slot2 with
            | dead => cases hRef
            | live opt2 =>
              cases opt2 with
              | none => cases hRef
              | some v2 =>
                have hv : v = v2 := hRef
                subst hv
                refine ⟨localsTgt, ?_, hInv, hWt2⟩
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
              let ⟨hRef, hWt2⟩ := hAll p.localId t (.live (some v)) slot2 hTy hS1 hS2
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
                    (liveUninitSlot_wellTyped t), hWt2⟩
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
    let ⟨ty0, optVal, locs1⟩ := res
    rw [hS] at hEval; dsimp at hEval
    cases hPrim : isPrimitiveReadableTy ty0 with
    | false => rw [hPrim] at hEval; cases hEval
    | true =>
      rw [hPrim] at hEval; dsimp at hEval
      cases optVal with
      | none => cases hEval
      | some v0 =>
        injection hEval with hEq
        injection hEq with hV hL
        subst hV; subst hL
        let ⟨locs2, hT, hInv', _⟩ := evalOperandToSlot_fwd_eq hInv hS
        refine ⟨locs2, ?_, hInv'⟩
        dsimp [evalPrimitiveOperand]; rw [hT]; dsimp; rw [hPrim]; rfl

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
          let ⟨locs2, hT, hInv', _⟩ := evalOperandToSlot_fwd_eq hInv hS
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
                        | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEval
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEval
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hEval

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

private theorem evalTerminator_fwd_eq
    {bSrc bTgt : Body} {bbSrc bbTgt : BasicBlock}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hTerm : bbSrc.terminator = bbTgt.terminator)
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
  let ⟨_, hLen2, hAll⟩ := hInv
  refine ⟨?_, ?_⟩
  · intro s' hEv
    unfold evalTerminator at hEv
    cases hTm : bbSrc.terminator with
    | goto tgt =>
      rw [hTm] at hEv
      injection hEv with hEq; subst hEq
      refine ⟨tgt, fSrc.locals, fTgt.locals, rfl, ?_, hInv⟩
      unfold evalTerminator; rw [← hTerm, hTm]; rfl
    | return_ =>
      rw [hTm] at hEv; dsimp at hEv
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
          | live o => cases o <;> cases hEv
    | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
      rw [hTm] at hEv; cases hEv
    | switchInt discr targets =>
      rw [hTm] at hEv; dsimp at hEv
      cases hD : evalPrimitiveOperand bSrc.locals fSrc.locals discr with
      | error _ => rw [hD] at hEv; cases hEv
      | ok res =>
        let ⟨dv, locs1⟩ := res
        rw [hD] at hEv; dsimp at hEv
        let ⟨locs2, hD2, hInv1⟩ := evalPrimitiveOperand_fwd_eq hInv hD
        cases dv with
        | scalar sv =>
          dsimp at hEv
          cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
          | error _ => rw [hSw] at hEv; cases hEv
          | ok tgt =>
            rw [hSw] at hEv; injection hEv with hEq; subst hEq
            refine ⟨tgt, locs1, locs2, rfl, ?_, hInv1⟩
            unfold evalTerminator; rw [← hTerm, hTm, ← hLocEq]; dsimp
            rw [hD2]; dsimp; rw [hSw]; rfl
        | bool b =>
          dsimp at hEv
          cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
          | error _ => rw [hSw] at hEv; cases hEv
          | ok tgt =>
            rw [hSw] at hEv; injection hEv with hEq; subst hEq
            refine ⟨tgt, locs1, locs2, rfl, ?_, hInv1⟩
            unfold evalTerminator; rw [← hTerm, hTm, ← hLocEq]; dsimp
            rw [hD2]; dsimp; rw [hSw]; rfl
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
  · intro out hDone
    unfold evalTerminator at hDone
    cases hTm : bbSrc.terminator with
    | goto _ | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
      rw [hTm] at hDone; cases hDone
    | switchInt discr targets =>
      rw [hTm] at hDone; dsimp at hDone
      cases hD : evalPrimitiveOperand bSrc.locals fSrc.locals discr with
      | error _ => rw [hD] at hDone; cases hDone
      | ok res =>
        let ⟨dv, _⟩ := res
        rw [hD] at hDone; dsimp at hDone
        cases dv with
        | scalar sv =>
          dsimp at hDone
          cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;>
            rw [hSw] at hDone <;> cases hDone
        | bool b =>
          dsimp at hDone
          cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches <;>
            rw [hSw] at hDone <;> cases hDone
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hDone
    | return_ =>
      rw [hTm] at hDone; dsimp at hDone
      cases hC : bbSrc.cleanup with
      | true => rw [hC] at hDone; cases hDone
      | false =>
        rw [hC] at hDone; dsimp at hDone
        cases h0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
        | none => rw [h0] at hDone; cases hDone
        | some sl1 =>
          rw [h0] at hDone
          cases sl1 with
          | dead => cases hDone
          | live opt1 =>
            cases opt1 with
            | none => cases hDone
            | some retV =>
              injection hDone with hOut; subst hOut
              have hLt0 : 0 < bSrc.locals.length := by
                rw [← hInv.1]; exact getElem?_some_lt h0
              let ⟨ty0, hTy0⟩ := getElem?_some_of_lt bSrc.locals 0 hLt0
              let ⟨sl2, hS2⟩ := getElem?_some_of_lt fTgt.locals 0
                (by rw [hLen2]; exact hLt0)
              let ⟨hRef, _⟩ := hAll 0 ty0 (.live (some retV)) sl2 hTy0 h0 hS2
              cases sl2 with
              | dead => cases hRef
              | live opt2 =>
                cases opt2 with
                | none => cases hRef
                | some v2 =>
                  have hv : retV = v2 := hRef; subst hv
                  unfold evalTerminator; rw [← hTerm, hTm, ← hClean, hC]; dsimp
                  rw [hS2]

/-! ### Stage 4 Private Helpers — Layer C: `ConstAbsSlot` Abstract Domain
Soundness -/

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
    let ⟨_, v, hsl, _, hchk⟩ := h
    subst hsl
    exact hchk
  | liveUnknown =>
    let ⟨v, hsl, hchk⟩ := h
    subst hsl
    exact hchk
  | liveUninit =>
    let ⟨opt, hsl, hwt⟩ := h
    subst hsl
    exact hwt
  | dead => exact h

private theorem slotMatchesConst_not_bottom {ty : MirTy} {abs : ConstAbsSlot} {sl : LocalSlot}
    (h : SlotMatchesConst ty abs sl) : abs ≠ .bottom := by
  intro hEq
  subst hEq
  exact h

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

private theorem slotMatchesConst_implies_knownConst {ty : MirTy} {abs : ConstAbsSlot}
    {cTy : MirTy} {cLit : ConstLit} {sl : LocalSlot}
    (hMatch : SlotMatchesConst ty abs sl)
    (hImp : constSlotImplies abs (.knownConst cTy cLit) = true) :
    cTy = ty ∧
    ∃ v, sl = .live (some v) ∧
      evalConstLit ty cLit = .ok v ∧
      checkVal v ty = true := by
  have hM2 := slotMatchesConst_mono hImp hMatch
  exact hM2

private theorem slotMatchesConst_liveUninit (ty : MirTy) :
    SlotMatchesConst ty (liveUninitConstSlot ty) (liveUninitSlot ty) := by
  unfold liveUninitConstSlot
  cases hZ : isAlwaysInhabitedZst ty with
  | false =>
    rw [if_bool_false rfl]
    let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
    refine ⟨opt, hOpt, ?_⟩
    rw [← hOpt]
    exact liveUninitSlot_wellTyped ty
  | true =>
    rw [if_bool_true rfl]
    cases ty with
    | unit =>
      exact ⟨.unit, rfl, rfl⟩
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
    have hi : i = id := nat_beq_eq hEq
    subst hi
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
    dsimp [initConstEnvLoop, List.length]
    rw [ih (base + 1)]

private theorem initConstEnvLoop_getElem? (body : Body) (base : Nat) (tys : List MirTy)
    (i : Nat) (ty : MirTy)
    (hTy : Trusted.MirSemantics.getElem? tys i = some ty) :
    Trusted.MirSemantics.getElem? (initConstEnvLoop body base tys) i =
      some (initConstSlot body (base + i) ty) := by
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
    dsimp [Nat.beq]
    exact slotMatchesConst_liveUninit ty
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
      rw [hV]
      exact ⟨v, rfl, hChk⟩
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

private theorem valToVerifiedConstSlot_matches {dstTy : MirTy} {resVal : Val}
    (hChk : checkVal resVal dstTy = true) :
    SlotMatchesConst dstTy (valToVerifiedConstSlot dstTy resVal) (.live (some resVal)) := by
  unfold valToVerifiedConstSlot
  cases hCond : (!(isSupportedScalarOrUnitTy dstTy && checkVal resVal dstTy)) with
  | true =>
    rw [if_bool_true rfl]
    exact ⟨resVal, rfl, hChk⟩
  | false =>
    rw [if_bool_false rfl]
    have hCheckLit : ∀ lit : ConstLit,
        SlotMatchesConst dstTy
          (match evalConstLit dstTy lit with
           | .ok vCheck =>
             if valBeq vCheck resVal then .knownConst dstTy lit else .liveUnknown
           | .error _ => .liveUnknown)
          (.live (some resVal)) := by
      intro lit
      cases hEv : evalConstLit dstTy lit with
      | error _ => exact ⟨resVal, rfl, hChk⟩
      | ok vCheck =>
        dsimp only
        cases hBeq : valBeq vCheck resVal with
        | false =>
          rw [if_bool_false rfl]
          exact ⟨resVal, rfl, hChk⟩
        | true =>
          rw [if_bool_true rfl]
          have hvEq := valBeq_eq hBeq
          subst hvEq
          exact ⟨rfl, vCheck, rfl, hEv, hChk⟩
    cases resVal with
    | scalar sv =>
      dsimp only
      cases sv.wf with
      | false => exact ⟨.scalar sv, rfl, hChk⟩
      | true => exact hCheckLit (.scalar sv.bits)
    | bool b =>
      cases b with
      | false => exact hCheckLit (.scalar (BitVec.ofNat 128 0))
      | true => exact hCheckLit (.scalar (BitVec.ofNat 128 1))
    | unit => exact hCheckLit .zeroSized
    | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
      exact ⟨_, rfl, hChk⟩

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
      injection hPr with hTyEq hLitEq
      subst hTyEq; subst hLitEq
      let ⟨_, _, v, hEvC, hChk⟩ := validTypedConstOperand_elim hVal
      dsimp [evalOperandToSlot] at hEval
      rw [hEvC] at hEval
      injection hEval with hEq
      injection hEq with hSrc hR
      injection hR with hOpt _
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
              injection hPr with hOpTy hLitEq
              subst hOpTy; subst hLitEq
              dsimp [evalOperandToSlot] at hEval
              rw [hProj, hTy] at hEval; dsimp at hEval
              cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
              | none => rw [hSl] at hEval; cases hEval
              | some sl =>
                rw [hSl] at hEval
                let ⟨_, v, hsl, hEvL, hChk⟩ := hAll p.localId ty (.knownConst cTy cLit) sl hTy hAbs hSl
                subst hsl
                injection hEval with hEq
                injection hEq with hSrc hR
                injection hR with hOpt _
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
              injection hPr with hOpTy hLitEq
              subst hOpTy; subst hLitEq
              dsimp [evalOperandToSlot] at hEval
              rw [hProj, hTy] at hEval; dsimp at hEval
              cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
              | none => rw [hSl] at hEval; cases hEval
              | some sl =>
                rw [hSl] at hEval
                let ⟨_, v, hsl, hEvL, hChk⟩ := hAll p.localId ty (.knownConst cTy cLit) sl hTy hAbs hSl
                subst hsl
                dsimp at hEval
                cases hSet : setElem? locals p.localId (liveUninitSlot ty) with
                | none => rw [hSet] at hEval; cases hEval
                | some _ =>
                  rw [hSet] at hEval
                  injection hEval with hEq
                  injection hEq with hSrc hR
                  injection hR with hOpt _
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
      subst hLoc
      exact hMatch
  | copy p =>
    dsimp [evalOperandToSlot] at hEval
    cases hP : p.projection.isEmpty with
    | false => rw [hP] at hEval; cases hEval
    | true =>
      rw [hP] at hEval; dsimp at hEval
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hEval; cases hEval
      | some t =>
        rw [hTy] at hEval
        cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hSl] at hEval; cases hEval
        | some sl =>
          rw [hSl] at hEval
          cases sl with
          | dead => cases hEval
          | live _ =>
            injection hEval with h1; injection h1 with _ h2; injection h2 with _ hLoc
            subst hLoc
            exact hMatch
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
    let ⟨ty0, optVal, locs1⟩ := res
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

private theorem evalPrimitiveOperand_const_sound {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {opTy : MirTy} {lit : ConstLit} {v : Val}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hConst : evalOperandConst? bodyLocals env opnd = some (opTy, lit))
    (hEval : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    isPrimitiveReadableTy opTy = true ∧
    evalConstLit opTy lit = .ok v ∧
    LocalsMatchConstEnv bodyLocals (deinitMoveOperandConst bodyLocals env opnd) locals' := by
  dsimp [evalPrimitiveOperand] at hEval
  cases hS : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [hS] at hEval; cases hEval
  | ok res =>
    let ⟨srcTy, optVal, locs1⟩ := res
    rw [hS] at hEval; dsimp at hEval
    let ⟨hTyEq, v', hOptEq, hEvL, _⟩ := evalOperandConst?_sound hMatch hConst hS
    rw [hTyEq] at hEval; subst hOptEq
    cases hP : isPrimitiveReadableTy opTy with
    | false => rw [hP] at hEval; cases hEval
    | true =>
      rw [hP] at hEval; dsimp at hEval
      injection hEval with h1; injection h1 with hv hl
      subst hv; subst hl
      exact ⟨rfl, hEvL, deinitMoveOperandConst_sound hMatch hS⟩

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
      let ⟨srcTy, optVal, locs1⟩ := res
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
          have hDeinit := deinitMoveOperandConst_sound hMatch hS
          refine ⟨hDeinit, ?_⟩
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
      let ⟨ov, locs1⟩ := resO
      rw [hEO] at hEval; dsimp at hEval
      cases hUn : evalUnOp uop ov with
      | error _ => rw [hUn] at hEval; cases hEval
      | ok resV =>
        rw [hUn] at hEval
        injection hEval with h1; injection h1 with hv hl
        rw [← hv] at hChk; rw [← hv]; subst hl
        refine ⟨deinitMovePrimitiveOperand_sound hMatch hEO, ?_⟩
        dsimp [rvalueConstSlot]
        cases hC : evalOperandConst? bodyLocals env opnd with
        | none => exact ⟨resV, rfl, hChk⟩
        | some pr =>
          let ⟨opTy, lit⟩ := pr
          let ⟨hPrim, hEvL, _⟩ := evalPrimitiveOperand_const_sound hMatch hC hEO
          dsimp only
          rw [hPrim, if_bool_false (rfl : (!true) = false)]
          rw [hEvL]; dsimp only
          rw [hUn]
          exact valToVerifiedConstSlot_matches hChk
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
        let ⟨rvv, locs2⟩ := resR
        rw [hER] at hEval; dsimp at hEval
        have hMatch2 := deinitMovePrimitiveOperand_sound hMatch1 hER
        cases hBin : evalBinOp bop lv rvv with
        | error _ => rw [hBin] at hEval; cases hEval
        | ok resV =>
          rw [hBin] at hEval
          injection hEval with h1; injection h1 with hv hl
          rw [← hv] at hChk; rw [← hv]; subst hl
          refine ⟨hMatch2, ?_⟩
          dsimp [rvalueConstSlot]
          cases hCL : evalOperandConst? bodyLocals env lhs with
          | none => exact ⟨resV, rfl, hChk⟩
          | some prL =>
            let ⟨lTy, lLit⟩ := prL
            cases hCR : evalOperandConst? bodyLocals (deinitMoveOperandConst bodyLocals env lhs) rhs with
            | none => exact ⟨resV, rfl, hChk⟩
            | some prR =>
              let ⟨rTy, rLit⟩ := prR
              let ⟨hPrimL, hEvLL, _⟩ := evalPrimitiveOperand_const_sound hMatch hCL hEL
              let ⟨hPrimR, hEvRL, _⟩ := evalPrimitiveOperand_const_sound hMatch1 hCR hER
              dsimp only
              rw [hPrimL, hPrimR, if_bool_false (rfl : (!(true && true)) = false)]
              rw [hEvLL, hEvRL]; dsimp only
              rw [hBin]
              exact valToVerifiedConstSlot_matches hChk
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
    injection h with hEq
    exact Or.inl hEq.symm
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
    injection h with hEq
    exact Or.inl hEq.symm
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
                    let ⟨_, hb⟩ := checkVal_bool_iff.mp hChk
                    cases hb
                  | inr hI =>
                    let ⟨w, s, hIS⟩ := hI
                    subst hIS
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
                  cases hCond : (isPrimitiveReadableTy (.int sv.width sv.signed) &&
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
                        | mk sw ss sb =>
                          dsimp at hBitsEq; subst hBitsEq; rfl
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
                    let ⟨_, _, hIS⟩ := hI
                    subst hIS
                    let ⟨_, hsc, _⟩ := checkVal_int_iff.mp hChk
                    cases hsc
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
  rw [nat_lt_blt hLt] at hEdge
  dsimp at hEdge
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
            subst hOw
            exact checkConstEdge_sound hAfter hOwEdge hLt
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
            subst hOw
            exact checkConstEdge_sound hAfter hOwEdge hLt
          | inr hBr =>
            let ⟨i, caseBits, hGetBr, hEvC⟩ := hBr
            have hBrEdge := list_all_getElem? hBrAll hGetBr
            dsimp only at hBrEdge
            have hRefMatch := refineSwitchBranchEnv_bool_sound hMatch hD hEvC
            exact checkConstEdge_sound hRefMatch hBrEdge hLt
      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

/-! ### Stage 4 Private Helpers — Layer D1: `ConstPropCopy` & Forward
`ConstPropMove` -/

private theorem checkConstPropCopyBlocksLoop_get {bSrc bTgt : Body}
    {cert : BodyConstCert} {base k : Nat} {rest : List BasicBlock} {bbSrc : BasicBlock}
    (hLoop : checkConstPropCopyBlocksLoop bSrc bTgt cert base rest = true)
    (hGet : Trusted.MirSemantics.getElem? rest k = some bbSrc) :
    checkConstPropCopyBlock bSrc bTgt cert (base + k) bbSrc = true := by
  induction rest generalizing base k with
  | nil => cases hGet
  | cons hd tl ih =>
    dsimp [checkConstPropCopyBlocksLoop] at hLoop
    let ⟨hHere, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hGet with hEq; subst hEq
      rw [Nat.add_zero]
      exact hHere
    | succ m =>
      have hRec := ih hTail hGet
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hRec
      exact hRec

private theorem checkConstPropMoveBlocksLoop_get {bSrc bTgt : Body}
    {cert : BodyConstCert} {base k : Nat} {rest : List BasicBlock} {bbSrc : BasicBlock}
    (hLoop : checkConstPropMoveBlocksLoop bSrc bTgt cert base rest = true)
    (hGet : Trusted.MirSemantics.getElem? rest k = some bbSrc) :
    checkConstPropMoveBlock bSrc bTgt cert (base + k) bbSrc = true := by
  induction rest generalizing base k with
  | nil => cases hGet
  | cons hd tl ih =>
    dsimp [checkConstPropMoveBlocksLoop] at hLoop
    let ⟨hHere, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hGet with hEq; subst hEq
      rw [Nat.add_zero]
      exact hHere
    | succ m =>
      have hRec := ih hTail hGet
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hRec
      exact hRec

private theorem evalOperandToSlot_constPropCopy {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals : List LocalSlot}
    {opSrc opTgt : Operand}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hChk : checkConstPropCopyOperand bodyLocals env opSrc opTgt = true) :
    evalOperandToSlot bodyLocals locals opSrc =
      evalOperandToSlot bodyLocals locals opTgt := by
  cases opSrc with
  | move p1 =>
    cases opTgt with
    | move p2 => rw [@operandEq_eq (.move p1) (.move p2) hChk]
    | _ => cases hChk
  | constant c1 =>
    cases opTgt with
    | constant c2 => rw [@operandEq_eq (.constant c1) (.constant c2) hChk]
    | _ => cases hChk
  | copy p =>
    cases opTgt with
    | copy p2 => rw [@operandEq_eq (.copy p) (.copy p2) hChk]
    | move _ => cases hChk
    | constant c =>
      dsimp [checkConstPropCopyOperand] at hChk
      let ⟨hProj, hRest⟩ := bool_and_true hChk
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hRest; cases hRest
      | some ty =>
        rw [hTy] at hRest
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hRest; cases hRest
        | some abs =>
          rw [hAbs] at hRest; dsimp at hRest
          let ⟨hValC, hImp⟩ := bool_and_true hRest
          let ⟨hcTy, _, vc, hEvC, _⟩ := validTypedConstOperand_elim hValC
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId
            (by rw [hMatch.2.1]; exact getElem?_some_lt hTy)
          have hM := hMatch.2.2 p.localId ty abs sl hTy hAbs hSl
          let ⟨_, v, hsl, hEvL, _⟩ := slotMatchesConst_implies_knownConst hM hImp
          subst hsl
          rw [hEvC] at hEvL; injection hEvL with hv; subst hv
          dsimp [evalOperandToSlot]
          rw [hProj, if_bool_false (rfl : (!true) = false), hTy, hSl]
          rw [hcTy, hEvC]

private theorem evalPrimitiveOperand_constPropCopy {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals : List LocalSlot}
    {opSrc opTgt : Operand}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hChk : checkConstPropCopyOperand bodyLocals env opSrc opTgt = true) :
    evalPrimitiveOperand bodyLocals locals opSrc =
      evalPrimitiveOperand bodyLocals locals opTgt := by
  unfold evalPrimitiveOperand
  rw [evalOperandToSlot_constPropCopy hMatch hChk]

private theorem evalRvalue_constPropCopy {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {locals : List LocalSlot}
    {dstTy : MirTy} {rvSrc rvTgt : Rvalue}
    (hMatch : LocalsMatchConstEnv bodyLocals env locals)
    (hChk : checkConstPropCopyRvalue bodyLocals env rvSrc rvTgt = true) :
    evalRvalue bodyLocals locals dstTy rvSrc =
      evalRvalue bodyLocals locals dstTy rvTgt := by
  cases rvSrc with
  | use o1 =>
    cases rvTgt with
    | use o2 =>
      dsimp [checkConstPropCopyRvalue] at hChk
      dsimp [evalRvalue]
      rw [evalOperandToSlot_constPropCopy hMatch hChk]
    | _ => cases hChk
  | unaryOp uop1 o1 =>
    cases rvTgt with
    | unaryOp uop2 o2 =>
      dsimp [checkConstPropCopyRvalue] at hChk
      let ⟨hOp, hO⟩ := bool_and_true hChk
      rw [unOpEq_eq hOp]
      dsimp [evalRvalue]
      rw [evalPrimitiveOperand_constPropCopy hMatch hO]
    | _ => cases hChk
  | binaryOp bop1 l1 r1 =>
    cases rvTgt with
    | binaryOp bop2 l2 r2 =>
      dsimp [checkConstPropCopyRvalue] at hChk
      let ⟨h12, hR⟩ := bool_and_true hChk
      let ⟨hOp, hL⟩ := bool_and_true h12
      rw [binOpEq_eq hOp]
      dsimp [evalRvalue]
      rw [← evalPrimitiveOperand_constPropCopy hMatch hL]
      cases hEL : evalPrimitiveOperand bodyLocals locals l1 with
      | error _ => rfl
      | ok resL =>
        let ⟨lv, locs1⟩ := resL
        dsimp only
        have hMatch1 := deinitMovePrimitiveOperand_sound hMatch hEL
        rw [evalPrimitiveOperand_constPropCopy hMatch1 hR]
    | _ => cases hChk
  | discriminant p1 =>
    rw [@rvalueEq_eq (.discriminant p1) rvTgt hChk]
  | ref m1 p1 =>
    rw [@rvalueEq_eq (.ref m1 p1) rvTgt hChk]
  | addressOf m1 p1 =>
    rw [@rvalueEq_eq (.addressOf m1 p1) rvTgt hChk]
  | aggregateTuple fs1 =>
    rw [@rvalueEq_eq (.aggregateTuple fs1) rvTgt hChk]
  | unsupported =>
    rw [@rvalueEq_eq .unsupported rvTgt hChk]

private theorem evalTerminator_constPropCopy {bSrc bTgt : Body}
    {bbSrc bbTgt : BasicBlock} {env : List ConstAbsSlot}
    {frame : FrameState} {cm : CallerMemory}
    (hLocs : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hMatch : LocalsMatchConstEnv bSrc.locals env frame.locals)
    (hChk : checkConstPropCopyTerminator bSrc.locals env
      bbSrc.terminator bbTgt.terminator = true) :
    evalTerminator bSrc bbSrc frame cm = evalTerminator bTgt bbTgt frame cm := by
  cases hT1 : bbSrc.terminator with
  | switchInt d1 ts1 =>
    rw [hT1] at hChk
    cases hT2 : bbTgt.terminator with
    | switchInt d2 ts2 =>
      rw [hT2] at hChk
      dsimp [checkConstPropCopyTerminator] at hChk
      let ⟨hD, hTs⟩ := bool_and_true hChk
      have hTsEq := switchTargetsEq_eq hTs
      subst hTsEq
      unfold evalTerminator
      rw [hT1, hT2, ← hLocs]
      dsimp only
      rw [evalPrimitiveOperand_constPropCopy hMatch hD]
    | _ =>
      rw [hT2] at hChk
      cases hChk
  | goto t1 =>
    rw [hT1] at hChk
    exact evalTerminator_eq_of_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq (.goto t1) bbTgt.terminator hChk)
  | return_ =>
    rw [hT1] at hChk
    exact evalTerminator_eq_of_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq .return_ bbTgt.terminator hChk)
  | unreachable =>
    rw [hT1] at hChk
    exact evalTerminator_eq_of_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq .unreachable bbTgt.terminator hChk)
  | unwindResume =>
    rw [hT1] at hChk
    exact evalTerminator_eq_of_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq .unwindResume bbTgt.terminator hChk)
  | assert c1 e1 m1 t1 u1 =>
    rw [hT1] at hChk
    exact evalTerminator_eq_of_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq (.assert c1 e1 m1 t1 u1) bbTgt.terminator hChk)
  | call f1 as1 d1 t1 u1 =>
    rw [hT1] at hChk
    exact evalTerminator_eq_of_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq (.call f1 as1 d1 t1 u1) bbTgt.terminator hChk)
  | unsupported =>
    rw [hT1] at hChk
    exact evalTerminator_eq_of_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq .unsupported bbTgt.terminator hChk)

private theorem isConstPropCopyProgram_initState_eq {pSrc pTgt : Program}
    {cert : ProgramConstCert}
    (hRel : isConstPropCopyProgram pSrc pTgt = true)
    (hCert : checkConstPropCopyProgram cert pSrc pTgt = true)
    (q : Query) :
    initState pSrc q = initState pTgt q := by
  let ⟨hHdr, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLen, hCertBodies⟩ := bool_and_true hCert
  let ⟨_, hCertAt, _⟩ := listRel_zip_left_rel (nat_beq_eq hCertLen) hCertBodies
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodiesRel
  · intro b1 hB1
    let ⟨b2, hB2, hBRel⟩ := listRel_getElem?_left hBodiesRel hB1
    let ⟨cBody, b2', _, hB2', hBCert⟩ := hCertAt pSrc.entryDefId b1 hB1
    rw [hB2] at hB2'; injection hB2' with hEqB; subst hEqB
    rw [hEnt] at hB2
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨h123, _⟩ := bool_and_true hBCert
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hPres, _⟩ := bool_and_true h12
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨b2, hB2, hBHdr, list_isEmpty_eq_of_length (listRel_length hBBsRel),
           hBounds, initLocalsLoop_eq_of_preservesStorage q.args hBHdr hPres⟩

private noncomputable def ConstPropCopyFrameInv (pSrc pTgt : Program)
    (cert : ProgramConstCert) (s : State) : Prop :=
  ∃ frame bSrc bTgt cBody,
    s.frames = [frame] ∧
    Trusted.MirSemantics.getElem? pSrc.bodies frame.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies frame.defId = some bTgt ∧
    Trusted.MirSemantics.getElem? cert frame.defId = some cBody ∧
    isConstPropCopyBody bSrc bTgt = true ∧
    checkConstPropCopyBody cBody bSrc bTgt = true ∧
    LocalsWellTyped bSrc.locals frame.locals ∧
    (bSrc.basicBlocks.length ≤ frame.blockIdx ∨
      ∃ bbSrc bbTgt entryEnv curEnv exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks frame.blockIdx = some bbTgt ∧
        Trusted.MirSemantics.getElem? cBody frame.blockIdx = some (some entryEnv) ∧
        frame.stmtIdx ≤ bbSrc.statements.length ∧
        LocalsMatchConstEnv bSrc.locals curEnv frame.locals ∧
        stepConstPropCopyCertStmts bSrc.locals curEnv
          (bbSrc.statements.drop frame.stmtIdx)
          (bbTgt.statements.drop frame.stmtIdx) = some exitEnv ∧
        checkConstPropCopyTerminator bSrc.locals exitEnv
          bbSrc.terminator bbTgt.terminator = true ∧
        checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length
          cBody exitEnv bbSrc.terminator = true)

private noncomputable def checkConstPropCopyStmtPair (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (sSrc sTgt : StatementKind) : Bool :=
  match sSrc, sTgt with
  | .assign d₁ rv₁, .assign d₂ rv₂ =>
    placeEq d₁ d₂ && d₁.projection.isEmpty &&
      checkConstPropCopyRvalue bodyLocals env rv₁ rv₂
  | _, _ => stmtEq sSrc sTgt

private theorem stepConstPropCopyCertStmts_cons_elim {bodyLocals : List MirTy}
    {env exitEnv : List ConstAbsSlot} {sSrc sTgt : StatementKind}
    {restSrc restTgt : List StatementKind}
    (h : stepConstPropCopyCertStmts bodyLocals env (sSrc :: restSrc) (sTgt :: restTgt) = some exitEnv) :
    checkConstPropCopyStmtPair bodyLocals env sSrc sTgt = true ∧
    ∃ nextEnv,
      stepPlainStmtConst bodyLocals env sSrc = some nextEnv ∧
      stepConstPropCopyCertStmts bodyLocals nextEnv restSrc restTgt = some exitEnv := by
  have hFold :
      (if !(checkConstPropCopyStmtPair bodyLocals env sSrc sTgt) then none
       else
         match stepPlainStmtConst bodyLocals env sSrc with
         | none => none
         | some env' => stepConstPropCopyCertStmts bodyLocals env' restSrc restTgt) =
        some exitEnv := by
    cases sSrc <;> cases sTgt <;> exact h
  cases hOk : checkConstPropCopyStmtPair bodyLocals env sSrc sTgt with
  | false =>
    rw [hOk, if_bool_true (rfl : (!false) = true)] at hFold
    cases hFold
  | true =>
    rw [hOk, if_bool_false (rfl : (!true) = false)] at hFold
    cases hPlain : stepPlainStmtConst bodyLocals env sSrc with
    | none => rw [hPlain] at hFold; cases hFold
    | some nextEnv =>
      rw [hPlain] at hFold
      exact ⟨rfl, nextEnv, rfl, hFold⟩

private theorem constPropCopy_block_entry {bSrc bTgt : Body} {cBody : BodyConstCert}
    {bbIdx : BasicBlockId} {tgtEnv : List ConstAbsSlot} {locals : List LocalSlot}
    (hBRel : isConstPropCopyBody bSrc bTgt = true)
    (hBCert : checkConstPropCopyBody cBody bSrc bTgt = true)
    (hLt : bbIdx < bSrc.basicBlocks.length)
    (hCGet : Trusted.MirSemantics.getElem? cBody bbIdx = some (some tgtEnv))
    (hMatch : LocalsMatchConstEnv bSrc.locals tgtEnv locals) :
    ∃ bbSrc bbTgt exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt ∧
      0 ≤ bbSrc.statements.length ∧
      LocalsMatchConstEnv bSrc.locals tgtEnv locals ∧
      stepConstPropCopyCertStmts bSrc.locals tgtEnv
        (bbSrc.statements.drop 0) (bbTgt.statements.drop 0) = some exitEnv ∧
      checkConstPropCopyTerminator bSrc.locals exitEnv
        bbSrc.terminator bbTgt.terminator = true ∧
      checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length
        cBody exitEnv bbSrc.terminator = true := by
  let ⟨_, hBBsRel⟩ := bool_and_true hBRel
  let ⟨_, hLoop⟩ := bool_and_true hBCert
  let ⟨bbSrc, hBBSrc⟩ := getElem?_some_of_lt bSrc.basicBlocks bbIdx hLt
  let ⟨bbTgt, hBBTgt, _⟩ := listRel_getElem?_left hBBsRel hBBSrc
  have hBlkCert := checkConstPropCopyBlocksLoop_get hLoop hBBSrc
  rw [Nat.zero_add] at hBlkCert
  unfold checkConstPropCopyBlock at hBlkCert
  rw [hCGet, hBBTgt] at hBlkCert; dsimp at hBlkCert
  let ⟨h12, hStOpt⟩ := bool_and_true hBlkCert
  cases hStepS : stepConstPropCopyCertStmts bSrc.locals tgtEnv bbSrc.statements bbTgt.statements with
  | none => rw [hStepS] at hStOpt; cases hStOpt
  | some exitEnv =>
    rw [hStepS] at hStOpt; dsimp at hStOpt
    let ⟨hTermC, hEdgesC⟩ := bool_and_true hStOpt
    exact ⟨bbSrc, bbTgt, exitEnv, hBBSrc, hBBTgt, Nat.zero_le _, hMatch, hStepS, hTermC, hEdgesC⟩

private theorem constPropCopy_query_iff {pSrc pTgt : Program} {cert : ProgramConstCert}
    (hRel : isConstPropCopyProgram pSrc pTgt = true)
    (hCert : checkConstPropCopyProgram cert pSrc pTgt = true)
    (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLen, hCertBodies⟩ := bool_and_true hCert
  let ⟨_, hCertAt, _⟩ := listRel_zip_left_rel (nat_beq_eq hCertLen) hCertBodies
  apply lockstep_inv_query_iff
    (Inv := ConstPropCopyFrameInv pSrc pTgt cert)
    (isConstPropCopyProgram_initState_eq hRel hCert q)
  · intro s₀ hOk
    let ⟨_, _, bSrc, hBSrc, hNotEmpty, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodiesRel hBSrc
    let ⟨cBody, bTgt', hCBody, hBTgt', hBCert⟩ := hCertAt pSrc.entryDefId bSrc hBSrc
    rw [hBTgt] at hBTgt'; injection hBTgt' with hEqB; subst hEqB
    let ⟨h123, _⟩ := bool_and_true hBCert
    let ⟨_, hEntryOk⟩ := bool_and_true h123
    rw [hNotEmpty, if_bool_false rfl] at hEntryOk
    cases hC0 : Trusted.MirSemantics.getElem? cBody 0 with
    | none => rw [hC0] at hEntryOk; cases hEntryOk
    | some opt0 =>
      rw [hC0] at hEntryOk
      cases opt0 with
      | none => cases hEntryOk
      | some env₀ =>
        have hMatch0 := localsMatchConstEnv_mono hEntryOk (initConstEnvLoop_matches hArgs)
        have hPos := list_pos_of_isEmpty_false hNotEmpty
        let ⟨bbSrc, bbTgt, exitEnv, hBBS, hBBT, hLe0, hM0, hSt0, hTm0, hEd0⟩ :=
          constPropCopy_block_entry hBRel hBCert hPos hC0 hMatch0
        exact ⟨_, bSrc, bTgt, cBody, rfl, hBSrc, hBTgt, hCBody, hBRel, hBCert,
               localsMatchConstEnv_wt hMatch0,
               Or.inr ⟨bbSrc, bbTgt, env₀, env₀, exitEnv, hBBS, hBBT, hC0, hLe0, hM0, hSt0, hTm0, hEd0⟩⟩
  · intro s hInv
    let ⟨frame, bSrc, bTgt, cBody, hFs, hBSrc, hBTgt, hCBody, hBRel, hBCert, hWt, hBlkInv⟩ := hInv
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    cases s with
    | mk fs cm =>
      dsimp at hFs; subst hFs
      cases hBlkInv with
      | inl hOob =>
        have hNoneS := getElem?_none_of_ge hOob
        have hNoneT := (listRel_getElem?_none_iff frame.blockIdx hBBsRel).mp hNoneS
        have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
            evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
          unfold evalStep; dsimp; rw [hBSrc, hBTgt]; dsimp; rw [hNoneS, hNoneT]
        refine ⟨hEvEq, ?_⟩
        intro s' hStepS
        unfold evalStep at hStepS; dsimp at hStepS
        rw [hBSrc] at hStepS; dsimp at hStepS; rw [hNoneS] at hStepS; cases hStepS
      | inr hIn =>
        let ⟨bbSrc, bbTgt, entryEnv, curEnv, exitEnv, hBBS, hBBT, hCGet, hIdxLe, hMatch, hStDrop, hTermC, hEdgesC⟩ := hIn
        have hRelBB : isConstPropCopyBlock bbSrc bbTgt = true := by
          let ⟨bbT', hBBT', hR⟩ := listRel_getElem?_left hBBsRel hBBS
          rw [hBBT] at hBBT'; injection hBBT' with hE; subst hE; exact hR
        let ⟨hBB12, _⟩ := bool_and_true hRelBB
        let ⟨hCleanB, hStmtsRel⟩ := bool_and_true hBB12
        have hCleanEq := bool_beq_eq hCleanB
        have hLenStEq := listRel_length hStmtsRel
        cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements frame.stmtIdx with
        | some sSrc =>
          let ⟨sTgt, hStT, _⟩ := listRel_getElem?_left hStmtsRel hStS
          rw [drop_eq_cons_of_getElem? hStS, drop_eq_cons_of_getElem? hStT] at hStDrop
          let ⟨hOk, nextEnv, hPlain, hStRest⟩ := stepConstPropCopyCertStmts_cons_elim hStDrop
          have hEvStmtEq : evalStatement bSrc frame cm sSrc = evalStatement bTgt frame cm sTgt := by
            cases sSrc with
            | assign d1 rv1 =>
              cases sTgt with
              | assign d2 rv2 =>
                dsimp [checkConstPropCopyStmtPair] at hOk
                let ⟨h12, hRvC⟩ := bool_and_true hOk
                let ⟨hPEq, _⟩ := bool_and_true h12
                rw [placeEq_eq hPEq]
                unfold evalStatement; dsimp only
                rw [← hLocEq]
                cases d2.projection.isEmpty with
                | false => rfl
                | true =>
                  rw [if_bool_false (rfl : (!true) = false),
                      if_bool_false (rfl : (!true) = false)]
                  cases Trusted.MirSemantics.getElem? bSrc.locals d2.localId with
                  | none => rfl
                  | some dstTy =>
                    dsimp only
                    rw [evalRvalue_constPropCopy hMatch hRvC]
              | nop | storageLive _ | storageDead _ | unsupported =>
                dsimp [checkConstPropCopyStmtPair] at hOk
                cases hOk
            | nop =>
              dsimp [checkConstPropCopyStmtPair] at hOk
              rw [← @stmtEq_eq .nop sTgt hOk]
              exact evalStatement_eq_of_same frame cm .nop hLocEq
            | storageLive id =>
              dsimp [checkConstPropCopyStmtPair] at hOk
              rw [← @stmtEq_eq (.storageLive id) sTgt hOk]
              exact evalStatement_eq_of_same frame cm (.storageLive id) hLocEq
            | storageDead id =>
              dsimp [checkConstPropCopyStmtPair] at hOk
              rw [← @stmtEq_eq (.storageDead id) sTgt hOk]
              exact evalStatement_eq_of_same frame cm (.storageDead id) hLocEq
            | unsupported =>
              dsimp [checkConstPropCopyStmtPair] at hOk
              rw [← @stmtEq_eq .unsupported sTgt hOk]
              exact evalStatement_eq_of_same frame cm .unsupported hLocEq
          have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
              evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
            unfold evalStep; dsimp; rw [hBSrc, hBTgt]; dsimp
            rw [hBBS, hBBT]; dsimp; rw [hStS, hStT]; dsimp
            exact hEvStmtEq
          refine ⟨hEvEq, ?_⟩
          intro s' hStepS
          unfold evalStep at hStepS; dsimp at hStepS
          rw [hBSrc] at hStepS; dsimp at hStepS
          rw [hBBS] at hStepS; dsimp at hStepS
          rw [hStS] at hStepS; dsimp at hStepS
          let ⟨locs', hEqS', hNextMatch⟩ := stepPlainStmtConst_sound hMatch hPlain hStepS
          subst hEqS'
          have hNextLe : frame.stmtIdx + 1 ≤ bbSrc.statements.length :=
            getElem?_some_lt hStS
          exact ⟨_, bSrc, bTgt, cBody, rfl, hBSrc, hBTgt, hCBody, hBRel, hBCert,
                 localsMatchConstEnv_wt hNextMatch,
                 Or.inr ⟨bbSrc, bbTgt, entryEnv, nextEnv, exitEnv,
                         hBBS, hBBT, hCGet, hNextLe, hNextMatch, hStRest, hTermC, hEdgesC⟩⟩
        | none =>
          have hStT := (listRel_getElem?_none_iff frame.stmtIdx hStmtsRel).mp hStS
          have hGe : bbSrc.statements.length ≤ frame.stmtIdx := by
            cases Nat.lt_or_ge frame.stmtIdx bbSrc.statements.length with
            | inr hge => exact hge
            | inl hlt =>
              let ⟨x, hx⟩ := getElem?_some_of_lt bbSrc.statements frame.stmtIdx hlt
              rw [hStS] at hx; cases hx
          have hIdxEq : frame.stmtIdx = bbSrc.statements.length :=
            Nat.le_antisymm hIdxLe hGe
          have hIdxEqT : frame.stmtIdx = bbTgt.statements.length := by
            rw [← hLenStEq]; exact hIdxEq
          rw [hIdxEq, drop_length_nil, hLenStEq, drop_length_nil] at hStDrop
          dsimp [stepConstPropCopyCertStmts] at hStDrop
          injection hStDrop with hCurExit
          subst hCurExit
          have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
              evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
            unfold evalStep; dsimp; rw [hBSrc, hBTgt]; dsimp
            rw [hBBS, hBBT]; dsimp; rw [hStS, hStT]; dsimp
            rw [nat_beq_of_eq hIdxEq, nat_beq_of_eq hIdxEqT]
            rw [if_bool_true rfl, if_bool_true rfl]
            exact evalTerminator_constPropCopy hLocEq hCleanEq hMatch hTermC
          refine ⟨hEvEq, ?_⟩
          intro s' hStepS
          unfold evalStep at hStepS; dsimp at hStepS
          rw [hBSrc] at hStepS; dsimp at hStepS
          rw [hBBS] at hStepS; dsimp at hStepS
          rw [hStS] at hStepS; dsimp at hStepS
          rw [nat_beq_of_eq hIdxEq, if_bool_true rfl] at hStepS
          let ⟨target, locs', hEqS', hWt', hTargetCert⟩ :=
            evalTerminator_constEdges_sound hMatch hEdgesC hStepS
          subst hEqS'
          refine ⟨_, bSrc, bTgt, cBody, rfl, hBSrc, hBTgt, hCBody, hBRel, hBCert, hWt', ?_⟩
          cases Nat.lt_or_ge target bSrc.basicBlocks.length with
          | inr hGeT => exact Or.inl hGeT
          | inl hLtT =>
            let ⟨tgtEnv, hCTgt, hTgtMatch⟩ := hTargetCert hLtT
            let ⟨bbSrc2, bbTgt2, exitEnv2, hBBS2, hBBT2, hLe2, hM2, hSt2, hTm2, hEd2⟩ :=
              constPropCopy_block_entry hBRel hBCert hLtT hCTgt hTgtMatch
            exact Or.inr ⟨bbSrc2, bbTgt2, tgtEnv, tgtEnv, exitEnv2,
                          hBBS2, hBBT2, hCTgt, hLe2, hM2, hSt2, hTm2, hEd2⟩

private theorem constPropCopy_certified_bidirectional_iff_priv
    (pSrc pTgt : Program) (cert : ProgramConstCert)
    (hRel : isConstPropCopyProgram pSrc pTgt = true)
    (hCert : checkConstPropCopyProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hHdr, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLen, hCertBodies⟩ := bool_and_true hCert
  let ⟨_, hCertAt, _⟩ := listRel_zip_left_rel (nat_beq_eq hCertLen) hCertBodies
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodiesRel hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨cBody, bTgt'', _, hBT'', hBCert⟩ := hCertAt defId bSrc hBS
    rw [hBT] at hBT''; injection hBT'' with hEqB2; subst hEqB2
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨h123, _⟩ := bool_and_true hBCert
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hPres, _⟩ := bool_and_true h12
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨hBHdr, list_isEmpty_eq_of_length (listRel_length hBBsRel), hBounds⟩
  · intro q
    exact constPropCopy_query_iff hRel hCert q
  · intro defId args
    have hRelEntry : isConstPropCopyProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodiesRel
    exact (constPropCopy_query_iff hRelEntry hCert { args := args }).1

/-! #### Theorem 1b: Forward `ConstPropMove` Refinement
(`codegen_constPropMove_certified_refines`) -/

private theorem evalOperandToSlot_constPropMove_fwd {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {opSrc opTgt : Operand} {ty : MirTy} {v : Val}
    (hMatch : LocalsMatchConstEnv bodyLocals env localsSrc)
    (hFwd : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hChk : checkConstPropMoveOperand bodyLocals env opSrc opTgt = true)
    (hEval : evalOperandToSlot bodyLocals localsSrc opSrc = .ok (ty, some v, localsSrc')) :
    ∃ localsTgt',
      evalOperandToSlot bodyLocals localsTgt opTgt = .ok (ty, some v, localsTgt') ∧
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' := by
  cases opSrc with
  | copy p1 =>
    cases opTgt with
    | copy p2 =>
      rw [← @operandEq_eq (.copy p1) (.copy p2) hChk]
      let ⟨l2, hE2, hF2, _⟩ := evalOperandToSlot_fwd_eq hFwd hEval
      exact ⟨l2, hE2, hF2⟩
    | _ => cases hChk
  | constant c1 =>
    cases opTgt with
    | constant c2 =>
      rw [← @operandEq_eq (.constant c1) (.constant c2) hChk]
      let ⟨l2, hE2, hF2, _⟩ := evalOperandToSlot_fwd_eq hFwd hEval
      exact ⟨l2, hE2, hF2⟩
    | _ => cases hChk
  | move p =>
    cases opTgt with
    | copy _ => cases hChk
    | move p2 =>
      rw [← @operandEq_eq (.move p) (.move p2) hChk]
      let ⟨l2, hE2, hF2, _⟩ := evalOperandToSlot_fwd_eq hFwd hEval
      exact ⟨l2, hE2, hF2⟩
    | constant c =>
      dsimp [checkConstPropMoveOperand] at hChk
      let ⟨hProj, hRest⟩ := bool_and_true hChk
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hRest; cases hRest
      | some ty0 =>
        rw [hTy] at hRest
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hRest; cases hRest
        | some abs =>
          rw [hAbs] at hRest; dsimp at hRest
          let ⟨hValC, hImp⟩ := bool_and_true hRest
          let ⟨hcTy, _, vc, hEvC, _⟩ := validTypedConstOperand_elim hValC
          dsimp [evalOperandToSlot] at hEval
          rw [hProj, if_bool_false (rfl : (!true) = false), hTy] at hEval
          cases hSl1 : Trusted.MirSemantics.getElem? localsSrc p.localId with
          | none => rw [hSl1] at hEval; cases hEval
          | some sl1 =>
            rw [hSl1] at hEval
            have hM := hMatch.2.2 p.localId ty0 abs sl1 hTy hAbs hSl1
            let ⟨_, v0, hsl1, hEvL, _⟩ := slotMatchesConst_implies_knownConst hM hImp
            subst hsl1
            dsimp at hEval
            cases hSet1 : setElem? localsSrc p.localId (liveUninitSlot ty0) with
            | none => rw [hSet1] at hEval; cases hEval
            | some locs1' =>
              rw [hSet1] at hEval
              injection hEval with h1; injection h1 with hTyEq h2
              injection h2 with hOptEq hLocEq
              injection hOptEq with hv0
              subst hTyEq; subst hv0; subst hLocEq
              rw [hEvC] at hEvL; injection hEvL with hvc; subst hvc
              let ⟨sl2, hSl2⟩ := getElem?_some_of_lt localsTgt p.localId
                (by rw [hFwd.2.1]; exact getElem?_some_lt hTy)
              let ⟨hRef, hWt2⟩ := hFwd.2.2 p.localId _ _ sl2 hTy hSl1 hSl2
              cases sl2 with
              | dead => cases hRef
              | live opt2 =>
                refine ⟨localsTgt, ?_,
                  localsFwdRefines_set_left hFwd hTy hSl2 hSet1
                    (slotFwdRefines_liveUninit_left hWt2)⟩
                dsimp [evalOperandToSlot]
                rw [hcTy, hEvC]

private theorem evalPrimitiveOperand_constPropMove_fwd {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {opSrc opTgt : Operand} {v : Val}
    (hMatch : LocalsMatchConstEnv bodyLocals env localsSrc)
    (hFwd : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hChk : checkConstPropMoveOperand bodyLocals env opSrc opTgt = true)
    (hEval : evalPrimitiveOperand bodyLocals localsSrc opSrc = .ok (v, localsSrc')) :
    ∃ localsTgt',
      evalPrimitiveOperand bodyLocals localsTgt opTgt = .ok (v, localsTgt') ∧
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' := by
  dsimp [evalPrimitiveOperand] at hEval
  cases hS : evalOperandToSlot bodyLocals localsSrc opSrc with
  | error _ => rw [hS] at hEval; cases hEval
  | ok res =>
    let ⟨ty0, optVal, locs1⟩ := res
    rw [hS] at hEval; dsimp at hEval
    cases hPrim : isPrimitiveReadableTy ty0 with
    | false => rw [hPrim] at hEval; cases hEval
    | true =>
      rw [hPrim] at hEval; dsimp at hEval
      cases optVal with
      | none => cases hEval
      | some v0 =>
        injection hEval with h1; injection h1 with hv hl
        subst hv; subst hl
        let ⟨locs2, hE2, hF2⟩ := evalOperandToSlot_constPropMove_fwd hMatch hFwd hChk hS
        refine ⟨locs2, ?_, hF2⟩
        dsimp [evalPrimitiveOperand]; rw [hE2]; dsimp; rw [hPrim]; rfl

private theorem evalRvalue_constPropMove_fwd {bodyLocals : List MirTy}
    {env : List ConstAbsSlot} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {dstTy : MirTy} {rvSrc rvTgt : Rvalue} {v : Val}
    (hMatch : LocalsMatchConstEnv bodyLocals env localsSrc)
    (hFwd : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hChk : checkConstPropMoveRvalue bodyLocals env rvSrc rvTgt = true)
    (hEval : evalRvalue bodyLocals localsSrc dstTy rvSrc = .ok (v, localsSrc')) :
    ∃ localsTgt',
      evalRvalue bodyLocals localsTgt dstTy rvTgt = .ok (v, localsTgt') ∧
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' := by
  cases rvSrc with
  | use o1 =>
    cases rvTgt with
    | use o2 =>
      dsimp [checkConstPropMoveRvalue] at hChk
      dsimp [evalRvalue] at hEval
      cases hS : evalOperandToSlot bodyLocals localsSrc o1 with
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
            injection hEval with h1; injection h1 with hv hl
            subst hv; subst hl
            let ⟨locs2, hE2, hF2⟩ := evalOperandToSlot_constPropMove_fwd hMatch hFwd hChk hS
            refine ⟨locs2, ?_, hF2⟩
            dsimp [evalRvalue]; rw [hE2]; dsimp; rw [hEqTy]; rfl
    | _ => cases hChk
  | unaryOp uop1 o1 =>
    cases rvTgt with
    | unaryOp uop2 o2 =>
      dsimp [checkConstPropMoveRvalue] at hChk
      let ⟨hOp, hO⟩ := bool_and_true hChk
      rw [← unOpEq_eq hOp]
      dsimp [evalRvalue] at hEval
      cases hEO : evalPrimitiveOperand bodyLocals localsSrc o1 with
      | error _ => rw [hEO] at hEval; cases hEval
      | ok resO =>
        let ⟨ov, locs1⟩ := resO
        rw [hEO] at hEval; dsimp at hEval
        cases hUn : evalUnOp uop1 ov with
        | error _ => rw [hUn] at hEval; cases hEval
        | ok resV =>
          rw [hUn] at hEval; injection hEval with h1; injection h1 with hv hl
          subst hv; subst hl
          let ⟨locs2, hEO2, hF2⟩ := evalPrimitiveOperand_constPropMove_fwd hMatch hFwd hO hEO
          refine ⟨locs2, ?_, hF2⟩
          dsimp [evalRvalue]; rw [hEO2]; dsimp; rw [hUn]
    | _ => cases hChk
  | binaryOp bop1 l1 r1 =>
    cases rvTgt with
    | binaryOp bop2 l2 r2 =>
      dsimp [checkConstPropMoveRvalue] at hChk
      let ⟨h12, hR⟩ := bool_and_true hChk
      let ⟨hOp, hL⟩ := bool_and_true h12
      rw [← binOpEq_eq hOp]
      dsimp [evalRvalue] at hEval
      cases hEL : evalPrimitiveOperand bodyLocals localsSrc l1 with
      | error _ => rw [hEL] at hEval; cases hEval
      | ok resL =>
        let ⟨lv, locs1⟩ := resL
        rw [hEL] at hEval; dsimp at hEval
        have hMatch1 := deinitMovePrimitiveOperand_sound hMatch hEL
        let ⟨tLocs1, hEL2, hF1⟩ := evalPrimitiveOperand_constPropMove_fwd hMatch hFwd hL hEL
        cases hER : evalPrimitiveOperand bodyLocals locs1 r1 with
        | error _ => rw [hER] at hEval; cases hEval
        | ok resR =>
          let ⟨rvv, locs2⟩ := resR
          rw [hER] at hEval; dsimp at hEval
          let ⟨tLocs2, hER2, hF2⟩ := evalPrimitiveOperand_constPropMove_fwd hMatch1 hF1 hR hER
          cases hBin : evalBinOp bop1 lv rvv with
          | error _ => rw [hBin] at hEval; cases hEval
          | ok resV =>
            rw [hBin] at hEval; injection hEval with h1; injection h1 with hv hl
            subst hv; subst hl
            refine ⟨tLocs2, ?_, hF2⟩
            dsimp [evalRvalue]; rw [hEL2]; dsimp; rw [hER2]; dsimp; rw [hBin]
    | _ => cases hChk
  | discriminant p1 =>
    rw [← @rvalueEq_eq (.discriminant p1) rvTgt hChk]; exact evalRvalue_fwd_eq hFwd hEval
  | ref m1 p1 =>
    rw [← @rvalueEq_eq (.ref m1 p1) rvTgt hChk]; exact evalRvalue_fwd_eq hFwd hEval
  | addressOf m1 p1 =>
    rw [← @rvalueEq_eq (.addressOf m1 p1) rvTgt hChk]; exact evalRvalue_fwd_eq hFwd hEval
  | aggregateTuple fs1 =>
    rw [← @rvalueEq_eq (.aggregateTuple fs1) rvTgt hChk]; exact evalRvalue_fwd_eq hFwd hEval
  | unsupported =>
    rw [← @rvalueEq_eq .unsupported rvTgt hChk]; exact evalRvalue_fwd_eq hFwd hEval

private theorem evalTerminator_constPropMove_fwd {bSrc bTgt : Body}
    {bbSrc bbTgt : BasicBlock} {env : List ConstAbsSlot}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hLocs : bSrc.locals = bTgt.locals)
    (hClean : bbSrc.cleanup = bbTgt.cleanup)
    (hMatch : LocalsMatchConstEnv bSrc.locals env fSrc.locals)
    (hFwd : LocalsFwdRefines bSrc.locals fSrc.locals fTgt.locals)
    (hChk : checkConstPropMoveTerminator bSrc.locals env
      bbSrc.terminator bbTgt.terminator = true) :
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
  cases hT1 : bbSrc.terminator with
  | switchInt d1 ts1 =>
    rw [hT1] at hChk
    cases hT2 : bbTgt.terminator with
    | switchInt d2 ts2 =>
      rw [hT2] at hChk
      dsimp [checkConstPropMoveTerminator] at hChk
      let ⟨hD, hTs⟩ := bool_and_true hChk
      have hTsEq := switchTargetsEq_eq hTs
      subst hTsEq
      refine ⟨?_, ?_⟩
      · intro s' hEv
        unfold evalTerminator at hEv
        rw [hT1] at hEv; dsimp at hEv
        cases hED : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
        | error _ => rw [hED] at hEv; cases hEv
        | ok resD =>
          let ⟨dv, locs1⟩ := resD
          rw [hED] at hEv; dsimp at hEv
          let ⟨locs2, hED2, hFwd1⟩ := evalPrimitiveOperand_constPropMove_fwd hMatch hFwd hD hED
          cases dv with
          | scalar sv =>
            dsimp at hEv
            cases hSw : evalSwitchBranches sv.width sv.bits ts1.otherwise ts1.branches with
            | error _ => rw [hSw] at hEv; cases hEv
            | ok tgt =>
              rw [hSw] at hEv; injection hEv with hEqS; subst hEqS
              refine ⟨tgt, locs1, locs2, rfl, ?_, hFwd1⟩
              unfold evalTerminator; rw [hT2, ← hLocs]; dsimp; rw [hED2]; dsimp; rw [hSw]; rfl
          | bool b =>
            dsimp at hEv
            cases hSw : evalBoolSwitchBranches b ts1.otherwise ts1.branches with
            | error _ => rw [hSw] at hEv; cases hEv
            | ok tgt =>
              rw [hSw] at hEv; injection hEv with hEqS; subst hEqS
              refine ⟨tgt, locs1, locs2, rfl, ?_, hFwd1⟩
              unfold evalTerminator; rw [hT2, ← hLocs]; dsimp; rw [hED2]; dsimp; rw [hSw]; rfl
          | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv
      · intro out hDone
        unfold evalTerminator at hDone
        rw [hT1] at hDone; dsimp at hDone
        cases hED : evalPrimitiveOperand bSrc.locals fSrc.locals d1 with
        | error _ => rw [hED] at hDone; cases hDone
        | ok resD =>
          let ⟨dv, _⟩ := resD
          rw [hED] at hDone; dsimp at hDone
          cases dv with
          | scalar sv =>
            dsimp at hDone
            cases hSw : evalSwitchBranches sv.width sv.bits ts1.otherwise ts1.branches <;>
              rw [hSw] at hDone <;> cases hDone
          | bool b =>
            dsimp at hDone
            cases hSw : evalBoolSwitchBranches b ts1.otherwise ts1.branches <;>
              rw [hSw] at hDone <;> cases hDone
          | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hDone
    | _ =>
      rw [hT2] at hChk
      cases hChk
  | goto t1 =>
    rw [hT1] at hChk
    exact evalTerminator_fwd_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq (.goto t1) bbTgt.terminator hChk) hFwd
  | return_ =>
    rw [hT1] at hChk
    exact evalTerminator_fwd_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq .return_ bbTgt.terminator hChk) hFwd
  | unreachable =>
    rw [hT1] at hChk
    exact evalTerminator_fwd_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq .unreachable bbTgt.terminator hChk) hFwd
  | unwindResume =>
    rw [hT1] at hChk
    exact evalTerminator_fwd_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq .unwindResume bbTgt.terminator hChk) hFwd
  | assert c1 e1 m1 t1 u1 =>
    rw [hT1] at hChk
    exact evalTerminator_fwd_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq (.assert c1 e1 m1 t1 u1) bbTgt.terminator hChk) hFwd
  | call f1 as1 d1 t1 u1 =>
    rw [hT1] at hChk
    exact evalTerminator_fwd_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq (.call f1 as1 d1 t1 u1) bbTgt.terminator hChk) hFwd
  | unsupported =>
    rw [hT1] at hChk
    exact evalTerminator_fwd_eq hLocs hClean
      (by rw [hT1]; exact @terminatorEq_eq .unsupported bbTgt.terminator hChk) hFwd

private theorem isConstPropMoveProgram_initState_eq {pSrc pTgt : Program}
    {cert : ProgramConstCert}
    (hRel : isConstPropMoveProgram pSrc pTgt = true)
    (hCert : checkConstPropMoveProgram cert pSrc pTgt = true)
    (q : Query) :
    initState pSrc q = initState pTgt q := by
  let ⟨hHdr, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLen, hCertBodies⟩ := bool_and_true hCert
  let ⟨_, hCertAt, _⟩ := listRel_zip_left_rel (nat_beq_eq hCertLen) hCertBodies
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodiesRel
  · intro b1 hB1
    let ⟨b2, hB2, hBRel⟩ := listRel_getElem?_left hBodiesRel hB1
    let ⟨cBody, b2', _, hB2', hBCert⟩ := hCertAt pSrc.entryDefId b1 hB1
    rw [hB2] at hB2'; injection hB2' with hEqB; subst hEqB
    rw [hEnt] at hB2
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨h123, _⟩ := bool_and_true hBCert
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hPres, _⟩ := bool_and_true h12
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨b2, hB2, hBHdr, list_isEmpty_eq_of_length (listRel_length hBBsRel),
           hBounds, initLocalsLoop_eq_of_preservesStorage q.args hBHdr hPres⟩

private noncomputable def checkConstPropMoveStmtPair (bodyLocals : List MirTy)
    (env : List ConstAbsSlot) (sSrc sTgt : StatementKind) : Bool :=
  match sSrc, sTgt with
  | .assign d₁ rv₁, .assign d₂ rv₂ =>
    placeEq d₁ d₂ && d₁.projection.isEmpty &&
      checkConstPropMoveRvalue bodyLocals env rv₁ rv₂
  | _, _ => stmtEq sSrc sTgt

private theorem stepConstPropMoveCertStmts_cons_elim {bodyLocals : List MirTy}
    {env exitEnv : List ConstAbsSlot} {sSrc sTgt : StatementKind}
    {restSrc restTgt : List StatementKind}
    (h : stepConstPropMoveCertStmts bodyLocals env (sSrc :: restSrc) (sTgt :: restTgt) = some exitEnv) :
    checkConstPropMoveStmtPair bodyLocals env sSrc sTgt = true ∧
    ∃ nextEnv,
      stepPlainStmtConst bodyLocals env sSrc = some nextEnv ∧
      stepConstPropMoveCertStmts bodyLocals nextEnv restSrc restTgt = some exitEnv := by
  have hFold :
      (if !(checkConstPropMoveStmtPair bodyLocals env sSrc sTgt) then none
       else
         match stepPlainStmtConst bodyLocals env sSrc with
         | none => none
         | some env' => stepConstPropMoveCertStmts bodyLocals env' restSrc restTgt) =
        some exitEnv := by
    cases sSrc <;> cases sTgt <;> exact h
  cases hOk : checkConstPropMoveStmtPair bodyLocals env sSrc sTgt with
  | false =>
    rw [hOk, if_bool_true (rfl : (!false) = true)] at hFold
    cases hFold
  | true =>
    rw [hOk, if_bool_false (rfl : (!true) = false)] at hFold
    cases hPlain : stepPlainStmtConst bodyLocals env sSrc with
    | none => rw [hPlain] at hFold; cases hFold
    | some nextEnv =>
      rw [hPlain] at hFold
      exact ⟨rfl, nextEnv, rfl, hFold⟩

private theorem constPropMove_block_entry {bSrc bTgt : Body} {cBody : BodyConstCert}
    {bbIdx : BasicBlockId} {tgtEnv : List ConstAbsSlot} {localsSrc : List LocalSlot}
    (hBRel : isConstPropMoveBody bSrc bTgt = true)
    (hBCert : checkConstPropMoveBody cBody bSrc bTgt = true)
    (hLt : bbIdx < bSrc.basicBlocks.length)
    (hCGet : Trusted.MirSemantics.getElem? cBody bbIdx = some (some tgtEnv))
    (hMatch : LocalsMatchConstEnv bSrc.locals tgtEnv localsSrc) :
    ∃ bbSrc bbTgt exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt ∧
      0 ≤ bbSrc.statements.length ∧
      LocalsMatchConstEnv bSrc.locals tgtEnv localsSrc ∧
      stepConstPropMoveCertStmts bSrc.locals tgtEnv
        (bbSrc.statements.drop 0) (bbTgt.statements.drop 0) = some exitEnv ∧
      checkConstPropMoveTerminator bSrc.locals exitEnv
        bbSrc.terminator bbTgt.terminator = true ∧
      checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length
        cBody exitEnv bbSrc.terminator = true := by
  let ⟨_, hBBsRel⟩ := bool_and_true hBRel
  let ⟨_, hLoop⟩ := bool_and_true hBCert
  let ⟨bbSrc, hBBSrc⟩ := getElem?_some_of_lt bSrc.basicBlocks bbIdx hLt
  let ⟨bbTgt, hBBTgt, _⟩ := listRel_getElem?_left hBBsRel hBBSrc
  have hBlkCert := checkConstPropMoveBlocksLoop_get hLoop hBBSrc
  rw [Nat.zero_add] at hBlkCert
  unfold checkConstPropMoveBlock at hBlkCert
  rw [hCGet, hBBTgt] at hBlkCert; dsimp at hBlkCert
  let ⟨_, hStOpt⟩ := bool_and_true hBlkCert
  cases hStepS : stepConstPropMoveCertStmts bSrc.locals tgtEnv bbSrc.statements bbTgt.statements with
  | none => rw [hStepS] at hStOpt; cases hStOpt
  | some exitEnv =>
    rw [hStepS] at hStOpt; dsimp at hStOpt
    let ⟨hTermC, hEdgesC⟩ := bool_and_true hStOpt
    exact ⟨bbSrc, bbTgt, exitEnv, hBBSrc, hBBTgt, Nat.zero_le _, hMatch, hStepS, hTermC, hEdgesC⟩

private noncomputable def ConstPropMoveFwdRel (pSrc pTgt : Program)
    (cert : ProgramConstCert) (s t : State) : Prop :=
  ∃ fSrc fTgt bSrc bTgt cBody,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
    Trusted.MirSemantics.getElem? cert fSrc.defId = some cBody ∧
    isConstPropMoveBody bSrc bTgt = true ∧
    checkConstPropMoveBody cBody bSrc bTgt = true ∧
    LocalsFwdRefines bSrc.locals fSrc.locals fTgt.locals ∧
    (bSrc.basicBlocks.length ≤ fSrc.blockIdx ∨
      ∃ bbSrc bbTgt entryEnv curEnv exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt ∧
        Trusted.MirSemantics.getElem? cBody fSrc.blockIdx = some (some entryEnv) ∧
        fSrc.stmtIdx ≤ bbSrc.statements.length ∧
        LocalsMatchConstEnv bSrc.locals curEnv fSrc.locals ∧
        stepConstPropMoveCertStmts bSrc.locals curEnv
          (bbSrc.statements.drop fSrc.stmtIdx)
          (bbTgt.statements.drop fSrc.stmtIdx) = some exitEnv ∧
        checkConstPropMoveTerminator bSrc.locals exitEnv
          bbSrc.terminator bbTgt.terminator = true ∧
        checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length
          cBody exitEnv bbSrc.terminator = true)

private theorem constPropMove_query_fwd {pSrc pTgt : Program} {cert : ProgramConstCert}
    (hRel : isConstPropMoveProgram pSrc pTgt = true)
    (hCert : checkConstPropMoveProgram cert pSrc pTgt = true)
    (q : Query) (hWfSrc : WellFormed pSrc q) :
    WellFormed pTgt q ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLen, hCertBodies⟩ := bool_and_true hCert
  let ⟨_, hCertAt, _⟩ := listRel_zip_left_rel (nat_beq_eq hCertLen) hCertBodies
  apply fwd_sim_lift (R := ConstPropMoveFwdRel pSrc pTgt cert) ?_ ?_ hWfSrc
  · intro s₀ hInitSrc
    have hInitTgt : initState pTgt q = .ok s₀ := by
      rw [← isConstPropMoveProgram_initState_eq hRel hCert q]; exact hInitSrc
    let ⟨_, _, bSrc, hBSrc, hNotEmpty, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hInitSrc
    subst hEqS
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodiesRel hBSrc
    let ⟨cBody, bTgt', hCBody, hBTgt', hBCert⟩ := hCertAt pSrc.entryDefId bSrc hBSrc
    rw [hBTgt] at hBTgt'; injection hBTgt' with hEqB; subst hEqB
    let ⟨h123, _⟩ := bool_and_true hBCert
    let ⟨_, hEntryOk⟩ := bool_and_true h123
    rw [hNotEmpty, if_bool_false rfl] at hEntryOk
    cases hC0 : Trusted.MirSemantics.getElem? cBody 0 with
    | none => rw [hC0] at hEntryOk; cases hEntryOk
    | some opt0 =>
      rw [hC0] at hEntryOk
      cases opt0 with
      | none => cases hEntryOk
      | some env₀ =>
        have hMatch0 := localsMatchConstEnv_mono hEntryOk (initConstEnvLoop_matches hArgs)
        have hPos := list_pos_of_isEmpty_false hNotEmpty
        let ⟨bbSrc, bbTgt, exitEnv, hBBS, hBBT, hLe0, hM0, hSt0, hTm0, hEd0⟩ :=
          constPropMove_block_entry hBRel hBCert hPos hC0 hMatch0
        exact ⟨_, hInitTgt, _, _, bSrc, bTgt, cBody,
               rfl, rfl, rfl, rfl, rfl, rfl, hBSrc, hBTgt, hCBody, hBRel, hBCert,
               localsFwdRefines_refl_of_wt (localsMatchConstEnv_wt hMatch0),
               Or.inr ⟨bbSrc, bbTgt, env₀, env₀, exitEnv, hBBS, hBBT, hC0, hLe0, hM0, hSt0, hTm0, hEd0⟩⟩
  · intro s t hR
    let ⟨fSrc, fTgt, bSrc, bTgt, cBody, hFS, hFT, hCM, hDefEq, hBlkEq, hIdxEq,
         hBSrc, hBTgt, hCBody, hBRel, hBCert, hFwd, hBlkInv⟩ := hR
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    cases s with
    | mk fsS cmS =>
      cases t with
      | mk fsT cmT =>
        dsimp at hFS hFT hCM
        subst hFS; subst hFT; subst hCM
        cases hBlkInv with
        | inl hOob =>
          have hNoneS := getElem?_none_of_ge hOob
          refine ⟨?_, ?_⟩
          · intro s' hEvS
            unfold evalStep at hEvS; dsimp at hEvS
            rw [hBSrc] at hEvS; dsimp at hEvS; rw [hNoneS] at hEvS; cases hEvS
          · intro out hDoneS
            unfold evalStep at hDoneS; dsimp at hDoneS
            rw [hBSrc] at hDoneS; dsimp at hDoneS; rw [hNoneS] at hDoneS; cases hDoneS
        | inr hIn =>
          let ⟨bbSrc, bbTgt, entryEnv, curEnv, exitEnv, hBBS, hBBT, hCGet, hIdxLe, hMatch, hStDrop, hTermC, hEdgesC⟩ := hIn
          have hRelBB : isConstPropMoveBlock bbSrc bbTgt = true := by
            let ⟨bbT', hBBT', hRelBB'⟩ := listRel_getElem?_left hBBsRel hBBS
            rw [hBBT] at hBBT'; injection hBBT' with hE; subst hE; exact hRelBB'
          let ⟨hBB12, _⟩ := bool_and_true hRelBB
          let ⟨hCleanB, hStmtsRel⟩ := bool_and_true hBB12
          have hCleanEq := bool_beq_eq hCleanB
          have hLenStEq := listRel_length hStmtsRel
          have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
            rw [← hDefEq]; exact hBTgt
          have hBBT2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
            rw [← hBlkEq]; exact hBBT
          refine ⟨?_, ?_⟩
          · intro s' hEvS
            unfold evalStep at hEvS; dsimp at hEvS
            rw [hBSrc] at hEvS; dsimp at hEvS
            rw [hBBS] at hEvS; dsimp at hEvS
            cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
            | some sSrc =>
              rw [hStS] at hEvS; dsimp at hEvS
              let ⟨sTgt, hStT, _⟩ := listRel_getElem?_left hStmtsRel hStS
              have hStT2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some sTgt := by
                rw [← hIdxEq]; exact hStT
              rw [drop_eq_cons_of_getElem? hStS, drop_eq_cons_of_getElem? hStT] at hStDrop
              let ⟨hOk, nextEnv, hPlain, hStRest⟩ := stepConstPropMoveCertStmts_cons_elim hStDrop
              have hStepPair : ∃ locs1' locs2',
                  s' = { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' }],
                         callerMem := cmS } ∧
                  evalStatement bTgt fTgt cmS sTgt =
                    .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' }],
                            callerMem := cmS } ∧
                  LocalsFwdRefines bSrc.locals locs1' locs2' := by
                cases sSrc with
                | assign d1 rv1 =>
                  cases sTgt with
                  | assign d2 rv2 =>
                    dsimp [checkConstPropMoveStmtPair] at hOk
                    let ⟨h12, hRvC⟩ := bool_and_true hOk
                    let ⟨hPEq, hDEmp⟩ := bool_and_true h12
                    have hdEq := placeEq_eq hPEq; subst hdEq
                    dsimp [evalStatement] at hEvS
                    rw [hDEmp, if_bool_false (rfl : (!true) = false)] at hEvS
                    cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals d1.localId with
                    | none => rw [hDstTy] at hEvS; cases hEvS
                    | some dstTy =>
                      rw [hDstTy] at hEvS; dsimp at hEvS
                      cases hRV1 : evalRvalue bSrc.locals fSrc.locals dstTy rv1 with
                      | error _ => rw [hRV1] at hEvS; cases hEvS
                      | ok res1 =>
                        let ⟨val, locs1⟩ := res1
                        rw [hRV1] at hEvS; dsimp at hEvS
                        cases hW1 : writePlace locs1 d1.localId dstTy val with
                        | error _ => rw [hW1] at hEvS; cases hEvS
                        | ok locs1' =>
                          rw [hW1] at hEvS; injection hEvS with hEqS'
                          let ⟨locs2, hRV2, hFwd1⟩ := evalRvalue_constPropMove_fwd hMatch hFwd hRvC hRV1
                          let ⟨locs2', hW2, hFwd2⟩ := writePlace_fwd hFwd1 hDstTy hW1
                          refine ⟨locs1', locs2', hEqS'.symm, ?_, hFwd2⟩
                          dsimp [evalStatement]
                          rw [hDEmp, if_bool_false (rfl : (!true) = false), ← hLocEq, hDstTy]
                          dsimp; rw [hRV2]; dsimp; rw [hW2]
                  | nop | storageLive _ | storageDead _ | unsupported =>
                    dsimp [checkConstPropMoveStmtPair] at hOk
                    cases hOk
                | nop =>
                  dsimp [checkConstPropMoveStmtPair] at hOk
                  rw [← @stmtEq_eq .nop sTgt hOk]
                  exact evalStatement_fwd_eq hLocEq hFwd hEvS
                | storageLive id =>
                  dsimp [checkConstPropMoveStmtPair] at hOk
                  rw [← @stmtEq_eq (.storageLive id) sTgt hOk]
                  exact evalStatement_fwd_eq hLocEq hFwd hEvS
                | storageDead id =>
                  dsimp [checkConstPropMoveStmtPair] at hOk
                  rw [← @stmtEq_eq (.storageDead id) sTgt hOk]
                  exact evalStatement_fwd_eq hLocEq hFwd hEvS
                | unsupported =>
                  dsimp [checkConstPropMoveStmtPair] at hOk
                  rw [← @stmtEq_eq .unsupported sTgt hOk]
                  exact evalStatement_fwd_eq hLocEq hFwd hEvS
              let ⟨locs1', locs2', hEqS', hEvT, hFwd'⟩ := hStepPair
              let ⟨locs1'', hEqS'', hNextMatch⟩ := stepPlainStmtConst_sound hMatch hPlain hEvS
              rw [hEqS'] at hEqS''
              injection hEqS'' with hFsEq _
              injection hFsEq with hFrEq _
              have hL1Eq : locs1' = locs1'' := congrArg FrameState.locals hFrEq
              subst hL1Eq
              subst hEqS'
              have hNextLe : fSrc.stmtIdx + 1 ≤ bbSrc.statements.length :=
                getElem?_some_lt hStS
              refine ⟨{ frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' }], callerMem := cmS },
                ?_,
                { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' },
                bSrc, bTgt, cBody,
                rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq],
                hBSrc, hBTgt, hCBody, hBRel, hBCert, hFwd',
                Or.inr ⟨bbSrc, bbTgt, entryEnv, nextEnv, exitEnv,
                        hBBS, hBBT, hCGet, hNextLe, hNextMatch, hStRest, hTermC, hEdgesC⟩⟩
              unfold evalStep; dsimp
              rw [hBTgt2]; dsimp; rw [hBBT2]; dsimp; rw [hStT2]; dsimp
              exact hEvT
            | none =>
              rw [hStS] at hEvS; dsimp at hEvS
              have hStT := (listRel_getElem?_none_iff fSrc.stmtIdx hStmtsRel).mp hStS
              have hStT2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
                rw [← hIdxEq]; exact hStT
              cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
              | false => rw [hEnd] at hEvS; cases hEvS
              | true =>
                rw [hEnd, if_bool_true rfl] at hEvS
                have hIdxLen := nat_beq_eq hEnd
                have hEndT2 : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
                  rw [← hIdxEq, ← hLenStEq]; exact hEnd
                rw [hIdxLen, drop_length_nil, hLenStEq, drop_length_nil] at hStDrop
                dsimp [stepConstPropMoveCertStmts] at hStDrop
                injection hStDrop with hCurExit; subst hCurExit
                let ⟨tgt, locs1', locs2', hEqS', hEvT, hFwd'⟩ :=
                  (evalTerminator_constPropMove_fwd hLocEq hCleanEq hMatch hFwd hTermC).1 s' hEvS
                let ⟨tgt', locs1'', hEqS'', _, hTargetCert⟩ :=
                  evalTerminator_constEdges_sound hMatch hEdgesC hEvS
                rw [hEqS'] at hEqS''
                injection hEqS'' with hFsEq _
                injection hFsEq with hFrEq _
                have hTgtEq : tgt = tgt' := congrArg FrameState.blockIdx hFrEq
                have hL1Eq : locs1' = locs1'' := congrArg FrameState.locals hFrEq
                subst hTgtEq; subst hL1Eq; subst hEqS'
                refine ⟨{ frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' }], callerMem := cmS },
                  ?_,
                  { fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs1' },
                  { fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' },
                  bSrc, bTgt, cBody,
                  rfl, rfl, rfl, hDefEq, rfl, rfl,
                  hBSrc, hBTgt, hCBody, hBRel, hBCert, hFwd', ?_⟩
                · unfold evalStep; dsimp
                  rw [hBTgt2]; dsimp; rw [hBBT2]; dsimp; rw [hStT2]; dsimp
                  rw [hEndT2, if_bool_true rfl]
                  exact hEvT
                · cases Nat.lt_or_ge tgt bSrc.basicBlocks.length with
                  | inr hGeT => exact Or.inl hGeT
                  | inl hLtT =>
                    let ⟨tgtEnv, hCTgt, hTgtMatch⟩ := hTargetCert hLtT
                    let ⟨bbSrc2, bbTgt2, exitEnv2, hBBS2, hBBT2, hLe2, hM2, hSt2, hTm2, hEd2⟩ :=
                      constPropMove_block_entry hBRel hBCert hLtT hCTgt hTgtMatch
                    exact Or.inr ⟨bbSrc2, bbTgt2, tgtEnv, tgtEnv, exitEnv2,
                                  hBBS2, hBBT2, hCTgt, hLe2, hM2, hSt2, hTm2, hEd2⟩
          · intro out hDoneS
            unfold evalStep at hDoneS; dsimp at hDoneS
            rw [hBSrc] at hDoneS; dsimp at hDoneS
            rw [hBBS] at hDoneS; dsimp at hDoneS
            cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
            | some sSrc =>
              rw [hStS] at hDoneS; dsimp at hDoneS
              exact False.elim (evalStatement_never_done bSrc fSrc cmS sSrc out hDoneS)
            | none =>
              rw [hStS] at hDoneS; dsimp at hDoneS
              have hStT := (listRel_getElem?_none_iff fSrc.stmtIdx hStmtsRel).mp hStS
              have hStT2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
                rw [← hIdxEq]; exact hStT
              cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
              | false => rw [hEnd] at hDoneS; cases hDoneS
              | true =>
                rw [hEnd, if_bool_true rfl] at hDoneS
                have hIdxLen := nat_beq_eq hEnd
                have hEndT2 : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
                  rw [← hIdxEq, ← hLenStEq]; exact hEnd
                rw [hIdxLen, drop_length_nil, hLenStEq, drop_length_nil] at hStDrop
                dsimp [stepConstPropMoveCertStmts] at hStDrop
                injection hStDrop with hCurExit; subst hCurExit
                have hDoneT := (evalTerminator_constPropMove_fwd hLocEq hCleanEq hMatch hFwd hTermC).2 out hDoneS
                unfold evalStep; dsimp
                rw [hBTgt2]; dsimp; rw [hBBT2]; dsimp; rw [hStT2]; dsimp
                rw [hEndT2, if_bool_true rfl]
                exact hDoneT

private theorem codegen_constPropMove_certified_refines_priv
    (pSrc pTgt : Program) (cert : ProgramConstCert)
    (hRel : isConstPropMoveProgram pSrc pTgt = true)
    (hCert : checkConstPropMoveProgram cert pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  let ⟨hHdr, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLen, hCertBodies⟩ := bool_and_true hCert
  let ⟨_, hCertAt, _⟩ := listRel_zip_left_rel (nat_beq_eq hCertLen) hCertBodies
  apply forwardCodegenRefines_of_query_fwd hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodiesRel hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨cBody, bTgt'', _, hBT'', hBCert⟩ := hCertAt defId bSrc hBS
    rw [hBT] at hBT''; injection hBT'' with hEqB2; subst hEqB2
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨h123, _⟩ := bool_and_true hBCert
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hPres, _⟩ := bool_and_true h12
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨hBHdr, list_isEmpty_eq_of_length (listRel_length hBBsRel), hBounds⟩
  · intro q hWf
    exact constPropMove_query_fwd hRel hCert q hWf
  · intro defId args hWf
    have hRelEntry : isConstPropMoveProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodiesRel
    exact (constPropMove_query_fwd hRelEntry hCert { args := args } hWf).1

/-! #### Theorem 1c: Bidirectional `ConstPropMove` With All-Paths Deadness
(`vc_transport_constPropMove_dead_certified_iff`) -/

private theorem liveUninitSlot_is_live (ty : MirTy) :
    ∃ o, liveUninitSlot ty = .live o := by
  cases ty with
  | unit => exact ⟨some .unit, rfl⟩
  | enum ety =>
    change ∃ o, (if isZstEnumTy ety then LocalSlot.live (some (.enumVal ety 0)) else .live none) = .live o
    cases isZstEnumTy ety with
    | true => exact ⟨some (.enumVal ety 0), rfl⟩
    | false => exact ⟨none, rfl⟩
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    exact ⟨none, rfl⟩

private noncomputable def SlotMoveDeadRel (deadHere : Prop) (sl1 sl2 : LocalSlot) : Prop :=
  sl1 = sl2 ∨ (deadHere ∧ (∃ o1, sl1 = .live o1) ∧ (∃ o2, sl2 = .live o2))

private noncomputable def LocalsMoveDeadRel (deadPred : LocalId → Prop)
    (locs1 locs2 : List LocalSlot) : Prop :=
  locs1.length = locs2.length ∧
  ∀ i sl1 sl2,
    Trusted.MirSemantics.getElem? locs1 i = some sl1 →
    Trusted.MirSemantics.getElem? locs2 i = some sl2 →
    SlotMoveDeadRel (i ≠ 0 ∧ deadPred i) sl1 sl2

private theorem localsMoveDeadRel_refl (deadPred : LocalId → Prop)
    (locs : List LocalSlot) :
    LocalsMoveDeadRel deadPred locs locs := by
  refine ⟨rfl, ?_⟩
  intro i sl1 sl2 h1 h2
  rw [h1] at h2; injection h2 with hEq
  exact Or.inl hEq

private theorem localsMoveDeadRel_mono {P Q : LocalId → Prop}
    {locs1 locs2 : List LocalSlot}
    (hImp : ∀ i, i ≠ 0 → P i → Q i)
    (hRel : LocalsMoveDeadRel P locs1 locs2) :
    LocalsMoveDeadRel Q locs1 locs2 := by
  refine ⟨hRel.1, ?_⟩
  intro i sl1 sl2 h1 h2
  cases hRel.2 i sl1 sl2 h1 h2 with
  | inl hEq => exact Or.inl hEq
  | inr hD =>
    let ⟨⟨hNe0, hPi⟩, hL1, hL2⟩ := hD
    exact Or.inr ⟨⟨hNe0, hImp i hNe0 hPi⟩, hL1, hL2⟩

private theorem localsMoveDeadRel_get_eq {P : LocalId → Prop}
    {locs1 locs2 : List LocalSlot} {i : LocalId}
    (hRel : LocalsMoveDeadRel P locs1 locs2)
    (hNotDead : i ≠ 0 → ¬ P i) :
    Trusted.MirSemantics.getElem? locs1 i = Trusted.MirSemantics.getElem? locs2 i := by
  cases h1 : Trusted.MirSemantics.getElem? locs1 i with
  | none =>
    cases h2 : Trusted.MirSemantics.getElem? locs2 i with
    | none => rfl
    | some sl2 =>
      have hLt1 : i < locs1.length := by rw [hRel.1]; exact getElem?_some_lt h2
      let ⟨sl1, h1'⟩ := getElem?_some_of_lt locs1 i hLt1
      rw [h1] at h1'; cases h1'
  | some sl1 =>
    cases h2 : Trusted.MirSemantics.getElem? locs2 i with
    | none =>
      have hLt2 : i < locs2.length := by rw [← hRel.1]; exact getElem?_some_lt h1
      let ⟨sl2, h2'⟩ := getElem?_some_of_lt locs2 i hLt2
      rw [h2] at h2'; cases h2'
    | some sl2 =>
      cases hRel.2 i sl1 sl2 h1 h2 with
      | inl hEq => rw [hEq]
      | inr hD =>
        let ⟨⟨hNe0, hPi⟩, _, _⟩ := hD
        exact False.elim (hNotDead hNe0 hPi)

private theorem localsMoveDeadRel_get0_eq {P : LocalId → Prop}
    {locs1 locs2 : List LocalSlot}
    (hRel : LocalsMoveDeadRel P locs1 locs2) :
    Trusted.MirSemantics.getElem? locs1 0 = Trusted.MirSemantics.getElem? locs2 0 :=
  localsMoveDeadRel_get_eq hRel (fun hNe => False.elim (hNe rfl))

private theorem setElem?_none_of_length_eq {α : Type} {xs ys : List α}
    {idx : Nat} {v : α}
    (hLen : xs.length = ys.length)
    (hNone : setElem? xs idx v = none) :
    setElem? ys idx v = none := by
  cases Nat.lt_or_ge idx ys.length with
  | inr hGe => exact setElem?_none_of_ge ys idx v hGe
  | inl hLt =>
    have hLtX : idx < xs.length := by rw [hLen]; exact hLt
    let ⟨xs', hSome⟩ := setElem?_some_of_lt xs idx v hLtX
    rw [hNone] at hSome; cases hSome

private theorem localsMoveDeadRel_set_both {P Q : LocalId → Prop}
    {locs1 locs2 locs1' : List LocalSlot} {idx : LocalId} {sl : LocalSlot}
    (hRel : LocalsMoveDeadRel P locs1 locs2)
    (hImp : ∀ i, i ≠ 0 → i ≠ idx → P i → Q i)
    (hSet1 : setElem? locs1 idx sl = some locs1') :
    ∃ locs2',
      setElem? locs2 idx sl = some locs2' ∧
      LocalsMoveDeadRel Q locs1' locs2' := by
  have hLt1 : idx < locs1.length := by
    cases Nat.lt_or_ge idx locs1.length with
    | inl h => exact h
    | inr hGe =>
      rw [setElem?_none_of_ge locs1 idx sl hGe] at hSet1; cases hSet1
  have hLt2 : idx < locs2.length := by rw [← hRel.1]; exact hLt1
  let ⟨locs2', hSet2⟩ := setElem?_some_of_lt locs2 idx sl hLt2
  refine ⟨locs2', hSet2, ?_, ?_⟩
  · rw [setElem?_length hSet1, setElem?_length hSet2, hRel.1]
  · intro i sl1 sl2 hG1 hG2
    cases Nat.decEq i idx with
    | isTrue hEq =>
      subst hEq
      rw [setElem?_getElem?_same hSet1] at hG1
      rw [setElem?_getElem?_same hSet2] at hG2
      injection hG1 with e1; injection hG2 with e2
      subst e1; subst e2
      exact Or.inl rfl
    | isFalse hNe =>
      rw [setElem?_getElem?_ne hSet1 hNe] at hG1
      rw [setElem?_getElem?_ne hSet2 hNe] at hG2
      cases hRel.2 i sl1 sl2 hG1 hG2 with
      | inl hEq => exact Or.inl hEq
      | inr hD =>
        let ⟨⟨hNe0, hPi⟩, hL1, hL2⟩ := hD
        exact Or.inr ⟨⟨hNe0, hImp i hNe0 hNe hPi⟩, hL1, hL2⟩

private theorem localsMoveDeadRel_set_left_live {P : LocalId → Prop}
    {locs1 locs2 locs1' : List LocalSlot} {idx : LocalId}
    {oNew oOld : Option Val}
    (hRel : LocalsMoveDeadRel P locs1 locs2)
    (hNe0 : idx ≠ 0)
    (hSl2 : Trusted.MirSemantics.getElem? locs2 idx = some (.live oOld))
    (hSet1 : setElem? locs1 idx (.live oNew) = some locs1') :
    LocalsMoveDeadRel (fun i => P i ∨ i = idx) locs1' locs2 := by
  refine ⟨by rw [setElem?_length hSet1, hRel.1], ?_⟩
  intro i sl1 sl2 hG1 hG2
  cases Nat.decEq i idx with
  | isTrue hEq =>
    subst hEq
    rw [setElem?_getElem?_same hSet1] at hG1
    rw [hSl2] at hG2
    injection hG1 with e1; injection hG2 with e2
    subst e1; subst e2
    exact Or.inr ⟨⟨hNe0, Or.inr rfl⟩, ⟨oNew, rfl⟩, ⟨oOld, rfl⟩⟩
  | isFalse hNe =>
    rw [setElem?_getElem?_ne hSet1 hNe] at hG1
    cases hRel.2 i sl1 sl2 hG1 hG2 with
    | inl hEq => exact Or.inl hEq
    | inr hD =>
      let ⟨⟨hI0, hPi⟩, hL1, hL2⟩ := hD
      exact Or.inr ⟨⟨hI0, Or.inl hPi⟩, hL1, hL2⟩

private theorem writePlace_moveDeadRel {P Q : LocalId → Prop}
    {locs1 locs2 : List LocalSlot} {dst : LocalId} {dstTy : MirTy} {val : Val}
    (hRel : LocalsMoveDeadRel P locs1 locs2)
    (hImp : ∀ i, i ≠ 0 → i ≠ dst → P i → Q i) :
    (∃ fk, writePlace locs1 dst dstTy val = .error fk ∧
           writePlace locs2 dst dstTy val = .error fk) ∨
    (∃ locs1' locs2',
      writePlace locs1 dst dstTy val = .ok locs1' ∧
      writePlace locs2 dst dstTy val = .ok locs2' ∧
      LocalsMoveDeadRel Q locs1' locs2') := by
  unfold writePlace
  cases hChk : checkVal val dstTy with
  | false =>
    exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | true =>
    rw [if_bool_false (rfl : (!true) = false),
        if_bool_false (rfl : (!true) = false)]
    cases hG1 : Trusted.MirSemantics.getElem? locs1 dst with
    | none =>
      have hG2 : Trusted.MirSemantics.getElem? locs2 dst = none := by
        cases h2 : Trusted.MirSemantics.getElem? locs2 dst with
        | none => rfl
        | some _ =>
          let ⟨_, hx⟩ := getElem?_some_of_lt locs1 dst (by rw [hRel.1]; exact getElem?_some_lt h2)
          rw [hG1] at hx; cases hx
      rw [hG2]
      exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | some sl1 =>
      have hLt2 : dst < locs2.length := by rw [← hRel.1]; exact getElem?_some_lt hG1
      let ⟨sl2, hG2⟩ := getElem?_some_of_lt locs2 dst hLt2
      rw [hG2]
      have hSlotR := hRel.2 dst sl1 sl2 hG1 hG2
      cases sl1 with
      | dead =>
        cases hSlotR with
        | inl hEq =>
          subst hEq
          exact Or.inl ⟨.undefined, rfl, rfl⟩
        | inr hD =>
          let ⟨_, ⟨_, hBad⟩, _⟩ := hD
          cases hBad
      | live o1 =>
        have hLive2 : ∃ o2, sl2 = .live o2 := by
          cases hSlotR with
          | inl hEq => exact ⟨o1, hEq.symm⟩
          | inr hD => exact hD.2.2
        let ⟨o2, hsl2⟩ := hLive2
        subst hsl2
        dsimp only
        cases hSet1 : setElem? locs1 dst (.live (some val)) with
        | none =>
          rw [setElem?_none_of_length_eq hRel.1 hSet1]
          exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | some locs1' =>
          let ⟨locs2', hSet2, hRel'⟩ := localsMoveDeadRel_set_both hRel hImp hSet1
          rw [hSet2]
          exact Or.inr ⟨locs1', locs2', rfl, rfl, hRel'⟩

private noncomputable def opAddedDead (opSrc opTgt : Operand) (i : LocalId) : Prop :=
  match opSrc, opTgt with
  | .move p, .constant _ => i = p.localId
  | _, _ => False

private theorem evalOperandToSlot_moveDead_same {P : LocalId → Prop}
    {bodyLocals : List MirTy} {locs1 locs2 : List LocalSlot} {op : Operand}
    (hRel : LocalsMoveDeadRel P locs1 locs2)
    (hNoTouch : ∀ i, i ≠ 0 → P i → operandTouchesLocal i op = false) :
    (∃ fk, evalOperandToSlot bodyLocals locs1 op = .error fk ∧
           evalOperandToSlot bodyLocals locs2 op = .error fk) ∨
    (∃ ty optV locs1' locs2',
      evalOperandToSlot bodyLocals locs1 op = .ok (ty, optV, locs1') ∧
      evalOperandToSlot bodyLocals locs2 op = .ok (ty, optV, locs2') ∧
      LocalsMoveDeadRel P locs1' locs2') := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot]
    cases evalConstLit c.ty c.lit with
    | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
    | ok v => exact Or.inr ⟨c.ty, some v, locs1, locs2, rfl, rfl, hRel⟩
  | copy p =>
    dsimp [evalOperandToSlot]
    cases p.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      rw [if_bool_false (rfl : (!true) = false),
          if_bool_false (rfl : (!true) = false)]
      cases Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        have hGEq : Trusted.MirSemantics.getElem? locs1 p.localId =
            Trusted.MirSemantics.getElem? locs2 p.localId := by
          apply localsMoveDeadRel_get_eq hRel
          intro hNe0 hPi
          have hT := hNoTouch p.localId hNe0 hPi
          dsimp [operandTouchesLocal] at hT
          rw [nat_beq_refl] at hT; cases hT
        rw [← hGEq]
        cases Trusted.MirSemantics.getElem? locs1 p.localId with
        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | some sl =>
          cases sl with
          | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
          | live optV => exact Or.inr ⟨ty, optV, locs1, locs2, rfl, rfl, hRel⟩
  | move p =>
    dsimp [evalOperandToSlot]
    cases p.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      rw [if_bool_false (rfl : (!true) = false),
          if_bool_false (rfl : (!true) = false)]
      cases Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        have hGEq : Trusted.MirSemantics.getElem? locs1 p.localId =
            Trusted.MirSemantics.getElem? locs2 p.localId := by
          apply localsMoveDeadRel_get_eq hRel
          intro hNe0 hPi
          have hT := hNoTouch p.localId hNe0 hPi
          dsimp [operandTouchesLocal] at hT
          rw [nat_beq_refl] at hT; cases hT
        rw [← hGEq]
        cases Trusted.MirSemantics.getElem? locs1 p.localId with
        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | some sl =>
          cases sl with
          | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
          | live optV =>
            dsimp only
            cases hSet1 : setElem? locs1 p.localId (liveUninitSlot ty) with
            | none =>
              rw [setElem?_none_of_length_eq hRel.1 hSet1]
              exact Or.inl ⟨.unsupported, rfl, rfl⟩
            | some locs1' =>
              let ⟨locs2', hSet2, hRel'⟩ :=
                localsMoveDeadRel_set_both hRel (fun _ _ _ h => h) hSet1
              rw [hSet2]
              exact Or.inr ⟨ty, optV, locs1', locs2', rfl, rfl, hRel'⟩

private theorem evalOperandToSlot_moveDead_step {P : LocalId → Prop}
    {bodyLocals : List MirTy} {env : List ConstAbsSlot}
    {locs1 locs2 : List LocalSlot} {opSrc opTgt : Operand}
    (hMatch : LocalsMatchConstEnv bodyLocals env locs1)
    (hRel : LocalsMoveDeadRel P locs1 locs2)
    (hChk : checkConstPropMoveOperand bodyLocals env opSrc opTgt = true)
    (hNoTouch : ∀ i, i ≠ 0 → P i → operandTouchesLocal i opSrc = false)
    (hMoveNe0 : ∀ p c, opSrc = .move p → opTgt = .constant c → p.localId ≠ 0) :
    (∃ fk, evalOperandToSlot bodyLocals locs1 opSrc = .error fk ∧
           evalOperandToSlot bodyLocals locs2 opTgt = .error fk) ∨
    (∃ ty optV locs1' locs2',
      evalOperandToSlot bodyLocals locs1 opSrc = .ok (ty, optV, locs1') ∧
      evalOperandToSlot bodyLocals locs2 opTgt = .ok (ty, optV, locs2') ∧
      LocalsMoveDeadRel (fun i => P i ∨ opAddedDead opSrc opTgt i) locs1' locs2') := by
  cases opSrc with
  | copy p1 =>
    cases opTgt with
    | copy p2 =>
      rw [← @operandEq_eq (.copy p1) (.copy p2) hChk]
      cases evalOperandToSlot_moveDead_same hRel hNoTouch with
      | inl hErr => exact Or.inl hErr
      | inr hOk =>
        let ⟨ty, optV, l1', l2', hE1, hE2, hR'⟩ := hOk
        exact Or.inr ⟨ty, optV, l1', l2', hE1, hE2,
          localsMoveDeadRel_mono (fun _ _ h => Or.inl h) hR'⟩
    | _ => cases hChk
  | constant c1 =>
    cases opTgt with
    | constant c2 =>
      rw [← @operandEq_eq (.constant c1) (.constant c2) hChk]
      cases evalOperandToSlot_moveDead_same hRel hNoTouch with
      | inl hErr => exact Or.inl hErr
      | inr hOk =>
        let ⟨ty, optV, l1', l2', hE1, hE2, hR'⟩ := hOk
        exact Or.inr ⟨ty, optV, l1', l2', hE1, hE2,
          localsMoveDeadRel_mono (fun _ _ h => Or.inl h) hR'⟩
    | _ => cases hChk
  | move p =>
    cases opTgt with
    | copy _ => cases hChk
    | move p2 =>
      rw [← @operandEq_eq (.move p) (.move p2) hChk]
      cases evalOperandToSlot_moveDead_same hRel hNoTouch with
      | inl hErr => exact Or.inl hErr
      | inr hOk =>
        let ⟨ty, optV, l1', l2', hE1, hE2, hR'⟩ := hOk
        exact Or.inr ⟨ty, optV, l1', l2', hE1, hE2,
          localsMoveDeadRel_mono (fun _ _ h => Or.inl h) hR'⟩
    | constant c =>
      dsimp [checkConstPropMoveOperand] at hChk
      let ⟨hProj, hRest⟩ := bool_and_true hChk
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hTy] at hRest; cases hRest
      | some ty =>
        rw [hTy] at hRest
        cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
        | none => rw [hAbs] at hRest; cases hRest
        | some abs =>
          rw [hAbs] at hRest; dsimp at hRest
          let ⟨hValC, hImp⟩ := bool_and_true hRest
          let ⟨hcTy, _, vc, hEvC, _⟩ := validTypedConstOperand_elim hValC
          have hLt1 : p.localId < locs1.length := by
            rw [hMatch.2.1]; exact getElem?_some_lt hTy
          let ⟨sl1, hSl1⟩ := getElem?_some_of_lt locs1 p.localId hLt1
          have hM := hMatch.2.2 p.localId ty abs sl1 hTy hAbs hSl1
          let ⟨_, v0, hsl1, hEvL, _⟩ := slotMatchesConst_implies_knownConst hM hImp
          subst hsl1
          rw [hEvC] at hEvL; injection hEvL with hv0; subst hv0
          have hGEq : Trusted.MirSemantics.getElem? locs1 p.localId =
              Trusted.MirSemantics.getElem? locs2 p.localId := by
            apply localsMoveDeadRel_get_eq hRel
            intro hNe0 hPi
            have hT := hNoTouch p.localId hNe0 hPi
            dsimp [operandTouchesLocal] at hT
            rw [nat_beq_refl] at hT; cases hT
          have hSl2 : Trusted.MirSemantics.getElem? locs2 p.localId = some (.live (some vc)) := by
            rw [← hGEq]; exact hSl1
          let ⟨locs1', hSet1⟩ := setElem?_some_of_lt locs1 p.localId (liveUninitSlot ty) hLt1
          let ⟨oNew, hUninitLive⟩ := liveUninitSlot_is_live ty
          have hSet1Live : setElem? locs1 p.localId (.live oNew) = some locs1' := by
            rw [← hUninitLive]; exact hSet1
          have hRel' := localsMoveDeadRel_set_left_live hRel
            (hMoveNe0 p c rfl rfl) hSl2 hSet1Live
          right
          refine ⟨ty, some vc, locs1', locs2, ?_, ?_, hRel'⟩
          · dsimp [evalOperandToSlot]
            rw [hProj, if_bool_false (rfl : (!true) = false), hTy, hSl1]
            dsimp only; rw [hSet1]
          · dsimp [evalOperandToSlot]
            rw [hcTy, hEvC]

private theorem evalPrimitiveOperand_moveDead_step {P : LocalId → Prop}
    {bodyLocals : List MirTy} {env : List ConstAbsSlot}
    {locs1 locs2 : List LocalSlot} {opSrc opTgt : Operand}
    (hMatch : LocalsMatchConstEnv bodyLocals env locs1)
    (hRel : LocalsMoveDeadRel P locs1 locs2)
    (hChk : checkConstPropMoveOperand bodyLocals env opSrc opTgt = true)
    (hNoTouch : ∀ i, i ≠ 0 → P i → operandTouchesLocal i opSrc = false)
    (hMoveNe0 : ∀ p c, opSrc = .move p → opTgt = .constant c → p.localId ≠ 0) :
    (∃ fk, evalPrimitiveOperand bodyLocals locs1 opSrc = .error fk ∧
           evalPrimitiveOperand bodyLocals locs2 opTgt = .error fk) ∨
    (∃ v locs1' locs2',
      evalPrimitiveOperand bodyLocals locs1 opSrc = .ok (v, locs1') ∧
      evalPrimitiveOperand bodyLocals locs2 opTgt = .ok (v, locs2') ∧
      LocalsMoveDeadRel (fun i => P i ∨ opAddedDead opSrc opTgt i) locs1' locs2') := by
  unfold evalPrimitiveOperand
  cases evalOperandToSlot_moveDead_step hMatch hRel hChk hNoTouch hMoveNe0 with
  | inl hErr =>
    let ⟨fk, hE1, hE2⟩ := hErr
    rw [hE1, hE2]
    exact Or.inl ⟨fk, rfl, rfl⟩
  | inr hOk =>
    let ⟨ty, optV, l1', l2', hE1, hE2, hR'⟩ := hOk
    rw [hE1, hE2]; dsimp only
    cases isPrimitiveReadableTy ty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      rw [if_bool_false (rfl : (!true) = false),
          if_bool_false (rfl : (!true) = false)]
      cases optV with
      | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
      | some v => exact Or.inr ⟨v, l1', l2', rfl, rfl, hR'⟩

private theorem isDeadAfterAssignMove_ne0 {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {dst x : LocalId} {restSrc : List StatementKind}
    {termSrc : TerminatorKind}
    (h : isDeadAfterAssignMove deadAtEntry numBlocks dst x restSrc termSrc = true) :
    x ≠ 0 := by
  let ⟨hNotZ, _⟩ := bool_and_true h
  exact nat_ne_of_beq_false (bool_not_true hNotZ)

private theorem isDeadAfterAssignMove_ne_dst {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {dst x : LocalId} {restSrc : List StatementKind}
    {termSrc : TerminatorKind}
    (h : isDeadAfterAssignMove deadAtEntry numBlocks dst x restSrc termSrc = true)
    (hNe : x ≠ dst) :
    isDeadAcrossCfg deadAtEntry numBlocks x restSrc termSrc = true := by
  let ⟨_, hOr⟩ := bool_and_true h
  rw [nat_beq_false_of_ne (Ne.symm hNe)] at hOr
  exact hOr

private theorem checkMoveRewriteDeadRvalue_unary_elim {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {dst : LocalId} {restSrc : List StatementKind}
    {termSrc : TerminatorKind} {uop1 uop2 : UnOp} {o1 o2 : Operand}
    (h : checkMoveRewriteDeadRvalue deadAtEntry numBlocks dst restSrc termSrc
      (.unaryOp uop1 o1) (.unaryOp uop2 o2) = true) :
    (∀ p c, o1 = .move p → o2 = .constant c →
      isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId restSrc termSrc = true) := by
  intro p c ho1 ho2
  subst ho1; subst ho2
  dsimp [checkMoveRewriteDeadRvalue] at h
  exact (bool_and_true h).2

private theorem checkMoveRewriteDeadRvalue_use_elim {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {dst : LocalId} {restSrc : List StatementKind}
    {termSrc : TerminatorKind} {o1 o2 : Operand}
    (h : checkMoveRewriteDeadRvalue deadAtEntry numBlocks dst restSrc termSrc
      (.use o1) (.use o2) = true) :
    (∀ p c, o1 = .move p → o2 = .constant c →
      isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId restSrc termSrc = true) := by
  intro p c ho1 ho2
  subst ho1; subst ho2
  dsimp [checkMoveRewriteDeadRvalue] at h
  exact (bool_and_true h).2

private theorem checkMoveRewriteDeadRvalue_binary_elim {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {dst : LocalId} {restSrc : List StatementKind}
    {termSrc : TerminatorKind} {bop1 bop2 : BinOp} {l1 r1 l2 r2 : Operand}
    (h : checkMoveRewriteDeadRvalue deadAtEntry numBlocks dst restSrc termSrc
      (.binaryOp bop1 l1 r1) (.binaryOp bop2 l2 r2) = true) :
    (∀ p c, l1 = .move p → l2 = .constant c →
      operandTouchesLocal p.localId r1 = false ∧
      isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId restSrc termSrc = true) ∧
    (∀ p c, r1 = .move p → r2 = .constant c →
      isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId restSrc termSrc = true) := by
  dsimp [checkMoveRewriteDeadRvalue] at h
  let ⟨hL, hR⟩ := bool_and_true h
  refine ⟨?_, ?_⟩
  · intro p c hl1 hl2
    subst hl1; subst hl2
    dsimp only at hL
    let ⟨h12, hDead⟩ := bool_and_true hL
    let ⟨_, hNotT⟩ := bool_and_true h12
    exact ⟨bool_not_true hNotT, hDead⟩
  · intro p c hr1 hr2
    subst hr1; subst hr2
    dsimp only at hR
    exact (bool_and_true hR).2

private theorem opAddedDead_implies_afterAssign {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {dst : LocalId} {restSrc : List StatementKind}
    {termSrc : TerminatorKind} {o1 o2 : Operand} {i : LocalId}
    (hElim : ∀ p c, o1 = .move p → o2 = .constant c →
      isDeadAfterAssignMove deadAtEntry numBlocks dst p.localId restSrc termSrc = true)
    (hAdded : opAddedDead o1 o2 i) :
    isDeadAfterAssignMove deadAtEntry numBlocks dst i restSrc termSrc = true := by
  cases o1 with
  | copy _ | constant _ => exact False.elim hAdded
  | move p =>
    cases o2 with
    | copy _ | move _ => exact False.elim hAdded
    | constant c =>
      dsimp [opAddedDead] at hAdded
      subst hAdded
      exact hElim p c rfl rfl

private theorem evalRvalue_moveDead_step {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {bodyLocals : List MirTy} {env : List ConstAbsSlot}
    {locs1 locs2 : List LocalSlot} {dst : Place} {dstTy : MirTy}
    {rvSrc rvTgt : Rvalue} {restSrc : List StatementKind} {termSrc : TerminatorKind}
    (hMatch : LocalsMatchConstEnv bodyLocals env locs1)
    (hRel : LocalsMoveDeadRel
      (fun i => isDeadAcrossCfg deadAtEntry numBlocks i
        (.assign dst rvSrc :: restSrc) termSrc = true)
      locs1 locs2)
    (hChk : checkConstPropMoveRvalue bodyLocals env rvSrc rvTgt = true)
    (hDeadRv : checkMoveRewriteDeadRvalue deadAtEntry numBlocks dst.localId
      restSrc termSrc rvSrc rvTgt = true) :
    (∃ fk, evalRvalue bodyLocals locs1 dstTy rvSrc = .error fk ∧
           evalRvalue bodyLocals locs2 dstTy rvTgt = .error fk) ∨
    (∃ v locs1' locs2',
      evalRvalue bodyLocals locs1 dstTy rvSrc = .ok (v, locs1') ∧
      evalRvalue bodyLocals locs2 dstTy rvTgt = .ok (v, locs2') ∧
      LocalsMoveDeadRel
        (fun i =>
          isDeadAcrossCfg deadAtEntry numBlocks i
            (.assign dst rvSrc :: restSrc) termSrc = true ∨
          isDeadAfterAssignMove deadAtEntry numBlocks dst.localId i
            restSrc termSrc = true)
        locs1' locs2') := by
  have hNotTouchRv : ∀ i, i ≠ 0 →
      isDeadAcrossCfg deadAtEntry numBlocks i (.assign dst rvSrc :: restSrc) termSrc = true →
      rvalueTouchesLocal i rvSrc = false := by
    intro i _ hD
    dsimp [isDeadAcrossCfg] at hD
    exact bool_not_true (bool_and_true hD).1
  cases rvSrc with
  | use o1 =>
    cases rvTgt with
    | use o2 =>
      dsimp [checkConstPropMoveRvalue] at hChk
      have hUseE := checkMoveRewriteDeadRvalue_use_elim hDeadRv
      have hStepO := evalOperandToSlot_moveDead_step hMatch hRel hChk
        (fun i hNe0 hD => hNotTouchRv i hNe0 hD)
        (fun p c ho1 ho2 => isDeadAfterAssignMove_ne0 (hUseE p c ho1 ho2))
      dsimp [evalRvalue]
      cases hStepO with
      | inl hErr =>
        let ⟨fk, e1, e2⟩ := hErr
        rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
      | inr hOk =>
        let ⟨srcTy, optV, l1', l2', e1, e2, hR'⟩ := hOk
        rw [e1, e2]; dsimp only
        cases MirTy.beq srcTy dstTy with
        | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | true =>
          rw [if_bool_false (rfl : (!true) = false),
              if_bool_false (rfl : (!true) = false)]
          cases optV with
          | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
          | some v =>
            refine Or.inr ⟨v, l1', l2', rfl, rfl,
              localsMoveDeadRel_mono ?_ hR'⟩
            intro i _ hDisj
            cases hDisj with
            | inl hP => exact Or.inl hP
            | inr hAdd => exact Or.inr (opAddedDead_implies_afterAssign hUseE hAdd)
    | _ => cases hChk
  | unaryOp uop1 o1 =>
    cases rvTgt with
    | unaryOp uop2 o2 =>
      dsimp [checkConstPropMoveRvalue] at hChk
      let ⟨hOp, hOC⟩ := bool_and_true hChk
      rw [← unOpEq_eq hOp]
      have hUnE := checkMoveRewriteDeadRvalue_unary_elim hDeadRv
      have hStepO := evalPrimitiveOperand_moveDead_step hMatch hRel hOC
        (fun i hNe0 hD => hNotTouchRv i hNe0 hD)
        (fun p c ho1 ho2 => isDeadAfterAssignMove_ne0 (hUnE p c ho1 ho2))
      dsimp [evalRvalue]
      cases hStepO with
      | inl hErr =>
        let ⟨fk, e1, e2⟩ := hErr
        rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
      | inr hOk =>
        let ⟨ov, l1', l2', e1, e2, hR'⟩ := hOk
        rw [e1, e2]; dsimp only
        cases evalUnOp uop1 ov with
        | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
        | ok resV =>
          refine Or.inr ⟨resV, l1', l2', rfl, rfl,
            localsMoveDeadRel_mono ?_ hR'⟩
          intro i _ hDisj
          cases hDisj with
          | inl hP => exact Or.inl hP
          | inr hAdd => exact Or.inr (opAddedDead_implies_afterAssign hUnE hAdd)
    | _ => cases hChk
  | binaryOp bop1 l1 r1 =>
    cases rvTgt with
    | binaryOp bop2 l2 r2 =>
      dsimp [checkConstPropMoveRvalue] at hChk
      let ⟨h12, hRC⟩ := bool_and_true hChk
      let ⟨hOp, hLC⟩ := bool_and_true h12
      rw [← binOpEq_eq hOp]
      let ⟨hBinL, hBinR⟩ := checkMoveRewriteDeadRvalue_binary_elim hDeadRv
      have hNoTouchL : ∀ i, i ≠ 0 →
          isDeadAcrossCfg deadAtEntry numBlocks i (.assign dst (.binaryOp bop1 l1 r1) :: restSrc) termSrc = true →
          operandTouchesLocal i l1 = false := by
        intro i hNe0 hD
        exact (bool_or_false (hNotTouchRv i hNe0 hD)).1
      have hNoTouchR0 : ∀ i, i ≠ 0 →
          isDeadAcrossCfg deadAtEntry numBlocks i (.assign dst (.binaryOp bop1 l1 r1) :: restSrc) termSrc = true →
          operandTouchesLocal i r1 = false := by
        intro i hNe0 hD
        exact (bool_or_false (hNotTouchRv i hNe0 hD)).2
      have hStepL := evalPrimitiveOperand_moveDead_step hMatch hRel hLC hNoTouchL
        (fun p c hl1 hl2 => isDeadAfterAssignMove_ne0 (hBinL p c hl1 hl2).2)
      dsimp [evalRvalue]
      cases hStepL with
      | inl hErrL =>
        let ⟨fk, e1, e2⟩ := hErrL
        rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
      | inr hOkL =>
        let ⟨lv, l1_mid, l2_mid, eL1, eL2, hRelMid⟩ := hOkL
        rw [eL1, eL2]; dsimp only
        have hMatchMid := deinitMovePrimitiveOperand_sound hMatch eL1
        have hNoTouchRMid : ∀ i, i ≠ 0 →
            (isDeadAcrossCfg deadAtEntry numBlocks i (.assign dst (.binaryOp bop1 l1 r1) :: restSrc) termSrc = true ∨
             opAddedDead l1 l2 i) →
            operandTouchesLocal i r1 = false := by
          intro i hNe0 hDisj
          cases hDisj with
          | inl hD => exact hNoTouchR0 i hNe0 hD
          | inr hAddL =>
            cases l1 with
            | copy _ | constant _ => exact False.elim hAddL
            | move pL =>
              cases l2 with
              | copy _ | move _ => exact False.elim hAddL
              | constant cL =>
                dsimp [opAddedDead] at hAddL
                subst hAddL
                exact (hBinL pL cL rfl rfl).1
        have hStepR := evalPrimitiveOperand_moveDead_step hMatchMid hRelMid hRC hNoTouchRMid
          (fun p c hr1 hr2 => isDeadAfterAssignMove_ne0 (hBinR p c hr1 hr2))
        cases hStepR with
        | inl hErrR =>
          let ⟨fk, eR1, eR2⟩ := hErrR
          rw [eR1, eR2]; exact Or.inl ⟨fk, rfl, rfl⟩
        | inr hOkR =>
          let ⟨rvv, l1', l2', eR1, eR2, hRelEnd⟩ := hOkR
          rw [eR1, eR2]; dsimp only
          cases evalBinOp bop1 lv rvv with
          | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
          | ok resV =>
            refine Or.inr ⟨resV, l1', l2', rfl, rfl,
              localsMoveDeadRel_mono ?_ hRelEnd⟩
            intro i _ hDisj
            cases hDisj with
            | inl hMid =>
              cases hMid with
              | inl hD => exact Or.inl hD
              | inr hAddL =>
                exact Or.inr (opAddedDead_implies_afterAssign
                  (fun p c hl1 hl2 => (hBinL p c hl1 hl2).2) hAddL)
            | inr hAddR =>
              exact Or.inr (opAddedDead_implies_afterAssign hBinR hAddR)
    | _ => cases hChk
  | discriminant p1 =>
    rw [← @rvalueEq_eq (.discriminant p1) rvTgt hChk]
    dsimp [evalRvalue]
    cases p1.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      rw [if_bool_false (rfl : (!true) = false),
          if_bool_false (rfl : (!true) = false)]
      have hGEq : Trusted.MirSemantics.getElem? locs1 p1.localId =
          Trusted.MirSemantics.getElem? locs2 p1.localId := by
        apply localsMoveDeadRel_get_eq hRel
        intro hNe0 hD
        have hT := hNotTouchRv p1.localId hNe0 hD
        dsimp [rvalueTouchesLocal] at hT
        rw [nat_beq_refl] at hT; cases hT
      rw [← hGEq]
      cases Trusted.MirSemantics.getElem? bodyLocals p1.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some ty =>
        cases ty with
        | enum ety =>
          cases Trusted.MirSemantics.getElem? locs1 p1.localId with
          | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
          | some sl =>
            dsimp only
            cases enumAdmitted ety with
            | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
            | true =>
              rw [if_bool_false (rfl : (!true) = false),
                  if_bool_false (rfl : (!true) = false)]
              have hRelUp : LocalsMoveDeadRel
                  (fun i =>
                    isDeadAcrossCfg deadAtEntry numBlocks i
                      (.assign dst (.discriminant p1) :: restSrc) termSrc = true ∨
                    isDeadAfterAssignMove deadAtEntry numBlocks dst.localId i
                      restSrc termSrc = true)
                  locs1 locs2 :=
                localsMoveDeadRel_mono (fun _ _ h => Or.inl h) hRel
              cases ety.tagRepr with
              | zeroSized =>
                cases sl with
                | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
                | live opt =>
                  cases opt with
                  | none =>
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                    | some disc => exact Or.inr ⟨_, locs1, locs2, rfl, rfl, hRelUp⟩
                  | some v0 =>
                    cases v0 with
                    | enumVal ety' k =>
                      dsimp only
                      cases (EnumTy.beq ety ety' && Nat.beq k 0) with
                      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                      | true =>
                        rw [if_bool_true rfl, if_bool_true rfl]
                        cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                        | some disc => exact Or.inr ⟨_, locs1, locs2, rfl, rfl, hRelUp⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ =>
                      exact Or.inl ⟨.unsupported, rfl, rfl⟩
              | scalar _ _ =>
                cases sl with
                | dead => exact Or.inl ⟨.undefined, rfl, rfl⟩
                | live opt =>
                  cases opt with
                  | none => exact Or.inl ⟨.undefined, rfl, rfl⟩
                  | some v0 =>
                    cases v0 with
                    | enumVal ety' k =>
                      dsimp only
                      cases (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
                      | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                      | true =>
                        rw [if_bool_true rfl, if_bool_true rfl]
                        cases Trusted.MirSemantics.getElem? ety.discriminants k with
                        | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
                        | some disc => exact Or.inr ⟨_, locs1, locs2, rfl, rfl, hRelUp⟩
                    | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ =>
                      exact Or.inl ⟨.unsupported, rfl, rfl⟩
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
          exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | ref m1 p1 =>
    rw [← @rvalueEq_eq (.ref m1 p1) rvTgt hChk]
    exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | addressOf m1 p1 =>
    rw [← @rvalueEq_eq (.addressOf m1 p1) rvTgt hChk]
    exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | aggregateTuple fs1 =>
    rw [← @rvalueEq_eq (.aggregateTuple fs1) rvTgt hChk]
    exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | unsupported =>
    rw [← @rvalueEq_eq .unsupported rvTgt hChk]
    exact Or.inl ⟨.unsupported, rfl, rfl⟩

private theorem checkDeadAtEntryLoop_get {bSrc : Body}
    {deadAtEntry rest : List (List LocalId)} {base k : Nat} {ds : List LocalId}
    (hLoop : checkDeadAtEntryLoop bSrc deadAtEntry base rest = true)
    (hGet : Trusted.MirSemantics.getElem? rest k = some ds) :
    ∃ bbSrc,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks (base + k) = some bbSrc ∧
      ds.all (fun d =>
        !Nat.beq d 0 &&
          isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length d
            bbSrc.statements bbSrc.terminator) = true := by
  induction rest generalizing base k with
  | nil => cases hGet
  | cons hd tl ih =>
    dsimp [checkDeadAtEntryLoop] at hLoop
    let ⟨hHere, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hGet with hEq; subst hEq
      rw [Nat.add_zero]
      cases hBB : Trusted.MirSemantics.getElem? bSrc.basicBlocks base with
      | none => rw [hBB] at hHere; cases hHere
      | some bbSrc =>
        rw [hBB] at hHere
        exact ⟨bbSrc, rfl, hHere⟩
    | succ m =>
      let ⟨bbSrc, hBB, hAll⟩ := ih hTail hGet
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hBB
      exact ⟨bbSrc, hBB, hAll⟩

private theorem isDeadAtTarget_sound {bSrc : Body} {deadAtEntry : List (List LocalId)}
    {d : LocalId} {target : BasicBlockId} {bbTarget : BasicBlock}
    (hLoop : checkDeadAtEntryLoop bSrc deadAtEntry 0 deadAtEntry = true)
    (hDeadT : isDeadAtTarget deadAtEntry bSrc.basicBlocks.length d target = true)
    (hBB : Trusted.MirSemantics.getElem? bSrc.basicBlocks target = some bbTarget) :
    isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length d
      bbTarget.statements bbTarget.terminator = true := by
  unfold isDeadAtTarget at hDeadT
  let ⟨_, hOpt⟩ := bool_and_true hDeadT
  cases hDS : Trusted.MirSemantics.getElem? deadAtEntry target with
  | none => rw [hDS] at hOpt; cases hOpt
  | some ds =>
    rw [hDS] at hOpt
    let ⟨bbSrc', hBB', hAll⟩ := checkDeadAtEntryLoop_get hLoop hDS
    rw [Nat.zero_add, hBB] at hBB'
    injection hBB' with hEqB; subst hEqB
    exact (bool_and_true (natElem_all hAll hOpt)).2

private theorem checkMoveRewriteDeadBlocksLoop_get {bSrc bTgt : Body}
    {cert : BodyConstMoveDeadCert} {base k : Nat} {rest : List BasicBlock}
    {bbSrc bbTgt : BasicBlock} {entryEnv : List ConstAbsSlot}
    (hLoop : checkMoveRewriteDeadBlocksLoop bSrc bTgt cert base rest = true)
    (hGet : Trusted.MirSemantics.getElem? rest k = some bbSrc)
    (hCGet : Trusted.MirSemantics.getElem? cert.constCert (base + k) = some (some entryEnv))
    (hBBTgt : Trusted.MirSemantics.getElem? bTgt.basicBlocks (base + k) = some bbTgt) :
    checkMoveRewriteDeadStmts cert.deadAtEntry bSrc.basicBlocks.length
      bbSrc.terminator bbSrc.statements bbTgt.statements = true ∧
    checkMoveRewriteDeadTerm cert.deadAtEntry bSrc.basicBlocks.length
      bbSrc.terminator bbTgt.terminator = true := by
  induction rest generalizing base k with
  | nil => cases hGet
  | cons hd tl ih =>
    dsimp [checkMoveRewriteDeadBlocksLoop] at hLoop
    let ⟨hHere, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hGet with hEq; subst hEq
      rw [Nat.add_zero] at hCGet hBBTgt
      rw [hCGet, hBBTgt] at hHere; dsimp at hHere
      exact bool_and_true hHere
    | succ m =>
      have hIdx : base + (m + 1) = base + 1 + m := by
        rw [Nat.add_assoc, Nat.add_comm 1 m]
      rw [hIdx] at hCGet hBBTgt
      exact ih hTail hGet hCGet hBBTgt

private noncomputable def checkMoveRewriteDeadStmtPair (deadAtEntry : List (List LocalId))
    (numBlocks : Nat) (restSrc : List StatementKind) (termSrc : TerminatorKind)
    (sSrc sTgt : StatementKind) : Bool :=
  match sSrc, sTgt with
  | .assign dstPlace rvSrc, .assign _ rvTgt =>
    dstPlace.projection.isEmpty &&
      checkMoveRewriteDeadRvalue deadAtEntry numBlocks dstPlace.localId
        restSrc termSrc rvSrc rvTgt
  | _, _ => true

private theorem checkMoveRewriteDeadStmts_cons_elim {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {termSrc : TerminatorKind}
    {sSrc sTgt : StatementKind} {restSrc restTgt : List StatementKind}
    (h : checkMoveRewriteDeadStmts deadAtEntry numBlocks termSrc
      (sSrc :: restSrc) (sTgt :: restTgt) = true) :
    checkMoveRewriteDeadStmtPair deadAtEntry numBlocks restSrc termSrc sSrc sTgt = true ∧
    checkMoveRewriteDeadStmts deadAtEntry numBlocks termSrc restSrc restTgt = true := by
  have hFold :
      (checkMoveRewriteDeadStmtPair deadAtEntry numBlocks restSrc termSrc sSrc sTgt &&
        checkMoveRewriteDeadStmts deadAtEntry numBlocks termSrc restSrc restTgt) = true := by
    cases sSrc <;> cases sTgt <;> exact h
  exact bool_and_true hFold

private theorem evalStatement_moveDead_step {bSrc bTgt : Body}
    {deadAtEntry : List (List LocalId)} {env : List ConstAbsSlot}
    {fSrc fTgt : FrameState} {cm : CallerMemory}
    {sSrc sTgt : StatementKind} {restSrc : List StatementKind} {termSrc : TerminatorKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hIdxEq : fSrc.stmtIdx = fTgt.stmtIdx)
    (hMatch : LocalsMatchConstEnv bSrc.locals env fSrc.locals)
    (hRel : LocalsMoveDeadRel
      (fun i => isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i
        (sSrc :: restSrc) termSrc = true)
      fSrc.locals fTgt.locals)
    (hOkMove : checkConstPropMoveStmtPair bSrc.locals env sSrc sTgt = true)
    (hOkDead : checkMoveRewriteDeadStmtPair deadAtEntry bSrc.basicBlocks.length
      restSrc termSrc sSrc sTgt = true) :
    (∃ fk, evalStatement bSrc fSrc cm sSrc = .fault fk ∧
           evalStatement bTgt fTgt cm sTgt = .fault fk) ∨
    (∃ locs1' locs2',
      evalStatement bSrc fSrc cm sSrc =
        .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' }],
                callerMem := cm } ∧
      evalStatement bTgt fTgt cm sTgt =
        .step { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' }],
                callerMem := cm } ∧
      LocalsMoveDeadRel
        (fun i => isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i restSrc termSrc = true)
        locs1' locs2') := by
  let _ := hIdxEq
  cases sSrc with
  | nop =>
    dsimp [checkConstPropMoveStmtPair] at hOkMove
    rw [← @stmtEq_eq .nop sTgt hOkMove]
    right
    exact ⟨fSrc.locals, fTgt.locals, rfl, rfl, hRel⟩
  | unsupported =>
    dsimp [checkConstPropMoveStmtPair] at hOkMove
    rw [← @stmtEq_eq .unsupported sTgt hOkMove]
    exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | storageLive id =>
    dsimp [checkConstPropMoveStmtPair] at hOkMove
    rw [← @stmtEq_eq (.storageLive id) sTgt hOkMove]
    dsimp [evalStatement]
    rw [← hLocEq]
    cases Trusted.MirSemantics.getElem? bSrc.locals id with
    | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | some localTy =>
      dsimp only
      cases hSet1 : setElem? fSrc.locals id (liveUninitSlot localTy) with
      | none =>
        rw [setElem?_none_of_length_eq hRel.1 hSet1]
        exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some locs1' =>
        have hImp : ∀ i, i ≠ 0 → i ≠ id →
            isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i (.storageLive id :: restSrc) termSrc = true →
            isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i restSrc termSrc = true := by
          intro i _ hNe hD
          dsimp [isDeadAcrossCfg] at hD
          rw [nat_beq_false_of_ne (Ne.symm hNe), if_bool_false rfl] at hD
          exact hD
        let ⟨locs2', hSet2, hRel'⟩ := localsMoveDeadRel_set_both hRel hImp hSet1
        rw [hSet2]
        exact Or.inr ⟨locs1', locs2', rfl, rfl, hRel'⟩
  | storageDead id =>
    dsimp [checkConstPropMoveStmtPair] at hOkMove
    rw [← @stmtEq_eq (.storageDead id) sTgt hOkMove]
    dsimp [evalStatement]
    cases Nat.beq id 0 with
    | true => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | false =>
      rw [if_bool_false rfl, if_bool_false rfl]
      cases hSet1 : setElem? fSrc.locals id .dead with
      | none =>
        rw [setElem?_none_of_length_eq hRel.1 hSet1]
        exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some locs1' =>
        have hImp : ∀ i, i ≠ 0 → i ≠ id →
            isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i (.storageDead id :: restSrc) termSrc = true →
            isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i restSrc termSrc = true := by
          intro i _ hNe hD
          dsimp [isDeadAcrossCfg] at hD
          rw [nat_beq_false_of_ne (Ne.symm hNe), if_bool_false rfl] at hD
          exact hD
        let ⟨locs2', hSet2, hRel'⟩ := localsMoveDeadRel_set_both hRel hImp hSet1
        rw [hSet2]
        exact Or.inr ⟨locs1', locs2', rfl, rfl, hRel'⟩
  | assign d1 rv1 =>
    cases sTgt with
    | nop | storageLive _ | storageDead _ | unsupported =>
      dsimp [checkConstPropMoveStmtPair] at hOkMove
      cases hOkMove
    | assign d2 rv2 =>
      dsimp [checkConstPropMoveStmtPair] at hOkMove
      let ⟨h12, hRvC⟩ := bool_and_true hOkMove
      let ⟨hPEq, hDEmp⟩ := bool_and_true h12
      have hdEq := placeEq_eq hPEq; subst hdEq
      dsimp [checkMoveRewriteDeadStmtPair] at hOkDead
      let ⟨_, hDeadRv⟩ := bool_and_true hOkDead
      dsimp [evalStatement]
      rw [hDEmp, if_bool_false (rfl : (!true) = false),
          if_bool_false (rfl : (!true) = false), ← hLocEq]
      cases Trusted.MirSemantics.getElem? bSrc.locals d1.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some dstTy =>
        dsimp only
        cases evalRvalue_moveDead_step hMatch hRel hRvC hDeadRv (dstTy := dstTy) with
        | inl hErrRv =>
          let ⟨fk, e1, e2⟩ := hErrRv
          rw [e1, e2]; exact Or.inl ⟨fk, rfl, rfl⟩
        | inr hOkRv =>
          let ⟨val, l1_rv, l2_rv, e1, e2, hRelRv⟩ := hOkRv
          rw [e1, e2]; dsimp only
          have hImpW : ∀ i, i ≠ 0 → i ≠ d1.localId →
              (isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i (.assign d1 rv1 :: restSrc) termSrc = true ∨
               isDeadAfterAssignMove deadAtEntry bSrc.basicBlocks.length d1.localId i restSrc termSrc = true) →
              isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i restSrc termSrc = true := by
            intro i _ hNe hDisj
            cases hDisj with
            | inl hD =>
              dsimp [isDeadAcrossCfg] at hD
              let ⟨_, hIf⟩ := bool_and_true hD
              rw [hDEmp, nat_beq_false_of_ne (Ne.symm hNe),
                  if_bool_false (rfl : (true && false) = false)] at hIf
              exact hIf
            | inr hAft =>
              exact isDeadAfterAssignMove_ne_dst hAft hNe
          cases writePlace_moveDeadRel hRelRv hImpW (dstTy := dstTy) (val := val) with
          | inl hErrW =>
            let ⟨fk, w1, w2⟩ := hErrW
            rw [w1, w2]; exact Or.inl ⟨fk, rfl, rfl⟩
          | inr hOkW =>
            let ⟨locs1', locs2', w1, w2, hRel'⟩ := hOkW
            rw [w1, w2]
            exact Or.inr ⟨locs1', locs2', rfl, rfl, hRel'⟩

private theorem checkMoveRewriteDeadTerm_elim {deadAtEntry : List (List LocalId)}
    {numBlocks : Nat} {d1 d2 : Operand} {ts1 ts2 : SwitchTargets}
    (h : checkMoveRewriteDeadTerm deadAtEntry numBlocks
      (.switchInt d1 ts1) (.switchInt d2 ts2) = true) :
    ∀ p c, d1 = .move p → d2 = .constant c →
      p.localId ≠ 0 ∧
      isDeadAtTarget deadAtEntry numBlocks p.localId ts1.otherwise = true ∧
      ts1.branches.all (fun br =>
        isDeadAtTarget deadAtEntry numBlocks p.localId br.2) = true := by
  intro p c hd1 hd2
  subst hd1; subst hd2
  dsimp [checkMoveRewriteDeadTerm] at h
  let ⟨h123, hBr⟩ := bool_and_true h
  let ⟨h12, hOw⟩ := bool_and_true h123
  let ⟨_, hNotZ⟩ := bool_and_true h12
  exact ⟨nat_ne_of_beq_false (bool_not_true hNotZ), hOw, hBr⟩

private theorem evalTerminator_moveDead_step {bSrc bTgt : Body}
    {deadAtEntry : List (List LocalId)} {bbSrc bbTgt : BasicBlock}
    {env : List ConstAbsSlot} {fSrc fTgt : FrameState} {cm : CallerMemory}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hCleanEq : bbSrc.cleanup = bbTgt.cleanup)
    (hMatch : LocalsMatchConstEnv bSrc.locals env fSrc.locals)
    (hRel : LocalsMoveDeadRel
      (fun i => isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i
        [] bbSrc.terminator = true)
      fSrc.locals fTgt.locals)
    (hTermC : checkConstPropMoveTerminator bSrc.locals env
      bbSrc.terminator bbTgt.terminator = true)
    (hTermDead : checkMoveRewriteDeadTerm deadAtEntry bSrc.basicBlocks.length
      bbSrc.terminator bbTgt.terminator = true) :
    (∃ tgt locs1' locs2',
      evalTerminator bSrc bbSrc fSrc cm =
        .step { frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs1' }],
                callerMem := cm } ∧
      evalTerminator bTgt bbTgt fTgt cm =
        .step { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' }],
                callerMem := cm } ∧
      LocalsMoveDeadRel
        (fun i => isDeadAtTarget deadAtEntry bSrc.basicBlocks.length i tgt = true)
        locs1' locs2') ∨
    (∃ out, evalTerminator bSrc bbSrc fSrc cm = .done out ∧
            evalTerminator bTgt bbTgt fTgt cm = .done out) ∨
    (∃ fk, evalTerminator bSrc bbSrc fSrc cm = .fault fk ∧
           evalTerminator bTgt bbTgt fTgt cm = .fault fk) := by
  cases hT1 : bbSrc.terminator with
  | goto tgt =>
    rw [hT1] at hTermC hRel
    have hT2 := @terminatorEq_eq (.goto tgt) bbTgt.terminator hTermC
    unfold evalTerminator
    rw [hT1, ← hT2]
    exact Or.inl ⟨tgt, fSrc.locals, fTgt.locals, rfl, rfl, hRel⟩
  | return_ =>
    rw [hT1] at hTermC
    have hT2 := @terminatorEq_eq .return_ bbTgt.terminator hTermC
    unfold evalTerminator
    rw [hT1, ← hT2, ← hCleanEq]
    cases bbSrc.cleanup with
    | true => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
    | false =>
      rw [if_bool_false rfl, if_bool_false rfl]
      rw [← localsMoveDeadRel_get0_eq hRel]
      cases Trusted.MirSemantics.getElem? fSrc.locals 0 with
      | none => exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
      | some sl0 =>
        cases sl0 with
        | dead => exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
        | live optV =>
          cases optV with
          | none => exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
          | some retVal => exact Or.inr (Or.inl ⟨.returned ⟨retVal, cm⟩, rfl, rfl⟩)
  | unreachable =>
    rw [hT1] at hTermC
    have hT2 := @terminatorEq_eq .unreachable bbTgt.terminator hTermC
    unfold evalTerminator; rw [hT1, ← hT2]
    exact Or.inr (Or.inr ⟨.undefined, rfl, rfl⟩)
  | unwindResume =>
    rw [hT1] at hTermC
    have hT2 := @terminatorEq_eq .unwindResume bbTgt.terminator hTermC
    unfold evalTerminator; rw [hT1, ← hT2]
    exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
  | assert c1 e1 m1 t1 u1 =>
    rw [hT1] at hTermC
    have hT2 := @terminatorEq_eq (.assert c1 e1 m1 t1 u1) bbTgt.terminator hTermC
    unfold evalTerminator; rw [hT1, ← hT2]
    exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
  | call f1 as1 d1 t1 u1 =>
    rw [hT1] at hTermC
    have hT2 := @terminatorEq_eq (.call f1 as1 d1 t1 u1) bbTgt.terminator hTermC
    unfold evalTerminator; rw [hT1, ← hT2]
    exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
  | unsupported =>
    rw [hT1] at hTermC
    have hT2 := @terminatorEq_eq .unsupported bbTgt.terminator hTermC
    unfold evalTerminator; rw [hT1, ← hT2]
    exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)
  | switchInt d1 ts1 =>
    rw [hT1] at hTermC hTermDead hRel
    cases hT2 : bbTgt.terminator with
    | goto _ | return_ | unreachable | unwindResume | assert _ _ _ _ _
    | call _ _ _ _ _ | unsupported =>
      rw [hT2] at hTermC; cases hTermC
    | switchInt d2 ts2 =>
      rw [hT2] at hTermC hTermDead
      dsimp [checkConstPropMoveTerminator] at hTermC
      let ⟨hDC, hTsEqB⟩ := bool_and_true hTermC
      have hTsEq := switchTargetsEq_eq hTsEqB; subst hTsEq
      have hSwE := checkMoveRewriteDeadTerm_elim hTermDead
      have hNoTouchD : ∀ i, i ≠ 0 →
          isDeadAcrossCfg deadAtEntry bSrc.basicBlocks.length i [] (.switchInt d1 ts1) = true →
          operandTouchesLocal i d1 = false := by
        intro i _ hD
        dsimp [isDeadAcrossCfg] at hD
        let ⟨h12, _⟩ := bool_and_true hD
        exact bool_not_true (bool_and_true h12).1
      have hStepD := evalPrimitiveOperand_moveDead_step hMatch hRel hDC hNoTouchD
        (fun p c hd1 hd2 => (hSwE p c hd1 hd2).1)
      unfold evalTerminator
      rw [hT1, hT2, ← hLocEq]
      dsimp only
      cases hStepD with
      | inl hErrD =>
        let ⟨fk, e1, e2⟩ := hErrD
        rw [e1, e2]; exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
      | inr hOkD =>
        let ⟨dv, locs1', locs2', e1, e2, hRelAfterD⟩ := hOkD
        rw [e1, e2]; dsimp only
        have hAtTgt : ∀ tgt,
            (tgt = ts1.otherwise ∨ ∃ idx cb, Trusted.MirSemantics.getElem? ts1.branches idx = some (cb, tgt)) →
            LocalsMoveDeadRel
              (fun i => isDeadAtTarget deadAtEntry bSrc.basicBlocks.length i tgt = true)
              locs1' locs2' := by
          intro tgt hOut
          apply localsMoveDeadRel_mono ?_ hRelAfterD
          intro i _ hDisj
          cases hDisj with
          | inl hPre =>
            dsimp [isDeadAcrossCfg] at hPre
            let ⟨h12, hBrAll⟩ := bool_and_true hPre
            let ⟨_, hOw⟩ := bool_and_true h12
            cases hOut with
            | inl hEqOw => subst hEqOw; exact hOw
            | inr hBr =>
              let ⟨idx, cb, hGetBr⟩ := hBr
              exact list_all_getElem?
                (p := fun br => isDeadAtTarget deadAtEntry bSrc.basicBlocks.length i br.2)
                hBrAll hGetBr
          | inr hAdd =>
            cases d1 with
            | copy _ | constant _ => exact False.elim hAdd
            | move p =>
              cases d2 with
              | copy _ | move _ => exact False.elim hAdd
              | constant c =>
                dsimp [opAddedDead] at hAdd; subst hAdd
                let ⟨_, hOw, hBrAll⟩ := hSwE p c rfl rfl
                cases hOut with
                | inl hEqOw => subst hEqOw; exact hOw
                | inr hBr =>
                  let ⟨idx, cb, hGetBr⟩ := hBr
                  exact list_all_getElem?
                    (p := fun br => isDeadAtTarget deadAtEntry bSrc.basicBlocks.length p.localId br.2)
                    hBrAll hGetBr
        cases dv with
        | scalar sv =>
          dsimp only
          cases hSw : evalSwitchBranches sv.width sv.bits ts1.otherwise ts1.branches with
          | error fk => exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
          | ok tgt =>
            have hOut : tgt = ts1.otherwise ∨ ∃ idx cb, Trusted.MirSemantics.getElem? ts1.branches idx = some (cb, tgt) := by
              cases evalSwitchBranches_outcome hSw with
              | inl hOw => exact Or.inl hOw
              | inr hB => let ⟨idx, cb, hG, _, _⟩ := hB; exact Or.inr ⟨idx, cb, hG⟩
            exact Or.inl ⟨tgt, locs1', locs2', rfl, rfl, hAtTgt tgt hOut⟩
        | bool b =>
          dsimp only
          cases hSw : evalBoolSwitchBranches b ts1.otherwise ts1.branches with
          | error fk => exact Or.inr (Or.inr ⟨fk, rfl, rfl⟩)
          | ok tgt =>
            have hOut : tgt = ts1.otherwise ∨ ∃ idx cb, Trusted.MirSemantics.getElem? ts1.branches idx = some (cb, tgt) := by
              cases evalBoolSwitchBranches_outcome hSw with
              | inl hOw => exact Or.inl hOw
              | inr hB => let ⟨idx, cb, hG, _⟩ := hB; exact Or.inr ⟨idx, cb, hG⟩
            exact Or.inl ⟨tgt, locs1', locs2', rfl, rfl, hAtTgt tgt hOut⟩
        | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ =>
          exact Or.inr (Or.inr ⟨.unsupported, rfl, rfl⟩)

private theorem constPropMoveDead_listRel_to_constCert {cs : List BodyConstMoveDeadCert}
    {bs1 bs2 : List Body}
    (hLen : Nat.beq cs.length bs1.length = true)
    (hRel : listRel (fun cPr bTgt => checkConstPropMoveDeadBody cPr.1 cPr.2 bTgt)
      (List.zip cs bs1) bs2 = true) :
    listRel (fun cPr bTgt => checkConstPropMoveBody cPr.1 cPr.2 bTgt)
      (List.zip (cs.map BodyConstMoveDeadCert.constCert) bs1) bs2 = true := by
  induction cs generalizing bs1 bs2 with
  | nil =>
    cases bs1 with
    | nil =>
      cases bs2 with
      | nil => rfl
      | cons _ _ => cases hRel
    | cons _ _ => cases hLen
  | cons c cs ih =>
    cases bs1 with
    | nil => cases hLen
    | cons b1 bs1 =>
      cases bs2 with
      | nil => cases hRel
      | cons b2 bs2 =>
        dsimp [List.zip, listRel] at hRel
        let ⟨hHere, hTail⟩ := bool_and_true hRel
        let ⟨h12, _⟩ := bool_and_true hHere
        let ⟨hMoveBody, _⟩ := bool_and_true h12
        dsimp [List.map, List.zip, listRel]
        exact bool_and_intro hMoveBody (ih hLen hTail)

private theorem list_length_map_local {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (list_length_map_local f xs)

private theorem constPropMoveDead_to_constCert {cert : ProgramConstMoveDeadCert}
    {pSrc pTgt : Program}
    (hCert : checkConstPropMoveDeadProgram cert pSrc pTgt = true) :
    checkConstPropMoveProgram (cert.map BodyConstMoveDeadCert.constCert) pSrc pTgt = true := by
  let ⟨hLenB, hRel⟩ := bool_and_true hCert
  apply bool_and_intro
  · rw [list_length_map_local]; exact hLenB
  · exact constPropMoveDead_listRel_to_constCert hLenB hRel

private noncomputable def ConstPropMoveDeadRel (pSrc pTgt : Program)
    (cert : ProgramConstMoveDeadCert) (s t : State) : Prop :=
  ∃ fSrc fTgt bSrc bTgt cBody,
    s.frames = [fSrc] ∧
    t.frames = [fTgt] ∧
    s.callerMem = t.callerMem ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    fSrc.stmtIdx = fTgt.stmtIdx ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies fSrc.defId = some bTgt ∧
    Trusted.MirSemantics.getElem? cert fSrc.defId = some cBody ∧
    isConstPropMoveBody bSrc bTgt = true ∧
    checkConstPropMoveDeadBody cBody bSrc bTgt = true ∧
    (bSrc.basicBlocks.length ≤ fSrc.blockIdx ∨
      ∃ bbSrc bbTgt entryEnv curEnv exitEnv,
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks fSrc.blockIdx = some bbTgt ∧
        Trusted.MirSemantics.getElem? cBody.constCert fSrc.blockIdx = some (some entryEnv) ∧
        fSrc.stmtIdx ≤ bbSrc.statements.length ∧
        LocalsMatchConstEnv bSrc.locals curEnv fSrc.locals ∧
        LocalsMoveDeadRel
          (fun i => isDeadAcrossCfg cBody.deadAtEntry bSrc.basicBlocks.length i
            (bbSrc.statements.drop fSrc.stmtIdx) bbSrc.terminator = true)
          fSrc.locals fTgt.locals ∧
        stepConstPropMoveCertStmts bSrc.locals curEnv
          (bbSrc.statements.drop fSrc.stmtIdx)
          (bbTgt.statements.drop fSrc.stmtIdx) = some exitEnv ∧
        checkMoveRewriteDeadStmts cBody.deadAtEntry bSrc.basicBlocks.length
          bbSrc.terminator
          (bbSrc.statements.drop fSrc.stmtIdx)
          (bbTgt.statements.drop fSrc.stmtIdx) = true ∧
        checkConstPropMoveTerminator bSrc.locals exitEnv
          bbSrc.terminator bbTgt.terminator = true ∧
        checkMoveRewriteDeadTerm cBody.deadAtEntry bSrc.basicBlocks.length
          bbSrc.terminator bbTgt.terminator = true ∧
        checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length
          cBody.constCert exitEnv bbSrc.terminator = true)

private theorem constPropMoveDead_block_entry {bSrc bTgt : Body}
    {cBody : BodyConstMoveDeadCert} {bbIdx : BasicBlockId}
    {tgtEnv : List ConstAbsSlot} {locs1 locs2 : List LocalSlot}
    (hBRel : isConstPropMoveBody bSrc bTgt = true)
    (hBCert : checkConstPropMoveDeadBody cBody bSrc bTgt = true)
    (hLt : bbIdx < bSrc.basicBlocks.length)
    (hCGet : Trusted.MirSemantics.getElem? cBody.constCert bbIdx = some (some tgtEnv))
    (hMatch : LocalsMatchConstEnv bSrc.locals tgtEnv locs1)
    (hDeadEntry : ∀ bbSrc,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc →
      LocalsMoveDeadRel
        (fun i => isDeadAcrossCfg cBody.deadAtEntry bSrc.basicBlocks.length i
          bbSrc.statements bbSrc.terminator = true)
        locs1 locs2) :
    ∃ bbSrc bbTgt exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt ∧
      0 ≤ bbSrc.statements.length ∧
      LocalsMatchConstEnv bSrc.locals tgtEnv locs1 ∧
      LocalsMoveDeadRel
        (fun i => isDeadAcrossCfg cBody.deadAtEntry bSrc.basicBlocks.length i
          (bbSrc.statements.drop 0) bbSrc.terminator = true)
        locs1 locs2 ∧
      stepConstPropMoveCertStmts bSrc.locals tgtEnv
        (bbSrc.statements.drop 0) (bbTgt.statements.drop 0) = some exitEnv ∧
      checkMoveRewriteDeadStmts cBody.deadAtEntry bSrc.basicBlocks.length
        bbSrc.terminator (bbSrc.statements.drop 0) (bbTgt.statements.drop 0) = true ∧
      checkConstPropMoveTerminator bSrc.locals exitEnv
        bbSrc.terminator bbTgt.terminator = true ∧
      checkMoveRewriteDeadTerm cBody.deadAtEntry bSrc.basicBlocks.length
        bbSrc.terminator bbTgt.terminator = true ∧
      checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length
        cBody.constCert exitEnv bbSrc.terminator = true := by
  let ⟨h12, hDeadLoop⟩ := bool_and_true hBCert
  let ⟨hMoveBody, _⟩ := bool_and_true h12
  let ⟨bbSrc, bbTgt, exitEnv, hBBS, hBBT, hLe0, hM, hSt0, hTm0, hEd0⟩ :=
    constPropMove_block_entry hBRel hMoveBody hLt hCGet hMatch
  have hCGet0 : Trusted.MirSemantics.getElem? cBody.constCert (0 + bbIdx) = some (some tgtEnv) := by
    rw [Nat.zero_add]; exact hCGet
  have hBBT0 : Trusted.MirSemantics.getElem? bTgt.basicBlocks (0 + bbIdx) = some bbTgt := by
    rw [Nat.zero_add]; exact hBBT
  let ⟨hDeadSt0, hDeadTm0⟩ := checkMoveRewriteDeadBlocksLoop_get hDeadLoop hBBS hCGet0 hBBT0
  exact ⟨bbSrc, bbTgt, exitEnv, hBBS, hBBT, hLe0, hM, hDeadEntry bbSrc hBBS,
         hSt0, hDeadSt0, hTm0, hDeadTm0, hEd0⟩

private theorem constPropMoveDead_query_iff {pSrc pTgt : Program}
    {cert : ProgramConstMoveDeadCert}
    (hRel : isConstPropMoveProgram pSrc pTgt = true)
    (hCert : checkConstPropMoveDeadProgram cert pSrc pTgt = true)
    (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hMoveCert := constPropMoveDead_to_constCert hCert
  have hInitEq := isConstPropMoveProgram_initState_eq hRel hMoveCert q
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLen, hCertBodies⟩ := bool_and_true hCert
  let ⟨_, hCertAt, _⟩ := listRel_zip_left_rel (nat_beq_eq hCertLen) hCertBodies
  apply bisim_lift_disj (R := ConstPropMoveDeadRel pSrc pTgt cert)
    (fun k => by rw [hInitEq])
  · intro s₀ t₀ hIS hIT
    have hInitS : initState pSrc q = .ok s₀ := hIS
    rw [hInitEq, hIT] at hIS; injection hIS with hST; subst hST
    let ⟨_, _, bSrc0, hBSrc0, hNotEmpty0, _, _, _, hArgs0, hEqS0⟩ := initState_ok_elim hInitS
    subst hEqS0
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodiesRel hBSrc0
    let ⟨cBody, bTgt', hCBody, hBTgt', hBCert⟩ := hCertAt pSrc.entryDefId bSrc0 hBSrc0
    rw [hBTgt] at hBTgt'; injection hBTgt' with hEqB; subst hEqB
    let ⟨h12, _⟩ := bool_and_true hBCert
    let ⟨hMoveBody, _⟩ := bool_and_true h12
    let ⟨hm123, _⟩ := bool_and_true hMoveBody
    let ⟨_, hEntryOk⟩ := bool_and_true hm123
    rw [hNotEmpty0, if_bool_false rfl] at hEntryOk
    cases hC0 : Trusted.MirSemantics.getElem? cBody.constCert 0 with
    | none => rw [hC0] at hEntryOk; cases hEntryOk
    | some opt0 =>
      rw [hC0] at hEntryOk
      cases opt0 with
      | none => cases hEntryOk
      | some env₀ =>
        have hMatch0 := localsMatchConstEnv_mono hEntryOk (initConstEnvLoop_matches hArgs0)
        have hPos := list_pos_of_isEmpty_false hNotEmpty0
        let ⟨bbSrc, bbTgt, exitEnv, hBBS, hBBT, hLe0, hM0, hDR0, hSt0, hDSt0, hTm0, hDTm0, hEd0⟩ :=
          constPropMoveDead_block_entry hBRel hBCert hPos hC0 hMatch0
            (fun _ _ => localsMoveDeadRel_refl _ _)
        exact ⟨_, _, bSrc0, bTgt, cBody,
               rfl, rfl, rfl, rfl, rfl, rfl, hBSrc0, hBTgt, hCBody, hBRel, hBCert,
               Or.inr ⟨bbSrc, bbTgt, env₀, env₀, exitEnv,
                       hBBS, hBBT, hC0, hLe0, hM0, hDR0, hSt0, hDSt0, hTm0, hDTm0, hEd0⟩⟩
  · intro s t hR
    let ⟨fSrc, fTgt, bSrc, bTgt, cBody, hFS, hFT, hCM, hDefEq, hBlkEq, hIdxEq,
         hBSrc, hBTgt, hCBody, hBRel, hBCert, hBlkInv⟩ := hR
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    let ⟨h12C, _⟩ := bool_and_true hBCert
    let ⟨_, hEntryDeadLoop⟩ := bool_and_true h12C
    have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
      rw [← hDefEq]; exact hBTgt
    cases s with
    | mk fsS cmS =>
      cases t with
      | mk fsT cmT =>
        dsimp at hFS hFT hCM
        subst hFS; subst hFT; subst hCM
        cases hBlkInv with
        | inl hOob =>
          have hNoneS := getElem?_none_of_ge hOob
          have hNoneT : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = none := by
            rw [← hBlkEq]; exact (listRel_getElem?_none_iff fSrc.blockIdx hBBsRel).mp hNoneS
          right; right
          refine ⟨.unsupported, ?_, ?_⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hNoneS]
          · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hNoneT]
        | inr hIn =>
          let ⟨bbSrc, bbTgt, entryEnv, curEnv, exitEnv, hBBS, hBBT, hCGet, hIdxLe,
               hMatch, hDeadRel, hStDrop, hDeadStDrop, hTermC, hDeadTermC, hEdgesC⟩ := hIn
          have hBBT2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
            rw [← hBlkEq]; exact hBBT
          have hRelBB : isConstPropMoveBlock bbSrc bbTgt = true := by
            let ⟨bbT', hBBT', hRelBB'⟩ := listRel_getElem?_left hBBsRel hBBS
            rw [hBBT] at hBBT'; injection hBBT' with hE; subst hE; exact hRelBB'
          let ⟨hBB12, _⟩ := bool_and_true hRelBB
          let ⟨hCleanB, hStmtsRel⟩ := bool_and_true hBB12
          have hCleanEq := bool_beq_eq hCleanB
          have hLenStEq := listRel_length hStmtsRel
          cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
          | some sSrc =>
            let ⟨sTgt, hStT, _⟩ := listRel_getElem?_left hStmtsRel hStS
            have hStT2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some sTgt := by
              rw [← hIdxEq]; exact hStT
            rw [drop_eq_cons_of_getElem? hStS, drop_eq_cons_of_getElem? hStT] at hStDrop hDeadStDrop
            rw [drop_eq_cons_of_getElem? hStS] at hDeadRel
            let ⟨hOkM, nextEnv, hPlain, hStRest⟩ := stepConstPropMoveCertStmts_cons_elim hStDrop
            let ⟨hOkD, hDeadStRest⟩ := checkMoveRewriteDeadStmts_cons_elim hDeadStDrop
            cases evalStatement_moveDead_step hLocEq hIdxEq hMatch hDeadRel hOkM hOkD (cm := cmS) with
            | inl hFlt =>
              let ⟨fk, e1, e2⟩ := hFlt
              right; right
              refine ⟨fk, ?_, ?_⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; exact e1
              · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBT2]; dsimp; rw [hStT2]; exact e2
            | inr hStp =>
              let ⟨locs1', locs2', e1, e2, hDeadRel'⟩ := hStp
              let ⟨locs1'', hEqS'', hNextMatch⟩ := stepPlainStmtConst_sound hMatch hPlain e1
              injection hEqS'' with hFsEq _
              injection hFsEq with hFrEq _
              have hL1Eq : locs1' = locs1'' := congrArg FrameState.locals hFrEq
              subst hL1Eq
              have hNextLe : fSrc.stmtIdx + 1 ≤ bbSrc.statements.length :=
                getElem?_some_lt hStS
              left
              refine ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' }], callerMem := cmS },
                      { frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' }], callerMem := cmS },
                      ?_, ?_,
                      { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                      { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' },
                      bSrc, bTgt, cBody,
                      rfl, rfl, rfl, hDefEq, hBlkEq, by dsimp; rw [hIdxEq],
                      hBSrc, hBTgt, hCBody, hBRel, hBCert,
                      Or.inr ⟨bbSrc, bbTgt, entryEnv, nextEnv, exitEnv,
                              hBBS, hBBT, hCGet, hNextLe, hNextMatch, hDeadRel',
                              hStRest, hDeadStRest, hTermC, hDeadTermC, hEdgesC⟩⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; exact e1
              · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBT2]; dsimp; rw [hStT2]; exact e2
          | none =>
            have hStT := (listRel_getElem?_none_iff fSrc.stmtIdx hStmtsRel).mp hStS
            have hStT2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
              rw [← hIdxEq]; exact hStT
            have hGe : bbSrc.statements.length ≤ fSrc.stmtIdx := by
              cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
              | inr hge => exact hge
              | inl hlt =>
                let ⟨_, hx⟩ := getElem?_some_of_lt bbSrc.statements fSrc.stmtIdx hlt
                rw [hStS] at hx; cases hx
            have hIdxLen : fSrc.stmtIdx = bbSrc.statements.length := Nat.le_antisymm hIdxLe hGe
            have hIdxLenT : fTgt.stmtIdx = bbTgt.statements.length := by
              rw [← hIdxEq, ← hLenStEq]; exact hIdxLen
            rw [hIdxLen, drop_length_nil, hLenStEq, drop_length_nil] at hStDrop
            rw [hIdxLen, drop_length_nil] at hDeadRel
            dsimp [stepConstPropMoveCertStmts] at hStDrop
            injection hStDrop with hCurExit; subst hCurExit
            cases evalTerminator_moveDead_step hLocEq hCleanEq hMatch hDeadRel hTermC hDeadTermC (cm := cmS) with
            | inr hTermEnd =>
              cases hTermEnd with
              | inl hDone =>
                let ⟨out, d1, d2⟩ := hDone
                right; left
                refine ⟨out, ?_, ?_⟩
                · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; dsimp
                  rw [nat_beq_of_eq hIdxLen, if_bool_true rfl]; exact d1
                · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBT2]; dsimp; rw [hStT2]; dsimp
                  rw [nat_beq_of_eq hIdxLenT, if_bool_true rfl]; exact d2
              | inr hFlt =>
                let ⟨fk, e1, e2⟩ := hFlt
                right; right
                refine ⟨fk, ?_, ?_⟩
                · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; dsimp
                  rw [nat_beq_of_eq hIdxLen, if_bool_true rfl]; exact e1
                · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBT2]; dsimp; rw [hStT2]; dsimp
                  rw [nat_beq_of_eq hIdxLenT, if_bool_true rfl]; exact e2
            | inl hJmp =>
              let ⟨tgt, locs1', locs2', e1, e2, hDeadAtTgt⟩ := hJmp
              let ⟨tgt', locs1'', hEqS'', _, hTargetCert⟩ :=
                evalTerminator_constEdges_sound hMatch hEdgesC e1
              injection hEqS'' with hFsEq _
              injection hFsEq with hFrEq _
              have hTgtEq : tgt = tgt' := congrArg FrameState.blockIdx hFrEq
              have hL1Eq : locs1' = locs1'' := congrArg FrameState.locals hFrEq
              subst hTgtEq; subst hL1Eq
              left
              refine ⟨{ frames := [{ fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs1' }], callerMem := cmS },
                      { frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' }], callerMem := cmS },
                      ?_, ?_,
                      { fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs1' },
                      { fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' },
                      bSrc, bTgt, cBody,
                      rfl, rfl, rfl, hDefEq, rfl, rfl,
                      hBSrc, hBTgt, hCBody, hBRel, hBCert, ?_⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; dsimp
                rw [nat_beq_of_eq hIdxLen, if_bool_true rfl]; exact e1
              · unfold evalStep; dsimp; rw [hBTgt2]; dsimp; rw [hBBT2]; dsimp; rw [hStT2]; dsimp
                rw [nat_beq_of_eq hIdxLenT, if_bool_true rfl]; exact e2
              · cases Nat.lt_or_ge tgt bSrc.basicBlocks.length with
                | inr hGeT => exact Or.inl hGeT
                | inl hLtT =>
                  let ⟨tgtEnv, hCTgt, hTgtMatch⟩ := hTargetCert hLtT
                  let ⟨bbSrc2, bbTgt2, exitEnv2, hBBS2, hBBT2, hLe2, hM2, hDR2, hSt2, hDSt2, hTm2, hDTm2, hEd2⟩ :=
                    constPropMoveDead_block_entry hBRel hBCert hLtT hCTgt hTgtMatch
                      (fun bbTgtS hBBTS =>
                        localsMoveDeadRel_mono
                          (fun i _ hDT => isDeadAtTarget_sound hEntryDeadLoop hDT hBBTS)
                          hDeadAtTgt)
                  exact Or.inr ⟨bbSrc2, bbTgt2, tgtEnv, tgtEnv, exitEnv2,
                                hBBS2, hBBT2, hCTgt, hLe2, hM2, hDR2, hSt2, hDSt2, hTm2, hDTm2, hEd2⟩

private theorem vc_transport_constPropMove_dead_certified_iff_priv
    (pSrc pTgt : Program) (cert : ProgramConstMoveDeadCert)
    (hRel : isConstPropMoveProgram pSrc pTgt = true)
    (hCert : checkConstPropMoveDeadProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  have hMoveCert := constPropMoveDead_to_constCert hCert
  let ⟨hHdr, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLen, hCertBodies⟩ := bool_and_true hMoveCert
  let ⟨_, hCertAt, _⟩ := listRel_zip_left_rel (nat_beq_eq hCertLen) hCertBodies
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodiesRel hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨cBody, bTgt'', _, hBT'', hBCert⟩ := hCertAt defId bSrc hBS
    rw [hBT] at hBT''; injection hBT'' with hEqB2; subst hEqB2
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨h123, _⟩ := bool_and_true hBCert
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨hPres, _⟩ := bool_and_true h12
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨hBHdr, list_isEmpty_eq_of_length (listRel_length hBBsRel), hBounds⟩
  · intro q
    exact constPropMoveDead_query_iff hRel hCert q
  · intro defId args
    have hRelEntry : isConstPropMoveProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodiesRel
    exact (constPropMoveDead_query_iff hRelEntry hCert { args := args }).1

/-! ### Stage 4 Private Helpers — Layer D2: `MatchBranchSimplify`
(`match_branches.rs`) -/

/-! #### Two's-Complement `decodeScalar` Injectivity Across All 6 `IntWidth`s -/

private theorem nat_mod_eq_of_lt_mb {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_mod_lt_mb (a : Nat) {b : Nat} (h : 0 < b) : Nat.mod a b < b :=
  Nat.mod_lt a h

private theorem nat_div_add_mod_mb (a b : Nat) : b * Nat.div a b + Nat.mod a b = a :=
  Nat.div_add_mod a b

private theorem nat_mul_add_mod_mb (a b c : Nat) : Nat.mod (a * b + c) a = Nat.mod c a := by
  rw [Nat.add_comm (a * b) c]
  exact Nat.add_mul_mod_self_left c a b

private theorem bv_isLt_mb {n : Nat} (x : BitVec n) : x.toNat < Nat.pow 2 n := x.isLt

private theorem intEmod_ofNat_mb (m p : Nat) :
    intEmod (Int.ofNat m) (Int.ofNat p) = Int.ofNat (Nat.mod m p) := rfl

private theorem intEmod_negSucc_mb (m p : Nat) :
    intEmod (Int.negSucc m) (Int.ofNat p) =
      Int.subNatNat p (Nat.succ (Nat.mod m p)) := rfl

private theorem nat_two_mul_mb (n : Nat) : 2 * n = n + n := by
  have h1 : 2 * n = 1 * n + n := Nat.succ_mul 1 n
  rw [h1, Nat.one_mul]

private theorem nat_lt_of_two_mul_lt_mb {a b : Nat} (h : 2 * a < 2 * b) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hLt => exact hLt
  | inr hGe =>
    exact False.elim (Nat.not_le_of_gt h (Nat.mul_le_mul_left 2 hGe))

private theorem nat_le_of_two_mul_le_mb {a b : Nat} (h : 2 * a ≤ 2 * b) : a ≤ b := by
  cases Nat.lt_or_ge b a with
  | inr hLe => exact hLe
  | inl hLt =>
    have hLt2 : 2 * b < 2 * a := by
      rw [nat_two_mul_mb b, nat_two_mul_mb a]
      exact Nat.add_lt_add hLt hLt
    exact False.elim (Nat.not_lt_of_ge h hLt2)

private theorem nat_sub_sub_self_mb {m n : Nat} (h : n ≤ m) : m - (m - n) = n := by
  have hAdd : n + (m - n) = m := Nat.add_sub_of_le h
  have hSub : (n + (m - n)) - (m - n) = n := Nat.add_sub_cancel n (m - n)
  rw [hAdd] at hSub
  exact hSub

private theorem nat_sub_pos_eq_succ_mb {m n : Nat} (hLt : n < m) :
    m - n = Nat.succ (m - 1 - n) := by
  cases m with
  | zero => exact False.elim (Nat.not_lt_zero n hLt)
  | succ k =>
    have hLe : n ≤ k := Nat.le_of_succ_le_succ hLt
    have h1 : Nat.succ k - 1 = k := rfl
    rw [h1]
    exact Nat.succ_sub hLe

private theorem nat_sub_lt_of_pos_le_mb {m k : Nat} (hPos : 0 < k) (hLe : k ≤ m) :
    m - k < m :=
  Nat.sub_lt (Nat.lt_of_lt_of_le hPos hLe) hPos

private theorem nat_mod_mul_mod_mb (n m k : Nat) :
    Nat.mod (Nat.mod n (m * k)) m = Nat.mod n m := by
  have hDivMod := nat_div_add_mod_mb n (m * k)
  have hAssoc : (m * k) * Nat.div n (m * k) = m * (k * Nat.div n (m * k)) :=
    Nat.mul_assoc m k (Nat.div n (m * k))
  rw [hAssoc] at hDivMod
  have hMod := congrArg (fun z => Nat.mod z m) hDivMod
  rw [nat_mul_add_mod_mb] at hMod
  exact hMod

private theorem int_ofNat_sub_eq_subNatNat_mb (a b : Nat) (hPos : 0 < b) :
    Int.ofNat a - Int.ofNat b = Int.subNatNat a b := by
  cases b with
  | zero => exact False.elim (Nat.not_lt_zero 0 hPos)
  | succ _ => rfl

private theorem int_subNatNat_of_le_mb {a b : Nat} (hLe : b ≤ a) :
    Int.subNatNat a b = Int.ofNat (a - b) := by
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le hLe]

private theorem int_subNatNat_of_lt_mb {a b : Nat} (hLt : a < b) :
    Int.subNatNat a b = Int.negSucc (b - 1 - a) := by
  unfold Int.subNatNat
  rw [nat_sub_pos_eq_succ_mb hLt]

private theorem int_beq_refl_mb (x : Int) : (x == x) = true :=
  decide_eq_true rfl

private theorem int_eq_of_beq_mb {x y : Int} (h : (x == y) = true) : x = y :=
  of_decide_eq_true h

private theorem bvToInt_bvOfInt_128_ofNat_mb {k : Nat} (hLt : k < Nat.pow 2 127) :
    bvToInt (bvOfInt 128 (Int.ofNat k)) = Int.ofNat k := by
  have hLt128 : k < Nat.pow 2 128 :=
    Nat.lt_trans hLt (by decide : Nat.pow 2 127 < Nat.pow 2 128)
  have hToNat : (bvOfInt 128 (Int.ofNat k)).toNat = k := by
    unfold bvOfInt
    rw [intEmod_ofNat_mb]
    change Nat.mod (Nat.mod k (Nat.pow 2 128)) (Nat.pow 2 128) = k
    rw [nat_mod_eq_of_lt_mb hLt128, nat_mod_eq_of_lt_mb hLt128]
  unfold bvToInt
  rw [hToNat]
  have hPow128 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
  have h2Lt : 2 * k < Nat.pow 2 128 := by
    rw [hPow128, nat_two_mul_mb k, nat_two_mul_mb (Nat.pow 2 127)]
    exact Nat.add_lt_add hLt hLt
  exact ite_prop_true h2Lt

private theorem bvToInt_bvOfInt_128_negSucc_mb {k : Nat} (hLt : k < Nat.pow 2 127) :
    bvToInt (bvOfInt 128 (Int.negSucc k)) = Int.negSucc k := by
  have hLt128 : k < Nat.pow 2 128 :=
    Nat.lt_trans hLt (by decide : Nat.pow 2 127 < Nat.pow 2 128)
  have hSuccLe127 : k + 1 ≤ Nat.pow 2 127 := hLt
  have hSuccLe128 : k + 1 ≤ Nat.pow 2 128 := hLt128
  have hSubLt128 : Nat.pow 2 128 - (k + 1) < Nat.pow 2 128 :=
    nat_sub_lt_of_pos_le_mb (Nat.zero_lt_succ k) hSuccLe128
  have hToNat : (bvOfInt 128 (Int.negSucc k)).toNat = Nat.pow 2 128 - (k + 1) := by
    unfold bvOfInt
    rw [intEmod_negSucc_mb, nat_mod_eq_of_lt_mb hLt128, int_subNatNat_of_le_mb hSuccLe128]
    change Nat.mod (Nat.pow 2 128 - (k + 1)) (Nat.pow 2 128) = _
    exact nat_mod_eq_of_lt_mb hSubLt128
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
  rw [int_ofNat_sub_eq_subNatNat_mb _ (Nat.pow 2 128) hPos128]
  rw [int_subNatNat_of_lt_mb hSubLt128]
  have hCancel : Nat.pow 2 128 - 1 - (Nat.pow 2 128 - (k + 1)) = k := by
    have h1 : Nat.pow 2 128 - (Nat.pow 2 128 - (k + 1)) = k + 1 :=
      nat_sub_sub_self_mb hSuccLe128
    have h2 : Nat.succ (Nat.pow 2 128 - 1 - (Nat.pow 2 128 - (k + 1))) = k + 1 := by
      rw [← nat_sub_pos_eq_succ_mb hSubLt128]
      exact h1
    exact Nat.succ.inj h2
  rw [hCancel]

private noncomputable def intWidthCofactor_mb : IntWidth → Nat
  | .i8 => Nat.pow 2 120
  | .i16 => Nat.pow 2 112
  | .i32 => Nat.pow 2 96
  | .i64 | .isize => Nat.pow 2 64
  | .i128 => 1

private theorem pow128_eq_mul_cofactor_mb (w : IntWidth) :
    Nat.pow 2 128 = Nat.pow 2 w.bitWidth * intWidthCofactor_mb w := by
  cases w <;> decide

private theorem toNat_truncateBits_bvOfInt_mb (w : IntWidth) (v : Int) :
    (truncateBits w (bvOfInt 128 v)).toNat =
      (intEmod v (Int.ofNat (Nat.pow 2 w.bitWidth))).toNat := by
  let M := Nat.pow 2 w.bitWidth
  let K := intWidthCofactor_mb w
  have hM : 0 < M := pow2_bitWidth_pos w
  have hP128 : 0 < Nat.pow 2 128 := by decide
  have hFac : Nat.pow 2 128 = M * K := pow128_eq_mul_cofactor_mb w
  rw [toNat_truncateBits]
  cases v with
  | ofNat n =>
    unfold bvOfInt
    rw [intEmod_ofNat_mb, intEmod_ofNat_mb]
    have hModLt128 : Nat.mod n (Nat.pow 2 128) < Nat.pow 2 128 :=
      nat_mod_lt_mb n hP128
    change Nat.mod (Nat.mod (Nat.mod n (Nat.pow 2 128)) (Nat.pow 2 128)) M = Nat.mod n M
    rw [nat_mod_eq_of_lt_mb hModLt128, hFac]
    exact nat_mod_mul_mod_mb n M K
  | negSucc n =>
    unfold bvOfInt
    rw [intEmod_negSucc_mb, intEmod_negSucc_mb]
    have hModP_lt : Nat.mod n (Nat.pow 2 128) < Nat.pow 2 128 := nat_mod_lt_mb n hP128
    have hModM_lt : Nat.mod n M < M := nat_mod_lt_mb n hM
    have hSuccP_le : Nat.succ (Nat.mod n (Nat.pow 2 128)) ≤ Nat.pow 2 128 := hModP_lt
    have hSuccM_le : Nat.succ (Nat.mod n M) ≤ M := hModM_lt
    rw [int_subNatNat_of_le_mb hSuccP_le, int_subNatNat_of_le_mb hSuccM_le]
    have hSubP_lt : Nat.pow 2 128 - Nat.succ (Nat.mod n (Nat.pow 2 128)) < Nat.pow 2 128 :=
      nat_sub_lt_of_pos_le_mb (Nat.zero_lt_succ _) hSuccP_le
    change Nat.mod (Nat.mod (Nat.pow 2 128 - Nat.succ (Nat.mod n (Nat.pow 2 128))) (Nat.pow 2 128)) M =
      M - Nat.succ (Nat.mod n M)
    rw [nat_mod_eq_of_lt_mb hSubP_lt]
    let remP := Nat.mod n (Nat.pow 2 128)
    let q := Nat.div remP M
    let r := Nat.mod remP M
    have hREq : r = Nat.mod n M := by
      dsimp [r, remP]
      rw [hFac]
      exact nat_mod_mul_mod_mb n M K
    have hDecomp : M * q + r = remP := nat_div_add_mod_mb remP M
    have hQLtK : q < K := by
      cases Nat.lt_or_ge q K with
      | inl hlt => exact hlt
      | inr hge =>
        have h1 : M * K ≤ M * q := Nat.mul_le_mul_left M hge
        have h2 : M * K ≤ M * q + r := Nat.le_trans h1 (Nat.le_add_right (M * q) r)
        rw [hDecomp, ← hFac] at h2
        exact False.elim (Nat.not_lt_of_ge h2 hModP_lt)
    have hKDecomp : K = (K - (q + 1)) + (q + 1) := by
      rw [Nat.add_comm]
      exact (Nat.add_sub_of_le hQLtK).symm
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
    rw [hRewriteSub, nat_mul_add_mod_mb]
    have hSubMLt : M - (r + 1) < M := nat_sub_lt_of_pos_le_mb (Nat.zero_lt_succ r) hRSuccLe
    rw [nat_mod_eq_of_lt_mb hSubMLt, hREq]

private theorem signExtendBits_concrete_width_mb {W H : Nat} {low : BitVec W}
    (hPow : Nat.pow 2 W = 2 * H)
    (hHPos : 0 < H)
    (hHLe127 : H ≤ Nat.pow 2 127) :
    bvToInt (bvSignExtend 128 low) =
      if 2 * low.toNat < Nat.pow 2 W then
        Int.ofNat low.toNat
      else
        Int.negSucc (Nat.pow 2 W - 1 - low.toNat) := by
  unfold bvSignExtend
  have hLowLt : low.toNat < Nat.pow 2 W := bv_isLt_mb low
  have hWPos : 0 < Nat.pow 2 W := by
    rw [hPow, nat_two_mul_mb H]
    exact Nat.lt_of_lt_of_le hHPos (Nat.le_add_right H H)
  cases Nat.lt_or_ge (2 * low.toNat) (Nat.pow 2 W) with
  | inl hCmp =>
    rw [ite_prop_true hCmp]
    have hBv : bvToInt low = Int.ofNat low.toNat := by
      unfold bvToInt; exact ite_prop_true hCmp
    rw [hBv]
    have hLtH : low.toNat < H := by
      apply nat_lt_of_two_mul_lt_mb
      rw [← hPow]; exact hCmp
    exact bvToInt_bvOfInt_128_ofNat_mb (Nat.lt_of_lt_of_le hLtH hHLe127)
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
    have hGeH : H ≤ low.toNat := by
      apply nat_le_of_two_mul_le_mb
      rw [← hPow]; exact hCmp
    have hBv : bvToInt low = Int.negSucc (Nat.pow 2 W - 1 - low.toNat) := by
      unfold bvToInt
      rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
      rw [int_ofNat_sub_eq_subNatNat_mb low.toNat (Nat.pow 2 W) hWPos]
      exact int_subNatNat_of_lt_mb hLowLt
    rw [hBv]
    let k := Nat.pow 2 W - 1 - low.toNat
    have hDiff : Nat.pow 2 W - low.toNat = k + 1 := nat_sub_pos_eq_succ_mb hLowLt
    have hKLtH : k < H := by
      have hSum : low.toNat + (k + 1) = H + H := by
        have hAdd := Nat.add_sub_of_le (Nat.le_of_lt hLowLt)
        rw [hDiff, hPow, nat_two_mul_mb H] at hAdd
        exact hAdd
      have hLeAdd : H + (k + 1) ≤ H + H := by
        rw [← hSum]
        exact Nat.add_le_add_right hGeH (k + 1)
      exact Nat.le_of_add_le_add_left hLeAdd
    exact bvToInt_bvOfInt_128_negSucc_mb (Nat.lt_of_lt_of_le hKLtH hHLe127)

private theorem signExtendBits_eq_mb {w : IntWidth} {b : BitVec 128}
    (hLt : b.toNat < Nat.pow 2 w.bitWidth) :
    signExtendBits w b =
      if 2 * b.toNat < Nat.pow 2 w.bitWidth then
        Int.ofNat b.toNat
      else
        Int.negSucc (Nat.pow 2 w.bitWidth - 1 - b.toNat) := by
  cases w
  · have hLow : (bvExtractLsb 7 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width_mb (H := Nat.pow 2 7) (low := bvExtractLsb 7 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 15 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width_mb (H := Nat.pow 2 15) (low := bvExtractLsb 15 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 31 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width_mb (H := Nat.pow 2 31) (low := bvExtractLsb 31 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 63 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width_mb (H := Nat.pow 2 63) (low := bvExtractLsb 63 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 127 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width_mb (H := Nat.pow 2 127) (low := bvExtractLsb 127 0 b)
      (by decide) (by decide) (Nat.le_refl _)
    rw [hLow] at hEq; exact hEq
  · have hLow : (bvExtractLsb 63 0 b).toNat = b.toNat := Nat.mod_eq_of_lt hLt
    have hEq := signExtendBits_concrete_width_mb (H := Nat.pow 2 63) (low := bvExtractLsb 63 0 b)
      (by decide) (by decide) (by decide)
    rw [hLow] at hEq; exact hEq

private theorem decodeScalar_unsigned_mb {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    decodeScalar ⟨w, false, b⟩ = Int.ofNat b.toNat := by
  change (if false then signExtendBits w (truncateBits w b) else Int.ofNat (truncateBits w b).toNat) = _
  rw [if_bool_false rfl, hWf]

private theorem decodeScalar_signed_mb {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    decodeScalar ⟨w, true, b⟩ = signExtendBits w b := by
  change (if true then signExtendBits w (truncateBits w b) else Int.ofNat (truncateBits w b).toNat) = _
  rw [if_bool_true rfl, hWf]

private theorem truncateBits_bvOfInt_decodeScalar_mb {w : IntWidth} {s : Bool} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvOfInt 128 (decodeScalar ⟨w, s, b⟩)) = b := by
  have hLt : b.toNat < Nat.pow 2 w.bitWidth := truncateBits_eq_iff.mp hWf
  apply bitvec_eq_of_toNat_eq
  rw [toNat_truncateBits_bvOfInt_mb]
  cases s with
  | false =>
    rw [decodeScalar_unsigned_mb hWf, intEmod_ofNat_mb]
    exact nat_mod_eq_of_lt_mb hLt
  | true =>
    rw [decodeScalar_signed_mb hWf, signExtendBits_eq_mb hLt]
    cases Nat.lt_or_ge (2 * b.toNat) (Nat.pow 2 w.bitWidth) with
    | inl hCmp =>
      rw [ite_prop_true hCmp, intEmod_ofNat_mb]
      exact nat_mod_eq_of_lt_mb hLt
    | inr hCmp =>
      rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
      let M := Nat.pow 2 w.bitWidth
      let k := M - 1 - b.toNat
      have hDiff : M - b.toNat = k + 1 := nat_sub_pos_eq_succ_mb hLt
      have hSum : b.toNat + (k + 1) = M := by
        have hAdd := Nat.add_sub_of_le (Nat.le_of_lt hLt)
        rw [hDiff] at hAdd; exact hAdd
      have hKLtM : k < M := by
        have hLe : k + 1 ≤ M := by rw [← hSum]; exact Nat.le_add_left (k + 1) b.toNat
        exact Nat.lt_of_succ_le hLe
      rw [intEmod_negSucc_mb, nat_mod_eq_of_lt_mb hKLtM, int_subNatNat_of_le_mb hKLtM]
      change M - (k + 1) = b.toNat
      rw [← hSum]
      exact Nat.add_sub_cancel b.toNat (k + 1)

private theorem decodeScalar_eq_iff_mb {w : IntWidth} {s : Bool} {a b : BitVec 128}
    (ha : truncateBits w a = a) (hb : truncateBits w b = b) :
    decodeScalar ⟨w, s, a⟩ = decodeScalar ⟨w, s, b⟩ ↔ a = b := by
  constructor
  · intro hDec
    have h1 := truncateBits_bvOfInt_decodeScalar_mb (s := s) ha
    have h2 := truncateBits_bvOfInt_decodeScalar_mb (s := s) hb
    rw [hDec, h2] at h1
    exact h1.symm
  · intro hEq; subst hEq; rfl

private theorem decodeScalar_beq_eq_mb {w : IntWidth} {s : Bool} {a b : BitVec 128}
    (ha : truncateBits w a = a) (hb : truncateBits w b = b) :
    (decodeScalar ⟨w, s, a⟩ == decodeScalar ⟨w, s, b⟩) = (a == b) := by
  cases hB : (a == b) with
  | true =>
    rw [bitvec_beq_eq hB]
    exact int_beq_refl_mb _
  | false =>
    have hNe : a ≠ b := bitvec_ne_of_beq_false hB
    cases hI : (decodeScalar ⟨w, s, a⟩ == decodeScalar ⟨w, s, b⟩) with
    | false => rfl
    | true =>
      exact False.elim (hNe ((decodeScalar_eq_iff_mb ha hb).mp (int_eq_of_beq_mb hI)))

/-! #### `checkMatchBranchBlocksLoop` & `checkMatchBranchRewriteAt`
Elimination -/

private theorem checkMatchBranchBlocksLoop_length {bSrc : Body} {base : Nat}
    {bs1 bs2 : List BasicBlock}
    (h : checkMatchBranchBlocksLoop bSrc base bs1 bs2 = true) :
    bs1.length = bs2.length := by
  induction bs1 generalizing base bs2 with
  | nil =>
    cases bs2 with
    | nil => rfl
    | cons _ _ => cases h
  | cons a rest1 ih =>
    cases bs2 with
    | nil => cases h
    | cons b rest2 =>
      dsimp [checkMatchBranchBlocksLoop] at h
      let ⟨_, hTail⟩ := bool_and_true h
      dsimp [List.length]
      rw [ih hTail]

private theorem checkMatchBranchBlocksLoop_get {bSrc : Body} {base k : Nat}
    {bs1 bs2 : List BasicBlock} {bbSrc : BasicBlock}
    (h : checkMatchBranchBlocksLoop bSrc base bs1 bs2 = true)
    (hGet : Trusted.MirSemantics.getElem? bs1 k = some bbSrc) :
    ∃ bbTgt,
      Trusted.MirSemantics.getElem? bs2 k = some bbTgt ∧
      (bbSrc = bbTgt ∨ checkMatchBranchRewriteAt bSrc (base + k) bbSrc bbTgt = true) := by
  induction bs1 generalizing base k bs2 with
  | nil => cases hGet
  | cons a rest1 ih =>
    cases bs2 with
    | nil => cases h
    | cons b rest2 =>
      dsimp [checkMatchBranchBlocksLoop] at h
      let ⟨hHere, hTail⟩ := bool_and_true h
      cases k with
      | zero =>
        injection hGet with hEq; subst hEq
        rw [Nat.add_zero]
        refine ⟨b, rfl, ?_⟩
        cases hRew : isMatchBranchRewriteAt bSrc base a b with
        | true =>
          rw [if_bool_true hRew] at hHere
          exact Or.inr hHere
        | false =>
          rw [if_bool_false hRew] at hHere
          exact Or.inl (blockEq_eq hHere)
      | succ m =>
        let ⟨bbTgt, hG2, hDisj⟩ := ih hTail hGet
        rw [Nat.add_assoc, Nat.add_comm 1 m] at hDisj
        exact ⟨bbTgt, hG2, hDisj⟩

private inductive MatchBranchDiamondSpec (bSrc : Body) (bbSrc bbTgt : BasicBlock) : Prop where
  | mk
    (dPlace : Place)
    (caseBits : BitVec 128)
    (bbCase : BasicBlockId)
    (bbOther : BasicBlockId)
    (bbJoin : BasicBlockId)
    (blkCase : BasicBlock)
    (blkOther : BasicBlock)
    (dst : Place)
    (cCase : ConstOperand)
    (cOther : ConstOperand)
    (discrTy : MirTy)
    (bCase : Bool)
    (hTermSrc : bbSrc.terminator =
      .switchInt (.copy dPlace) { branches := [(caseBits, bbCase)], otherwise := bbOther })
    (hTermTgt : bbTgt.terminator = .goto bbJoin)
    (hDProj : dPlace.projection.isEmpty = true)
    (hDstProj : dst.projection.isEmpty = true)
    (hGetCase : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbCase = some blkCase)
    (hGetOther : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbOther = some blkOther)
    (hStmtsCase : blkCase.statements = [.assign dst (.use (.constant cCase))])
    (hTermCase : blkCase.terminator = .goto bbJoin)
    (hStmtsOther : blkOther.statements = [.assign dst (.use (.constant cOther))])
    (hTermOther : blkOther.terminator = .goto bbJoin)
    (hLenTgt : bbTgt.statements.length = bbSrc.statements.length + 1)
    (hPrefixEq : ∀ j, j < bbSrc.statements.length →
      Trusted.MirSemantics.getElem? bbTgt.statements j =
        Trusted.MirSemantics.getElem? bbSrc.statements j)
    (hGetTgtCmp : Trusted.MirSemantics.getElem? bbTgt.statements bbSrc.statements.length =
      some (.assign dst (.binaryOp (if bCase then .eq else .ne)
        (.copy dPlace) (.constant ⟨discrTy, .scalar caseBits⟩))))
    (hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId = some .bool)
    (hDiscrTy : Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId = some discrTy)
    (hPrim : isPrimitiveReadableTy discrTy = true)
    (hValidCase : validTypedConstOperand discrTy ⟨discrTy, .scalar caseBits⟩ = true)
    (hCCaseTy : cCase.ty = .bool)
    (hCOtherTy : cOther.ty = .bool)
    (hEvCCase : evalConstLit .bool cCase.lit = .ok (.bool bCase))
    (hEvCOther : evalConstLit .bool cOther.lit = .ok (.bool (!bCase)))

private theorem checkMatchBranchRewriteAt_elim {bSrc : Body} {bbIdx : BasicBlockId}
    {bbSrc bbTgt : BasicBlock}
    (h : checkMatchBranchRewriteAt bSrc bbIdx bbSrc bbTgt = true) :
    MatchBranchDiamondSpec bSrc bbSrc bbTgt := by
  unfold checkMatchBranchRewriteAt isMatchBranchRewriteAt at h
  let ⟨hRew, hChk2⟩ := bool_and_true h
  let ⟨hCl12, hM1⟩ := bool_and_true hRew
  cases hTS : bbSrc.terminator with
  | goto _ | return_ | unreachable | unwindResume | assert _ _ _ _ _
  | call _ _ _ _ _ | unsupported =>
    rw [hTS] at hM1; cases hM1
  | switchInt discrOp swTargets =>
    rw [hTS] at hM1 hChk2
    cases discrOp with
    | move _ | constant _ => cases hM1
    | copy dPlace =>
      cases swTargets with
      | mk brs bbOther =>
        cases brs with
        | nil => cases hM1
        | cons br1 brRest =>
          cases brRest with
          | cons _ _ => cases hM1
          | nil =>
            cases br1 with
            | mk caseBits bbCase =>
              cases hTT : bbTgt.terminator with
              | switchInt _ _ | return_ | unreachable | unwindResume
              | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
                rw [hTT] at hM1; cases hM1
              | goto bbJoin =>
                rw [hTT] at hM1
                dsimp only at hM1 hChk2
                let ⟨h1234, hM2⟩ := bool_and_true hM1
                let ⟨h123, _⟩ := bool_and_true h1234
                let ⟨h12, _⟩ := bool_and_true h123
                let ⟨hDProj, _⟩ := bool_and_true h12
                cases hGC : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbCase with
                | none => rw [hGC] at hM2; cases hM2
                | some blkCase =>
                  rw [hGC] at hM2 hChk2
                  cases hGO : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbOther with
                  | none => rw [hGO] at hM2; cases hM2
                  | some blkOther =>
                    rw [hGO] at hM2 hChk2
                    dsimp only at hM2 hChk2
                    let ⟨_, hM3⟩ := bool_and_true hM2
                    cases hSC : blkCase.statements with
                    | nil => rw [hSC] at hM3; cases hM3
                    | cons sc1 scRest =>
                      rw [hSC] at hM3
                      cases sc1 with
                      | nop | storageLive _ | storageDead _ | unsupported => cases hM3
                      | assign dst1 rvc =>
                        cases rvc with
                        | binaryOp _ _ _ | unaryOp _ _ | discriminant _
                        | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hM3
                        | use opc =>
                          cases opc with
                          | copy _ | move _ => cases hM3
                          | constant cCase =>
                            cases scRest with
                            | cons _ _ => cases hM3
                            | nil =>
                              cases hTC : blkCase.terminator with
                              | switchInt _ _ | return_ | unreachable | unwindResume
                              | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
                                rw [hTC] at hM3; cases hM3
                              | goto join1 =>
                                rw [hTC] at hM3
                                cases hSO : blkOther.statements with
                                | nil => rw [hSO] at hM3; cases hM3
                                | cons so1 soRest =>
                                  rw [hSO] at hM3
                                  cases so1 with
                                  | nop | storageLive _ | storageDead _ | unsupported => cases hM3
                                  | assign dst2 rvo =>
                                    cases rvo with
                                    | binaryOp _ _ _ | unaryOp _ _ | discriminant _
                                    | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hM3
                                    | use opo =>
                                      cases opo with
                                      | copy _ | move _ => cases hM3
                                      | constant cOther =>
                                        cases soRest with
                                        | cons _ _ => cases hM3
                                        | nil =>
                                          cases hTO : blkOther.terminator with
                                          | switchInt _ _ | return_ | unreachable | unwindResume
                                          | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
                                            rw [hTO] at hM3; cases hM3
                                          | goto join2 =>
                                            rw [hTO] at hM3
                                            dsimp only at hM3
                                            let ⟨hA123456, hM4⟩ := bool_and_true hM3
                                            let ⟨hA12345, hPrefRel⟩ := bool_and_true hA123456
                                            let ⟨hA1234, hLenB⟩ := bool_and_true hA12345
                                            let ⟨hA123, hJ2B⟩ := bool_and_true hA1234
                                            let ⟨hA12, hJ1B⟩ := bool_and_true hA123
                                            let ⟨hDstProj, hDst12B⟩ := bool_and_true hA12
                                            cases hGT : Trusted.MirSemantics.getElem? bbTgt.statements bbSrc.statements.length with
                                            | none => rw [hGT] at hM4; cases hM4
                                            | some stCmp =>
                                              rw [hGT] at hM4 hChk2
                                              cases stCmp with
                                              | nop | storageLive _ | storageDead _ | unsupported => cases hM4
                                              | assign dstTgt rvCmp =>
                                                cases rvCmp with
                                                | use _ | unaryOp _ _ | discriminant _
                                                | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases hM4
                                                | binaryOp cmpOp lhsCmp rhsCmp =>
                                                  cases lhsCmp with
                                                  | move _ | constant _ => cases hM4
                                                  | copy dPlaceTgt =>
                                                    cases rhsCmp with
                                                    | copy _ | move _ => cases hM4
                                                    | constant caseConst =>
                                                      dsimp only at hM4 hChk2
                                                      rw [hSC, hSO] at hChk2
                                                      let ⟨hP12, hDP12B⟩ := bool_and_true hM4
                                                      let ⟨hDst1TB, _⟩ := bool_and_true hP12
                                                      cases hDTy : Trusted.MirSemantics.getElem? bSrc.locals dstTgt.localId with
                                                      | none => rw [hDTy] at hChk2; cases hChk2
                                                      | some dty =>
                                                        rw [hDTy] at hChk2
                                                        cases dty with
                                                        | int _ _ | unit | never | enum _ | tuple _
                                                        | ref _ _ | rawPtr _ _ | unsupported => cases hChk2
                                                        | bool =>
                                                          cases hDiscTy : Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId with
                                                          | none => rw [hDiscTy] at hChk2; cases hChk2
                                                          | some discrTy =>
                                                            rw [hDiscTy] at hChk2
                                                            dsimp only at hChk2
                                                            let ⟨hC12345, hEvM⟩ := bool_and_true hChk2
                                                            let ⟨hC1234, hCOthTyB⟩ := bool_and_true hC12345
                                                            let ⟨hC123, hCCasTyB⟩ := bool_and_true hC1234
                                                            let ⟨hC12, hValCase⟩ := bool_and_true hC123
                                                            let ⟨hPrim, hCEqB⟩ := bool_and_true hC12
                                                            cases hEC : evalConstLit .bool cCase.lit with
                                                            | error _ => rw [hEC] at hEvM; cases hEvM
                                                            | ok vc =>
                                                              rw [hEC] at hEvM
                                                              cases vc with
                                                              | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEvM
                                                              | bool bCase =>
                                                                cases hEO : evalConstLit .bool cOther.lit with
                                                                | error _ => rw [hEO] at hEvM; cases hEvM
                                                                | ok vo =>
                                                                  rw [hEO] at hEvM
                                                                  cases vo with
                                                                  | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEvM
                                                                  | bool bOther =>
                                                                    dsimp only at hEvM
                                                                    let ⟨hBOthEq, hCmpEqB⟩ := bool_and_true hEvM
                                                                    have hDst2 := placeEq_eq hDst12B
                                                                    have hDstT := placeEq_eq hDst1TB
                                                                    have hDPT := placeEq_eq hDP12B
                                                                    have hJ1 := nat_beq_eq hJ1B
                                                                    have hJ2 := nat_beq_eq hJ2B
                                                                    have hCC := constOpEq_eq hCEqB
                                                                    have hBO := bool_beq_eq hBOthEq
                                                                    have hCmp := binOpEq_eq hCmpEqB
                                                                    rw [← hDst2] at hSO
                                                                    rw [← hDstT] at hGT hDTy
                                                                    rw [← hDPT, hCC, hCmp] at hGT
                                                                    rw [hCC] at hValCase
                                                                    rw [hBO] at hEO
                                                                    rw [hJ1] at hTC
                                                                    rw [hJ2] at hTO
                                                                    have hTakeEq : bbSrc.statements =
                                                                        bbTgt.statements.take bbSrc.statements.length :=
                                                                      listRel_eq (fun _ _ => stmtEq_eq) hPrefRel
                                                                    exact MatchBranchDiamondSpec.mk
                                                                      dPlace caseBits bbCase bbOther bbJoin
                                                                      blkCase blkOther dst1 cCase cOther
                                                                      discrTy bCase
                                                                      hTS hTT hDProj hDstProj hGC hGO
                                                                      hSC hTC hSO hTO
                                                                      (nat_beq_eq hLenB)
                                                                      (fun j hLt => by
                                                                        have hTk := getElem?_take_lt bbTgt.statements bbSrc.statements.length j hLt
                                                                        rw [← hTakeEq] at hTk
                                                                        exact hTk.symm)
                                                                      hGT hDTy hDiscTy hPrim hValCase
                                                                      (mirTy_beq_eq hCCasTyB)
                                                                      (mirTy_beq_eq hCOthTyB)
                                                                      hEC hEO

private theorem isMatchBranchSimplifyProgram_initState_eq {pSrc pTgt : Program}
    (hRel : isMatchBranchSimplifyProgram pSrc pTgt = true)
    (hCert : checkMatchBranchSimplifyProgram pSrc pTgt = true)
    (q : Query) :
    initState pSrc q = initState pTgt q := by
  let ⟨hHdr, hBodiesRel⟩ := bool_and_true hRel
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff pSrc.entryDefId hBodiesRel
  · intro b1 hB1
    let ⟨b2, hB2, hBRel⟩ := listRel_getElem?_left hBodiesRel hB1
    let ⟨b2', hB2', hBCert⟩ := listRel_getElem?_left hCert hB1
    rw [hB2] at hB2'; injection hB2' with hEqB; subst hEqB
    rw [hEnt] at hB2
    let ⟨hBHdr, _⟩ := bool_and_true hBRel
    let ⟨hPres, hLoopC⟩ := bool_and_true hBCert
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨b2, hB2, hBHdr,
           list_isEmpty_eq_of_length (checkMatchBranchBlocksLoop_length hLoopC),
           hBounds, initLocalsLoop_eq_of_preservesStorage q.args hBHdr hPres⟩

/-! #### 3-State Stutter Bisimulation Relation (`MatchBranchRel`) -/

private noncomputable def MatchBranchRel (pSrc pTgt : Program) :
    Nat → State → State → Prop
  | k, s, t =>
    ∃ bSrc bTgt defId locals cm,
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc ∧
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt ∧
      isMatchBranchSimplifyBody bSrc bTgt = true ∧
      checkMatchBranchSimplifyBody bSrc bTgt = true ∧
      LocalsWellTyped bSrc.locals locals ∧
      ((k = 1 ∧
        ∃ bbIdx stmtIdx,
          s = { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }],
                callerMem := cm } ∧
          t = { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }],
                callerMem := cm } ∧
          (∀ bbSrc, Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc →
            stmtIdx ≤ bbSrc.statements.length)) ∨
       (k = 0 ∧
        ∃ bbArm blkArm cArm bbIdx bbTgt N dst rvTgt bbJoin resBool,
          s = { frames := [{ defId := defId, blockIdx := bbArm, stmtIdx := 0, locals := locals }],
                callerMem := cm } ∧
          t = { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := N, locals := locals }],
                callerMem := cm } ∧
          Trusted.MirSemantics.getElem? bSrc.basicBlocks bbArm = some blkArm ∧
          blkArm.statements = [.assign dst (.use (.constant cArm))] ∧
          blkArm.terminator = .goto bbJoin ∧
          dst.projection.isEmpty = true ∧
          Trusted.MirSemantics.getElem? bSrc.locals dst.localId = some .bool ∧
          cArm.ty = .bool ∧
          evalConstLit .bool cArm.lit = .ok (.bool resBool) ∧
          Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt ∧
          Trusted.MirSemantics.getElem? bbTgt.statements N = some (.assign dst rvTgt) ∧
          bbTgt.statements.length = N + 1 ∧
          bbTgt.terminator = .goto bbJoin ∧
          evalRvalue bTgt.locals locals .bool rvTgt = .ok (.bool resBool, locals)) ∨
       (k = 0 ∧
        ∃ bbArm blkArm bbIdx bbTgt N bbJoin,
          s = { frames := [{ defId := defId, blockIdx := bbArm, stmtIdx := 1, locals := locals }],
                callerMem := cm } ∧
          t = { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := N + 1, locals := locals }],
                callerMem := cm } ∧
          Trusted.MirSemantics.getElem? bSrc.basicBlocks bbArm = some blkArm ∧
          blkArm.statements.length = 1 ∧
          blkArm.terminator = .goto bbJoin ∧
          Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt ∧
          bbTgt.statements.length = N + 1 ∧
          bbTgt.terminator = .goto bbJoin))

private theorem bool_polarity_match (matched bCase : Bool) :
    (if bCase then matched else !matched) =
      (if matched then bCase else !bCase) := by
  cases matched <;> cases bCase <;> rfl

private theorem bool_switch_cmp_match (db cb : Bool) :
    (match cb with | false => !db | true => db) = (db == cb) := by
  cases db <;> cases cb <;> rfl

private theorem evalBinOp_scalar_eq_ne {w : IntWidth} {s bCase : Bool}
    {dBits caseBits : BitVec 128}
    (hTrD : truncateBits w dBits = dBits)
    (hTrC : truncateBits w caseBits = caseBits) :
    evalBinOp (if bCase then .eq else .ne)
      (.scalar ⟨w, s, dBits⟩) (.scalar ⟨w, s, caseBits⟩) =
      .ok (.bool (if (dBits == caseBits) then bCase else !bCase)) := by
  cases bCase with
  | true =>
    unfold evalBinOp
    change (if false then _
      else if !(IntWidth.beq w w && (s == s)) then _
      else Except.ok (Val.bool (decodeScalar ⟨w, s, dBits⟩ == decodeScalar ⟨w, s, caseBits⟩))) = _
    rw [if_bool_false rfl, intWidth_beq_refl w, bool_beq_refl s]
    rw [if_bool_false (rfl : (!(true && true)) = false)]
    rw [decodeScalar_beq_eq_mb hTrD hTrC]
    cases (dBits == caseBits) <;> rfl
  | false =>
    unfold evalBinOp
    change (if false then _
      else if !(IntWidth.beq w w && (s == s)) then _
      else Except.ok (Val.bool (decodeScalar ⟨w, s, dBits⟩ != decodeScalar ⟨w, s, caseBits⟩))) = _
    rw [if_bool_false rfl, intWidth_beq_refl w, bool_beq_refl s]
    rw [if_bool_false (rfl : (!(true && true)) = false)]
    change Except.ok (Val.bool (!(decodeScalar ⟨w, s, dBits⟩ == decodeScalar ⟨w, s, caseBits⟩))) = _
    rw [decodeScalar_beq_eq_mb hTrD hTrC]
    cases (dBits == caseBits) <;> rfl

private theorem evalBinOp_bool_eq_ne (bCase db cb : Bool) :
    evalBinOp (if bCase then .eq else .ne) (.bool db) (.bool cb) =
      .ok (.bool (if (db == cb) then bCase else !bCase)) := by
  cases bCase <;> cases db <;> cases cb <;> rfl

private theorem matchBranch_diamond_split {pSrc pTgt : Program}
    {bSrc bTgt : Body} {defId : DefId} {bbIdx : BasicBlockId}
    {bbSrc bbTgt : BasicBlock} {locals : List LocalSlot} {cm : CallerMemory}
    (hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc)
    (hBTgt : Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt)
    (hBRel : isMatchBranchSimplifyBody bSrc bTgt = true)
    (hBCert : checkMatchBranchSimplifyBody bSrc bTgt = true)
    (hWt : LocalsWellTyped bSrc.locals locals)
    (hBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc)
    (hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt)
    (sp : MatchBranchDiamondSpec bSrc bbSrc bbTgt) :
    let N := bbSrc.statements.length
    let fAligned : FrameState :=
      { defId := defId, blockIdx := bbIdx, stmtIdx := N, locals := locals }
    StutterStepOutcome pSrc pTgt (MatchBranchRel pSrc pTgt) 1
      { frames := [fAligned], callerMem := cm }
      { frames := [fAligned], callerMem := cm } := by
  let ⟨dPlace, caseBits, bbCase, bbOther, bbJoin, blkCase, blkOther, dst,
       cCase, cOther, discrTy, bCase, hTermSrc, hTermTgt, hDProj, hDstProj,
       hGetCase, hGetOther, hStmtsCase, hTermCase, hStmtsOther, hTermOther,
       hLenTgt, _, hGetTgtCmp, hDstTy, hDiscrTy, hPrim, hValidCase,
       hCCaseTy, hCOtherTy, hEvCCase, hEvCOther⟩ := sp
  let ⟨hBHdr, _⟩ := bool_and_true hBRel
  let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
  let N := bbSrc.statements.length
  have hStNoneS : Trusted.MirSemantics.getElem? bbSrc.statements N = none :=
    getElem?_none_of_ge (Nat.le_refl N)
  -- Inspect `locals[dPlace.localId]`
  cases hSlD : Trusted.MirSemantics.getElem? locals dPlace.localId with
  | none =>
    right; right; right
    refine ⟨.unsupported, ?_, ?_⟩
    · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp
      rw [hStNoneS]; dsimp; rw [nat_beq_refl N, if_bool_true rfl]
      unfold evalTerminator; rw [hTermSrc]
      dsimp [evalPrimitiveOperand, evalOperandToSlot]
      rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
    · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp
      rw [hGetTgtCmp]; dsimp [evalStatement]
      rw [hDstProj, if_bool_false (rfl : (!true) = false), ← hLocEq, hDstTy]
      dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
      rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
  | some slD =>
    cases slD with
    | dead =>
      right; right; right
      refine ⟨.undefined, ?_, ?_⟩
      · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp
        rw [hStNoneS]; dsimp; rw [nat_beq_refl N, if_bool_true rfl]
        unfold evalTerminator; rw [hTermSrc]
        dsimp [evalPrimitiveOperand, evalOperandToSlot]
        rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
      · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp
        rw [hGetTgtCmp]; dsimp [evalStatement]
        rw [hDstProj, if_bool_false (rfl : (!true) = false), ← hLocEq, hDstTy]
        dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
        rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
    | live optD =>
      cases optD with
      | none =>
        right; right; right
        refine ⟨.undefined, ?_, ?_⟩
        · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp
          rw [hStNoneS]; dsimp; rw [nat_beq_refl N, if_bool_true rfl]
          unfold evalTerminator; rw [hTermSrc]
          dsimp [evalPrimitiveOperand, evalOperandToSlot]
          rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
          dsimp only
          rw [hPrim, if_bool_false (rfl : (!true) = false)]
        · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp
          rw [hGetTgtCmp]; dsimp [evalStatement]
          rw [hDstProj, if_bool_false (rfl : (!true) = false), ← hLocEq, hDstTy]
          dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
          rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
          dsimp only
          rw [hPrim, if_bool_false (rfl : (!true) = false)]
      | some dv =>
        have hChkDv : checkVal dv discrTy = true :=
          hWt.2 dPlace.localId discrTy (.live (some dv)) hDiscrTy hSlD
        let ⟨_, _, vc, hEvCaseLit, hChkVc⟩ := validTypedConstOperand_elim hValidCase
        -- Split on `discrTy = .bool ∨ .int w s`
        cases isPrimitiveReadableTy_elim hPrim with
        | inl hBoolTy =>
          rw [hBoolTy] at hChkDv hEvCaseLit hChkVc
          dsimp only at hEvCaseLit
          let ⟨db, hdv⟩ := checkVal_bool_iff.mp hChkDv
          let ⟨cb, hvc⟩ := checkVal_bool_iff.mp hChkVc
          subst hdv; subst hvc
          have hEvTgtBool : evalRvalue bTgt.locals locals .bool
              (.binaryOp (if bCase then .eq else .ne)
                (.copy dPlace) (.constant ⟨discrTy, .scalar caseBits⟩)) =
              .ok (.bool (if (db == cb) then bCase else !bCase), locals) := by
            rw [← hLocEq]
            dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
            rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
            dsimp only
            rw [hBoolTy, isPrimitiveReadableTy_bool, if_bool_false (rfl : (!true) = false)]
            dsimp only
            rw [hEvCaseLit]; dsimp only
            rw [isPrimitiveReadableTy_bool, if_bool_false (rfl : (!true) = false)]
            dsimp only
            rw [evalBinOp_bool_eq_ne bCase db cb]
          have hStepSrcBool : evalStep pSrc 0
              { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := N, locals := locals }],
                callerMem := cm } =
              .step { frames := [{ defId := defId,
                                   blockIdx := if (db == cb) then bbCase else bbOther,
                                   stmtIdx := 0, locals := locals }],
                      callerMem := cm } := by
            unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp
            rw [hStNoneS]; dsimp; rw [nat_beq_refl N, if_bool_true rfl]
            unfold evalTerminator; rw [hTermSrc]
            dsimp [evalPrimitiveOperand, evalOperandToSlot]
            rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
            dsimp only
            rw [hBoolTy, isPrimitiveReadableTy_bool, if_bool_false (rfl : (!true) = false)]
            dsimp [evalBoolSwitchBranches]
            rw [hEvCaseLit]
            cases cb <;> cases db <;> rfl
          cases hM : (db == cb) with
          | true =>
            rw [hM, if_bool_true rfl] at hEvTgtBool hStepSrcBool
            left
            exact ⟨0, _, rfl, hStepSrcBool,
              bSrc, bTgt, defId, locals, cm, hBSrc, hBTgt, hBRel, hBCert, hWt,
              Or.inr (Or.inl ⟨rfl, bbCase, blkCase, cCase, bbIdx, bbTgt, N, dst,
                _, bbJoin, bCase, rfl, rfl,
                hGetCase, hStmtsCase, hTermCase, hDstProj, hDstTy, hCCaseTy, hEvCCase,
                hBBT, hGetTgtCmp, hLenTgt, hTermTgt, hEvTgtBool⟩)⟩
          | false =>
            rw [hM, if_bool_false rfl] at hEvTgtBool hStepSrcBool
            left
            exact ⟨0, _, rfl, hStepSrcBool,
              bSrc, bTgt, defId, locals, cm, hBSrc, hBTgt, hBRel, hBCert, hWt,
              Or.inr (Or.inl ⟨rfl, bbOther, blkOther, cOther, bbIdx, bbTgt, N, dst,
                _, bbJoin, !bCase, rfl, rfl,
                hGetOther, hStmtsOther, hTermOther, hDstProj, hDstTy, hCOtherTy, hEvCOther,
                hBBT, hGetTgtCmp, hLenTgt, hTermTgt, hEvTgtBool⟩)⟩
        | inr hIntTy =>
          let ⟨w, s, hTyEq⟩ := hIntTy
          rw [hTyEq] at hChkDv hEvCaseLit hChkVc
          dsimp only at hEvCaseLit
          let ⟨dBits, hdv, hTrD⟩ := checkVal_int_iff.mp hChkDv
          subst hdv
          have hCaseLit : vc = .scalar ⟨w, s, caseBits⟩ ∧
              truncateBits w caseBits = caseBits := by
            dsimp [evalConstLit] at hEvCaseLit
            cases hOvf : (truncateBits w caseBits != caseBits) with
            | true => rw [hOvf] at hEvCaseLit; cases hEvCaseLit
            | false =>
              rw [hOvf] at hEvCaseLit; dsimp at hEvCaseLit
              have hTrC := bitvec_eq_of_bne_false hOvf
              rw [hTrC] at hEvCaseLit
              injection hEvCaseLit with hEqV
              exact ⟨hEqV.symm, hTrC⟩
          let ⟨hvcEq, hTrC⟩ := hCaseLit
          subst hvcEq
          have hEvTgtInt : evalRvalue bTgt.locals locals .bool
              (.binaryOp (if bCase then .eq else .ne)
                (.copy dPlace) (.constant ⟨discrTy, .scalar caseBits⟩)) =
              .ok (.bool (if (dBits == caseBits) then bCase else !bCase), locals) := by
            rw [← hLocEq]
            dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
            rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
            dsimp only
            rw [hTyEq, isPrimitiveReadableTy_int, if_bool_false (rfl : (!true) = false)]
            dsimp only
            rw [hEvCaseLit]; dsimp only
            rw [isPrimitiveReadableTy_int, if_bool_false (rfl : (!true) = false)]
            dsimp only
            rw [evalBinOp_scalar_eq_ne (s := s) (bCase := bCase) hTrD hTrC]
          have hStepSrcInt : evalStep pSrc 0
              { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := N, locals := locals }],
                callerMem := cm } =
              .step { frames := [{ defId := defId,
                                   blockIdx := if (dBits == caseBits) then bbCase else bbOther,
                                   stmtIdx := 0, locals := locals }],
                      callerMem := cm } := by
            unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp
            rw [hStNoneS]; dsimp; rw [nat_beq_refl N, if_bool_true rfl]
            unfold evalTerminator; rw [hTermSrc]
            dsimp [evalPrimitiveOperand, evalOperandToSlot]
            rw [hDProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSlD]
            dsimp only
            rw [hTyEq, isPrimitiveReadableTy_int, if_bool_false (rfl : (!true) = false)]
            dsimp [evalSwitchBranches]
            rw [hTrC, hTrD]
            have hNotBne : (caseBits != caseBits) = false := by
              change (!(caseBits == caseBits)) = false
              rw [bitvec_beq_refl]
              rfl
            rw [hNotBne, if_bool_false rfl]
            cases (dBits == caseBits) <;> rfl
          cases hM : (dBits == caseBits) with
          | true =>
            rw [hM, if_bool_true rfl] at hEvTgtInt hStepSrcInt
            left
            exact ⟨0, _, rfl, hStepSrcInt,
              bSrc, bTgt, defId, locals, cm, hBSrc, hBTgt, hBRel, hBCert, hWt,
              Or.inr (Or.inl ⟨rfl, bbCase, blkCase, cCase, bbIdx, bbTgt, N, dst,
                _, bbJoin, bCase, rfl, rfl,
                hGetCase, hStmtsCase, hTermCase, hDstProj, hDstTy, hCCaseTy, hEvCCase,
                hBBT, hGetTgtCmp, hLenTgt, hTermTgt, hEvTgtInt⟩)⟩
          | false =>
            rw [hM, if_bool_false rfl] at hEvTgtInt hStepSrcInt
            left
            exact ⟨0, _, rfl, hStepSrcInt,
              bSrc, bTgt, defId, locals, cm, hBSrc, hBTgt, hBRel, hBCert, hWt,
              Or.inr (Or.inl ⟨rfl, bbOther, blkOther, cOther, bbIdx, bbTgt, N, dst,
                _, bbJoin, !bCase, rfl, rfl,
                hGetOther, hStmtsOther, hTermOther, hDstProj, hDstTy, hCOtherTy, hEvCOther,
                hBBT, hGetTgtCmp, hLenTgt, hTermTgt, hEvTgtInt⟩)⟩

private theorem matchBranchSimplify_query_iff {pSrc pTgt : Program}
    (hRel : isMatchBranchSimplifyProgram pSrc pTgt = true)
    (hCert : checkMatchBranchSimplifyProgram pSrc pTgt = true)
    (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := isMatchBranchSimplifyProgram_initState_eq hRel hCert q
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  apply stutter_bisim_lift (R := MatchBranchRel pSrc pTgt)
    (fun k => by rw [hInitEq])
  · intro s₀ t₀ hIS hIT
    have hInitS : initState pSrc q = .ok s₀ := hIS
    rw [hInitEq, hIT] at hIS; injection hIS with hST; subst hST
    let ⟨_, _, bSrc, hBSrc, _, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hInitS
    subst hEqS
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodiesRel hBSrc
    let ⟨bTgt', hBTgt', hBCert⟩ := listRel_getElem?_left hCert hBSrc
    rw [hBTgt] at hBTgt'; injection hBTgt' with hEqB; subst hEqB
    exact ⟨1, bSrc, bTgt, pSrc.entryDefId, _, q.callerMem,
           hBSrc, hBTgt, hBRel, hBCert, initLocalsLoop_wellTyped hArgs,
           Or.inl ⟨rfl, 0, 0, rfl, rfl, fun _ _ => Nat.zero_le _⟩⟩
  · intro k s t hR
    let ⟨bSrc, bTgt, defId, locals, cm, hBSrc, hBTgt, hBRel, hBCert, hWt, hModes⟩ := hR
    let ⟨hBHdr, _⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    let ⟨_, hLoopC⟩ := bool_and_true hBCert
    cases hModes with
    | inl hModeA =>
      let ⟨hk1, bbIdx, stmtIdx, hS, hT, hIdxBound⟩ := hModeA
      subst hk1; subst hS; subst hT
      let frame : FrameState :=
        { defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }
      cases hBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx with
      | none =>
        have hLenEq := checkMatchBranchBlocksLoop_length hLoopC
        have hGe : bSrc.basicBlocks.length ≤ bbIdx := by
          cases Nat.lt_or_ge bbIdx bSrc.basicBlocks.length with
          | inr hge => exact hge
          | inl hlt =>
            let ⟨_, hx⟩ := getElem?_some_of_lt bSrc.basicBlocks bbIdx hlt
            rw [hBBS] at hx; cases hx
        have hBBT : Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = none :=
          getElem?_none_of_ge (by rw [← hLenEq]; exact hGe)
        right; right; right
        refine ⟨.unsupported, ?_, ?_⟩
        · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]
        · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]
      | some bbSrc =>
        have hLe := hIdxBound bbSrc hBBS
        let ⟨bbTgt, hBBT, hBlkChoice⟩ := checkMatchBranchBlocksLoop_get hLoopC hBBS
        rw [Nat.zero_add] at hBlkChoice
        cases hBlkChoice with
        | inl hEqBB =>
          subst hEqBB
          -- Identical basic block on both sides!
          cases hSt : Trusted.MirSemantics.getElem? bbSrc.statements stmtIdx with
          | some stmt =>
            have hEvEq := evalStatement_eq_of_same frame cm stmt hLocEq
            cases hEvS : evalStatement bSrc frame cm stmt with
            | fault fk =>
              right; right; right
              refine ⟨fk, ?_, ?_⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hSt]; exact hEvS
              · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hSt]; dsimp
                rw [← hEvEq]; exact hEvS
            | done out =>
              exact False.elim (evalStatement_never_done bSrc frame cm stmt out hEvS)
            | step s' =>
              let ⟨locs', hEqS', hWt'⟩ := evalStatement_preserves_wt hWt hEvS
              subst hEqS'
              have hNextLe : stmtIdx + 1 ≤ bbSrc.statements.length := getElem?_some_lt hSt
              right; left
              refine ⟨1, _, _, ?_, ?_,
                bSrc, bTgt, defId, locs', cm, hBSrc, hBTgt, hBRel, hBCert, hWt',
                Or.inl ⟨rfl, bbIdx, stmtIdx + 1, rfl, rfl, fun bb' hBB' => by
                  rw [hBBS] at hBB'; injection hBB' with hE; subst hE; exact hNextLe⟩⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hSt]; exact hEvS
              · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hSt]; dsimp
                rw [← hEvEq]; exact hEvS
          | none =>
            have hGe : bbSrc.statements.length ≤ stmtIdx := by
              cases Nat.lt_or_ge stmtIdx bbSrc.statements.length with
              | inr hge => exact hge
              | inl hlt =>
                let ⟨_, hx⟩ := getElem?_some_of_lt bbSrc.statements stmtIdx hlt
                rw [hSt] at hx; cases hx
            have hIdxEq : stmtIdx = bbSrc.statements.length := Nat.le_antisymm hLe hGe
            have hEvEq := evalTerminator_eq_of_eq (bb₁ := bbSrc) (bb₂ := bbSrc)
              hLocEq rfl rfl (frame := frame) (cm := cm)
            cases hEvS : evalTerminator bSrc bbSrc frame cm with
            | fault fk =>
              right; right; right
              refine ⟨fk, ?_, ?_⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hSt]; dsimp
                rw [nat_beq_of_eq hIdxEq, if_bool_true rfl]; exact hEvS
              · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hSt]; dsimp
                rw [nat_beq_of_eq hIdxEq, if_bool_true rfl, ← hEvEq]; exact hEvS
            | done out =>
              right; right; left
              refine ⟨out, ?_, ?_⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hSt]; dsimp
                rw [nat_beq_of_eq hIdxEq, if_bool_true rfl]; exact hEvS
              · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hSt]; dsimp
                rw [nat_beq_of_eq hIdxEq, if_bool_true rfl, ← hEvEq]; exact hEvS
            | step s' =>
              let ⟨tgt, locs', hEqS', hWt'⟩ := evalTerminator_preserves_wt hWt hEvS
              subst hEqS'
              right; left
              refine ⟨1, _, _, ?_, ?_,
                bSrc, bTgt, defId, locs', cm, hBSrc, hBTgt, hBRel, hBCert, hWt',
                Or.inl ⟨rfl, tgt, 0, rfl, rfl, fun _ _ => Nat.zero_le _⟩⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hSt]; dsimp
                rw [nat_beq_of_eq hIdxEq, if_bool_true rfl]; exact hEvS
              · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hSt]; dsimp
                rw [nat_beq_of_eq hIdxEq, if_bool_true rfl, ← hEvEq]; exact hEvS
        | inr hRewAt =>
          have sp := checkMatchBranchRewriteAt_elim hRewAt
          cases hSt : Trusted.MirSemantics.getElem? bbSrc.statements stmtIdx with
          | some stmt =>
            let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPrefixEq, _, _, _, _, _, _, _, _, _⟩ := sp
            have hLt : stmtIdx < bbSrc.statements.length := getElem?_some_lt hSt
            have hStT : Trusted.MirSemantics.getElem? bbTgt.statements stmtIdx = some stmt := by
              rw [hPrefixEq stmtIdx hLt]; exact hSt
            have hEvEq := evalStatement_eq_of_same frame cm stmt hLocEq
            cases hEvS : evalStatement bSrc frame cm stmt with
            | fault fk =>
              right; right; right
              refine ⟨fk, ?_, ?_⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hSt]; exact hEvS
              · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hStT]; dsimp
                rw [← hEvEq]; exact hEvS
            | done out =>
              exact False.elim (evalStatement_never_done bSrc frame cm stmt out hEvS)
            | step s' =>
              let ⟨locs', hEqS', hWt'⟩ := evalStatement_preserves_wt hWt hEvS
              subst hEqS'
              right; left
              refine ⟨1, _, _, ?_, ?_,
                bSrc, bTgt, defId, locs', cm, hBSrc, hBTgt, hBRel, hBCert, hWt',
                Or.inl ⟨rfl, bbIdx, stmtIdx + 1, rfl, rfl, fun bb' hBB' => by
                  rw [hBBS] at hBB'; injection hBB' with hE; subst hE; exact hLt⟩⟩
              · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hSt]; exact hEvS
              · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hStT]; dsimp
                rw [← hEvEq]; exact hEvS
          | none =>
            have hGe : bbSrc.statements.length ≤ stmtIdx := by
              cases Nat.lt_or_ge stmtIdx bbSrc.statements.length with
              | inr hge => exact hge
              | inl hlt =>
                let ⟨_, hx⟩ := getElem?_some_of_lt bbSrc.statements stmtIdx hlt
                rw [hSt] at hx; cases hx
            have hIdxEq : stmtIdx = bbSrc.statements.length := Nat.le_antisymm hLe hGe
            subst hIdxEq
            exact matchBranch_diamond_split hBSrc hBTgt hBRel hBCert hWt hBBS hBBT sp
    | inr hModeRest =>
      cases hModeRest with
      | inl hModeB1 =>
        let ⟨hk0, bbArm, blkArm, cArm, bbIdx, bbTgt, N, dst, rvTgt, bbJoin, resBool,
             hS, hT, hGArm, hStArm, hTmArm, hDstProj, hDstTy, hCArmTy, hEvCArm,
             hBBT, hGetCmp, hLenT, hTmTgt, hEvRvT⟩ := hModeB1
        subst hk0; subst hS; subst hT
        have hDstTyT : Trusted.MirSemantics.getElem? bTgt.locals dst.localId = some .bool := by
          rw [← hLocEq]; exact hDstTy
        have hGetArm0 : Trusted.MirSemantics.getElem? blkArm.statements 0 =
            some (.assign dst (.use (.constant cArm))) := by
          rw [hStArm]; rfl
        have hEvRvS : evalRvalue bSrc.locals locals .bool (.use (.constant cArm)) =
            .ok (.bool resBool, locals) := by
          dsimp [evalRvalue, evalOperandToSlot]
          rw [hCArmTy, hEvCArm]
          rfl
        cases hW : writePlace locals dst.localId .bool (.bool resBool) with
        | error fk =>
          right; right; right
          refine ⟨fk, ?_, ?_⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hGArm]; dsimp; rw [hGetArm0]
            dsimp [evalStatement]
            rw [hDstProj, if_bool_false (rfl : (!true) = false), hDstTy]; dsimp
            rw [hEvRvS]; dsimp; rw [hW]
          · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hGetCmp]
            dsimp [evalStatement]
            rw [hDstProj, if_bool_false (rfl : (!true) = false), hDstTyT]; dsimp
            rw [hEvRvT]; dsimp; rw [hW]
        | ok locs' =>
          have hWt' := (writePlace_preserves_wt hWt hDstTy hW).1
          right; left
          refine ⟨0,
            { frames := [{ defId := defId, blockIdx := bbArm, stmtIdx := 1, locals := locs' }],
              callerMem := cm },
            { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := N + 1, locals := locs' }],
              callerMem := cm },
            ?_, ?_,
            bSrc, bTgt, defId, locs', cm, hBSrc, hBTgt, hBRel, hBCert, hWt',
            Or.inr (Or.inr ⟨rfl, bbArm, blkArm, bbIdx, bbTgt, N, bbJoin,
              rfl, rfl, hGArm, by rw [hStArm]; rfl, hTmArm, hBBT, hLenT, hTmTgt⟩)⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hGArm]; dsimp; rw [hGetArm0]
            dsimp [evalStatement]
            rw [hDstProj, if_bool_false (rfl : (!true) = false), hDstTy]; dsimp
            rw [hEvRvS]; dsimp; rw [hW]
          · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hGetCmp]
            dsimp [evalStatement]
            rw [hDstProj, if_bool_false (rfl : (!true) = false), hDstTyT]; dsimp
            rw [hEvRvT]; dsimp; rw [hW]
      | inr hModeB2 =>
        let ⟨hk0, bbArm, blkArm, bbIdx, bbTgt, N, bbJoin,
             hS, hT, hGArm, hLenArm, hTmArm, hBBT, hLenT, hTmTgt⟩ := hModeB2
        subst hk0; subst hS; subst hT
        have hNoneArm : Trusted.MirSemantics.getElem? blkArm.statements 1 = none :=
          getElem?_none_of_ge (by rw [hLenArm]; exact Nat.le_refl 1)
        have hNoneTgt : Trusted.MirSemantics.getElem? bbTgt.statements (N + 1) = none :=
          getElem?_none_of_ge (by rw [hLenT]; exact Nat.le_refl (N + 1))
        right; left
        refine ⟨1,
          { frames := [{ defId := defId, blockIdx := bbJoin, stmtIdx := 0, locals := locals }],
            callerMem := cm },
          { frames := [{ defId := defId, blockIdx := bbJoin, stmtIdx := 0, locals := locals }],
            callerMem := cm },
          ?_, ?_,
          bSrc, bTgt, defId, locals, cm, hBSrc, hBTgt, hBRel, hBCert, hWt,
          Or.inl ⟨rfl, bbJoin, 0, rfl, rfl, fun _ _ => Nat.zero_le _⟩⟩
        · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hGArm]; dsimp; rw [hNoneArm]; dsimp
          rw [hLenArm, if_bool_true (rfl : Nat.beq 1 1 = true)]
          unfold evalTerminator; rw [hTmArm]; rfl
        · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hNoneTgt]; dsimp
          rw [hLenT, nat_beq_refl (N + 1), if_bool_true rfl]
          unfold evalTerminator; rw [hTmTgt]; rfl

private theorem matchBranchSimplify_certified_bidirectional_iff_priv
    (pSrc pTgt : Program)
    (hRel : isMatchBranchSimplifyProgram pSrc pTgt = true)
    (hCert : checkMatchBranchSimplifyProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hHdr, hBodiesRel⟩ := bool_and_true hRel
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodiesRel hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨bTgt'', hBT'', hBCert⟩ := listRel_getElem?_left hCert hBS
    rw [hBT] at hBT''; injection hBT'' with hEqB2; subst hEqB2
    let ⟨hBHdr, _⟩ := bool_and_true hBRel
    let ⟨hPres, hLoopC⟩ := bool_and_true hBCert
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨hBHdr, list_isEmpty_eq_of_length (checkMatchBranchBlocksLoop_length hLoopC), hBounds⟩
  · intro q
    exact matchBranchSimplify_query_iff hRel hCert q
  · intro defId args
    have hRelEntry : isMatchBranchSimplifyProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true :=
      bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodiesRel
    exact (matchBranchSimplify_query_iff hRelEntry hCert { args := args }).1

/-! ### Stage 4 Private Helpers — Layer D3: `JumpThreading` & Mid-Pipeline
Composition -/

private theorem checkAppendedDupBlocks_length {bSrc : Body}
    {specs : List JumpThreadDupSpec} {dups : List BasicBlock}
    (h : checkAppendedDupBlocks bSrc specs dups = true) :
    specs.length = dups.length := by
  induction specs generalizing dups with
  | nil =>
    cases dups with
    | nil => rfl
    | cons _ _ => cases h
  | cons s restS ih =>
    cases dups with
    | nil => cases h
    | cons d restD =>
      dsimp [checkAppendedDupBlocks] at h
      let ⟨_, hTail⟩ := bool_and_true h
      dsimp [List.length]
      rw [ih hTail]

private theorem checkAppendedDupBlocks_get {bSrc : Body}
    {specs : List JumpThreadDupSpec} {dups : List BasicBlock}
    {d : Nat} {spec : JumpThreadDupSpec}
    (h : checkAppendedDupBlocks bSrc specs dups = true)
    (hGet : Trusted.MirSemantics.getElem? specs d = some spec) :
    ∃ bbDup bbJoin,
      Trusted.MirSemantics.getElem? dups d = some bbDup ∧
      spec.joinBlock < bSrc.basicBlocks.length ∧
      spec.resolvedTarget < bSrc.basicBlocks.length ∧
      bbDup.cleanup = false ∧
      Trusted.MirSemantics.getElem? bSrc.basicBlocks spec.joinBlock = some bbJoin ∧
      bbJoin.cleanup = false ∧
      bbJoin.statements = bbDup.statements ∧
      bbDup.terminator = .goto spec.resolvedTarget := by
  induction specs generalizing dups d with
  | nil => cases hGet
  | cons s restS ih =>
    cases dups with
    | nil => cases h
    | cons bbDup restD =>
      dsimp [checkAppendedDupBlocks] at h
      let ⟨hHere, hTail⟩ := bool_and_true h
      cases d with
      | zero =>
        injection hGet with hEq; subst hEq
        let ⟨h123, hM⟩ := bool_and_true hHere
        let ⟨h12, hNotClDup⟩ := bool_and_true h123
        let ⟨hJoinLt, hResLt⟩ := bool_and_true h12
        cases hGJ : Trusted.MirSemantics.getElem? bSrc.basicBlocks s.joinBlock with
        | none => rw [hGJ] at hM; cases hM
        | some bbJoin =>
          rw [hGJ] at hM
          cases hTD : bbDup.terminator with
          | switchInt _ _ | return_ | unreachable | unwindResume
          | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
            rw [hTD] at hM; cases hM
          | goto dupTgt =>
            rw [hTD] at hM; dsimp only at hM
            let ⟨hJ123, _⟩ := bool_and_true hM
            let ⟨hJ12, hStRel⟩ := bool_and_true hJ123
            let ⟨hNotClJoin, hDupTgtEq⟩ := bool_and_true hJ12
            have hTgtEq := nat_beq_eq hDupTgtEq
            subst hTgtEq
            exact ⟨bbDup, bbJoin, rfl, nat_blt_lt hJoinLt, nat_blt_lt hResLt,
                   bool_not_true hNotClDup, rfl, bool_not_true hNotClJoin,
                   listRel_eq (fun _ _ => stmtEq_eq) hStRel, hTD⟩
      | succ m =>
        dsimp [Trusted.MirSemantics.getElem?] at hGet
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih (dups := restD) hTail hGet

private theorem isJumpThreadingBody_isEmpty_eq {dupSpecs : List JumpThreadDupSpec}
    {bSrc bTgt : Body}
    (hRel : isJumpThreadingBody dupSpecs bSrc bTgt = true) :
    bSrc.basicBlocks.isEmpty = bTgt.basicBlocks.isEmpty := by
  unfold isJumpThreadingBody at hRel
  let ⟨h123, hApp⟩ := bool_and_true hRel
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨_, hLenB⟩ := bool_and_true h12
  have hLenTgt := nat_beq_eq hLenB
  cases hBS : bSrc.basicBlocks with
  | nil =>
    rw [hBS] at hLenTgt
    dsimp [List.length] at hLenTgt
    rw [Nat.zero_add] at hLenTgt
    cases dupSpecs with
    | nil =>
      dsimp [List.length] at hLenTgt
      cases hBT : bTgt.basicBlocks with
      | nil => rfl
      | cons _ _ => rw [hBT] at hLenTgt; cases hLenTgt
    | cons sp restS =>
      cases hDrop : bTgt.basicBlocks.drop bSrc.basicBlocks.length with
      | nil =>
        rw [hDrop] at hApp; cases hApp
      | cons bbD restD =>
        rw [hDrop] at hApp
        dsimp [checkAppendedDupBlocks] at hApp
        rw [hBS] at hApp
        dsimp [List.length] at hApp
        let ⟨hHere, _⟩ := bool_and_true hApp
        let ⟨h123', _⟩ := bool_and_true hHere
        let ⟨h12', _⟩ := bool_and_true h123'
        let ⟨hLt0, _⟩ := bool_and_true h12'
        exact False.elim (Nat.not_lt_zero _ (nat_blt_lt hLt0))
  | cons _ restB =>
    have hPosT : 0 < bTgt.basicBlocks.length := by
      rw [hLenTgt, hBS]
      dsimp [List.length]
      rw [Nat.succ_add]
      exact Nat.zero_lt_succ _
    cases hBT : bTgt.basicBlocks with
    | nil => rw [hBT] at hPosT; exact False.elim (Nat.not_lt_zero 0 hPosT)
    | cons _ _ => rfl

private theorem checkJumpThreadingBlocksLoop_get {bSrc bTgt : Body}
    {cert : BodyConstCert} {dupSpecs : List JumpThreadDupSpec}
    {base k : Nat} {rest : List BasicBlock} {bbSrc : BasicBlock}
    (hLoop : checkJumpThreadingBlocksLoop bSrc bTgt cert dupSpecs base rest = true)
    (hGet : Trusted.MirSemantics.getElem? rest k = some bbSrc) :
    checkJumpThreadingBlock bSrc bTgt cert dupSpecs (base + k) bbSrc = true := by
  induction rest generalizing base k with
  | nil => cases hGet
  | cons hd tl ih =>
    dsimp [checkJumpThreadingBlocksLoop] at hLoop
    let ⟨hHere, hTail⟩ := bool_and_true hLoop
    cases k with
    | zero =>
      injection hGet with hEq; subst hEq
      rw [Nat.add_zero]
      exact hHere
    | succ m =>
      have hRec := ih hTail hGet
      rw [Nat.add_assoc, Nat.add_comm 1 m] at hRec
      exact hRec

private theorem allJumpTargetsInBounds_at {bSrc : Body} {bbIdx : BasicBlockId}
    {bbSrc : BasicBlock}
    (hAll : allJumpTargetsInBounds bSrc = true)
    (hBB : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc) :
    (∀ tgt, bbSrc.terminator = .goto tgt → tgt < bSrc.basicBlocks.length) ∧
    (∀ discr ts, bbSrc.terminator = .switchInt discr ts →
      ts.otherwise < bSrc.basicBlocks.length ∧
      ∀ idx cb tgt, Trusted.MirSemantics.getElem? ts.branches idx = some (cb, tgt) →
        tgt < bSrc.basicBlocks.length) := by
  have hAt := list_all_getElem? hAll hBB
  refine ⟨?_, ?_⟩
  · intro tgt hTm
    rw [hTm] at hAt
    exact nat_blt_lt hAt
  · intro discr ts hTm
    rw [hTm] at hAt
    let ⟨hOw, hBrs⟩ := bool_and_true hAt
    refine ⟨nat_blt_lt hOw, ?_⟩
    intro idx cb tgt hGetBr
    exact nat_blt_lt (list_all_getElem?
      (p := fun br => Nat.blt br.2 bSrc.basicBlocks.length) hBrs hGetBr)

private theorem evalTerminator_in_bounds {bSrc : Body} {bbIdx : BasicBlockId}
    {bbSrc : BasicBlock} {frame : FrameState} {cm : CallerMemory} {s' : State}
    (hAll : allJumpTargetsInBounds bSrc = true)
    (hBB : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc)
    (hWt : LocalsWellTyped bSrc.locals frame.locals)
    (hEv : evalTerminator bSrc bbSrc frame cm = .step s') :
    ∃ tgt locs',
      s' = { frames := [{ frame with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
             callerMem := cm } ∧
      tgt < bSrc.basicBlocks.length ∧
      LocalsWellTyped bSrc.locals locs' := by
  let ⟨hGotoBnd, hSwBnd⟩ := allJumpTargetsInBounds_at hAll hBB
  unfold evalTerminator at hEv
  cases hTm : bbSrc.terminator with
  | goto tgt =>
    rw [hTm] at hEv
    injection hEv with hEq; subst hEq
    exact ⟨tgt, frame.locals, rfl, hGotoBnd tgt hTm, hWt⟩
  | return_ =>
    rw [hTm] at hEv; dsimp at hEv
    cases hCl : bbSrc.cleanup with
    | true => rw [hCl] at hEv; cases hEv
    | false =>
      rw [hCl] at hEv; dsimp at hEv
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at hEv; cases hEv
      | some sl0 =>
        rw [h0] at hEv
        cases sl0 with
        | dead => cases hEv
        | live opt0 => cases opt0 <;> cases hEv
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    rw [hTm] at hEv; cases hEv
  | switchInt discr ts =>
    rw [hTm] at hEv; dsimp at hEv
    let ⟨hOwLt, hBrLt⟩ := hSwBnd discr ts hTm
    cases hED : evalPrimitiveOperand bSrc.locals frame.locals discr with
    | error _ => rw [hED] at hEv; cases hEv
    | ok resD =>
      let ⟨dv, locs'⟩ := resD
      rw [hED] at hEv; dsimp at hEv
      have hWt' := evalPrimitiveOperand_preserves_wt hWt hED
      cases dv with
      | scalar sv =>
        dsimp at hEv
        cases hSw : evalSwitchBranches sv.width sv.bits ts.otherwise ts.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok tgt =>
          rw [hSw] at hEv; injection hEv with hEq; subst hEq
          have hTgtLt : tgt < bSrc.basicBlocks.length := by
            cases evalSwitchBranches_outcome hSw with
            | inl hOw => subst hOw; exact hOwLt
            | inr hB => let ⟨idx, cb, hG, _, _⟩ := hB; exact hBrLt idx cb tgt hG
          exact ⟨tgt, locs', rfl, hTgtLt, hWt'⟩
      | bool b =>
        dsimp at hEv
        cases hSw : evalBoolSwitchBranches b ts.otherwise ts.branches with
        | error _ => rw [hSw] at hEv; cases hEv
        | ok tgt =>
          rw [hSw] at hEv; injection hEv with hEq; subst hEq
          have hTgtLt : tgt < bSrc.basicBlocks.length := by
            cases evalBoolSwitchBranches_outcome hSw with
            | inl hOw => subst hOw; exact hOwLt
            | inr hB => let ⟨idx, cb, hG, _⟩ := hB; exact hBrLt idx cb tgt hG
          exact ⟨tgt, locs', rfl, hTgtLt, hWt'⟩
      | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hEv

private theorem evalStatement_diff_blockIdx {bSrc bTgt : Body}
    {defId : DefId} {blk1 blk2 stmtIdx : Nat}
    {locals : List LocalSlot} {cm : CallerMemory} {stmt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals) :
    let f1 : FrameState := { defId := defId, blockIdx := blk1, stmtIdx := stmtIdx, locals := locals }
    let f2 : FrameState := { defId := defId, blockIdx := blk2, stmtIdx := stmtIdx, locals := locals }
    (∃ fk, evalStatement bSrc f1 cm stmt = .fault fk ∧
           evalStatement bTgt f2 cm stmt = .fault fk) ∨
    (∃ locs',
      evalStatement bSrc f1 cm stmt =
        .step { frames := [{ f1 with stmtIdx := stmtIdx + 1, locals := locs' }], callerMem := cm } ∧
      evalStatement bTgt f2 cm stmt =
        .step { frames := [{ f2 with stmtIdx := stmtIdx + 1, locals := locs' }], callerMem := cm }) := by
  cases stmt with
  | nop => exact Or.inr ⟨locals, rfl, rfl⟩
  | unsupported => exact Or.inl ⟨.unsupported, rfl, rfl⟩
  | storageLive id =>
    dsimp [evalStatement]
    rw [← hLocEq]
    cases Trusted.MirSemantics.getElem? bSrc.locals id with
    | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | some ty =>
      dsimp only
      cases setElem? locals id (liveUninitSlot ty) with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some locs' => exact Or.inr ⟨locs', rfl, rfl⟩
  | storageDead id =>
    dsimp [evalStatement]
    cases Nat.beq id 0 with
    | true => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | false =>
      rw [if_bool_false rfl, if_bool_false rfl]
      cases setElem? locals id .dead with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some locs' => exact Or.inr ⟨locs', rfl, rfl⟩
  | assign dst rv =>
    dsimp [evalStatement]
    cases dst.projection.isEmpty with
    | false => exact Or.inl ⟨.unsupported, rfl, rfl⟩
    | true =>
      rw [if_bool_false (rfl : (!true) = false),
          if_bool_false (rfl : (!true) = false), ← hLocEq]
      cases Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
      | none => exact Or.inl ⟨.unsupported, rfl, rfl⟩
      | some dstTy =>
        dsimp only
        cases evalRvalue bSrc.locals locals dstTy rv with
        | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
        | ok res =>
          let ⟨val, locs1⟩ := res
          dsimp only
          cases writePlace locs1 dst.localId dstTy val with
          | error fk => exact Or.inl ⟨fk, rfl, rfl⟩
          | ok locs' => exact Or.inr ⟨locs', rfl, rfl⟩

private theorem resolveConstSwitchTarget_evalTerminator {bSrc : Body}
    {bbJoin : BasicBlock} {dPlace : Place} {targets : SwitchTargets}
    {discrTy : MirTy} {cLit : ConstLit} {resolvedTarget : BasicBlockId}
    {dupExitEnv : List ConstAbsSlot} {frame : FrameState} {cm : CallerMemory}
    (hTerm : bbJoin.terminator = .switchInt (.copy dPlace) targets)
    (hProj : dPlace.projection.isEmpty = true)
    (hDiscrTy : Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId = some discrTy)
    (hMatch : LocalsMatchConstEnv bSrc.locals dupExitEnv frame.locals)
    (hAbs : Trusted.MirSemantics.getElem? dupExitEnv dPlace.localId =
      some (.knownConst discrTy cLit))
    (hRes : resolveConstSwitchTarget ⟨discrTy, cLit⟩ targets = some resolvedTarget) :
    evalTerminator bSrc bbJoin frame cm =
      .step { frames := [{ frame with blockIdx := resolvedTarget, stmtIdx := 0 }],
              callerMem := cm } := by
  have hLtL : dPlace.localId < frame.locals.length := by
    rw [hMatch.2.1]; exact getElem?_some_lt hDiscrTy
  let ⟨sl, hSl⟩ := getElem?_some_of_lt frame.locals dPlace.localId hLtL
  have hSlotM := hMatch.2.2 dPlace.localId discrTy (.knownConst discrTy cLit) sl
    hDiscrTy hAbs hSl
  dsimp [SlotMatchesConst] at hSlotM
  let ⟨_, v, hsl, hEvLit, _⟩ := hSlotM
  subst hsl
  unfold resolveConstSwitchTarget at hRes
  dsimp only at hRes
  cases hPrim : isPrimitiveReadableTy discrTy with
  | false =>
    rw [hPrim, if_bool_true (rfl : (!false) = true)] at hRes
    cases hRes
  | true =>
    rw [hPrim, if_bool_false (rfl : (!true) = false)] at hRes
    rw [hEvLit] at hRes
    unfold evalTerminator
    rw [hTerm]
    dsimp [evalPrimitiveOperand, evalOperandToSlot]
    rw [hProj, if_bool_false (rfl : (!true) = false), hDiscrTy, hSl]
    dsimp only
    rw [hPrim, if_bool_false (rfl : (!true) = false)]
    dsimp only
    cases v with
    | scalar sv =>
      dsimp only at hRes
      cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
      | error _ => rw [hSw] at hRes; cases hRes
      | ok tgt =>
        rw [hSw] at hRes; injection hRes with hEq; subst hEq
        dsimp only; rw [hSw]; rfl
    | bool b =>
      dsimp only at hRes
      cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
      | error _ => rw [hSw] at hRes; cases hRes
      | ok tgt =>
        rw [hSw] at hRes; injection hRes with hEq; subst hEq
        dsimp only; rw [hSw]; rfl
    | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hRes

private theorem stepPlainStmtsConst_cons_elim {bodyLocals : List MirTy}
    {env exitEnv : List ConstAbsSlot} {s : StatementKind} {rest : List StatementKind}
    (h : stepPlainStmtsConst bodyLocals env (s :: rest) = some exitEnv) :
    ∃ nextEnv,
      stepPlainStmtConst bodyLocals env s = some nextEnv ∧
      stepPlainStmtsConst bodyLocals nextEnv rest = some exitEnv := by
  dsimp [stepPlainStmtsConst] at h
  cases hSt : stepPlainStmtConst bodyLocals env s with
  | none => rw [hSt] at h; cases h
  | some nextEnv =>
    rw [hSt] at h
    exact ⟨nextEnv, rfl, h⟩

private theorem jumpThreading_bodies_meta {cs : List BodyConstCert}
    {dss : List (List JumpThreadDupSpec)} {bs1 bs2 : List Body}
    (hLenD : Nat.beq dss.length bs1.length = true)
    (hRel : listRel (fun spPr bTgt => isJumpThreadingBody spPr.1 spPr.2 bTgt)
      (List.zip dss bs1) bs2 = true)
    (hLenC : Nat.beq cs.length bs1.length = true)
    (hCert : listRel (fun csPr bTgt => checkJumpThreadingBody csPr.1 csPr.2.1 csPr.2.2 bTgt)
      (List.zip cs (List.zip dss bs1)) bs2 = true) :
    bs1.length = bs2.length ∧
    (∀ i, Trusted.MirSemantics.getElem? bs1 i = none ↔
      Trusted.MirSemantics.getElem? bs2 i = none) ∧
    (∀ i bSrc, Trusted.MirSemantics.getElem? bs1 i = some bSrc →
      ∃ cBody dupSpecs bTgt,
        Trusted.MirSemantics.getElem? cs i = some cBody ∧
        Trusted.MirSemantics.getElem? dss i = some dupSpecs ∧
        Trusted.MirSemantics.getElem? bs2 i = some bTgt ∧
        isJumpThreadingBody dupSpecs bSrc bTgt = true ∧
        checkJumpThreadingBody cBody dupSpecs bSrc bTgt = true) := by
  induction bs1 generalizing cs dss bs2 with
  | nil =>
    cases dss with
    | cons _ _ => cases hLenD
    | nil =>
      cases bs2 with
      | cons _ _ => cases hRel
      | nil =>
        refine ⟨rfl, fun _ => Iff.rfl, ?_⟩
        intro _ _ hG; cases hG
  | cons b1 rest1 ih =>
    cases dss with
    | nil => cases hLenD
    | cons ds restD =>
      cases cs with
      | nil => cases hLenC
      | cons c restC =>
        cases bs2 with
        | nil => cases hRel
        | cons b2 rest2 =>
          dsimp [List.zip, listRel] at hRel hCert
          let ⟨hRHere, hRTail⟩ := bool_and_true hRel
          let ⟨hCHere, hCTail⟩ := bool_and_true hCert
          let ⟨hSubLen, hSubNone, hSubAt⟩ := ih hLenD hRTail hLenC hCTail
          refine ⟨by dsimp [List.length]; rw [hSubLen], ?_, ?_⟩
          · intro i
            cases i with
            | zero =>
              constructor <;> (intro h; cases h)
            | succ m => exact hSubNone m
          · intro i bSrc hG
            cases i with
            | zero =>
              injection hG with hEq; subst hEq
              exact ⟨c, ds, b2, rfl, rfl, rfl, hRHere, hCHere⟩
            | succ m =>
              exact hSubAt m bSrc hG

private theorem isJumpThreadingProgram_initState_eq {pSrc pTgt : Program}
    {cert : ProgramConstCert} {dupSpecsList : List (List JumpThreadDupSpec)}
    (hRel : isJumpThreadingProgram dupSpecsList pSrc pTgt = true)
    (hCert : checkJumpThreadingProgram cert dupSpecsList pSrc pTgt = true)
    (q : Query) :
    initState pSrc q = initState pTgt q := by
  let ⟨h12R, hBRel⟩ := bool_and_true hRel
  let ⟨hHdr, hLenD⟩ := bool_and_true h12R
  let ⟨h12C, hBCert⟩ := bool_and_true hCert
  let ⟨hLenC, _⟩ := bool_and_true h12C
  let ⟨_, hNoneIff, hAt⟩ := jumpThreading_bodies_meta hLenD hBRel hLenC hBCert
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact hNoneIff pSrc.entryDefId
  · intro b1 hB1
    let ⟨cBody, dupSpecs, b2, _, _, hB2, hJRel, hJCert⟩ := hAt pSrc.entryDefId b1 hB1
    rw [hEnt] at hB2
    let ⟨hJ123, _⟩ := bool_and_true hJRel
    let ⟨hJ12, _⟩ := bool_and_true hJ123
    let ⟨hBHdr, _⟩ := bool_and_true hJ12
    let ⟨hC1234, _⟩ := bool_and_true hJCert
    let ⟨hC123, _⟩ := bool_and_true hC1234
    let ⟨hC12, _⟩ := bool_and_true hC123
    let ⟨hPres, _⟩ := bool_and_true hC12
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨b2, hB2, hBHdr, isJumpThreadingBody_isEmpty_eq hJRel,
           hBounds, initLocalsLoop_eq_of_preservesStorage q.args hBHdr hPres⟩

private noncomputable def checkJumpThreadBlockTermCert (bSrc : Body)
    (cert : BodyConstCert) (dupSpecs : List JumpThreadDupSpec)
    (exitEnv : List ConstAbsSlot) (bbSrc bbTgt : BasicBlock) : Bool :=
  match bbSrc.terminator, bbTgt.terminator with
  | .goto _, .goto tgtIdx =>
    if Nat.blt tgtIdx bSrc.basicBlocks.length then
      blockEq bbSrc bbTgt
    else
      checkJumpThreadRedirectedEdge bSrc cert dupSpecs exitEnv tgtIdx
  | _, _ => blockEq bbSrc bbTgt

private noncomputable def JumpThreadRel (pSrc pTgt : Program)
    (cert : ProgramConstCert) (dupSpecsList : List (List JumpThreadDupSpec))
    (s t : State) : Prop :=
  ∃ defId bSrc bTgt cBody dupSpecs stmtIdx locals cm,
    Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc ∧
    Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt ∧
    Trusted.MirSemantics.getElem? cert defId = some cBody ∧
    Trusted.MirSemantics.getElem? dupSpecsList defId = some dupSpecs ∧
    isJumpThreadingBody dupSpecs bSrc bTgt = true ∧
    checkJumpThreadingBody cBody dupSpecs bSrc bTgt = true ∧
    ((-- Mode 1: Aligned inside original CFG `< bSrc.basicBlocks.length`
      ∃ bbIdx bbSrc bbTgt entryEnv curEnv exitEnv,
        s = { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }],
              callerMem := cm } ∧
        t = { frames := [{ defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }],
              callerMem := cm } ∧
        bbIdx < bSrc.basicBlocks.length ∧
        Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt ∧
        Trusted.MirSemantics.getElem? cBody bbIdx = some (some entryEnv) ∧
        stmtIdx ≤ bbSrc.statements.length ∧
        LocalsMatchConstEnv bSrc.locals curEnv locals ∧
        stepPlainStmtsConst bSrc.locals curEnv (bbSrc.statements.drop stmtIdx) = some exitEnv ∧
        checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length cBody exitEnv
          bbSrc.terminator = true ∧
        isJumpThreadOrigBlock bSrc.basicBlocks.length dupSpecs bbSrc bbTgt = true ∧
        checkJumpThreadBlockTermCert bSrc cBody dupSpecs exitEnv bbSrc bbTgt = true) ∨
     (-- Mode 2: Stepping through `(bbJoin, bbDup)` in 1-to-1 lockstep
      ∃ joinIdx tgtIdx bbJoin bbDup curEnv dupExitEnv dPlace targets resolvedTarget discrTy,
        s = { frames := [{ defId := defId, blockIdx := joinIdx, stmtIdx := stmtIdx, locals := locals }],
              callerMem := cm } ∧
        t = { frames := [{ defId := defId, blockIdx := tgtIdx, stmtIdx := stmtIdx, locals := locals }],
              callerMem := cm } ∧
        Trusted.MirSemantics.getElem? bSrc.basicBlocks joinIdx = some bbJoin ∧
        Trusted.MirSemantics.getElem? bTgt.basicBlocks tgtIdx = some bbDup ∧
        bbJoin.statements = bbDup.statements ∧
        bbJoin.terminator = .switchInt (.copy dPlace) targets ∧
        dPlace.projection.isEmpty = true ∧
        bbDup.terminator = .goto resolvedTarget ∧
        resolvedTarget < bSrc.basicBlocks.length ∧
        stmtIdx ≤ bbJoin.statements.length ∧
        LocalsMatchConstEnv bSrc.locals curEnv locals ∧
        stepPlainStmtsConst bSrc.locals curEnv (bbJoin.statements.drop stmtIdx) = some dupExitEnv ∧
        checkConstEdge bSrc.basicBlocks.length cBody dupExitEnv resolvedTarget = true ∧
        Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId = some discrTy ∧
        (Trusted.MirSemantics.getElem? dupExitEnv dPlace.localId = some .bottom ∨
          ∃ cLit,
            Trusted.MirSemantics.getElem? dupExitEnv dPlace.localId =
              some (.knownConst discrTy cLit) ∧
            resolveConstSwitchTarget ⟨discrTy, cLit⟩ targets = some resolvedTarget)))

private theorem jumpThreading_enter_orig {bSrc bTgt : Body}
    {cBody : BodyConstCert} {dupSpecs : List JumpThreadDupSpec}
    {bbIdx : BasicBlockId} {tgtEnv : List ConstAbsSlot}
    (hJRel : isJumpThreadingBody dupSpecs bSrc bTgt = true)
    (hJCert : checkJumpThreadingBody cBody dupSpecs bSrc bTgt = true)
    (hLt : bbIdx < bSrc.basicBlocks.length)
    (hCGet : Trusted.MirSemantics.getElem? cBody bbIdx = some (some tgtEnv)) :
    ∃ bbSrc bbTgt exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx = some bbTgt ∧
      0 ≤ bbSrc.statements.length ∧
      stepPlainStmtsConst bSrc.locals tgtEnv (bbSrc.statements.drop 0) = some exitEnv ∧
      checkConstTerminatorEdges bSrc.locals bSrc.basicBlocks.length cBody exitEnv
        bbSrc.terminator = true ∧
      isJumpThreadOrigBlock bSrc.basicBlocks.length dupSpecs bbSrc bbTgt = true ∧
      checkJumpThreadBlockTermCert bSrc cBody dupSpecs exitEnv bbSrc bbTgt = true := by
  let ⟨hR123, _⟩ := bool_and_true hJRel
  let ⟨_, hOrigRel⟩ := bool_and_true hR123
  let ⟨_, hLoopC⟩ := bool_and_true hJCert
  let ⟨bbSrc, hBBS⟩ := getElem?_some_of_lt bSrc.basicBlocks bbIdx hLt
  let ⟨bbTgt, hBBTake, hOrigB⟩ := listRel_getElem?_left hOrigRel hBBS
  rw [getElem?_take_lt bTgt.basicBlocks bSrc.basicBlocks.length bbIdx hLt] at hBBTake
  have hBlkC := checkJumpThreadingBlocksLoop_get hLoopC hBBS
  rw [Nat.zero_add] at hBlkC
  unfold checkJumpThreadingBlock at hBlkC
  rw [hCGet, hBBTake] at hBlkC; dsimp only at hBlkC
  let ⟨_, hStepM⟩ := bool_and_true hBlkC
  cases hStS : stepPlainStmtsConst bSrc.locals tgtEnv bbSrc.statements with
  | none => rw [hStS] at hStepM; cases hStepM
  | some exitEnv =>
    rw [hStS] at hStepM; dsimp only at hStepM
    let ⟨hEdges, hTermCertM⟩ := bool_and_true hStepM
    have hTermCert : checkJumpThreadBlockTermCert bSrc cBody dupSpecs exitEnv bbSrc bbTgt = true := by
      cases hTS : bbSrc.terminator <;> cases hTT : bbTgt.terminator <;>
        (rw [hTS, hTT] at hTermCertM; unfold checkJumpThreadBlockTermCert; rw [hTS, hTT]; exact hTermCertM)
    exact ⟨bbSrc, bbTgt, exitEnv, hBBS, hBBTake, Nat.zero_le _, hStS, hEdges, hOrigB, hTermCert⟩

private theorem isJumpThreadOrigBlock_stmts_eq {numSrc : Nat}
    {dupSpecs : List JumpThreadDupSpec} {bbSrc bbTgt : BasicBlock}
    (h : isJumpThreadOrigBlock numSrc dupSpecs bbSrc bbTgt = true) :
    bbSrc.cleanup = bbTgt.cleanup ∧ bbSrc.statements = bbTgt.statements := by
  unfold isJumpThreadOrigBlock at h
  cases bool_or_true h with
  | inl hEq =>
    rw [blockEq_eq hEq]
    exact ⟨rfl, rfl⟩
  | inr hRedir =>
    let ⟨h123, _⟩ := bool_and_true hRedir
    let ⟨h12, hStRel⟩ := bool_and_true h123
    let ⟨hCl1, hCl2⟩ := bool_and_true h12
    rw [bool_not_true hCl1, bool_not_true hCl2]
    exact ⟨rfl, listRel_eq (fun _ _ => stmtEq_eq) hStRel⟩

private theorem jumpThreading_redirect_enter {bSrc bTgt : Body}
    {cBody : BodyConstCert} {dupSpecs : List JumpThreadDupSpec}
    {bbIdx : BasicBlockId} {bbSrc bbTgt : BasicBlock} {exitEnv : List ConstAbsSlot}
    {joinIdx tgtIdx : BasicBlockId}
    (hJRel : isJumpThreadingBody dupSpecs bSrc bTgt = true)
    (hAllBnd : allJumpTargetsInBounds bSrc = true)
    (hBBS : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc)
    (hTS : bbSrc.terminator = .goto joinIdx)
    (hTT : bbTgt.terminator = .goto tgtIdx)
    (hGe : Nat.blt tgtIdx bSrc.basicBlocks.length = false)
    (hOrig : isJumpThreadOrigBlock bSrc.basicBlocks.length dupSpecs bbSrc bbTgt = true)
    (hRedirCert : checkJumpThreadRedirectedEdge bSrc cBody dupSpecs exitEnv tgtIdx = true) :
    ∃ bbJoin bbDup dupExitEnv dPlace targets resolvedTarget discrTy,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks joinIdx = some bbJoin ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks tgtIdx = some bbDup ∧
      bbJoin.statements = bbDup.statements ∧
      bbJoin.terminator = .switchInt (.copy dPlace) targets ∧
      dPlace.projection.isEmpty = true ∧
      bbDup.terminator = .goto resolvedTarget ∧
      resolvedTarget < bSrc.basicBlocks.length ∧
      stepPlainStmtsConst bSrc.locals exitEnv bbJoin.statements = some dupExitEnv ∧
      checkConstEdge bSrc.basicBlocks.length cBody dupExitEnv resolvedTarget = true ∧
      Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId = some discrTy ∧
      (Trusted.MirSemantics.getElem? dupExitEnv dPlace.localId = some .bottom ∨
        ∃ cLit,
          Trusted.MirSemantics.getElem? dupExitEnv dPlace.localId =
            some (.knownConst discrTy cLit) ∧
          resolveConstSwitchTarget ⟨discrTy, cLit⟩ targets = some resolvedTarget) := by
  have hJoinLt : joinIdx < bSrc.basicBlocks.length :=
    (allJumpTargetsInBounds_at hAllBnd hBBS).1 joinIdx hTS
  have hTgtGe : bSrc.basicBlocks.length ≤ tgtIdx := nat_blt_false_ge hGe
  have hJoinNeTgt : joinIdx ≠ tgtIdx := by
    intro hEq; subst hEq
    exact Nat.not_lt_of_ge hTgtGe hJoinLt
  -- In `isJumpThreadOrigBlock`, `blockEq bbSrc bbTgt` is impossible because `joinIdx ≠ tgtIdx`
  have hOrigRight :
      (!bbSrc.cleanup && !bbTgt.cleanup &&
        listRel stmtEq bbSrc.statements bbTgt.statements &&
        match bbSrc.terminator, bbTgt.terminator with
        | .goto j1, .goto t1 =>
          !Nat.blt t1 bSrc.basicBlocks.length &&
            match Trusted.MirSemantics.getElem? dupSpecs (t1 - bSrc.basicBlocks.length) with
            | some spec => Nat.beq spec.joinBlock j1
            | none => false
        | _, _ => false) = true := by
    unfold isJumpThreadOrigBlock at hOrig
    cases bool_or_true hOrig with
    | inr hR => exact hR
    | inl hEq =>
      have hBE := blockEq_eq hEq
      have hTmE : bbSrc.terminator = bbTgt.terminator := congrArg BasicBlock.terminator hBE
      rw [hTS, hTT] at hTmE
      injection hTmE with hJT
      exact False.elim (hJoinNeTgt hJT)
  let ⟨_, hOrigM⟩ := bool_and_true hOrigRight
  rw [hTS, hTT] at hOrigM; dsimp only at hOrigM
  let ⟨_, hSpecM⟩ := bool_and_true hOrigM
  let d := tgtIdx - bSrc.basicBlocks.length
  have hTgtDecomp : bSrc.basicBlocks.length + d = tgtIdx :=
    Nat.add_sub_of_le hTgtGe
  cases hSpec : Trusted.MirSemantics.getElem? dupSpecs d with
  | none => rw [hSpec] at hSpecM; cases hSpecM
  | some spec =>
    rw [hSpec] at hSpecM
    have hSpecJoin : spec.joinBlock = joinIdx := nat_beq_eq hSpecM
    let ⟨_, hApp⟩ := bool_and_true hJRel
    let ⟨bbDup, bbJoin0, hGetDrop, _, hResLt, _, hGJ0, _, hStEq, hDupTm⟩ :=
      checkAppendedDupBlocks_get hApp hSpec
    rw [getElem?_drop bTgt.basicBlocks bSrc.basicBlocks.length d, hTgtDecomp] at hGetDrop
    rw [hSpecJoin] at hGJ0
    -- Unpack `checkJumpThreadRedirectedEdge`
    unfold checkJumpThreadRedirectedEdge at hRedirCert
    dsimp only at hRedirCert
    let ⟨_, hRC1⟩ := bool_and_true hRedirCert
    rw [hSpec] at hRC1; dsimp only at hRC1
    rw [hSpecJoin, hGJ0] at hRC1; dsimp only at hRC1
    cases hJTerm : bbJoin0.terminator with
    | goto _ | return_ | unreachable | unwindResume
    | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
      rw [hJTerm] at hRC1; cases hRC1
    | switchInt discrOp targets =>
      rw [hJTerm] at hRC1
      cases discrOp with
      | move _ | constant _ => cases hRC1
      | copy dPlace =>
        cases hStepDup : stepPlainStmtsConst bSrc.locals exitEnv bbJoin0.statements with
        | none => rw [hStepDup] at hRC1; cases hRC1
        | some dupExitEnv =>
          rw [hStepDup] at hRC1; dsimp only at hRC1
          let ⟨h12, hAbsM⟩ := bool_and_true hRC1
          let ⟨hDProj, hEdgeC⟩ := bool_and_true h12
          cases hDTy : Trusted.MirSemantics.getElem? bSrc.locals dPlace.localId with
          | none => rw [hDTy] at hAbsM; cases hAbsM
          | some discrTy =>
            rw [hDTy] at hAbsM
            cases hDAbs : Trusted.MirSemantics.getElem? dupExitEnv dPlace.localId with
            | none => rw [hDAbs] at hAbsM; cases hAbsM
            | some absSlot =>
              rw [hDAbs] at hAbsM
              cases absSlot with
              | liveUnknown | liveUninit | dead => cases hAbsM
              | bottom =>
                exact ⟨bbJoin0, bbDup, dupExitEnv, dPlace, targets, spec.resolvedTarget, discrTy,
                       hGJ0, hGetDrop, hStEq, hJTerm, hDProj, hDupTm, hResLt,
                       hStepDup, hEdgeC, hDTy, Or.inl hDAbs⟩
              | knownConst cTy cLit =>
                dsimp only at hAbsM
                let ⟨hCTyEqB, hResM⟩ := bool_and_true hAbsM
                have hCTyEq := mirTy_beq_eq hCTyEqB
                subst hCTyEq
                cases hResSw : resolveConstSwitchTarget ⟨cTy, cLit⟩ targets with
                | none => rw [hResSw] at hResM; cases hResM
                | some res =>
                  rw [hResSw] at hResM
                  have hResEq := nat_beq_eq hResM
                  subst hResEq
                  exact ⟨bbJoin0, bbDup, dupExitEnv, dPlace, targets, spec.resolvedTarget, cTy,
                         hGJ0, hGetDrop, hStEq, hJTerm, hDProj, hDupTm, hResLt,
                         hStepDup, hEdgeC, hDTy, Or.inr ⟨cLit, hDAbs, hResSw⟩⟩

private theorem jumpThreading_query_iff {pSrc pTgt : Program}
    {cert : ProgramConstCert} {dupSpecsList : List (List JumpThreadDupSpec)}
    (hRel : isJumpThreadingProgram dupSpecsList pSrc pTgt = true)
    (hCert : checkJumpThreadingProgram cert dupSpecsList pSrc pTgt = true)
    (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hInitEq := isJumpThreadingProgram_initState_eq hRel hCert q
  let ⟨h12R, hBRel⟩ := bool_and_true hRel
  let ⟨_, hLenD⟩ := bool_and_true h12R
  let ⟨h12C, hBCert⟩ := bool_and_true hCert
  let ⟨hLenC, _⟩ := bool_and_true h12C
  let ⟨_, _, hAt⟩ := jumpThreading_bodies_meta hLenD hBRel hLenC hBCert
  apply bisim_lift_disj (R := JumpThreadRel pSrc pTgt cert dupSpecsList)
    (fun k => by rw [hInitEq])
  · intro s₀ t₀ hIS hIT
    have hInitS : initState pSrc q = .ok s₀ := hIS
    rw [hInitEq, hIT] at hIS; injection hIS with hST; subst hST
    let ⟨_, _, bSrc, hBSrc, hNotEmpty, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hInitS
    subst hEqS
    let ⟨cBody, dupSpecs, bTgt, hCBody, hDS, hBTgt, hJRel, hJCert⟩ := hAt pSrc.entryDefId bSrc hBSrc
    let ⟨hC1234, _⟩ := bool_and_true hJCert
    let ⟨_, hEntryOk⟩ := bool_and_true hC1234
    rw [hNotEmpty, if_bool_false rfl] at hEntryOk
    cases hC0 : Trusted.MirSemantics.getElem? cBody 0 with
    | none => rw [hC0] at hEntryOk; cases hEntryOk
    | some opt0 =>
      rw [hC0] at hEntryOk
      cases opt0 with
      | none => cases hEntryOk
      | some env₀ =>
        have hMatch0 := localsMatchConstEnv_mono hEntryOk (initConstEnvLoop_matches hArgs)
        have hPos := list_pos_of_isEmpty_false hNotEmpty
        let ⟨bbSrc, bbTgt, exitEnv, hBBS, hBBT, hLe0, hSt0, hEd0, hOrig0, hTmC0⟩ :=
          jumpThreading_enter_orig hJRel hJCert hPos hC0
        exact ⟨pSrc.entryDefId, bSrc, bTgt, cBody, dupSpecs, 0, _, q.callerMem,
               hBSrc, hBTgt, hCBody, hDS, hJRel, hJCert,
               Or.inl ⟨0, bbSrc, bbTgt, env₀, env₀, exitEnv,
                 rfl, rfl, hPos, hBBS, hBBT, hC0, hLe0, hMatch0, hSt0, hEd0, hOrig0, hTmC0⟩⟩
  · intro s t hR
    let ⟨defId, bSrc, bTgt, cBody, dupSpecs, stmtIdx, locals, cm,
         hBSrc, hBTgt, hCBody, hDS, hJRel, hJCert, hModes⟩ := hR
    let ⟨hR123, _⟩ := bool_and_true hJRel
    let ⟨hR12, _⟩ := bool_and_true hR123
    let ⟨hBHdr, _⟩ := bool_and_true hR12
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    let ⟨hC1234, _⟩ := bool_and_true hJCert
    let ⟨hC123, _⟩ := bool_and_true hC1234
    let ⟨hC12, _⟩ := bool_and_true hC123
    let ⟨_, hAllBnd⟩ := bool_and_true hC12
    cases hModes with
    | inl hMode1 =>
      let ⟨bbIdx, bbSrc, bbTgt, entryEnv, curEnv, exitEnv,
           hS, hT, hBbLt, hBBS, hBBT, hCGet, hIdxLe, hMatch, hStDrop,
           hEdges, hOrigB, hTermCert⟩ := hMode1
      subst hS; subst hT
      let ⟨hCleanEq, hStmtsEq⟩ := isJumpThreadOrigBlock_stmts_eq hOrigB
      let frame : FrameState :=
        { defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }
      cases hStS : Trusted.MirSemantics.getElem? bbSrc.statements stmtIdx with
      | some stmt =>
        have hStT : Trusted.MirSemantics.getElem? bbTgt.statements stmtIdx = some stmt := by
          rw [← hStmtsEq]; exact hStS
        rw [drop_eq_cons_of_getElem? hStS] at hStDrop
        let ⟨nextEnv, hPlain, hStRest⟩ := stepPlainStmtsConst_cons_elim hStDrop
        have hEvEq := evalStatement_eq_of_same frame cm stmt hLocEq
        cases hEvS : evalStatement bSrc frame cm stmt with
        | fault fk =>
          right; right
          refine ⟨fk, ?_, ?_⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; exact hEvS
          · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hStT]; dsimp
            rw [← hEvEq]; exact hEvS
        | done out =>
          exact False.elim (evalStatement_never_done bSrc frame cm stmt out hEvS)
        | step s' =>
          let ⟨locs', hEqS', hNextMatch⟩ := stepPlainStmtConst_sound hMatch hPlain hEvS
          subst hEqS'
          have hNextLe : stmtIdx + 1 ≤ bbSrc.statements.length := getElem?_some_lt hStS
          left
          refine ⟨_, _, ?_, ?_,
            defId, bSrc, bTgt, cBody, dupSpecs, stmtIdx + 1, locs', cm,
            hBSrc, hBTgt, hCBody, hDS, hJRel, hJCert,
            Or.inl ⟨bbIdx, bbSrc, bbTgt, entryEnv, nextEnv, exitEnv,
              rfl, rfl, hBbLt, hBBS, hBBT, hCGet, hNextLe, hNextMatch, hStRest,
              hEdges, hOrigB, hTermCert⟩⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; exact hEvS
          · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hStT]; dsimp
            rw [← hEvEq]; exact hEvS
      | none =>
        have hStT : Trusted.MirSemantics.getElem? bbTgt.statements stmtIdx = none := by
          rw [← hStmtsEq]; exact hStS
        have hGe : bbSrc.statements.length ≤ stmtIdx := by
          cases Nat.lt_or_ge stmtIdx bbSrc.statements.length with
          | inr hge => exact hge
          | inl hlt =>
            let ⟨_, hx⟩ := getElem?_some_of_lt bbSrc.statements stmtIdx hlt
            rw [hStS] at hx; cases hx
        have hIdxLen : stmtIdx = bbSrc.statements.length := Nat.le_antisymm hIdxLe hGe
        have hIdxLenT : stmtIdx = bbTgt.statements.length := by
          rw [← hStmtsEq]; exact hIdxLen
        rw [hIdxLen, drop_length_nil] at hStDrop
        dsimp [stepPlainStmtsConst] at hStDrop
        injection hStDrop with hCurExit; subst hCurExit
        -- Split on whether `bbSrc` and `bbTgt` have `blockEq` or redirected `.goto`
        have hBlockOrRedir :
            blockEq bbSrc bbTgt = true ∨
            (∃ joinIdx tgtIdx,
              bbSrc.terminator = .goto joinIdx ∧
              bbTgt.terminator = .goto tgtIdx ∧
              Nat.blt tgtIdx bSrc.basicBlocks.length = false ∧
              checkJumpThreadRedirectedEdge bSrc cBody dupSpecs curEnv tgtIdx = true) := by
          unfold checkJumpThreadBlockTermCert at hTermCert
          cases hTS : bbSrc.terminator with
          | goto joinIdx =>
            rw [hTS] at hTermCert
            cases hTT : bbTgt.terminator with
            | goto tgtIdx =>
              rw [hTT] at hTermCert; dsimp only at hTermCert
              cases hBlt : Nat.blt tgtIdx bSrc.basicBlocks.length with
              | true =>
                rw [if_bool_true hBlt] at hTermCert
                exact Or.inl hTermCert
              | false =>
                rw [if_bool_false hBlt] at hTermCert
                exact Or.inr ⟨joinIdx, tgtIdx, rfl, rfl, hBlt, hTermCert⟩
            | switchInt _ _ | return_ | unreachable | unwindResume
            | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
              rw [hTT] at hTermCert; exact Or.inl hTermCert
          | switchInt _ _ | return_ | unreachable | unwindResume
          | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
            rw [hTS] at hTermCert; exact Or.inl hTermCert
        cases hBlockOrRedir with
        | inl hBlkEq =>
          have hBBEq := blockEq_eq hBlkEq
          subst hBBEq
          have hEvEq := evalTerminator_eq_of_eq (bb₁ := bbSrc) (bb₂ := bbSrc)
            hLocEq rfl rfl (frame := frame) (cm := cm)
          cases hEvS : evalTerminator bSrc bbSrc frame cm with
          | fault fk =>
            right; right
            refine ⟨fk, ?_, ?_⟩
            · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; dsimp
              rw [nat_beq_of_eq hIdxLen, if_bool_true rfl]; exact hEvS
            · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hStS]; dsimp
              rw [nat_beq_of_eq hIdxLen, if_bool_true rfl, ← hEvEq]; exact hEvS
          | done out =>
            right; left
            refine ⟨out, ?_, ?_⟩
            · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; dsimp
              rw [nat_beq_of_eq hIdxLen, if_bool_true rfl]; exact hEvS
            · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hStS]; dsimp
              rw [nat_beq_of_eq hIdxLen, if_bool_true rfl, ← hEvEq]; exact hEvS
          | step s' =>
            let ⟨tgt, locs', hEqS', hTgtLt, _⟩ :=
              evalTerminator_in_bounds hAllBnd hBBS (localsMatchConstEnv_wt hMatch) hEvS
            let ⟨tgt', locs'', hEqS'', _, hTgtCert⟩ :=
              evalTerminator_constEdges_sound hMatch hEdges hEvS
            rw [hEqS'] at hEqS''
            injection hEqS'' with hFsE _
            injection hFsE with hFrE _
            have hTEq : tgt = tgt' := congrArg FrameState.blockIdx hFrE
            have hLEq : locs' = locs'' := congrArg FrameState.locals hFrE
            subst hTEq; subst hLEq; subst hEqS'
            let ⟨tgtEnv, hCTgt, hTgtMatch⟩ := hTgtCert hTgtLt
            let ⟨bbSrc2, bbTgt2, exitEnv2, hBBS2, hBBT2, hLe2, hSt2, hEd2, hOrig2, hTmC2⟩ :=
              jumpThreading_enter_orig hJRel hJCert hTgtLt hCTgt
            left
            refine ⟨_, _, ?_, ?_,
              defId, bSrc, bTgt, cBody, dupSpecs, 0, locs', cm,
              hBSrc, hBTgt, hCBody, hDS, hJRel, hJCert,
              Or.inl ⟨tgt, bbSrc2, bbTgt2, tgtEnv, tgtEnv, exitEnv2,
                rfl, rfl, hTgtLt, hBBS2, hBBT2, hCTgt, hLe2, hTgtMatch, hSt2, hEd2, hOrig2, hTmC2⟩⟩
            · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; dsimp
              rw [nat_beq_of_eq hIdxLen, if_bool_true rfl]; exact hEvS
            · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hStS]; dsimp
              rw [nat_beq_of_eq hIdxLen, if_bool_true rfl, ← hEvEq]; exact hEvS
        | inr hRedir =>
          let ⟨joinIdx, tgtIdx, hTS, hTT, hGeTgt, hRedirC⟩ := hRedir
          let ⟨bbJoin, bbDup, dupExitEnv, dPlace, targets, resolvedTarget, discrTy,
               hGJ, hGDup, hStJD, hJTerm, hDProj, hDupTm, hResLt,
               hStepDup, hEdgeRes, hDTy, hAbsDisj⟩ :=
            jumpThreading_redirect_enter hJRel hAllBnd hBBS hTS hTT hGeTgt hOrigB hRedirC
          left
          refine ⟨{ frames := [{ defId := defId, blockIdx := joinIdx, stmtIdx := 0, locals := locals }],
                    callerMem := cm },
                  { frames := [{ defId := defId, blockIdx := tgtIdx, stmtIdx := 0, locals := locals }],
                    callerMem := cm },
                  ?_, ?_,
                  defId, bSrc, bTgt, cBody, dupSpecs, 0, locals, cm,
                  hBSrc, hBTgt, hCBody, hDS, hJRel, hJCert,
                  Or.inr ⟨joinIdx, tgtIdx, bbJoin, bbDup, curEnv, dupExitEnv,
                    dPlace, targets, resolvedTarget, discrTy,
                    rfl, rfl, hGJ, hGDup, hStJD, hJTerm, hDProj, hDupTm, hResLt,
                    Nat.zero_le _, hMatch, hStepDup, hEdgeRes, hDTy, hAbsDisj⟩⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hBBS]; dsimp; rw [hStS]; dsimp
            rw [nat_beq_of_eq hIdxLen, if_bool_true rfl]
            unfold evalTerminator; rw [hTS]; rfl
          · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hBBT]; dsimp; rw [hStT]; dsimp
            rw [nat_beq_of_eq hIdxLenT, if_bool_true rfl]
            unfold evalTerminator; rw [hTT]; rfl
    | inr hMode2 =>
      let ⟨joinIdx, tgtIdx, bbJoin, bbDup, curEnv, dupExitEnv,
           dPlace, targets, resolvedTarget, discrTy,
           hS, hT, hGJ, hGDup, hStJD, hJTerm, hDProj, hDupTm, hResLt,
           hIdxLe, hMatch, hStDrop, hEdgeRes, hDTy, hAbsDisj⟩ := hMode2
      subst hS; subst hT
      cases hStJ : Trusted.MirSemantics.getElem? bbJoin.statements stmtIdx with
      | some stmt =>
        have hStD : Trusted.MirSemantics.getElem? bbDup.statements stmtIdx = some stmt := by
          rw [← hStJD]; exact hStJ
        rw [drop_eq_cons_of_getElem? hStJ] at hStDrop
        let ⟨nextEnv, hPlain, hStRest⟩ := stepPlainStmtsConst_cons_elim hStDrop
        cases evalStatement_diff_blockIdx (defId := defId) (blk1 := joinIdx) (blk2 := tgtIdx)
            (stmtIdx := stmtIdx) (locals := locals) (cm := cm) (stmt := stmt) hLocEq with
        | inl hFlt =>
          let ⟨fk, e1, e2⟩ := hFlt
          right; right
          refine ⟨fk, ?_, ?_⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hGJ]; dsimp; rw [hStJ]; exact e1
          · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hGDup]; dsimp; rw [hStD]; exact e2
        | inr hStp =>
          let ⟨locs', e1, e2⟩ := hStp
          let ⟨locs'', hEqS'', hNextMatch⟩ := stepPlainStmtConst_sound hMatch hPlain e1
          injection hEqS'' with hFsE _
          injection hFsE with hFrE _
          have hLEq : locs' = locs'' := congrArg FrameState.locals hFrE
          subst hLEq
          have hNextLe : stmtIdx + 1 ≤ bbJoin.statements.length := getElem?_some_lt hStJ
          left
          refine ⟨_, _, ?_, ?_,
            defId, bSrc, bTgt, cBody, dupSpecs, stmtIdx + 1, locs', cm,
            hBSrc, hBTgt, hCBody, hDS, hJRel, hJCert,
            Or.inr ⟨joinIdx, tgtIdx, bbJoin, bbDup, nextEnv, dupExitEnv,
              dPlace, targets, resolvedTarget, discrTy,
              rfl, rfl, hGJ, hGDup, hStJD, hJTerm, hDProj, hDupTm, hResLt,
              hNextLe, hNextMatch, hStRest, hEdgeRes, hDTy, hAbsDisj⟩⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hGJ]; dsimp; rw [hStJ]; exact e1
          · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hGDup]; dsimp; rw [hStD]; exact e2
      | none =>
        have hStD : Trusted.MirSemantics.getElem? bbDup.statements stmtIdx = none := by
          rw [← hStJD]; exact hStJ
        have hGe : bbJoin.statements.length ≤ stmtIdx := by
          cases Nat.lt_or_ge stmtIdx bbJoin.statements.length with
          | inr hge => exact hge
          | inl hlt =>
            let ⟨_, hx⟩ := getElem?_some_of_lt bbJoin.statements stmtIdx hlt
            rw [hStJ] at hx; cases hx
        have hIdxLen : stmtIdx = bbJoin.statements.length := Nat.le_antisymm hIdxLe hGe
        have hIdxLenD : stmtIdx = bbDup.statements.length := by
          rw [← hStJD]; exact hIdxLen
        rw [hIdxLen, drop_length_nil] at hStDrop
        dsimp [stepPlainStmtsConst] at hStDrop
        injection hStDrop with hCurExit; subst hCurExit
        cases hAbsDisj with
        | inl hBot =>
          have hLtL : dPlace.localId < locals.length := by
            rw [hMatch.2.1]; exact getElem?_some_lt hDTy
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals dPlace.localId hLtL
          exact False.elim (hMatch.2.2 dPlace.localId discrTy .bottom sl hDTy hBot hSl)
        | inr hKnown =>
          let ⟨cLit, hKA, hResSw⟩ := hKnown
          have hEvJoin := resolveConstSwitchTarget_evalTerminator
            (frame := { defId := defId, blockIdx := joinIdx, stmtIdx := stmtIdx, locals := locals })
            (cm := cm)
            hJTerm hDProj hDTy hMatch hKA hResSw
          let ⟨tgtEnv, hCTgt, hTgtMatch⟩ := checkConstEdge_sound hMatch hEdgeRes hResLt
          let ⟨bbSrc2, bbTgt2, exitEnv2, hBBS2, hBBT2, hLe2, hSt2, hEd2, hOrig2, hTmC2⟩ :=
            jumpThreading_enter_orig hJRel hJCert hResLt hCTgt
          left
          refine ⟨{ frames := [{ defId := defId, blockIdx := resolvedTarget, stmtIdx := 0, locals := locals }],
                    callerMem := cm },
                  { frames := [{ defId := defId, blockIdx := resolvedTarget, stmtIdx := 0, locals := locals }],
                    callerMem := cm },
                  ?_, ?_,
                  defId, bSrc, bTgt, cBody, dupSpecs, 0, locals, cm,
                  hBSrc, hBTgt, hCBody, hDS, hJRel, hJCert,
                  Or.inl ⟨resolvedTarget, bbSrc2, bbTgt2, tgtEnv, tgtEnv, exitEnv2,
                    rfl, rfl, hResLt, hBBS2, hBBT2, hCTgt, hLe2, hTgtMatch, hSt2, hEd2, hOrig2, hTmC2⟩⟩
          · unfold evalStep; dsimp; rw [hBSrc]; dsimp; rw [hGJ]; dsimp; rw [hStJ]; dsimp
            rw [nat_beq_of_eq hIdxLen, if_bool_true rfl]
            exact hEvJoin
          · unfold evalStep; dsimp; rw [hBTgt]; dsimp; rw [hGDup]; dsimp; rw [hStD]; dsimp
            rw [nat_beq_of_eq hIdxLenD, if_bool_true rfl]
            unfold evalTerminator; rw [hDupTm]; rfl

private theorem jumpThreading_copyDiscr_certified_bidirectional_iff_priv
    (pSrc pTgt : Program) (cert : ProgramConstCert)
    (dupSpecsList : List (List JumpThreadDupSpec))
    (hRel : isJumpThreadingProgram dupSpecsList pSrc pTgt = true)
    (hCert : checkJumpThreadingProgram cert dupSpecsList pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨h12R, hBRel⟩ := bool_and_true hRel
  let ⟨hHdr, hLenD⟩ := bool_and_true h12R
  let ⟨h12C, hBCert⟩ := bool_and_true hCert
  let ⟨hLenC, _⟩ := bool_and_true h12C
  let ⟨_, _, hAt⟩ := jumpThreading_bodies_meta hLenD hBRel hLenC hBCert
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨cBody, dupSpecs, bTgt', _, _, hBT', hJRel, hJCert⟩ := hAt defId bSrc hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hJ123, _⟩ := bool_and_true hJRel
    let ⟨hJ12, _⟩ := bool_and_true hJ123
    let ⟨hBHdr, _⟩ := bool_and_true hJ12
    let ⟨hC1234, _⟩ := bool_and_true hJCert
    let ⟨hC123, _⟩ := bool_and_true hC1234
    let ⟨hC12, _⟩ := bool_and_true hC123
    let ⟨hPres, _⟩ := bool_and_true hC12
    let ⟨hBounds, _⟩ := preservesAllStorageAnnotations_elim hPres
    exact ⟨hBHdr, isJumpThreadingBody_isEmpty_eq hJRel, hBounds⟩
  · intro q
    exact jumpThreading_query_iff hRel hCert q
  · intro defId args
    have hRelEntry : isJumpThreadingProgram dupSpecsList
        (entryProgForBody pSrc defId) (entryProgForBody pTgt defId) = true :=
      bool_and_intro (bool_and_intro (programHeaderEq_entryProg defId hHdr) hLenD) hBRel
    exact (jumpThreading_query_iff hRelEntry hCert { args := args }).1

/-! #### Theorem 4: End-to-End Mid-Pipeline `CrateTheorem` & `UnitTheorem`
Transport -/

private theorem map_identity_eq_of_listRel_hdr {r : Body → Body → Bool}
    (hHdr : ∀ b1 b2, r b1 b2 = true → bodyHeaderEq b1 b2 = true)
    {bs1 bs2 : List Body} (hRel : listRel r bs1 bs2 = true) :
    bs1.map (fun b => b.identity) = bs2.map (fun b => b.identity) := by
  induction bs1 generalizing bs2 with
  | nil =>
    cases bs2 with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons b1 rest1 ih =>
    cases bs2 with
    | nil => cases hRel
    | cons b2 rest2 =>
      let ⟨hHere, hTail⟩ := bool_and_true hRel
      let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim (hHdr b1 b2 hHere)
      dsimp [List.map]
      rw [hIdEq, ih hTail]

private theorem map_identity_eq_of_jumpThreading {dss : List (List JumpThreadDupSpec)}
    {bs1 bs2 : List Body}
    (hLen : Nat.beq dss.length bs1.length = true)
    (hRel : listRel (fun spPr bTgt => isJumpThreadingBody spPr.1 spPr.2 bTgt)
      (List.zip dss bs1) bs2 = true) :
    bs1.map (fun b => b.identity) = bs2.map (fun b => b.identity) := by
  induction bs1 generalizing dss bs2 with
  | nil =>
    cases dss with
    | cons _ _ => cases hLen
    | nil =>
      cases bs2 with
      | nil => rfl
      | cons _ _ => cases hRel
  | cons b1 rest1 ih =>
    cases dss with
    | nil => cases hLen
    | cons ds restD =>
      cases bs2 with
      | nil => cases hRel
      | cons b2 rest2 =>
        dsimp [List.zip, listRel] at hRel
        let ⟨hHere, hTail⟩ := bool_and_true hRel
        let ⟨h123, _⟩ := bool_and_true hHere
        let ⟨h12, _⟩ := bool_and_true h123
        let ⟨hBHdr, _⟩ := bool_and_true h12
        let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim hBHdr
        dsimp [List.map]
        rw [hIdEq, ih hLen hTail]

private theorem branchAndConstProp_pipeline_crate_and_unit_iff_priv
    (p₀ p₁ p₂ p₃ p₄ : Program)
    (cpCopyCert : ProgramConstCert)
    (cpMoveCert : ProgramConstMoveDeadCert)
    (jtCert : ProgramConstCert)
    (dupSpecsList : List (List JumpThreadDupSpec))
    (hMatch : isMatchBranchSimplifyProgram p₀ p₁ = true)
    (hMatchCert : checkMatchBranchSimplifyProgram p₀ p₁ = true)
    (hCopy : isConstPropCopyProgram p₁ p₂ = true)
    (hCopyCert : checkConstPropCopyProgram cpCopyCert p₁ p₂ = true)
    (hMove : isConstPropMoveProgram p₂ p₃ = true)
    (hMoveCert : checkConstPropMoveDeadProgram cpMoveCert p₂ p₃ = true)
    (hJt : isJumpThreadingProgram dupSpecsList p₃ p₄ = true)
    (hJtCert : checkJumpThreadingProgram jtCert dupSpecsList p₃ p₄ = true) :
    FullSemanticEquiv p₀ p₄ ∧
    (∀ (safety : String → List Val → Prop) (prop : Program → Prop),
      (prop p₄ ↔ prop p₀) →
      (CrateTheorem ⟨p₄, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨p₀, ⟨safety, prop⟩⟩) ∧
      (UnitTheorem ⟨p₄, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨p₀, ⟨safety, prop⟩⟩)) := by
  have hEq01 := matchBranchSimplify_certified_bidirectional_iff_priv p₀ p₁ hMatch hMatchCert
  have hEq12 := constPropCopy_certified_bidirectional_iff_priv p₁ p₂ cpCopyCert hCopy hCopyCert
  have hEq23 := vc_transport_constPropMove_dead_certified_iff_priv p₂ p₃ cpMoveCert hMove hMoveCert
  have hEq34 := jumpThreading_copyDiscr_certified_bidirectional_iff_priv p₃ p₄ jtCert dupSpecsList hJt hJtCert
  let ⟨hHdr01, hB01⟩ := bool_and_true hMatch
  let ⟨hHdr12, hB12⟩ := bool_and_true hCopy
  let ⟨hHdr23, hB23⟩ := bool_and_true hMove
  let ⟨hJt12, hB34⟩ := bool_and_true hJt
  let ⟨hHdr34, hLenD⟩ := bool_and_true hJt12
  have hLen01 : p₀.bodies.length = p₁.bodies.length := listRel_length hB01
  have hLen12 : p₁.bodies.length = p₂.bodies.length := listRel_length hB12
  have hLen23 : p₂.bodies.length = p₃.bodies.length := listRel_length hB23
  have hEq02 := fullSemanticEquiv_trans hLen01 hEq01 hEq12
  have hEq03 := fullSemanticEquiv_trans (hLen01.trans hLen12) hEq02 hEq23
  have hEq04 := fullSemanticEquiv_trans (hLen01.trans (hLen12.trans hLen23)) hEq03 hEq34
  refine ⟨hEq04, ?_⟩
  intro safety prop hProp
  let ⟨hPw01, hVer01, hEnt01, hSc01⟩ := programHeaderEq_elim hHdr01
  let ⟨hPw12, hVer12, hEnt12, hSc12⟩ := programHeaderEq_elim hHdr12
  let ⟨hPw23, hVer23, hEnt23, hSc23⟩ := programHeaderEq_elim hHdr23
  let ⟨hPw34, hVer34, hEnt34, hSc34⟩ := programHeaderEq_elim hHdr34
  have hIds01 := map_identity_eq_of_listRel_hdr
    (fun _ _ h => (bool_and_true h).1) hB01
  have hIds12 := map_identity_eq_of_listRel_hdr
    (fun _ _ h => (bool_and_true h).1) hB12
  have hIds23 := map_identity_eq_of_listRel_hdr
    (fun _ _ h => (bool_and_true h).1) hB23
  have hIds34 := map_identity_eq_of_jumpThreading hLenD hB34
  exact programVerified_iff_of_equiv hEq04
    (hPw01.trans (hPw12.trans (hPw23.trans hPw34)))
    (hVer01.trans (hVer12.trans (hVer23.trans hVer34)))
    (hEnt01.trans (hEnt12.trans (hEnt23.trans hEnt34)))
    (hSc01.trans (hSc12.trans (hSc23.trans hSc34)))
    (hIds01.trans (hIds12.trans (hIds23.trans hIds34)))
    safety prop hProp

/-! ## Part III: Core Target Theorems Directly Over `Trusted.MirSemantics` -/

/-- **Theorem 1a (Certified `ConstPropCopy` Bidirectional Equivalence,
`single_use_consts.rs:25-206` & `dataflow_const_prop.rs:931-1013`):**
Rewriting `Operand.copy ⟨x, []⟩ ↦ Operand.constant c` (`isConstPropCopyProgram`)
under a flow-sensitive `ConstAbsSlot` certificate (`checkConstPropCopyProgram`,
including `SwitchInt` equality-branch refinement) preserves `WellFormed`,
`Behavior`, `ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and
`BodyVerified` bidirectionally (`↔`). -/
theorem constPropCopy_certified_bidirectional_iff
    (pSrc pTgt : Program) (cert : ProgramConstCert)
    (hRel : isConstPropCopyProgram pSrc pTgt = true)
    (hCert : checkConstPropCopyProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact constPropCopy_certified_bidirectional_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 1b (Forward Codegen Refinement for Certified `ConstPropMove`
Without Post-Move Deadness, `single_use_consts.rs:180-188` &
`dataflow_const_prop.rs:953-963`):**
Rewriting `Operand.move ⟨x, []⟩ ↦ Operand.constant c` (`isConstPropMoveProgram`)
when `x` is certified `KnownConst` (`checkConstPropMoveProgram`) refines all
well-formed executions forward (`pSrc → pTgt`) even when `x` is NOT dead after
the move (because skipping `deinitMovedPlace = true` deinitialization leaves
`pTgt`'s local storage strictly more initialized than `pSrc`'s). -/
theorem codegen_constPropMove_certified_refines
    (pSrc pTgt : Program) (cert : ProgramConstCert)
    (hRel : isConstPropMoveProgram pSrc pTgt = true)
    (hCert : checkConstPropMoveProgram cert pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  exact codegen_constPropMove_certified_refines_priv pSrc pTgt cert hRel hCert

/-- **Theorem 1c (Certified Bidirectional VC Transport for `ConstPropMove` With
All-Paths Post-Move Deadness):**
Pairing `isConstPropMoveProgram` with `checkConstPropMoveDeadProgram`
(guaranteeing both `KnownConst` at each rewritten `Operand.move ⟨x, []⟩` and
all-paths deadness of `x` afterward) restores full bidirectional equivalence
(`↔`) across $M_{\text{anneal}}$. -/
theorem vc_transport_constPropMove_dead_certified_iff
    (pSrc pTgt : Program) (cert : ProgramConstMoveDeadCert)
    (hRel : isConstPropMoveProgram pSrc pTgt = true)
    (hCert : checkConstPropMoveDeadProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact vc_transport_constPropMove_dead_certified_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 2 (Certified `MatchBranchSimplification` Bidirectional Equivalence,
`match_branches.rs:116-148, 359-463`):**
Collapsing a boolean-assigning `SwitchInt (.copy ⟨discr, []⟩)` diamond into an
in-place `BinaryOp (.eq / .ne)` + `Goto bbJoin` (`isMatchBranchSimplifyProgram`
paired with `checkMatchBranchSimplifyProgram`) preserves `FullSemanticEquiv`
(`↔`) across all 6 integer widths (signed and unsigned) and `bool`. -/
theorem matchBranchSimplify_certified_bidirectional_iff
    (pSrc pTgt : Program)
    (hRel : isMatchBranchSimplifyProgram pSrc pTgt = true)
    (hCert : checkMatchBranchSimplifyProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact matchBranchSimplify_certified_bidirectional_iff_priv pSrc pTgt hRel hCert

/-- **Theorem 3 (Certified `JumpThreading` Over `Operand.copy` Discriminants
Bidirectional Equivalence, `jump_threading.rs:73-148, 985-1100`):**
Appending specialized duplicate join block(s)
`bbDup = { statements := bbJoin.statements, terminator := .goto resolvedTarget }`
and redirecting certified `Goto bbJoin` predecessor edge(s) to `Goto bbDup`
(`isJumpThreadingProgram` paired with `checkJumpThreadingProgram`) preserves
`FullSemanticEquiv` (`↔`) in exact 1-to-1 step lockstep (including `Diverges`). -/
theorem jumpThreading_copyDiscr_certified_bidirectional_iff
    (pSrc pTgt : Program) (cert : ProgramConstCert)
    (dupSpecsList : List (List JumpThreadDupSpec))
    (hRel : isJumpThreadingProgram dupSpecsList pSrc pTgt = true)
    (hCert : checkJumpThreadingProgram cert dupSpecsList pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact jumpThreading_copyDiscr_certified_bidirectional_iff_priv pSrc pTgt cert dupSpecsList hRel hCert

/-- **Theorem 4 (End-to-End Mid-Pipeline Branch & Constant-Propagation
Bidirectional `CrateTheorem` & `UnitTheorem` Transport, `lib.rs:762-766`):**
Composing certified `MatchBranchSimplify`, certified `ConstPropCopy`, certified
dead-after-move `ConstPropMove`, and certified `JumpThreading` preserves
`FullSemanticEquiv` and transports `CrateTheorem` and `UnitTheorem`
bidirectionally (`↔`) whenever `specs.property` respects the pipeline endpoints. -/
theorem branchAndConstProp_pipeline_crate_and_unit_iff
    (p₀ p₁ p₂ p₃ p₄ : Program)
    (cpCopyCert : ProgramConstCert)
    (cpMoveCert : ProgramConstMoveDeadCert)
    (jtCert : ProgramConstCert)
    (dupSpecsList : List (List JumpThreadDupSpec))
    (hMatch : isMatchBranchSimplifyProgram p₀ p₁ = true)
    (hMatchCert : checkMatchBranchSimplifyProgram p₀ p₁ = true)
    (hCopy : isConstPropCopyProgram p₁ p₂ = true)
    (hCopyCert : checkConstPropCopyProgram cpCopyCert p₁ p₂ = true)
    (hMove : isConstPropMoveProgram p₂ p₃ = true)
    (hMoveCert : checkConstPropMoveDeadProgram cpMoveCert p₂ p₃ = true)
    (hJt : isJumpThreadingProgram dupSpecsList p₃ p₄ = true)
    (hJtCert : checkJumpThreadingProgram jtCert dupSpecsList p₃ p₄ = true) :
    FullSemanticEquiv p₀ p₄ ∧
    (∀ (safety : String → List Val → Prop) (prop : Program → Prop),
      (prop p₄ ↔ prop p₀) →
      (CrateTheorem ⟨p₄, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨p₀, ⟨safety, prop⟩⟩) ∧
      (UnitTheorem ⟨p₄, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨p₀, ⟨safety, prop⟩⟩)) := by
  exact branchAndConstProp_pipeline_crate_and_unit_iff_priv p₀ p₁ p₂ p₃ p₄ cpCopyCert cpMoveCert jtCert dupSpecsList hMatch hMatchCert hCopy hCopyCert hMove hMoveCert hJt hJtCert

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

/-! ### Sharpness Counterexample 1 (`E3-14` `custom_read_after_move_scalar`): `ConstPropMove` Without Post-Move Deadness Erases Use-After-Move UB in Reverse VC Transport -/

noncomputable def progMoveReadAfterSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::constprop_move_read_after"
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progMoveReadAfterTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::constprop_move_read_after"
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .assign ⟨2, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def moveReadAfterConstCert : ProgramConstCert := [[
  some [.liveUninit, .liveUninit, .liveUninit]
]]

noncomputable def moveReadAfterDeadCert : ProgramConstMoveDeadCert := [{
  constCert := [some [.liveUninit, .liveUninit, .liveUninit]]
}]

/-- **Sharpness Theorem CE1 (`E3-14` `custom_read_after_move_scalar`):**
In `_1 = 7_u32; _2 = move _1; _0 = copy _1 + copy _2`, rewriting
`move _1 ↦ const 7_u32` passes `isConstPropMoveProgram` and
`checkConstPropMoveProgram` (so `ForwardCodegenRefines` holds vacuously), yet is
rejected by `checkConstPropMoveDeadProgram` because `_1` is read afterward:
`pSrc` faults with `FaultKind.undefined` (`deinitMovedPlace = true`) whereas
`pTgt` succeeds and returns `14_u32`. -/
theorem ce_constprop_move_without_deadness_reverse_unsound :
    isConstPropMoveProgram progMoveReadAfterSrc progMoveReadAfterTgt = true ∧
    checkConstPropMoveProgram moveReadAfterConstCert
      progMoveReadAfterSrc progMoveReadAfterTgt = true ∧
    checkConstPropMoveDeadProgram moveReadAfterDeadCert
      progMoveReadAfterSrc progMoveReadAfterTgt = false ∧
    NegativeCanaryClaim progMoveReadAfterSrc queryEmpty
      .undefined .unsupported ∧
    PositiveCanaryClaim progMoveReadAfterTgt queryEmpty (u32Val 14) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact negativeCanary_of_execFaults (fuel := 6) (by intro h; cases h) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Sharpness Counterexample 2: Propagating a Constant Clobbered Between Definition and Use Is Unsound -/

noncomputable def progConstClobberSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::constprop_clobbered"
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progConstClobberBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::constprop_clobbered"
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩)),
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE2:** Propagating stale `7_u32` past `_1 = const 99_u32`
into `_0 = copy _1` satisfies syntactic `isConstPropCopyProgram`, is rejected by
flow-sensitive `checkConstPropCopyProgram`, and changes the return value from
`99_u32` to `7_u32`. -/
theorem ce_constprop_clobbered_between_def_and_use_unsound :
    isConstPropCopyProgram progConstClobberSrc progConstClobberBadTgt = true ∧
    checkConstPropCopyProgram [[some [.liveUninit, .liveUninit]]]
      progConstClobberSrc progConstClobberBadTgt = false ∧
    PositiveCanaryClaim progConstClobberSrc queryEmpty (u32Val 99) ∧
    PositiveCanaryClaim progConstClobberBadTgt queryEmpty (u32Val 7) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 6) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Sharpness Counterexample 3: `MatchBranchSimplify` Without `evalConstLit` Boolean Validation Erases `InvalidBool` UB -/

noncomputable def progMatchInvalidBoolSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.bool, u32Ty]
    identity := "ce::match_branch_invalid_bool"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 42, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := []
        terminator := .return_
      }
    ]
  }]

noncomputable def progMatchInvalidBoolBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.bool, u32Ty]
    identity := "ce::match_branch_invalid_bool"
    basicBlocks := [
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .eq (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := []
        terminator := .return_
      }
    ]
  }]

/-- **Sharpness Theorem CE3a:** Collapsing a `SwitchInt` diamond whose matched
arm assigns an invalid `bool` bit pattern (`2`, `ScalarIntError.invalidBool`)
into `_0 = Eq(copy _1, 42_u32)` passes syntactic `isMatchBranchSimplifyProgram`,
is rejected by `checkMatchBranchSimplifyProgram`, and erases `FaultKind.undefined`
on input `42_u32`. -/
theorem ce_match_branch_invalid_bool_or_uninit_discr_unsound :
    isMatchBranchSimplifyProgram
      progMatchInvalidBoolSrc progMatchInvalidBoolBadTgt = true ∧
    checkMatchBranchSimplifyProgram
      progMatchInvalidBoolSrc progMatchInvalidBoolBadTgt = false ∧
    NegativeCanaryClaim progMatchInvalidBoolSrc { args := [u32Val 42] }
      .undefined .unsupported ∧
    PositiveCanaryClaim progMatchInvalidBoolBadTgt { args := [u32Val 42] }
      (.bool true) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact negativeCanary_of_execFaults (fuel := 6) (by intro h; cases h) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Sharpness Counterexample 3b: `MatchBranchSimplify` With Mismatched Comparison Constant Flips Return Value -/

noncomputable def progMatchMismatchSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.bool, u32Ty]
    identity := "ce::match_branch_mismatch_const"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 42, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := []
        terminator := .return_
      }
    ]
  }]

noncomputable def progMatchMismatchBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.bool, u32Ty]
    identity := "ce::match_branch_mismatch_const"
    basicBlocks := [
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .eq (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := []
        terminator := .return_
      }
    ]
  }]

/-- **Sharpness Theorem CE3b:** Emitting `99_u32` instead of `caseBits = 42_u32`
in `MatchBranchSimplify` passes `isMatchBranchSimplifyProgram`, is rejected by
`checkMatchBranchSimplifyProgram`, and flips `42_u32` from `true` to `false`. -/
theorem ce_match_branch_mismatched_case_const_unsound :
    isMatchBranchSimplifyProgram
      progMatchMismatchSrc progMatchMismatchBadTgt = true ∧
    checkMatchBranchSimplifyProgram
      progMatchMismatchSrc progMatchMismatchBadTgt = false ∧
    PositiveCanaryClaim progMatchMismatchSrc { args := [u32Val 42] }
      (.bool true) ∧
    PositiveCanaryClaim progMatchMismatchBadTgt { args := [u32Val 42] }
      (.bool false) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 6) rfl
  · exact positiveCanary_of_execReturns (fuel := 6) rfl

/-! ### Sharpness Counterexample 4 (`E3-14` `custom_jt_preserves_join_prefix`): `JumpThreading` Skipping `bbJoin.statements` Drops Prefix Computations -/

noncomputable def progJtSkipPrefixSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, .bool, u32Ty, u32Ty]
    identity := "ce::jt_skip_join_prefix"
    basicBlocks := [
      {
        statements := [
          .assign ⟨4, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 1, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
        ]
        terminator := .switchInt (.copy ⟨3, []⟩) {
          branches := [(BitVec.ofNat 128 1, 4)]
          otherwise := 5
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def progJtSkipPrefixBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, .bool, u32Ty, u32Ty]
    identity := "ce::jt_skip_join_prefix"
    basicBlocks := [
      {
        statements := [
          .assign ⟨4, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 1, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 6
      },
      {
        statements := [
          .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
        ]
        terminator := .switchInt (.copy ⟨3, []⟩) {
          branches := [(BitVec.ofNat 128 1, 4)]
          otherwise := 5
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩))
        ]
        terminator := .return_
      },
      {
        -- Buggy `bbDup`: omits `bb3`'s prefix `_4 = Add(copy _1, 5_u32)`!
        statements := []
        terminator := .goto 4
      }
    ]
  }]

/-- **Sharpness Theorem CE4 (`E3-14` `custom_jt_preserves_join_prefix`):**
Threading `bb1` through a `bbDup` that omits `bb3.statements`
(`_4 = Add(copy _1, 5_u32)`) is rejected by `isJumpThreadingProgram` and drops
the `+ 5` prefix update on `(10_u32, true)` (`115_u32` in `pSrc` vs. `100_u32`
in `BadTgt`). -/
theorem ce_jumpthread_skipping_join_prefix_stmts_unsound :
    isJumpThreadingProgram [[⟨3, 4⟩]]
      progJtSkipPrefixSrc progJtSkipPrefixBadTgt = false ∧
    PositiveCanaryClaim progJtSkipPrefixSrc
      { args := [u32Val 10, .bool true] } (u32Val 115) ∧
    PositiveCanaryClaim progJtSkipPrefixBadTgt
      { args := [u32Val 10, .bool true] } (u32Val 100) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 12) rfl
  · exact positiveCanary_of_execReturns (fuel := 12) rfl

/-! ### Sharpness Counterexample 5: `JumpThreading` Across `SwitchInt(Move(tag))` Without Deadness Erases Use-After-Move UB -/

noncomputable def progJtMoveDiscrSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::jt_move_discr_no_dead"
    basicBlocks := [
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 1
      },
      {
        statements := []
        terminator := .switchInt (.move ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 1, 2)]
          otherwise := 3
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
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

noncomputable def progJtMoveDiscrBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::jt_move_discr_no_dead"
    basicBlocks := [
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 4
      },
      {
        statements := []
        terminator := .switchInt (.move ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 1, 2)]
          otherwise := 3
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      },
      {
        statements := []
        terminator := .goto 2
      }
    ]
  }]

/-- **Sharpness Theorem CE5:** Replacing `SwitchInt(Move(_1))` with `Goto(2)` in
`bbDup` skips `Operand.move` deinitialization (`deinitMovedPlace = true`), is
rejected by `isJumpThreadingProgram` (`SwitchInt` requires `Operand.copy`), and
erases use-after-move UB (`FaultKind.undefined` in `pSrc` vs. returning `1_u32`
in `BadTgt`). -/
theorem ce_jumpthread_move_discr_without_deadness_reverse_unsound :
    isJumpThreadingProgram [[⟨1, 2⟩]]
      progJtMoveDiscrSrc progJtMoveDiscrBadTgt = false ∧
    NegativeCanaryClaim progJtMoveDiscrSrc queryEmpty
      .undefined .unsupported ∧
    PositiveCanaryClaim progJtMoveDiscrBadTgt queryEmpty (u32Val 1) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact negativeCanary_of_execFaults (fuel := 8) (by intro h; cases h) rfl
  · exact positiveCanary_of_execReturns (fuel := 8) rfl

/-! ### Sharpness Counterexample 6 (`jump_threading.rs:127-134`): `JumpThreading` Using `bbPred` Value When `bbJoin.statements` Mutates `discr` Misroutes Branch -/

noncomputable def progJtMutDiscrSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::jt_mutated_discr_in_join"
    basicBlocks := [
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 1
      },
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 1, 2)]
          otherwise := 3
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def progJtMutDiscrBadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::jt_mutated_discr_in_join"
    basicBlocks := [
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 4
      },
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 1, 2)]
          otherwise := 3
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .goto 2
      }
    ]
  }]

noncomputable def jtMutDiscrAttemptCert : ProgramConstCert := [[
  some [.liveUninit, .liveUninit],
  some [.liveUninit, .knownConst u32Ty (.scalar (BitVec.ofNat 128 1))],
  some [.liveUninit, .liveUnknown],
  some [.liveUninit, .liveUnknown]
]]

/-- **Sharpness Theorem CE6 (`jump_threading.rs:127-134` Mutation Kill Rule):**
When `bb1` overwrites `_1 = const 2_u32` before `SwitchInt(copy _1)`, threading
`bb0` (`_1 = const 1_u32`) to `bb2` (`100_u32`) passes syntactic
`isJumpThreadingProgram [[⟨1, 2⟩]]`, is rejected by `checkJumpThreadingProgram`
(which evaluates `bbJoin.statements` to `dupExitEnv[1] = 2_u32 -> bb3`), and
misroutes `200_u32` to `100_u32`. -/
theorem ce_jumpthread_mutated_discr_in_join_prefix_unsound :
    isJumpThreadingProgram [[⟨1, 2⟩]]
      progJtMutDiscrSrc progJtMutDiscrBadTgt = true ∧
    checkJumpThreadingProgram jtMutDiscrAttemptCert [[⟨1, 2⟩]]
      progJtMutDiscrSrc progJtMutDiscrBadTgt = false ∧
    PositiveCanaryClaim progJtMutDiscrSrc queryEmpty (u32Val 200) ∧
    PositiveCanaryClaim progJtMutDiscrBadTgt queryEmpty (u32Val 100) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 8) rfl
  · exact positiveCanary_of_execReturns (fuel := 8) rfl

/-! ### Constructive Witness 1: Exact `E3-14` `custom_jt_preserves_join_prefix` Two-Arm Duplication (`bb6` & `bb7`) -/

noncomputable def progJtE314Src : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, .bool, u32Ty, u32Ty]
    identity := "witness::e3_14_jt_preserves_prefix"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 1, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
        ]
        terminator := .switchInt (.copy ⟨3, []⟩) {
          branches := [(BitVec.ofNat 128 1, 4)]
          otherwise := 5
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def progJtE314Tgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [u32Ty, u32Ty, .bool, u32Ty, u32Ty]
    identity := "witness::e3_14_jt_preserves_prefix"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 1, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 7
      },
      {
        statements := [
          .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .goto 6
      },
      {
        statements := [
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
        ]
        terminator := .switchInt (.copy ⟨3, []⟩) {
          branches := [(BitVec.ofNat 128 1, 4)]
          otherwise := 5
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩))
        ]
        terminator := .return_
      },
      {
        -- `bb6`: specialized `bb3` duplicate for `bb2` (`_3 == 2 -> bb5`)
        statements := [
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
        ]
        terminator := .goto 5
      },
      {
        -- `bb7`: specialized `bb3` duplicate for `bb1` (`_3 == 1 -> bb4`)
        statements := [
          .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
        ]
        terminator := .goto 4
      }
    ]
  }]

noncomputable def jtE314DupSpecs : List (List JumpThreadDupSpec) := [[
  ⟨3, 5⟩,
  ⟨3, 4⟩
]]

noncomputable def jtE314Cert : ProgramConstCert := [[
  some [.liveUninit, .liveUnknown, .liveUnknown, .liveUninit, .liveUninit],
  some [.liveUninit, .liveUnknown, .liveUnknown, .liveUninit, .liveUninit],
  some [.liveUninit, .liveUnknown, .liveUnknown, .liveUninit, .liveUninit],
  some [.liveUninit, .liveUnknown, .liveUnknown, .liveUnknown, .liveUninit],
  some [.liveUninit, .liveUnknown, .liveUnknown, .liveUnknown, .liveUnknown],
  some [.liveUninit, .liveUnknown, .liveUnknown, .liveUnknown, .liveUnknown]
]]

/-- **Constructive Witness 1 (`E3-14` `custom_jt_after_mir`):**
Exact 1-to-1 encoding of `rustc`'s `JumpThreading` output on
`custom_jt_preserves_join_prefix`, appending `bb6` (`_3 = 2 -> bb5`) and `bb7`
(`_3 = 1 -> bb4`) with `bb3`'s prefix `_4 = Add(copy _1, 5_u32)` preserved,
passing `isJumpThreadingProgram` and `checkJumpThreadingProgram` and returning
`115_u32` on `(10_u32, true)` and `215_u32` on `(10_u32, false)`. -/
theorem witness_e3_14_jump_threading_preserves_join_prefix_exact :
    isJumpThreadingProgram jtE314DupSpecs progJtE314Src progJtE314Tgt = true ∧
    checkJumpThreadingProgram jtE314Cert jtE314DupSpecs
      progJtE314Src progJtE314Tgt = true ∧
    PositiveCanaryClaim progJtE314Src
      { args := [u32Val 10, .bool true] } (u32Val 115) ∧
    PositiveCanaryClaim progJtE314Tgt
      { args := [u32Val 10, .bool true] } (u32Val 115) ∧
    PositiveCanaryClaim progJtE314Src
      { args := [u32Val 10, .bool false] } (u32Val 215) ∧
    PositiveCanaryClaim progJtE314Tgt
      { args := [u32Val 10, .bool false] } (u32Val 215) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 12) rfl
  · exact positiveCanary_of_execReturns (fuel := 12) rfl
  · exact positiveCanary_of_execReturns (fuel := 12) rfl
  · exact positiveCanary_of_execReturns (fuel := 12) rfl

/-! ### Constructive Witness 2: End-to-End 4-Stage Pipeline (`MatchBranchSimplify` -> `ConstPropCopy` -> `ConstPropMove` -> `JumpThreading`) -/

/-- Parameterized 9-local multi-block program exercising all 4 `F1-8` stages
(`pPipe₀ → pPipe₁ → pPipe₂ → pPipe₃ → pPipe₄`) on `(x, flag)`:
1. `MatchBranchSimplify` (`pPipe₀ → pPipe₁`): collapses `bb0`'s `SwitchInt(copy _2)`
   diamond (`bb1`/`bb2` assigning `_6 = true`/`false`) into
   `_6 = BinaryOp(.eq, copy _2, const true); Goto(3)`;
2. `ConstPropCopy` (`pPipe₁ → pPipe₂`): propagates `_3 = 10_u32` across `bb0 ->
   bb3 -> bb4` into `_4 = Use(copy _3) ↦ _4 = Use(const 10_u32)` while `bb3`
   refines `_6` along `SwitchInt(copy _6) [1 -> bb4]`;
3. `ConstPropMove` with cross-block `deadAtEntry` (`pPipe₂ → pPipe₃`): rewrites
   `_5 = Add(copy _1, move _4) ↦ _5 = Add(copy _1, const 10_u32)` in `bb4` with
   `_4` certified dead across `bb6`, `bb7`, and `bb8`; and
4. `JumpThreading` (`pPipe₃ → pPipe₄`): appends `bb9` duplicating `bb6`'s prefix
   `_8 = Add(copy _5, 5_u32)` and redirects `bb4`'s `Goto(6)` to `Goto(9) ->
   Goto(7)`. -/
noncomputable def mkBranchAndConstPipeProg (bb0 : BasicBlock)
    (sCopy4 sMove5 : StatementKind) (bb4Target : BasicBlockId)
    (extraBlocks : List BasicBlock) : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [
      u32Ty, u32Ty, .bool, u32Ty, u32Ty,
      u32Ty, .bool, u32Ty, u32Ty
    ]
    identity := "witness::f1_8_branch_and_constprop_pipeline"
    basicBlocks := [
      bb0,
      {
        statements := [
          .assign ⟨6, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := [
          .assign ⟨6, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .goto 3
      },
      {
        statements := []
        terminator := .switchInt (.copy ⟨6, []⟩) {
          branches := [(BitVec.ofNat 128 1, 4)]
          otherwise := 5
        }
      },
      {
        statements := [
          sCopy4,
          sMove5,
          .assign ⟨7, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .goto bb4Target
      },
      {
        statements := [
          .assign ⟨5, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
          .assign ⟨7, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .goto 6
      },
      {
        statements := [
          .assign ⟨8, []⟩ (.binaryOp .add (.copy ⟨5, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
        ]
        terminator := .switchInt (.copy ⟨7, []⟩) {
          branches := [(BitVec.ofNat 128 1, 7)]
          otherwise := 8
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨8, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨8, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩))
        ]
        terminator := .return_
      }
    ] ++ extraBlocks
  }]

noncomputable def pipeBb0Src : BasicBlock := {
  statements := [
    .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩))
  ]
  terminator := .switchInt (.copy ⟨2, []⟩) {
    branches := [(BitVec.ofNat 128 1, 1)]
    otherwise := 2
  }
}

noncomputable def pipeBb0Simplified : BasicBlock := {
  statements := [
    .assign ⟨3, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩)),
    .assign ⟨6, []⟩ (.binaryOp .eq (.copy ⟨2, []⟩)
      (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩))
  ]
  terminator := .goto 3
}

noncomputable def pipeSCopy4Src : StatementKind :=
  .assign ⟨4, []⟩ (.use (.copy ⟨3, []⟩))

noncomputable def pipeSCopy4Tgt : StatementKind :=
  .assign ⟨4, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩))

noncomputable def pipeSMove5Src : StatementKind :=
  .assign ⟨5, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.move ⟨4, []⟩))

noncomputable def pipeSMove5Tgt : StatementKind :=
  .assign ⟨5, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
    (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 10)⟩))

noncomputable def pipeBb9Dup : BasicBlock := {
  statements := [
    .assign ⟨8, []⟩ (.binaryOp .add (.copy ⟨5, []⟩)
      (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
  ]
  terminator := .goto 7
}

noncomputable def pPipe₀ : Program :=
  mkBranchAndConstPipeProg pipeBb0Src pipeSCopy4Src pipeSMove5Src 6 []

noncomputable def pPipe₁ : Program :=
  mkBranchAndConstPipeProg pipeBb0Simplified pipeSCopy4Src pipeSMove5Src 6 []

noncomputable def pPipe₂ : Program :=
  mkBranchAndConstPipeProg pipeBb0Simplified pipeSCopy4Tgt pipeSMove5Src 6 []

noncomputable def pPipe₃ : Program :=
  mkBranchAndConstPipeProg pipeBb0Simplified pipeSCopy4Tgt pipeSMove5Tgt 6 []

noncomputable def pPipe₄ : Program :=
  mkBranchAndConstPipeProg pipeBb0Simplified pipeSCopy4Tgt pipeSMove5Tgt 9
    [pipeBb9Dup]

noncomputable def pipeEntryEnv : List ConstAbsSlot := [
  .liveUninit, .liveUnknown, .liveUnknown, .liveUninit, .liveUninit,
  .liveUninit, .liveUninit, .liveUninit, .liveUninit
]

noncomputable def pipeBb3Env : List ConstAbsSlot := [
  .liveUninit, .liveUnknown, .liveUnknown,
  .knownConst u32Ty (.scalar (BitVec.ofNat 128 10)), .liveUninit,
  .liveUninit, .liveUnknown, .liveUninit, .liveUninit
]

noncomputable def pipeBb4Env : List ConstAbsSlot := [
  .liveUninit, .liveUnknown, .liveUnknown,
  .knownConst u32Ty (.scalar (BitVec.ofNat 128 10)), .liveUninit,
  .liveUninit, .knownConst .bool (.scalar (BitVec.ofNat 128 1)),
  .liveUninit, .liveUninit
]

noncomputable def pipeBb6Env : List ConstAbsSlot := [
  .liveUninit, .liveUnknown, .liveUnknown,
  .knownConst u32Ty (.scalar (BitVec.ofNat 128 10)), .liveUninit,
  .liveUnknown, .liveUnknown, .liveUnknown, .liveUninit
]

noncomputable def pipeBb78Env : List ConstAbsSlot := [
  .liveUninit, .liveUnknown, .liveUnknown,
  .knownConst u32Ty (.scalar (BitVec.ofNat 128 10)), .liveUninit,
  .liveUnknown, .liveUnknown, .liveUnknown, .liveUnknown
]

noncomputable def pipeBodyConstCert : BodyConstCert := [
  some pipeEntryEnv,
  none,
  none,
  some pipeBb3Env,
  some pipeBb4Env,
  some pipeBb3Env,
  some pipeBb6Env,
  some pipeBb78Env,
  some pipeBb78Env
]

noncomputable def pipeConstCert : ProgramConstCert := [pipeBodyConstCert]

noncomputable def pipeMoveDeadCert : ProgramConstMoveDeadCert := [{
  constCert := pipeBodyConstCert
  deadAtEntry := [[], [], [], [], [], [], [4], [4], [4]]
}]

noncomputable def pipeDupSpecs : List (List JumpThreadDupSpec) := [[⟨6, 7⟩]]

/-- **Constructive Witness 2:** Non-vacuous 4-stage pipeline witness
(`pPipe₀ ≠ pPipe₄`) simultaneously certifying `MatchBranchSimplify`,
`ConstPropCopy` (with `SwitchInt` equality-branch refinement), `ConstPropMove`
(with cross-block `deadAtEntry`), and prefix-duplicating `JumpThreading`,
returning `142_u32` on `(27_u32, true)` and `242_u32` on `(27_u32, false)`. -/
theorem witness_branchAndConstProp_pipeline_nonvacuous :
    pPipe₀ ≠ pPipe₄ ∧
    isMatchBranchSimplifyProgram pPipe₀ pPipe₁ = true ∧
    checkMatchBranchSimplifyProgram pPipe₀ pPipe₁ = true ∧
    isConstPropCopyProgram pPipe₁ pPipe₂ = true ∧
    checkConstPropCopyProgram pipeConstCert pPipe₁ pPipe₂ = true ∧
    isConstPropMoveProgram pPipe₂ pPipe₃ = true ∧
    checkConstPropMoveDeadProgram pipeMoveDeadCert pPipe₂ pPipe₃ = true ∧
    isJumpThreadingProgram pipeDupSpecs pPipe₃ pPipe₄ = true ∧
    checkJumpThreadingProgram pipeConstCert pipeDupSpecs pPipe₃ pPipe₄ = true ∧
    PositiveCanaryClaim pPipe₀
      { args := [u32Val 27, .bool true] } (u32Val 142) ∧
    PositiveCanaryClaim pPipe₄
      { args := [u32Val 27, .bool true] } (u32Val 142) ∧
    PositiveCanaryClaim pPipe₀
      { args := [u32Val 27, .bool false] } (u32Val 242) ∧
    PositiveCanaryClaim pPipe₄
      { args := [u32Val 27, .bool false] } (u32Val 242) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    cases h
  · exact positiveCanary_of_execReturns (fuel := 18) rfl
  · exact positiveCanary_of_execReturns (fuel := 18) rfl
  · exact positiveCanary_of_execReturns (fuel := 18) rfl
  · exact positiveCanary_of_execReturns (fuel := 18) rfl

end VrustcFormal.F1_8
