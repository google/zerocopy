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

namespace VrustcFormal.F1_6

open Trusted.MirAst Trusted.MirSemantics

/-!
# Direct `Trusted.MirSemantics` Bridge: `InstSimplify` & `GVN` Algebraic Peepholes, Constant Folding, and Enum-Discriminant Simplification (`VrustcFormal.F1_6`)

This module formalizes the expression-level algebraic simplification, constant
folding, double-unary involution, and enum-discriminant folding passes of
`compiler/rustc_mir_transform/src/instsimplify.rs` (`simplify_bool_cmp`) and
`compiler/rustc_mir_transform/src/gvn.rs` (`simplify_unary`,
`simplify_binary_inner`, and `simplify_discriminant` at `rust-lang/rust` commit
`8144389c895da997dbdecaa635e41d6a50be6ffd`) directly over Anneal's live TCB
syntax (`Trusted.MirAst`) and small-step operational semantics
(`Trusted.MirSemantics`).

All public theorem statements reference strictly `Init.*`, `Trusted.MirAst.*`,
`Trusted.MirSemantics.*`, and pure definitions in `VrustcFormal.F1_6` (zero
surrogate MIR AST, zero `Anneal.*` references).

## Five Ground-Truth Semantic Findings Mechanized Directly on $M_{\text{anneal}}$

1. **Exact Unconditional Bidirectional Equivalence of `InstSimplify` Boolean
   Comparison Simplification and `GVN` Neutral-Identity Peepholes (`↔`):**
   - `InstSimplify::simplify_bool_cmp` (`instsimplify.rs:106-135`, rewriting
     `Eq`/`Ne` on statically `.bool`-typed operands against valid `false`/`true`
     boolean constants to `Use(opnd)` or `UnaryOp(Not, opnd)`) and
     `GVN::simplify_binary_inner` neutral-identity rules (`gvn.rs:1463-1499`,
     covering `Add`/`AddUnchecked`/`BitOr`/`BitXor` with `0`, `Sub`/`SubUnchecked`
     with right `0`, `Mul`/`MulUnchecked` with `1`, `Div` with right `+1` even
     at signed `INT_MIN`, `BitAnd` with width-truncated `ALL_ONES`, and wrapping
     `Shl`/`Shr` with any valid integer `0` RHS) are **unconditionally
     bidirectionally equivalent (`↔`)** across all $M_{\text{anneal}}$ judgments
     without any dataflow certificate.
   - By contrast, rewriting `Div(x, -1)` to `Neg(x)` is **unsound** at signed
     `INT_MIN` (`ce_div_neg_one_to_neg_unsound_at_int_min`).

2. **Live Upstream `GVN` UB-Erasure Asymmetry on `0 / x` and `0 % x`
   (`gvn.rs:1511-1518`):**
   - Upstream `gvn.rs:1511-1518` folds `(BinOp::Div | BinOp::Rem, Left(0), _) =>
     0` unconditionally—even under `-Zmir-preserve-ub=yes`—silently erasing
     `DivisionByZero` / `RemainderByZero` UB when `rhs == 0`
     (`ce_gvn_zero_div_zero_erases_ub`).
   - On $M_{\text{anneal}}$, `isZeroLhsDivRemProgram` is **unconditionally
     forward-sound** for codegen (`ForwardCodegenRefines pSrc pTgt`), while
     reverse VC transport (`pTgt → pSrc`) requires `checkZeroLhsDivRemProgram`
     certifying that `rhs` is a non-`move`, initialized, non-zero operand.

3. **Absorbing & Self-Canceling Peephole Asymmetry (`gvn.rs:1501-1540`):**
   - Folding `Mul`/`MulUnchecked`/`BitAnd` with `0`, wrapping `Shl`/`Shr` with
     left `0` (excluding `ShlUnchecked`/`ShrUnchecked`, locked by
     `ce_shl_unchecked_zero_lhs_overflow_unsound`), `Rem(x, 1)` with right `+1`,
     `BitOr` with `ALL_ONES`, and self-canceling `Sub`/`SubUnchecked`/`BitXor`/
     `Eq`/`Ne` on identical `.copy place` operands (never `.move place`, locked
     by `ce_self_xor_double_move_unsound`) is **unconditionally forward-sound**
     for codegen (`Theorem 4a`), but erases uninitialized-read UB
     (`ce_absorbing_mul_zero_uninit_unsound`) and `deinitMovedPlace = true`
     use-after-move UB (`ce_absorbing_mul_zero_move_deinit_unsound`) in reverse
     VC transport unless paired with `checkAbsorbingOrSelfCancelProgram`
     (`Theorem 4b`).

4. **Exact Unconditional Involution of Adjacent `Not(Not(x))` and `Neg(Neg(x))`
   Chains—Including Signed `INT_MIN` (`gvn.rs:1356-1358`):**
   - Because `Rvalue::UnaryOp(UnOp::Neg, _)` in runtime MIR wraps modulo $2^w$
     (`-INT_MIN == INT_MIN` in two's complement without faulting), rewriting
     `_t = UnaryOp(op, copy x); _dst = UnaryOp(op, copy _t)` (with `_t ≠ x` and
     `op ∈ {.not, .neg}`) to `_t = UnaryOp(op, copy x); _dst = Use(copy x)` is
     **unconditionally bidirectionally equivalent (`↔`)** across all inputs,
     including `INT8_MIN = -128i8` (`witness_neg_neg_int8_min_exact`).

5. **Constant `UnaryOp`/`BinaryOp` Folding & Certified Enum `Discriminant`
   Simplification (`gvn.rs:1134-1144`):**
   - Validated constant folding via `evalConstLit` + `evalUnOp`/`evalBinOp` and
     1-variant enum `Discriminant` folding refine unconditionally forward
     (`Theorem 6a`), while `DeadLocal` UB on a `.dead` 1-variant ZST enum
     (`ce_enum_discr_dead_zst_unsound`) and variant selection on multi-variant
     enums require `checkConstAndEnumDiscrFoldProgram` for full bidirectional
     equivalence (`Theorem 6b`).
-/

/-! ## Part I: Structural Equality & Executable Algebraic Pass Predicates -/

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

/-- Static `MirTy` lookup for unprojected `Place`s and `ConstOperand`s. -/
noncomputable def operandStaticTy? (bodyLocals : List MirTy) :
    Operand → Option MirTy
  | .copy p | .move p =>
    if p.projection.isEmpty then
      Trusted.MirSemantics.getElem? bodyLocals p.localId
    else
      none
  | .constant c => some c.ty

/-- Width-truncated `ALL_ONES` bitmask (`2^(w.bitWidth) - 1` in `BitVec 128`),
matching `layout.size.truncate(u128::MAX)` in `gvn.rs:1495`. -/
noncomputable def allOnesBits (w : IntWidth) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.pow 2 w.bitWidth - 1)

/-- Check `c == ConstOperand⟨.bool, .scalar 0⟩`. -/
noncomputable def isFalseBoolConst (c : ConstOperand) : Bool :=
  MirTy.beq c.ty .bool && constLitEq c.lit (.scalar (BitVec.ofNat 128 0))

/-- Check `c == ConstOperand⟨.bool, .scalar 1⟩`. -/
noncomputable def isTrueBoolConst (c : ConstOperand) : Bool :=
  MirTy.beq c.ty .bool && constLitEq c.lit (.scalar (BitVec.ofNat 128 1))

/-- Check `c == ConstOperand⟨.int w s, .scalar 0⟩`. -/
noncomputable def isIntZeroConst (w : IntWidth) (s : Bool)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty (.int w s) && constLitEq c.lit (.scalar (BitVec.ofNat 128 0))

/-- Check `c == ConstOperand⟨.int w s, .scalar 1⟩` (`+1` at all `IntWidth`s). -/
noncomputable def isIntOneConst (w : IntWidth) (s : Bool)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty (.int w s) && constLitEq c.lit (.scalar (BitVec.ofNat 128 1))

/-- Check `c == ConstOperand⟨.int w s, .scalar (allOnesBits w)⟩`. -/
noncomputable def isIntAllOnesConst (w : IntWidth) (s : Bool)
    (c : ConstOperand) : Bool :=
  MirTy.beq c.ty (.int w s) && constLitEq c.lit (.scalar (allOnesBits w))

/-- Check whether `c` is a valid `0` constant of any integer type `.int rw rs`
(used for shift-by-zero `Shl`/`Shr` RHS operands). -/
noncomputable def isAnyIntZeroConst (c : ConstOperand) : Bool :=
  match c.ty, c.lit with
  | .int _ _, .scalar bits => bits == BitVec.ofNat 128 0
  | _, _ => false

/-! ### Pass 1: `InstSimplify::simplify_bool_cmp` (`instsimplify.rs:106-135`) -/

/-- Match one orientation of `simplify_bool_cmp` where `c` is the constant
boolean operand and `opnd` is the retained `.bool`-typed operand. -/
noncomputable def matchesBoolCmpArm (bodyLocals : List MirTy) (op : BinOp)
    (c : ConstOperand) (opnd : Operand) (rvTgt : Rvalue) : Bool :=
  match operandStaticTy? bodyLocals opnd with
  | some .bool =>
    if (binOpEq op .eq && isTrueBoolConst c) ||
        (binOpEq op .ne && isFalseBoolConst c) then
      rvalueEq rvTgt (.use opnd)
    else if (binOpEq op .eq && isFalseBoolConst c) ||
        (binOpEq op .ne && isTrueBoolConst c) then
      rvalueEq rvTgt (.unaryOp .not opnd)
    else
      false
  | _ => false

noncomputable def isBoolCmpSimplifyRewrite (bodyLocals : List MirTy) :
    StatementKind → StatementKind → Bool
  | .assign dst (.binaryOp op lhs rhs), .assign dst' rvTgt =>
    placeEq dst dst' &&
      dst.projection.isEmpty &&
      (match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
       | some .bool => true
       | _ => false) &&
      ((match lhs with
        | .constant c => matchesBoolCmpArm bodyLocals op c rhs rvTgt
        | _ => false) ||
       (match rhs with
        | .constant c => matchesBoolCmpArm bodyLocals op c lhs rvTgt
        | _ => false))
  | _, _ => false

noncomputable def isBoolCmpSimplifyStmt (bodyLocals : List MirTy)
    (sSrc sTgt : StatementKind) : Bool :=
  isBoolCmpSimplifyRewrite bodyLocals sSrc sTgt || stmtEq sSrc sTgt

noncomputable def isBoolCmpSimplifyBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (isBoolCmpSimplifyStmt bodyLocals) b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isBoolCmpSimplifyBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isBoolCmpSimplifyBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isBoolCmpSimplifyProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt && listRel isBoolCmpSimplifyBody pSrc.bodies pTgt.bodies

/-! ### Pass 2: `GVN::simplify_binary_inner` Neutral Identities (`gvn.rs:1463-1499`) -/

/-- Left-neutral constant `c` (`op(c, opnd) ↦ opnd`) for type `dstTy`. -/
noncomputable def isLeftNeutralConstFor (dstTy : MirTy) (op : BinOp)
    (c : ConstOperand) : Bool :=
  match dstTy with
  | .int w s =>
    match op with
    | .add | .addUnchecked | .bitOr | .bitXor => isIntZeroConst w s c
    | .mul | .mulUnchecked => isIntOneConst w s c
    | .bitAnd => isIntAllOnesConst w s c
    | _ => false
  | .bool =>
    match op with
    | .bitOr | .bitXor => isFalseBoolConst c
    | .bitAnd => isTrueBoolConst c
    | _ => false
  | _ => false

/-- Right-neutral constant `c` (`op(opnd, c) ↦ opnd`) for type `dstTy`,
including `Sub`/`SubUnchecked` with `0`, `Div` with `+1` (valid even at signed
`INT_MIN`), and checked/wrapping `Shl`/`Shr` with any valid integer `0` RHS. -/
noncomputable def isRightNeutralConstFor (dstTy : MirTy) (op : BinOp)
    (c : ConstOperand) : Bool :=
  match dstTy with
  | .int w s =>
    match op with
    | .add | .addUnchecked | .sub | .subUnchecked
    | .bitOr | .bitXor => isIntZeroConst w s c
    | .mul | .mulUnchecked | .div => isIntOneConst w s c
    | .bitAnd => isIntAllOnesConst w s c
    | .shl | .shr => isAnyIntZeroConst c
    | _ => false
  | .bool =>
    match op with
    | .bitOr | .bitXor => isFalseBoolConst c
    | .bitAnd => isTrueBoolConst c
    | _ => false
  | _ => false

noncomputable def isNeutralIdentityRewrite (bodyLocals : List MirTy) :
    StatementKind → StatementKind → Bool
  | .assign dst (.binaryOp op lhs rhs), .assign dst' (.use opndTgt) =>
    placeEq dst dst' &&
      dst.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => false
      | some dstTy =>
        ((match lhs, operandStaticTy? bodyLocals rhs with
          | .constant c, some rhsTy =>
            MirTy.beq rhsTy dstTy &&
              isLeftNeutralConstFor dstTy op c &&
              operandEq rhs opndTgt
          | _, _ => false) ||
         (match rhs, operandStaticTy? bodyLocals lhs with
          | .constant c, some lhsTy =>
            MirTy.beq lhsTy dstTy &&
              isRightNeutralConstFor dstTy op c &&
              operandEq lhs opndTgt
          | _, _ => false))
  | _, _ => false

noncomputable def isNeutralIdentityStmt (bodyLocals : List MirTy)
    (sSrc sTgt : StatementKind) : Bool :=
  isNeutralIdentityRewrite bodyLocals sSrc sTgt || stmtEq sSrc sTgt

noncomputable def isNeutralIdentityBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (isNeutralIdentityStmt bodyLocals) b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isNeutralIdentityBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isNeutralIdentityBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isNeutralIdentityProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt && listRel isNeutralIdentityBody pSrc.bodies pTgt.bodies

/-! ### Pass 3: `GVN::simplify_binary_inner` Zero-LHS `Div`/`Rem` (`gvn.rs:1511-1518`) -/

noncomputable def isZeroLhsDivRemRewrite (bodyLocals : List MirTy) :
    StatementKind → StatementKind → Bool
  | .assign dst (.binaryOp op (.constant zeroConst) rhs),
      .assign dst' (.use (.constant zeroConst')) =>
    placeEq dst dst' &&
      dst.projection.isEmpty &&
      (binOpEq op .div || binOpEq op .rem) &&
      constOpEq zeroConst zeroConst' &&
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId,
          operandStaticTy? bodyLocals rhs with
      | some (.int w s), some rhsTy =>
        MirTy.beq rhsTy (.int w s) && isIntZeroConst w s zeroConst
      | _, _ => false
  | _, _ => false

noncomputable def isZeroLhsDivRemStmt (bodyLocals : List MirTy)
    (sSrc sTgt : StatementKind) : Bool :=
  isZeroLhsDivRemRewrite bodyLocals sSrc sTgt || stmtEq sSrc sTgt

noncomputable def isZeroLhsDivRemBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (isZeroLhsDivRemStmt bodyLocals) b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isZeroLhsDivRemBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isZeroLhsDivRemBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isZeroLhsDivRemProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt && listRel isZeroLhsDivRemBody pSrc.bodies pTgt.bodies

/-! ### Pass 4: `GVN::simplify_binary_inner` Absorbing & Self-Canceling Rules (`gvn.rs:1501-1540`) -/

/-- Left-absorbing constant `c` (`op(c, rhs) ↦ cOut`) for destination type `dstTy`
(excluding `*Unchecked` shifts!). -/
noncomputable def isLeftAbsorbingFor (dstTy rhsTy : MirTy) (op : BinOp)
    (c cOut : ConstOperand) : Bool :=
  match dstTy with
  | .int w s =>
    match op with
    | .mul | .mulUnchecked | .bitAnd =>
      MirTy.beq rhsTy (.int w s) &&
        isIntZeroConst w s c && isIntZeroConst w s cOut
    | .shl | .shr =>
      (match rhsTy with | .int _ _ => true | _ => false) &&
        isIntZeroConst w s c && isIntZeroConst w s cOut
    | .bitOr =>
      MirTy.beq rhsTy (.int w s) &&
        isIntAllOnesConst w s c && isIntAllOnesConst w s cOut
    | _ => false
  | .bool =>
    MirTy.beq rhsTy .bool &&
      match op with
      | .bitAnd => isFalseBoolConst c && isFalseBoolConst cOut
      | .bitOr => isTrueBoolConst c && isTrueBoolConst cOut
      | _ => false
  | _ => false

/-- Right-absorbing constant `c` (`op(lhs, c) ↦ cOut`) for destination type
`dstTy`, including `Rem(lhs, 1) ↦ 0`. -/
noncomputable def isRightAbsorbingFor (dstTy lhsTy : MirTy) (op : BinOp)
    (c cOut : ConstOperand) : Bool :=
  match dstTy with
  | .int w s =>
    MirTy.beq lhsTy (.int w s) &&
      match op with
      | .mul | .mulUnchecked | .bitAnd =>
        isIntZeroConst w s c && isIntZeroConst w s cOut
      | .rem =>
        isIntOneConst w s c && isIntZeroConst w s cOut
      | .bitOr =>
        isIntAllOnesConst w s c && isIntAllOnesConst w s cOut
      | _ => false
  | .bool =>
    MirTy.beq lhsTy .bool &&
      match op with
      | .bitAnd => isFalseBoolConst c && isFalseBoolConst cOut
      | .bitOr => isTrueBoolConst c && isTrueBoolConst cOut
      | _ => false
  | _ => false

/-- Self-canceling `.copy p` binary operations (`Sub`/`SubUnchecked`/`BitXor`
`↦ 0`, `Eq ↦ true`, `Ne ↦ false`). Restricted strictly to `.copy` (never
`.move`, because `op(move p, move p)` deinitializes `p` on LHS before reading
RHS and unconditionally faults `.undefined`!). -/
noncomputable def isSelfCancelFor (dstTy opndTy : MirTy) (op : BinOp)
    (cOut : ConstOperand) : Bool :=
  match opndTy with
  | .int w s =>
    match op with
    | .sub | .subUnchecked | .bitXor =>
      MirTy.beq dstTy (.int w s) && isIntZeroConst w s cOut
    | .eq => MirTy.beq dstTy .bool && isTrueBoolConst cOut
    | .ne => MirTy.beq dstTy .bool && isFalseBoolConst cOut
    | _ => false
  | .bool =>
    MirTy.beq dstTy .bool &&
      match op with
      | .bitXor | .ne => isFalseBoolConst cOut
      | .eq => isTrueBoolConst cOut
      | _ => false
  | _ => false

noncomputable def isAbsorbingOrSelfCancelRewrite (bodyLocals : List MirTy) :
    StatementKind → StatementKind → Bool
  | .assign dst (.binaryOp op lhs rhs), .assign dst' (.use (.constant cOut)) =>
    placeEq dst dst' &&
      dst.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => false
      | some dstTy =>
        ((match lhs, operandStaticTy? bodyLocals rhs with
          | .constant c, some rhsTy =>
            isLeftAbsorbingFor dstTy rhsTy op c cOut
          | _, _ => false) ||
         (match rhs, operandStaticTy? bodyLocals lhs with
          | .constant c, some lhsTy =>
            isRightAbsorbingFor dstTy lhsTy op c cOut
          | _, _ => false) ||
         (match lhs, rhs with
          | .copy p₁, .copy p₂ =>
            placeEq p₁ p₂ && p₁.projection.isEmpty &&
              match Trusted.MirSemantics.getElem? bodyLocals p₁.localId with
              | some opndTy => isSelfCancelFor dstTy opndTy op cOut
              | none => false
          | _, _ => false))
  | _, _ => false

noncomputable def isAbsorbingOrSelfCancelStmt (bodyLocals : List MirTy)
    (sSrc sTgt : StatementKind) : Bool :=
  isAbsorbingOrSelfCancelRewrite bodyLocals sSrc sTgt || stmtEq sSrc sTgt

noncomputable def isAbsorbingOrSelfCancelBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (isAbsorbingOrSelfCancelStmt bodyLocals) b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isAbsorbingOrSelfCancelBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isAbsorbingOrSelfCancelBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isAbsorbingOrSelfCancelProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isAbsorbingOrSelfCancelBody pSrc.bodies pTgt.bodies

/-! ### Pass 5: Adjacent Double-Unary Involution (`GVN::simplify_unary`, `gvn.rs:1356-1358`) -/

/-- Valid `(op, ty)` combinations for double-unary involution (`Not` on `.bool`
or `.int w s`; `Neg` on signed `.int w true`, including wrapping `INT_MIN`). -/
noncomputable def isValidInvolutiveUnOpTy (op : UnOp) (ty : MirTy) : Bool :=
  match op, ty with
  | .not, .bool => true
  | .not, .int _ _ => true
  | .neg, .int _ true => true
  | _, _ => false

/-- Check whether adjacent source statements `(s₁, s₂)` and target statements
`(t₁, t₂)` form `_t = UnaryOp(op, copy x); _dst = UnaryOp(op, copy _t)`
rewritten to `_t = UnaryOp(op, copy x); _dst = Use(copy x)` with `_t ≠ x` and
matching static types. -/
noncomputable def isDoubleUnaryPair (bodyLocals : List MirTy)
    (s₁ s₂ t₁ t₂ : StatementKind) : Bool :=
  stmtEq s₁ t₁ &&
    match s₁, s₂, t₂ with
    | .assign tmp (.unaryOp op₁ (.copy x)),
      .assign dst (.unaryOp op₂ (.copy tmp')),
      .assign dst' (.use (.copy x')) =>
      unOpEq op₁ op₂ &&
        placeEq tmp tmp' &&
        placeEq dst dst' &&
        placeEq x x' &&
        x.projection.isEmpty &&
        tmp.projection.isEmpty &&
        dst.projection.isEmpty &&
        !Nat.beq tmp.localId x.localId &&
        match Trusted.MirSemantics.getElem? bodyLocals x.localId,
            Trusted.MirSemantics.getElem? bodyLocals tmp.localId,
            Trusted.MirSemantics.getElem? bodyLocals dst.localId with
        | some xTy, some tmpTy, some dstTy =>
          isValidInvolutiveUnOpTy op₁ xTy &&
            MirTy.beq xTy tmpTy &&
            MirTy.beq xTy dstTy
        | _, _, _ => false
    | _, _, _ => false

noncomputable def isDoubleUnaryChainStmts (bodyLocals : List MirTy) :
    List StatementKind → List StatementKind → Bool
  | [], [] => true
  | [s₁], [t₁] => stmtEq s₁ t₁
  | s₁ :: s₂ :: restSrc, t₁ :: t₂ :: restTgt =>
    if isDoubleUnaryPair bodyLocals s₁ s₂ t₁ t₂ then
      isDoubleUnaryChainStmts bodyLocals restSrc restTgt
    else
      stmtEq s₁ t₁ &&
        isDoubleUnaryChainStmts bodyLocals (s₂ :: restSrc) (t₂ :: restTgt)
  | _, _ => false

noncomputable def isDoubleUnaryChainBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    isDoubleUnaryChainStmts bodyLocals b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isDoubleUnaryChainBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isDoubleUnaryChainBlock b₁.locals) b₁.basicBlocks b₂.basicBlocks

noncomputable def isDoubleUnaryChainProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isDoubleUnaryChainBody pSrc.bodies pTgt.bodies

/-! ### Pass 6: Constant `UnaryOp`/`BinaryOp` Folding & Enum `Discriminant` Folding (`gvn.rs:1134-1144`) -/

/-- Re-encode a well-formed primitive `Val` (`.scalar` or `.bool`) back into a
canonical `ConstOperand`. -/
noncomputable def valToConstOperand? : Val → Option ConstOperand
  | .scalar sv =>
    if sv.wf then some ⟨.int sv.width sv.signed, .scalar sv.bits⟩ else none
  | .bool false => some ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩
  | .bool true => some ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩
  | _ => none

/-- Compile-time `UnaryOp` evaluator mirroring `evalPrimitiveOperand` + `evalUnOp`. -/
noncomputable def evalConstUnaryToOperand? (op : UnOp) (c : ConstOperand) :
    Option ConstOperand :=
  if !isPrimitiveReadableTy c.ty then none
  else
    match evalConstLit c.ty c.lit with
    | .error _ => none
    | .ok v =>
      match evalUnOp op v with
      | .error _ => none
      | .ok res => valToConstOperand? res

/-- Compile-time `BinaryOp` evaluator mirroring `evalPrimitiveOperand` + `evalBinOp`. -/
noncomputable def evalConstBinaryToOperand? (op : BinOp)
    (cL cR : ConstOperand) : Option ConstOperand :=
  if !isPrimitiveReadableTy cL.ty || !isPrimitiveReadableTy cR.ty then none
  else
    match evalConstLit cL.ty cL.lit, evalConstLit cR.ty cR.lit with
    | .ok vL, .ok vR =>
      match evalBinOp op vL vR with
      | .ok res => valToConstOperand? res
      | .error _ => none
    | _, _ => none

/-- Construct the declared discriminant `ConstOperand` for variant `vIdx` of an
admitted fieldless enum `ety`. -/
noncomputable def enumVariantDiscrConst? (ety : EnumTy) (vIdx : Nat) :
    Option ConstOperand :=
  if !enumAdmitted ety || !Nat.blt vIdx ety.discriminants.length then none
  else
    match Trusted.MirSemantics.getElem? ety.discriminants vIdx with
    | none => none
    | some disc =>
      some ⟨.int ety.discrWidth ety.discrSigned,
        .scalar (truncateBits ety.discrWidth (BitVec.ofNat 128 disc))⟩

/-- True iff `cOut` equals `enumVariantDiscrConst? ety idx` for some variant of `ety`. -/
noncomputable def hasMatchingVariantAux (ety : EnumTy) (cOut : ConstOperand) :
    Nat → List Nat → Bool
  | _, [] => false
  | idx, _ :: rest =>
    (match enumVariantDiscrConst? ety idx with
     | some cand => constOpEq cand cOut
     | none => false) || hasMatchingVariantAux ety cOut (idx + 1) rest

/-- Pure constant `UnaryOp` or `BinaryOp` fold rewrite. -/
noncomputable def isConstOpFoldRewrite (bodyLocals : List MirTy) :
    StatementKind → StatementKind → Bool
  | .assign dst (.unaryOp op (.constant c)),
      .assign dst' (.use (.constant cOut)) =>
    placeEq dst dst' && dst.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId,
          evalConstUnaryToOperand? op c with
      | some dstTy, some cand =>
        constOpEq cand cOut && MirTy.beq cOut.ty dstTy
      | _, _ => false
  | .assign dst (.binaryOp op (.constant cL) (.constant cR)),
      .assign dst' (.use (.constant cOut)) =>
    placeEq dst dst' && dst.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId,
          evalConstBinaryToOperand? op cL cR with
      | some dstTy, some cand =>
        constOpEq cand cOut && MirTy.beq cOut.ty dstTy
      | _, _ => false
  | _, _ => false

/-- Enum `Discriminant(place) ↦ Use(const discr)` rewrite (`singleOnly = true`
restricts to 1-variant enums for uncertified forward codegen refinement;
`singleOnly = false` admits arbitrary multi-variant enums when paired with
`checkConstAndEnumDiscrFoldProgram`). -/
noncomputable def isEnumDiscrFoldRewrite (singleOnly : Bool)
    (bodyLocals : List MirTy) : StatementKind → StatementKind → Bool
  | .assign dst (.discriminant p), .assign dst' (.use (.constant cOut)) =>
    placeEq dst dst' &&
      dst.projection.isEmpty &&
      p.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId,
          Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | some dstTy, some (.enum ety) =>
        enumAdmitted ety &&
          MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned) &&
          (if singleOnly then
             Nat.beq ety.discriminants.length 1 &&
               match enumVariantDiscrConst? ety 0 with
               | some cand => constOpEq cand cOut
               | none => false
           else
             hasMatchingVariantAux ety cOut 0 ety.discriminants)
      | _, _ => false
  | _, _ => false

noncomputable def isUncondConstAndSingleDiscrFoldStmt (bodyLocals : List MirTy)
    (sSrc sTgt : StatementKind) : Bool :=
  isConstOpFoldRewrite bodyLocals sSrc sTgt ||
    isEnumDiscrFoldRewrite true bodyLocals sSrc sTgt ||
    stmtEq sSrc sTgt

noncomputable def isUncondConstAndSingleDiscrFoldBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (isUncondConstAndSingleDiscrFoldStmt bodyLocals)
      b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isUncondConstAndSingleDiscrFoldBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isUncondConstAndSingleDiscrFoldBlock b₁.locals)
      b₁.basicBlocks b₂.basicBlocks

/-- Uncertified Pass 6 sub-relation (constant `UnaryOp`/`BinaryOp` folding plus
1-variant enum `Discriminant` folding), which is unconditionally forward-sound
for codegen (`Theorem 6a`) yet still requires liveness certification for reverse
VC transport (`ce_enum_discr_dead_zst_unsound`). -/
noncomputable def isUncondConstAndSingleDiscrFoldProgram
    (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isUncondConstAndSingleDiscrFoldBody pSrc.bodies pTgt.bodies

noncomputable def isConstAndEnumDiscrFoldStmt (bodyLocals : List MirTy)
    (sSrc sTgt : StatementKind) : Bool :=
  isConstOpFoldRewrite bodyLocals sSrc sTgt ||
    isEnumDiscrFoldRewrite false bodyLocals sSrc sTgt ||
    stmtEq sSrc sTgt

noncomputable def isConstAndEnumDiscrFoldBlock (bodyLocals : List MirTy)
    (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (isConstAndEnumDiscrFoldStmt bodyLocals)
      b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

noncomputable def isConstAndEnumDiscrFoldBody (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (isConstAndEnumDiscrFoldBlock b₁.locals)
      b₁.basicBlocks b₂.basicBlocks

/-- General Pass 6 relation covering constant `UnaryOp`/`BinaryOp` folding and
arbitrary fieldless-enum `Discriminant` folding (`GVN::simplify_discriminant`). -/
noncomputable def isConstAndEnumDiscrFoldProgram (pSrc pTgt : Program) : Bool :=
  programHeaderEq pSrc pTgt &&
    listRel isConstAndEnumDiscrFoldBody pSrc.bodies pTgt.bodies

/-! ## Part II: Decidable Flow-Sensitive Certificates for Bidirectional VC Transport -/

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

/-! ### Certificate 1 (`checkZeroLhsDivRemProgram`): Non-Zero & Non-Move RHS Certificate -/

/-- 4-point abstract local domain for `ZeroLhsDivRem` certification:
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

abbrev BodyNonZeroCert := List (Option (List NonZeroAbsSlot))
abbrev ProgramNonZeroCert := List BodyNonZeroCert

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

noncomputable def stepNonZeroStmtPair (bodyLocals : List MirTy)
    (env : List NonZeroAbsSlot) (sSrc sTgt : StatementKind) :
    Option (List NonZeroAbsSlot) :=
  if stmtEq sSrc sTgt then
    match sSrc with
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
  else
    match sSrc with
    | .assign dst (.binaryOp _ (.constant _) rhs) =>
      if !isZeroLhsDivRemRewrite bodyLocals sSrc sTgt then none
      else
        match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
        | some (.int w s) =>
          if isCertifiedNonZeroDivisor bodyLocals env w s rhs then
            setElem? env dst.localId .liveInit
          else
            none
        | _ => none
    | _ => none

noncomputable def stepNonZeroStmtsPair (bodyLocals : List MirTy) :
    List NonZeroAbsSlot → List StatementKind → List StatementKind →
    Option (List NonZeroAbsSlot)
  | env, [], [] => some env
  | env, sSrc :: restSrc, sTgt :: restTgt =>
    match stepNonZeroStmtPair bodyLocals env sSrc sTgt with
    | none => none
    | some env' => stepNonZeroStmtsPair bodyLocals env' restSrc restTgt
  | _, _, _ => none

/-- Check whether `branches` contains a valid width-`w` `0` guard with no
preceding overflowing `caseBits` (so falling through to `otherwise` guarantees
`truncateBits w sv.bits != 0`, hence `decodeScalar sv != 0`). -/
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

noncomputable def checkNonZeroEdge (numBlocks : Nat) (cert : BodyNonZeroCert)
    (exitEnv : List NonZeroAbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? cert target with
    | some (some tgtEnv) => nonZeroEnvImplies exitEnv tgtEnv
    | _ => false

noncomputable def checkZeroLhsDivRemBlock (bSrc bTgt : Body)
    (cert : BodyNonZeroCert) (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      match stepNonZeroStmtsPair bSrc.locals entryEnv
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

noncomputable def checkZeroLhsDivRemBlocksLoop (bSrc bTgt : Body)
    (cert : BodyNonZeroCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkZeroLhsDivRemBlock bSrc bTgt cert idx bbSrc &&
      checkZeroLhsDivRemBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkZeroLhsDivRemBody (cert : BodyNonZeroCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         nonZeroEnvImplies (initNonZeroEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkZeroLhsDivRemBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkZeroLhsDivRemProgram (cert : ProgramNonZeroCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkZeroLhsDivRemBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Certificate 2 (`checkAbsorbingOrSelfCancelProgram`): 3-Point Initialization & Non-Move Certificate -/

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

/-- Check that an operand eliminated by an absorbing or self-canceling fold is
a non-`move`, fault-free primitive read (`.constant` with valid `evalConstLit`,
or `.copy` of an unprojected `.liveInit` primitive-readable local). -/
noncomputable def operandCertifiedLivePrimitiveRead (bodyLocals : List MirTy)
    (env : List AbsSlot) : Operand → Bool
  | .constant c =>
    isPrimitiveReadableTy c.ty &&
      match evalConstLit c.ty c.lit with
      | .ok _ => true
      | .error _ => false
  | .copy p =>
    p.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some ty, some .liveInit => isPrimitiveReadableTy ty
      | _, _ => false
  | .move _ => false

noncomputable def stepAbsorbStmtPair (bodyLocals : List MirTy)
    (env : List AbsSlot) (sSrc sTgt : StatementKind) : Option (List AbsSlot) :=
  if stmtEq sSrc sTgt then
    match sSrc with
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
  else
    match sSrc with
    | .assign dst (.binaryOp _ lhs rhs) =>
      if !isAbsorbingOrSelfCancelRewrite bodyLocals sSrc sTgt then none
      else if operandCertifiedLivePrimitiveRead bodyLocals env lhs &&
          operandCertifiedLivePrimitiveRead bodyLocals env rhs then
        setElem? env dst.localId .liveInit
      else
        none
    | _ => none

noncomputable def stepAbsorbStmtsPair (bodyLocals : List MirTy) :
    List AbsSlot → List StatementKind → List StatementKind →
    Option (List AbsSlot)
  | env, [], [] => some env
  | env, sSrc :: restSrc, sTgt :: restTgt =>
    match stepAbsorbStmtPair bodyLocals env sSrc sTgt with
    | none => none
    | some env' => stepAbsorbStmtsPair bodyLocals env' restSrc restTgt
  | _, _, _ => none

noncomputable def checkAbsEdge (numBlocks : Nat) (cert : BodyAbsCert)
    (exitEnv : List AbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? cert target with
    | some (some tgtEnv) => absEnvImplies exitEnv tgtEnv
    | _ => false

noncomputable def checkAbsorbingBlock (bSrc bTgt : Body) (cert : BodyAbsCert)
    (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      match stepAbsorbStmtsPair bSrc.locals entryEnv
          bbSrc.statements bbTgt.statements with
      | none => false
      | some exitEnv =>
        let numBlocks := bSrc.basicBlocks.length
        match bbSrc.terminator with
        | .goto target => checkAbsEdge numBlocks cert exitEnv target
        | .switchInt discr targets =>
          let afterDiscrEnv := deinitMoveOperandAbs bSrc.locals exitEnv discr
          checkAbsEdge numBlocks cert afterDiscrEnv targets.otherwise &&
            targets.branches.all (fun br =>
              checkAbsEdge numBlocks cert afterDiscrEnv br.2)
        | _ => true

noncomputable def checkAbsorbingBlocksLoop (bSrc bTgt : Body)
    (cert : BodyAbsCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkAbsorbingBlock bSrc bTgt cert idx bbSrc &&
      checkAbsorbingBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkAbsorbingOrSelfCancelBody (cert : BodyAbsCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         absEnvImplies (initAbsEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkAbsorbingBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkAbsorbingOrSelfCancelProgram (cert : ProgramAbsCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkAbsorbingOrSelfCancelBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

/-! ### Certificate 3 (`checkConstAndEnumDiscrFoldProgram`): Enum-Variant & Liveness Certificate -/

/-- Abstract local domain tracking live liveness and known fieldless-enum
variant indices (`knownEnum ety vIdx ⊑ liveSlot ⊑ dead`). -/
inductive DiscrAbsSlot where
  | knownEnum (ety : EnumTy) (variant : Nat)
  | liveSlot
  | dead

noncomputable def discrSlotImplies : DiscrAbsSlot → DiscrAbsSlot → Bool
  | _, .dead => true
  | .knownEnum _ _, .liveSlot | .liveSlot, .liveSlot => true
  | .knownEnum e₁ v₁, .knownEnum e₂ v₂ =>
    EnumTy.beq e₁ e₂ && Nat.beq v₁ v₂
  | _, _ => false

noncomputable def discrEnvImplies :
    List DiscrAbsSlot → List DiscrAbsSlot → Bool :=
  listRel discrSlotImplies

abbrev BodyDiscrCert := List (Option (List DiscrAbsSlot))
abbrev ProgramDiscrCert := List BodyDiscrCert

noncomputable def initDiscrSlot (body : Body) (idx : Nat) : DiscrAbsSlot :=
  if Nat.beq idx 0 then
    .liveSlot
  else if Nat.ble idx body.argumentCount then
    .liveSlot
  else if hasStorageAnnotation body idx then
    .dead
  else
    .liveSlot

noncomputable def initDiscrEnvLoop (body : Body) :
    Nat → List MirTy → List DiscrAbsSlot
  | _, [] => []
  | idx, _ :: rest =>
    initDiscrSlot body idx :: initDiscrEnvLoop body (idx + 1) rest

noncomputable def deinitMoveOperandDiscr (bodyLocals : List MirTy)
    (env : List DiscrAbsSlot) : Operand → List DiscrAbsSlot
  | .move p =>
    if !p.projection.isEmpty then env
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => env
      | some (.enum ety) =>
        let nextSlot :=
          if isZstEnumTy ety then .knownEnum ety 0 else .liveSlot
        match setElem? env p.localId nextSlot with
        | some env' => env'
        | none => env
      | some _ =>
        match setElem? env p.localId .liveSlot with
        | some env' => env'
        | none => env
  | _ => env

noncomputable def deinitMovesInRvalueDiscr (bodyLocals : List MirTy)
    (env : List DiscrAbsSlot) : Rvalue → List DiscrAbsSlot
  | .use opnd | .unaryOp _ opnd => deinitMoveOperandDiscr bodyLocals env opnd
  | .binaryOp _ lhs rhs =>
    let env₁ := deinitMoveOperandDiscr bodyLocals env lhs
    deinitMoveOperandDiscr bodyLocals env₁ rhs
  | _ => env

noncomputable def rvalueKnownEnumSlot (bodyLocals : List MirTy)
    (env : List DiscrAbsSlot) (dstTy : MirTy) : Rvalue → DiscrAbsSlot
  | .use (.constant c) =>
    match dstTy with
    | .enum ety =>
      if !MirTy.beq c.ty (.enum ety) then .liveSlot
      else
        match evalConstLit (.enum ety) c.lit with
        | .ok (.enumVal etyRes vIdx) => .knownEnum etyRes vIdx
        | _ => .liveSlot
    | _ => .liveSlot
  | .use (.copy p) | .use (.move p) =>
    if !p.projection.isEmpty then .liveSlot
    else
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some srcTy, some (.knownEnum ety vIdx) =>
        if MirTy.beq srcTy dstTy && MirTy.beq dstTy (.enum ety) then
          .knownEnum ety vIdx
        else
          .liveSlot
      | _, _ => .liveSlot
  | _ => .liveSlot

noncomputable def stepDiscrStmtPair (bodyLocals : List MirTy)
    (env : List DiscrAbsSlot) (sSrc sTgt : StatementKind) :
    Option (List DiscrAbsSlot) :=
  if stmtEq sSrc sTgt then
    match sSrc with
    | .nop | .unsupported => some env
    | .storageLive id =>
      match Trusted.MirSemantics.getElem? bodyLocals id with
      | none => none
      | some (.enum ety) =>
        let nextSlot :=
          if isZstEnumTy ety then .knownEnum ety 0 else .liveSlot
        setElem? env id nextSlot
      | some _ => setElem? env id .liveSlot
    | .storageDead id =>
      if Nat.beq id 0 then none else setElem? env id .dead
    | .assign dst rv =>
      if !dst.projection.isEmpty then none
      else
        match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
        | none => none
        | some dstTy =>
          let dstSlot := rvalueKnownEnumSlot bodyLocals env dstTy rv
          let env₁ := deinitMovesInRvalueDiscr bodyLocals env rv
          setElem? env₁ dst.localId dstSlot
  else if isConstOpFoldRewrite bodyLocals sSrc sTgt then
    match sSrc with
    | .assign dst _ => setElem? env dst.localId .liveSlot
    | _ => none
  else if isEnumDiscrFoldRewrite false bodyLocals sSrc sTgt then
    match sSrc, sTgt with
    | .assign dst (.discriminant p), .assign _ (.use (.constant cOut)) =>
      match Trusted.MirSemantics.getElem? bodyLocals p.localId,
          Trusted.MirSemantics.getElem? env p.localId with
      | some (.enum ety), some slot =>
        let certifiedOk :=
          if isZstEnumTy ety then
            discrSlotImplies slot .liveSlot &&
              match enumVariantDiscrConst? ety 0 with
              | some cand => constOpEq cand cOut
              | none => false
          else
            match slot with
            | .knownEnum etyKnown vIdx =>
              EnumTy.beq ety etyKnown &&
                match enumVariantDiscrConst? ety vIdx with
                | some cand => constOpEq cand cOut
                | none => false
            | _ => false
        if certifiedOk then setElem? env dst.localId .liveSlot else none
      | _, _ => none
    | _, _ => none
  else
    none

noncomputable def stepDiscrStmtsPair (bodyLocals : List MirTy) :
    List DiscrAbsSlot → List StatementKind → List StatementKind →
    Option (List DiscrAbsSlot)
  | env, [], [] => some env
  | env, sSrc :: restSrc, sTgt :: restTgt =>
    match stepDiscrStmtPair bodyLocals env sSrc sTgt with
    | none => none
    | some env' => stepDiscrStmtsPair bodyLocals env' restSrc restTgt
  | _, _, _ => none

noncomputable def checkDiscrEdge (numBlocks : Nat) (cert : BodyDiscrCert)
    (exitEnv : List DiscrAbsSlot) (target : BasicBlockId) : Bool :=
  if !Nat.blt target numBlocks then
    true
  else
    match Trusted.MirSemantics.getElem? cert target with
    | some (some tgtEnv) => discrEnvImplies exitEnv tgtEnv
    | _ => false

noncomputable def checkDiscrBlock (bSrc bTgt : Body) (cert : BodyDiscrCert)
    (bbIdx : Nat) (bbSrc : BasicBlock) : Bool :=
  match Trusted.MirSemantics.getElem? cert bbIdx,
      Trusted.MirSemantics.getElem? bTgt.basicBlocks bbIdx with
  | _, none => false
  | none, _ => false
  | some none, some _ => true
  | some (some entryEnv), some bbTgt =>
    Nat.beq entryEnv.length bSrc.locals.length &&
      match stepDiscrStmtsPair bSrc.locals entryEnv
          bbSrc.statements bbTgt.statements with
      | none => false
      | some exitEnv =>
        let numBlocks := bSrc.basicBlocks.length
        match bbSrc.terminator with
        | .goto target => checkDiscrEdge numBlocks cert exitEnv target
        | .switchInt discr targets =>
          let afterDiscrEnv := deinitMoveOperandDiscr bSrc.locals exitEnv discr
          checkDiscrEdge numBlocks cert afterDiscrEnv targets.otherwise &&
            targets.branches.all (fun br =>
              checkDiscrEdge numBlocks cert afterDiscrEnv br.2)
        | _ => true

noncomputable def checkDiscrBlocksLoop (bSrc bTgt : Body)
    (cert : BodyDiscrCert) : Nat → List BasicBlock → Bool
  | _, [] => true
  | idx, bbSrc :: rest =>
    checkDiscrBlock bSrc bTgt cert idx bbSrc &&
      checkDiscrBlocksLoop bSrc bTgt cert (idx + 1) rest

noncomputable def checkConstAndEnumDiscrFoldBody (cert : BodyDiscrCert)
    (bSrc bTgt : Body) : Bool :=
  preservesAllStorageAnnotations bSrc bTgt &&
    Nat.beq cert.length bSrc.basicBlocks.length &&
    (if bSrc.basicBlocks.isEmpty then true
     else
       match Trusted.MirSemantics.getElem? cert 0 with
       | some (some env₀) =>
         discrEnvImplies (initDiscrEnvLoop bSrc 0 bSrc.locals) env₀
       | _ => false) &&
    checkDiscrBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks

noncomputable def checkConstAndEnumDiscrFoldProgram (cert : ProgramDiscrCert)
    (pSrc pTgt : Program) : Bool :=
  Nat.beq cert.length pSrc.bodies.length &&
    listRel (fun cPr bTgt => checkConstAndEnumDiscrFoldBody cPr.1 cPr.2 bTgt)
      (List.zip cert pSrc.bodies) pTgt.bodies

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

/-! ### Stage 4 Private Helpers — Layer B: Deterministic Simulation & Lifting -/

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
Refinement, & Generic Pass Lifters -/

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

private theorem scalarWf_truncateBits (w : IntWidth) (s : Bool) (x : BitVec 128) :
    ScalarVal.wf ⟨w, s, truncateBits w x⟩ = true := by
  unfold ScalarVal.wf
  dsimp only
  rw [truncateBits_idem]
  exact beq_self_eq_true (truncateBits w x)

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
    LocalsWellTyped bodyLocals locals' ∧
    (∀ ty, operandStaticTy? bodyLocals op = some ty → checkVal v ty = true) := by
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
      | some v0 =>
        injection hEv with hEq
        injection hEq with hv hl; subst hv; subst hl
        let ⟨hWt1, hChk0⟩ := evalOperandToSlot_preserves_wt hWt hS
        refine ⟨hWt1, ?_⟩
        intro ty hStTy
        have hTyEq : ty0 = ty := by
          cases op with
          | constant c =>
            dsimp [operandStaticTy?] at hStTy
            injection hStTy with hCEq; subst hCEq
            dsimp [evalOperandToSlot] at hS
            cases hCL : evalConstLit c.ty c.lit with
            | error _ => rw [hCL] at hS; cases hS
            | ok _ =>
              rw [hCL] at hS; injection hS with h1; injection h1 with h2 _; exact h2.symm
          | copy p | move p =>
            dsimp [operandStaticTy?] at hStTy
            cases hP : p.projection.isEmpty with
            | false => rw [hP] at hStTy; cases hStTy
            | true =>
              rw [hP] at hStTy; dsimp at hStTy
              dsimp [evalOperandToSlot] at hS
              rw [hP] at hS; dsimp at hS
              rw [hStTy] at hS
              cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
              | none => rw [hSl] at hS; cases hS
              | some sl =>
                rw [hSl] at hS
                cases sl with
                | dead => cases hS
                | live _ =>
                  first
                  | (injection hS with h1; injection h1 with h2 _; exact h2.symm)
                  | (dsimp at hS;
                     cases hSet : setElem? locals p.localId (liveUninitSlot ty) with
                     | none => rw [hSet] at hS; cases hS
                     | some _ =>
                       rw [hSet] at hS; injection hS with h1; injection h1 with h2 _; exact h2.symm)
        subst hTyEq
        exact hChk0 v0 rfl

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
          have hWt1 := (evalPrimitiveOperand_preserves_wt hWt hL).1
          exact (evalPrimitiveOperand_preserves_wt hWt1 hR).1
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
        exact (evalPrimitiveOperand_preserves_wt hWt hO).1
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
      have hWtAfter := (evalPrimitiveOperand_preserves_wt hWt hD).1
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

private theorem evalTerminator_eq_of_eq {b₁ b₂ : Body} {bb₁ bb₂ : BasicBlock}
    {frame : FrameState} {cm : CallerMemory}
    (hLocs : b₁.locals = b₂.locals)
    (hClean : bb₁.cleanup = bb₂.cleanup)
    (hTerm : bb₁.terminator = bb₂.terminator) :
    evalTerminator b₁ bb₁ frame cm = evalTerminator b₂ bb₂ frame cm := by
  unfold evalTerminator
  rw [hTerm, hLocs, hClean]

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
      LocalsFwdRefines bodyLocals localsSrc' localsTgt' ∧
      (∀ ty, operandStaticTy? bodyLocals op = some ty → checkVal v ty = true) := by
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
        let ⟨locs2, hT, hInv', hChk0⟩ := evalOperandToSlot_fwd_eq hInv hS
        refine ⟨locs2, ?_, hInv', ?_⟩
        · dsimp [evalPrimitiveOperand]; rw [hT]; dsimp; rw [hPrim]; rfl
        · intro ty hStTy
          have hTyEq : ty0 = ty := by
            cases op with
            | constant c =>
              dsimp [operandStaticTy?] at hStTy; injection hStTy with hc; subst hc
              dsimp [evalOperandToSlot] at hT
              cases hCL : evalConstLit c.ty c.lit with
              | error _ => rw [hCL] at hT; cases hT
              | ok _ => rw [hCL] at hT; injection hT with h1; injection h1 with h2 _; exact h2.symm
            | copy p | move p =>
              dsimp [operandStaticTy?] at hStTy
              cases hP : p.projection.isEmpty with
              | false => rw [hP] at hStTy; cases hStTy
              | true =>
                rw [hP] at hStTy; dsimp at hStTy
                dsimp [evalOperandToSlot] at hT
                rw [hP, hStTy] at hT; dsimp at hT
                cases hSl2 : Trusted.MirSemantics.getElem? localsTgt p.localId with
                | none => rw [hSl2] at hT; cases hT
                | some sl2 =>
                  rw [hSl2] at hT
                  cases sl2 with
                  | dead => cases hT
                  | live _ =>
                    first
                    | (injection hT with h1; injection h1 with h2 _; exact h2.symm)
                    | (dsimp at hT;
                       cases hSet : setElem? localsTgt p.localId (liveUninitSlot ty) with
                       | none => rw [hSet] at hT; cases hT
                       | some _ => rw [hSet] at hT; injection hT with h1; injection h1 with h2 _; exact h2.symm)
          subst hTyEq
          exact hChk0

private theorem evalPrimitiveOperand_discarded_fwd
    {bodyLocals : List MirTy} {localsSrc localsTgt localsSrc' : List LocalSlot}
    {op : Operand} {dv : Val}
    (hInv : LocalsFwdRefines bodyLocals localsSrc localsTgt)
    (hEval : evalPrimitiveOperand bodyLocals localsSrc op = .ok (dv, localsSrc')) :
    LocalsFwdRefines bodyLocals localsSrc' localsTgt ∧
    (∀ ty, operandStaticTy? bodyLocals op = some ty → checkVal dv ty = true) := by
  let ⟨_, hLen2, hAll⟩ := hInv
  let ⟨_, _, _, hChk⟩ := evalPrimitiveOperand_fwd_eq hInv hEval
  refine ⟨?_, hChk⟩
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
        cases op with
        | constant c =>
          dsimp [evalOperandToSlot] at hS
          cases hC : evalConstLit c.ty c.lit with
          | error _ => rw [hC] at hS; cases hS
          | ok _ =>
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
                | live _ =>
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
                | live _ =>
                  dsimp at hS
                  cases hSet1 : setElem? localsSrc p.localId (liveUninitSlot t) with
                  | none => rw [hSet1] at hS; cases hS
                  | some _ =>
                    rw [hSet1] at hS; injection hS with hEq2
                    injection hEq2 with hTyEq hR2; injection hR2 with hOptEq hLEq
                    subst hTyEq; subst hOptEq; subst hLEq
                    let ⟨sl2, hG2⟩ := getElem?_some_of_lt localsTgt p.localId
                      (by rw [hLen2]; exact getElem?_some_lt hTy)
                    let ⟨hRef, hWt2⟩ := hAll p.localId _ _ sl2 hTy hG1 hG2
                    cases sl2 with
                    | dead => cases hRef
                    | live _ =>
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
          let ⟨tLocs1, hTL, hInv1, _⟩ := evalPrimitiveOperand_fwd_eq hInv hEL
          let ⟨tLocs2, hTR, hInv2, _⟩ := evalPrimitiveOperand_fwd_eq hInv1 hER
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
        let ⟨tLocs1, hTO, hInv1, _⟩ := evalPrimitiveOperand_fwd_eq hInv hEO
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
        let ⟨locs2, hD2, hInv1, _⟩ := evalPrimitiveOperand_fwd_eq hInv hD
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

/-! #### Generic Statement-Wise Program Lifting (`genericProgRel`) -/

private noncomputable def stmtStorageInBounds (numLocals : Nat) (stmt : StatementKind) : Bool :=
  match stmt with
  | .storageLive id | .storageDead id => Nat.blt id numLocals
  | _ => true

private noncomputable def genericBlockRel (stmtRel : List MirTy → StatementKind → StatementKind → Bool)
    (bodyLocals : List MirTy) (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel (stmtRel bodyLocals) b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

private noncomputable def genericBodyRel (stmtRel : List MirTy → StatementKind → StatementKind → Bool)
    (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ &&
    listRel (genericBlockRel stmtRel b₁.locals) b₁.basicBlocks b₂.basicBlocks

private noncomputable def genericProgRel (stmtRel : List MirTy → StatementKind → StatementKind → Bool)
    (p₁ p₂ : Program) : Bool :=
  programHeaderEq p₁ p₂ &&
    listRel (genericBodyRel stmtRel) p₁.bodies p₂.bodies

private theorem genericBodyRel_storage_eq
    {stmtRel : List MirTy → StatementKind → StatementKind → Bool}
    (hAssignOnly : ∀ locs s₁ s₂, stmtRel locs s₁ s₂ = true →
      s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂))
    {b₁ b₂ : Body} (hBody : genericBodyRel stmtRel b₁ b₂ = true) :
    bodyHeaderEq b₁ b₂ = true ∧
    b₁.basicBlocks.length = b₂.basicBlocks.length ∧
    b₁.basicBlocks.isEmpty = b₂.basicBlocks.isEmpty ∧
    (∀ idx, hasStorageAnnotation b₁ idx = hasStorageAnnotation b₂ idx) ∧
    storageAnnotationsInBounds b₁ = storageAnnotationsInBounds b₂ ∧
    (∀ args, initLocalsLoop b₁ args 0 b₁.locals = initLocalsLoop b₂ args 0 b₂.locals) := by
  let ⟨hBHdr, hBBs⟩ := bool_and_true hBody
  let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  have hBBLen := listRel_length hBBs
  have hBBEmpty := list_isEmpty_eq_of_length hBBLen
  have hMarker : ∀ idx, hasStorageAnnotation b₁ idx = hasStorageAnnotation b₂ idx := by
    intro idx
    unfold hasStorageAnnotation
    apply list_any_eq_of_rel hBBs
    intro bb₁ bb₂ hBB
    let ⟨h12, _⟩ := bool_and_true hBB
    let ⟨_, hStmts⟩ := bool_and_true h12
    apply list_any_eq_of_rel hStmts
    intro s₁ s₂ hS
    cases hAssignOnly b₁.locals s₁ s₂ hS with
    | inl hEq => rw [hEq]
    | inr hAsg =>
      let ⟨d₁, rv₁, d₂, rv₂, hs₁, hs₂⟩ := hAsg
      rw [hs₁, hs₂]; rfl
  have hBounds : storageAnnotationsInBounds b₁ = storageAnnotationsInBounds b₂ := by
    unfold storageAnnotationsInBounds
    dsimp only
    rw [← hLoc]
    apply list_all_eq_of_rel hBBs
    intro bb₁ bb₂ hBB
    let ⟨h12, _⟩ := bool_and_true hBB
    let ⟨_, hStmts⟩ := bool_and_true h12
    apply list_all_eq_of_rel hStmts
    intro s₁ s₂ hS
    cases hAssignOnly b₁.locals s₁ s₂ hS with
    | inl hEq => rw [hEq]
    | inr hAsg =>
      let ⟨d₁, rv₁, d₂, rv₂, hs₁, hs₂⟩ := hAsg
      rw [hs₁, hs₂]
  exact ⟨hBHdr, hBBLen, hBBEmpty, hMarker, hBounds,
         fun args => initLocalsLoop_eq_of_storage_eq args hArg hLoc (fun idx _ _ => hMarker idx)⟩

private theorem genericProgRel_initState_eq
    {stmtRel : List MirTy → StatementKind → StatementKind → Bool}
    (hAssignOnly : ∀ locs s₁ s₂, stmtRel locs s₁ s₂ = true →
      s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂))
    {p₁ p₂ : Program} (hProg : genericProgRel stmtRel p₁ p₂ = true) (q : Query) :
    initState p₁ q = initState p₂ q := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hProg
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff p₁.entryDefId hBodies
  · intro b₁ hB₁
    let ⟨b₂, hB₂, hBRel⟩ := listRel_getElem?_left hBodies hB₁
    rw [hEnt] at hB₂
    let ⟨hBHdr, _, hBBEmpty, _, hBounds, hInitLoop⟩ :=
      genericBodyRel_storage_eq hAssignOnly hBRel
    exact ⟨b₂, hB₂, hBHdr, hBBEmpty, hBounds, hInitLoop q.args⟩

private theorem genericProgRel_entryProg
    {stmtRel : List MirTy → StatementKind → StatementKind → Bool}
    {p₁ p₂ : Program} (defId : DefId)
    (hProg : genericProgRel stmtRel p₁ p₂ = true) :
    genericProgRel stmtRel (entryProgForBody p₁ defId) (entryProgForBody p₂ defId) = true := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hProg
  exact bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies

private theorem genericProgRel_query_lockstep
    {stmtRel : List MirTy → StatementKind → StatementKind → Bool}
    (hAssignOnly : ∀ locs s₁ s₂, stmtRel locs s₁ s₂ = true →
      s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂))
    (hStmtStep : ∀ b₁ b₂ frame cm s₁ s₂,
      b₁.locals = b₂.locals →
      LocalsWellTyped b₁.locals frame.locals →
      stmtRel b₁.locals s₁ s₂ = true →
      evalStatement b₁ frame cm s₁ = evalStatement b₂ frame cm s₂)
    {pSrc pTgt : Program} (hProg : genericProgRel stmtRel pSrc pTgt = true) (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodies⟩ := bool_and_true hProg
  apply lockstep_inv_query_iff
    (Inv := fun s =>
      ∃ frame bSrc,
        s.frames = [frame] ∧
        Trusted.MirSemantics.getElem? pSrc.bodies frame.defId = some bSrc ∧
        LocalsWellTyped bSrc.locals frame.locals)
    (genericProgRel_initState_eq hAssignOnly hProg q)
  · intro s₀ hOk
    let ⟨_, _, body, hBody, _, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    exact ⟨_, body, rfl, hBody, initLocalsLoop_wellTyped hArgs⟩
  · intro s hInv
    let ⟨frame, bSrc, hFrames, hBSrc, hWt⟩ := hInv
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodies hBSrc
    let ⟨hBHdr, hBBs⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    have hEvEq : evalStep pSrc 0 s = evalStep pTgt 0 s := by
      cases s with
      | mk fs cm =>
        dsimp at hFrames; subst hFrames
        unfold evalStep; dsimp
        rw [hBSrc, hBTgt]; dsimp
        cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
        | none =>
          rw [(listRel_getElem?_none_iff frame.blockIdx hBBs).mp hBBSrc]
        | some bbSrc =>
          let ⟨bbTgt, hBBTgt, hBBRel⟩ := listRel_getElem?_left hBBs hBBSrc
          rw [hBBTgt]; dsimp
          let ⟨h12, hTermRel⟩ := bool_and_true hBBRel
          let ⟨hCleanEq, hStmtsRel⟩ := bool_and_true h12
          cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements frame.stmtIdx with
          | some sSrc =>
            let ⟨sTgt, hStTgt, hSRel⟩ := listRel_getElem?_left hStmtsRel hStSrc
            rw [hStTgt]; dsimp
            exact hStmtStep bSrc bTgt frame cm sSrc sTgt hLocEq hWt hSRel
          | none =>
            rw [(listRel_getElem?_none_iff frame.stmtIdx hStmtsRel).mp hStSrc]; dsimp
            rw [listRel_length hStmtsRel]
            cases Nat.beq frame.stmtIdx bbTgt.statements.length with
            | false => rfl
            | true =>
              rw [if_bool_true rfl, if_bool_true rfl]
              exact evalTerminator_eq_of_eq hLocEq (bool_beq_eq hCleanEq) (terminatorEq_eq hTermRel)
    refine ⟨hEvEq, ?_⟩
    intro s' hStepS
    cases s with
    | mk fs cm =>
      dsimp at hFrames; subst hFrames
      unfold evalStep at hStepS; dsimp at hStepS
      rw [hBSrc] at hStepS; dsimp at hStepS
      cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
      | none => rw [hBBSrc] at hStepS; cases hStepS
      | some bbSrc =>
        rw [hBBSrc] at hStepS; dsimp at hStepS
        cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements frame.stmtIdx with
        | some sSrc =>
          rw [hStSrc] at hStepS; dsimp at hStepS
          let ⟨locs', hEqS', hWt'⟩ := evalStatement_preserves_wt hWt hStepS
          subst hEqS'
          exact ⟨_, bSrc, rfl, hBSrc, hWt'⟩
        | none =>
          rw [hStSrc] at hStepS; dsimp at hStepS
          cases hEnd : Nat.beq frame.stmtIdx bbSrc.statements.length with
          | false => rw [hEnd] at hStepS; cases hStepS
          | true =>
            rw [hEnd] at hStepS; dsimp at hStepS
            let ⟨tgt, locs', hEqS', hWt'⟩ := evalTerminator_preserves_wt hWt hStepS
            subst hEqS'
            exact ⟨_, bSrc, rfl, hBSrc, hWt'⟩

private theorem fullSemanticEquiv_of_stmtRel_lockstep
    {stmtRel : List MirTy → StatementKind → StatementKind → Bool}
    (hAssignOnly : ∀ locs s₁ s₂, stmtRel locs s₁ s₂ = true →
      s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂))
    (hStmtStep : ∀ b₁ b₂ frame cm s₁ s₂,
      b₁.locals = b₂.locals →
      LocalsWellTyped b₁.locals frame.locals →
      stmtRel b₁.locals s₁ s₂ = true →
      evalStatement b₁ frame cm s₁ = evalStatement b₂ frame cm s₂)
    {pSrc pTgt : Program} (hProg : genericProgRel stmtRel pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hProg
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hBHdr, _, hBBEmpty, _, hBounds, _⟩ := genericBodyRel_storage_eq hAssignOnly hBRel
    exact ⟨hBHdr, hBBEmpty, hBounds⟩
  · intro q
    exact genericProgRel_query_lockstep hAssignOnly hStmtStep hProg q
  · intro defId args
    exact (genericProgRel_query_lockstep hAssignOnly hStmtStep
      (genericProgRel_entryProg defId hProg) { args := args }).1

private theorem genericProgRel_query_fwd
    {stmtRel : List MirTy → StatementKind → StatementKind → Bool}
    (hAssignOnly : ∀ locs s₁ s₂, stmtRel locs s₁ s₂ = true →
      s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂))
    (hStmtFwd : ∀ b₁ b₂ f₁ f₂ cm s₁ s₂ s',
      b₁.locals = b₂.locals →
      LocalsFwdRefines b₁.locals f₁.locals f₂.locals →
      stmtRel b₁.locals s₁ s₂ = true →
      evalStatement b₁ f₁ cm s₁ = .step s' →
      ∃ locs1' locs2',
        s' = { frames := [{ f₁ with stmtIdx := f₁.stmtIdx + 1, locals := locs1' }],
               callerMem := cm } ∧
        evalStatement b₂ f₂ cm s₂ =
          .step { frames := [{ f₂ with stmtIdx := f₂.stmtIdx + 1, locals := locs2' }],
                  callerMem := cm } ∧
        LocalsFwdRefines b₁.locals locs1' locs2')
    {pSrc pTgt : Program} (hProg : genericProgRel stmtRel pSrc pTgt = true)
    (q : Query) (hWfSrc : WellFormed pSrc q) :
    WellFormed pTgt q ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodies⟩ := bool_and_true hProg
  apply fwd_sim_lift
    (R := fun s t =>
      ∃ fSrc fTgt bSrc,
        s.frames = [fSrc] ∧
        t.frames = [fTgt] ∧
        s.callerMem = t.callerMem ∧
        fSrc.defId = fTgt.defId ∧
        fSrc.blockIdx = fTgt.blockIdx ∧
        fSrc.stmtIdx = fTgt.stmtIdx ∧
        Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
        LocalsFwdRefines bSrc.locals fSrc.locals fTgt.locals)
    ?_ ?_ hWfSrc
  · intro s₀ hInitSrc
    have hInitTgt : initState pTgt q = .ok s₀ := by
      rw [← genericProgRel_initState_eq hAssignOnly hProg q]; exact hInitSrc
    let ⟨_, _, body, hBody, _, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hInitSrc
    subst hEqS
    exact ⟨_, hInitTgt, _, _, body, rfl, rfl, rfl, rfl, rfl, rfl, hBody,
           localsFwdRefines_refl_of_wt (initLocalsLoop_wellTyped hArgs)⟩
  · intro s t hRel
    let ⟨fSrc, fTgt, bSrc, hFS, hFT, hCM, hDefEq, hBlkEq, hStIdxEq, hBSrc, hInv⟩ := hRel
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodies hBSrc
    let ⟨hBHdr, hBBs⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    cases s with
    | mk fsS cmS =>
      cases t with
      | mk fsT cmT =>
        dsimp at hFS hFT hCM
        subst hFS; subst hFT; subst hCM
        refine ⟨?_, ?_⟩
        · intro s' hEvS
          unfold evalStep at hEvS; dsimp at hEvS
          rw [hBSrc] at hEvS; dsimp at hEvS
          cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
          | none => rw [hBBSrc] at hEvS; cases hEvS
          | some bbSrc =>
            rw [hBBSrc] at hEvS; dsimp at hEvS
            let ⟨bbTgt, hBBTgt, hBBRel⟩ := listRel_getElem?_left hBBs hBBSrc
            let ⟨h12, hTermRel⟩ := bool_and_true hBBRel
            let ⟨hCleanEq, hStmtsRel⟩ := bool_and_true h12
            cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
            | some sSrc =>
              rw [hStSrc] at hEvS; dsimp at hEvS
              let ⟨sTgt, hStTgt, hSRel⟩ := listRel_getElem?_left hStmtsRel hStSrc
              let ⟨locs1', locs2', hEqS', hEvT, hInv'⟩ :=
                hStmtFwd bSrc bTgt fSrc fTgt cmS sSrc sTgt s' hLocEq hInv hSRel hEvS
              subst hEqS'
              refine ⟨{ frames := [{ fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' }], callerMem := cmS },
                ?_,
                { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locs1' },
                { fTgt with stmtIdx := fTgt.stmtIdx + 1, locals := locs2' },
                bSrc, rfl, rfl, rfl, hDefEq, hBlkEq,
                by dsimp; rw [hStIdxEq], hBSrc, hInv'⟩
              unfold evalStep; dsimp
              have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                rw [← hDefEq]; exact hBTgt
              have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                rw [← hBlkEq]; exact hBBTgt
              have hStTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = some sTgt := by
                rw [← hStIdxEq]; exact hStTgt
              rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp; rw [hStTgt2]; dsimp
              exact hEvT
            | none =>
              rw [hStSrc] at hEvS; dsimp at hEvS
              cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
              | false => rw [hEnd] at hEvS; cases hEvS
              | true =>
                rw [hEnd] at hEvS; dsimp at hEvS
                let ⟨tgt, locs1', locs2', hEqS', hEvT, hInv'⟩ :=
                  (evalTerminator_fwd_eq hLocEq (bool_beq_eq hCleanEq)
                    (terminatorEq_eq hTermRel) hInv).1 s' hEvS
                subst hEqS'
                refine ⟨{ frames := [{ fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' }], callerMem := cmS },
                  ?_,
                  { fSrc with blockIdx := tgt, stmtIdx := 0, locals := locs1' },
                  { fTgt with blockIdx := tgt, stmtIdx := 0, locals := locs2' },
                  bSrc, rfl, rfl, rfl, hDefEq, rfl, rfl, hBSrc, hInv'⟩
                unfold evalStep; dsimp
                have hBTgt2 : Trusted.MirSemantics.getElem? pTgt.bodies fTgt.defId = some bTgt := by
                  rw [← hDefEq]; exact hBTgt
                have hBBTgt2 : Trusted.MirSemantics.getElem? bTgt.basicBlocks fTgt.blockIdx = some bbTgt := by
                  rw [← hBlkEq]; exact hBBTgt
                have hNoneTgt2 : Trusted.MirSemantics.getElem? bbTgt.statements fTgt.stmtIdx = none := by
                  rw [← hStIdxEq]; exact (listRel_getElem?_none_iff fSrc.stmtIdx hStmtsRel).mp hStSrc
                have hEndTgt2 : Nat.beq fTgt.stmtIdx bbTgt.statements.length = true := by
                  rw [← hStIdxEq, ← listRel_length hStmtsRel]; exact hEnd
                rw [hBTgt2]; dsimp; rw [hBBTgt2]; dsimp; rw [hNoneTgt2]; dsimp; rw [hEndTgt2]; dsimp
                exact hEvT
        · intro out hDoneS
          unfold evalStep at hDoneS; dsimp at hDoneS
          rw [hBSrc] at hDoneS; dsimp at hDoneS
          cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
          | none => rw [hBBSrc] at hDoneS; cases hDoneS
          | some bbSrc =>
            rw [hBBSrc] at hDoneS; dsimp at hDoneS
            let ⟨bbTgt, hBBTgt, hBBRel⟩ := listRel_getElem?_left hBBs hBBSrc
            let ⟨h12, hTermRel⟩ := bool_and_true hBBRel
            let ⟨hCleanEq, hStmtsRel⟩ := bool_and_true h12
            cases hStSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
            | some sSrc =>
              rw [hStSrc] at hDoneS; dsimp at hDoneS
              exact False.elim (evalStatement_never_done bSrc fSrc cmS sSrc out hDoneS)
            | none =>
              rw [hStSrc] at hDoneS; dsimp at hDoneS
              cases hEnd : Nat.beq fSrc.stmtIdx bbSrc.statements.length with
              | false => rw [hEnd] at hDoneS; cases hDoneS
              | true =>
                rw [hEnd] at hDoneS; dsimp at hDoneS
                have hDoneT := (evalTerminator_fwd_eq hLocEq (bool_beq_eq hCleanEq)
                  (terminatorEq_eq hTermRel) hInv).2 out hDoneS
                unfold evalStep; dsimp
                rw [← hDefEq, hBTgt]; dsimp
                rw [← hBlkEq, hBBTgt]; dsimp
                rw [← hStIdxEq, (listRel_getElem?_none_iff fSrc.stmtIdx hStmtsRel).mp hStSrc]; dsimp
                rw [← listRel_length hStmtsRel, hEnd]; dsimp
                exact hDoneT

private theorem forwardCodegenRefines_of_stmtRel_fwd
    {stmtRel : List MirTy → StatementKind → StatementKind → Bool}
    (hAssignOnly : ∀ locs s₁ s₂, stmtRel locs s₁ s₂ = true →
      s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂))
    (hStmtFwd : ∀ b₁ b₂ f₁ f₂ cm s₁ s₂ s',
      b₁.locals = b₂.locals →
      LocalsFwdRefines b₁.locals f₁.locals f₂.locals →
      stmtRel b₁.locals s₁ s₂ = true →
      evalStatement b₁ f₁ cm s₁ = .step s' →
      ∃ locs1' locs2',
        s' = { frames := [{ f₁ with stmtIdx := f₁.stmtIdx + 1, locals := locs1' }],
               callerMem := cm } ∧
        evalStatement b₂ f₂ cm s₂ =
          .step { frames := [{ f₂ with stmtIdx := f₂.stmtIdx + 1, locals := locs2' }],
                  callerMem := cm } ∧
        LocalsFwdRefines b₁.locals locs1' locs2')
    {pSrc pTgt : Program} (hProg : genericProgRel stmtRel pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hProg
  apply forwardCodegenRefines_of_query_fwd hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hBHdr, _, hBBEmpty, _, hBounds, _⟩ := genericBodyRel_storage_eq hAssignOnly hBRel
    exact ⟨hBHdr, hBBEmpty, hBounds⟩
  · intro q hWf
    exact genericProgRel_query_fwd hAssignOnly hStmtFwd hProg q hWf
  · intro defId args hWf
    exact (genericProgRel_query_fwd hAssignOnly hStmtFwd
      (genericProgRel_entryProg defId hProg) { args := args } hWf).1

/-! ### Stage 4 Private Helpers — Layer C: Modular, Bitwise, & Operator
Algebra -/

/-! #### Elementary `Nat` & `Int` Arithmetic Wrappers (Zero `omega`, Zero
Forbidden Syntax) -/

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_mod_lt (a : Nat) {b : Nat} (h : 0 < b) : Nat.mod a b < b :=
  Nat.mod_lt a h

private theorem nat_div_add_mod (a b : Nat) : b * Nat.div a b + Nat.mod a b = a :=
  Nat.div_add_mod a b

private theorem nat_mul_add_mod (a b c : Nat) : Nat.mod (a * b + c) a = Nat.mod c a := by
  rw [Nat.add_comm (a * b) c]
  exact Nat.add_mul_mod_self_left c a b

private theorem nat_div_one (a : Nat) : Nat.div a 1 = a := Nat.div_one a
private theorem nat_mod_one (a : Nat) : Nat.mod a 1 = 0 := Nat.mod_one a
private theorem nat_zero_div (a : Nat) : Nat.div 0 a = 0 := Nat.zero_div a
private theorem nat_zero_mod (a : Nat) : Nat.mod 0 a = 0 := Nat.zero_mod a

private theorem bv_isLt {n : Nat} (x : BitVec n) : x.toNat < Nat.pow 2 n := x.isLt

private theorem intEmod_ofNat (m p : Nat) :
    intEmod (Int.ofNat m) (Int.ofNat p) = Int.ofNat (Nat.mod m p) := rfl

private theorem intEmod_negSucc (m p : Nat) :
    intEmod (Int.negSucc m) (Int.ofNat p) =
      Int.subNatNat p (Nat.succ (Nat.mod m p)) := rfl

private theorem nat_le_pred_of_lt {a m : Nat} (h : a < m) : a ≤ m - 1 := by
  cases m with
  | zero => exact False.elim (Nat.not_lt_zero a h)
  | succ k => exact Nat.le_of_succ_le_succ h

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

private theorem int_eq_of_beq {x y : Int} (h : (x == y) = true) : x = y :=
  of_decide_eq_true h

private theorem bitvec_beq_refl {n : Nat} (x : BitVec n) : (x == x) = true :=
  decide_eq_true rfl

private theorem int_zero_add (x : Int) : 0 + x = x := by
  cases x with
  | ofNat n =>
    change Int.ofNat (0 + n) = Int.ofNat n
    rw [Nat.zero_add]
  | negSucc _ => rfl

private theorem int_add_zero (x : Int) : x + 0 = x := by
  cases x with
  | ofNat _ => rfl
  | negSucc _ => rfl

private theorem int_sub_zero (x : Int) : x - 0 = x := by
  cases x with
  | ofNat _ => rfl
  | negSucc _ => rfl

private theorem int_one_mul (x : Int) : 1 * x = x := by
  cases x with
  | ofNat n =>
    change Int.ofNat (1 * n) = Int.ofNat n
    rw [Nat.one_mul]
  | negSucc n =>
    change Int.negOfNat (1 * Nat.succ n) = Int.negSucc n
    rw [Nat.one_mul]
    rfl

private theorem int_mul_one (x : Int) : x * 1 = x := by
  cases x with
  | ofNat n =>
    change Int.ofNat (n * 1) = Int.ofNat n
    rw [Nat.mul_one]
  | negSucc n =>
    change Int.negOfNat (Nat.succ n * 1) = Int.negSucc n
    rw [Nat.mul_one]
    rfl

private theorem int_zero_mul (x : Int) : 0 * x = 0 := by
  cases x with
  | ofNat n =>
    change Int.ofNat (0 * n) = 0
    rw [Nat.zero_mul]
    rfl
  | negSucc n =>
    change Int.negOfNat (0 * Nat.succ n) = 0
    rw [Nat.zero_mul]
    rfl

private theorem int_mul_zero (x : Int) : x * 0 = 0 := by
  cases x with
  | ofNat _ => rfl
  | negSucc _ => rfl

private theorem int_sub_self (x : Int) : x - x = 0 := by
  cases x with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ k =>
      change Int.subNatNat (k + 1) (k + 1) = 0
      rw [int_subNatNat_of_le (Nat.le_refl (k + 1)), Nat.sub_self]
      rfl
  | negSucc k =>
    change Int.subNatNat (k + 1) (k + 1) = 0
    rw [int_subNatNat_of_le (Nat.le_refl (k + 1)), Nat.sub_self]
    rfl

/-! #### Two's-Complement `bvToInt`, `bvOfInt`, `signExtendBits`, &
`truncateScalar` -/

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
    unfold bvOfInt
    rw [intEmod_ofNat, intEmod_ofNat]
    have hModLt128 : Nat.mod n (Nat.pow 2 128) < Nat.pow 2 128 :=
      nat_mod_lt n hP128
    change Nat.mod (Nat.mod (Nat.mod n (Nat.pow 2 128)) (Nat.pow 2 128)) M = Nat.mod n M
    rw [nat_mod_eq_of_lt hModLt128, hFac]
    exact nat_mod_mul_mod n M K
  | negSucc n =>
    unfold bvOfInt
    rw [intEmod_negSucc, intEmod_negSucc]
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
      dsimp [r, remP]
      rw [hFac]
      exact nat_mod_mul_mod n M K
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
  | false =>
    exact ⟨_, rfl, (fun _ => rfl), (fun h => nomatch h)⟩
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
    dsimp
    unfold signExtendBits
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
    rw [decide_eq_false hNotNeg, decide_eq_false hNotGe]
    rfl

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
      rw [← hSum]
      exact Nat.add_sub_cancel b.toNat (k + 1)

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
      rw [decodeScalar_unsigned hWf]
      unfold bvOfInt
      rw [intEmod_ofNat]
      apply bitvec_eq_of_toNat_eq
      change Nat.mod (Nat.mod b.toNat (Nat.pow 2 128)) (Nat.pow 2 128) = b.toNat
      rw [nat_mod_eq_of_lt (bv_isLt b), nat_mod_eq_of_lt (bv_isLt b)]
    rw [hBvEq] at hL
    have hLossyFalse : (b != b) = false := by
      change (!(b == b)) = false
      rw [bitvec_beq_refl b]; rfl
    rw [hLossyFalse] at hL
    subst hL; exact hTr
  | true =>
    have hL := hTrue rfl
    rw [hBits] at hL
    have hDecEq : bvToInt (bvOfInt 128 (decodeScalar ⟨w, true, b⟩)) = signExtendBits w b := by
      rw [decodeScalar_signed hWf]
      unfold signExtendBits
      let x := bvSignExtend 128 (bvExtractLsb (w.bitWidth - 1) 0 b)
      change bvToInt (bvOfInt 128 (bvToInt x)) = bvToInt x
      rw [bvOfInt_bvToInt_128 x]
    rw [hDecEq] at hL
    have hLossyFalse : (signExtendBits w b != signExtendBits w b) = false := by
      change (!(signExtendBits w b == signExtendBits w b)) = false
      rw [int_beq_refl]; rfl
    rw [hLossyFalse] at hL
    subst hL; exact hTr

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

/-! #### Constant Predicate Inversions -/

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

private theorem isTrueBoolConst_elim {c : ConstOperand} (h : isTrueBoolConst c = true) :
    c = ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩ ∧
    evalConstLit c.ty c.lit = .ok (.bool true) := by
  cases c with
  | mk ty lit =>
    unfold isTrueBoolConst at h; dsimp at h
    let ⟨h1, h2⟩ := bool_and_true h
    have hTy := mirTy_beq_eq h1
    have hLit := constLitEq_eq h2
    subst hTy; subst hLit
    exact ⟨rfl, rfl⟩

private theorem truncateBits_zero (w : IntWidth) :
    truncateBits w (BitVec.ofNat 128 0) = BitVec.ofNat 128 0 := by
  cases w <;> decide

private theorem truncateBits_one (w : IntWidth) :
    truncateBits w (BitVec.ofNat 128 1) = BitVec.ofNat 128 1 := by
  cases w <;> decide

private theorem truncateBits_allOnes (w : IntWidth) :
    truncateBits w (allOnesBits w) = allOnesBits w := by
  cases w <;> decide

private theorem toNat_allOnes (w : IntWidth) :
    (allOnesBits w).toNat = Nat.pow 2 w.bitWidth - 1 := by
  cases w <;> decide

private theorem decodeScalar_zero (w : IntWidth) (s : Bool) :
    decodeScalar ⟨w, s, BitVec.ofNat 128 0⟩ = 0 := by
  cases w <;> cases s <;> decide

private theorem decodeScalar_one (w : IntWidth) (s : Bool) :
    decodeScalar ⟨w, s, BitVec.ofNat 128 1⟩ = 1 := by
  cases w <;> cases s <;> decide

private theorem truncateScalar_zero (w : IntWidth) (s : Bool) :
    truncateScalar w s 0 = .ok (⟨w, s, BitVec.ofNat 128 0⟩, false) := by
  rw [← decodeScalar_zero w s]
  exact truncateScalar_decodeScalar (truncateBits_zero w)

private theorem signedMinInt_ne_zero (w : IntWidth) :
    ((0 : Int) == signedMinInt w) = false := by
  cases w <;> decide

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
    dsimp only
    unfold evalConstLit
    dsimp only
    rw [truncateBits_zero w]
    rfl

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
    dsimp only
    unfold evalConstLit
    dsimp only
    rw [truncateBits_one w]
    rfl

private theorem isIntAllOnesConst_elim {w : IntWidth} {s : Bool} {c : ConstOperand}
    (h : isIntAllOnesConst w s c = true) :
    c = ⟨.int w s, .scalar (allOnesBits w)⟩ ∧
    evalConstLit c.ty c.lit = .ok (.scalar ⟨w, s, allOnesBits w⟩) := by
  cases c with
  | mk ty lit =>
    unfold isIntAllOnesConst at h; dsimp at h
    let ⟨h1, h2⟩ := bool_and_true h
    have hTy := mirTy_beq_eq h1
    have hLit := constLitEq_eq h2
    subst hTy; subst hLit
    refine ⟨rfl, ?_⟩
    dsimp only
    unfold evalConstLit
    dsimp only
    rw [truncateBits_allOnes w]
    have hBne : (allOnesBits w != allOnesBits w) = false := by
      change (!(allOnesBits w == allOnesBits w)) = false
      rw [bitvec_beq_refl]; rfl
    rw [hBne]; rfl

private theorem isAnyIntZeroConst_elim {c : ConstOperand}
    (h : isAnyIntZeroConst c = true) :
    ∃ rw rs,
      c = ⟨.int rw rs, .scalar (BitVec.ofNat 128 0)⟩ ∧
      evalConstLit c.ty c.lit = .ok (.scalar ⟨rw, rs, BitVec.ofNat 128 0⟩) := by
  cases c with
  | mk ty lit =>
    unfold isAnyIntZeroConst at h; dsimp at h
    cases ty with
    | int rw rs =>
      cases lit with
      | zeroSized => cases h
      | scalar bits =>
        have hBits := bitvec_beq_eq h
        subst hBits
        refine ⟨rw, rs, rfl, ?_⟩
        dsimp only
        unfold evalConstLit
        dsimp only
        rw [truncateBits_zero rw]; rfl
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
      cases h

/-! #### Bitwise Identities Over `Nat.bitwise` (`land`, `lor`, `xor`) -/

private theorem nat_lor_zero_left (m : Nat) : Nat.lor 0 m = m := by
  unfold Nat.lor; rw [Nat.bitwise.eq_1]; rfl

private theorem nat_lor_zero_right (n : Nat) : Nat.lor n 0 = n := by
  unfold Nat.lor; rw [Nat.bitwise.eq_1]; cases n <;> rfl

private theorem nat_xor_zero_left (m : Nat) : Nat.xor 0 m = m := by
  unfold Nat.xor; rw [Nat.bitwise.eq_1]; rfl

private theorem nat_xor_zero_right (n : Nat) : Nat.xor n 0 = n := by
  unfold Nat.xor; rw [Nat.bitwise.eq_1]; cases n <;> rfl

private theorem nat_land_zero_left (m : Nat) : Nat.land 0 m = 0 := by
  unfold Nat.land; rw [Nat.bitwise.eq_1]; rfl

private theorem nat_land_zero_right (n : Nat) : Nat.land n 0 = 0 := by
  unfold Nat.land; rw [Nat.bitwise.eq_1]; cases n <;> rfl

private theorem nat_pow2_succ (k : Nat) : Nat.pow 2 (k + 1) = 2 * Nat.pow 2 k := by
  change Nat.pow 2 k * 2 = 2 * Nat.pow 2 k
  exact Nat.mul_comm (Nat.pow 2 k) 2

private theorem nat_hdiv2_lt_pow {k n : Nat} (h : n < Nat.pow 2 (k + 1)) :
    HDiv.hDiv n 2 < Nat.pow 2 k := by
  rw [nat_pow2_succ] at h
  cases Nat.lt_or_ge (HDiv.hDiv n 2) (Nat.pow 2 k) with
  | inl hlt => exact hlt
  | inr hge =>
    have h1 : 2 * Nat.pow 2 k ≤ 2 * HDiv.hDiv n 2 := Nat.mul_le_mul_left 2 hge
    have h2 : 2 * HDiv.hDiv n 2 ≤ 2 * HDiv.hDiv n 2 + HMod.hMod n 2 :=
      Nat.le_add_right _ _
    rw [Nat.div_add_mod n 2] at h2
    exact False.elim (Nat.not_lt_of_ge (Nat.le_trans h1 h2) h)

private theorem nat_xor_self_bounded (k : Nat) :
    ∀ n, n < Nat.pow 2 k → Nat.xor n n = 0 := by
  induction k with
  | zero =>
    intro n hLt
    cases n with
    | zero => rfl
    | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hLt))
  | succ k ih =>
    intro n hLt
    unfold Nat.xor
    rw [Nat.bitwise.eq_1]
    cases hn : n with
    | zero => rfl
    | succ _ =>
      rw [← hn]
      have hNe : n ≠ 0 := by rw [hn]; intro hc; cases hc
      rw [ite_prop_false hNe, ite_prop_false hNe]
      dsimp only
      have hRec : Nat.bitwise bne (HDiv.hDiv n 2) (HDiv.hDiv n 2) = 0 :=
        ih (HDiv.hDiv n 2) (nat_hdiv2_lt_pow hLt)
      rw [hRec]
      have hBneSelf : ∀ b : Bool, bne b b = false := by intro b; cases b <;> rfl
      rw [hBneSelf]
      rfl

private theorem pow2_pos_any (k : Nat) : 0 < Nat.pow 2 k := by
  induction k with
  | zero => decide
  | succ m ih =>
    rw [nat_pow2_succ, nat_two_mul]
    exact Nat.lt_of_lt_of_le ih (Nat.le_add_right _ _)

private theorem pow2_succ_pred_hdiv_hmod (k : Nat) :
    Nat.pow 2 (k + 1) - 1 ≠ 0 ∧
    HDiv.hDiv (Nat.pow 2 (k + 1) - 1) 2 = Nat.pow 2 k - 1 ∧
    HMod.hMod (Nat.pow 2 (k + 1) - 1) 2 = 1 := by
  have hPos : 0 < Nat.pow 2 k := pow2_pos_any k
  cases hH : Nat.pow 2 k with
  | zero => rw [hH] at hPos; exact False.elim (Nat.not_lt_zero 0 hPos)
  | succ h =>
    have hPowSucc : Nat.pow 2 (k + 1) - 1 = 2 * h + 1 := by
      rw [nat_pow2_succ, hH, Nat.mul_add 2 h 1]
      rfl
    rw [hPowSucc]
    have hSubH : Nat.succ h - 1 = h := rfl
    rw [hSubH]
    refine ⟨?_, ?_, ?_⟩
    · intro hc; cases hc
    · rw [Nat.add_comm (2 * h) 1, Nat.add_mul_div_left 1 h (by decide : 0 < 2)]
      exact Nat.zero_add h
    · rw [Nat.add_comm (2 * h) 1, Nat.add_mul_mod_self_left 1 2 h]

private theorem nat_reconstruct_hdiv2 (n : Nat) :
    (if decide (HMod.hMod n 2 = 1) then
       HDiv.hDiv n 2 + HDiv.hDiv n 2 + 1
     else
       HDiv.hDiv n 2 + HDiv.hDiv n 2) = n := by
  have hDM := Nat.div_add_mod n 2
  rw [nat_two_mul (HDiv.hDiv n 2)] at hDM
  have hModLt : HMod.hMod n 2 < 2 := Nat.mod_lt n (by decide : 0 < 2)
  cases hm : HMod.hMod n 2 with
  | zero =>
    rw [hm] at hDM
    rw [Nat.add_zero] at hDM
    have hF : decide (0 = 1) = false := rfl
    rw [hF]; exact hDM
  | succ r =>
    rw [hm] at hModLt
    cases r with
    | zero =>
      rw [hm] at hDM
      have hT : decide (1 = 1) = true := rfl
      rw [hT]; exact hDM
    | succ r2 =>
      exact False.elim (Nat.not_lt_zero r2 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hModLt)))

private theorem nat_land_allOnes_right_bounded (k : Nat) :
    ∀ n, n < Nat.pow 2 k → Nat.land n (Nat.pow 2 k - 1) = n := by
  induction k with
  | zero =>
    intro n hLt
    cases n with
    | zero => rfl
    | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hLt))
  | succ k ih =>
    intro n hLt
    cases hn : n with
    | zero => exact nat_land_zero_left _
    | succ _ =>
      rw [← hn]
      have hNeN : n ≠ 0 := by rw [hn]; intro hc; cases hc
      let ⟨hNeM, hDivM, hModM⟩ := pow2_succ_pred_hdiv_hmod k
      unfold Nat.land
      rw [Nat.bitwise.eq_1]
      rw [ite_prop_false hNeN, ite_prop_false hNeM]
      dsimp only
      rw [hDivM, hModM]
      have hRec : Nat.bitwise and (HDiv.hDiv n 2) (Nat.pow 2 k - 1) = HDiv.hDiv n 2 :=
        ih (HDiv.hDiv n 2) (nat_hdiv2_lt_pow hLt)
      rw [hRec]
      have hDec1 : decide ((1 : Nat) = 1) = true := rfl
      rw [hDec1, Bool.and_true]
      exact nat_reconstruct_hdiv2 n

private theorem nat_land_allOnes_left_bounded (k : Nat) :
    ∀ n, n < Nat.pow 2 k → Nat.land (Nat.pow 2 k - 1) n = n := by
  induction k with
  | zero =>
    intro n hLt
    cases n with
    | zero => rfl
    | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hLt))
  | succ k ih =>
    intro n hLt
    cases hn : n with
    | zero => exact nat_land_zero_right _
    | succ _ =>
      rw [← hn]
      have hNeN : n ≠ 0 := by rw [hn]; intro hc; cases hc
      let ⟨hNeM, hDivM, hModM⟩ := pow2_succ_pred_hdiv_hmod k
      unfold Nat.land
      rw [Nat.bitwise.eq_1]
      rw [ite_prop_false hNeM, ite_prop_false hNeN]
      dsimp only
      rw [hDivM, hModM]
      have hRec : Nat.bitwise and (Nat.pow 2 k - 1) (HDiv.hDiv n 2) = HDiv.hDiv n 2 :=
        ih (HDiv.hDiv n 2) (nat_hdiv2_lt_pow hLt)
      rw [hRec]
      have hDec1 : decide ((1 : Nat) = 1) = true := rfl
      rw [hDec1, Bool.true_and]
      exact nat_reconstruct_hdiv2 n

private theorem nat_lor_allOnes_right_bounded (k : Nat) :
    ∀ n, n < Nat.pow 2 k → Nat.lor n (Nat.pow 2 k - 1) = Nat.pow 2 k - 1 := by
  induction k with
  | zero =>
    intro n hLt
    cases n with
    | zero => rfl
    | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hLt))
  | succ k ih =>
    intro n hLt
    cases hn : n with
    | zero => exact nat_lor_zero_left _
    | succ _ =>
      rw [← hn]
      have hNeN : n ≠ 0 := by rw [hn]; intro hc; cases hc
      let ⟨hNeM, hDivM, hModM⟩ := pow2_succ_pred_hdiv_hmod k
      unfold Nat.lor
      rw [Nat.bitwise.eq_1]
      rw [ite_prop_false hNeN, ite_prop_false hNeM]
      dsimp only
      rw [hDivM, hModM]
      have hRec : Nat.bitwise or (HDiv.hDiv n 2) (Nat.pow 2 k - 1) = Nat.pow 2 k - 1 :=
        ih (HDiv.hDiv n 2) (nat_hdiv2_lt_pow hLt)
      rw [hRec]
      have hDec1 : decide ((1 : Nat) = 1) = true := rfl
      rw [hDec1, Bool.or_true]
      have hRecM := nat_reconstruct_hdiv2 (Nat.pow 2 (k + 1) - 1)
      rw [hDivM, hModM, hDec1] at hRecM
      exact hRecM

private theorem nat_lor_allOnes_left_bounded (k : Nat) :
    ∀ n, n < Nat.pow 2 k → Nat.lor (Nat.pow 2 k - 1) n = Nat.pow 2 k - 1 := by
  induction k with
  | zero =>
    intro n hLt
    cases n with
    | zero => rfl
    | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hLt))
  | succ k ih =>
    intro n hLt
    cases hn : n with
    | zero => exact nat_lor_zero_right _
    | succ _ =>
      rw [← hn]
      have hNeN : n ≠ 0 := by rw [hn]; intro hc; cases hc
      let ⟨hNeM, hDivM, hModM⟩ := pow2_succ_pred_hdiv_hmod k
      unfold Nat.lor
      rw [Nat.bitwise.eq_1]
      rw [ite_prop_false hNeM, ite_prop_false hNeN]
      dsimp only
      rw [hDivM, hModM]
      have hRec : Nat.bitwise or (Nat.pow 2 k - 1) (HDiv.hDiv n 2) = Nat.pow 2 k - 1 :=
        ih (HDiv.hDiv n 2) (nat_hdiv2_lt_pow hLt)
      rw [hRec]
      have hDec1 : decide ((1 : Nat) = 1) = true := rfl
      rw [hDec1, Bool.true_or]
      have hRecM := nat_reconstruct_hdiv2 (Nat.pow 2 (k + 1) - 1)
      rw [hDivM, hModM, hDec1] at hRecM
      exact hRecM

private theorem truncateBits_bvOr_zero_left {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvOr (BitVec.ofNat 128 0) b) = b := by
  have h0 : (BitVec.ofNat 128 0).toNat = 0 := rfl
  have hEq : bvOr (BitVec.ofNat 128 0) b = b := by
    apply bitvec_eq_of_toNat_eq
    unfold bvOr; rw [h0, nat_lor_zero_left]
    exact nat_mod_eq_of_lt (bv_isLt b)
  rw [hEq, hWf]

private theorem truncateBits_bvOr_zero_right {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvOr b (BitVec.ofNat 128 0)) = b := by
  have h0 : (BitVec.ofNat 128 0).toNat = 0 := rfl
  have hEq : bvOr b (BitVec.ofNat 128 0) = b := by
    apply bitvec_eq_of_toNat_eq
    unfold bvOr; rw [h0, nat_lor_zero_right]
    exact nat_mod_eq_of_lt (bv_isLt b)
  rw [hEq, hWf]

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

private theorem truncateBits_bvXor_self {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvXor b b) = BitVec.ofNat 128 0 := by
  have hLt := truncateBits_eq_iff.mp hWf
  have hEq : bvXor b b = BitVec.ofNat 128 0 := by
    apply bitvec_eq_of_toNat_eq
    unfold bvXor
    rw [nat_xor_self_bounded w.bitWidth b.toNat hLt]
  rw [hEq, truncateBits_zero w]

private theorem truncateBits_bvAnd_zero_left (w : IntWidth) (b : BitVec 128) :
    truncateBits w (bvAnd (BitVec.ofNat 128 0) b) = BitVec.ofNat 128 0 := by
  have h0 : (BitVec.ofNat 128 0).toNat = 0 := rfl
  have hEq : bvAnd (BitVec.ofNat 128 0) b = BitVec.ofNat 128 0 := by
    apply bitvec_eq_of_toNat_eq
    unfold bvAnd; rw [h0, nat_land_zero_left]; rfl
  rw [hEq, truncateBits_zero w]

private theorem truncateBits_bvAnd_zero_right (w : IntWidth) (b : BitVec 128) :
    truncateBits w (bvAnd b (BitVec.ofNat 128 0)) = BitVec.ofNat 128 0 := by
  have h0 : (BitVec.ofNat 128 0).toNat = 0 := rfl
  have hEq : bvAnd b (BitVec.ofNat 128 0) = BitVec.ofNat 128 0 := by
    apply bitvec_eq_of_toNat_eq
    unfold bvAnd; rw [h0, nat_land_zero_right]; rfl
  rw [hEq, truncateBits_zero w]

private theorem truncateBits_bvAnd_allOnes_left {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvAnd (allOnesBits w) b) = b := by
  have hLt := truncateBits_eq_iff.mp hWf
  have hEq : bvAnd (allOnesBits w) b = b := by
    apply bitvec_eq_of_toNat_eq
    unfold bvAnd
    rw [toNat_allOnes w, nat_land_allOnes_left_bounded w.bitWidth b.toNat hLt]
    exact nat_mod_eq_of_lt (bv_isLt b)
  rw [hEq, hWf]

private theorem truncateBits_bvAnd_allOnes_right {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvAnd b (allOnesBits w)) = b := by
  have hLt := truncateBits_eq_iff.mp hWf
  have hEq : bvAnd b (allOnesBits w) = b := by
    apply bitvec_eq_of_toNat_eq
    unfold bvAnd
    rw [toNat_allOnes w, nat_land_allOnes_right_bounded w.bitWidth b.toNat hLt]
    exact nat_mod_eq_of_lt (bv_isLt b)
  rw [hEq, hWf]

private theorem truncateBits_bvOr_allOnes_left {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvOr (allOnesBits w) b) = allOnesBits w := by
  have hLt := truncateBits_eq_iff.mp hWf
  have hEq : bvOr (allOnesBits w) b = allOnesBits w := by
    apply bitvec_eq_of_toNat_eq
    unfold bvOr
    rw [toNat_allOnes w, nat_lor_allOnes_left_bounded w.bitWidth b.toNat hLt, ← toNat_allOnes w]
    exact nat_mod_eq_of_lt (bv_isLt (allOnesBits w))
  rw [hEq, truncateBits_allOnes w]

private theorem truncateBits_bvOr_allOnes_right {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    truncateBits w (bvOr b (allOnesBits w)) = allOnesBits w := by
  have hLt := truncateBits_eq_iff.mp hWf
  have hEq : bvOr b (allOnesBits w) = allOnesBits w := by
    apply bitvec_eq_of_toNat_eq
    unfold bvOr
    rw [toNat_allOnes w, nat_lor_allOnes_right_bounded w.bitWidth b.toNat hLt, ← toNat_allOnes w]
    exact nat_mod_eq_of_lt (bv_isLt (allOnesBits w))
  rw [hEq, truncateBits_allOnes w]

/-! #### `intTdiv`, `intTmod`, `intShiftLeft`, `intShiftRight` Identities -/

private theorem intTdiv_one_right (x : Int) : intTdiv x 1 = x := by
  cases x with
  | ofNat m =>
    dsimp [intTdiv]; rw [nat_div_one]
  | negSucc m =>
    dsimp [intTdiv]; rw [nat_div_one]; rfl

private theorem intTdiv_zero_left (r : Int) : intTdiv 0 r = 0 := by
  cases r with
  | ofNat n =>
    dsimp [intTdiv]; rw [nat_zero_div]; rfl
  | negSucc n =>
    dsimp [intTdiv]; rw [nat_zero_div]; rfl

private theorem intTmod_zero_left (r : Int) : intTmod 0 r = 0 := by
  cases r with
  | ofNat n =>
    dsimp [intTmod]; rw [nat_zero_mod]; rfl
  | negSucc n =>
    dsimp [intTmod]; rw [nat_zero_mod]; rfl

private theorem intTmod_one_right (x : Int) : intTmod x 1 = 0 := by
  cases x with
  | ofNat m =>
    dsimp [intTmod]; rw [nat_mod_one]; rfl
  | negSucc m =>
    dsimp [intTmod]; rw [nat_mod_one]; rfl

private theorem nat_shiftLeft_zero_left (s : Nat) : Nat.shiftLeft 0 s = 0 := by
  induction s with
  | zero => rfl
  | succ _ ih => dsimp [Nat.shiftLeft]; exact ih

private theorem nat_shiftRight_zero_left (s : Nat) : Nat.shiftRight 0 s = 0 := by
  induction s with
  | zero => rfl
  | succ m ih =>
    change HDiv.hDiv (Nat.shiftRight 0 m) 2 = 0
    rw [ih]

private theorem intShiftLeft_zero_right (x : Int) : intShiftLeft x 0 = x := by
  cases x <;> rfl

private theorem intShiftRight_zero_right (x : Int) : intShiftRight x 0 = x := by
  cases x <;> rfl

private theorem intShiftLeft_zero_left (k : Nat) : intShiftLeft 0 k = 0 := by
  unfold intShiftLeft
  change Int.ofNat (Nat.shiftLeft 0 k) = Int.ofNat 0
  rw [nat_shiftLeft_zero_left]

private theorem intShiftRight_zero_left (k : Nat) : intShiftRight 0 k = 0 := by
  unfold intShiftRight
  change Int.ofNat (Nat.shiftRight 0 k) = Int.ofNat 0
  rw [nat_shiftRight_zero_left]

private theorem intEmod_zero_left (m : Int) : intEmod 0 m = 0 := by
  dsimp [intEmod]; rw [nat_zero_mod]; rfl

/-! #### High-Level `evalArithOp`, `evalBinOp`, and `evalUnOp` Theorems -/

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
  unfold evalBinOp
  dsimp only
  rw [intWidth_beq_refl w, bool_beq_refl s]
  cases op <;> cases hShift <;> rfl

private theorem evalBinOp_scalar_shift {op : BinOp} {w rw : IntWidth} {s rs : Bool}
    {b₁ b₂ : BitVec 128} (hShift : op.isShift = true) :
    evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨rw, rs, b₂⟩) =
      evalShiftOp op w s (decodeScalar ⟨w, s, b₁⟩) (decodeScalar ⟨rw, rs, b₂⟩) := by
  unfold evalBinOp
  dsimp only
  rw [hShift]
  rfl

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
    rw [hHost, hTrunc]
    dsimp
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | bitXor | bitAnd | bitOr | shl | shlUnchecked | shr | shrUnchecked
  | eq | lt | le | ne | ge | gt | offset =>
    cases hRes

private theorem evalArithOp_zero_result {op : BinOp} {w : IntWidth} {s : Bool}
    {l r : Int}
    (hNotDivZero : (binOpIsDivOrRem op && (r == 0)) = false)
    (hNotMinNeg1 : (s && binOpIsDivOrRem op && (l == signedMinInt w && r == Neg.neg 1)) = false)
    (hRes : evalArithMath op l r = some 0) :
    evalArithOp op w s l r = .ok (.scalar ⟨w, s, BitVec.ofNat 128 0⟩) := by
  rw [← decodeScalar_zero w s] at hRes
  exact evalArithOp_preserves_scalar (truncateBits_zero w) hNotDivZero hNotMinNeg1 hRes

private theorem evalBinOp_leftNeutral {dstTy : MirTy} {op : BinOp} {c : ConstOperand}
    {v : Val}
    (hNeutral : isLeftNeutralConstFor dstTy op c = true)
    (hChk : checkVal v dstTy = true) :
    ∃ vc,
      evalConstLit c.ty c.lit = .ok vc ∧
      isPrimitiveReadableTy c.ty = true ∧
      isPrimitiveReadableTy dstTy = true ∧
      evalBinOp op vc v = .ok v := by
  cases dstTy with
  | int w s =>
    let ⟨bits, hv, hWf⟩ := checkVal_int_iff.mp hChk
    subst hv
    unfold isLeftNeutralConstFor at hNeutral
    cases op with
    | add =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_zero_add]
    | addUnchecked =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_zero_add]
    | mul =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_one w s, int_one_mul]
    | mulUnchecked =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_one w s, int_one_mul]
    | bitOr =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_zero w, hWf, truncateBits_bvOr_zero_left hWf]
    | bitXor =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_zero w, hWf, truncateBits_bvXor_zero_left hWf]
    | bitAnd =>
      let ⟨hc, hEvC⟩ := isIntAllOnesConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_allOnes w, hWf, truncateBits_bvAnd_allOnes_left hWf]
    | addWithOverflow | sub | subUnchecked | subWithOverflow | mulWithOverflow
    | div | rem | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset => cases hNeutral
  | bool =>
    let ⟨b, hb⟩ := checkVal_bool_iff.mp hChk
    subst hb
    unfold isLeftNeutralConstFor at hNeutral
    cases op with
    | bitOr =>
      let ⟨hc, hEvC⟩ := isFalseBoolConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      cases b <;> rfl
    | bitXor =>
      let ⟨hc, hEvC⟩ := isFalseBoolConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      cases b <;> rfl
    | bitAnd =>
      let ⟨hc, hEvC⟩ := isTrueBoolConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      cases b <;> rfl
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mul | mulUnchecked | mulWithOverflow | div | rem
    | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset => cases hNeutral
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases hNeutral

private theorem evalBinOp_rightNeutral {dstTy : MirTy} {op : BinOp} {c : ConstOperand}
    {v : Val}
    (hNeutral : isRightNeutralConstFor dstTy op c = true)
    (hChk : checkVal v dstTy = true) :
    ∃ vc,
      evalConstLit c.ty c.lit = .ok vc ∧
      isPrimitiveReadableTy c.ty = true ∧
      isPrimitiveReadableTy dstTy = true ∧
      evalBinOp op v vc = .ok v := by
  cases dstTy with
  | int w s =>
    let ⟨bits, hv, hWf⟩ := checkVal_int_iff.mp hChk
    subst hv
    unfold isRightNeutralConstFor at hNeutral
    cases op with
    | add =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_add_zero]
    | addUnchecked =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_add_zero]
    | sub =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_sub_zero]
    | subUnchecked =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_sub_zero]
    | mul =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_one w s, int_mul_one]
    | mulUnchecked =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_preserves_scalar hWf rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_one w s, int_mul_one]
    | div =>
      let ⟨hc, hEvC⟩ := isIntOneConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      have hOneNe0 : ((1 : Int) == 0) = false := rfl
      have hOneNeNeg1 : ((1 : Int) == Neg.neg 1) = false := rfl
      refine evalArithOp_preserves_scalar hWf ?_ ?_ ?_
      · dsimp [binOpIsDivOrRem]; rw [decodeScalar_one w s]; exact hOneNe0
      · dsimp [binOpIsDivOrRem]; rw [decodeScalar_one w s, hOneNeNeg1, Bool.and_false, Bool.and_false]
      · dsimp [evalArithMath]; rw [decodeScalar_one w s, intTdiv_one_right]
    | bitOr =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_zero w, hWf, truncateBits_bvOr_zero_right hWf]
    | bitXor =>
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_zero w, hWf, truncateBits_bvXor_zero_right hWf]
    | bitAnd =>
      let ⟨hc, hEvC⟩ := isIntAllOnesConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_allOnes w, hWf, truncateBits_bvAnd_allOnes_right hWf]
    | shl =>
      let ⟨rw, rs, hc, hEvC⟩ := isAnyIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_shift rfl]
      unfold evalShiftOp
      dsimp only [BinOp.isUnchecked]
      rw [decodeScalar_zero rw rs, intEmod_zero_left]
      have hToNat0 : (0 : Int).toNat = 0 := rfl
      rw [hToNat0, intShiftLeft_zero_right, truncateScalar_decodeScalar hWf]
      rfl
    | shr =>
      let ⟨rw, rs, hc, hEvC⟩ := isAnyIntZeroConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      rw [evalBinOp_scalar_shift rfl]
      unfold evalShiftOp
      dsimp only [BinOp.isUnchecked]
      rw [decodeScalar_zero rw rs, intEmod_zero_left]
      have hToNat0 : (0 : Int).toNat = 0 := rfl
      rw [hToNat0, intShiftRight_zero_right, truncateScalar_decodeScalar hWf]
      rfl
    | addWithOverflow | subWithOverflow | mulWithOverflow | rem
    | shlUnchecked | shrUnchecked | eq | lt | le | ne | ge | gt | offset =>
      cases hNeutral
  | bool =>
    let ⟨b, hb⟩ := checkVal_bool_iff.mp hChk
    subst hb
    unfold isRightNeutralConstFor at hNeutral
    cases op with
    | bitOr =>
      let ⟨hc, hEvC⟩ := isFalseBoolConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      cases b <;> rfl
    | bitXor =>
      let ⟨hc, hEvC⟩ := isFalseBoolConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      cases b <;> rfl
    | bitAnd =>
      let ⟨hc, hEvC⟩ := isTrueBoolConst_elim hNeutral
      refine ⟨_, hEvC, by rw [hc]; rfl, rfl, ?_⟩
      cases b <;> rfl
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mul | mulUnchecked | mulWithOverflow | div | rem
    | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset => cases hNeutral
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases hNeutral

private theorem evalBinOp_zeroLhs_div_rem_of_ne_zero {op : BinOp} {w : IntWidth} {s : Bool}
    {b : BitVec 128}
    (hOp : (binOpEq op .div || binOpEq op .rem) = true)
    (hNe0 : decodeScalar ⟨w, s, b⟩ ≠ 0) :
    evalBinOp op (.scalar ⟨w, s, BitVec.ofNat 128 0⟩) (.scalar ⟨w, s, b⟩) =
      .ok (.scalar ⟨w, s, BitVec.ofNat 128 0⟩) := by
  have hBeq0 : (decodeScalar ⟨w, s, b⟩ == 0) = false := by
    cases hB : (decodeScalar ⟨w, s, b⟩ == 0) with
    | false => rfl
    | true => exact False.elim (hNe0 (int_eq_of_beq hB))
  have hMin : (decodeScalar ⟨w, s, BitVec.ofNat 128 0⟩ == signedMinInt w) = false := by
    rw [decodeScalar_zero w s]; exact signedMinInt_ne_zero w
  cases bool_or_true hOp with
  | inl hDiv =>
    have hEq := binOpEq_eq hDiv; subst hEq
    rw [evalBinOp_scalar_nonShift rfl]; dsimp only
    refine evalArithOp_zero_result ?_ ?_ ?_
    · dsimp [binOpIsDivOrRem]; exact hBeq0
    · dsimp [binOpIsDivOrRem]; rw [hMin, Bool.false_and, Bool.and_false]
    · dsimp [evalArithMath]; rw [decodeScalar_zero w s, intTdiv_zero_left]
  | inr hRem =>
    have hEq := binOpEq_eq hRem; subst hEq
    rw [evalBinOp_scalar_nonShift rfl]; dsimp only
    refine evalArithOp_zero_result ?_ ?_ ?_
    · dsimp [binOpIsDivOrRem]; exact hBeq0
    · dsimp [binOpIsDivOrRem]; rw [hMin, Bool.false_and, Bool.and_false]
    · dsimp [evalArithMath]; rw [decodeScalar_zero w s, intTmod_zero_left]

private theorem evalBinOp_zeroLhs_div_rem_fwd {op : BinOp} {w : IntWidth} {s : Bool}
    {vr res : Val}
    (hOp : (binOpEq op .div || binOpEq op .rem) = true)
    (hChk : checkVal vr (.int w s) = true)
    (hEv : evalBinOp op (.scalar ⟨w, s, BitVec.ofNat 128 0⟩) vr = .ok res) :
    res = .scalar ⟨w, s, BitVec.ofNat 128 0⟩ := by
  let ⟨b, hvr, _⟩ := checkVal_int_iff.mp hChk
  subst hvr
  cases hZero : (decodeScalar ⟨w, s, b⟩ == 0) with
  | true =>
    cases bool_or_true hOp with
    | inl hDiv =>
      have hO := binOpEq_eq hDiv; subst hO
      rw [evalBinOp_scalar_nonShift rfl] at hEv
      unfold evalArithOp at hEv
      dsimp only at hEv
      rw [hZero] at hEv; cases hEv
    | inr hRem =>
      have hO := binOpEq_eq hRem; subst hO
      rw [evalBinOp_scalar_nonShift rfl] at hEv
      unfold evalArithOp at hEv
      dsimp only at hEv
      rw [hZero] at hEv; cases hEv
  | false =>
    have hNe0 : decodeScalar ⟨w, s, b⟩ ≠ 0 := by
      intro hc; rw [hc] at hZero; cases hZero
    have hOk := evalBinOp_zeroLhs_div_rem_of_ne_zero hOp hNe0
    rw [hOk] at hEv
    injection hEv with hRes
    exact hRes.symm

private theorem evalBinOp_leftAbsorbing {dstTy rhsTy : MirTy} {op : BinOp}
    {c cOut : ConstOperand} {vr : Val}
    (hAbs : isLeftAbsorbingFor dstTy rhsTy op c cOut = true)
    (hChkR : checkVal vr rhsTy = true) :
    ∃ vc vOut,
      evalConstLit c.ty c.lit = .ok vc ∧
      evalConstLit cOut.ty cOut.lit = .ok vOut ∧
      cOut.ty = dstTy ∧
      isPrimitiveReadableTy c.ty = true ∧
      evalBinOp op vc vr = .ok vOut := by
  cases dstTy with
  | int w s =>
    unfold isLeftAbsorbingFor at hAbs
    cases op with
    | mul =>
      let ⟨h12, hOut⟩ := bool_and_true hAbs
      let ⟨hRTy, hC⟩ := bool_and_true h12
      have hREq := mirTy_beq_eq hRTy; subst hREq
      let ⟨b, hvr, _⟩ := checkVal_int_iff.mp hChkR; subst hvr
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_zero_result rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_zero_mul]
    | mulUnchecked =>
      let ⟨h12, hOut⟩ := bool_and_true hAbs
      let ⟨hRTy, hC⟩ := bool_and_true h12
      have hREq := mirTy_beq_eq hRTy; subst hREq
      let ⟨b, hvr, _⟩ := checkVal_int_iff.mp hChkR; subst hvr
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_zero_result rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_zero_mul]
    | bitAnd =>
      let ⟨h12, hOut⟩ := bool_and_true hAbs
      let ⟨hRTy, hC⟩ := bool_and_true h12
      have hREq := mirTy_beq_eq hRTy; subst hREq
      let ⟨b, hvr, _⟩ := checkVal_int_iff.mp hChkR; subst hvr
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_zero w, truncateBits_bvAnd_zero_left]
    | bitOr =>
      let ⟨h12, hOut⟩ := bool_and_true hAbs
      let ⟨hRTy, hC⟩ := bool_and_true h12
      have hREq := mirTy_beq_eq hRTy; subst hREq
      let ⟨b, hvr, hWfR⟩ := checkVal_int_iff.mp hChkR; subst hvr
      let ⟨hc, hEvC⟩ := isIntAllOnesConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntAllOnesConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_allOnes w, hWfR, truncateBits_bvOr_allOnes_left hWfR]
    | shl =>
      let ⟨h12, hOut⟩ := bool_and_true hAbs
      let ⟨hRInt, hC⟩ := bool_and_true h12
      cases rhsTy with
      | int rw rs =>
        let ⟨b, hvr, _⟩ := checkVal_int_iff.mp hChkR; subst hvr
        let ⟨hc, hEvC⟩ := isIntZeroConst_elim hC
        let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
        refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
        rw [evalBinOp_scalar_shift rfl]
        unfold evalShiftOp
        rw [decodeScalar_zero w s]
        dsimp only
        rw [intShiftLeft_zero_left, truncateScalar_zero w s]
        dsimp only [BinOp.isUnchecked]
        exact if_bool_false (Bool.and_false _)
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
        cases hRInt
    | shr =>
      let ⟨h12, hOut⟩ := bool_and_true hAbs
      let ⟨hRInt, hC⟩ := bool_and_true h12
      cases rhsTy with
      | int rw rs =>
        let ⟨b, hvr, _⟩ := checkVal_int_iff.mp hChkR; subst hvr
        let ⟨hc, hEvC⟩ := isIntZeroConst_elim hC
        let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
        refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
        rw [evalBinOp_scalar_shift rfl]
        unfold evalShiftOp
        rw [decodeScalar_zero w s]
        dsimp only
        rw [intShiftRight_zero_left, truncateScalar_zero w s]
        dsimp only [BinOp.isUnchecked]
        exact if_bool_false (Bool.and_false _)
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
        cases hRInt
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mulWithOverflow | div | rem | bitXor | shlUnchecked | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset => cases hAbs
  | bool =>
    unfold isLeftAbsorbingFor at hAbs
    let ⟨hRTy, hRest⟩ := bool_and_true hAbs
    have hREq := mirTy_beq_eq hRTy; subst hREq
    let ⟨b, hvr⟩ := checkVal_bool_iff.mp hChkR; subst hvr
    cases op with
    | bitAnd =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isFalseBoolConst_elim hC
      let ⟨hcO, hEvCO⟩ := isFalseBoolConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      cases b <;> rfl
    | bitOr =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isTrueBoolConst_elim hC
      let ⟨hcO, hEvCO⟩ := isTrueBoolConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      cases b <;> rfl
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mul | mulUnchecked | mulWithOverflow | div | rem | bitXor
    | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset => cases hRest
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases hAbs

private theorem evalBinOp_rightAbsorbing {dstTy lhsTy : MirTy} {op : BinOp}
    {c cOut : ConstOperand} {vl : Val}
    (hAbs : isRightAbsorbingFor dstTy lhsTy op c cOut = true)
    (hChkL : checkVal vl lhsTy = true) :
    ∃ vc vOut,
      evalConstLit c.ty c.lit = .ok vc ∧
      evalConstLit cOut.ty cOut.lit = .ok vOut ∧
      cOut.ty = dstTy ∧
      isPrimitiveReadableTy c.ty = true ∧
      evalBinOp op vl vc = .ok vOut := by
  cases dstTy with
  | int w s =>
    unfold isRightAbsorbingFor at hAbs
    let ⟨hLTy, hRest⟩ := bool_and_true hAbs
    have hLEq := mirTy_beq_eq hLTy; subst hLEq
    let ⟨b, hvl, hWfL⟩ := checkVal_int_iff.mp hChkL; subst hvl
    cases op with
    | mul =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_zero_result rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_mul_zero]
    | mulUnchecked =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_zero_result rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [decodeScalar_zero w s, int_mul_zero]
    | bitAnd =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isIntZeroConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_zero w, truncateBits_bvAnd_zero_right]
    | rem =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isIntOneConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      have hOneNe0 : ((1 : Int) == 0) = false := rfl
      have hOneNeNeg1 : ((1 : Int) == Neg.neg 1) = false := rfl
      refine evalArithOp_zero_result ?_ ?_ ?_
      · dsimp [binOpIsDivOrRem]; rw [decodeScalar_one w s]; exact hOneNe0
      · dsimp [binOpIsDivOrRem]; rw [decodeScalar_one w s, hOneNeNeg1, Bool.and_false, Bool.and_false]
      · dsimp [evalArithMath]; rw [decodeScalar_one w s, intTmod_one_right]
    | bitOr =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isIntAllOnesConst_elim hC
      let ⟨hcO, hEvCO⟩ := isIntAllOnesConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [truncateBits_allOnes w, hWfL, truncateBits_bvOr_allOnes_right hWfL]
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mulWithOverflow | div | bitXor
    | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset => cases hRest
  | bool =>
    unfold isRightAbsorbingFor at hAbs
    let ⟨hLTy, hRest⟩ := bool_and_true hAbs
    have hLEq := mirTy_beq_eq hLTy; subst hLEq
    let ⟨b, hvl⟩ := checkVal_bool_iff.mp hChkL; subst hvl
    cases op with
    | bitAnd =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isFalseBoolConst_elim hC
      let ⟨hcO, hEvCO⟩ := isFalseBoolConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      cases b <;> rfl
    | bitOr =>
      let ⟨hC, hOut⟩ := bool_and_true hRest
      let ⟨hc, hEvC⟩ := isTrueBoolConst_elim hC
      let ⟨hcO, hEvCO⟩ := isTrueBoolConst_elim hOut
      refine ⟨_, _, hEvC, hEvCO, by rw [hcO], by rw [hc]; rfl, ?_⟩
      cases b <;> rfl
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mul | mulUnchecked | mulWithOverflow | div | rem | bitXor
    | shl | shlUnchecked | shr | shrUnchecked
    | eq | lt | le | ne | ge | gt | offset => cases hRest
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases hAbs

private theorem evalBinOp_selfCancel {dstTy opndTy : MirTy} {op : BinOp}
    {cOut : ConstOperand} {v : Val}
    (hSelf : isSelfCancelFor dstTy opndTy op cOut = true)
    (hChk : checkVal v opndTy = true) :
    ∃ vOut,
      evalConstLit cOut.ty cOut.lit = .ok vOut ∧
      cOut.ty = dstTy ∧
      isPrimitiveReadableTy opndTy = true ∧
      evalBinOp op v v = .ok vOut := by
  cases opndTy with
  | int w s =>
    let ⟨b, hv, hWf⟩ := checkVal_int_iff.mp hChk; subst hv
    unfold isSelfCancelFor at hSelf
    cases op with
    | sub =>
      let ⟨hDTy, hOut⟩ := bool_and_true hSelf
      have hDEq := mirTy_beq_eq hDTy; subst hDEq
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, hEvCO, by rw [hcO], rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_zero_result rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [int_sub_self]
    | subUnchecked =>
      let ⟨hDTy, hOut⟩ := bool_and_true hSelf
      have hDEq := mirTy_beq_eq hDTy; subst hDEq
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, hEvCO, by rw [hcO], rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      refine evalArithOp_zero_result rfl (by cases s <;> rfl) ?_
      dsimp [evalArithMath]; rw [int_sub_self]
    | bitXor =>
      let ⟨hDTy, hOut⟩ := bool_and_true hSelf
      have hDEq := mirTy_beq_eq hDTy; subst hDEq
      let ⟨hcO, hEvCO⟩ := isIntZeroConst_elim hOut
      refine ⟨_, hEvCO, by rw [hcO], rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [hWf, truncateBits_bvXor_self hWf]
    | eq =>
      let ⟨hDTy, hOut⟩ := bool_and_true hSelf
      have hDEq := mirTy_beq_eq hDTy; subst hDEq
      let ⟨hcO, hEvCO⟩ := isTrueBoolConst_elim hOut
      refine ⟨_, hEvCO, by rw [hcO], rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      rw [int_beq_refl]
    | ne =>
      let ⟨hDTy, hOut⟩ := bool_and_true hSelf
      have hDEq := mirTy_beq_eq hDTy; subst hDEq
      let ⟨hcO, hEvCO⟩ := isFalseBoolConst_elim hOut
      refine ⟨_, hEvCO, by rw [hcO], rfl, ?_⟩
      rw [evalBinOp_scalar_nonShift rfl]; dsimp only
      have hBneSelf : (decodeScalar ⟨w, s, b⟩ != decodeScalar ⟨w, s, b⟩) = false := by
        change (!(decodeScalar ⟨w, s, b⟩ == decodeScalar ⟨w, s, b⟩)) = false
        rw [int_beq_refl]; rfl
      rw [hBneSelf]
    | add | addUnchecked | addWithOverflow | subWithOverflow
    | mul | mulUnchecked | mulWithOverflow | div | rem | bitAnd | bitOr
    | shl | shlUnchecked | shr | shrUnchecked | lt | le | ge | gt | offset =>
      cases hSelf
  | bool =>
    let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
    unfold isSelfCancelFor at hSelf
    let ⟨hDTy, hRest⟩ := bool_and_true hSelf
    have hDEq := mirTy_beq_eq hDTy; subst hDEq
    cases op with
    | bitXor =>
      let ⟨hcO, hEvCO⟩ := isFalseBoolConst_elim hRest
      refine ⟨_, hEvCO, by rw [hcO], rfl, ?_⟩
      cases b <;> rfl
    | ne =>
      let ⟨hcO, hEvCO⟩ := isFalseBoolConst_elim hRest
      refine ⟨_, hEvCO, by rw [hcO], rfl, ?_⟩
      cases b <;> rfl
    | eq =>
      let ⟨hcO, hEvCO⟩ := isTrueBoolConst_elim hRest
      refine ⟨_, hEvCO, by rw [hcO], rfl, ?_⟩
      cases b <;> rfl
    | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
    | mul | mulUnchecked | mulWithOverflow | div | rem | bitAnd | bitOr
    | shl | shlUnchecked | shr | shrUnchecked | lt | le | ge | gt | offset =>
      cases hRest
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases hSelf

/-! #### Pass 5 Double-Unary Involution (`Not(Not(x))` and `Neg(Neg(x))`) -/

private theorem evalUnOp_not_scalar_bits {w : IntWidth} {s : Bool} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    ∃ b₁ : BitVec 128,
      evalUnOp .not (.scalar ⟨w, s, b⟩) = .ok (.scalar ⟨w, s, b₁⟩) ∧
      truncateBits w b₁ = b₁ ∧
      b₁.toNat = (Nat.pow 2 w.bitWidth - 1) - b.toNat := by
  let M := Nat.pow 2 w.bitWidth
  have hLt : b.toNat < M := truncateBits_eq_iff.mp hWf
  let ⟨lossy, hTr, _, _⟩ := truncateScalar_eq w s (intNot (decodeScalar ⟨w, s, b⟩))
  let b₁ := truncateBits w (bvOfInt 128 (intNot (decodeScalar ⟨w, s, b⟩)))
  refine ⟨b₁, ?_, truncateBits_idem w _, ?_⟩
  · unfold evalUnOp; dsimp only; rw [hTr]
  · change (truncateBits w (bvOfInt 128 (intNot (decodeScalar ⟨w, s, b⟩)))).toNat =
      (M - 1) - b.toNat
    rw [toNat_truncateBits_bvOfInt]
    cases s with
    | false =>
      rw [decodeScalar_unsigned hWf]
      change (intEmod (Int.negSucc b.toNat) (Int.ofNat M)).toNat = (M - 1) - b.toNat
      rw [intEmod_negSucc, nat_mod_eq_of_lt hLt, int_subNatNat_of_le hLt]
      change M - (b.toNat + 1) = (M - 1) - b.toNat
      rw [Nat.add_comm b.toNat 1, ← Nat.sub_sub]
    | true =>
      rw [decodeScalar_signed hWf, signExtendBits_eq hLt]
      cases Nat.lt_or_ge (2 * b.toNat) M with
      | inl hCmp =>
        rw [ite_prop_true hCmp]
        change (intEmod (Int.negSucc b.toNat) (Int.ofNat M)).toNat = (M - 1) - b.toNat
        rw [intEmod_negSucc, nat_mod_eq_of_lt hLt, int_subNatNat_of_le hLt]
        change M - (b.toNat + 1) = (M - 1) - b.toNat
        rw [Nat.add_comm b.toNat 1, ← Nat.sub_sub]
      | inr hCmp =>
        rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
        change (intEmod (Int.ofNat ((M - 1) - b.toNat)) (Int.ofNat M)).toNat =
          (M - 1) - b.toNat
        rw [intEmod_ofNat]
        have hSubLt : (M - 1) - b.toNat < M :=
          Nat.lt_of_le_of_lt (Nat.sub_le (M - 1) b.toNat)
            (nat_sub_lt_of_pos_le Nat.zero_lt_one (pow2_bitWidth_pos w))
        exact nat_mod_eq_of_lt hSubLt

private theorem evalUnOp_neg_signed_bits {w : IntWidth} {b : BitVec 128}
    (hWf : truncateBits w b = b) :
    ∃ b₁ : BitVec 128,
      evalUnOp .neg (.scalar ⟨w, true, b⟩) = .ok (.scalar ⟨w, true, b₁⟩) ∧
      truncateBits w b₁ = b₁ ∧
      b₁.toNat = (if b.toNat = 0 then 0 else Nat.pow 2 w.bitWidth - b.toNat) := by
  let M := Nat.pow 2 w.bitWidth
  have hLt : b.toNat < M := truncateBits_eq_iff.mp hWf
  let ⟨lossy, hTr, _, _⟩ := truncateScalar_eq w true (Neg.neg (decodeScalar ⟨w, true, b⟩))
  let b₁ := truncateBits w (bvOfInt 128 (Neg.neg (decodeScalar ⟨w, true, b⟩)))
  refine ⟨b₁, ?_, truncateBits_idem w _, ?_⟩
  · unfold evalUnOp; dsimp; rw [hTr]
  · change (truncateBits w (bvOfInt 128 (Neg.neg (decodeScalar ⟨w, true, b⟩)))).toNat =
      if b.toNat = 0 then 0 else M - b.toNat
    rw [toNat_truncateBits_bvOfInt, decodeScalar_signed hWf, signExtendBits_eq hLt]
    cases hb : b.toNat with
    | zero =>
      rw [ite_prop_true rfl]
      have h2Z : 2 * 0 < M := pow2_bitWidth_pos w
      rw [ite_prop_true h2Z]
      change (intEmod (Int.ofNat 0) (Int.ofNat M)).toNat = 0
      rw [intEmod_ofNat, nat_zero_mod]
      rfl
    | succ k =>
      have hLtK : Nat.succ k < M := by rw [hb] at hLt; exact hLt
      have hNe0 : Nat.succ k ≠ 0 := fun hc => by cases hc
      rw [ite_prop_false hNe0]
      cases Nat.lt_or_ge (2 * Nat.succ k) M with
      | inl hCmp =>
        rw [ite_prop_true hCmp]
        change (intEmod (Int.negSucc k) (Int.ofNat M)).toNat = M - Nat.succ k
        have hKLtM : k < M := Nat.lt_trans (Nat.lt_succ_self k) hLtK
        rw [intEmod_negSucc, nat_mod_eq_of_lt hKLtM, int_subNatNat_of_le (Nat.le_of_lt hLtK)]
        rfl
      | inr hCmp =>
        rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
        change (intEmod (Int.ofNat (Nat.succ (M - 1 - Nat.succ k))) (Int.ofNat M)).toNat =
          M - Nat.succ k
        have hSuccEq : Nat.succ (M - 1 - Nat.succ k) = M - Nat.succ k :=
          (nat_sub_pos_eq_succ hLtK).symm
        rw [hSuccEq, intEmod_ofNat]
        have hSubLtM : M - Nat.succ k < M :=
          nat_sub_lt_of_pos_le (Nat.zero_lt_succ k) (Nat.le_of_lt hLtK)
        exact nat_mod_eq_of_lt hSubLtM

private theorem evalUnOp_involutive {op : UnOp} {xTy : MirTy} {vx : Val}
    (hValid : isValidInvolutiveUnOpTy op xTy = true)
    (hChk : checkVal vx xTy = true) :
    ∃ v1,
      evalUnOp op vx = .ok v1 ∧
      checkVal v1 xTy = true ∧
      evalUnOp op v1 = .ok vx := by
  cases op with
  | ptrMetadata => cases xTy <;> cases hValid
  | not =>
    cases xTy with
    | bool =>
      let ⟨b, hvx⟩ := checkVal_bool_iff.mp hChk; subst hvx
      refine ⟨.bool (!b), rfl, rfl, ?_⟩
      cases b <;> rfl
    | int w s =>
      let ⟨b, hvx, hWf⟩ := checkVal_int_iff.mp hChk; subst hvx
      let M := Nat.pow 2 w.bitWidth
      have hLt : b.toNat < M := truncateBits_eq_iff.mp hWf
      let ⟨b₁, hEv1, hWf1, hToNat1⟩ := evalUnOp_not_scalar_bits (s := s) hWf
      let ⟨b₂, hEv2, _, hToNat2⟩ := evalUnOp_not_scalar_bits (s := s) hWf1
      have hLePred : b.toNat ≤ M - 1 := nat_le_pred_of_lt hLt
      have hb₂Eq : b₂ = b := by
        apply bitvec_eq_of_toNat_eq
        rw [hToNat2, hToNat1]
        exact nat_sub_sub_self hLePred
      subst hb₂Eq
      exact ⟨.scalar ⟨w, s, b₁⟩, hEv1, checkVal_int_iff.mpr ⟨b₁, rfl, hWf1⟩, hEv2⟩
    | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
      cases hValid
  | neg =>
    cases xTy with
    | int w s =>
      cases s with
      | false => cases hValid
      | true =>
        let ⟨b, hvx, hWf⟩ := checkVal_int_iff.mp hChk; subst hvx
        let M := Nat.pow 2 w.bitWidth
        have hLt : b.toNat < M := truncateBits_eq_iff.mp hWf
        let ⟨b₁, hEv1, hWf1, hToNat1⟩ := evalUnOp_neg_signed_bits hWf
        let ⟨b₂, hEv2, _, hToNat2⟩ := evalUnOp_neg_signed_bits hWf1
        have hb₂Eq : b₂ = b := by
          apply bitvec_eq_of_toNat_eq
          rw [hToNat2, hToNat1]
          cases hb0 : b.toNat with
          | zero =>
            rw [ite_prop_true rfl, ite_prop_true rfl]
          | succ k =>
            have hLtK : Nat.succ k < M := by rw [hb0] at hLt; exact hLt
            have hNe0 : Nat.succ k ≠ 0 := fun hc => by cases hc
            rw [ite_prop_false hNe0]
            have hSubNe0 : M - Nat.succ k ≠ 0 := by
              intro hZ
              exact Nat.not_le_of_gt hLtK (Nat.le_of_sub_eq_zero hZ)
            rw [ite_prop_false hSubNe0]
            exact nat_sub_sub_self (Nat.le_of_lt hLtK)
        subst hb₂Eq
        exact ⟨.scalar ⟨w, true, b₁⟩, hEv1, checkVal_int_iff.mpr ⟨b₁, rfl, hWf1⟩, hEv2⟩
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
      cases hValid

/-! ### Stage 4 Private Helpers — Layer D: Unconditional Bidirectional Passes
1, 2, & 5 -/

private theorem evalOperandToSlot_staticTy {bodyLocals : List MirTy} {locals : List LocalSlot}
    {opnd : Operand} {expectedTy srcTy : MirTy} {optVal : Option Val} {locals' : List LocalSlot}
    (hStatic : operandStaticTy? bodyLocals opnd = some expectedTy)
    (hEv : evalOperandToSlot bodyLocals locals opnd = .ok (srcTy, optVal, locals')) :
    srcTy = expectedTy := by
  cases opnd with
  | constant c =>
    unfold operandStaticTy? at hStatic
    injection hStatic with hCEq
    unfold evalOperandToSlot at hEv; dsimp at hEv
    cases hLit : evalConstLit c.ty c.lit with
    | error _ => rw [hLit] at hEv; cases hEv
    | ok v =>
      rw [hLit] at hEv
      injection hEv with hTup
      injection hTup with hSrcEq _
      exact hSrcEq.symm.trans hCEq
  | copy p =>
    dsimp [operandStaticTy?] at hStatic
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hStatic; cases hStatic
    | true =>
      rw [hProj] at hStatic; dsimp at hStatic
      dsimp [evalOperandToSlot] at hEv
      rw [hProj] at hEv; dsimp at hEv
      rw [hStatic] at hEv
      cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
      | none => rw [hSl] at hEv; cases hEv
      | some sl =>
        rw [hSl] at hEv
        cases sl with
        | dead => cases hEv
        | live o =>
          injection hEv with hTup
          injection hTup with hSrcEq _
          exact hSrcEq.symm
  | move p =>
    dsimp [operandStaticTy?] at hStatic
    cases hProj : p.projection.isEmpty with
    | false => rw [hProj] at hStatic; cases hStatic
    | true =>
      rw [hProj] at hStatic; dsimp at hStatic
      dsimp [evalOperandToSlot] at hEv
      rw [hProj] at hEv; dsimp at hEv
      rw [hStatic] at hEv
      cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
      | none => rw [hSl] at hEv; cases hEv
      | some sl =>
        rw [hSl] at hEv
        cases sl with
        | dead => cases hEv
        | live o =>
          dsimp at hEv
          cases hSet : setElem? locals p.localId (liveUninitSlot expectedTy) with
          | none => rw [hSet] at hEv; cases hEv
          | some locs1 =>
            rw [hSet] at hEv
            injection hEv with hTup
            injection hTup with hSrcEq _
            exact hSrcEq.symm

private theorem evalStatement_eq_of_same {b₁ b₂ : Body} (frame : FrameState)
    (cm : CallerMemory) (s : StatementKind) (hLoc : b₁.locals = b₂.locals) :
    evalStatement b₁ frame cm s = evalStatement b₂ frame cm s := by
  unfold evalStatement
  cases s with
  | nop | storageDead _ | unsupported => rfl
  | storageLive id => dsimp only; rw [hLoc]
  | assign dst rv => dsimp only; rw [hLoc]

/-! #### Theorem 1: `BoolCmpSimplify` (`InstSimplify::simplify_bool_cmp`) -/

private theorem isBoolCmpSimplifyStmt_assignOnly (locs : List MirTy)
    (s₁ s₂ : StatementKind) (h : isBoolCmpSimplifyStmt locs s₁ s₂ = true) :
    s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂) := by
  unfold isBoolCmpSimplifyStmt at h
  cases bool_or_true h with
  | inr hEq => exact Or.inl (stmtEq_eq hEq)
  | inl hRw =>
    cases s₁ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hRw
    | assign d₁ rv₁ =>
      cases rv₁ with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
      | aggregateTuple _ | unsupported => cases hRw
      | binaryOp op lhs rhs =>
        cases s₂ with
        | nop | storageLive _ | storageDead _ | unsupported => cases hRw
        | assign d₂ rv₂ => exact Or.inr ⟨d₁, .binaryOp op lhs rhs, d₂, rv₂, rfl, rfl⟩

private theorem isPrimitiveReadableTy_bool : isPrimitiveReadableTy .bool = true := rfl

private theorem evalRvalue_matchesBoolCmpArm_left {bodyLocals : List MirTy}
    {locals : List LocalSlot} {op : BinOp} {c : ConstOperand}
    {opnd : Operand} {rvTgt : Rvalue}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hArm : matchesBoolCmpArm bodyLocals op c opnd rvTgt = true) :
    evalRvalue bodyLocals locals .bool (.binaryOp op (.constant c) opnd) =
      evalRvalue bodyLocals locals .bool rvTgt := by
  unfold matchesBoolCmpArm at hArm
  cases hSt : operandStaticTy? bodyLocals opnd with
  | none => rw [hSt] at hArm; cases hArm
  | some opTy =>
    rw [hSt] at hArm
    cases opTy with
    | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
      cases hArm
    | bool =>
      dsimp only at hArm
      cases hId : ((binOpEq op .eq && isTrueBoolConst c) ||
          (binOpEq op .ne && isFalseBoolConst c)) with
      | true =>
        rw [hId, if_bool_true rfl] at hArm
        have hRv := rvalueEq_eq hArm; subst hRv
        cases bool_or_true hId with
        | inl hEqT =>
          let ⟨hOp, hCT⟩ := bool_and_true hEqT
          have hOpEq := binOpEq_eq hOp; subst hOpEq
          let ⟨hcEq, hEvC⟩ := isTrueBoolConst_elim hCT
          have hPrimC : isPrimitiveReadableTy c.ty = true := by rw [hcEq]; rfl
          unfold evalRvalue evalPrimitiveOperand
          dsimp
          have hSlotC : evalOperandToSlot bodyLocals locals (.constant c) =
              .ok (c.ty, some (.bool true), locals) := by
            dsimp [evalOperandToSlot]; rw [hEvC]
          rw [hSlotC]; dsimp; rw [hPrimC]; dsimp
          cases hEvOp : evalOperandToSlot bodyLocals locals opnd with
          | error k => rfl
          | ok tup =>
            cases tup with
            | mk srcTy rest =>
              cases rest with
              | mk optVal locals₁ =>
                have hSrcB := evalOperandToSlot_staticTy hSt hEvOp
                subst hSrcB
                dsimp [isPrimitiveReadableTy_bool, mirTy_beq_refl]
                cases optVal with
                | none => rfl
                | some v =>
                  have hChk := (evalOperandToSlot_preserves_wt hWt hEvOp).2 v rfl
                  let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
                  cases b <;> rfl
        | inr hNeF =>
          let ⟨hOp, hCF⟩ := bool_and_true hNeF
          have hOpEq := binOpEq_eq hOp; subst hOpEq
          let ⟨hcEq, hEvC⟩ := isFalseBoolConst_elim hCF
          have hPrimC : isPrimitiveReadableTy c.ty = true := by rw [hcEq]; rfl
          unfold evalRvalue evalPrimitiveOperand
          dsimp
          have hSlotC : evalOperandToSlot bodyLocals locals (.constant c) =
              .ok (c.ty, some (.bool false), locals) := by
            dsimp [evalOperandToSlot]; rw [hEvC]
          rw [hSlotC]; dsimp; rw [hPrimC]; dsimp
          cases hEvOp : evalOperandToSlot bodyLocals locals opnd with
          | error k => rfl
          | ok tup =>
            cases tup with
            | mk srcTy rest =>
              cases rest with
              | mk optVal locals₁ =>
                have hSrcB := evalOperandToSlot_staticTy hSt hEvOp
                subst hSrcB
                dsimp [isPrimitiveReadableTy_bool, mirTy_beq_refl]
                cases optVal with
                | none => rfl
                | some v =>
                  have hChk := (evalOperandToSlot_preserves_wt hWt hEvOp).2 v rfl
                  let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
                  cases b <;> rfl
      | false =>
        rw [hId, if_bool_false rfl] at hArm
        cases hNeg : ((binOpEq op .eq && isFalseBoolConst c) ||
            (binOpEq op .ne && isTrueBoolConst c)) with
        | false => rw [hNeg] at hArm; cases hArm
        | true =>
          rw [hNeg, if_bool_true rfl] at hArm
          have hRv := rvalueEq_eq hArm; subst hRv
          cases bool_or_true hNeg with
          | inl hEqF =>
            let ⟨hOp, hCF⟩ := bool_and_true hEqF
            have hOpEq := binOpEq_eq hOp; subst hOpEq
            let ⟨hcEq, hEvC⟩ := isFalseBoolConst_elim hCF
            have hPrimC : isPrimitiveReadableTy c.ty = true := by rw [hcEq]; rfl
            unfold evalRvalue evalPrimitiveOperand
            dsimp
            have hSlotC : evalOperandToSlot bodyLocals locals (.constant c) =
                .ok (c.ty, some (.bool false), locals) := by
              unfold evalOperandToSlot; dsimp; rw [hEvC]
            rw [hSlotC]; dsimp; rw [hPrimC]; dsimp
            cases hEvOp : evalOperandToSlot bodyLocals locals opnd with
            | error k => rfl
            | ok tup =>
              cases tup with
              | mk srcTy rest =>
                cases rest with
                | mk optVal locals₁ =>
                  have hSrcB := evalOperandToSlot_staticTy hSt hEvOp
                  subst hSrcB
                  dsimp [isPrimitiveReadableTy_bool, mirTy_beq_refl]
                  cases optVal with
                  | none => rfl
                  | some v =>
                    have hChk := (evalOperandToSlot_preserves_wt hWt hEvOp).2 v rfl
                    let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
                    cases b <;> rfl
          | inr hNeT =>
            let ⟨hOp, hCT⟩ := bool_and_true hNeT
            have hOpEq := binOpEq_eq hOp; subst hOpEq
            let ⟨hcEq, hEvC⟩ := isTrueBoolConst_elim hCT
            have hPrimC : isPrimitiveReadableTy c.ty = true := by rw [hcEq]; rfl
            unfold evalRvalue evalPrimitiveOperand
            dsimp
            have hSlotC : evalOperandToSlot bodyLocals locals (.constant c) =
                .ok (c.ty, some (.bool true), locals) := by
              unfold evalOperandToSlot; dsimp; rw [hEvC]
            rw [hSlotC]; dsimp; rw [hPrimC]; dsimp
            cases hEvOp : evalOperandToSlot bodyLocals locals opnd with
            | error k => rfl
            | ok tup =>
              cases tup with
              | mk srcTy rest =>
                cases rest with
                | mk optVal locals₁ =>
                  have hSrcB := evalOperandToSlot_staticTy hSt hEvOp
                  subst hSrcB
                  dsimp [isPrimitiveReadableTy_bool, mirTy_beq_refl]
                  cases optVal with
                  | none => rfl
                  | some v =>
                    have hChk := (evalOperandToSlot_preserves_wt hWt hEvOp).2 v rfl
                    let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
                    cases b <;> rfl

private theorem evalRvalue_matchesBoolCmpArm_right {bodyLocals : List MirTy}
    {locals : List LocalSlot} {op : BinOp} {c : ConstOperand}
    {opnd : Operand} {rvTgt : Rvalue}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hArm : matchesBoolCmpArm bodyLocals op c opnd rvTgt = true) :
    evalRvalue bodyLocals locals .bool (.binaryOp op opnd (.constant c)) =
      evalRvalue bodyLocals locals .bool rvTgt := by
  unfold matchesBoolCmpArm at hArm
  cases hSt : operandStaticTy? bodyLocals opnd with
  | none => rw [hSt] at hArm; cases hArm
  | some opTy =>
    rw [hSt] at hArm
    cases opTy with
    | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
      cases hArm
    | bool =>
      dsimp only at hArm
      cases hId : ((binOpEq op .eq && isTrueBoolConst c) ||
          (binOpEq op .ne && isFalseBoolConst c)) with
      | true =>
        rw [hId, if_bool_true rfl] at hArm
        have hRv := rvalueEq_eq hArm; subst hRv
        cases bool_or_true hId with
        | inl hEqT =>
          let ⟨hOp, hCT⟩ := bool_and_true hEqT
          have hOpEq := binOpEq_eq hOp; subst hOpEq
          let ⟨hcEq, _⟩ := isTrueBoolConst_elim hCT; subst hcEq
          unfold evalRvalue evalPrimitiveOperand
          dsimp only
          cases hEvOp : evalOperandToSlot bodyLocals locals opnd with
          | error k => rfl
          | ok tup =>
            cases tup with
            | mk srcTy rest =>
              cases rest with
              | mk optVal locals₁ =>
                have hSrcB := evalOperandToSlot_staticTy hSt hEvOp
                subst hSrcB
                dsimp [isPrimitiveReadableTy_bool, mirTy_beq_refl]
                cases optVal with
                | none => rfl
                | some v =>
                  have hChk := (evalOperandToSlot_preserves_wt hWt hEvOp).2 v rfl
                  let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
                  cases b <;> rfl
        | inr hNeF =>
          let ⟨hOp, hCF⟩ := bool_and_true hNeF
          have hOpEq := binOpEq_eq hOp; subst hOpEq
          let ⟨hcEq, _⟩ := isFalseBoolConst_elim hCF; subst hcEq
          unfold evalRvalue evalPrimitiveOperand
          dsimp only
          cases hEvOp : evalOperandToSlot bodyLocals locals opnd with
          | error k => rfl
          | ok tup =>
            cases tup with
            | mk srcTy rest =>
              cases rest with
              | mk optVal locals₁ =>
                have hSrcB := evalOperandToSlot_staticTy hSt hEvOp
                subst hSrcB
                dsimp [isPrimitiveReadableTy_bool, mirTy_beq_refl]
                cases optVal with
                | none => rfl
                | some v =>
                  have hChk := (evalOperandToSlot_preserves_wt hWt hEvOp).2 v rfl
                  let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
                  cases b <;> rfl
      | false =>
        rw [hId, if_bool_false rfl] at hArm
        cases hNeg : ((binOpEq op .eq && isFalseBoolConst c) ||
            (binOpEq op .ne && isTrueBoolConst c)) with
        | false => rw [hNeg] at hArm; cases hArm
        | true =>
          rw [hNeg, if_bool_true rfl] at hArm
          have hRv := rvalueEq_eq hArm; subst hRv
          cases bool_or_true hNeg with
          | inl hEqF =>
            let ⟨hOp, hCF⟩ := bool_and_true hEqF
            have hOpEq := binOpEq_eq hOp; subst hOpEq
            let ⟨hcEq, _⟩ := isFalseBoolConst_elim hCF; subst hcEq
            unfold evalRvalue evalPrimitiveOperand
            dsimp only
            cases hEvOp : evalOperandToSlot bodyLocals locals opnd with
            | error k => rfl
            | ok tup =>
              cases tup with
              | mk srcTy rest =>
                cases rest with
                | mk optVal locals₁ =>
                  have hSrcB := evalOperandToSlot_staticTy hSt hEvOp
                  subst hSrcB
                  dsimp [isPrimitiveReadableTy_bool, mirTy_beq_refl]
                  cases optVal with
                  | none => rfl
                  | some v =>
                    have hChk := (evalOperandToSlot_preserves_wt hWt hEvOp).2 v rfl
                    let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
                    cases b <;> rfl
          | inr hNeT =>
            let ⟨hOp, hCT⟩ := bool_and_true hNeT
            have hOpEq := binOpEq_eq hOp; subst hOpEq
            let ⟨hcEq, _⟩ := isTrueBoolConst_elim hCT; subst hcEq
            unfold evalRvalue evalPrimitiveOperand
            dsimp only
            cases hEvOp : evalOperandToSlot bodyLocals locals opnd with
            | error k => rfl
            | ok tup =>
              cases tup with
              | mk srcTy rest =>
                cases rest with
                | mk optVal locals₁ =>
                  have hSrcB := evalOperandToSlot_staticTy hSt hEvOp
                  subst hSrcB
                  dsimp [isPrimitiveReadableTy_bool, mirTy_beq_refl]
                  cases optVal with
                  | none => rfl
                  | some v =>
                    have hChk := (evalOperandToSlot_preserves_wt hWt hEvOp).2 v rfl
                    let ⟨b, hv⟩ := checkVal_bool_iff.mp hChk; subst hv
                    cases b <;> rfl

private theorem evalStatement_boolCmpSimplify (b₁ b₂ : Body) (frame : FrameState)
    (cm : CallerMemory) (s₁ s₂ : StatementKind)
    (hLoc : b₁.locals = b₂.locals)
    (hWt : LocalsWellTyped b₁.locals frame.locals)
    (hRel : isBoolCmpSimplifyStmt b₁.locals s₁ s₂ = true) :
    evalStatement b₁ frame cm s₁ = evalStatement b₂ frame cm s₂ := by
  unfold isBoolCmpSimplifyStmt at hRel
  cases bool_or_true hRel with
  | inr hEq =>
    rw [stmtEq_eq hEq]
    exact evalStatement_eq_of_same frame cm s₂ hLoc
  | inl hRw =>
    cases s₁ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hRw
    | assign dst rvSrc =>
      cases rvSrc with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
      | aggregateTuple _ | unsupported => cases hRw
      | binaryOp op lhs rhs =>
        cases s₂ with
        | nop | storageLive _ | storageDead _ | unsupported => cases hRw
        | assign dst' rvTgt =>
          unfold isBoolCmpSimplifyRewrite at hRw
          let ⟨h123, hArms⟩ := bool_and_true hRw
          let ⟨h12, hDstBool⟩ := bool_and_true h123
          let ⟨hDstEq, hDstEmpty⟩ := bool_and_true h12
          have hDEq := placeEq_eq hDstEq; subst hDEq
          cases hDstTy : Trusted.MirSemantics.getElem? b₁.locals dst.localId with
          | none => rw [hDstTy] at hDstBool; cases hDstBool
          | some dTy =>
            rw [hDstTy] at hDstBool
            cases dTy with
            | int _ _ | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
              cases hDstBool
            | bool =>
              unfold evalStatement
              dsimp only
              rw [← hLoc, hDstEmpty, hDstTy]
              dsimp only
              cases bool_or_true hArms with
              | inl hL =>
                cases lhs with
                | copy _ | move _ => cases hL
                | constant c =>
                  rw [evalRvalue_matchesBoolCmpArm_left hWt hL]
              | inr hR =>
                cases rhs with
                | copy _ | move _ => cases hR
                | constant c =>
                  rw [evalRvalue_matchesBoolCmpArm_right hWt hR]

private theorem isBoolCmpSimplifyProgram_to_generic {pSrc pTgt : Program}
    (h : isBoolCmpSimplifyProgram pSrc pTgt = true) :
    genericProgRel isBoolCmpSimplifyStmt pSrc pTgt = true := by
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  refine bool_and_intro hHdr ?_
  refine listRel_mono (fun b₁ b₂ hb => ?_) hBodies
  let ⟨hBHdr, hBBs⟩ := bool_and_true hb
  exact bool_and_intro hBHdr (listRel_mono (fun _ _ hbb => hbb) hBBs)

private theorem boolCmpSimplify_bidirectional_iff_priv
    (pSrc pTgt : Program)
    (hRel : isBoolCmpSimplifyProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt :=
  fullSemanticEquiv_of_stmtRel_lockstep
    isBoolCmpSimplifyStmt_assignOnly
    evalStatement_boolCmpSimplify
    (isBoolCmpSimplifyProgram_to_generic hRel)

/-! #### Theorem 2: `NeutralIdentity` (`GVN::simplify_binary_inner`) -/

private theorem isNeutralIdentityStmt_assignOnly (locs : List MirTy)
    (s₁ s₂ : StatementKind) (h : isNeutralIdentityStmt locs s₁ s₂ = true) :
    s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂) := by
  unfold isNeutralIdentityStmt at h
  cases bool_or_true h with
  | inr hEq => exact Or.inl (stmtEq_eq hEq)
  | inl hRw =>
    cases s₁ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hRw
    | assign d₁ rv₁ =>
      cases rv₁ with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
      | aggregateTuple _ | unsupported => cases hRw
      | binaryOp op lhs rhs =>
        cases s₂ with
        | nop | storageLive _ | storageDead _ | unsupported => cases hRw
        | assign d₂ rv₂ => exact Or.inr ⟨d₁, .binaryOp op lhs rhs, d₂, rv₂, rfl, rfl⟩

private theorem checkVal_dummy_of_leftNeutral {dstTy : MirTy} {op : BinOp} {c : ConstOperand}
    (h : isLeftNeutralConstFor dstTy op c = true) :
    ∃ v₀, checkVal v₀ dstTy = true := by
  cases dstTy with
  | int w s =>
    exact ⟨.scalar ⟨w, s, BitVec.ofNat 128 0⟩,
      checkVal_int_iff.mpr ⟨BitVec.ofNat 128 0, rfl, truncateBits_zero w⟩⟩
  | bool => exact ⟨.bool false, rfl⟩
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h

private theorem checkVal_dummy_of_rightNeutral {dstTy : MirTy} {op : BinOp} {c : ConstOperand}
    (h : isRightNeutralConstFor dstTy op c = true) :
    ∃ v₀, checkVal v₀ dstTy = true := by
  cases dstTy with
  | int w s =>
    exact ⟨.scalar ⟨w, s, BitVec.ofNat 128 0⟩,
      checkVal_int_iff.mpr ⟨BitVec.ofNat 128 0, rfl, truncateBits_zero w⟩⟩
  | bool => exact ⟨.bool false, rfl⟩
  | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h

private theorem evalRvalue_leftNeutral {bodyLocals : List MirTy} {locals : List LocalSlot}
    {dstTy rhsTy : MirTy} {op : BinOp} {c : ConstOperand} {rhs : Operand}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hSt : operandStaticTy? bodyLocals rhs = some rhsTy)
    (hTyEq : MirTy.beq rhsTy dstTy = true)
    (hNeutral : isLeftNeutralConstFor dstTy op c = true) :
    evalRvalue bodyLocals locals dstTy (.binaryOp op (.constant c) rhs) =
      evalRvalue bodyLocals locals dstTy (.use rhs) := by
  have hRhsEq := mirTy_beq_eq hTyEq; subst hRhsEq
  let ⟨v₀, hChk0⟩ := checkVal_dummy_of_leftNeutral hNeutral
  let ⟨vc, hEvC, hPrimC, hPrimDst, _⟩ := evalBinOp_leftNeutral hNeutral hChk0
  unfold evalRvalue evalPrimitiveOperand
  dsimp only
  have hSlotC : evalOperandToSlot bodyLocals locals (.constant c) =
      .ok (c.ty, some vc, locals) := by
    unfold evalOperandToSlot; dsimp; rw [hEvC]
  rw [hSlotC]; dsimp; rw [hPrimC]; dsimp
  cases hEvR : evalOperandToSlot bodyLocals locals rhs with
  | error k => rfl
  | ok tup =>
    cases tup with
    | mk srcTy rest =>
      cases rest with
      | mk optVal locals₁ =>
        have hSrcEq := evalOperandToSlot_staticTy hSt hEvR
        subst hSrcEq
        dsimp only
        rw [hPrimDst, mirTy_beq_refl srcTy]
        dsimp
        cases optVal with
        | none => rfl
        | some v =>
          dsimp only
          have hChkV := (evalOperandToSlot_preserves_wt hWt hEvR).2 v rfl
          let ⟨vc', hEvC', _, _, hBin⟩ := evalBinOp_leftNeutral hNeutral hChkV
          rw [hEvC] at hEvC'
          injection hEvC' with hVcEq; subst hVcEq
          rw [hBin]

private theorem evalRvalue_rightNeutral {bodyLocals : List MirTy} {locals : List LocalSlot}
    {dstTy lhsTy : MirTy} {op : BinOp} {c : ConstOperand} {lhs : Operand}
    (hWt : LocalsWellTyped bodyLocals locals)
    (hSt : operandStaticTy? bodyLocals lhs = some lhsTy)
    (hTyEq : MirTy.beq lhsTy dstTy = true)
    (hNeutral : isRightNeutralConstFor dstTy op c = true) :
    evalRvalue bodyLocals locals dstTy (.binaryOp op lhs (.constant c)) =
      evalRvalue bodyLocals locals dstTy (.use lhs) := by
  have hLhsEq := mirTy_beq_eq hTyEq; subst hLhsEq
  let ⟨v₀, hChk0⟩ := checkVal_dummy_of_rightNeutral hNeutral
  let ⟨vc, hEvC, hPrimC, hPrimDst, _⟩ := evalBinOp_rightNeutral hNeutral hChk0
  unfold evalRvalue evalPrimitiveOperand
  dsimp only
  cases hEvL : evalOperandToSlot bodyLocals locals lhs with
  | error k => rfl
  | ok tup =>
    cases tup with
    | mk srcTy rest =>
      cases rest with
      | mk optVal locals₁ =>
        have hSrcEq := evalOperandToSlot_staticTy hSt hEvL
        subst hSrcEq
        dsimp only
        rw [hPrimDst, mirTy_beq_refl srcTy]
        dsimp
        cases optVal with
        | none => rfl
        | some v =>
          dsimp only
          have hSlotC : evalOperandToSlot bodyLocals locals₁ (.constant c) =
              .ok (c.ty, some vc, locals₁) := by
            unfold evalOperandToSlot; dsimp; rw [hEvC]
          rw [hSlotC]; dsimp; rw [hPrimC]; dsimp
          have hChkV := (evalOperandToSlot_preserves_wt hWt hEvL).2 v rfl
          let ⟨vc', hEvC', _, _, hBin⟩ := evalBinOp_rightNeutral hNeutral hChkV
          rw [hEvC] at hEvC'
          injection hEvC' with hVcEq; subst hVcEq
          rw [hBin]

private theorem evalStatement_neutralIdentity (b₁ b₂ : Body) (frame : FrameState)
    (cm : CallerMemory) (s₁ s₂ : StatementKind)
    (hLoc : b₁.locals = b₂.locals)
    (hWt : LocalsWellTyped b₁.locals frame.locals)
    (hRel : isNeutralIdentityStmt b₁.locals s₁ s₂ = true) :
    evalStatement b₁ frame cm s₁ = evalStatement b₂ frame cm s₂ := by
  unfold isNeutralIdentityStmt at hRel
  cases bool_or_true hRel with
  | inr hEq =>
    rw [stmtEq_eq hEq]
    exact evalStatement_eq_of_same frame cm s₂ hLoc
  | inl hRw =>
    cases s₁ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hRw
    | assign dst rvSrc =>
      cases rvSrc with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
      | aggregateTuple _ | unsupported => cases hRw
      | binaryOp op lhs rhs =>
        cases s₂ with
        | nop | storageLive _ | storageDead _ | unsupported => cases hRw
        | assign dst' rvTgt =>
          cases rvTgt with
          | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
          | aggregateTuple _ | unsupported => cases hRw
          | use opndTgt =>
            unfold isNeutralIdentityRewrite at hRw
            let ⟨h12, hRest⟩ := bool_and_true hRw
            let ⟨hDstEq, hDstEmpty⟩ := bool_and_true h12
            have hDEq := placeEq_eq hDstEq; subst hDEq
            cases hDstTy : Trusted.MirSemantics.getElem? b₁.locals dst.localId with
            | none => rw [hDstTy] at hRest; cases hRest
            | some dstTy =>
              rw [hDstTy] at hRest
              unfold evalStatement; dsimp only
              rw [← hLoc, hDstEmpty, hDstTy]; dsimp only
              cases bool_or_true hRest with
              | inl hLeft =>
                cases lhs with
                | copy _ | move _ => cases hLeft
                | constant c =>
                  cases hStR : operandStaticTy? b₁.locals rhs with
                  | none => rw [hStR] at hLeft; cases hLeft
                  | some rhsTy =>
                    rw [hStR] at hLeft
                    let ⟨h12L, hOpEq⟩ := bool_and_true hLeft
                    let ⟨hTyEq, hNeut⟩ := bool_and_true h12L
                    rw [← operandEq_eq hOpEq]
                    rw [evalRvalue_leftNeutral hWt hStR hTyEq hNeut]
              | inr hRight =>
                cases rhs with
                | copy _ | move _ => cases hRight
                | constant c =>
                  cases hStL : operandStaticTy? b₁.locals lhs with
                  | none => rw [hStL] at hRight; cases hRight
                  | some lhsTy =>
                    rw [hStL] at hRight
                    let ⟨h12R, hOpEq⟩ := bool_and_true hRight
                    let ⟨hTyEq, hNeut⟩ := bool_and_true h12R
                    rw [← operandEq_eq hOpEq]
                    rw [evalRvalue_rightNeutral hWt hStL hTyEq hNeut]

private theorem isNeutralIdentityProgram_to_generic {pSrc pTgt : Program}
    (h : isNeutralIdentityProgram pSrc pTgt = true) :
    genericProgRel isNeutralIdentityStmt pSrc pTgt = true := by
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  refine bool_and_intro hHdr ?_
  refine listRel_mono (fun b₁ b₂ hb => ?_) hBodies
  let ⟨hBHdr, hBBs⟩ := bool_and_true hb
  exact bool_and_intro hBHdr (listRel_mono (fun _ _ hbb => hbb) hBBs)

private theorem neutralIdentity_bidirectional_iff_priv
    (pSrc pTgt : Program)
    (hRel : isNeutralIdentityProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt :=
  fullSemanticEquiv_of_stmtRel_lockstep
    isNeutralIdentityStmt_assignOnly
    evalStatement_neutralIdentity
    (isNeutralIdentityProgram_to_generic hRel)

/-! #### Theorem 5: `DoubleUnaryChain` (`GVN::simplify_unary`) -/

private theorem isDoubleUnaryPair_elim {bodyLocals : List MirTy}
    {s₁ s₂ t₁ t₂ : StatementKind}
    (h : isDoubleUnaryPair bodyLocals s₁ s₂ t₁ t₂ = true) :
    ∃ (tmp dst x : Place) (op : UnOp) (xTy : MirTy),
      s₁ = .assign tmp (.unaryOp op (.copy x)) ∧
      t₁ = .assign tmp (.unaryOp op (.copy x)) ∧
      s₂ = .assign dst (.unaryOp op (.copy tmp)) ∧
      t₂ = .assign dst (.use (.copy x)) ∧
      x.projection.isEmpty = true ∧
      tmp.projection.isEmpty = true ∧
      dst.projection.isEmpty = true ∧
      tmp.localId ≠ x.localId ∧
      Trusted.MirSemantics.getElem? bodyLocals x.localId = some xTy ∧
      Trusted.MirSemantics.getElem? bodyLocals tmp.localId = some xTy ∧
      Trusted.MirSemantics.getElem? bodyLocals dst.localId = some xTy ∧
      isValidInvolutiveUnOpTy op xTy = true := by
  unfold isDoubleUnaryPair at h
  let ⟨hSt1, hMatch⟩ := bool_and_true h
  have hEq1 := stmtEq_eq hSt1
  cases s₁ with
  | nop | storageLive _ | storageDead _ | unsupported => cases hMatch
  | assign tmp rv1 =>
    cases rv1 with
    | use _ | binaryOp _ _ _ | discriminant _ | ref _ _ | addressOf _ _
    | aggregateTuple _ | unsupported => cases hMatch
    | unaryOp op₁ opnd1 =>
      cases opnd1 with
      | move _ | constant _ => cases hMatch
      | copy x =>
        cases s₂ with
        | nop | storageLive _ | storageDead _ | unsupported => cases hMatch
        | assign dst rv2 =>
          cases rv2 with
          | use _ | binaryOp _ _ _ | discriminant _ | ref _ _ | addressOf _ _
          | aggregateTuple _ | unsupported => cases hMatch
          | unaryOp op₂ opnd2 =>
            cases opnd2 with
            | move _ | constant _ => cases hMatch
            | copy tmp' =>
              cases t₂ with
              | nop | storageLive _ | storageDead _ | unsupported => cases hMatch
              | assign dst' rvt2 =>
                cases rvt2 with
                | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
                | aggregateTuple _ | unsupported => cases hMatch
                | use opndt2 =>
                  cases opndt2 with
                  | move _ | constant _ => cases hMatch
                  | copy x' =>
                    dsimp only at hMatch
                    let ⟨hPre, hTypes⟩ := bool_and_true hMatch
                    let ⟨hPre7, hNeBeq⟩ := bool_and_true hPre
                    let ⟨hPre6, hDstEmp⟩ := bool_and_true hPre7
                    let ⟨hPre5, hTmpEmp⟩ := bool_and_true hPre6
                    let ⟨hPre4, hXEmp⟩ := bool_and_true hPre5
                    let ⟨hPre3, hXEq⟩ := bool_and_true hPre4
                    let ⟨hPre2, hDstEq⟩ := bool_and_true hPre3
                    let ⟨hOpEq, hTmpEq⟩ := bool_and_true hPre2
                    have hOp := unOpEq_eq hOpEq; subst hOp
                    have hTmp := placeEq_eq hTmpEq; subst hTmp
                    have hDst := placeEq_eq hDstEq; subst hDst
                    have hX := placeEq_eq hXEq; subst hX
                    have hNe : tmp.localId ≠ x.localId :=
                      nat_ne_of_beq_false (bool_not_true hNeBeq)
                    cases hTx : Trusted.MirSemantics.getElem? bodyLocals x.localId with
                    | none => rw [hTx] at hTypes; cases hTypes
                    | some xTy =>
                      rw [hTx] at hTypes
                      cases hTt : Trusted.MirSemantics.getElem? bodyLocals tmp.localId with
                      | none => rw [hTt] at hTypes; cases hTypes
                      | some tmpTy =>
                        rw [hTt] at hTypes
                        cases hTd : Trusted.MirSemantics.getElem? bodyLocals dst.localId with
                        | none => rw [hTd] at hTypes; cases hTypes
                        | some dstTy =>
                          rw [hTd] at hTypes
                          let ⟨h12T, hDstTyEq⟩ := bool_and_true hTypes
                          let ⟨hValOp, hTmpTyEq⟩ := bool_and_true h12T
                          have hTmpTy := mirTy_beq_eq hTmpTyEq; subst hTmpTy
                          have hDstTy := mirTy_beq_eq hDstTyEq; subst hDstTy
                          exact ⟨tmp, dst, x, op₁, xTy, rfl, hEq1.symm, rfl, rfl,
                                 hXEmp, hTmpEmp, hDstEmp, hNe, hTx, hTt, hTd, hValOp⟩

private theorem isPrimitiveReadable_of_involutive {op : UnOp} {ty : MirTy}
    (h : isValidInvolutiveUnOpTy op ty = true) :
    isPrimitiveReadableTy ty = true := by
  cases op with
  | ptrMetadata => cases ty <;> cases h
  | not =>
    cases ty with
    | bool | int _ _ => rfl
    | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h
  | neg =>
    cases ty with
    | int _ s => cases s <;> first | rfl | cases h
    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h

private theorem isDoubleUnaryChainStmts_props_fueled (bodyLocals : List MirTy) (fuel : Nat) :
    ∀ ss ts, ss.length ≤ fuel →
      isDoubleUnaryChainStmts bodyLocals ss ts = true →
      ss.length = ts.length ∧
      (∀ idx, ss.any (stmtHasStorageMarker idx) = ts.any (stmtHasStorageMarker idx)) ∧
      (∀ n, ss.all (stmtStorageInBounds n) = ts.all (stmtStorageInBounds n)) := by
  induction fuel with
  | zero =>
    intro ss ts hLe hRel
    cases ss with
    | cons _ _ => exact False.elim (Nat.not_lt_zero _ hLe)
    | nil =>
      cases ts with
      | nil => exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
      | cons t1 restT =>
        cases restT <;> cases hRel
  | succ k ih =>
    intro ss ts hLe hRel
    cases ss with
    | nil =>
      cases ts with
      | nil => exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
      | cons t1 restT => cases restT <;> cases hRel
    | cons s₁ ss1 =>
      cases ss1 with
      | nil =>
        cases ts with
        | nil => cases hRel
        | cons t₁ ts1 =>
          cases ts1 with
          | cons _ _ => cases hRel
          | nil =>
            have hEq := stmtEq_eq hRel; subst hEq
            exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
      | cons s₂ restSrc =>
        cases ts with
        | nil => cases hRel
        | cons t₁ ts1 =>
          cases ts1 with
          | nil => cases hRel
          | cons t₂ restTgt =>
            unfold isDoubleUnaryChainStmts at hRel
            cases hPair : isDoubleUnaryPair bodyLocals s₁ s₂ t₁ t₂ with
            | true =>
              rw [hPair, if_bool_true rfl] at hRel
              have hLenRest : restSrc.length ≤ k := by
                have h1 : restSrc.length + 1 ≤ restSrc.length + 2 := Nat.le_succ _
                have h2 : restSrc.length + 1 ≤ k + 1 := Nat.le_trans h1 hLe
                exact Nat.le_of_succ_le_succ h2
              let ⟨hL, hAny, hAll⟩ := ih restSrc restTgt hLenRest hRel
              let ⟨tmp, dst, x, op, _, hs1, ht1, hs2, ht2, _⟩ := isDoubleUnaryPair_elim hPair
              subst hs1; subst ht1; subst hs2; subst ht2
              refine ⟨by dsimp; rw [hL], ?_, ?_⟩
              · intro idx; dsimp [List.any, stmtHasStorageMarker]; exact hAny idx
              · intro n; dsimp [List.all, stmtStorageInBounds]; exact hAll n
            | false =>
              rw [hPair, if_bool_false rfl] at hRel
              let ⟨hSt1, hRestRel⟩ := bool_and_true hRel
              have hEq1 := stmtEq_eq hSt1; subst hEq1
              have hLenSub : (s₂ :: restSrc).length ≤ k := Nat.le_of_succ_le_succ hLe
              let ⟨hL, hAny, hAll⟩ := ih (s₂ :: restSrc) (t₂ :: restTgt) hLenSub hRestRel
              refine ⟨congrArg (· + 1) hL, ?_, ?_⟩
              · intro idx
                change (stmtHasStorageMarker idx s₁ || (s₂ :: restSrc).any (stmtHasStorageMarker idx)) =
                  (stmtHasStorageMarker idx s₁ || (t₂ :: restTgt).any (stmtHasStorageMarker idx))
                rw [hAny idx]
              · intro n
                change (stmtStorageInBounds n s₁ && (s₂ :: restSrc).all (stmtStorageInBounds n)) =
                  (stmtStorageInBounds n s₁ && (t₂ :: restTgt).all (stmtStorageInBounds n))
                rw [hAll n]

private theorem isDoubleUnaryChainStmts_props {bodyLocals : List MirTy}
    {ss ts : List StatementKind}
    (hRel : isDoubleUnaryChainStmts bodyLocals ss ts = true) :
    ss.length = ts.length ∧
    (∀ idx, ss.any (stmtHasStorageMarker idx) = ts.any (stmtHasStorageMarker idx)) ∧
    (∀ n, ss.all (stmtStorageInBounds n) = ts.all (stmtStorageInBounds n)) :=
  isDoubleUnaryChainStmts_props_fueled bodyLocals ss.length ss ts (Nat.le_refl _) hRel

private theorem isDoubleUnaryChainBody_storage_eq {b₁ b₂ : Body}
    (hBody : isDoubleUnaryChainBody b₁ b₂ = true) :
    bodyHeaderEq b₁ b₂ = true ∧
    b₁.basicBlocks.length = b₂.basicBlocks.length ∧
    b₁.basicBlocks.isEmpty = b₂.basicBlocks.isEmpty ∧
    (∀ idx, hasStorageAnnotation b₁ idx = hasStorageAnnotation b₂ idx) ∧
    storageAnnotationsInBounds b₁ = storageAnnotationsInBounds b₂ ∧
    (∀ args, initLocalsLoop b₁ args 0 b₁.locals = initLocalsLoop b₂ args 0 b₂.locals) := by
  let ⟨hBHdr, hBBs⟩ := bool_and_true hBody
  let ⟨hArg, hLoc, _, _⟩ := bodyHeaderEq_elim hBHdr
  have hBBLen := listRel_length hBBs
  have hBBEmpty := list_isEmpty_eq_of_length hBBLen
  have hMarker : ∀ idx, hasStorageAnnotation b₁ idx = hasStorageAnnotation b₂ idx := by
    intro idx
    unfold hasStorageAnnotation
    apply list_any_eq_of_rel hBBs
    intro bb₁ bb₂ hBB
    let ⟨h12, _⟩ := bool_and_true hBB
    let ⟨_, hStmts⟩ := bool_and_true h12
    exact (isDoubleUnaryChainStmts_props hStmts).2.1 idx
  have hBounds : storageAnnotationsInBounds b₁ = storageAnnotationsInBounds b₂ := by
    unfold storageAnnotationsInBounds
    dsimp only
    rw [← hLoc]
    apply list_all_eq_of_rel hBBs
    intro bb₁ bb₂ hBB
    let ⟨h12, _⟩ := bool_and_true hBB
    let ⟨_, hStmts⟩ := bool_and_true h12
    have hEqAll := (isDoubleUnaryChainStmts_props hStmts).2.2 b₁.locals.length
    exact hEqAll
  exact ⟨hBHdr, hBBLen, hBBEmpty, hMarker, hBounds,
         fun args => initLocalsLoop_eq_of_storage_eq args hArg hLoc (fun idx _ _ => hMarker idx)⟩

private theorem isDoubleUnaryChainProgram_initState_eq {p₁ p₂ : Program}
    (hProg : isDoubleUnaryChainProgram p₁ p₂ = true) (q : Query) :
    initState p₁ q = initState p₂ q := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hProg
  let ⟨_, _, hEnt, _⟩ := programHeaderEq_elim hHdr
  apply initState_eq_of_matching_entry q hHdr
  · rw [← hEnt]; exact listRel_getElem?_none_iff p₁.entryDefId hBodies
  · intro b₁ hB₁
    let ⟨b₂, hB₂, hBRel⟩ := listRel_getElem?_left hBodies hB₁
    rw [hEnt] at hB₂
    let ⟨hBHdr, _, hBBEmpty, _, hBounds, hInitLoop⟩ :=
      isDoubleUnaryChainBody_storage_eq hBRel
    exact ⟨b₂, hB₂, hBHdr, hBBEmpty, hBounds, hInitLoop q.args⟩

private noncomputable def DoubleUnaryStmtInv (bodyLocals : List MirTy)
    (locals : List LocalSlot) (ss ts : List StatementKind) (stmtIdx : Nat) : Prop :=
  isDoubleUnaryChainStmts bodyLocals (ss.drop stmtIdx) (ts.drop stmtIdx) = true ∨
  ∃ (tmp dst x : Place) (op : UnOp) (xTy : MirTy) (vx v1 : Val) (restSrc restTgt : List StatementKind),
    ss.drop stmtIdx = (.assign dst (.unaryOp op (.copy tmp))) :: restSrc ∧
    ts.drop stmtIdx = (.assign dst (.use (.copy x))) :: restTgt ∧
    isDoubleUnaryChainStmts bodyLocals restSrc restTgt = true ∧
    x.projection.isEmpty = true ∧
    tmp.projection.isEmpty = true ∧
    dst.projection.isEmpty = true ∧
    Trusted.MirSemantics.getElem? bodyLocals x.localId = some xTy ∧
    Trusted.MirSemantics.getElem? bodyLocals tmp.localId = some xTy ∧
    Trusted.MirSemantics.getElem? bodyLocals dst.localId = some xTy ∧
    isValidInvolutiveUnOpTy op xTy = true ∧
    Trusted.MirSemantics.getElem? locals x.localId = some (.live (some vx)) ∧
    Trusted.MirSemantics.getElem? locals tmp.localId = some (.live (some v1)) ∧
    evalUnOp op v1 = .ok vx

private theorem evalStatement_doubleUnary_first_ok {bSrc : Body} {frame : FrameState}
    {cm : CallerMemory} {s' : State} {tmp x : Place} {op : UnOp} {xTy : MirTy}
    (hWt : LocalsWellTyped bSrc.locals frame.locals)
    (hXEmp : x.projection.isEmpty = true)
    (hTmpEmp : tmp.projection.isEmpty = true)
    (hNe : tmp.localId ≠ x.localId)
    (hTx : Trusted.MirSemantics.getElem? bSrc.locals x.localId = some xTy)
    (hTt : Trusted.MirSemantics.getElem? bSrc.locals tmp.localId = some xTy)
    (hValOp : isValidInvolutiveUnOpTy op xTy = true)
    (hStep : evalStatement bSrc frame cm (.assign tmp (.unaryOp op (.copy x))) = .step s') :
    ∃ locs' vx v1,
      s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
             callerMem := cm } ∧
      LocalsWellTyped bSrc.locals locs' ∧
      Trusted.MirSemantics.getElem? locs' x.localId = some (.live (some vx)) ∧
      Trusted.MirSemantics.getElem? locs' tmp.localId = some (.live (some v1)) ∧
      evalUnOp op v1 = .ok vx := by
  have hWtPres := evalStatement_preserves_wt hWt hStep
  let ⟨locs', hEqS', hWt'⟩ := hWtPres
  dsimp [evalStatement] at hStep
  rw [hTmpEmp] at hStep; dsimp at hStep
  rw [hTt] at hStep; dsimp at hStep
  dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot] at hStep
  rw [hXEmp] at hStep; dsimp at hStep
  rw [hTx] at hStep
  cases hSlX : Trusted.MirSemantics.getElem? frame.locals x.localId with
  | none => rw [hSlX] at hStep; cases hStep
  | some slX =>
    rw [hSlX] at hStep
    cases slX with
    | dead => cases hStep
    | live optX =>
      dsimp at hStep
      have hPrim := isPrimitiveReadable_of_involutive hValOp
      rw [hPrim] at hStep; dsimp at hStep
      cases optX with
      | none => cases hStep
      | some vx =>
        dsimp at hStep
        have hChkVx : checkVal vx xTy = true := hWt.2 x.localId xTy (.live (some vx)) hTx hSlX
        let ⟨v1, hEv1, _, hEv2⟩ := evalUnOp_involutive hValOp hChkVx
        rw [hEv1] at hStep; dsimp at hStep
        unfold writePlace at hStep
        cases hChk1 : checkVal v1 xTy with
        | false => rw [hChk1] at hStep; dsimp at hStep; cases hStep
        | true =>
          rw [hChk1] at hStep; dsimp at hStep
          cases hSlTmp : Trusted.MirSemantics.getElem? frame.locals tmp.localId with
          | none => rw [hSlTmp] at hStep; cases hStep
          | some slTmp =>
            rw [hSlTmp] at hStep
            cases slTmp with
            | dead => cases hStep
            | live _ =>
              dsimp only at hStep
              cases hSet : setElem? frame.locals tmp.localId (.live (some v1)) with
              | none => rw [hSet] at hStep; cases hStep
              | some locsW =>
                rw [hSet] at hStep
                dsimp only at hStep
                injection hStep with hStEq
                rw [hEqS'] at hStEq
                injection hStEq with hFsEq _
                injection hFsEq with hFrEq _
                have hLocsEq : locsW = locs' := congrArg FrameState.locals hFrEq
                subst hLocsEq
                exact ⟨locsW, vx, v1, hEqS', hWt',
                       (setElem?_getElem?_ne hSet hNe.symm).trans hSlX,
                       setElem?_getElem?_same hSet,
                       hEv2⟩

private theorem doubleUnaryChain_query_lockstep {pSrc pTgt : Program}
    (hProg : isDoubleUnaryChainProgram pSrc pTgt = true) (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  let ⟨_, hBodies⟩ := bool_and_true hProg
  apply lockstep_inv_query_iff
    (Inv := fun s =>
      ∃ frame bSrc,
        s.frames = [frame] ∧
        Trusted.MirSemantics.getElem? pSrc.bodies frame.defId = some bSrc ∧
        LocalsWellTyped bSrc.locals frame.locals ∧
        (∀ bbSrc bbTgt,
          Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx = some bbSrc →
          ∀ bTgt, Trusted.MirSemantics.getElem? pTgt.bodies frame.defId = some bTgt →
          Trusted.MirSemantics.getElem? bTgt.basicBlocks frame.blockIdx = some bbTgt →
          DoubleUnaryStmtInv bSrc.locals frame.locals
            bbSrc.statements bbTgt.statements frame.stmtIdx))
    (isDoubleUnaryChainProgram_initState_eq hProg q)
  · intro s₀ hOk
    let ⟨_, _, body, hBody, _, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    refine ⟨_, body, rfl, hBody, initLocalsLoop_wellTyped hArgs, ?_⟩
    intro bbSrc bbTgt hBBSrc bTgt hBTgt hBBTgt
    let ⟨bTgt', hBTgt', hBRel⟩ := listRel_getElem?_left hBodies hBody
    rw [hBTgt] at hBTgt'; injection hBTgt' with hB; subst hB
    let ⟨_, hBBs⟩ := bool_and_true hBRel
    let ⟨bbTgt', hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBs hBBSrc
    rw [hBBTgt] at hBBTgt'; injection hBBTgt' with hBB; subst hBB
    let ⟨h12, _⟩ := bool_and_true hBBRel
    let ⟨_, hStRel⟩ := bool_and_true h12
    exact Or.inl hStRel
  · intro s hInv
    let ⟨frame, bSrc, hFrames, hBSrc, hWt, hAlnAll⟩ := hInv
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodies hBSrc
    let ⟨hBHdr, hBBs⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    cases s with
    | mk fs cm =>
      dsimp at hFrames; subst hFrames
      cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
      | none =>
        have hBBTgtNone := (listRel_getElem?_none_iff frame.blockIdx hBBs).mp hBBSrc
        have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
            evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
          unfold evalStep; dsimp; rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgtNone]
        refine ⟨hEvEq, ?_⟩
        intro s' hStepS
        unfold evalStep at hStepS; dsimp at hStepS
        rw [hBSrc] at hStepS; dsimp at hStepS; rw [hBBSrc] at hStepS; cases hStepS
      | some bbSrc =>
        let ⟨bbTgt, hBBTgt, hBBRel⟩ := listRel_getElem?_left hBBs hBBSrc
        let ⟨h12, hTermRel⟩ := bool_and_true hBBRel
        let ⟨hCleanEq, hFullStRel⟩ := bool_and_true h12
        have hLenEq : bbSrc.statements.length = bbTgt.statements.length :=
          (isDoubleUnaryChainStmts_props hFullStRel).1
        have hAln := hAlnAll bbSrc bbTgt hBBSrc bTgt hBTgt hBBTgt
        cases hAln with
        | inl hPhaseA =>
          cases hDropS : bbSrc.statements.drop frame.stmtIdx with
          | nil =>
            rw [hDropS] at hPhaseA
            cases hDropT : bbTgt.statements.drop frame.stmtIdx with
            | cons t1 rt =>
              rw [hDropT] at hPhaseA
              cases rt <;> cases hPhaseA
            | nil =>
              have hNoneS := getElem?_none_of_ge (le_of_drop_eq_nil hDropS)
              have hNoneT := getElem?_none_of_ge (le_of_drop_eq_nil hDropT)
              have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                  evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                unfold evalStep; dsimp
                rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
                rw [hNoneS, hNoneT]; dsimp; rw [hLenEq]
                cases Nat.beq frame.stmtIdx bbTgt.statements.length with
                | false => rfl
                | true =>
                  rw [if_bool_true rfl, if_bool_true rfl]
                  exact evalTerminator_eq_of_eq hLocEq (bool_beq_eq hCleanEq) (terminatorEq_eq hTermRel)
              refine ⟨hEvEq, ?_⟩
              intro s' hStepS
              unfold evalStep at hStepS; dsimp at hStepS
              rw [hBSrc] at hStepS; dsimp at hStepS
              rw [hBBSrc] at hStepS; dsimp at hStepS
              rw [hNoneS] at hStepS; dsimp at hStepS
              cases hEnd : Nat.beq frame.stmtIdx bbSrc.statements.length with
              | false => rw [hEnd] at hStepS; cases hStepS
              | true =>
                rw [hEnd] at hStepS; dsimp at hStepS
                let ⟨tgt, locs', hEqS', hWt'⟩ := evalTerminator_preserves_wt hWt hStepS
                subst hEqS'
                refine ⟨_, bSrc, rfl, hBSrc, hWt', ?_⟩
                intro bbSrc2 bbTgt2 hBBS2 bTgt2 hBT2 hBBT2
                rw [hBTgt] at hBT2; injection hBT2 with hB2; subst hB2
                let ⟨bbTgt2', hBBT2', hBBR2⟩ := listRel_getElem?_left hBBs hBBS2
                rw [hBBT2] at hBBT2'; injection hBBT2' with hBB2; subst hBB2
                let ⟨h12_2, _⟩ := bool_and_true hBBR2
                exact Or.inl (bool_and_true h12_2).2
          | cons s₁ restS1 =>
            rw [hDropS] at hPhaseA
            let ⟨hGetS1, hDropNextS⟩ := getElem?_of_drop_eq_cons hDropS
            cases restS1 with
            | nil =>
              cases hDropT : bbTgt.statements.drop frame.stmtIdx with
              | nil => rw [hDropT] at hPhaseA; cases hPhaseA
              | cons t₁ restT1 =>
                rw [hDropT] at hPhaseA
                cases restT1 with
                | cons _ _ => cases hPhaseA
                | nil =>
                  have hStEq1 := stmtEq_eq hPhaseA; subst hStEq1
                  let ⟨hGetT1, hDropNextT⟩ := getElem?_of_drop_eq_cons hDropT
                  have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                      evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                    unfold evalStep; dsimp
                    rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
                    rw [hGetS1, hGetT1]; dsimp
                    exact evalStatement_eq_of_same frame cm s₁ hLocEq
                  refine ⟨hEvEq, ?_⟩
                  intro s' hStepS
                  unfold evalStep at hStepS; dsimp at hStepS
                  rw [hBSrc] at hStepS; dsimp at hStepS
                  rw [hBBSrc] at hStepS; dsimp at hStepS
                  rw [hGetS1] at hStepS; dsimp at hStepS
                  let ⟨locs', hEqS', hWt'⟩ := evalStatement_preserves_wt hWt hStepS
                  subst hEqS'
                  refine ⟨_, bSrc, rfl, hBSrc, hWt', ?_⟩
                  intro bbSrc2 bbTgt2 hBBS2 bTgt2 hBT2 hBBT2
                  dsimp at hBBS2 hBT2 hBBT2; dsimp
                  rw [hBBSrc] at hBBS2; injection hBBS2 with hE1; subst hE1
                  rw [hBTgt] at hBT2; injection hBT2 with hE2; subst hE2
                  rw [hBBTgt] at hBBT2; injection hBBT2 with hE3; subst hE3
                  left
                  rw [hDropNextS, hDropNextT]; rfl
            | cons s₂ restSrc =>
              cases hDropT : bbTgt.statements.drop frame.stmtIdx with
              | nil => rw [hDropT] at hPhaseA; cases hPhaseA
              | cons t₁ restT1 =>
                rw [hDropT] at hPhaseA
                cases restT1 with
                | nil => cases hPhaseA
                | cons t₂ restTgt =>
                  let ⟨hGetT1, hDropNextT⟩ := getElem?_of_drop_eq_cons hDropT
                  unfold isDoubleUnaryChainStmts at hPhaseA
                  cases hPair : isDoubleUnaryPair bSrc.locals s₁ s₂ t₁ t₂ with
                  | false =>
                    rw [hPair, if_bool_false rfl] at hPhaseA
                    let ⟨hSt1, hNextRel⟩ := bool_and_true hPhaseA
                    have hEq1 := stmtEq_eq hSt1; subst hEq1
                    have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                        evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                      unfold evalStep; dsimp
                      rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
                      rw [hGetS1, hGetT1]; dsimp
                      exact evalStatement_eq_of_same frame cm s₁ hLocEq
                    refine ⟨hEvEq, ?_⟩
                    intro s' hStepS
                    unfold evalStep at hStepS; dsimp at hStepS
                    rw [hBSrc] at hStepS; dsimp at hStepS
                    rw [hBBSrc] at hStepS; dsimp at hStepS
                    rw [hGetS1] at hStepS; dsimp at hStepS
                    let ⟨locs', hEqS', hWt'⟩ := evalStatement_preserves_wt hWt hStepS
                    subst hEqS'
                    refine ⟨_, bSrc, rfl, hBSrc, hWt', ?_⟩
                    intro bbSrc2 bbTgt2 hBBS2 bTgt2 hBT2 hBBT2
                    dsimp at hBBS2 hBT2 hBBT2; dsimp
                    rw [hBBSrc] at hBBS2; injection hBBS2 with hE1; subst hE1
                    rw [hBTgt] at hBT2; injection hBT2 with hE2; subst hE2
                    rw [hBBTgt] at hBBT2; injection hBBT2 with hE3; subst hE3
                    left
                    rw [hDropNextS, hDropNextT]; exact hNextRel
                  | true =>
                    rw [hPair, if_bool_true rfl] at hPhaseA
                    let ⟨tmp, dst, x, op, xTy, hs1, ht1, hs2, ht2,
                         hXEmp, hTmpEmp, hDstEmp, hNe, hTx, hTt, hTd, hValOp⟩ :=
                      isDoubleUnaryPair_elim hPair
                    subst hs1; subst ht1; subst hs2; subst ht2
                    have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                        evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                      unfold evalStep; dsimp
                      rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
                      rw [hGetS1, hGetT1]; dsimp
                      exact evalStatement_eq_of_same frame cm _ hLocEq
                    refine ⟨hEvEq, ?_⟩
                    intro s' hStepS
                    unfold evalStep at hStepS; dsimp at hStepS
                    rw [hBSrc] at hStepS; dsimp at hStepS
                    rw [hBBSrc] at hStepS; dsimp at hStepS
                    rw [hGetS1] at hStepS; dsimp at hStepS
                    let ⟨locs', vx, v1, hEqS', hWt', hGetX, hGetTmp, hEvUn2⟩ :=
                      evalStatement_doubleUnary_first_ok hWt hXEmp hTmpEmp hNe hTx hTt hValOp hStepS
                    subst hEqS'
                    refine ⟨_, bSrc, rfl, hBSrc, hWt', ?_⟩
                    intro bbSrc2 bbTgt2 hBBS2 bTgt2 hBT2 hBBT2
                    dsimp at hBBS2 hBT2 hBBT2; dsimp
                    rw [hBBSrc] at hBBS2; injection hBBS2 with hE1; subst hE1
                    rw [hBTgt] at hBT2; injection hBT2 with hE2; subst hE2
                    rw [hBBTgt] at hBBT2; injection hBBT2 with hE3; subst hE3
                    right
                    exact ⟨tmp, dst, x, op, xTy, vx, v1, restSrc, restTgt,
                           hDropNextS, hDropNextT, hPhaseA,
                           hXEmp, hTmpEmp, hDstEmp, hTx, hTt, hTd, hValOp,
                           hGetX, hGetTmp, hEvUn2⟩
        | inr hPhaseB =>
          let ⟨tmp, dst, x, op, xTy, vx, v1, restSrc, restTgt,
               hDropS, hDropT, hRestRel,
               hXEmp, hTmpEmp, hDstEmp, hTx, hTt, hTd, hValOp,
               hGetX, hGetTmp, hEvUn2⟩ := hPhaseB
          let ⟨hGetS2, hDropNextS⟩ := getElem?_of_drop_eq_cons hDropS
          let ⟨hGetT2, hDropNextT⟩ := getElem?_of_drop_eq_cons hDropT
          have hPrimX := isPrimitiveReadable_of_involutive hValOp
          have hStmtEq : evalStatement bSrc frame cm (.assign dst (.unaryOp op (.copy tmp))) =
              evalStatement bTgt frame cm (.assign dst (.use (.copy x))) := by
            unfold evalStatement; dsimp
            rw [← hLocEq, hDstEmp]; dsimp
            rw [hTd]; dsimp
            unfold evalRvalue evalPrimitiveOperand evalOperandToSlot
            dsimp
            rw [hTmpEmp, hXEmp]; dsimp
            rw [hTt, hTx, hGetTmp, hGetX]; dsimp
            rw [hPrimX, mirTy_beq_refl xTy]; dsimp
            rw [hEvUn2]
          have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
              evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
            unfold evalStep; dsimp
            rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
            rw [hGetS2, hGetT2]; dsimp
            exact hStmtEq
          refine ⟨hEvEq, ?_⟩
          intro s' hStepS
          unfold evalStep at hStepS; dsimp at hStepS
          rw [hBSrc] at hStepS; dsimp at hStepS
          rw [hBBSrc] at hStepS; dsimp at hStepS
          rw [hGetS2] at hStepS; dsimp at hStepS
          let ⟨locs', hEqS', hWt'⟩ := evalStatement_preserves_wt hWt hStepS
          subst hEqS'
          refine ⟨_, bSrc, rfl, hBSrc, hWt', ?_⟩
          intro bbSrc2 bbTgt2 hBBS2 bTgt2 hBT2 hBBT2
          dsimp at hBBS2 hBT2 hBBT2; dsimp
          rw [hBBSrc] at hBBS2; injection hBBS2 with hE1; subst hE1
          rw [hBTgt] at hBT2; injection hBT2 with hE2; subst hE2
          rw [hBBTgt] at hBBT2; injection hBBT2 with hE3; subst hE3
          left
          rw [hDropNextS, hDropNextT]; exact hRestRel

private theorem isDoubleUnaryChainProgram_entryProg {p₁ p₂ : Program} (defId : DefId)
    (hProg : isDoubleUnaryChainProgram p₁ p₂ = true) :
    isDoubleUnaryChainProgram (entryProgForBody p₁ defId)
      (entryProgForBody p₂ defId) = true := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hProg
  exact bool_and_intro (programHeaderEq_entryProg defId hHdr) hBodies

private theorem doubleUnaryChain_bidirectional_iff_priv
    (pSrc pTgt : Program)
    (hRel : isDoubleUnaryChainProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  let ⟨hHdr, hBodies⟩ := bool_and_true hRel
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hBHdr, _, hBBEmpty, _, hBounds, _⟩ := isDoubleUnaryChainBody_storage_eq hBRel
    exact ⟨hBHdr, hBBEmpty, hBounds⟩
  · intro q
    exact doubleUnaryChain_query_lockstep hRel q
  · intro defId args
    exact (doubleUnaryChain_query_lockstep
      (isDoubleUnaryChainProgram_entryProg defId hRel) { args := args }).1

/-! ### Stage 4 Private Helpers — Layer E: Forward & Certified Passes 3 & 4 -/

/-! #### Shared List / Switch / Certificate Lookup Helpers -/

private theorem list_all_mem_true {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (hAll : xs.all p = true) (hMem : x ∈ xs) : p x = true := by
  induction hMem with
  | head rest =>
    exact (bool_and_true hAll).1
  | tail y _ ih =>
    exact ih (bool_and_true hAll).2

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
        | succ k =>
          dsimp [Trusted.MirSemantics.getElem?] at hX
          dsimp [Trusted.MirSemantics.getElem?]
          exact ih hLenTail hTail hX

private theorem bitvec_eq_of_beq {a b : BitVec 128} (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

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
          | inl hIn =>
            let ⟨cb, hMem⟩ := hIn
            exact Or.inl ⟨cb, List.Mem.tail (caseBits, bTgt) hMem⟩
          | inr hFall =>
            let ⟨hTgt, hGuardRest⟩ := hFall
            refine Or.inr ⟨hTgt, ?_⟩
            intro hG
            dsimp [hasValidZeroGuard] at hG
            rw [hOvf] at hG; dsimp at hG
            cases hCaseZero : (caseBits == BitVec.ofNat 128 0) with
            | true =>
              have hCEq := bitvec_eq_of_beq hCaseZero
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
              | inl hIn =>
                let ⟨cb, hMem⟩ := hIn
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
              | inl hIn =>
                let ⟨cb, hMem⟩ := hIn
                exact Or.inl ⟨cb, List.Mem.tail (caseBits, bTgt) hMem⟩
              | inr hTgt => exact Or.inr hTgt

/-! #### Theorem 3a: Unconditional Forward Codegen Refinement for
`ZeroLhsDivRem` -/

private theorem isZeroLhsDivRemStmt_assignOnly (locs : List MirTy)
    (s₁ s₂ : StatementKind) (h : isZeroLhsDivRemStmt locs s₁ s₂ = true) :
    s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂) := by
  unfold isZeroLhsDivRemStmt at h
  cases bool_or_true h with
  | inr hEq => exact Or.inl (stmtEq_eq hEq)
  | inl hRw =>
    cases s₁ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hRw
    | assign d₁ rv₁ =>
      cases rv₁ with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
      | aggregateTuple _ | unsupported => cases hRw
      | binaryOp op lhs rhs =>
        cases lhs with
        | copy _ | move _ => cases hRw
        | constant c =>
          cases s₂ with
          | nop | storageLive _ | storageDead _ | unsupported => cases hRw
          | assign d₂ rv₂ =>
            exact Or.inr ⟨d₁, .binaryOp op (.constant c) rhs, d₂, rv₂, rfl, rfl⟩

private theorem isZeroLhsDivRemProgram_to_generic {pSrc pTgt : Program}
    (h : isZeroLhsDivRemProgram pSrc pTgt = true) :
    genericProgRel isZeroLhsDivRemStmt pSrc pTgt = true := by
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  refine bool_and_intro hHdr ?_
  refine listRel_mono (fun b₁ b₂ hb => ?_) hBodies
  let ⟨hBHdr, hBBs⟩ := bool_and_true hb
  exact bool_and_intro hBHdr (listRel_mono (fun _ _ hbb => hbb) hBBs)

private theorem evalStatement_zeroLhsDivRem_fwd (b₁ b₂ : Body) (f₁ f₂ : FrameState)
    (cm : CallerMemory) (s₁ s₂ : StatementKind) (s' : State)
    (hLocEq : b₁.locals = b₂.locals)
    (hInv : LocalsFwdRefines b₁.locals f₁.locals f₂.locals)
    (hRel : isZeroLhsDivRemStmt b₁.locals s₁ s₂ = true)
    (hEv : evalStatement b₁ f₁ cm s₁ = .step s') :
    ∃ locs1' locs2',
      s' = { frames := [{ f₁ with stmtIdx := f₁.stmtIdx + 1, locals := locs1' }],
             callerMem := cm } ∧
      evalStatement b₂ f₂ cm s₂ =
        .step { frames := [{ f₂ with stmtIdx := f₂.stmtIdx + 1, locals := locs2' }],
                callerMem := cm } ∧
      LocalsFwdRefines b₁.locals locs1' locs2' := by
  unfold isZeroLhsDivRemStmt at hRel
  cases bool_or_true hRel with
  | inr hEq =>
    rw [stmtEq_eq hEq] at hEv
    exact evalStatement_fwd_eq hLocEq hInv hEv
  | inl hRw =>
    cases s₁ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hRw
    | assign dst rv₁ =>
      cases rv₁ with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
      | aggregateTuple _ | unsupported => cases hRw
      | binaryOp op lhs rhs =>
        cases lhs with
        | copy _ | move _ => cases hRw
        | constant zeroConst =>
          cases s₂ with
          | nop | storageLive _ | storageDead _ | unsupported => cases hRw
          | assign dst' rv₂ =>
            cases rv₂ with
            | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
            | aggregateTuple _ | unsupported => cases hRw
            | use opnd₂ =>
              cases opnd₂ with
              | copy _ | move _ => cases hRw
              | constant zeroConst' =>
                unfold isZeroLhsDivRemRewrite at hRw
                let ⟨hPre, hTypes⟩ := bool_and_true hRw
                let ⟨h123, hCEq⟩ := bool_and_true hPre
                let ⟨h12, hOp⟩ := bool_and_true h123
                let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12
                have hDEq := placeEq_eq hDstEq; subst hDEq
                have hConstEq := constOpEq_eq hCEq; subst hConstEq
                cases hDstTy : Trusted.MirSemantics.getElem? b₁.locals dst.localId with
                | none => rw [hDstTy] at hTypes; cases hTypes
                | some dTy =>
                  rw [hDstTy] at hTypes
                  cases dTy with
                  | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
                    cases hTypes
                  | int w s =>
                    cases hStR : operandStaticTy? b₁.locals rhs with
                    | none => rw [hStR] at hTypes; cases hTypes
                    | some rhsTy =>
                      rw [hStR] at hTypes
                      let ⟨hRTyEq, hZeroC⟩ := bool_and_true hTypes
                      have hREq := mirTy_beq_eq hRTyEq; subst hREq
                      let ⟨hZStruct, hEvZ⟩ := isIntZeroConst_elim hZeroC
                      have hZTy : zeroConst.ty = .int w s := by rw [hZStruct]
                      have hPrimZ : isPrimitiveReadableTy zeroConst.ty = true := by
                        rw [hZTy]; rfl
                      dsimp [evalStatement] at hEv
                      rw [hDstEmp] at hEv; dsimp at hEv
                      rw [hDstTy] at hEv; dsimp at hEv
                      dsimp [evalRvalue] at hEv
                      have hPrimOpZ : evalPrimitiveOperand b₁.locals f₁.locals (.constant zeroConst) =
                          .ok (.scalar ⟨w, s, BitVec.ofNat 128 0⟩, f₁.locals) := by
                        dsimp [evalPrimitiveOperand, evalOperandToSlot]
                        rw [hEvZ]; dsimp; rw [hPrimZ]; rfl
                      rw [hPrimOpZ] at hEv; dsimp at hEv
                      cases hEvR : evalPrimitiveOperand b₁.locals f₁.locals rhs with
                      | error _ => rw [hEvR] at hEv; cases hEv
                      | ok resR =>
                        let ⟨vr, locsAfterRhs⟩ := resR
                        rw [hEvR] at hEv; dsimp at hEv
                        let ⟨hInv1, hChkFn⟩ := evalPrimitiveOperand_discarded_fwd hInv hEvR
                        have hChkVr : checkVal vr (.int w s) = true := hChkFn (.int w s) hStR
                        cases hEvB : evalBinOp op (.scalar ⟨w, s, BitVec.ofNat 128 0⟩) vr with
                        | error _ => rw [hEvB] at hEv; cases hEv
                        | ok resVal =>
                          rw [hEvB] at hEv; dsimp at hEv
                          have hResEq := evalBinOp_zeroLhs_div_rem_fwd hOp hChkVr hEvB
                          subst hResEq
                          cases hW1 : writePlace locsAfterRhs dst.localId (.int w s)
                              (.scalar ⟨w, s, BitVec.ofNat 128 0⟩) with
                          | error _ => rw [hW1] at hEv; cases hEv
                          | ok locs1' =>
                            rw [hW1] at hEv
                            injection hEv with hStEq
                            let ⟨locs2', hW2, hInv2⟩ := writePlace_fwd hInv1 hDstTy hW1
                            refine ⟨locs1', locs2', hStEq.symm, ?_, hInv2⟩
                            dsimp [evalStatement]
                            rw [hDstEmp]; dsimp
                            rw [← hLocEq, hDstTy]; dsimp
                            dsimp [evalRvalue, evalOperandToSlot]
                            rw [hEvZ]; dsimp
                            rw [hZTy, mirTy_beq_refl (.int w s)]; dsimp
                            rw [hW2]

private theorem codegen_zeroLhsDivRem_refines_unconditional_priv
    (pSrc pTgt : Program)
    (hRel : isZeroLhsDivRemProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt :=
  forwardCodegenRefines_of_stmtRel_fwd
    isZeroLhsDivRemStmt_assignOnly
    evalStatement_zeroLhsDivRem_fwd
    (isZeroLhsDivRemProgram_to_generic hRel)

/-! #### Theorem 3b: Certified Bidirectional VC Transport for `ZeroLhsDivRem` -/

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

private theorem stepNonZeroStmtPair_sound {bSrc bTgt : Body}
    {env env' : List NonZeroAbsSlot} {frame : FrameState}
    {cm : CallerMemory} {sSrc sTgt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEnv : NonZeroEnvSound bSrc.locals env frame.locals)
    (hPair : stepNonZeroStmtPair bSrc.locals env sSrc sTgt = some env') :
    evalStatement bSrc frame cm sSrc = evalStatement bTgt frame cm sTgt ∧
    (∀ s', evalStatement bSrc frame cm sSrc = .step s' →
      ∃ locs',
        s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
               callerMem := cm } ∧
        NonZeroEnvSound bSrc.locals env' locs') := by
  unfold stepNonZeroStmtPair at hPair
  cases hStEq : stmtEq sSrc sTgt with
  | true =>
    rw [hStEq, if_bool_true rfl] at hPair
    have hEq := stmtEq_eq hStEq; subst hEq
    refine ⟨evalStatement_eq_of_same frame cm sSrc hLocEq, ?_⟩
    intro s' hEv
    cases sSrc with
    | nop =>
      injection hPair with hEnvEq; subst hEnvEq
      injection hEv with hSEq; subst hSEq
      exact ⟨frame.locals, rfl, hEnv⟩
    | unsupported => cases hEv
    | storageLive id =>
      dsimp at hPair
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals id with
      | none => rw [hTy] at hPair; cases hPair
      | some ty =>
        rw [hTy] at hPair; dsimp at hPair
        dsimp [evalStatement] at hEv; rw [hTy] at hEv; dsimp at hEv
        cases hSetL : setElem? frame.locals id (liveUninitSlot ty) with
        | none => rw [hSetL] at hEv; cases hEv
        | some locs' =>
          rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
          exact ⟨locs', rfl,
            nonZeroEnvSound_set hEnv hTy hPair hSetL (nonZeroSlotSound_liveUninit ty)⟩
    | storageDead id =>
      dsimp at hPair
      cases hZ : Nat.beq id 0 with
      | true => rw [hZ] at hPair; cases hPair
      | false =>
        rw [hZ] at hPair; dsimp at hPair
        dsimp [evalStatement] at hEv; rw [hZ] at hEv; dsimp at hEv
        cases hSetL : setElem? frame.locals id .dead with
        | none => rw [hSetL] at hEv; cases hEv
        | some locs' =>
          rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
          have hLt : id < bSrc.locals.length := by
            rw [← hEnv.2.1]
            cases Nat.lt_or_ge id env.length with
            | inl hlt => exact hlt
            | inr hge =>
              rw [setElem?_none_of_ge env id .dead hge] at hPair; cases hPair
          let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals id hLt
          exact ⟨locs', rfl,
            nonZeroEnvSound_set hEnv hTy hPair hSetL ⟨True.intro, True.intro⟩⟩
    | assign dst rv =>
      dsimp at hPair
      cases hPEmp : dst.projection.isEmpty with
      | false => rw [hPEmp] at hPair; cases hPair
      | true =>
        rw [hPEmp] at hPair; dsimp at hPair
        cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
        | none => rw [hDstTy] at hPair; cases hPair
        | some dstTy =>
          rw [hDstTy] at hPair; dsimp at hPair
          dsimp [evalStatement] at hEv; rw [hPEmp] at hEv; dsimp at hEv
          rw [hDstTy] at hEv; dsimp at hEv
          cases hRv : evalRvalue bSrc.locals frame.locals dstTy rv with
          | error _ => rw [hRv] at hEv; cases hEv
          | ok res =>
            let ⟨val, locs1⟩ := res
            rw [hRv] at hEv; dsimp at hEv
            have hEnv1 := deinitMovesInRvalueNonZero_sound hEnv hRv
            cases hW : writePlace locs1 dst.localId dstTy val with
            | error _ => rw [hW] at hEv; cases hEv
            | ok locs' =>
              rw [hW] at hEv; injection hEv with hSEq; subst hSEq
              dsimp [writePlace] at hW
              cases hChk : checkVal val dstTy with
              | false => rw [hChk] at hW; cases hW
              | true =>
                rw [hChk] at hW; dsimp at hW
                cases hSl1 : Trusted.MirSemantics.getElem? locs1 dst.localId with
                | none => rw [hSl1] at hW; cases hW
                | some sl1 =>
                  rw [hSl1] at hW
                  cases sl1 with
                  | dead => cases hW
                  | live _ =>
                    cases hSetL : setElem? locs1 dst.localId (.live (some val)) with
                    | none => rw [hSetL] at hW; cases hW
                    | some locsW =>
                      rw [hSetL] at hW; injection hW with hWEq; subst hWEq
                      refine ⟨locsW, rfl,
                        nonZeroEnvSound_set hEnv1 hDstTy hPair hSetL ?_⟩
                      cases hProd : rvalueProducesNonZero bSrc.locals env dstTy rv with
                      | true =>
                        exact rvalueProducesNonZero_sound hEnv hProd hRv hChk
                      | false =>
                        exact ⟨hChk, ⟨val, rfl⟩⟩
  | false =>
    rw [hStEq, if_bool_false rfl] at hPair
    cases sSrc with
    | nop | storageLive _ | storageDead _ | unsupported => cases hPair
    | assign dst rvS =>
      cases rvS with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _
      | addressOf _ | aggregateTuple _ | unsupported => cases hPair
      | binaryOp op lhs rhs =>
        cases lhs with
        | copy _ | move _ => cases hPair
        | constant zeroConst =>
          dsimp at hPair
          cases hRw : isZeroLhsDivRemRewrite bSrc.locals
              (.assign dst (.binaryOp op (.constant zeroConst) rhs)) sTgt with
          | false => rw [hRw] at hPair; cases hPair
          | true =>
            rw [hRw] at hPair; dsimp at hPair
            cases sTgt with
            | nop | storageLive _ | storageDead _ | unsupported => cases hRw
            | assign dst' rvT =>
              cases rvT with
              | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
              | addressOf _ | aggregateTuple _ | unsupported => cases hRw
              | use opndT =>
                cases opndT with
                | copy _ | move _ => cases hRw
                | constant zeroConst' =>
                  unfold isZeroLhsDivRemRewrite at hRw
                  let ⟨hPre, hTypes⟩ := bool_and_true hRw
                  let ⟨h123, hCEq⟩ := bool_and_true hPre
                  let ⟨h12, hOp⟩ := bool_and_true h123
                  let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12
                  have hDEq := placeEq_eq hDstEq; subst hDEq
                  have hConstEq := constOpEq_eq hCEq; subst hConstEq
                  cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
                  | none => rw [hDstTy] at hPair; cases hPair
                  | some dTy =>
                    rw [hDstTy] at hPair; rw [hDstTy] at hTypes
                    cases dTy with
                    | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
                      cases hPair
                    | int w s =>
                      dsimp at hPair
                      cases hCertDiv : isCertifiedNonZeroDivisor bSrc.locals env w s rhs with
                      | false => rw [hCertDiv] at hPair; cases hPair
                      | true =>
                        rw [hCertDiv] at hPair; dsimp at hPair
                        cases hStR : operandStaticTy? bSrc.locals rhs with
                        | none => rw [hStR] at hTypes; cases hTypes
                        | some rhsTy =>
                          rw [hStR] at hTypes
                          let ⟨_, hZeroC⟩ := bool_and_true hTypes
                          let ⟨hZStruct, hEvZ⟩ := isIntZeroConst_elim hZeroC
                          have hZTy : zeroConst.ty = .int w s := by rw [hZStruct]
                          have hPrimZ : isPrimitiveReadableTy zeroConst.ty = true := by
                            rw [hZTy]; rfl
                          let ⟨bR, hEvRhs, _, hNe0R⟩ :=
                            isCertifiedNonZeroDivisor_sound hEnv hCertDiv
                          have hBinOk := evalBinOp_zeroLhs_div_rem_of_ne_zero hOp hNe0R
                          have hRvEq :
                              evalRvalue bSrc.locals frame.locals (.int w s)
                                (.binaryOp op (.constant zeroConst) rhs) =
                              .ok (.scalar ⟨w, s, BitVec.ofNat 128 0⟩, frame.locals) := by
                            dsimp [evalRvalue]
                            have hPZ : evalPrimitiveOperand bSrc.locals frame.locals (.constant zeroConst) =
                                .ok (.scalar ⟨w, s, BitVec.ofNat 128 0⟩, frame.locals) := by
                              dsimp [evalPrimitiveOperand, evalOperandToSlot]
                              rw [hEvZ]; dsimp; rw [hPrimZ]; rfl
                            rw [hPZ]; dsimp; rw [hEvRhs]; dsimp; rw [hBinOk]
                          have hRvTgtEq :
                              evalRvalue bSrc.locals frame.locals (.int w s)
                                (.use (.constant zeroConst)) =
                              .ok (.scalar ⟨w, s, BitVec.ofNat 128 0⟩, frame.locals) := by
                            dsimp [evalRvalue, evalOperandToSlot]
                            rw [hEvZ]; dsimp; rw [hZTy, mirTy_beq_refl (.int w s)]; dsimp
                          have hStmtEq :
                              evalStatement bSrc frame cm
                                (.assign dst (.binaryOp op (.constant zeroConst) rhs)) =
                              evalStatement bTgt frame cm
                                (.assign dst (.use (.constant zeroConst))) := by
                            dsimp [evalStatement]
                            rw [← hLocEq, hDstEmp]; dsimp
                            rw [hDstTy]; dsimp; rw [hRvEq, hRvTgtEq]
                          refine ⟨hStmtEq, ?_⟩
                          intro s' hEvS
                          dsimp [evalStatement] at hEvS
                          rw [hDstEmp] at hEvS; dsimp at hEvS
                          rw [hDstTy] at hEvS; dsimp at hEvS
                          rw [hRvEq] at hEvS; dsimp at hEvS
                          dsimp [writePlace] at hEvS
                          have hChk0 : checkVal (.scalar ⟨w, s, BitVec.ofNat 128 0⟩) (.int w s) = true :=
                            checkVal_int_iff.mpr ⟨BitVec.ofNat 128 0, rfl, truncateBits_zero w⟩
                          rw [hChk0] at hEvS; dsimp at hEvS
                          cases hSlD : Trusted.MirSemantics.getElem? frame.locals dst.localId with
                          | none => rw [hSlD] at hEvS; cases hEvS
                          | some slD =>
                            rw [hSlD] at hEvS
                            cases slD with
                            | dead => cases hEvS
                            | live _ =>
                              cases hSetL : setElem? frame.locals dst.localId
                                  (.live (some (.scalar ⟨w, s, BitVec.ofNat 128 0⟩))) with
                              | none => rw [hSetL] at hEvS; cases hEvS
                              | some locsW =>
                                rw [hSetL] at hEvS; injection hEvS with hSEq; subst hSEq
                                exact ⟨locsW, rfl,
                                  nonZeroEnvSound_set hEnv hDstTy hPair hSetL
                                    ⟨hChk0, ⟨_, rfl⟩⟩⟩

private theorem checkZeroLhsDivRemBlocksLoop_getElem? (bSrc bTgt : Body)
    (cert : BodyNonZeroCert) :
    ∀ base bbs k bbSrc,
      checkZeroLhsDivRemBlocksLoop bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      checkZeroLhsDivRemBlock bSrc bTgt cert (base + k) bbSrc = true := by
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

private theorem checkNonZeroEdge_sound {bSrc bTgt : Body} {cert : BodyNonZeroCert}
    {edgeEnv : List NonZeroAbsSlot} {locs' : List LocalSlot} {tgt : BasicBlockId}
    (hBBLen : bSrc.basicBlocks.length = bTgt.basicBlocks.length)
    (hLoops : checkZeroLhsDivRemBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks = true)
    (hEdge : checkNonZeroEdge bSrc.basicBlocks.length cert edgeEnv tgt = true)
    (hSound : NonZeroEnvSound bSrc.locals edgeEnv locs')
    (hLt : tgt < bSrc.basicBlocks.length) :
    ∃ bbSrc bbTgt entryEnv exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbTgt ∧
      Trusted.MirSemantics.getElem? cert tgt = some (some entryEnv) ∧
      NonZeroEnvSound bSrc.locals entryEnv locs' ∧
      stepNonZeroStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements = some exitEnv ∧
      checkZeroLhsDivRemBlock bSrc bTgt cert tgt bbSrc = true := by
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
      have hChkBlk := checkZeroLhsDivRemBlocksLoop_getElem? bSrc bTgt cert 0
        bSrc.basicBlocks tgt bbSrc hLoops hBBSrc
      rw [Nat.zero_add] at hChkBlk
      have hChkCopy := hChkBlk
      unfold checkZeroLhsDivRemBlock at hChkCopy
      rw [hCertTgt, hBBTgt] at hChkCopy; dsimp at hChkCopy
      let ⟨_, hStmtsMatch⟩ := bool_and_true hChkCopy
      cases hPair : stepNonZeroStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements with
      | none => rw [hPair] at hStmtsMatch; cases hStmtsMatch
      | some exitEnv =>
        exact ⟨bbSrc, bbTgt, entryEnv, exitEnv, hBBSrc, hBBTgt, rfl,
               nonZeroEnvImplies_sound hEdge hSound, hPair, hChkBlk⟩

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

private theorem zeroLhsDivRem_certified_query_lockstep
    {pSrc pTgt : Program} {cert : ProgramNonZeroCert}
    (hRel : isZeroLhsDivRemProgram pSrc pTgt = true)
    (hCert : checkZeroLhsDivRemProgram cert pSrc pTgt = true)
    (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hGen := isZeroLhsDivRemProgram_to_generic hRel
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLenB, hCertZip⟩ := bool_and_true hCert
  have hCertLen := nat_beq_eq hCertLenB
  apply lockstep_inv_query_iff
    (Inv := fun s =>
      ∃ frame bSrc bTgt bodyCert,
        s.frames = [frame] ∧
        Trusted.MirSemantics.getElem? pSrc.bodies frame.defId = some bSrc ∧
        Trusted.MirSemantics.getElem? pTgt.bodies frame.defId = some bTgt ∧
        Trusted.MirSemantics.getElem? cert frame.defId = some bodyCert ∧
        isZeroLhsDivRemBody bSrc bTgt = true ∧
        checkZeroLhsDivRemBody bodyCert bSrc bTgt = true ∧
        LocalsWellTyped bSrc.locals frame.locals ∧
        (frame.blockIdx < bSrc.basicBlocks.length →
          ∃ bbSrc bbTgt entryEnv curEnv exitEnv,
            Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx = some bbSrc ∧
            Trusted.MirSemantics.getElem? bTgt.basicBlocks frame.blockIdx = some bbTgt ∧
            Trusted.MirSemantics.getElem? bodyCert frame.blockIdx = some (some entryEnv) ∧
            NonZeroEnvSound bSrc.locals curEnv frame.locals ∧
            stepNonZeroStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements = some exitEnv ∧
            stepNonZeroStmtsPair bSrc.locals curEnv
              (bbSrc.statements.drop frame.stmtIdx)
              (bbTgt.statements.drop frame.stmtIdx) = some exitEnv ∧
            checkZeroLhsDivRemBlock bSrc bTgt bodyCert frame.blockIdx bbSrc = true))
    (genericProgRel_initState_eq isZeroLhsDivRemStmt_assignOnly hGen q)
  · intro s₀ hOk
    let ⟨_, _, bSrc, hBSrc, hNotEmp, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodiesRel hBSrc
    let ⟨bodyCert, bTgt', hBCert, hBTgt', hBodyCertOk⟩ :=
      listRel_zip_getElem? hCertLen hCertZip hBSrc
    rw [hBTgt] at hBTgt'; injection hBTgt' with hBEq; subst hBEq
    refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert, hBRel, hBodyCertOk,
            initLocalsLoop_wellTyped hArgs, ?_⟩
    intro hLt0
    have hBodyCertCopy := hBodyCertOk
    unfold checkZeroLhsDivRemBody at hBodyCertCopy
    let ⟨h123, hLoops⟩ := bool_and_true hBodyCertCopy
    let ⟨_, hEntryChk⟩ := bool_and_true h123
    rw [hNotEmp, if_bool_false rfl] at hEntryChk
    cases hC0 : Trusted.MirSemantics.getElem? bodyCert 0 with
    | none => rw [hC0] at hEntryChk; cases hEntryChk
    | some optE0 =>
      rw [hC0] at hEntryChk
      cases optE0 with
      | none => cases hEntryChk
      | some env₀ =>
        have hEnv0Sound := nonZeroEnvImplies_sound hEntryChk (initNonZeroEnvLoop_sound hArgs)
        let ⟨_, hBBsRel⟩ := bool_and_true hBRel
        have hBBLen := listRel_length hBBsRel
        let ⟨bbSrc, hBBSrc⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 hLt0
        let ⟨bbTgt, hBBTgt⟩ := getElem?_some_of_lt bTgt.basicBlocks 0
          (by rw [← hBBLen]; exact hLt0)
        have hChk0 := checkZeroLhsDivRemBlocksLoop_getElem? bSrc bTgt bodyCert 0
          bSrc.basicBlocks 0 bbSrc hLoops hBBSrc
        rw [Nat.zero_add] at hChk0
        have hChk0Copy := hChk0
        unfold checkZeroLhsDivRemBlock at hChk0Copy
        rw [hC0, hBBTgt] at hChk0Copy; dsimp at hChk0Copy
        let ⟨_, hStMatch⟩ := bool_and_true hChk0Copy
        cases hPair0 : stepNonZeroStmtsPair bSrc.locals env₀ bbSrc.statements bbTgt.statements with
        | none => rw [hPair0] at hStMatch; cases hStMatch
        | some exitEnv =>
          exact ⟨bbSrc, bbTgt, env₀, env₀, exitEnv, hBBSrc, hBBTgt, rfl,
                 hEnv0Sound, hPair0, hPair0, hChk0⟩
  · intro s hInv
    let ⟨frame, bSrc, bTgt, bodyCert, hFrames, hBSrc, hBTgt, hBCert,
         hBRel, hBodyCertOk, hWt, hBlkInv⟩ := hInv
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    have hBBLen := listRel_length hBBsRel
    have hBodyCertCopy := hBodyCertOk
    unfold checkZeroLhsDivRemBody at hBodyCertCopy
    let ⟨_, hLoops⟩ := bool_and_true hBodyCertCopy
    cases s with
    | mk fs cm =>
      dsimp at hFrames; subst hFrames
      cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
      | none =>
        have hBBTgtNone := (listRel_getElem?_none_iff frame.blockIdx hBBsRel).mp hBBSrc
        have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
            evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
          unfold evalStep; dsimp; rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgtNone]
        refine ⟨hEvEq, ?_⟩
        intro s' hStepS
        unfold evalStep at hStepS; dsimp at hStepS
        rw [hBSrc] at hStepS; dsimp at hStepS; rw [hBBSrc] at hStepS; cases hStepS
      | some bbSrc =>
        have hLtBlk : frame.blockIdx < bSrc.basicBlocks.length := getElem?_some_lt hBBSrc
        let ⟨bbSrc', bbTgt, entryEnv, curEnv, exitEnv,
             hBBSrc', hBBTgt, hCertEntry, hCurSound, hFullPair, hRemPair, hChkBlk⟩ :=
          hBlkInv hLtBlk
        rw [hBBSrc] at hBBSrc'; injection hBBSrc' with hBBEq; subst hBBEq
        let ⟨_, hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBsRel hBBSrc
        rw [hBBTgt] at hBBTgt'; injection hBBTgt' with hBBTEq; subst hBBTEq
        let ⟨h12BB, hTermRel⟩ := bool_and_true hBBRel
        let ⟨hCleanEq, hStmtsRel⟩ := bool_and_true h12BB
        have hStLenEq := listRel_length hStmtsRel
        cases hDropS : bbSrc.statements.drop frame.stmtIdx with
        | cons sSrc restS =>
          rw [hDropS] at hRemPair
          cases hDropT : bbTgt.statements.drop frame.stmtIdx with
          | nil => rw [hDropT] at hRemPair; cases hRemPair
          | cons sTgt restT =>
            rw [hDropT] at hRemPair
            dsimp [stepNonZeroStmtsPair] at hRemPair
            cases hOne : stepNonZeroStmtPair bSrc.locals curEnv sSrc sTgt with
            | none => rw [hOne] at hRemPair; cases hRemPair
            | some nextEnv =>
              rw [hOne] at hRemPair
              let ⟨hGetS, hDropNextS⟩ := getElem?_of_drop_eq_cons hDropS
              let ⟨hGetT, hDropNextT⟩ := getElem?_of_drop_eq_cons hDropT
              let ⟨hStmtEq, hStmtNext⟩ := stepNonZeroStmtPair_sound (cm := cm) hLocEq hCurSound hOne
              have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                  evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                unfold evalStep; dsimp
                rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
                rw [hGetS, hGetT]; dsimp
                exact hStmtEq
              refine ⟨hEvEq, ?_⟩
              intro s' hStepS
              unfold evalStep at hStepS; dsimp at hStepS
              rw [hBSrc] at hStepS; dsimp at hStepS
              rw [hBBSrc] at hStepS; dsimp at hStepS
              rw [hGetS] at hStepS; dsimp at hStepS
              let ⟨locs', hEqS', hNextSound⟩ := hStmtNext s' hStepS
              subst hEqS'
              refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                      hBRel, hBodyCertOk, hNextSound.1, ?_⟩
              intro _
              refine ⟨bbSrc, bbTgt, entryEnv, nextEnv, exitEnv,
                      hBBSrc, hBBTgt, hCertEntry, hNextSound, hFullPair, ?_, hChkBlk⟩
              dsimp; rw [hDropNextS, hDropNextT]; exact hRemPair
        | nil =>
          rw [hDropS] at hRemPair
          cases hDropT : bbTgt.statements.drop frame.stmtIdx with
          | cons _ _ => rw [hDropT] at hRemPair; cases hRemPair
          | nil =>
            rw [hDropT] at hRemPair
            injection hRemPair with hCurExit; subst hCurExit
            have hNoneS := getElem?_none_of_ge (le_of_drop_eq_nil hDropS)
            have hNoneT := getElem?_none_of_ge (le_of_drop_eq_nil hDropT)
            have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
              unfold evalStep; dsimp
              rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
              rw [hNoneS, hNoneT]; dsimp; rw [hStLenEq]
              cases Nat.beq frame.stmtIdx bbTgt.statements.length with
              | false => rfl
              | true =>
                rw [if_bool_true rfl, if_bool_true rfl]
                exact evalTerminator_eq_of_eq hLocEq (bool_beq_eq hCleanEq)
                  (terminatorEq_eq hTermRel)
            refine ⟨hEvEq, ?_⟩
            intro s' hStepS
            unfold evalStep at hStepS; dsimp at hStepS
            rw [hBSrc] at hStepS; dsimp at hStepS
            rw [hBBSrc] at hStepS; dsimp at hStepS
            rw [hNoneS] at hStepS; dsimp at hStepS
            cases hEnd : Nat.beq frame.stmtIdx bbSrc.statements.length with
            | false => rw [hEnd] at hStepS; cases hStepS
            | true =>
              rw [hEnd] at hStepS; dsimp at hStepS
              have hChkBlkCopy := hChkBlk
              unfold checkZeroLhsDivRemBlock at hChkBlkCopy
              rw [hCertEntry, hBBTgt] at hChkBlkCopy; dsimp at hChkBlkCopy
              let ⟨_, hTermChk⟩ := bool_and_true hChkBlkCopy
              rw [hFullPair] at hTermChk; dsimp at hTermChk
              unfold evalTerminator at hStepS
              cases hTm : bbSrc.terminator with
              | return_ =>
                rw [hTm] at hStepS; dsimp at hStepS
                cases hCl : bbSrc.cleanup with
                | true => rw [hCl] at hStepS; cases hStepS
                | false =>
                  rw [hCl] at hStepS; dsimp at hStepS
                  cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
                  | none => rw [h0] at hStepS; cases hStepS
                  | some sl0 =>
                    rw [h0] at hStepS
                    cases sl0 with
                    | dead => cases hStepS
                    | live o => cases o <;> cases hStepS
              | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
                rw [hTm] at hStepS; cases hStepS
              | goto tgt =>
                rw [hTm] at hStepS; rw [hTm] at hTermChk; dsimp at hTermChk
                injection hStepS with hSEq; subst hSEq
                refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                        hBRel, hBodyCertOk, hWt, ?_⟩
                intro hLtTgt
                let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                  checkNonZeroEdge_sound hBBLen hLoops hTermChk hCurSound hLtTgt
                exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
              | switchInt discr targets =>
                rw [hTm] at hStepS; rw [hTm] at hTermChk; dsimp at hStepS; dsimp at hTermChk
                let ⟨hOtherEdge, hBranchEdges⟩ := bool_and_true hTermChk
                cases hEvD : evalPrimitiveOperand bSrc.locals frame.locals discr with
                | error _ => rw [hEvD] at hStepS; cases hStepS
                | ok resD =>
                  let ⟨dv, locsAfter⟩ := resD
                  rw [hEvD] at hStepS; dsimp at hStepS
                  have hAfterSound := deinitMovePrimNonZero_sound hCurSound hEvD
                  cases dv with
                  | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hStepS
                  | bool bv =>
                    dsimp at hStepS
                    cases hSwB : evalBoolSwitchBranches bv targets.otherwise targets.branches with
                    | error _ => rw [hSwB] at hStepS; cases hStepS
                    | ok tgt =>
                      rw [hSwB] at hStepS
                      injection hStepS with hSEq; subst hSEq
                      refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                              hBRel, hBodyCertOk, hAfterSound.1, ?_⟩
                      intro hLtTgt
                      cases evalBoolSwitchBranches_cases hSwB with
                      | inl hIn =>
                        let ⟨cb, hMem⟩ := hIn
                        have hBrEdge := list_all_mem_true hBranchEdges hMem
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkNonZeroEdge_sound hBBLen hLoops hBrEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                      | inr hTgtEq =>
                        subst hTgtEq
                        change checkNonZeroEdge bSrc.basicBlocks.length bodyCert
                          (refineSwitchNonZeroEnv bSrc.locals
                            (deinitMoveOperandNonZero bSrc.locals curEnv discr)
                            discr targets.branches)
                          targets.otherwise = true at hOtherEdge
                        rw [refineSwitchNonZeroEnv_bool hCurSound.1 hEvD] at hOtherEdge
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkNonZeroEdge_sound hBBLen hLoops hOtherEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                  | scalar sv =>
                    dsimp at hStepS
                    cases hSwS : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                    | error _ => rw [hSwS] at hStepS; cases hStepS
                    | ok tgt =>
                      rw [hSwS] at hStepS
                      injection hStepS with hSEq; subst hSEq
                      refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                              hBRel, hBodyCertOk, hAfterSound.1, ?_⟩
                      intro hLtTgt
                      cases evalSwitchBranches_cases hSwS with
                      | inl hIn =>
                        let ⟨cb, hMem⟩ := hIn
                        have hBrEdge := list_all_mem_true hBranchEdges hMem
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkNonZeroEdge_sound hBBLen hLoops hBrEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                      | inr hFall =>
                        let ⟨hTgtEq, hGuardFn⟩ := hFall
                        subst hTgtEq
                        change checkNonZeroEdge bSrc.basicBlocks.length bodyCert
                          (refineSwitchNonZeroEnv bSrc.locals
                            (deinitMoveOperandNonZero bSrc.locals curEnv discr)
                            discr targets.branches)
                          targets.otherwise = true at hOtherEdge
                        have hOtherSound :=
                          refineSwitchNonZeroEnv_scalar hCurSound hAfterSound hEvD hGuardFn
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkNonZeroEdge_sound hBBLen hLoops hOtherEdge hOtherSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩

private theorem vc_transport_zeroLhsDivRem_certified_iff_priv
    (pSrc pTgt : Program) (cert : ProgramNonZeroCert)
    (hRel : isZeroLhsDivRemProgram pSrc pTgt = true)
    (hCert : checkZeroLhsDivRemProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  have hGen := isZeroLhsDivRemProgram_to_generic hRel
  let ⟨hHdr, hBodies⟩ := bool_and_true hGen
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hBHdr, _, hBBEmpty, _, hBounds, _⟩ :=
      genericBodyRel_storage_eq isZeroLhsDivRemStmt_assignOnly hBRel
    exact ⟨hBHdr, hBBEmpty, hBounds⟩
  · intro q
    exact zeroLhsDivRem_certified_query_lockstep hRel hCert q
  · intro defId args
    have hRelE : isZeroLhsDivRemProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true := by
      let ⟨hPH, hPB⟩ := bool_and_true hRel
      exact bool_and_intro (programHeaderEq_entryProg defId hPH) hPB
    exact (zeroLhsDivRem_certified_query_lockstep hRelE hCert { args := args }).1

/-! #### Theorem 4a: Unconditional Forward Codegen Refinement for
`AbsorbingOrSelfCancel` -/

private theorem isAbsorbingOrSelfCancelStmt_assignOnly (locs : List MirTy)
    (s₁ s₂ : StatementKind) (h : isAbsorbingOrSelfCancelStmt locs s₁ s₂ = true) :
    s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂) := by
  unfold isAbsorbingOrSelfCancelStmt at h
  cases bool_or_true h with
  | inr hEq => exact Or.inl (stmtEq_eq hEq)
  | inl hRw =>
    cases s₁ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hRw
    | assign d₁ rv₁ =>
      cases rv₁ with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
      | aggregateTuple _ | unsupported => cases hRw
      | binaryOp op lhs rhs =>
        cases s₂ with
        | nop | storageLive _ | storageDead _ | unsupported => cases hRw
        | assign d₂ rv₂ =>
          exact Or.inr ⟨d₁, .binaryOp op lhs rhs, d₂, rv₂, rfl, rfl⟩

private theorem isAbsorbingOrSelfCancelProgram_to_generic {pSrc pTgt : Program}
    (h : isAbsorbingOrSelfCancelProgram pSrc pTgt = true) :
    genericProgRel isAbsorbingOrSelfCancelStmt pSrc pTgt = true := by
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  refine bool_and_intro hHdr ?_
  refine listRel_mono (fun b₁ b₂ hb => ?_) hBodies
  let ⟨hBHdr, hBBs⟩ := bool_and_true hb
  exact bool_and_intro hBHdr (listRel_mono (fun _ _ hbb => hbb) hBBs)

private theorem evalPrimitiveOperand_const_eq {bodyLocals : List MirTy} {locals : List LocalSlot}
    {c : ConstOperand} {vc v : Val} {locals' : List LocalSlot}
    (hEvC : evalConstLit c.ty c.lit = .ok vc)
    (hEvOp : evalPrimitiveOperand bodyLocals locals (.constant c) = .ok (v, locals')) :
    v = vc ∧ locals' = locals := by
  dsimp [evalPrimitiveOperand, evalOperandToSlot] at hEvOp
  rw [hEvC] at hEvOp; dsimp at hEvOp
  cases hPrim : isPrimitiveReadableTy c.ty with
  | false => rw [hPrim] at hEvOp; cases hEvOp
  | true =>
    rw [hPrim] at hEvOp; dsimp at hEvOp
    injection hEvOp with hEq
    injection hEq with hV hL
    exact ⟨hV.symm, hL.symm⟩

private theorem evalPrimitiveOperand_copy_locals_eq {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {p : Place} {v : Val}
    (hEv : evalPrimitiveOperand bodyLocals locals (.copy p) = .ok (v, locals')) :
    locals' = locals := by
  dsimp [evalPrimitiveOperand, evalOperandToSlot] at hEv
  cases hPE : p.projection.isEmpty with
  | false => rw [hPE] at hEv; cases hEv
  | true =>
    rw [hPE] at hEv; dsimp at hEv
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
        | live opt =>
          dsimp at hEv
          cases hPr : isPrimitiveReadableTy ty with
          | false => rw [hPr] at hEv; cases hEv
          | true =>
            rw [hPr] at hEv; dsimp at hEv
            cases opt with
            | none => cases hEv
            | some _ =>
              injection hEv with h1; injection h1 with _ hL
              exact hL.symm

private theorem evalStatement_absorbingAndSelfCancel_fwd (b₁ b₂ : Body) (f₁ f₂ : FrameState)
    (cm : CallerMemory) (s₁ s₂ : StatementKind) (s' : State)
    (hLocEq : b₁.locals = b₂.locals)
    (hInv : LocalsFwdRefines b₁.locals f₁.locals f₂.locals)
    (hRel : isAbsorbingOrSelfCancelStmt b₁.locals s₁ s₂ = true)
    (hEv : evalStatement b₁ f₁ cm s₁ = .step s') :
    ∃ locs1' locs2',
      s' = { frames := [{ f₁ with stmtIdx := f₁.stmtIdx + 1, locals := locs1' }],
             callerMem := cm } ∧
      evalStatement b₂ f₂ cm s₂ =
        .step { frames := [{ f₂ with stmtIdx := f₂.stmtIdx + 1, locals := locs2' }],
                callerMem := cm } ∧
      LocalsFwdRefines b₁.locals locs1' locs2' := by
  unfold isAbsorbingOrSelfCancelStmt at hRel
  cases bool_or_true hRel with
  | inr hEq =>
    rw [stmtEq_eq hEq] at hEv
    exact evalStatement_fwd_eq hLocEq hInv hEv
  | inl hRw =>
    cases s₁ with
    | nop | storageLive _ | storageDead _ | unsupported => cases hRw
    | assign dst rv₁ =>
      cases rv₁ with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
      | aggregateTuple _ | unsupported => cases hRw
      | binaryOp op lhs rhs =>
        cases s₂ with
        | nop | storageLive _ | storageDead _ | unsupported => cases hRw
        | assign dst' rv₂ =>
          cases rv₂ with
          | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
          | aggregateTuple _ | unsupported => cases hRw
          | use opnd₂ =>
            cases opnd₂ with
            | copy _ | move _ => cases hRw
            | constant cOut =>
              unfold isAbsorbingOrSelfCancelRewrite at hRw
              let ⟨h12, hBodyMatch⟩ := bool_and_true hRw
              let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12
              have hDEq := placeEq_eq hDstEq; subst hDEq
              cases hDstTy : Trusted.MirSemantics.getElem? b₁.locals dst.localId with
              | none => rw [hDstTy] at hBodyMatch; cases hBodyMatch
              | some dstTy =>
                rw [hDstTy] at hBodyMatch
                dsimp [evalStatement] at hEv
                rw [hDstEmp] at hEv; dsimp at hEv
                rw [hDstTy] at hEv; dsimp at hEv
                dsimp [evalRvalue] at hEv
                cases hEL : evalPrimitiveOperand b₁.locals f₁.locals lhs with
                | error _ => rw [hEL] at hEv; cases hEv
                | ok resL =>
                  let ⟨vl, locsL⟩ := resL
                  rw [hEL] at hEv; dsimp at hEv
                  let ⟨hInvL, hChkL⟩ := evalPrimitiveOperand_discarded_fwd hInv hEL
                  cases hER : evalPrimitiveOperand b₁.locals locsL rhs with
                  | error _ => rw [hER] at hEv; cases hEv
                  | ok resR =>
                    let ⟨vr, locsR⟩ := resR
                    rw [hER] at hEv; dsimp at hEv
                    let ⟨hInvR, hChkR⟩ := evalPrimitiveOperand_discarded_fwd hInvL hER
                    cases hEB : evalBinOp op vl vr with
                    | error _ => rw [hEB] at hEv; cases hEv
                    | ok resV =>
                      rw [hEB] at hEv; dsimp at hEv
                      cases hW1 : writePlace locsR dst.localId dstTy resV with
                      | error _ => rw [hW1] at hEv; cases hEv
                      | ok locs1' =>
                        rw [hW1] at hEv
                        injection hEv with hStEq
                        let ⟨locs2', hW2, hInv2⟩ := writePlace_fwd hInvR hDstTy hW1
                        have hOutConst : evalConstLit cOut.ty cOut.lit = .ok resV ∧ cOut.ty = dstTy := by
                          cases bool_or_true hBodyMatch with
                          | inl hLR =>
                            cases bool_or_true hLR with
                            | inl hLeft =>
                              cases lhs with
                              | copy _ | move _ => cases hLeft
                              | constant c =>
                                cases hStR : operandStaticTy? b₁.locals rhs with
                                | none => rw [hStR] at hLeft; cases hLeft
                                | some rhsTy =>
                                  rw [hStR] at hLeft
                                  let ⟨vc, vOut, hEvC, hEvCO, hCOTy, _, hBinOk⟩ :=
                                    evalBinOp_leftAbsorbing hLeft (hChkR rhsTy hStR)
                                  let ⟨hVlEq, _⟩ := evalPrimitiveOperand_const_eq hEvC hEL
                                  subst hVlEq
                                  rw [hBinOk] at hEB; injection hEB with hVOut; subst hVOut
                                  exact ⟨hEvCO, hCOTy⟩
                            | inr hRight =>
                              cases rhs with
                              | copy _ | move _ => cases hRight
                              | constant c =>
                                cases hStL : operandStaticTy? b₁.locals lhs with
                                | none => rw [hStL] at hRight; cases hRight
                                | some lhsTy =>
                                  rw [hStL] at hRight
                                  let ⟨vc, vOut, hEvC, hEvCO, hCOTy, _, hBinOk⟩ :=
                                    evalBinOp_rightAbsorbing hRight (hChkL lhsTy hStL)
                                  let ⟨hVrEq, _⟩ := evalPrimitiveOperand_const_eq hEvC hER
                                  subst hVrEq
                                  rw [hBinOk] at hEB; injection hEB with hVOut; subst hVOut
                                  exact ⟨hEvCO, hCOTy⟩
                          | inr hSelfArm =>
                            cases lhs with
                            | move _ | constant _ => cases hSelfArm
                            | copy p₁ =>
                              cases rhs with
                              | move _ | constant _ => cases hSelfArm
                              | copy p₂ =>
                                let ⟨hP12, hSelfRest⟩ := bool_and_true hSelfArm
                                let ⟨hPEq, hP1Emp⟩ := bool_and_true hP12
                                have hP12Eq := placeEq_eq hPEq; subst hP12Eq
                                cases hOpTy : Trusted.MirSemantics.getElem? b₁.locals p₁.localId with
                                | none => rw [hOpTy] at hSelfRest; cases hSelfRest
                                | some opndTy =>
                                  rw [hOpTy] at hSelfRest
                                  have hStP1 : operandStaticTy? b₁.locals (.copy p₁) = some opndTy := by
                                    dsimp [operandStaticTy?]; rw [hP1Emp]; dsimp; exact hOpTy
                                  have hLocsLEq := evalPrimitiveOperand_copy_locals_eq hEL
                                  rw [hLocsLEq, hEL] at hER
                                  injection hER with hTupEq; injection hTupEq with hVrVl _
                                  subst hVrVl
                                  let ⟨vOut, hEvCO, hCOTy, _, hBinOk⟩ :=
                                    evalBinOp_selfCancel hSelfRest (hChkL opndTy hStP1)
                                  rw [hBinOk] at hEB; injection hEB with hVOut; subst hVOut
                                  exact ⟨hEvCO, hCOTy⟩
                        let ⟨hEvCO, hCOTy⟩ := hOutConst
                        refine ⟨locs1', locs2', hStEq.symm, ?_, hInv2⟩
                        dsimp [evalStatement]
                        rw [hDstEmp]; dsimp
                        rw [← hLocEq, hDstTy]; dsimp
                        dsimp [evalRvalue, evalOperandToSlot]
                        rw [hEvCO]; dsimp
                        rw [hCOTy, mirTy_beq_refl dstTy]; dsimp
                        rw [hW2]

private theorem codegen_absorbingAndSelfCancel_refines_unconditional_priv
    (pSrc pTgt : Program)
    (hRel : isAbsorbingOrSelfCancelProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt :=
  forwardCodegenRefines_of_stmtRel_fwd
    isAbsorbingOrSelfCancelStmt_assignOnly
    evalStatement_absorbingAndSelfCancel_fwd
    (isAbsorbingOrSelfCancelProgram_to_generic hRel)

/-! #### Theorem 4b: Certified Bidirectional VC Transport for
`AbsorbingOrSelfCancel` -/

private noncomputable def AbsSlotSound (ty : MirTy) (abs : AbsSlot) (sl : LocalSlot) : Prop :=
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
  | cons t₀ rest ih =>
    intro k ty h
    cases k with
    | zero =>
      injection h with hEq; subst hEq
      dsimp [initAbsEnvLoop, Trusted.MirSemantics.getElem?]
    | succ m =>
      dsimp [Trusted.MirSemantics.getElem?] at h
      dsimp [initAbsEnvLoop, Trusted.MirSemantics.getElem?]
      rw [ih (base + 1) m ty h]
      rw [Nat.add_assoc, Nat.add_comm 1 m]

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

private theorem operandCertifiedLivePrimitiveRead_sound {bodyLocals : List MirTy}
    {env : List AbsSlot} {locals : List LocalSlot} {opnd : Operand}
    (hEnv : AbsEnvSound bodyLocals env locals)
    (hCertOp : operandCertifiedLivePrimitiveRead bodyLocals env opnd = true) :
    ∃ v : Val,
      evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals) ∧
      (∀ ty, operandStaticTy? bodyLocals opnd = some ty → checkVal v ty = true) := by
  cases opnd with
  | move _ => cases hCertOp
  | constant c =>
    dsimp [operandCertifiedLivePrimitiveRead] at hCertOp
    let ⟨hPrim, hLitOk⟩ := bool_and_true hCertOp
    cases hEvC : evalConstLit c.ty c.lit with
    | error _ => rw [hEvC] at hLitOk; cases hLitOk
    | ok v =>
      have hEvP : evalPrimitiveOperand bodyLocals locals (.constant c) = .ok (v, locals) := by
        dsimp [evalPrimitiveOperand, evalOperandToSlot]
        rw [hEvC]; dsimp; rw [hPrim]; rfl
      exact ⟨v, hEvP, (evalPrimitiveOperand_preserves_wt hEnv.1 hEvP).2⟩
  | copy p =>
    dsimp [operandCertifiedLivePrimitiveRead] at hCertOp
    let ⟨hPEmp, hMatch⟩ := bool_and_true hCertOp
    cases hTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
    | none => rw [hTy] at hMatch; cases hMatch
    | some ty =>
      rw [hTy] at hMatch
      cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
      | none => rw [hAbs] at hMatch; cases hMatch
      | some abs =>
        rw [hAbs] at hMatch
        cases abs with
        | dead | liveUninit => cases hMatch
        | liveInit =>
          dsimp at hMatch
          have hLtL : p.localId < locals.length := by
            rw [hEnv.1.1]; exact getElem?_some_lt hTy
          let ⟨sl, hSl⟩ := getElem?_some_of_lt locals p.localId hLtL
          let ⟨_, v, hSlEq⟩ := hEnv.2.2 p.localId ty .liveInit sl hTy hAbs hSl
          have hEvP : evalPrimitiveOperand bodyLocals locals (.copy p) = .ok (v, locals) := by
            dsimp [evalPrimitiveOperand, evalOperandToSlot]
            rw [hPEmp]; dsimp; rw [hTy, hSl, hSlEq]; dsimp; rw [hMatch]; rfl
          exact ⟨v, hEvP, (evalPrimitiveOperand_preserves_wt hEnv.1 hEvP).2⟩

private theorem stepAbsorbStmtPair_sound {bSrc bTgt : Body}
    {env env' : List AbsSlot} {frame : FrameState}
    {cm : CallerMemory} {sSrc sTgt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEnv : AbsEnvSound bSrc.locals env frame.locals)
    (hPair : stepAbsorbStmtPair bSrc.locals env sSrc sTgt = some env') :
    evalStatement bSrc frame cm sSrc = evalStatement bTgt frame cm sTgt ∧
    (∀ s', evalStatement bSrc frame cm sSrc = .step s' →
      ∃ locs',
        s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
               callerMem := cm } ∧
        AbsEnvSound bSrc.locals env' locs') := by
  unfold stepAbsorbStmtPair at hPair
  cases hStEq : stmtEq sSrc sTgt with
  | true =>
    rw [hStEq, if_bool_true rfl] at hPair
    have hEq := stmtEq_eq hStEq; subst hEq
    refine ⟨evalStatement_eq_of_same frame cm sSrc hLocEq, ?_⟩
    intro s' hEv
    cases sSrc with
    | nop =>
      injection hPair with hEnvEq; subst hEnvEq
      injection hEv with hSEq; subst hSEq
      exact ⟨frame.locals, rfl, hEnv⟩
    | unsupported => cases hEv
    | storageLive id =>
      dsimp at hPair
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals id with
      | none => rw [hTy] at hPair; cases hPair
      | some ty =>
        rw [hTy] at hPair; dsimp at hPair
        dsimp [evalStatement] at hEv; rw [hTy] at hEv; dsimp at hEv
        cases hSetL : setElem? frame.locals id (liveUninitSlot ty) with
        | none => rw [hSetL] at hEv; cases hEv
        | some locs' =>
          rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
          exact ⟨locs', rfl,
            absEnvSound_set hEnv hTy hPair hSetL (absSlotSound_liveUninit ty)⟩
    | storageDead id =>
      dsimp at hPair
      cases hZ : Nat.beq id 0 with
      | true => rw [hZ] at hPair; cases hPair
      | false =>
        rw [hZ] at hPair; dsimp at hPair
        dsimp [evalStatement] at hEv; rw [hZ] at hEv; dsimp at hEv
        cases hSetL : setElem? frame.locals id .dead with
        | none => rw [hSetL] at hEv; cases hEv
        | some locs' =>
          rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
          have hLt : id < bSrc.locals.length := by
            rw [← hEnv.2.1]
            cases Nat.lt_or_ge id env.length with
            | inl hlt => exact hlt
            | inr hge =>
              rw [setElem?_none_of_ge env id .dead hge] at hPair; cases hPair
          let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals id hLt
          exact ⟨locs', rfl,
            absEnvSound_set hEnv hTy hPair hSetL ⟨True.intro, True.intro⟩⟩
    | assign dst rv =>
      dsimp at hPair
      cases hPEmp : dst.projection.isEmpty with
      | false => rw [hPEmp] at hPair; cases hPair
      | true =>
        rw [hPEmp] at hPair; dsimp at hPair
        cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
        | none => rw [hDstTy] at hPair; cases hPair
        | some dstTy =>
          rw [hDstTy] at hPair; dsimp at hPair
          dsimp [evalStatement] at hEv; rw [hPEmp] at hEv; dsimp at hEv
          rw [hDstTy] at hEv; dsimp at hEv
          cases hRv : evalRvalue bSrc.locals frame.locals dstTy rv with
          | error _ => rw [hRv] at hEv; cases hEv
          | ok res =>
            let ⟨val, locs1⟩ := res
            rw [hRv] at hEv; dsimp at hEv
            have hEnv1 := deinitMovesInRvalueAbs_sound hEnv hRv
            cases hW : writePlace locs1 dst.localId dstTy val with
            | error _ => rw [hW] at hEv; cases hEv
            | ok locs' =>
              rw [hW] at hEv; injection hEv with hSEq; subst hSEq
              dsimp [writePlace] at hW
              cases hChk : checkVal val dstTy with
              | false => rw [hChk] at hW; cases hW
              | true =>
                rw [hChk] at hW; dsimp at hW
                cases hSl1 : Trusted.MirSemantics.getElem? locs1 dst.localId with
                | none => rw [hSl1] at hW; cases hW
                | some sl1 =>
                  rw [hSl1] at hW
                  cases sl1 with
                  | dead => cases hW
                  | live _ =>
                    cases hSetL : setElem? locs1 dst.localId (.live (some val)) with
                    | none => rw [hSetL] at hW; cases hW
                    | some locsW =>
                      rw [hSetL] at hW; injection hW with hWEq; subst hWEq
                      exact ⟨locsW, rfl,
                        absEnvSound_set hEnv1 hDstTy hPair hSetL ⟨hChk, ⟨val, rfl⟩⟩⟩
  | false =>
    rw [hStEq, if_bool_false rfl] at hPair
    cases sSrc with
    | nop | storageLive _ | storageDead _ | unsupported => cases hPair
    | assign dst rvS =>
      cases rvS with
      | use _ | unaryOp _ _ | discriminant _ | ref _ _
      | addressOf _ | aggregateTuple _ | unsupported => cases hPair
      | binaryOp op lhs rhs =>
        dsimp at hPair
        cases hRw : isAbsorbingOrSelfCancelRewrite bSrc.locals
            (.assign dst (.binaryOp op lhs rhs)) sTgt with
        | false => rw [hRw] at hPair; cases hPair
        | true =>
          rw [hRw] at hPair; dsimp at hPair
          cases hBothLive : (operandCertifiedLivePrimitiveRead bSrc.locals env lhs &&
              operandCertifiedLivePrimitiveRead bSrc.locals env rhs) with
          | false => rw [hBothLive] at hPair; cases hPair
          | true =>
            rw [hBothLive] at hPair; dsimp at hPair
            let ⟨hCertL, hCertR⟩ := bool_and_true hBothLive
            let ⟨vl, hEL, hChkL⟩ := operandCertifiedLivePrimitiveRead_sound hEnv hCertL
            let ⟨vr, hER, hChkR⟩ := operandCertifiedLivePrimitiveRead_sound hEnv hCertR
            cases sTgt with
            | nop | storageLive _ | storageDead _ | unsupported => cases hRw
            | assign dst' rvT =>
              cases rvT with
              | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
              | addressOf _ | aggregateTuple _ | unsupported => cases hRw
              | use opndT =>
                cases opndT with
                | copy _ | move _ => cases hRw
                | constant cOut =>
                  unfold isAbsorbingOrSelfCancelRewrite at hRw
                  let ⟨h12, hBodyMatch⟩ := bool_and_true hRw
                  let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12
                  have hDEq := placeEq_eq hDstEq; subst hDEq
                  cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
                  | none => rw [hDstTy] at hBodyMatch; cases hBodyMatch
                  | some dstTy =>
                    rw [hDstTy] at hBodyMatch
                    have hOutAll :
                        ∃ vOut,
                          evalConstLit cOut.ty cOut.lit = .ok vOut ∧
                          cOut.ty = dstTy ∧
                          evalBinOp op vl vr = .ok vOut := by
                      cases bool_or_true hBodyMatch with
                      | inl hLR =>
                        cases bool_or_true hLR with
                        | inl hLeft =>
                          cases lhs with
                          | copy _ | move _ => cases hLeft
                          | constant c =>
                            cases hStR : operandStaticTy? bSrc.locals rhs with
                            | none => rw [hStR] at hLeft; cases hLeft
                            | some rhsTy =>
                              rw [hStR] at hLeft
                              let ⟨vc, vOut, hEvC, hEvCO, hCOTy, _, hBinOk⟩ :=
                                evalBinOp_leftAbsorbing hLeft (hChkR rhsTy hStR)
                              let ⟨hVlEq, _⟩ := evalPrimitiveOperand_const_eq hEvC hEL
                              subst hVlEq
                              exact ⟨vOut, hEvCO, hCOTy, hBinOk⟩
                        | inr hRight =>
                          cases rhs with
                          | copy _ | move _ => cases hRight
                          | constant c =>
                            cases hStL : operandStaticTy? bSrc.locals lhs with
                            | none => rw [hStL] at hRight; cases hRight
                            | some lhsTy =>
                              rw [hStL] at hRight
                              let ⟨vc, vOut, hEvC, hEvCO, hCOTy, _, hBinOk⟩ :=
                                evalBinOp_rightAbsorbing hRight (hChkL lhsTy hStL)
                              let ⟨hVrEq, _⟩ := evalPrimitiveOperand_const_eq hEvC hER
                              subst hVrEq
                              exact ⟨vOut, hEvCO, hCOTy, hBinOk⟩
                      | inr hSelfArm =>
                        cases lhs with
                        | move _ | constant _ => cases hSelfArm
                        | copy p₁ =>
                          cases rhs with
                          | move _ | constant _ => cases hSelfArm
                          | copy p₂ =>
                            let ⟨hP12, hSelfRest⟩ := bool_and_true hSelfArm
                            let ⟨hPEq, hP1Emp⟩ := bool_and_true hP12
                            have hP12Eq := placeEq_eq hPEq; subst hP12Eq
                            cases hOpTy : Trusted.MirSemantics.getElem? bSrc.locals p₁.localId with
                            | none => rw [hOpTy] at hSelfRest; cases hSelfRest
                            | some opndTy =>
                              rw [hOpTy] at hSelfRest
                              have hStP1 : operandStaticTy? bSrc.locals (.copy p₁) = some opndTy := by
                                dsimp [operandStaticTy?]; rw [hP1Emp]; dsimp; exact hOpTy
                              have hSame := hEL.symm.trans hER
                              injection hSame with hTup; injection hTup with hVlVr _
                              subst hVlVr
                              let ⟨vOut, hEvCO, hCOTy, _, hBinOk⟩ :=
                                evalBinOp_selfCancel hSelfRest (hChkL opndTy hStP1)
                              exact ⟨vOut, hEvCO, hCOTy, hBinOk⟩
                    let ⟨vOut, hEvCO, hCOTy, hBinOk⟩ := hOutAll
                    have hRvSrc :
                        evalRvalue bSrc.locals frame.locals dstTy (.binaryOp op lhs rhs) =
                        .ok (vOut, frame.locals) := by
                      dsimp [evalRvalue]; rw [hEL]; dsimp; rw [hER]; dsimp; rw [hBinOk]
                    have hRvTgt :
                        evalRvalue bSrc.locals frame.locals dstTy (.use (.constant cOut)) =
                        .ok (vOut, frame.locals) := by
                      dsimp [evalRvalue, evalOperandToSlot]
                      rw [hEvCO]; dsimp; rw [hCOTy, mirTy_beq_refl dstTy]; dsimp
                    have hStmtEq :
                        evalStatement bSrc frame cm (.assign dst (.binaryOp op lhs rhs)) =
                        evalStatement bTgt frame cm (.assign dst (.use (.constant cOut))) := by
                      dsimp [evalStatement]
                      rw [← hLocEq, hDstEmp]; dsimp
                      rw [hDstTy]; dsimp; rw [hRvSrc, hRvTgt]
                    refine ⟨hStmtEq, ?_⟩
                    intro s' hEvS
                    dsimp [evalStatement] at hEvS
                    rw [hDstEmp] at hEvS; dsimp at hEvS
                    rw [hDstTy] at hEvS; dsimp at hEvS
                    rw [hRvSrc] at hEvS; dsimp at hEvS
                    dsimp [writePlace] at hEvS
                    have hChkOut : checkVal vOut dstTy = true := by
                      rw [← hCOTy]; exact evalConstLit_checkVal hEvCO
                    rw [hChkOut] at hEvS; dsimp at hEvS
                    cases hSlD : Trusted.MirSemantics.getElem? frame.locals dst.localId with
                    | none => rw [hSlD] at hEvS; cases hEvS
                    | some slD =>
                      rw [hSlD] at hEvS
                      cases slD with
                      | dead => cases hEvS
                      | live _ =>
                        cases hSetL : setElem? frame.locals dst.localId (.live (some vOut)) with
                        | none => rw [hSetL] at hEvS; cases hEvS
                        | some locsW =>
                          rw [hSetL] at hEvS; injection hEvS with hSEq; subst hSEq
                          exact ⟨locsW, rfl,
                            absEnvSound_set hEnv hDstTy hPair hSetL ⟨hChkOut, ⟨vOut, rfl⟩⟩⟩

private theorem checkAbsorbingBlocksLoop_getElem? (bSrc bTgt : Body)
    (cert : BodyAbsCert) :
    ∀ base bbs k bbSrc,
      checkAbsorbingBlocksLoop bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      checkAbsorbingBlock bSrc bTgt cert (base + k) bbSrc = true := by
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

private theorem checkAbsEdge_sound {bSrc bTgt : Body} {cert : BodyAbsCert}
    {edgeEnv : List AbsSlot} {locs' : List LocalSlot} {tgt : BasicBlockId}
    (hBBLen : bSrc.basicBlocks.length = bTgt.basicBlocks.length)
    (hLoops : checkAbsorbingBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks = true)
    (hEdge : checkAbsEdge bSrc.basicBlocks.length cert edgeEnv tgt = true)
    (hSound : AbsEnvSound bSrc.locals edgeEnv locs')
    (hLt : tgt < bSrc.basicBlocks.length) :
    ∃ bbSrc bbTgt entryEnv exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbTgt ∧
      Trusted.MirSemantics.getElem? cert tgt = some (some entryEnv) ∧
      AbsEnvSound bSrc.locals entryEnv locs' ∧
      stepAbsorbStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements = some exitEnv ∧
      checkAbsorbingBlock bSrc bTgt cert tgt bbSrc = true := by
  unfold checkAbsEdge at hEdge
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
      have hChkBlk := checkAbsorbingBlocksLoop_getElem? bSrc bTgt cert 0
        bSrc.basicBlocks tgt bbSrc hLoops hBBSrc
      rw [Nat.zero_add] at hChkBlk
      have hChkCopy := hChkBlk
      unfold checkAbsorbingBlock at hChkCopy
      rw [hCertTgt, hBBTgt] at hChkCopy; dsimp at hChkCopy
      let ⟨_, hStmtsMatch⟩ := bool_and_true hChkCopy
      cases hPair : stepAbsorbStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements with
      | none => rw [hPair] at hStmtsMatch; cases hStmtsMatch
      | some exitEnv =>
        exact ⟨bbSrc, bbTgt, entryEnv, exitEnv, hBBSrc, hBBTgt, rfl,
               absEnvImplies_sound hEdge hSound, hPair, hChkBlk⟩

private theorem absorbingAndSelfCancel_certified_query_lockstep
    {pSrc pTgt : Program} {cert : ProgramAbsCert}
    (hRel : isAbsorbingOrSelfCancelProgram pSrc pTgt = true)
    (hCert : checkAbsorbingOrSelfCancelProgram cert pSrc pTgt = true)
    (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hGen := isAbsorbingOrSelfCancelProgram_to_generic hRel
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLenB, hCertZip⟩ := bool_and_true hCert
  have hCertLen := nat_beq_eq hCertLenB
  apply lockstep_inv_query_iff
    (Inv := fun s =>
      ∃ frame bSrc bTgt bodyCert,
        s.frames = [frame] ∧
        Trusted.MirSemantics.getElem? pSrc.bodies frame.defId = some bSrc ∧
        Trusted.MirSemantics.getElem? pTgt.bodies frame.defId = some bTgt ∧
        Trusted.MirSemantics.getElem? cert frame.defId = some bodyCert ∧
        isAbsorbingOrSelfCancelBody bSrc bTgt = true ∧
        checkAbsorbingOrSelfCancelBody bodyCert bSrc bTgt = true ∧
        LocalsWellTyped bSrc.locals frame.locals ∧
        (frame.blockIdx < bSrc.basicBlocks.length →
          ∃ bbSrc bbTgt entryEnv curEnv exitEnv,
            Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx = some bbSrc ∧
            Trusted.MirSemantics.getElem? bTgt.basicBlocks frame.blockIdx = some bbTgt ∧
            Trusted.MirSemantics.getElem? bodyCert frame.blockIdx = some (some entryEnv) ∧
            AbsEnvSound bSrc.locals curEnv frame.locals ∧
            stepAbsorbStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements = some exitEnv ∧
            stepAbsorbStmtsPair bSrc.locals curEnv
              (bbSrc.statements.drop frame.stmtIdx)
              (bbTgt.statements.drop frame.stmtIdx) = some exitEnv ∧
            checkAbsorbingBlock bSrc bTgt bodyCert frame.blockIdx bbSrc = true))
    (genericProgRel_initState_eq isAbsorbingOrSelfCancelStmt_assignOnly hGen q)
  · intro s₀ hOk
    let ⟨_, _, bSrc, hBSrc, hNotEmp, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodiesRel hBSrc
    let ⟨bodyCert, bTgt', hBCert, hBTgt', hBodyCertOk⟩ :=
      listRel_zip_getElem? hCertLen hCertZip hBSrc
    rw [hBTgt] at hBTgt'; injection hBTgt' with hBEq; subst hBEq
    refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert, hBRel, hBodyCertOk,
            initLocalsLoop_wellTyped hArgs, ?_⟩
    intro hLt0
    have hBodyCertCopy := hBodyCertOk
    unfold checkAbsorbingOrSelfCancelBody at hBodyCertCopy
    let ⟨h123, hLoops⟩ := bool_and_true hBodyCertCopy
    let ⟨_, hEntryChk⟩ := bool_and_true h123
    rw [hNotEmp, if_bool_false rfl] at hEntryChk
    cases hC0 : Trusted.MirSemantics.getElem? bodyCert 0 with
    | none => rw [hC0] at hEntryChk; cases hEntryChk
    | some optE0 =>
      rw [hC0] at hEntryChk
      cases optE0 with
      | none => cases hEntryChk
      | some env₀ =>
        have hEnv0Sound := absEnvImplies_sound hEntryChk (initAbsEnvLoop_sound hArgs)
        let ⟨_, hBBsRel⟩ := bool_and_true hBRel
        have hBBLen := listRel_length hBBsRel
        let ⟨bbSrc, hBBSrc⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 hLt0
        let ⟨bbTgt, hBBTgt⟩ := getElem?_some_of_lt bTgt.basicBlocks 0
          (by rw [← hBBLen]; exact hLt0)
        have hChk0 := checkAbsorbingBlocksLoop_getElem? bSrc bTgt bodyCert 0
          bSrc.basicBlocks 0 bbSrc hLoops hBBSrc
        rw [Nat.zero_add] at hChk0
        have hChk0Copy := hChk0
        unfold checkAbsorbingBlock at hChk0Copy
        rw [hC0, hBBTgt] at hChk0Copy; dsimp at hChk0Copy
        let ⟨_, hStMatch⟩ := bool_and_true hChk0Copy
        cases hPair0 : stepAbsorbStmtsPair bSrc.locals env₀ bbSrc.statements bbTgt.statements with
        | none => rw [hPair0] at hStMatch; cases hStMatch
        | some exitEnv =>
          exact ⟨bbSrc, bbTgt, env₀, env₀, exitEnv, hBBSrc, hBBTgt, rfl,
                 hEnv0Sound, hPair0, hPair0, hChk0⟩
  · intro s hInv
    let ⟨frame, bSrc, bTgt, bodyCert, hFrames, hBSrc, hBTgt, hBCert,
         hBRel, hBodyCertOk, hWt, hBlkInv⟩ := hInv
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    have hBBLen := listRel_length hBBsRel
    have hBodyCertCopy := hBodyCertOk
    unfold checkAbsorbingOrSelfCancelBody at hBodyCertCopy
    let ⟨_, hLoops⟩ := bool_and_true hBodyCertCopy
    cases s with
    | mk fs cm =>
      dsimp at hFrames; subst hFrames
      cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
      | none =>
        have hBBTgtNone := (listRel_getElem?_none_iff frame.blockIdx hBBsRel).mp hBBSrc
        have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
            evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
          unfold evalStep; dsimp; rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgtNone]
        refine ⟨hEvEq, ?_⟩
        intro s' hStepS
        unfold evalStep at hStepS; dsimp at hStepS
        rw [hBSrc] at hStepS; dsimp at hStepS; rw [hBBSrc] at hStepS; cases hStepS
      | some bbSrc =>
        have hLtBlk : frame.blockIdx < bSrc.basicBlocks.length := getElem?_some_lt hBBSrc
        let ⟨bbSrc', bbTgt, entryEnv, curEnv, exitEnv,
             hBBSrc', hBBTgt, hCertEntry, hCurSound, hFullPair, hRemPair, hChkBlk⟩ :=
          hBlkInv hLtBlk
        rw [hBBSrc] at hBBSrc'; injection hBBSrc' with hBBEq; subst hBBEq
        let ⟨_, hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBsRel hBBSrc
        rw [hBBTgt] at hBBTgt'; injection hBBTgt' with hBBTEq; subst hBBTEq
        let ⟨h12BB, hTermRel⟩ := bool_and_true hBBRel
        let ⟨hCleanEq, hStmtsRel⟩ := bool_and_true h12BB
        have hStLenEq := listRel_length hStmtsRel
        cases hDropS : bbSrc.statements.drop frame.stmtIdx with
        | cons sSrc restS =>
          rw [hDropS] at hRemPair
          cases hDropT : bbTgt.statements.drop frame.stmtIdx with
          | nil => rw [hDropT] at hRemPair; cases hRemPair
          | cons sTgt restT =>
            rw [hDropT] at hRemPair
            dsimp [stepAbsorbStmtsPair] at hRemPair
            cases hOne : stepAbsorbStmtPair bSrc.locals curEnv sSrc sTgt with
            | none => rw [hOne] at hRemPair; cases hRemPair
            | some nextEnv =>
              rw [hOne] at hRemPair
              let ⟨hGetS, hDropNextS⟩ := getElem?_of_drop_eq_cons hDropS
              let ⟨hGetT, hDropNextT⟩ := getElem?_of_drop_eq_cons hDropT
              let ⟨hStmtEq, hStmtNext⟩ := stepAbsorbStmtPair_sound (cm := cm) hLocEq hCurSound hOne
              have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                  evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                unfold evalStep; dsimp
                rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
                rw [hGetS, hGetT]; dsimp
                exact hStmtEq
              refine ⟨hEvEq, ?_⟩
              intro s' hStepS
              unfold evalStep at hStepS; dsimp at hStepS
              rw [hBSrc] at hStepS; dsimp at hStepS
              rw [hBBSrc] at hStepS; dsimp at hStepS
              rw [hGetS] at hStepS; dsimp at hStepS
              let ⟨locs', hEqS', hNextSound⟩ := hStmtNext s' hStepS
              subst hEqS'
              refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                      hBRel, hBodyCertOk, hNextSound.1, ?_⟩
              intro _
              refine ⟨bbSrc, bbTgt, entryEnv, nextEnv, exitEnv,
                      hBBSrc, hBBTgt, hCertEntry, hNextSound, hFullPair, ?_, hChkBlk⟩
              dsimp; rw [hDropNextS, hDropNextT]; exact hRemPair
        | nil =>
          rw [hDropS] at hRemPair
          cases hDropT : bbTgt.statements.drop frame.stmtIdx with
          | cons _ _ => rw [hDropT] at hRemPair; cases hRemPair
          | nil =>
            rw [hDropT] at hRemPair
            injection hRemPair with hCurExit; subst hCurExit
            have hNoneS := getElem?_none_of_ge (le_of_drop_eq_nil hDropS)
            have hNoneT := getElem?_none_of_ge (le_of_drop_eq_nil hDropT)
            have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
              unfold evalStep; dsimp
              rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
              rw [hNoneS, hNoneT]; dsimp; rw [hStLenEq]
              cases Nat.beq frame.stmtIdx bbTgt.statements.length with
              | false => rfl
              | true =>
                rw [if_bool_true rfl, if_bool_true rfl]
                exact evalTerminator_eq_of_eq hLocEq (bool_beq_eq hCleanEq)
                  (terminatorEq_eq hTermRel)
            refine ⟨hEvEq, ?_⟩
            intro s' hStepS
            unfold evalStep at hStepS; dsimp at hStepS
            rw [hBSrc] at hStepS; dsimp at hStepS
            rw [hBBSrc] at hStepS; dsimp at hStepS
            rw [hNoneS] at hStepS; dsimp at hStepS
            cases hEnd : Nat.beq frame.stmtIdx bbSrc.statements.length with
            | false => rw [hEnd] at hStepS; cases hStepS
            | true =>
              rw [hEnd] at hStepS; dsimp at hStepS
              have hChkBlkCopy := hChkBlk
              unfold checkAbsorbingBlock at hChkBlkCopy
              rw [hCertEntry, hBBTgt] at hChkBlkCopy; dsimp at hChkBlkCopy
              let ⟨_, hTermChk⟩ := bool_and_true hChkBlkCopy
              rw [hFullPair] at hTermChk; dsimp at hTermChk
              unfold evalTerminator at hStepS
              cases hTm : bbSrc.terminator with
              | return_ =>
                rw [hTm] at hStepS; dsimp at hStepS
                cases hCl : bbSrc.cleanup with
                | true => rw [hCl] at hStepS; cases hStepS
                | false =>
                  rw [hCl] at hStepS; dsimp at hStepS
                  cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
                  | none => rw [h0] at hStepS; cases hStepS
                  | some sl0 =>
                    rw [h0] at hStepS
                    cases sl0 with
                    | dead => cases hStepS
                    | live o => cases o <;> cases hStepS
              | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
                rw [hTm] at hStepS; cases hStepS
              | goto tgt =>
                rw [hTm] at hStepS; rw [hTm] at hTermChk; dsimp at hTermChk
                injection hStepS with hSEq; subst hSEq
                refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                        hBRel, hBodyCertOk, hWt, ?_⟩
                intro hLtTgt
                let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                  checkAbsEdge_sound hBBLen hLoops hTermChk hCurSound hLtTgt
                exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
              | switchInt discr targets =>
                rw [hTm] at hStepS; rw [hTm] at hTermChk; dsimp at hStepS; dsimp at hTermChk
                let ⟨hOtherEdge, hBranchEdges⟩ := bool_and_true hTermChk
                cases hEvD : evalPrimitiveOperand bSrc.locals frame.locals discr with
                | error _ => rw [hEvD] at hStepS; cases hStepS
                | ok resD =>
                  let ⟨dv, locsAfter⟩ := resD
                  rw [hEvD] at hStepS; dsimp at hStepS
                  have hAfterSound := deinitMovePrimAbs_sound hCurSound hEvD
                  cases dv with
                  | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hStepS
                  | bool bv =>
                    dsimp at hStepS
                    cases hSwB : evalBoolSwitchBranches bv targets.otherwise targets.branches with
                    | error _ => rw [hSwB] at hStepS; cases hStepS
                    | ok tgt =>
                      rw [hSwB] at hStepS
                      injection hStepS with hSEq; subst hSEq
                      refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                              hBRel, hBodyCertOk, hAfterSound.1, ?_⟩
                      intro hLtTgt
                      cases evalBoolSwitchBranches_cases hSwB with
                      | inl hIn =>
                        let ⟨cb, hMem⟩ := hIn
                        have hBrEdge := list_all_mem_true hBranchEdges hMem
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkAbsEdge_sound hBBLen hLoops hBrEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                      | inr hTgtEq =>
                        subst hTgtEq
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkAbsEdge_sound hBBLen hLoops hOtherEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                  | scalar sv =>
                    dsimp at hStepS
                    cases hSwS : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                    | error _ => rw [hSwS] at hStepS; cases hStepS
                    | ok tgt =>
                      rw [hSwS] at hStepS
                      injection hStepS with hSEq; subst hSEq
                      refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                              hBRel, hBodyCertOk, hAfterSound.1, ?_⟩
                      intro hLtTgt
                      cases evalSwitchBranches_cases hSwS with
                      | inl hIn =>
                        let ⟨cb, hMem⟩ := hIn
                        have hBrEdge := list_all_mem_true hBranchEdges hMem
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkAbsEdge_sound hBBLen hLoops hBrEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                      | inr hFall =>
                        let ⟨hTgtEq, _⟩ := hFall
                        subst hTgtEq
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkAbsEdge_sound hBBLen hLoops hOtherEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩

private theorem vc_transport_absorbingAndSelfCancel_certified_iff_priv
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isAbsorbingOrSelfCancelProgram pSrc pTgt = true)
    (hCert : checkAbsorbingOrSelfCancelProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  have hGen := isAbsorbingOrSelfCancelProgram_to_generic hRel
  let ⟨hHdr, hBodies⟩ := bool_and_true hGen
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hBHdr, _, hBBEmpty, _, hBounds, _⟩ :=
      genericBodyRel_storage_eq isAbsorbingOrSelfCancelStmt_assignOnly hBRel
    exact ⟨hBHdr, hBBEmpty, hBounds⟩
  · intro q
    exact absorbingAndSelfCancel_certified_query_lockstep hRel hCert q
  · intro defId args
    have hRelE : isAbsorbingOrSelfCancelProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true := by
      let ⟨hPH, hPB⟩ := bool_and_true hRel
      exact bool_and_intro (programHeaderEq_entryProg defId hPH) hPB
    exact (absorbingAndSelfCancel_certified_query_lockstep hRelE hCert { args := args }).1

/-! ### Stage 4 Private Helpers — Layer F: Pass 6 (Constant & Enum
Discriminant Folding) & Pipeline Theorem 7 -/

/-! #### Constant Re-Encoding & Enum Discriminant Constant Helpers -/

private theorem evalConstLit_of_valToConstOperand? {res : Val} {cand : ConstOperand}
    (h : valToConstOperand? res = some cand) :
    evalConstLit cand.ty cand.lit = .ok res := by
  cases res with
  | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases h
  | bool b =>
    cases b with
    | false =>
      dsimp [valToConstOperand?] at h
      injection h with hcEq; subst hcEq
      rfl
    | true =>
      dsimp [valToConstOperand?] at h
      injection h with hcEq; subst hcEq
      rfl
  | scalar sv =>
    dsimp [valToConstOperand?] at h
    cases hWfB : sv.wf with
    | false => rw [hWfB] at h; cases h
    | true =>
      rw [hWfB] at h; dsimp at h
      injection h with hcEq; subst hcEq
      unfold ScalarVal.wf at hWfB
      have hWf : truncateBits sv.width sv.bits = sv.bits := bitvec_eq_of_beq hWfB
      dsimp [evalConstLit]
      have hBneFalse : (truncateBits sv.width sv.bits != sv.bits) = false := by
        rw [hWf]
        change (!(sv.bits == sv.bits)) = false
        rw [bitvec_beq_refl]; rfl
      rw [hBneFalse]; dsimp; rw [hWf]

private theorem evalConstUnaryToOperand?_elim {op : UnOp} {c cand : ConstOperand}
    (h : evalConstUnaryToOperand? op c = some cand) :
    ∃ v res,
      isPrimitiveReadableTy c.ty = true ∧
      evalConstLit c.ty c.lit = .ok v ∧
      evalUnOp op v = .ok res ∧
      evalConstLit cand.ty cand.lit = .ok res := by
  unfold evalConstUnaryToOperand? at h
  cases hPrim : isPrimitiveReadableTy c.ty with
  | false => rw [hPrim] at h; cases h
  | true =>
    rw [hPrim] at h; dsimp at h
    cases hLit : evalConstLit c.ty c.lit with
    | error _ => rw [hLit] at h; cases h
    | ok v =>
      rw [hLit] at h; dsimp at h
      cases hUn : evalUnOp op v with
      | error _ => rw [hUn] at h; cases h
      | ok res =>
        rw [hUn] at h; dsimp at h
        exact ⟨v, res, rfl, rfl, hUn, evalConstLit_of_valToConstOperand? h⟩

private theorem evalConstBinaryToOperand?_elim {op : BinOp} {cL cR cand : ConstOperand}
    (h : evalConstBinaryToOperand? op cL cR = some cand) :
    ∃ vL vR res,
      isPrimitiveReadableTy cL.ty = true ∧
      isPrimitiveReadableTy cR.ty = true ∧
      evalConstLit cL.ty cL.lit = .ok vL ∧
      evalConstLit cR.ty cR.lit = .ok vR ∧
      evalBinOp op vL vR = .ok res ∧
      evalConstLit cand.ty cand.lit = .ok res := by
  unfold evalConstBinaryToOperand? at h
  cases hPL : isPrimitiveReadableTy cL.ty with
  | false => rw [hPL] at h; cases h
  | true =>
    rw [hPL] at h
    cases hPR : isPrimitiveReadableTy cR.ty with
    | false => rw [hPR] at h; cases h
    | true =>
      rw [hPR] at h; dsimp at h
      cases hLL : evalConstLit cL.ty cL.lit with
      | error _ => rw [hLL] at h; cases h
      | ok vL =>
        rw [hLL] at h
        cases hLR : evalConstLit cR.ty cR.lit with
        | error _ => rw [hLR] at h; cases h
        | ok vR =>
          rw [hLR] at h; dsimp at h
          cases hBin : evalBinOp op vL vR with
          | error _ => rw [hBin] at h; cases h
          | ok res =>
            rw [hBin] at h; dsimp at h
            exact ⟨vL, vR, res, rfl, rfl, rfl, rfl, hBin,
                   evalConstLit_of_valToConstOperand? h⟩

private theorem isConstOpFoldRewrite_elim {bodyLocals : List MirTy}
    {sSrc sTgt : StatementKind}
    (hRw : isConstOpFoldRewrite bodyLocals sSrc sTgt = true) :
    ∃ dst rvSrc cOut dstTy res,
      sSrc = .assign dst rvSrc ∧
      sTgt = .assign dst (.use (.constant cOut)) ∧
      dst.projection.isEmpty = true ∧
      Trusted.MirSemantics.getElem? bodyLocals dst.localId = some dstTy ∧
      cOut.ty = dstTy ∧
      evalConstLit cOut.ty cOut.lit = .ok res ∧
      (∀ locs, evalRvalue bodyLocals locs dstTy rvSrc = .ok (res, locs)) ∧
      (∀ locs2 locsTgt,
        evalRvalue locs2 locsTgt dstTy (.use (.constant cOut)) = .ok (res, locsTgt)) := by
  cases sSrc with
  | nop | storageLive _ | storageDead _ | unsupported => cases hRw
  | assign dst rvSrc =>
    cases rvSrc with
    | use _ | discriminant _ | ref _ _ | addressOf _ _
    | aggregateTuple _ | unsupported => cases hRw
    | unaryOp op opnd =>
      cases opnd with
      | copy _ | move _ => cases hRw
      | constant c =>
        cases sTgt with
        | nop | storageLive _ | storageDead _ | unsupported => cases hRw
        | assign dst' rvTgt =>
          cases rvTgt with
          | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
          | addressOf _ _ | aggregateTuple _ | unsupported => cases hRw
          | use opndOut =>
            cases opndOut with
            | copy _ | move _ => cases hRw
            | constant cOut =>
              dsimp [isConstOpFoldRewrite] at hRw
              let ⟨h12, hRest⟩ := bool_and_true hRw
              let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12
              have hDEq := placeEq_eq hDstEq; subst hDEq
              cases hDstTy : Trusted.MirSemantics.getElem? bodyLocals dst.localId with
              | none => rw [hDstTy] at hRest; cases hRest
              | some dstTy =>
                rw [hDstTy] at hRest
                cases hCU : evalConstUnaryToOperand? op c with
                | none => rw [hCU] at hRest; cases hRest
                | some cand =>
                  rw [hCU] at hRest
                  let ⟨hCEq, hTyEq⟩ := bool_and_true hRest
                  have hCandEq := constOpEq_eq hCEq; subst hCandEq
                  have hCOTy := mirTy_beq_eq hTyEq
                  let ⟨v, res, hPrimC, hEvC, hEvUn, hEvOut⟩ :=
                    evalConstUnaryToOperand?_elim hCU
                  refine ⟨dst, .unaryOp op (.constant c), cand, dstTy, res,
                          rfl, rfl, hDstEmp, hDstTy, hCOTy, hEvOut, ?_, ?_⟩
                  · intro locs
                    dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
                    rw [hEvC]; dsimp; rw [hPrimC]; dsimp; rw [hEvUn]
                  · intro locs2 locsTgt
                    dsimp [evalRvalue, evalOperandToSlot]
                    rw [hEvOut]; dsimp; rw [hCOTy, mirTy_beq_refl dstTy]; dsimp
    | binaryOp op lhs rhs =>
      cases lhs with
      | copy _ | move _ => cases hRw
      | constant cL =>
        cases rhs with
        | copy _ | move _ => cases hRw
        | constant cR =>
          cases sTgt with
          | nop | storageLive _ | storageDead _ | unsupported => cases hRw
          | assign dst' rvTgt =>
            cases rvTgt with
            | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
            | addressOf _ _ | aggregateTuple _ | unsupported => cases hRw
            | use opndOut =>
              cases opndOut with
              | copy _ | move _ => cases hRw
              | constant cOut =>
                dsimp [isConstOpFoldRewrite] at hRw
                let ⟨h12, hRest⟩ := bool_and_true hRw
                let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12
                have hDEq := placeEq_eq hDstEq; subst hDEq
                cases hDstTy : Trusted.MirSemantics.getElem? bodyLocals dst.localId with
                | none => rw [hDstTy] at hRest; cases hRest
                | some dstTy =>
                  rw [hDstTy] at hRest
                  cases hCB : evalConstBinaryToOperand? op cL cR with
                  | none => rw [hCB] at hRest; cases hRest
                  | some cand =>
                    rw [hCB] at hRest
                    let ⟨hCEq, hTyEq⟩ := bool_and_true hRest
                    have hCandEq := constOpEq_eq hCEq; subst hCandEq
                    have hCOTy := mirTy_beq_eq hTyEq
                    let ⟨vL, vR, res, hPL, hPR, hLL, hLR, hBin, hEvOut⟩ :=
                      evalConstBinaryToOperand?_elim hCB
                    refine ⟨dst, .binaryOp op (.constant cL) (.constant cR), cand, dstTy, res,
                            rfl, rfl, hDstEmp, hDstTy, hCOTy, hEvOut, ?_, ?_⟩
                    · intro locs
                      dsimp [evalRvalue, evalPrimitiveOperand, evalOperandToSlot]
                      rw [hLL]; dsimp; rw [hPL]; dsimp
                      rw [hLR]; dsimp; rw [hPR]; dsimp; rw [hBin]
                    · intro locs2 locsTgt
                      dsimp [evalRvalue, evalOperandToSlot]
                      rw [hEvOut]; dsimp; rw [hCOTy, mirTy_beq_refl dstTy]; dsimp

private theorem enumVariantDiscrConst?_elim {ety : EnumTy} {vIdx : Nat} {cand : ConstOperand}
    (h : enumVariantDiscrConst? ety vIdx = some cand) :
    ∃ disc : Nat,
      enumAdmitted ety = true ∧
      vIdx < ety.discriminants.length ∧
      Trusted.MirSemantics.getElem? ety.discriminants vIdx = some disc ∧
      cand.ty = .int ety.discrWidth ety.discrSigned ∧
      evalConstLit cand.ty cand.lit =
        .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
          truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩) := by
  unfold enumVariantDiscrConst? at h
  cases hAdm : enumAdmitted ety with
  | false => rw [hAdm] at h; cases h
  | true =>
    rw [hAdm] at h
    cases hBlt : Nat.blt vIdx ety.discriminants.length with
    | false => rw [hBlt] at h; cases h
    | true =>
      rw [hBlt] at h; dsimp at h
      cases hD : Trusted.MirSemantics.getElem? ety.discriminants vIdx with
      | none => rw [hD] at h; cases h
      | some disc =>
        rw [hD] at h
        injection h with hcEq; subst hcEq
        refine ⟨disc, rfl, nat_blt_lt hBlt, rfl, rfl, ?_⟩
        dsimp [evalConstLit]
        let b := truncateBits ety.discrWidth (BitVec.ofNat 128 disc)
        have hIdem : truncateBits ety.discrWidth b = b :=
          truncateBits_idem ety.discrWidth (BitVec.ofNat 128 disc)
        have hBneFalse : (truncateBits ety.discrWidth b != b) = false := by
          change (!(truncateBits ety.discrWidth b == b)) = false
          rw [hIdem, bitvec_beq_refl]; rfl
        change (if (truncateBits ety.discrWidth b != b) = true then
                  Except.error FaultKind.unsupported
                else
                  Except.ok (Val.scalar ⟨ety.discrWidth, ety.discrSigned,
                    truncateBits ety.discrWidth b⟩)) =
               Except.ok (Val.scalar ⟨ety.discrWidth, ety.discrSigned, b⟩)
        rw [hBneFalse]; dsimp; rw [hIdem]

/-! #### Theorem 6a: Unconditional Forward Codegen Refinement for
`UncondConstAndSingleDiscrFold` -/

private theorem isUncondConstAndSingleDiscrFoldStmt_assignOnly (locs : List MirTy)
    (s₁ s₂ : StatementKind) (h : isUncondConstAndSingleDiscrFoldStmt locs s₁ s₂ = true) :
    s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂) := by
  unfold isUncondConstAndSingleDiscrFoldStmt at h
  cases bool_or_true h with
  | inr hEq => exact Or.inl (stmtEq_eq hEq)
  | inl h12 =>
    cases bool_or_true h12 with
    | inl hConst =>
      let ⟨dst, rvSrc, cOut, _, _, hs1, hs2, _⟩ := isConstOpFoldRewrite_elim hConst
      exact Or.inr ⟨dst, rvSrc, dst, .use (.constant cOut), hs1, hs2⟩
    | inr hDiscr =>
      cases s₁ with
      | nop | storageLive _ | storageDead _ | unsupported => cases hDiscr
      | assign d₁ rv₁ =>
        cases rv₁ with
        | use _ | binaryOp _ _ _ | unaryOp _ _ | ref _ _
        | addressOf _ _ | aggregateTuple _ | unsupported => cases hDiscr
        | discriminant p =>
          cases s₂ with
          | nop | storageLive _ | storageDead _ | unsupported => cases hDiscr
          | assign d₂ rv₂ =>
            exact Or.inr ⟨d₁, .discriminant p, d₂, rv₂, rfl, rfl⟩

private theorem isUncondConstAndSingleDiscrFoldProgram_to_generic {pSrc pTgt : Program}
    (h : isUncondConstAndSingleDiscrFoldProgram pSrc pTgt = true) :
    genericProgRel isUncondConstAndSingleDiscrFoldStmt pSrc pTgt = true := by
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  refine bool_and_intro hHdr ?_
  refine listRel_mono (fun b₁ b₂ hb => ?_) hBodies
  let ⟨hBHdr, hBBs⟩ := bool_and_true hb
  exact bool_and_intro hBHdr (listRel_mono (fun _ _ hbb => hbb) hBBs)

private theorem evalRvalue_singleVariant_discriminant_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dstTy : MirTy} {p : Place}
    {ety : EnumTy} {disc : Nat} {val : Val}
    (hPEmp : p.projection.isEmpty = true)
    (hPTy : Trusted.MirSemantics.getElem? bodyLocals p.localId = some (.enum ety))
    (hLen1 : ety.discriminants.length = 1)
    (hD0 : Trusted.MirSemantics.getElem? ety.discriminants 0 = some disc)
    (hEv : evalRvalue bodyLocals locals dstTy (.discriminant p) = .ok (val, locals')) :
    val = .scalar ⟨ety.discrWidth, ety.discrSigned,
            truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩ ∧
    locals' = locals := by
  dsimp [evalRvalue] at hEv
  rw [hPEmp] at hEv; dsimp at hEv
  rw [hPTy] at hEv
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
            dsimp at hEv; rw [hD0] at hEv
            injection hEv with h1; injection h1 with hV hL
            exact ⟨hV.symm, hL.symm⟩
          | some v =>
            cases v with
            | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
            | enumVal ety' k =>
              dsimp at hEv
              cases hC : (EnumTy.beq ety ety' && Nat.beq k 0) with
              | false => rw [hC] at hEv; cases hEv
              | true =>
                rw [hC] at hEv; dsimp at hEv; rw [hD0] at hEv
                injection hEv with h1; injection h1 with hV hL
                exact ⟨hV.symm, hL.symm⟩
      | scalar tw ts =>
        rw [hTr] at hEv
        cases slot with
        | dead => cases hEv
        | live opt =>
          cases opt with
          | none => cases hEv
          | some v =>
            cases v with
            | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ => cases hEv
            | enumVal ety' k =>
              dsimp at hEv
              cases hC : (EnumTy.beq ety ety' && Nat.blt k ety.discriminants.length) with
              | false => rw [hC] at hEv; cases hEv
              | true =>
                rw [hC] at hEv; dsimp at hEv
                let ⟨_, hKBlt⟩ := bool_and_true hC
                have hKLt1 : k < 1 := by rw [← hLen1]; exact nat_blt_lt hKBlt
                have hk0 : k = 0 := by
                  cases k with
                  | zero => rfl
                  | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hKLt1))
                rw [hk0, hD0] at hEv
                injection hEv with h1; injection h1 with hV hL
                exact ⟨hV.symm, hL.symm⟩

private theorem evalStatement_uncondConstAndSingleDiscr_fwd (b₁ b₂ : Body)
    (f₁ f₂ : FrameState) (cm : CallerMemory) (s₁ s₂ : StatementKind) (s' : State)
    (hLocEq : b₁.locals = b₂.locals)
    (hInv : LocalsFwdRefines b₁.locals f₁.locals f₂.locals)
    (hRel : isUncondConstAndSingleDiscrFoldStmt b₁.locals s₁ s₂ = true)
    (hEv : evalStatement b₁ f₁ cm s₁ = .step s') :
    ∃ locs1' locs2',
      s' = { frames := [{ f₁ with stmtIdx := f₁.stmtIdx + 1, locals := locs1' }],
             callerMem := cm } ∧
      evalStatement b₂ f₂ cm s₂ =
        .step { frames := [{ f₂ with stmtIdx := f₂.stmtIdx + 1, locals := locs2' }],
                callerMem := cm } ∧
      LocalsFwdRefines b₁.locals locs1' locs2' := by
  unfold isUncondConstAndSingleDiscrFoldStmt at hRel
  cases bool_or_true hRel with
  | inr hEq =>
    rw [stmtEq_eq hEq] at hEv
    exact evalStatement_fwd_eq hLocEq hInv hEv
  | inl h12 =>
    cases bool_or_true h12 with
    | inl hConst =>
      let ⟨dst, rvSrc, cOut, dstTy, res, hs1, hs2, hDstEmp, hDstTy, _, _, hRvSrc, hRvTgt⟩ :=
        isConstOpFoldRewrite_elim hConst
      subst hs1; subst hs2
      dsimp [evalStatement] at hEv
      rw [hDstEmp] at hEv; dsimp at hEv
      rw [hDstTy] at hEv; dsimp at hEv
      rw [hRvSrc f₁.locals] at hEv; dsimp at hEv
      cases hW1 : writePlace f₁.locals dst.localId dstTy res with
      | error _ => rw [hW1] at hEv; cases hEv
      | ok locs1' =>
        rw [hW1] at hEv; injection hEv with hSEq
        let ⟨locs2', hW2, hInv2⟩ := writePlace_fwd hInv hDstTy hW1
        refine ⟨locs1', locs2', hSEq.symm, ?_, hInv2⟩
        dsimp [evalStatement]
        rw [hDstEmp]; dsimp
        rw [← hLocEq, hDstTy]; dsimp
        rw [hRvTgt b₁.locals f₂.locals]; dsimp; rw [hW2]
    | inr hDiscr =>
      cases s₁ with
      | nop | storageLive _ | storageDead _ | unsupported => cases hDiscr
      | assign dst rv₁ =>
        cases rv₁ with
        | use _ | binaryOp _ _ _ | unaryOp _ _ | ref _ _
        | addressOf _ _ | aggregateTuple _ | unsupported => cases hDiscr
        | discriminant p =>
          cases s₂ with
          | nop | storageLive _ | storageDead _ | unsupported => cases hDiscr
          | assign dst' rv₂ =>
            cases rv₂ with
            | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
            | addressOf _ _ | aggregateTuple _ | unsupported => cases hDiscr
            | use opnd₂ =>
              cases opnd₂ with
              | copy _ | move _ => cases hDiscr
              | constant cOut =>
                dsimp [isEnumDiscrFoldRewrite] at hDiscr
                let ⟨hPre, hTypes⟩ := bool_and_true hDiscr
                let ⟨h12P, hPEmp⟩ := bool_and_true hPre
                let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12P
                have hDEq := placeEq_eq hDstEq; subst hDEq
                cases hDstTy : Trusted.MirSemantics.getElem? b₁.locals dst.localId with
                | none => rw [hDstTy] at hTypes; cases hTypes
                | some dstTy =>
                  rw [hDstTy] at hTypes
                  cases hPTy : Trusted.MirSemantics.getElem? b₁.locals p.localId with
                  | none => rw [hPTy] at hTypes; cases hTypes
                  | some pTy =>
                    rw [hPTy] at hTypes
                    cases pTy with
                    | bool | int _ _ | unit | never | tuple _
                    | ref _ _ | rawPtr _ _ | unsupported => cases hTypes
                    | enum ety =>
                      dsimp at hTypes
                      let ⟨h12E, hSingle⟩ := bool_and_true hTypes
                      let ⟨_, hDTyEq⟩ := bool_and_true h12E
                      have hDstTyEq := mirTy_beq_eq hDTyEq; subst hDstTyEq
                      let ⟨hLen1B, hCandMatch⟩ := bool_and_true hSingle
                      have hLen1 := nat_beq_eq hLen1B
                      cases hCand : enumVariantDiscrConst? ety 0 with
                      | none => rw [hCand] at hCandMatch; cases hCandMatch
                      | some cand =>
                        rw [hCand] at hCandMatch
                        have hCEq := constOpEq_eq hCandMatch; subst hCEq
                        let ⟨disc, _, _, hD0, hCTy, hEvC⟩ := enumVariantDiscrConst?_elim hCand
                        dsimp [evalStatement] at hEv
                        rw [hDstEmp] at hEv; dsimp at hEv
                        rw [hDstTy] at hEv; dsimp at hEv
                        cases hRv : evalRvalue b₁.locals f₁.locals
                            (.int ety.discrWidth ety.discrSigned) (.discriminant p) with
                        | error _ => rw [hRv] at hEv; cases hEv
                        | ok resR =>
                          let ⟨val, locsAfter⟩ := resR
                          rw [hRv] at hEv; dsimp at hEv
                          let ⟨hValEq, hLocsAfterEq⟩ :=
                            evalRvalue_singleVariant_discriminant_ok hPEmp hPTy hLen1 hD0 hRv
                          subst hValEq; subst hLocsAfterEq
                          cases hW1 : writePlace f₁.locals dst.localId
                              (.int ety.discrWidth ety.discrSigned)
                              (.scalar ⟨ety.discrWidth, ety.discrSigned,
                                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩) with
                          | error _ => rw [hW1] at hEv; cases hEv
                          | ok locs1' =>
                            rw [hW1] at hEv; injection hEv with hSEq
                            let ⟨locs2', hW2, hInv2⟩ := writePlace_fwd hInv hDstTy hW1
                            refine ⟨locs1', locs2', hSEq.symm, ?_, hInv2⟩
                            dsimp [evalStatement]
                            rw [hDstEmp]; dsimp
                            rw [← hLocEq, hDstTy]; dsimp
                            dsimp [evalRvalue, evalOperandToSlot]
                            rw [hEvC]; dsimp
                            rw [hCTy, mirTy_beq_refl (.int ety.discrWidth ety.discrSigned)]; dsimp
                            rw [hW2]

private theorem codegen_constAndEnumDiscrFold_refines_unconditional_priv
    (pSrc pTgt : Program)
    (hRel : isUncondConstAndSingleDiscrFoldProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt :=
  forwardCodegenRefines_of_stmtRel_fwd
    isUncondConstAndSingleDiscrFoldStmt_assignOnly
    evalStatement_uncondConstAndSingleDiscr_fwd
    (isUncondConstAndSingleDiscrFoldProgram_to_generic hRel)

/-! #### Theorem 6b: Certified Bidirectional VC Transport for
`ConstAndEnumDiscrFold` -/

private theorem isConstAndEnumDiscrFoldStmt_assignOnly (locs : List MirTy)
    (s₁ s₂ : StatementKind) (h : isConstAndEnumDiscrFoldStmt locs s₁ s₂ = true) :
    s₁ = s₂ ∨ (∃ d₁ rv₁ d₂ rv₂, s₁ = .assign d₁ rv₁ ∧ s₂ = .assign d₂ rv₂) := by
  unfold isConstAndEnumDiscrFoldStmt at h
  cases bool_or_true h with
  | inr hEq => exact Or.inl (stmtEq_eq hEq)
  | inl h12 =>
    cases bool_or_true h12 with
    | inl hConst =>
      let ⟨dst, rvSrc, cOut, _, _, hs1, hs2, _⟩ := isConstOpFoldRewrite_elim hConst
      exact Or.inr ⟨dst, rvSrc, dst, .use (.constant cOut), hs1, hs2⟩
    | inr hDiscr =>
      cases s₁ with
      | nop | storageLive _ | storageDead _ | unsupported => cases hDiscr
      | assign d₁ rv₁ =>
        cases rv₁ with
        | use _ | binaryOp _ _ _ | unaryOp _ _ | ref _ _
        | addressOf _ _ | aggregateTuple _ | unsupported => cases hDiscr
        | discriminant p =>
          cases s₂ with
          | nop | storageLive _ | storageDead _ | unsupported => cases hDiscr
          | assign d₂ rv₂ =>
            exact Or.inr ⟨d₁, .discriminant p, d₂, rv₂, rfl, rfl⟩

private theorem isConstAndEnumDiscrFoldProgram_to_generic {pSrc pTgt : Program}
    (h : isConstAndEnumDiscrFoldProgram pSrc pTgt = true) :
    genericProgRel isConstAndEnumDiscrFoldStmt pSrc pTgt = true := by
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  refine bool_and_intro hHdr ?_
  refine listRel_mono (fun b₁ b₂ hb => ?_) hBodies
  let ⟨hBHdr, hBBs⟩ := bool_and_true hb
  exact bool_and_intro hBHdr (listRel_mono (fun _ _ hbb => hbb) hBBs)

private noncomputable def DiscrSlotSound (ty : MirTy) (abs : DiscrAbsSlot)
    (sl : LocalSlot) : Prop :=
  SlotWellTyped ty sl ∧
  match abs with
  | .dead => True
  | .liveSlot => ∃ o, sl = .live o
  | .knownEnum ety vIdx =>
    ty = .enum ety ∧
    enumAdmitted ety = true ∧
    vIdx < ety.discriminants.length ∧
    sl = .live (some (.enumVal ety vIdx))

private noncomputable def DiscrEnvSound (bodyLocals : List MirTy)
    (env : List DiscrAbsSlot) (locals : List LocalSlot) : Prop :=
  LocalsWellTyped bodyLocals locals ∧
  env.length = bodyLocals.length ∧
  ∀ i ty abs sl,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? env i = some abs →
    Trusted.MirSemantics.getElem? locals i = some sl →
    DiscrSlotSound ty abs sl

private theorem discrSlotImplies_sound {ty : MirTy} {a₁ a₂ : DiscrAbsSlot} {sl : LocalSlot}
    (hImp : discrSlotImplies a₁ a₂ = true)
    (hSound : DiscrSlotSound ty a₁ sl) :
    DiscrSlotSound ty a₂ sl := by
  let ⟨hWt, hS⟩ := hSound
  cases a₂ with
  | dead => exact ⟨hWt, True.intro⟩
  | liveSlot =>
    cases a₁ with
    | dead => cases hImp
    | liveSlot => exact ⟨hWt, hS⟩
    | knownEnum ety vIdx =>
      let ⟨_, _, _, hsl⟩ := hS
      exact ⟨hWt, ⟨some (.enumVal ety vIdx), hsl⟩⟩
  | knownEnum e₂ v₂ =>
    cases a₁ with
    | dead | liveSlot => cases hImp
    | knownEnum e₁ v₁ =>
      let ⟨hEB, hVB⟩ := bool_and_true hImp
      have hEEq := enumTy_beq_eq hEB
      have hVEq := nat_beq_eq hVB
      subst hEEq; subst hVEq
      exact ⟨hWt, hS⟩

private theorem discrEnvImplies_sound {bodyLocals : List MirTy}
    {env₁ env₂ : List DiscrAbsSlot} {locals : List LocalSlot}
    (hImp : discrEnvImplies env₁ env₂ = true)
    (hSound : DiscrEnvSound bodyLocals env₁ locals) :
    DiscrEnvSound bodyLocals env₂ locals := by
  let ⟨hWt, hLen1, hAll⟩ := hSound
  have hLen12 : env₁.length = env₂.length := listRel_length hImp
  refine ⟨hWt, hLen12.symm.trans hLen1, ?_⟩
  intro i ty a₂ sl hTy hA2 hSl
  let ⟨a₁, hA1, hImpSlot⟩ := listRel_getElem?_right hImp hA2
  exact discrSlotImplies_sound hImpSlot (hAll i ty a₁ sl hTy hA1 hSl)

private theorem discrSlotSound_liveSlot_liveUninit (ty : MirTy) :
    DiscrSlotSound ty .liveSlot (liveUninitSlot ty) := by
  let ⟨opt, hOpt⟩ := liveUninitSlot_isLive ty
  exact ⟨liveUninitSlot_wellTyped ty, ⟨opt, hOpt⟩⟩

private theorem discrSlotSound_enum_liveUninit (ety : EnumTy) :
    DiscrSlotSound (.enum ety)
      (if isZstEnumTy ety then .knownEnum ety 0 else .liveSlot)
      (liveUninitSlot (.enum ety)) := by
  cases hZ : isZstEnumTy ety with
  | true =>
    let ⟨_, hAdm, hLen1⟩ := isZstEnumTy_elim hZ
    have hSl : liveUninitSlot (.enum ety) = .live (some (.enumVal ety 0)) := by
      dsimp [liveUninitSlot]; rw [hZ]; rfl
    rw [hSl]; dsimp
    exact ⟨by rw [← hSl]; exact liveUninitSlot_wellTyped (.enum ety),
           ⟨rfl, hAdm, by rw [hLen1]; exact Nat.zero_lt_one, rfl⟩⟩
  | false =>
    have hSl : liveUninitSlot (.enum ety) = .live none := by
      dsimp [liveUninitSlot]; rw [hZ]; rfl
    rw [hSl]; dsimp
    exact ⟨by rw [← hSl]; exact liveUninitSlot_wellTyped (.enum ety), ⟨none, rfl⟩⟩

private theorem initDiscrEnvLoop_length (body : Body) :
    ∀ idx tys, (initDiscrEnvLoop body idx tys).length = tys.length := by
  intro idx tys
  induction tys generalizing idx with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [initDiscrEnvLoop, List.length]
    rw [ih (idx + 1)]

private theorem initDiscrEnvLoop_getElem? (body : Body) :
    ∀ base tys k ty,
      Trusted.MirSemantics.getElem? tys k = some ty →
      Trusted.MirSemantics.getElem? (initDiscrEnvLoop body base tys) k =
        some (initDiscrSlot body (base + k)) := by
  intro base tys
  induction tys generalizing base with
  | nil => intro _ _ h; cases h
  | cons _ rest ih =>
    intro k ty h
    cases k with
    | zero =>
      dsimp [initDiscrEnvLoop, Trusted.MirSemantics.getElem?]
    | succ m =>
      dsimp [Trusted.MirSemantics.getElem?] at h
      dsimp [initDiscrEnvLoop, Trusted.MirSemantics.getElem?]
      rw [ih (base + 1) m ty h]
      rw [Nat.add_assoc, Nat.add_comm 1 m]

private theorem initDiscrEnvLoop_sound {body : Body} {args : List Val}
    (hArgs : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true) :
    DiscrEnvSound body.locals
      (initDiscrEnvLoop body 0 body.locals)
      (initLocalsLoop body args 0 body.locals) := by
  have hWt := initLocalsLoop_wellTyped hArgs
  refine ⟨hWt, initDiscrEnvLoop_length body 0 body.locals, ?_⟩
  intro i ty abs sl hTy hAbs hSl
  have hGetAbs := initDiscrEnvLoop_getElem? body 0 body.locals i ty hTy
  rw [Nat.zero_add] at hGetAbs
  rw [hGetAbs] at hAbs; injection hAbs with hEqA; subst hEqA
  have hGetSl := initLocalsLoop_getElem? body args 0 body.locals i ty hTy
  rw [Nat.zero_add] at hGetSl
  rw [hGetSl] at hSl; injection hSl with hEqS; subst hEqS
  cases i with
  | zero =>
    dsimp [initDiscrSlot, Nat.beq]
    exact discrSlotSound_liveSlot_liveUninit ty
  | succ k =>
    dsimp [initDiscrSlot, Nat.beq]
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
      exact ⟨hChk, ⟨some v, rfl⟩⟩
    | false =>
      dsimp
      cases hasStorageAnnotation body (k + 1) with
      | true => dsimp; exact ⟨True.intro, True.intro⟩
      | false => dsimp; exact discrSlotSound_liveSlot_liveUninit ty

private theorem discrEnvSound_set {bodyLocals : List MirTy}
    {env env' : List DiscrAbsSlot} {locals locals' : List LocalSlot}
    {id : Nat} {ty : MirTy} {abs' : DiscrAbsSlot} {sl' : LocalSlot}
    (hEnv : DiscrEnvSound bodyLocals env locals)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hSetE : setElem? env id abs' = some env')
    (hSetL : setElem? locals id sl' = some locals')
    (hSlSound : DiscrSlotSound ty abs' sl') :
    DiscrEnvSound bodyLocals env' locals' := by
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

private theorem deinitMoveOperandDiscr_sound {bodyLocals : List MirTy}
    {env : List DiscrAbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {srcTy : MirTy} {optVal : Option Val}
    (hEnv : DiscrEnvSound bodyLocals env locals)
    (hEv : evalOperandToSlot bodyLocals locals opnd = .ok (srcTy, optVal, locals')) :
    DiscrEnvSound bodyLocals (deinitMoveOperandDiscr bodyLocals env opnd) locals' := by
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
              cases ty with
              | enum ety =>
                let ⟨env', hSetE⟩ := setElem?_some_of_lt env p.localId
                  (if isZstEnumTy ety then .knownEnum ety 0 else .liveSlot) hLtE
                dsimp [deinitMoveOperandDiscr]
                rw [hP]; dsimp; rw [hTy]; dsimp; rw [hSetE]
                exact discrEnvSound_set hEnv hTy hSetE hSetL
                  (discrSlotSound_enum_liveUninit ety)
              | bool | int _ _ | unit | never | tuple _
              | ref _ _ | rawPtr _ _ | unsupported =>
                let ⟨env', hSetE⟩ := setElem?_some_of_lt env p.localId .liveSlot hLtE
                dsimp [deinitMoveOperandDiscr]
                rw [hP]; dsimp; rw [hTy]; dsimp; rw [hSetE]
                exact discrEnvSound_set hEnv hTy hSetE hSetL
                  (discrSlotSound_liveSlot_liveUninit _)

private theorem deinitMovePrimDiscr_sound {bodyLocals : List MirTy}
    {env : List DiscrAbsSlot} {locals locals' : List LocalSlot}
    {opnd : Operand} {v : Val}
    (hEnv : DiscrEnvSound bodyLocals env locals)
    (hEv : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    DiscrEnvSound bodyLocals (deinitMoveOperandDiscr bodyLocals env opnd) locals' := by
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
        exact deinitMoveOperandDiscr_sound hEnv hS

private theorem deinitMovesInRvalueDiscr_sound {bodyLocals : List MirTy}
    {env : List DiscrAbsSlot} {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hEnv : DiscrEnvSound bodyLocals env locals)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    DiscrEnvSound bodyLocals (deinitMovesInRvalueDiscr bodyLocals env rv) locals' := by
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
          exact deinitMoveOperandDiscr_sound hEnv hS
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
        exact deinitMovePrimDiscr_sound hEnv hO
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
          exact deinitMovePrimDiscr_sound (deinitMovePrimDiscr_sound hEnv hL) hR
  | discriminant p =>
    dsimp [deinitMovesInRvalueDiscr]
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

private theorem rvalueKnownEnumSlot_sound {bodyLocals : List MirTy}
    {env : List DiscrAbsSlot} {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hEnv : DiscrEnvSound bodyLocals env locals)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals'))
    (hChk : checkVal v dstTy = true) :
    DiscrSlotSound dstTy (rvalueKnownEnumSlot bodyLocals env dstTy rv) (.live (some v)) := by
  cases rv with
  | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
  | addressOf _ _ | aggregateTuple _ | unsupported =>
    exact ⟨hChk, ⟨some v, rfl⟩⟩
  | use opnd =>
    cases opnd with
    | constant c =>
      dsimp [rvalueKnownEnumSlot]
      cases dstTy with
      | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
        exact ⟨hChk, ⟨some v, rfl⟩⟩
      | enum ety =>
        dsimp
        cases hTyB : MirTy.beq c.ty (.enum ety) with
        | false => dsimp; exact ⟨hChk, ⟨some v, rfl⟩⟩
        | true =>
          dsimp
          have hCTy := mirTy_beq_eq hTyB
          dsimp [evalRvalue, evalOperandToSlot] at hEv
          rw [hCTy] at hEv
          cases hCL : evalConstLit (.enum ety) c.lit with
          | error _ => rw [hCL] at hEv; cases hEv
          | ok cv =>
            rw [hCL] at hEv; dsimp at hEv
            rw [mirTy_beq_refl (.enum ety)] at hEv; dsimp at hEv
            injection hEv with h1; injection h1 with hvEq _; subst hvEq
            cases cv with
            | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ =>
              exact ⟨hChk, ⟨some _, rfl⟩⟩
            | enumVal etyRes vIdx =>
              dsimp
              let ⟨hAdm, k, hLt, hValEq⟩ := checkVal_enum_iff.mp hChk
              injection hValEq with heEq hkEq; subst heEq; subst hkEq
              exact ⟨hChk, ⟨rfl, hAdm, hLt, rfl⟩⟩
    | copy p =>
      dsimp [rvalueKnownEnumSlot]
      cases hPE : p.projection.isEmpty with
      | false => dsimp; exact ⟨hChk, ⟨some v, rfl⟩⟩
      | true =>
        dsimp
        cases hSrcTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
        | none => exact ⟨hChk, ⟨some v, rfl⟩⟩
        | some srcTy =>
          cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
          | none => exact ⟨hChk, ⟨some v, rfl⟩⟩
          | some abs =>
            cases abs with
            | dead | liveSlot => exact ⟨hChk, ⟨some v, rfl⟩⟩
            | knownEnum ety vIdx =>
              dsimp
              cases hCond : (MirTy.beq srcTy dstTy && MirTy.beq dstTy (.enum ety)) with
              | false => dsimp; exact ⟨hChk, ⟨some v, rfl⟩⟩
              | true =>
                dsimp
                let ⟨hSD, hDE⟩ := bool_and_true hCond
                have hSDEq := mirTy_beq_eq hSD
                have hDEEq := mirTy_beq_eq hDE
                subst hSDEq; subst hDEEq
                dsimp [evalRvalue, evalOperandToSlot] at hEv
                rw [hPE] at hEv; dsimp at hEv; rw [hSrcTy] at hEv
                cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
                | none => rw [hSl] at hEv; cases hEv
                | some sl =>
                  rw [hSl] at hEv
                  let ⟨_, _, hAdm, hLt, hSlEq⟩ :=
                    hEnv.2.2 p.localId (.enum ety) (.knownEnum ety vIdx) sl hSrcTy hAbs hSl
                  rw [hSlEq] at hEv; dsimp at hEv
                  rw [mirTy_beq_refl (.enum ety)] at hEv; dsimp at hEv
                  injection hEv with h1; injection h1 with hvEq _; subst hvEq
                  exact ⟨hChk, ⟨rfl, hAdm, hLt, rfl⟩⟩
    | move p =>
      dsimp [rvalueKnownEnumSlot]
      cases hPE : p.projection.isEmpty with
      | false => dsimp; exact ⟨hChk, ⟨some v, rfl⟩⟩
      | true =>
        dsimp
        cases hSrcTy : Trusted.MirSemantics.getElem? bodyLocals p.localId with
        | none => exact ⟨hChk, ⟨some v, rfl⟩⟩
        | some srcTy =>
          cases hAbs : Trusted.MirSemantics.getElem? env p.localId with
          | none => exact ⟨hChk, ⟨some v, rfl⟩⟩
          | some abs =>
            cases abs with
            | dead | liveSlot => exact ⟨hChk, ⟨some v, rfl⟩⟩
            | knownEnum ety vIdx =>
              dsimp
              cases hCond : (MirTy.beq srcTy dstTy && MirTy.beq dstTy (.enum ety)) with
              | false => dsimp; exact ⟨hChk, ⟨some v, rfl⟩⟩
              | true =>
                dsimp
                let ⟨hSD, hDE⟩ := bool_and_true hCond
                have hSDEq := mirTy_beq_eq hSD
                have hDEEq := mirTy_beq_eq hDE
                subst hSDEq; subst hDEEq
                dsimp [evalRvalue, evalOperandToSlot] at hEv
                rw [hPE] at hEv; dsimp at hEv; rw [hSrcTy] at hEv
                cases hSl : Trusted.MirSemantics.getElem? locals p.localId with
                | none => rw [hSl] at hEv; cases hEv
                | some sl =>
                  rw [hSl] at hEv
                  let ⟨_, _, hAdm, hLt, hSlEq⟩ :=
                    hEnv.2.2 p.localId (.enum ety) (.knownEnum ety vIdx) sl hSrcTy hAbs hSl
                  rw [hSlEq] at hEv; dsimp at hEv
                  cases hSetL : setElem? locals p.localId (liveUninitSlot (.enum ety)) with
                  | none => rw [hSetL] at hEv; cases hEv
                  | some _ =>
                    rw [hSetL] at hEv; dsimp at hEv
                    rw [mirTy_beq_refl (.enum ety)] at hEv; dsimp at hEv
                    injection hEv with h1; injection h1 with hvEq _; subst hvEq
                    exact ⟨hChk, ⟨rfl, hAdm, hLt, rfl⟩⟩

private theorem stepDiscrStmtPair_sound {bSrc bTgt : Body}
    {env env' : List DiscrAbsSlot} {frame : FrameState}
    {cm : CallerMemory} {sSrc sTgt : StatementKind}
    (hLocEq : bSrc.locals = bTgt.locals)
    (hEnv : DiscrEnvSound bSrc.locals env frame.locals)
    (hPair : stepDiscrStmtPair bSrc.locals env sSrc sTgt = some env') :
    evalStatement bSrc frame cm sSrc = evalStatement bTgt frame cm sTgt ∧
    (∀ s', evalStatement bSrc frame cm sSrc = .step s' →
      ∃ locs',
        s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
               callerMem := cm } ∧
        DiscrEnvSound bSrc.locals env' locs') := by
  unfold stepDiscrStmtPair at hPair
  cases hStEq : stmtEq sSrc sTgt with
  | true =>
    rw [hStEq, if_bool_true rfl] at hPair
    have hEq := stmtEq_eq hStEq; subst hEq
    refine ⟨evalStatement_eq_of_same frame cm sSrc hLocEq, ?_⟩
    intro s' hEv
    cases sSrc with
    | nop =>
      injection hPair with hEnvEq; subst hEnvEq
      injection hEv with hSEq; subst hSEq
      exact ⟨frame.locals, rfl, hEnv⟩
    | unsupported => cases hEv
    | storageLive id =>
      dsimp at hPair
      cases hTy : Trusted.MirSemantics.getElem? bSrc.locals id with
      | none => rw [hTy] at hPair; cases hPair
      | some ty =>
        rw [hTy] at hPair
        dsimp [evalStatement] at hEv; rw [hTy] at hEv; dsimp at hEv
        cases hSetL : setElem? frame.locals id (liveUninitSlot ty) with
        | none => rw [hSetL] at hEv; cases hEv
        | some locs' =>
          rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
          cases ty with
          | enum ety =>
            dsimp at hPair
            exact ⟨locs', rfl,
              discrEnvSound_set hEnv hTy hPair hSetL (discrSlotSound_enum_liveUninit ety)⟩
          | bool | int _ _ | unit | never | tuple _
          | ref _ _ | rawPtr _ _ | unsupported =>
            dsimp at hPair
            exact ⟨locs', rfl,
              discrEnvSound_set hEnv hTy hPair hSetL (discrSlotSound_liveSlot_liveUninit _)⟩
    | storageDead id =>
      dsimp at hPair
      cases hZ : Nat.beq id 0 with
      | true => rw [hZ] at hPair; cases hPair
      | false =>
        rw [hZ] at hPair; dsimp at hPair
        dsimp [evalStatement] at hEv; rw [hZ] at hEv; dsimp at hEv
        cases hSetL : setElem? frame.locals id .dead with
        | none => rw [hSetL] at hEv; cases hEv
        | some locs' =>
          rw [hSetL] at hEv; injection hEv with hSEq; subst hSEq
          have hLt : id < bSrc.locals.length := by
            rw [← hEnv.2.1]
            cases Nat.lt_or_ge id env.length with
            | inl hlt => exact hlt
            | inr hge =>
              rw [setElem?_none_of_ge env id .dead hge] at hPair; cases hPair
          let ⟨ty, hTy⟩ := getElem?_some_of_lt bSrc.locals id hLt
          exact ⟨locs', rfl,
            discrEnvSound_set hEnv hTy hPair hSetL ⟨True.intro, True.intro⟩⟩
    | assign dst rv =>
      dsimp at hPair
      cases hPEmp : dst.projection.isEmpty with
      | false => rw [hPEmp] at hPair; cases hPair
      | true =>
        rw [hPEmp] at hPair; dsimp at hPair
        cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
        | none => rw [hDstTy] at hPair; cases hPair
        | some dstTy =>
          rw [hDstTy] at hPair; dsimp at hPair
          dsimp [evalStatement] at hEv; rw [hPEmp] at hEv; dsimp at hEv
          rw [hDstTy] at hEv; dsimp at hEv
          cases hRv : evalRvalue bSrc.locals frame.locals dstTy rv with
          | error _ => rw [hRv] at hEv; cases hEv
          | ok res =>
            let ⟨val, locs1⟩ := res
            rw [hRv] at hEv; dsimp at hEv
            have hEnv1 := deinitMovesInRvalueDiscr_sound hEnv hRv
            cases hW : writePlace locs1 dst.localId dstTy val with
            | error _ => rw [hW] at hEv; cases hEv
            | ok locs' =>
              rw [hW] at hEv; injection hEv with hSEq; subst hSEq
              dsimp [writePlace] at hW
              cases hChk : checkVal val dstTy with
              | false => rw [hChk] at hW; cases hW
              | true =>
                rw [hChk] at hW; dsimp at hW
                cases hSl1 : Trusted.MirSemantics.getElem? locs1 dst.localId with
                | none => rw [hSl1] at hW; cases hW
                | some sl1 =>
                  rw [hSl1] at hW
                  cases sl1 with
                  | dead => cases hW
                  | live _ =>
                    cases hSetL : setElem? locs1 dst.localId (.live (some val)) with
                    | none => rw [hSetL] at hW; cases hW
                    | some locsW =>
                      rw [hSetL] at hW; injection hW with hWEq; subst hWEq
                      exact ⟨locsW, rfl,
                        discrEnvSound_set hEnv1 hDstTy hPair hSetL
                          (rvalueKnownEnumSlot_sound hEnv hRv hChk)⟩
  | false =>
    rw [hStEq, if_bool_false rfl] at hPair
    cases hConstRw : isConstOpFoldRewrite bSrc.locals sSrc sTgt with
    | true =>
      rw [hConstRw, if_bool_true rfl] at hPair
      let ⟨dst, rvSrc, cOut, dstTy, res, hs1, hs2, hDstEmp, hDstTy, hCOTy, hEvOut, hRvSrc, hRvTgt⟩ :=
        isConstOpFoldRewrite_elim hConstRw
      subst hs1; subst hs2
      dsimp at hPair
      have hStmtEq :
          evalStatement bSrc frame cm (.assign dst rvSrc) =
          evalStatement bTgt frame cm (.assign dst (.use (.constant cOut))) := by
        dsimp [evalStatement]
        rw [← hLocEq, hDstEmp]; dsimp
        rw [hDstTy]; dsimp
        rw [hRvSrc frame.locals, hRvTgt bSrc.locals frame.locals]
      refine ⟨hStmtEq, ?_⟩
      intro s' hEvS
      dsimp [evalStatement] at hEvS
      rw [hDstEmp] at hEvS; dsimp at hEvS
      rw [hDstTy] at hEvS; dsimp at hEvS
      rw [hRvSrc frame.locals] at hEvS; dsimp at hEvS
      dsimp [writePlace] at hEvS
      have hChkOut : checkVal res dstTy = true := by
        rw [← hCOTy]; exact evalConstLit_checkVal hEvOut
      rw [hChkOut] at hEvS; dsimp at hEvS
      cases hSlD : Trusted.MirSemantics.getElem? frame.locals dst.localId with
      | none => rw [hSlD] at hEvS; cases hEvS
      | some slD =>
        rw [hSlD] at hEvS
        cases slD with
        | dead => cases hEvS
        | live _ =>
          cases hSetL : setElem? frame.locals dst.localId (.live (some res)) with
          | none => rw [hSetL] at hEvS; cases hEvS
          | some locsW =>
            rw [hSetL] at hEvS; injection hEvS with hSEq; subst hSEq
            exact ⟨locsW, rfl,
              discrEnvSound_set hEnv hDstTy hPair hSetL ⟨hChkOut, ⟨some res, rfl⟩⟩⟩
    | false =>
      rw [hConstRw, if_bool_false rfl] at hPair
      cases hDiscrRw : isEnumDiscrFoldRewrite false bSrc.locals sSrc sTgt with
      | false => rw [hDiscrRw] at hPair; cases hPair
      | true =>
        rw [hDiscrRw, if_bool_true rfl] at hPair
        cases sSrc with
        | nop | storageLive _ | storageDead _ | unsupported => cases hDiscrRw
        | assign dst rvS =>
          cases rvS with
          | use _ | binaryOp _ _ _ | unaryOp _ _ | ref _ _
          | addressOf _ _ | aggregateTuple _ | unsupported => cases hDiscrRw
          | discriminant p =>
            cases sTgt with
            | nop | storageLive _ | storageDead _ | unsupported => cases hDiscrRw
            | assign dst' rvT =>
              cases rvT with
              | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
              | addressOf _ _ | aggregateTuple _ | unsupported => cases hDiscrRw
              | use opndT =>
                cases opndT with
                | copy _ | move _ => cases hDiscrRw
                | constant cOut =>
                  dsimp [isEnumDiscrFoldRewrite] at hDiscrRw
                  dsimp at hPair
                  let ⟨hPre, hTypes⟩ := bool_and_true hDiscrRw
                  let ⟨h12P, hPEmp⟩ := bool_and_true hPre
                  let ⟨hDstEq, hDstEmp⟩ := bool_and_true h12P
                  have hDEq := placeEq_eq hDstEq; subst hDEq
                  cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
                  | none => rw [hDstTy] at hTypes; cases hTypes
                  | some dstTy =>
                    rw [hDstTy] at hTypes
                    cases hPTy : Trusted.MirSemantics.getElem? bSrc.locals p.localId with
                    | none => rw [hPTy] at hPair; cases hPair
                    | some pTy =>
                      rw [hPTy] at hPair; rw [hPTy] at hTypes
                      cases pTy with
                      | bool | int _ _ | unit | never | tuple _
                      | ref _ _ | rawPtr _ _ | unsupported => cases hPair
                      | enum ety =>
                        dsimp at hTypes
                        let ⟨h12E, _⟩ := bool_and_true hTypes
                        let ⟨hAdm, hDTyEq⟩ := bool_and_true h12E
                        have hDstTyEq := mirTy_beq_eq hDTyEq; subst hDstTyEq
                        cases hAbsP : Trusted.MirSemantics.getElem? env p.localId with
                        | none => rw [hAbsP] at hPair; cases hPair
                        | some slot =>
                          rw [hAbsP] at hPair; dsimp at hPair
                          have hLtL : p.localId < frame.locals.length := by
                            rw [hEnv.1.1]; exact getElem?_some_lt hPTy
                          let ⟨slP, hSlP⟩ := getElem?_some_of_lt frame.locals p.localId hLtL
                          have hSlPSound := hEnv.2.2 p.localId (.enum ety) slot slP hPTy hAbsP hSlP
                          have hBothEval :
                              ∃ res,
                                evalConstLit cOut.ty cOut.lit = .ok res ∧
                                cOut.ty = .int ety.discrWidth ety.discrSigned ∧
                                evalRvalue bSrc.locals frame.locals
                                  (.int ety.discrWidth ety.discrSigned) (.discriminant p) =
                                  .ok (res, frame.locals) ∧
                                setElem? env dst.localId .liveSlot = some env' := by
                            cases hZ : isZstEnumTy ety with
                            | true =>
                              rw [hZ, if_bool_true rfl] at hPair
                              cases hCand : enumVariantDiscrConst? ety 0 with
                              | none =>
                                rw [hCand] at hPair; dsimp at hPair
                                rw [Bool.and_false] at hPair; cases hPair
                              | some cand =>
                                rw [hCand] at hPair; dsimp at hPair
                                cases hCertOk : (discrSlotImplies slot .liveSlot && constOpEq cand cOut) with
                                | false => rw [hCertOk] at hPair; cases hPair
                                | true =>
                                  rw [hCertOk, if_bool_true rfl] at hPair
                                  let ⟨hImpLive, hCandMatch⟩ := bool_and_true hCertOk
                                  have hCEq := constOpEq_eq hCandMatch; subst hCEq
                                  let ⟨disc, _, _, hD0, hCTy, hEvC⟩ :=
                                    enumVariantDiscrConst?_elim hCand
                                  let ⟨hTrZ, _, _⟩ := isZstEnumTy_elim hZ
                                  let ⟨hWtP, oP, hSlPEq⟩ :=
                                    discrSlotImplies_sound hImpLive hSlPSound
                                  subst hSlPEq
                                  refine ⟨_, hEvC, hCTy, ?_, hPair⟩
                                  dsimp [evalRvalue]
                                  rw [hPEmp]; dsimp; rw [hPTy, hSlP]; dsimp
                                  rw [hAdm]; dsimp; rw [hTrZ]
                                  cases oP with
                                  | none => dsimp; rw [hD0]
                                  | some vp =>
                                    have hVpEq := checkVal_zstEnum_eq hZ hWtP
                                    subst hVpEq
                                    dsimp; rw [enumTy_beq_refl ety]; dsimp [Nat.beq]; rw [hD0]
                            | false =>
                              rw [hZ, if_bool_false rfl] at hPair
                              cases slot with
                              | dead | liveSlot => cases hPair
                              | knownEnum etyKnown vIdx =>
                                change (if (EnumTy.beq ety etyKnown &&
                                    match enumVariantDiscrConst? ety vIdx with
                                    | some cand => constOpEq cand cOut
                                    | none => false) = true then
                                    setElem? env dst.localId .liveSlot
                                  else none) = some env' at hPair
                                cases hCand : enumVariantDiscrConst? ety vIdx with
                                | none =>
                                  rw [hCand] at hPair; dsimp at hPair
                                  rw [Bool.and_false] at hPair; cases hPair
                                | some cand =>
                                  rw [hCand] at hPair; dsimp at hPair
                                  cases hCertOk : (EnumTy.beq ety etyKnown && constOpEq cand cOut) with
                                  | false => rw [hCertOk] at hPair; cases hPair
                                  | true =>
                                    rw [hCertOk, if_bool_true rfl] at hPair
                                    let ⟨hEEqB, hCandMatch⟩ := bool_and_true hCertOk
                                    have hEEq := enumTy_beq_eq hEEqB; subst hEEq
                                    have hCEq := constOpEq_eq hCandMatch; subst hCEq
                                    let ⟨disc, _, hVLt, hDV, hCTy, hEvC⟩ :=
                                      enumVariantDiscrConst?_elim hCand
                                    let ⟨_, _, _, _, hSlPEq⟩ := hSlPSound
                                    subst hSlPEq
                                    refine ⟨_, hEvC, hCTy, ?_, hPair⟩
                                    dsimp [evalRvalue]
                                    rw [hPEmp]; dsimp; rw [hPTy, hSlP]; dsimp
                                    rw [hAdm]; dsimp
                                    cases hTr : ety.tagRepr with
                                    | zeroSized =>
                                      unfold isZstEnumTy at hZ
                                      rw [hTr, hAdm] at hZ; cases hZ
                                    | scalar tw ts =>
                                      dsimp
                                      rw [enumTy_beq_refl ety, nat_lt_blt hVLt]; dsimp
                                      rw [hDV]
                          let ⟨res, hEvOut, hCOTy, hRvSrc, hSetEnv⟩ := hBothEval
                          have hRvTgt :
                              evalRvalue bSrc.locals frame.locals
                                (.int ety.discrWidth ety.discrSigned)
                                (.use (.constant cOut)) =
                              .ok (res, frame.locals) := by
                            dsimp [evalRvalue, evalOperandToSlot]
                            rw [hEvOut]; dsimp
                            rw [hCOTy, mirTy_beq_refl (.int ety.discrWidth ety.discrSigned)]; dsimp
                          have hStmtEq :
                              evalStatement bSrc frame cm (.assign dst (.discriminant p)) =
                              evalStatement bTgt frame cm (.assign dst (.use (.constant cOut))) := by
                            dsimp [evalStatement]
                            rw [← hLocEq, hDstEmp]; dsimp
                            rw [hDstTy]; dsimp; rw [hRvSrc, hRvTgt]
                          refine ⟨hStmtEq, ?_⟩
                          intro s' hEvS
                          dsimp [evalStatement] at hEvS
                          rw [hDstEmp] at hEvS; dsimp at hEvS
                          rw [hDstTy] at hEvS; dsimp at hEvS
                          rw [hRvSrc] at hEvS; dsimp at hEvS
                          dsimp [writePlace] at hEvS
                          have hChkOut :
                              checkVal res (.int ety.discrWidth ety.discrSigned) = true := by
                            rw [← hCOTy]; exact evalConstLit_checkVal hEvOut
                          rw [hChkOut] at hEvS; dsimp at hEvS
                          cases hSlD : Trusted.MirSemantics.getElem? frame.locals dst.localId with
                          | none => rw [hSlD] at hEvS; cases hEvS
                          | some slD =>
                            rw [hSlD] at hEvS
                            cases slD with
                            | dead => cases hEvS
                            | live _ =>
                              cases hSetL : setElem? frame.locals dst.localId (.live (some res)) with
                              | none => rw [hSetL] at hEvS; cases hEvS
                              | some locsW =>
                                rw [hSetL] at hEvS; injection hEvS with hSEq; subst hSEq
                                exact ⟨locsW, rfl,
                                  discrEnvSound_set hEnv hDstTy hSetEnv hSetL
                                    ⟨hChkOut, ⟨some res, rfl⟩⟩⟩

private theorem checkDiscrBlocksLoop_getElem? (bSrc bTgt : Body)
    (cert : BodyDiscrCert) :
    ∀ base bbs k bbSrc,
      checkDiscrBlocksLoop bSrc bTgt cert base bbs = true →
      Trusted.MirSemantics.getElem? bbs k = some bbSrc →
      checkDiscrBlock bSrc bTgt cert (base + k) bbSrc = true := by
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

private theorem checkDiscrEdge_sound {bSrc bTgt : Body} {cert : BodyDiscrCert}
    {edgeEnv : List DiscrAbsSlot} {locs' : List LocalSlot} {tgt : BasicBlockId}
    (hBBLen : bSrc.basicBlocks.length = bTgt.basicBlocks.length)
    (hLoops : checkDiscrBlocksLoop bSrc bTgt cert 0 bSrc.basicBlocks = true)
    (hEdge : checkDiscrEdge bSrc.basicBlocks.length cert edgeEnv tgt = true)
    (hSound : DiscrEnvSound bSrc.locals edgeEnv locs')
    (hLt : tgt < bSrc.basicBlocks.length) :
    ∃ bbSrc bbTgt entryEnv exitEnv,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks tgt = some bbSrc ∧
      Trusted.MirSemantics.getElem? bTgt.basicBlocks tgt = some bbTgt ∧
      Trusted.MirSemantics.getElem? cert tgt = some (some entryEnv) ∧
      DiscrEnvSound bSrc.locals entryEnv locs' ∧
      stepDiscrStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements = some exitEnv ∧
      checkDiscrBlock bSrc bTgt cert tgt bbSrc = true := by
  unfold checkDiscrEdge at hEdge
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
      have hChkBlk := checkDiscrBlocksLoop_getElem? bSrc bTgt cert 0
        bSrc.basicBlocks tgt bbSrc hLoops hBBSrc
      rw [Nat.zero_add] at hChkBlk
      have hChkCopy := hChkBlk
      unfold checkDiscrBlock at hChkCopy
      rw [hCertTgt, hBBTgt] at hChkCopy; dsimp at hChkCopy
      let ⟨_, hStmtsMatch⟩ := bool_and_true hChkCopy
      cases hPair : stepDiscrStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements with
      | none => rw [hPair] at hStmtsMatch; cases hStmtsMatch
      | some exitEnv =>
        exact ⟨bbSrc, bbTgt, entryEnv, exitEnv, hBBSrc, hBBTgt, rfl,
               discrEnvImplies_sound hEdge hSound, hPair, hChkBlk⟩

private theorem constAndEnumDiscrFold_certified_query_lockstep
    {pSrc pTgt : Program} {cert : ProgramDiscrCert}
    (hRel : isConstAndEnumDiscrFoldProgram pSrc pTgt = true)
    (hCert : checkConstAndEnumDiscrFoldProgram cert pSrc pTgt = true)
    (q : Query) :
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q) := by
  have hGen := isConstAndEnumDiscrFoldProgram_to_generic hRel
  let ⟨_, hBodiesRel⟩ := bool_and_true hRel
  let ⟨hCertLenB, hCertZip⟩ := bool_and_true hCert
  have hCertLen := nat_beq_eq hCertLenB
  apply lockstep_inv_query_iff
    (Inv := fun s =>
      ∃ frame bSrc bTgt bodyCert,
        s.frames = [frame] ∧
        Trusted.MirSemantics.getElem? pSrc.bodies frame.defId = some bSrc ∧
        Trusted.MirSemantics.getElem? pTgt.bodies frame.defId = some bTgt ∧
        Trusted.MirSemantics.getElem? cert frame.defId = some bodyCert ∧
        isConstAndEnumDiscrFoldBody bSrc bTgt = true ∧
        checkConstAndEnumDiscrFoldBody bodyCert bSrc bTgt = true ∧
        LocalsWellTyped bSrc.locals frame.locals ∧
        (frame.blockIdx < bSrc.basicBlocks.length →
          ∃ bbSrc bbTgt entryEnv curEnv exitEnv,
            Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx = some bbSrc ∧
            Trusted.MirSemantics.getElem? bTgt.basicBlocks frame.blockIdx = some bbTgt ∧
            Trusted.MirSemantics.getElem? bodyCert frame.blockIdx = some (some entryEnv) ∧
            DiscrEnvSound bSrc.locals curEnv frame.locals ∧
            stepDiscrStmtsPair bSrc.locals entryEnv bbSrc.statements bbTgt.statements = some exitEnv ∧
            stepDiscrStmtsPair bSrc.locals curEnv
              (bbSrc.statements.drop frame.stmtIdx)
              (bbTgt.statements.drop frame.stmtIdx) = some exitEnv ∧
            checkDiscrBlock bSrc bTgt bodyCert frame.blockIdx bbSrc = true))
    (genericProgRel_initState_eq isConstAndEnumDiscrFoldStmt_assignOnly hGen q)
  · intro s₀ hOk
    let ⟨_, _, bSrc, hBSrc, hNotEmp, _, _, _, hArgs, hEqS⟩ := initState_ok_elim hOk
    subst hEqS
    let ⟨bTgt, hBTgt, hBRel⟩ := listRel_getElem?_left hBodiesRel hBSrc
    let ⟨bodyCert, bTgt', hBCert, hBTgt', hBodyCertOk⟩ :=
      listRel_zip_getElem? hCertLen hCertZip hBSrc
    rw [hBTgt] at hBTgt'; injection hBTgt' with hBEq; subst hBEq
    refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert, hBRel, hBodyCertOk,
            initLocalsLoop_wellTyped hArgs, ?_⟩
    intro hLt0
    have hBodyCertCopy := hBodyCertOk
    unfold checkConstAndEnumDiscrFoldBody at hBodyCertCopy
    let ⟨h123, hLoops⟩ := bool_and_true hBodyCertCopy
    let ⟨_, hEntryChk⟩ := bool_and_true h123
    rw [hNotEmp, if_bool_false rfl] at hEntryChk
    cases hC0 : Trusted.MirSemantics.getElem? bodyCert 0 with
    | none => rw [hC0] at hEntryChk; cases hEntryChk
    | some optE0 =>
      rw [hC0] at hEntryChk
      cases optE0 with
      | none => cases hEntryChk
      | some env₀ =>
        have hEnv0Sound := discrEnvImplies_sound hEntryChk (initDiscrEnvLoop_sound hArgs)
        let ⟨_, hBBsRel⟩ := bool_and_true hBRel
        have hBBLen := listRel_length hBBsRel
        let ⟨bbSrc, hBBSrc⟩ := getElem?_some_of_lt bSrc.basicBlocks 0 hLt0
        let ⟨bbTgt, hBBTgt⟩ := getElem?_some_of_lt bTgt.basicBlocks 0
          (by rw [← hBBLen]; exact hLt0)
        have hChk0 := checkDiscrBlocksLoop_getElem? bSrc bTgt bodyCert 0
          bSrc.basicBlocks 0 bbSrc hLoops hBBSrc
        rw [Nat.zero_add] at hChk0
        have hChk0Copy := hChk0
        unfold checkDiscrBlock at hChk0Copy
        rw [hC0, hBBTgt] at hChk0Copy; dsimp at hChk0Copy
        let ⟨_, hStMatch⟩ := bool_and_true hChk0Copy
        cases hPair0 : stepDiscrStmtsPair bSrc.locals env₀ bbSrc.statements bbTgt.statements with
        | none => rw [hPair0] at hStMatch; cases hStMatch
        | some exitEnv =>
          exact ⟨bbSrc, bbTgt, env₀, env₀, exitEnv, hBBSrc, hBBTgt, rfl,
                 hEnv0Sound, hPair0, hPair0, hChk0⟩
  · intro s hInv
    let ⟨frame, bSrc, bTgt, bodyCert, hFrames, hBSrc, hBTgt, hBCert,
         hBRel, hBodyCertOk, hWt, hBlkInv⟩ := hInv
    let ⟨hBHdr, hBBsRel⟩ := bool_and_true hBRel
    let ⟨_, hLocEq, _, _⟩ := bodyHeaderEq_elim hBHdr
    have hBBLen := listRel_length hBBsRel
    have hBodyCertCopy := hBodyCertOk
    unfold checkConstAndEnumDiscrFoldBody at hBodyCertCopy
    let ⟨_, hLoops⟩ := bool_and_true hBodyCertCopy
    cases s with
    | mk fs cm =>
      dsimp at hFrames; subst hFrames
      cases hBBSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks frame.blockIdx with
      | none =>
        have hBBTgtNone := (listRel_getElem?_none_iff frame.blockIdx hBBsRel).mp hBBSrc
        have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
            evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
          unfold evalStep; dsimp; rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgtNone]
        refine ⟨hEvEq, ?_⟩
        intro s' hStepS
        unfold evalStep at hStepS; dsimp at hStepS
        rw [hBSrc] at hStepS; dsimp at hStepS; rw [hBBSrc] at hStepS; cases hStepS
      | some bbSrc =>
        have hLtBlk : frame.blockIdx < bSrc.basicBlocks.length := getElem?_some_lt hBBSrc
        let ⟨bbSrc', bbTgt, entryEnv, curEnv, exitEnv,
             hBBSrc', hBBTgt, hCertEntry, hCurSound, hFullPair, hRemPair, hChkBlk⟩ :=
          hBlkInv hLtBlk
        rw [hBBSrc] at hBBSrc'; injection hBBSrc' with hBBEq; subst hBBEq
        let ⟨_, hBBTgt', hBBRel⟩ := listRel_getElem?_left hBBsRel hBBSrc
        rw [hBBTgt] at hBBTgt'; injection hBBTgt' with hBBTEq; subst hBBTEq
        let ⟨h12BB, hTermRel⟩ := bool_and_true hBBRel
        let ⟨hCleanEq, hStmtsRel⟩ := bool_and_true h12BB
        have hStLenEq := listRel_length hStmtsRel
        cases hDropS : bbSrc.statements.drop frame.stmtIdx with
        | cons sSrc restS =>
          rw [hDropS] at hRemPair
          cases hDropT : bbTgt.statements.drop frame.stmtIdx with
          | nil => rw [hDropT] at hRemPair; cases hRemPair
          | cons sTgt restT =>
            rw [hDropT] at hRemPair
            dsimp [stepDiscrStmtsPair] at hRemPair
            cases hOne : stepDiscrStmtPair bSrc.locals curEnv sSrc sTgt with
            | none => rw [hOne] at hRemPair; cases hRemPair
            | some nextEnv =>
              rw [hOne] at hRemPair
              let ⟨hGetS, hDropNextS⟩ := getElem?_of_drop_eq_cons hDropS
              let ⟨hGetT, hDropNextT⟩ := getElem?_of_drop_eq_cons hDropT
              let ⟨hStmtEq, hStmtNext⟩ := stepDiscrStmtPair_sound (cm := cm) hLocEq hCurSound hOne
              have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                  evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
                unfold evalStep; dsimp
                rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
                rw [hGetS, hGetT]; dsimp
                exact hStmtEq
              refine ⟨hEvEq, ?_⟩
              intro s' hStepS
              unfold evalStep at hStepS; dsimp at hStepS
              rw [hBSrc] at hStepS; dsimp at hStepS
              rw [hBBSrc] at hStepS; dsimp at hStepS
              rw [hGetS] at hStepS; dsimp at hStepS
              let ⟨locs', hEqS', hNextSound⟩ := hStmtNext s' hStepS
              subst hEqS'
              refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                      hBRel, hBodyCertOk, hNextSound.1, ?_⟩
              intro _
              refine ⟨bbSrc, bbTgt, entryEnv, nextEnv, exitEnv,
                      hBBSrc, hBBTgt, hCertEntry, hNextSound, hFullPair, ?_, hChkBlk⟩
              dsimp; rw [hDropNextS, hDropNextT]; exact hRemPair
        | nil =>
          rw [hDropS] at hRemPair
          cases hDropT : bbTgt.statements.drop frame.stmtIdx with
          | cons _ _ => rw [hDropT] at hRemPair; cases hRemPair
          | nil =>
            rw [hDropT] at hRemPair
            injection hRemPair with hCurExit; subst hCurExit
            have hNoneS := getElem?_none_of_ge (le_of_drop_eq_nil hDropS)
            have hNoneT := getElem?_none_of_ge (le_of_drop_eq_nil hDropT)
            have hEvEq : evalStep pSrc 0 { frames := [frame], callerMem := cm } =
                evalStep pTgt 0 { frames := [frame], callerMem := cm } := by
              unfold evalStep; dsimp
              rw [hBSrc, hBTgt]; dsimp; rw [hBBSrc, hBBTgt]; dsimp
              rw [hNoneS, hNoneT]; dsimp; rw [hStLenEq]
              cases Nat.beq frame.stmtIdx bbTgt.statements.length with
              | false => rfl
              | true =>
                rw [if_bool_true rfl, if_bool_true rfl]
                exact evalTerminator_eq_of_eq hLocEq (bool_beq_eq hCleanEq)
                  (terminatorEq_eq hTermRel)
            refine ⟨hEvEq, ?_⟩
            intro s' hStepS
            unfold evalStep at hStepS; dsimp at hStepS
            rw [hBSrc] at hStepS; dsimp at hStepS
            rw [hBBSrc] at hStepS; dsimp at hStepS
            rw [hNoneS] at hStepS; dsimp at hStepS
            cases hEnd : Nat.beq frame.stmtIdx bbSrc.statements.length with
            | false => rw [hEnd] at hStepS; cases hStepS
            | true =>
              rw [hEnd] at hStepS; dsimp at hStepS
              have hChkBlkCopy := hChkBlk
              unfold checkDiscrBlock at hChkBlkCopy
              rw [hCertEntry, hBBTgt] at hChkBlkCopy; dsimp at hChkBlkCopy
              let ⟨_, hTermChk⟩ := bool_and_true hChkBlkCopy
              rw [hFullPair] at hTermChk; dsimp at hTermChk
              unfold evalTerminator at hStepS
              cases hTm : bbSrc.terminator with
              | return_ =>
                rw [hTm] at hStepS; dsimp at hStepS
                cases hCl : bbSrc.cleanup with
                | true => rw [hCl] at hStepS; cases hStepS
                | false =>
                  rw [hCl] at hStepS; dsimp at hStepS
                  cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
                  | none => rw [h0] at hStepS; cases hStepS
                  | some sl0 =>
                    rw [h0] at hStepS
                    cases sl0 with
                    | dead => cases hStepS
                    | live o => cases o <;> cases hStepS
              | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
                rw [hTm] at hStepS; cases hStepS
              | goto tgt =>
                rw [hTm] at hStepS; rw [hTm] at hTermChk; dsimp at hTermChk
                injection hStepS with hSEq; subst hSEq
                refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                        hBRel, hBodyCertOk, hWt, ?_⟩
                intro hLtTgt
                let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                  checkDiscrEdge_sound hBBLen hLoops hTermChk hCurSound hLtTgt
                exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
              | switchInt discr targets =>
                rw [hTm] at hStepS; rw [hTm] at hTermChk; dsimp at hStepS; dsimp at hTermChk
                let ⟨hOtherEdge, hBranchEdges⟩ := bool_and_true hTermChk
                cases hEvD : evalPrimitiveOperand bSrc.locals frame.locals discr with
                | error _ => rw [hEvD] at hStepS; cases hStepS
                | ok resD =>
                  let ⟨dv, locsAfter⟩ := resD
                  rw [hEvD] at hStepS; dsimp at hStepS
                  have hAfterSound := deinitMovePrimDiscr_sound hCurSound hEvD
                  cases dv with
                  | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => cases hStepS
                  | bool bv =>
                    dsimp at hStepS
                    cases hSwB : evalBoolSwitchBranches bv targets.otherwise targets.branches with
                    | error _ => rw [hSwB] at hStepS; cases hStepS
                    | ok tgt =>
                      rw [hSwB] at hStepS
                      injection hStepS with hSEq; subst hSEq
                      refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                              hBRel, hBodyCertOk, hAfterSound.1, ?_⟩
                      intro hLtTgt
                      cases evalBoolSwitchBranches_cases hSwB with
                      | inl hIn =>
                        let ⟨cb, hMem⟩ := hIn
                        have hBrEdge := list_all_mem_true hBranchEdges hMem
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkDiscrEdge_sound hBBLen hLoops hBrEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                      | inr hTgtEq =>
                        subst hTgtEq
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkDiscrEdge_sound hBBLen hLoops hOtherEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                  | scalar sv =>
                    dsimp at hStepS
                    cases hSwS : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                    | error _ => rw [hSwS] at hStepS; cases hStepS
                    | ok tgt =>
                      rw [hSwS] at hStepS
                      injection hStepS with hSEq; subst hSEq
                      refine ⟨_, bSrc, bTgt, bodyCert, rfl, hBSrc, hBTgt, hBCert,
                              hBRel, hBodyCertOk, hAfterSound.1, ?_⟩
                      intro hLtTgt
                      cases evalSwitchBranches_cases hSwS with
                      | inl hIn =>
                        let ⟨cb, hMem⟩ := hIn
                        have hBrEdge := list_all_mem_true hBranchEdges hMem
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkDiscrEdge_sound hBBLen hLoops hBrEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩
                      | inr hFall =>
                        let ⟨hTgtEq, _⟩ := hFall
                        subst hTgtEq
                        let ⟨bbS2, bbT2, eEnv2, xEnv2, hBBS2, hBBT2, hCE2, hES2, hP2, hCB2⟩ :=
                          checkDiscrEdge_sound hBBLen hLoops hOtherEdge hAfterSound hLtTgt
                        exact ⟨bbS2, bbT2, eEnv2, eEnv2, xEnv2,
                               hBBS2, hBBT2, hCE2, hES2, hP2, hP2, hCB2⟩

private theorem vc_transport_constAndEnumDiscrFold_certified_iff_priv
    (pSrc pTgt : Program) (cert : ProgramDiscrCert)
    (hRel : isConstAndEnumDiscrFoldProgram pSrc pTgt = true)
    (hCert : checkConstAndEnumDiscrFoldProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  have hGen := isConstAndEnumDiscrFoldProgram_to_generic hRel
  let ⟨hHdr, hBodies⟩ := bool_and_true hGen
  apply fullSemanticEquiv_of_query_iff hHdr
  · intro defId bSrc bTgt hBS hBT
    let ⟨bTgt', hBT', hBRel⟩ := listRel_getElem?_left hBodies hBS
    rw [hBT] at hBT'; injection hBT' with hEqB; subst hEqB
    let ⟨hBHdr, _, hBBEmpty, _, hBounds, _⟩ :=
      genericBodyRel_storage_eq isConstAndEnumDiscrFoldStmt_assignOnly hBRel
    exact ⟨hBHdr, hBBEmpty, hBounds⟩
  · intro q
    exact constAndEnumDiscrFold_certified_query_lockstep hRel hCert q
  · intro defId args
    have hRelE : isConstAndEnumDiscrFoldProgram (entryProgForBody pSrc defId)
        (entryProgForBody pTgt defId) = true := by
      let ⟨hPH, hPB⟩ := bool_and_true hRel
      exact bool_and_intro (programHeaderEq_entryProg defId hPH) hPB
    exact (constAndEnumDiscrFold_certified_query_lockstep hRelE hCert { args := args }).1

/-! #### Theorem 7: End-to-End 6-Stage `InstSimplify` + `GVN` Pipeline
Theorem -/

private theorem bodies_map_identity_eq_of_rel {r : Body → Body → Bool}
    (hId : ∀ b₁ b₂, r b₁ b₂ = true → bodyHeaderEq b₁ b₂ = true) :
    ∀ {bs₁ bs₂ : List Body},
      listRel r bs₁ bs₂ = true →
      bs₁.map (fun b => b.identity) = bs₂.map (fun b => b.identity)
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | b₁ :: rest₁, b₂ :: rest₂, h => by
    let ⟨hHead, hTail⟩ := bool_and_true h
    let ⟨_, _, _, hIdEq⟩ := bodyHeaderEq_elim (hId b₁ b₂ hHead)
    dsimp [List.map]
    rw [hIdEq, bodies_map_identity_eq_of_rel hId hTail]

private theorem prog_pass_meta_eq {bodyRel : Body → Body → Bool}
    (hId : ∀ b₁ b₂, bodyRel b₁ b₂ = true → bodyHeaderEq b₁ b₂ = true)
    {p₁ p₂ : Program}
    (h : (programHeaderEq p₁ p₂ && listRel bodyRel p₁.bodies p₂.bodies) = true) :
    p₁.pointerWidthBits = p₂.pointerWidthBits ∧
    p₁.mirProfileVersion = p₂.mirProfileVersion ∧
    p₁.entryDefId = p₂.entryDefId ∧
    p₁.scope = p₂.scope ∧
    p₁.bodies.length = p₂.bodies.length ∧
    p₁.bodies.map (fun b => b.identity) = p₂.bodies.map (fun b => b.identity) := by
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  let ⟨hPw, hVer, hEnt, hSc⟩ := programHeaderEq_elim hHdr
  exact ⟨hPw, hVer, hEnt, hSc, listRel_length hBodies,
         bodies_map_identity_eq_of_rel hId hBodies⟩

private theorem gvnInstSimplify_pipeline_crate_and_unit_iff_priv
    (p₀ p₁ p₂ p₃ p₄ p₅ p₆ : Program)
    (zCert : ProgramNonZeroCert)
    (aCert : ProgramAbsCert)
    (dCert : ProgramDiscrCert)
    (hBoolCmp : isBoolCmpSimplifyProgram p₀ p₁ = true)
    (hNeutral : isNeutralIdentityProgram p₁ p₂ = true)
    (hZeroDiv : isZeroLhsDivRemProgram p₂ p₃ = true)
    (hZeroDivCert : checkZeroLhsDivRemProgram zCert p₂ p₃ = true)
    (hAbsorb : isAbsorbingOrSelfCancelProgram p₃ p₄ = true)
    (hAbsorbCert : checkAbsorbingOrSelfCancelProgram aCert p₃ p₄ = true)
    (hDoubleUn : isDoubleUnaryChainProgram p₄ p₅ = true)
    (hConstDiscr : isConstAndEnumDiscrFoldProgram p₅ p₆ = true)
    (hConstDiscrCert : checkConstAndEnumDiscrFoldProgram dCert p₅ p₆ = true) :
    FullSemanticEquiv p₀ p₆ ∧
    (∀ (safety : String → List Val → Prop) (prop : Program → Prop),
      (prop p₆ ↔ prop p₀) →
      (CrateTheorem ⟨p₆, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨p₀, ⟨safety, prop⟩⟩) ∧
      (UnitTheorem ⟨p₆, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨p₀, ⟨safety, prop⟩⟩)) := by
  let ⟨hPw01, hVer01, hEnt01, hSc01, hLen01, hId01⟩ :=
    prog_pass_meta_eq (fun _ _ hb => (bool_and_true hb).1) hBoolCmp
  let ⟨hPw12, hVer12, hEnt12, hSc12, hLen12, hId12⟩ :=
    prog_pass_meta_eq (fun _ _ hb => (bool_and_true hb).1) hNeutral
  let ⟨hPw23, hVer23, hEnt23, hSc23, hLen23, hId23⟩ :=
    prog_pass_meta_eq (fun _ _ hb => (bool_and_true hb).1) hZeroDiv
  let ⟨hPw34, hVer34, hEnt34, hSc34, hLen34, hId34⟩ :=
    prog_pass_meta_eq (fun _ _ hb => (bool_and_true hb).1) hAbsorb
  let ⟨hPw45, hVer45, hEnt45, hSc45, hLen45, hId45⟩ :=
    prog_pass_meta_eq (fun _ _ hb => (bool_and_true hb).1) hDoubleUn
  let ⟨hPw56, hVer56, hEnt56, hSc56, hLen56, hId56⟩ :=
    prog_pass_meta_eq (fun _ _ hb => (bool_and_true hb).1) hConstDiscr
  have hEq01 := boolCmpSimplify_bidirectional_iff_priv p₀ p₁ hBoolCmp
  have hEq12 := neutralIdentity_bidirectional_iff_priv p₁ p₂ hNeutral
  have hEq23 := vc_transport_zeroLhsDivRem_certified_iff_priv p₂ p₃ zCert hZeroDiv hZeroDivCert
  have hEq34 := vc_transport_absorbingAndSelfCancel_certified_iff_priv p₃ p₄ aCert hAbsorb hAbsorbCert
  have hEq45 := doubleUnaryChain_bidirectional_iff_priv p₄ p₅ hDoubleUn
  have hEq56 := vc_transport_constAndEnumDiscrFold_certified_iff_priv p₅ p₆ dCert hConstDiscr hConstDiscrCert
  have hEq02 := fullSemanticEquiv_trans hLen01 hEq01 hEq12
  have hLen02 := hLen01.trans hLen12
  have hEq03 := fullSemanticEquiv_trans hLen02 hEq02 hEq23
  have hLen03 := hLen02.trans hLen23
  have hEq04 := fullSemanticEquiv_trans hLen03 hEq03 hEq34
  have hLen04 := hLen03.trans hLen34
  have hEq05 := fullSemanticEquiv_trans hLen04 hEq04 hEq45
  have hLen05 := hLen04.trans hLen45
  have hEq06 := fullSemanticEquiv_trans hLen05 hEq05 hEq56
  refine ⟨hEq06, ?_⟩
  intro safety prop hProp
  exact programVerified_iff_of_equiv hEq06
    (hPw01.trans (hPw12.trans (hPw23.trans (hPw34.trans (hPw45.trans hPw56)))))
    (hVer01.trans (hVer12.trans (hVer23.trans (hVer34.trans (hVer45.trans hVer56)))))
    (hEnt01.trans (hEnt12.trans (hEnt23.trans (hEnt34.trans (hEnt45.trans hEnt56)))))
    (hSc01.trans (hSc12.trans (hSc23.trans (hSc34.trans (hSc45.trans hSc56)))))
    (hId01.trans (hId12.trans (hId23.trans (hId34.trans (hId45.trans hId56)))))
    safety prop hProp

/-! ## Part III: Core Target Theorems Directly Over `Trusted.MirSemantics` -/

/-- **Theorem 1 (`InstSimplify::simplify_bool_cmp` Unconditional Bidirectional
Equivalence):**
Simplifying boolean `Eq`/`Ne` comparisons against valid `false`/`true` constants
into `Use(opnd)` or `UnaryOp(Not, opnd)` (`isBoolCmpSimplifyProgram`) preserves
`WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`,
`SatisfiesPost`, and `BodyVerified` unconditionally in both directions (`↔`). -/
theorem boolCmpSimplify_bidirectional_iff
    (pSrc pTgt : Program)
    (hRel : isBoolCmpSimplifyProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact boolCmpSimplify_bidirectional_iff_priv pSrc pTgt hRel

/-- **Theorem 2 (`GVN::simplify_binary_inner` Neutral-Identity Unconditional
Bidirectional Equivalence):**
Rewriting neutral-element binary operations (`+ 0`, `- 0`, `| 0`, `^ 0`, `* 1`,
`/ +1` including at signed `INT_MIN`, `& ALL_ONES`, and wrapping `<< 0` / `>> 0`)
into `Use(opnd)` (`isNeutralIdentityProgram`) preserves full bidirectional
equivalence (`↔`) across all $M_{\text{anneal}}$ judgments. -/
theorem neutralIdentity_bidirectional_iff
    (pSrc pTgt : Program)
    (hRel : isNeutralIdentityProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact neutralIdentity_bidirectional_iff_priv pSrc pTgt hRel

/-- **Theorem 3a (Unconditional Forward Codegen Refinement for `0 / rhs ↦ 0` and
`0 % rhs ↦ 0`, `GVN::simplify_binary_inner`):**
Folding `Div(0, rhs)` or `Rem(0, rhs)` to `Use(0)` (`isZeroLhsDivRemProgram`)
unconditionally refines well-formed executions (`pSrc → pTgt`). -/
theorem codegen_zeroLhsDivRem_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isZeroLhsDivRemProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  exact codegen_zeroLhsDivRem_refines_unconditional_priv pSrc pTgt hRel

/-- **Theorem 3b (Certified Bidirectional VC Transport for `0 / rhs ↦ 0` and
`0 % rhs ↦ 0`):**
Pairing `isZeroLhsDivRemProgram` with `checkZeroLhsDivRemProgram` (requiring
`rhs` to be a non-`move`, initialized, non-zero divisor) restores full
bidirectional equivalence (`↔`) across all queries. -/
theorem vc_transport_zeroLhsDivRem_certified_iff
    (pSrc pTgt : Program) (cert : ProgramNonZeroCert)
    (hRel : isZeroLhsDivRemProgram pSrc pTgt = true)
    (hCert : checkZeroLhsDivRemProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact vc_transport_zeroLhsDivRem_certified_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 4a (Unconditional Forward Codegen Refinement for Absorbing &
Self-Canceling Peepholes, `GVN::simplify_binary_inner`):**
Folding absorbing (`* 0`, `& 0`, wrapping `0 << rhs` / `0 >> rhs`, `% 1`,
`| ALL_ONES`) and `.copy` self-canceling (`-`, `^`, `==`, `!=`) operations
unconditionally refines well-formed executions (`pSrc → pTgt`). -/
theorem codegen_absorbingAndSelfCancel_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isAbsorbingOrSelfCancelProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  exact codegen_absorbingAndSelfCancel_refines_unconditional_priv pSrc pTgt hRel

/-- **Theorem 4b (Certified Bidirectional VC Transport for Absorbing &
Self-Canceling Peepholes):**
Pairing `isAbsorbingOrSelfCancelProgram` with `checkAbsorbingOrSelfCancelProgram`
(requiring eliminated operands to be non-`move` live-initialized primitive reads)
restores full bidirectional equivalence (`↔`) across all queries. -/
theorem vc_transport_absorbingAndSelfCancel_certified_iff
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isAbsorbingOrSelfCancelProgram pSrc pTgt = true)
    (hCert : checkAbsorbingOrSelfCancelProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact vc_transport_absorbingAndSelfCancel_certified_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 5 (`GVN::simplify_unary` Adjacent `Not(Not(x))` & `Neg(Neg(x))`
Unconditional Bidirectional Equivalence):**
Rewriting `_t = UnaryOp(op, copy x); _dst = UnaryOp(op, copy _t)` (`_t ≠ x`,
`op ∈ {.not, .neg}`) to `_t = UnaryOp(op, copy x); _dst = Use(copy x)` preserves
full bidirectional equivalence (`↔`) across all inputs—including signed
`INT_MIN` (`-(-INT_MIN) = INT_MIN` under two's-complement wrapping). -/
theorem doubleUnaryChain_bidirectional_iff
    (pSrc pTgt : Program)
    (hRel : isDoubleUnaryChainProgram pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact doubleUnaryChain_bidirectional_iff_priv pSrc pTgt hRel

/-- **Theorem 6a (Unconditional Forward Codegen Refinement for Constant
`UnaryOp`/`BinaryOp` Folding & 1-Variant Enum `Discriminant` Folding):**
Validated constant `UnaryOp`/`BinaryOp` folding and 1-variant enum
`Discriminant` folding unconditionally refine well-formed executions
(`pSrc → pTgt`). -/
theorem codegen_constAndEnumDiscrFold_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isUncondConstAndSingleDiscrFoldProgram pSrc pTgt = true) :
    ForwardCodegenRefines pSrc pTgt := by
  exact codegen_constAndEnumDiscrFold_refines_unconditional_priv pSrc pTgt hRel

/-- **Theorem 6b (Certified Bidirectional VC Transport for Constant Folding &
General Enum `Discriminant` Folding, `GVN::simplify_discriminant`):**
Pairing `isConstAndEnumDiscrFoldProgram` with `checkConstAndEnumDiscrFoldProgram`
restores full bidirectional equivalence (`↔`) across both 1-variant ZST and
multi-variant scalar-tagged fieldless enums. -/
theorem vc_transport_constAndEnumDiscrFold_certified_iff
    (pSrc pTgt : Program) (cert : ProgramDiscrCert)
    (hRel : isConstAndEnumDiscrFoldProgram pSrc pTgt = true)
    (hCert : checkConstAndEnumDiscrFoldProgram cert pSrc pTgt = true) :
    FullSemanticEquiv pSrc pTgt := by
  exact vc_transport_constAndEnumDiscrFold_certified_iff_priv pSrc pTgt cert hRel hCert

/-- **Theorem 7 (End-to-End 6-Stage `InstSimplify` + `GVN` Pipeline Bidirectional
`CrateTheorem` & `UnitTheorem` Transport):**
Composing `BoolCmpSimplify`, `NeutralIdentity`, certified `ZeroLhsDivRem`,
certified `AbsorbingOrSelfCancel`, `DoubleUnaryChain`, and certified
`ConstAndEnumDiscrFold` preserves `FullSemanticEquiv` and transports
`CrateTheorem` and `UnitTheorem` bidirectionally (`↔`) whenever `specs.property`
respects the pipeline endpoints. -/
theorem gvnInstSimplify_pipeline_crate_and_unit_iff
    (p₀ p₁ p₂ p₃ p₄ p₅ p₆ : Program)
    (zCert : ProgramNonZeroCert)
    (aCert : ProgramAbsCert)
    (dCert : ProgramDiscrCert)
    (hBoolCmp : isBoolCmpSimplifyProgram p₀ p₁ = true)
    (hNeutral : isNeutralIdentityProgram p₁ p₂ = true)
    (hZeroDiv : isZeroLhsDivRemProgram p₂ p₃ = true)
    (hZeroDivCert : checkZeroLhsDivRemProgram zCert p₂ p₃ = true)
    (hAbsorb : isAbsorbingOrSelfCancelProgram p₃ p₄ = true)
    (hAbsorbCert : checkAbsorbingOrSelfCancelProgram aCert p₃ p₄ = true)
    (hDoubleUn : isDoubleUnaryChainProgram p₄ p₅ = true)
    (hConstDiscr : isConstAndEnumDiscrFoldProgram p₅ p₆ = true)
    (hConstDiscrCert : checkConstAndEnumDiscrFoldProgram dCert p₅ p₆ = true) :
    FullSemanticEquiv p₀ p₆ ∧
    (∀ (safety : String → List Val → Prop) (prop : Program → Prop),
      (prop p₆ ↔ prop p₀) →
      (CrateTheorem ⟨p₆, ⟨safety, prop⟩⟩ ↔ CrateTheorem ⟨p₀, ⟨safety, prop⟩⟩) ∧
      (UnitTheorem ⟨p₆, ⟨safety, prop⟩⟩ ↔ UnitTheorem ⟨p₀, ⟨safety, prop⟩⟩)) := by
  exact gvnInstSimplify_pipeline_crate_and_unit_iff_priv p₀ p₁ p₂ p₃ p₄ p₅ p₆ zCert aCert dCert hBoolCmp hNeutral hZeroDiv hZeroDivCert hAbsorb hAbsorbCert hDoubleUn hConstDiscr hConstDiscrCert

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

/-! ### Sharpness Counterexample 1: `GVN` `0_u32 / x ↦ 0_u32` Erases `DivisionByZero` UB (`gvn.rs:1516`) -/

noncomputable def progZeroDivZeroSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce::zero_div_zero"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .div
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩)
          (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progZeroDivZeroTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce::zero_div_zero"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE1 (Live `E3-6` `Miri` `-Zmir-preserve-ub` Bug):**
`0_u32 / x ↦ 0_u32` satisfies `isZeroLhsDivRemProgram`, returns `0_u32` in
`pTgt` at `x = 0`, yet faults with `FaultKind.undefined` (`DivisionByZero`) in
`pSrc` at `x = 0`, and is rejected by `checkZeroLhsDivRemProgram`! -/
theorem ce_gvn_zero_div_zero_erases_ub :
    isZeroLhsDivRemProgram progZeroDivZeroSrc progZeroDivZeroTgt = true ∧
    checkZeroLhsDivRemProgram [[some [.liveUninit, .liveInit]]]
      progZeroDivZeroSrc progZeroDivZeroTgt = false ∧
    PositiveCanaryClaim progZeroDivZeroTgt { args := [u32Val 0] } (u32Val 0) ∧
    NegativeCanaryClaim progZeroDivZeroSrc { args := [u32Val 0] }
      .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 3) rfl
  · exact negativeCanary_of_execFaults (fuel := 2) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 2: `Div(x, -1_i8) ↦ Neg(x)` Is Unsound at `INT8_MIN = -128_i8` -/

noncomputable def progDivNegOneI8Src : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [i8Ty, i8Ty]
    identity := "ce::div_neg_one_i8"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩)
          (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 255)⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progNegI8Tgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [i8Ty, i8Ty]
    identity := "ce::div_neg_one_i8"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.unaryOp .neg (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- **Sharpness Theorem CE2:** `Div(x, -1_i8)` faults `.undefined` at
`x = -128_i8` (`i8Val 128`), whereas `Neg(x)` wraps to `-128_i8`! -/
theorem ce_div_neg_one_to_neg_unsound_at_int_min :
    isNeutralIdentityProgram progDivNegOneI8Src progNegI8Tgt = false ∧
    PositiveCanaryClaim progNegI8Tgt { args := [i8Val 128] } (i8Val 128) ∧
    NegativeCanaryClaim progDivNegOneI8Src { args := [i8Val 128] }
      .undefined .unsupported := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 3) rfl
  · exact negativeCanary_of_execFaults (fuel := 2) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 3: Absorbing `Mul(copy _uninit, 0_u32) ↦ 0_u32` Erases Uninitialized Read UB -/

noncomputable def progAbsorbMulZeroUninitSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::absorb_mul_uninit"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .mul (.copy ⟨1, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progAbsorbMulZeroUninitTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    identity := "ce::absorb_mul_uninit"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }]

theorem ce_absorbing_mul_zero_uninit_unsound :
    isAbsorbingOrSelfCancelProgram
      progAbsorbMulZeroUninitSrc progAbsorbMulZeroUninitTgt = true ∧
    checkAbsorbingOrSelfCancelProgram [[some [.liveUninit, .liveUninit]]]
      progAbsorbMulZeroUninitSrc progAbsorbMulZeroUninitTgt = false ∧
    PositiveCanaryClaim progAbsorbMulZeroUninitTgt queryEmpty (u32Val 0) ∧
    NegativeCanaryClaim progAbsorbMulZeroUninitSrc queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 3) rfl
  · exact negativeCanary_of_execFaults (fuel := 2) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 4: Absorbing `Mul(move _1, 0_u32) ↦ 0_u32` Erases `deinitMovedPlace = true` Use-After-Move UB -/

noncomputable def progAbsorbMulZeroMoveSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::absorb_mul_move"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.binaryOp .mul (.move ⟨1, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progAbsorbMulZeroMoveTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    identity := "ce::absorb_mul_move"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

theorem ce_absorbing_mul_zero_move_deinit_unsound :
    isAbsorbingOrSelfCancelProgram
      progAbsorbMulZeroMoveSrc progAbsorbMulZeroMoveTgt = true ∧
    checkAbsorbingOrSelfCancelProgram
      [[some [.liveUninit, .liveInit, .liveUninit]]]
      progAbsorbMulZeroMoveSrc progAbsorbMulZeroMoveTgt = false ∧
    PositiveCanaryClaim progAbsorbMulZeroMoveTgt
      { args := [u32Val 7] } (u32Val 7) ∧
    NegativeCanaryClaim progAbsorbMulZeroMoveSrc
      { args := [u32Val 7] } .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 4) rfl
  · exact negativeCanary_of_execFaults (fuel := 3) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 5: `BitXor(move _1, move _1) ↦ 0_u32` Double-Move UB -/

noncomputable def progSelfXorDoubleMoveSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce::self_xor_double_move"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .bitXor (.move ⟨1, []⟩) (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progSelfXorDoubleMoveTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    identity := "ce::self_xor_double_move"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }]

theorem ce_self_xor_double_move_unsound :
    isAbsorbingOrSelfCancelProgram
      progSelfXorDoubleMoveSrc progSelfXorDoubleMoveTgt = false ∧
    PositiveCanaryClaim progSelfXorDoubleMoveTgt
      { args := [u32Val 42] } (u32Val 0) ∧
    NegativeCanaryClaim progSelfXorDoubleMoveSrc
      { args := [u32Val 42] } .undefined .unsupported := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 3) rfl
  · exact negativeCanary_of_execFaults (fuel := 2) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 6: `ShlUnchecked(0_u32, 32_u32) ↦ 0_u32` Shift-Overflow UB -/

noncomputable def progShlUncheckedZeroLhsSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce::shl_unchecked_zero_lhs"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .shlUnchecked
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 32)⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progShlUncheckedZeroLhsTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty]
    identity := "ce::shl_unchecked_zero_lhs"
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }]

theorem ce_shl_unchecked_zero_lhs_overflow_unsound :
    isAbsorbingOrSelfCancelProgram
      progShlUncheckedZeroLhsSrc progShlUncheckedZeroLhsTgt = false ∧
    isConstAndEnumDiscrFoldProgram
      progShlUncheckedZeroLhsSrc progShlUncheckedZeroLhsTgt = false ∧
    PositiveCanaryClaim progShlUncheckedZeroLhsTgt queryEmpty (u32Val 0) ∧
    NegativeCanaryClaim progShlUncheckedZeroLhsSrc queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 3) rfl
  · exact negativeCanary_of_execFaults (fuel := 2) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 7: Folding `Discriminant(_dead_zst_enum) ↦ const 42_isize` Erases `DeadLocal` UB -/

noncomputable def progEnumDiscrDeadZstSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.int .isize true, .enum canarySingleZstEnumTy]
    identity := "ce::enum_discr_dead_zst"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .storageDead 1,
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)
      ]
      terminator := .return_
    }]
  }]

noncomputable def progEnumDiscrDeadZstTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.int .isize true, .enum canarySingleZstEnumTy]
    identity := "ce::enum_discr_dead_zst"
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .storageDead 1,
        .assign ⟨0, []⟩ (.use (.constant
          ⟨.int .isize true, .scalar (BitVec.ofNat 128 42)⟩))
      ]
      terminator := .return_
    }]
  }]

theorem ce_enum_discr_dead_zst_unsound :
    isUncondConstAndSingleDiscrFoldProgram
      progEnumDiscrDeadZstSrc progEnumDiscrDeadZstTgt = true ∧
    isConstAndEnumDiscrFoldProgram
      progEnumDiscrDeadZstSrc progEnumDiscrDeadZstTgt = true ∧
    checkConstAndEnumDiscrFoldProgram [[some [.liveSlot, .dead]]]
      progEnumDiscrDeadZstSrc progEnumDiscrDeadZstTgt = false ∧
    PositiveCanaryClaim progEnumDiscrDeadZstTgt queryEmpty
      (scalarNatVal .isize true 42) ∧
    NegativeCanaryClaim progEnumDiscrDeadZstSrc queryEmpty
      .undefined .unsupported := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 5) rfl
  · exact negativeCanary_of_execFaults (fuel := 4) (by intro h; cases h) rfl

/-! ### Constructive Witness 1: `Neg(Neg(INT8_MIN))` Wrapping Involution on `-128_i8` -/

noncomputable def progDoubleNegI8Src : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [i8Ty, i8Ty, i8Ty]
    identity := "witness::double_neg_i8"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.unaryOp .neg (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.unaryOp .neg (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progDoubleNegI8Tgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [i8Ty, i8Ty, i8Ty]
    identity := "witness::double_neg_i8"
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.unaryOp .neg (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

theorem witness_neg_neg_int8_min_exact :
    isDoubleUnaryChainProgram progDoubleNegI8Src progDoubleNegI8Tgt = true ∧
    PositiveCanaryClaim progDoubleNegI8Src { args := [i8Val 128] } (i8Val 128) ∧
    PositiveCanaryClaim progDoubleNegI8Tgt { args := [i8Val 128] } (i8Val 128) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 4) rfl
  · exact positiveCanary_of_execReturns (fuel := 4) rfl

/-! ### Constructive Witness 2: End-to-End 6-Stage `InstSimplify` + `GVN` Pipeline Witness -/

/-- Two-variant `#[repr(i8)]` enum `enum TagI8 { Ten = 10, Forty = 40 }`. -/
noncomputable def pipeEnumI8Ty : EnumTy := {
  id := 7
  discrWidth := .i8
  discrSigned := true
  tagRepr := .scalar .i8 true
  discriminants := [10, 40]
}

/-- `pPipe₀`: exercises all 6 passes and all 3 certificates end-to-end on
`(b = true, x = -128_i8)`:
- `bb0`: `_3 = Eq(copy _1, const true)` (`BoolCmpSimplify`);
  `SwitchInt(copy _3) [1 -> bb1, otherwise -> bb3]`
- `bb1`: `SwitchInt(copy _2) [0 -> bb3, otherwise -> bb2]` (refining `_2` to
  `.liveNonZero` along `bb2`!)
- `bb2`:
  * `_4 = Div(const 0_i8, copy _2)` (`ZeroLhsDivRem` via guarded `.liveNonZero`!)
  * `_5 = BitXor(copy _2, copy _2)` (`AbsorbingOrSelfCancel` self-XOR!)
  * `_6 = Neg(copy _2); _8 = Neg(copy _6)` (`DoubleUnaryChain` at `INT8_MIN`!)
  * `_7 = const TagI8::Forty; _4 = Discriminant(_7)` (`ConstAndEnumDiscrFold`!)
  * `_5 = Add(const 1_i8, const 2_i8)` (`ConstAndEnumDiscrFold` binary fold!)
  * `_0 = Add(copy _8, const 0_i8)` (`NeutralIdentity` `+ 0`!)
  * `Return`
- `bb3`: `_0 = const 0_i8; Return` -/
noncomputable def mkPipeProg (sBoolCmp sZeroDiv sSelfXor sNeg2
    sEnumDiscr sConstAdd sNeutral : StatementKind) : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [
      i8Ty, .bool, i8Ty, .bool, i8Ty, i8Ty, i8Ty, .enum pipeEnumI8Ty, i8Ty
    ]
    identity := "witness::gvn_instsimplify_pipeline"
    basicBlocks := [
      {
        statements := [sBoolCmp]
        terminator := .switchInt (.copy ⟨3, []⟩) {
          branches := [(BitVec.ofNat 128 1, 1)]
          otherwise := 3
        }
      },
      {
        statements := []
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 3)]
          otherwise := 2
        }
      },
      {
        statements := [
          sZeroDiv,
          sSelfXor,
          .assign ⟨6, []⟩ (.unaryOp .neg (.copy ⟨2, []⟩)),
          sNeg2,
          .assign ⟨7, []⟩ (.use (.constant
            ⟨.enum pipeEnumI8Ty, .scalar (BitVec.ofNat 128 40)⟩)),
          sEnumDiscr,
          sConstAdd,
          sNeutral
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

noncomputable def sBoolCmpSrc : StatementKind :=
  .assign ⟨3, []⟩ (.binaryOp .eq (.copy ⟨1, []⟩)
    (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩))
noncomputable def sBoolCmpTgt : StatementKind :=
  .assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩))

noncomputable def sZeroDivSrc : StatementKind :=
  .assign ⟨4, []⟩ (.binaryOp .div
    (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 0)⟩) (.copy ⟨2, []⟩))
noncomputable def sZeroDivTgt : StatementKind :=
  .assign ⟨4, []⟩ (.use (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 0)⟩))

noncomputable def sSelfXorSrc : StatementKind :=
  .assign ⟨5, []⟩ (.binaryOp .bitXor (.copy ⟨2, []⟩) (.copy ⟨2, []⟩))
noncomputable def sSelfXorTgt : StatementKind :=
  .assign ⟨5, []⟩ (.use (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 0)⟩))

noncomputable def sNeg2Src : StatementKind :=
  .assign ⟨8, []⟩ (.unaryOp .neg (.copy ⟨6, []⟩))
noncomputable def sNeg2Tgt : StatementKind :=
  .assign ⟨8, []⟩ (.use (.copy ⟨2, []⟩))

noncomputable def sEnumDiscrSrc : StatementKind :=
  .assign ⟨4, []⟩ (.discriminant ⟨7, []⟩)
noncomputable def sEnumDiscrTgt : StatementKind :=
  .assign ⟨4, []⟩ (.use (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 40)⟩))

noncomputable def sConstAddSrc : StatementKind :=
  .assign ⟨5, []⟩ (.binaryOp .add
    (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 1)⟩)
    (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 2)⟩))
noncomputable def sConstAddTgt : StatementKind :=
  .assign ⟨5, []⟩ (.use (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 3)⟩))

noncomputable def sNeutralSrc : StatementKind :=
  .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨8, []⟩)
    (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 0)⟩))
noncomputable def sNeutralTgt : StatementKind :=
  .assign ⟨0, []⟩ (.use (.copy ⟨8, []⟩))

noncomputable def pPipe₀ : Program :=
  mkPipeProg sBoolCmpSrc sZeroDivSrc sSelfXorSrc sNeg2Src
    sEnumDiscrSrc sConstAddSrc sNeutralSrc

noncomputable def pPipe₁ : Program :=
  mkPipeProg sBoolCmpTgt sZeroDivSrc sSelfXorSrc sNeg2Src
    sEnumDiscrSrc sConstAddSrc sNeutralSrc

noncomputable def pPipe₂ : Program :=
  mkPipeProg sBoolCmpTgt sZeroDivSrc sSelfXorSrc sNeg2Src
    sEnumDiscrSrc sConstAddSrc sNeutralTgt

noncomputable def pPipe₃ : Program :=
  mkPipeProg sBoolCmpTgt sZeroDivTgt sSelfXorSrc sNeg2Src
    sEnumDiscrSrc sConstAddSrc sNeutralTgt

noncomputable def pPipe₄ : Program :=
  mkPipeProg sBoolCmpTgt sZeroDivTgt sSelfXorTgt sNeg2Src
    sEnumDiscrSrc sConstAddSrc sNeutralTgt

noncomputable def pPipe₅ : Program :=
  mkPipeProg sBoolCmpTgt sZeroDivTgt sSelfXorTgt sNeg2Tgt
    sEnumDiscrSrc sConstAddSrc sNeutralTgt

noncomputable def pPipe₆ : Program :=
  mkPipeProg sBoolCmpTgt sZeroDivTgt sSelfXorTgt sNeg2Tgt
    sEnumDiscrTgt sConstAddTgt sNeutralTgt

noncomputable def pipeZeroDivCert : ProgramNonZeroCert := [[
  some [
    .liveUninit, .liveInit, .liveInit, .liveUninit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ],
  some [
    .liveUninit, .liveInit, .liveInit, .liveInit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ],
  some [
    .liveUninit, .liveInit, .liveNonZero, .liveInit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ],
  some [
    .liveUninit, .liveInit, .liveInit, .liveInit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ]
]]

noncomputable def pipeAbsorbCert : ProgramAbsCert := [[
  some [
    .liveUninit, .liveInit, .liveInit, .liveUninit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ],
  some [
    .liveUninit, .liveInit, .liveInit, .liveInit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ],
  some [
    .liveUninit, .liveInit, .liveInit, .liveInit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ],
  some [
    .liveUninit, .liveInit, .liveInit, .liveInit,
    .liveUninit, .liveUninit, .liveUninit, .liveUninit, .liveUninit
  ]
]]

noncomputable def pipeDiscrCert : ProgramDiscrCert := [[
  some [
    .liveSlot, .liveSlot, .liveSlot, .liveSlot,
    .liveSlot, .liveSlot, .liveSlot, .liveSlot, .liveSlot
  ],
  some [
    .liveSlot, .liveSlot, .liveSlot, .liveSlot,
    .liveSlot, .liveSlot, .liveSlot, .liveSlot, .liveSlot
  ],
  some [
    .liveSlot, .liveSlot, .liveSlot, .liveSlot,
    .liveSlot, .liveSlot, .liveSlot, .liveSlot, .liveSlot
  ],
  some [
    .liveSlot, .liveSlot, .liveSlot, .liveSlot,
    .liveSlot, .liveSlot, .liveSlot, .liveSlot, .liveSlot
  ]
]]

theorem witness_full_gvnInstSimplify_pipeline_nonvacuous :
    isBoolCmpSimplifyProgram pPipe₀ pPipe₁ = true ∧
    isNeutralIdentityProgram pPipe₁ pPipe₂ = true ∧
    isZeroLhsDivRemProgram pPipe₂ pPipe₃ = true ∧
    checkZeroLhsDivRemProgram pipeZeroDivCert pPipe₂ pPipe₃ = true ∧
    isAbsorbingOrSelfCancelProgram pPipe₃ pPipe₄ = true ∧
    checkAbsorbingOrSelfCancelProgram pipeAbsorbCert pPipe₃ pPipe₄ = true ∧
    isDoubleUnaryChainProgram pPipe₄ pPipe₅ = true ∧
    isConstAndEnumDiscrFoldProgram pPipe₅ pPipe₆ = true ∧
    checkConstAndEnumDiscrFoldProgram pipeDiscrCert pPipe₅ pPipe₆ = true ∧
    PositiveCanaryClaim pPipe₀ { args := [.bool true, i8Val 128] } (i8Val 128) ∧
    PositiveCanaryClaim pPipe₆ { args := [.bool true, i8Val 128] } (i8Val 128) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact positiveCanary_of_execReturns (fuel := 14) rfl
  · exact positiveCanary_of_execReturns (fuel := 14) rfl

end VrustcFormal.F1_6
