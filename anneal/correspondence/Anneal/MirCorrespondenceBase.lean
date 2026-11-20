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
import Trusted
import Trusted.Correspondence
import Anneal.MirWp

namespace Anneal.MirCorrespondenceBase

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# MIR Correspondence Codec and Bridge Lemmas (`Anneal.MirCorrespondenceBase`)

This module proves the foundational codec, simulation-uniqueness, and
`vendor/lean-miri` scalar/enum bridge lemmas consumed by
`Anneal.MirCorrespondenceProof`:

1. **Unconditional codec round-trip (`decodeProg_encodeProg_base`), canonical
   type deduplication (`encodeProg_types_canonical_base`), and constructor
   preservation:** Every `p : Program` (including `pointerWidthBits`,
   `mirProfileVersion`, and `scope`) round-trips through `encodeProg` and
   `decodeProg` with zero preconditions via generic `List.foldl` / `mapOption`
   traversal lemmas; `encodeStmt_no_dormant_noops_base` guarantees that
   `encodeStmt` maps `.nop` and only `.nop` to `.nop`; and
   `encodeRvalue_binaryOp_iff_base`, `encodeRvalue_unaryOp_iff_base`, and
   `encodeStmt_assign_iff_base` prevent operator or assignment permutation.
2. **One-to-one simulation uniqueness (`state_unique_of_simulationInv_base`,
   `refState_unique_of_simulationInv_base`):** Proves 1-to-1 uniqueness of
   `SimulationInv` between $M_{\text{anneal}}$ (`State`) and $M_{\text{ref}}$
   (`RefState`) up to `(stepsExecuted, maxSteps)`.
3. **`vendor/lean-miri` arithmetic, cast, constant, enum, and `SwitchInt`
   equivalence (`evalRefUnOp_eq`, `evalRefBinOp_eq`,
   `evalRefMiriIntToIntCast_eq`, `evalRefConstLit_eq`, `checkRefVal_eq`,
   `readDiscriminant_enum_scalar_eq`, `evalRefSwitchScalarCase_eq`):** Bridges
   `Miri.Memory.ScalarInt`, `Miri.ABI.Size`, `Miri.Interpreter.IntegerOps`,
   `Miri.Interpreter.IntegerCast`, and `Miri.Interpreter.Discriminant` to
   `Trusted.MirSemantics`.
4. **Tuple field projection equivalence (`refProjectTy?_eq`,
   `refReadSlotPath?_eq`, `refWriteSlotPath?_eq`):** The reference machine's
   field projections over a translated `Miri.MIR` projection agree with
   `projectTy?`, `readSlotPath?`, and `writeSlotPath?` over the decoded
   projection.

Per-step simulation (`evalRefStep_eq`), end-to-end correspondence
(`anneal_corresponds_to_miri`, `reachesResult_fault_iff_refReachesOutcome`,
`miri_move_deinit_wiring_claim_holds`), and non-vacuity canaries (`D6`–`D24`)
are proved in `Anneal.MirCorrespondenceProof`.
-/

theorem Bool.false_eq_true : (false = true) = False :=
  propext ⟨fun h => Bool.noConfusion h, False.elim⟩

theorem Nat.add_right_cancel_iff {n m k : Nat} : (n + k = m + k) ↔ (n = m) :=
  ⟨Nat.add_right_cancel, fun h => h ▸ rfl⟩

theorem IntWidth.beq_refl (w : IntWidth) : IntWidth.beq w w = true := by
  cases w <;> rfl

theorem IntWidth.eq_of_beq {w₁ w₂ : IntWidth}
    (h : IntWidth.beq w₁ w₂ = true) : w₁ = w₂ := by
  cases w₁ <;> cases w₂ <;> first | rfl | cases h

theorem Mutability.beq_refl (m : Mutability) : Mutability.beq m m = true := by
  cases m <;> rfl

theorem Mutability.eq_of_beq {m₁ m₂ : Mutability}
    (h : Mutability.beq m₁ m₂ = true) : m₁ = m₂ := by
  cases m₁ <;> cases m₂ <;> first | rfl | cases h

theorem natListBeq_refl (xs : List Nat) : natListBeq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    change (Nat.beq x x && natListBeq rest rest) = true
    rw [Nat.beq_refl, ih]
    rfl

theorem eq_of_natListBeq {xs ys : List Nat}
    (h : natListBeq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | rfl | cases h
  | cons x xs' ih =>
    cases ys with
    | nil => cases h
    | cons y ys' =>
      change (Nat.beq x y && natListBeq xs' ys') = true at h
      cases h_x : Nat.beq x y <;> rw [h_x] at h
      · cases h
      · rw [Nat.eq_of_beq_eq_true h_x, ih h]

theorem EnumTagRepr.beq_refl (r : EnumTagRepr) :
    EnumTagRepr.beq r r = true := by
  cases r with
  | zeroSized => rfl
  | scalar w s =>
    change (IntWidth.beq w w && (s == s)) = true
    rw [IntWidth.beq_refl]
    cases s <;> rfl

theorem EnumTagRepr.eq_of_beq {r₁ r₂ : EnumTagRepr}
    (h : EnumTagRepr.beq r₁ r₂ = true) : r₁ = r₂ := by
  cases r₁ with
  | zeroSized => cases r₂ <;> first | rfl | cases h
  | scalar w₁ s₁ =>
    cases r₂ with
    | scalar w₂ s₂ =>
      change (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true at h
      cases h_w : IntWidth.beq w₁ w₂ <;> rw [h_w] at h
      · cases h
      · rw [IntWidth.eq_of_beq h_w]
        cases s₁ <;> cases s₂ <;> first | rfl | cases h
    | zeroSized => cases h

theorem EnumTy.beq_refl (e : EnumTy) : EnumTy.beq e e = true := by
  cases e with
  | mk id dw ds tr discrs =>
    change ((((Nat.beq id id && IntWidth.beq dw dw) && (ds == ds)) &&
        EnumTagRepr.beq tr tr) && natListBeq discrs discrs) = true
    rw [Nat.beq_refl, IntWidth.beq_refl, EnumTagRepr.beq_refl, natListBeq_refl]
    cases ds <;> rfl

theorem EnumTy.eq_of_beq {a b : EnumTy}
    (h : EnumTy.beq a b = true) : a = b := by
  cases a with
  | mk id₁ dw₁ ds₁ tr₁ discrs₁ =>
    cases b with
    | mk id₂ dw₂ ds₂ tr₂ discrs₂ =>
      change ((((Nat.beq id₁ id₂ && IntWidth.beq dw₁ dw₂) && (ds₁ == ds₂)) &&
          EnumTagRepr.beq tr₁ tr₂) && natListBeq discrs₁ discrs₂) = true at h
      cases h1 : Nat.beq id₁ id₂ <;> rw [h1] at h
      · cases h
      · cases h2 : IntWidth.beq dw₁ dw₂ <;> rw [h2] at h
        · cases h
        · cases h3 : (ds₁ == ds₂) <;> rw [h3] at h
          · cases h
          · cases h4 : EnumTagRepr.beq tr₁ tr₂ <;> rw [h4] at h
            · cases h
            · have h_ds : ds₁ = ds₂ := by
                cases ds₁ <;> cases ds₂ <;> first | rfl | cases h3
              rw [Nat.eq_of_beq_eq_true h1, IntWidth.eq_of_beq h2, h_ds,
                EnumTagRepr.eq_of_beq h4, eq_of_natListBeq h]

mutual
  theorem MirTy.beq_refl (t : MirTy) : MirTy.beq t t = true := by
    cases t with
    | bool => rfl
    | int w s =>
      change (IntWidth.beq w w && (s == s)) = true
      rw [IntWidth.beq_refl]
      cases s <;> rfl
    | unit => rfl
    | never => rfl
    | enum ety => exact EnumTy.beq_refl ety
    | tuple fs =>
      change MirTy.beqList fs fs = true
      exact MirTy.beqList_refl fs
    | ref m p =>
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [Mutability.beq_refl, MirTy.beq_refl p]
      rfl
    | rawPtr m p =>
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [Mutability.beq_refl, MirTy.beq_refl p]
      rfl
    | unsupported => rfl

  theorem MirTy.beqList_refl
      (ts : List MirTy) : MirTy.beqList ts ts = true := by
    cases ts with
    | nil => rfl
    | cons t rest =>
      change (MirTy.beq t t && MirTy.beqList rest rest) = true
      rw [MirTy.beq_refl t, MirTy.beqList_refl rest]
      rfl
end

mutual
  theorem MirTy.eq_of_beq {a b : MirTy} (h : MirTy.beq a b = true) : a = b := by
    cases a with
    | bool => cases b <;> first | rfl | cases h
    | int w₁ s₁ =>
      cases b with
      | int w₂ s₂ =>
        change (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true at h
        cases h_w : IntWidth.beq w₁ w₂ <;> rw [h_w] at h
        · cases h
        · rw [IntWidth.eq_of_beq h_w]
          cases s₁ <;> cases s₂ <;> first | rfl | cases h
      | _ => cases h
    | unit => cases b <;> first | rfl | cases h
    | never => cases b <;> first | rfl | cases h
    | enum ety₁ =>
      cases b with
      | enum ety₂ =>
        change EnumTy.beq ety₁ ety₂ = true at h
        rw [EnumTy.eq_of_beq h]
      | _ => cases h
    | tuple fs₁ =>
      cases b with
      | tuple fs₂ =>
        change MirTy.beqList fs₁ fs₂ = true at h
        rw [MirTy.eq_of_beqList h]
      | _ => cases h
    | ref m₁ p₁ =>
      cases b with
      | ref m₂ p₂ =>
        change (Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂) = true at h
        cases h_m : Mutability.beq m₁ m₂ <;> rw [h_m] at h
        · cases h
        · rw [Mutability.eq_of_beq h_m, MirTy.eq_of_beq h]
      | _ => cases h
    | rawPtr m₁ p₁ =>
      cases b with
      | rawPtr m₂ p₂ =>
        change (Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂) = true at h
        cases h_m : Mutability.beq m₁ m₂ <;> rw [h_m] at h
        · cases h
        · rw [Mutability.eq_of_beq h_m, MirTy.eq_of_beq h]
      | _ => cases h
    | unsupported => cases b <;> first | rfl | cases h

  theorem MirTy.eq_of_beqList {xs ys : List MirTy}
      (h : MirTy.beqList xs ys = true) : xs = ys := by
    cases xs with
    | nil => cases ys <;> first | rfl | cases h
    | cons x xs' =>
      cases ys with
      | nil => cases h
      | cons y ys' =>
        change (MirTy.beq x y && MirTy.beqList xs' ys') = true at h
        cases h_x : MirTy.beq x y <;> rw [h_x] at h
        · cases h
        · rw [MirTy.eq_of_beq h_x, MirTy.eq_of_beqList h]
end

theorem MirTy.beq_eq_false_of_ne {a b : MirTy}
    (h : a ≠ b) : MirTy.beq a b = false := by
  cases h_b : MirTy.beq a b with
  | false => rfl
  | true => exact False.elim (h (MirTy.eq_of_beq h_b))

theorem MirTy.ne_of_beq_eq_false {a b : MirTy}
    (h : MirTy.beq a b = false) : a ≠ b := by
  intro h_eq
  subst h_eq
  rw [MirTy.beq_refl] at h
  cases h


theorem indexOfTy_insertTy_none {t ty : MirTy} {ts : List MirTy}
    (h_ne : t ≠ ty) (h_none : indexOfTy ts t = none) :
    indexOfTy (insertTy ty ts) t = none := by
  induction ts with
  | nil =>
    dsimp only [insertTy, indexOfTy]
    have h_dec : MirTy.beq ty t = false :=
      MirTy.beq_eq_false_of_ne (fun h => h_ne h.symm)
    rw [h_dec]
    rfl
  | cons a rest ih =>
    dsimp only [indexOfTy] at h_none
    cases h_at : MirTy.beq a t with
    | true => rw [h_at] at h_none; cases h_none
    | false =>
      rw [h_at] at h_none
      cases h_rest : indexOfTy rest t with
      | some _ => rw [h_rest] at h_none; cases h_none
      | none =>
        dsimp only [insertTy]
        cases h_ay : MirTy.beq a ty with
        | true =>
          change indexOfTy (a :: rest) t = none
          dsimp only [indexOfTy]
          rw [h_at, h_rest]
          rfl
        | false =>
          change indexOfTy (a :: insertTy ty rest) t = none
          dsimp only [indexOfTy]
          rw [h_at, ih h_rest]
          rfl

theorem typesAreCanonical_insertTy (ty : MirTy) (ts : List MirTy)
    (h_can : typesAreCanonical ts = true) :
    typesAreCanonical (insertTy ty ts) = true := by
  induction ts with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [typesAreCanonical] at h_can
    cases h_none : indexOfTy rest a with
    | some _ => rw [h_none] at h_can; cases h_can
    | none =>
      rw [h_none] at h_can
      simp only [Option.isNone, Bool.true_and] at h_can
      dsimp only [insertTy]
      cases h_ay : MirTy.beq a ty with
      | true =>
        change typesAreCanonical (a :: rest) = true
        dsimp only [typesAreCanonical]
        rw [h_none]
        exact h_can
      | false =>
        have h_ne : a ≠ ty := MirTy.ne_of_beq_eq_false h_ay
        change typesAreCanonical (a :: insertTy ty rest) = true
        dsimp only [typesAreCanonical]
        rw [indexOfTy_insertTy_none h_ne h_none]
        exact ih h_can


/-- Componentwise structural homomorphism laws for `encodeBody` and
`encodeBasicBlock`. -/
theorem encodeBody_basicBlocks_eq (ts : List MirTy) (b : Body) :
    (encodeBody ts b).basicBlocks =
      b.basicBlocks.map (encodeBasicBlock ts) := rfl

theorem encodeBasicBlock_statements_eq (ts : List MirTy) (bb : BasicBlock) :
    (encodeBasicBlock ts bb).statements =
      bb.statements.map (encodeStmt ts) := rfl

/-- Anti-laundering guarantee: `encodeStmt` maps `.nop` and only `.nop` to
`.nop`. -/
theorem encodeStmt_no_dormant_noops_base : EncodeStmtNoDormantNoopsClaim := by
  intro ts s
  cases s <;> constructor <;> intro h <;> first | rfl | cases h

/-! ### Constructor preservation

`decodeProg_encodeProg` alone would still allow an encoder that permutes
semantic constructors (for example, `.add` ↔ `.addUnchecked`) as long as the
decoder permutes them back. The following lemmas lock the operator, operands,
and destination of every encoded assignment, binary operation, and unary
operation to the source constructor. -/

/-- `encodeRvalue` produces `.binaryOp op l' r'` exactly when the source is a
`.binaryOp` with the same operator `op` and operands encoding to `l'` and
`r'`. -/
theorem encodeRvalue_binaryOp_iff_base : EncodeRvalueBinaryOpIffClaim := by
  intro ts rv op l' r'
  cases rv with
  | binaryOp op₀ l r =>
    constructor
    · intro h
      injection h with h_op h_l h_r
      subst h_op
      exact ⟨l, r, rfl, h_l, h_r⟩
    · intro h
      let ⟨l₁, r₁, h_rv, h_l, h_r⟩ := h
      injection h_rv with h_op h_l₁ h_r₁
      subst h_op; subst h_l₁; subst h_r₁
      dsimp only [encodeRvalue]
      rw [h_l, h_r]
  | use _ | unaryOp _ _ | discriminant _ | ref _ _ | addressOf _ _
  | aggregateTuple _ | cast _ _ _ | unsupported =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, _, h_rv, _, _⟩ := h
      cases h_rv

/-- `encodeRvalue` produces `.unaryOp op o'` exactly when the source is a
`.unaryOp` with the same operator `op` and an operand encoding to `o'`. -/
theorem encodeRvalue_unaryOp_iff_base : EncodeRvalueUnaryOpIffClaim := by
  intro ts rv op o'
  cases rv with
  | unaryOp op₀ o =>
    constructor
    · intro h
      injection h with h_op h_o
      subst h_op
      exact ⟨o, rfl, h_o⟩
    · intro h
      let ⟨o₁, h_rv, h_o⟩ := h
      injection h_rv with h_op h_o₁
      subst h_op; subst h_o₁
      dsimp only [encodeRvalue]
      rw [h_o]
  | use _ | binaryOp _ _ _ | discriminant _ | ref _ _ | addressOf _ _
  | aggregateTuple _ | cast _ _ _ | unsupported =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, h_rv, _⟩ := h
      cases h_rv

/-- `encodeStmt` produces `.assign dst' rv'` exactly when the source is an
`.assign` whose destination and rvalue encode to `dst'` and `rv'`. -/
theorem encodeStmt_assign_iff_base : EncodeStmtAssignIffClaim := by
  intro ts s dst' rv'
  cases s with
  | assign dst rv =>
    constructor
    · intro h
      injection h with h_dst h_rv
      exact ⟨dst, rv, rfl, h_dst, h_rv⟩
    · intro h
      let ⟨dst₁, rv₁, h_s, h_dst, h_rv⟩ := h
      injection h_s with h_dst₁ h_rv₁
      subst h_dst₁; subst h_rv₁
      dsimp only [encodeStmt]
      rw [h_dst, h_rv]
  | storageLive _ | storageDead _ | nop | unsupported =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, _, h_s, _, _⟩ := h
      cases h_s



abbrev SubTable (xs ys : List MirTy) : Prop :=
  ∀ t : MirTy, (∃ i, indexOfTy xs t = some i) → (∃ j, indexOfTy ys t = some j)

theorem SubTable.refl (xs : List MirTy) : SubTable xs xs :=
  fun _ h => h

theorem SubTable.trans {xs ys zs : List MirTy}
    (h₁ : SubTable xs ys) (h₂ : SubTable ys zs) : SubTable xs zs :=
  fun t ht => h₂ t (h₁ t ht)

theorem getElem?_of_indexOfTy {ts : List MirTy} {ty : MirTy} {i : TyId}
    (h : indexOfTy ts ty = some i) :
    MirSemantics.getElem? ts i = some ty := by
  induction ts generalizing i with
  | nil => cases h
  | cons t rest ih =>
    dsimp only [indexOfTy] at h
    cases h_eq : MirTy.beq t ty with
    | true =>
      rw [h_eq] at h
      injection h with h_zero
      subst h_zero
      have h_t : t = ty := MirTy.eq_of_beq h_eq
      subst h_t
      rfl
    | false =>
      rw [h_eq] at h
      cases h_idx : indexOfTy rest ty with
      | none => rw [h_idx] at h; cases h
      | some j =>
        rw [h_idx] at h
        injection h with h_succ
        subst h_succ
        exact ih h_idx

theorem indexOfTy_some_of_getElem? {ts : List MirTy} {i : TyId} {ty : MirTy}
    (h : MirSemantics.getElem? ts i = some ty) :
    ∃ tid, indexOfTy ts ty = some tid := by
  induction ts generalizing i with
  | nil => cases h
  | cons t rest ih =>
    cases h_eq : MirTy.beq t ty with
    | true =>
      refine ⟨0, ?_⟩
      dsimp only [indexOfTy]
      rw [h_eq]
      rfl
    | false =>
      cases i with
      | zero =>
        injection h with h_t
        subst h_t
        rw [MirTy.beq_refl] at h_eq
        cases h_eq
      | succ j =>
        let ⟨k, hk⟩ := ih h
        refine ⟨k + 1, ?_⟩
        dsimp only [indexOfTy]
        rw [h_eq, hk]
        rfl

theorem indexOfTy_insertTy_self (ty : MirTy) (ts : List MirTy) :
    ∃ i, indexOfTy (insertTy ty ts) ty = some i := by
  induction ts with
  | nil =>
    refine ⟨0, ?_⟩
    dsimp only [insertTy, indexOfTy]
    rw [MirTy.beq_refl]
    rfl
  | cons t rest ih =>
    cases h_eq : MirTy.beq t ty with
    | true =>
      refine ⟨0, ?_⟩
      dsimp only [insertTy]
      rw [h_eq]
      change indexOfTy (t :: rest) ty = some 0
      dsimp only [indexOfTy]
      rw [h_eq]
      rfl
    | false =>
      let ⟨j, hj⟩ := ih
      refine ⟨j + 1, ?_⟩
      dsimp only [insertTy]
      rw [h_eq]
      change indexOfTy (t :: insertTy ty rest) ty = some (j + 1)
      dsimp only [indexOfTy]
      rw [h_eq, hj]
      rfl

theorem subTable_insertTy (ty : MirTy) (acc : List MirTy) :
    SubTable acc (insertTy ty acc) := by
  intro t ⟨i, hi⟩
  induction acc generalizing i with
  | nil => cases hi
  | cons a rest ih =>
    cases h_ay : MirTy.beq a ty with
    | true =>
      dsimp only [insertTy]; rw [h_ay]; exact ⟨i, hi⟩
    | false =>
      dsimp only [indexOfTy] at hi
      cases h_at : MirTy.beq a t with
      | true =>
        refine ⟨0, ?_⟩
        dsimp only [insertTy]
        rw [h_ay]
        change indexOfTy (a :: insertTy ty rest) t = some 0
        dsimp only [indexOfTy]
        rw [h_at]
        rfl
      | false =>
        rw [h_at] at hi
        cases h_rest : indexOfTy rest t with
        | none => rw [h_rest] at hi; cases hi
        | some j =>
          let ⟨k, hk⟩ := ih j h_rest
          refine ⟨k + 1, ?_⟩
          dsimp only [insertTy]
          rw [h_ay]
          change indexOfTy (a :: insertTy ty rest) t = some (k + 1)
          dsimp only [indexOfTy]
          rw [h_at, hk]
          rfl

theorem getElem?_lookupTyId_of_subTable {ty : MirTy} {acc ts : List MirTy}
    (h_sub : SubTable (insertTy ty acc) ts) :
    MirSemantics.getElem? ts (lookupTyId ts ty) = some ty := by
  let ⟨j, hj⟩ := h_sub ty (indexOfTy_insertTy_self ty acc)
  unfold lookupTyId
  rw [hj]
  exact getElem?_of_indexOfTy hj

mutual
  theorem collectTy_spec (acc : List MirTy) (ty : MirTy) :
      SubTable acc (collectTy acc ty) ∧
      (∀ ts, SubTable (collectTy acc ty) ts →
        MirSemantics.getElem? ts (lookupTyId ts ty) = some ty) := by
    cases ty with
    | bool =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .bool acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | int w s =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy (.int w s) acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | unit =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .unit acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | never =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .never acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | enum ety =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy (.enum ety) acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | unsupported =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .unsupported acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | ref m p =>
      dsimp only [collectTy]
      let ⟨h_sub_p, _⟩ := collectTy_spec acc p
      exact ⟨SubTable.trans h_sub_p
          (subTable_insertTy (.ref m p) (collectTy acc p)),
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | rawPtr m p =>
      dsimp only [collectTy]
      let ⟨h_sub_p, _⟩ := collectTy_spec acc p
      exact ⟨SubTable.trans h_sub_p
          (subTable_insertTy (.rawPtr m p) (collectTy acc p)),
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | tuple fs =>
      dsimp only [collectTy]
      let ⟨h_sub_fs, _⟩ := collectTyList_spec acc fs
      exact ⟨SubTable.trans h_sub_fs
          (subTable_insertTy (.tuple fs) (collectTyList acc fs)),
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩

  theorem collectTyList_spec (acc : List MirTy) (tys : List MirTy) :
      SubTable acc (collectTyList acc tys) ∧
      (∀ ts, SubTable (collectTyList acc tys) ts →
        decodeLocalTys ts (tys.map (lookupTyId ts)) = some tys) := by
    cases tys with
    | nil =>
      dsimp only [collectTyList]
      exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
    | cons ty rest =>
      dsimp only [collectTyList]
      let ⟨h_sub₁, h_dec₁⟩ := collectTy_spec acc ty
      let ⟨h_sub₂, h_dec₂⟩ := collectTyList_spec (collectTy acc ty) rest
      refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
      change optMap2 List.cons
        (MirSemantics.getElem? ts (lookupTyId ts ty))
        (decodeLocalTys ts (List.map (lookupTyId ts) rest)) = some (ty :: rest)
      rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
      rfl
end

/-- Generic round-trip lemma for `List.foldl` type collection paired with
`List.map` encoding and `mapOption` decoding. -/
theorem foldl_collect_mapOption_spec {α β : Type}
    (collect : List MirTy → α → List MirTy)
    (enc : List MirTy → α → β)
    (dec : List MirTy → β → Option α)
    (h_elem : ∀ acc x, SubTable acc (collect acc x) ∧
      ∀ ts, SubTable (collect acc x) ts → dec ts (enc ts x) = some x)
    (acc : List MirTy) (xs : List α) :
    SubTable acc (xs.foldl collect acc) ∧
    (∀ ts, SubTable (xs.foldl collect acc) ts →
      mapOption (dec ts) (xs.map (enc ts)) = some xs) := by
  induction xs generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons x rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := h_elem acc x
    let ⟨h_sub₂, h_dec₂⟩ := ih (collect acc x)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_sub => ?_⟩
    dsimp only [List.map, mapOption]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_sub), h_dec₂ ts h_sub]
    rfl

/-- Generic invariant-preservation lemma for `List.foldl`. -/
theorem foldl_preserve {α σ : Type} (P : σ → Prop) (step : σ → α → σ)
    (h_step : ∀ s x, P s → P (step s x)) :
    ∀ (xs : List α) {s : σ}, P s → P (xs.foldl step s)
  | [], _, hs => hs
  | x :: rest, s, hs => foldl_preserve P step h_step rest (h_step s x hs)

theorem mapOption_length {α β : Type} {f : α → Option β} {xs : List α}
    {ys : List β} (h : mapOption f xs = some ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons x rest ih =>
    dsimp only [mapOption] at h
    cases h₁ : f x with
    | none => rw [h₁] at h; cases h
    | some y =>
      cases h₂ : mapOption f rest with
      | none => rw [h₁, h₂] at h; cases h
      | some ys' =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        simp only [List.length_cons, ih h₂]

theorem mapOption_isEmpty {α β : Type} {f : α → Option β} {xs : List α}
    {ys : List β} (h : mapOption f xs = some ys) :
    xs.isEmpty = ys.isEmpty := by
  cases xs with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons x rest =>
    dsimp only [mapOption] at h
    cases h₁ : f x <;> cases h₂ : mapOption f rest <;>
      rw [h₁, h₂] at h <;> cases h
    rfl

theorem mapOption_getElem? {α β : Type} {f : α → Option β} {xs : List α}
    {ys : List β} (h : mapOption f xs = some ys) (i : Nat) :
    (MirSemantics.getElem? ys i = none → MirSemantics.getElem? xs i = none) ∧
    (∀ y, MirSemantics.getElem? ys i = some y →
      ∃ x, MirSemantics.getElem? xs i = some x ∧ f x = some y) := by
  induction xs generalizing ys i with
  | nil =>
    injection h with h_eq
    subst h_eq
    refine ⟨fun _ => rfl, ?_⟩
    intro _ hy
    cases hy
  | cons x rest ih =>
    dsimp only [mapOption] at h
    cases h₁ : f x with
    | none => rw [h₁] at h; cases h
    | some y₀ =>
      cases h₂ : mapOption f rest with
      | none => rw [h₁, h₂] at h; cases h
      | some ys₀ =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        cases i with
        | zero =>
          refine ⟨?_, ?_⟩
          · intro hy; cases hy
          · intro y hy
            injection hy with h_eq
            subst h_eq
            exact ⟨x, rfl, h₁⟩
        | succ j => exact ih h₂ j

theorem mapOption_any_eq {α β : Type} {f : α → Option β} {pa : α → Bool}
    {pb : β → Bool} (h_pred : ∀ x y, f x = some y → pa x = pb y)
    {xs : List α} {ys : List β} (h : mapOption f xs = some ys) :
    xs.any pa = ys.any pb := by
  induction xs generalizing ys with
  | nil => injection h with h_eq; subst h_eq; rfl
  | cons x rest ih =>
    dsimp only [mapOption] at h
    cases h₁ : f x with
    | none => rw [h₁] at h; cases h
    | some y =>
      cases h₂ : mapOption f rest with
      | none => rw [h₁, h₂] at h; cases h
      | some ys' =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        simp only [List.any_cons, h_pred x y h₁, ih h₂]

theorem mapOption_all_eq {α β : Type} {f : α → Option β} {pa : α → Bool}
    {pb : β → Bool} (h_pred : ∀ x y, f x = some y → pa x = pb y)
    {xs : List α} {ys : List β} (h : mapOption f xs = some ys) :
    xs.all pa = ys.all pb := by
  induction xs generalizing ys with
  | nil => injection h with h_eq; subst h_eq; rfl
  | cons x rest ih =>
    dsimp only [mapOption] at h
    cases h₁ : f x with
    | none => rw [h₁] at h; cases h
    | some y =>
      cases h₂ : mapOption f rest with
      | none => rw [h₁, h₂] at h; cases h
      | some ys' =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        simp only [List.all_cons, h_pred x y h₁, ih h₂]

theorem collectProjElem_spec (acc : List MirTy) (e : ProjectionElem) :
    SubTable acc (collectProjElem acc e) ∧
    (∀ ts, SubTable (collectProjElem acc e) ts →
      decodeProjElem ts (encodeProjElem ts e) = some e) := by
  cases e with
  | deref => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | unsupported => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | field idx ty =>
    let ⟨h_sub₁, h_dec₁⟩ := collectTy_spec acc ty
    refine ⟨h_sub₁, fun ts h_sub => ?_⟩
    dsimp only [encodeProjElem, decodeProjElem]
    rw [h_dec₁ ts h_sub]
    rfl

theorem collectPlace_spec (acc : List MirTy) (p : Place) :
    SubTable acc (collectPlace acc p) ∧
    (∀ ts, SubTable (collectPlace acc p) ts →
      decodePlace ts (encodePlace ts p) = some p) := by
  cases p with
  | mk localId proj =>
    let ⟨h_sub, h_dec⟩ := foldl_collect_mapOption_spec collectProjElem
      encodeProjElem decodeProjElem collectProjElem_spec acc proj
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodePlace, decodePlace]
    rw [h_dec ts h_s]
    rfl

theorem collectOperand_spec (acc : List MirTy) (op : Operand) :
    SubTable acc (collectOperand acc op) ∧
    (∀ ts, SubTable (collectOperand acc op) ts →
      decodeOperand ts (encodeOperand ts op) = some op) := by
  cases op with
  | copy p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeOperand, decodeOperand]
    rw [h_dec ts h_s]
    rfl
  | move p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeOperand, decodeOperand]
    rw [h_dec ts h_s]
    rfl
  | constant c =>
    cases c with
    | mk ty lit =>
      let ⟨h_sub₁, h_dec₁⟩ := collectTy_spec acc ty
      refine ⟨h_sub₁, fun ts h_s => ?_⟩
      dsimp only [encodeOperand, decodeOperand]
      rw [h_dec₁ ts h_s]
      rfl

theorem collectRvalue_spec (acc : List MirTy) (rv : Rvalue) :
    SubTable acc (collectRvalue acc rv) ∧
    (∀ ts, SubTable (collectRvalue acc rv) ts →
      decodeRvalue ts (encodeRvalue ts rv) = some rv) := by
  cases rv with
  | use op =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc op
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
    rfl
  | binaryOp op l r =>
    let ⟨h_sub₁, h_dec₁⟩ := collectOperand_spec acc l
    let ⟨h_sub₂, h_dec₂⟩ := collectOperand_spec (collectOperand acc l) r
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl
  | unaryOp op opnd =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc opnd
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
    rfl
  | discriminant p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
    rfl
  | ref m p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
    rfl
  | addressOf m p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
    rfl
  | aggregateTuple ops =>
    let ⟨h_sub, h_dec⟩ := foldl_collect_mapOption_spec collectOperand
      encodeOperand decodeOperand collectOperand_spec acc ops
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
    rfl
  | cast kind op ty =>
    let ⟨h_sub₁, h_dec₁⟩ := collectOperand_spec acc op
    let ⟨h_sub₂, h_dec₂⟩ := collectTy_spec (collectOperand acc op) ty
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl
  | unsupported => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩

theorem collectStmt_spec (acc : List MirTy) (s : StatementKind) :
    SubTable acc (collectStmt acc s) ∧
    (∀ ts, SubTable (collectStmt acc s) ts →
      decodeStmt ts (encodeStmt ts s) = some s) := by
  cases s with
  | assign dst rv =>
    let ⟨h_sub₁, h_dec₁⟩ := collectPlace_spec acc dst
    let ⟨h_sub₂, h_dec₂⟩ := collectRvalue_spec (collectPlace acc dst) rv
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeStmt, decodeStmt]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl
  | storageLive _ | storageDead _ | nop | unsupported =>
    exact ⟨SubTable.refl acc, fun _ _ => rfl⟩

theorem collectTerminator_spec (acc : List MirTy) (term : TerminatorKind) :
    SubTable acc (collectTerminator acc term) ∧
    (∀ ts, SubTable (collectTerminator acc term) ts →
      decodeTerminator ts (encodeTerminator ts term) = some term) := by
  cases term with
  | goto _ | return_ | unreachable | unwindResume | unsupported =>
    exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | switchInt d targets =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc d
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeTerminator, decodeTerminator]
    rw [h_dec ts h_s]
    rfl
  | assert c exp msg t u =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc c
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeTerminator, decodeTerminator]
    rw [h_dec ts h_s]
    rfl
  | call callee args dst t u =>
    let ⟨h_sub₁, h_dec₁⟩ := foldl_collect_mapOption_spec collectOperand
      encodeOperand decodeOperand collectOperand_spec acc args
    let ⟨h_sub₂, h_dec₂⟩ :=
      collectPlace_spec (args.foldl collectOperand acc) dst
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeTerminator, decodeTerminator]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl
  | callBuiltin builtin args dst t u =>
    let ⟨h_sub₁, h_dec₁⟩ := foldl_collect_mapOption_spec collectOperand
      encodeOperand decodeOperand collectOperand_spec acc args
    let ⟨h_sub₂, h_dec₂⟩ :=
      collectPlace_spec (args.foldl collectOperand acc) dst
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeTerminator, decodeTerminator]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl

theorem collectBasicBlock_spec (acc : List MirTy) (bb : BasicBlock) :
    SubTable acc (collectBasicBlock acc bb) ∧
    (∀ ts, SubTable (collectBasicBlock acc bb) ts →
      decodeBasicBlock ts (encodeBasicBlock ts bb) = some bb) := by
  cases bb with
  | mk stmts term cleanup =>
    let ⟨h_sub₁, h_dec₁⟩ := foldl_collect_mapOption_spec collectStmt
      encodeStmt decodeStmt collectStmt_spec acc stmts
    let ⟨h_sub₂, h_dec₂⟩ :=
      collectTerminator_spec (stmts.foldl collectStmt acc) term
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeBasicBlock, decodeBasicBlock]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl

theorem collectBody_spec (acc : List MirTy) (b : Body) :
    SubTable acc (collectBody acc b) ∧
    (∀ ts, SubTable (collectBody acc b) ts →
      decodeBody ts (encodeBody ts b) = some b) := by
  cases b with
  | mk argCount locals bbs isUnsafe identity =>
    let ⟨h_sub₁, h_dec₁⟩ := collectTyList_spec acc locals
    let ⟨h_sub₂, h_dec₂⟩ := foldl_collect_mapOption_spec collectBasicBlock
      encodeBasicBlock decodeBasicBlock collectBasicBlock_spec
      (collectTyList acc locals) bbs
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeBody, decodeBody]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl

/-- Unconditional global anti-laundering theorem: every `p : Program` with
inline `MirTy` round-trips through `encodeProg` and `decodeProg` with zero
preconditions, including its target `pointerWidthBits`, `mirProfileVersion`,
and `scope`. -/
theorem decodeProg_encodeProg_base : DecodeProgEncodeProgClaim := by
  intro p
  cases p with
  | mk bodies entryDefId pointerWidthBits mirProfileVersion scope =>
    dsimp only [encodeProg, decodeProg, collectProgTypes]
    let ⟨_, h_dec⟩ := foldl_collect_mapOption_spec collectBody
      encodeBody decodeBody collectBody_spec [] bodies
    rw [h_dec (bodies.foldl collectBody []) (SubTable.refl _)]
    rfl

mutual
  theorem collectTy_canonical (acc : List MirTy) (ty : MirTy)
      (h : typesAreCanonical acc = true) :
      typesAreCanonical (collectTy acc ty) = true := by
    cases ty with
    | bool =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .bool acc h
    | int w s =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.int w s) acc h
    | unit =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .unit acc h
    | never =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .never acc h
    | enum ety =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.enum ety) acc h
    | unsupported =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .unsupported acc h
    | ref m p =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.ref m p) (collectTy acc p)
        (collectTy_canonical acc p h)
    | rawPtr m p =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.rawPtr m p) (collectTy acc p)
        (collectTy_canonical acc p h)
    | tuple fs =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.tuple fs) (collectTyList acc fs)
        (collectTyList_canonical acc fs h)

  theorem collectTyList_canonical (acc : List MirTy) (tys : List MirTy)
      (h : typesAreCanonical acc = true) :
      typesAreCanonical (collectTyList acc tys) = true := by
    cases tys with
    | nil =>
      dsimp only [collectTyList]
      exact h
    | cons ty rest =>
      dsimp only [collectTyList]
      exact collectTyList_canonical (collectTy acc ty) rest
        (collectTy_canonical acc ty h)
end

theorem collectProjElem_canonical (acc : List MirTy) (e : ProjectionElem)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectProjElem acc e) = true := by
  cases e with
  | deref | unsupported => exact h
  | field _ ty => exact collectTy_canonical acc ty h

theorem collectPlace_canonical (acc : List MirTy) (p : Place)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectPlace acc p) = true :=
  foldl_preserve (fun ts => typesAreCanonical ts = true) collectProjElem
    collectProjElem_canonical p.projection h

theorem collectOperand_canonical (acc : List MirTy) (op : Operand)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectOperand acc op) = true := by
  cases op with
  | copy p | move p => exact collectPlace_canonical acc p h
  | constant c => exact collectTy_canonical acc c.ty h

theorem collectRvalue_canonical (acc : List MirTy) (rv : Rvalue)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectRvalue acc rv) = true := by
  cases rv with
  | use op | unaryOp _ op => exact collectOperand_canonical acc op h
  | binaryOp _ l r =>
    exact collectOperand_canonical (collectOperand acc l) r
      (collectOperand_canonical acc l h)
  | discriminant p | ref _ p | addressOf _ p =>
    exact collectPlace_canonical acc p h
  | aggregateTuple ops =>
    exact foldl_preserve (fun ts => typesAreCanonical ts = true) collectOperand
      collectOperand_canonical ops h
  | cast _ op ty =>
    exact collectTy_canonical (collectOperand acc op) ty
      (collectOperand_canonical acc op h)
  | unsupported => exact h

theorem collectStmt_canonical (acc : List MirTy) (s : StatementKind)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectStmt acc s) = true := by
  cases s with
  | assign dst rv =>
    exact collectRvalue_canonical (collectPlace acc dst) rv
      (collectPlace_canonical acc dst h)
  | storageLive _ | storageDead _ | nop | unsupported => exact h

theorem collectTerminator_canonical (acc : List MirTy) (term : TerminatorKind)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectTerminator acc term) = true := by
  cases term with
  | goto _ | return_ | unreachable | unwindResume | unsupported => exact h
  | switchInt d _ | assert d _ _ _ _ => exact collectOperand_canonical acc d h
  | call _ args dst _ _ | callBuiltin _ args dst _ _ =>
    exact collectPlace_canonical (args.foldl collectOperand acc) dst
      (foldl_preserve (fun ts => typesAreCanonical ts = true) collectOperand
        collectOperand_canonical args h)

theorem collectBasicBlock_canonical (acc : List MirTy) (bb : BasicBlock)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectBasicBlock acc bb) = true :=
  collectTerminator_canonical (bb.statements.foldl collectStmt acc)
    bb.terminator
    (foldl_preserve (fun ts => typesAreCanonical ts = true) collectStmt
      collectStmt_canonical bb.statements h)

theorem collectBody_canonical (acc : List MirTy) (b : Body)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectBody acc b) = true :=
  foldl_preserve (fun ts => typesAreCanonical ts = true) collectBasicBlock
    collectBasicBlock_canonical b.basicBlocks
    (collectTyList_canonical acc b.locals h)

/-- Canonical type deduplication theorem: for every `p : Program`,
`(encodeProg p).types` contains no duplicate `MirTy` entries, guaranteeing
that nominal `TyId` equality in `lean-miri` (`assertSameType`,
`assertRvalueLayout`) agrees with structural `MirTy` equality. -/
theorem encodeProg_types_canonical_base : EncodeProgTypesCanonicalClaim :=
  fun p =>
    foldl_preserve (fun ts => typesAreCanonical ts = true) collectBody
      collectBody_canonical p.bodies rfl

/-! ## One-to-One Simulation Invariant (`SimulationInv`) -/

/-- Project the runtime `LocalSlot` list from a `RefLocalState` list. -/
noncomputable def unzipRefSlots
    (rlocals : List RefLocalState) : List LocalSlot :=
  rlocals.map (·.slot)

theorem unzipRefSlots_zipRefLocals {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    (h_len : slots.length = bodyLocals.length) :
    unzipRefSlots (zipRefLocals bodyLocals slots) = slots := by
  induction bodyLocals generalizing slots with
  | nil =>
    cases slots with
    | nil => rfl
    | cons _ _ => cases h_len
  | cons ty tys ih =>
    cases slots with
    | nil => cases h_len
    | cons s ss =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      exact congrArg (s :: ·) (ih h_len)

theorem list_reverse_inj {α : Type} {xs ys : List α}
    (h : xs.reverse = ys.reverse) : xs = ys := by
  have h' := congrArg List.reverse h
  rw [List.reverse_reverse, List.reverse_reverse] at h'
  exact h'

theorem frame_unique_of_frameSimInv {p : Program} {f₁ f₂ : FrameState}
    {rf : RefFrameState}
    (h₁ : FrameSimInv p f₁ rf) (h₂ : FrameSimInv p f₂ rf) : f₁ = f₂ := by
  let ⟨body₁, _, hlen₁, hrf₁⟩ := h₁
  let ⟨body₂, _, hlen₂, hrf₂⟩ := h₂
  have h_eq := hrf₁.symm.trans hrf₂
  have h_def : f₁.defId = f₂.defId := congrArg RefFrameState.defId h_eq
  have h_blk : f₁.blockIdx = f₂.blockIdx :=
    congrArg RefFrameState.blockIdx h_eq
  have h_stmt : f₁.stmtIdx = f₂.stmtIdx := congrArg RefFrameState.stmtIdx h_eq
  have h_cont : f₁.returnCont = f₂.returnCont :=
    congrArg RefFrameState.returnCont h_eq
  have h_loc_eq : zipRefLocals body₁.locals f₁.locals =
      zipRefLocals body₂.locals f₂.locals :=
    congrArg RefFrameState.locals h_eq
  have h_slots : f₁.locals = f₂.locals := by
    have h_u := congrArg unzipRefSlots h_loc_eq
    rw [unzipRefSlots_zipRefLocals hlen₁,
      unzipRefSlots_zipRefLocals hlen₂] at h_u
    exact h_u
  cases f₁; cases f₂
  simp only [FrameState.mk.injEq]
  exact ⟨h_def, h_blk, h_stmt, h_slots, h_cont⟩

theorem refFrame_unique_of_frameSimInv {p : Program} {f : FrameState}
    {rf₁ rf₂ : RefFrameState}
    (h₁ : FrameSimInv p f rf₁) (h₂ : FrameSimInv p f rf₂) : rf₁ = rf₂ := by
  let ⟨body₁, hbody₁, _, hrf₁⟩ := h₁
  let ⟨body₂, hbody₂, _, hrf₂⟩ := h₂
  rw [hbody₁] at hbody₂
  injection hbody₂ with h_b_eq
  subst h_b_eq
  exact hrf₁.trans hrf₂.symm

theorem frames_unique_of_framesSimInv {p : Program} {fs₁ fs₂ : List FrameState}
    {rfs : List RefFrameState}
    (h₁ : FramesSimInv p fs₁ rfs) (h₂ : FramesSimInv p fs₂ rfs) :
    fs₁ = fs₂ := by
  induction rfs generalizing fs₁ fs₂ with
  | nil =>
    cases fs₁ with
    | nil =>
      cases fs₂ with
      | nil => rfl
      | cons _ _ => cases h₂
    | cons _ _ => cases h₁
  | cons rf rest ih =>
    cases fs₁ with
    | nil => cases h₁
    | cons f₁ t₁ =>
      cases fs₂ with
      | nil => cases h₂
      | cons f₂ t₂ =>
        rw [frame_unique_of_frameSimInv h₁.1 h₂.1, ih h₁.2 h₂.2]

theorem refFrames_unique_of_framesSimInv {p : Program} {fs : List FrameState}
    {rfs₁ rfs₂ : List RefFrameState}
    (h₁ : FramesSimInv p fs rfs₁) (h₂ : FramesSimInv p fs rfs₂) :
    rfs₁ = rfs₂ := by
  induction fs generalizing rfs₁ rfs₂ with
  | nil =>
    cases rfs₁ with
    | nil =>
      cases rfs₂ with
      | nil => rfl
      | cons _ _ => cases h₂
    | cons _ _ => cases h₁
  | cons f rest ih =>
    cases rfs₁ with
    | nil => cases h₁
    | cons rf₁ t₁ =>
      cases rfs₂ with
      | nil => cases h₂
      | cons rf₂ t₂ =>
        rw [refFrame_unique_of_frameSimInv h₁.1 h₂.1, ih h₁.2 h₂.2]

/-- One-to-one uniqueness of `SimulationInv` (left-injective): any `RefState`
`rs` corresponds to at most one $M_{\text{anneal}}$ `State`. -/
theorem state_unique_of_simulationInv_base :
    StateUniqueOfSimulationInvClaim := by
  intro p s₁ s₂ rs h₁ h₂
  let ⟨rfs₁, _, _, hrs₁, hcm₁, _, hfs₁⟩ := h₁
  let ⟨rfs₂, _, _, hrs₂, hcm₂, _, hfs₂⟩ := h₂
  rw [hrs₁] at hrs₂
  injection hrs₂ with _ h_rev
  have h_rfs := list_reverse_inj h_rev
  subst h_rfs
  have h_frames := frames_unique_of_framesSimInv hfs₁ hfs₂
  cases s₁; cases s₂
  simp only [State.mk.injEq]
  exact ⟨h_frames, hcm₁.symm.trans hcm₂⟩

/-- One-to-one uniqueness of `SimulationInv` (right-injective at fixed step
counters): any $M_{\text{anneal}}$ `State` `s` and step counters
`(stepsExecuted, maxSteps)` uniquely determine `rs`, including its caller
sentinel frame. -/
theorem refState_unique_of_simulationInv_base :
    RefStateUniqueOfSimulationInvClaim := by
  intro p s rs₁ rs₂ h₁ h₂ h_steps h_max
  let ⟨rfs₁, retTy₁, _, hrs₁, hcm₁, hret₁, hfs₁⟩ := h₁
  let ⟨rfs₂, retTy₂, _, hrs₂, hcm₂, hret₂, hfs₂⟩ := h₂
  rw [hret₁] at hret₂
  injection hret₂ with h_ret_eq
  subst h_ret_eq
  have h_rfs := refFrames_unique_of_framesSimInv hfs₁ hfs₂
  subst h_rfs
  cases rs₁; cases rs₂
  simp only [RefState.mk.injEq]
  exact ⟨hrs₁.trans hrs₂.symm, hcm₁.trans hcm₂.symm, h_steps, h_max⟩

theorem getElem?_zipRefLocals_some {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot : LocalSlot}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_slot : MirSemantics.getElem? slots i = some slot) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i =
      some ⟨slot, some ty⟩ := by
  induction bodyLocals generalizing slots i with
  | nil => cases h_ty
  | cons t ts ih =>
    cases slots with
    | nil => cases h_slot
    | cons s ss =>
      cases i with
      | zero =>
        injection h_ty with h_t
        injection h_slot with h_s
        subst h_t; subst h_s
        rfl
      | succ j =>
        exact ih h_ty h_slot

theorem getElem?_zipRefLocals_none_left {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} (h_ty : MirSemantics.getElem? bodyLocals i = none) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_ty
      | succ j => exact ih h_ty

theorem getElem?_zipRefLocals_none_right {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} (h_slot : MirSemantics.getElem? slots i = none) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_slot
      | succ j => exact ih h_slot

theorem getElem?_some_of_length_eq {α β : Type} {xs : List α} {ys : List β}
    {i : Nat} {x : α}
    (h_len : xs.length = ys.length)
    (h_x : MirSemantics.getElem? xs i = some x) :
    ∃ y : β, MirSemantics.getElem? ys i = some y := by
  induction xs generalizing ys i with
  | nil => cases h_x
  | cons a as ih =>
    cases ys with
    | nil => cases h_len
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      cases i with
      | zero => exact ⟨b, rfl⟩
      | succ j => exact @ih bs j h_len h_x

theorem setElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : MirSemantics.setElem? xs i v = some xs') :
    xs'.length = xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons x rest ih =>
    cases i with
    | zero =>
      injection h with h_eq
      subst h_eq
      rfl
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_rest : MirSemantics.setElem? rest j v with
      | none => rw [h_rest] at h; cases h
      | some rest' =>
        rw [h_rest] at h
        injection h with h_eq
        subst h_eq
        simp only [List.length_cons, ih h_rest]

theorem setElem?_zipRefLocals_some {bodyLocals : List MirTy}
    {slots slots' : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot' : LocalSlot}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_set : MirSemantics.setElem? slots i slot' = some slots') :
    MirSemantics.setElem? (zipRefLocals bodyLocals slots) i ⟨slot', some ty⟩ =
      some (zipRefLocals bodyLocals slots') := by
  induction bodyLocals generalizing slots slots' i with
  | nil => cases h_ty
  | cons t ts ih =>
    cases slots with
    | nil => cases h_set
    | cons s ss =>
      cases i with
      | zero =>
        injection h_ty with h_t
        injection h_set with h_s
        subst h_t; subst h_s
        rfl
      | succ j =>
        dsimp only [MirSemantics.setElem?] at h_set
        cases h_ss : MirSemantics.setElem? ss j slot' with
        | none => rw [h_ss] at h_set; cases h_set
        | some ss' =>
          rw [h_ss] at h_set
          injection h_set with h_s
          subst h_s
          dsimp only [zipRefLocals, MirSemantics.setElem?]
          rw [ih h_ty h_ss]

theorem setElem?_zipRefLocals_none {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} {rval : RefLocalState} {slot' : LocalSlot}
    (h_set : MirSemantics.setElem? slots i slot' = none) :
    MirSemantics.setElem? (zipRefLocals bodyLocals slots) i rval = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_set
      | succ j =>
        dsimp only [MirSemantics.setElem?] at h_set
        cases h_ss : MirSemantics.setElem? ss j slot' with
        | some _ => rw [h_ss] at h_set; cases h_set
        | none =>
          dsimp only [zipRefLocals, MirSemantics.setElem?]
          rw [ih h_ss]

theorem evalPlaceOperand_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {place : Place} {isMove : Bool}
    {ty : MirTy} {sv : SlotVal}
    (h : evalPlaceOperand bodyLocals locals place isMove =
      .ok (ty, sv, locals')) :
    locals'.length = locals.length := by
  unfold evalPlaceOperand at h
  cases h_ty : MirSemantics.getElem? bodyLocals place.localId with
  | none => rw [h_ty] at h; cases h
  | some localTy =>
    cases h_sl : MirSemantics.getElem? locals place.localId with
    | none => rw [h_ty, h_sl] at h; cases h
    | some slot =>
      rw [h_ty, h_sl] at h
      cases slot with
      | dead => cases h
      | live root =>
        dsimp only at h
        cases h_pt : projectTy? localTy place.projection with
        | none => rw [h_pt] at h; cases h
        | some pty =>
          cases h_rd : readSlotPath? root place.projection with
          | none => rw [h_pt, h_rd] at h; cases h
          | some psv =>
            rw [h_pt, h_rd] at h
            cases isMove with
            | false =>
              injection h with h_tup
              injection h_tup with _ h_rest
              injection h_rest with _ h_loc
              subst h_loc
              rfl
            | true =>
              dsimp only at h
              cases h_w : writeSlotPath? root place.projection
                  (uninitSlotVal pty) with
              | none => rw [h_w] at h; cases h
              | some root' =>
                rw [h_w] at h
                dsimp only at h
                cases h_set :
                    MirSemantics.setElem? locals place.localId (.live root') <;>
                  rw [h_set] at h
                · cases h
                · injection h with h_tup
                  injection h_tup with _ h_rest
                  injection h_rest with _ h_loc
                  subst h_loc
                  exact setElem?_length h_set

theorem evalOperandToSlot_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {op : Operand} {ty : MirTy} {sv : SlotVal}
    (h : evalOperandToSlot bodyLocals locals op = .ok (ty, sv, locals')) :
    locals'.length = locals.length := by
  cases op with
  | copy p => exact evalPlaceOperand_length h
  | move p => exact evalPlaceOperand_length h
  | constant c =>
    dsimp only [evalOperandToSlot] at h
    cases h_lit : evalConstLit c.ty c.lit <;> rw [h_lit] at h
    · cases h
    · injection h with h_tup
      injection h_tup with _ h_rest
      injection h_rest with _ h_loc
      subst h_loc
      rfl

theorem evalPrimitiveOperand_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {opnd : Operand} {v : Val}
    (h : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    locals'.length = locals.length := by
  unfold evalPrimitiveOperand at h
  cases h_op : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [h_op] at h; cases h
  | ok res =>
    let ⟨ty, sv₀, l₁⟩ := res
    rw [h_op] at h
    dsimp only at h
    cases h_pr : isPrimitiveReadableTy ty <;> rw [h_pr] at h
    · cases h
    · cases h_v : SlotVal.toVal? sv₀ with
      | none => rw [h_v] at h; cases h
      | some v₀ =>
        rw [h_v] at h
        injection h with h_tup
        injection h_tup with _ h_loc
        subst h_loc
        exact evalOperandToSlot_length h_op

theorem evalRvalue_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (h : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    locals'.length = locals.length := by
  cases rv with
  | use opnd =>
    dsimp only [evalRvalue] at h
    cases h_op : evalOperandToSlot bodyLocals locals opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨srcTy, sv₀, l₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_eq_ty : MirTy.beq srcTy dstTy <;> rw [h_eq_ty] at h
      · cases h
      · cases h_v : SlotVal.toVal? sv₀ with
        | none => rw [h_v] at h; cases h
        | some v₀ =>
          rw [h_v] at h
          injection h with h_tup
          injection h_tup with _ h_loc
          subst h_loc
          exact evalOperandToSlot_length h_op
  | binaryOp op lhs rhs =>
    dsimp only [evalRvalue] at h
    cases h_l : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [h_l] at h; cases h
    | ok resL =>
      let ⟨lVal, l₁⟩ := resL
      rw [h_l] at h
      dsimp only at h
      cases h_r : evalPrimitiveOperand bodyLocals l₁ rhs with
      | error _ => rw [h_r] at h; cases h
      | ok resR =>
        let ⟨rVal, l₂⟩ := resR
        rw [h_r] at h
        dsimp only at h
        cases h_b : evalBinOp op lVal rVal <;> rw [h_b] at h
        · cases h
        · injection h with h_tup
          injection h_tup with _ h_loc
          subst h_loc
          exact (evalPrimitiveOperand_length h_r).trans
            (evalPrimitiveOperand_length h_l)
  | unaryOp op opnd =>
    dsimp only [evalRvalue] at h
    cases h_op : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨v₀, l₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_u : evalUnOp op v₀ <;> rw [h_u] at h
      · cases h
      · injection h with h_tup
        injection h_tup with _ h_loc
        subst h_loc
        exact evalPrimitiveOperand_length h_op
  | discriminant place =>
    dsimp only [evalRvalue] at h
    cases h_emp : place.projection.isEmpty <;> rw [h_emp] at h
    · cases h
    · cases h_ty : MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [h_ty] at h; cases h
      | some ty =>
        rw [h_ty] at h
        cases ty with
        | enum ety =>
          cases h_sl : MirSemantics.getElem? locals place.localId with
          | none => rw [h_sl] at h; cases h
          | some slot =>
            rw [h_sl] at h
            dsimp only at h
            cases h_adm : enumAdmitted ety <;> rw [h_adm] at h
            · cases h
            · cases h_tr : ety.tagRepr <;> rw [h_tr] at h
              · cases slot with
                | dead => cases h
                | live sv₀ =>
                  cases sv₀ with
                  | uninit =>
                    dsimp only at h
                    cases h_d : MirSemantics.getElem? ety.discriminants 0 <;>
                      rw [h_d] at h
                    · cases h
                    · injection h with h_tup
                      injection h_tup with _ h_loc
                      subst h_loc
                      rfl
                  | enumVal ety' v =>
                    dsimp only at h
                    cases h_chk : (EnumTy.beq ety ety' && Nat.beq v 0) <;>
                      rw [h_chk] at h
                    · cases h
                    · cases h_d :
                          MirSemantics.getElem? ety.discriminants 0 <;>
                        rw [h_d] at h
                      · cases h
                      · injection h with h_tup
                        injection h_tup with _ h_loc
                        subst h_loc
                        rfl
                  | _ => cases h
              · cases slot with
                | dead => cases h
                | live sv₀ =>
                  cases sv₀ with
                  | enumVal ety' v =>
                    dsimp only at h
                    cases h_chk :
                      (EnumTy.beq ety ety' &&
                        Nat.blt v ety.discriminants.length) <;>
                      rw [h_chk] at h
                    · cases h
                    · cases h_d :
                          MirSemantics.getElem? ety.discriminants v <;>
                        rw [h_d] at h
                      · cases h
                      · injection h with h_tup
                        injection h_tup with _ h_loc
                        subst h_loc
                        rfl
                  | _ => cases h
        | _ => cases h
  | aggregateTuple _ => cases h
  | cast kind opnd castTy =>
    dsimp only [evalRvalue] at h
    cases h_op : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨v₀, l₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases kind with
      | unsupported => cases h
      | intToInt =>
        dsimp only at h
        cases h_ty : MirTy.beq castTy dstTy <;> rw [h_ty] at h
        · cases h
        · cases h_c : evalIntToIntCast v₀ castTy <;> rw [h_c] at h
          · cases h
          · injection h with h_tup
            injection h_tup with _ h_loc
            subst h_loc
            exact evalPrimitiveOperand_length h_op
  | ref _ _ | addressOf _ _ | unsupported =>
    cases h

theorem writePlace_length {locals locals' : List LocalSlot}
    {dst : Place} {dstTy : MirTy} {val : Val}
    (h : writePlace locals dst dstTy val = .ok locals') :
    locals'.length = locals.length := by
  unfold writePlace at h
  cases h_chk : checkVal val dstTy <;> rw [h_chk] at h
  · cases h
  · cases h_get : MirSemantics.getElem? locals dst.localId with
    | none => rw [h_get] at h; cases h
    | some slot =>
      rw [h_get] at h
      cases slot with
      | dead => cases h
      | live root =>
        dsimp only at h
        cases h_w : writeSlotPath? root dst.projection val.toSlotVal with
        | none => rw [h_w] at h; cases h
        | some root' =>
          rw [h_w] at h
          dsimp only at h
          cases h_set :
              MirSemantics.setElem? locals dst.localId (.live root') <;>
            rw [h_set] at h
          · cases h
          · injection h with h_eq
            subst h_eq
            exact setElem?_length h_set

theorem writeAggregateTupleFields_length {bodyLocals : List MirTy}
    {dst : Place} {idx : Nat} {locals locals' : List LocalSlot}
    {ops : List Operand} {fieldTys : List MirTy}
    (h : writeAggregateTupleFields bodyLocals dst idx locals ops fieldTys =
      .ok locals') :
    locals'.length = locals.length := by
  induction ops generalizing idx locals fieldTys with
  | nil =>
    cases fieldTys with
    | nil =>
      injection h with h_loc
      subst h_loc
      rfl
    | cons _ _ => cases h
  | cons o os ih =>
    cases fieldTys with
    | nil => cases h
    | cons ft fts =>
      dsimp only [writeAggregateTupleFields] at h
      cases h_op : evalOperandToSlot bodyLocals locals o with
      | error _ => rw [h_op] at h; cases h
      | ok res =>
        let ⟨srcTy, sv₀, l₁⟩ := res
        rw [h_op] at h
        dsimp only at h
        cases h_ty : MirTy.beq srcTy ft <;> rw [h_ty] at h
        · cases h
        · cases h_v : SlotVal.toVal? sv₀ with
          | none => rw [h_v] at h; cases h
          | some v₀ =>
            rw [h_v] at h
            dsimp only at h
            cases h_wr : writePlace l₁
                { dst with projection := dst.projection ++ [.field idx ft] }
                ft v₀ with
            | error _ => rw [h_wr] at h; cases h
            | ok l₂ =>
              rw [h_wr] at h
              exact ((ih h).trans (writePlace_length h_wr)).trans
                (evalOperandToSlot_length h_op)

theorem writeAggregateTuple_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dst : Place} {dstTy : MirTy}
    {ops : List Operand}
    (h : writeAggregateTuple bodyLocals locals dst dstTy ops = .ok locals') :
    locals'.length = locals.length := by
  unfold writeAggregateTuple at h
  cases ops with
  | nil =>
    cases dstTy with
    | unit => exact writePlace_length h
    | _ => cases h
  | cons o os =>
    cases dstTy with
    | tuple fieldTys =>
      dsimp only at h
      cases h_len : Nat.beq (o :: os).length fieldTys.length <;>
        rw [h_len] at h
      · cases h
      · exact writeAggregateTupleFields_length h
    | _ => cases h

theorem decodePlace_inv {ts : List MirTy} {rp : RefPlace} {p : Place}
    (h : decodePlace ts rp = some p) :
    rp.localId = p.localId ∧ rp.projection.isEmpty = p.projection.isEmpty := by
  dsimp only [decodePlace] at h
  cases h_proj : mapOption (decodeProjElem ts) rp.projection with
  | none => rw [h_proj] at h; cases h
  | some proj =>
    rw [h_proj] at h
    injection h with h_eq
    subst h_eq
    exact ⟨rfl, mapOption_isEmpty h_proj⟩

/-- A decoded place keeps its local, and its projection is the element-wise
decoding of the reference projection. -/
theorem decodePlace_proj_inv {ts : List MirTy} {rp : RefPlace} {p : Place}
    (h : decodePlace ts rp = some p) :
    rp.localId = p.localId ∧
      mapOption (decodeProjElem ts) rp.projection = some p.projection := by
  dsimp only [decodePlace] at h
  cases h_proj : mapOption (decodeProjElem ts) rp.projection with
  | none => rw [h_proj] at h; cases h
  | some proj =>
    rw [h_proj] at h
    injection h with h_eq
    subst h_eq
    exact ⟨rfl, rfl⟩

/-- Inversion of `mapOption` on a non-empty list: the head and the tail both
decode. -/
theorem mapOption_cons_inv {α β : Type} {f : α → Option β} {x : α}
    {xs : List α} {ys : List β}
    (h : mapOption f (x :: xs) = some ys) :
    ∃ y ys', f x = some y ∧ mapOption f xs = some ys' ∧ ys = y :: ys' := by
  dsimp only [mapOption, optMap2] at h
  cases h_x : f x with
  | none => rw [h_x] at h; cases h
  | some y =>
    cases h_xs : mapOption f xs with
    | none => rw [h_x, h_xs] at h; cases h
    | some ys' =>
      rw [h_x, h_xs] at h
      injection h with h_eq
      exact ⟨y, ys', rfl, rfl, h_eq.symm⟩

/-- The reference type projection over the translated projection agrees with
`projectTy?` over the decoded projection. -/
theorem refProjectTy?_eq {ts : List MirTy} {rproj : List RefProjectionElem}
    {proj : List ProjectionElem}
    (h : mapOption (decodeProjElem ts) rproj = some proj) (ty : MirTy) :
    refProjectTy? ts ty (rproj.map toMiriProjElem) = projectTy? ty proj := by
  induction rproj generalizing proj ty with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons e es ih =>
    let ⟨e', es', h_e, h_es, h_eq⟩ := mapOption_cons_inv h
    subst h_eq
    cases e with
    | deref =>
      injection h_e with h_e'
      subst h_e'
      cases ty <;> rfl
    | unsupported =>
      injection h_e with h_e'
      subst h_e'
      cases ty <;> rfl
    | field idx tyId =>
      dsimp only [decodeProjElem, optMap] at h_e
      cases h_t : MirSemantics.getElem? ts tyId with
      | none => rw [h_t] at h_e; cases h_e
      | some fty =>
        rw [h_t] at h_e
        injection h_e with h_e'
        subst h_e'
        cases ty with
        | tuple fieldTys =>
          dsimp only [List.map, toMiriProjElem, refProjectTy?, projectTy?]
          rw [h_t]
          cases h_f : MirSemantics.getElem? fieldTys idx with
          | none => rfl
          | some ft =>
            dsimp only
            rw [ih h_es ft]
        | _ => rfl

/-- The reference slot read over the translated projection agrees with
`readSlotPath?` over the decoded projection. -/
theorem refReadSlotPath?_eq {ts : List MirTy} {rproj : List RefProjectionElem}
    {proj : List ProjectionElem}
    (h : mapOption (decodeProjElem ts) rproj = some proj) (sv : SlotVal) :
    refReadSlotPath? sv (rproj.map toMiriProjElem) = readSlotPath? sv proj := by
  induction rproj generalizing proj sv with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons e es ih =>
    let ⟨e', es', h_e, h_es, h_eq⟩ := mapOption_cons_inv h
    subst h_eq
    cases e with
    | deref =>
      injection h_e with h_e'
      subst h_e'
      cases sv <;> rfl
    | unsupported =>
      injection h_e with h_e'
      subst h_e'
      cases sv <;> rfl
    | field idx tyId =>
      dsimp only [decodeProjElem, optMap] at h_e
      cases h_t : MirSemantics.getElem? ts tyId with
      | none => rw [h_t] at h_e; cases h_e
      | some fty =>
        rw [h_t] at h_e
        injection h_e with h_e'
        subst h_e'
        cases sv with
        | tuple fields =>
          dsimp only [List.map, toMiriProjElem, refReadSlotPath?,
            readSlotPath?]
          cases h_f : MirSemantics.getElem? fields idx with
          | none => rfl
          | some field =>
            dsimp only
            rw [ih h_es field]
        | _ => rfl

/-- The reference slot update over the translated projection agrees with
`writeSlotPath?` over the decoded projection. -/
theorem refWriteSlotPath?_eq {ts : List MirTy} {rproj : List RefProjectionElem}
    {proj : List ProjectionElem}
    (h : mapOption (decodeProjElem ts) rproj = some proj)
    (sv new : SlotVal) :
    refWriteSlotPath? sv (rproj.map toMiriProjElem) new =
      writeSlotPath? sv proj new := by
  induction rproj generalizing proj sv with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons e es ih =>
    let ⟨e', es', h_e, h_es, h_eq⟩ := mapOption_cons_inv h
    subst h_eq
    cases e with
    | deref =>
      injection h_e with h_e'
      subst h_e'
      cases sv <;> rfl
    | unsupported =>
      injection h_e with h_e'
      subst h_e'
      cases sv <;> rfl
    | field idx tyId =>
      dsimp only [decodeProjElem, optMap] at h_e
      cases h_t : MirSemantics.getElem? ts tyId with
      | none => rw [h_t] at h_e; cases h_e
      | some fty =>
        rw [h_t] at h_e
        injection h_e with h_e'
        subst h_e'
        cases sv with
        | tuple fields =>
          dsimp only [List.map, toMiriProjElem, refWriteSlotPath?,
            writeSlotPath?]
          cases h_f : MirSemantics.getElem? fields idx with
          | none => rfl
          | some field =>
            dsimp only
            rw [ih h_es field]
            cases writeSlotPath? field es' new <;> rfl
        | _ => rfl

theorem evalCallArgs_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {args : List Operand}
    {pairs : List (MirTy × SlotVal)}
    (h : evalCallArgs bodyLocals locals args = .ok (pairs, locals')) :
    locals'.length = locals.length := by
  induction args generalizing locals pairs with
  | nil =>
    injection h with h_p
    injection h_p with _ h_loc
    subst h_loc
    rfl
  | cons a rest ih =>
    dsimp only [evalCallArgs] at h
    cases h_op : evalOperandToSlot bodyLocals locals a with
    | error _ => rw [h_op] at h; cases h
    | ok r₁ =>
      let ⟨ty, sv, l₁⟩ := r₁
      rw [h_op] at h
      dsimp only at h
      cases h_rest : evalCallArgs bodyLocals l₁ rest with
      | error _ => rw [h_rest] at h; cases h
      | ok r₂ =>
        let ⟨ps, l₂⟩ := r₂
        rw [h_rest] at h
        injection h with h_p
        injection h_p with _ h_loc
        subst h_loc
        exact (ih h_rest).trans (evalOperandToSlot_length h_op)

/-- `refProjectReturnTy?` agrees with `projectTy?` on every decoded place
projection. -/
theorem refProjectReturnTy?_eq (ty : MirTy) (proj : List ProjectionElem) :
    refProjectReturnTy? ty proj = projectTy? ty proj := by
  induction proj generalizing ty with
  | nil => rfl
  | cons e rest ih =>
    cases ty with
    | tuple fieldTys =>
      cases e with
      | field idx statedTy =>
        dsimp only [refProjectReturnTy?, projectTy?]
        cases MirSemantics.getElem? fieldTys idx with
        | none => rfl
        | some ft =>
          dsimp only
          rw [ih ft]
      | deref | unsupported => rfl
    | _ => rfl

/-- `refWriteSlotPath?` over `proj.map toMiriReturnProjElem` agrees with
`writeSlotPath?` over `proj`. -/
theorem refWriteSlotPath?_toMiriReturnProjElem_eq (sv : SlotVal)
    (proj : List ProjectionElem) (new : SlotVal) :
    refWriteSlotPath? sv (proj.map toMiriReturnProjElem) new =
      writeSlotPath? sv proj new := by
  induction proj generalizing sv with
  | nil => rfl
  | cons e rest ih =>
    cases sv with
    | tuple fields =>
      cases e with
      | field idx _ =>
        dsimp only [List.map, toMiriReturnProjElem, refWriteSlotPath?,
          writeSlotPath?]
        cases MirSemantics.getElem? fields idx with
        | none => rfl
        | some field =>
          dsimp only
          rw [ih field]
          cases writeSlotPath? field rest new <;> rfl
      | deref | unsupported => rfl
    | _ => rfl

/-- `decodeMiriProjElem` inverts `toMiriProjElem` to `decodeProjElem`. -/
theorem decodeMiriProjElem_toMiriProjElem (ts : List MirTy)
    (e : RefProjectionElem) :
    decodeMiriProjElem ts (toMiriProjElem e) = decodeProjElem ts e := by
  cases e <;> rfl

/-- `decodeMiriPlace` inverts `toMiriPlace` to `decodePlace`. -/
theorem decodeMiriPlace_toMiriPlace (ts : List MirTy) (rp : RefPlace) :
    decodeMiriPlace ts (toMiriPlace rp) = decodePlace ts rp := by
  cases rp with
  | mk localId proj =>
    dsimp only [decodeMiriPlace, decodePlace, toMiriPlace]
    have h_map :
        mapOption (decodeMiriProjElem ts) (proj.map toMiriProjElem) =
          mapOption (decodeProjElem ts) proj := by
      induction proj with
      | nil => rfl
      | cons e rest ih =>
        dsimp only [List.map, mapOption]
        rw [decodeMiriProjElem_toMiriProjElem, ih]
    rw [h_map]

/-- The translated projection of a reference place is empty exactly when the
reference projection is. -/
theorem toMiriPlace_proj_toList (rp : RefPlace) :
    (toMiriPlace rp).projection.toList =
      rp.projection.map toMiriProjElem := rfl

noncomputable def mapSlotRes (bodyLocals : List MirTy) :
    Except FaultKind (MirTy × SlotVal × List LocalSlot) →
    Except FaultKind (MirTy × SlotVal × List RefLocalState)
  | .error k => .error k
  | .ok (ty, sv, slots') => .ok (ty, sv, zipRefLocals bodyLocals slots')

noncomputable def mapSlotsRes (bodyLocals : List MirTy) :
    Except FaultKind (List LocalSlot) →
    Except FaultKind (List RefLocalState)
  | .error k => .error k
  | .ok slots' => .ok (zipRefLocals bodyLocals slots')

/-!
## Reference Arithmetic, Constant, and Branch Equivalence (`vendor/lean-miri`)
-/

section MiriEquiv

open Miri.ABI Miri.Memory Miri.Interpreter

theorem bitVec_zeroExtend_eq {w : Nat} (hw : w ≤ 128) (x : BitVec w) :
    BitVec.zeroExtend 128 x = bvZeroExtend 128 x := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [BitVec.zeroExtend, BitVec.setWidth, bvZeroExtend]
  rw [dite_eq_left hw, BitVec.toNat_setWidth', BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.setWidth'._proof_1 hw x)).symm

theorem bitVec_ofInt_eq (n : Nat) (i : Int) :
    BitVec.ofInt n i = bvOfInt n i := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvOfInt]
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  change (intEmod i (Int.ofNat (HPow.hPow 2 n))).toNat =
    HMod.hMod (intEmod i (Int.ofNat (HPow.hPow 2 n))).toNat (HPow.hPow 2 n)
  exact (Nat.mod_eq_of_lt (BitVec.ofInt._proof_1 n i)).symm

theorem bitVec_signExtend_eq {w : Nat} (v : Nat) (x : BitVec w) :
    BitVec.signExtend v x = bvSignExtend v x := by
  dsimp only [BitVec.signExtend, bvSignExtend]
  rw [bitVec_ofInt_eq]
  rfl

theorem size_truncate_eq (w : IntWidth) (v : BitVec 128) :
    (toMiriSize w).truncate v = .ok (truncateBits w v) := by
  cases w <;> (
    change Except.ok (BitVec.zeroExtend 128 (BitVec.extractLsb _ 0 v)) =
      .ok (truncateBits _ v)
    rw [bitVec_zeroExtend_eq (by decide)]
    rfl)

theorem size_signExtend_eq (w : IntWidth) (v : BitVec 128) :
    (toMiriSize w).signExtend v = .ok (signExtendBits w v) := by
  cases w <;> (
    change Except.ok (BitVec.signExtend 128 (BitVec.extractLsb _ 0 v)).toInt =
      .ok (signExtendBits _ v)
    rw [bitVec_signExtend_eq]
    rfl)

theorem miriScalar_toUInt (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toUInt (toMiriSize w) = .ok (truncateBits w bits) := by
  have h : (miriScalar w bits).toUInt (toMiriSize w) =
      ((toMiriSize w).truncate bits).mapError ScalarIntError.sizeError := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  rfl

theorem miriScalar_toInt (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toInt (toMiriSize w) =
      .ok (signExtendBits w (truncateBits w bits)) := by
  have h : (miriScalar w bits).toInt (toMiriSize w) =
      match (toMiriSize w).truncate bits with
      | .ok b =>
        ((toMiriSize w).signExtend b).mapError ScalarIntError.sizeError
      | .error e => .error (.sizeError e) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  dsimp only
  rw [size_signExtend_eq]
  rfl

theorem integerOps_decode_eq (sv : ScalarVal) :
    IntegerOps.decode (miriIntValue sv) = .ok (decodeScalar sv) := by
  cases sv with
  | mk w s bits =>
    have hs : (toMiriIntType w s).signed = s := by cases w <;> cases s <;> rfl
    dsimp only [IntegerOps.decode, miriIntValue, decodeScalar]
    rw [hs]
    cases s with
    | true =>
      change ((miriScalar w bits).toInt (toMiriSize w)).mapError
        IntegerOpError.scalar = _
      rw [miriScalar_toInt]
      rfl
    | false =>
      change bind
        (((miriScalar w bits).toUInt (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun u => pure (Int.ofNat u.toNat)) = _
      rw [miriScalar_toUInt]
      rfl

theorem toMiriIntType_signed (w : IntWidth) (s : Bool) :
    (toMiriIntType w s).signed = s := by
  cases w <;> cases s <;> rfl

theorem toMiriIntType_size (w : IntWidth) (s : Bool) :
    (toMiriIntType w s).size = toMiriSize w := rfl

theorem unary_truncate_signed_eq (w : IntWidth) (resInt : Int) :
    (match bind
        ((ScalarInt.truncateFromInt
          (BitVec.ofInt 128 resInt).toInt (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w true resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [bitVec_ofInt_eq]
  change (match bind
      ((ScalarInt.truncateFromInt
        (bvToInt (bvOfInt 128 resInt)) (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w true resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k)
  dsimp only [truncateScalar]
  let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
  rw [h_w]
  cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
  | true =>
    cases w <;> (
      dsimp only [ScalarInt.truncateFromInt]
      rw [h_oob]
      rfl)
  | false =>
    have h : (match bind
        ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
      | .ok sc =>
        (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
      | .ok b =>
        match (toMiriSize w).signExtend b with
        | .ok _ => .ok (.scalar ⟨w, true, b⟩)
        | .error _ => .error .unsupported
      | .error _ => .error .unsupported) := by
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    rw [h, bitVec_ofInt_eq, size_truncate_eq]
    dsimp only
    rw [size_signExtend_eq]
    rfl

theorem unary_truncate_unsigned_eq (w : IntWidth) (resInt : Int) :
    (match bind
        ((ScalarInt.truncateFromUInt
          (BitVec.ofInt 128 resInt) (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w false resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [bitVec_ofInt_eq]
  dsimp only [truncateScalar]
  let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
  rw [h_raw]
  have h : (match bind
      ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match (toMiriSize w).truncate raw with
    | .ok b => .ok (.scalar ⟨w, false, b⟩)
    | .error _ => .error .unsupported) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  rfl

theorem unary_truncate_eq (w : IntWidth) (s : Bool) (resInt : Int) :
    (match bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped (toMiriIntType w s).size).mapError
            IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt
            (BitVec.ofInt 128 resInt) (toMiriIntType w s).size).mapError
            IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [toMiriIntType_signed, toMiriIntType_size]
  cases s with
  | true => exact unary_truncate_signed_eq w resInt
  | false => exact unary_truncate_unsigned_eq w resInt

/-- Proof-side shorthand lifting `Trusted.MirAst.UnOp` into
`Trusted.Correspondence.evalRefMiriUnOp`. -/
noncomputable def evalRefUnOp (op : UnOp) (v : Val) : Except FaultKind Val :=
  evalRefMiriUnOp (toMiriUnOp op) v

theorem evalRefUnOp_eq (op : UnOp) (v : Val) :
    evalRefUnOp op v = evalUnOp op v := by
  cases v with
  | bool b => cases op <;> rfl
  | unit | enumVal _ _ | ptr _ | tuple _ | bytes _ => cases op <;> rfl
  | scalar sv =>
    cases sv with
    | mk w s bits =>
      cases op with
      | not =>
        dsimp only [evalRefUnOp, evalRefMiriUnOp, evalUnOp, toMiriUnOp,
          IntegerOps.unary]
        rw [integerOps_decode_eq]
        exact unary_truncate_eq w s (intNot (decodeScalar ⟨w, s, bits⟩))
      | neg =>
        dsimp only [evalRefUnOp, evalRefMiriUnOp, evalUnOp, toMiriUnOp,
          IntegerOps.unary]
        rw [integerOps_decode_eq]
        change (match
            (let k := fun (result : Int) =>
              bind
                (if (toMiriIntType w s).signed then
                  let wrapped := (BitVec.ofInt 128 result).toInt
                  (ScalarInt.truncateFromInt wrapped
                    (toMiriIntType w s).size).mapError IntegerOpError.scalar
                else
                  (ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
                    (toMiriIntType w s).size).mapError IntegerOpError.scalar)
                (fun x => pure x.1)
            if (toMiriIntType w s).signed then
              bind (pure (Neg.neg (decodeScalar ⟨w, s, bits⟩))) k
            else
              bind (throw (IntegerOpError.invalidUnaryOperator .Neg
                (toMiriIntType w s).signed)) k) with
          | .ok sc =>
            (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
          | .error (.undefinedBehavior _) => .error .undefined
          | .error _ => .error .unsupported) =
          if s then
            match truncateScalar w s (Neg.neg (decodeScalar ⟨w, s, bits⟩)) with
            | .ok (res, _) => .ok (.scalar res)
            | .error k => .error k
          else
            .error .unsupported
        let ⟨resInt, h_res⟩ : ∃ x, Neg.neg (decodeScalar ⟨w, s, bits⟩) = x :=
          ⟨_, rfl⟩
        rw [h_res, toMiriIntType_signed, toMiriIntType_size]
        cases s with
        | false => rfl
        | true => exact unary_truncate_signed_eq w resInt
      | ptrMetadata =>
        dsimp only [evalRefUnOp, evalRefMiriUnOp, evalUnOp, toMiriUnOp,
          IntegerOps.unary]
        rw [integerOps_decode_eq]
        rfl

theorem size_signedIntMin_eq (w : IntWidth) :
    (toMiriSize w).signedIntMin = .ok (signedMinInt w) := by
  cases w <;> rfl

theorem bvAnd_eq (x y : BitVec 128) : HAnd.hAnd x y = bvAnd x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvAnd]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.and._proof_1 x y)).symm

theorem bvOr_eq (x y : BitVec 128) : HOr.hOr x y = bvOr x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvOr]
  rw [BitVec.toNat_or, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.or._proof_1 x y)).symm

theorem bvXor_eq (x y : BitVec 128) : HXor.hXor x y = bvXor x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvXor]
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.xor._proof_1 x y)).symm

theorem toMiriBinOp_isUnchecked (op : BinOp) :
    (toMiriBinOp op).isUnchecked = op.isUnchecked := by
  cases op <;> rfl

theorem shift_truncate_eq (op : BinOp) (w : IntWidth) (s rs : Bool)
    (resInt r : Int) (overflow : Bool) :
    (match bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (res, _) =>
      if overflow && op.isUnchecked then
        .error .undefined
      else
        .ok (.scalar res)) := by
  rw [toMiriIntType_signed, toMiriIntType_size, bitVec_ofInt_eq,
      toMiriBinOp_isUnchecked]
  cases s with
  | true =>
    change (match bind
        ((ScalarInt.truncateFromInt (bvToInt (bvOfInt 128 resInt))
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res))
    dsimp only [truncateScalar]
    let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
    rw [h_w]
    cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
    | true =>
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    | false =>
      have h : (match bind
          ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar)
          (fun (value, _) =>
            if overflow && op.isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.shiftOverflow (toMiriBinOp op) r rs))
            else
              pure (IntegerResult.scalar value)) with
        | .ok (.scalar sc) =>
          (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
        | .ok (.boolean b) => .ok (.bool b)
        | .ok _ => .error .unsupported
        | .error (.undefinedBehavior _) => .error .undefined
        | .error _ => .error .unsupported) =
        (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
        | .ok b =>
          match (toMiriSize w).signExtend b with
          | .ok _ =>
            if overflow && op.isUnchecked then
              .error .undefined
            else
              .ok (.scalar ⟨w, true, b⟩)
          | .error _ => .error .unsupported
        | .error _ => .error .unsupported) := by
        cases w <;> (
          dsimp only [ScalarInt.truncateFromInt]
          rw [h_oob]
          cases (overflow && op.isUnchecked) <;> rfl)
      rw [h, bitVec_ofInt_eq, size_truncate_eq]
      dsimp only
      rw [size_signExtend_eq]
      rfl
  | false =>
    change (match bind
        ((ScalarInt.truncateFromUInt (bvOfInt 128 resInt)
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w false resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res))
    dsimp only [truncateScalar]
    let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
    rw [h_raw]
    have h : (match bind
        ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate raw with
      | .ok b =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar ⟨w, false, b⟩)
      | .error _ => .error .unsupported) := by
      cases w <;> cases (overflow && op.isUnchecked) <;> rfl
    rw [h, size_truncate_eq]
    rfl

theorem binary_truncate_scalarResult_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (resInt : Int) (hostOverflow : Bool)
    (h_ovf : (toMiriBinOp op).isOverflowing = false) :
    (match bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (val, lossy) =>
      if (hostOverflow || lossy) && op.isUnchecked then
        .error .undefined
      else
        .ok (.scalar val)) := by
  rw [toMiriIntType_signed, toMiriIntType_size, bitVec_ofInt_eq, h_ovf,
      toMiriBinOp_isUnchecked]
  cases s with
  | true =>
    change (match bind
        ((ScalarInt.truncateFromInt (bvToInt (bvOfInt 128 resInt))
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if false then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if (hostOverflow || lossy) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar val))
    dsimp only [truncateScalar]
    let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
    rw [h_w]
    cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
    | true =>
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    | false =>
      have h : (match bind
          ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && op.isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if false then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value)) with
        | .ok (.scalar sc) =>
          (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
        | .ok (.boolean b) => .ok (.bool b)
        | .ok _ => .error .unsupported
        | .error (.undefinedBehavior _) => .error .undefined
        | .error _ => .error .unsupported) =
        (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
        | .ok b =>
          match (toMiriSize w).signExtend b with
          | .ok dec =>
            if (hostOverflow || (dec != wrapped)) && op.isUnchecked then
              .error .undefined
            else
              .ok (.scalar ⟨w, true, b⟩)
          | .error _ => .error .unsupported
        | .error _ => .error .unsupported) := by
        cases w <;> (
          dsimp only [ScalarInt.truncateFromInt]
          rw [h_oob]
          change (match (if ((hostOverflow || _) && op.isUnchecked) = true then
              Except.error (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              Except.ok (IntegerResult.scalar _)) with
            | .ok (.scalar sc) =>
              (Except.ok (Val.scalar ⟨_, true, sc.data⟩) : Except FaultKind Val)
            | .ok (.boolean b) => .ok (.bool b)
            | .ok _ => .error .unsupported
            | .error (.undefinedBehavior _) => .error .undefined
            | .error _ => .error .unsupported) =
            if ((hostOverflow || _) && op.isUnchecked) = true then
              Except.error FaultKind.undefined
            else
              Except.ok (Val.scalar ⟨_, true, _⟩)
          cases ((hostOverflow || _) && op.isUnchecked) <;> rfl)
      rw [h, bitVec_ofInt_eq, size_truncate_eq]
      dsimp only
      rw [size_signExtend_eq]
      rfl
  | false =>
    change (match bind
        ((ScalarInt.truncateFromUInt (bvOfInt 128 resInt)
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if false then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w false resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if (hostOverflow || lossy) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar val))
    dsimp only [truncateScalar]
    let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
    rw [h_raw]
    have h : (match bind
        ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if false then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate raw with
      | .ok b =>
        if (hostOverflow || (b != raw)) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar ⟨w, false, b⟩)
      | .error _ => .error .unsupported) := by
      cases w <;> (
        change (match (if ((hostOverflow || _) && op.isUnchecked) = true then
            Except.error (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            Except.ok (IntegerResult.scalar _)) with
          | .ok (.scalar sc) =>
            (Except.ok (Val.scalar ⟨_, false, sc.data⟩) : Except FaultKind Val)
          | .ok (.boolean b) => .ok (.bool b)
          | .ok _ => .error .unsupported
          | .error (.undefinedBehavior _) => .error .undefined
          | .error _ => .error .unsupported) =
          if ((hostOverflow || _) && op.isUnchecked) = true then
            Except.error FaultKind.undefined
          else
            Except.ok (Val.scalar ⟨_, false, _⟩)
        cases ((hostOverflow || _) && op.isUnchecked) <;> rfl)
    rw [h, size_truncate_eq]
    rfl

/-- Overflowing-operator counterpart of `binary_truncate_scalarResult_eq`: for
an operator that reports overflow (`isOverflowing = true`, never unchecked),
`Miri.Interpreter.IntegerOps`' truncation of the mathematical result `resInt`
yields the pair `(wrapped, hostOverflow || lossy)` that
`Trusted.MirSemantics.evalOverflowingArithOp` builds from `truncateScalar`. -/
theorem binary_truncate_overflowResult_eq (op : BinOp) (w : IntWidth)
    (s : Bool) (resInt : Int) (hostOverflow : Bool)
    (h_ovf : (toMiriBinOp op).isOverflowing = true)
    (h_unc : op.isUnchecked = false) :
    (match bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
    | .ok (.withOverflow sc overflow) =>
      (Except.ok (Val.tuple [.scalar ⟨w, s, sc.data⟩, .bool overflow]) :
        Except FaultKind Val)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (val, lossy) =>
      .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)])) := by
  rw [toMiriIntType_signed, toMiriIntType_size, bitVec_ofInt_eq, h_ovf,
      toMiriBinOp_isUnchecked, h_unc]
  simp only [Bool.and_false]
  cases s with
  | true =>
    change (match bind
        ((ScalarInt.truncateFromInt (bvToInt (bvOfInt 128 resInt))
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if false then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if true then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.withOverflow sc overflow) =>
        (Except.ok (Val.tuple [.scalar ⟨w, true, sc.data⟩, .bool overflow]) :
          Except FaultKind Val)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)]))
    dsimp only [truncateScalar]
    let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
    rw [h_w]
    cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
    | true =>
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    | false =>
      have h : (match bind
          ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar)
          (fun (value, lossy) =>
            if false then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if true then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value)) with
        | .ok (.withOverflow sc overflow) =>
          (Except.ok (Val.tuple [.scalar ⟨w, true, sc.data⟩,
            .bool overflow]) : Except FaultKind Val)
        | .ok _ => .error .unsupported
        | .error (.undefinedBehavior _) => .error .undefined
        | .error _ => .error .unsupported) =
        (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
        | .ok b =>
          match (toMiriSize w).signExtend b with
          | .ok dec =>
            .ok (.tuple [.scalar ⟨w, true, b⟩,
              .bool (hostOverflow || (dec != wrapped))])
          | .error _ => .error .unsupported
        | .error _ => .error .unsupported) := by
        cases w <;> (
          dsimp only [ScalarInt.truncateFromInt]
          rw [h_oob]
          rfl)
      rw [h, bitVec_ofInt_eq, size_truncate_eq]
      dsimp only
      rw [size_signExtend_eq]
      rfl
  | false =>
    change (match bind
        ((ScalarInt.truncateFromUInt (bvOfInt 128 resInt)
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if false then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if true then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.withOverflow sc overflow) =>
        (Except.ok (Val.tuple [.scalar ⟨w, false, sc.data⟩, .bool overflow]) :
          Except FaultKind Val)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w false resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)]))
    dsimp only [truncateScalar]
    let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
    rw [h_raw]
    have h : (match bind
        ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, lossy) =>
          if false then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if true then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.withOverflow sc overflow) =>
        (Except.ok (Val.tuple [.scalar ⟨w, false, sc.data⟩, .bool overflow]) :
          Except FaultKind Val)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate raw with
      | .ok b =>
        .ok (.tuple [.scalar ⟨w, false, b⟩,
          .bool (hostOverflow || (b != raw))])
      | .error _ => .error .unsupported) := by
      cases w <;> rfl
    rw [h, size_truncate_eq]
    rfl

theorem toMiriIntType_bne_of_false {w₁ w₂ : IntWidth} {s₁ s₂ : Bool}
    (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = false) :
    (toMiriIntType w₁ s₁ != toMiriIntType w₂ s₂) = true := by
  cases w₁ <;> cases w₂ <;> cases s₁ <;> cases s₂ <;>
    first | rfl | nomatch h

theorem eq_of_intWidth_beq_and_signed {w₁ w₂ : IntWidth} {s₁ s₂ : Bool}
    (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true) : w₁ = w₂ ∧ s₁ = s₂ := by
  cases w₁ <;> cases w₂ <;> cases s₁ <;> cases s₂ <;>
    first | exact ⟨rfl, rfl⟩ | nomatch h

theorem toMiriIntType_bne_self (w : IntWidth) (s : Bool) :
    (toMiriIntType w s != toMiriIntType w s) = false := by
  cases w <;> cases s <;> rfl

theorem bitwise_truncate_eq (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    (match bind
        ((ScalarInt.truncateFromUInt bits (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, _) => pure (IntegerResult.scalar value)) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    .ok (.scalar ⟨w, s, truncateBits w bits⟩) := by
  have h : (match bind
      ((ScalarInt.truncateFromUInt bits (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun (value, _) => pure (IntegerResult.scalar value)) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match (toMiriSize w).truncate bits with
    | .ok b => .ok (.scalar ⟨w, s, b⟩)
    | .error _ => .error .unsupported) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

/-- Proof-side shorthand lifting `Trusted.MirAst.BinOp` into
`Trusted.Correspondence.evalRefMiriBinOp`. -/
noncomputable def evalRefBinOp (op : BinOp) (lhs rhs : Val) :
    Except FaultKind Val :=
  evalRefMiriBinOp (toMiriBinOp op) lhs rhs

theorem evalShiftOp_eq (op : BinOp) (w₁ w₂ : IntWidth) (s₁ s₂ : Bool)
    (bits₁ bits₂ : BitVec 128) (h_sh : op.isShift = true) :
    evalRefBinOp op (.scalar ⟨w₁, s₁, bits₁⟩) (.scalar ⟨w₂, s₂, bits₂⟩) =
    evalBinOp op (.scalar ⟨w₁, s₁, bits₁⟩) (.scalar ⟨w₂, s₂, bits₂⟩) := by
  have proveShift (op' : BinOp) (resInt rInt : Int) (w : IntWidth) :
      (match bind
          (if (toMiriIntType w s₁).signed then
            let wrapped := (BitVec.ofInt 128 resInt).toInt
            (ScalarInt.truncateFromInt wrapped
              (toMiriIntType w s₁).size).mapError IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
              (toMiriIntType w s₁).size).mapError IntegerOpError.scalar)
          (fun (value, _) =>
            if (intEmod rInt (Int.ofNat w.bitWidth) != rInt) &&
                (toMiriBinOp op').isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.shiftOverflow (toMiriBinOp op') rInt
                  (toMiriIntType w₂ s₂).signed))
            else
              pure (IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, s₁, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w s₁ resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if (intEmod rInt (Int.ofNat w.bitWidth) != rInt) && op'.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res)) :=
    shift_truncate_eq op' w s₁ (toMiriIntType w₂ s₂).signed resInt rInt _
  cases op with
  | shl =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp, evalShiftOp,
      toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .isize
  | shr =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp, evalShiftOp,
      toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .isize
  | shlUnchecked =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp, evalShiftOp,
      toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .isize
  | shrUnchecked =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp, evalShiftOp,
      toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .isize
  | _ => nomatch h_sh

theorem miriIntValue_type_bne_of_false (w₁ w₂ : IntWidth) (s₁ s₂ : Bool)
    (b₁ b₂ : BitVec 128) (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = false) :
    ((miriIntValue ⟨w₁, s₁, b₁⟩).type != (miriIntValue ⟨w₂, s₂, b₂⟩).type) =
      true :=
  toMiriIntType_bne_of_false h

theorem miriIntValue_type_bne_self (w : IntWidth) (s : Bool)
    (b₁ b₂ : BitVec 128) :
    ((miriIntValue ⟨w, s, b₁⟩).type != (miriIntValue ⟨w, s, b₂⟩).type) =
      false :=
  toMiriIntType_bne_self w s

theorem miriIntValue_toUInt (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    (miriIntValue ⟨w, s, bits⟩).scalar.toUInt
      (miriIntValue ⟨w, s, bits⟩).type.size =
    .ok (truncateBits w bits) :=
  miriScalar_toUInt w bits

theorem arith_after_rw_eq (op : BinOp) (w : IntWidth) (s : Bool) (resInt : Int)
    (h_ovf : (toMiriBinOp op).isOverflowing = false) :
    (match (let hostOverflow := if s then
          decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (resInt ≥ HPow.hPow (2 : Int) 127)
        else
          decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)
      bind (if s then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value))) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (val, lossy) =>
      if ((if s then
            decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 127)
          else
            decide (resInt < 0) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 128)) ||
          lossy) && op.isUnchecked then
        .error .undefined
      else
        .ok (.scalar val)) := by
  have h := binary_truncate_scalarResult_eq op w s resInt
    (if s then
      decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (resInt ≥ HPow.hPow (2 : Int) 127)
    else
      decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)) h_ovf
  rw [toMiriIntType_signed, toMiriIntType_size] at h
  exact h

theorem int_tdiv_eq (a b : Int) : Int.tdiv a b = intTdiv a b := by
  cases a <;> cases b <;> rfl

theorem int_tmod_eq (a b : Int) : Int.tmod a b = intTmod a b := by
  cases a <;> cases b <;> rfl

theorem div_rem_signed_eq (op : BinOp) (w : IntWidth) (lInt rInt resInt : Int)
    (h_ovf : (toMiriBinOp op).isOverflowing = false) :
    (match
      (let jp := fun (_ : PUnit) =>
        let hostOverflow := if true then
            decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 127)
          else
            decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)
        bind (if true then
            let wrapped := (BitVec.ofInt 128 resInt).toInt
            (ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
              IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
              (toMiriSize w)).mapError IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if (toMiriBinOp op).isOverflowing then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value))
      if lInt == signedMinInt w && rInt == Neg.neg 1 then
        bind (throw (IntegerOpError.undefinedBehavior
          (if toMiriBinOp op == Miri.MIR.BinOp.Div then
            .divisionOverflow
          else
            .remainderOverflow))) jp
      else
        jp PUnit.unit) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (if (false : Bool) then
      .error .undefined
    else if lInt == signedMinInt w && rInt == Neg.neg 1 then
      .error .undefined
    else
      match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if ((if true then
              decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
                decide (resInt ≥ HPow.hPow (2 : Int) 127)
            else
              decide (resInt < 0) ||
                decide (resInt ≥ HPow.hPow (2 : Int) 128)) ||
            lossy) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar val)) := by
  cases (lInt == signedMinInt w && rInt == Neg.neg 1) with
  | true => rfl
  | false => exact arith_after_rw_eq op w true resInt h_ovf

theorem arith_full_eq (op : BinOp) (w : IntWidth) (s : Bool) (lInt rInt : Int)
    (h_op : (match op with
      | .add | .sub | .mul | .addUnchecked | .subUnchecked | .mulUnchecked
      | .div | .rem => true
      | _ => false) = true) :
    (match
      (let jp3 := fun (result : Int) =>
        let hostOverflow := if (toMiriIntType w s).signed then
            decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (result ≥ HPow.hPow (2 : Int) 127)
          else
            decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
        bind (if (toMiriIntType w s).signed then
            let wrapped := (BitVec.ofInt 128 result).toInt
            (ScalarInt.truncateFromInt wrapped
              (toMiriIntType w s).size).mapError IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
              (toMiriIntType w s).size).mapError IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if (toMiriBinOp op).isOverflowing then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value))
      let jp2 := fun (_ : PUnit) =>
        match toMiriBinOp op with
        | .Add | .AddUnchecked | .AddWithOverflow =>
          bind (pure (lInt + rInt)) jp3
        | .Sub | .SubUnchecked | .SubWithOverflow =>
          bind (pure (lInt - rInt)) jp3
        | .Mul | .MulUnchecked | .MulWithOverflow =>
          bind (pure (lInt * rInt)) jp3
        | .Div => bind (pure (Int.tdiv lInt rInt)) jp3
        | .Rem => bind (pure (Int.tmod lInt rInt)) jp3
        | _ =>
          bind (throw (IntegerOpError.invalidBinaryOperator (toMiriBinOp op)))
            jp3
      let jp1 := fun (_ : PUnit) =>
        if (toMiriIntType w s).signed &&
            (toMiriBinOp op == Miri.MIR.BinOp.Div ||
              toMiriBinOp op == Miri.MIR.BinOp.Rem) then
          bind (((toMiriIntType w s).size.signedIntMin).mapError
              (Function.comp IntegerOpError.scalar ScalarIntError.sizeError))
            (fun min =>
              if lInt == min && rInt == Neg.neg 1 then
                bind (throw (IntegerOpError.undefinedBehavior
                  (if toMiriBinOp op == Miri.MIR.BinOp.Div then
                    .divisionOverflow
                  else
                    .remainderOverflow))) jp2
              else
                jp2 PUnit.unit)
        else
          jp2 PUnit.unit
      if rInt == 0 then
        let jp0 := fun (_ : PUnit) =>
          if toMiriBinOp op == Miri.MIR.BinOp.Rem then
            bind (throw (IntegerOpError.undefinedBehavior .remainderByZero))
              jp1
          else
            jp1 PUnit.unit
        if toMiriBinOp op == Miri.MIR.BinOp.Div then
          bind (throw (IntegerOpError.undefinedBehavior .divisionByZero)) jp0
        else
          jp0 PUnit.unit
      else
        jp1 PUnit.unit) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    evalArithOp op w s lInt rInt := by
  rw [toMiriIntType_signed, toMiriIntType_size, size_signedIntMin_eq,
      int_tdiv_eq, int_tmod_eq]
  cases op with
  | add =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .add w false (lInt + rInt) rfl
    | true => exact arith_after_rw_eq .add w true (lInt + rInt) rfl
  | sub =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .sub w false (lInt - rInt) rfl
    | true => exact arith_after_rw_eq .sub w true (lInt - rInt) rfl
  | mul =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .mul w false (lInt * rInt) rfl
    | true => exact arith_after_rw_eq .mul w true (lInt * rInt) rfl
  | addUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .addUnchecked w false (lInt + rInt) rfl
    | true => exact arith_after_rw_eq .addUnchecked w true (lInt + rInt) rfl
  | subUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .subUnchecked w false (lInt - rInt) rfl
    | true => exact arith_after_rw_eq .subUnchecked w true (lInt - rInt) rfl
  | mulUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .mulUnchecked w false (lInt * rInt) rfl
    | true => exact arith_after_rw_eq .mulUnchecked w true (lInt * rInt) rfl
  | div =>
    dsimp only [evalArithOp]
    cases (rInt == 0) with
    | true => rfl
    | false =>
      cases s with
      | false => exact arith_after_rw_eq .div w false (intTdiv lInt rInt) rfl
      | true => exact div_rem_signed_eq .div w lInt rInt (intTdiv lInt rInt) rfl
  | rem =>
    dsimp only [evalArithOp]
    cases (rInt == 0) with
    | true => rfl
    | false =>
      cases s with
      | false => exact arith_after_rw_eq .rem w false (intTmod lInt rInt) rfl
      | true => exact div_rem_signed_eq .rem w lInt rInt (intTmod lInt rInt) rfl
  | _ => nomatch h_op

theorem evalArithOp_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (bits₁ bits₂ : BitVec 128)
    (h_op : (match op with
      | .add | .sub | .mul | .addUnchecked | .subUnchecked | .mulUnchecked
      | .div | .rem => true
      | _ => false) = true) :
    evalRefBinOp op (.scalar ⟨w, s, bits₁⟩) (.scalar ⟨w, s, bits₂⟩) =
    evalArithOp op w s (decodeScalar ⟨w, s, bits₁⟩)
      (decodeScalar ⟨w, s, bits₂⟩) := by
  have h_full := arith_full_eq op w s
    (decodeScalar ⟨w, s, bits₁⟩) (decodeScalar ⟨w, s, bits₂⟩) h_op
  cases op with
  | add | sub | mul | addUnchecked | subUnchecked | mulUnchecked | div | rem =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [miriIntValue_type_bne_self]
    exact h_full
  | _ => nomatch h_op

theorem overflow_after_rw_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (resInt : Int)
    (h_ovf : (toMiriBinOp op).isOverflowing = true)
    (h_unc : op.isUnchecked = false) :
    (match (let hostOverflow := if s then
          decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (resInt ≥ HPow.hPow (2 : Int) 127)
        else
          decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)
      bind (if s then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value))) with
    | .ok (.withOverflow sc overflow) =>
      (Except.ok (Val.tuple [.scalar ⟨w, s, sc.data⟩, .bool overflow]) :
        Except FaultKind Val)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (val, lossy) =>
      .ok (.tuple [.scalar val, .bool ((if s then
            decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 127)
          else
            decide (resInt < 0) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 128)) || lossy)])) := by
  have h := binary_truncate_overflowResult_eq op w s resInt
    (if s then
      decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (resInt ≥ HPow.hPow (2 : Int) 127)
    else
      decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128))
    h_ovf h_unc
  rw [toMiriIntType_signed, toMiriIntType_size] at h
  exact h

theorem overflow_full_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (lInt rInt : Int)
    (h_op : (match op with
      | .addWithOverflow | .subWithOverflow | .mulWithOverflow => true
      | _ => false) = true) :
    (match
      (let jp3 := fun (result : Int) =>
        let hostOverflow := if (toMiriIntType w s).signed then
            decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (result ≥ HPow.hPow (2 : Int) 127)
          else
            decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
        bind (if (toMiriIntType w s).signed then
            let wrapped := (BitVec.ofInt 128 result).toInt
            (ScalarInt.truncateFromInt wrapped
              (toMiriIntType w s).size).mapError IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
              (toMiriIntType w s).size).mapError IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if (toMiriBinOp op).isOverflowing then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value))
      let jp2 := fun (_ : PUnit) =>
        match toMiriBinOp op with
        | .Add | .AddUnchecked | .AddWithOverflow =>
          bind (pure (lInt + rInt)) jp3
        | .Sub | .SubUnchecked | .SubWithOverflow =>
          bind (pure (lInt - rInt)) jp3
        | .Mul | .MulUnchecked | .MulWithOverflow =>
          bind (pure (lInt * rInt)) jp3
        | .Div => bind (pure (Int.tdiv lInt rInt)) jp3
        | .Rem => bind (pure (Int.tmod lInt rInt)) jp3
        | _ =>
          bind (throw (IntegerOpError.invalidBinaryOperator (toMiriBinOp op)))
            jp3
      let jp1 := fun (_ : PUnit) =>
        if (toMiriIntType w s).signed &&
            (toMiriBinOp op == Miri.MIR.BinOp.Div ||
              toMiriBinOp op == Miri.MIR.BinOp.Rem) then
          bind (((toMiriIntType w s).size.signedIntMin).mapError
              (Function.comp IntegerOpError.scalar ScalarIntError.sizeError))
            (fun min =>
              if lInt == min && rInt == Neg.neg 1 then
                bind (throw (IntegerOpError.undefinedBehavior
                  (if toMiriBinOp op == Miri.MIR.BinOp.Div then
                    .divisionOverflow
                  else
                    .remainderOverflow))) jp2
              else
                jp2 PUnit.unit)
        else
          jp2 PUnit.unit
      if rInt == 0 then
        let jp0 := fun (_ : PUnit) =>
          if toMiriBinOp op == Miri.MIR.BinOp.Rem then
            bind (throw (IntegerOpError.undefinedBehavior .remainderByZero))
              jp1
          else
            jp1 PUnit.unit
        if toMiriBinOp op == Miri.MIR.BinOp.Div then
          bind (throw (IntegerOpError.undefinedBehavior .divisionByZero)) jp0
        else
          jp0 PUnit.unit
      else
        jp1 PUnit.unit) with
    | .ok (.withOverflow sc overflow) =>
      (Except.ok (Val.tuple [.scalar ⟨w, s, sc.data⟩, .bool overflow]) :
        Except FaultKind Val)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    evalOverflowingArithOp op w s lInt rInt := by
  rw [toMiriIntType_signed, toMiriIntType_size, size_signedIntMin_eq,
      int_tdiv_eq, int_tmod_eq]
  cases op with
  | addWithOverflow =>
    cases (rInt == 0) <;> cases s with
    | false =>
      exact overflow_after_rw_eq .addWithOverflow w false (lInt + rInt) rfl rfl
    | true =>
      exact overflow_after_rw_eq .addWithOverflow w true (lInt + rInt) rfl rfl
  | subWithOverflow =>
    cases (rInt == 0) <;> cases s with
    | false =>
      exact overflow_after_rw_eq .subWithOverflow w false (lInt - rInt) rfl rfl
    | true =>
      exact overflow_after_rw_eq .subWithOverflow w true (lInt - rInt) rfl rfl
  | mulWithOverflow =>
    cases (rInt == 0) <;> cases s with
    | false =>
      exact overflow_after_rw_eq .mulWithOverflow w false (lInt * rInt) rfl rfl
    | true =>
      exact overflow_after_rw_eq .mulWithOverflow w true (lInt * rInt) rfl rfl
  | _ => nomatch h_op

theorem evalOverflowingArithOp_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (bits₁ bits₂ : BitVec 128)
    (h_op : (match op with
      | .addWithOverflow | .subWithOverflow | .mulWithOverflow => true
      | _ => false) = true) :
    evalRefBinOp op (.scalar ⟨w, s, bits₁⟩) (.scalar ⟨w, s, bits₂⟩) =
    evalOverflowingArithOp op w s (decodeScalar ⟨w, s, bits₁⟩)
      (decodeScalar ⟨w, s, bits₂⟩) := by
  have h_full := overflow_full_eq op w s
    (decodeScalar ⟨w, s, bits₁⟩) (decodeScalar ⟨w, s, bits₂⟩) h_op
  cases op with
  | addWithOverflow | subWithOverflow | mulWithOverflow =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [miriIntValue_type_bne_self]
    exact h_full
  | _ => nomatch h_op

theorem evalRefBinOp_eq (op : BinOp) (lhs rhs : Val) :
    evalRefBinOp op lhs rhs = evalBinOp op lhs rhs := by
  cases lhs with
  | unit | enumVal _ _ | ptr _ | tuple _ | bytes _ => cases rhs <;> rfl
  | bool l =>
    cases rhs with
    | unit | enumVal _ _ | ptr _ | tuple _ | bytes _ | scalar _ => rfl
    | bool r => cases op <;> cases l <;> cases r <;> rfl
  | scalar l =>
    cases rhs with
    | unit | enumVal _ _ | ptr _ | tuple _ | bytes _ | bool _ => rfl
    | scalar r =>
      cases l with
      | mk w₁ s₁ bits₁ =>
        cases r with
        | mk w₂ s₂ bits₂ =>
          cases h_sh : op.isShift with
          | true => exact evalShiftOp_eq op w₁ w₂ s₁ s₂ bits₁ bits₂ h_sh
          | false =>
            cases h_ty : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) with
            | false =>
              have h_bne :=
                miriIntValue_type_bne_of_false w₁ w₂ s₁ s₂ bits₁ bits₂ h_ty
              cases op with
              | shl | shr | shlUnchecked | shrUnchecked => nomatch h_sh
              | _ =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty]
                first | rfl | (
                  rw [integerOps_decode_eq, integerOps_decode_eq]
                  let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                    ⟨_, rfl⟩
                  let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x :=
                    ⟨_, rfl⟩
                  rw [h_l, h_r]
                  dsimp only [bind, Except.bind, pure, Except.pure]
                  rw [h_bne]
                  rfl)
            | true =>
              let ⟨h_w, h_s⟩ := eq_of_intWidth_beq_and_signed h_ty
              subst h_w
              subst h_s
              have h_bne := miriIntValue_type_bne_self w₁ s₁ bits₁ bits₂
              cases op with
              | shl | shr | shlUnchecked | shrUnchecked => nomatch h_sh
              | offset =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp]
                rw [h_ty]
                rfl
              | addWithOverflow =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalOverflowingArithOp_eq .addWithOverflow w₁ s₁ bits₁
                  bits₂ rfl
              | subWithOverflow =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalOverflowingArithOp_eq .subWithOverflow w₁ s₁ bits₁
                  bits₂ rfl
              | mulWithOverflow =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalOverflowingArithOp_eq .mulWithOverflow w₁ s₁ bits₁
                  bits₂ rfl
              | eq | ne | lt | le | gt | ge =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne]
                rfl
              | bitAnd =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvAnd_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | bitOr =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvOr_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | bitXor =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvXor_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | add =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .add w₁ s₁ bits₁ bits₂ rfl
              | sub =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .sub w₁ s₁ bits₁ bits₂ rfl
              | mul =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .mul w₁ s₁ bits₁ bits₂ rfl
              | addUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .addUnchecked w₁ s₁ bits₁ bits₂ rfl
              | subUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .subUnchecked w₁ s₁ bits₁ bits₂ rfl
              | mulUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .mulUnchecked w₁ s₁ bits₁ bits₂ rfl
              | div =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .div w₁ s₁ bits₁ bits₂ rfl
              | rem =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .rem w₁ s₁ bits₁ bits₂ rfl

theorem tryFromUInt_eq_truncateFromUInt (value : U128) (size : Size) :
    ScalarInt.tryFromUInt value size =
    bind (ScalarInt.truncateFromUInt value size)
      (fun (result, overflow) =>
        if overflow then pure none else pure (some result)) := rfl

theorem match_truncateFromUInt_eq {α : Type} (w : IntWidth) (raw : BitVec 128)
    (f : BitVec 128 → Bool → α) (d : α) :
    (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => f sc.data lossy
    | .error _ => d) =
    f (truncateBits w raw) (truncateBits w raw != raw) := by
  have h : (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => f sc.data lossy
    | .error _ => d) =
    (match (toMiriSize w).truncate raw with
    | .ok b => f b (b != raw)
    | .error _ => d) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

theorem match_tryFromUInt_eq {α : Type} (w : IntWidth) (raw : BitVec 128)
    (onSome : BitVec 128 → α) (onNone : α) :
    (match ScalarInt.tryFromUInt raw (toMiriSize w) with
    | .ok (some sc) => onSome sc.data
    | _ => onNone) =
    if truncateBits w raw != raw then onNone
    else onSome (truncateBits w raw) := by
  have h : (match ScalarInt.tryFromUInt raw (toMiriSize w) with
    | .ok (some sc) => onSome sc.data
    | _ => onNone) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => if lossy then onNone else onSome sc.data
    | .error _ => onNone) := by
    rw [tryFromUInt_eq_truncateFromUInt]
    cases ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | error _ => rfl
    | ok pair =>
      let ⟨sc, lossy⟩ := pair
      cases lossy <;> rfl
  rw [h, match_truncateFromUInt_eq w raw
    (fun d lossy => if lossy then onNone else onSome d) onNone]

theorem match_bool_uint8_eq {α : Type} (v : UInt8)
    (onBool : Bool → α) (onInvalidBool onErr : α) :
    (match ((if v == 0 then pure false
        else if v == 1 then pure true
        else throw (ScalarIntError.invalidBool v)) :
        Except ScalarIntError Bool) with
    | .ok b => onBool b
    | .error (.invalidBool _) => onInvalidBool
    | .error _ => onErr) =
    (if v == 0 then onBool false
     else if v == 1 then onBool true
     else onInvalidBool) := by
  cases (v == 0) with
  | true => rfl
  | false => cases (v == 1) <;> rfl

theorem match_tryFromUInt_tryToBool_eq {α : Type} (raw : BitVec 128)
    (onBool : Bool → α) (onInvalidBool onErr : α) :
    (match ScalarInt.tryFromUInt raw (toMiriSize .i8) with
    | .ok (some sc) =>
      match sc.tryToBool with
      | .ok b => onBool b
      | .error (.invalidBool _) => onInvalidBool
      | .error _ => onErr
    | _ => onErr) =
    if truncateBits .i8 raw != raw then
      onErr
    else
      let v := UInt8.ofNat (truncateBits .i8 raw).toNat
      if v == 0 then onBool false
      else if v == 1 then onBool true
      else onInvalidBool := by
  have h1 : (match ScalarInt.tryFromUInt raw (toMiriSize .i8) with
    | .ok (some sc) =>
      match sc.tryToBool with
      | .ok b => onBool b
      | .error (.invalidBool _) => onInvalidBool
      | .error _ => onErr
    | _ => onErr) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match sc.tryToBool with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) := by
    rw [tryFromUInt_eq_truncateFromUInt]
    cases ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | error _ => rfl
    | ok pair =>
      let ⟨sc, lossy⟩ := pair
      cases lossy <;> rfl
  have h2 : (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match sc.tryToBool with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match ((let v := UInt8.ofNat sc.data.toNat
          if v == 0 then pure false
          else if v == 1 then pure true
          else throw (ScalarIntError.invalidBool v)) :
          Except ScalarIntError Bool) with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) := rfl
  rw [h1, h2,
      match_truncateFromUInt_eq .i8 raw
        (fun d lossy =>
          if lossy then onErr
          else
            match ((let v := UInt8.ofNat d.toNat
              if v == 0 then pure false
              else if v == 1 then pure true
              else throw (ScalarIntError.invalidBool v)) :
              Except ScalarIntError Bool) with
            | .ok b => onBool b
            | .error (.invalidBool _) => onInvalidBool
            | .error _ => onErr)
        onErr,
      match_bool_uint8_eq]

theorem intWidth_modulus_pos (w : IntWidth) : 0 < Nat.pow 2 w.bitWidth := by
  cases w <;> decide

theorem intWidth_modulus_le_u128 (w : IntWidth) :
    Nat.pow 2 w.bitWidth ≤ Nat.pow 2 128 := by
  cases w <;> decide

theorem nat_ble_imp_le : ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => by cases h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (nat_ble_imp_le h)

theorem nat_lt_of_blt_eq_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  nat_ble_imp_le h

theorem nat_shiftRight_zero (n : Nat) : Nat.shiftRight n 0 = n := rfl

theorem ite_false_eq_true {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

theorem ite_true_eq_true {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

theorem intWidth_lsb_width (w : IntWidth) :
    w.bitWidth - 1 - 0 + 1 = w.bitWidth := by
  cases w <;> decide

theorem toNat_truncateBits (w : IntWidth) (x : BitVec 128) :
    (truncateBits w x).toNat = Nat.mod x.toNat (Nat.pow 2 w.bitWidth) := by
  dsimp only [truncateBits, bvZeroExtend, bvExtractLsb, bvExtractLsb']
  rw [nat_shiftRight_zero, intWidth_lsb_width,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change Nat.mod (Nat.mod x.toNat (Nat.pow 2 w.bitWidth)) (Nat.pow 2 128) =
    Nat.mod x.toNat (Nat.pow 2 w.bitWidth)
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le (Nat.mod_lt x.toNat (intWidth_modulus_pos w))
      (intWidth_modulus_le_u128 w))

theorem truncateBits_eq_ofNat_mod (w : IntWidth) (x : BitVec 128) :
    truncateBits w x =
      BitVec.ofNat 128 (Nat.mod x.toNat (Nat.pow 2 w.bitWidth)) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_truncateBits, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le (Nat.mod_lt x.toNat (intWidth_modulus_pos w))
      (intWidth_modulus_le_u128 w))).symm

theorem truncateBits_idem (w : IntWidth) (x : BitVec 128) :
    truncateBits w (truncateBits w x) = truncateBits w x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_truncateBits, toNat_truncateBits]
  exact Nat.mod_eq_of_lt (Nat.mod_lt x.toNat (intWidth_modulus_pos w))

theorem truncateBits_eq_of_beq_false {w : IntWidth} {x : BitVec 128}
    (h : (truncateBits w x != x) = false) :
    truncateBits w x = x := by
  have h_beq : (truncateBits w x == x) = true := by
    cases h_eq : (truncateBits w x == x) with
    | true => rfl
    | false =>
      change (!(truncateBits w x == x)) = false at h
      rw [h_eq] at h
      cases h
  exact eq_of_beq h_beq

theorem refNatNotElem_eq (x : Nat) (ys : List Nat) :
    refNatNotElem x ys = natNotElem x ys := by
  induction ys with
  | nil => rfl
  | cons y rest ih =>
    dsimp only [refNatNotElem, natNotElem]
    rw [ih]

theorem refNatListPairwiseNe_eq (xs : List Nat) :
    refNatListPairwiseNe xs = natListPairwiseNe xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [refNatListPairwiseNe, natListPairwiseNe]
    rw [refNatNotElem_eq, ih]

theorem refFindDiscrVariantAux_eq (idx : Nat) (discrBits : BitVec 128)
    (ds : List Nat) :
    refFindDiscrVariantAux idx discrBits ds =
      findDiscrVariantAux idx discrBits ds := by
  induction ds generalizing idx with
  | nil => rfl
  | cons d rest ih =>
    dsimp only [refFindDiscrVariantAux, findDiscrVariantAux]
    rw [ih (idx + 1)]

theorem refFindDiscrVariant?_eq (discrBits : BitVec 128) (ds : List Nat) :
    refFindDiscrVariant? discrBits ds = findDiscrVariant? discrBits ds :=
  refFindDiscrVariantAux_eq 0 discrBits ds

theorem refMiriTagToDiscrBits_eq (tagW : IntWidth) (tagS : Bool)
    (discrW : IntWidth) (tagBits : BitVec 128) :
    refMiriTagToDiscrBits tagW tagS discrW tagBits =
      some (tagBitsToDiscrBits tagW tagS discrW tagBits) := by
  cases tagS with
  | true =>
    change
      (match
          match (toMiriSize tagW).signExtend tagBits with
          | .ok integer => some (BitVec.ofInt 128 integer)
          | .error _ => none
        with
        | some extended =>
          match (toMiriSize discrW).truncate extended with
          | .ok discrBits => some discrBits
          | .error _ => none
        | none => none) =
      some (truncateBits discrW (bvOfInt 128 (signExtendBits tagW tagBits)))
    rw [size_signExtend_eq]
    dsimp only
    rw [bitVec_ofInt_eq, size_truncate_eq]
  | false =>
    change
      (match
          match (toMiriSize tagW).truncate tagBits with
          | .ok trunc => some trunc
          | .error _ => none
        with
        | some extended =>
          match (toMiriSize discrW).truncate extended with
          | .ok discrBits => some discrBits
          | .error _ => none
        | none => none) =
      some (truncateBits discrW (truncateBits tagW tagBits))
    rw [size_truncate_eq]
    dsimp only
    rw [size_truncate_eq]

theorem refEnumDiscrInBounds_eq (w : IntWidth) (d : Nat) :
    (Nat.blt d (Nat.pow 2 128) &&
      match ScalarInt.tryFromUInt (BitVec.ofNat 128 d) (toMiriSize w) with
      | .ok (some _) => true
      | .ok none => false
      | .error _ => false) =
    Nat.blt d (Nat.pow 2 w.bitWidth) := by
  have h_match :
      (match ScalarInt.tryFromUInt (BitVec.ofNat 128 d) (toMiriSize w) with
      | .ok (some _) => true
      | .ok none => false
      | .error _ => false) =
      (match ScalarInt.tryFromUInt (BitVec.ofNat 128 d) (toMiriSize w) with
      | .ok (some _) => true
      | _ => false) := by
    cases ScalarInt.tryFromUInt (BitVec.ofNat 128 d) (toMiriSize w) with
    | error _ => rfl
    | ok o => cases o <;> rfl
  rw [h_match,
    @match_tryFromUInt_eq Bool w (BitVec.ofNat 128 d) (fun _ => true) false]
  cases h_u128 : Nat.blt d (Nat.pow 2 128) with
  | false =>
    cases h_mod : Nat.blt d (Nat.pow 2 w.bitWidth) with
    | false => rfl
    | true =>
      have hd_lt : d < Nat.pow 2 128 :=
        Nat.lt_of_lt_of_le (nat_lt_of_blt_eq_true h_mod)
          (intWidth_modulus_le_u128 w)
      have h_true : Nat.blt d (Nat.pow 2 128) = true :=
        Nat.ble_eq_true_of_le hd_lt
      rw [h_true] at h_u128
      cases h_u128
  | true =>
    have hd_u128 : d < Nat.pow 2 128 := nat_lt_of_blt_eq_true h_u128
    have h_btonat : (BitVec.ofNat 128 d).toNat = d := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hd_u128
    cases h_mod : Nat.blt d (Nat.pow 2 w.bitWidth) with
    | true =>
      have hd_mod : d < Nat.pow 2 w.bitWidth := nat_lt_of_blt_eq_true h_mod
      have h_eq : truncateBits w (BitVec.ofNat 128 d) = BitVec.ofNat 128 d := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_truncateBits, h_btonat]
        exact Nat.mod_eq_of_lt hd_mod
      have h_bne :
          (truncateBits w (BitVec.ofNat 128 d) != BitVec.ofNat 128 d) =
            false := by
        rw [h_eq]
        exact bne_self_eq_false (BitVec.ofNat 128 d)
      rw [h_bne]
      rfl
    | false =>
      have h_ne : truncateBits w (BitVec.ofNat 128 d) ≠ BitVec.ofNat 128 d := by
        intro h_eq
        have h_tn : (truncateBits w (BitVec.ofNat 128 d)).toNat =
            (BitVec.ofNat 128 d).toNat := congrArg BitVec.toNat h_eq
        rw [toNat_truncateBits, h_btonat] at h_tn
        have hd_lt : d < Nat.pow 2 w.bitWidth := by
          rw [← h_tn]
          exact Nat.mod_lt d (intWidth_modulus_pos w)
        have h_true : Nat.blt d (Nat.pow 2 w.bitWidth) = true :=
          Nat.ble_eq_true_of_le hd_lt
        rw [h_true] at h_mod
        cases h_mod
      have h_bne :
          (truncateBits w (BitVec.ofNat 128 d) != BitVec.ofNat 128 d) =
            true := by
        cases h_b : (truncateBits w (BitVec.ofNat 128 d) == BitVec.ofNat 128 d)
        · change
            (!(truncateBits w (BitVec.ofNat 128 d) == BitVec.ofNat 128 d)) =
              true
          rw [h_b]
          rfl
        · exact False.elim (h_ne (eq_of_beq h_b))
      rw [h_bne]
      rfl

theorem list_all_congr_eq {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x, f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [List.all]
    rw [h x, ih]

theorem bool_and_congr {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (a₁ && b₁) = (a₂ && b₂) := by
  rw [ha, hb]

theorem refEnumAdmitted_eq (ety : EnumTy) :
    refEnumAdmitted ety = enumAdmitted ety := by
  have h_bnds :
      ety.discriminants.all (fun d =>
        Nat.blt d (Nat.pow 2 128) &&
          match ScalarInt.tryFromUInt (BitVec.ofNat 128 d)
              (toMiriSize ety.discrWidth) with
          | .ok (some _) => true
          | .ok none => false
          | .error _ => false) =
      ety.discriminants.all
        (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) :=
    list_all_congr_eq ety.discriminants _ _
      (refEnumDiscrInBounds_eq ety.discrWidth)
  have h_tag :
      (match ety.tagRepr with
      | .zeroSized => Nat.beq ety.discriminants.length 1
      | .scalar tagW tagS =>
        ety.discriminants.all (fun d =>
          let dBits := BitVec.ofNat 128 d
          match (toMiriSize tagW).truncate dBits with
          | .ok truncTag =>
            match refMiriTagToDiscrBits tagW tagS ety.discrWidth truncTag with
            | some recovered => recovered == dBits
            | none => false
          | .error _ => false)) =
      (match ety.tagRepr with
      | .zeroSized => Nat.beq ety.discriminants.length 1
      | .scalar tagW tagS =>
        ety.discriminants.all (fun d =>
          let dBits := BitVec.ofNat 128 d
          tagBitsToDiscrBits tagW tagS ety.discrWidth
            (truncateBits tagW dBits) == dBits)) := by
    cases ety.tagRepr with
    | zeroSized => rfl
    | scalar tagW tagS =>
      apply list_all_congr_eq
      intro d
      dsimp only
      rw [size_truncate_eq]
      dsimp only
      rw [refMiriTagToDiscrBits_eq]
  exact bool_and_congr
    (bool_and_congr (bool_and_congr rfl h_bnds)
      (refNatListPairwiseNe_eq ety.discriminants))
    h_tag

theorem refIsZstEnumTy_eq (ety : EnumTy) :
    refIsZstEnumTy ety = isZstEnumTy ety := by
  unfold refIsZstEnumTy isZstEnumTy
  cases ety.tagRepr with
  | zeroSized => exact refEnumAdmitted_eq ety
  | scalar _ _ => rfl

mutual
  theorem refIsSupportedLocalTy_eq : ∀ (ty : MirTy),
      refIsSupportedLocalTy ty = isSupportedScalarOrUnitTy ty
    | .bool | .int _ _ | .unit | .never | .ref _ _ | .rawPtr _ _
    | .unsupported => rfl
    | .enum ety => by
      dsimp only [refIsSupportedLocalTy, isSupportedScalarOrUnitTy]
      exact refEnumAdmitted_eq ety
    | .tuple fields => by
      dsimp only [refIsSupportedLocalTy, isSupportedScalarOrUnitTy]
      rw [refAreSupportedFieldTys_eq fields]

  theorem refAreSupportedFieldTys_eq : ∀ (tys : List MirTy),
      refAreSupportedFieldTys tys = areSupportedFieldTys tys
    | [] => rfl
    | ty :: tys => by
      dsimp only [refAreSupportedFieldTys, areSupportedFieldTys]
      rw [refIsSupportedLocalTy_eq ty, refAreSupportedFieldTys_eq tys]
end

theorem refIsPrimitiveReadableTy_eq (ty : MirTy) :
    refIsPrimitiveReadableTy ty = isPrimitiveReadableTy ty := by
  cases ty <;> rfl

mutual
  theorem refUninitSlotVal_eq : ∀ (ty : MirTy),
      refUninitSlotVal ty = uninitSlotVal ty
    | .bool | .int _ _ | .unit | .never | .ref _ _ | .rawPtr _ _
    | .unsupported => rfl
    | .enum ety => by
      dsimp only [refUninitSlotVal, uninitSlotVal]
      rw [refIsZstEnumTy_eq]
    | .tuple fields => by
      dsimp only [refUninitSlotVal, uninitSlotVal]
      rw [refUninitSlotVals_eq fields]

  theorem refUninitSlotVals_eq : ∀ (tys : List MirTy),
      refUninitSlotVals tys = uninitSlotVals tys
    | [] => rfl
    | ty :: tys => by
      dsimp only [refUninitSlotVals, uninitSlotVals]
      rw [refUninitSlotVal_eq ty, refUninitSlotVals_eq tys]
end

theorem refLiveUninitSlot_eq (ty : MirTy) :
    refLiveUninitSlot ty = liveUninitSlot ty := by
  dsimp only [refLiveUninitSlot, liveUninitSlot]
  rw [refUninitSlotVal_eq]

theorem fullRange_contains_truncateBits (w : IntWidth) (raw : BitVec 128) :
    match WrappingRange.full (toMiriSize w) with
    | .ok range => range.contains (truncateBits w raw) = true
    | .error _ => False := by
  have h_lt : (truncateBits w raw).toNat < Nat.pow 2 w.bitWidth := by
    rw [toNat_truncateBits]
    exact Nat.mod_lt raw.toNat (intWidth_modulus_pos w)
  cases w <;> (
    dsimp only [toMiriSize, WrappingRange.full, WrappingRange.contains]
    change
      (if (0 : BitVec 128).toNat ≤ (BitVec.ofNat 128 (_ - 1)).toNat then
        decide ((0 : BitVec 128).toNat ≤ (truncateBits _ raw).toNat) &&
          decide ((truncateBits _ raw).toNat ≤ (BitVec.ofNat 128 (_ - 1)).toNat)
      else _) = true
    have h_max : (truncateBits _ raw).toNat ≤ _ - 1 :=
      Nat.le_sub_one_of_lt h_lt
    simp only [BitVec.toNat_ofNat]
    exact decide_eq_true (by
      exact Nat.le_trans h_max (by decide)))

noncomputable def fullRangeOf (w : IntWidth) : WrappingRange :=
  match WrappingRange.full (toMiriSize w) with
  | .ok r => r
  | .error _ => ⟨0, 0⟩

theorem fullRangeOf_contains_truncateBits (w : IntWidth) (raw : BitVec 128) :
    (fullRangeOf w).contains (truncateBits w raw) = true := by
  have h := fullRange_contains_truncateBits w raw
  cases w <;> exact h

theorem findDiscrVariantAux_lt {idx : Nat} {discrBits : BitVec 128}
    {ds : List Nat} {v : Nat}
    (h : findDiscrVariantAux idx discrBits ds = some v) :
    v < idx + ds.length := by
  induction ds generalizing idx with
  | nil => cases h
  | cons d rest ih =>
    dsimp only [findDiscrVariantAux] at h
    cases h_eq : (BitVec.ofNat 128 d == discrBits) <;> rw [h_eq] at h
    · have h_sub := ih h
      dsimp only [List.length]
      have h_arith : idx + 1 + rest.length = idx + (rest.length + 1) :=
        Nat.add_right_comm idx 1 rest.length
      rw [← h_arith]
      exact h_sub
    · injection h with hv
      subst hv
      dsimp only [List.length]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos rest.length)

theorem findDiscrVariant?_lt {discrBits : BitVec 128} {ds : List Nat} {v : Nat}
    (h : findDiscrVariant? discrBits ds = some v) :
    v < ds.length := by
  have h0 := findDiscrVariantAux_lt h
  rw [Nat.zero_add] at h0
  exact h0

private theorem list_get_map_const {α β : Type} (xs : List α) (c : β) (i : Nat)
    (hi : i < (xs.map (fun _ => c)).length) :
    (xs.map (fun _ => c)).get ⟨i, hi⟩ = c := by
  induction xs generalizing i with
  | nil => cases hi
  | cons _ rest ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j (Nat.lt_of_succ_lt_succ hi)

theorem array_map_inhabited_getElem?_uninhabited (ds : List Nat) (v : Nat)
    (hv : v < ds.length) :
    Option.getD
      ((Array.mk (ds.map (fun _ => refInhabitedVariantLayout)))[v]?.map
        VariantLayout.uninhabited) true = false := by
  dsimp only [Array.size, GetElem?.getElem?, Array.instGetElem?NatLtSize,
    decidableGetElem?, GetElem.getElem, Array.instGetElemNatLtSize,
    Array.getInternal]
  have hv' : v < (ds.map (fun _ => refInhabitedVariantLayout)).length := by
    rw [List.length_map]
    exact hv
  rw [dite_eq_left hv']
  dsimp only [Option.map, Option.getD]
  rw [list_get_map_const ds refInhabitedVariantLayout v hv']
  rfl

theorem truncateFromUInt_eq_miriScalar (w : IntWidth) (raw : BitVec 128) :
    ScalarInt.truncateFromUInt raw (toMiriSize w) =
      .ok (miriScalar w raw, truncateBits w raw != raw) := by
  have h : ScalarInt.truncateFromUInt raw (toMiriSize w) =
      match (toMiriSize w).truncate raw with
      | .ok b => .ok (miriScalar w raw, b != raw)
      | .error e => .error (.sizeError e) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

theorem miriScalar_data (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).data = truncateBits w bits := by
  have h : (miriScalar w bits).data =
      match (toMiriSize w).truncate bits with
      | .ok b => b
      | .error _ => bits := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

private noncomputable def runDirectTagFinal (S : Type) (uninhabited : Bool)
    (v : Nat) : Miri.Interpreter.RvalueM S Nat :=
  let jp := fun (_ : Unit) => (Pure.pure v : Miri.Interpreter.RvalueM S Nat)
  if uninhabited then
    Bind.bind
      (throw (.undefinedBehavior
        (toString "UninhabitedEnumVariantRead(" ++ toString v ++ toString ")")))
      jp
  else
    jp ()

private noncomputable def runDirectTagAfterLookup (S : Type) (ety₀ : EnumTy)
    (optIdx : Option Nat) : Miri.Interpreter.RvalueM S Nat :=
  Bind.bind
    (fun s' => .ok optIdx s' : Miri.Interpreter.RvalueM S (Option Nat))
    (fun opt =>
      match opt with
      | some index =>
        runDirectTagFinal S
          ((refEnumLayoutData ety₀).isVariantUninhabited index) index
      | _ =>
        throw (.undefinedBehavior "InvalidTag(no declared discriminant)"))

private noncomputable def runDirectTagAfterTrunc (S : Type) (ety₀ : EnumTy)
    (truncRes : Except SizeError (BitVec 128)) :
    Miri.Interpreter.RvalueM S Nat :=
  let jp := fun (discrBits : BitVec 128) =>
    runDirectTagAfterLookup S ety₀
      (refFindDiscrVariant? discrBits ety₀.discriminants)
  match truncRes with
  | .ok v => Bind.bind (Pure.pure v) jp
  | .error e => Bind.bind (throw (.invalidProgram (toString e))) jp

private noncomputable def runDirectTagAfterSignExt (S : Type) (ety₀ : EnumTy)
    (discrW : IntWidth) (extRes : Except SizeError Int) :
    Miri.Interpreter.RvalueM S Nat :=
  let jpExt := fun (extended : BitVec 128) =>
    runDirectTagAfterTrunc S ety₀ ((toMiriSize discrW).truncate extended)
  let jpInt := fun (integer : Int) =>
    Bind.bind (Pure.pure (BitVec.ofInt 128 integer)) jpExt
  match extRes with
  | .ok v => Bind.bind (Pure.pure v) jpInt
  | .error e => Bind.bind (throw (.invalidProgram (toString e))) jpInt

private noncomputable def runDirectTagAction (S : Type) (ety₀ : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (discrW : IntWidth)
    (inRange : Bool) (b₀ : BitVec 128) : Miri.Interpreter.RvalueM S Nat :=
  let jpRange := fun (_ : Unit) =>
    let jpExt := fun (extended : BitVec 128) =>
      runDirectTagAfterTrunc S ety₀ ((toMiriSize discrW).truncate extended)
    if tagS then
      let jpInt := fun (integer : Int) =>
        Bind.bind (Pure.pure (BitVec.ofInt 128 integer)) jpExt
      match (toMiriSize tagW).signExtend b₀ with
      | .ok v => Bind.bind (Pure.pure v) jpInt
      | .error e => Bind.bind (throw (.invalidProgram (toString e))) jpInt
    else
      Bind.bind (Pure.pure b₀) jpExt
  if !inRange then
    Bind.bind (throw (.undefinedBehavior "InvalidTag(outside valid range)"))
      jpRange
  else
    jpRange ()

theorem readDiscriminant_enum_scalar_eq (S : Type)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool) (raw : BitVec 128) (s : S)
    (h_tr : ety.tagRepr = .scalar tagW tagS) :
    Miri.Interpreter.runRvalue
      (Miri.Interpreter.Discriminant.readDiscriminant
        (refDiscriminantHooks S ety) ()
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW raw))),
          ⟨0, refEnumLayoutData ety⟩⟩) s =
    match findDiscrVariant?
        (tagBitsToDiscrBits tagW tagS ety.discrWidth (truncateBits tagW raw))
        ety.discriminants with
    | some v => (s, .ok v)
    | none =>
      (s, .error (.undefinedBehavior
        "InvalidTag(no declared discriminant)")) := by
  cases ety with
  | mk id discrW discrS tr ds =>
    dsimp only at h_tr
    subst h_tr
    let ety₀ := EnumTy.mk id discrW discrS (.scalar tagW tagS) ds
    have h_step :
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.Discriminant.readDiscriminant
            (refDiscriminantHooks S ety₀) ()
            ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW raw))),
              ⟨0, refEnumLayoutData ety₀⟩⟩) s =
        Miri.Interpreter.runRvalue
          (runDirectTagAction S ety₀ tagW tagS discrW
            ((fullRangeOf tagW).contains (miriScalar tagW raw).data)
            (miriScalar tagW raw).data) s := by
      cases tagW <;> cases tagS <;> cases discrW <;> rfl
    rw [h_step, miriScalar_data, fullRangeOf_contains_truncateBits]
    cases tagS with
    | false =>
      have h₁ :
          Miri.Interpreter.runRvalue
            (runDirectTagAction S ety₀ tagW false discrW true
              (truncateBits tagW raw)) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterTrunc S ety₀
              ((toMiriSize discrW).truncate (truncateBits tagW raw))) s := rfl
      rw [h₁, size_truncate_eq]
      have h₂ :
          Miri.Interpreter.runRvalue
            (runDirectTagAfterTrunc S ety₀
              (.ok (truncateBits discrW (truncateBits tagW raw)))) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterLookup S ety₀
              (refFindDiscrVariant?
                (truncateBits discrW (truncateBits tagW raw)) ds)) s := rfl
      rw [h₂, refFindDiscrVariant?_eq]
      dsimp only [tagBitsToDiscrBits]
      rw [ite_false_eq_true, truncateBits_idem]
      cases h_f : findDiscrVariant?
          (truncateBits discrW (truncateBits tagW raw)) ds with
      | none => rfl
      | some v =>
        have h₃ :
            Miri.Interpreter.runRvalue
              (runDirectTagAfterLookup S ety₀ (some v)) s =
            Miri.Interpreter.runRvalue
              (runDirectTagFinal S
                ((refEnumLayoutData ety₀).isVariantUninhabited v) v) s := rfl
        rw [h₃]
        dsimp only [ety₀, LayoutData.isVariantUninhabited, refEnumLayoutData]
        rw [array_map_inhabited_getElem?_uninhabited ds v
          (findDiscrVariant?_lt h_f)]
        rfl
    | true =>
      have h₁ :
          Miri.Interpreter.runRvalue
            (runDirectTagAction S ety₀ tagW true discrW true
              (truncateBits tagW raw)) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterSignExt S ety₀ discrW
              ((toMiriSize tagW).signExtend (truncateBits tagW raw))) s := rfl
      rw [h₁, size_signExtend_eq]
      have h₂ :
          Miri.Interpreter.runRvalue
            (runDirectTagAfterSignExt S ety₀ discrW
              (.ok (signExtendBits tagW (truncateBits tagW raw)))) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterTrunc S ety₀
              ((toMiriSize discrW).truncate
                (BitVec.ofInt 128
                  (signExtendBits tagW (truncateBits tagW raw))))) s := rfl
      rw [h₂, bitVec_ofInt_eq, size_truncate_eq]
      have h₃ :
          Miri.Interpreter.runRvalue
            (runDirectTagAfterTrunc S ety₀
              (.ok (truncateBits discrW
                (bvOfInt 128
                  (signExtendBits tagW (truncateBits tagW raw)))))) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterLookup S ety₀
              (refFindDiscrVariant?
                (truncateBits discrW
                  (bvOfInt 128
                    (signExtendBits tagW (truncateBits tagW raw))))
                ds)) s := rfl
      rw [h₃, refFindDiscrVariant?_eq]
      dsimp only [tagBitsToDiscrBits]
      rw [ite_true_eq_true]
      cases h_f : findDiscrVariant?
          (truncateBits discrW
            (bvOfInt 128 (signExtendBits tagW (truncateBits tagW raw)))) ds with
      | none => rfl
      | some v =>
        have h₄ :
            Miri.Interpreter.runRvalue
              (runDirectTagAfterLookup S ety₀ (some v)) s =
            Miri.Interpreter.runRvalue
              (runDirectTagFinal S
                ((refEnumLayoutData ety₀).isVariantUninhabited v) v) s := rfl
        rw [h₄]
        dsimp only [ety₀, LayoutData.isVariantUninhabited, refEnumLayoutData]
        rw [array_map_inhabited_getElem?_uninhabited ds v
          (findDiscrVariant?_lt h_f)]
        rfl

private theorem match_readDiscr_eq_runRvalue {α : Type}
    (m : Miri.Interpreter.RvalueM Unit Nat)
    (onOk : Nat → α) (onUb onErr : α) :
    (match m () with
    | .ok v _ => onOk v
    | .error (.undefinedBehavior _) _ => onUb
    | .error _ _ => onErr) =
    (match (Miri.Interpreter.runRvalue m ()).2 with
    | .ok v => onOk v
    | .error (.undefinedBehavior _) => onUb
    | .error _ => onErr) := by
  dsimp only [Miri.Interpreter.runRvalue]
  cases m () with
  | ok _ _ => rfl
  | error e _ => cases e <;> rfl

theorem evalRefConstLit_eq (ty : MirTy) (lit : ConstLit) :
    evalRefConstLit ty lit = evalConstLit ty lit := by
  cases ty with
  | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases lit <;> rfl
  | int w s =>
    cases lit with
    | zeroSized => rfl
    | scalar bits =>
      dsimp only [evalRefConstLit, evalConstLit]
      exact @match_tryFromUInt_eq (Except FaultKind Val) w bits
        (fun d => .ok (.scalar ⟨w, s, d⟩)) (.error .unsupported)
  | bool =>
    cases lit with
    | zeroSized => rfl
    | scalar bits =>
      dsimp only [evalRefConstLit, evalConstLit]
      exact @match_tryFromUInt_tryToBool_eq (Except FaultKind Val) bits
        (fun b => .ok (.bool b)) (.error .undefined) (.error .unsupported)
  | enum ety =>
    cases lit with
    | zeroSized =>
      dsimp only [evalRefConstLit, evalConstLit]
      rw [refIsZstEnumTy_eq]
    | scalar bits =>
      have h_unfold :
          evalRefConstLit (.enum ety) (.scalar bits) =
            match ety.tagRepr with
            | .zeroSized => .error .unsupported
            | .scalar tagW _ =>
              if !refEnumAdmitted ety then
                .error .unsupported
              else
                match ScalarInt.tryFromUInt bits (toMiriSize tagW) with
                | .ok (some sc) =>
                  let op : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
                    ⟨.immediate (.scalar (.fromScalarInt sc)),
                      ⟨0, refEnumLayoutData ety⟩⟩
                  match (Miri.Interpreter.runRvalue
                      (Miri.Interpreter.Discriminant.readDiscriminant
                        (refDiscriminantHooks Unit ety) () op) ()).2 with
                  | .ok v => .ok (.enumVal ety v)
                  | .error (.undefinedBehavior _) => .error .undefined
                  | .error _ => .error .unsupported
                | _ => .error .unsupported := by
        cases ety with
        | mk id dw ds tr discrs =>
          cases tr with
          | zeroSized => rfl
          | scalar tw ts =>
            let ety' : EnumTy := ⟨id, dw, ds, .scalar tw ts, discrs⟩
            dsimp only [evalRefConstLit]
            cases refEnumAdmitted ety' with
            | false => rfl
            | true =>
              rw [Bool.not_true, ite_false_eq_true, ite_false_eq_true]
              cases ScalarInt.tryFromUInt bits (toMiriSize tw) with
              | error _ => rfl
              | ok optSc =>
                cases optSc with
                | none => rfl
                | some sc =>
                  dsimp only
                  exact @match_readDiscr_eq_runRvalue (Except FaultKind Val)
                    (Miri.Interpreter.Discriminant.readDiscriminant
                      (refDiscriminantHooks Unit ety') ()
                      ⟨.immediate (.scalar (.fromScalarInt sc)),
                        ⟨0, refEnumLayoutData ety'⟩⟩)
                    (fun v => .ok (.enumVal ety' v))
                    (.error .undefined)
                    (.error .unsupported)
      rw [h_unfold]
      dsimp only [evalConstLit]
      cases h_tr : ety.tagRepr with
      | zeroSized => rfl
      | scalar tagW tagS =>
        dsimp only
        rw [refEnumAdmitted_eq]
        cases h_adm : enumAdmitted ety with
        | false => rfl
        | true =>
          rw [Bool.not_true, ite_false_eq_true, Bool.false_or]
          rw [tryFromUInt_eq_truncateFromUInt,
              truncateFromUInt_eq_miriScalar tagW bits]
          dsimp only [bind, Except.bind, pure, Except.pure]
          cases h_ov : (truncateBits tagW bits != bits) with
          | true => rfl
          | false =>
            rw [ite_false_eq_true]
            dsimp only
            rw [readDiscriminant_enum_scalar_eq Unit ety tagW tagS bits
              () h_tr]
            rw [truncateBits_eq_of_beq_false h_ov]
            cases findDiscrVariant?
                (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
                ety.discriminants <;> rfl

theorem checkRefVal_int_aux (b : Bool) (vw w : IntWidth) (vs s : Bool) :
    (if (!b) = true then false else IntWidth.beq vw w && (vs == s)) =
    (match if b = true then some (MirTy.int vw vs) else none with
    | some vTy => MirTy.beq vTy (MirTy.int w s)
    | none => false) := by
  cases b <;> rfl

mutual
  theorem checkRefVal_eq : ∀ (v : Val) (ty : MirTy),
      checkRefVal v ty = checkVal v ty
    | .unit, ty => by cases ty <;> rfl
    | .ptr _, ty => by cases ty <;> rfl
    | .bytes _, ty => by cases ty <;> rfl
    | .bool b, ty => by cases ty <;> cases b <;> rfl
    | .enumVal ety v, ty => by
      cases ty with
      | enum ety' =>
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        rw [refEnumAdmitted_eq]
        cases (enumAdmitted ety && Nat.blt v ety.discriminants.length) <;> rfl
      | _ =>
        dsimp only [checkRefVal, checkVal, Val.ty?]
        cases (enumAdmitted ety && Nat.blt v ety.discriminants.length) <;> rfl
    | .scalar sv, ty => by
      cases sv with
      | mk vw vs vbits =>
        cases ty with
        | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
        | unsupported =>
          dsimp only [checkRefVal, checkVal, Val.ty?]
          cases (ScalarVal.wf ⟨vw, vs, vbits⟩) <;> rfl
        | int w s =>
          have h_m :
              (match ScalarInt.tryFromUInt vbits (toMiriSize vw) with
              | .ok (some _) => IntWidth.beq vw w && (vs == s)
              | _ => false) =
              if truncateBits vw vbits != vbits then false
              else IntWidth.beq vw w && (vs == s) :=
            @match_tryFromUInt_eq Bool vw vbits
              (fun _ => IntWidth.beq vw w && (vs == s)) false
          exact h_m.trans
            (checkRefVal_int_aux (truncateBits vw vbits == vbits) vw w vs s)
    | .tuple fields, ty => by
      cases ty with
      | tuple fieldTys =>
        dsimp only [checkRefVal, checkVal, Val.ty?]
        rw [checkRefVals_eq fields fieldTys]
        cases fields.isEmpty with
        | true => rfl
        | false => cases Val.tys? fields <;> rfl
      | _ =>
        dsimp only [checkRefVal, checkVal, Val.ty?]
        cases fields.isEmpty with
        | true => rfl
        | false => cases Val.tys? fields <;> rfl

  theorem checkRefVals_eq : ∀ (vs : List Val) (tys : List MirTy),
      checkRefVals vs tys =
        (match Val.tys? vs with
        | some vTys => MirTy.beqList vTys tys
        | none => false)
    | [], [] => rfl
    | [], _ :: _ => rfl
    | v :: vs, [] => by
      dsimp only [checkRefVals, Val.tys?]
      cases Val.ty? v <;> cases Val.tys? vs <;> rfl
    | v :: vs, ty :: tys => by
      dsimp only [checkRefVals, Val.tys?]
      rw [checkRefVal_eq v ty, checkRefVals_eq vs tys]
      dsimp only [checkVal]
      cases Val.ty? v with
      | none => rfl
      | some vt =>
        cases Val.tys? vs with
        | none => exact Bool.and_false _
        | some vts => rfl
end

theorem checkRefArgsMatch_eq (vs : List Val) (tys : List MirTy) :
    checkRefArgsMatch vs tys = checkArgsMatch vs tys := by
  induction vs generalizing tys with
  | nil => cases tys <;> rfl
  | cons v rest ih =>
    cases tys with
    | nil => rfl
    | cons ty tys' =>
      dsimp only [checkRefArgsMatch, checkArgsMatch]
      rw [checkRefVal_eq, ih]

theorem bitVec128_ofNat_toNat (bits : BitVec 128) :
    BitVec.ofNat 128 bits.toNat = bits := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt bits.isLt

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem bvToInt_inj {n : Nat} {u v : BitVec n}
    (h : bvToInt u = bvToInt v) : u = v := by
  dsimp only [bvToInt] at h
  cases hu : decide (2 * u.toNat < Nat.pow 2 n) <;>
    cases hv : decide (2 * v.toNat < Nat.pow 2 n)
  · rw [ite_eq_right (of_decide_eq_false hu),
      ite_eq_right (of_decide_eq_false hv)] at h
    have h_add := congrArg (fun z : Int => z + Int.ofNat (Nat.pow 2 n)) h
    rw [Int.sub_add_cancel, Int.sub_add_cancel] at h_add
    exact BitVec.eq_of_toNat_eq (Int.ofNat.inj h_add)
  · rw [ite_eq_right (of_decide_eq_false hu),
      ite_eq_left (of_decide_eq_true hv)] at h
    have h_add := congrArg (fun z : Int => z + Int.ofNat (Nat.pow 2 n)) h
    rw [Int.sub_add_cancel] at h_add
    change Int.ofNat u.toNat = Int.ofNat (v.toNat + Nat.pow 2 n) at h_add
    have h_nat : u.toNat = v.toNat + Nat.pow 2 n := Int.ofNat.inj h_add
    have h_lt : Nat.pow 2 n < Nat.pow 2 n :=
      Nat.lt_of_le_of_lt (Nat.le_add_left (Nat.pow 2 n) v.toNat)
        (h_nat ▸ u.isLt)
    exact False.elim (Nat.lt_irrefl _ h_lt)
  · rw [ite_eq_left (of_decide_eq_true hu),
      ite_eq_right (of_decide_eq_false hv)] at h
    have h_add := congrArg (fun z : Int => z + Int.ofNat (Nat.pow 2 n)) h
    rw [Int.sub_add_cancel] at h_add
    change Int.ofNat (u.toNat + Nat.pow 2 n) = Int.ofNat v.toNat at h_add
    have h_nat : u.toNat + Nat.pow 2 n = v.toNat := Int.ofNat.inj h_add
    have h_lt : Nat.pow 2 n < Nat.pow 2 n :=
      Nat.lt_of_le_of_lt (Nat.le_add_left (Nat.pow 2 n) u.toNat)
        (h_nat ▸ v.isLt)
    exact False.elim (Nat.lt_irrefl _ h_lt)
  · rw [ite_eq_left (of_decide_eq_true hu),
      ite_eq_left (of_decide_eq_true hv)] at h
    exact BitVec.eq_of_toNat_eq (Int.ofNat.inj h)

private theorem nat_sub_sub_eq_add_sub {a b c : Nat} (hbc : b ≤ c)
    (hca : c ≤ a) : a - (c - b) = (a - c) + b := by
  have h1 : a - (c - b) + (c - b) = a :=
    Nat.sub_add_cancel (Nat.le_trans (Nat.sub_le c b) hca)
  have h2 : (a - c) + b + (c - b) = a := by
    rw [Nat.add_assoc, Nat.add_comm b (c - b), Nat.sub_add_cancel hbc,
      Nat.sub_add_cancel hca]
  exact Nat.add_right_cancel (h1.trans h2.symm)

private theorem bvSignExtend_toNat_mod {n m : Nat} (hn : n ≤ m)
    (u : BitVec n) :
    Nat.mod (bvSignExtend m u).toNat (Nat.pow 2 n) = u.toNat := by
  have h_pow_le : Nat.pow 2 n ≤ Nat.pow 2 m :=
    Nat.pow_le_pow_right (by decide) hn
  have h_pow_mul :
      Nat.pow 2 m = Nat.pow 2 n * Nat.pow 2 (m - n) :=
    (congrArg (Nat.pow 2) (Nat.add_sub_of_le hn).symm).trans
      (Nat.pow_add 2 n (m - n))
  have h_pow_sub_pos : 1 ≤ Nat.pow 2 (m - n) :=
    Nat.one_le_pow (m - n) 2 (by decide)
  have h_sub_eq :
      Nat.pow 2 m - Nat.pow 2 n =
        Nat.pow 2 n * (Nat.pow 2 (m - n) - 1) := by
    have h_m :
        Nat.pow 2 m =
          Nat.pow 2 n * (Nat.pow 2 (m - n) - 1) + Nat.pow 2 n := by
      have h_mul :
          Nat.pow 2 n * (Nat.pow 2 (m - n) - 1) + Nat.pow 2 n =
            Nat.pow 2 n * ((Nat.pow 2 (m - n) - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [h_mul, Nat.sub_add_cancel h_pow_sub_pos]
      exact h_pow_mul
    rw [h_m, Nat.add_sub_cancel]
  dsimp only [bvSignExtend, bvOfInt, bvToInt]
  rw [BitVec.toNat_ofNat]
  cases hu : decide (2 * u.toNat < Nat.pow 2 n) with
  | true =>
    rw [ite_eq_left (of_decide_eq_true hu)]
    dsimp only [intEmod, Int.natAbs, Int.toNat]
    have h_ltm : u.toNat < Nat.pow 2 m := Nat.lt_of_lt_of_le u.isLt h_pow_le
    change Nat.mod (Nat.mod (Nat.mod u.toNat (Nat.pow 2 m)) (Nat.pow 2 m))
      (Nat.pow 2 n) = u.toNat
    rw [nat_mod_eq_of_lt h_ltm, nat_mod_eq_of_lt h_ltm]
    exact nat_mod_eq_of_lt u.isLt
  | false =>
    rw [ite_eq_right (of_decide_eq_false hu)]
    have h_sub_pos : 1 ≤ Nat.pow 2 n - u.toNat :=
      Nat.sub_pos_of_lt u.isLt
    let k := Nat.pow 2 n - u.toNat - 1
    have hk_succ : Nat.succ k = Nat.pow 2 n - u.toNat :=
      Nat.sub_add_cancel h_sub_pos
    have h_int_eq :
        Int.ofNat u.toNat - Int.ofNat (Nat.pow 2 n) = Int.negSucc k := by
      have h_add : Int.negSucc k + Int.ofNat (Nat.pow 2 n) =
          Int.ofNat u.toNat := by
        change Int.subNatNat (Nat.pow 2 n) (Nat.succ k) = Int.ofNat u.toNat
        rw [hk_succ]
        have h_le : Nat.pow 2 n - u.toNat ≤ Nat.pow 2 n := Nat.sub_le _ _
        dsimp only [Int.subNatNat]
        have h_z : (Nat.pow 2 n - u.toNat) - Nat.pow 2 n = 0 :=
          Nat.sub_eq_zero_of_le h_le
        rw [h_z]
        have h_uu : Nat.pow 2 n - (Nat.pow 2 n - u.toNat) = u.toNat :=
          Nat.sub_sub_self (Nat.le_of_lt u.isLt)
        rw [h_uu]
      exact Int.sub_eq_iff_eq_add.mpr h_add.symm
    rw [h_int_eq]
    dsimp only [intEmod, Int.natAbs]
    have hk_lt : k < Nat.pow 2 m := by
      have h1 : k < Nat.succ k := Nat.lt_succ_self k
      rw [hk_succ] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.le_trans (Nat.sub_le _ _) h_pow_le)
    rw [nat_mod_eq_of_lt hk_lt, hk_succ]
    have h_lem : Nat.pow 2 n - u.toNat ≤ Nat.pow 2 m :=
      Nat.le_trans (Nat.sub_le _ _) h_pow_le
    dsimp only [Int.subNatNat]
    rw [Nat.sub_eq_zero_of_le h_lem]
    dsimp only [Int.toNat]
    have h_lt_sub : Nat.pow 2 m - (Nat.pow 2 n - u.toNat) < Nat.pow 2 m :=
      Nat.sub_lt (Nat.pow_pos (by decide)) h_sub_pos
    change Nat.mod
      (Nat.mod (Nat.pow 2 m - (Nat.pow 2 n - u.toNat)) (Nat.pow 2 m))
      (Nat.pow 2 n) = u.toNat
    have hu_le : u.toNat ≤ Nat.pow 2 n := Nat.le_of_lt u.isLt
    rw [nat_mod_eq_of_lt h_lt_sub,
      nat_sub_sub_eq_add_sub hu_le h_pow_le, h_sub_eq]
    exact (Nat.mul_add_mod _ _ _).trans (Nat.mod_eq_of_lt u.isLt)

private theorem signExtendBits_inj (w : IntWidth) (x y : BitVec 128)
    (h : signExtendBits w (truncateBits w x) =
      signExtendBits w (truncateBits w y)) :
    truncateBits w x = truncateBits w y := by
  dsimp only [signExtendBits] at h
  have h_se := bvToInt_inj h
  have hn : w.bitWidth - 1 - 0 + 1 ≤ 128 := by cases w <;> decide
  have h_mod :=
    congrArg
      (fun z : BitVec 128 =>
        Nat.mod z.toNat (Nat.pow 2 (w.bitWidth - 1 - 0 + 1)))
      h_se
  rw [bvSignExtend_toNat_mod hn, bvSignExtend_toNat_mod hn] at h_mod
  have h_low :
      bvExtractLsb (w.bitWidth - 1) 0 (truncateBits w x) =
        bvExtractLsb (w.bitWidth - 1) 0 (truncateBits w y) :=
    BitVec.eq_of_toNat_eq h_mod
  have h_ze := congrArg (bvZeroExtend 128) h_low
  change truncateBits w (truncateBits w x) =
    truncateBits w (truncateBits w y) at h_ze
  rw [truncateBits_idem, truncateBits_idem] at h_ze
  exact h_ze

/-- Wrapping the unsigned value of a 128-bit vector back into 128 bits is the
identity. -/
theorem bvOfInt_ofNat_toNat (x : BitVec 128) :
    bvOfInt 128 (Int.ofNat x.toNat) = x := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvOfInt, intEmod]
  rw [BitVec.toNat_ofNat]
  change HMod.hMod (Nat.mod x.toNat (Nat.pow 2 128)) (HPow.hPow 2 128) =
    x.toNat
  rw [nat_mod_eq_of_lt x.isLt]
  exact Nat.mod_eq_of_lt x.isLt

/-- `Miri.Interpreter.IntegerCast.cast` from an integer source to an integer
target, with its private source decoding spelled out: a signed source is
sign-extended to 128 bits, an unsigned source is zero-extended, and the result
is truncated to the target size. -/
theorem integerCast_int_eq (sw : IntWidth) (ss : Bool) (bits : BitVec 128)
    (w : IntWidth) (s : Bool) :
    IntegerCast.cast (.integer (toMiriIntType sw ss)) (miriScalar sw bits)
        (.integer (toMiriIntType w s)) =
      bind
        (if ss then
          bind (((miriScalar sw bits).toInt (toMiriSize sw)).mapError
              IntegerCastError.scalar)
            (fun signedValue => pure (BitVec.ofInt 128 signedValue).toNat)
        else
          bind (((miriScalar sw bits).toUInt (toMiriSize sw)).mapError
              IntegerCastError.scalar)
            (fun value => pure value.toNat))
        (fun decoded =>
          bind ((ScalarInt.truncateFromUInt (BitVec.ofNat 128 decoded)
              (toMiriSize w)).mapError IntegerCastError.scalar)
            (fun (result, _) => pure result)) := by
  cases sw <;> cases ss <;> rfl

/-- `Miri.Interpreter.IntegerCast.cast` from a `bool` source to an integer
target: `false` is `0`, `true` is `1`, truncated to the target size. -/
theorem integerCast_bool_eq (b : Bool) (w : IntWidth) (s : Bool) :
    IntegerCast.cast .boolean (ScalarInt.ofBool b)
        (.integer (toMiriIntType w s)) =
      bind ((ScalarInt.truncateFromUInt
          (BitVec.ofNat 128 (if b then 1 else 0))
          (toMiriSize w)).mapError IntegerCastError.scalar)
        (fun (result, _) => pure result) := by
  cases b <;> rfl

/-- Truncating 128-bit `x` to the target size through
`Miri.Memory.ScalarInt.truncateFromUInt` yields `truncateBits w x`. -/
theorem cast_truncate_eq (w : IntWidth) (s : Bool) (x : BitVec 128) :
    (match bind ((ScalarInt.truncateFromUInt x (toMiriSize w)).mapError
          IntegerCastError.scalar)
        (fun (result, _) => pure result) with
    | .ok sc => (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .error _ => .error .unsupported) =
    .ok (.scalar ⟨w, s, truncateBits w x⟩) := by
  have h : (match bind ((ScalarInt.truncateFromUInt x (toMiriSize w)).mapError
          IntegerCastError.scalar)
        (fun (result, _) => pure result) with
      | .ok sc =>
        (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate x with
      | .ok b => .ok (.scalar ⟨w, s, b⟩)
      | .error _ => .error .unsupported) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

/-- The reference `IntToInt` cast (`Miri.Interpreter.IntegerCast.cast`) agrees
with `Trusted.MirSemantics.evalIntToIntCast`. -/
theorem evalRefMiriIntToIntCast_eq (src : Val) (castTy : MirTy) :
    evalRefMiriIntToIntCast src castTy = evalIntToIntCast src castTy := by
  cases castTy with
  | int w s =>
    cases src with
    | scalar sv =>
      cases sv with
      | mk sw ss bits =>
        dsimp only [evalRefMiriIntToIntCast, evalIntToIntCast]
        rw [integerCast_int_eq]
        cases ss with
        | true =>
          rw [miriScalar_toInt]
          change (match bind ((ScalarInt.truncateFromUInt
                (BitVec.ofNat 128 (BitVec.ofInt 128
                  (signExtendBits sw (truncateBits sw bits))).toNat)
                (toMiriSize w)).mapError IntegerCastError.scalar)
              (fun (result, _) => pure result) with
            | .ok sc =>
              (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
            | .error _ => .error .unsupported) = _
          rw [bitVec128_ofNat_toNat, cast_truncate_eq, bitVec_ofInt_eq]
          rfl
        | false =>
          rw [miriScalar_toUInt]
          change (match bind ((ScalarInt.truncateFromUInt
                (BitVec.ofNat 128 (truncateBits sw bits).toNat)
                (toMiriSize w)).mapError IntegerCastError.scalar)
              (fun (result, _) => pure result) with
            | .ok sc =>
              (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
            | .error _ => .error .unsupported) = _
          rw [bitVec128_ofNat_toNat, cast_truncate_eq]
          change Except.ok (Val.scalar ⟨w, s,
            truncateBits w (truncateBits sw bits)⟩) =
            Except.ok (Val.scalar ⟨w, s, truncateBits w
              (bvOfInt 128 (Int.ofNat (truncateBits sw bits).toNat))⟩)
          rw [bvOfInt_ofNat_toNat]
    | bool b =>
      dsimp only [evalRefMiriIntToIntCast, evalIntToIntCast]
      rw [integerCast_bool_eq]
      exact cast_truncate_eq w s _
    | unit | enumVal _ _ | ptr _ | tuple _ | bytes _ => rfl
  | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
  | unsupported => rfl

theorem decodeScalar_beq_eq (w : IntWidth) (s : Bool) (x y : BitVec 128) :
    (decodeScalar ⟨w, s, x⟩ == decodeScalar ⟨w, s, y⟩) =
      (truncateBits w x == truncateBits w y) := by
  cases h_eq : (truncateBits w x == truncateBits w y) with
  | true =>
    have h_t := eq_of_beq h_eq
    dsimp only [decodeScalar]
    rw [h_t]
    exact beq_self_eq_true _
  | false =>
    cases h_d : (decodeScalar ⟨w, s, x⟩ == decodeScalar ⟨w, s, y⟩) with
    | false => rfl
    | true =>
      have h_deq := eq_of_beq h_d
      dsimp only [decodeScalar] at h_deq
      have h_t : truncateBits w x = truncateBits w y := by
        cases s with
        | false =>
          exact BitVec.eq_of_toNat_eq (Int.ofNat.inj h_deq)
        | true =>
          exact signExtendBits_inj w x y h_deq
      rw [h_t, beq_self_eq_true] at h_eq
      cases h_eq

theorem evalRefSwitchScalarCase_eq (rp : RefProg)
    (callerMem : CallerMemory) (sv : ScalarVal) (caseBits : BitVec 128)
    (st : Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout
      Unit RefStepMachine) :
    (refTerminatorHooksFor rp callerMem).compareSwitchCase () (.scalar sv)
        caseBits.toNat st =
      (st,
        if truncateBits sv.width caseBits != caseBits then
          .error (faultToStepError .unsupported)
        else
          .ok (truncateBits sv.width sv.bits ==
            truncateBits sv.width caseBits)) := by
  dsimp only [refTerminatorHooksFor]
  rw [bitVec128_ofNat_toNat caseBits]
  apply congrArg (Prod.mk st)
  rw [evalRefConstLit_eq]
  dsimp only [evalConstLit]
  cases h_ov : (truncateBits sv.width caseBits != caseBits) with
  | true => rfl
  | false =>
    rw [ite_false_eq_true, ite_false_eq_true]
    change (match evalRefBinOp .eq (.scalar sv)
          (.scalar ⟨sv.width, sv.signed,
            truncateBits sv.width caseBits⟩) with
      | .ok (.bool eq) => Except.ok eq
      | .error k => .error (faultToStepError k)
      | .ok _ => .error (.unsupported "non-bool SwitchInt Eq result")) = _
    rw [evalRefBinOp_eq]
    dsimp only [evalBinOp]
    have h_w : IntWidth.beq sv.width sv.width = true := by
      cases sv.width <;> rfl
    rw [h_w, beq_self_eq_true]
    change Except.ok (decodeScalar sv ==
        decodeScalar ⟨sv.width, sv.signed, truncateBits sv.width caseBits⟩) = _
    rw [decodeScalar_beq_eq, truncateBits_idem]

theorem evalRefSwitchBoolCase_eq (rp : RefProg)
    (callerMem : CallerMemory) (b : Bool) (caseBits : BitVec 128)
    (st : Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout
      Unit RefStepMachine) :
    (refTerminatorHooksFor rp callerMem).compareSwitchCase () (.bool b)
        caseBits.toNat st =
      (st,
        match evalConstLit .bool (.scalar caseBits) with
        | .ok (.bool cb) => .ok (b == cb)
        | .error k => .error (faultToStepError k)
        | .ok _ => .error (faultToStepError .unsupported)) := by
  dsimp only [refTerminatorHooksFor]
  rw [bitVec128_ofNat_toNat caseBits]
  apply congrArg (Prod.mk st)
  rw [evalRefConstLit_eq]
  cases evalConstLit .bool (.scalar caseBits) with
  | error k => rfl
  | ok v =>
    cases v with
    | bool cb =>
      change (match evalRefBinOp .eq (.bool b) (.bool cb) with
        | .ok (.bool eq) => Except.ok eq
        | .error k => .error (faultToStepError k)
        | .ok _ => .error (.unsupported "non-bool SwitchInt Eq result")) = _
      rw [evalRefBinOp_eq]
      rfl
    | scalar _ | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => rfl

private theorem miriScalar_toBits (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toBits (toMiriSize w) = .ok (truncateBits w bits) := by
  have h : (miriScalar w bits).toBits (toMiriSize w) =
      ((toMiriSize w).truncate bits).mapError ScalarIntError.sizeError := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  rfl

/-- `refReadPrimitiveArgs` agrees with `readPrimitiveArgs` element by element.
-/
theorem refReadPrimitiveArgs_eq (pairs : List (MirTy × SlotVal)) :
    refReadPrimitiveArgs pairs = readPrimitiveArgs pairs := by
  induction pairs with
  | nil => rfl
  | cons p rest ih =>
    cases p with
    | mk ty sv =>
      dsimp only [refReadPrimitiveArgs, readPrimitiveArgs,
        readRefPrimitiveSlot]
      rw [refIsPrimitiveReadableTy_eq]
      cases isPrimitiveReadableTy ty with
      | false => rfl
      | true =>
        dsimp only [Bool.not, ite_false_eq_true]
        cases sv.toVal? with
        | none => rfl
        | some v =>
          dsimp only
          rw [ih]
          rfl

private theorem nat_testBit_of_lt {raw k : Nat} (h : raw < HPow.hPow 2 k) :
    Nat.testBit raw k = false := by
  dsimp only [Nat.testBit]
  rw [Nat.shiftRight_eq_zero raw k h]
  rfl

private theorem nat_div_pow_eq_one {raw k : Nat}
    (h_lo : HPow.hPow 2 k ≤ raw) (h_hi : raw < HPow.hPow 2 (k + 1)) :
    HDiv.hDiv raw (HPow.hPow 2 k) = 1 := by
  have h_pos : 0 < HPow.hPow 2 k := Nat.pow_pos (by decide)
  have h_sub_lt : raw - HPow.hPow 2 k < HPow.hPow 2 k := by
    have h_add : raw - HPow.hPow 2 k + HPow.hPow 2 k <
        HPow.hPow 2 k + HPow.hPow 2 k := by
      rw [Nat.sub_add_cancel h_lo]
      have h_pow : HPow.hPow 2 (k + 1) = HPow.hPow 2 k + HPow.hPow 2 k := by
        rw [Nat.pow_succ, Nat.mul_two]
      rw [← h_pow]
      exact h_hi
    exact Nat.lt_of_add_lt_add_right h_add
  have h_eq : raw = (raw - HPow.hPow 2 k) + 1 * HPow.hPow 2 k := by
    rw [Nat.one_mul, Nat.sub_add_cancel h_lo]
  have h_div : HDiv.hDiv raw (HPow.hPow 2 k) =
      HDiv.hDiv ((raw - HPow.hPow 2 k) + 1 * HPow.hPow 2 k) (HPow.hPow 2 k) :=
    congrArg (fun x => HDiv.hDiv x (HPow.hPow 2 k)) h_eq
  rw [h_div, Nat.add_mul_div_right _ _ h_pos, Nat.div_eq_of_lt h_sub_lt]

private theorem nat_testBit_of_range {raw k : Nat}
    (h_lo : HPow.hPow 2 k ≤ raw) (h_hi : raw < HPow.hPow 2 (k + 1)) :
    Nat.testBit raw k = true := by
  dsimp only [Nat.testBit]
  rw [Nat.shiftRight_eq_div_pow, nat_div_pow_eq_one h_lo h_hi]
  rfl

private theorem nat_log2_eq_of_range (k : Nat) :
    ∀ {raw : Nat}, HPow.hPow 2 k ≤ raw → raw < HPow.hPow 2 (k + 1) →
      Nat.log2 raw = k := by
  induction k with
  | zero =>
    intro raw h_lo h_hi
    cases raw with
    | zero => cases h_lo
    | succ r =>
      cases r with
      | zero => rfl
      | succ r' =>
        have h_lt : Nat.succ (Nat.succ r') < 2 := h_hi
        cases Nat.not_lt_zero r'
          (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h_lt))
  | succ k ih =>
    intro raw h_lo h_hi
    have h_ge2 : 2 ≤ raw := by
      have h1 : 1 ≤ HPow.hPow 2 k := Nat.one_le_pow k 2 (by decide)
      have h2 : 2 ≤ HPow.hPow 2 (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_two]
        exact Nat.add_le_add h1 h1
      exact Nat.le_trans h2 h_lo
    rw [Nat.log2_def, ite_eq_left h_ge2]
    have h_div_lo : HPow.hPow 2 k ≤ HDiv.hDiv raw 2 := by
      rw [Nat.le_div_iff_mul_le (by decide)]
      rw [← Nat.pow_succ]
      exact h_lo
    have h_div_hi : HDiv.hDiv raw 2 < HPow.hPow 2 (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      rw [← Nat.pow_succ]
      exact h_hi
    rw [ih h_div_lo h_div_hi]

private theorem countLeadingZerosNat_zero (width : Nat) :
    countLeadingZerosNat 0 width = width := by
  induction width with
  | zero => rfl
  | succ k ih =>
    change (if Nat.testBit 0 k then 0 else countLeadingZerosNat 0 k + 1) =
      k + 1
    rw [nat_testBit_of_lt (Nat.pow_pos (by decide)), ih]
    rfl

private theorem countLeadingZerosNat_pos (k : Nat) :
    ∀ {raw : Nat}, 0 < raw → raw < HPow.hPow 2 k →
      Nat.log2 raw < k ∧
        countLeadingZerosNat raw k = k - (Nat.log2 raw + 1) := by
  induction k with
  | zero =>
    intro raw h_pos h_lt
    cases raw with
    | zero => cases h_pos
    | succ r =>
      cases Nat.not_lt_zero r (Nat.lt_of_succ_lt_succ h_lt)
  | succ k ih =>
    intro raw h_pos h_lt
    cases h_cmp : decide (raw < HPow.hPow 2 k) with
    | true =>
      have h_lt_k : raw < HPow.hPow 2 k := of_decide_eq_true h_cmp
      let ⟨h_log_lt, h_clz⟩ := ih h_pos h_lt_k
      refine ⟨Nat.lt_succ_of_lt h_log_lt, ?_⟩
      change (if Nat.testBit raw k then 0
          else countLeadingZerosNat raw k + 1) = k + 1 - (Nat.log2 raw + 1)
      rw [nat_testBit_of_lt h_lt_k, h_clz]
      dsimp only [ite_false_eq_true]
      exact (Nat.sub_add_comm h_log_lt).symm
    | false =>
      have h_ge_k : HPow.hPow 2 k ≤ raw :=
        Nat.le_of_not_lt (of_decide_eq_false h_cmp)
      have h_log : Nat.log2 raw = k := nat_log2_eq_of_range k h_ge_k h_lt
      refine ⟨h_log ▸ Nat.lt_succ_self k, ?_⟩
      change (if Nat.testBit raw k then 0
          else countLeadingZerosNat raw k + 1) = k + 1 - (Nat.log2 raw + 1)
      rw [nat_testBit_of_range h_ge_k h_lt, h_log, Nat.sub_self]
      rfl

theorem countLeadingZerosNat_eq (raw width : Nat)
    (h_lt : raw < HPow.hPow 2 width) :
    (if raw == 0 then width else width - (Nat.log2 raw + 1)) =
      countLeadingZerosNat raw width := by
  cases raw with
  | zero =>
    exact (countLeadingZerosNat_zero width).symm
  | succ r =>
    have h_pos : 0 < Nat.succ r := Nat.succ_pos r
    exact (countLeadingZerosNat_pos width h_pos h_lt).2.symm

private theorem ctz_forIn_range'_eq (raw width : Nat) :
    ∀ (m : Nat), m ≤ width →
      (Option.casesOn (motive := fun _ => Nat)
        (forIn (m := Id) (List.range' (width - m) m 1)
          ((none : Option Nat), Unit.unit)
          (fun index _ =>
            if Nat.testBit raw index = true then
              pure (ForInStep.done (some index, Unit.unit))
            else
              pure (ForInStep.yield (none, Unit.unit)))).1
        width (fun r => r)) =
        (width - m) +
          @Nat.rec (fun _ => Nat) 0
            (fun k ih => if Nat.testBit raw (width - 1 - k) then 0 else ih + 1)
            m := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [List.range', List.forIn_nil]
    dsimp only [Pure.pure, Id.run]
    rw [Nat.sub_zero]
    change width = width + 0
    rw [Nat.add_zero]
  | succ m ih =>
    intro h_le
    rw [List.range', List.forIn_cons]
    have h_idx : width - (m + 1) = width - 1 - m := by
      rw [Nat.sub_sub, Nat.add_comm 1 m]
    have h_step : width - (m + 1) + 1 = width - m := by
      have h_pos : 0 < width - m := Nat.sub_pos_of_lt h_le
      rw [← Nat.sub_sub, Nat.sub_add_cancel h_pos]
    dsimp only [Bind.bind, Pure.pure, Id.run]
    rw [h_idx]
    cases h_tb : Nat.testBit raw (width - 1 - m) with
    | true =>
      simp only [ite_true, Nat.add_zero]
    | false =>
      have h_next' : width - 1 - m + 1 = width - m := by
        rw [← h_idx]
        exact h_step
      rw [h_next']
      simp only [Bool.false_eq_true, ite_false]
      dsimp only [Pure.pure, Id.run] at ih
      rw [ih (Nat.le_of_succ_le h_le)]
      rw [← h_next', Nat.add_assoc, Nat.add_comm 1]

private theorem integerIntrinsic_ctlz_eq (w : IntWidth) (s : Bool)
    (bits : BitVec 128) :
    (match IntegerIntrinsic.run .ctlz (miriScalar w bits)
        (toMiriIntType w s) (toMiriIntType .i32 false) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨.i32, false, sc.data⟩) : Except FaultKind Val)
    | .error _ => .error .unsupported) =
      .ok (.scalar ⟨.i32, false,
        truncateBits .i32 (BitVec.ofNat 128
          (if (truncateBits w bits).toNat == 0 then w.bitWidth
           else w.bitWidth - (Nat.log2 (truncateBits w bits).toNat + 1)))⟩) := by
  dsimp only [IntegerIntrinsic.run, bind, Except.bind, pure, Except.pure,
    Except.mapError]
  rw [toMiriIntType_size, miriScalar_toBits]
  have h_w : (toMiriSize w).bits = .ok (UInt64.ofNat w.bitWidth) := by
    cases w <;> rfl
  have h_toNat : (UInt64.ofNat w.bitWidth).toNat = w.bitWidth := by
    cases w <;> rfl
  have h_nz :
      (IntegerIntrinsic.ctlz == .cttzNonzero ||
        IntegerIntrinsic.ctlz == .ctlzNonzero) = false := rfl
  dsimp only
  rw [h_w]
  dsimp only
  rw [h_toNat, toMiriIntType_size, h_nz]
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  cases ((truncateBits w bits).toNat == 0) with
  | true =>
    simp only [ite_true]
    rw [truncateFromUInt_eq_miriScalar]
    dsimp only
    rw [miriScalar_data]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [truncateFromUInt_eq_miriScalar]
    dsimp only
    rw [miriScalar_data]

private theorem integerIntrinsic_cttz_eq (w : IntWidth) (s : Bool)
    (bits : BitVec 128) :
    (match IntegerIntrinsic.run .cttz (miriScalar w bits)
        (toMiriIntType w s) (toMiriIntType .i32 false) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨.i32, false, sc.data⟩) : Except FaultKind Val)
    | .error _ => .error .unsupported) =
      .ok (.scalar ⟨.i32, false,
        truncateBits .i32 (BitVec.ofNat 128
          (countTrailingZerosNat (truncateBits w bits).toNat w.bitWidth))⟩) := by
  dsimp only [IntegerIntrinsic.run, bind, Except.bind, pure, Except.pure,
    Except.mapError]
  rw [toMiriIntType_size, miriScalar_toBits]
  have h_w : (toMiriSize w).bits = .ok (UInt64.ofNat w.bitWidth) := by
    cases w <;> rfl
  have h_toNat : (UInt64.ofNat w.bitWidth).toNat = w.bitWidth := by
    cases w <;> rfl
  have h_nz :
      (IntegerIntrinsic.cttz == .cttzNonzero ||
        IntegerIntrinsic.cttz == .ctlzNonzero) = false := rfl
  dsimp only
  rw [h_w]
  dsimp only
  rw [h_toNat, toMiriIntType_size, h_nz]
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  rw [truncateFromUInt_eq_miriScalar]
  dsimp only
  rw [miriScalar_data]
  change Except.ok (Val.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128
    (Break.runK.match_1 (motive := fun _ => Id Nat)
      (forIn (m := Id) (Std.Legacy.Range.mk 0 w.bitWidth 1 (by decide))
        ((none : Option Nat), Unit.unit)
        (fun index _ =>
          if Nat.testBit (truncateBits w bits).toNat index = true then
            pure (ForInStep.done (some index, Unit.unit))
          else
            pure (ForInStep.yield (none, Unit.unit)))).1
      (fun r => pure r) (fun _ => pure w.bitWidth)))⟩) = _
  have h_brk : ∀ (opt : Option Nat),
      Break.runK.match_1 (motive := fun _ => Id Nat) opt
        (fun r => pure r) (fun _ => pure w.bitWidth) =
        Option.casesOn (motive := fun _ => Nat) opt w.bitWidth (fun r => r) := by
    intro opt; cases opt <;> rfl
  rw [h_brk]
  dsimp only [Pure.pure, Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size,
    Std.Legacy.Range.step]
  have h_sz : HDiv.hDiv (w.bitWidth - 0 + 1 - 1) 1 = w.bitWidth := by
    cases w <;> rfl
  rw [h_sz]
  have h_ctz := ctz_forIn_range'_eq (truncateBits w bits).toNat w.bitWidth
    w.bitWidth (Nat.le_refl w.bitWidth)
  rw [Nat.sub_self, Nat.zero_add] at h_ctz
  dsimp only [Pure.pure, Id.run] at h_ctz
  exact congrArg
    (fun n => (Except.ok (Val.scalar ⟨.i32, false,
      truncateBits .i32 (BitVec.ofNat 128 n)⟩) : Except FaultKind Val))
    h_ctz

private theorem intWidth_modulus_eq_pow (w : IntWidth) :
    Nat.pow 2 w.bitWidth = HPow.hPow 2 w.bitWidth := by
  cases w <;> rfl

private theorem truncateBits_toNat_lt_pow (w : IntWidth) (bits : BitVec 128) :
    (truncateBits w bits).toNat < HPow.hPow 2 w.bitWidth := by
  rw [toNat_truncateBits, ← intWidth_modulus_eq_pow]
  exact Nat.mod_lt bits.toNat (intWidth_modulus_pos w)

private theorem saturatingArith_clamp_eq (isAdd : Bool) (w : IntWidth)
    (s : Bool) (lBits : BitVec 128) :
    (match
      (if (toMiriIntType w s).signed then
        bind ((IntegerOps.decode (miriIntValue ⟨w, s, lBits⟩)).mapError
            IntegerArithmeticIntrinsicError.integerOperation)
          (fun first =>
            if first ≥ 0 then
              bind (((toMiriIntType w s).size.signedIntMax).mapError
                  (fun e => .scalar (.sizeError e)))
                (fun maximum =>
                  bind ((ScalarInt.truncateFromInt maximum
                      (toMiriIntType w s).size).mapError .scalar)
                    (fun p => pure p.1))
            else
              bind (((toMiriIntType w s).size.signedIntMin).mapError
                  (fun e => .scalar (.sizeError e)))
                (fun minimum =>
                  bind ((ScalarInt.truncateFromInt minimum
                      (toMiriIntType w s).size).mapError .scalar)
                    (fun p => pure p.1)))
      else if (if isAdd then IntegerSaturatingOp.add else .sub) == .add then
        bind (((toMiriIntType w s).size.unsignedIntMax).mapError
            (fun e => .scalar (.sizeError e)))
          (fun maximum =>
            bind ((ScalarInt.truncateFromUInt maximum
                (toMiriIntType w s).size).mapError .scalar)
              (fun p => pure p.1))
      else
        (ScalarInt.null (toMiriIntType w s).size).mapError .scalar) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .error _ => .error .unsupported) =
      .ok (.scalar ⟨w, s,
        if s then
          if decide (decodeScalar ⟨w, s, lBits⟩ ≥ 0) then
            BitVec.ofNat 128 (Nat.pow 2 (w.bitWidth - 1) - 1)
          else
            BitVec.ofNat 128 (Nat.pow 2 (w.bitWidth - 1))
        else if isAdd then
          BitVec.ofNat 128 (Nat.pow 2 w.bitWidth - 1)
        else
          BitVec.ofNat 128 0⟩) := by
  rw [toMiriIntType_signed, toMiriIntType_size]
  cases s with
  | true =>
    rw [integerOps_decode_eq]
    dsimp only [bind, Except.bind, pure, Except.pure, Except.mapError]
    cases h_ge : decide (decodeScalar ⟨w, true, lBits⟩ ≥ 0) with
    | true =>
      rw [ite_eq_left (of_decide_eq_true h_ge)]
      cases w <;> rfl
    | false =>
      rw [ite_eq_right (of_decide_eq_false h_ge)]
      cases w <;> rfl
  | false =>
    cases isAdd <;> cases w <;> rfl

private theorem truncateScalar_ne_undefined (w : IntWidth) (s : Bool) (v : Int) :
    truncateScalar w s v ≠ .error .undefined := by
  unfold truncateScalar
  cases s with
  | false => intro h; cases h
  | true =>
    dsimp only
    cases (decide (bvToInt (bvOfInt 128 v) < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (bvToInt (bvOfInt 128 v) ≥ HPow.hPow (2 : Int) 127)) <;>
      (intro h; cases h)

private theorem evalOverflowingArithOp_addSub_ne_undefined (isAdd : Bool)
    (w : IntWidth) (s : Bool) (a b : Int) :
    evalOverflowingArithOp (if isAdd then .addWithOverflow else .subWithOverflow)
        w s a b ≠ .error .undefined := by
  intro h
  cases isAdd with
  | true =>
    simp only [ite_true] at h
    dsimp only [evalOverflowingArithOp] at h
    cases h_ts : truncateScalar w s (a + b) with
    | ok p => rw [h_ts] at h; cases h
    | error k =>
      rw [h_ts] at h
      injection h with hk
      subst hk
      exact truncateScalar_ne_undefined w s (a + b) h_ts
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    dsimp only [evalOverflowingArithOp] at h
    cases h_ts : truncateScalar w s (a - b) with
    | ok p => rw [h_ts] at h; cases h
    | error k =>
      rw [h_ts] at h
      injection h with hk
      subst hk
      exact truncateScalar_ne_undefined w s (a - b) h_ts

private theorem evalRefSaturatingOp_eq (isAdd : Bool) (l r : ScalarVal) :
    (match IntegerArithmeticIntrinsic.saturatingArith
        (if isAdd then .add else .sub) (miriIntValue l) (miriIntValue r) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨l.width, l.signed, sc.data⟩) :
        Except FaultKind Val)
    | .error _ => .error .unsupported) =
      evalSaturatingOp isAdd (.scalar l) (.scalar r) := by
  cases l with
  | mk w₁ s₁ bits₁ =>
    cases r with
    | mk w₂ s₂ bits₂ =>
      let op : BinOp := if isAdd then .addWithOverflow else .subWithOverflow
      have h_bin_eq :
          evalRefBinOp op (.scalar ⟨w₁, s₁, bits₁⟩) (.scalar ⟨w₂, s₂, bits₂⟩) =
            evalBinOp op (.scalar ⟨w₁, s₁, bits₁⟩) (.scalar ⟨w₂, s₂, bits₂⟩) :=
        evalRefBinOp_eq op _ _
      cases h_ty : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) with
      | false =>
        have h_bne :=
          miriIntValue_type_bne_of_false w₁ w₂ s₁ s₂ bits₁ bits₂ h_ty
        dsimp only [evalSaturatingOp, IntegerArithmeticIntrinsic.saturatingArith]
        rw [h_ty]
        cases isAdd <;> (
          dsimp only [IntegerOps.binary, bind, Except.bind, Except.mapError]
          rw [integerOps_decode_eq, integerOps_decode_eq]
          dsimp only [bind, Except.bind, pure, Except.pure]
          rw [h_bne]
          rfl)
      | true =>
        let ⟨hw, hs⟩ := eq_of_intWidth_beq_and_signed h_ty
        subst hw; subst hs
        have h_ovf_case :
            (match IntegerOps.binary (toMiriBinOp op)
                (miriIntValue ⟨w₁, s₁, bits₁⟩)
                (miriIntValue ⟨w₁, s₁, bits₂⟩) with
            | .ok (.withOverflow sc overflow) =>
              (Except.ok (Val.tuple
                [.scalar ⟨w₁, s₁, sc.data⟩, .bool overflow]) :
                Except FaultKind Val)
            | .ok _ => .error .unsupported
            | .error (.undefinedBehavior _) => .error .undefined
            | .error _ => .error .unsupported) =
              evalOverflowingArithOp op w₁ s₁
                (decodeScalar ⟨w₁, s₁, bits₁⟩)
                (decodeScalar ⟨w₁, s₁, bits₂⟩) := by
          dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp] at h_bin_eq
          rw [h_ty] at h_bin_eq
          have h_not_sh : op.isShift = false := by cases isAdd <;> rfl
          rw [h_not_sh] at h_bin_eq
          cases isAdd <;> exact h_bin_eq
        cases isAdd with
        | true =>
          dsimp only [evalSaturatingOp,
            IntegerArithmeticIntrinsic.saturatingArith, op] at h_ovf_case
          dsimp only [evalSaturatingOp,
            IntegerArithmeticIntrinsic.saturatingArith, op]
          simp only [ite_true] at h_ovf_case
          simp only [ite_true]
          dsimp only [toMiriBinOp] at h_ovf_case
          rw [h_ty]
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          dsimp only [bind, Except.bind, pure, Except.pure, Except.mapError]
          cases h_res : IntegerOps.binary .AddWithOverflow
              (miriIntValue ⟨w₁, s₁, bits₁⟩)
              (miriIntValue ⟨w₁, s₁, bits₂⟩) with
          | error e =>
            rw [h_res] at h_ovf_case
            cases e with
            | undefinedBehavior _ =>
              exact False.elim
                (evalOverflowingArithOp_addSub_ne_undefined true w₁ s₁
                  (decodeScalar ⟨w₁, s₁, bits₁⟩)
                  (decodeScalar ⟨w₁, s₁, bits₂⟩) h_ovf_case.symm)
            | scalar _ | asymmetricTypes _ _
            | invalidBinaryOperator _ | invalidUnaryOperator _ _ =>
              rw [← h_ovf_case]
          | ok ir =>
            rw [h_res] at h_ovf_case
            cases ir with
            | scalar _ | boolean _ | ordering _ =>
              rw [← h_ovf_case]
              rfl
            | withOverflow sc ovf =>
              rw [← h_ovf_case]
              cases ovf with
              | false => rfl
              | true =>
                have h_clamp := saturatingArith_clamp_eq true w₁ s₁ bits₁
                simp only [ite_true] at h_clamp
                dsimp only [bind, Except.bind, pure, Except.pure,
                  Except.mapError] at h_clamp
                exact h_clamp
        | false =>
          dsimp only [evalSaturatingOp,
            IntegerArithmeticIntrinsic.saturatingArith, op] at h_ovf_case
          dsimp only [evalSaturatingOp,
            IntegerArithmeticIntrinsic.saturatingArith, op]
          simp only [Bool.false_eq_true, ite_false] at h_ovf_case
          simp only [Bool.false_eq_true, ite_false]
          dsimp only [toMiriBinOp] at h_ovf_case
          rw [h_ty]
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          dsimp only [bind, Except.bind, pure, Except.pure, Except.mapError]
          cases h_res : IntegerOps.binary .SubWithOverflow
              (miriIntValue ⟨w₁, s₁, bits₁⟩)
              (miriIntValue ⟨w₁, s₁, bits₂⟩) with
          | error e =>
            rw [h_res] at h_ovf_case
            cases e with
            | undefinedBehavior _ =>
              exact False.elim
                (evalOverflowingArithOp_addSub_ne_undefined false w₁ s₁
                  (decodeScalar ⟨w₁, s₁, bits₁⟩)
                  (decodeScalar ⟨w₁, s₁, bits₂⟩) h_ovf_case.symm)
            | scalar _ | asymmetricTypes _ _
            | invalidBinaryOperator _ | invalidUnaryOperator _ _ =>
              rw [← h_ovf_case]
          | ok ir =>
            rw [h_res] at h_ovf_case
            cases ir with
            | scalar _ | boolean _ | ordering _ =>
              rw [← h_ovf_case]
              rfl
            | withOverflow sc ovf =>
              rw [← h_ovf_case]
              cases ovf with
              | false => rfl
              | true =>
                have h_clamp := saturatingArith_clamp_eq false w₁ s₁ bits₁
                simp only [Bool.false_eq_true, ite_false] at h_clamp
                dsimp only [bind, Except.bind, pure, Except.pure,
                  Except.mapError] at h_clamp
                exact h_clamp

private theorem int_ofNat_beq_zero (n : Nat) :
    (Int.ofNat n == (0 : Int)) = Nat.beq n 0 := by
  cases n <;> rfl

private theorem int_ofNat_beq_ofNat_zero (n : Nat) :
    (Int.ofNat n == Int.ofNat 0) = Nat.beq n 0 := by
  cases n <;> rfl

private theorem evalRefIsMultipleOf_eq (w : IntWidth) (b₁ b₂ : BitVec 128) :
    (let zero : Val := .scalar ⟨w, false, BitVec.ofNat 128 0⟩
     match evalRefMiriBinOp .Eq (.scalar ⟨w, false, b₂⟩) zero with
     | .ok (.bool true) => evalRefMiriBinOp .Eq (.scalar ⟨w, false, b₁⟩) zero
     | .ok (.bool false) =>
       match evalRefMiriBinOp .Rem (.scalar ⟨w, false, b₁⟩)
           (.scalar ⟨w, false, b₂⟩) with
       | .ok remVal => evalRefMiriBinOp .Eq remVal zero
       | .error k => .error k
     | .error k => .error k
     | .ok _ => .error .unsupported) =
      (let lNat := (truncateBits w b₁).toNat
       let rNat := (truncateBits w b₂).toNat
       if Nat.beq rNat 0 then
         .ok (.bool (Nat.beq lNat 0))
       else
         .ok (.bool (Nat.beq (Nat.mod lNat rNat) 0))) := by
  have h_w : IntWidth.beq w w = true := IntWidth.beq_refl w
  have h_z0 : (truncateBits w (BitVec.ofNat 128 0)).toNat = 0 := by
    cases w <;> rfl
  have h_eq_zero : ∀ b : BitVec 128,
      evalRefMiriBinOp .Eq (.scalar ⟨w, false, b⟩)
          (.scalar ⟨w, false, BitVec.ofNat 128 0⟩) =
        .ok (.bool (Nat.beq (truncateBits w b).toNat 0)) := by
    intro b
    have h := evalRefBinOp_eq .eq (.scalar ⟨w, false, b⟩)
      (.scalar ⟨w, false, BitVec.ofNat 128 0⟩)
    dsimp only [evalRefBinOp, toMiriBinOp, evalBinOp, BinOp.isShift,
      decodeScalar] at h
    rw [h_w, h_z0] at h
    simp only [Bool.false_eq_true, ite_false, Bool.and_true, beq_self_eq_true,
      Bool.not_true] at h
    rw [int_ofNat_beq_ofNat_zero] at h
    exact h
  dsimp only
  rw [h_eq_zero b₂]
  cases h_r0 : Nat.beq (truncateBits w b₂).toNat 0 with
  | true => exact h_eq_zero b₁
  | false =>
    have h_rem := evalRefBinOp_eq .rem (.scalar ⟨w, false, b₁⟩)
      (.scalar ⟨w, false, b₂⟩)
    dsimp only [evalRefBinOp, toMiriBinOp, evalBinOp, BinOp.isShift,
      evalArithOp, decodeScalar] at h_rem
    rw [h_w] at h_rem
    simp only [Bool.false_eq_true, ite_false, Bool.and_true, beq_self_eq_true,
      Bool.not_true, Bool.true_and, Bool.false_and] at h_rem
    rw [int_ofNat_beq_zero, h_r0] at h_rem
    simp only [Bool.false_eq_true, ite_false, BinOp.isUnchecked, Bool.and_false,
      intTmod, truncateScalar, bvOfInt, intEmod, Int.natAbs, Int.toNat] at h_rem
    rw [h_rem]
    dsimp only
    rw [h_eq_zero]
    have h_mod_lt_w :
        Nat.mod (truncateBits w b₁).toNat (truncateBits w b₂).toNat <
          Nat.pow 2 w.bitWidth := by
      have h_pos : 0 < (truncateBits w b₂).toNat := by
        cases h_n : (truncateBits w b₂).toNat with
        | zero => rw [h_n] at h_r0; cases h_r0
        | succ _ => exact Nat.succ_pos _
      rw [intWidth_modulus_eq_pow]
      exact Nat.lt_trans (Nat.mod_lt _ h_pos) (truncateBits_toNat_lt_pow w b₂)
    have h_mod_lt_128 :
        Nat.mod (truncateBits w b₁).toNat (truncateBits w b₂).toNat <
          Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le h_mod_lt_w (intWidth_modulus_le_u128 w)
    have h_trunc_mod :
        (truncateBits w (truncateBits w (BitVec.ofNat 128
          (Nat.mod (Nat.mod (truncateBits w b₁).toNat (truncateBits w b₂).toNat)
            (Nat.pow 2 128))))).toNat =
          Nat.mod (truncateBits w b₁).toNat (truncateBits w b₂).toNat := by
      rw [truncateBits_idem, toNat_truncateBits, BitVec.toNat_ofNat]
      change HMod.hMod
        (HMod.hMod
          (HMod.hMod (Nat.mod (truncateBits w b₁).toNat (truncateBits w b₂).toNat)
            (Nat.pow 2 128))
          (Nat.pow 2 128))
        (Nat.pow 2 w.bitWidth) = _
      rw [Nat.mod_eq_of_lt h_mod_lt_128, Nat.mod_eq_of_lt h_mod_lt_128,
        Nat.mod_eq_of_lt h_mod_lt_w]
    simp only [Bool.false_eq_true, ite_false]
    rw [h_trunc_mod]

/-- The reference `CoreBuiltin` evaluator (`evalRefCoreBuiltin`) agrees with
`Trusted.MirSemantics.evalCoreBuiltin` across all 15 builtins and all argument
lists. -/
theorem evalRefCoreBuiltin_eq (builtin : CoreBuiltin) (args : List Val) :
    evalRefCoreBuiltin builtin args = evalCoreBuiltin builtin args := by
  cases builtin with
  | wrappingAdd =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | nil => exact evalRefBinOp_eq .add (.scalar l) (.scalar r)
            | cons _ _ => rfl
          | _ => rfl
      | _ => rfl
  | wrappingSub =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | nil => exact evalRefBinOp_eq .sub (.scalar l) (.scalar r)
            | cons _ _ => rfl
          | _ => rfl
      | _ => rfl
  | wrappingMul =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | nil => exact evalRefBinOp_eq .mul (.scalar l) (.scalar r)
            | cons _ _ => rfl
          | _ => rfl
      | _ => rfl
  | wrappingShl =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | cons _ _ => rfl
            | nil =>
              dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
              cases (IntWidth.beq r.width .i32 && !r.signed) with
              | false => rfl
              | true => exact evalRefBinOp_eq .shl (.scalar l) (.scalar r)
          | _ => rfl
      | _ => rfl
  | wrappingShr =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | cons _ _ => rfl
            | nil =>
              dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
              cases (IntWidth.beq r.width .i32 && !r.signed) with
              | false => rfl
              | true => exact evalRefBinOp_eq .shr (.scalar l) (.scalar r)
          | _ => rfl
      | _ => rfl
  | overflowingAdd =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | nil => exact evalRefBinOp_eq .addWithOverflow (.scalar l) (.scalar r)
            | cons _ _ => rfl
          | _ => rfl
      | _ => rfl
  | overflowingSub =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | nil => exact evalRefBinOp_eq .subWithOverflow (.scalar l) (.scalar r)
            | cons _ _ => rfl
          | _ => rfl
      | _ => rfl
  | overflowingMul =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | nil => exact evalRefBinOp_eq .mulWithOverflow (.scalar l) (.scalar r)
            | cons _ _ => rfl
          | _ => rfl
      | _ => rfl
  | saturatingAdd =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => cases a <;> rfl
      | cons b rest' =>
        cases rest' with
        | cons _ _ => cases a <;> cases b <;> rfl
        | nil =>
          cases a with
          | scalar l =>
            cases b with
            | scalar r => exact evalRefSaturatingOp_eq true l r
            | _ => rfl
          | _ => rfl
  | saturatingSub =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => cases a <;> rfl
      | cons b rest' =>
        cases rest' with
        | cons _ _ => cases a <;> cases b <;> rfl
        | nil =>
          cases a with
          | scalar l =>
            cases b with
            | scalar r => exact evalRefSaturatingOp_eq false l r
            | _ => rfl
          | _ => rfl
  | leadingZeros =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar sv =>
        cases rest with
        | cons _ _ => rfl
        | nil =>
          cases sv with
          | mk w s bits =>
            dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
            have h_clz := integerIntrinsic_ctlz_eq w s bits
            rw [countLeadingZerosNat_eq _ _ (truncateBits_toNat_lt_pow w bits)]
              at h_clz
            exact h_clz
      | _ => rfl
  | trailingZeros =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar sv =>
        cases rest with
        | cons _ _ => rfl
        | nil =>
          cases sv with
          | mk w s bits =>
            dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
            exact integerIntrinsic_cttz_eq w s bits
      | _ => rfl
  | isMultipleOf =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | cons _ _ => rfl
            | nil =>
              cases l with
              | mk w₁ s₁ b₁ =>
                cases r with
                | mk w₂ s₂ b₂ =>
                  dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
                  cases s₁ with
                  | true => rfl
                  | false =>
                    cases s₂ with
                    | true => rfl
                    | false =>
                      cases h_w : IntWidth.beq w₁ w₂ with
                      | false => rfl
                      | true =>
                        have hw := IntWidth.eq_of_beq h_w
                        subst hw
                        dsimp only [Bool.false_or, Bool.not, ite_false_eq_true]
                        exact evalRefIsMultipleOf_eq w₁ b₁ b₂
          | _ => rfl
      | _ => rfl
  | cmpMin =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | cons _ _ => rfl
            | nil =>
              dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
              have h_le := evalRefBinOp_eq .le (.scalar l) (.scalar r)
              simp only [evalRefBinOp, toMiriBinOp, evalBinOp, BinOp.isShift,
                Bool.false_eq_true, ite_false] at h_le
              rw [h_le]
              cases (IntWidth.beq l.width r.width && (l.signed == r.signed)) with
              | false => rfl
              | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases decide (decodeScalar l ≤ decodeScalar r) with
                | true => simp only [ite_true, miriScalar_data]
                | false =>
                  simp only [Bool.false_eq_true, ite_false, miriScalar_data]
          | _ => rfl
      | _ => rfl
  | cmpMax =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar l =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          cases b with
          | scalar r =>
            cases rest' with
            | cons _ _ => rfl
            | nil =>
              dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
              have h_ge := evalRefBinOp_eq .ge (.scalar l) (.scalar r)
              simp only [evalRefBinOp, toMiriBinOp, evalBinOp, BinOp.isShift,
                Bool.false_eq_true, ite_false] at h_ge
              rw [h_ge]
              cases (IntWidth.beq l.width r.width && (l.signed == r.signed)) with
              | false => rfl
              | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases decide (decodeScalar l ≥ decodeScalar r) with
                | true => simp only [ite_true, miriScalar_data]
                | false =>
                  simp only [Bool.false_eq_true, ite_false, miriScalar_data]
          | _ => rfl
      | _ => rfl

end MiriEquiv

end Anneal.MirCorrespondenceBase
