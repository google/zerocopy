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
   `projectTy?`, `readPlaceSlotPath?`, and `writePlaceSlotPath?` over decoded
   projection.

Per-step simulation (`evalRefStep_eq`), end-to-end correspondence
(`anneal_corresponds_to_miri`, `reachesResult_fault_iff_refReachesOutcome`,
`miri_move_deinit_wiring_claim_holds`), and non-vacuity canaries (`D6`–`D24`)
are proved in `Anneal.MirCorrespondenceProof`.
-/

theorem Bool.false_eq_true : (false = true) = False :=
  propext ⟨fun h => Bool.noConfusion h, False.elim⟩

theorem ite_false_eq_true {α : Sort u} (a b : α) :
    (if false = true then a else b) = b := rfl

theorem ite_true_eq_true {α : Sort u} (a b : α) :
    (if true = true then a else b) = a := rfl

theorem nat_blt_eq_true_of_lt {a b : Nat} (h : a < b) :
    Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

theorem bool_eq_false_of_not_eq_true {b : Bool} (h : (!b) = true) :
    b = false := by
  cases hb : b with
  | false => rfl
  | true => rw [hb] at h; cases h

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
    EnumTagRepr.beq r r = true :=
  Anneal.MirWp.EnumTagRepr.beq_iff.mpr rfl

theorem EnumTagRepr.eq_of_beq {r₁ r₂ : EnumTagRepr}
    (h : EnumTagRepr.beq r₁ r₂ = true) : r₁ = r₂ :=
  Anneal.MirWp.EnumTagRepr.beq_iff.mp h

theorem StructTy.beq_refl (s : StructTy) : StructTy.beq s s = true :=
  Anneal.MirWp.StructTy.beq_iff.mpr rfl

theorem StructTy.eq_of_beq {a b : StructTy}
    (h : StructTy.beq a b = true) : a = b :=
  Anneal.MirWp.StructTy.beq_iff.mp h

theorem EnumTy.beq_refl (e : EnumTy) : EnumTy.beq e e = true :=
  Anneal.MirWp.EnumTy.beq_iff.mpr rfl

theorem EnumTy.eq_of_beq {a b : EnumTy}
    (h : EnumTy.beq a b = true) : a = b :=
  Anneal.MirWp.EnumTy.beq_iff.mp h

theorem MirTy.beq_refl (t : MirTy) : MirTy.beq t t = true :=
  Anneal.MirWp.MirTy.beq_iff.mpr rfl

theorem MirTy.beqList_refl (ts : List MirTy) : MirTy.beqList ts ts = true :=
  Anneal.MirWp.MirTy.beqList_iff.mpr rfl

theorem MirTy.eq_of_beq {a b : MirTy} (h : MirTy.beq a b = true) : a = b :=
  Anneal.MirWp.MirTy.beq_iff.mp h

theorem MirTy.eq_of_beqList {xs ys : List MirTy}
    (h : MirTy.beqList xs ys = true) : xs = ys :=
  Anneal.MirWp.MirTy.beqList_iff.mp h

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
  | aggregate _ _ | repeat_ _ _ | cast _ _ _ | unsupported =>
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
  | aggregate _ _ | repeat_ _ _ | cast _ _ _ | unsupported =>
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
  | setDiscriminant _ _ | storageLive _ | storageDead _ | nop | unsupported =>
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
    | adtStruct sty =>
      cases sty with
      | mk id fs =>
        dsimp only [collectTy]
        let ⟨h_sub_fs, _⟩ := collectTyList_spec acc fs
        exact ⟨SubTable.trans h_sub_fs
            (subTable_insertTy (.adtStruct ⟨id, fs⟩) (collectTyList acc fs)),
          fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | enum ety =>
      cases ety with
      | mk id dw ds tr d vf =>
        dsimp only [collectTy]
        have h_sub_vf := collectTyListList_spec acc vf
        exact ⟨SubTable.trans h_sub_vf
            (subTable_insertTy (.enum ⟨id, dw, ds, tr, d, vf⟩)
              (collectTyListList acc vf)),
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
    | array elemTy len =>
      dsimp only [collectTy]
      let ⟨h_sub_e, _⟩ := collectTy_spec acc elemTy
      exact ⟨SubTable.trans h_sub_e
          (subTable_insertTy (.array elemTy len) (collectTy acc elemTy)),
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

  theorem collectTyListList_spec (acc : List MirTy)
      (vss : List (List MirTy)) :
      SubTable acc (collectTyListList acc vss) := by
    cases vss with
    | nil =>
      dsimp only [collectTyListList]
      exact SubTable.refl acc
    | cons fs fss =>
      dsimp only [collectTyListList]
      let ⟨h_sub₁, _⟩ := collectTyList_spec acc fs
      exact SubTable.trans h_sub₁
        (collectTyListList_spec (collectTyList acc fs) fss)
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
  | deref | downcast _ | index _ | constantIndex _ _ _ | unsupported =>
    exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
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

theorem collectAggregateKind_spec (acc : List MirTy) (kind : AggregateKind) :
    SubTable acc (collectAggregateKind acc kind) ∧
    (∀ ts, SubTable (collectAggregateKind acc kind) ts →
      decodeAggregateKind ts (encodeAggregateKind ts kind) = some kind) := by
  cases kind with
  | tuple => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | adtStruct sty =>
    let ⟨h_sub, h_dec⟩ := collectTy_spec acc (.adtStruct sty)
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeAggregateKind, decodeAggregateKind]
    rw [h_dec ts h_s]
  | adtEnum ety v =>
    let ⟨h_sub, h_dec⟩ := collectTy_spec acc (.enum ety)
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeAggregateKind, decodeAggregateKind]
    rw [h_dec ts h_s]
  | array elemTy =>
    let ⟨h_sub, h_dec⟩ := collectTy_spec acc elemTy
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeAggregateKind, decodeAggregateKind]
    rw [h_dec ts h_s]
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
  | aggregate kind ops =>
    let ⟨h_sub₁, h_dec₁⟩ := collectAggregateKind_spec acc kind
    let ⟨h_sub₂, h_dec₂⟩ := foldl_collect_mapOption_spec collectOperand
      encodeOperand decodeOperand collectOperand_spec
      (collectAggregateKind acc kind) ops
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl
  | repeat_ op count =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc op
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
  | setDiscriminant p v =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeStmt, decodeStmt]
    rw [h_dec ts h_s]
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
    | adtStruct sty =>
      cases sty with
      | mk id fs =>
        dsimp only [collectTy]
        exact typesAreCanonical_insertTy (.adtStruct ⟨id, fs⟩)
          (collectTyList acc fs) (collectTyList_canonical acc fs h)
    | enum ety =>
      cases ety with
      | mk id dw ds tr d vf =>
        dsimp only [collectTy]
        exact typesAreCanonical_insertTy (.enum ⟨id, dw, ds, tr, d, vf⟩)
          (collectTyListList acc vf) (collectTyListList_canonical acc vf h)
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
    | array elemTy len =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.array elemTy len)
        (collectTy acc elemTy) (collectTy_canonical acc elemTy h)

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

  theorem collectTyListList_canonical (acc : List MirTy)
      (vss : List (List MirTy)) (h : typesAreCanonical acc = true) :
      typesAreCanonical (collectTyListList acc vss) = true := by
    cases vss with
    | nil =>
      dsimp only [collectTyListList]
      exact h
    | cons fs fss =>
      dsimp only [collectTyListList]
      exact collectTyListList_canonical (collectTyList acc fs) fss
        (collectTyList_canonical acc fs h)
end

theorem collectProjElem_canonical (acc : List MirTy) (e : ProjectionElem)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectProjElem acc e) = true := by
  cases e with
  | deref | downcast _ | index _ | constantIndex _ _ _ | unsupported => exact h
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

theorem collectAggregateKind_canonical (acc : List MirTy) (kind : AggregateKind)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectAggregateKind acc kind) = true := by
  cases kind with
  | tuple => exact h
  | adtStruct sty => exact collectTy_canonical acc (.adtStruct sty) h
  | adtEnum ety _ => exact collectTy_canonical acc (.enum ety) h
  | array elemTy => exact collectTy_canonical acc elemTy h

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
  | aggregate kind ops =>
    exact foldl_preserve (fun ts => typesAreCanonical ts = true) collectOperand
      collectOperand_canonical ops (collectAggregateKind_canonical acc kind h)
  | repeat_ op _ => exact collectOperand_canonical acc op h
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
  | setDiscriminant p _ => exact collectPlace_canonical acc p h
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
          rw [h_pt] at h
          dsimp only at h
          cases h_res : resolveProjPath bodyLocals locals (.ty localTy)
              place.projection with
          | error _ => rw [h_res] at h; cases h
          | ok resolvedProj =>
            rw [h_res] at h
            dsimp only at h
            cases h_rd :
                readPlaceSlotPath? (.ty localTy) root resolvedProj with
            | none => rw [h_rd] at h; cases h
            | some psv =>
              rw [h_rd] at h
              cases isMove with
              | false =>
                injection h with h_tup
                injection h_tup with _ h_rest
                injection h_rest with _ h_loc
                subst h_loc
                rfl
              | true =>
                dsimp only at h
                cases h_w : writePlaceSlotPath? (.ty localTy) root resolvedProj
                    (uninitSlotVal pty) with
                | none => rw [h_w] at h; cases h
                | some root' =>
                  rw [h_w] at h
                  dsimp only at h
                  cases h_set :
                      MirSemantics.setElem? locals place.localId
                        (.live root') <;>
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
    cases h_pl : evalPlaceOperand bodyLocals locals place false with
    | error _ => rw [h_pl] at h; cases h
    | ok res =>
      let ⟨srcTy, sv₀, l₁⟩ := res
      rw [h_pl] at h
      cases srcTy with
      | enum ety =>
        dsimp only at h
        cases h_adm : enumAdmitted ety <;> rw [h_adm] at h
        · cases h
        · cases h_rd : evalReadDiscriminantVariant ety sv₀ with
          | error _ => rw [h_rd] at h; cases h
          | ok varIdx =>
            rw [h_rd] at h
            dsimp only at h
            cases h_d : MirSemantics.getElem? ety.discriminants varIdx <;>
              rw [h_d] at h
            · cases h
            · injection h with h_tup
              injection h_tup with _ h_loc
              subst h_loc
              exact evalPlaceOperand_length h_pl
      | _ => cases h
  | aggregate _ _ => cases h
  | repeat_ opnd count =>
    dsimp only [evalRvalue] at h
    cases dstTy with
    | array elemTy len =>
      dsimp only at h
      cases h_c : (!Nat.beq count len || !Nat.blt len (Nat.pow 2 64)) <;>
        rw [h_c] at h
      · cases h_op : evalOperandToSlot bodyLocals locals opnd with
        | error _ => rw [h_op] at h; cases h
        | ok res =>
          let ⟨srcTy, sv, l₁⟩ := res
          rw [h_op] at h
          dsimp only at h
          cases h_ty : MirTy.beq srcTy elemTy <;> rw [h_ty] at h
          · cases h
          · cases h_z : Nat.beq count 0 <;> rw [h_z] at h
            · cases h_v : sv.toVal? <;> rw [h_v] at h
              · cases h
              · injection h with h_tup
                injection h_tup with _ h_loc
                subst h_loc
                exact evalOperandToSlot_length h_op
            · injection h with h_tup
              injection h_tup with _ h_loc
              subst h_loc
              exact evalOperandToSlot_length h_op
      · cases h
    | _ => cases h
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

theorem writePlaceWithLocalTy_length {localTy : MirTy}
    {locals locals' : List LocalSlot} {dst : Place} {dstTy : MirTy} {val : Val}
    (h : writePlaceWithLocalTy localTy locals dst dstTy val = .ok locals') :
    locals'.length = locals.length := by
  unfold writePlaceWithLocalTy at h
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
        cases h_w : writePlaceSlotPath? (.ty localTy) root dst.projection
            val.toSlotVal with
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

private noncomputable def setDiscrNextFields? (ety : EnumTy) (variantIdx : Nat)
    (varFields : List MirTy) : SlotVal → Option (List SlotVal)
  | .uninit => some (uninitSlotVals varFields)
  | .enumUntagged ety' v' fs =>
    if EnumTy.beq ety ety' && Nat.beq v' variantIdx then some fs else none
  | .enumVal ety' v' fs =>
    if !EnumTy.beq ety ety' then
      none
    else if Nat.beq v' variantIdx then
      some fs
    else
      some (uninitSlotVals varFields)
  | _ => none

private noncomputable def setDiscrTagCheck (ety : EnumTy) (variantIdx : Nat)
    (curSv : SlotVal) : Except FaultKind Unit :=
  match ety.tagRepr with
  | .zeroSized =>
    if Nat.beq variantIdx 0 then .ok () else .error .undefined
  | .single v₀ =>
    if Nat.beq variantIdx v₀ then .ok () else .error .undefined
  | .scalar _ _ => .ok ()
  | .niche _ _ _ _ _ untagged start last _ =>
    if Nat.beq variantIdx untagged then
      match evalReadDiscriminantVariant ety curSv with
      | .error k => .error k
      | .ok actual =>
        if Nat.beq actual variantIdx then .ok () else .error .undefined
    else if Nat.ble start variantIdx && Nat.ble variantIdx last then
      .ok ()
    else
      .error .unsupported

theorem evalSetDiscriminantResolved_length {localTy : MirTy}
    {locals locals' : List LocalSlot} {resolvedDst : Place} {dstTy : MirTy}
    {variantIdx : Nat}
    (h : evalSetDiscriminantResolved localTy locals resolvedDst dstTy
      variantIdx = .ok locals') :
    locals'.length = locals.length := by
  unfold evalSetDiscriminantResolved at h
  cases dstTy with
  | enum ety =>
    dsimp only at h
    cases h_adm : enumAdmitted ety <;> rw [h_adm] at h
    · cases h
    · cases h_uninh : isVariantUninhabited ety variantIdx <;>
        rw [h_uninh] at h
      · cases h_get : MirSemantics.getElem? locals resolvedDst.localId with
        | none => rw [h_get] at h; cases h
        | some slot =>
          rw [h_get] at h
          cases slot with
          | dead => cases h
          | live root =>
            dsimp only [Bool.not_true] at h
            cases h_rd : readPlaceSlotPath? (.ty localTy) root
                resolvedDst.projection with
            | none => rw [h_rd] at h; cases h
            | some curSv =>
              cases h_fv : fieldsForVariant? ety variantIdx with
              | none => rw [h_rd, h_fv] at h; cases h
              | some varFields =>
                rw [h_rd, h_fv] at h
                dsimp only at h
                have h_step :
                    (match setDiscrNextFields? ety variantIdx varFields
                        curSv with
                    | none => Except.error FaultKind.unsupported
                    | some nf =>
                      match setDiscrTagCheck ety variantIdx curSv with
                      | .error k => .error k
                      | .ok () =>
                        match writePlaceSlotPath? (.ty localTy) root
                            resolvedDst.projection
                            (.enumVal ety variantIdx nf) with
                        | none => .error .unsupported
                        | some root' =>
                          match MirSemantics.setElem? locals
                              resolvedDst.localId (.live root') with
                          | some ls' => .ok ls'
                          | none => .error .unsupported) = .ok locals' := by
                  cases curSv <;> exact h
                cases h_nf : setDiscrNextFields? ety variantIdx varFields
                    curSv with
                | none => rw [h_nf] at h_step; cases h_step
                | some nextFields =>
                  rw [h_nf] at h_step
                  dsimp only at h_step
                  cases h_tc : setDiscrTagCheck ety variantIdx curSv with
                  | error _ => rw [h_tc] at h_step; cases h_step
                  | ok u =>
                    rw [h_tc] at h_step
                    cases u
                    dsimp only at h_step
                    cases h_w : writePlaceSlotPath? (.ty localTy) root
                        resolvedDst.projection
                        (.enumVal ety variantIdx nextFields) with
                    | none => rw [h_w] at h_step; cases h_step
                    | some root' =>
                      rw [h_w] at h_step
                      dsimp only at h_step
                      cases h_set : MirSemantics.setElem? locals
                          resolvedDst.localId (.live root') <;>
                        rw [h_set] at h_step
                      · cases h_step
                      · injection h_step with h_eq
                        subst h_eq
                        exact setElem?_length h_set
      · cases h_g : MirSemantics.getElem? locals resolvedDst.localId <;>
          (rw [h_g] at h; cases h)
  | bool | int _ _ | unit | never | adtStruct _ | tuple _ | array _ _
  | ref _ _ | rawPtr _ _ | unsupported =>
    cases h_g : MirSemantics.getElem? locals resolvedDst.localId with
    | none => rw [h_g] at h; cases h
    | some slot =>
      rw [h_g] at h
      cases slot with
      | dead => cases h
      | live root =>
        dsimp only at h
        cases h_rd : readPlaceSlotPath? (.ty localTy) root
            resolvedDst.projection with
        | none => rw [h_rd] at h; cases h
        | some _ =>
          rw [h_rd] at h
          dsimp only at h
          cases h_b : (isTypeUninhabited _ || !Nat.beq variantIdx 0) <;>
            rw [h_b] at h
          · injection h with h_eq; subst h_eq; rfl
          · cases h

theorem writeAggregateFields_length {bodyLocals : List MirTy} {localTy : MirTy}
    {dstLocal : LocalId} {baseProj : List ProjectionElem} {idx : Nat}
    {locals locals' : List LocalSlot} {ops : List Operand}
    {fieldTys : List MirTy}
    (h : writeAggregateFields bodyLocals localTy dstLocal baseProj idx locals
      ops fieldTys = .ok locals') :
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
      dsimp only [writeAggregateFields] at h
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
            cases h_wr : writePlaceWithLocalTy localTy l₁
                { localId := dstLocal, projection := baseProj ++ [.field idx ft] }
                ft v₀ with
            | error _ => rw [h_wr] at h; cases h
            | ok l₂ =>
              rw [h_wr] at h
              exact ((ih h).trans (writePlaceWithLocalTy_length h_wr)).trans
                (evalOperandToSlot_length h_op)

theorem writeAggregateArrayElems_length {bodyLocals : List MirTy}
    {localTy elemTy : MirTy} {dstLocal : LocalId}
    {baseProj : List ProjectionElem} {idx : Nat}
    {locals locals' : List LocalSlot} {ops : List Operand}
    (h : writeAggregateArrayElems bodyLocals localTy dstLocal baseProj elemTy
      idx locals ops = .ok locals') :
    locals'.length = locals.length := by
  induction ops generalizing idx locals with
  | nil =>
    injection h with h_loc
    subst h_loc
    rfl
  | cons o os ih =>
    dsimp only [writeAggregateArrayElems] at h
    cases h_op : evalOperandToSlot bodyLocals locals o with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨srcTy, sv₀, l₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_ty : MirTy.beq srcTy elemTy <;> rw [h_ty] at h
      · cases h
      · cases h_v : SlotVal.toVal? sv₀ with
        | none => rw [h_v] at h; cases h
        | some v₀ =>
          rw [h_v] at h
          dsimp only at h
          cases h_wr : writePlaceWithLocalTy localTy l₁
              { localId := dstLocal
                projection := baseProj ++ [.constantIndex idx (idx + 1) false] }
              elemTy v₀ with
          | error _ => rw [h_wr] at h; cases h
          | ok l₂ =>
            rw [h_wr] at h
            exact ((ih h).trans (writePlaceWithLocalTy_length h_wr)).trans
              (evalOperandToSlot_length h_op)

theorem writeAggregate_length {bodyLocals : List MirTy} {localTy : MirTy}
    {locals locals' : List LocalSlot} {resolvedDst : Place} {dstTy : MirTy}
    {kind : AggregateKind} {ops : List Operand}
    (h : writeAggregate bodyLocals localTy locals resolvedDst dstTy kind ops =
      .ok locals') :
    locals'.length = locals.length := by
  unfold writeAggregate at h
  cases kind with
  | tuple =>
    cases dstTy with
    | unit =>
      dsimp only at h
      cases h_emp : ops.isEmpty <;> rw [h_emp] at h
      · cases h
      · rw [Bool.not_true, ite_false_eq_true] at h
        exact writePlaceWithLocalTy_length h
    | tuple fieldTys =>
      dsimp only at h
      cases h_cond : (fieldTys.isEmpty || !Nat.beq ops.length fieldTys.length) <;>
        rw [h_cond] at h
      · dsimp only [ite_false_eq_true] at h
        exact writeAggregateFields_length h
      · cases h
    | _ => cases h
  | adtStruct sty =>
    cases dstTy with
    | adtStruct dstSty =>
      dsimp only at h
      cases h_cond : (!StructTy.beq sty dstSty ||
          !Nat.beq ops.length sty.fields.length ||
          !areSupportedFieldTys sty.fields ||
          isTypeUninhabited (.adtStruct sty)) <;> rw [h_cond] at h
      · cases h_emp : ops.isEmpty <;> rw [h_emp] at h
        · dsimp only [ite_false_eq_true] at h
          exact writeAggregateFields_length h
        · dsimp only [ite_false_eq_true, ite_true_eq_true] at h
          exact writePlaceWithLocalTy_length h
      · cases h
    | _ => cases h
  | adtEnum ety variantIdx =>
    cases dstTy with
    | enum dstEty =>
      dsimp only at h
      cases h_cond : (!EnumTy.beq ety dstEty || !enumAdmitted ety) <;>
        rw [h_cond] at h
      · cases h_fv : fieldsForVariant? ety variantIdx with
        | none => rw [h_fv] at h; cases h
        | some varFieldTys =>
          rw [h_fv] at h
          dsimp only [ite_false_eq_true] at h
          cases h_len : Nat.beq ops.length varFieldTys.length <;>
            rw [h_len] at h
          · cases h
          · rw [Bool.not_true, ite_false_eq_true] at h
            cases h_wf : writeAggregateFields bodyLocals localTy
                resolvedDst.localId
                (resolvedDst.projection ++ [.downcast variantIdx])
                0 locals ops varFieldTys with
            | error _ => rw [h_wf] at h; cases h
            | ok l₁ =>
              rw [h_wf] at h
              dsimp only at h
              exact (evalSetDiscriminantResolved_length h).trans
                (writeAggregateFields_length h_wf)
      · cases h
    | _ => cases h
  | array elemTy =>
    cases dstTy with
    | array dstElemTy len =>
      dsimp only at h
      cases h_cond : (!MirTy.beq elemTy dstElemTy || !Nat.beq ops.length len ||
          !isSupportedScalarOrUnitTy elemTy ||
          !Nat.blt len (Nat.pow 2 64)) <;> rw [h_cond] at h
      · cases h_emp : ops.isEmpty <;> rw [h_emp] at h
        · dsimp only [ite_false_eq_true] at h
          exact writeAggregateArrayElems_length h
        · dsimp only [ite_false_eq_true, ite_true_eq_true] at h
          exact writePlaceWithLocalTy_length h
      · cases h
    | _ => cases h

theorem deinitPlaceWithLocalTy_length {localTy : MirTy}
    {locals locals' : List LocalSlot} {place : Place} {ty : MirTy}
    (h : deinitPlaceWithLocalTy localTy locals place ty = .ok locals') :
    locals'.length = locals.length := by
  unfold deinitPlaceWithLocalTy at h
  cases h_get : MirSemantics.getElem? locals place.localId with
  | none => rw [h_get] at h; cases h
  | some slot =>
    rw [h_get] at h
    cases slot with
    | dead => cases h
    | live root =>
      dsimp only at h
      cases h_w : writePlaceSlotPath? (.ty localTy) root place.projection
          (uninitSlotVal ty) with
      | none => rw [h_w] at h; cases h
      | some root' =>
        rw [h_w] at h
        dsimp only at h
        cases h_set :
            MirSemantics.setElem? locals place.localId (.live root') <;>
          rw [h_set] at h
        · cases h
        · injection h with h_eq
          subst h_eq
          exact setElem?_length h_set

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
  | unit | structVal _ _ | enumVal _ _ _ | ptr _ | tuple _ | array _ _
  | bytes _ => cases op <;> rfl
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
  | unit | structVal _ _ | enumVal _ _ _ | ptr _ | tuple _ | array _ _
  | bytes _ => cases rhs <;> rfl
  | bool l =>
    cases rhs with
    | unit | structVal _ _ | enumVal _ _ _ | ptr _ | tuple _ | array _ _
    | bytes _ | scalar _ => rfl
    | bool r => cases op <;> cases l <;> cases r <;> rfl
  | scalar l =>
    cases rhs with
    | unit | structVal _ _ | enumVal _ _ _ | ptr _ | tuple _ | array _ _
    | bytes _ | bool _ => rfl
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

theorem bool_or_congr {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (a₁ || b₁) = (a₂ || b₂) := by
  rw [ha, hb]

theorem decide_le_eq_nat_ble (a b : Nat) : decide (a ≤ b) = Nat.ble a b := by
  cases h : Nat.ble a b with
  | true => exact decide_eq_true (Nat.le_of_ble_eq_true h)
  | false =>
    apply decide_eq_false
    intro h_le
    rw [Nat.ble_eq_true_of_le h_le] at h
    cases h

theorem decide_lt_eq_nat_blt (a b : Nat) : decide (a < b) = Nat.blt a b :=
  decide_le_eq_nat_ble (Nat.succ a) b

theorem decide_eq_nat_beq (a b : Nat) : decide (a = b) = Nat.beq a b := by
  cases h : Nat.beq a b with
  | true => exact decide_eq_true (Nat.eq_of_beq_eq_true h)
  | false =>
    apply decide_eq_false
    intro h_eq
    rw [h_eq, Nat.beq_refl] at h
    cases h

theorem wrappingRange_contains_eq (vs ve val : BitVec 128) :
    (WrappingRange.mk vs ve).contains val =
      wrappingRangeContains vs ve val := by
  dsimp only [WrappingRange.contains, wrappingRangeContains]
  rw [decide_le_eq_nat_ble vs.toNat val.toNat,
      decide_le_eq_nat_ble val.toNat ve.toNat]
  cases h_le : Nat.ble vs.toNat ve.toNat with
  | true =>
    rw [ite_eq_left (Nat.le_of_ble_eq_true h_le)]
    rfl
  | false =>
    have h_nle : ¬ (vs.toNat ≤ ve.toNat) := by
      intro hp
      rw [Nat.ble_eq_true_of_le hp] at h_le
      cases h_le
    rw [ite_eq_right h_nle]
    rfl

theorem list_getElem?_eq_getElem? {α : Type} (xs : List α) (k : Nat) :
    xs[k]? = MirSemantics.getElem? xs k := by
  induction xs generalizing k with
  | nil => rfl
  | cons _ rest ih =>
    cases k with
    | zero => rfl
    | succ j => exact ih j

theorem tryFromUInt_isSome_eq_truncateBits_beq (w : IntWidth)
    (b : BitVec 128) :
    (match ScalarInt.tryFromUInt b (toMiriSize w) with
    | .ok (some _) => true
    | _ => false) = (truncateBits w b == b) := by
  rw [@match_tryFromUInt_eq Bool w b (fun _ => true) false]
  change (if (!(truncateBits w b == b)) = true then false else true) =
    (truncateBits w b == b)
  cases (truncateBits w b == b) <;> rfl

theorem refFieldsForVariant?_eq (ety : EnumTy) (v : Nat) :
    refFieldsForVariant? ety v = fieldsForVariant? ety v := by
  dsimp only [refFieldsForVariant?, fieldsForVariant?]
  rw [list_getElem?_eq_getElem?]

theorem refHasEnumPayloadFields_eq (ety : EnumTy) :
    refHasEnumPayloadFields ety = hasEnumPayloadFields ety := rfl

mutual
  theorem refIsTypeUninhabited_eq : ∀ (ty : MirTy),
      refIsTypeUninhabited ty = isTypeUninhabited ty
    | .bool | .int _ _ | .unit | .never | .ref _ _ | .rawPtr _ _
    | .unsupported => rfl
    | .adtStruct ⟨_, fs⟩ => refAnyFieldUninhabited_eq fs
    | .enum ⟨_, _, _, _, ds, vf⟩ => by
      dsimp only [refIsTypeUninhabited, isTypeUninhabited]
      rw [refAllVariantsUninhabited_eq vf]
    | .tuple fs => refAnyFieldUninhabited_eq fs
    | .array elemTy len => by
      dsimp only [refIsTypeUninhabited, isTypeUninhabited]
      rw [refIsTypeUninhabited_eq elemTy]

  theorem refAnyFieldUninhabited_eq : ∀ (tys : List MirTy),
      refAnyFieldUninhabited tys = anyFieldUninhabited tys
    | [] => rfl
    | ty :: tys => by
      dsimp only [refAnyFieldUninhabited, anyFieldUninhabited]
      rw [refIsTypeUninhabited_eq ty, refAnyFieldUninhabited_eq tys]

  theorem refAllVariantsUninhabited_eq : ∀ (vss : List (List MirTy)),
      refAllVariantsUninhabited vss = allVariantsUninhabited vss
    | [] => rfl
    | fs :: fss => by
      dsimp only [refAllVariantsUninhabited, allVariantsUninhabited]
      rw [refAnyFieldUninhabited_eq fs, refAllVariantsUninhabited_eq fss]
end

theorem refIsVariantUninhabited_eq (ety : EnumTy) (v : Nat) :
    refIsVariantUninhabited ety v = isVariantUninhabited ety v := by
  dsimp only [refIsVariantUninhabited, isVariantUninhabited]
  rw [refFieldsForVariant?_eq]
  cases fieldsForVariant? ety v with
  | none => rfl
  | some fs => exact refAnyFieldUninhabited_eq fs

mutual
  theorem refIsZeroSizedTy_eq : ∀ (ty : MirTy),
      refIsZeroSizedTy ty = isZeroSizedTy ty
    | .unit | .never | .bool | .int _ _ | .ref _ _ | .rawPtr _ _
    | .unsupported => rfl
    | .adtStruct ⟨_, fs⟩ => refAreAllZeroSizedTys_eq fs
    | .enum ⟨_, _, _, tagRepr, ds, vf⟩ => by
      dsimp only [refIsZeroSizedTy, isZeroSizedTy]
      cases tagRepr with
      | zeroSized =>
        dsimp only
        rw [refVariantZeroSizedFlags_eq vf]
      | single v =>
        dsimp only
        rw [list_getElem?_eq_getElem?, refVariantZeroSizedFlags_eq vf]
        cases MirSemantics.getElem? (variantZeroSizedFlags vf) v <;> rfl
      | scalar _ _ | niche _ _ _ _ _ _ _ _ _ => rfl
    | .tuple fs => refAreAllZeroSizedTys_eq fs
    | .array elemTy len => by
      dsimp only [refIsZeroSizedTy, isZeroSizedTy]
      rw [refIsZeroSizedTy_eq elemTy]

  theorem refAreAllZeroSizedTys_eq : ∀ (tys : List MirTy),
      refAreAllZeroSizedTys tys = areAllZeroSizedTys tys
    | [] => rfl
    | ty :: tys => by
      dsimp only [refAreAllZeroSizedTys, areAllZeroSizedTys]
      rw [refIsZeroSizedTy_eq ty, refAreAllZeroSizedTys_eq tys]

  theorem refVariantZeroSizedFlags_eq : ∀ (vss : List (List MirTy)),
      refVariantZeroSizedFlags vss = variantZeroSizedFlags vss
    | [] => rfl
    | fs :: fss => by
      dsimp only [refVariantZeroSizedFlags, variantZeroSizedFlags]
      rw [refAreAllZeroSizedTys_eq fs, refVariantZeroSizedFlags_eq fss]
end

theorem refNicheResolveFromTy_eq (ty : MirTy) (path : List Nat) :
    refNicheResolveFromTy ty path = nicheResolveFromTy ty path := by
  induction path generalizing ty with
  | nil => rfl
  | cons idx rest ih =>
    cases ty with
    | adtStruct sty =>
      dsimp only [refNicheResolveFromTy, nicheResolveFromTy]
      rw [list_getElem?_eq_getElem?]
      cases MirSemantics.getElem? sty.fields idx with
      | none => rfl
      | some fTy => exact ih fTy
    | tuple fs =>
      dsimp only [refNicheResolveFromTy, nicheResolveFromTy]
      rw [list_getElem?_eq_getElem?]
      cases MirSemantics.getElem? fs idx with
      | none => rfl
      | some fTy => exact ih fTy
    | array elemTy len =>
      dsimp only [refNicheResolveFromTy, nicheResolveFromTy]
      cases Nat.blt idx len with
      | false => rfl
      | true => exact ih elemTy
    | _ => rfl

theorem refNicheLeafTy?_eq (nichePath : List Nat) (varFields : List MirTy) :
    refNicheLeafTy? nichePath varFields = nicheLeafTy? nichePath varFields := by
  cases nichePath with
  | nil => rfl
  | cons idx rest =>
    dsimp only [refNicheLeafTy?, nicheLeafTy?]
    rw [list_getElem?_eq_getElem?]
    cases MirSemantics.getElem? varFields idx with
    | none => rfl
    | some fTy => exact refNicheResolveFromTy_eq fTy rest

theorem refNicheLeafMatchesTag_eq (tagW : IntWidth) (tagS : Bool) (ty : MirTy) :
    refNicheLeafMatchesTag tagW tagS ty = nicheLeafMatchesTag tagW tagS ty := by
  cases ty <;> rfl

theorem refAllNicheTagsInValidRange_eq (tagW : IntWidth)
    (vs ve nicheStart : BitVec 128) (count : Nat) :
    refAllNicheTagsInValidRange tagW vs ve nicheStart count =
      allNicheTagsInValidRange tagW vs ve nicheStart count := by
  induction count with
  | zero => rfl
  | succ k ih =>
    change (refAllNicheTagsInValidRange tagW vs ve nicheStart k &&
        match (toMiriSize tagW).truncate (BitVec.ofNat 128 k + nicheStart) with
        | .ok trunc => (WrappingRange.mk vs ve).contains trunc
        | .error _ => false) =
      (allNicheTagsInValidRange tagW vs ve nicheStart k &&
        wrappingRangeContains vs ve
          (truncateBits tagW (BitVec.ofNat 128 k + nicheStart)))
    rw [ih, size_truncate_eq]
    dsimp only
    rw [wrappingRange_contains_eq]

theorem refOtherVariantsUninhabited_eq (ety : EnumTy) (singleVar total : Nat) :
    refOtherVariantsUninhabited ety singleVar total =
      otherVariantsUninhabited ety singleVar total := by
  induction total with
  | zero => rfl
  | succ k ih =>
    change (refOtherVariantsUninhabited ety singleVar k &&
        (Nat.beq k singleVar || refIsVariantUninhabited ety k)) =
      (otherVariantsUninhabited ety singleVar k &&
        (Nat.beq k singleVar || isVariantUninhabited ety k))
    rw [ih, refIsVariantUninhabited_eq]

theorem refOtherVariantsValidForNiche_eq (ety : EnumTy)
    (untagged start last total : Nat) :
    refOtherVariantsValidForNiche ety untagged start last total =
      otherVariantsValidForNiche ety untagged start last total := by
  induction total with
  | zero => rfl
  | succ k ih =>
    change (refOtherVariantsValidForNiche ety untagged start last k &&
        (if Nat.beq k untagged then true
         else if refIsVariantUninhabited ety k then true
         else Nat.ble start k && Nat.ble k last &&
           match refFieldsForVariant? ety k with
           | some fs => refAreAllZeroSizedTys fs
           | none => false)) =
      (otherVariantsValidForNiche ety untagged start last k &&
        (if Nat.beq k untagged then true
         else if isVariantUninhabited ety k then true
         else Nat.ble start k && Nat.ble k last &&
           match fieldsForVariant? ety k with
           | some fs => areAllZeroSizedTys fs
           | none => false))
    rw [ih, refIsVariantUninhabited_eq, refFieldsForVariant?_eq]
    cases fieldsForVariant? ety k with
    | none => rfl
    | some fs =>
      dsimp only
      rw [refAreAllZeroSizedTys_eq]

theorem refEnumAdmittedCore_eq (ety : EnumTy) :
    refEnumAdmittedCore ety = enumAdmittedCore ety := by
  dsimp only [refEnumAdmittedCore, enumAdmittedCore]
  apply bool_and_congr
  · apply bool_and_congr
    · apply bool_and_congr
      · rfl
      · exact list_all_congr_eq ety.discriminants _ _
          (refEnumDiscrInBounds_eq ety.discrWidth)
    · exact refNatListPairwiseNe_eq ety.discriminants
  · cases ety.tagRepr with
    | zeroSized => rfl
    | single v =>
      dsimp only
      rw [refOtherVariantsUninhabited_eq]
    | scalar tagW tagS =>
      dsimp only
      apply list_all_congr_eq
      intro d
      rw [size_truncate_eq]
      dsimp only
      rw [refMiriTagToDiscrBits_eq]
    | niche tagW tagS vs ve nichePath untagged start last nicheStart =>
      dsimp only
      apply bool_and_congr
      · apply bool_and_congr
        · apply bool_and_congr
          · apply bool_and_congr
            · apply bool_and_congr
              · apply bool_and_congr
                · apply bool_and_congr
                  · rfl
                  · exact tryFromUInt_isSome_eq_truncateBits_beq tagW vs
                · exact tryFromUInt_isSome_eq_truncateBits_beq tagW ve
              · exact tryFromUInt_isSome_eq_truncateBits_beq tagW nicheStart
            · rfl
          · exact refAllNicheTagsInValidRange_eq tagW vs ve nicheStart _
        · exact refOtherVariantsValidForNiche_eq ety untagged start last _
      · rw [refFieldsForVariant?_eq]
        cases fieldsForVariant? ety untagged with
        | none => rfl
        | some uFields =>
          dsimp only
          rw [refNicheLeafTy?_eq]
          cases nicheLeafTy? nichePath uFields with
          | none => rfl
          | some leafTy =>
            dsimp only
            rw [refNicheLeafMatchesTag_eq]

mutual
  theorem refIsSupportedLocalTy_eq : ∀ (ty : MirTy),
      refIsSupportedLocalTy ty = isSupportedScalarOrUnitTy ty
    | .bool | .int _ _ | .unit | .never | .ref _ _ | .rawPtr _ _
    | .unsupported => rfl
    | .adtStruct ⟨_, fs⟩ => refAreSupportedFieldTys_eq fs
    | .enum ⟨id, dw, ds, tr, d, vf⟩ => by
      dsimp only [refIsSupportedLocalTy, isSupportedScalarOrUnitTy]
      rw [refEnumAdmittedCore_eq, refAreSupportedVariantFieldLists_eq vf]
    | .tuple fields => by
      dsimp only [refIsSupportedLocalTy, isSupportedScalarOrUnitTy]
      rw [refAreSupportedFieldTys_eq fields]
    | .array elemTy len => by
      dsimp only [refIsSupportedLocalTy, isSupportedScalarOrUnitTy]
      rw [refIsSupportedLocalTy_eq elemTy]

  theorem refAreSupportedFieldTys_eq : ∀ (tys : List MirTy),
      refAreSupportedFieldTys tys = areSupportedFieldTys tys
    | [] => rfl
    | ty :: tys => by
      dsimp only [refAreSupportedFieldTys, areSupportedFieldTys]
      rw [refIsSupportedLocalTy_eq ty, refAreSupportedFieldTys_eq tys]

  theorem refAreSupportedVariantFieldLists_eq : ∀ (vss : List (List MirTy)),
      refAreSupportedVariantFieldLists vss = areSupportedVariantFieldLists vss
    | [] => rfl
    | fs :: fss => by
      dsimp only [refAreSupportedVariantFieldLists,
        areSupportedVariantFieldLists]
      rw [refAreSupportedFieldTys_eq fs,
        refAreSupportedVariantFieldLists_eq fss]
end

theorem refEnumAdmitted_eq (ety : EnumTy) :
    refEnumAdmitted ety = enumAdmitted ety := by
  dsimp only [refEnumAdmitted, enumAdmitted]
  rw [refEnumAdmittedCore_eq, refAreSupportedVariantFieldLists_eq]

theorem refIsZstEnumTy_eq (ety : EnumTy) :
    refIsZstEnumTy ety = isZstEnumTy ety := by
  unfold refIsZstEnumTy isZstEnumTy
  cases ety.tagRepr with
  | zeroSized => exact refEnumAdmitted_eq ety
  | _ => rfl

theorem refIsPrimitiveReadableTy_eq (ty : MirTy) :
    refIsPrimitiveReadableTy ty = isPrimitiveReadableTy ty := by
  cases ty <;> rfl

theorem refReplicateVal_eq (n : Nat) (v : Val) :
    refReplicateVal n v = replicateVal n v := rfl

theorem refReplicateSlotVal_eq (n : Nat) (sv : SlotVal) :
    refReplicateSlotVal n sv = replicateSlotVal n sv := rfl

mutual
  theorem refUninitSlotVal_eq : ∀ (ty : MirTy),
      refUninitSlotVal ty = uninitSlotVal ty
    | .bool | .int _ _ | .unit | .never | .ref _ _ | .rawPtr _ _
    | .unsupported => rfl
    | .adtStruct ⟨id, fs⟩ => by
      dsimp only [refUninitSlotVal, uninitSlotVal]
      rw [refUninitSlotVals_eq fs]
    | .enum ⟨id, dw, ds, tr, d, vf⟩ => by
      dsimp only [refUninitSlotVal, uninitSlotVal]
      cases tr with
      | zeroSized =>
        dsimp only
        rw [refEnumAdmittedCore_eq, refAreSupportedVariantFieldLists_eq vf]
      | single v =>
        dsimp only
        rw [refEnumAdmittedCore_eq, refAreSupportedVariantFieldLists_eq vf,
            refUninitVariantSlotLists_eq vf, refIsTypeUninhabited_eq]
        cases MirSemantics.getElem? (uninitVariantSlotLists vf) v <;> rfl
      | scalar _ _ | niche _ _ _ _ _ _ _ _ _ => rfl
    | .tuple fields => by
      dsimp only [refUninitSlotVal, uninitSlotVal]
      rw [refUninitSlotVals_eq fields]
    | .array elemTy len => by
      dsimp only [refUninitSlotVal, uninitSlotVal]
      rw [refUninitSlotVal_eq elemTy, refReplicateSlotVal_eq]

  theorem refUninitSlotVals_eq : ∀ (tys : List MirTy),
      refUninitSlotVals tys = uninitSlotVals tys
    | [] => rfl
    | ty :: tys => by
      dsimp only [refUninitSlotVals, uninitSlotVals]
      rw [refUninitSlotVal_eq ty, refUninitSlotVals_eq tys]

  theorem refUninitVariantSlotLists_eq : ∀ (vss : List (List MirTy)),
      refUninitVariantSlotLists vss = uninitVariantSlotLists vss
    | [] => rfl
    | fs :: fss => by
      dsimp only [refUninitVariantSlotLists, uninitVariantSlotLists]
      rw [refUninitSlotVals_eq fs, refUninitVariantSlotLists_eq fss]
end

theorem refLiveUninitSlot_eq (ty : MirTy) :
    refLiveUninitSlot ty = liveUninitSlot ty := by
  dsimp only [refLiveUninitSlot, liveUninitSlot]
  rw [refUninitSlotVal_eq]

theorem miriImmToPayload?_roundtrip {α : Type} (x : α) :
    miriImmediateToPayload? (payloadToMiriImmediate x) = some x := rfl

theorem evalPlaceToOp_sized_live (sv : SlotVal) :
    Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false)
        (mkSingleLocalMiriFrame (slotToMiriLocalValue (.live sv)) false) ()
        ⟨0, Array.empty⟩ (some refSizedLocalLayout) =
      ⟨mkSingleLocalMiriFrame (slotToMiriLocalValue (.live sv)) false, (),
        .ok ⟨.immediate (payloadToMiriImmediate sv), refSizedLocalLayout⟩⟩ :=
  rfl

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

theorem array_mk_getElem?_eq_getElem? {α : Type} (xs : List α) (k : Nat) :
    (Array.mk xs)[k]? = MirSemantics.getElem? xs k := by
  dsimp only [Array.size, GetElem?.getElem?, Array.instGetElem?NatLtSize,
    decidableGetElem?, GetElem.getElem, Array.instGetElemNatLtSize,
    Array.getInternal]
  induction xs generalizing k with
  | nil => rfl
  | cons x rest ih =>
    cases k with
    | zero =>
      have h0 : 0 < (x :: rest).length := Nat.succ_pos rest.length
      rw [dite_eq_left h0]
      rfl
    | succ j =>
      cases h_lt : decide (j < rest.length) with
      | true =>
        have hj : j < rest.length := of_decide_eq_true h_lt
        have hj1 : j + 1 < (x :: rest).length := Nat.succ_lt_succ hj
        rw [dite_eq_left hj1]
        have h_sub := ih j
        rw [dite_eq_left hj] at h_sub
        exact h_sub
      | false =>
        have hnj : ¬ (j < rest.length) := of_decide_eq_false h_lt
        have hnj1 : ¬ (j + 1 < (x :: rest).length) :=
          fun h => hnj (Nat.lt_of_succ_lt_succ h)
        rw [dite_eq_right hnj1]
        have h_sub := ih j
        rw [dite_eq_right hnj] at h_sub
        exact h_sub

private theorem getElem?_refVariantLayoutsLoop (ety : EnumTy) (base : Nat)
    (ds : List Nat) (k : Nat) :
    MirSemantics.getElem? (refVariantLayoutsLoop ety base ds) k =
      if Nat.blt k ds.length then
        some { refInhabitedVariantLayout with
               uninhabited := refIsVariantUninhabited ety (base + k) }
      else
        none := by
  induction ds generalizing base k with
  | nil =>
    cases k <;> rfl
  | cons _ rest ih =>
    cases k with
    | zero =>
      dsimp only [refVariantLayoutsLoop, MirSemantics.getElem?]
      rw [List.length_cons]
      have h0 : Nat.blt 0 (rest.length + 1) = true :=
        nat_blt_eq_true_of_lt (Nat.succ_pos rest.length)
      rw [h0, ite_true_eq_true, Nat.add_zero]
    | succ j =>
      dsimp only [refVariantLayoutsLoop, MirSemantics.getElem?]
      rw [List.length_cons]
      have h_blt : Nat.blt (j + 1) (rest.length + 1) = Nat.blt j rest.length :=
        rfl
      rw [h_blt, ih (base + 1) j, Nat.add_right_comm base 1 j, Nat.add_assoc]

private theorem no_payload_fields_eq_nil {vf : List (List MirTy)} {k : Nat}
    {fs : List MirTy}
    (h_no : vf.any (fun xs => !xs.isEmpty) = false)
    (h_get : MirSemantics.getElem? vf k = some fs) :
    fs = [] := by
  induction vf generalizing k with
  | nil => cases h_get
  | cons x rest ih =>
    dsimp only [List.any] at h_no
    cases hx : x with
    | cons _ _ =>
      rw [hx] at h_no
      cases h_no
    | nil =>
      rw [hx] at h_no
      rw [Anneal.MirWp.list_isEmpty_nil, Bool.not_true, Bool.false_or] at h_no
      cases k with
      | zero =>
        rw [hx] at h_get
        injection h_get with h_eq
        exact h_eq.symm
      | succ j => exact ih h_no h_get

private theorem getElem?_some_of_lt {α : Type} :
    ∀ (xs : List α) (k : Nat), k < xs.length →
      ∃ x : α, MirSemantics.getElem? xs k = some x
  | [], _, hk => nomatch hk
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: rest, k + 1, hk =>
    getElem?_some_of_lt rest k (Nat.lt_of_succ_lt_succ hk)

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) :
    a = true := by
  cases a with
  | false => cases h
  | true => rfl

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a with
  | false => cases h
  | true => exact h

theorem enumAdmittedCore_of_enumAdmitted {ety : EnumTy}
    (h : enumAdmitted ety = true) :
    enumAdmittedCore ety = true :=
  bool_and_left h

theorem enumAdmitted_vf_len {ety : EnumTy} (h : enumAdmitted ety = true) :
    Nat.beq ety.variantFields.length ety.discriminants.length = true := by
  have hc := enumAdmittedCore_of_enumAdmitted h
  dsimp only [enumAdmittedCore] at hc
  exact bool_and_right
    (bool_and_left (bool_and_left (bool_and_left hc)))

theorem enumAdmitted_nonempty_discr {ety : EnumTy}
    (h : enumAdmitted ety = true) :
    ety.discriminants.isEmpty = false := by
  have hc := enumAdmittedCore_of_enumAdmitted h
  dsimp only [enumAdmittedCore] at hc
  exact bool_eq_false_of_not_eq_true
    (bool_and_left (bool_and_left
      (bool_and_left (bool_and_left (bool_and_left hc)))))

theorem enumAdmitted_discr_len_lt {ety : EnumTy}
    (h : enumAdmitted ety = true) :
    Nat.blt ety.discriminants.length (Nat.pow 2 32) = true := by
  have hc := enumAdmittedCore_of_enumAdmitted h
  dsimp only [enumAdmittedCore] at hc
  exact bool_and_right (bool_and_left
    (bool_and_left (bool_and_left (bool_and_left hc))))

theorem enumAdmitted_discr_in_bounds {ety : EnumTy}
    (h : enumAdmitted ety = true) :
    ety.discriminants.all (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) = true :=
  bool_and_right (bool_and_left (bool_and_left
    (enumAdmittedCore_of_enumAdmitted h)))

theorem enumAdmitted_pairwiseNe {ety : EnumTy}
    (h : enumAdmitted ety = true) :
    natListPairwiseNe ety.discriminants = true :=
  bool_and_right (bool_and_left (enumAdmittedCore_of_enumAdmitted h))

theorem isVariantUninhabited_of_no_payload {ety : EnumTy} {v : Nat}
    (h_adm : enumAdmitted ety = true)
    (h_no : hasEnumPayloadFields ety = false)
    (hv : v < ety.discriminants.length) :
    isVariantUninhabited ety v = false := by
  have h_vf := enumAdmitted_vf_len h_adm
  dsimp only [isVariantUninhabited, fieldsForVariant?]
  rw [nat_blt_eq_true_of_lt hv, h_vf, list_getElem?_eq_getElem?, Bool.not_true,
      Bool.false_or, ite_false_eq_true]
  have h_len := Nat.eq_of_beq_eq_true h_vf
  have hv_vf : v < ety.variantFields.length := by
    rw [h_len]; exact hv
  let ⟨fs, h_get⟩ := getElem?_some_of_lt ety.variantFields v hv_vf
  rw [h_get]
  dsimp only
  rw [no_payload_fields_eq_nil h_no h_get]
  rfl

private theorem allVariantsUninhabited_getElem? {vf : List (List MirTy)}
    {k : Nat} {fs : List MirTy}
    (h_all : allVariantsUninhabited vf = true)
    (h_get : MirSemantics.getElem? vf k = some fs) :
    anyFieldUninhabited fs = true := by
  induction vf generalizing k with
  | nil => cases h_get
  | cons x rest ih =>
    dsimp only [allVariantsUninhabited] at h_all
    cases k with
    | zero =>
      injection h_get with h_eq
      subst h_eq
      exact bool_and_left h_all
    | succ j =>
      exact ih (bool_and_right h_all) h_get

private theorem allVariantsUninhabited_of_all_idx :
    ∀ (vf : List (List MirTy)),
      (∀ (k : Nat) (fs : List MirTy),
        k < vf.length → MirSemantics.getElem? vf k = some fs →
        anyFieldUninhabited fs = true) →
      allVariantsUninhabited vf = true
  | [], _ => rfl
  | fs :: rest, h => by
    dsimp only [allVariantsUninhabited]
    have h0 : anyFieldUninhabited fs = true :=
      h 0 fs (Nat.succ_pos rest.length) rfl
    have h_rest : allVariantsUninhabited rest = true :=
      allVariantsUninhabited_of_all_idx rest
        (fun k fs' hk hget => h (k + 1) fs' (Nat.succ_lt_succ hk) hget)
    rw [h0, h_rest]
    rfl

theorem otherVariantsUninhabited_at {ety : EnumTy} {v₀ : Nat} :
    ∀ {n k : Nat},
      otherVariantsUninhabited ety v₀ n = true →
      k < n →
      (Nat.beq k v₀ || isVariantUninhabited ety k) = true
  | 0, _, _, hk => nomatch hk
  | m + 1, k, h_oth, hk => by
    have h_step :
        (otherVariantsUninhabited ety v₀ m &&
          (Nat.beq m v₀ || isVariantUninhabited ety m)) = true := h_oth
    cases h_km : Nat.beq k m with
    | true =>
      have h_eq := Nat.eq_of_beq_eq_true h_km
      subst h_eq
      exact bool_and_right h_step
    | false =>
      have h_ne : k ≠ m := by
        intro h_eq; subst h_eq; rw [Nat.beq_refl] at h_km; cases h_km
      have hk_lt : k < m :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) h_ne
      exact otherVariantsUninhabited_at (bool_and_left h_step) hk_lt

theorem isTypeUninhabited_zeroSized_eq_false {ety : EnumTy}
    (h_adm : enumAdmitted ety = true)
    (h_tr : ety.tagRepr = .zeroSized) :
    isTypeUninhabited (.enum ety) = false := by
  have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
  rw [h_tr] at hc
  dsimp only at hc
  have h_no : hasEnumPayloadFields ety = false :=
    bool_eq_false_of_not_eq_true (bool_and_right hc)
  have h_ne := enumAdmitted_nonempty_discr h_adm
  have h_len1 := Nat.eq_of_beq_eq_true (bool_and_left hc)
  have h_vf := enumAdmitted_vf_len h_adm
  cases ety with
  | mk id dw ds tr discrs vf =>
    first | dsimp only [isTypeUninhabited, hasEnumPayloadFields] at h_ne h_no h_len1 h_vf | change _
    first | dsimp only [isTypeUninhabited, hasEnumPayloadFields] | change _
    rw [h_ne, h_vf, Bool.not_true, Bool.false_or, ite_false_eq_true]
    have h_vflen : vf.length = 1 := by
      rw [Nat.eq_of_beq_eq_true h_vf, h_len1]
    cases vf with
    | nil => cases h_vflen
    | cons fs₀ fss =>
      cases fss with
      | cons _ _ => cases h_vflen
      | nil =>
        have h_fs0 : fs₀ = [] := @no_payload_fields_eq_nil [fs₀] 0 fs₀ h_no rfl
        subst h_fs0
        rfl

theorem isTypeUninhabited_single_eq {ety : EnumTy} {v₀ : Nat}
    (h_adm : enumAdmitted ety = true)
    (h_tr : ety.tagRepr = .single v₀) :
    isTypeUninhabited (.enum ety) = isVariantUninhabited ety v₀ := by
  have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
  rw [h_tr] at hc
  dsimp only at hc
  have hv₀_lt : v₀ < ety.discriminants.length :=
    nat_lt_of_blt_eq_true (bool_and_left hc)
  have h_oth : otherVariantsUninhabited ety v₀ ety.discriminants.length = true :=
    bool_and_right hc
  have h_ne := enumAdmitted_nonempty_discr h_adm
  have h_vf := enumAdmitted_vf_len h_adm
  have h_vflen : ety.variantFields.length = ety.discriminants.length :=
    Nat.eq_of_beq_eq_true h_vf
  have h_lhs_eq :
      isTypeUninhabited (.enum ety) =
        allVariantsUninhabited ety.variantFields := by
    cases ety with
    | mk id dw ds tr discrs vf =>
      first | dsimp only [isTypeUninhabited] at h_ne h_vf | change _
      first | dsimp only [isTypeUninhabited] | change _
      rw [h_ne, h_vf, Bool.not_true, Bool.false_or, ite_false_eq_true]
  rw [h_lhs_eq]
  have hv₀_vf : v₀ < ety.variantFields.length := by
    rw [h_vflen]; exact hv₀_lt
  let ⟨fs₀, h_get₀⟩ := getElem?_some_of_lt ety.variantFields v₀ hv₀_vf
  have h_rhs_eq :
      isVariantUninhabited ety v₀ = anyFieldUninhabited fs₀ := by
    dsimp only [isVariantUninhabited, fieldsForVariant?]
    rw [list_getElem?_eq_getElem?, nat_blt_eq_true_of_lt hv₀_lt, h_vf,
        Bool.not_true, Bool.false_or, ite_false_eq_true, h_get₀]
  rw [h_rhs_eq]
  cases h_u₀ : anyFieldUninhabited fs₀ with
  | false =>
    cases h_all : allVariantsUninhabited ety.variantFields with
    | false => rfl
    | true =>
      have h_abs := allVariantsUninhabited_getElem? h_all h_get₀
      rw [h_u₀] at h_abs
      cases h_abs
  | true =>
    apply allVariantsUninhabited_of_all_idx
    intro k fs hk h_getk
    cases h_kv : Nat.beq k v₀ with
    | true =>
      have h_eq := Nat.eq_of_beq_eq_true h_kv
      subst h_eq
      rw [h_get₀] at h_getk
      injection h_getk with h_fs
      subst h_fs
      exact h_u₀
    | false =>
      have hk_d : k < ety.discriminants.length := by
        rw [← h_vflen]; exact hk
      have h_or := otherVariantsUninhabited_at h_oth hk_d
      rw [h_kv, Bool.false_or] at h_or
      dsimp only [isVariantUninhabited, fieldsForVariant?] at h_or
      rw [list_getElem?_eq_getElem?, nat_blt_eq_true_of_lt hk_d, h_vf,
          Bool.not_true, Bool.false_or, ite_false_eq_true, h_getk] at h_or
      exact h_or

theorem refEnumLayoutData_isVariantUninhabited_eq {ety : EnumTy}
    (h_adm : enumAdmitted ety = true) (index : Nat) :
    (refEnumLayoutData ety).isVariantUninhabited index =
      isVariantUninhabited ety index := by
  cases h_tr : ety.tagRepr with
  | zeroSized =>
    have h_uninh := isTypeUninhabited_zeroSized_eq_false h_adm h_tr
    have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
    rw [h_tr] at hc
    dsimp only at hc
    have h_len1 := Nat.eq_of_beq_eq_true (bool_and_left hc)
    have h_no : hasEnumPayloadFields ety = false :=
      bool_eq_false_of_not_eq_true (bool_and_right hc)
    dsimp only [refEnumLayoutData, refBaseLayoutData,
      LayoutData.isVariantUninhabited]
    rw [h_tr]
    dsimp only
    rw [refIsTypeUninhabited_eq, h_uninh, Bool.or_false]
    cases index with
    | zero =>
      have h0_lt : 0 < ety.discriminants.length := by
        rw [h_len1]; exact Nat.succ_pos 0
      rw [isVariantUninhabited_of_no_payload h_adm h_no h0_lt]
      rfl
    | succ j =>
      have h_nlt : Nat.blt (j + 1) ety.discriminants.length = false := by
        rw [h_len1]
        cases j <;> rfl
      dsimp only [isVariantUninhabited, fieldsForVariant?]
      rw [h_nlt]
      rfl
  | single v₀ =>
    have h_uninh := isTypeUninhabited_single_eq h_adm h_tr
    have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
    rw [h_tr] at hc
    dsimp only at hc
    have h_oth :
        otherVariantsUninhabited ety v₀ ety.discriminants.length = true :=
      bool_and_right hc
    dsimp only [refEnumLayoutData, LayoutData.isVariantUninhabited]
    rw [h_tr]
    dsimp only
    rw [refIsTypeUninhabited_eq, h_uninh]
    cases h_eq : Nat.beq index v₀ with
    | true =>
      have h_iv := Nat.eq_of_beq_eq_true h_eq
      subst h_iv
      have h_bne : (index != index) = false := by
        change (!(index == index)) = false
        rw [beq_self_eq_true]
        rfl
      rw [h_bne, Bool.false_or]
    | false =>
      have h_bne : (index != v₀) = true := by
        change (!(index == v₀)) = true
        have h_b : (index == v₀) = Nat.beq index v₀ :=
          decide_eq_nat_beq index v₀
        rw [h_b, h_eq]
        rfl
      rw [h_bne, Bool.true_or]
      cases h_lt : Nat.blt index ety.discriminants.length with
      | false =>
        dsimp only [isVariantUninhabited, fieldsForVariant?]
        rw [h_lt]
        rfl
      | true =>
        have h_or :=
          otherVariantsUninhabited_at h_oth (nat_lt_of_blt_eq_true h_lt)
        rw [h_eq, Bool.false_or] at h_or
        exact h_or.symm
  | scalar tagW tagS =>
    dsimp only [refEnumLayoutData, LayoutData.isVariantUninhabited]
    rw [h_tr]
    dsimp only
    rw [array_mk_getElem?_eq_getElem?, getElem?_refVariantLayoutsLoop]
    cases h_lt : Nat.blt index ety.discriminants.length with
    | true =>
      rw [ite_true_eq_true]
      dsimp only [Option.map, Option.getD]
      rw [Nat.zero_add, refIsVariantUninhabited_eq]
    | false =>
      rw [ite_false_eq_true]
      dsimp only [Option.map, Option.getD, isVariantUninhabited,
        fieldsForVariant?]
      rw [h_lt]
      rfl
  | niche tagW tagS vs ve nichePath untagged start last nicheStart =>
    dsimp only [refEnumLayoutData, LayoutData.isVariantUninhabited]
    rw [h_tr]
    dsimp only
    rw [array_mk_getElem?_eq_getElem?, getElem?_refVariantLayoutsLoop]
    cases h_lt : Nat.blt index ety.discriminants.length with
    | true =>
      rw [ite_true_eq_true]
      dsimp only [Option.map, Option.getD]
      rw [Nat.zero_add, refIsVariantUninhabited_eq]
    | false =>
      rw [ite_false_eq_true]
      dsimp only [Option.map, Option.getD, isVariantUninhabited,
        fieldsForVariant?]
      rw [h_lt]
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

private theorem bitVec128_toNat_truncateBits_lt (w : IntWidth) (bits : BitVec 128) :
    (truncateBits w bits).toNat < Nat.pow 2 w.bitWidth := by
  rw [toNat_truncateBits]
  exact Nat.mod_lt _ (by cases w <;> decide)

private theorem bitVec128_zeroExtend_extractLsb_eq_truncateBits (w : IntWidth)
    (b : BitVec 128) :
    BitVec.zeroExtend 128 (BitVec.extractLsb (w.bitWidth - 1) 0 b) =
      truncateBits w b := by
  have h := size_truncate_eq w b
  have h2 : (toMiriSize w).truncate b =
      .ok (BitVec.zeroExtend 128 (BitVec.extractLsb (w.bitWidth - 1) 0 b)) := by
    cases w <;> rfl
  rw [h2] at h
  injection h

private theorem miriScalar_eq_ofUInt (w' : IntWidth) (b : BitVec 128) :
    miriScalar w' b =
      match w' with
      | .i8 => ScalarInt.ofUInt8 (UInt8.ofNat (truncateBits .i8 b).toNat)
      | .i16 => ScalarInt.ofUInt16 (UInt16.ofNat (truncateBits .i16 b).toNat)
      | .i32 => ScalarInt.ofUInt32 (UInt32.ofNat (truncateBits .i32 b).toNat)
      | .i64 => ScalarInt.ofUInt64 (UInt64.ofNat (truncateBits .i64 b).toNat)
      | .isize =>
        ScalarInt.ofUInt64 (UInt64.ofNat (truncateBits .isize b).toNat)
      | .i128 => ScalarInt.ofUInt128 (truncateBits .i128 b) := by
  cases w' with
  | i8 =>
    have h_z := bitVec128_zeroExtend_extractLsb_eq_truncateBits .i8 b
    dsimp only [IntWidth.bitWidth, IntWidth.byteSize] at h_z
    have h_lt := bitVec128_toNat_truncateBits_lt .i8 b
    change (truncateBits .i8 b).toNat < HPow.hPow 2 8 at h_lt
    have h_eq :
        BitVec.ofNat 128 (UInt8.ofNat (truncateBits .i8 b).toNat).toNat =
          BitVec.zeroExtend 128 (BitVec.extractLsb 7 0 b) := by
      rw [h_z]
      apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat 128
        (BitVec.ofNat 8 (truncateBits .i8 b).toNat).toNat).toNat = _
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt,
          Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))]
    dsimp only [ScalarInt.ofUInt8]
    rw [h_eq]
    rfl
  | i16 =>
    have h_z := bitVec128_zeroExtend_extractLsb_eq_truncateBits .i16 b
    dsimp only [IntWidth.bitWidth, IntWidth.byteSize] at h_z
    have h_lt := bitVec128_toNat_truncateBits_lt .i16 b
    change (truncateBits .i16 b).toNat < HPow.hPow 2 16 at h_lt
    have h_eq :
        BitVec.ofNat 128 (UInt16.ofNat (truncateBits .i16 b).toNat).toNat =
          BitVec.zeroExtend 128 (BitVec.extractLsb 15 0 b) := by
      rw [h_z]
      apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat 128
        (BitVec.ofNat 16 (truncateBits .i16 b).toNat).toNat).toNat = _
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt,
          Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))]
    dsimp only [ScalarInt.ofUInt16]
    rw [h_eq]
    rfl
  | i32 =>
    have h_z := bitVec128_zeroExtend_extractLsb_eq_truncateBits .i32 b
    dsimp only [IntWidth.bitWidth, IntWidth.byteSize] at h_z
    have h_lt := bitVec128_toNat_truncateBits_lt .i32 b
    change (truncateBits .i32 b).toNat < HPow.hPow 2 32 at h_lt
    have h_eq :
        BitVec.ofNat 128 (UInt32.ofNat (truncateBits .i32 b).toNat).toNat =
          BitVec.zeroExtend 128 (BitVec.extractLsb 31 0 b) := by
      rw [h_z]
      apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat 128
        (BitVec.ofNat 32 (truncateBits .i32 b).toNat).toNat).toNat = _
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt,
          Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))]
    dsimp only [ScalarInt.ofUInt32]
    rw [h_eq]
    rfl
  | i64 =>
    have h_z := bitVec128_zeroExtend_extractLsb_eq_truncateBits .i64 b
    dsimp only [IntWidth.bitWidth, IntWidth.byteSize] at h_z
    have h_lt := bitVec128_toNat_truncateBits_lt .i64 b
    change (truncateBits .i64 b).toNat < HPow.hPow 2 64 at h_lt
    have h_eq :
        BitVec.ofNat 128 (UInt64.ofNat (truncateBits .i64 b).toNat).toNat =
          BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 b) := by
      rw [h_z]
      apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat 128
        (BitVec.ofNat 64 (truncateBits .i64 b).toNat).toNat).toNat = _
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt,
          Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))]
    dsimp only [ScalarInt.ofUInt64]
    rw [h_eq]
    rfl
  | isize =>
    have h_z := bitVec128_zeroExtend_extractLsb_eq_truncateBits .isize b
    dsimp only [IntWidth.bitWidth, IntWidth.byteSize] at h_z
    have h_lt := bitVec128_toNat_truncateBits_lt .isize b
    change (truncateBits .isize b).toNat < HPow.hPow 2 64 at h_lt
    have h_eq :
        BitVec.ofNat 128 (UInt64.ofNat (truncateBits .isize b).toNat).toNat =
          BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 b) := by
      rw [h_z]
      apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat 128
        (BitVec.ofNat 64 (truncateBits .isize b).toNat).toNat).toNat = _
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt,
          Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))]
    dsimp only [ScalarInt.ofUInt64]
    rw [h_eq]
    rfl
  | i128 =>
    have h_eq := bitVec128_zeroExtend_extractLsb_eq_truncateBits .i128 b
    dsimp only [IntWidth.bitWidth, IntWidth.byteSize] at h_eq
    dsimp only [ScalarInt.ofUInt128]
    rw [← h_eq]
    rfl

theorem miriScalar_truncateBits (w : IntWidth) (bits : BitVec 128) :
    miriScalar w (truncateBits w bits) = miriScalar w bits := by
  cases w <;>
    (rw [miriScalar_eq_ofUInt, miriScalar_eq_ofUInt];
     dsimp only;
     rw [truncateBits_idem])

theorem miriScalar_toBits_eq (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toBits (toMiriSize w) = .ok (truncateBits w bits) := by
  have h : (miriScalar w bits).toBits (toMiriSize w) =
      ((toMiriSize w).truncate bits).mapError ScalarIntError.sizeError := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  rfl

theorem scalar_fromUInt_of_truncateBits_beq {P : Type} {w : IntWidth}
    {b : BitVec 128} (h_eq : (truncateBits w b == b) = true) :
    Miri.Memory.Scalar.fromUInt (Prov := P) b (toMiriSize w) =
      .ok (.fromScalarInt (miriScalar w b)) := by
  have h_bne : (truncateBits w b != b) = false := by
    change (!(truncateBits w b == b)) = false
    rw [h_eq]; rfl
  dsimp only [Miri.Memory.Scalar.fromUInt]
  rw [tryFromUInt_eq_truncateFromUInt, truncateFromUInt_eq_miriScalar, h_bne]
  rfl

noncomputable def stepErrorToFaultKind :
    Miri.Interpreter.StepError → FaultKind
  | .undefinedBehavior _ => .undefined
  | .stack (.localExpectedLive _) => .undefined
  | _ => .unsupported

noncomputable def mapStepExcept {α : Type} :
    Except Miri.Interpreter.StepError α → Except FaultKind α
  | .ok x => .ok x
  | .error e => .error (stepErrorToFaultKind e)

def RefReadDiscrHooksSpec {S V : Type} (ety : EnumTy)
    (h : Miri.Interpreter.DiscriminantHooks Miri.Memory.Provenance S Unit V) :
    Prop :=
  h.runtimeTarget = Miri.ABI.RuntimeTargetDataLayout.default ∧
  h.discriminantLayout = (refDiscriminantHooks S ety).discriminantLayout ∧
  h.tagLayout = (refDiscriminantHooks S ety).tagLayout ∧
  h.variantForDiscriminant =
    (refDiscriminantHooks S ety).variantForDiscriminant ∧
  h.adtVariantCount = (refDiscriminantHooks S ety).adtVariantCount ∧
  h.projectRead = (refDiscriminantHooks S ety).projectRead ∧
  h.readImmediate = (refDiscriminantHooks S ety).readImmediate ∧
  h.scalarMayBeNull = (refDiscriminantHooks S ety).scalarMayBeNull

theorem refDiscriminantHooks_spec (S : Type) (ety : EnumTy) :
    RefReadDiscrHooksSpec ety (refDiscriminantHooks S ety) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem refWriteDiscriminantHooks_spec (S : Type)
    (getLocals : S → List RefLocalState) (ety : EnumTy) (variantIdx : Nat) :
    RefReadDiscrHooksSpec ety
      (refWriteDiscriminantHooks S getLocals (.enum ety) (some ety)
        variantIdx) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem readDiscriminant_eq_refDiscriminantHooks {S V : Type} (ety : EnumTy)
    (h : Miri.Interpreter.DiscriminantHooks Miri.Memory.Provenance S Unit V)
    (h_spec : RefReadDiscrHooksSpec ety h)
    (op : Miri.Interpreter.OpTy Miri.Memory.Provenance) (s : S) :
    Miri.Interpreter.Discriminant.readDiscriminant h () op s =
      Miri.Interpreter.Discriminant.readDiscriminant
        (refDiscriminantHooks S ety) () op s := by
  cases h with
  | mk rt dl tl dv vfd avc pr ri dstL pw ws toOp smbn =>
    let ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_spec
    dsimp only at h1 h2 h3 h4 h5 h6 h7 h8
    subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
    subst h8
    rfl

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
    (h_adm : enumAdmitted ety = true)
    (h_tr : ety.tagRepr = .scalar tagW tagS) :
    Miri.Interpreter.runRvalue
      (Miri.Interpreter.Discriminant.readDiscriminant
        (refDiscriminantHooks S ety) ()
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW raw))),
          ⟨0, refEnumLayoutData ety⟩⟩) s =
    match findDiscrVariant?
        (tagBitsToDiscrBits tagW tagS ety.discrWidth (truncateBits tagW raw))
        ety.discriminants with
    | some v =>
      if isVariantUninhabited ety v then
        (s, .error (.undefinedBehavior
          (toString "UninhabitedEnumVariantRead(" ++ toString v ++
            toString ")")))
      else
        (s, .ok v)
    | none =>
      (s, .error (.undefinedBehavior
        "InvalidTag(no declared discriminant)")) := by
  cases ety with
  | mk id discrW discrS tr ds vf =>
    dsimp only at h_tr
    subst h_tr
    let ety₀ := EnumTy.mk id discrW discrS (.scalar tagW tagS) ds vf
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
        rw [h₃, refEnumLayoutData_isVariantUninhabited_eq h_adm v]
        dsimp only [ety₀]
        cases isVariantUninhabited _ v <;> rfl
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
        rw [h₄, refEnumLayoutData_isVariantUninhabited_eq h_adm v]
        dsimp only [ety₀]
        cases isVariantUninhabited _ v <;> rfl

private theorem runRvalue_bind {S A B : Type}
    (m : Miri.Interpreter.RvalueM S A)
    (k : A → Miri.Interpreter.RvalueM S B) (s : S) :
    Miri.Interpreter.runRvalue (Bind.bind m k) s =
      match Miri.Interpreter.runRvalue m s with
      | (s', .ok a) => Miri.Interpreter.runRvalue (k a) s'
      | (s', .error e) => (s', .error e) := by
  dsimp only [Miri.Interpreter.runRvalue, Bind.bind, EStateM.bind]
  cases m s <;> rfl

private theorem runRvalue_pure {S A : Type} (a : A) (s : S) :
    Miri.Interpreter.runRvalue (Pure.pure a) s = (s, .ok a) := rfl

private noncomputable def liftStepExcept {S A : Type}
    (res : Except Miri.Interpreter.StepError A)
    (k : A → Miri.Interpreter.RvalueM S Nat) :
    Miri.Interpreter.RvalueM S Nat :=
  Bind.bind (match res with | .ok v => Pure.pure v | .error e => throw e) k

private noncomputable def runNicheTagAfterTrunc (S : Type) (ety₀ : EnumTy)
    (vs ve : BitVec 128) (untagged start last : Nat) (cleanBits : BitVec 128)
    (truncRes : Except SizeError (BitVec 128)) :
    Miri.Interpreter.RvalueM S Nat :=
  let jpOuter := fun (index : Nat) =>
    runDirectTagFinal S
      ((refEnumLayoutData ety₀).isVariantUninhabited index) index
  liftStepExcept
    (truncRes.mapError
      (fun e => Miri.Interpreter.StepError.invalidProgram (toString e)))
    (fun relative =>
      if relative.toNat ≤ last - start then
        let index := start + relative.toNat
        let jp1 : Unit → Miri.Interpreter.RvalueM S Nat := fun _ =>
          Bind.bind
            (Pure.pure ety₀.discriminants.length :
              Miri.Interpreter.RvalueM S Nat)
            (fun count =>
              let jp2 : Unit → Miri.Interpreter.RvalueM S Nat := fun _ =>
                Bind.bind (Pure.pure (WrappingRange.mk vs ve)) (fun range =>
                  let jp3 : Unit → Miri.Interpreter.RvalueM S Nat := fun _ =>
                    let jp4 : Unit → Miri.Interpreter.RvalueM S Nat := fun _ =>
                      Bind.bind (Pure.pure index) jpOuter
                    if index == untagged then
                      Bind.bind
                        (throw (.undefinedBehavior
                          "InvalidTag(untagged variant encoded in niche)"))
                        jp4
                    else
                      jp4 ()
                  if !range.contains cleanBits then
                    Bind.bind
                      (throw (.invalidProgram
                        "niche encoding violates tag valid range"))
                      jp3
                  else
                    jp3 ())
              if index ≥ count then
                Bind.bind
                  (throw (.invalidProgram
                    "niche variant outside ADT variant list"))
                  jp2
              else
                jp2 ())
        if index ≥ HPow.hPow 2 32 then
          Bind.bind
            (throw (.invalidProgram "absolute niche variant index overflow"))
            jp1
        else
          jp1 ()
      else
        Bind.bind (Pure.pure (WrappingRange.mk vs ve)) (fun range =>
          let jpOut : Unit → Miri.Interpreter.RvalueM S Nat := fun _ =>
            Bind.bind (Pure.pure untagged) jpOuter
          if !range.contains cleanBits then
            Bind.bind
              (throw (.undefinedBehavior "InvalidTag(outside valid range)"))
              jpOut
          else
            jpOut ()))

private noncomputable def runNicheTagAction (S : Type) (ety₀ : EnumTy)
    (tagW : IntWidth) (vs ve : BitVec 128) (untagged start last : Nat)
    (nicheStart : BitVec 128) (hdrBad : Bool)
    (bitsRes : Except ScalarIntError (BitVec 128))
    (nsRes : Except ScalarError (Miri.Memory.Scalar Miri.Memory.Provenance)) :
    Miri.Interpreter.RvalueM S Nat :=
  let jpHdr : Unit → Miri.Interpreter.RvalueM S Nat := fun _ =>
    liftStepExcept
      (bitsRes.mapError Miri.Interpreter.ScalarOps.scalarIntError)
      (fun bits =>
        liftStepExcept
          (nsRes.mapError Miri.Interpreter.ScalarOps.scalarError)
          (fun _ =>
            runNicheTagAfterTrunc S ety₀ vs ve untagged start last bits
              ((toMiriSize tagW).truncate (bits - nicheStart))))
  if hdrBad then
    Bind.bind (throw (.invalidProgram "invalid niche variant range")) jpHdr
  else
    jpHdr ()

theorem readDiscriminant_enum_niche_stateless (S : Type) (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (vs ve : BitVec 128)
    (nichePath : List Nat) (untagged start last : Nat)
    (nicheStart raw : BitVec 128) (s : S)
    (h_adm : enumAdmitted ety = true)
    (h_tr : ety.tagRepr =
      .niche tagW tagS vs ve nichePath untagged start last nicheStart) :
    let m :=
      Miri.Interpreter.Discriminant.readDiscriminant
        (refDiscriminantHooks S ety) ()
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW raw))),
          ⟨0, refEnumLayoutData ety⟩⟩
    (Miri.Interpreter.runRvalue m s).1 = s ∧
    mapStepExcept (Miri.Interpreter.runRvalue m s).2 =
      match decodeNicheTagBits tagW vs ve untagged start last nicheStart
          ety.discriminants.length raw with
      | .error fk => .error fk
      | .ok idx =>
        if isVariantUninhabited ety idx then
          .error .undefined
        else
          .ok idx := by
  have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
  rw [h_tr] at hc
  dsimp only at hc
  have h_dlen_lt : ety.discriminants.length < Nat.pow 2 32 :=
    nat_lt_of_blt_eq_true (enumAdmitted_discr_len_lt h_adm)
  have h_last_lt_d : last < ety.discriminants.length :=
    nat_lt_of_blt_eq_true
      (bool_and_right (bool_and_left (bool_and_left (bool_and_left
        (bool_and_left (bool_and_left (bool_and_left (bool_and_left
          (bool_and_left hc)))))))))
  have h_start_le_last : start ≤ last :=
    Nat.le_of_ble_eq_true
      (bool_and_right (bool_and_left (bool_and_left (bool_and_left
        (bool_and_left (bool_and_left (bool_and_left
          (bool_and_left hc))))))))
  have h_ns_fits : (truncateBits tagW nicheStart == nicheStart) = true :=
    bool_and_right (bool_and_left (bool_and_left (bool_and_left
      (bool_and_left hc))))
  have h_last_u32 : last < HPow.hPow 2 32 := Nat.lt_trans h_last_lt_d h_dlen_lt
  have h_start_u32 : start < HPow.hPow 2 32 :=
    Nat.lt_of_le_of_lt h_start_le_last h_last_u32
  have h_hdr_false :
      (decide (start ≥ HPow.hPow 2 32) || decide (last ≥ HPow.hPow 2 32) ||
        decide (last < start)) = false := by
    have h1 : decide (start ≥ HPow.hPow 2 32) = false :=
      decide_eq_false (Nat.not_le_of_gt h_start_u32)
    have h2 : decide (last ≥ HPow.hPow 2 32) = false :=
      decide_eq_false (Nat.not_le_of_gt h_last_u32)
    have h3 : decide (last < start) = false :=
      decide_eq_false (Nat.not_lt_of_ge h_start_le_last)
    rw [h1, h2, h3]; rfl
  have h_ns_ok :=
    scalar_fromUInt_of_truncateBits_beq
      (P := Miri.Memory.Provenance) h_ns_fits
  cases ety with
  | mk id discrW discrS tr ds vf =>
    dsimp only at h_tr
    subst h_tr
    let ety₀ := EnumTy.mk id discrW discrS
      (.niche tagW tagS vs ve nichePath untagged start last nicheStart) ds vf
    have h_step₁ :
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.Discriminant.readDiscriminant
            (refDiscriminantHooks S ety₀) ()
            ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW raw))),
              ⟨0, refEnumLayoutData ety₀⟩⟩) s =
        Miri.Interpreter.runRvalue
          (runNicheTagAction S ety₀ tagW vs ve untagged start last nicheStart
            (decide (start ≥ HPow.hPow 2 32) ||
              decide (last ≥ HPow.hPow 2 32) ||
              decide (last < start))
            ((miriScalar tagW raw).toBits (toMiriSize tagW))
            (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              nicheStart (toMiriSize tagW))) s := by
      cases tagW <;> cases tagS <;> cases discrW <;> rfl
    have h_step₂ :
        Miri.Interpreter.runRvalue
          (runNicheTagAction S ety₀ tagW vs ve untagged start last nicheStart
            false (.ok (truncateBits tagW raw))
            (.ok (.fromScalarInt (miriScalar tagW nicheStart)))) s =
        Miri.Interpreter.runRvalue
          (runNicheTagAfterTrunc S ety₀ vs ve untagged start last
            (truncateBits tagW raw)
            ((toMiriSize tagW).truncate
              ((truncateBits tagW raw) - nicheStart))) s := rfl
    dsimp only
    rw [h_step₁, h_hdr_false, miriScalar_toBits_eq, h_ns_ok, h_step₂,
        size_truncate_eq]
    let cleanBits := truncateBits tagW raw
    let relative := truncateBits tagW (cleanBits - nicheStart)
    change
      (Miri.Interpreter.runRvalue
        (runNicheTagAfterTrunc S ety₀ vs ve untagged start last cleanBits
          (.ok relative)) s).1 = s ∧
      mapStepExcept
        (Miri.Interpreter.runRvalue
          (runNicheTagAfterTrunc S ety₀ vs ve untagged start last cleanBits
            (.ok relative)) s).2 = _
    dsimp only [decodeNicheTagBits, runNicheTagAfterTrunc, liftStepExcept,
      Except.mapError]
    rw [runRvalue_bind, runRvalue_pure]
    dsimp only
    cases h_rel : Nat.ble relative.toNat (last - start) with
    | true =>
      have h_rel_le := Nat.le_of_ble_eq_true h_rel
      rw [ite_eq_left h_rel_le, ite_true_eq_true]
      let index := start + relative.toNat
      cases h_idx_u32 : Nat.blt index (Nat.pow 2 32) with
      | false =>
        have h_ge : index ≥ HPow.hPow 2 32 := by
          cases h_d : decide (index ≥ HPow.hPow 2 32) with
          | true => exact of_decide_eq_true h_d
          | false =>
            have h_lt : index < HPow.hPow 2 32 :=
              Nat.lt_of_not_le (of_decide_eq_false h_d)
            rw [nat_blt_eq_true_of_lt h_lt] at h_idx_u32
            cases h_idx_u32
        rw [ite_eq_left h_ge]
        exact ⟨rfl, rfl⟩
      | true =>
        have h_not_ge : ¬ (index ≥ HPow.hPow 2 32) :=
          Nat.not_le_of_gt (nat_lt_of_blt_eq_true h_idx_u32)
        rw [ite_eq_right h_not_ge]
        rw [runRvalue_bind, runRvalue_pure]
        dsimp only
        cases h_idx_cnt : Nat.blt index ds.length with
        | false =>
          have h_ge_cnt : index ≥ ds.length := by
            cases h_d : decide (index ≥ ds.length) with
            | true => exact of_decide_eq_true h_d
            | false =>
              have h_lt : index < ds.length :=
                Nat.lt_of_not_le (of_decide_eq_false h_d)
              rw [nat_blt_eq_true_of_lt h_lt] at h_idx_cnt
              cases h_idx_cnt
          rw [ite_eq_left h_ge_cnt]
          exact ⟨rfl, rfl⟩
        | true =>
          have h_not_ge_cnt : ¬ (index ≥ ds.length) :=
            Nat.not_le_of_gt (nat_lt_of_blt_eq_true h_idx_cnt)
          rw [ite_eq_right h_not_ge_cnt]
          simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true,
            ite_false]
          rw [runRvalue_bind, runRvalue_pure]
          dsimp only
          rw [wrappingRange_contains_eq]
          cases wrappingRangeContains vs ve cleanBits with
          | false => exact ⟨rfl, rfl⟩
          | true =>
            rw [Bool.not_true, ite_false_eq_true, ite_false_eq_true]
            have h_beq : (index == untagged) = Nat.beq index untagged :=
              decide_eq_nat_beq index untagged
            rw [h_beq]
            cases Nat.beq index untagged with
            | true => exact ⟨rfl, rfl⟩
            | false =>
              rw [ite_false_eq_true, ite_false_eq_true]
              rw [runRvalue_bind, runRvalue_pure]
              dsimp only [runDirectTagFinal]
              rw [refEnumLayoutData_isVariantUninhabited_eq h_adm index]
              cases isVariantUninhabited _ index <;> exact ⟨rfl, rfl⟩
    | false =>
      have h_nrel : ¬ (relative.toNat ≤ last - start) := by
        intro h_le; rw [Nat.ble_eq_true_of_le h_le] at h_rel; cases h_rel
      rw [ite_eq_right h_nrel, ite_false_eq_true]
      rw [runRvalue_bind, runRvalue_pure]
      dsimp only
      rw [wrappingRange_contains_eq]
      cases wrappingRangeContains vs ve cleanBits with
      | false => exact ⟨rfl, rfl⟩
      | true =>
        rw [Bool.not_true, ite_false_eq_true, ite_false_eq_true]
        rw [runRvalue_bind, runRvalue_pure]
        dsimp only [runDirectTagFinal]
        rw [refEnumLayoutData_isVariantUninhabited_eq h_adm untagged]
        cases isVariantUninhabited _ untagged <;> exact ⟨rfl, rfl⟩

private theorem intWidth_modulus_dvd_u128 (w : IntWidth) :
    ∃ q : Nat, (Nat.pow 2 w.bitWidth) * q = Nat.pow 2 128 := by
  cases w with
  | i8 => exact ⟨Nat.pow 2 120, by decide⟩
  | i16 => exact ⟨Nat.pow 2 112, by decide⟩
  | i32 => exact ⟨Nat.pow 2 96, by decide⟩
  | i64 => exact ⟨Nat.pow 2 64, by decide⟩
  | isize => exact ⟨Nat.pow 2 64, by decide⟩
  | i128 => exact ⟨1, by decide⟩

private theorem nat_mod_u128_mod_width (w : IntWidth) (x : Nat) :
    HMod.hMod (HMod.hMod x (Nat.pow 2 128)) (Nat.pow 2 w.bitWidth) =
      HMod.hMod x (Nat.pow 2 w.bitWidth) := by
  let ⟨q, hq⟩ := intWidth_modulus_dvd_u128 w
  have h_dvd : Dvd.dvd (Nat.pow 2 w.bitWidth) (Nat.pow 2 128) := ⟨q, hq.symm⟩
  exact Nat.mod_mod_of_dvd x h_dvd

private theorem nat_add_mod_right_mod (a b m : Nat) :
    HMod.hMod (a + HMod.hMod b m) m = HMod.hMod (a + b) m := by
  rw [Nat.add_mod a (HMod.hMod b m) m, Nat.mod_mod, ← Nat.add_mod a b m]

theorem truncateBits_sub_add_cancel (w : IntWidth) (k : Nat) (ns : BitVec 128)
    (hk : k < (Nat.pow 2 w.bitWidth)) :
    (truncateBits w (truncateBits w (BitVec.ofNat 128 k + ns) - ns)).toNat =
      k := by
  let ⟨q, hq⟩ := intWidth_modulus_dvd_u128 w
  have hk_u128 : k < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hk (intWidth_modulus_le_u128 w)
  let c := truncateBits w (BitVec.ofNat 128 k + ns)
  have hc_mod : HMod.hMod c.toNat (Nat.pow 2 w.bitWidth) =
      HMod.hMod (k + ns.toNat) (Nat.pow 2 w.bitWidth) := by
    dsimp only [c]
    have h_tn : HMod.hMod c.toNat (Nat.pow 2 w.bitWidth) = c.toNat := by
      dsimp only [c]
      rw [toNat_truncateBits]
      exact Nat.mod_eq_of_lt (Nat.mod_lt _ (intWidth_modulus_pos w))
    rw [h_tn, toNat_truncateBits]
    change HMod.hMod (BitVec.ofNat 128 k + ns).toNat (Nat.pow 2 w.bitWidth) = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hk_pow : k < HPow.hPow 2 128 := hk_u128
    rw [Nat.mod_eq_of_lt hk_pow]
    exact nat_mod_u128_mod_width w (k + ns.toNat)
  rw [toNat_truncateBits]
  change HMod.hMod (c - ns).toNat (Nat.pow 2 w.bitWidth) = k
  have h_sub_nat :
      (c - ns).toNat =
        HMod.hMod ((Nat.pow 2 128 - ns.toNat) + c.toNat) (Nat.pow 2 128) := by
    change (BitVec.ofNat 128 ((Nat.pow 2 128 - ns.toNat) + c.toNat)).toNat = _
    exact BitVec.toNat_ofNat _ _
  have hns_lt : ns.toNat < Nat.pow 2 128 := ns.isLt
  rw [h_sub_nat, nat_mod_u128_mod_width w,
      ← nat_add_mod_right_mod (Nat.pow 2 128 - ns.toNat) c.toNat (Nat.pow 2 w.bitWidth),
      hc_mod,
      nat_add_mod_right_mod (Nat.pow 2 128 - ns.toNat) (k + ns.toNat) (Nat.pow 2 w.bitWidth),
      Nat.add_comm k ns.toNat, ← Nat.add_assoc,
      Nat.sub_add_cancel (Nat.le_of_lt hns_lt),
      ← hq, Nat.add_comm ((Nat.pow 2 w.bitWidth) * q) k,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

theorem allNicheTagsInValidRange_at {tagW : IntWidth}
    {vs ve nicheStart : BitVec 128} :
    ∀ {n k : Nat},
      allNicheTagsInValidRange tagW vs ve nicheStart n = true →
      k < n →
      wrappingRangeContains vs ve
        (truncateBits tagW (BitVec.ofNat 128 k + nicheStart)) = true
  | 0, _, _, hk => nomatch hk
  | m + 1, k, h_all, hk => by
    have h_step :
        (allNicheTagsInValidRange tagW vs ve nicheStart m &&
          wrappingRangeContains vs ve
            (truncateBits tagW (BitVec.ofNat 128 m + nicheStart))) = true :=
      h_all
    cases h_km : Nat.beq k m with
    | true =>
      have h_eq := Nat.eq_of_beq_eq_true h_km
      subst h_eq
      exact bool_and_right h_step
    | false =>
      have h_ne : k ≠ m := by
        intro h_eq; subst h_eq; rw [Nat.beq_refl] at h_km; cases h_km
      have hk_lt : k < m :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) h_ne
      exact allNicheTagsInValidRange_at (bool_and_left h_step) hk_lt

theorem decodeNicheTagBits_niche_variant {ety : EnumTy}
    {tagW : IntWidth} {tagS : Bool} {vs ve : BitVec 128}
    {nichePath : List Nat} {untagged start last : Nat}
    {nicheStart : BitVec 128} {v : Nat}
    (h_adm : enumAdmitted ety = true)
    (h_tr : ety.tagRepr =
      .niche tagW tagS vs ve nichePath untagged start last nicheStart)
    (h_ne_u : Nat.beq v untagged = false)
    (h_lo : Nat.ble start v = true)
    (h_hi : Nat.ble v last = true) :
    decodeNicheTagBits tagW vs ve untagged start last nicheStart
      ety.discriminants.length
      (BitVec.ofNat 128 (v - start) + nicheStart) = .ok v := by
  have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
  rw [h_tr] at hc
  dsimp only at hc
  have h_dlen_lt : ety.discriminants.length < Nat.pow 2 32 :=
    nat_lt_of_blt_eq_true (enumAdmitted_discr_len_lt h_adm)
  have h_last_lt_d : last < ety.discriminants.length :=
    nat_lt_of_blt_eq_true
      (bool_and_right (bool_and_left (bool_and_left (bool_and_left
        (bool_and_left (bool_and_left (bool_and_left (bool_and_left
          (bool_and_left hc)))))))))
  have h_span_mod : last - start < (Nat.pow 2 tagW.bitWidth) :=
    nat_lt_of_blt_eq_true
      (bool_and_right (bool_and_left (bool_and_left (bool_and_left hc))))
  have h_tags_vr :
      allNicheTagsInValidRange tagW vs ve nicheStart (last - start + 1) =
        true :=
    bool_and_right (bool_and_left (bool_and_left hc))
  have hv_ge : start ≤ v := Nat.le_of_ble_eq_true h_lo
  have hv_le : v ≤ last := Nat.le_of_ble_eq_true h_hi
  have hk_le : v - start ≤ last - start := Nat.sub_le_sub_right hv_le start
  have hk_mod : v - start < (Nat.pow 2 tagW.bitWidth) :=
    Nat.lt_of_le_of_lt hk_le h_span_mod
  have h_rel :=
    truncateBits_sub_add_cancel tagW (v - start) nicheStart hk_mod
  have h_add_sub : start + (v - start) = v := by
    rw [Nat.add_comm, Nat.sub_add_cancel hv_ge]
  have hv_lt_d : v < ety.discriminants.length :=
    Nat.lt_of_le_of_lt hv_le h_last_lt_d
  have hv_lt_u32 : v < Nat.pow 2 32 := Nat.lt_trans hv_lt_d h_dlen_lt
  have h_vr := allNicheTagsInValidRange_at h_tags_vr
    (Nat.lt_succ_of_le hk_le)
  dsimp only [decodeNicheTagBits]
  rw [h_rel, Nat.ble_eq_true_of_le hk_le, ite_true_eq_true, h_add_sub,
      nat_blt_eq_true_of_lt hv_lt_u32, nat_blt_eq_true_of_lt hv_lt_d,
      h_vr, h_ne_u]
  rfl

theorem refExtractSlotNicheBits_eq (sv : SlotVal) (path : List Nat) :
    refExtractSlotNicheBits sv path = extractSlotNicheBits sv path := by
  induction path generalizing sv with
  | nil =>
    cases sv with
    | scalar sc =>
      dsimp only [refExtractSlotNicheBits, extractSlotNicheBits]
      rw [miriScalar_data]
    | enumVal innerEty innerVar innerFs =>
      cases innerFs with
      | cons _ _ => rfl
      | nil =>
        dsimp only [refExtractSlotNicheBits, extractSlotNicheBits]
        cases innerEty.tagRepr with
        | scalar w _ =>
          cases MirSemantics.getElem? innerEty.discriminants innerVar with
          | none => rfl
          | some d =>
            dsimp only
            rw [miriScalar_data]
        | _ => rfl
    | _ => rfl
  | cons idx rest ih =>
    cases sv with
    | structVal _ fs =>
      dsimp only [refExtractSlotNicheBits, extractSlotNicheBits]
      cases MirSemantics.getElem? fs idx with
      | none => rfl
      | some fSv => exact ih fSv
    | tuple fs =>
      dsimp only [refExtractSlotNicheBits, extractSlotNicheBits]
      cases MirSemantics.getElem? fs idx with
      | none => rfl
      | some fSv => exact ih fSv
    | array _ elems =>
      dsimp only [refExtractSlotNicheBits, extractSlotNicheBits]
      cases MirSemantics.getElem? elems idx with
      | none => rfl
      | some eSv => exact ih eSv
    | enumVal _ _ fs => cases fs <;> rfl
    | _ => rfl

theorem refExtractSlotNicheBitsFromFields_eq (nichePath : List Nat)
    (fields : List SlotVal) :
    refExtractSlotNicheBitsFromFields nichePath fields =
      extractSlotNicheBitsFromFields nichePath fields := by
  cases nichePath with
  | nil => rfl
  | cons idx rest =>
    dsimp only [refExtractSlotNicheBitsFromFields,
      extractSlotNicheBitsFromFields]
    cases MirSemantics.getElem? fields idx with
    | none => rfl
    | some fSv => exact refExtractSlotNicheBits_eq fSv rest

theorem refExtractValNicheBits_eq (v : Val) (path : List Nat) :
    refExtractValNicheBits v path = extractValNicheBits v path := by
  induction path generalizing v with
  | nil =>
    cases v with
    | scalar sc =>
      dsimp only [refExtractValNicheBits, extractValNicheBits]
      rw [miriScalar_data]
    | enumVal innerEty innerVar innerFs =>
      cases innerFs with
      | cons _ _ => rfl
      | nil =>
        dsimp only [refExtractValNicheBits, extractValNicheBits]
        rw [list_getElem?_eq_getElem?]
        cases innerEty.tagRepr with
        | scalar w _ =>
          cases MirSemantics.getElem? innerEty.discriminants innerVar with
          | none => rfl
          | some d =>
            dsimp only
            rw [miriScalar_data]
        | _ => rfl
    | _ => rfl
  | cons idx rest ih =>
    cases v with
    | structVal _ fs =>
      dsimp only [refExtractValNicheBits, extractValNicheBits]
      rw [list_getElem?_eq_getElem?]
      cases MirSemantics.getElem? fs idx with
      | none => rfl
      | some fVal => exact ih fVal
    | tuple fs =>
      dsimp only [refExtractValNicheBits, extractValNicheBits]
      rw [list_getElem?_eq_getElem?]
      cases MirSemantics.getElem? fs idx with
      | none => rfl
      | some fVal => exact ih fVal
    | array _ elems =>
      dsimp only [refExtractValNicheBits, extractValNicheBits]
      rw [list_getElem?_eq_getElem?]
      cases MirSemantics.getElem? elems idx with
      | none => rfl
      | some eVal => exact ih eVal
    | enumVal _ _ fs => cases fs <;> rfl
    | _ => rfl

theorem refExtractValNicheBitsFromFields_eq (nichePath : List Nat)
    (fields : List Val) :
    refExtractValNicheBitsFromFields nichePath fields =
      extractValNicheBitsFromFields nichePath fields := by
  cases nichePath with
  | nil => rfl
  | cons idx rest =>
    dsimp only [refExtractValNicheBitsFromFields,
      extractValNicheBitsFromFields]
    rw [list_getElem?_eq_getElem?]
    cases MirSemantics.getElem? fields idx with
    | none => rfl
    | some fVal => exact refExtractValNicheBits_eq fVal rest

theorem list_all_of_getElem? {α : Type} {xs : List α} {p : α → Bool}
    {i : Nat} {x : α} (h_all : xs.all p = true)
    (h_get : MirSemantics.getElem? xs i = some x) : p x = true := by
  induction xs generalizing i with
  | nil => cases h_get
  | cons y rest ih =>
    dsimp only [List.all] at h_all
    cases hy : p y <;> rw [hy] at h_all
    · cases h_all
    · cases i with
      | zero =>
        injection h_get with h_eq
        subst h_eq
        exact hy
      | succ j =>
        exact ih h_all h_get

theorem natNotElem_ne_of_getElem? {d : Nat} {xs : List Nat} {i : Nat}
    {x : Nat} (h_not : natNotElem d xs = true)
    (h_get : MirSemantics.getElem? xs i = some x) : d ≠ x := by
  induction xs generalizing i with
  | nil => cases h_get
  | cons y rest ih =>
    dsimp only [natNotElem] at h_not
    cases h_eq : Nat.beq d y <;> rw [h_eq] at h_not
    · cases i with
      | zero =>
        injection h_get with hyx
        subst hyx
        intro h_dx
        subst h_dx
        rw [Nat.beq_refl] at h_eq
        cases h_eq
      | succ j =>
        exact ih h_not h_get
    · cases h_not

theorem findDiscrVariantAux_of_getElem? {w : IntWidth}
    {ds : List Nat} {idx : Nat} {disc : Nat} (k : Nat)
    (h_all : ds.all (fun d => Nat.blt d (Nat.pow 2 w.bitWidth)) = true)
    (h_pw : natListPairwiseNe ds = true)
    (h_get : MirSemantics.getElem? ds idx = some disc) :
    findDiscrVariantAux k (BitVec.ofNat 128 disc) ds = some (k + idx) := by
  induction ds generalizing k idx with
  | nil => cases h_get
  | cons d rest ih =>
    dsimp only [List.all] at h_all
    cases hd_blt : Nat.blt d (Nat.pow 2 w.bitWidth) <;> rw [hd_blt] at h_all
    · cases h_all
    · dsimp only [natListPairwiseNe] at h_pw
      cases h_not : natNotElem d rest <;> rw [h_not] at h_pw
      · cases h_pw
      · have h_all' : rest.all (fun d => Nat.blt d (Nat.pow 2 w.bitWidth)) = true := h_all
        have h_pw' : natListPairwiseNe rest = true := h_pw
        cases idx with
        | zero =>
          injection h_get with h_eq
          subst h_eq
          dsimp only [findDiscrVariantAux]
          have h_self :
              (BitVec.ofNat 128 d == BitVec.ofNat 128 d) = true :=
            beq_self_eq_true _
          rw [h_self, Nat.add_zero]
          rfl
        | succ j =>
          dsimp only [MirSemantics.getElem?] at h_get
          have h_ne : d ≠ disc := natNotElem_ne_of_getElem? h_not h_get
          have hd_u128 : d < Nat.pow 2 128 :=
            Nat.lt_of_lt_of_le (nat_lt_of_blt_eq_true hd_blt)
              (intWidth_modulus_le_u128 w)
          have hdisc_blt : Nat.blt disc (Nat.pow 2 w.bitWidth) = true :=
            @list_all_of_getElem? Nat rest (fun d => Nat.blt d (Nat.pow 2 w.bitWidth))
              j disc h_all' h_get
          have hdisc_u128 : disc < Nat.pow 2 128 :=
            Nat.lt_of_lt_of_le (nat_lt_of_blt_eq_true hdisc_blt)
              (intWidth_modulus_le_u128 w)
          have h_bv_false :
              (BitVec.ofNat 128 d == BitVec.ofNat 128 disc) = false := by
            cases h_b : (BitVec.ofNat 128 d == BitVec.ofNat 128 disc) with
            | false => rfl
            | true =>
              have h_tn := congrArg BitVec.toNat (eq_of_beq h_b)
              rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hd_u128, Nat.mod_eq_of_lt hdisc_u128] at h_tn
              exact False.elim (h_ne h_tn)
          dsimp only [findDiscrVariantAux]
          rw [h_bv_false, ite_false_eq_true]
          rw [ih (k + 1) h_all' h_pw' h_get, Nat.add_right_comm k 1 j,
              Nat.add_assoc]

theorem findDiscrVariant?_of_getElem? {w : IntWidth}
    {ds : List Nat} {idx : Nat} {disc : Nat}
    (h_all : ds.all (fun d => Nat.blt d (Nat.pow 2 w.bitWidth)) = true)
    (h_pw : natListPairwiseNe ds = true)
    (h_get : MirSemantics.getElem? ds idx = some disc) :
    findDiscrVariant? (BitVec.ofNat 128 disc) ds = some idx := by
  have h := findDiscrVariantAux_of_getElem? 0 h_all h_pw h_get
  rw [Nat.zero_add] at h
  exact h

private theorem readDiscr_uninit_multiple_err (S : Type) (ety : EnumTy)
    (tag : Miri.ABI.Scalar) (enc : Miri.ABI.TagEncoding)
    (vars : Array Miri.ABI.VariantLayout) (uninh : Bool) (s : S)
    (tagW : IntWidth) (tagS : Bool)
    (h_tag : tag.primitive = .Int (toMiriInteger tagW) tagS) :
    Miri.Interpreter.runRvalue
      (Miri.Interpreter.Discriminant.readDiscriminant
        (refDiscriminantHooks S ety) ()
        ⟨.immediate .uninit,
          ⟨0, { refScalarLayoutData tagW tagS with
                variants := .Multiple tag enc 0 vars
                uninhabited := uninh }⟩⟩) s =
      (s, .error (.undefinedBehavior "InvalidUninitBytes(None)")) := by
  cases tag <;> (
    dsimp only [Miri.ABI.Scalar.primitive] at h_tag
    subst h_tag
    cases tagW <;> cases tagS <;> rfl)

theorem readDiscriminant_encodeRefEnumTagOp_stateless {S V : Type}
    (ety : EnumTy) (sv : SlotVal) (s : S)
    (h : Miri.Interpreter.DiscriminantHooks Miri.Memory.Provenance S Unit V)
    (h_spec : RefReadDiscrHooksSpec ety h)
    (h_adm : enumAdmitted ety = true) :
    let act : Miri.Interpreter.RvalueM S Nat :=
      match encodeRefEnumTagOp ety sv with
      | .error err => throw err
      | .ok op => Miri.Interpreter.Discriminant.readDiscriminant h () op
    (Miri.Interpreter.runRvalue act s).1 = s ∧
    mapStepExcept (Miri.Interpreter.runRvalue act s).2 =
      evalReadDiscriminantVariant ety sv := by
  dsimp only [encodeRefEnumTagOp, evalReadDiscriminantVariant]
  cases h_tr : ety.tagRepr with
  | zeroSized =>
    have h_single :
        Miri.Interpreter.Discriminant.readDiscriminant h ()
          ⟨.immediate .uninit, ⟨0, refEnumLayoutData ety⟩⟩ s =
        if isTypeUninhabited (.enum ety) then
          .error (.undefinedBehavior
            (toString "UninhabitedEnumVariantRead(" ++ toString (0 : Nat) ++
              toString ")")) s
        else
          .ok 0 s := by
      rw [readDiscriminant_eq_refDiscriminantHooks ety h h_spec]
      dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
        refDiscriminantHooks, refEnumLayoutData, LayoutData.isUninhabited,
        Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
      rw [h_tr]
      dsimp only
      rw [refIsTypeUninhabited_eq]
      cases isTypeUninhabited (.enum ety) <;> rfl
    cases sv with
    | uninit =>
      dsimp only [Miri.Interpreter.runRvalue]
      rw [h_single]
      cases isTypeUninhabited (.enum ety) <;> exact ⟨rfl, rfl⟩
    | enumVal ety' v fs =>
      cases fs with
      | cons _ _ => exact ⟨rfl, rfl⟩
      | nil =>
        dsimp only
        cases (EnumTy.beq ety ety' && Nat.beq v 0) with
        | false => exact ⟨rfl, rfl⟩
        | true =>
          dsimp only [ite_true_eq_true, Miri.Interpreter.runRvalue]
          rw [h_single]
          cases isTypeUninhabited (.enum ety) <;> exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩
  | single v₀ =>
    have h_single :
        Miri.Interpreter.Discriminant.readDiscriminant h ()
          ⟨.immediate .uninit, ⟨0, refEnumLayoutData ety⟩⟩ s =
        if isTypeUninhabited (.enum ety) then
          .error (.undefinedBehavior
            (toString "UninhabitedEnumVariantRead(" ++ toString v₀ ++
              toString ")")) s
        else
          .ok v₀ s := by
      rw [readDiscriminant_eq_refDiscriminantHooks ety h h_spec]
      dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
        refDiscriminantHooks, refEnumLayoutData, LayoutData.isUninhabited,
        Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
      rw [h_tr]
      dsimp only
      rw [refIsTypeUninhabited_eq]
      cases isTypeUninhabited (.enum ety) <;> rfl
    cases sv with
    | uninit =>
      dsimp only [Miri.Interpreter.runRvalue]
      rw [h_single]
      cases isTypeUninhabited (.enum ety) <;> exact ⟨rfl, rfl⟩
    | enumVal ety' v _ | enumUntagged ety' v _ =>
      dsimp only
      cases (EnumTy.beq ety ety' && Nat.beq v v₀) with
      | false => exact ⟨rfl, rfl⟩
      | true =>
        dsimp only [ite_true_eq_true, Miri.Interpreter.runRvalue]
        rw [h_single]
        cases isTypeUninhabited (.enum ety) <;> exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩
  | scalar tagW tagS =>
    have h_uninit :
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.Discriminant.readDiscriminant h ()
            ⟨.immediate .uninit, ⟨0, refEnumLayoutData ety⟩⟩) s =
          (s, .error (.undefinedBehavior "InvalidUninitBytes(None)")) := by
      dsimp only [Miri.Interpreter.runRvalue]
      rw [readDiscriminant_eq_refDiscriminantHooks ety h h_spec]
      dsimp only [refEnumLayoutData]
      rw [h_tr]
      dsimp only
      exact readDiscr_uninit_multiple_err S ety
        (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct
        (Array.mk (refVariantLayoutsLoop ety 0 ety.discriminants))
        (refIsTypeUninhabited (.enum ety)) s tagW tagS rfl
    cases sv with
    | uninit | enumUntagged _ _ _ =>
      dsimp only
      rw [h_uninit]
      exact ⟨rfl, rfl⟩
    | enumVal ety' v _ =>
      dsimp only
      cases h_cond : (EnumTy.beq ety ety' &&
          Nat.blt v ety.discriminants.length) with
      | false => exact ⟨rfl, rfl⟩
      | true =>
        dsimp only [ite_true_eq_true]
        have hv_lt : v < ety.discriminants.length :=
          nat_lt_of_blt_eq_true (bool_and_right h_cond)
        let ⟨disc, h_disc⟩ := getElem?_some_of_lt ety.discriminants v hv_lt
        rw [h_disc]
        dsimp only
        rw [truncateFromUInt_eq_miriScalar]
        dsimp only [Miri.Interpreter.runRvalue]
        rw [readDiscriminant_eq_refDiscriminantHooks ety h h_spec]
        have h_rd :=
          readDiscriminant_enum_scalar_eq S ety tagW tagS
            (BitVec.ofNat 128 disc) s h_adm h_tr
        dsimp only [Miri.Interpreter.runRvalue] at h_rd
        have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
        rw [h_tr] at hc
        dsimp only at hc
        have h_recov := eq_of_beq
          (@list_all_of_getElem? Nat ety.discriminants
            (fun d =>
              tagBitsToDiscrBits tagW tagS ety.discrWidth
                (truncateBits tagW (BitVec.ofNat 128 d)) ==
              BitVec.ofNat 128 d)
            v disc hc h_disc)
        have h_find := findDiscrVariant?_of_getElem?
          (enumAdmitted_discr_in_bounds h_adm)
          (enumAdmitted_pairwiseNe h_adm) h_disc
        rw [h_recov, h_find] at h_rd
        dsimp only at h_rd
        cases h_uv : isVariantUninhabited ety v with
        | true =>
          rw [h_uv, ite_true_eq_true] at h_rd
          cases h_m : Miri.Interpreter.Discriminant.readDiscriminant
              (refDiscriminantHooks S ety) ()
              ⟨.immediate (.scalar (.fromScalarInt
                  (miriScalar tagW (BitVec.ofNat 128 disc)))),
                ⟨0, refEnumLayoutData ety⟩⟩ s with
          | ok a s' => rw [h_m] at h_rd; cases h_rd
          | error e s' =>
            rw [h_m] at h_rd
            injection h_rd with hs he
            injection he with he'
            subst hs; subst he'
            exact ⟨rfl, rfl⟩
        | false =>
          rw [h_uv, ite_false_eq_true] at h_rd
          cases h_m : Miri.Interpreter.Discriminant.readDiscriminant
              (refDiscriminantHooks S ety) ()
              ⟨.immediate (.scalar (.fromScalarInt
                  (miriScalar tagW (BitVec.ofNat 128 disc)))),
                ⟨0, refEnumLayoutData ety⟩⟩ s with
          | error e s' => rw [h_m] at h_rd; cases h_rd
          | ok a s' =>
            rw [h_m] at h_rd
            injection h_rd with hs ha
            injection ha with ha'
            subst hs; subst ha'
            exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩
  | niche tagW tagS vs ve nichePath untagged start last nicheStart =>
    have h_uninit :
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.Discriminant.readDiscriminant h ()
            ⟨.immediate .uninit, ⟨0, refEnumLayoutData ety⟩⟩) s =
          (s, .error (.undefinedBehavior "InvalidUninitBytes(None)")) := by
      dsimp only [Miri.Interpreter.runRvalue]
      rw [readDiscriminant_eq_refDiscriminantHooks ety h h_spec]
      dsimp only [refEnumLayoutData]
      rw [h_tr]
      dsimp only
      exact readDiscr_uninit_multiple_err S ety
        (.Initialized (value := .Int (toMiriInteger tagW) tagS)
          (validRange := ⟨vs, ve⟩))
        (.Niche untagged start last nicheStart)
        (Array.mk (refVariantLayoutsLoop ety 0 ety.discriminants))
        (refIsTypeUninhabited (.enum ety)) s tagW tagS rfl
    have h_niche_bits : ∀ (bits : BitVec 128),
        let m := Miri.Interpreter.Discriminant.readDiscriminant h ()
          ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW bits))),
            ⟨0, refEnumLayoutData ety⟩⟩
        (Miri.Interpreter.runRvalue m s).1 = s ∧
        mapStepExcept (Miri.Interpreter.runRvalue m s).2 =
          match decodeNicheTagBits tagW vs ve untagged start last nicheStart
              ety.discriminants.length bits with
          | .error fk => .error fk
          | .ok idx =>
            if isVariantUninhabited ety idx then
              .error .undefined
            else
              .ok idx := by
      intro bits
      have h_eq_m :
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.Discriminant.readDiscriminant h ()
              ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW bits))),
                ⟨0, refEnumLayoutData ety⟩⟩) s =
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.Discriminant.readDiscriminant
              (refDiscriminantHooks S ety) ()
              ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW bits))),
                ⟨0, refEnumLayoutData ety⟩⟩) s := by
        dsimp only [Miri.Interpreter.runRvalue]
        rw [readDiscriminant_eq_refDiscriminantHooks ety h h_spec]
      dsimp only
      rw [h_eq_m]
      exact readDiscriminant_enum_niche_stateless S ety tagW tagS vs ve
        nichePath untagged start last nicheStart bits s h_adm h_tr
    cases sv with
    | uninit =>
      dsimp only
      rw [h_uninit]
      exact ⟨rfl, rfl⟩
    | enumVal ety' v fields =>
      dsimp only
      cases EnumTy.beq ety ety' with
      | false => exact ⟨rfl, rfl⟩
      | true =>
        rw [Bool.not_true, ite_false_eq_true]
        cases h_vu : Nat.beq v untagged with
        | true =>
          rw [ite_true_eq_true, refExtractSlotNicheBitsFromFields_eq]
          cases extractSlotNicheBitsFromFields nichePath fields with
          | error fk =>
            cases fk with
            | undefined =>
              dsimp only
              rw [h_uninit]
              exact ⟨rfl, rfl⟩
            | unsupported => exact ⟨rfl, rfl⟩
          | ok bits =>
            dsimp only
            rw [truncateFromUInt_eq_miriScalar]
            exact h_niche_bits bits
        | false =>
          rw [ite_false_eq_true]
          cases h_sv : Nat.ble start v with
          | false => exact ⟨rfl, rfl⟩
          | true =>
            cases h_vl : Nat.ble v last with
            | false => exact ⟨rfl, rfl⟩
            | true =>
              dsimp only [Bool.and, ite_true_eq_true]
              rw [truncateFromUInt_eq_miriScalar]
              dsimp only
              have h_nb := h_niche_bits
                (BitVec.ofNat 128 (v - start) + nicheStart)
              rw [decodeNicheTagBits_niche_variant h_adm h_tr h_vu h_sv h_vl]
                at h_nb
              exact h_nb
    | enumUntagged ety' v fields =>
      dsimp only
      cases EnumTy.beq ety ety' with
      | false => exact ⟨rfl, rfl⟩
      | true =>
        rw [Bool.not_true, ite_false_eq_true]
        cases h_vu : Nat.beq v untagged with
        | true =>
          rw [ite_true_eq_true, refExtractSlotNicheBitsFromFields_eq]
          cases extractSlotNicheBitsFromFields nichePath fields with
          | error fk =>
            cases fk with
            | undefined =>
              dsimp only
              rw [h_uninit]
              exact ⟨rfl, rfl⟩
            | unsupported => exact ⟨rfl, rfl⟩
          | ok bits =>
            dsimp only
            rw [truncateFromUInt_eq_miriScalar]
            exact h_niche_bits bits
        | false =>
          rw [ite_false_eq_true]
          dsimp only
          rw [h_uninit]
          exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩

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
  | adtStruct sty =>
    cases lit with
    | scalar _ => rfl
    | zeroSized =>
      dsimp only [evalRefConstLit, evalConstLit]
      rw [refAreSupportedFieldTys_eq, refAreAllZeroSizedTys_eq,
          refIsTypeUninhabited_eq, refUninitSlotVal_eq]
      rfl
  | array elemTy len =>
    cases len with
    | succ _ => cases lit <;> rfl
    | zero =>
      cases lit with
      | scalar _ => rfl
      | zeroSized =>
        change (if refIsSupportedLocalTy elemTy then
            Except.ok (Val.array elemTy [])
          else Except.error FaultKind.unsupported) =
          (if isSupportedScalarOrUnitTy elemTy then
            Except.ok (Val.array elemTy [])
          else Except.error FaultKind.unsupported)
        rw [refIsSupportedLocalTy_eq]
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
      simp only [refIsZstEnumTy_eq, refEnumAdmitted_eq,
        refIsVariantUninhabited_eq, refFieldsForVariant?_eq]
      rfl
    | scalar bits =>
      dsimp only [evalRefConstLit, evalConstLit]
      rw [refEnumAdmitted_eq]
      cases h_adm : enumAdmitted ety with
      | false => rfl
      | true =>
        rw [Bool.not_true, ite_false_eq_true, ite_false_eq_true]
        cases h_tr : ety.tagRepr with
        | zeroSized | single _ => rfl
        | scalar tagW tagS =>
          dsimp only
          rw [tryFromUInt_eq_truncateFromUInt,
              truncateFromUInt_eq_miriScalar tagW bits]
          dsimp only [bind, Except.bind, pure, Except.pure]
          cases h_ov : (truncateBits tagW bits != bits) with
          | true => rfl
          | false =>
            rw [ite_false_eq_true]
            dsimp only
            let m := Miri.Interpreter.Discriminant.readDiscriminant
              (refDiscriminantHooks Unit ety) ()
              ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW bits))),
                ⟨0, refEnumLayoutData ety⟩⟩
            have h_m :
                (match m () with
                | .ok v _ =>
                  match refFieldsForVariant? ety v with
                  | some [] => Except.ok (Val.enumVal ety v [])
                  | _ => Except.error FaultKind.unsupported
                | .error (.undefinedBehavior _) _
                | .error (.stack (.localExpectedLive _)) _ =>
                  Except.error FaultKind.undefined
                | .error _ _ => Except.error FaultKind.unsupported) =
                (match (Miri.Interpreter.runRvalue m ()).2 with
                | .ok v =>
                  match fieldsForVariant? ety v with
                  | some [] => Except.ok (Val.enumVal ety v [])
                  | _ => Except.error FaultKind.unsupported
                | .error (.undefinedBehavior _)
                | .error (.stack (.localExpectedLive _)) =>
                  Except.error FaultKind.undefined
                | .error _ => Except.error FaultKind.unsupported) := by
              dsimp only [Miri.Interpreter.runRvalue]
              cases m () with
              | ok v _ => dsimp only; rw [refFieldsForVariant?_eq]
              | error e _ =>
                cases e with
                | undefinedBehavior _ => rfl
                | stack se => cases se <;> rfl
                | _ => rfl
            change (match m () with
                | .ok v _ =>
                  match refFieldsForVariant? ety v with
                  | some [] => Except.ok (Val.enumVal ety v [])
                  | _ => Except.error FaultKind.unsupported
                | .error (.undefinedBehavior _) _
                | .error (.stack (.localExpectedLive _)) _ =>
                  Except.error FaultKind.undefined
                | .error _ _ => Except.error FaultKind.unsupported) = _
            rw [h_m]
            rw [readDiscriminant_enum_scalar_eq Unit ety tagW tagS bits
              () h_adm h_tr]
            rw [truncateBits_eq_of_beq_false h_ov]
            cases findDiscrVariant?
                (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
                ety.discriminants with
            | none => rfl
            | some v =>
              dsimp only
              cases isVariantUninhabited ety v <;> rfl
        | niche tagW tagS vs ve nichePath untagged start last nicheStart =>
          dsimp only
          rw [tryFromUInt_eq_truncateFromUInt,
              truncateFromUInt_eq_miriScalar tagW bits]
          dsimp only [bind, Except.bind, pure, Except.pure]
          cases h_ov : (truncateBits tagW bits != bits) with
          | true => rfl
          | false =>
            rw [ite_false_eq_true]
            dsimp only
            let m := Miri.Interpreter.Discriminant.readDiscriminant
              (refDiscriminantHooks Unit ety) ()
              ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW bits))),
                ⟨0, refEnumLayoutData ety⟩⟩
            have h_m :
                (match m () with
                | .ok v _ =>
                  match refFieldsForVariant? ety v with
                  | some [] => Except.ok (Val.enumVal ety v [])
                  | _ => Except.error FaultKind.unsupported
                | .error (.undefinedBehavior _) _
                | .error (.stack (.localExpectedLive _)) _ =>
                  Except.error FaultKind.undefined
                | .error _ _ => Except.error FaultKind.unsupported) =
                (match mapStepExcept (Miri.Interpreter.runRvalue m ()).2 with
                | .ok v =>
                  match fieldsForVariant? ety v with
                  | some [] => Except.ok (Val.enumVal ety v [])
                  | _ => Except.error FaultKind.unsupported
                | .error k => Except.error k) := by
              dsimp only [Miri.Interpreter.runRvalue, mapStepExcept]
              cases m () with
              | ok v _ => dsimp only; rw [refFieldsForVariant?_eq]
              | error e _ =>
                cases e with
                | undefinedBehavior _ => rfl
                | stack se => cases se <;> rfl
                | _ => rfl
            change (match m () with
                | .ok v _ =>
                  match refFieldsForVariant? ety v with
                  | some [] => Except.ok (Val.enumVal ety v [])
                  | _ => Except.error FaultKind.unsupported
                | .error (.undefinedBehavior _) _
                | .error (.stack (.localExpectedLive _)) _ =>
                  Except.error FaultKind.undefined
                | .error _ _ => Except.error FaultKind.unsupported) = _
            rw [h_m]
            have h_st := (readDiscriminant_enum_niche_stateless Unit ety tagW
              tagS vs ve nichePath untagged start last nicheStart bits ()
              h_adm h_tr).2
            rw [h_st, ite_false_eq_true]
            cases decodeNicheTagBits tagW vs ve untagged start last nicheStart
                ety.discriminants.length bits with
            | error _ => rfl
            | ok v =>
              dsimp only
              cases isVariantUninhabited ety v <;> rfl

theorem refEnumValNicheValid_eq {ety : EnumTy} {variant : Nat}
    (h_adm : enumAdmitted ety = true)
    (h_inh : isVariantUninhabited ety variant = false)
    (fields : List Val) :
    refEnumValNicheValid ety variant fields =
      enumValNicheValid ety variant fields := by
  dsimp only [refEnumValNicheValid, enumValNicheValid]
  cases h_tr : ety.tagRepr with
  | zeroSized | single _ | scalar _ _ => rfl
  | niche tagW tagS vs ve nichePath untagged start last nicheStart =>
    dsimp only
    cases h_vu : Nat.beq variant untagged with
    | false => rfl
    | true =>
      have hv_eq := Nat.eq_of_beq_eq_true h_vu
      subst hv_eq
      dsimp only [ite_true_eq_true]
      rw [refExtractValNicheBitsFromFields_eq]
      cases extractValNicheBitsFromFields nichePath fields with
      | none => rfl
      | some bits =>
        dsimp only
        rw [truncateFromUInt_eq_miriScalar]
        dsimp only
        let m := Miri.Interpreter.Discriminant.readDiscriminant
          (refDiscriminantHooks Unit ety) ()
          ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW bits))),
            ⟨0, refEnumLayoutData ety⟩⟩
        have h_m :
            (match m () with
            | .ok decoded _ => Nat.beq decoded variant
            | .error _ _ => false) =
            (match mapStepExcept (Miri.Interpreter.runRvalue m ()).2 with
            | .ok decoded => Nat.beq decoded variant
            | .error _ => false) := by
          dsimp only [Miri.Interpreter.runRvalue, mapStepExcept]
          cases m () <;> rfl
        change (match m () with
            | .ok decoded _ => Nat.beq decoded variant
            | .error _ _ => false) = _
        rw [h_m]
        have h_st := (readDiscriminant_enum_niche_stateless Unit ety tagW tagS
          vs ve nichePath variant start last nicheStart bits () h_adm h_tr).2
        rw [h_st]
        cases decodeNicheTagBits tagW vs ve variant start last nicheStart
            ety.discriminants.length bits with
        | error _ => rfl
        | ok decoded =>
          dsimp only
          cases h_dv : Nat.beq decoded variant with
          | true =>
            have hd_eq := Nat.eq_of_beq_eq_true h_dv
            subst hd_eq
            rw [h_inh, ite_false_eq_true]
            dsimp only
            exact Nat.beq_refl decoded
          | false =>
            cases isVariantUninhabited ety decoded with
            | true => rfl
            | false => exact h_dv

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
    | .structVal sty fields, ty => by
      cases ty with
      | adtStruct dstSty =>
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        rw [refAreSupportedFieldTys_eq, refIsTypeUninhabited_eq,
            checkRefVals_eq fields sty.fields]
        cases areSupportedFieldTys sty.fields with
        | false => rfl
        | true =>
          cases isTypeUninhabited (.adtStruct sty) with
          | true => rfl
          | false =>
            cases Val.tys? fields with
            | none => rfl
            | some tys =>
              dsimp only
              cases MirTy.beqList tys sty.fields with
              | false => rfl
              | true => cases sty; cases dstSty; rfl
      | bool | int _ _ | unit | never | enum _ | tuple _ | array _ _
      | ref _ _ | rawPtr _ _ | unsupported =>
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        cases (!areSupportedFieldTys sty.fields ||
            isTypeUninhabited (.adtStruct sty)) with
        | true => rfl
        | false =>
          cases Val.tys? fields with
          | none => rfl
          | some tys =>
            dsimp only
            cases MirTy.beqList tys sty.fields with
            | false => rfl
            | true => cases sty; rfl
    | .enumVal ety v fields, ty => by
      cases ty with
      | enum ety' =>
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        rw [refEnumAdmitted_eq, refIsVariantUninhabited_eq,
            refFieldsForVariant?_eq]
        cases h_adm : enumAdmitted ety with
        | false => rfl
        | true =>
          cases h_uninh : isVariantUninhabited ety v with
          | true => rfl
          | false =>
            rw [refEnumValNicheValid_eq h_adm h_uninh fields]
            cases enumValNicheValid ety v fields with
            | false => rfl
            | true =>
              cases fieldsForVariant? ety v with
              | none => rfl
              | some expectedTys =>
                dsimp only
                rw [checkRefVals_eq fields expectedTys]
                cases Val.tys? fields with
                | none => rfl
                | some actualTys =>
                  dsimp only
                  cases MirTy.beqList actualTys expectedTys with
                  | false => rfl
                  | true => cases ety; cases ety'; rfl
      | bool | int _ _ | unit | never | adtStruct _ | tuple _ | array _ _
      | ref _ _ | rawPtr _ _ | unsupported =>
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        cases (!enumAdmitted ety || isVariantUninhabited ety v ||
            !enumValNicheValid ety v fields) with
        | true => rfl
        | false =>
          cases fieldsForVariant? ety v with
          | none => rfl
          | some expectedTys =>
            cases Val.tys? fields with
            | none => rfl
            | some actualTys =>
              dsimp only
              cases MirTy.beqList actualTys expectedTys with
              | false => rfl
              | true => cases ety; rfl
    | .scalar sv, ty => by
      cases sv with
      | mk vw vs vbits =>
        cases ty with
        | bool | unit | never | adtStruct _ | enum _ | tuple _ | array _ _
        | ref _ _ | rawPtr _ _ | unsupported =>
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
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        rw [checkRefVals_eq fields fieldTys]
        cases fields.isEmpty with
        | true => rfl
        | false => cases Val.tys? fields <;> rfl
      | _ =>
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        cases fields.isEmpty with
        | true => rfl
        | false => cases Val.tys? fields <;> rfl
    | .array elemTy elems, ty => by
      cases ty with
      | array dstElemTy len =>
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        rw [refIsSupportedLocalTy_eq, refIsTypeUninhabited_eq,
            checkRefAllHaveTy_eq elems elemTy]
        cases isSupportedScalarOrUnitTy elemTy with
        | false => rfl
        | true =>
          cases Nat.blt elems.length (Nat.pow 2 64) with
          | false => rfl
          | true =>
            cases (!Nat.beq elems.length 0 && isTypeUninhabited elemTy) with
            | true => rfl
            | false =>
              cases Val.checkElemsHaveTy elemTy elems <;> rfl
      | _ =>
        dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
        cases (!isSupportedScalarOrUnitTy elemTy ||
            !Nat.blt elems.length (Nat.pow 2 64) ||
            (!Nat.beq elems.length 0 && isTypeUninhabited elemTy)) with
        | true => rfl
        | false =>
          cases Val.checkElemsHaveTy elemTy elems <;> rfl

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

  theorem checkRefAllHaveTy_eq : ∀ (vs : List Val) (elemTy : MirTy),
      checkRefAllHaveTy vs elemTy = Val.checkElemsHaveTy elemTy vs
    | [], _ => rfl
    | v :: vs, elemTy => by
      dsimp only [checkRefAllHaveTy, Val.checkElemsHaveTy]
      rw [checkRefVal_eq v elemTy, checkRefAllHaveTy_eq vs elemTy]
      dsimp only [checkVal]
      cases Val.ty? v <;> rfl
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

noncomputable def placeTyToRefPlaceTy : PlaceTy → RefPlaceTy
  | .ty t => .ty t
  | .variant ety v => .variant ety v

theorem refProjectPlaceTy?_eq {ts : List MirTy}
    {rproj : List RefProjectionElem} {proj : List ProjectionElem}
    (h : mapOption (decodeProjElem ts) rproj = some proj) (pty : PlaceTy) :
    refProjectPlaceTy? ts (placeTyToRefPlaceTy pty)
        (rproj.map toMiriProjElem) =
      optMap placeTyToRefPlaceTy (projectPlaceTy? pty proj) := by
  induction rproj generalizing proj pty with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons re res ih =>
    let ⟨e, es, h_re, h_res, h_eq⟩ := mapOption_cons_inv h
    subst h_eq
    cases re with
    | deref =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t => cases t <;> rfl
    | unsupported =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t => cases t <;> rfl
    | field idx tyId =>
      dsimp only [decodeProjElem, optMap] at h_re
      cases h_t : MirSemantics.getElem? ts tyId with
      | none => rw [h_t] at h_re; cases h_re
      | some statedTy =>
        rw [h_t] at h_re
        injection h_re with h_e
        subst h_e
        cases pty with
        | variant ety v =>
          dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refProjectPlaceTy?, projectPlaceTy?]
          rw [refFieldsForVariant?_eq, h_t]
          cases fieldsForVariant? ety v with
          | none => rfl
          | some varFields =>
            dsimp only
            cases MirSemantics.getElem? varFields idx with
            | none => rfl
            | some fTy =>
              dsimp only
              cases MirTy.beq fTy statedTy with
              | false => rfl
              | true => exact ih h_res (.ty fTy)
        | ty t =>
          cases t with
          | tuple fieldTys =>
            dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
              refProjectPlaceTy?, projectPlaceTy?]
            rw [h_t]
            cases MirSemantics.getElem? fieldTys idx with
            | none => rfl
            | some fTy =>
              dsimp only
              cases MirTy.beq fTy statedTy with
              | false => rfl
              | true => exact ih h_res (.ty fTy)
          | adtStruct sty =>
            dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
              refProjectPlaceTy?, projectPlaceTy?]
            rw [h_t]
            cases MirSemantics.getElem? sty.fields idx with
            | none => rfl
            | some fTy =>
              dsimp only
              cases MirTy.beq fTy statedTy with
              | false => rfl
              | true => exact ih h_res (.ty fTy)
          | _ => rfl
    | downcast v =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | enum ety =>
          dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refProjectPlaceTy?, projectPlaceTy?]
          rw [refEnumAdmitted_eq]
          cases (enumAdmitted ety && Nat.blt v ety.discriminants.length) with
          | false => rfl
          | true => exact ih h_res (.variant ety v)
        | _ => rfl
    | constantIndex offset minLength fromEnd =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | array elemTy len =>
          dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refProjectPlaceTy?, projectPlaceTy?]
          cases Nat.blt len (Nat.pow 2 64) with
          | false => rfl
          | true => exact ih h_res (.ty elemTy)
        | _ => rfl
    | index idxLocal =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | array elemTy len =>
          dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refProjectPlaceTy?, projectPlaceTy?]
          cases Nat.blt len (Nat.pow 2 64) with
          | false => rfl
          | true => exact ih h_res (.ty elemTy)
        | _ => rfl

theorem refProjectTy?_eq {ts : List MirTy}
    {rproj : List RefProjectionElem} {proj : List ProjectionElem}
    {ty : MirTy}
    (h : mapOption (decodeProjElem ts) rproj = some proj) :
    refProjectTy? ts ty (rproj.map toMiriProjElem) = projectTy? ty proj := by
  dsimp only [refProjectTy?, projectTy?]
  have h_sub := refProjectPlaceTy?_eq h (.ty ty)
  dsimp only [placeTyToRefPlaceTy] at h_sub
  rw [h_sub]
  cases projectPlaceTy? (.ty ty) proj with
  | none => rfl
  | some pty => cases pty <;> rfl

theorem refProjectReturnPlaceTy?_eq (pty : PlaceTy)
    (proj : List ProjectionElem) :
    refProjectReturnPlaceTy? (placeTyToRefPlaceTy pty) proj =
      optMap placeTyToRefPlaceTy (projectPlaceTy? pty proj) := by
  induction proj generalizing pty with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | deref | unsupported =>
      cases pty with
      | variant _ _ => rfl
      | ty t => cases t <;> rfl
    | field idx statedTy =>
      cases pty with
      | variant ety v =>
        dsimp only [placeTyToRefPlaceTy, refProjectReturnPlaceTy?,
          projectPlaceTy?]
        rw [refFieldsForVariant?_eq]
        cases fieldsForVariant? ety v with
        | none => rfl
        | some varFields =>
          dsimp only
          cases MirSemantics.getElem? varFields idx with
          | none => rfl
          | some fTy =>
            dsimp only
            cases MirTy.beq fTy statedTy with
            | false => rfl
            | true => exact ih (.ty fTy)
      | ty t =>
        cases t with
        | tuple fieldTys =>
          dsimp only [placeTyToRefPlaceTy, refProjectReturnPlaceTy?,
            projectPlaceTy?]
          cases MirSemantics.getElem? fieldTys idx with
          | none => rfl
          | some fTy =>
            dsimp only
            cases MirTy.beq fTy statedTy with
            | false => rfl
            | true => exact ih (.ty fTy)
        | adtStruct sty =>
          dsimp only [placeTyToRefPlaceTy, refProjectReturnPlaceTy?,
            projectPlaceTy?]
          cases MirSemantics.getElem? sty.fields idx with
          | none => rfl
          | some fTy =>
            dsimp only
            cases MirTy.beq fTy statedTy with
            | false => rfl
            | true => exact ih (.ty fTy)
        | _ => rfl
    | downcast v =>
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | enum ety =>
          dsimp only [placeTyToRefPlaceTy, refProjectReturnPlaceTy?,
            projectPlaceTy?]
          rw [refEnumAdmitted_eq]
          cases (enumAdmitted ety && Nat.blt v ety.discriminants.length) with
          | false => rfl
          | true => exact ih (.variant ety v)
        | _ => rfl
    | constantIndex _ _ _ =>
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | array elemTy len =>
          dsimp only [placeTyToRefPlaceTy, refProjectReturnPlaceTy?,
            projectPlaceTy?]
          cases Nat.blt len (Nat.pow 2 64) with
          | false => rfl
          | true => exact ih (.ty elemTy)
        | _ => rfl
    | index _ =>
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | array elemTy len =>
          dsimp only [placeTyToRefPlaceTy, refProjectReturnPlaceTy?,
            projectPlaceTy?]
          cases Nat.blt len (Nat.pow 2 64) with
          | false => rfl
          | true => exact ih (.ty elemTy)
        | _ => rfl

theorem refProjectReturnTy?_eq (ty : MirTy) (proj : List ProjectionElem) :
    refProjectReturnTy? ty proj = projectTy? ty proj := by
  dsimp only [refProjectReturnTy?, projectTy?]
  have h_sub := refProjectReturnPlaceTy?_eq (.ty ty) proj
  dsimp only [placeTyToRefPlaceTy] at h_sub
  rw [h_sub]
  cases projectPlaceTy? (.ty ty) proj with
  | none => rfl
  | some pty => cases pty <;> rfl

def CanonProjElem : Miri.MIR.ProjectionElem → ProjectionElem → Prop
  | .Field idx _, .field idx' _ => idx = idx'
  | .Downcast _ v, .downcast v' => v = v'
  | .ConstantIndex idx minLen false, .constantIndex idx' minLen' false =>
    idx = idx' ∧ minLen = minLen'
  | _, _ => False

def CanonProjList (mps : List Miri.MIR.ProjectionElem)
    (ps : List ProjectionElem) : Prop :=
  @List.rec Miri.MIR.ProjectionElem (fun _ => List ProjectionElem → Prop)
    (fun ys => match ys with | [] => True | _ :: _ => False)
    (fun mp _ ih ys =>
      match ys with
      | [] => False
      | p :: ys' => CanonProjElem mp p ∧ ih ys')
    mps ps

theorem CanonProjList.append {mps₁ mps₂ : List Miri.MIR.ProjectionElem}
    {ps₁ ps₂ : List ProjectionElem}
    (h₁ : CanonProjList mps₁ ps₁) (h₂ : CanonProjList mps₂ ps₂) :
    CanonProjList (mps₁ ++ mps₂) (ps₁ ++ ps₂) := by
  induction mps₁ generalizing ps₁ with
  | nil =>
    cases ps₁ with
    | nil => exact h₂
    | cons _ _ => cases h₁
  | cons mp rest ih =>
    cases ps₁ with
    | nil => cases h₁
    | cons p ps => exact ⟨h₁.1, ih h₁.2⟩

theorem refReadPlaceSlotPath?_eq {mps : List Miri.MIR.ProjectionElem}
    {ps : List ProjectionElem}
    (h : CanonProjList mps ps) (pty : PlaceTy) (sv : SlotVal) :
    refReadPlaceSlotPath? (placeTyToRefPlaceTy pty) sv mps =
      readPlaceSlotPath? pty sv ps := by
  induction mps generalizing ps pty sv with
  | nil =>
    cases ps with
    | nil => cases pty <;> rfl
    | cons _ _ => cases h
  | cons mp mps' ih =>
    cases ps with
    | nil => cases h
    | cons p ps' =>
      let ⟨h_hd, h_tl⟩ := h
      cases mp with
      | Deref | Index _ | Subslice _ _ _ | OpaqueCast _ | PhantomDeref
      | UnwrapUnsafeBinder _ =>
        cases p <;> cases h_hd
      | Field idx _ =>
        cases p with
        | field idx' _ =>
          dsimp only [CanonProjElem] at h_hd
          subst h_hd
          cases pty with
          | variant ety v =>
            dsimp only [placeTyToRefPlaceTy, refReadPlaceSlotPath?,
              readPlaceSlotPath?]
            rw [refFieldsForVariant?_eq]
            cases fieldsForVariant? ety v with
            | none => rfl
            | some varFields =>
              dsimp only
              cases MirSemantics.getElem? varFields idx with
              | none => rfl
              | some fTy =>
                dsimp only
                cases sv with
                | uninit =>
                  dsimp only
                  rw [refUninitSlotVal_eq]
                  exact ih h_tl (.ty fTy) (uninitSlotVal fTy)
                | enumVal ety' v' fields =>
                  dsimp only
                  cases EnumTy.beq ety ety' with
                  | false => rfl
                  | true =>
                    cases Nat.beq v' v with
                    | true =>
                      cases MirSemantics.getElem? fields idx with
                      | none => rfl
                      | some field => exact ih h_tl (.ty fTy) field
                    | false =>
                      rw [refFieldsForVariant?_eq]
                      cases fieldsForVariant? ety v' with
                      | none => rfl
                      | some activeFieldTys =>
                        dsimp only
                        rw [refAreAllZeroSizedTys_eq, refUninitSlotVal_eq]
                        cases areAllZeroSizedTys activeFieldTys with
                        | false => rfl
                        | true => exact ih h_tl (.ty fTy) (uninitSlotVal fTy)
                | enumUntagged ety' v' fields =>
                  dsimp only
                  cases (EnumTy.beq ety ety' && Nat.beq v' v) with
                  | false => rfl
                  | true =>
                    cases MirSemantics.getElem? fields idx with
                    | none => rfl
                    | some field => exact ih h_tl (.ty fTy) field
                | _ => rfl
          | ty t =>
            cases t with
            | tuple fieldTys =>
              cases sv with
              | tuple fields =>
                dsimp only [placeTyToRefPlaceTy, refReadPlaceSlotPath?,
                  readPlaceSlotPath?]
                cases MirSemantics.getElem? fieldTys idx with
                | none => rfl
                | some fTy =>
                  cases MirSemantics.getElem? fields idx with
                  | none => rfl
                  | some field => exact ih h_tl (.ty fTy) field
              | _ => rfl
            | adtStruct sty =>
              cases sv with
              | structVal sty' fields =>
                dsimp only [placeTyToRefPlaceTy, refReadPlaceSlotPath?,
                  readPlaceSlotPath?]
                cases StructTy.beq sty sty' with
                | false => rfl
                | true =>
                  cases MirSemantics.getElem? sty.fields idx with
                  | none => rfl
                  | some fTy =>
                    cases MirSemantics.getElem? fields idx with
                    | none => rfl
                    | some field => exact ih h_tl (.ty fTy) field
              | _ => rfl
            | _ => cases sv <;> rfl
        | _ => cases h_hd
      | Downcast _ v =>
        cases p with
        | downcast v' =>
          dsimp only [CanonProjElem] at h_hd
          subst h_hd
          cases pty with
          | variant _ _ => rfl
          | ty t =>
            cases t with
            | enum ety =>
              dsimp only [placeTyToRefPlaceTy, refReadPlaceSlotPath?,
                readPlaceSlotPath?]
              cases Nat.blt v ety.discriminants.length with
              | false => rfl
              | true => exact ih h_tl (.variant ety v) sv
            | _ => cases sv <;> rfl
        | _ => cases h_hd
      | ConstantIndex idx minLen fromEnd =>
        cases fromEnd with
        | true => cases p <;> cases h_hd
        | false =>
          cases p with
          | constantIndex idx' minLen' fromEnd' =>
            cases fromEnd' with
            | true => cases h_hd
            | false =>
              let ⟨hi, hm⟩ := h_hd
              subst hi; subst hm
              cases pty with
              | variant _ _ => rfl
              | ty t =>
                cases t with
                | array elemTy len =>
                  cases sv with
                  | array elemTy' elems =>
                    dsimp only [placeTyToRefPlaceTy, refReadPlaceSlotPath?,
                      readPlaceSlotPath?]
                    cases (!MirTy.beq elemTy elemTy' ||
                        !Nat.beq elems.length len) with
                    | true => rfl
                    | false =>
                      cases MirSemantics.getElem? elems idx with
                      | none => rfl
                      | some elem => exact ih h_tl (.ty elemTy) elem
                  | _ => rfl
                | _ => cases sv <;> rfl
          | _ => cases h_hd

theorem refWritePlaceSlotPath?_eq {mps : List Miri.MIR.ProjectionElem}
    {ps : List ProjectionElem}
    (h : CanonProjList mps ps) (pty : PlaceTy) (sv new : SlotVal) :
    refWritePlaceSlotPath? (placeTyToRefPlaceTy pty) sv mps new =
      writePlaceSlotPath? pty sv ps new := by
  induction mps generalizing ps pty sv with
  | nil =>
    cases ps with
    | nil => cases pty <;> rfl
    | cons _ _ => cases h
  | cons mp mps' ih =>
    cases ps with
    | nil => cases h
    | cons p ps' =>
      let ⟨h_hd, h_tl⟩ := h
      cases mp with
      | Deref | Index _ | Subslice _ _ _ | OpaqueCast _ | PhantomDeref
      | UnwrapUnsafeBinder _ =>
        cases p <;> cases h_hd
      | Field idx _ =>
        cases p with
        | field idx' _ =>
          dsimp only [CanonProjElem] at h_hd
          subst h_hd
          cases pty with
          | variant ety v =>
            dsimp only [placeTyToRefPlaceTy, refWritePlaceSlotPath?,
              writePlaceSlotPath?]
            rw [refFieldsForVariant?_eq]
            cases fieldsForVariant? ety v with
            | none => rfl
            | some varFields =>
              dsimp only
              cases MirSemantics.getElem? varFields idx with
              | none => rfl
              | some fTy =>
                dsimp only
                cases sv with
                | uninit =>
                  dsimp only
                  rw [refUninitSlotVals_eq]
                  cases MirSemantics.getElem? (uninitSlotVals varFields) idx with
                  | none => rfl
                  | some field =>
                    dsimp only
                    have h_sub := ih h_tl (.ty fTy) field
                    dsimp only [placeTyToRefPlaceTy] at h_sub
                    rw [h_sub]
                    cases writePlaceSlotPath? (.ty fTy) field ps' new <;> rfl
                | enumUntagged ety' v' fields =>
                  dsimp only
                  cases (EnumTy.beq ety ety' && Nat.beq v' v) with
                  | false => rfl
                  | true =>
                    cases MirSemantics.getElem? fields idx with
                    | none => rfl
                    | some field =>
                      dsimp only
                      have h_sub := ih h_tl (.ty fTy) field
                      dsimp only [placeTyToRefPlaceTy] at h_sub
                      rw [h_sub]
                      cases writePlaceSlotPath? (.ty fTy) field ps' new <;> rfl
                | enumVal ety' v' fields =>
                  dsimp only
                  cases EnumTy.beq ety ety' with
                  | false => rfl
                  | true =>
                    cases Nat.beq v' v with
                    | true =>
                      cases MirSemantics.getElem? fields idx with
                      | none => rfl
                      | some field =>
                        dsimp only
                        have h_sub := ih h_tl (.ty fTy) field
                        dsimp only [placeTyToRefPlaceTy] at h_sub
                        rw [h_sub]
                        cases writePlaceSlotPath? (.ty fTy) field ps' new <;>
                          rfl
                    | false =>
                      rw [refUninitSlotVals_eq]
                      cases MirSemantics.getElem?
                          (uninitSlotVals varFields) idx with
                      | none => rfl
                      | some field =>
                        dsimp only
                        have h_sub := ih h_tl (.ty fTy) field
                        dsimp only [placeTyToRefPlaceTy] at h_sub
                        rw [h_sub]
                        cases writePlaceSlotPath? (.ty fTy) field ps' new <;>
                          rfl
                | _ => rfl
          | ty t =>
            cases t with
            | tuple fieldTys =>
              cases sv with
              | tuple fields =>
                dsimp only [placeTyToRefPlaceTy, refWritePlaceSlotPath?,
                  writePlaceSlotPath?]
                cases MirSemantics.getElem? fieldTys idx with
                | none => rfl
                | some fTy =>
                  cases MirSemantics.getElem? fields idx with
                  | none => rfl
                  | some field =>
                    dsimp only
                    have h_sub := ih h_tl (.ty fTy) field
                    dsimp only [placeTyToRefPlaceTy] at h_sub
                    rw [h_sub]
                    cases writePlaceSlotPath? (.ty fTy) field ps' new <;> rfl
              | _ => rfl
            | adtStruct sty =>
              cases sv with
              | structVal sty' fields =>
                dsimp only [placeTyToRefPlaceTy, refWritePlaceSlotPath?,
                  writePlaceSlotPath?]
                cases StructTy.beq sty sty' with
                | false => rfl
                | true =>
                  cases MirSemantics.getElem? sty.fields idx with
                  | none => rfl
                  | some fTy =>
                    cases MirSemantics.getElem? fields idx with
                    | none => rfl
                    | some field =>
                      dsimp only
                      have h_sub := ih h_tl (.ty fTy) field
                      dsimp only [placeTyToRefPlaceTy] at h_sub
                      rw [h_sub]
                      cases writePlaceSlotPath? (.ty fTy) field ps' new <;> rfl
              | _ => rfl
            | _ => cases sv <;> rfl
        | _ => cases h_hd
      | Downcast _ v =>
        cases p with
        | downcast v' =>
          dsimp only [CanonProjElem] at h_hd
          subst h_hd
          cases pty with
          | variant _ _ => rfl
          | ty t =>
            cases t with
            | enum ety =>
              dsimp only [placeTyToRefPlaceTy, refWritePlaceSlotPath?,
                writePlaceSlotPath?]
              cases Nat.blt v ety.discriminants.length with
              | false => rfl
              | true => exact ih h_tl (.variant ety v) sv
            | _ => cases sv <;> rfl
        | _ => cases h_hd
      | ConstantIndex idx minLen fromEnd =>
        cases fromEnd with
        | true => cases p <;> cases h_hd
        | false =>
          cases p with
          | constantIndex idx' minLen' fromEnd' =>
            cases fromEnd' with
            | true => cases h_hd
            | false =>
              let ⟨hi, hm⟩ := h_hd
              subst hi; subst hm
              cases pty with
              | variant _ _ => rfl
              | ty t =>
                cases t with
                | array elemTy len =>
                  cases sv with
                  | array elemTy' elems =>
                    dsimp only [placeTyToRefPlaceTy, refWritePlaceSlotPath?,
                      writePlaceSlotPath?]
                    cases (!MirTy.beq elemTy elemTy' ||
                        !Nat.beq elems.length len) with
                    | true => rfl
                    | false =>
                      cases MirSemantics.getElem? elems idx with
                      | none => rfl
                      | some elem =>
                        dsimp only
                        have h_sub := ih h_tl (.ty elemTy) elem
                        dsimp only [placeTyToRefPlaceTy] at h_sub
                        rw [h_sub]
                        cases writePlaceSlotPath? (.ty elemTy) elem ps' new <;>
                          rfl
                  | _ => rfl
                | _ => cases sv <;> rfl
          | _ => cases h_hd

private theorem getElem?_lt_of_some {α : Type} {xs : List α} {idx : Nat}
    {x : α} (h : MirSemantics.getElem? xs idx = some x) :
    idx < xs.length := by
  induction xs generalizing idx with
  | nil => cases h
  | cons _ rest ih =>
    cases idx with
    | zero => exact Nat.succ_pos rest.length
    | succ j => exact Nat.succ_lt_succ (ih h)

private theorem getElem?_none_ge {α : Type} {xs : List α} {idx : Nat}
    (h : MirSemantics.getElem? xs idx = none) :
    idx ≥ xs.length := by
  induction xs generalizing idx with
  | nil => exact Nat.zero_le idx
  | cons _ rest ih =>
    cases idx with
    | zero => cases h
    | succ j => exact Nat.succ_le_succ (ih h)

private theorem getElem?_list_replicate {α : Type} (n : Nat) (c : α)
    (idx : Nat) :
    MirSemantics.getElem? (List.replicate n c) idx =
      if Nat.blt idx n then some c else none := by
  induction n generalizing idx with
  | zero => cases idx <;> rfl
  | succ m ih =>
    cases idx with
    | zero => rfl
    | succ j => exact ih j

private theorem fieldsShape_arbitrary_offset_zero (n idx : Nat) :
    Miri.ABI.FieldsShape.offset
        (.Arbitrary (Array.replicate n Miri.ABI.Size.ZERO) Array.empty) idx =
      if idx < n then
        .ok Miri.ABI.Size.ZERO
      else
        .error (.fieldOutOfBounds idx n) := by
  have h_arr : Array.replicate n Miri.ABI.Size.ZERO =
      Array.mk (List.replicate n Miri.ABI.Size.ZERO) := rfl
  have h_cnt :
      Miri.ABI.FieldsShape.count
        (.Arbitrary (Array.replicate n Miri.ABI.Size.ZERO) Array.empty) =
      n := List.length_replicate
  dsimp only [Miri.ABI.FieldsShape.offset]
  rw [h_cnt]
  cases h_lt : decide (idx < n) with
  | false =>
    have h_ge : idx ≥ n := Nat.le_of_not_lt (of_decide_eq_false h_lt)
    rw [ite_eq_left h_ge, ite_eq_right (of_decide_eq_false h_lt)]
    rfl
  | true =>
    have h_ltn : idx < n := of_decide_eq_true h_lt
    have h_nge : ¬ (idx ≥ n) := Nat.not_le_of_gt h_ltn
    rw [ite_eq_right h_nge, ite_eq_left h_ltn]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [h_arr, array_mk_getElem?_eq_getElem?, getElem?_list_replicate,
        nat_blt_eq_true_of_lt h_ltn, ite_true_eq_true]

private theorem fieldsShape_primitive_offset_err (idx : Nat) :
    Miri.ABI.FieldsShape.offset .Primitive idx =
      .error (.fieldOutOfBounds idx 0) := by
  cases idx <;> rfl

private theorem projectField_refProjectionCx_eq
    (localIndexFn : Miri.MIR.LocalId →
      Except Miri.Interpreter.ProjectionError UInt64)
    (pty : PlaceTy) (idx tyId : Nat) :
    let curPty := placeTyToRefPlaceTy pty
    let elem : Miri.MIR.ProjectionElem := .Field idx tyId
    let fieldTy? : Option MirTy :=
      match pty with
      | .ty (.tuple fieldTys) => MirSemantics.getElem? fieldTys idx
      | .ty (.adtStruct sty) => MirSemantics.getElem? sty.fields idx
      | .variant ety v =>
        match fieldsForVariant? ety v with
        | some varFields => MirSemantics.getElem? varFields idx
        | none => none
      | _ => none
    match fieldTy? with
    | some _ =>
      Miri.Interpreter.project (refProjectionCx curPty localIndexFn)
        (refBaseOpForProjStep curPty elem) elem =
      .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩,
        refSizedLocalLayout⟩
    | none =>
      ∃ n,
        Miri.Interpreter.project (refProjectionCx curPty localIndexFn)
          (refBaseOpForProjStep curPty elem) elem =
        .error (.layout (.fieldOutOfBounds idx n)) := by
  dsimp only [Miri.Interpreter.project, Miri.Interpreter.projectField]
  cases pty with
  | variant ety v =>
    dsimp only [placeTyToRefPlaceTy, refBaseOpForProjStep, refProjectionCx]
    rw [refFieldsForVariant?_eq]
    cases fieldsForVariant? ety v with
    | none =>
      dsimp only [bind, Except.bind]
      rw [fieldsShape_primitive_offset_err]
      exact ⟨0, rfl⟩
    | some varFields =>
      dsimp only [bind, Except.bind]
      rw [fieldsShape_arbitrary_offset_zero varFields.length idx]
      cases h_get : MirSemantics.getElem? varFields idx with
      | none =>
        rw [ite_eq_right (Nat.not_lt_of_ge (getElem?_none_ge h_get))]
        exact ⟨varFields.length, rfl⟩
      | some fTy =>
        rw [ite_eq_left (getElem?_lt_of_some h_get)]
        rfl
  | ty t =>
    cases t with
    | tuple fieldTys =>
      dsimp only [placeTyToRefPlaceTy, refBaseOpForProjStep, refProjectionCx,
        bind, Except.bind]
      rw [fieldsShape_arbitrary_offset_zero fieldTys.length idx]
      cases h_get : MirSemantics.getElem? fieldTys idx with
      | none =>
        rw [ite_eq_right (Nat.not_lt_of_ge (getElem?_none_ge h_get))]
        exact ⟨fieldTys.length, rfl⟩
      | some fTy =>
        rw [ite_eq_left (getElem?_lt_of_some h_get)]
        rfl
    | adtStruct sty =>
      dsimp only [placeTyToRefPlaceTy, refBaseOpForProjStep, refProjectionCx,
        bind, Except.bind]
      rw [fieldsShape_arbitrary_offset_zero sty.fields.length idx]
      cases h_get : MirSemantics.getElem? sty.fields idx with
      | none =>
        rw [ite_eq_right (Nat.not_lt_of_ge (getElem?_none_ge h_get))]
        exact ⟨sty.fields.length, rfl⟩
      | some fTy =>
        rw [ite_eq_left (getElem?_lt_of_some h_get)]
        rfl
    | bool | int _ _ | unit | never | enum _ | array _ _ | ref _ _
    | rawPtr _ _ | unsupported =>
      dsimp only [placeTyToRefPlaceTy, refBaseOpForProjStep, bind, Except.bind]
      rw [fieldsShape_primitive_offset_err]
      exact ⟨0, rfl⟩

private theorem uint64_toNat_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (UInt64.ofNat n).toNat = n := by
  change (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

private theorem uint64_lt_iff_toNat {a b : UInt64} :
    (a < b) ↔ (a.toNat < b.toNat) := Iff.rfl

private theorem uint64_le_iff_toNat {a b : UInt64} :
    (a ≤ b) ↔ (a.toNat ≤ b.toNat) := Iff.rfl

private theorem uint64_sub_ofNat_eq {a b : Nat}
    (ha : a < Nat.pow 2 64) (hb_le : b ≤ a) :
    UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b) := by
  have hb : b < Nat.pow 2 64 := Nat.lt_of_le_of_lt hb_le ha
  have h_sub_lt : a - b < Nat.pow 2 64 := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64
      ((Nat.pow 2 64 - (BitVec.ofNat 64 b).toNat) +
        (BitVec.ofNat 64 a).toNat)).toNat =
    (BitVec.ofNat 64 (a - b)).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt h_sub_lt]
  have h_sum : (Nat.pow 2 64 - b) + a = (a - b) + 1 * Nat.pow 2 64 := by
    apply @Nat.add_right_cancel _ b
    rw [Nat.one_mul, Nat.add_right_comm (Nat.pow 2 64 - b) a b,
        Nat.sub_add_cancel (Nat.le_of_lt hb),
        Nat.add_right_comm (a - b) (Nat.pow 2 64) b,
        Nat.sub_add_cancel hb_le]
    exact Nat.add_comm (Nat.pow 2 64) a
  rw [h_sum, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt h_sub_lt

private theorem projectIndex_array_eq
    (localIndexFn : Miri.MIR.LocalId →
      Except Miri.Interpreter.ProjectionError UInt64)
    (elemTy : MirTy) {len idx : Nat}
    (h_len : len < Nat.pow 2 64) (h_idx_u64 : idx < Nat.pow 2 64) :
    let curPty : RefPlaceTy := .ty (.array elemTy len)
    let base : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
      ⟨.indirect ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩,
        ⟨0, { refSizedLocalLayout.layout with
              fields := .Array (Miri.ABI.Size.ofBytes 1)
                (UInt64.ofNat len) }⟩⟩
    Miri.Interpreter.projectIndex (refProjectionCx curPty localIndexFn) base
        (UInt64.ofNat idx) =
      if Nat.blt idx len then
        .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (UInt64.ofNat idx), none⟩,
              .none, none⟩,
            refSizedLocalLayout⟩
      else
        .error (.bounds (UInt64.ofNat len) (UInt64.ofNat idx)) := by
  have h_len_blt : Nat.blt len (Nat.pow 2 64) = true :=
    Nat.ble_eq_true_of_le h_len
  have h_len_tn := uint64_toNat_ofNat_lt h_len
  have h_idx_tn := uint64_toNat_ofNat_lt h_idx_u64
  have h_max_tn :
      (UInt64.ofNat (Nat.pow 2 64 - 1)).toNat = Nat.pow 2 64 - 1 :=
    uint64_toNat_ofNat_lt (by decide)
  dsimp only [Miri.Interpreter.projectIndex, Miri.Interpreter.OpTy.len,
    refSizedLocalLayout, refBaseLayoutData, LayoutData.isSized,
    BackendRepr.isSized, BackendRepr.isUnsized,
    bind, Except.bind, pure, Except.pure]
  simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false]
  cases h_blt : Nat.blt idx len with
  | false =>
    have h_ge_nat : len ≤ idx := by
      cases h_d : decide (idx < len) with
      | false => exact Nat.le_of_not_lt (of_decide_eq_false h_d)
      | true =>
        rw [nat_blt_eq_true_of_lt (of_decide_eq_true h_d)] at h_blt
        cases h_blt
    have h_ge_u64 : UInt64.ofNat idx ≥ UInt64.ofNat len := by
      change (UInt64.ofNat len).toNat ≤ (UInt64.ofNat idx).toNat
      rw [h_len_tn, h_idx_tn]
      exact h_ge_nat
    rw [ite_eq_left h_ge_u64]
    rfl
  | true =>
    have h_lt_nat : idx < len := nat_lt_of_blt_eq_true h_blt
    have h_nge_u64 : ¬ (UInt64.ofNat idx ≥ UInt64.ofNat len) := by
      change ¬ ((UInt64.ofNat len).toNat ≤ (UInt64.ofNat idx).toNat)
      rw [h_len_tn, h_idx_tn]
      exact Nat.not_le_of_gt h_lt_nat
    rw [ite_eq_right h_nge_u64]
    dsimp only [Miri.Interpreter.IntegerOps.computeSizeInBytes,
      Miri.ABI.Size.ofBytes, refProjectionCx]
    have h_one : (1 : UInt64).toNat = 1 := rfl
    rw [h_one, Nat.one_mul, h_idx_tn, h_max_tn]
    have h_le_max : idx ≤ Nat.pow 2 64 - 1 :=
      Nat.le_sub_one_of_lt h_idx_u64
    have h_cond :
        (decide (idx < HPow.hPow 2 64) &&
          decide (idx ≤ Nat.pow 2 64 - 1)) = true := by
      rw [decide_eq_true h_idx_u64, decide_eq_true h_le_max]
      rfl
    rw [h_cond, ite_true_eq_true, h_len_blt]
    rfl

private theorem projectConstantIndex_array_eq
    (localIndexFn : Miri.MIR.LocalId →
      Except Miri.Interpreter.ProjectionError UInt64)
    (elemTy : MirTy) (len offset minLength : Nat) (fromEnd : Bool)
    (h_len : len < Nat.pow 2 64) :
    let curPty : RefPlaceTy := .ty (.array elemTy len)
    let elem : Miri.MIR.ProjectionElem :=
      .ConstantIndex offset minLength fromEnd
    match evalConstantIndex len offset minLength fromEnd with
    | .ok idx =>
      Miri.Interpreter.project (refProjectionCx curPty localIndexFn)
        (refBaseOpForProjStep curPty elem) elem =
      .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (UInt64.ofNat idx), none⟩,
            .none, none⟩,
          refSizedLocalLayout⟩ ∧
      (UInt64.ofNat idx).toNat = idx
    | .error k =>
      ∃ err,
        Miri.Interpreter.project (refProjectionCx curPty localIndexFn)
          (refBaseOpForProjStep curPty elem) elem = .error err ∧
        projErrorToFaultKind err = k := by
  have h_len_blt : Nat.blt len (Nat.pow 2 64) = true :=
    Nat.ble_eq_true_of_le h_len
  dsimp only [Miri.Interpreter.project, evalConstantIndex,
    refBaseOpForProjStep]
  rw [h_len_blt, ite_true_eq_true]
  cases h_ov : (!Nat.blt offset (Nat.pow 2 64) ||
      !Nat.blt minLength (Nat.pow 2 64)) with
  | true =>
    have h_ge : (decide (offset ≥ HPow.hPow 2 64) ||
        decide (minLength ≥ HPow.hPow 2 64)) = true := by
      cases h_o : Nat.blt offset (Nat.pow 2 64) with
      | false =>
        have ho_ge : offset ≥ HPow.hPow 2 64 := by
          cases hd : decide (offset < HPow.hPow 2 64) with
          | false => exact Nat.le_of_not_lt (of_decide_eq_false hd)
          | true =>
            rw [nat_blt_eq_true_of_lt (of_decide_eq_true hd)] at h_o
            cases h_o
        rw [decide_eq_true ho_ge, Bool.true_or]
      | true =>
        rw [h_o, Bool.not_true, Bool.false_or] at h_ov
        cases h_m : Nat.blt minLength (Nat.pow 2 64) with
        | true => rw [h_m] at h_ov; cases h_ov
        | false =>
          have hm_ge : minLength ≥ HPow.hPow 2 64 := by
            cases hd : decide (minLength < HPow.hPow 2 64) with
            | false => exact Nat.le_of_not_lt (of_decide_eq_false hd)
            | true =>
              rw [nat_blt_eq_true_of_lt (of_decide_eq_true hd)] at h_m
              cases h_m
          rw [decide_eq_true hm_ge, Bool.or_true]
    rw [h_ge, ite_true_eq_true]
    exact ⟨.invariant "MIR index exceeds u64", rfl, rfl⟩
  | false =>
    have ho_blt : Nat.blt offset (Nat.pow 2 64) = true := by
      cases h_o : Nat.blt offset (Nat.pow 2 64) with
      | true => rfl
      | false => rw [h_o] at h_ov; cases h_ov
    have hm_blt : Nat.blt minLength (Nat.pow 2 64) = true := by
      rw [ho_blt, Bool.not_true, Bool.false_or] at h_ov
      cases h_m : Nat.blt minLength (Nat.pow 2 64) with
      | true => rfl
      | false => rw [h_m] at h_ov; cases h_ov
    have ho_lt := nat_lt_of_blt_eq_true ho_blt
    have hm_lt := nat_lt_of_blt_eq_true hm_blt
    have h_nge : (decide (offset ≥ HPow.hPow 2 64) ||
        decide (minLength ≥ HPow.hPow 2 64)) = false := by
      rw [decide_eq_false (Nat.not_le_of_gt ho_lt),
          decide_eq_false (Nat.not_le_of_gt hm_lt)]
      rfl
    rw [h_nge, ite_false_eq_true, ite_false_eq_true]
    dsimp only [Miri.Interpreter.projectConstantIndex,
      Miri.Interpreter.OpTy.len, refSizedLocalLayout, refBaseLayoutData,
      LayoutData.isSized, BackendRepr.isSized, BackendRepr.isUnsized,
      bind, Except.bind, pure, Except.pure]
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false]
    have h_len_tn := uint64_toNat_ofNat_lt h_len
    have ho_tn := uint64_toNat_ofNat_lt ho_lt
    have hm_tn := uint64_toNat_ofNat_lt hm_lt
    cases h_lm : Nat.blt len minLength with
    | true =>
      rw [ite_true_eq_true]
      dsimp only
      have h_lt_u64 : UInt64.ofNat len < UInt64.ofNat minLength := by
        change (UInt64.ofNat len).toNat < (UInt64.ofNat minLength).toNat
        rw [h_len_tn, hm_tn]
        exact nat_lt_of_blt_eq_true h_lm
      rw [ite_eq_left h_lt_u64]
      exact ⟨.bounds (UInt64.ofNat minLength) (UInt64.ofNat len), rfl, rfl⟩
    | false =>
      have h_min_le_len : minLength ≤ len := by
        cases hd : decide (len < minLength) with
        | false => exact Nat.le_of_not_lt (of_decide_eq_false hd)
        | true =>
          rw [nat_blt_eq_true_of_lt (of_decide_eq_true hd)] at h_lm
          cases h_lm
      have h_nlt_u64 : ¬ (UInt64.ofNat len < UInt64.ofNat minLength) := by
        change ¬ ((UInt64.ofNat len).toNat < (UInt64.ofNat minLength).toNat)
        rw [h_len_tn, hm_tn]
        exact Nat.not_lt_of_ge h_min_le_len
      rw [ite_false_eq_true]
      cases fromEnd with
      | true =>
        rw [ite_true_eq_true]
        have h_oz : (UInt64.ofNat offset == 0) = Nat.beq offset 0 := by
          cases h_z : Nat.beq offset 0 with
          | true =>
            rw [Nat.eq_of_beq_eq_true h_z]
            rfl
          | false =>
            cases h_b : (UInt64.ofNat offset == 0) with
            | false => rfl
            | true =>
              have h_eq := congrArg UInt64.toNat (eq_of_beq h_b)
              rw [ho_tn] at h_eq
              rw [h_eq] at h_z
              cases h_z
        have h_om :
            decide (UInt64.ofNat offset > UInt64.ofNat minLength) =
              Nat.blt minLength offset := by
          change decide ((UInt64.ofNat minLength).toNat <
              (UInt64.ofNat offset).toNat) = _
          rw [hm_tn, ho_tn]
          exact decide_lt_eq_nat_blt minLength offset
        cases h_bad : (Nat.beq offset 0 || Nat.blt minLength offset) with
        | true =>
          rw [ite_true_eq_true]
          dsimp only
          rw [ite_eq_right h_nlt_u64, h_oz, h_om, h_bad, ite_true_eq_true]
          exact ⟨.invariant "invalid from-end constant index", rfl, rfl⟩
        | false =>
          have ho_pos : 0 < offset := by
            cases offset with
            | zero => cases h_bad
            | succ k => exact Nat.succ_pos k
          have ho_le_min : offset ≤ minLength := by
            cases hd : decide (minLength < offset) with
            | false => exact Nat.le_of_not_lt (of_decide_eq_false hd)
            | true =>
              rw [nat_blt_eq_true_of_lt (of_decide_eq_true hd),
                  Bool.or_true] at h_bad
              cases h_bad
          have ho_le_len : offset ≤ len :=
            Nat.le_trans ho_le_min h_min_le_len
          have h_len_nlt_off : Nat.blt len offset = false := by
            cases hd : Nat.blt len offset with
            | false => rfl
            | true =>
              exact False.elim
                (Nat.not_lt_of_ge ho_le_len (nat_lt_of_blt_eq_true hd))
          have h_sub_lt_len : len - offset < len :=
            Nat.sub_lt (Nat.lt_of_lt_of_le ho_pos ho_le_len) ho_pos
          have h_sub_u64 : len - offset < Nat.pow 2 64 :=
            Nat.lt_trans h_sub_lt_len h_len
          rw [ite_false_eq_true, h_len_nlt_off, ite_false_eq_true]
          dsimp only
          rw [ite_eq_right h_nlt_u64, h_oz, h_om, h_bad, ite_false_eq_true,
              uint64_sub_ofNat_eq h_len ho_le_len]
          have h_pi := projectIndex_array_eq localIndexFn elemTy h_len
            h_sub_u64
          dsimp only at h_pi
          rw [nat_blt_eq_true_of_lt h_sub_lt_len, ite_true_eq_true] at h_pi
          exact ⟨h_pi, uint64_toNat_ofNat_lt h_sub_u64⟩
      | false =>
        rw [ite_false_eq_true]
        cases h_om : Nat.blt offset minLength with
        | false =>
          rw [Bool.not_false, ite_true_eq_true]
          dsimp only
          rw [ite_eq_right h_nlt_u64]
          have h_ge_om : UInt64.ofNat offset ≥ UInt64.ofNat minLength := by
            change (UInt64.ofNat minLength).toNat ≤ (UInt64.ofNat offset).toNat
            rw [hm_tn, ho_tn]
            cases hd : decide (offset < minLength) with
            | false => exact Nat.le_of_not_lt (of_decide_eq_false hd)
            | true =>
              rw [nat_blt_eq_true_of_lt (of_decide_eq_true hd)] at h_om
              cases h_om
          rw [ite_eq_left h_ge_om]
          exact ⟨.invariant "invalid constant index", rfl, rfl⟩
        | true =>
          have ho_lt_min := nat_lt_of_blt_eq_true h_om
          have ho_lt_len : offset < len :=
            Nat.lt_of_lt_of_le ho_lt_min h_min_le_len
          have h_nge_om : ¬ (UInt64.ofNat offset ≥ UInt64.ofNat minLength) := by
            change ¬ ((UInt64.ofNat minLength).toNat ≤
              (UInt64.ofNat offset).toNat)
            rw [hm_tn, ho_tn]
            exact Nat.not_le_of_gt ho_lt_min
          rw [Bool.not_true, ite_false_eq_true,
              nat_blt_eq_true_of_lt ho_lt_len, Bool.not_true,
              ite_false_eq_true]
          dsimp only
          rw [ite_eq_right h_nlt_u64, ite_eq_right h_nge_om]
          have h_pi := projectIndex_array_eq localIndexFn elemTy h_len ho_lt
          dsimp only at h_pi
          rw [nat_blt_eq_true_of_lt ho_lt_len, ite_true_eq_true] at h_pi
          exact ⟨h_pi, ho_tn⟩

private noncomputable def expectedRefLocalIndex :
    MirTy → LocalSlot → Except Miri.Interpreter.ProjectionError UInt64
  | .int .isize false, .live (.scalar sv) =>
    .ok (UInt64.ofNat (truncateBits .isize sv.bits).toNat)
  | .int .isize false, .live .uninit =>
    .error (.machineError (.undefinedBehavior "uninit usize index local"))
  | .int .isize false, .dead =>
    .error (.machineError (.undefinedBehavior "dead usize index local"))
  | .int .isize false, _ =>
    .error (.invariant "non-scalar usize index local")
  | _, _ =>
    .error (.invariant "non-usize index local")

theorem refResolveProjPath_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot} {rproj : List RefProjectionElem}
    {proj : List ProjectionElem}
    (h_dec : mapOption (decodeProjElem ts) rproj = some proj)
    (pty : PlaceTy) :
    match resolveProjPath bodyLocals slots pty proj with
    | .error k =>
      refResolveProjPath ts (zipRefLocals bodyLocals slots)
        (placeTyToRefPlaceTy pty) (rproj.map toMiriProjElem) = .error k
    | .ok resolvedProj =>
      ∃ resolvedMiriProj,
        refResolveProjPath ts (zipRefLocals bodyLocals slots)
          (placeTyToRefPlaceTy pty) (rproj.map toMiriProjElem) =
          .ok resolvedMiriProj ∧
        mapOption (decodeMiriProjElem ts) resolvedMiriProj =
          some resolvedProj ∧
        CanonProjList resolvedMiriProj resolvedProj := by
  induction rproj generalizing proj pty with
  | nil =>
    injection h_dec with h_eq
    subst h_eq
    cases pty with
    | ty _ => exact ⟨[], rfl, rfl, trivial⟩
    | variant _ _ => rfl
  | cons re res ih =>
    let ⟨e, es, h_re, h_res, h_eq⟩ := mapOption_cons_inv h_dec
    subst h_eq
    let rlocals := zipRefLocals bodyLocals slots
    cases re with
    | deref =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t => cases t <;> rfl
    | unsupported =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t => cases t <;> rfl
    | field idx tyId =>
      dsimp only [decodeProjElem, optMap] at h_re
      cases h_t : MirSemantics.getElem? ts tyId with
      | none => rw [h_t] at h_re; cases h_re
      | some statedTy =>
        rw [h_t] at h_re
        injection h_re with h_e
        subst h_e
        have h_pf :=
          projectField_refProjectionCx_eq (refProjLocalIndex rlocals) pty idx
            tyId
        cases pty with
        | variant ety v =>
          first | dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refResolveProjPath, refProjectStep, resolveProjPath] at h_pf | change _
          first | dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refResolveProjPath, refProjectStep, resolveProjPath] | change _
          cases h_fv : fieldsForVariant? ety v with
          | none =>
            rw [h_fv] at h_pf
            first | dsimp only at h_pf | change _
            first | dsimp only | change _
            let ⟨n, h_err⟩ := h_pf
            rw [h_err]
            rfl
          | some varFields =>
            rw [h_fv] at h_pf
            first | dsimp only at h_pf | change _
            first | dsimp only | change _
            cases h_gf : MirSemantics.getElem? varFields idx with
            | none =>
              rw [h_gf] at h_pf
              first | dsimp only at h_pf | change _
              first | dsimp only | change _
              let ⟨n, h_err⟩ := h_pf
              rw [h_err]
              rfl
            | some ty' =>
              rw [h_gf] at h_pf
              first | dsimp only at h_pf | change _
              first | dsimp only | change _
              cases h_beq : MirTy.beq ty' statedTy with
              | false =>
                dsimp only [ite_false_eq_true]
                rw [h_pf]
                dsimp only
                rw [refFieldsForVariant?_eq, h_fv, h_t]
                dsimp only
                rw [h_gf]
                dsimp only
                rw [h_beq]
                rfl
              | true =>
                rw [ite_true_eq_true]
                have h_sub := ih h_res (.ty ty')
                cases h_rp : resolveProjPath bodyLocals slots (.ty ty') es with
                | error k =>
                  rw [h_rp] at h_sub
                  first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                  first | dsimp only [placeTyToRefPlaceTy] | change _
                  rw [h_pf]
                  dsimp only
                  rw [refFieldsForVariant?_eq, h_fv, h_t]
                  dsimp only
                  rw [h_gf]
                  dsimp only
                  rw [h_beq, ite_true_eq_true]
                  change (match refResolveProjPath ts rlocals (.ty ty')
                        (res.map toMiriProjElem) with
                      | Except.ok rest' =>
                        Except.ok (Miri.MIR.ProjectionElem.Field idx tyId :: rest')
                      | Except.error k => Except.error k) = Except.error k
                  rw [h_sub]
                | ok rest' =>
                  rw [h_rp] at h_sub
                  first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                  first | dsimp only [placeTyToRefPlaceTy] | change _
                  let ⟨mps, h_ok, h_mdec, h_canon⟩ := h_sub
                  refine ⟨.Field idx tyId :: mps, ?_, ?_, ⟨rfl, h_canon⟩⟩
                  · rw [h_pf]
                    dsimp only
                    rw [refFieldsForVariant?_eq, h_fv, h_t]
                    dsimp only
                    rw [h_gf]
                    dsimp only
                    rw [h_beq, ite_true_eq_true]
                    change (match refResolveProjPath ts rlocals (.ty ty')
                          (res.map toMiriProjElem) with
                        | Except.ok r' =>
                          Except.ok (Miri.MIR.ProjectionElem.Field idx tyId :: r')
                        | Except.error k => Except.error k) = _
                    rw [h_ok]
                  · dsimp only [mapOption, decodeMiriProjElem, optMap, optMap2]
                    rw [h_t, h_mdec]
        | ty t =>
          cases t with
          | tuple fieldTys =>
            first | dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
              refResolveProjPath, refProjectStep, resolveProjPath] at h_pf | change _
            first | dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
              refResolveProjPath, refProjectStep, resolveProjPath] | change _
            cases h_gf : MirSemantics.getElem? fieldTys idx with
            | none =>
              rw [h_gf] at h_pf
              first | dsimp only at h_pf | change _
              first | dsimp only | change _
              let ⟨n, h_err⟩ := h_pf
              rw [h_err]
              rfl
            | some ty' =>
              rw [h_gf] at h_pf
              first | dsimp only at h_pf | change _
              first | dsimp only | change _
              cases h_beq : MirTy.beq ty' statedTy with
              | false =>
                dsimp only [ite_false_eq_true]
                rw [h_pf]
                dsimp only
                rw [h_t]
                dsimp only
                rw [h_beq]
                rfl
              | true =>
                rw [ite_true_eq_true]
                have h_sub := ih h_res (.ty ty')
                cases h_rp : resolveProjPath bodyLocals slots (.ty ty') es with
                | error k =>
                  rw [h_rp] at h_sub
                  first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                  first | dsimp only [placeTyToRefPlaceTy] | change _
                  rw [h_pf]
                  dsimp only
                  rw [h_t]
                  dsimp only
                  rw [h_beq, ite_true_eq_true]
                  change (match refResolveProjPath ts rlocals (.ty ty')
                        (res.map toMiriProjElem) with
                      | Except.ok rest' =>
                        Except.ok (Miri.MIR.ProjectionElem.Field idx tyId :: rest')
                      | Except.error k => Except.error k) = Except.error k
                  rw [h_sub]
                | ok rest' =>
                  rw [h_rp] at h_sub
                  first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                  first | dsimp only [placeTyToRefPlaceTy] | change _
                  let ⟨mps, h_ok, h_mdec, h_canon⟩ := h_sub
                  refine ⟨.Field idx tyId :: mps, ?_, ?_, ⟨rfl, h_canon⟩⟩
                  · rw [h_pf]
                    dsimp only
                    rw [h_t]
                    dsimp only
                    rw [h_beq, ite_true_eq_true]
                    change (match refResolveProjPath ts rlocals (.ty ty')
                          (res.map toMiriProjElem) with
                        | Except.ok r' =>
                          Except.ok (Miri.MIR.ProjectionElem.Field idx tyId :: r')
                        | Except.error k => Except.error k) = _
                    rw [h_ok]
                  · dsimp only [mapOption, decodeMiriProjElem, optMap, optMap2]
                    rw [h_t, h_mdec]
          | adtStruct sty =>
            first | dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
              refResolveProjPath, refProjectStep, resolveProjPath] at h_pf | change _
            first | dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
              refResolveProjPath, refProjectStep, resolveProjPath] | change _
            cases h_gf : MirSemantics.getElem? sty.fields idx with
            | none =>
              rw [h_gf] at h_pf
              first | dsimp only at h_pf | change _
              first | dsimp only | change _
              let ⟨n, h_err⟩ := h_pf
              rw [h_err]
              rfl
            | some ty' =>
              rw [h_gf] at h_pf
              first | dsimp only at h_pf | change _
              first | dsimp only | change _
              cases h_beq : MirTy.beq ty' statedTy with
              | false =>
                dsimp only [ite_false_eq_true]
                rw [h_pf]
                dsimp only
                rw [h_t]
                dsimp only
                rw [h_beq]
                rfl
              | true =>
                rw [ite_true_eq_true]
                have h_sub := ih h_res (.ty ty')
                cases h_rp : resolveProjPath bodyLocals slots (.ty ty') es with
                | error k =>
                  rw [h_rp] at h_sub
                  first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                  first | dsimp only [placeTyToRefPlaceTy] | change _
                  rw [h_pf]
                  dsimp only
                  rw [h_t]
                  dsimp only
                  rw [h_beq, ite_true_eq_true]
                  change (match refResolveProjPath ts rlocals (.ty ty')
                        (res.map toMiriProjElem) with
                      | Except.ok rest' =>
                        Except.ok (Miri.MIR.ProjectionElem.Field idx tyId :: rest')
                      | Except.error k => Except.error k) = Except.error k
                  rw [h_sub]
                | ok rest' =>
                  rw [h_rp] at h_sub
                  first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                  first | dsimp only [placeTyToRefPlaceTy] | change _
                  let ⟨mps, h_ok, h_mdec, h_canon⟩ := h_sub
                  refine ⟨.Field idx tyId :: mps, ?_, ?_, ⟨rfl, h_canon⟩⟩
                  · rw [h_pf]
                    dsimp only
                    rw [h_t]
                    dsimp only
                    rw [h_beq, ite_true_eq_true]
                    change (match refResolveProjPath ts rlocals (.ty ty')
                          (res.map toMiriProjElem) with
                        | Except.ok r' =>
                          Except.ok (Miri.MIR.ProjectionElem.Field idx tyId :: r')
                        | Except.error k => Except.error k) = _
                    rw [h_ok]
                  · dsimp only [mapOption, decodeMiriProjElem, optMap, optMap2]
                    rw [h_t, h_mdec]
          | bool | int _ _ | unit | never | enum _ | array _ _ | ref _ _
          | rawPtr _ _ | unsupported =>
            first | dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
              refResolveProjPath, refProjectStep, resolveProjPath] at h_pf | change _
            first | dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
              refResolveProjPath, refProjectStep, resolveProjPath] | change _
            let ⟨n, h_err⟩ := h_pf
            rw [h_err]
            rfl
    | downcast v =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | enum ety =>
          dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refResolveProjPath, refProjectStep, Miri.Interpreter.project,
            Miri.Interpreter.projectDowncast, refProjectionCx,
            resolveProjPath, bind, Except.bind]
          rw [refEnumAdmitted_eq]
          cases (enumAdmitted ety && Nat.blt v ety.discriminants.length) with
          | false => rfl
          | true =>
            rw [ite_true_eq_true]
            dsimp only [Miri.Interpreter.OpTy.metadata,
              Miri.Interpreter.MemPlaceMeta.hasMeta, refBaseOpForProjStep,
              Miri.Interpreter.OpTy.offset, refSizedLocalLayout,
              refBaseLayoutData, LayoutData.isSized, BackendRepr.isSized,
              BackendRepr.isUnsized, Bool.not_false, Bool.not_true,
              ite_false_eq_true, Miri.Interpreter.OpTy.offsetWithMeta, pure,
              Except.pure]
            have h_sub := ih h_res (.variant ety v)
            cases h_rp :
                resolveProjPath bodyLocals slots (.variant ety v) es with
            | error k =>
              rw [h_rp] at h_sub
              first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
              first | dsimp only [placeTyToRefPlaceTy] | change _
              change (match refResolveProjPath ts rlocals (.variant ety v)
                    (res.map toMiriProjElem) with
                  | Except.ok r' =>
                    Except.ok (Miri.MIR.ProjectionElem.Downcast none v :: r')
                  | Except.error k => Except.error k) = Except.error k
              rw [h_sub]
            | ok rest' =>
              rw [h_rp] at h_sub
              first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
              first | dsimp only [placeTyToRefPlaceTy] | change _
              let ⟨mps, h_ok, h_mdec, h_canon⟩ := h_sub
              refine ⟨.Downcast none v :: mps, ?_, ?_, ⟨rfl, h_canon⟩⟩
              · change (match refResolveProjPath ts rlocals (.variant ety v)
                      (res.map toMiriProjElem) with
                    | Except.ok r' =>
                      Except.ok (Miri.MIR.ProjectionElem.Downcast none v :: r')
                    | Except.error k => Except.error k) = _
                rw [h_ok]
              · dsimp only [mapOption, decodeMiriProjElem, optMap2]
                rw [h_mdec]
        | bool | int _ _ | unit | never | adtStruct _ | tuple _ | array _ _
        | ref _ _ | rawPtr _ _ | unsupported => rfl
    | constantIndex offset minLength fromEnd =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ =>
        dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
          refResolveProjPath, refProjectStep, Miri.Interpreter.project,
          resolveProjPath]
        cases (decide (offset ≥ HPow.hPow 2 64) ||
          decide (minLength ≥ HPow.hPow 2 64)) <;> rfl
      | ty t =>
        cases t with
        | array elemTy len =>
          dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refResolveProjPath, refProjectStep, resolveProjPath]
          cases h_len : Nat.blt len (Nat.pow 2 64) with
          | false =>
            rw [Bool.not_false, ite_true_eq_true]
            dsimp only [Miri.Interpreter.project, refBaseOpForProjStep]
            rw [h_len, ite_false_eq_true]
            cases (decide (offset ≥ HPow.hPow 2 64) ||
              decide (minLength ≥ HPow.hPow 2 64)) <;> rfl
          | true =>
            rw [Bool.not_true, ite_false_eq_true]
            have h_pc := projectConstantIndex_array_eq
              (refProjLocalIndex rlocals) elemTy len offset minLength fromEnd
              (nat_lt_of_blt_eq_true h_len)
            cases h_ci : evalConstantIndex len offset minLength fromEnd with
            | error k =>
              rw [h_ci] at h_pc
              first | dsimp only at h_pc | change _
              first | dsimp only | change _
              let ⟨err, h_err, h_fk⟩ := h_pc
              rw [h_err]
              dsimp only
              rw [h_fk]
            | ok idx =>
              rw [h_ci] at h_pc
              first | dsimp only at h_pc | change _
              first | dsimp only | change _
              let ⟨h_ok_op, h_tn⟩ := h_pc
              have h_sub := ih h_res (.ty elemTy)
              cases h_rp :
                  resolveProjPath bodyLocals slots (.ty elemTy) es with
              | error k =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                rw [h_ok_op]
                dsimp only [Miri.ABI.Size.ofBytes]
                rw [h_tn]
                change (match refResolveProjPath ts rlocals (.ty elemTy)
                      (res.map toMiriProjElem) with
                    | Except.ok r' =>
                      Except.ok
                        (Miri.MIR.ProjectionElem.ConstantIndex idx (idx + 1)
                          false :: r')
                    | Except.error k => Except.error k) = Except.error k
                rw [h_sub]
              | ok rest' =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                let ⟨mps, h_ok, h_mdec, h_canon⟩ := h_sub
                refine ⟨.ConstantIndex idx (idx + 1) false :: mps, ?_, ?_,
                  ⟨⟨rfl, rfl⟩, h_canon⟩⟩
                · rw [h_ok_op]
                  dsimp only [Miri.ABI.Size.ofBytes]
                  rw [h_tn]
                  change (match refResolveProjPath ts rlocals (.ty elemTy)
                        (res.map toMiriProjElem) with
                      | Except.ok r' =>
                        Except.ok
                          (Miri.MIR.ProjectionElem.ConstantIndex idx (idx + 1)
                            false :: r')
                      | Except.error k => Except.error k) = _
                  rw [h_ok]
                · dsimp only [mapOption, decodeMiriProjElem, optMap2]
                  rw [h_mdec]
        | bool | int _ _ | unit | never | adtStruct _ | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | unsupported =>
          dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refResolveProjPath, refProjectStep, Miri.Interpreter.project,
            resolveProjPath]
          cases (decide (offset ≥ HPow.hPow 2 64) ||
            decide (minLength ≥ HPow.hPow 2 64)) <;> rfl
    | index idxLocal =>
      injection h_re with h_e
      subst h_e
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | array elemTy len =>
          dsimp only [List.map, toMiriProjElem, placeTyToRefPlaceTy,
            refResolveProjPath, resolveProjPath]
          cases h_len : Nat.blt len (Nat.pow 2 64) with
          | false =>
            rw [Bool.not_false, ite_true_eq_true]
            dsimp only [refProjectStep, Miri.Interpreter.project,
              refProjectionCx]
            rw [h_len]
            rfl
          | true =>
            rw [Bool.not_true, ite_false_eq_true]
            let cx :=
              refProjectionCx (.ty (.array elemTy len))
                (refProjLocalIndex rlocals)
            have h_li_def :
                cx.localIndex idxLocal = refProjLocalIndex rlocals idxLocal := by
              dsimp only [cx, refProjectionCx]
              rw [h_len, ite_true_eq_true]
            have h_proj_idx :
                refProjectStep ts (refProjLocalIndex rlocals)
                  (.ty (.array elemTy len)) (.Index idxLocal) =
                match refProjLocalIndex rlocals idxLocal with
                | .error err => .error (projErrorToFaultKind err)
                | .ok index =>
                  match Miri.Interpreter.projectIndex cx
                      (refBaseOpForProjStep (.ty (.array elemTy len))
                        (.Index idxLocal)) index with
                  | .error err => .error (projErrorToFaultKind err)
                  | .ok outOp =>
                    match outOp.op with
                    | .indirect mp =>
                      let idx := mp.ptr.offset.bytes.toNat
                      .ok (.ty elemTy, .ConstantIndex idx (idx + 1) false)
                    | .immediate _ => .error .unsupported := by
              dsimp only [refProjectStep, Miri.Interpreter.project, bind,
                Except.bind]
              rw [h_li_def]
              cases refProjLocalIndex rlocals idxLocal <;> rfl
            rw [h_proj_idx]
            cases h_bty : MirSemantics.getElem? bodyLocals idxLocal with
            | none =>
              dsimp only [refProjLocalIndex, rlocals]
              rw [getElem?_zipRefLocals_none_left h_bty]
              rfl
            | some idxTy =>
              cases h_isl : MirSemantics.getElem? slots idxLocal with
              | none =>
                dsimp only [refProjLocalIndex, rlocals]
                rw [getElem?_zipRefLocals_none_right h_isl]
                cases idxTy with
                | int w s => cases w <;> cases s <;> rfl
                | _ => rfl
              | some idxSlot =>
                have h_z := getElem?_zipRefLocals_some h_bty h_isl
                have h_rpli :
                    refProjLocalIndex rlocals idxLocal =
                      expectedRefLocalIndex idxTy idxSlot := by
                  dsimp only [refProjLocalIndex, rlocals]
                  rw [h_z]
                  cases idxTy with
                  | int w s =>
                    cases w with
                    | isize =>
                      cases s with
                      | true => rfl
                      | false =>
                        cases idxSlot with
                        | dead => rfl
                        | live idxSv =>
                          dsimp only
                          rw [evalPlaceToOp_sized_live]
                          dsimp only
                          rw [miriImmToPayload?_roundtrip]
                          cases idxSv with
                          | scalar sv =>
                            dsimp only [expectedRefLocalIndex]
                            rw [miriScalar_data]
                          | _ => rfl
                    | _ => rfl
                  | _ => rfl
                rw [h_rpli]
                cases idxTy with
                | int w s =>
                  cases w with
                  | isize =>
                    cases s with
                    | true => rfl
                    | false =>
                      cases idxSlot with
                      | dead => rfl
                      | live idxSv =>
                        cases idxSv with
                        | uninit => rfl
                        | scalar sv =>
                          dsimp only [expectedRefLocalIndex,
                            refBaseOpForProjStep]
                          rw [h_len, ite_true_eq_true]
                          let idx := (truncateBits .isize sv.bits).toNat
                          have h_idx_u64 : idx < Nat.pow 2 64 := by
                            dsimp only [idx]
                            rw [toNat_truncateBits]
                            exact Nat.mod_lt sv.bits.toNat
                              (intWidth_modulus_pos .isize)
                          have h_pi := projectIndex_array_eq
                            (refProjLocalIndex rlocals) elemTy
                            (nat_lt_of_blt_eq_true h_len) h_idx_u64
                          first | dsimp only [cx, idx] at h_pi | change _
                          first | dsimp only [cx, idx] | change _
                          cases h_ib : Nat.blt idx len with
                          | false =>
                            dsimp only [idx] at h_ib
                            rw [h_ib, ite_false_eq_true] at h_pi
                            rw [ite_false_eq_true]
                            dsimp only
                            rw [h_pi]
                            rfl
                          | true =>
                            dsimp only [idx] at h_ib
                            rw [h_ib, ite_true_eq_true] at h_pi
                            rw [ite_true_eq_true]
                            have h_sub := ih h_res (.ty elemTy)
                            cases h_rp : resolveProjPath bodyLocals slots
                                (.ty elemTy) es with
                            | error k =>
                              rw [h_rp] at h_sub
                              first | dsimp only [placeTyToRefPlaceTy, rlocals] at h_sub | change _
                              first | dsimp only [placeTyToRefPlaceTy, rlocals] | change _
                              dsimp only [rlocals] at h_pi
                              rw [h_pi]
                              dsimp only [Miri.ABI.Size.ofBytes]
                              rw [uint64_toNat_ofNat_lt h_idx_u64]
                              change (match refResolveProjPath ts
                                    (zipRefLocals bodyLocals slots)
                                    (.ty elemTy)
                                    (res.map toMiriProjElem) with
                                  | Except.ok r' =>
                                    Except.ok
                                      (Miri.MIR.ProjectionElem.ConstantIndex
                                        idx (idx + 1) false :: r')
                                  | Except.error k =>
                                    Except.error k) = Except.error k
                              rw [h_sub]
                            | ok rest' =>
                              rw [h_rp] at h_sub
                              first | dsimp only [placeTyToRefPlaceTy, rlocals] at h_sub | change _
                              first | dsimp only [placeTyToRefPlaceTy, rlocals] | change _
                              dsimp only [rlocals] at h_pi
                              let ⟨mps, h_ok, h_mdec, h_canon⟩ := h_sub
                              refine ⟨.ConstantIndex idx (idx + 1) false :: mps,
                                ?_, ?_, ⟨⟨rfl, rfl⟩, h_canon⟩⟩
                              · rw [h_pi]
                                dsimp only [Miri.ABI.Size.ofBytes]
                                rw [uint64_toNat_ofNat_lt h_idx_u64]
                                change (match refResolveProjPath ts
                                      (zipRefLocals bodyLocals slots)
                                      (.ty elemTy)
                                      (res.map toMiriProjElem) with
                                    | Except.ok r' =>
                                      Except.ok
                                        (Miri.MIR.ProjectionElem.ConstantIndex
                                          idx (idx + 1) false :: r')
                                    | Except.error k => Except.error k) = _
                                rw [h_ok]
                              · dsimp only [mapOption, decodeMiriProjElem,
                                  optMap2]
                                rw [h_mdec]
                        | _ => rfl
                  | _ => rfl
                | _ => rfl
        | bool | int _ _ | unit | never | adtStruct _ | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | unsupported => rfl

theorem refResolveStaticReturnProj_eq (pty : PlaceTy)
    (proj : List ProjectionElem) :
    match resolveStaticProjPath pty proj with
    | .error k =>
      refResolveStaticReturnProj (placeTyToRefPlaceTy pty) proj = .error k
    | .ok resolvedProj =>
      ∃ resolvedMiriProj,
        refResolveStaticReturnProj (placeTyToRefPlaceTy pty) proj =
          .ok resolvedMiriProj ∧
        CanonProjList resolvedMiriProj resolvedProj := by
  induction proj generalizing pty with
  | nil =>
    cases pty with
    | ty _ => exact ⟨[], rfl, trivial⟩
    | variant _ _ => rfl
  | cons e es ih =>
    let noIdx : Miri.MIR.LocalId →
        Except Miri.Interpreter.ProjectionError UInt64 :=
      fun _ => .error (.invariant "dynamic index in static return proj")
    cases e with
    | deref | index _ | unsupported =>
      cases pty with
      | variant _ _ => rfl
      | ty t => cases t <;> rfl
    | field idx statedTy =>
      have h_pf := projectField_refProjectionCx_eq noIdx pty idx 0
      cases pty with
      | variant ety v =>
        first | dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
          resolveStaticProjPath] at h_pf | change _
        first | dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
          resolveStaticProjPath] | change _
        cases h_fv : fieldsForVariant? ety v with
        | none =>
          rw [h_fv] at h_pf
          first | dsimp only at h_pf | change _
          first | dsimp only | change _
          let ⟨n, h_err⟩ := h_pf
          rw [h_err]; rfl
        | some varFields =>
          rw [h_fv] at h_pf
          first | dsimp only at h_pf | change _
          first | dsimp only | change _
          cases h_gf : MirSemantics.getElem? varFields idx with
          | none =>
            rw [h_gf] at h_pf
            first | dsimp only at h_pf | change _
            first | dsimp only | change _
            let ⟨n, h_err⟩ := h_pf
            rw [h_err]; rfl
          | some ty' =>
            rw [h_gf] at h_pf
            first | dsimp only at h_pf | change _
            first | dsimp only | change _
            cases h_beq : MirTy.beq ty' statedTy with
            | false =>
              dsimp only [ite_false_eq_true]
              rw [h_pf]
              dsimp only
              rw [refFieldsForVariant?_eq, h_fv]
              dsimp only
              rw [h_gf]
              dsimp only
              rw [h_beq]
              rfl
            | true =>
              rw [ite_true_eq_true]
              have h_sub := ih (.ty ty')
              cases h_rp : resolveStaticProjPath (.ty ty') es with
              | error k =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                rw [h_pf]
                dsimp only
                rw [refFieldsForVariant?_eq, h_fv]
                dsimp only
                rw [h_gf]
                dsimp only
                rw [h_beq, ite_true_eq_true]
                change (match refResolveStaticReturnProj (.ty ty') es with
                    | Except.ok r' =>
                      Except.ok (Miri.MIR.ProjectionElem.Field idx 0 :: r')
                    | Except.error k => Except.error k) = Except.error k
                rw [h_sub]
              | ok rest' =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                let ⟨mps, h_ok, h_canon⟩ := h_sub
                refine ⟨.Field idx 0 :: mps, ?_, ⟨rfl, h_canon⟩⟩
                rw [h_pf]
                dsimp only
                rw [refFieldsForVariant?_eq, h_fv]
                dsimp only
                rw [h_gf]
                dsimp only
                rw [h_beq, ite_true_eq_true]
                change (match refResolveStaticReturnProj (.ty ty') es with
                    | Except.ok r' =>
                      Except.ok (Miri.MIR.ProjectionElem.Field idx 0 :: r')
                    | Except.error k => Except.error k) = _
                rw [h_ok]
      | ty t =>
        cases t with
        | tuple fieldTys =>
          first | dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            resolveStaticProjPath] at h_pf | change _
          first | dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            resolveStaticProjPath] | change _
          cases h_gf : MirSemantics.getElem? fieldTys idx with
          | none =>
            rw [h_gf] at h_pf
            first | dsimp only at h_pf | change _
            first | dsimp only | change _
            let ⟨n, h_err⟩ := h_pf
            rw [h_err]; rfl
          | some ty' =>
            rw [h_gf] at h_pf
            first | dsimp only at h_pf | change _
            first | dsimp only | change _
            cases h_beq : MirTy.beq ty' statedTy with
            | false =>
              dsimp only [ite_false_eq_true]
              rw [h_pf]
            | true =>
              rw [ite_true_eq_true]
              have h_sub := ih (.ty ty')
              cases h_rp : resolveStaticProjPath (.ty ty') es with
              | error k =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                rw [h_pf]
                dsimp only [ite_true_eq_true]
                change (match refResolveStaticReturnProj (.ty ty') es with
                    | Except.ok r' =>
                      Except.ok (Miri.MIR.ProjectionElem.Field idx 0 :: r')
                    | Except.error k => Except.error k) = Except.error k
                rw [h_sub]
              | ok rest' =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                let ⟨mps, h_ok, h_canon⟩ := h_sub
                refine ⟨.Field idx 0 :: mps, ?_, ⟨rfl, h_canon⟩⟩
                rw [h_pf]
                dsimp only [ite_true_eq_true]
                change (match refResolveStaticReturnProj (.ty ty') es with
                    | Except.ok r' =>
                      Except.ok (Miri.MIR.ProjectionElem.Field idx 0 :: r')
                    | Except.error k => Except.error k) = _
                rw [h_ok]
        | adtStruct sty =>
          first | dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            resolveStaticProjPath] at h_pf | change _
          first | dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            resolveStaticProjPath] | change _
          cases h_gf : MirSemantics.getElem? sty.fields idx with
          | none =>
            rw [h_gf] at h_pf
            first | dsimp only at h_pf | change _
            first | dsimp only | change _
            let ⟨n, h_err⟩ := h_pf
            rw [h_err]; rfl
          | some ty' =>
            rw [h_gf] at h_pf
            first | dsimp only at h_pf | change _
            first | dsimp only | change _
            cases h_beq : MirTy.beq ty' statedTy with
            | false =>
              dsimp only [ite_false_eq_true]
              rw [h_pf]
            | true =>
              rw [ite_true_eq_true]
              have h_sub := ih (.ty ty')
              cases h_rp : resolveStaticProjPath (.ty ty') es with
              | error k =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                rw [h_pf]
                dsimp only [ite_true_eq_true]
                change (match refResolveStaticReturnProj (.ty ty') es with
                    | Except.ok r' =>
                      Except.ok (Miri.MIR.ProjectionElem.Field idx 0 :: r')
                    | Except.error k => Except.error k) = Except.error k
                rw [h_sub]
              | ok rest' =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                let ⟨mps, h_ok, h_canon⟩ := h_sub
                refine ⟨.Field idx 0 :: mps, ?_, ⟨rfl, h_canon⟩⟩
                rw [h_pf]
                dsimp only [ite_true_eq_true]
                change (match refResolveStaticReturnProj (.ty ty') es with
                    | Except.ok r' =>
                      Except.ok (Miri.MIR.ProjectionElem.Field idx 0 :: r')
                    | Except.error k => Except.error k) = _
                rw [h_ok]
        | bool | int _ _ | unit | never | enum _ | array _ _ | ref _ _
        | rawPtr _ _ | unsupported =>
          first | dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            resolveStaticProjPath] at h_pf | change _
          first | dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            resolveStaticProjPath] | change _
          let ⟨n, h_err⟩ := h_pf
          rw [h_err]; rfl
    | downcast v =>
      cases pty with
      | variant _ _ => rfl
      | ty t =>
        cases t with
        | enum ety =>
          dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            Miri.Interpreter.project, Miri.Interpreter.projectDowncast,
            refProjectionCx, resolveStaticProjPath, bind, Except.bind]
          rw [refEnumAdmitted_eq]
          cases (enumAdmitted ety && Nat.blt v ety.discriminants.length) with
          | false => rfl
          | true =>
            rw [ite_true_eq_true]
            dsimp only [Miri.Interpreter.OpTy.metadata,
              Miri.Interpreter.MemPlaceMeta.hasMeta, refBaseOpForProjStep,
              Miri.Interpreter.OpTy.offset, refSizedLocalLayout,
              refBaseLayoutData, LayoutData.isSized, BackendRepr.isSized,
              BackendRepr.isUnsized, Bool.not_false, Bool.not_true,
              ite_false_eq_true, Miri.Interpreter.OpTy.offsetWithMeta, pure,
              Except.pure]
            have h_sub := ih (.variant ety v)
            cases h_rp : resolveStaticProjPath (.variant ety v) es with
            | error k =>
              rw [h_rp] at h_sub
              first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
              first | dsimp only [placeTyToRefPlaceTy] | change _
              change (match refResolveStaticReturnProj (.variant ety v) es with
                  | Except.ok r' =>
                    Except.ok (Miri.MIR.ProjectionElem.Downcast none v :: r')
                  | Except.error k => Except.error k) = Except.error k
              rw [h_sub]
            | ok rest' =>
              rw [h_rp] at h_sub
              first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
              first | dsimp only [placeTyToRefPlaceTy] | change _
              let ⟨mps, h_ok, h_canon⟩ := h_sub
              refine ⟨.Downcast none v :: mps, ?_, ⟨rfl, h_canon⟩⟩
              change (match refResolveStaticReturnProj (.variant ety v) es with
                  | Except.ok r' =>
                    Except.ok (Miri.MIR.ProjectionElem.Downcast none v :: r')
                  | Except.error k => Except.error k) = _
              rw [h_ok]
        | bool | int _ _ | unit | never | adtStruct _ | tuple _ | array _ _
        | ref _ _ | rawPtr _ _ | unsupported => rfl
    | constantIndex offset minLength fromEnd =>
      cases pty with
      | variant _ _ =>
        dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
          Miri.Interpreter.project, resolveStaticProjPath]
        cases (decide (offset ≥ HPow.hPow 2 64) ||
          decide (minLength ≥ HPow.hPow 2 64)) <;> rfl
      | ty t =>
        cases t with
        | array elemTy len =>
          dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            resolveStaticProjPath]
          cases h_len : Nat.blt len (Nat.pow 2 64) with
          | false =>
            rw [Bool.not_false, ite_true_eq_true]
            dsimp only [Miri.Interpreter.project, refBaseOpForProjStep]
            rw [h_len, ite_false_eq_true]
            cases (decide (offset ≥ HPow.hPow 2 64) ||
              decide (minLength ≥ HPow.hPow 2 64)) <;> rfl
          | true =>
            rw [Bool.not_true, ite_false_eq_true]
            have h_pc := projectConstantIndex_array_eq noIdx elemTy len offset
              minLength fromEnd (nat_lt_of_blt_eq_true h_len)
            cases h_ci : evalConstantIndex len offset minLength fromEnd with
            | error k =>
              rw [h_ci] at h_pc
              first | dsimp only at h_pc | change _
              first | dsimp only | change _
              let ⟨err, h_err, h_fk⟩ := h_pc
              rw [h_err]
              dsimp only
              rw [h_fk]
            | ok idx =>
              rw [h_ci] at h_pc
              first | dsimp only at h_pc | change _
              first | dsimp only | change _
              let ⟨h_ok_op, h_tn⟩ := h_pc
              have h_sub := ih (.ty elemTy)
              cases h_rp : resolveStaticProjPath (.ty elemTy) es with
              | error k =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                rw [h_ok_op]
                dsimp only [Miri.ABI.Size.ofBytes]
                rw [h_tn]
                change (match refResolveStaticReturnProj (.ty elemTy) es with
                    | Except.ok r' =>
                      Except.ok
                        (Miri.MIR.ProjectionElem.ConstantIndex idx (idx + 1)
                          false :: r')
                    | Except.error k => Except.error k) = Except.error k
                rw [h_sub]
              | ok rest' =>
                rw [h_rp] at h_sub
                first | dsimp only [placeTyToRefPlaceTy] at h_sub | change _
                first | dsimp only [placeTyToRefPlaceTy] | change _
                let ⟨mps, h_ok, h_canon⟩ := h_sub
                refine ⟨.ConstantIndex idx (idx + 1) false :: mps, ?_,
                  ⟨⟨rfl, rfl⟩, h_canon⟩⟩
                rw [h_ok_op]
                dsimp only [Miri.ABI.Size.ofBytes]
                rw [h_tn]
                change (match refResolveStaticReturnProj (.ty elemTy) es with
                    | Except.ok r' =>
                      Except.ok
                        (Miri.MIR.ProjectionElem.ConstantIndex idx (idx + 1)
                          false :: r')
                    | Except.error k => Except.error k) = _
                rw [h_ok]
        | bool | int _ _ | unit | never | adtStruct _ | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | unsupported =>
          dsimp only [placeTyToRefPlaceTy, refResolveStaticReturnProj,
            Miri.Interpreter.project, resolveStaticProjPath]
          cases (decide (offset ≥ HPow.hPow 2 64) ||
            decide (minLength ≥ HPow.hPow 2 64)) <;> rfl

private theorem size_zero_mul_eq (c : UInt64) :
    Miri.ABI.Size.ZERO.mul c = .ok Miri.ABI.Size.ZERO := by
  have h_zero_mul : (0 : UInt64) * c = 0 := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 (0 * c.toNat)).toNat = 0
    rw [Nat.zero_mul]
    rfl
  have h_zero_div : HDiv.hDiv (0 : UInt64) c = 0 := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change HDiv.hDiv 0 c.toNat = 0
    exact Nat.zero_div c.toNat
  dsimp only [Miri.ABI.Size.mul, Miri.ABI.Size.ZERO]
  rw [h_zero_mul, h_zero_div]
  have h_bne : ((0 : UInt64) != 0) = false := rfl
  rw [h_bne, Bool.and_false, ite_false_eq_true]
  rfl

private theorem ite_estate_apply {S E A : Type} (c : Prop) [inst : Decidable c]
    (f g : EStateM E S A) (s : S) :
    (if c then f else g) s = (if c then f s else g s) := by
  cases inst <;> rfl

theorem refProjectArrayAggregateElem_eq (elemTy : MirTy) {len index : Nat}
    (h_len : len < Nat.pow 2 64) (h_idx : index < len) :
    refProjectArrayAggregateElem elemTy len index =
      .ok (.ConstantIndex index (index + 1) false) := by
  have h_len_blt : Nat.blt len (Nat.pow 2 64) = true :=
    Nat.ble_eq_true_of_le h_len
  have h_idx_blt : Nat.blt index len = true :=
    Nat.ble_eq_true_of_le h_idx
  have h_idx_u64 : index < Nat.pow 2 64 := Nat.lt_trans h_idx h_len
  have h_len_tn := uint64_toNat_ofNat_lt h_len
  have h_idx_tn := uint64_toNat_ofNat_lt h_idx_u64
  dsimp only [refProjectArrayAggregateElem,
    Miri.Interpreter.projectArrayFields, Miri.Interpreter.OpTy.len,
    refSizedLocalLayout, refBaseLayoutData, LayoutData.isSized,
    BackendRepr.isSized, BackendRepr.isUnsized,
    refProjectionCx, bind, Except.bind, pure, Except.pure]
  simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false]
  rw [h_len_blt]
  dsimp only [Nat.beq, Bool.true_and, ite_true_eq_true]
  rw [size_zero_mul_eq]
  dsimp only [Miri.Interpreter.OpTy.offset, refLocalLayoutZst,
    refBaseLayoutData, LayoutData.isSized, BackendRepr.isSized,
    BackendRepr.isUnsized, Miri.Interpreter.OpTy.offsetWithMeta,
    bind, Except.bind, pure, Except.pure, Except.mapError, Bool.true_and]
  simp only [Bool.and_self, ite_true, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ite_false, h_idx_blt]
  dsimp only [Miri.Interpreter.ProjectionArrayIterator.next, Bind.bind,
    Pure.pure, EStateM.bind, EStateM.get]
  have h_nge : ¬ (UInt64.ofNat index ≥ UInt64.ofNat len) := by
    change ¬ ((UInt64.ofNat len).toNat ≤ (UInt64.ofNat index).toNat)
    rw [h_len_tn, h_idx_tn]
    exact Nat.not_le_of_gt h_idx
  rw [ite_estate_apply, ite_eq_right h_nge]
  dsimp only [EStateM.bind, EStateM.pure, EStateM.set]
  rw [size_zero_mul_eq]
  dsimp only [Miri.Interpreter.OpTy.offsetWithMeta, EStateM.bind, EStateM.pure,
    bind, Except.bind, pure, Except.pure]
  rw [h_idx_tn]

theorem otherVariantsValidForNiche_at {ety : EnumTy}
    {untagged start last : Nat} :
    ∀ {n k : Nat},
      otherVariantsValidForNiche ety untagged start last n = true →
      k < n →
      (if Nat.beq k untagged then
         true
       else if isVariantUninhabited ety k then
         true
       else
         Nat.ble start k &&
           Nat.ble k last &&
           match fieldsForVariant? ety k with
           | some fs => areAllZeroSizedTys fs
           | none => false) = true
  | 0, _, _, hk => nomatch hk
  | m + 1, k, h_all, hk => by
    cases h_km : Nat.beq k m with
    | true =>
      have h_eq := Nat.eq_of_beq_eq_true h_km
      subst h_eq
      exact bool_and_right h_all
    | false =>
      have h_ne : k ≠ m := by
        intro h_eq; subst h_eq; rw [Nat.beq_refl] at h_km; cases h_km
      have hk_lt : k < m :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) h_ne
      exact otherVariantsValidForNiche_at (bool_and_left h_all) hk_lt

private theorem refScalarLayoutData_size_eq (w : IntWidth) (signed : Bool) :
    (refScalarLayoutData w signed).size = toMiriSize w := by
  cases w <;> cases signed <;> rfl

private noncomputable def liftOptTag {S A : Type}
    (res : Except Miri.Interpreter.StepError A)
    (k : A → Miri.Interpreter.RvalueM S (Option (ScalarInt × Nat))) :
    Miri.Interpreter.RvalueM S (Option (ScalarInt × Nat)) :=
  Bind.bind (match res with | .ok v => Pure.pure v | .error e => throw e) k

private noncomputable def runTagForVariantInner (S : Type)
    (getL : S → List RefLocalState) (ety : EnumTy) (variantIdx : Nat) :
    Miri.Interpreter.RvalueM S (Option (ScalarInt × Nat)) :=
  let h := refWriteDiscriminantHooks S getL (.enum ety) (some ety) variantIdx
  match (refEnumLayoutData ety).variants with
  | .Empty => throw (.invalidProgram "inhabited empty layout")
  | .Single _ => Pure.pure none
  | .Multiple tag .Direct field _ =>
    Bind.bind
      (Miri.Interpreter.Discriminant.discriminantForVariant h () 0 variantIdx)
      (fun discr =>
        liftOptTag
          (discr.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError)
          (fun sc =>
            liftOptTag
              ((sc.toBits discr.layout.layout.size).mapError
                Miri.Interpreter.ScalarOps.scalarError)
              (fun bits =>
                Bind.bind
                  (match tag.size h.runtimeTarget with
                   | .ok sz => Pure.pure sz
                   | .error e =>
                     throw (.invalidProgram
                       (toString "tag scalar size: " ++ toString (repr e))))
                  (fun sz =>
                    liftOptTag
                      ((sz.truncate bits).mapError
                        (fun e =>
                          Miri.Interpreter.StepError.invalidProgram
                            (toString e)))
                      (fun tBits =>
                        liftOptTag
                          ((Miri.Memory.Scalar.fromUInt
                            (Prov := Miri.Memory.Provenance) tBits sz).mapError
                            Miri.Interpreter.ScalarOps.scalarError)
                          (fun tSc0 =>
                            liftOptTag
                              (tSc0.toScalarInt.mapError
                                Miri.Interpreter.ScalarOps.scalarError)
                              (fun si => Pure.pure (some (si, field)))))))))
  | .Multiple tag (.Niche untagged start last nicheStart) field _ =>
    if variantIdx == untagged then
      Pure.pure none
    else
      let jpRange : Unit →
          Miri.Interpreter.RvalueM S (Option (ScalarInt × Nat)) := fun _ =>
        let jpU32 : Unit →
            Miri.Interpreter.RvalueM S (Option (ScalarInt × Nat)) := fun _ =>
          Bind.bind (h.tagLayout () tag) (fun tagLayout =>
            let sz := tagLayout.layout.size
            liftOptTag
              ((Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                nicheStart sz).mapError Miri.Interpreter.ScalarOps.scalarError)
              (fun _ =>
                let relative := BitVec.ofNat 128 (variantIdx - start)
                liftOptTag
                  ((Miri.Memory.Scalar.fromUInt
                    (Prov := Miri.Memory.Provenance) relative sz).mapError
                    Miri.Interpreter.ScalarOps.scalarError)
                  (fun _ =>
                    liftOptTag
                      ((sz.truncate (relative + nicheStart)).mapError
                        (fun e =>
                          Miri.Interpreter.StepError.invalidProgram
                            (toString e)))
                      (fun bits =>
                        liftOptTag
                          ((Miri.Memory.Scalar.fromUInt
                            (Prov := Miri.Memory.Provenance) bits sz).mapError
                            Miri.Interpreter.ScalarOps.scalarError)
                          (fun sc0 =>
                            liftOptTag
                              (sc0.toScalarInt.mapError
                                Miri.Interpreter.ScalarOps.scalarError)
                              (fun si => Pure.pure (some (si, field))))))))
        if decide (variantIdx ≥ HPow.hPow 2 32) ||
            decide (start ≥ HPow.hPow 2 32) ||
            decide (last ≥ HPow.hPow 2 32) then
          Bind.bind (throw (.invalidProgram "variant index exceeds u32")) jpU32
        else
          jpU32 ()
      if decide (variantIdx < start) || decide (variantIdx > last) then
        Bind.bind (throw (.invalidProgram "variant outside niche range"))
          jpRange
      else
        jpRange ()

private theorem runRvalue_tagForVariant_split (S : Type)
    (getL : S → List RefLocalState) (ety : EnumTy) (variantIdx : Nat)
    (rdest : RefDest) (s : S) :
    let h := refWriteDiscriminantHooks S getL (.enum ety) (some ety) variantIdx
    Miri.Interpreter.runRvalue
      (Miri.Interpreter.Discriminant.tagForVariant h () (h.destLayout rdest)
        variantIdx) s =
    Miri.Interpreter.runRvalue
      (if (refEnumLayoutData ety).isVariantUninhabited variantIdx then
        Bind.bind
          (throw (.undefinedBehavior
            (toString "UninhabitedEnumVariantWritten(" ++
              toString variantIdx ++ toString ")")))
          (fun (_ : Unit) => runTagForVariantInner S getL ety variantIdx)
       else
        runTagForVariantInner S getL ety variantIdx) s := rfl

private theorem match_writeDiscr_eq_runRvalue {α : Type}
    (m : Miri.Interpreter.RvalueM (List RefLocalState) Unit)
    (rlocals : List RefLocalState)
    (onOk onUb onErr : α) :
    (match m rlocals with
    | .error (.undefinedBehavior _) _
    | .error (.stack (.localExpectedLive _)) _ => onUb
    | .error _ _ => onErr
    | .ok () _ => onOk) =
    (match (Miri.Interpreter.runRvalue m rlocals).2 with
    | .error (.undefinedBehavior _)
    | .error (.stack (.localExpectedLive _)) => onUb
    | .error _ => onErr
    | .ok () => onOk) := by
  dsimp only [Miri.Interpreter.runRvalue]
  cases m rlocals with
  | ok u _ => cases u; rfl
  | error e _ =>
    cases e with
    | undefinedBehavior _ => rfl
    | stack se => cases se <;> rfl
    | _ => rfl

private theorem toMiriInteger_size_eq (w : IntWidth) :
    (toMiriInteger w).size = toMiriSize w := by
  cases w <;> rfl

private theorem runRvalue_liftOptTag_ok {S A : Type}
    (a : A)
    (k : A → Miri.Interpreter.RvalueM S (Option (ScalarInt × Nat)))
    (s : S) :
    Miri.Interpreter.runRvalue (liftOptTag (.ok a) k) s =
      Miri.Interpreter.runRvalue (k a) s := rfl

private theorem scalar_fromScalarInt_toBits_eq (w : IntWidth)
    (bits : BitVec 128) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).toBits (toMiriSize w) =
    .ok (truncateBits w bits) := by
  have h :
      (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
        (miriScalar w bits)).toBits (toMiriSize w) =
      match (miriScalar w bits).toBits (toMiriSize w) with
      | .ok v => .ok v
      | .error e => .error (.scalarInt e) := by
    cases w <;> rfl
  rw [h, miriScalar_toBits_eq]

private theorem scalar_fromScalarInt_toScalarInt_eq (si : ScalarInt) :
    (Miri.Memory.Scalar.fromScalarInt
      (Prov := Miri.Memory.Provenance) si).toScalarInt = .ok si := rfl

private theorem tagForVariant_admitted_inhabited
    (rlocals : List RefLocalState) (rdest : RefDest) (ety : EnumTy)
    (variantIdx : Nat)
    (h_adm : enumAdmitted ety = true)
    (h_inh : isVariantUninhabited ety variantIdx = false) :
    let h :=
      refWriteDiscriminantHooks (List RefLocalState) id (.enum ety) (some ety)
        variantIdx
    match ety.tagRepr with
    | .zeroSized =>
      Nat.beq variantIdx 0 = true ∧
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.Discriminant.tagForVariant h () (h.destLayout rdest)
          variantIdx) rlocals = (rlocals, .ok none)
    | .single v₀ =>
      Nat.beq variantIdx v₀ = true ∧
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.Discriminant.tagForVariant h () (h.destLayout rdest)
          variantIdx) rlocals = (rlocals, .ok none)
    | .scalar _ _ =>
      ∃ sc,
        (∀ nf, encodeRefEnumTagOp ety (.enumVal ety variantIdx nf) =
          .ok ⟨.immediate (.scalar (.fromScalarInt sc)),
            ⟨0, refEnumLayoutData ety⟩⟩) ∧
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.Discriminant.tagForVariant h () (h.destLayout rdest)
            variantIdx) rlocals = (rlocals, .ok (some (sc, 0)))
    | .niche _ _ _ _ _ untagged start last _ =>
      if Nat.beq variantIdx untagged then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.Discriminant.tagForVariant h () (h.destLayout rdest)
            variantIdx) rlocals = (rlocals, .ok none)
      else
        Nat.ble start variantIdx = true ∧
        Nat.ble variantIdx last = true ∧
        ∃ sc,
          (∀ nf, encodeRefEnumTagOp ety (.enumVal ety variantIdx nf) =
            .ok ⟨.immediate (.scalar (.fromScalarInt sc)),
              ⟨0, refEnumLayoutData ety⟩⟩) ∧
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.Discriminant.tagForVariant h ()
              (h.destLayout rdest) variantIdx) rlocals =
            (rlocals, .ok (some (sc, 0))) := by
  intro h
  have h_split := runRvalue_tagForVariant_split (List RefLocalState) id ety
    variantIdx rdest rlocals
  dsimp only at h_split
  have h_uninh_eq := refEnumLayoutData_isVariantUninhabited_eq h_adm variantIdx
  rw [h_inh] at h_uninh_eq
  rw [h_uninh_eq, ite_false_eq_true] at h_split
  have hv_blt : Nat.blt variantIdx ety.discriminants.length = true := by
    cases h_b : Nat.blt variantIdx ety.discriminants.length with
    | true => rfl
    | false =>
      dsimp only [isVariantUninhabited, fieldsForVariant?] at h_inh
      rw [h_b] at h_inh
      cases h_inh
  have hv_lt := nat_lt_of_blt_eq_true hv_blt
  cases h_tr : ety.tagRepr with
  | zeroSized =>
    have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
    rw [h_tr] at hc
    have h_len1 := Nat.eq_of_beq_eq_true (bool_and_left hc)
    have hv0 : Nat.beq variantIdx 0 = true := by
      rw [h_len1] at hv_lt
      cases variantIdx with
      | zero => rfl
      | succ k => cases Nat.lt_of_succ_lt_succ hv_lt
    refine ⟨hv0, ?_⟩
    rw [h_split]
    dsimp only [runTagForVariantInner, refEnumLayoutData]
    rw [h_tr]
    rfl
  | single v₀ =>
    have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
    rw [h_tr] at hc
    have h_oth := bool_and_right hc
    have h_or := otherVariantsUninhabited_at h_oth hv_lt
    rw [h_inh, Bool.or_false] at h_or
    refine ⟨h_or, ?_⟩
    rw [h_split]
    dsimp only [runTagForVariantInner, refEnumLayoutData]
    rw [h_tr]
    rfl
  | scalar tagW tagS =>
    let ⟨disc, h_disc⟩ := getElem?_some_of_lt ety.discriminants variantIdx hv_lt
    have hd_blt : Nat.blt disc (Nat.pow 2 ety.discrWidth.bitWidth) = true :=
      @list_all_of_getElem? Nat ety.discriminants _ variantIdx disc
        (enumAdmitted_discr_in_bounds h_adm) h_disc
    have hd_mod := nat_lt_of_blt_eq_true hd_blt
    have hd_u128 :=
      Nat.lt_of_lt_of_le hd_mod (intWidth_modulus_le_u128 ety.discrWidth)
    have hd_fits :
        (truncateBits ety.discrWidth (BitVec.ofNat 128 disc) ==
          BitVec.ofNat 128 disc) = true := by
      have h_eq : truncateBits ety.discrWidth (BitVec.ofNat 128 disc) =
          BitVec.ofNat 128 disc := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_truncateBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd_u128]
        exact Nat.mod_eq_of_lt hd_mod
      rw [h_eq]; exact beq_self_eq_true _
    have h_df := scalar_fromUInt_of_truncateBits_beq
      (P := Miri.Memory.Provenance) hd_fits
    let tBits :=
      truncateBits tagW (truncateBits ety.discrWidth (BitVec.ofNat 128 disc))
    have ht_fits : (truncateBits tagW tBits == tBits) = true := by
      dsimp only [tBits]; rw [truncateBits_idem]; exact beq_self_eq_true _
    have h_tf := scalar_fromUInt_of_truncateBits_beq
      (P := Miri.Memory.Provenance) ht_fits
    have h_dfv :
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.Discriminant.discriminantForVariant h () 0
            variantIdx) rlocals =
        (rlocals,
          .ok ⟨.scalar (.fromScalarInt
                (miriScalar ety.discrWidth (BitVec.ofNat 128 disc))),
              ⟨1, refScalarLayoutData ety.discrWidth ety.discrSigned⟩⟩) := by
      dsimp only [Miri.Interpreter.Discriminant.discriminantForVariant, h,
        refWriteDiscriminantHooks, Nat.beq, Miri.Interpreter.runRvalue,
        Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
      simp only [ite_true]
      rw [h_disc]
      have h_11 : ((1 : Nat) != 1) = false := rfl
      dsimp only
      rw [h_11, ite_false_eq_true]
      dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
      rw [refScalarLayoutData_size_eq, h_df]
      rfl
    have h_tag_sz :
        (Miri.ABI.Scalar.Union (value := .Int (toMiriInteger tagW) tagS)).size
          h.runtimeTarget = .ok (toMiriSize tagW) := by
      cases tagW <;> cases tagS <;> rfl
    have h_enc_sc : ∀ nf,
        encodeRefEnumTagOp ety (.enumVal ety variantIdx nf) =
          .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW tBits))),
            ⟨0, refEnumLayoutData ety⟩⟩ := by
      intro nf
      dsimp only [encodeRefEnumTagOp]
      rw [h_tr]
      dsimp only
      rw [EnumTy.beq_refl, hv_blt, Bool.true_and, ite_true_eq_true,
          h_disc]
      dsimp only
      rw [truncateFromUInt_eq_miriScalar]
      have hd_eq : truncateBits ety.discrWidth (BitVec.ofNat 128 disc) =
          BitVec.ofNat 128 disc := eq_of_beq hd_fits
      have h_sc_eq : miriScalar tagW (BitVec.ofNat 128 disc) =
          miriScalar tagW tBits := by
        dsimp only [tBits]
        rw [hd_eq]
        exact (miriScalar_truncateBits tagW (BitVec.ofNat 128 disc)).symm
      rw [h_sc_eq]
    refine ⟨miriScalar tagW tBits, h_enc_sc, ?_⟩
    rw [h_split]
    dsimp only [runTagForVariantInner, refEnumLayoutData]
    rw [h_tr]
    dsimp only
    rw [runRvalue_bind, h_dfv]
    dsimp only [Miri.Interpreter.Immediate.toScalar, Except.mapError]
    rw [runRvalue_liftOptTag_ok, refScalarLayoutData_size_eq,
        scalar_fromScalarInt_toBits_eq]
    dsimp only [Except.mapError]
    rw [runRvalue_liftOptTag_ok, h_tag_sz]
    dsimp only
    rw [runRvalue_bind, runRvalue_pure]
    dsimp only
    rw [size_truncate_eq]
    dsimp only [Except.mapError]
    rw [runRvalue_liftOptTag_ok]
    dsimp only [tBits] at h_tf
    rw [h_tf]
    dsimp only [Except.mapError]
    rw [runRvalue_liftOptTag_ok, scalar_fromScalarInt_toScalarInt_eq]
    dsimp only [Except.mapError]
    rw [runRvalue_liftOptTag_ok, runRvalue_pure]
  | niche tagW tagS vs ve nichePath untagged start last nicheStart =>
    dsimp only
    cases h_vu : Nat.beq variantIdx untagged with
    | true =>
      rw [ite_true_eq_true, h_split]
      dsimp only [runTagForVariantInner, refEnumLayoutData]
      rw [h_tr]
      dsimp only
      have h_eq : (variantIdx == untagged) = true :=
        (decide_eq_nat_beq variantIdx untagged).trans h_vu
      rw [h_eq]
      rfl
    | false =>
      rw [ite_false_eq_true]
      have hc := bool_and_right (enumAdmittedCore_of_enumAdmitted h_adm)
      rw [h_tr] at hc
      dsimp only at hc
      have h_dlen_lt : ety.discriminants.length < Nat.pow 2 32 :=
        nat_lt_of_blt_eq_true (enumAdmitted_discr_len_lt h_adm)
      have h_last_lt_d : last < ety.discriminants.length :=
        nat_lt_of_blt_eq_true
          (bool_and_right (bool_and_left (bool_and_left (bool_and_left
            (bool_and_left (bool_and_left (bool_and_left (bool_and_left
              (bool_and_left hc)))))))))
      have h_start_le_last : start ≤ last :=
        Nat.le_of_ble_eq_true
          (bool_and_right (bool_and_left (bool_and_left (bool_and_left
            (bool_and_left (bool_and_left (bool_and_left
              (bool_and_left hc))))))))
      have h_ns_fits : (truncateBits tagW nicheStart == nicheStart) = true :=
        bool_and_right (bool_and_left (bool_and_left (bool_and_left
          (bool_and_left hc))))
      have h_span_mod : last - start < (Nat.pow 2 tagW.bitWidth) :=
        nat_lt_of_blt_eq_true
          (bool_and_right (bool_and_left (bool_and_left (bool_and_left hc))))
      have h_oth_n := bool_and_right (bool_and_left hc)
      have h_at := otherVariantsValidForNiche_at h_oth_n hv_lt
      rw [h_vu, ite_false_eq_true, h_inh, ite_false_eq_true] at h_at
      have h_sv : Nat.ble start variantIdx = true :=
        bool_and_left (bool_and_left h_at)
      have h_vl : Nat.ble variantIdx last = true :=
        bool_and_right (bool_and_left h_at)
      have hv_ge := Nat.le_of_ble_eq_true h_sv
      have hv_le := Nat.le_of_ble_eq_true h_vl
      have h_last_u32 : last < HPow.hPow 2 32 := Nat.lt_trans h_last_lt_d h_dlen_lt
      have h_start_u32 : start < HPow.hPow 2 32 :=
        Nat.lt_of_le_of_lt h_start_le_last h_last_u32
      have hv_u32 : variantIdx < HPow.hPow 2 32 :=
        Nat.lt_of_le_of_lt hv_le h_last_u32
      have h_rng_false :
          (decide (variantIdx < start) || decide (variantIdx > last)) =
            false := by
        rw [decide_eq_false (Nat.not_lt_of_ge hv_ge),
            decide_eq_false (Nat.not_lt_of_ge hv_le)]
        rfl
      have h_u32_false :
          (decide (variantIdx ≥ HPow.hPow 2 32) ||
            decide (start ≥ HPow.hPow 2 32) ||
            decide (last ≥ HPow.hPow 2 32)) = false := by
        rw [decide_eq_false (Nat.not_le_of_gt hv_u32),
            decide_eq_false (Nat.not_le_of_gt h_start_u32),
            decide_eq_false (Nat.not_le_of_gt h_last_u32)]
        rfl
      have h_ns_ok := scalar_fromUInt_of_truncateBits_beq
        (P := Miri.Memory.Provenance) h_ns_fits
      let rel := BitVec.ofNat 128 (variantIdx - start)
      have hk_mod : variantIdx - start < (Nat.pow 2 tagW.bitWidth) :=
        Nat.lt_of_le_of_lt (Nat.sub_le_sub_right hv_le start) h_span_mod
      have hk_u128 :=
        Nat.lt_of_lt_of_le hk_mod (intWidth_modulus_le_u128 tagW)
      have h_rel_fits : (truncateBits tagW rel == rel) = true := by
        have h_eq : truncateBits tagW rel = rel := by
          apply BitVec.eq_of_toNat_eq
          dsimp only [rel]
          rw [toNat_truncateBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_u128]
          exact Nat.mod_eq_of_lt hk_mod
        rw [h_eq]; exact beq_self_eq_true _
      have h_rel_ok := scalar_fromUInt_of_truncateBits_beq
        (P := Miri.Memory.Provenance) h_rel_fits
      let tBits := truncateBits tagW (rel + nicheStart)
      have ht_fits : (truncateBits tagW tBits == tBits) = true := by
        dsimp only [tBits]; rw [truncateBits_idem]; exact beq_self_eq_true _
      have h_tf := scalar_fromUInt_of_truncateBits_beq
        (P := Miri.Memory.Provenance) ht_fits
      have h_enc_niche : ∀ nf,
          encodeRefEnumTagOp ety (.enumVal ety variantIdx nf) =
            .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW tBits))),
              ⟨0, refEnumLayoutData ety⟩⟩ := by
        intro nf
        dsimp only [encodeRefEnumTagOp]
        rw [h_tr]
        dsimp only
        rw [EnumTy.beq_refl, Bool.not_true, ite_false_eq_true,
            h_vu, ite_false_eq_true, h_sv, h_vl, Bool.true_and,
            ite_true_eq_true, truncateFromUInt_eq_miriScalar]
        have h_sc_eq : miriScalar tagW (rel + nicheStart) =
            miriScalar tagW tBits :=
          (miriScalar_truncateBits tagW (rel + nicheStart)).symm
        change Except.ok (Miri.Interpreter.OpTy.mk
            (.immediate (.scalar
              (.fromScalarInt (miriScalar tagW (rel + nicheStart)))))
            ⟨0, refEnumLayoutData ety⟩) = _
        rw [h_sc_eq]
      refine ⟨h_sv, h_vl, miriScalar tagW tBits, h_enc_niche, ?_⟩
      rw [h_split]
      dsimp only [runTagForVariantInner, refEnumLayoutData]
      rw [h_tr]
      dsimp only
      have h_eq : (variantIdx == untagged) = false :=
        (decide_eq_nat_beq variantIdx untagged).trans h_vu
      let nicheTag : Miri.ABI.Scalar :=
        .Initialized (value := .Int (toMiriInteger tagW) tagS)
          (validRange := ⟨vs, ve⟩)
      have h_tl :
          Miri.Interpreter.runRvalue
            (h.tagLayout () nicheTag) rlocals =
          (rlocals,
            .ok ⟨0, refBaseLayoutData (.Scalar nicheTag) (toMiriSize tagW)⟩) := by
        cases tagW <;> rfl
      rw [h_eq, ite_false_eq_true, h_rng_false, ite_false_eq_true,
          h_u32_false, ite_false_eq_true, runRvalue_bind, h_tl]
      dsimp only [refBaseLayoutData]
      rw [h_ns_ok]
      dsimp only [Except.mapError]
      rw [runRvalue_liftOptTag_ok]
      dsimp only [rel] at h_rel_ok
      rw [h_rel_ok]
      dsimp only [Except.mapError]
      rw [runRvalue_liftOptTag_ok, size_truncate_eq]
      dsimp only [Except.mapError]
      rw [runRvalue_liftOptTag_ok]
      dsimp only [tBits, rel] at h_tf
      rw [h_tf]
      dsimp only [Except.mapError]
      rw [runRvalue_liftOptTag_ok, scalar_fromScalarInt_toScalarInt_eq]
      dsimp only [Except.mapError]
      rw [runRvalue_liftOptTag_ok, runRvalue_pure]

private theorem refPrepSetDiscriminant_eq {bodyLocals : List MirTy}
    {slots : List LocalSlot} {dstId : LocalId}
    {mps : List Miri.MIR.ProjectionElem} {ps : List ProjectionElem}
    {localTy dstTy : MirTy} (ety : EnumTy) (variantIdx : Nat)
    (h_bty : MirSemantics.getElem? bodyLocals dstId = some localTy)
    (h_canon : CanonProjList mps ps) :
    refPrepSetDiscriminant (zipRefLocals bodyLocals slots)
        ⟨dstId, mps, .ty dstTy⟩ ety variantIdx =
      match MirSemantics.getElem? slots dstId with
      | none => .error .unsupported
      | some .dead => .error .undefined
      | some (.live root) =>
        match readPlaceSlotPath? (.ty localTy) root ps,
            fieldsForVariant? ety variantIdx with
        | some curSv, some varFields =>
          match setDiscrNextFields? ety variantIdx varFields curSv with
          | some nextFields => .ok (localTy, root, curSv, nextFields)
          | none => .error .unsupported
        | _, _ => .error .unsupported := by
  dsimp only [refPrepSetDiscriminant]
  cases h_sl : MirSemantics.getElem? slots dstId with
  | none =>
    rw [getElem?_zipRefLocals_none_right h_sl]
  | some slot =>
    rw [getElem?_zipRefLocals_some h_bty h_sl]
    cases slot with
    | dead => rfl
    | live root =>
      dsimp only
      rw [evalPlaceToOp_sized_live]
      dsimp only
      rw [miriImmToPayload?_roundtrip]
      dsimp only
      have h_rd := refReadPlaceSlotPath?_eq h_canon (.ty localTy) root
      dsimp only [placeTyToRefPlaceTy] at h_rd
      rw [h_rd, refFieldsForVariant?_eq]
      cases readPlaceSlotPath? (.ty localTy) root ps with
      | none => rfl
      | some curSv =>
        cases fieldsForVariant? ety variantIdx with
        | none => rfl
        | some varFields =>
          dsimp only [refSetDiscrNextFields?, setDiscrNextFields?]
          rw [refUninitSlotVals_eq]
          cases curSv <;> rfl

private noncomputable def refCommitSetDiscrOpt (rlocals : List RefLocalState)
    (slot : LocalSlot) (dstId : LocalId) (localTy : MirTy)
    (optRoot' : Option SlotVal) : Except FaultKind (List RefLocalState) :=
  match optRoot' with
  | none => .error .unsupported
  | some root' =>
    let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
    match Miri.Interpreter.placeWriteLocalImmediate
        EStateM.get EStateM.set (pure true)
        (fun _ _ => pure ()) (fun _ _ => pure ())
        0 refSizedLocalLayout (payloadToMiriImmediate root') frame₀ with
    | .ok () frame₁ =>
      match frame₁.getLocal 0,
          MirSemantics.setElem? rlocals dstId ⟨.live root', some localTy⟩ with
      | .ok ⟨.live (.immediate _), _⟩, some rlocals' => .ok rlocals'
      | .ok ⟨.live (.immediate _), _⟩, none => .error .unsupported
      | _, _ => .error .undefined
    | .error _ _ => .error .undefined

private theorem evalSetDiscriminantResolved_live_eq (localTy : MirTy)
    (slots : List LocalSlot) (dstId : LocalId) (ps : List ProjectionElem)
    (ety : EnumTy) (variantIdx : Nat) (root : SlotVal)
    (h_adm : enumAdmitted ety = true)
    (h_inh : isVariantUninhabited ety variantIdx = false)
    (h_sl : MirSemantics.getElem? slots dstId = some (.live root)) :
    evalSetDiscriminantResolved localTy slots ⟨dstId, ps⟩ (.enum ety)
      variantIdx =
    match readPlaceSlotPath? (.ty localTy) root ps,
        fieldsForVariant? ety variantIdx with
    | some curSv, some varFields =>
      match setDiscrNextFields? ety variantIdx varFields curSv with
      | none => .error .unsupported
      | some nextFields =>
        let tagCheck : Except FaultKind Unit :=
          match ety.tagRepr with
          | .zeroSized =>
            if Nat.beq variantIdx 0 then .ok () else .error .undefined
          | .single v₀ =>
            if Nat.beq variantIdx v₀ then .ok () else .error .undefined
          | .scalar _ _ => .ok ()
          | .niche _ _ _ _ _ untagged start last _ =>
            if Nat.beq variantIdx untagged then
              match evalReadDiscriminantVariant ety curSv with
              | .error k => .error k
              | .ok actual =>
                if Nat.beq actual variantIdx then .ok ()
                else .error .undefined
            else if Nat.ble start variantIdx && Nat.ble variantIdx last then
              .ok ()
            else
              .error .unsupported
        match tagCheck with
        | .error k => .error k
        | .ok () =>
          match writePlaceSlotPath? (.ty localTy) root ps
              (.enumVal ety variantIdx nextFields) with
          | none => .error .unsupported
          | some root' =>
            match MirSemantics.setElem? slots dstId (.live root') with
            | some locals' => .ok locals'
            | none => .error .unsupported
    | _, _ => .error .unsupported := by
  dsimp only [evalSetDiscriminantResolved]
  rw [h_adm, Bool.not_true, ite_false_eq_true, h_inh, ite_false_eq_true, h_sl]
  dsimp only
  cases readPlaceSlotPath? (.ty localTy) root ps with
  | none => rfl
  | some curSv =>
    cases fieldsForVariant? ety variantIdx with
    | none => rfl
    | some varFields =>
      cases curSv <;> rfl

private theorem evalRefSetDiscriminant_nonEnum_live {bodyLocals : List MirTy}
    {slots : List LocalSlot} {dstId : LocalId}
    {mps : List Miri.MIR.ProjectionElem} {ps : List ProjectionElem}
    {localTy dstTy : MirTy} (variantIdx : Nat) (root curSv : SlotVal)
    (h_bty : MirSemantics.getElem? bodyLocals dstId = some localTy)
    (h_sl : MirSemantics.getElem? slots dstId = some (.live root))
    (h_canon : CanonProjList mps ps)
    (h_rp : readPlaceSlotPath? (.ty localTy) root ps = some curSv) :
    let rlocals := zipRefLocals bodyLocals slots
    let rdest : RefDest := ⟨dstId, mps, .ty dstTy⟩
    let h_hooks :=
      refWriteDiscriminantHooks (List RefLocalState) id dstTy none variantIdx
    (match Miri.Interpreter.Discriminant.writeDiscriminant h_hooks ()
        variantIdx rdest rlocals with
      | .error (.undefinedBehavior _) _
      | .error (.stack (.localExpectedLive _)) _ =>
        Except.error FaultKind.undefined
      | .error _ _ => Except.error FaultKind.unsupported
      | .ok () _ => Except.ok rlocals) =
    mapSlotsRes bodyLocals
      (if isTypeUninhabited dstTy || !Nat.beq variantIdx 0 then
        Except.error FaultKind.undefined
      else
        Except.ok slots) := by
  intro rlocals rdest h_hooks
  rw [match_writeDiscr_eq_runRvalue
      (Miri.Interpreter.Discriminant.writeDiscriminant h_hooks ()
        variantIdx rdest) rlocals]
  dsimp only [Miri.Interpreter.Discriminant.writeDiscriminant]
  rw [runRvalue_bind]
  have h_uninh_eq :
      (h_hooks.destLayout rdest).layout.isVariantUninhabited variantIdx =
        (!Nat.beq variantIdx 0 || isTypeUninhabited dstTy) := by
    dsimp only [h_hooks, refWriteDiscriminantHooks,
      LayoutData.isVariantUninhabited]
    rw [refIsTypeUninhabited_eq]
    change (!(decide (variantIdx = 0)) || isTypeUninhabited dstTy) = _
    rw [decide_eq_nat_beq]
  have h_tfv :
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.Discriminant.tagForVariant h_hooks ()
          (h_hooks.destLayout rdest) variantIdx) rlocals =
      if !Nat.beq variantIdx 0 || isTypeUninhabited dstTy then
        (rlocals, .error (.undefinedBehavior
          (toString "UninhabitedEnumVariantWritten(" ++
            toString variantIdx ++ toString ")")))
      else
        (rlocals, .ok none) := by
    dsimp only [Miri.Interpreter.Discriminant.tagForVariant,
      Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
      EStateM.pure]
    rw [h_uninh_eq]
    cases (!Nat.beq variantIdx 0 || isTypeUninhabited dstTy) with
    | true => rfl
    | false => rfl
  rw [h_tfv]
  cases h_u : isTypeUninhabited dstTy with
  | true =>
    simp only [Bool.or_true, Bool.true_or, ite_true]
    rfl
  | false =>
    cases h_v0 : Nat.beq variantIdx 0 with
    | false =>
      simp only [Bool.not_false, Bool.true_or, Bool.or_true, ite_true]
      rfl
    | true =>
      have hv_eq : variantIdx = 0 := Nat.eq_of_beq_eq_true h_v0
      subst hv_eq
      simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
      rw [runRvalue_bind]
      have h_rd_slot := refReadPlaceSlotPath?_eq h_canon (.ty localTy) root
      dsimp only [placeTyToRefPlaceTy] at h_rd_slot
      have h_toOp :
          Miri.Interpreter.runRvalue (h_hooks.toOp () rdest) rlocals =
            (rlocals, .ok ⟨.immediate .uninit, h_hooks.destLayout rdest⟩) := by
        dsimp only [Miri.Interpreter.runRvalue, h_hooks,
          refWriteDiscriminantHooks, id, rlocals, rdest]
        rw [getElem?_zipRefLocals_some h_bty h_sl]
        dsimp only
        rw [h_rd_slot, h_rp]
      rw [h_toOp]
      dsimp only
      rw [runRvalue_bind]
      have h_rd :
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.Discriminant.readDiscriminant h_hooks ()
              ⟨.immediate .uninit, h_hooks.destLayout rdest⟩) rlocals =
            (rlocals, .ok 0) := by
        dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
          Miri.Interpreter.runRvalue, h_hooks, refWriteDiscriminantHooks,
          LayoutData.isUninhabited, LayoutData.isVariantUninhabited,
          Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
        rw [refIsTypeUninhabited_eq, h_u]
        rfl
      rw [h_rd]
      rfl

theorem evalRefSetDiscriminant_eq {bodyLocals : List MirTy}
    {slots : List LocalSlot} {dstId : LocalId}
    {mps : List Miri.MIR.ProjectionElem} {ps : List ProjectionElem}
    {localTy dstTy : MirTy} (variantIdx : Nat)
    (h_bty : MirSemantics.getElem? bodyLocals dstId = some localTy)
    (h_canon : CanonProjList mps ps) :
    evalRefSetDiscriminant (zipRefLocals bodyLocals slots)
        ⟨dstId, mps, .ty dstTy⟩ variantIdx =
      mapSlotsRes bodyLocals
        (evalSetDiscriminantResolved localTy slots ⟨dstId, ps⟩ dstTy
          variantIdx) := by
  unfold evalRefSetDiscriminant
  cases h_sl : MirSemantics.getElem? slots dstId with
  | none =>
    rw [getElem?_zipRefLocals_none_right h_sl]
    dsimp only [evalSetDiscriminantResolved]
    rw [h_sl]
    cases dstTy with
    | enum ety =>
      dsimp only
      cases enumAdmitted ety with
      | false => rfl
      | true =>
        cases isVariantUninhabited ety variantIdx <;> rfl
    | bool | int _ _ | unit | never | adtStruct _ | tuple _ | array _ _
    | ref _ _ | rawPtr _ _ | unsupported => rfl
  | some slot =>
    rw [getElem?_zipRefLocals_some h_bty h_sl]
    cases dstTy with
    | bool | int _ _ | unit | never | adtStruct _ | tuple _ | array _ _
    | ref _ _ | rawPtr _ _ | unsupported =>
      dsimp only [evalSetDiscriminantResolved]
      rw [h_sl]
      cases slot with
      | dead => rfl
      | live root =>
        dsimp only
        have h_rd := refReadPlaceSlotPath?_eq h_canon (.ty localTy) root
        dsimp only [placeTyToRefPlaceTy] at h_rd
        rw [h_rd]
        cases h_rp : readPlaceSlotPath? (.ty localTy) root ps with
        | none => rfl
        | some curSv =>
          exact evalRefSetDiscriminant_nonEnum_live variantIdx root curSv
            h_bty h_sl h_canon h_rp
    | enum ety =>
      dsimp only
      rw [refEnumAdmitted_eq]
      cases h_adm : enumAdmitted ety with
      | false =>
        dsimp only [evalSetDiscriminantResolved]
        rw [h_adm]
        rfl
      | true =>
        rw [ite_true_eq_true]
        dsimp only
        let rlocals := zipRefLocals bodyLocals slots
        let rdest : RefDest := ⟨dstId, mps, .ty (.enum ety)⟩
        let h_hooks :=
          refWriteDiscriminantHooks (List RefLocalState) id (.enum ety)
            (some ety) variantIdx
        change (match Miri.Interpreter.Discriminant.writeDiscriminant h_hooks ()
              variantIdx rdest rlocals with
            | .error (.undefinedBehavior _) _
            | .error (.stack (.localExpectedLive _)) _ =>
              Except.error FaultKind.undefined
            | .error _ _ => Except.error FaultKind.unsupported
            | .ok () _ =>
              match refPrepSetDiscriminant rlocals rdest ety variantIdx with
              | .error k => Except.error k
              | .ok (locTy, root, _, nextFields) =>
                refCommitSetDiscrOpt rlocals slot dstId locTy
                  (refWritePlaceSlotPath? (.ty locTy) root mps
                    (.enumVal ety variantIdx nextFields))) = _
        rw [match_writeDiscr_eq_runRvalue
            (Miri.Interpreter.Discriminant.writeDiscriminant h_hooks ()
              variantIdx rdest) rlocals]
        dsimp only [Miri.Interpreter.Discriminant.writeDiscriminant]
        rw [runRvalue_bind]
        cases h_uninh : isVariantUninhabited ety variantIdx with
        | true =>
          have h_split := runRvalue_tagForVariant_split (List RefLocalState) id
            ety variantIdx rdest rlocals
          dsimp only at h_split
          rw [refEnumLayoutData_isVariantUninhabited_eq h_adm variantIdx,
              h_uninh, ite_true_eq_true] at h_split
          rw [h_split]
          dsimp only [evalSetDiscriminantResolved]
          rw [h_adm, Bool.not_true, ite_false_eq_true, h_uninh,
              ite_true_eq_true, h_sl]
          rfl
        | false =>
          have h_tfv := tagForVariant_admitted_inhabited rlocals rdest ety
            variantIdx h_adm h_uninh
          dsimp only at h_tfv
          have h_prep := @refPrepSetDiscriminant_eq bodyLocals slots dstId mps
            ps localTy (.enum ety) ety variantIdx h_bty h_canon
          rw [h_sl] at h_prep
          have h_commit : ∀ (root : SlotVal) (nextFields : List SlotVal),
              slot = .live root →
              refCommitSetDiscrOpt rlocals slot dstId localTy
                (refWritePlaceSlotPath? (.ty localTy) root mps
                  (.enumVal ety variantIdx nextFields)) =
              mapSlotsRes bodyLocals
                (match writePlaceSlotPath? (.ty localTy) root ps
                      (.enumVal ety variantIdx nextFields) with
                 | none => .error .unsupported
                 | some root' =>
                   match MirSemantics.setElem? slots dstId (.live root') with
                   | some locals' => .ok locals'
                   | none => .error .unsupported) := by
            intro root nextFields h_slot_eq
            subst h_slot_eq
            have h_wr := refWritePlaceSlotPath?_eq h_canon (.ty localTy) root
              (.enumVal ety variantIdx nextFields)
            dsimp only [placeTyToRefPlaceTy] at h_wr
            rw [h_wr]
            cases writePlaceSlotPath? (.ty localTy) root ps
                (.enumVal ety variantIdx nextFields) with
            | none => rfl
            | some root' =>
              dsimp only [rlocals]
              cases h_set :
                  MirSemantics.setElem? slots dstId (.live root') with
              | none =>
                dsimp only [refCommitSetDiscrOpt]
                rw [setElem?_zipRefLocals_none h_set]
                rfl
              | some slots' =>
                dsimp only [refCommitSetDiscrOpt]
                rw [setElem?_zipRefLocals_some h_bty h_set]
                rfl
          cases slot with
          | dead =>
            dsimp only [evalSetDiscriminantResolved]
            rw [h_adm, Bool.not_true, ite_false_eq_true, h_uninh,
                ite_false_eq_true, h_sl]
            first | dsimp only at h_prep | change _
            first | dsimp only | change _
            cases h_tr : ety.tagRepr with
            | zeroSized =>
              rw [h_tr] at h_tfv
              let ⟨_, h_tv⟩ := h_tfv
              rw [h_tv]
              dsimp only
              rw [runRvalue_bind]
              have h_toOp :
                  Miri.Interpreter.runRvalue (h_hooks.toOp () rdest) rlocals =
                    (rlocals, .error (faultToStepError .undefined)) := by
                dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                  refWriteDiscriminantHooks, id]
                rw [h_tr, h_prep]
              rw [h_toOp]
              rfl
            | single v₀ =>
              rw [h_tr] at h_tfv
              let ⟨_, h_tv⟩ := h_tfv
              rw [h_tv]
              dsimp only
              rw [runRvalue_bind]
              have h_toOp :
                  Miri.Interpreter.runRvalue (h_hooks.toOp () rdest) rlocals =
                    (rlocals, .error (faultToStepError .undefined)) := by
                dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                  refWriteDiscriminantHooks, id]
                rw [h_tr, h_prep]
              rw [h_toOp]
              rfl
            | scalar tagW tagS =>
              rw [h_tr] at h_tfv
              let ⟨sc, _, h_tv⟩ := h_tfv
              rw [h_tv]
              dsimp only
              rw [runRvalue_bind]
              have h_pw :
                  Miri.Interpreter.runRvalue
                    (h_hooks.projectWrite () rdest 0) rlocals =
                    (rlocals, .ok rdest) := rfl
              rw [h_pw]
              dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                refWriteDiscriminantHooks, id]
              rw [h_prep]
              rfl
            | niche tagW tagS vs ve nichePath untagged start last nicheStart =>
              rw [h_tr] at h_tfv
              dsimp only at h_tfv
              cases h_vu : Nat.beq variantIdx untagged with
              | false =>
                rw [h_vu, ite_false_eq_true] at h_tfv
                let ⟨_, _, sc, _, h_tv⟩ := h_tfv
                rw [h_tv]
                dsimp only
                rw [runRvalue_bind]
                have h_pw :
                    Miri.Interpreter.runRvalue
                      (h_hooks.projectWrite () rdest 0) rlocals =
                      (rlocals, .ok rdest) := rfl
                rw [h_pw]
                dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                  refWriteDiscriminantHooks, id]
                rw [h_prep]
                rfl
              | true =>
                rw [h_vu, ite_true_eq_true] at h_tfv
                rw [h_tfv]
                dsimp only
                rw [runRvalue_bind]
                have h_toOp :
                    Miri.Interpreter.runRvalue (h_hooks.toOp () rdest)
                      rlocals =
                    (rlocals, .error (faultToStepError .undefined)) := by
                  dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                    refWriteDiscriminantHooks, id]
                  rw [h_tr, h_prep]
                rw [h_toOp]
                rfl
          | live root =>
            rw [evalSetDiscriminantResolved_live_eq localTy slots dstId ps ety
                variantIdx root h_adm h_uninh h_sl]
            dsimp only at h_prep
            cases h_tr : ety.tagRepr with
            | zeroSized =>
              dsimp only
              rw [h_tr] at h_tfv
              let ⟨hv0, h_tv⟩ := h_tfv
              rw [h_tv, hv0, ite_true_eq_true]
              dsimp only
              rw [runRvalue_bind]
              have h_toOp :
                  Miri.Interpreter.runRvalue (h_hooks.toOp () rdest) rlocals =
                    match refPrepSetDiscriminant rlocals rdest ety
                        variantIdx with
                    | .error k => (rlocals, .error (faultToStepError k))
                    | .ok _ =>
                      (rlocals,
                        .ok ⟨.immediate .uninit,
                          ⟨0, refEnumLayoutData ety⟩⟩) := by
                dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                  refWriteDiscriminantHooks, id]
                rw [h_tr]
                cases refPrepSetDiscriminant rlocals rdest ety variantIdx <;>
                  rfl
              rw [h_toOp, h_prep]
              cases readPlaceSlotPath? (.ty localTy) root ps with
              | none => rfl
              | some curSv =>
                cases fieldsForVariant? ety variantIdx with
                | none => rfl
                | some varFields =>
                  dsimp only
                  cases h_nf :
                      setDiscrNextFields? ety variantIdx varFields curSv with
                  | none => rfl
                  | some nextFields =>
                    dsimp only
                    rw [runRvalue_bind]
                    have h_rd :
                        Miri.Interpreter.runRvalue
                          (Miri.Interpreter.Discriminant.readDiscriminant
                            h_hooks ()
                            ⟨.immediate .uninit,
                              ⟨0, refEnumLayoutData ety⟩⟩) rlocals =
                        (rlocals, .ok 0) := by
                      dsimp only [Miri.Interpreter.runRvalue]
                      rw [readDiscriminant_eq_refDiscriminantHooks ety _
                          (refWriteDiscriminantHooks_spec _ _ ety variantIdx)]
                      dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
                        refDiscriminantHooks, refEnumLayoutData,
                        LayoutData.isUninhabited, Bind.bind, Pure.pure,
                        EStateM.bind, EStateM.pure]
                      rw [h_tr]
                      dsimp only
                      rw [refIsTypeUninhabited_eq,
                          isTypeUninhabited_zeroSized_eq_false h_adm h_tr]
                      rfl
                    rw [h_rd]
                    dsimp only
                    have h_0v : ((0 : Nat) != variantIdx) = false := by
                      rw [Nat.eq_of_beq_eq_true hv0]; rfl
                    rw [h_0v, ite_false_eq_true]
                    dsimp only [Miri.Interpreter.runRvalue, Pure.pure,
                      EStateM.pure]
                    exact h_commit root nextFields rfl
            | single v₀ =>
              dsimp only
              rw [h_tr] at h_tfv
              let ⟨hvv₀, h_tv⟩ := h_tfv
              rw [h_tv, hvv₀, ite_true_eq_true]
              dsimp only
              rw [runRvalue_bind]
              have h_toOp :
                  Miri.Interpreter.runRvalue (h_hooks.toOp () rdest) rlocals =
                    match refPrepSetDiscriminant rlocals rdest ety
                        variantIdx with
                    | .error k => (rlocals, .error (faultToStepError k))
                    | .ok _ =>
                      (rlocals,
                        .ok ⟨.immediate .uninit,
                          ⟨0, refEnumLayoutData ety⟩⟩) := by
                dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                  refWriteDiscriminantHooks, id]
                rw [h_tr]
                cases refPrepSetDiscriminant rlocals rdest ety variantIdx <;>
                  rfl
              rw [h_toOp, h_prep]
              cases readPlaceSlotPath? (.ty localTy) root ps with
              | none => rfl
              | some curSv =>
                cases fieldsForVariant? ety variantIdx with
                | none => rfl
                | some varFields =>
                  dsimp only
                  cases h_nf :
                      setDiscrNextFields? ety variantIdx varFields curSv with
                  | none => rfl
                  | some nextFields =>
                    dsimp only
                    rw [runRvalue_bind]
                    have hv_eq := Nat.eq_of_beq_eq_true hvv₀
                    have h_rd :
                        Miri.Interpreter.runRvalue
                          (Miri.Interpreter.Discriminant.readDiscriminant
                            h_hooks ()
                            ⟨.immediate .uninit,
                              ⟨0, refEnumLayoutData ety⟩⟩) rlocals =
                        (rlocals, .ok v₀) := by
                      dsimp only [Miri.Interpreter.runRvalue]
                      rw [readDiscriminant_eq_refDiscriminantHooks ety _
                          (refWriteDiscriminantHooks_spec _ _ ety variantIdx)]
                      dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
                        refDiscriminantHooks, refEnumLayoutData,
                        LayoutData.isUninhabited, Bind.bind, Pure.pure,
                        EStateM.bind, EStateM.pure]
                      rw [h_tr]
                      dsimp only
                      rw [refIsTypeUninhabited_eq,
                          isTypeUninhabited_single_eq h_adm h_tr,
                          ← hv_eq, h_uninh]
                      rfl
                    rw [h_rd]
                    dsimp only
                    have h_bne : (v₀ != variantIdx) = false := by
                      rw [← hv_eq]
                      change (!(variantIdx == variantIdx)) = false
                      rw [beq_self_eq_true]; rfl
                    rw [h_bne, ite_false_eq_true]
                    dsimp only [Miri.Interpreter.runRvalue, Pure.pure,
                      EStateM.pure]
                    exact h_commit root nextFields rfl
            | scalar tagW tagS =>
              dsimp only
              rw [h_tr] at h_tfv
              let ⟨sc, h_enc, h_tv⟩ := h_tfv
              rw [h_tv]
              dsimp only
              rw [runRvalue_bind]
              have h_pw :
                  Miri.Interpreter.runRvalue
                    (h_hooks.projectWrite () rdest 0) rlocals =
                    (rlocals, .ok rdest) := rfl
              rw [h_pw]
              dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                refWriteDiscriminantHooks, id]
              rw [h_prep]
              cases readPlaceSlotPath? (.ty localTy) root ps with
              | none => rfl
              | some curSv =>
                cases fieldsForVariant? ety variantIdx with
                | none => rfl
                | some varFields =>
                  dsimp only
                  cases h_nf :
                      setDiscrNextFields? ety variantIdx varFields curSv with
                  | none => rfl
                  | some nextFields =>
                    dsimp only
                    rw [h_enc nextFields]
                    dsimp only [Miri.Memory.Scalar.tryToScalarInt,
                      Miri.Memory.Scalar.fromScalarInt, Pure.pure, Except.pure]
                    rw [beq_self_eq_true, ite_true_eq_true]
                    exact h_commit root nextFields rfl
            | niche tagW tagS vs ve nichePath untagged start last nicheStart =>
              dsimp only
              rw [h_tr] at h_tfv
              dsimp only at h_tfv
              cases h_vu : Nat.beq variantIdx untagged with
              | false =>
                rw [h_vu, ite_false_eq_true] at h_tfv
                let ⟨h_sv, h_vl, sc, h_enc, h_tv⟩ := h_tfv
                simp only [Bool.false_eq_true, ite_false]
                rw [h_tv, h_sv, h_vl, Bool.true_and, ite_true_eq_true]
                dsimp only
                rw [runRvalue_bind]
                have h_pw :
                    Miri.Interpreter.runRvalue
                      (h_hooks.projectWrite () rdest 0) rlocals =
                      (rlocals, .ok rdest) := rfl
                rw [h_pw]
                dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                  refWriteDiscriminantHooks, id]
                rw [h_prep]
                cases readPlaceSlotPath? (.ty localTy) root ps with
                | none => rfl
                | some curSv =>
                  cases fieldsForVariant? ety variantIdx with
                  | none => rfl
                  | some varFields =>
                    dsimp only
                    cases h_nf :
                        setDiscrNextFields? ety variantIdx varFields curSv with
                    | none => rfl
                    | some nextFields =>
                      dsimp only
                      rw [h_enc nextFields]
                      dsimp only [Miri.Memory.Scalar.tryToScalarInt,
                        Miri.Memory.Scalar.fromScalarInt, Pure.pure,
                        Except.pure]
                      rw [beq_self_eq_true, ite_true_eq_true]
                      exact h_commit root nextFields rfl
              | true =>
                rw [h_vu, ite_true_eq_true] at h_tfv
                simp only [ite_true]
                rw [h_tfv]
                dsimp only
                rw [runRvalue_bind]
                have h_toOp :
                    Miri.Interpreter.runRvalue (h_hooks.toOp () rdest)
                      rlocals =
                      match refPrepSetDiscriminant rlocals rdest ety
                          variantIdx with
                      | .error k => (rlocals, .error (faultToStepError k))
                      | .ok (_, _, curSv, _) =>
                        match encodeRefEnumTagOp ety curSv with
                        | .ok op => (rlocals, .ok op)
                        | .error err => (rlocals, .error err) := by
                  dsimp only [Miri.Interpreter.runRvalue, h_hooks,
                    refWriteDiscriminantHooks, id]
                  rw [h_tr]
                  cases refPrepSetDiscriminant rlocals rdest ety variantIdx with
                  | error _ => rfl
                  | ok q =>
                    let ⟨_, _, curSv, _⟩ := q
                    dsimp only
                    cases encodeRefEnumTagOp ety curSv <;> rfl
                rw [h_toOp, h_prep]
                cases readPlaceSlotPath? (.ty localTy) root ps with
                | none => rfl
                | some curSv =>
                  cases fieldsForVariant? ety variantIdx with
                  | none => rfl
                  | some varFields =>
                    dsimp only
                    cases h_nf :
                        setDiscrNextFields? ety variantIdx varFields curSv with
                    | none => rfl
                    | some nextFields =>
                      dsimp only
                      have h_st := readDiscriminant_encodeRefEnumTagOp_stateless
                        ety curSv rlocals h_hooks
                        (refWriteDiscriminantHooks_spec _ _ ety variantIdx)
                        h_adm
                      dsimp only at h_st
                      cases h_enc : encodeRefEnumTagOp ety curSv with
                      | error err =>
                        rw [h_enc] at h_st
                        first | dsimp only [Miri.Interpreter.runRvalue, throw,
                          throwThe, MonadExceptOf.throw, EStateM.throw,
                          mapStepExcept] at h_st | change _
                        first | dsimp only [Miri.Interpreter.runRvalue, throw,
                          throwThe, MonadExceptOf.throw, EStateM.throw,
                          mapStepExcept] | change _
                        rw [← h_st.2]
                        cases err with
                        | undefinedBehavior _ => rfl
                        | stack se => cases se <;> rfl
                        | _ => rfl
                      | ok op =>
                        rw [h_enc] at h_st
                        first | dsimp only at h_st | change _
                        first | dsimp only | change _
                        rw [runRvalue_bind]
                        let ⟨h_st1, h_st2⟩ := h_st
                        cases h_ra :
                            Miri.Interpreter.runRvalue
                              (Miri.Interpreter.Discriminant.readDiscriminant
                                h_hooks () op) rlocals with
                        | mk s' resAct =>
                          rw [h_ra] at h_st1 h_st2
                          dsimp only at h_st1 h_st2
                          subst h_st1
                          cases resAct with
                          | error err =>
                            dsimp only [mapStepExcept] at h_st2
                            rw [← h_st2]
                            cases err with
                            | undefinedBehavior _ => rfl
                            | stack se => cases se <;> rfl
                            | _ => rfl
                          | ok actual =>
                            dsimp only [mapStepExcept] at h_st2
                            rw [← h_st2]
                            dsimp only
                            have h_bne :
                                (actual != variantIdx) =
                                  !Nat.beq actual variantIdx := by
                              cases h_b : Nat.beq actual variantIdx with
                              | true =>
                                rw [Nat.eq_of_beq_eq_true h_b]
                                exact bne_self_eq_false variantIdx
                              | false =>
                                refine bne_iff_ne.2 (fun he => ?_)
                                subst he
                                rw [Nat.beq_refl] at h_b
                                cases h_b
                            rw [h_bne]
                            cases Nat.beq actual variantIdx with
                            | false =>
                              simp only [Bool.not_false, Bool.false_eq_true,
                                ite_true, ite_false]
                              rfl
                            | true =>
                              simp only [Bool.not_true, Bool.false_eq_true,
                                ite_false, ite_true]
                              dsimp only [Miri.Interpreter.runRvalue, Pure.pure,
                                EStateM.pure]
                              exact h_commit root nextFields rfl

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
    | unit | structVal _ _ | enumVal _ _ _ | ptr _ | tuple _ | array _ _
    | bytes _ => rfl
  | bool | unit | never | adtStruct _ | enum _ | tuple _ | array _ _ | ref _ _
  | rawPtr _ _ | unsupported => rfl

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
    | scalar _ | unit | structVal _ _ | enumVal _ _ _ | tuple _ | array _ _
    | ptr _ | bytes _ => rfl

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
          first | dsimp only [evalSaturatingOp,
            IntegerArithmeticIntrinsic.saturatingArith, op] at h_ovf_case | change _
          first | dsimp only [evalSaturatingOp,
            IntegerArithmeticIntrinsic.saturatingArith, op] | change _
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
          first | dsimp only [evalSaturatingOp,
            IntegerArithmeticIntrinsic.saturatingArith, op] at h_ovf_case | change _
          first | dsimp only [evalSaturatingOp,
            IntegerArithmeticIntrinsic.saturatingArith, op] | change _
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

theorem refReadBuiltinArgs_eq (builtin : CoreBuiltin)
    (pairs : List (MirTy × SlotVal)) :
    refReadBuiltinArgs builtin pairs = readBuiltinArgs builtin pairs := by
  cases builtin with
  | fromLeBytes => rfl
  | wrappingAdd | wrappingSub | wrappingMul | wrappingShl | wrappingShr
  | overflowingAdd | overflowingSub | overflowingMul
  | saturatingAdd | saturatingSub
  | checkedAdd | checkedSub | checkedMul
  | leadingZeros | trailingZeros | isMultipleOf
  | toLeBytes | cmpMin | cmpMax =>
    exact refReadPrimitiveArgs_eq pairs

theorem refIsOptionEnumForTy_eq (ety : EnumTy) (innerTy : MirTy) :
    refIsOptionEnumForTy ety innerTy = isOptionEnumForTy ety innerTy := by
  dsimp only [refIsOptionEnumForTy, isOptionEnumForTy]
  rw [refEnumAdmitted_eq, refFieldsForVariant?_eq, refFieldsForVariant?_eq]
  cases fieldsForVariant? ety 0 with
  | none => rfl
  | some f0 =>
    cases f0 with
    | cons _ _ => rfl
    | nil =>
      cases fieldsForVariant? ety 1 with
      | none => rfl
      | some f1 =>
        cases f1 with
        | nil => rfl
        | cons fTy rest => cases rest <;> rfl

theorem evalRefCheckedArithOp_eq (op : BinOp) (dstTy : MirTy)
    (l r : ScalarVal) :
    evalRefCheckedArithOp (toMiriBinOp op) dstTy l r =
      evalCheckedArithOp op dstTy l r := by
  cases dstTy with
  | enum ety =>
    dsimp only [evalRefCheckedArithOp, evalCheckedArithOp]
    rw [refIsOptionEnumForTy_eq]
    cases isOptionEnumForTy ety (.int l.width l.signed) with
    | false => rfl
    | true =>
      rw [Bool.not_true, ite_false_eq_true, ite_false_eq_true]
      have h_bin := evalRefBinOp_eq op (.scalar l) (.scalar r)
      dsimp only [evalRefBinOp] at h_bin
      rw [h_bin]
      cases evalBinOp op (.scalar l) (.scalar r) with
      | error _ => rfl
      | ok resVal =>
        cases resVal with
        | tuple fs =>
          cases fs with
          | nil => rfl
          | cons f0 fs1 =>
            cases f0 with
            | scalar wrapped =>
              cases fs1 with
              | nil => rfl
              | cons f1 fs2 =>
                cases f1 with
                | bool ovf =>
                  cases ovf <;> (
                    cases fs2 with
                    | cons _ _ => rfl
                    | nil =>
                      dsimp only
                      rw [checkRefVal_eq])
                | _ => rfl
            | _ => rfl
        | _ => rfl
  | _ => rfl

private theorem u8_ofNat_bv8_toNat (b : BitVec 8) :
    (UInt8.ofNat b.toNat).toNat = b.toNat := by
  change (BitVec.ofNat 8 b.toNat).toNat = b.toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt b.isLt

theorem refValsToUInt8List?_eq (elems : List Val) :
    refValsToUInt8List? elems =
      (valsToU8Bytes? elems).map (List.map (fun b => UInt8.ofNat b.toNat)) := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
    cases v with
    | scalar sv =>
      cases sv with
      | mk w s bits =>
        cases w with
        | i8 =>
          cases s with
          | true => rfl
          | false =>
            dsimp only [refValsToUInt8List?, valsToU8Bytes?]
            rw [tryFromUInt_eq_truncateFromUInt,
                truncateFromUInt_eq_miriScalar .i8 bits]
            dsimp only [bind, Except.bind, pure, Except.pure]
            cases h_ov : (truncateBits .i8 bits != bits) with
            | true => rfl
            | false =>
              rw [ite_false_eq_true, ite_false_eq_true]
              dsimp only
              rw [miriScalar_data, truncateBits_eq_of_beq_false h_ov, ih]
              cases valsToU8Bytes? rest with
              | none => rfl
              | some bs =>
                dsimp only [Option.map, List.map]
                have h_lt : bits.toNat < 256 := by
                  have h_t := bitVec128_toNat_truncateBits_lt .i8 bits
                  rw [truncateBits_eq_of_beq_false h_ov] at h_t
                  exact h_t
                have h_bv : (BitVec.ofNat 8 bits.toNat).toNat = bits.toNat := by
                  rw [BitVec.toNat_ofNat]
                  exact Nat.mod_eq_of_lt h_lt
                rw [h_bv]
        | _ => rfl
    | _ => rfl

private theorem valsToU8Bytes?_length :
    ∀ {elems : List Val} {bs : List (BitVec 8)},
      valsToU8Bytes? elems = some bs → bs.length = elems.length
  | [], _, h => by injection h with h_eq; subst h_eq; rfl
  | .scalar ⟨.i8, false, bits⟩ :: rest, bs, h => by
    dsimp only [valsToU8Bytes?] at h
    cases h_ov : (truncateBits .i8 bits != bits) with
    | true => rw [h_ov] at h; cases h
    | false =>
      rw [h_ov, ite_false_eq_true] at h
      cases h_r : valsToU8Bytes? rest with
      | none => rw [h_r] at h; cases h
      | some restBs =>
        rw [h_r] at h
        injection h with h_eq
        subst h_eq
        exact congrArg Nat.succ (valsToU8Bytes?_length h_r)
  | .scalar ⟨.i16, _, _⟩ :: _, _, h => by cases h
  | .scalar ⟨.i32, _, _⟩ :: _, _, h => by cases h
  | .scalar ⟨.i64, _, _⟩ :: _, _, h => by cases h
  | .scalar ⟨.i128, _, _⟩ :: _, _, h => by cases h
  | .scalar ⟨.isize, _, _⟩ :: _, _, h => by cases h
  | .scalar ⟨.i8, true, _⟩ :: _, _, h => by cases h
  | .bool _ :: _, _, h => by cases h
  | .unit :: _, _, h => by cases h
  | .ptr _ :: _, _, h => by cases h
  | .structVal _ _ :: _, _, h => by cases h
  | .enumVal _ _ _ :: _, _, h => by cases h
  | .tuple _ :: _, _, h => by cases h
  | .array _ _ :: _, _, h => by cases h
  | .bytes _ :: _, _, h => by cases h

private theorem leByte_u8_toNat (n k : Nat) :
    (UInt8.ofNat (HMod.hMod (HDiv.hDiv n (HPow.hPow 2 (8 * k))) 256)).toNat =
      (BitVec.ofNat 8 (HDiv.hDiv n (HPow.hPow 256 k))).toNat := by
  have h_pow : HPow.hPow 2 (8 * k) = HPow.hPow 256 k := by
    induction k with
    | zero => rfl
    | succ j ih =>
      rw [Nat.mul_succ, Nat.pow_add, ih, Nat.pow_succ]
      rfl
  change (BitVec.ofNat 8
    (HMod.hMod (HDiv.hDiv n (HPow.hPow 2 (8 * k))) 256)).toNat =
    (BitVec.ofNat 8 (HDiv.hDiv n (HPow.hPow 256 k))).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, h_pow]
  exact Nat.mod_mod _ _

private theorem div_256_pow_step (n k : Nat) :
    HDiv.hDiv (HDiv.hDiv n (HPow.hPow 256 k)) 256 =
      HDiv.hDiv n (HPow.hPow 256 (k + 1)) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

private noncomputable def allocLeByteVal (n k : Nat) : Val :=
  Val.scalar ⟨.i8, false,
    BitVec.ofNat 128
      (UInt8.ofNat (HMod.hMod (HDiv.hDiv n (HPow.hPow 2 (8 * k))) 256)).toNat⟩

private theorem allocLeByteVal_eq (n k : Nat) :
    allocLeByteVal n k =
      Val.scalar ⟨.i8, false,
        BitVec.ofNat 128
          (BitVec.ofNat 8 (HDiv.hDiv n (HPow.hPow 256 k))).toNat⟩ := by
  dsimp only [allocLeByteVal]
  rw [leByte_u8_toNat]

private theorem u8BytesToVals_scalarToLeBytesAux_step (n m k : Nat) :
    u8BytesToVals (scalarToLeBytesAux (m + 1) (HDiv.hDiv n (HPow.hPow 256 k))) =
      allocLeByteVal n k ::
        u8BytesToVals (scalarToLeBytesAux m (HDiv.hDiv n (HPow.hPow 256 (k + 1)))) := by
  dsimp only [scalarToLeBytesAux, u8BytesToVals]
  rw [allocLeByteVal_eq, div_256_pow_step]

private noncomputable def leSumPow (acc p : Nat) : List (BitVec 8) → Nat
  | [] => acc
  | b :: rest => leSumPow (acc + b.toNat * p) (p * 256) rest

private theorem leSumPow_eq (bs : List (BitVec 8)) :
    ∀ (acc p : Nat), leSumPow acc p bs = acc + p * scalarFromLeBytes bs := by
  induction bs with
  | nil =>
    intro acc p
    dsimp only [leSumPow, scalarFromLeBytes, List.foldr]
    rw [Nat.mul_zero, Nat.add_zero]
  | cons b rest ih =>
    intro acc p
    dsimp only [leSumPow, scalarFromLeBytes, List.foldr]
    rw [ih (acc + b.toNat * p) (p * 256), Nat.mul_add, Nat.add_assoc,
        Nat.mul_comm b.toNat p, Nat.mul_assoc]
    rfl

private theorem scalarFromLeBytes_lt (bs : List (BitVec 8)) :
    scalarFromLeBytes bs < Nat.pow 2 (8 * bs.length) := by
  induction bs with
  | nil => decide
  | cons b rest ih =>
    dsimp only [scalarFromLeBytes, List.foldr, List.length]
    have h_step : 256 * scalarFromLeBytes rest + 256 ≤
        256 * Nat.pow 2 (8 * rest.length) := by
      have h_le : scalarFromLeBytes rest + 1 ≤ Nat.pow 2 (8 * rest.length) := ih
      have h_m := Nat.mul_le_mul_left 256 h_le
      rw [Nat.mul_add, Nat.mul_one] at h_m
      exact h_m
    have h_add : b.toNat + 256 * scalarFromLeBytes rest <
        256 + 256 * scalarFromLeBytes rest :=
      Nat.add_lt_add_right b.isLt _
    rw [Nat.add_comm 256 (256 * scalarFromLeBytes rest)] at h_add
    have h_lt := Nat.lt_of_lt_of_le h_add h_step
    have h_pow : 256 * Nat.pow 2 (8 * rest.length) =
        Nat.pow 2 (8 * (rest.length + 1)) := by
      change 256 * HPow.hPow 2 (8 * rest.length) =
        HPow.hPow 2 (8 * (rest.length + 1))
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [← h_pow]
    exact h_lt

private theorem truncateBits_ofNat_leBytes (w : IntWidth) (bs : List (BitVec 8))
    (h_len : bs.length = w.byteSize) :
    (truncateBits w (BitVec.ofNat 128 (scalarFromLeBytes bs)) ==
      BitVec.ofNat 128 (scalarFromLeBytes bs)) = true := by
  have h_bw : 8 * bs.length = w.bitWidth := by
    rw [h_len]
    cases w <;> rfl
  have h_lt : scalarFromLeBytes bs < Nat.pow 2 w.bitWidth := by
    rw [← h_bw]
    exact scalarFromLeBytes_lt bs
  have h_lt128 : scalarFromLeBytes bs < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le h_lt (intWidth_modulus_le_u128 w)
  have h_eq : truncateBits w (BitVec.ofNat 128 (scalarFromLeBytes bs)) =
      BitVec.ofNat 128 (scalarFromLeBytes bs) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt128]
    exact Nat.mod_eq_of_lt h_lt
  rw [h_eq]
  exact beq_self_eq_true _

private theorem rangeForIn_eq_listRange {m : Type → Type} {β : Type} [Monad m]
    (n : Nat) (b : β) (f : Nat → β → m (ForInStep β)) :
    forIn ({ start := 0, stop := n, step := 1,
             step_pos := Nat.zero_lt_one } : Std.Legacy.Range) b f =
      forIn (List.range' 0 n 1) b f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only [Std.Legacy.Range.size]
  rw [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]

private noncomputable def allocByte (n k : Nat) : UInt8 :=
  UInt8.ofNat (HMod.hMod (HDiv.hDiv n (HPow.hPow 2 (8 * k))) 256)

private noncomputable def writeLoopGenFn (f : Nat → UInt8) (index : Nat)
    (result : Array UInt8) :
    Except Miri.Memory.AllocError (ForInStep (Array UInt8)) :=
  Except.ok (ForInStep.yield (result.push (f index)))

private theorem eval_writeLoopGen (f : Nat → UInt8) (is : List Nat) :
    ∀ (acc : List UInt8),
      forIn is (Array.mk acc) (writeLoopGenFn f) =
        Except.ok (Array.mk (acc ++ is.map f)) := by
  induction is with
  | nil =>
    intro acc
    rw [List.map_nil, List.append_nil]
    rfl
  | cons i rest ih =>
    intro acc
    rw [List.forIn_cons]
    dsimp only [writeLoopGenFn, bind, Except.bind, Array.push]
    rw [List.concat_eq_append, ih, List.append_assoc]
    rfl

private theorem refUInt8ListToVals_map_allocByte (n : Nat) :
    ∀ (m k : Nat),
      refUInt8ListToVals ((List.range' k m 1).map (allocByte n)) =
        u8BytesToVals (scalarToLeBytesAux m (HDiv.hDiv n (HPow.hPow 256 k))) := by
  intro m
  induction m with
  | zero => intro k; rfl
  | succ m' ih =>
    intro k
    dsimp only [List.range', List.map, refUInt8ListToVals]
    rw [u8BytesToVals_scalarToLeBytesAux_step, ih (k + 1)]
    rfl

private theorem refUInt8ListToVals_map_allocByte_zero (n m : Nat) :
    refUInt8ListToVals ((List.range' 0 m 1).map (allocByte n)) =
      u8BytesToVals (scalarToLeBytesAux m n) := by
  have h := refUInt8ListToVals_map_allocByte n m 0
  change _ = u8BytesToVals (scalarToLeBytesAux m (HDiv.hDiv n 1)) at h
  rw [Nat.div_one] at h
  exact h

private theorem toNat_ofNat128_u8_truncateBits (bits : BitVec 128) :
    (BitVec.ofNat 128
      (UInt8.ofNat (truncateBits .i8 bits).toNat).toNat).toNat =
      (truncateBits .i8 bits).toNat := by
  have h_lt := bitVec128_toNat_truncateBits_lt .i8 bits
  change (truncateBits .i8 bits).toNat < HPow.hPow 2 8 at h_lt
  change (BitVec.ofNat 128
    (BitVec.ofNat 8 (truncateBits .i8 bits).toNat).toNat).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))

private theorem toNat_ofNat128_u16_truncateBits (bits : BitVec 128) :
    (BitVec.ofNat 128
      (UInt16.ofNat (truncateBits .i16 bits).toNat).toNat).toNat =
      (truncateBits .i16 bits).toNat := by
  have h_lt := bitVec128_toNat_truncateBits_lt .i16 bits
  change (truncateBits .i16 bits).toNat < HPow.hPow 2 16 at h_lt
  change (BitVec.ofNat 128
    (BitVec.ofNat 16 (truncateBits .i16 bits).toNat).toNat).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))

private theorem toNat_ofNat128_u32_truncateBits (bits : BitVec 128) :
    (BitVec.ofNat 128
      (UInt32.ofNat (truncateBits .i32 bits).toNat).toNat).toNat =
      (truncateBits .i32 bits).toNat := by
  have h_lt := bitVec128_toNat_truncateBits_lt .i32 bits
  change (truncateBits .i32 bits).toNat < HPow.hPow 2 32 at h_lt
  change (BitVec.ofNat 128
    (BitVec.ofNat 32 (truncateBits .i32 bits).toNat).toNat).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))

private theorem toNat_ofNat128_u64_truncateBits (w : IntWidth)
    (h_bw : w.bitWidth = 64) (bits : BitVec 128) :
    (BitVec.ofNat 128
      (UInt64.ofNat (truncateBits w bits).toNat).toNat).toNat =
      (truncateBits w bits).toNat := by
  have h_lt := bitVec128_toNat_truncateBits_lt w bits
  rw [h_bw] at h_lt
  change (truncateBits w bits).toNat < HPow.hPow 2 64 at h_lt
  change (BitVec.ofNat 128
    (BitVec.ofNat 64 (truncateBits w bits).toNat).toNat).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))

private theorem refAllocWrite_u8 (u : UInt8) (data : Array UInt8)
    (h_loop : forIn (List.range' 0 1 1) (Array.mk ([] : List UInt8))
      (writeLoopGenFn (allocByte (BitVec.ofNat 128 u.toNat).toNat)) =
      Except.ok data)
    (h_sz : data.size = 1) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk (refReplicateUInt8 1 0)) Miri.ABI.Align.ONE .Mut with
      | .error _ => Except.error FaultKind.unsupported
      | .ok alloc₀ =>
        match Miri.Memory.Allocation.writeScalar refLittleEndianTargetLayout
            ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 1⟩
            (.fromScalarInt (.ofUInt8 u)) alloc₀ with
        | .error _ _ => Except.error FaultKind.unsupported
        | .ok () alloc₁ =>
          match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
              refLittleEndianTargetLayout
              ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 1⟩ with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) =
      Except.ok (refUInt8ListToVals data.toList) := by
  have h_app :
      ((Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)) =
        data := by
    rw [Array.empty_append, Array.append_empty]
  have h_ex : data.extract 0 1 = data := by
    rw [← h_sz]; exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes Miri.Memory.Allocation.writeScalar
  change (match
      ((match (Except.bind
          (forIn ({ start := 0, stop := 1, step := 1,
                    step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
            (Array.mk ([] : List UInt8))
            (writeLoopGenFn (allocByte (BitVec.ofNat 128 u.toNat).toNat)))
          (fun r => (Except.ok r : Except Miri.Memory.AllocError (Array UInt8)))) with
        | Except.ok arr => _
        | Except.error e => _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 1⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [rangeForIn_eq_listRange, h_loop]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != (Miri.ABI.Size.ofBytes 1).bytes.toNat then _
        else _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 1⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != 1 then _
        else Except.ok (bytes.extract 0 1)) :
          Except Miri.Memory.AllocError (Array UInt8)) with
    | Except.error _ => Except.error FaultKind.unsupported
    | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz, h_ex]; rfl

private theorem refAllocWrite_u16 (u : UInt16) (data : Array UInt8)
    (h_loop : forIn (List.range' 0 2 1) (Array.mk ([] : List UInt8))
      (writeLoopGenFn (allocByte (BitVec.ofNat 128 u.toNat).toNat)) =
      Except.ok data)
    (h_sz : data.size = 2) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk (refReplicateUInt8 2 0)) Miri.ABI.Align.ONE .Mut with
      | .error _ => Except.error FaultKind.unsupported
      | .ok alloc₀ =>
        match Miri.Memory.Allocation.writeScalar refLittleEndianTargetLayout
            ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 2⟩
            (.fromScalarInt (.ofUInt16 u)) alloc₀ with
        | .error _ _ => Except.error FaultKind.unsupported
        | .ok () alloc₁ =>
          match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
              refLittleEndianTargetLayout
              ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 2⟩ with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) =
      Except.ok (refUInt8ListToVals data.toList) := by
  have h_app :
      ((Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)) =
        data := by
    rw [Array.empty_append, Array.append_empty]
  have h_ex : data.extract 0 2 = data := by
    rw [← h_sz]; exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes Miri.Memory.Allocation.writeScalar
  change (match
      ((match (Except.bind
          (forIn ({ start := 0, stop := 2, step := 1,
                    step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
            (Array.mk ([] : List UInt8))
            (writeLoopGenFn (allocByte (BitVec.ofNat 128 u.toNat).toNat)))
          (fun r => (Except.ok r : Except Miri.Memory.AllocError (Array UInt8)))) with
        | Except.ok arr => _
        | Except.error e => _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 2⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [rangeForIn_eq_listRange, h_loop]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != (Miri.ABI.Size.ofBytes 2).bytes.toNat then _
        else _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 2⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != 2 then _
        else Except.ok (bytes.extract 0 2)) :
          Except Miri.Memory.AllocError (Array UInt8)) with
    | Except.error _ => Except.error FaultKind.unsupported
    | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz, h_ex]; rfl

private theorem refAllocWrite_u32 (u : UInt32) (data : Array UInt8)
    (h_loop : forIn (List.range' 0 4 1) (Array.mk ([] : List UInt8))
      (writeLoopGenFn (allocByte (BitVec.ofNat 128 u.toNat).toNat)) =
      Except.ok data)
    (h_sz : data.size = 4) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk (refReplicateUInt8 4 0)) Miri.ABI.Align.ONE .Mut with
      | .error _ => Except.error FaultKind.unsupported
      | .ok alloc₀ =>
        match Miri.Memory.Allocation.writeScalar refLittleEndianTargetLayout
            ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4⟩
            (.fromScalarInt (.ofUInt32 u)) alloc₀ with
        | .error _ _ => Except.error FaultKind.unsupported
        | .ok () alloc₁ =>
          match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
              refLittleEndianTargetLayout
              ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4⟩ with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) =
      Except.ok (refUInt8ListToVals data.toList) := by
  have h_app :
      ((Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)) =
        data := by
    rw [Array.empty_append, Array.append_empty]
  have h_ex : data.extract 0 4 = data := by
    rw [← h_sz]; exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes Miri.Memory.Allocation.writeScalar
  change (match
      ((match (Except.bind
          (forIn ({ start := 0, stop := 4, step := 1,
                    step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
            (Array.mk ([] : List UInt8))
            (writeLoopGenFn (allocByte (BitVec.ofNat 128 u.toNat).toNat)))
          (fun r => (Except.ok r : Except Miri.Memory.AllocError (Array UInt8)))) with
        | Except.ok arr => _
        | Except.error e => _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [rangeForIn_eq_listRange, h_loop]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != (Miri.ABI.Size.ofBytes 4).bytes.toNat then _
        else _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != 4 then _
        else Except.ok (bytes.extract 0 4)) :
          Except Miri.Memory.AllocError (Array UInt8)) with
    | Except.error _ => Except.error FaultKind.unsupported
    | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz, h_ex]; rfl

private theorem refAllocWrite_u64 (u : UInt64) (data : Array UInt8)
    (h_loop : forIn (List.range' 0 8 1) (Array.mk ([] : List UInt8))
      (writeLoopGenFn (allocByte (BitVec.ofNat 128 u.toNat).toNat)) =
      Except.ok data)
    (h_sz : data.size = 8) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk (refReplicateUInt8 8 0)) Miri.ABI.Align.ONE .Mut with
      | .error _ => Except.error FaultKind.unsupported
      | .ok alloc₀ =>
        match Miri.Memory.Allocation.writeScalar refLittleEndianTargetLayout
            ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8⟩
            (.fromScalarInt (.ofUInt64 u)) alloc₀ with
        | .error _ _ => Except.error FaultKind.unsupported
        | .ok () alloc₁ =>
          match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
              refLittleEndianTargetLayout
              ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8⟩ with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) =
      Except.ok (refUInt8ListToVals data.toList) := by
  have h_app :
      ((Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)) =
        data := by
    rw [Array.empty_append, Array.append_empty]
  have h_ex : data.extract 0 8 = data := by
    rw [← h_sz]; exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes Miri.Memory.Allocation.writeScalar
  change (match
      ((match (Except.bind
          (forIn ({ start := 0, stop := 8, step := 1,
                    step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
            (Array.mk ([] : List UInt8))
            (writeLoopGenFn (allocByte (BitVec.ofNat 128 u.toNat).toNat)))
          (fun r => (Except.ok r : Except Miri.Memory.AllocError (Array UInt8)))) with
        | Except.ok arr => _
        | Except.error e => _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [rangeForIn_eq_listRange, h_loop]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != (Miri.ABI.Size.ofBytes 8).bytes.toNat then _
        else _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != 8 then _
        else Except.ok (bytes.extract 0 8)) :
          Except Miri.Memory.AllocError (Array UInt8)) with
    | Except.error _ => Except.error FaultKind.unsupported
    | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz, h_ex]; rfl

private theorem refAllocWrite_u128 (d : BitVec 128) (data : Array UInt8)
    (h_loop : forIn (List.range' 0 16 1) (Array.mk ([] : List UInt8))
      (writeLoopGenFn (allocByte d.toNat)) = Except.ok data)
    (h_sz : data.size = 16) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk (refReplicateUInt8 16 0)) Miri.ABI.Align.ONE .Mut with
      | .error _ => Except.error FaultKind.unsupported
      | .ok alloc₀ =>
        match Miri.Memory.Allocation.writeScalar refLittleEndianTargetLayout
            ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 16⟩
            (.fromScalarInt (.ofUInt128 d)) alloc₀ with
        | .error _ _ => Except.error FaultKind.unsupported
        | .ok () alloc₁ =>
          match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
              refLittleEndianTargetLayout
              ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 16⟩ with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) =
      Except.ok (refUInt8ListToVals data.toList) := by
  have h_app :
      ((Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)) =
        data := by
    rw [Array.empty_append, Array.append_empty]
  have h_ex : data.extract 0 16 = data := by
    rw [← h_sz]; exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes Miri.Memory.Allocation.writeScalar
  change (match
      ((match (Except.bind
          (forIn ({ start := 0, stop := 16, step := 1,
                    step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
            (Array.mk ([] : List UInt8)) (writeLoopGenFn (allocByte d.toNat)))
          (fun r => (Except.ok r : Except Miri.Memory.AllocError (Array UInt8)))) with
        | Except.ok arr => _
        | Except.error e => _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 16⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [rangeForIn_eq_listRange, h_loop]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != (Miri.ABI.Size.ofBytes 16).bytes.toNat then _
        else _) :
          EStateM.Result Miri.Memory.AllocError
            (Miri.Memory.Allocation Miri.Memory.Provenance Unit) Unit) with
    | EStateM.Result.error _ _ => Except.error FaultKind.unsupported
    | EStateM.Result.ok () alloc₁ =>
      match Miri.Memory.Allocation.getBytesStripProvenance alloc₁
          refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 16⟩ with
      | Except.error _ => Except.error FaultKind.unsupported
      | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz]
  change (match
      ((let bytes :=
          (Array.mk ([] : List UInt8)) ++ data ++ Array.mk ([] : List UInt8)
        if bytes.size != 16 then _
        else Except.ok (bytes.extract 0 16)) :
          Except Miri.Memory.AllocError (Array UInt8)) with
    | Except.error _ => Except.error FaultKind.unsupported
    | Except.ok bytes => Except.ok (refUInt8ListToVals bytes.toList)) = _
  rw [h_app]; simp only [h_sz, h_ex]; rfl

private theorem refAllocScalarToLeBytes_eq (sv : ScalarVal) :
    refAllocScalarToLeBytes sv =
      .ok (u8BytesToVals
        (scalarToLeBytesAux sv.width.byteSize
          (truncateBits sv.width sv.bits).toNat)) := by
  cases sv with
  | mk w s bits =>
    cases w with
    | i8 =>
      dsimp only [refAllocScalarToLeBytes, IntWidth.byteSize, toMiriSize]
      rw [miriScalar_eq_ofUInt]
      dsimp only
      have h_loop := eval_writeLoopGen
        (allocByte (BitVec.ofNat 128
          (UInt8.ofNat (truncateBits .i8 bits).toNat).toNat).toNat)
        (List.range' 0 1 1) []
      rw [List.nil_append] at h_loop
      have h_sz :
          (Array.mk ((List.range' 0 1 1).map
            (allocByte (BitVec.ofNat 128
              (UInt8.ofNat (truncateBits .i8 bits).toNat).toNat).toNat))).size =
            1 := by
        change (List.map _ _).length = 1
        rw [List.length_map, List.length_range']
      refine Eq.trans (refAllocWrite_u8 _ _ h_loop h_sz) ?_
      dsimp only
      rw [toNat_ofNat128_u8_truncateBits]
      exact congrArg Except.ok
        (refUInt8ListToVals_map_allocByte_zero (truncateBits .i8 bits).toNat 1)
    | i16 =>
      dsimp only [refAllocScalarToLeBytes, IntWidth.byteSize, toMiriSize]
      rw [miriScalar_eq_ofUInt]
      dsimp only
      have h_loop := eval_writeLoopGen
        (allocByte (BitVec.ofNat 128
          (UInt16.ofNat (truncateBits .i16 bits).toNat).toNat).toNat)
        (List.range' 0 2 1) []
      rw [List.nil_append] at h_loop
      have h_sz :
          (Array.mk ((List.range' 0 2 1).map
            (allocByte (BitVec.ofNat 128
              (UInt16.ofNat (truncateBits .i16 bits).toNat).toNat).toNat))).size =
            2 := by
        change (List.map _ _).length = 2
        rw [List.length_map, List.length_range']
      refine Eq.trans (refAllocWrite_u16 _ _ h_loop h_sz) ?_
      dsimp only
      rw [toNat_ofNat128_u16_truncateBits]
      exact congrArg Except.ok
        (refUInt8ListToVals_map_allocByte_zero (truncateBits .i16 bits).toNat 2)
    | i32 =>
      dsimp only [refAllocScalarToLeBytes, IntWidth.byteSize, toMiriSize]
      rw [miriScalar_eq_ofUInt]
      dsimp only
      have h_loop := eval_writeLoopGen
        (allocByte (BitVec.ofNat 128
          (UInt32.ofNat (truncateBits .i32 bits).toNat).toNat).toNat)
        (List.range' 0 4 1) []
      rw [List.nil_append] at h_loop
      have h_sz :
          (Array.mk ((List.range' 0 4 1).map
            (allocByte (BitVec.ofNat 128
              (UInt32.ofNat (truncateBits .i32 bits).toNat).toNat).toNat))).size =
            4 := by
        change (List.map _ _).length = 4
        rw [List.length_map, List.length_range']
      refine Eq.trans (refAllocWrite_u32 _ _ h_loop h_sz) ?_
      dsimp only
      rw [toNat_ofNat128_u32_truncateBits]
      exact congrArg Except.ok
        (refUInt8ListToVals_map_allocByte_zero (truncateBits .i32 bits).toNat 4)
    | i64 =>
      dsimp only [refAllocScalarToLeBytes, IntWidth.byteSize, toMiriSize]
      rw [miriScalar_eq_ofUInt]
      dsimp only
      have h_loop := eval_writeLoopGen
        (allocByte (BitVec.ofNat 128
          (UInt64.ofNat (truncateBits .i64 bits).toNat).toNat).toNat)
        (List.range' 0 8 1) []
      rw [List.nil_append] at h_loop
      have h_sz :
          (Array.mk ((List.range' 0 8 1).map
            (allocByte (BitVec.ofNat 128
              (UInt64.ofNat (truncateBits .i64 bits).toNat).toNat).toNat))).size =
            8 := by
        change (List.map _ _).length = 8
        rw [List.length_map, List.length_range']
      refine Eq.trans (refAllocWrite_u64 _ _ h_loop h_sz) ?_
      dsimp only
      rw [toNat_ofNat128_u64_truncateBits .i64 rfl]
      exact congrArg Except.ok
        (refUInt8ListToVals_map_allocByte_zero (truncateBits .i64 bits).toNat 8)
    | isize =>
      dsimp only [refAllocScalarToLeBytes, IntWidth.byteSize, toMiriSize]
      rw [miriScalar_eq_ofUInt]
      dsimp only
      have h_loop := eval_writeLoopGen
        (allocByte (BitVec.ofNat 128
          (UInt64.ofNat (truncateBits .isize bits).toNat).toNat).toNat)
        (List.range' 0 8 1) []
      rw [List.nil_append] at h_loop
      have h_sz :
          (Array.mk ((List.range' 0 8 1).map
            (allocByte (BitVec.ofNat 128
              (UInt64.ofNat (truncateBits .isize bits).toNat).toNat).toNat))).size =
            8 := by
        change (List.map _ _).length = 8
        rw [List.length_map, List.length_range']
      refine Eq.trans (refAllocWrite_u64 _ _ h_loop h_sz) ?_
      dsimp only
      rw [toNat_ofNat128_u64_truncateBits .isize rfl]
      exact congrArg Except.ok
        (refUInt8ListToVals_map_allocByte_zero (truncateBits .isize bits).toNat 8)
    | i128 =>
      dsimp only [refAllocScalarToLeBytes, IntWidth.byteSize, toMiriSize]
      rw [miriScalar_eq_ofUInt]
      dsimp only
      have h_loop := eval_writeLoopGen
        (allocByte (truncateBits .i128 bits).toNat)
        (List.range' 0 16 1) []
      rw [List.nil_append] at h_loop
      have h_sz :
          (Array.mk ((List.range' 0 16 1).map
            (allocByte (truncateBits .i128 bits).toNat))).size = 16 := by
        change (List.map _ _).length = 16
        rw [List.length_map, List.length_range']
      refine Eq.trans (refAllocWrite_u128 _ _ h_loop h_sz) ?_
      dsimp only
      exact congrArg Except.ok
        (refUInt8ListToVals_map_allocByte_zero (truncateBits .i128 bits).toNat 16)

private noncomputable def readListLoopFn (k : Nat) (us : List UInt8) (index r : Nat) :
    Except Miri.Memory.AllocError (ForInStep Nat) :=
  match us[index]? with
  | some byte =>
    Except.ok (ForInStep.yield
      (r + byte.toNat * HPow.hPow 2 (8 * index)))
  | none =>
    Except.error
      (Miri.Memory.AllocError.invalidSliceEndpoints index (index + 1) k)

private theorem list_getElem?_append_len {α : Type} :
    ∀ (pfx : List α) (x : α) (sfx : List α),
      (pfx ++ x :: sfx)[pfx.length]? = some x
  | [], _, _ => rfl
  | _ :: rest, x, sfx => list_getElem?_append_len rest x sfx

private theorem pow2_8_succ (n : Nat) :
    HPow.hPow 2 (8 * (n + 1)) = HPow.hPow 2 (8 * n) * 256 := by
  rw [Nat.mul_succ, Nat.pow_add]

private theorem eval_readListLoop_sfx (k : Nat) (sfx : List (BitVec 8)) :
    ∀ (pfx : List (BitVec 8)) (acc : Nat),
      forIn (List.range' pfx.length sfx.length 1) acc
        (readListLoopFn k
          (List.map (fun b => UInt8.ofNat b.toNat) (pfx ++ sfx))) =
      Except.ok (leSumPow acc (HPow.hPow 2 (8 * pfx.length)) sfx) := by
  induction sfx with
  | nil =>
    intro pfx acc
    rfl
  | cons b rest ih =>
    intro pfx acc
    dsimp only [List.length, List.range', leSumPow]
    rw [List.forIn_cons]
    have h_map : List.map (fun b => UInt8.ofNat b.toNat) (pfx ++ b :: rest) =
        List.map (fun b => UInt8.ofNat b.toNat) pfx ++
          UInt8.ofNat b.toNat :: List.map (fun b => UInt8.ofNat b.toNat) rest := by
      rw [List.map_append]; rfl
    dsimp only [readListLoopFn]
    rw [h_map,
        ← List.length_map (as := pfx)
            (f := fun b : BitVec 8 => UInt8.ofNat b.toNat),
        list_getElem?_append_len, List.length_map]
    dsimp only [bind, Except.bind]
    rw [u8_ofNat_bv8_toNat]
    have h_app : pfx ++ b :: rest = (pfx ++ [b]) ++ rest := by
      rw [List.append_assoc]; rfl
    have h_len : (pfx ++ [b]).length = pfx.length + 1 := List.length_append
    rw [← h_len, ← h_map, h_app]
    rw [ih (pfx ++ [b]) (acc + b.toNat * HPow.hPow 2 (8 * pfx.length)),
        h_len, pow2_8_succ]

private theorem eval_readListLoop_zero (k : Nat) (bs : List (BitVec 8))
    (h_blen : bs.length = k) :
    forIn (List.range' 0 k 1) (0 : Nat)
      (readListLoopFn k (List.map (fun b => UInt8.ofNat b.toNat) bs)) =
      Except.ok (leSumPow 0 1 bs) := by
  subst h_blen
  exact eval_readListLoop_sfx bs.length bs [] 0

private theorem read_arr_1 (arr : Array UInt8) (h_sz : arr.size = 1) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        arr Miri.ABI.Align.ONE .Not with
      | .error e => Except.error e
      | .ok alloc =>
        Miri.Memory.Allocation.readScalar alloc refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 1⟩ false) =
      Except.bind
        (Except.bind
          (forIn (List.range' 0 1 1) (0 : Nat) (readListLoopFn 1 arr.toList))
          (fun r => Except.ok (BitVec.ofNat 128 r)))
        (fun bits =>
          Except.mapError Miri.Memory.AllocError.scalar
            (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              bits (Miri.ABI.Size.ofBytes 1))) := by
  have h_ex : arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes + (Miri.ABI.Size.ofBytes 1).bytes)).bytes.toNat =
      arr := by
    change arr.extract 0 1 = arr
    rw [← h_sz]
    exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes
  simp only [h_sz]
  change Except.bind
    (if arr.size != (Miri.ABI.Size.ofBytes 1).bytes.toNat then _
     else _)
    _ = _
  simp only [h_sz]
  change Except.bind
    (let bs := arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes +
          (Miri.ABI.Size.ofBytes 1).bytes)).bytes.toNat
     if bs.size > 16 then _
     else
       Except.bind
         (forIn ({ start := 0, stop := bs.size, step := 1,
                   step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
           (0 : Nat) _)
         _)
    _ = _
  simp only [h_ex, h_sz]
  change Except.bind
    (Except.bind
      (forIn ({ start := 0, stop := 1, step := 1,
                step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
        (0 : Nat) _)
      _)
    _ = _
  rw [rangeForIn_eq_listRange]
  refine congr (congrArg Except.bind (congr (congrArg Except.bind
    (congrArg (forIn (List.range' 0 1 1) (0 : Nat)) ?_)) rfl)) ?_
  · funext index r
    dsimp only [readListLoopFn]
    rw [← Array.getElem?_toList]
    cases arr.toList[index]? <;> rfl
  · funext bits
    rfl

private theorem read_arr_2 (arr : Array UInt8) (h_sz : arr.size = 2) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        arr Miri.ABI.Align.ONE .Not with
      | .error e => Except.error e
      | .ok alloc =>
        Miri.Memory.Allocation.readScalar alloc refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 2⟩ false) =
      Except.bind
        (Except.bind
          (forIn (List.range' 0 2 1) (0 : Nat) (readListLoopFn 2 arr.toList))
          (fun r => Except.ok (BitVec.ofNat 128 r)))
        (fun bits =>
          Except.mapError Miri.Memory.AllocError.scalar
            (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              bits (Miri.ABI.Size.ofBytes 2))) := by
  have h_ex : arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes + (Miri.ABI.Size.ofBytes 2).bytes)).bytes.toNat =
      arr := by
    change arr.extract 0 2 = arr
    rw [← h_sz]
    exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes
  simp only [h_sz]
  change Except.bind
    (if arr.size != (Miri.ABI.Size.ofBytes 2).bytes.toNat then _
     else _)
    _ = _
  simp only [h_sz]
  change Except.bind
    (let bs := arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes +
          (Miri.ABI.Size.ofBytes 2).bytes)).bytes.toNat
     if bs.size > 16 then _
     else
       Except.bind
         (forIn ({ start := 0, stop := bs.size, step := 1,
                   step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
           (0 : Nat) _)
         _)
    _ = _
  simp only [h_ex, h_sz]
  change Except.bind
    (Except.bind
      (forIn ({ start := 0, stop := 2, step := 1,
                step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
        (0 : Nat) _)
      _)
    _ = _
  rw [rangeForIn_eq_listRange]
  refine congr (congrArg Except.bind (congr (congrArg Except.bind
    (congrArg (forIn (List.range' 0 2 1) (0 : Nat)) ?_)) rfl)) ?_
  · funext index r
    dsimp only [readListLoopFn]
    rw [← Array.getElem?_toList]
    cases arr.toList[index]? <;> rfl
  · funext bits
    rfl

private theorem read_arr_4 (arr : Array UInt8) (h_sz : arr.size = 4) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        arr Miri.ABI.Align.ONE .Not with
      | .error e => Except.error e
      | .ok alloc =>
        Miri.Memory.Allocation.readScalar alloc refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4⟩ false) =
      Except.bind
        (Except.bind
          (forIn (List.range' 0 4 1) (0 : Nat) (readListLoopFn 4 arr.toList))
          (fun r => Except.ok (BitVec.ofNat 128 r)))
        (fun bits =>
          Except.mapError Miri.Memory.AllocError.scalar
            (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              bits (Miri.ABI.Size.ofBytes 4))) := by
  have h_ex : arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes + (Miri.ABI.Size.ofBytes 4).bytes)).bytes.toNat =
      arr := by
    change arr.extract 0 4 = arr
    rw [← h_sz]
    exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes
  simp only [h_sz]
  change Except.bind
    (if arr.size != (Miri.ABI.Size.ofBytes 4).bytes.toNat then _
     else _)
    _ = _
  simp only [h_sz]
  change Except.bind
    (let bs := arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes +
          (Miri.ABI.Size.ofBytes 4).bytes)).bytes.toNat
     if bs.size > 16 then _
     else
       Except.bind
         (forIn ({ start := 0, stop := bs.size, step := 1,
                   step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
           (0 : Nat) _)
         _)
    _ = _
  simp only [h_ex, h_sz]
  change Except.bind
    (Except.bind
      (forIn ({ start := 0, stop := 4, step := 1,
                step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
        (0 : Nat) _)
      _)
    _ = _
  rw [rangeForIn_eq_listRange]
  refine congr (congrArg Except.bind (congr (congrArg Except.bind
    (congrArg (forIn (List.range' 0 4 1) (0 : Nat)) ?_)) rfl)) ?_
  · funext index r
    dsimp only [readListLoopFn]
    rw [← Array.getElem?_toList]
    cases arr.toList[index]? <;> rfl
  · funext bits
    rfl

private theorem read_arr_8 (arr : Array UInt8) (h_sz : arr.size = 8) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        arr Miri.ABI.Align.ONE .Not with
      | .error e => Except.error e
      | .ok alloc =>
        Miri.Memory.Allocation.readScalar alloc refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8⟩ false) =
      Except.bind
        (Except.bind
          (forIn (List.range' 0 8 1) (0 : Nat) (readListLoopFn 8 arr.toList))
          (fun r => Except.ok (BitVec.ofNat 128 r)))
        (fun bits =>
          Except.mapError Miri.Memory.AllocError.scalar
            (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              bits (Miri.ABI.Size.ofBytes 8))) := by
  have h_ex : arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes + (Miri.ABI.Size.ofBytes 8).bytes)).bytes.toNat =
      arr := by
    change arr.extract 0 8 = arr
    rw [← h_sz]
    exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes
  simp only [h_sz]
  change Except.bind
    (if arr.size != (Miri.ABI.Size.ofBytes 8).bytes.toNat then _
     else _)
    _ = _
  simp only [h_sz]
  change Except.bind
    (let bs := arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes +
          (Miri.ABI.Size.ofBytes 8).bytes)).bytes.toNat
     if bs.size > 16 then _
     else
       Except.bind
         (forIn ({ start := 0, stop := bs.size, step := 1,
                   step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
           (0 : Nat) _)
         _)
    _ = _
  simp only [h_ex, h_sz]
  change Except.bind
    (Except.bind
      (forIn ({ start := 0, stop := 8, step := 1,
                step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
        (0 : Nat) _)
      _)
    _ = _
  rw [rangeForIn_eq_listRange]
  refine congr (congrArg Except.bind (congr (congrArg Except.bind
    (congrArg (forIn (List.range' 0 8 1) (0 : Nat)) ?_)) rfl)) ?_
  · funext index r
    dsimp only [readListLoopFn]
    rw [← Array.getElem?_toList]
    cases arr.toList[index]? <;> rfl
  · funext bits
    rfl

private theorem read_arr_16 (arr : Array UInt8) (h_sz : arr.size = 16) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        arr Miri.ABI.Align.ONE .Not with
      | .error e => Except.error e
      | .ok alloc =>
        Miri.Memory.Allocation.readScalar alloc refLittleEndianTargetLayout
          ⟨Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 16⟩ false) =
      Except.bind
        (Except.bind
          (forIn (List.range' 0 16 1) (0 : Nat) (readListLoopFn 16 arr.toList))
          (fun r => Except.ok (BitVec.ofNat 128 r)))
        (fun bits =>
          Except.mapError Miri.Memory.AllocError.scalar
            (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              bits (Miri.ABI.Size.ofBytes 16))) := by
  have h_ex : arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes + (Miri.ABI.Size.ofBytes 16).bytes)).bytes.toNat =
      arr := by
    change arr.extract 0 16 = arr
    rw [← h_sz]
    exact Array.extract_size
  unfold Miri.Memory.Allocation.fromBytes
  simp only [h_sz]
  change Except.bind
    (if arr.size != (Miri.ABI.Size.ofBytes 16).bytes.toNat then _
     else _)
    _ = _
  simp only [h_sz]
  change Except.bind
    (let bs := arr.extract Miri.ABI.Size.ZERO.bytes.toNat
      (Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes +
          (Miri.ABI.Size.ofBytes 16).bytes)).bytes.toNat
     if bs.size > 16 then _
     else
       Except.bind
         (forIn ({ start := 0, stop := bs.size, step := 1,
                   step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
           (0 : Nat) _)
         _)
    _ = _
  simp only [h_ex, h_sz]
  change Except.bind
    (Except.bind
      (forIn ({ start := 0, stop := 16, step := 1,
                step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
        (0 : Nat) _)
      _)
    _ = _
  rw [rangeForIn_eq_listRange]
  refine congr (congrArg Except.bind (congr (congrArg Except.bind
    (congrArg (forIn (List.range' 0 16 1) (0 : Nat)) ?_)) rfl)) ?_
  · funext index r
    dsimp only [readListLoopFn]
    rw [← Array.getElem?_toList]
    cases arr.toList[index]? <;> rfl
  · funext bits
    rfl

private theorem refAllocRead_eq_fromUInt_finish (w : IntWidth) (s : Bool)
    (bs : List (BitVec 8)) (h_len : bs.length = w.byteSize) :
    (match Except.mapError Miri.Memory.AllocError.scalar
        (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
          (BitVec.ofNat 128 (leSumPow 0 1 bs)) (toMiriSize w)) with
      | .error _ => Except.error FaultKind.unsupported
      | .ok sc =>
        match sc.toBits (toMiriSize w) with
        | .error _ => Except.error FaultKind.unsupported
        | .ok bits =>
          Except.ok (Val.scalar ⟨w, s, (miriScalar w bits).data⟩)) =
      Except.ok (Val.scalar ⟨w, s,
        truncateBits w (BitVec.ofNat 128 (scalarFromLeBytes bs))⟩) := by
  rw [leSumPow_eq, Nat.zero_add, Nat.one_mul]
  rw [scalar_fromUInt_of_truncateBits_beq (truncateBits_ofNat_leBytes w bs h_len)]
  dsimp only [Except.mapError]
  rw [scalar_fromScalarInt_toBits_eq]
  dsimp only
  rw [miriScalar_data, truncateBits_idem]

private theorem refAllocFromLeBytes_chain (w : IntWidth) (s : Bool)
    (us : List UInt8) :
    (match Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk us) Miri.ABI.Align.ONE .Not with
      | .error _ => Except.error FaultKind.unsupported
      | .ok alloc =>
        match Miri.Memory.Allocation.readScalar alloc
            refLittleEndianTargetLayout
            ⟨Miri.ABI.Size.ZERO, toMiriSize w⟩ false with
        | .error _ => Except.error FaultKind.unsupported
        | .ok sc =>
          match sc.toBits (toMiriSize w) with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bits =>
            Except.ok (Val.scalar ⟨w, s, (miriScalar w bits).data⟩)) =
      (match (match Miri.Memory.Allocation.fromBytes
          (Prov := Miri.Memory.Provenance)
          (Array.mk us) Miri.ABI.Align.ONE .Not with
        | .error e => Except.error e
        | .ok alloc =>
          Miri.Memory.Allocation.readScalar alloc refLittleEndianTargetLayout
            ⟨Miri.ABI.Size.ZERO, toMiriSize w⟩ false) with
      | .error _ => Except.error FaultKind.unsupported
      | .ok sc =>
        match sc.toBits (toMiriSize w) with
        | .error _ => Except.error FaultKind.unsupported
        | .ok bits =>
          Except.ok (Val.scalar ⟨w, s, (miriScalar w bits).data⟩)) := by
  cases Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
      (Array.mk us) Miri.ABI.Align.ONE .Not <;> rfl

private theorem refAllocScalarFromLeBytes_eq (w : IntWidth) (s : Bool)
    (elems : List Val) (h_len : Nat.beq elems.length w.byteSize = true) :
    refAllocScalarFromLeBytes w s elems =
      match valsToU8Bytes? elems with
      | none => .error .unsupported
      | some bs =>
        .ok (.scalar ⟨w, s,
          truncateBits w (BitVec.ofNat 128 (scalarFromLeBytes bs))⟩) := by
  dsimp only [refAllocScalarFromLeBytes]
  rw [refValsToUInt8List?_eq]
  cases h_v : valsToU8Bytes? elems with
  | none => rfl
  | some bs =>
    dsimp only [Option.map]
    have h_blen : bs.length = w.byteSize :=
      (valsToU8Bytes?_length h_v).trans (Nat.eq_of_beq_eq_true h_len)
    refine Eq.trans (refAllocFromLeBytes_chain w s _) ?_
    cases w with
    | i8 =>
      dsimp only [IntWidth.byteSize] at h_blen
      have h_asz :
          (Array.mk (List.map (fun b : BitVec 8 => UInt8.ofNat b.toNat) bs)).size =
            1 := by
        change (List.map _ bs).length = 1
        rw [List.length_map, h_blen]
      have h_rl := eval_readListLoop_zero 1 bs h_blen
      have h_rd := read_arr_1 _ h_asz
      dsimp only [Array.toList] at h_rd
      refine Eq.trans (congrArg (fun inner =>
        match inner with
        | .error _ => Except.error FaultKind.unsupported
        | .ok sc =>
          match sc.toBits (toMiriSize .i8) with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bits =>
            Except.ok (Val.scalar ⟨.i8, s, (miriScalar .i8 bits).data⟩)) h_rd) ?_
      rw [h_rl]
      dsimp only [Except.bind]
      exact refAllocRead_eq_fromUInt_finish .i8 s bs h_blen
    | i16 =>
      dsimp only [IntWidth.byteSize] at h_blen
      have h_asz :
          (Array.mk (List.map (fun b : BitVec 8 => UInt8.ofNat b.toNat) bs)).size =
            2 := by
        change (List.map _ bs).length = 2
        rw [List.length_map, h_blen]
      have h_rl := eval_readListLoop_zero 2 bs h_blen
      have h_rd := read_arr_2 _ h_asz
      dsimp only [Array.toList] at h_rd
      refine Eq.trans (congrArg (fun inner =>
        match inner with
        | .error _ => Except.error FaultKind.unsupported
        | .ok sc =>
          match sc.toBits (toMiriSize .i16) with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bits =>
            Except.ok (Val.scalar ⟨.i16, s, (miriScalar .i16 bits).data⟩)) h_rd) ?_
      rw [h_rl]
      dsimp only [Except.bind]
      exact refAllocRead_eq_fromUInt_finish .i16 s bs h_blen
    | i32 =>
      dsimp only [IntWidth.byteSize] at h_blen
      have h_asz :
          (Array.mk (List.map (fun b : BitVec 8 => UInt8.ofNat b.toNat) bs)).size =
            4 := by
        change (List.map _ bs).length = 4
        rw [List.length_map, h_blen]
      have h_rl := eval_readListLoop_zero 4 bs h_blen
      have h_rd := read_arr_4 _ h_asz
      dsimp only [Array.toList] at h_rd
      refine Eq.trans (congrArg (fun inner =>
        match inner with
        | .error _ => Except.error FaultKind.unsupported
        | .ok sc =>
          match sc.toBits (toMiriSize .i32) with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bits =>
            Except.ok (Val.scalar ⟨.i32, s, (miriScalar .i32 bits).data⟩)) h_rd) ?_
      rw [h_rl]
      dsimp only [Except.bind]
      exact refAllocRead_eq_fromUInt_finish .i32 s bs h_blen
    | i64 =>
      dsimp only [IntWidth.byteSize] at h_blen
      have h_asz :
          (Array.mk (List.map (fun b : BitVec 8 => UInt8.ofNat b.toNat) bs)).size =
            8 := by
        change (List.map _ bs).length = 8
        rw [List.length_map, h_blen]
      have h_rl := eval_readListLoop_zero 8 bs h_blen
      have h_rd := read_arr_8 _ h_asz
      dsimp only [Array.toList] at h_rd
      refine Eq.trans (congrArg (fun inner =>
        match inner with
        | .error _ => Except.error FaultKind.unsupported
        | .ok sc =>
          match sc.toBits (toMiriSize .i64) with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bits =>
            Except.ok (Val.scalar ⟨.i64, s, (miriScalar .i64 bits).data⟩)) h_rd) ?_
      rw [h_rl]
      dsimp only [Except.bind]
      exact refAllocRead_eq_fromUInt_finish .i64 s bs h_blen
    | isize =>
      dsimp only [IntWidth.byteSize] at h_blen
      have h_asz :
          (Array.mk (List.map (fun b : BitVec 8 => UInt8.ofNat b.toNat) bs)).size =
            8 := by
        change (List.map _ bs).length = 8
        rw [List.length_map, h_blen]
      have h_rl := eval_readListLoop_zero 8 bs h_blen
      have h_rd := read_arr_8 _ h_asz
      dsimp only [Array.toList] at h_rd
      refine Eq.trans (congrArg (fun inner =>
        match inner with
        | .error _ => Except.error FaultKind.unsupported
        | .ok sc =>
          match sc.toBits (toMiriSize .isize) with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bits =>
            Except.ok (Val.scalar ⟨.isize, s, (miriScalar .isize bits).data⟩)) h_rd) ?_
      rw [h_rl]
      dsimp only [Except.bind]
      exact refAllocRead_eq_fromUInt_finish .isize s bs h_blen
    | i128 =>
      dsimp only [IntWidth.byteSize] at h_blen
      have h_asz :
          (Array.mk (List.map (fun b : BitVec 8 => UInt8.ofNat b.toNat) bs)).size =
            16 := by
        change (List.map _ bs).length = 16
        rw [List.length_map, h_blen]
      have h_rl := eval_readListLoop_zero 16 bs h_blen
      have h_rd := read_arr_16 _ h_asz
      dsimp only [Array.toList] at h_rd
      refine Eq.trans (congrArg (fun inner =>
        match inner with
        | .error _ => Except.error FaultKind.unsupported
        | .ok sc =>
          match sc.toBits (toMiriSize .i128) with
          | .error _ => Except.error FaultKind.unsupported
          | .ok bits =>
            Except.ok (Val.scalar ⟨.i128, s, (miriScalar .i128 bits).data⟩)) h_rd) ?_
      rw [h_rl]
      dsimp only [Except.bind]
      exact refAllocRead_eq_fromUInt_finish .i128 s bs h_blen

/-- The reference `CoreBuiltin` evaluator (`evalRefCoreBuiltin`) agrees with
`Trusted.MirSemantics.evalCoreBuiltin` across all 20 builtins, destination
types, and argument lists. -/
theorem evalRefCoreBuiltin_eq (builtin : CoreBuiltin) (dstTy : MirTy)
    (args : List Val) :
    evalRefCoreBuiltin builtin dstTy args =
      evalCoreBuiltin builtin dstTy args := by
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
            | nil =>
              exact evalRefBinOp_eq .addWithOverflow (.scalar l) (.scalar r)
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
            | nil =>
              exact evalRefBinOp_eq .subWithOverflow (.scalar l) (.scalar r)
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
            | nil =>
              exact evalRefBinOp_eq .mulWithOverflow (.scalar l) (.scalar r)
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
  | checkedAdd =>
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
            | nil => exact evalRefCheckedArithOp_eq .addWithOverflow dstTy l r
            | cons _ _ => rfl
          | _ => rfl
      | _ => rfl
  | checkedSub =>
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
            | nil => exact evalRefCheckedArithOp_eq .subWithOverflow dstTy l r
            | cons _ _ => rfl
          | _ => rfl
      | _ => rfl
  | checkedMul =>
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
            | nil => exact evalRefCheckedArithOp_eq .mulWithOverflow dstTy l r
            | cons _ _ => rfl
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
  | toLeBytes =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | scalar sv =>
        cases rest with
        | cons _ _ => rfl
        | nil =>
          cases dstTy with
          | array arrElemTy len =>
            cases arrElemTy with
            | int w s =>
              cases w with
              | i8 =>
                cases s with
                | true => rfl
                | false =>
                  dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
                  cases Nat.beq len sv.width.byteSize with
                  | false => rfl
                  | true =>
                    rw [Bool.not_true, ite_false_eq_true, ite_false_eq_true,
                        refAllocScalarToLeBytes_eq]
              | _ => rfl
            | _ => rfl
          | _ => rfl
      | _ => rfl
  | fromLeBytes =>
    cases args with
    | nil => rfl
    | cons a rest =>
      cases a with
      | array arrElemTy elems =>
        cases arrElemTy with
        | int ew es =>
          cases ew with
          | i8 =>
            cases es with
            | true => rfl
            | false =>
              cases rest with
              | cons _ _ => rfl
              | nil =>
                cases dstTy with
                | int w s =>
                  dsimp only [evalRefCoreBuiltin, evalCoreBuiltin]
                  cases h_len : Nat.beq elems.length w.byteSize with
                  | false => rfl
                  | true =>
                    rw [Bool.not_true, ite_false_eq_true, ite_false_eq_true]
                    exact refAllocScalarFromLeBytes_eq w s elems h_len
                | _ => rfl
          | _ => rfl
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
              cases (IntWidth.beq l.width r.width &&
                  (l.signed == r.signed)) with
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
              cases (IntWidth.beq l.width r.width &&
                  (l.signed == r.signed)) with
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
