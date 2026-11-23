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

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# Canonical Type Interner and Codec Proofs (`Anneal.MirCorrespondence.Codec`)

Type-equality reflection, canonical deduplication, round-trip
(`decodeProg_encodeProg_base`), and constructor-preservation proofs.
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
    | char => rfl
    | ordering => rfl
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
    | char => cases b <;> first | rfl | cases h
    | ordering => cases b <;> first | rfl | cases h
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


/-- Anti-laundering guarantee: `encodeStmt` maps `.nop` and only `.nop` to
`.Nop`. -/
theorem encodeStmt_no_dormant_noops_base : EncodeStmtNoDormantNoopsClaim := by
  intro ts s
  cases s <;> constructor <;> intro h <;> first | rfl | cases h

private theorem fromMiriBinOp_toMiriBinOp (op : BinOp) :
    fromMiriBinOp (toMiriBinOp op) = some op := by
  cases op <;> rfl

private theorem toMiriBinOp_inj {a b : BinOp}
    (h : toMiriBinOp a = toMiriBinOp b) : a = b := by
  have ha := fromMiriBinOp_toMiriBinOp a
  rw [h, fromMiriBinOp_toMiriBinOp b] at ha
  injection ha with h_eq
  exact h_eq.symm

private theorem fromMiriUnOp_toMiriUnOp (op : UnOp) :
    fromMiriUnOp (toMiriUnOp op) = some op := by
  cases op <;> rfl

private theorem toMiriUnOp_inj {a b : UnOp}
    (h : toMiriUnOp a = toMiriUnOp b) : a = b := by
  have ha := fromMiriUnOp_toMiriUnOp a
  rw [h, fromMiriUnOp_toMiriUnOp b] at ha
  injection ha with h_eq
  exact h_eq.symm

/-! ### Constructor preservation

`decodeProg_encodeProg` alone would still allow an encoder that permutes
semantic constructors (for example, `.add` ↔ `.addUnchecked`) as long as the
decoder permutes them back. The following lemmas lock the operator, operands,
and destination of every encoded assignment, binary operation, and unary
operation directly on `Miri.MIR.*`. -/

/-- `encodeRvalue` produces `.BinaryOp (toMiriBinOp op) l' r'` exactly when the
source is a `.binaryOp` with the same operator `op` and operands encoding to
`l'` and `r'`. -/
theorem encodeRvalue_binaryOp_iff_base : EncodeRvalueBinaryOpIffClaim := by
  intro ts rv op l' r'
  cases rv with
  | binaryOp op₀ l r =>
    constructor
    · intro h
      injection h with h_op h_l h_r
      exact ⟨l, r, by rw [toMiriBinOp_inj h_op], h_l, h_r⟩
    · intro h
      let ⟨l₁, r₁, h_rv, h_l, h_r⟩ := h
      injection h_rv with h_op h_l₁ h_r₁
      subst h_op; subst h_l₁; subst h_r₁
      dsimp only [encodeRvalue]
      rw [h_l, h_r]
  | cast k _ _ =>
    cases k <;>
      (constructor
       · intro h; cases h
       · intro h; let ⟨_, _, h_rv, _, _⟩ := h; cases h_rv)
  | use _ | unaryOp _ _ | discriminant _ | ref _ _
  | addressOf _ _ | aggregateTuple _ | unsupported =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, _, h_rv, _, _⟩ := h
      cases h_rv

/-- `encodeRvalue` produces `.UnaryOp (toMiriUnOp op) o'` exactly when the
source is a `.unaryOp` with the same operator `op` and an operand encoding to
`o'`. -/
theorem encodeRvalue_unaryOp_iff_base : EncodeRvalueUnaryOpIffClaim := by
  intro ts rv op o'
  cases rv with
  | unaryOp op₀ o =>
    constructor
    · intro h
      injection h with h_op h_o
      exact ⟨o, by rw [toMiriUnOp_inj h_op], h_o⟩
    · intro h
      let ⟨o₁, h_rv, h_o⟩ := h
      injection h_rv with h_op h_o₁
      subst h_op; subst h_o₁
      dsimp only [encodeRvalue]
      rw [h_o]
  | cast k _ _ =>
    cases k <;>
      (constructor
       · intro h; cases h
       · intro h; let ⟨_, h_rv, _⟩ := h; cases h_rv)
  | use _ | binaryOp _ _ _ | discriminant _ | ref _ _
  | addressOf _ _ | aggregateTuple _ | unsupported =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, h_rv, _⟩ := h
      cases h_rv

/-- `encodeStmt` produces `.Assign dst' rv'` exactly when the source is an
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
    | char =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .char acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | ordering =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .ordering acc,
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

private theorem bitVec128_ofNat_toNat_codec (bits : BitVec 128) :
    BitVec.ofNat 128 bits.toNat = bits := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt bits.isLt

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
      cases lit with
      | scalar bits =>
        simp only [encodeOperand, encodeConstOperand, decodeOperand,
          decodeConstOperand, optMap]
        rw [h_dec₁ ts h_s]
        dsimp only [optMap]
        rw [bitVec128_ofNat_toNat_codec bits]
      | zeroSized =>
        simp only [encodeOperand, encodeConstOperand, decodeOperand,
          decodeConstOperand, optMap]
        rw [h_dec₁ ts h_s]

private theorem decodeProjUntilStop_append (acc : List MirTy)
    (proj : List ProjectionElem) :
    SubTable acc (proj.foldl collectProjElem acc) ∧
    (∀ ts rest, SubTable (proj.foldl collectProjElem acc) ts →
      decodeProjUntilStop ts
        (proj.map (encodeProjElem ts) ++ .Downcast none 0 :: rest) =
      some (proj, rest)) := by
  induction proj generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ _ => rfl⟩
  | cons e es ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectProjElem_spec acc e
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectProjElem acc e)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts rest h_s => ?_⟩
    dsimp only [List.map, List.cons_append]
    have h_e := h_dec₁ ts (SubTable.trans h_sub₂ h_s)
    have h_es := h_dec₂ ts rest h_s
    cases e with
    | deref =>
      dsimp only [encodeProjElem, decodeProjUntilStop, decodeProjElem]
      rw [h_es]
    | unsupported =>
      dsimp only [encodeProjElem, decodeProjUntilStop, decodeProjElem]
      rw [h_es]
    | field idx ty =>
      dsimp only [encodeProjElem, decodeProjElem, optMap] at h_e
      dsimp only [encodeProjElem, decodeProjUntilStop, decodeProjElem, optMap]
      cases h_g : MirSemantics.getElem? ts (lookupTyId ts ty) with
      | none => rw [h_g] at h_e; cases h_e
      | some ty' =>
        rw [h_g] at h_e
        dsimp only [optMap] at h_e
        dsimp only [optMap]
        injection h_e with h_e_eq
        rw [h_e_eq, h_es]

private theorem collectOperandElems_spec (acc : List MirTy) (op : Operand) :
    SubTable acc (collectOperand acc op) ∧
    (∀ ts rest, SubTable (collectOperand acc op) ts →
      decodeOperandElems ts (encodeOperandElems ts op ++ rest) =
        some (op, rest)) := by
  cases op with
  | copy p =>
    cases p with
    | mk locId proj =>
      let ⟨h_sub, h_dec⟩ := decodeProjUntilStop_append acc proj
      refine ⟨h_sub, fun ts rest h_s => ?_⟩
      simp only [encodeOperandElems, List.cons_append, List.nil_append,
        List.append_assoc, decodeOperandElems, optMap]
      rw [h_dec ts rest h_s]
  | move p =>
    cases p with
    | mk locId proj =>
      let ⟨h_sub, h_dec⟩ := decodeProjUntilStop_append acc proj
      refine ⟨h_sub, fun ts rest h_s => ?_⟩
      simp only [encodeOperandElems, List.cons_append, List.nil_append,
        List.append_assoc, decodeOperandElems, optMap]
      rw [h_dec ts rest h_s]
  | constant c =>
    cases c with
    | mk ty lit =>
      let ⟨h_sub, h_dec⟩ := collectTy_spec acc ty
      refine ⟨h_sub, fun ts rest h_s => ?_⟩
      cases lit with
      | scalar bits =>
        simp only [encodeOperandElems, List.cons_append,
          List.nil_append, decodeOperandElems, optMap]
        rw [h_dec ts h_s]
        dsimp only [optMap]
        rw [bitVec128_ofNat_toNat_codec bits]
      | zeroSized =>
        simp only [encodeOperandElems, List.cons_append,
          List.nil_append, decodeOperandElems, optMap]
        rw [h_dec ts h_s]

private theorem encodeOperandListElems_nonnil_of_cons (ts : List MirTy)
    (op : Operand) (ops : List Operand) :
    ∃ x xs, encodeOperandListElems ts (op :: ops) = x :: xs := by
  cases op with
  | copy _ => exact ⟨_, _, rfl⟩
  | move _ => exact ⟨_, _, rfl⟩
  | constant c =>
    cases c with
    | mk ty lit =>
      cases lit with
      | scalar _ => exact ⟨_, _, rfl⟩
      | zeroSized => exact ⟨_, _, rfl⟩

private theorem encodeOperandListElems_length_le (ts : List MirTy)
    (ops : List Operand) :
    ops.length ≤ (encodeOperandListElems ts ops).length := by
  induction ops with
  | nil => exact Nat.le_refl 0
  | cons op ops ih =>
    dsimp only [encodeOperandListElems]
    have h_len : 1 ≤ (encodeOperandElems ts op).length := by
      cases op with
      | copy _ => exact Nat.succ_le_succ (Nat.zero_le _)
      | move _ => exact Nat.succ_le_succ (Nat.zero_le _)
      | constant c =>
        cases c with
        | mk ty lit => cases lit <;> exact Nat.le_refl 1
    rw [List.length_append, Nat.add_comm (encodeOperandElems ts op).length]
    exact Nat.add_le_add ih h_len

private theorem collectOperandListElems_spec (ops : List Operand)
    (acc : List MirTy) :
    SubTable acc (ops.foldl collectOperand acc) ∧
    (∀ ts fuel, ops.length ≤ fuel →
      SubTable (ops.foldl collectOperand acc) ts →
      decodeOperandListLoop fuel ts (encodeOperandListElems ts ops) =
        some ops) := by
  induction ops generalizing acc with
  | nil =>
    exact ⟨SubTable.refl acc, fun _ fuel _ _ => by cases fuel <;> rfl⟩
  | cons op rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectOperandElems_spec acc op
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectOperand acc op)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts fuel h_le h_s => ?_⟩
    cases fuel with
    | zero => cases h_le
    | succ fuel' =>
      let ⟨x, xs, h_cons⟩ :=
        encodeOperandListElems_nonnil_of_cons ts op rest
      rw [h_cons]
      simp only [decodeOperandListLoop]
      rw [← h_cons]
      dsimp only [encodeOperandListElems]
      rw [h_dec₁ ts (encodeOperandListElems ts rest) (SubTable.trans h_sub₂ h_s)]
      dsimp only [optMap]
      rw [h_dec₂ ts fuel' (Nat.le_of_succ_le_succ h_le) h_s]

private theorem natToMutability_mutabilityToNat (m : Mutability) :
    natToMutability (mutabilityToNat m) = some m := by
  cases m <;> rfl

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
    rw [fromMiriBinOp_toMiriBinOp op, h_dec₁ ts (SubTable.trans h_sub₂ h_s),
      h_dec₂ ts h_s]
  | unaryOp op opnd =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc opnd
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [fromMiriUnOp_toMiriUnOp op, h_dec ts h_s]
  | cast k opnd ty =>
    cases k with
    | intToInt =>
      let ⟨h_sub₁, h_dec₁⟩ := collectOperand_spec acc opnd
      let ⟨h_sub₂, h_dec₂⟩ := collectTy_spec (collectOperand acc opnd) ty
      refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
      dsimp only [encodeRvalue, decodeRvalue]
      rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
      rfl
    | unsupported =>
      let ⟨h_sub₁, h_dec₁⟩ := collectOperandElems_spec acc opnd
      let ⟨h_sub₂, h_dec₂⟩ := collectTy_spec (collectOperand acc opnd) ty
      refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
      simp only [encodeRvalue, decodeRvalue, decodeCopyForDeref]
      rw [← List.append_nil (encodeOperandElems ts opnd),
        h_dec₁ ts [] (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
  | discriminant p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
    rfl
  | ref m p =>
    let ⟨h_sub, h_dec⟩ := foldl_collect_mapOption_spec collectProjElem
      encodeProjElem decodeProjElem collectProjElem_spec acc p.projection
    refine ⟨h_sub, fun ts h_s => ?_⟩
    simp only [encodeRvalue, decodeRvalue, decodeCopyForDeref, optMap2]
    rw [natToMutability_mutabilityToNat m, h_dec ts h_s]
  | addressOf m p =>
    let ⟨h_sub, h_dec⟩ := foldl_collect_mapOption_spec collectProjElem
      encodeProjElem decodeProjElem collectProjElem_spec acc p.projection
    refine ⟨h_sub, fun ts h_s => ?_⟩
    simp only [encodeRvalue, decodeRvalue, decodeCopyForDeref, optMap2]
    rw [natToMutability_mutabilityToNat m, h_dec ts h_s]
  | aggregateTuple ops =>
    let ⟨h_sub, h_dec⟩ := collectOperandListElems_spec ops acc
    refine ⟨h_sub, fun ts h_s => ?_⟩
    simp only [encodeRvalue, decodeRvalue, decodeCopyForDeref, optMap]
    rw [h_dec ts (encodeOperandListElems ts ops).length
      (encodeOperandListElems_length_le ts ops) h_s]
  | unsupported => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩

theorem decodeCopyForDeref_not_discr_intCast {ts : List MirTy}
    {pl : Miri.MIR.Place} {rv : Rvalue}
    (h : decodeCopyForDeref ts pl = some rv) :
    (∀ src, rv ≠ .discriminant src) ∧
    (∀ op ty, rv ≠ .cast .intToInt op ty) := by
  cases pl with
  | mk tag elems =>
    cases elems with
    | mk xs =>
      cases tag with
      | zero =>
        simp only [decodeCopyForDeref] at h
        cases h_e : (Array.mk xs).isEmpty <;> rw [h_e] at h
        · cases h
        · injection h with h_eq; subst h_eq
          exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
      | succ tag =>
        cases tag with
        | zero =>
          simp only [decodeCopyForDeref] at h
          cases xs with
          | nil => cases h
          | cons e rest =>
            cases e with
            | OpaqueCast tyId =>
              dsimp only at h
              cases h_oe : decodeOperandElems ts rest with
              | none => rw [h_oe] at h; cases h
              | some pair =>
                rw [h_oe] at h
                cases pair with
                | mk op' rem =>
                  cases rem with
                  | cons _ _ => cases h
                  | nil =>
                    cases h_ty : MirSemantics.getElem? ts tyId with
                    | none => rw [h_ty] at h; cases h
                    | some _ =>
                      rw [h_ty] at h
                      injection h with h_eq; subst h_eq
                      exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
            | _ => cases h
        | succ tag =>
          cases tag with
          | zero =>
            simp only [decodeCopyForDeref, optMap2] at h
            cases xs with
            | nil => cases h
            | cons e rest =>
              cases e with
              | OpaqueCast mCode =>
                cases rest with
                | nil => cases h
                | cons e2 rest2 =>
                  cases e2 with
                  | Index _ =>
                    dsimp only at h
                    cases h_m : natToMutability mCode <;> rw [h_m] at h
                    · cases h
                    · cases h_p : mapOption (decodeProjElem ts) rest2 <;> rw [h_p] at h
                      · cases h
                      · injection h with h_eq; subst h_eq
                        exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
                  | _ => cases h
              | _ => cases h
          | succ tag =>
            cases tag with
            | zero =>
              simp only [decodeCopyForDeref, optMap2] at h
              cases xs with
              | nil => cases h
              | cons e rest =>
                cases e with
                | OpaqueCast mCode =>
                  cases rest with
                  | nil => cases h
                  | cons e2 rest2 =>
                    cases e2 with
                    | Index _ =>
                      dsimp only at h
                      cases h_m : natToMutability mCode <;> rw [h_m] at h
                      · cases h
                      · cases h_p : mapOption (decodeProjElem ts) rest2 <;> rw [h_p] at h
                        · cases h
                        · injection h with h_eq; subst h_eq
                          exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
                    | _ => cases h
                | _ => cases h
            | succ tag =>
              cases tag with
              | zero =>
                simp only [decodeCopyForDeref, optMap] at h
                cases h_l : decodeOperandListLoop xs.length ts xs <;>
                  rw [h_l] at h
                · cases h
                · injection h with h_eq; subst h_eq
                  exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
              | succ _ =>
                simp only [decodeCopyForDeref] at h
                cases h

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

private theorem decodeSwitchTargets_encode (targets : SwitchTargets) :
    decodeSwitchTargets (encodeSwitchTargets targets) = targets := by
  cases targets with
  | mk branches otherwise =>
    dsimp only [encodeSwitchTargets, decodeSwitchTargets]
    induction branches with
    | nil => rfl
    | cons b bs ih =>
      dsimp only [List.map]
      rw [bitVec128_ofNat_toNat_codec b.1]
      injection ih with h_b _
      rw [h_b]

private theorem decodeAssertConst_encode (msg : AssertKind) :
    decodeAssertConst (encodeAssertConst msg) = some msg := by
  cases msg with
  | overflow op =>
    simp only [encodeAssertConst, decodeAssertConst, optMap]
    rw [fromMiriBinOp_toMiriBinOp op]
  | overflowNeg | divByZero | remByZero | boundsCheck
  | misalignedPtrDeref | nullPtrDeref | unsupported => rfl

private theorem fromMiriUnwindAction_toMiri (u : UnwindAction) :
    fromMiriUnwindAction (toMiriUnwindAction u) = some u := by
  cases u <;> rfl

private theorem collectCallArgs_spec (acc : List MirTy) (args : List Operand) :
    SubTable acc (args.foldl collectOperand acc) ∧
    (∀ ts, SubTable (args.foldl collectOperand acc) ts →
      decodeCallArgs ts
        (args.map (fun a => Miri.MIR.InlineAsmOperand.In (.Reg .X86 "")
          (encodeOperand ts a))) = some args) := by
  induction args generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons a rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectOperand_spec acc a
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectOperand acc a)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    simp only [List.map, decodeCallArgs, optMap2]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

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
    rw [h_dec ts h_s, decodeSwitchTargets_encode targets]
    rfl
  | assert c exp msg t u =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc c
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeTerminator, decodeTerminator]
    rw [fromMiriUnwindAction_toMiri u]
    have h_x86 : (Miri.MIR.InlineAsmArch.X86 == .X86 && "" == "") = true := rfl
    dsimp only
    simp only [h_x86, ite_true, optMap2]
    rw [h_dec ts h_s, decodeAssertConst_encode msg]
  | call callee args dst t u =>
    let ⟨h_sub₁, h_dec₁⟩ := collectCallArgs_spec acc args
    let ⟨h_sub₂, h_dec₂⟩ :=
      collectPlace_spec (args.foldl collectOperand acc) dst
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    have h_x86 : (Miri.MIR.InlineAsmArch.X86 == .X86 && "" == "") = true := rfl
    cases t with
    | none =>
      dsimp only [encodeTerminator, decodeTerminator]
      rw [fromMiriUnwindAction_toMiri u]
      dsimp only
      simp only [h_x86, ite_true, optMap2]
      rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    | some target =>
      dsimp only [encodeTerminator, decodeTerminator]
      rw [fromMiriUnwindAction_toMiri u]
      dsimp only
      simp only [h_x86, ite_true, optMap2]
      rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

private theorem collectStmtEntries_spec (acc : List MirTy)
    (stmts : List StatementKind) :
    SubTable acc (stmts.foldl collectStmt acc) ∧
    (∀ ts, SubTable (stmts.foldl collectStmt acc) ts →
      mapOption (fun st => decodeStmt ts st.kind)
        (stmts.map (fun s =>
          ({ sourceInfo := ⟨⟨0⟩, 0⟩, kind := encodeStmt ts s } :
            Miri.MIR.Statement))) = some stmts) := by
  induction stmts generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons s rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectStmt_spec acc s
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectStmt acc s)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [List.map, mapOption]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl

theorem collectBasicBlock_spec (acc : List MirTy) (bb : BasicBlock) :
    SubTable acc (collectBasicBlock acc bb) ∧
    (∀ ts, SubTable (collectBasicBlock acc bb) ts →
      decodeBasicBlock ts (encodeBasicBlock ts bb) = some bb) := by
  cases bb with
  | mk stmts term cleanup =>
    let ⟨h_sub₁, h_dec₁⟩ := collectStmtEntries_spec acc stmts
    let ⟨h_sub₂, h_dec₂⟩ :=
      collectTerminator_spec (stmts.foldl collectStmt acc) term
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeBasicBlock, decodeBasicBlock]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl

theorem collectBody_spec (acc : List MirTy) (b : Body) :
    SubTable acc (collectBody acc b) ∧
    (∀ ts, SubTable (collectBody acc b) ts →
      decodeBody ts (encodeBodyMeta b) (encodeBody ts b) = some b) := by
  cases b with
  | mk argCount locals bbs isUnsafe identity =>
    let ⟨h_sub₁, h_dec₁⟩ := collectTyList_spec acc locals
    let ⟨h_sub₂, h_dec₂⟩ := foldl_collect_mapOption_spec collectBasicBlock
      encodeBasicBlock decodeBasicBlock collectBasicBlock_spec
      (collectTyList acc locals) bbs
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeBody, encodeBodyMeta, decodeBody]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
    rfl

private theorem collectBodies_spec (acc : List MirTy) (bodies : List Body) :
    SubTable acc (bodies.foldl collectBody acc) ∧
    (∀ ts, SubTable (bodies.foldl collectBody acc) ts →
      decodeBodies ts (bodies.map (encodeBody ts))
        (bodies.map encodeBodyMeta) = some bodies) := by
  induction bodies generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons b rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectBody_spec acc b
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectBody acc b)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [List.map, decodeBodies, optMap2]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

/-- Unconditional global anti-laundering theorem: every `p : Program` with
inline `MirTy` round-trips through `encodeToMiri` and `decodeProg` with zero
preconditions, including its target `pointerWidthBits`, `mirProfileVersion`,
and `scope`. -/
theorem decodeProg_encodeProg_base : DecodeProgEncodeProgClaim := by
  intro p
  cases p with
  | mk bodies entryDefId pointerWidthBits mirProfileVersion scope =>
    dsimp only [encodeToMiri, decodeProg, collectProgTypes]
    let ⟨_, h_dec⟩ := collectBodies_spec [] bodies
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
    | char =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .char acc h
    | ordering =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .ordering acc h
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
  | cast _ op ty =>
    exact collectTy_canonical (collectOperand acc op) ty
      (collectOperand_canonical acc op h)
  | discriminant p | ref _ p | addressOf _ p =>
    exact collectPlace_canonical acc p h
  | aggregateTuple ops =>
    exact foldl_preserve (fun ts => typesAreCanonical ts = true) collectOperand
      collectOperand_canonical ops h
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
  | call _ args dst _ _ =>
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
`(encodeToMiri p).types` contains no duplicate `MirTy` entries, guaranteeing
that nominal `TyId` equality in `lean-miri` (`assertSameType`,
`assertRvalueLayout`) agrees with structural `MirTy` equality. -/
theorem encodeProg_types_canonical_base : EncodeProgTypesCanonicalClaim :=
  fun p =>
    foldl_preserve (fun ts => typesAreCanonical ts = true) collectBody
      collectBody_canonical p.bodies rfl

end Anneal.MirCorrespondence
