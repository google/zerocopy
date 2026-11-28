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
import Init.Data.Char.Basic
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Ops
import Trusted.MirSemantics.Enum
import Trusted.MirSemantics.Layout
import Trusted.MirSemantics.Memory
import Trusted.MirSemantics.Bytes
import Trusted.MirSemantics.State
import Anneal.MiniRust.Syntax
import Anneal.MiniRust.Memory
import Anneal.MiniRust.Machine
import Anneal.MiniRust.Translate

namespace Anneal.MiniRust

open Trusted.MirAst
open Trusted.MirSemantics

/-!
# State Relation and Representation Equivalence (`Anneal.MiniRust.Relation`)

Couples `Trusted.MirSemantics.State` with `Anneal.MiniRust.Machine` via
`StateRel exact p s m`, proves little-endian byte-codec and value-representation
equivalence against `Trusted.MirSemantics.Bytes` & `Trusted.MirSemantics.Enum`,
and proves entry initialization (`init_stateRel`) across `initMrMachine` and
the `initBlock` `StorageLive` prologue.
-/

/-! ## Core `IntWidth`, `BitVec`, and `IntType` Bridge Lemmas -/

theorem bv_toNat_ofNat (n v : Nat) :
    (BitVec.ofNat n v).toNat = Nat.mod v (Nat.pow 2 n) := rfl

theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

theorem nat_mod_one (a : Nat) : Nat.mod a 1 = 0 :=
  Nat.mod_one a

theorem if_false_eq_true {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

theorem if_true_eq_true {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

theorem if_not_true {α : Type} (a b : α) :
    (if (!true) = true then a else b) = b := rfl

theorem if_not_false {α : Type} (a b : α) :
    (if (!false) = true then a else b) = a := rfl

theorem list_replicate_add {α : Type} (a : α) (m n : Nat) :
    List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
    rw [Nat.succ_add]
    dsimp only [List.replicate, List.cons_append]
    rw [ih]

theorem char_ofNat_toNat (c : Char) : Char.ofNat c.toNat = c := by
  cases c with
  | mk v hv =>
    dsimp only [Char.ofNat, Char.toNat, Char.ofNatAux]
    have hvalid : v.toNat.isValidChar := hv
    simp only [hvalid, dite_true]
    cases v with
    | ofBitVec bv =>
      cases bv with
      | ofFin fv =>
        cases fv with
        | mk vn hvn =>
          rfl

theorem bool_cases (b : Bool) : b = false ∨ b = true := by
  cases b with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

theorem intWidth_eq_of_beq {a b : IntWidth} (h : IntWidth.beq a b = true) :
    a = b := by
  cases a with
  | i8 => cases b with | i8 => rfl | i16 => cases h | i32 => cases h | i64 => cases h | i128 => cases h | isize => cases h
  | i16 => cases b with | i8 => cases h | i16 => rfl | i32 => cases h | i64 => cases h | i128 => cases h | isize => cases h
  | i32 => cases b with | i8 => cases h | i16 => cases h | i32 => rfl | i64 => cases h | i128 => cases h | isize => cases h
  | i64 => cases b with | i8 => cases h | i16 => cases h | i32 => cases h | i64 => rfl | i128 => cases h | isize => cases h
  | i128 => cases b with | i8 => cases h | i16 => cases h | i32 => cases h | i64 => cases h | i128 => rfl | isize => cases h
  | isize => cases b with | i8 => cases h | i16 => cases h | i32 => cases h | i64 => cases h | i128 => cases h | isize => rfl

theorem bool_eq_of_beq {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a with
  | false => cases b with | false => rfl | true => cases h
  | true => cases b with | false => cases h | true => rfl

theorem natList_eq_of_beq : ∀ {l1 l2 : List Nat}, natListBeq l1 l2 = true → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    dsimp only [natListBeq] at h
    cases hab : Nat.beq a b with
    | false => rw [hab] at h; cases h
    | true =>
      rw [hab] at h
      rw [Nat.eq_of_beq_eq_true hab, natList_eq_of_beq h]

theorem enumTagRepr_eq_of_beq {a b : EnumTagRepr}
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
      dsimp only [EnumTagRepr.beq] at h
      cases hw : IntWidth.beq w1 w2 with
      | false => rw [hw] at h; cases h
      | true =>
        rw [hw] at h
        rw [intWidth_eq_of_beq hw, bool_eq_of_beq h]

theorem enumTy_eq_of_beq {a b : EnumTy} (h : EnumTy.beq a b = true) : a = b := by
  cases a with
  | mk id1 dw1 ds1 tr1 dl1 =>
    cases b with
    | mk id2 dw2 ds2 tr2 dl2 =>
      dsimp only [EnumTy.beq] at h
      cases h1 : Nat.beq id1 id2 with
      | false => rw [h1] at h; cases h
      | true =>
        cases h2 : IntWidth.beq dw1 dw2 with
        | false => rw [h1, h2] at h; cases h
        | true =>
          cases h3 : (ds1 == ds2) with
          | false => rw [h1, h2, h3] at h; cases h
          | true =>
            cases h4 : EnumTagRepr.beq tr1 tr2 with
            | false => rw [h1, h2, h3, h4] at h; cases h
            | true =>
              rw [h1, h2, h3, h4] at h
              rw [Nat.eq_of_beq_eq_true h1, intWidth_eq_of_beq h2,
                bool_eq_of_beq h3, enumTagRepr_eq_of_beq h4,
                natList_eq_of_beq h]

theorem structLayout_eq_of_beq {a b : StructLayout}
    (h : StructLayout.beq a b = true) : a = b := by
  cases a with
  | mk id1 sz1 al1 offs1 =>
    cases b with
    | mk id2 sz2 al2 offs2 =>
      dsimp only [StructLayout.beq] at h
      cases h1 : Nat.beq id1 id2 with
      | false => rw [h1] at h; cases h
      | true =>
        cases h2 : Nat.beq sz1 sz2 with
        | false => rw [h1, h2] at h; cases h
        | true =>
          cases h3 : Nat.beq al1 al2 with
          | false => rw [h1, h2, h3] at h; cases h
          | true =>
            rw [h1, h2, h3] at h
            rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
              Nat.eq_of_beq_eq_true h3, natList_eq_of_beq h]

mutual
theorem mirTy_eq_of_beq : ∀ {a b : MirTy}, MirTy.beq a b = true → a = b
  | .bool, b, h => by cases b <;> first | rfl | cases h
  | .int w1 s1, b, h => by
    cases b with
    | int w2 s2 =>
      dsimp only [MirTy.beq] at h
      cases hw : IntWidth.beq w1 w2 with
      | false => rw [hw] at h; cases h
      | true =>
        rw [hw] at h
        rw [intWidth_eq_of_beq hw, bool_eq_of_beq h]
    | _ => cases h
  | .unit, b, h => by cases b <;> first | rfl | cases h
  | .never, b, h => by cases b <;> first | rfl | cases h
  | .char, b, h => by cases b <;> first | rfl | cases h
  | .str, b, h => by cases b <;> first | rfl | cases h
  | .ordering, b, h => by cases b <;> first | rfl | cases h
  | .enum e1, b, h => by
    cases b with
    | enum e2 => exact congrArg MirTy.enum (enumTy_eq_of_beq h)
    | _ => cases h
  | .ref m1 t1, b, h => by
    cases b with
    | ref m2 t2 =>
      cases m1 <;> cases m2 <;>
        first | exact congrArg _ (mirTy_eq_of_beq h) | cases h
    | _ => cases h
  | .rawPtr m1 t1, b, h => by
    cases b with
    | rawPtr m2 t2 =>
      cases m1 <;> cases m2 <;>
        first | exact congrArg _ (mirTy_eq_of_beq h) | cases h
    | _ => cases h
  | .tuple ts1, b, h => by
    cases b with
    | tuple ts2 => exact congrArg MirTy.tuple (mirTyList_eq_of_beq h)
    | _ => cases h
  | .slice t1, b, h => by
    cases b with
    | slice t2 => exact congrArg MirTy.slice (mirTy_eq_of_beq h)
    | _ => cases h
  | .array e1 n1, b, h => by
    cases b with
    | array e2 n2 =>
      dsimp only [MirTy.beq] at h
      cases hn : Nat.beq n1 n2 with
      | false => rw [hn] at h; cases h
      | true =>
        rw [hn] at h
        rw [Nat.eq_of_beq_eq_true hn, mirTy_eq_of_beq h]
    | _ => cases h
  | .range t1, b, h => by
    cases b with
    | range t2 => exact congrArg MirTy.range (mirTy_eq_of_beq h)
    | _ => cases h
  | .rangeTo t1, b, h => by
    cases b with
    | rangeTo t2 => exact congrArg MirTy.rangeTo (mirTy_eq_of_beq h)
    | _ => cases h
  | .rangeFrom t1, b, h => by
    cases b with
    | rangeFrom t2 => exact congrArg MirTy.rangeFrom (mirTy_eq_of_beq h)
    | _ => cases h
  | .option t1, b, h => by
    cases b with
    | option t2 => exact congrArg MirTy.option (mirTy_eq_of_beq h)
    | _ => cases h
  | .vec t1, b, h => by
    cases b with
    | vec t2 => exact congrArg MirTy.vec (mirTy_eq_of_beq h)
    | _ => cases h
  | .box t1, b, h => by
    cases b with
    | box t2 => exact congrArg MirTy.box (mirTy_eq_of_beq h)
    | _ => cases h
  | .struct_ l1 fs1, b, h => by
    cases b with
    | struct_ l2 fs2 =>
      dsimp only [MirTy.beq] at h
      cases hl : StructLayout.beq l1 l2 with
      | false => rw [hl] at h; cases h
      | true =>
        rw [hl] at h
        rw [structLayout_eq_of_beq hl, mirTyList_eq_of_beq h]
    | _ => cases h
  | .unsupported, b, h => by cases b <;> first | rfl | cases h

theorem mirTyList_eq_of_beq : ∀ {l1 l2 : List MirTy}, MirTy.beqList l1 l2 = true → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    dsimp only [MirTy.beqList] at h
    cases hab : MirTy.beq a b with
    | false => rw [hab] at h; cases h
    | true =>
      rw [hab] at h
      rw [mirTy_eq_of_beq hab, mirTyList_eq_of_beq h]
end

theorem checkVal_ty_eq {v : Val} {ty : MirTy} (h : checkVal v ty = true) :
    v.ty? = some ty := by
  dsimp only [checkVal] at h
  cases hty : v.ty? with
  | none => rw [hty] at h; cases h
  | some t =>
    rw [hty] at h
    rw [mirTy_eq_of_beq h]

theorem bv_eq_of_toNat_eq {n : Nat} {a b : BitVec n} (h : a.toNat = b.toNat) :
    a = b := by
  cases a with | ofFin fa =>
  cases b with | ofFin fb =>
  cases fa; cases fb; dsimp only [BitVec.toNat] at h; subst h; rfl

theorem list_length_map {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => dsimp only [List.map, List.length]; rw [ih]

theorem nat_beq_eq_true_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

theorem nat_blt_eq_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

theorem nat_lt_of_blt_eq_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem nat_mod_succ_eq (n m : Nat) :
    Nat.mod (Nat.succ n) m = Nat.mod (Nat.mod n m + 1) m := by
  have h1 : m * Nat.div n m + Nat.mod n m = n := Nat.div_add_mod n m
  have h2 : Nat.succ n = m * Nat.div n m + (Nat.mod n m + 1) := by
    rw [← Nat.add_assoc, h1]
  rw [h2]
  exact nat_mul_add_mod_local m (Nat.div n m) (Nat.mod n m + 1)

theorem nat_mod_self_local (m : Nat) : Nat.mod m m = 0 := by
  have h := nat_mul_add_mod_local m 1 0
  rw [Nat.mul_one, Nat.add_zero] at h
  exact h

theorem nat_mod_mod_local (a m : Nat) (hm : 0 < m) :
    Nat.mod (Nat.mod a m) m = Nat.mod a m :=
  Nat.mod_eq_of_lt (Nat.mod_lt a hm)

theorem nat_sub_sub_self_local {a b : Nat} (h : a ≤ b) : b - (b - a) = a := by
  have h1 : b - a + a = b := Nat.sub_add_cancel h
  have h2 : (b - a + a) - (b - a) = a := by
    rw [Nat.add_comm]
    exact Nat.add_sub_cancel a (b - a)
  rw [h1] at h2
  exact h2

theorem int_ofNat_zero_le (n : Nat) : (0 : Int) ≤ Int.ofNat n :=
  Int.NonNeg.mk n

theorem int_ofNat_le_ofNat {a b : Nat} (h : a ≤ b) : Int.ofNat a ≤ Int.ofNat b := by
  cases a with
  | zero => exact Int.NonNeg.mk b
  | succ a' =>
    change Int.NonNeg (Int.subNatNat b (Nat.succ a'))
    dsimp only [Int.subNatNat]
    rw [Nat.sub_eq_zero_of_le h]
    exact Int.NonNeg.mk (b - Nat.succ a')

theorem int_le_of_ofNat_le_ofNat {a b : Nat} (h : Int.ofNat a ≤ Int.ofNat b) : a ≤ b := by
  cases a with
  | zero => exact Nat.zero_le b
  | succ a' =>
    have h1 : Int.NonNeg (Int.subNatNat b (Nat.succ a')) := h
    dsimp only [Int.subNatNat] at h1
    cases hd : Nat.succ a' - b with
    | zero => exact Nat.le_of_sub_eq_zero hd
    | succ k => rw [hd] at h1; cases h1

theorem int_ofNat_lt_ofNat {a b : Nat} (h : a < b) : Int.ofNat a < Int.ofNat b :=
  int_ofNat_le_ofNat h

theorem int_lt_of_ofNat_lt_ofNat {a b : Nat} (h : Int.ofNat a < Int.ofNat b) : a < b :=
  int_le_of_ofNat_le_ofNat h

theorem int_neg_nonpos (n : Nat) : Neg.neg (Int.ofNat n) ≤ (0 : Int) := by
  cases n with
  | zero => exact Int.NonNeg.mk 0
  | succ k =>
    change Int.NonNeg (Int.ofNat (0 + Nat.succ k))
    exact Int.NonNeg.mk (0 + Nat.succ k)

theorem int_negSucc_le_negSucc {a b : Nat} (h : b ≤ a) : Int.negSucc a ≤ Int.negSucc b := by
  change Int.NonNeg (Int.subNatNat (Nat.succ a) (Nat.succ b))
  dsimp only [Int.subNatNat]
  rw [Nat.sub_eq_zero_of_le (Nat.succ_le_succ h)]
  exact Int.NonNeg.mk (Nat.succ a - Nat.succ b)

theorem int_le_of_negSucc_le_negSucc {a b : Nat} (h : Int.negSucc a ≤ Int.negSucc b) : b ≤ a := by
  have h1 : Int.NonNeg (Int.subNatNat (Nat.succ a) (Nat.succ b)) := h
  dsimp only [Int.subNatNat] at h1
  cases hd : Nat.succ b - Nat.succ a with
  | zero => exact Nat.le_of_succ_le_succ (Nat.le_of_sub_eq_zero hd)
  | succ k => rw [hd] at h1; cases h1

theorem int_negSucc_le_ofNat (a b : Nat) : Int.negSucc a ≤ Int.ofNat b :=
  Int.NonNeg.mk (b + Nat.succ a)

theorem int_ofNat_not_le_negSucc (a b : Nat) (h : Int.ofNat a ≤ Int.negSucc b) : False := by
  cases a with
  | zero => cases h
  | succ k => cases h

theorem int_le_refl (a : Int) : a ≤ a := by
  cases a with
  | ofNat n => exact int_ofNat_le_ofNat (Nat.le_refl n)
  | negSucc n => exact int_negSucc_le_negSucc (Nat.le_refl n)

theorem int_le_trans {a b c : Int} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a with
  | ofNat m =>
    cases b with
    | negSucc _ => exact False.elim (int_ofNat_not_le_negSucc _ _ hab)
    | ofNat k =>
      cases c with
      | negSucc _ => exact False.elim (int_ofNat_not_le_negSucc _ _ hbc)
      | ofNat p =>
        exact int_ofNat_le_ofNat (Nat.le_trans (int_le_of_ofNat_le_ofNat hab)
          (int_le_of_ofNat_le_ofNat hbc))
  | negSucc m =>
    cases c with
    | ofNat p => exact int_negSucc_le_ofNat m p
    | negSucc p =>
      cases b with
      | ofNat k => exact False.elim (int_ofNat_not_le_negSucc _ _ hbc)
      | negSucc k =>
        exact int_negSucc_le_negSucc (Nat.le_trans (int_le_of_negSucc_le_negSucc hbc)
          (int_le_of_negSucc_le_negSucc hab))

theorem int_le_antisymm {a b : Int} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | negSucc _ => exact False.elim (int_ofNat_not_le_negSucc _ _ hab)
    | ofNat k =>
      rw [Nat.le_antisymm (int_le_of_ofNat_le_ofNat hab) (int_le_of_ofNat_le_ofNat hba)]
  | negSucc m =>
    cases b with
    | ofNat _ => exact False.elim (int_ofNat_not_le_negSucc _ _ hba)
    | negSucc k =>
      rw [Nat.le_antisymm (int_le_of_negSucc_le_negSucc hba) (int_le_of_negSucc_le_negSucc hab)]

theorem int_neg_le_neg {a b : Int} (h : a ≤ b) : Neg.neg b ≤ Neg.neg a := by
  cases a with
  | ofNat m =>
    cases b with
    | negSucc _ => exact False.elim (int_ofNat_not_le_negSucc _ _ h)
    | ofNat k =>
      have hle := int_le_of_ofNat_le_ofNat h
      cases m with
      | zero => exact int_neg_nonpos k
      | succ m' =>
        cases k with
        | zero => cases hle
        | succ k' => exact int_negSucc_le_negSucc (Nat.le_of_succ_le_succ hle)
  | negSucc m =>
    cases b with
    | ofNat k =>
      cases k with
      | zero => exact int_ofNat_zero_le (Nat.succ m)
      | succ k' => exact int_negSucc_le_ofNat k' (Nat.succ m)
    | negSucc k =>
      exact int_ofNat_le_ofNat (Nat.succ_le_succ (int_le_of_negSucc_le_negSucc h))

theorem int_ofNat_sub_ofNat_lt {a b : Nat} (h : a < b) :
    Int.ofNat a - Int.ofNat b = Int.negSucc (b - a - 1) := by
  cases b with
  | zero => cases h
  | succ b' =>
    change Int.subNatNat a (Nat.succ b') = Int.negSucc (Nat.succ b' - a - 1)
    dsimp only [Int.subNatNat]
    cases hd : Nat.succ b' - a with
    | zero => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_sub_eq_zero hd) h)
    | succ k => rfl

theorem int_ofNat_sub_le {a b c : Nat} (ha : a ≤ b) (hb : b < c) :
    Neg.neg (Int.ofNat (c - a)) ≤ Int.ofNat b - Int.ofNat c := by
  rw [int_ofNat_sub_ofNat_lt hb]
  have hpos : 0 < c - a := Nat.sub_pos_of_lt (Nat.lt_of_le_of_lt ha hb)
  cases hca : c - a with
  | zero => rw [hca] at hpos; cases hpos
  | succ m =>
    change Int.negSucc m ≤ Int.negSucc (c - b - 1)
    apply int_negSucc_le_negSucc
    have hle1 : c - b ≤ c - a := Nat.sub_le_sub_left ha c
    rw [hca] at hle1
    exact Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_of_eq (Nat.sub_add_cancel (Nat.sub_pos_of_lt hb))) hle1)

theorem int_sub_lt_zero_of_lt {a b : Nat} (h : a < b) :
    Int.ofNat a - Int.ofNat b < (0 : Int) := by
  rw [int_ofNat_sub_ofNat_lt h]
  cases hd : b - a - 1 with
  | zero => exact Int.NonNeg.mk 0
  | succ k => exact int_negSucc_le_ofNat k 0

theorem int_sub_self_negSucc (m k : Nat) (h : Nat.succ k ≤ m) :
    Int.ofNat (m - Nat.succ k) - Int.ofNat m = Int.negSucc k := by
  have hlt : m - Nat.succ k < m :=
    Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) h) (Nat.zero_lt_succ k)
  rw [int_ofNat_sub_ofNat_lt hlt, nat_sub_sub_self_local h]
  rfl

theorem int_lt_of_lt_of_le {a b c : Int} (hab : a < b) (hbc : b ≤ c) : a < c :=
  int_le_trans hab hbc

theorem int_lt_add_one_iff_le {a b : Int} : a < b + 1 ↔ a ≤ b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat k =>
      constructor
      · intro h; exact int_ofNat_le_ofNat (Nat.le_of_succ_le_succ (int_le_of_ofNat_le_ofNat h))
      · intro h; exact int_ofNat_le_ofNat (Nat.succ_le_succ (int_le_of_ofNat_le_ofNat h))
    | negSucc k =>
      cases k with
      | zero =>
        constructor
        · intro h
          have h0 : Int.ofNat (m + 1) ≤ Int.ofNat 0 := h
          exact False.elim (Nat.not_succ_le_zero m (int_le_of_ofNat_le_ofNat h0))
        · intro h; exact False.elim (int_ofNat_not_le_negSucc m 0 h)
      | succ k' =>
        constructor
        · intro h; exact False.elim (int_ofNat_not_le_negSucc (m + 1) k' h)
        · intro h; exact False.elim (int_ofNat_not_le_negSucc m (Nat.succ k') h)
  | negSucc m =>
    cases b with
    | ofNat k =>
      constructor
      · intro _; exact int_negSucc_le_ofNat m k
      · intro _
        cases m with
        | zero => exact int_ofNat_zero_le (k + 1)
        | succ m' => exact int_negSucc_le_ofNat m' (k + 1)
    | negSucc k =>
      cases m with
      | zero =>
        cases k with
        | zero => constructor <;> intro _ <;> exact Int.NonNeg.mk 0
        | succ k' =>
          constructor
          · intro h; exact False.elim (int_ofNat_not_le_negSucc 0 k' h)
          · intro h
            have := int_le_of_negSucc_le_negSucc h
            cases this
      | succ m' =>
        cases k with
        | zero =>
          constructor
          · intro _; exact int_negSucc_le_negSucc (Nat.zero_le (Nat.succ m'))
          · intro _; exact int_negSucc_le_ofNat m' 0
        | succ k' =>
          constructor
          · intro h; exact int_negSucc_le_negSucc (Nat.succ_le_succ (int_le_of_negSucc_le_negSucc h))
          · intro h; exact int_negSucc_le_negSucc (Nat.le_of_succ_le_succ (int_le_of_negSucc_le_negSucc h))

theorem intWidth_bitWidth_pos (w : IntWidth) : 0 < w.bitWidth := by
  cases w <;> decide

theorem intWidth_bitWidth_le_128 (w : IntWidth) : w.bitWidth ≤ 128 := by
  cases w <;> decide

theorem intWidth_byteSize_pos (w : IntWidth) : 0 < w.byteSize := by
  cases w <;> decide

theorem intWidth_pow_two_half (w : IntWidth) :
    2 * Nat.pow 2 (w.bitWidth - 1) = Nat.pow 2 w.bitWidth := by
  cases w <;> decide

theorem intWidth_pow_le_pow128 (w : IntWidth) :
    Nat.pow 2 w.bitWidth ≤ Nat.pow 2 128 := by
  cases w <;> decide

theorem intWidth_half_le_half128 (w : IntWidth) :
    Nat.pow 2 (w.bitWidth - 1) ≤ Nat.pow 2 127 := by
  cases w <;> decide

theorem intEmodNat_lt (i : Int) (m : Nat) (hm : 0 < m) :
    intEmodNat i m < m := by
  cases i with
  | ofNat n =>
    dsimp only [intEmodNat]
    exact Nat.mod_lt n hm
  | negSucc n =>
    dsimp only [intEmodNat]
    cases hr : Nat.beq (Nat.mod (Nat.succ n) m) 0 with
    | true => exact hm
    | false =>
      have hne : Nat.mod (Nat.succ n) m ≠ 0 := by
        intro heq
        rw [heq] at hr
        cases hr
      have hpos : 0 < Nat.mod (Nat.succ n) m :=
        Nat.pos_of_ne_zero hne
      exact Nat.sub_lt hm hpos

theorem intEmod_toNat_eq_intEmodNat (i : Int) (m : Nat) (hm : 0 < m) :
    (intEmod i (Int.ofNat m)).toNat = intEmodNat i m := by
  cases i with
  | ofNat n => rfl
  | negSucc n =>
    dsimp only [intEmod, intEmodNat, Int.natAbs]
    have hmod_lt : Nat.mod n m < m := Nat.mod_lt n hm
    have hsucc_le : Nat.succ (Nat.mod n m) ≤ m := hmod_lt
    have hsub : Int.subNatNat m (Nat.succ (Nat.mod n m)) =
        Int.ofNat (m - Nat.succ (Nat.mod n m)) := by
      dsimp only [Int.subNatNat]
      have hzero : Nat.succ (Nat.mod n m) - m = 0 := Nat.sub_eq_zero_of_le hsucc_le
      rw [hzero]
    rw [hsub]
    dsimp only [Int.toNat]
    have hmod_succ : Nat.mod (Nat.succ n) m =
        if Nat.beq (Nat.succ (Nat.mod n m)) m then 0
        else Nat.succ (Nat.mod n m) := by
      rw [nat_mod_succ_eq]
      cases heq : Nat.beq (Nat.succ (Nat.mod n m)) m with
      | true =>
        change Nat.mod (Nat.mod n m + 1) m = 0
        have hEq : Nat.mod n m + 1 = m := Nat.eq_of_beq_eq_true heq
        rw [hEq, nat_mod_self_local]
      | false =>
        change Nat.mod (Nat.mod n m + 1) m = Nat.succ (Nat.mod n m)
        have hne : Nat.mod n m + 1 ≠ m := by
          intro h
          have hb := nat_beq_eq_true_of_eq h
          rw [hb] at heq
          cases heq
        have hlt : Nat.mod n m + 1 < m := Nat.lt_of_le_of_ne hsucc_le hne
        exact Nat.mod_eq_of_lt hlt
    rw [hmod_succ]
    cases heq : Nat.beq (Nat.succ (Nat.mod n m)) m with
    | true =>
      have hEq : Nat.succ (Nat.mod n m) = m := Nat.eq_of_beq_eq_true heq
      rw [hEq, Nat.sub_self]
      rfl
    | false =>
      change m - Nat.succ (Nat.mod n m) =
        if Nat.beq (Nat.succ (Nat.mod n m)) 0 then 0 else m - Nat.succ (Nat.mod n m)
      rfl

theorem intEmodNat_ofNat_lt (n m : Nat) (h : n < m) :
    intEmodNat (Int.ofNat n) m = n :=
  Nat.mod_eq_of_lt h

theorem intEmodNat_sub_of_lt (u m : Nat) (h : u < m) :
    intEmodNat (Int.ofNat u - Int.ofNat m) m = u := by
  rw [int_ofNat_sub_ofNat_lt h]
  dsimp only [intEmodNat]
  have hsucc : Nat.succ (m - u - 1) = m - u :=
    Nat.sub_add_cancel (Nat.sub_pos_of_lt h)
  rw [hsucc]
  cases u with
  | zero =>
    rw [Nat.sub_zero, nat_mod_self_local]
    rfl
  | succ k =>
    have hlt : m - Nat.succ k < m :=
      Nat.sub_lt (Nat.lt_trans (Nat.zero_lt_succ k) h) (Nat.zero_lt_succ k)
    have hmeq : Nat.mod (m - Nat.succ k) m = m - Nat.succ k := Nat.mod_eq_of_lt hlt
    rw [hmeq]
    have hpos : 0 < m - Nat.succ k := Nat.sub_pos_of_lt h
    have hne : Nat.beq (m - Nat.succ k) 0 = false := by
      cases hdiff : m - Nat.succ k with
      | zero => rw [hdiff] at hpos; cases hpos
      | succ _ => rfl
    rw [hne]
    exact nat_sub_sub_self_local (Nat.le_of_lt h)

theorem intEmodNat_mod_self (i : Int) (m : Nat) (hm : 0 < m) :
    Nat.mod (intEmodNat i m) m = intEmodNat i m :=
  Nat.mod_eq_of_lt (intEmodNat_lt i m hm)

theorem intEmodNat_bringInBounds (it : IntType) (i : Int) (hpos : 0 < it.bitWidth) :
    intEmodNat (it.bringInBounds i) (Nat.pow 2 it.bitWidth) =
      intEmodNat i (Nat.pow 2 it.bitWidth) := by
  cases it with
  | mk sg sz =>
    cases sz with
    | mk nbytes =>
      cases nbytes with
      | zero => cases hpos
      | succ nb =>
        have hm : 0 < Nat.pow 2 ((nb + 1) * 8) := Nat.pow_pos (by decide)
        have hlt : intEmodNat i (Nat.pow 2 ((nb + 1) * 8)) <
            Nat.pow 2 ((nb + 1) * 8) := intEmodNat_lt i _ hm
        dsimp only [IntType.bringInBounds, IntType.bitWidth, Size.bits]
        cases sg with
        | unsigned => exact intEmodNat_ofNat_lt _ _ hlt
        | signed =>
          have hne : Nat.beq ((nb + 1) * 8) 0 = false := by
            rw [Nat.add_mul, Nat.one_mul]
            rfl
          simp only [hne]
          cases bool_cases (Nat.blt (intEmodNat i (Nat.pow 2 ((nb + 1) * 8)))
              (Nat.pow 2 ((nb + 1) * 8 - 1))) with
          | inl hblt => simp only [hblt]; exact intEmodNat_sub_of_lt _ _ hlt
          | inr hblt => simp only [hblt]; exact intEmodNat_ofNat_lt _ _ hlt

theorem bringInBounds_canRepresent (it : IntType) (i : Int)
    (hpos : 0 < it.bitWidth) :
    it.canRepresent (it.bringInBounds i) = true := by
  cases it with
  | mk sg sz =>
    cases sz with
    | mk nbytes =>
      cases nbytes with
      | zero => cases hpos
      | succ nb =>
        have hm : 0 < Nat.pow 2 ((nb + 1) * 8) := Nat.pow_pos (by decide)
        have hlt : intEmodNat i (Nat.pow 2 ((nb + 1) * 8)) <
            Nat.pow 2 ((nb + 1) * 8) := intEmodNat_lt i _ hm
        cases sg with
        | unsigned =>
          dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal,
            IntType.bringInBounds, IntType.bitWidth, Size.bits]
          have h0 : decide ((0 : Int) ≤ Int.ofNat (intEmodNat i (Nat.pow 2 ((nb + 1) * 8)))) = true :=
            decide_eq_true (int_ofNat_zero_le _)
          have h1 : decide (Int.ofNat (intEmodNat i (Nat.pow 2 ((nb + 1) * 8))) <
              Int.ofNat (Nat.pow 2 ((nb + 1) * 8))) = true :=
            decide_eq_true (int_ofNat_lt_ofNat hlt)
          change (decide ((0 : Int) ≤ Int.ofNat (intEmodNat i (Nat.pow 2 ((nb + 1) * 8)))) &&
            decide (Int.ofNat (intEmodNat i (Nat.pow 2 ((nb + 1) * 8))) <
              Int.ofNat (Nat.pow 2 ((nb + 1) * 8)))) = true
          rw [h0, h1]
          rfl
        | signed =>
          dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal,
            IntType.bringInBounds, IntType.bitWidth, Size.bits]
          have hbitsEq : (nb + 1) * 8 = (nb * 8 + 7) + 1 := by
            rw [Nat.add_mul, Nat.one_mul]
          have hne : Nat.beq ((nb + 1) * 8) 0 = false := by
            rw [hbitsEq]; rfl
          have hsub1 : (nb + 1) * 8 - 1 = nb * 8 + 7 := by
            rw [hbitsEq]; rfl
          have hpow : Nat.pow 2 ((nb + 1) * 8) =
              Nat.pow 2 (nb * 8 + 7) + Nat.pow 2 (nb * 8 + 7) := by
            rw [hbitsEq]
            change Nat.pow 2 (nb * 8 + 7) * 2 = Nat.pow 2 (nb * 8 + 7) + Nat.pow 2 (nb * 8 + 7)
            exact Nat.mul_two (Nat.pow 2 (nb * 8 + 7))
          simp only [hne, hsub1, if_false_eq_true]
          cases bool_cases (Nat.blt (intEmodNat i (Nat.pow 2 ((nb + 1) * 8)))
              (Nat.pow 2 (nb * 8 + 7))) with
          | inr hblt =>
            simp only [hblt, ite_true]
            have hltHalf : intEmodNat i (Nat.pow 2 ((nb + 1) * 8)) <
                Nat.pow 2 (nb * 8 + 7) := nat_lt_of_blt_eq_true hblt
            have hlo : decide (Neg.neg (Int.ofNat (Nat.pow 2 (nb * 8 + 7))) ≤
                Int.ofNat (intEmodNat i (Nat.pow 2 ((nb + 1) * 8)))) = true :=
              decide_eq_true (int_le_trans (int_neg_nonpos _) (int_ofNat_zero_le _))
            have hhi : decide (Int.ofNat (intEmodNat i (Nat.pow 2 ((nb + 1) * 8))) <
                Int.ofNat (Nat.pow 2 (nb * 8 + 7))) = true :=
              decide_eq_true (int_ofNat_lt_ofNat hltHalf)
            rw [hlo, hhi]
            rfl
          | inl hblt =>
            simp only [hblt, if_false_eq_true]
            have hgeHalf : Nat.pow 2 (nb * 8 + 7) ≤
                intEmodNat i (Nat.pow 2 ((nb + 1) * 8)) := by
              cases Nat.lt_or_ge (intEmodNat i (Nat.pow 2 ((nb + 1) * 8)))
                  (Nat.pow 2 (nb * 8 + 7)) with
              | inl h =>
                have hb := nat_blt_eq_true_of_lt h
                rw [hb] at hblt; cases hblt
              | inr h => exact h
            have hlo : decide (Neg.neg (Int.ofNat (Nat.pow 2 (nb * 8 + 7))) ≤
                Int.ofNat (intEmodNat i (Nat.pow 2 ((nb + 1) * 8))) -
                  Int.ofNat (Nat.pow 2 ((nb + 1) * 8))) = true := by
              apply decide_eq_true
              have hsub := int_ofNat_sub_le hgeHalf hlt
              have hdiff : Nat.pow 2 ((nb + 1) * 8) - Nat.pow 2 (nb * 8 + 7) =
                  Nat.pow 2 (nb * 8 + 7) := by
                rw [hpow, Nat.add_sub_cancel]
              rw [hdiff] at hsub
              exact hsub
            have hhi : decide (Int.ofNat (intEmodNat i (Nat.pow 2 ((nb + 1) * 8))) -
                Int.ofNat (Nat.pow 2 ((nb + 1) * 8)) <
                Int.ofNat (Nat.pow 2 (nb * 8 + 7))) = true :=
              decide_eq_true (int_lt_of_lt_of_le (int_sub_lt_zero_of_lt hlt) (int_ofNat_zero_le _))
            rw [hlo, hhi]
            rfl

theorem bringInBounds_of_canRepresent (it : IntType) (i : Int)
    (hpos : 0 < it.bitWidth) (hcan : it.canRepresent i = true) :
    it.bringInBounds i = i := by
  cases it with
  | mk sg sz =>
    cases sz with
    | mk nbytes =>
      cases nbytes with
      | zero => cases hpos
      | succ nb =>
        cases sg with
        | unsigned =>
          dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal, IntType.bringInBounds, IntType.bitWidth, Size.bits] at hcan
          dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal, IntType.bringInBounds, IntType.bitWidth, Size.bits]
          have hcan' : (decide ((0 : Int) ≤ i) &&
              decide (i < Int.ofNat (Nat.pow 2 ((nb + 1) * 8)))) = true := hcan
          cases bool_cases (decide ((0 : Int) ≤ i)) with
          | inl hlo => rw [hlo] at hcan'; cases hcan'
          | inr hlo =>
            rw [hlo] at hcan'
            have hge0 : (0 : Int) ≤ i := of_decide_eq_true hlo
            have hltM : i < Int.ofNat (Nat.pow 2 ((nb + 1) * 8)) := of_decide_eq_true hcan'
            cases i with
            | negSucc _ => cases hge0
            | ofNat n =>
              have hlt : n < Nat.pow 2 ((nb + 1) * 8) := int_lt_of_ofNat_lt_ofNat hltM
              exact congrArg Int.ofNat (intEmodNat_ofNat_lt n _ hlt)
        | signed =>
          dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal, IntType.bringInBounds, IntType.bitWidth, Size.bits] at hcan
          dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal, IntType.bringInBounds, IntType.bitWidth, Size.bits]
          have hbitsEq : (nb + 1) * 8 = (nb * 8 + 7) + 1 := by
            rw [Nat.add_mul, Nat.one_mul]
          have hne : Nat.beq ((nb + 1) * 8) 0 = false := by
            rw [hbitsEq]; rfl
          have hsub1 : (nb + 1) * 8 - 1 = nb * 8 + 7 := by
            rw [hbitsEq]; rfl
          have hpow : Nat.pow 2 ((nb + 1) * 8) =
              Nat.pow 2 (nb * 8 + 7) + Nat.pow 2 (nb * 8 + 7) := by
            rw [hbitsEq]
            change Nat.pow 2 (nb * 8 + 7) * 2 = Nat.pow 2 (nb * 8 + 7) + Nat.pow 2 (nb * 8 + 7)
            exact Nat.mul_two (Nat.pow 2 (nb * 8 + 7))
          simp only [hne, hsub1, if_false_eq_true] at hcan; simp only [hne, hsub1, if_false_eq_true]
          cases bool_cases (decide (Neg.neg (Int.ofNat (Nat.pow 2 (nb * 8 + 7))) ≤ i)) with
          | inl hlo => rw [hlo] at hcan; cases hcan
          | inr hlo =>
            rw [hlo] at hcan
            have hgeMin : Neg.neg (Int.ofNat (Nat.pow 2 (nb * 8 + 7))) ≤ i :=
              of_decide_eq_true hlo
            have hltMax : i < Int.ofNat (Nat.pow 2 (nb * 8 + 7)) :=
              of_decide_eq_true hcan
            cases i with
            | ofNat n =>
              have hltHalf : n < Nat.pow 2 (nb * 8 + 7) := int_lt_of_ofNat_lt_ofNat hltMax
              have hltM : n < Nat.pow 2 ((nb + 1) * 8) := by
                rw [hpow]
                exact Nat.lt_of_lt_of_le hltHalf (Nat.le_add_right _ _)
              simp only [intEmodNat_ofNat_lt n _ hltM, nat_blt_eq_true_of_lt hltHalf, ite_true]
            | negSucc n =>
              have hposHalf : 0 < Nat.pow 2 (nb * 8 + 7) := Nat.pow_pos (by decide)
              have hleHalf : Nat.succ n ≤ Nat.pow 2 (nb * 8 + 7) := by
                cases hp : Nat.pow 2 (nb * 8 + 7) with
                | zero => rw [hp] at hposHalf; cases hposHalf
                | succ half' =>
                  rw [hp] at hgeMin
                  have hle' := int_le_of_negSucc_le_negSucc hgeMin
                  exact Nat.succ_le_succ hle'
              have hltM : Nat.succ n < Nat.pow 2 ((nb + 1) * 8) := by
                rw [hpow]
                exact Nat.lt_of_le_of_lt hleHalf (Nat.lt_add_of_pos_right hposHalf)
              have heqMod : intEmodNat (Int.negSucc n) (Nat.pow 2 ((nb + 1) * 8)) =
                  Nat.pow 2 ((nb + 1) * 8) - Nat.succ n := by
                dsimp only [intEmodNat]
                rw [nat_mod_eq_of_lt hltM]
                rfl
              have hgeHalf : Nat.pow 2 (nb * 8 + 7) ≤
                  Nat.pow 2 ((nb + 1) * 8) - Nat.succ n := by
                rw [hpow]
                exact Nat.le_sub_of_add_le (Nat.add_le_add_left hleHalf _)
              have hblt : Nat.blt (Nat.pow 2 ((nb + 1) * 8) - Nat.succ n)
                  (Nat.pow 2 (nb * 8 + 7)) = false := by
                cases hb : Nat.blt (Nat.pow 2 ((nb + 1) * 8) - Nat.succ n)
                    (Nat.pow 2 (nb * 8 + 7)) with
                | false => rfl
                | true =>
                  exact False.elim (Nat.not_lt_of_ge hgeHalf (nat_lt_of_blt_eq_true hb))
              simp only [heqMod, hblt]
              exact int_sub_self_negSucc (Nat.pow 2 ((nb + 1) * 8)) n (Nat.le_of_lt hltM)

theorem truncateBits_toNat (w : IntWidth) (v : BitVec 128) :
    (truncateBits w v).toNat = Nat.mod v.toNat (Nat.pow 2 w.bitWidth) := by
  cases w with
  | i8 =>
    change Nat.mod (Nat.mod (Nat.shiftRight v.toNat 0) (Nat.pow 2 8)) (Nat.pow 2 128) =
      Nat.mod v.toNat (Nat.pow 2 8)
    have hlt : Nat.mod v.toNat (Nat.pow 2 8) < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt v.toNat (by decide)) (by decide)
    exact Nat.mod_eq_of_lt hlt
  | i16 =>
    change Nat.mod (Nat.mod (Nat.shiftRight v.toNat 0) (Nat.pow 2 16)) (Nat.pow 2 128) =
      Nat.mod v.toNat (Nat.pow 2 16)
    have hlt : Nat.mod v.toNat (Nat.pow 2 16) < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt v.toNat (by decide)) (by decide)
    exact Nat.mod_eq_of_lt hlt
  | i32 =>
    change Nat.mod (Nat.mod (Nat.shiftRight v.toNat 0) (Nat.pow 2 32)) (Nat.pow 2 128) =
      Nat.mod v.toNat (Nat.pow 2 32)
    have hlt : Nat.mod v.toNat (Nat.pow 2 32) < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt v.toNat (by decide)) (by decide)
    exact Nat.mod_eq_of_lt hlt
  | i64 =>
    change Nat.mod (Nat.mod (Nat.shiftRight v.toNat 0) (Nat.pow 2 64)) (Nat.pow 2 128) =
      Nat.mod v.toNat (Nat.pow 2 64)
    have hlt : Nat.mod v.toNat (Nat.pow 2 64) < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt v.toNat (by decide)) (by decide)
    exact Nat.mod_eq_of_lt hlt
  | isize =>
    change Nat.mod (Nat.mod (Nat.shiftRight v.toNat 0) (Nat.pow 2 64)) (Nat.pow 2 128) =
      Nat.mod v.toNat (Nat.pow 2 64)
    have hlt : Nat.mod v.toNat (Nat.pow 2 64) < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt v.toNat (by decide)) (by decide)
    exact Nat.mod_eq_of_lt hlt
  | i128 =>
    change Nat.mod (Nat.mod (Nat.shiftRight v.toNat 0) (Nat.pow 2 128)) (Nat.pow 2 128) =
      Nat.mod v.toNat (Nat.pow 2 128)
    exact Nat.mod_eq_of_lt (Nat.mod_lt v.toNat (by decide))

theorem bvToInt_bvOfInt_128_eq (x : Int)
    (hlo : Neg.neg (Int.ofNat (Nat.pow 2 127)) ≤ x)
    (hhi : x < Int.ofNat (Nat.pow 2 127)) :
    bvToInt (bvOfInt 128 x) = x := by
  have hcan : i128Ty.canRepresent x = true := by
    have hd1 : decide (Neg.neg (Int.ofNat (Nat.pow 2 127)) ≤ x) = true := decide_eq_true hlo
    have hd2 : decide (x < Int.ofNat (Nat.pow 2 127)) = true := decide_eq_true hhi
    change (decide (Neg.neg (Int.ofNat (Nat.pow 2 127)) ≤ x) &&
      decide (x < Int.ofNat (Nat.pow 2 127))) = true
    rw [hd1, hd2]
    rfl
  have hbib := bringInBounds_of_canRepresent i128Ty x (by decide) hcan
  dsimp only [bvToInt, bvOfInt]
  rw [bv_toNat_ofNat, intEmod_toNat_eq_intEmodNat x (Nat.pow 2 128) (by decide)]
  rw [intEmodNat_mod_self x (Nat.pow 2 128) (by decide)]
  have hbib' : (if Nat.blt (intEmodNat x (Nat.pow 2 128)) (Nat.pow 2 127)
      then Int.ofNat (intEmodNat x (Nat.pow 2 128))
      else Int.ofNat (intEmodNat x (Nat.pow 2 128)) -
        Int.ofNat (Nat.pow 2 128)) = x := hbib
  cases bool_cases (Nat.blt (intEmodNat x (Nat.pow 2 128)) (Nat.pow 2 127)) with
  | inr hblt =>
    simp only [hblt] at hbib'
    have hlt2 : 2 * intEmodNat x (Nat.pow 2 128) < Nat.pow 2 128 := by
      have h1 := nat_lt_of_blt_eq_true hblt
      have h2 : 2 * Nat.pow 2 127 = Nat.pow 2 128 := by decide
      rw [← h2]
      exact Nat.mul_lt_mul_of_pos_left h1 (by decide)
    simp only [hlt2, ite_true]
    exact hbib'
  | inl hblt =>
    simp only [hblt] at hbib'
    have hge : Nat.pow 2 127 ≤ intEmodNat x (Nat.pow 2 128) := by
      cases Nat.lt_or_ge (intEmodNat x (Nat.pow 2 128)) (Nat.pow 2 127) with
      | inl h =>
        have hb := nat_blt_eq_true_of_lt h
        rw [hb] at hblt; cases hblt
      | inr h => exact h
    have hnotlt : ¬ (2 * intEmodNat x (Nat.pow 2 128) < Nat.pow 2 128) := by
      have h2 : 2 * Nat.pow 2 127 = Nat.pow 2 128 := by decide
      rw [← h2]
      exact Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 hge)
    simp only [hnotlt, ite_false]
    exact hbib'

theorem decodeScalar_eq_bringInBounds_aux (w : IntWidth) (bits : BitVec 128) :
    signExtendBits w (truncateBits w bits) =
      (translateIntTy w true).bringInBounds (Int.ofNat bits.toNat) := by
  have hwid : w.bitWidth - 1 - 0 + 1 = w.bitWidth := by cases w <;> decide
  have hlow : (bvExtractLsb (w.bitWidth - 1) 0 (truncateBits w bits)).toNat =
      Nat.mod bits.toNat (Nat.pow 2 w.bitWidth) := by
    dsimp only [bvExtractLsb, bvExtractLsb']
    rw [bv_toNat_ofNat]
    have hs0 : Nat.shiftRight (truncateBits w bits).toNat 0 = (truncateBits w bits).toNat := rfl
    rw [hs0, truncateBits_toNat, hwid]
    exact nat_mod_mod_local bits.toNat (Nat.pow 2 w.bitWidth) (Nat.pow_pos (by decide))
  have hbv : bvToInt (bvExtractLsb (w.bitWidth - 1) 0 (truncateBits w bits)) =
      (translateIntTy w true).bringInBounds (Int.ofNat bits.toNat) := by
    have hpow2 : 2 * Nat.pow 2 (w.byteSize * 8 - 1) = Nat.pow 2 (w.byteSize * 8) :=
      intWidth_pow_two_half w
    have hne : Nat.beq (w.byteSize * 8) 0 = false := by cases w <;> decide
    dsimp only [bvToInt, translateIntTy, IntType.bringInBounds,
      IntType.bitWidth, Size.bits, intEmodNat]
    simp only [hlow, hwid, hne, if_false_eq_true]
    cases bool_cases (Nat.blt (Nat.mod bits.toNat (Nat.pow 2 (w.byteSize * 8)))
        (Nat.pow 2 (w.byteSize * 8 - 1))) with
    | inr hblt =>
      simp only [hblt, ite_true]
      have h1 := nat_lt_of_blt_eq_true hblt
      have hlt2 : 2 * Nat.mod bits.toNat (Nat.pow 2 (w.byteSize * 8)) <
          Nat.pow 2 (w.byteSize * 8) := by
        have hm := Nat.mul_lt_mul_of_pos_left h1 (by decide : 0 < 2)
        rw [hpow2] at hm
        exact hm
      have hlt2' : 2 * Nat.mod bits.toNat (Nat.pow 2 w.bitWidth) <
          Nat.pow 2 w.bitWidth := hlt2
      simp only [hlt2', ite_true]
      rfl
    | inl hblt =>
      simp only [hblt, if_false_eq_true]
      have hge : Nat.pow 2 (w.byteSize * 8 - 1) ≤
          Nat.mod bits.toNat (Nat.pow 2 (w.byteSize * 8)) := by
        cases Nat.lt_or_ge (Nat.mod bits.toNat (Nat.pow 2 (w.byteSize * 8)))
            (Nat.pow 2 (w.byteSize * 8 - 1)) with
        | inl h =>
          have hb := nat_blt_eq_true_of_lt h
          rw [hb] at hblt; cases hblt
        | inr h => exact h
      have hnotlt : ¬ (2 * Nat.mod bits.toNat (Nat.pow 2 w.bitWidth) <
          Nat.pow 2 w.bitWidth) := by
        have hm := Nat.mul_le_mul_left 2 hge
        rw [hpow2] at hm
        exact Nat.not_lt_of_ge hm
      simp only [hnotlt, ite_false]
      rfl
  dsimp only [signExtendBits, bvSignExtend]
  rw [hbv]
  have hcan := bringInBounds_canRepresent (translateIntTy w true)
    (Int.ofNat bits.toNat) (intWidth_bitWidth_pos w)
  have hne : Nat.beq (w.byteSize * 8) 0 = false := by cases w <;> decide
  dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal,
    translateIntTy, IntType.bitWidth, Size.bits] at hcan
  simp only [hne, if_false_eq_true] at hcan
  have hcan' : (decide (Neg.neg (Int.ofNat (Nat.pow 2 (w.byteSize * 8 - 1))) ≤
        (translateIntTy w true).bringInBounds (Int.ofNat bits.toNat)) &&
      decide ((translateIntTy w true).bringInBounds (Int.ofNat bits.toNat) <
        Int.ofNat (Nat.pow 2 (w.byteSize * 8 - 1)))) = true := hcan
  cases bool_cases (decide (Neg.neg (Int.ofNat (Nat.pow 2 (w.byteSize * 8 - 1))) ≤
      (translateIntTy w true).bringInBounds (Int.ofNat bits.toNat))) with
  | inl h1 => rw [h1] at hcan'; cases hcan'
  | inr h1 =>
    rw [h1] at hcan'
    have hle := of_decide_eq_true h1
    have hlt := of_decide_eq_true hcan'
    have hleHalf : Int.ofNat (Nat.pow 2 (w.byteSize * 8 - 1)) ≤
        Int.ofNat (Nat.pow 2 127) :=
      int_ofNat_le_ofNat (intWidth_half_le_half128 w)
    exact bvToInt_bvOfInt_128_eq _
      (int_le_trans (int_neg_le_neg hleHalf) hle)
      (int_lt_of_lt_of_le hlt hleHalf)

theorem decodeScalar_eq_bringInBounds (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    decodeScalar ⟨w, s, bits⟩ =
      (translateIntTy w s).bringInBounds (Int.ofNat bits.toNat) := by
  cases s with
  | false =>
    dsimp only [decodeScalar, translateIntTy, IntType.bringInBounds,
      IntType.bitWidth, Size.bits, intEmodNat]
    rw [truncateBits_toNat]
    rfl
  | true =>
    exact decodeScalar_eq_bringInBounds_aux w bits

theorem canRepresent_decodeScalar (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    (translateIntTy w s).canRepresent (decodeScalar ⟨w, s, bits⟩) = true := by
  rw [decodeScalar_eq_bringInBounds]
  exact bringInBounds_canRepresent (translateIntTy w s) _ (intWidth_bitWidth_pos w)

theorem intEmodNat_decodeScalar (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    intEmodNat (decodeScalar ⟨w, s, bits⟩) (Nat.pow 2 w.bitWidth) =
      (truncateBits w bits).toNat := by
  rw [decodeScalar_eq_bringInBounds]
  have h := intEmodNat_bringInBounds (translateIntTy w s) (Int.ofNat bits.toNat)
    (intWidth_bitWidth_pos w)
  dsimp only [translateIntTy, IntType.bitWidth, Size.bits, intEmodNat] at h
  rw [truncateBits_toNat]
  exact h

/-! ## Byte-Codec and Representation Relation Equivalence -/

/-- Convert `Trusted.MirSemantics` abstract bytes (dropping provenance) into
`Anneal.MiniRust.AbstractByte`. -/
def toMrBytes : List AllocByte → List AbstractByte
  | [] => []
  | .uninit :: rest => .uninit :: toMrBytes rest
  | .init b _ :: rest => .init b :: toMrBytes rest

theorem toMrBytes_append (xs ys : List AllocByte) :
    toMrBytes (xs ++ ys) = toMrBytes xs ++ toMrBytes ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | uninit => dsimp only [List.cons_append, toMrBytes]; rw [ih]
    | init _ _ => dsimp only [List.cons_append, toMrBytes]; rw [ih]

theorem toMrBytes_replicate_uninit (n : Nat) :
    toMrBytes (List.replicate n AllocByte.uninit) =
      List.replicate n AbstractByte.uninit := by
  induction n with
  | zero => rfl
  | succ k ih => dsimp only [List.replicate, toMrBytes]; rw [ih]

theorem toMrBytes_map_init (bs : List UInt8) :
    toMrBytes (bs.map (fun b => AllocByte.init b none)) =
      bs.map AbstractByte.init := by
  induction bs with
  | nil => rfl
  | cons b rest ih => dsimp only [List.map, toMrBytes]; rw [ih]

theorem mrLeBytesOfNat_eq_leBytesOfNat (n v : Nat) :
    mrLeBytesOfNat n v = leBytesOfNat n v := by
  induction n generalizing v with
  | zero => rfl
  | succ k ih =>
    dsimp only [mrLeBytesOfNat, leBytesOfNat]
    rw [ih]

theorem mrNatOfLeBytes_eq_natOfLeBytes (bs : List UInt8) :
    mrNatOfLeBytes bs = natOfLeBytes bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    dsimp only [mrNatOfLeBytes, natOfLeBytes]
    rw [ih]

theorem decodeInt_encodeInt (it : IntType) (i : Int)
    (hpos : 0 < it.bitWidth) (hcan : it.canRepresent i = true) :
    ∃ bs, encodeInt it i = some bs ∧ bs.length = it.size.bytes ∧
      decodeInt it bs = some i := by
  dsimp only [encodeInt]
  simp only [hcan]
  refine ⟨(mrLeBytesOfNat it.size.bytes
      (intEmodNat i (Nat.pow 2 it.bitWidth))).map AbstractByte.init, rfl, ?_, ?_⟩
  · rw [list_length_map, mrLeBytesOfNat_length]
  · dsimp only [decodeInt]
    rw [list_length_map, mrLeBytesOfNat_length, Nat.beq_refl, if_not_true]
    rw [extractInitBytes_map_init]
    dsimp only
    rw [mrNatOfLeBytes_mrLeBytesOfNat]
    have hlt : intEmodNat i (Nat.pow 2 it.bitWidth) < Nat.pow 2 it.bitWidth :=
      intEmodNat_lt i _ (Nat.pow_pos (by decide))
    have hmod : Nat.mod (intEmodNat i (Nat.pow 2 it.bitWidth))
        (Nat.pow 2 (it.size.bytes * 8)) =
        intEmodNat i (Nat.pow 2 it.bitWidth) := nat_mod_eq_of_lt hlt
    rw [hmod]
    have hbib := bringInBounds_of_canRepresent it i hpos hcan
    dsimp only [IntType.bringInBounds] at hbib; dsimp only [IntType.bringInBounds]
    rw [intEmodNat_ofNat_lt _ _ hlt]
    rw [hbib]

theorem decodeInt_replicate_uninit (it : IntType) (hpos : 0 < it.size.bytes) :
    decodeInt it (List.replicate it.size.bytes AbstractByte.uninit) = none := by
  cases hsz : it.size.bytes with
  | zero => rw [hsz] at hpos; cases hpos
  | succ k =>
    dsimp only [decodeInt]
    rw [hsz, List.length_replicate, Nat.beq_refl]
    rfl

theorem mrEncode_length_and_decode_int (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    ∃ bs, mrEncode (.int (translateIntTy w s)) (.int (decodeScalar ⟨w, s, bits⟩)) = some bs ∧
      bs.length = w.byteSize ∧
      mrDecode (.int (translateIntTy w s)) bs = some (.int (decodeScalar ⟨w, s, bits⟩)) := by
  cases decodeInt_encodeInt (translateIntTy w s) (decodeScalar ⟨w, s, bits⟩)
      (intWidth_bitWidth_pos w) (canRepresent_decodeScalar w s bits) with
  | intro bs hbs =>
    refine ⟨bs, hbs.1, hbs.2.1, ?_⟩
    dsimp only [mrDecode]
    rw [hbs.2.2]

theorem encodeVal_little_scalar_eq (w : IntWidth) (s : Bool) (sv : ScalarVal)
    (hwf : checkVal (.scalar sv) (.int w s) = true) :
    ∃ bs, encodeVal .little (.int w s) (.scalar sv) = .ok bs ∧
      mrEncode (translateTy (.int w s)) (translateVal (.scalar sv)) =
        some (toMrBytes bs) := by
  dsimp only [encodeVal]
  rw [hwf]
  dsimp only [encodeUInt, translateTy, translateVal, mrEncode, encodeInt]
  have hcheck : sv.width = w ∧ sv.signed = s ∧ sv.wf = true := by
    have htyEq := checkVal_ty_eq hwf
    dsimp only [Val.ty?] at htyEq
    cases h1 : sv.wf with
    | false => rw [h1] at htyEq; cases htyEq
    | true =>
      rw [h1] at htyEq
      injection htyEq with ht
      injection ht with hw hs
      exact ⟨hw, hs, rfl⟩
  cases hcheck with
  | intro hw hrest =>
    cases hrest with
    | intro hs hsvwf =>
      cases sv with
      | mk svw svs svbits =>
        dsimp only at hw hs hsvwf
        subst hw; subst hs
        simp only [canRepresent_decodeScalar svw svs svbits]
        have htrunc : truncateBits svw svbits = svbits :=
          eq_of_beq hsvwf
        have heq : intEmodNat (decodeScalar ⟨svw, svs, svbits⟩)
            (Nat.pow 2 (translateIntTy svw svs).bitWidth) = svbits.toNat := by
          have h1 := intEmodNat_decodeScalar svw svs svbits
          rw [htrunc] at h1
          exact h1
        refine ⟨(leBytesOfNat svw.byteSize svbits.toNat).map
          (fun b => AllocByte.init b none), rfl, ?_⟩
        rw [toMrBytes_map_init, ← mrLeBytesOfNat_eq_leBytesOfNat, heq]
        rfl

theorem enum_discriminant_decode_roundtrip (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (hrepr : ety.tagRepr = .scalar tagW tagS)
    (hadm : enumAdmitted ety = true) (v : Nat) (d : Nat)
    (hget : Trusted.MirSemantics.getElem? ety.discriminants v = some d) :
    ∃ bs, mrEncode (translateEnumTy ety) (translateVal (.enumVal ety v)) = some bs ∧
      bs.length = tagW.byteSize ∧
      decodeDiscriminant bs
        (.branch 0 (translateIntTy tagW tagS)
          (buildEnumBranches ety tagW tagS ety.discriminants) .invalid) =
        some (discrIntOfNat ety.discrWidth ety.discrSigned d) ∧
      mrDecode (translateEnumTy ety) bs =
        some (translateVal (.enumVal ety v)) := by
  -- Helper lemmas for `buildEnumVariants` and `buildEnumBranches` on distinct
  -- tags.
  have hdist : natListPairwiseNe ety.discriminants = true ∧
      ety.discriminants.all
        (fun x => Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth)) = true ∧
      ety.discriminants.all (fun x =>
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 x)) == BitVec.ofNat 128 x) = true := by
    dsimp only [enumAdmitted] at hadm
    rw [hrepr] at hadm
    cases h1 : !ety.discriminants.isEmpty with
    | false => rw [h1] at hadm; cases hadm
    | true =>
      cases h2 : Nat.blt ety.discriminants.length (Nat.pow 2 32) with
      | false => rw [h1, h2] at hadm; cases hadm
      | true =>
        cases h3 : ety.discriminants.all
            (fun x => Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth)) with
        | false => rw [h1, h2, h3] at hadm; cases hadm
        | true =>
          cases h4 : natListPairwiseNe ety.discriminants with
          | false => rw [h1, h2, h3, h4] at hadm; cases hadm
          | true =>
            rw [h1, h2, h3, h4] at hadm
            exact ⟨rfl, rfl, hadm⟩
  -- Prove lookup agreement along `ety.discriminants` by induction on `ds`.
  have hTagInj : ∀ x y : Nat,
      Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth) = true →
      Nat.blt y (Nat.pow 2 ety.discrWidth.bitWidth) = true →
      (tagBitsToDiscrBits tagW tagS ety.discrWidth
        (truncateBits tagW (BitVec.ofNat 128 x)) == BitVec.ofNat 128 x) = true →
      (tagBitsToDiscrBits tagW tagS ety.discrWidth
        (truncateBits tagW (BitVec.ofNat 128 y)) == BitVec.ofNat 128 y) = true →
      tagIntOfNat tagW tagS x = tagIntOfNat tagW tagS y → x = y := by
    intro x y hx hy hrx hry hteq
    have hxlt : x < Nat.pow 2 ety.discrWidth.bitWidth := nat_lt_of_blt_eq_true hx
    have hylt : y < Nat.pow 2 ety.discrWidth.bitWidth := nat_lt_of_blt_eq_true hy
    have htx : (truncateBits tagW (BitVec.ofNat 128 x)).toNat =
        (truncateBits tagW (BitVec.ofNat 128 y)).toNat := by
      have h1 := intEmodNat_decodeScalar tagW tagS (truncateBits tagW (BitVec.ofNat 128 x))
      have h2 := intEmodNat_decodeScalar tagW tagS (truncateBits tagW (BitVec.ofNat 128 y))
      have ht1 : truncateBits tagW (truncateBits tagW (BitVec.ofNat 128 x)) =
          truncateBits tagW (BitVec.ofNat 128 x) := by
        apply bv_eq_of_toNat_eq
        rw [truncateBits_toNat, truncateBits_toNat]
        exact nat_mod_mod_local (BitVec.ofNat 128 x).toNat (Nat.pow 2 tagW.bitWidth) (Nat.pow_pos (by decide))
      have ht2 : truncateBits tagW (truncateBits tagW (BitVec.ofNat 128 y)) =
          truncateBits tagW (BitVec.ofNat 128 y) := by
        apply bv_eq_of_toNat_eq
        rw [truncateBits_toNat, truncateBits_toNat]
        exact nat_mod_mod_local (BitVec.ofNat 128 y).toNat (Nat.pow 2 tagW.bitWidth) (Nat.pow_pos (by decide))
      rw [ht1] at h1
      rw [ht2] at h2
      dsimp only [tagIntOfNat] at hteq
      rw [← h1, hteq, h2]
    have htbv : truncateBits tagW (BitVec.ofNat 128 x) =
        truncateBits tagW (BitVec.ofNat 128 y) := bv_eq_of_toNat_eq htx
    have hbx : tagBitsToDiscrBits tagW tagS ety.discrWidth
        (truncateBits tagW (BitVec.ofNat 128 x)) = BitVec.ofNat 128 x :=
      eq_of_beq hrx
    have hby : tagBitsToDiscrBits tagW tagS ety.discrWidth
        (truncateBits tagW (BitVec.ofNat 128 y)) = BitVec.ofNat 128 y :=
      eq_of_beq hry
    rw [htbv, hby] at hbx
    have hx128 : x < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le hxlt (intWidth_pow_le_pow128 ety.discrWidth)
    have hy128 : y < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le hylt (intWidth_pow_le_pow128 ety.discrWidth)
    have htn : (BitVec.ofNat 128 y).toNat = (BitVec.ofNat 128 x).toNat :=
      congrArg BitVec.toNat hbx
    rw [bv_toNat_ofNat, bv_toNat_ofNat] at htn
    rw [nat_mod_eq_of_lt hy128, nat_mod_eq_of_lt hx128] at htn
    exact htn.symm
  have hDiscrInj : ∀ x y : Nat,
      Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth) = true →
      Nat.blt y (Nat.pow 2 ety.discrWidth.bitWidth) = true →
      discrIntOfNat ety.discrWidth ety.discrSigned x =
        discrIntOfNat ety.discrWidth ety.discrSigned y → x = y := by
    intro x y hx hy hdeq
    have hxlt : x < Nat.pow 2 ety.discrWidth.bitWidth := nat_lt_of_blt_eq_true hx
    have hylt : y < Nat.pow 2 ety.discrWidth.bitWidth := nat_lt_of_blt_eq_true hy
    have h1 := intEmodNat_decodeScalar ety.discrWidth ety.discrSigned
      (truncateBits ety.discrWidth (BitVec.ofNat 128 x))
    have h2 := intEmodNat_decodeScalar ety.discrWidth ety.discrSigned
      (truncateBits ety.discrWidth (BitVec.ofNat 128 y))
    have hx128 : x < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le hxlt (intWidth_pow_le_pow128 ety.discrWidth)
    have hy128 : y < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le hylt (intWidth_pow_le_pow128 ety.discrWidth)
    rw [truncateBits_toNat, truncateBits_toNat, bv_toNat_ofNat] at h1
    rw [nat_mod_eq_of_lt hx128, nat_mod_eq_of_lt hxlt, nat_mod_eq_of_lt hxlt] at h1
    rw [truncateBits_toNat, truncateBits_toNat, bv_toNat_ofNat] at h2
    rw [nat_mod_eq_of_lt hy128, nat_mod_eq_of_lt hylt, nat_mod_eq_of_lt hylt] at h2
    dsimp only [discrIntOfNat] at hdeq
    rw [← h1, hdeq, h2]
  have hEncodeTag := decodeInt_encodeInt (translateIntTy tagW tagS)
    (tagIntOfNat tagW tagS d) (intWidth_bitWidth_pos tagW)
    (canRepresent_decodeScalar tagW tagS (truncateBits tagW (BitVec.ofNat 128 d)))
  cases hEncodeTag with
  | intro tagBs hTagBs =>
    have hLookupVar : ∀ (ds : List Nat) (k : Nat),
        natListPairwiseNe ds = true →
        ds.all (fun x => Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth)) = true →
        Trusted.MirSemantics.getElem? ds k = some d →
        mrEncodeEnumVariant (discrIntOfNat ety.discrWidth ety.discrSigned d)
            unitValue (buildEnumVariants ety tagW tagS ds) = some tagBs ∧
          mrDecodeEnumVariant (discrIntOfNat ety.discrWidth ety.discrSigned d)
            (buildEnumVariants ety tagW tagS ds) tagBs = some unitValue := by
      intro ds
      induction ds with
      | nil => intro k _ _ hg; cases hg
      | cons x xs ih =>
        intro k hpw hall hg
        dsimp only [natListPairwiseNe, List.all] at hpw hall
        cases hne1 : natNotElem x xs with
        | false => rw [hne1] at hpw; cases hpw
        | true =>
          rw [hne1] at hpw
          cases hxlt : Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth) with
          | false => rw [hxlt] at hall; cases hall
          | true =>
            rw [hxlt] at hall
            cases k with
            | zero =>
              dsimp only [Trusted.MirSemantics.getElem?] at hg
              injection hg with hxd
              subst hxd
              dsimp only [buildEnumVariants, mrEncodeEnumVariant, mrDecodeEnumVariant]
              rw [beq_self_eq_true, if_true_eq_true, if_true_eq_true]
              dsimp only [mrEncode, emptySizedTy, mrEncodeFields, encodeDiscriminant,
                mrDecode, mrDecodeFields, unitValue]
              have hlenT : tagBs.length = tagW.byteSize := hTagBs.2.1
              rw [hTagBs.1, hlenT, Nat.beq_refl, if_not_true]
              dsimp only
              have hwr : byteWriteSubslice (List.replicate tagW.byteSize AbstractByte.uninit)
                  0 tagBs = tagBs :=
                byteWriteSubslice_zero_eq _ _ (by rw [List.length_replicate]; exact hlenT)
              rw [hwr]
              exact ⟨rfl, rfl⟩
            | succ k' =>
              dsimp only [Trusted.MirSemantics.getElem?] at hg
              have hdNotX : x ≠ d := by
                intro heq
                subst heq
                have hmem : ∀ (ys : List Nat) (idx : Nat),
                    natNotElem x ys = true →
                    Trusted.MirSemantics.getElem? ys idx = some x → False := by
                  intro ys
                  induction ys with
                  | nil => intro idx _ hg'; cases hg'
                  | cons y ys' ih' =>
                    intro idx hne' hg'
                    dsimp only [natNotElem] at hne'
                    cases idx with
                    | zero =>
                      dsimp only [Trusted.MirSemantics.getElem?] at hg'
                      injection hg' with hyx
                      subst hyx
                      rw [Nat.beq_refl] at hne'
                      cases hne'
                    | succ idx' =>
                      cases hby : !Nat.beq x y with
                      | false => rw [hby] at hne'; cases hne'
                      | true => rw [hby] at hne'; exact ih' idx' hne' hg'
                exact hmem xs k' hne1 hg
              have hdlt : Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth) = true := by
                have hallGet : ∀ (ys : List Nat) (idx : Nat),
                    ys.all (fun z => Nat.blt z (Nat.pow 2 ety.discrWidth.bitWidth)) = true →
                    Trusted.MirSemantics.getElem? ys idx = some d →
                    Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth) = true := by
                  intro ys
                  induction ys with
                  | nil => intro idx _ hg'; cases hg'
                  | cons y ys' ih' =>
                    intro idx ha' hg'
                    dsimp only [List.all] at ha'
                    cases hy : Nat.blt y (Nat.pow 2 ety.discrWidth.bitWidth) with
                    | false => rw [hy] at ha'; cases ha'
                    | true =>
                      rw [hy] at ha'
                      cases idx with
                      | zero =>
                        dsimp only [Trusted.MirSemantics.getElem?] at hg'
                        injection hg' with hyd; subst hyd; exact hy
                      | succ idx' => exact ih' idx' ha' hg'
                exact hallGet xs k' hall hg
              have hneqD : (discrIntOfNat ety.discrWidth ety.discrSigned x ==
                  discrIntOfNat ety.discrWidth ety.discrSigned d) = false := by
                cases hbeq : (discrIntOfNat ety.discrWidth ety.discrSigned x ==
                    discrIntOfNat ety.discrWidth ety.discrSigned d) with
                | false => rfl
                | true =>
                  exact False.elim (hdNotX (hDiscrInj x d hxlt hdlt (eq_of_beq hbeq)))
              dsimp only [buildEnumVariants, mrEncodeEnumVariant, mrDecodeEnumVariant]
              rw [hneqD]
              exact ih k' hpw hall hg
    have hLookupBr : ∀ (ds : List Nat) (k : Nat),
        natListPairwiseNe ds = true →
        ds.all (fun x => Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth)) = true →
        ds.all (fun x =>
          tagBitsToDiscrBits tagW tagS ety.discrWidth
            (truncateBits tagW (BitVec.ofNat 128 x)) == BitVec.ofNat 128 x) = true →
        Trusted.MirSemantics.getElem? ds k = some d →
        decodeDiscrBranches tagBs (tagIntOfNat tagW tagS d)
          (buildEnumBranches ety tagW tagS ds) =
          some (some (discrIntOfNat ety.discrWidth ety.discrSigned d)) := by
      intro ds
      induction ds with
      | nil => intro k _ _ _ hg; cases hg
      | cons x xs ih =>
        intro k hpw hall hrt hg
        dsimp only [natListPairwiseNe, List.all] at hpw hall hrt
        cases hne1 : natNotElem x xs with
        | false => rw [hne1] at hpw; cases hpw
        | true =>
          rw [hne1] at hpw
          cases hxlt : Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth) with
          | false => rw [hxlt] at hall; cases hall
          | true =>
            rw [hxlt] at hall
            cases hxrt : (tagBitsToDiscrBits tagW tagS ety.discrWidth
                (truncateBits tagW (BitVec.ofNat 128 x)) == BitVec.ofNat 128 x) with
            | false => rw [hxrt] at hrt; cases hrt
            | true =>
              rw [hxrt] at hrt
              cases k with
              | zero =>
                dsimp only [Trusted.MirSemantics.getElem?] at hg
                injection hg with hxd; subst hxd
                dsimp only [buildEnumBranches, decodeDiscrBranches]
                have hle : tagIntOfNat tagW tagS x ≤ tagIntOfNat tagW tagS x := int_le_refl _
                have hlt : tagIntOfNat tagW tagS x < tagIntOfNat tagW tagS x + 1 :=
                  int_lt_add_one_iff_le.mpr (int_le_refl _)
                rw [decide_eq_true hle, decide_eq_true hlt]
                rfl
              | succ k' =>
                dsimp only [Trusted.MirSemantics.getElem?] at hg
                have hdNotX : x ≠ d := by
                  intro heq; subst heq
                  have hmem : ∀ (ys : List Nat) (idx : Nat),
                      natNotElem x ys = true →
                      Trusted.MirSemantics.getElem? ys idx = some x → False := by
                    intro ys
                    induction ys with
                    | nil => intro idx _ hg'; cases hg'
                    | cons y ys' ih' =>
                      intro idx hne' hg'
                      dsimp only [natNotElem] at hne'
                      cases idx with
                      | zero =>
                        dsimp only [Trusted.MirSemantics.getElem?] at hg'
                        injection hg' with hyx; subst hyx
                        rw [Nat.beq_refl] at hne'; cases hne'
                      | succ idx' =>
                        cases hby : !Nat.beq x y with
                        | false => rw [hby] at hne'; cases hne'
                        | true => rw [hby] at hne'; exact ih' idx' hne' hg'
                  exact hmem xs k' hne1 hg
                have hdProps : Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth) = true ∧
                    (tagBitsToDiscrBits tagW tagS ety.discrWidth
                      (truncateBits tagW (BitVec.ofNat 128 d)) == BitVec.ofNat 128 d) = true := by
                  have hgetAll : ∀ (p : Nat → Bool) (ys : List Nat) (idx : Nat),
                      ys.all p = true →
                      Trusted.MirSemantics.getElem? ys idx = some d → p d = true := by
                    intro p ys
                    induction ys with
                    | nil => intro idx _ hg'; cases hg'
                    | cons y ys' ih' =>
                      intro idx ha' hg'
                      dsimp only [List.all] at ha'
                      cases hp : p y with
                      | false => rw [hp] at ha'; cases ha'
                      | true =>
                        rw [hp] at ha'
                        cases idx with
                        | zero =>
                          dsimp only [Trusted.MirSemantics.getElem?] at hg'
                          injection hg' with hyd; subst hyd; exact hp
                        | succ idx' => exact ih' idx' ha' hg'
                  exact ⟨hgetAll _ xs k' hall hg, hgetAll _ xs k' hrt hg⟩
                have hneqTag : tagIntOfNat tagW tagS x ≠ tagIntOfNat tagW tagS d := by
                  intro heq
                  exact hdNotX (hTagInj x d hxlt hdProps.1 hxrt hdProps.2 heq)
                have hcondFalse : (decide (tagIntOfNat tagW tagS x ≤ tagIntOfNat tagW tagS d) &&
                    decide (tagIntOfNat tagW tagS d < tagIntOfNat tagW tagS x + 1)) = false := by
                  cases hc1 : decide (tagIntOfNat tagW tagS x ≤ tagIntOfNat tagW tagS d) with
                  | false => rfl
                  | true =>
                    cases hc2 : decide (tagIntOfNat tagW tagS d < tagIntOfNat tagW tagS x + 1) with
                    | false => rfl
                    | true =>
                      have h1 := of_decide_eq_true hc1
                      have h2 := int_lt_add_one_iff_le.mp (of_decide_eq_true hc2)
                      exact False.elim (hneqTag (int_le_antisymm h1 h2))
                dsimp only [buildEnumBranches, decodeDiscrBranches]
                rw [hcondFalse]
                exact ih k' hpw hall hrt hg
    have hV := hLookupVar ety.discriminants v hdist.1 hdist.2.1 hget
    have hB := hLookupBr ety.discriminants v hdist.1 hdist.2.1 hdist.2.2 hget
    have hDiscr : decodeDiscriminant tagBs
        (.branch 0 (translateIntTy tagW tagS)
          (buildEnumBranches ety tagW tagS ety.discriminants) .invalid) =
        some (discrIntOfNat ety.discrWidth ety.discrSigned d) := by
      dsimp only [decodeDiscriminant]
      have hsub : byteSubslice tagBs 0 (translateIntTy tagW tagS).size.bytes = tagBs := by
        rw [← hTagBs.2.1]
        exact byteSubslice_zero_eq tagBs
      rw [hsub, hTagBs.2.2]
      dsimp only
      rw [hB]
    refine ⟨tagBs, ?_, hTagBs.2.1, hDiscr, ?_⟩
    · dsimp only [translateEnumTy, translateVal, mrEncode]
      rw [hrepr, hget]
      exact hV.1
    · dsimp only [translateEnumTy, translateVal, mrDecode]
      rw [hrepr, hget]
      dsimp only [mrDecode, MrType.size]
      have hlenT : tagBs.length = tagW.byteSize := hTagBs.2.1
      rw [hlenT, Nat.beq_refl, if_not_true]
      rw [hDiscr]
      dsimp only
      rw [hV.2]

/-- Master MiniRust representation round-trip theorem for every admitted Profile
v1 value and type (`bool`, `int`, `char`, `Ordering`, `unit`, admitted fieldless
`enum`, and `(int, bool)` overflow pair). -/
theorem mrEncode_mrDecode_roundtrip (ty : MirTy) (v : Val)
    (hty : isSupportedScalarOrUnitTy ty = true)
    (hv : checkVal v ty = true) :
    ∃ bs, mrEncode (translateTy ty) (translateVal v) = some bs ∧
      bs.length = (translateTy ty).size.bytes ∧
      mrDecode (translateTy ty) bs = some (translateVal v) := by
  have hvty := checkVal_ty_eq hv
  cases v with
  | bool b =>
    dsimp only [Val.ty?] at hvty
    injection hvty with heqTy
    subst heqTy
    refine ⟨[.init (if b then 1 else 0)], rfl, rfl, ?_⟩
    cases b <;> rfl
  | scalar sv =>
    dsimp only [Val.ty?] at hvty
    cases hwf : sv.wf with
    | false => rw [hwf] at hvty; cases hvty
    | true =>
      rw [hwf] at hvty
      injection hvty with heqTy
      subst heqTy
      cases sv with
      | mk svw svs svbits =>
        exact mrEncode_length_and_decode_int svw svs svbits
  | unit =>
    dsimp only [Val.ty?] at hvty
    injection hvty with heqTy
    subst heqTy
    exact ⟨[], rfl, rfl, rfl⟩
  | char c =>
    dsimp only [Val.ty?] at hvty
    injection hvty with heqTy
    subst heqTy
    have hlt32 : c.toNat < Nat.pow 2 32 := by
      dsimp only [Char.toNat]
      cases c.valid with
      | inl h => exact Nat.lt_trans h (by decide)
      | inr h => exact Nat.lt_trans h.2 (by decide)
    have hlt128 : c.toNat < Nat.pow 2 128 := Nat.lt_trans hlt32 (by decide)
    have hds : decodeScalar ⟨.i32, false, BitVec.ofNat 128 c.toNat⟩ =
        Int.ofNat c.toNat := by
      dsimp only [decodeScalar]
      rw [if_false_eq_true, truncateBits_toNat, bv_toNat_ofNat,
        nat_mod_eq_of_lt hlt128]
      dsimp only [IntWidth.bitWidth, IntWidth.byteSize]
      rw [nat_mod_eq_of_lt hlt32]
    cases mrEncode_length_and_decode_int .i32 false (BitVec.ofNat 128 c.toNat) with
    | intro bs hbs =>
      rw [hds] at hbs
      exact ⟨bs, hbs⟩
  | ordering ord =>
    dsimp only [Val.ty?] at hvty
    injection hvty with heqTy
    subst heqTy
    cases ord with
    | less => exact ⟨[.init 255], rfl, rfl, rfl⟩
    | equal => exact ⟨[.init 0], rfl, rfl, rfl⟩
    | greater => exact ⟨[.init 1], rfl, rfl, rfl⟩
  | enumVal ety' idx =>
    dsimp only [Val.ty?] at hvty
    cases h1 : enumAdmitted ety' with
    | false => rw [h1] at hvty; cases hvty
    | true =>
      cases h2 : Nat.blt idx ety'.discriminants.length with
      | false => rw [h1, h2] at hvty; cases hvty
      | true =>
        rw [h1, h2] at hvty
        injection hvty with heqTy
        subst heqTy
        dsimp only [isSupportedScalarOrUnitTy] at hty
        cases hrepr : ety'.tagRepr with
        | zeroSized =>
          have hlen1 : ety'.discriminants.length = 1 := by
            dsimp only [enumAdmitted] at hty
            rw [hrepr] at hty
            cases h1' : !ety'.discriminants.isEmpty with
            | false => rw [h1'] at hty; cases hty
            | true =>
              cases h2' : Nat.blt ety'.discriminants.length (Nat.pow 2 32) with
              | false => rw [h1', h2'] at hty; cases hty
              | true =>
                cases h3' : ety'.discriminants.all _ with
                | false => rw [h1', h2', h3'] at hty; cases hty
                | true =>
                  cases h4' : natListPairwiseNe ety'.discriminants with
                  | false => rw [h1', h2', h3', h4'] at hty; cases hty
                  | true =>
                    rw [h1', h2', h3', h4'] at hty
                    exact Nat.eq_of_beq_eq_true hty
          have hidx0 : idx = 0 := by
            have hlt := nat_lt_of_blt_eq_true h2
            rw [hlen1] at hlt
            cases idx with
            | zero => rfl
            | succ k => exact False.elim (Nat.not_lt_zero k (Nat.lt_of_succ_lt_succ hlt))
          subst hidx0
          refine ⟨[], ?_, ?_, ?_⟩
          · dsimp only [translateTy, translateEnumTy, translateVal]
            rw [hrepr]
            dsimp only [mrEncode, mrEncodeEnumVariant]
            rw [beq_self_eq_true]
            rfl
          · dsimp only [translateTy, translateEnumTy]
            rw [hrepr]
            rfl
          · dsimp only [translateTy, translateEnumTy, translateVal]
            rw [hrepr]
            dsimp only [mrDecode, decodeDiscriminant, mrDecodeEnumVariant]
            rw [beq_self_eq_true]
            rfl
        | scalar tagW tagS =>
          have hltLen : idx < ety'.discriminants.length := nat_lt_of_blt_eq_true h2
          have hgetSome : ∃ d, Trusted.MirSemantics.getElem? ety'.discriminants idx = some d := by
            have haux : ∀ (xs : List Nat) (k : Nat), k < xs.length →
                ∃ d, Trusted.MirSemantics.getElem? xs k = some d := by
              intro xs
              induction xs with
              | nil => intro k hk; cases hk
              | cons a as iha =>
                intro k hk
                cases k with
                | zero => exact ⟨a, rfl⟩
                | succ k' => exact iha k' (Nat.lt_of_succ_lt_succ hk)
            exact haux ety'.discriminants idx hltLen
          cases hgetSome with
          | intro d hd =>
            cases enum_discriminant_decode_roundtrip ety' tagW tagS hrepr hty idx d hd with
            | intro bs hbs =>
              refine ⟨bs, hbs.1, ?_, hbs.2.2.2⟩
              dsimp only [translateTy, translateEnumTy]
              rw [hrepr]
              exact hbs.2.1
  | ptr _ | slicePtr _ _ | array _ | range _ _ | rangeTo _ | rangeFrom _ | optionVal _
  | vec _ _ _ | boxPtr _ _ =>
    dsimp only [Val.ty?] at hvty
    cases hvty
  | bytes _ =>
    dsimp only [Val.ty?] at hvty
    cases hvty
  | tuple vs =>
    cases vs with
    | nil => cases hvty
    | cons v0 vrest =>
      cases v0 with
      | scalar sv =>
        cases vrest with
        | nil => cases hvty
        | cons v1 vrest2 =>
          cases v1 with
          | bool b =>
            cases vrest2 with
            | cons _ _ => cases hvty
            | nil =>
              dsimp only [Val.ty?] at hvty
              cases hwf : sv.wf with
              | false => rw [hwf] at hvty; cases hvty
              | true =>
                rw [hwf] at hvty
                injection hvty with heqTy
                subst heqTy
                cases sv with
                | mk w svs svbits =>
                  cases mrEncode_length_and_decode_int w svs svbits with
                  | intro ibs hibs =>
                    let full := ibs ++ [.init (if b then 1 else 0)] ++
                      List.replicate (w.byteSize - 1) .uninit
                    have hszPos : 1 ≤ w.byteSize := intWidth_byteSize_pos w
                    have hlenFull : full.length = 2 * w.byteSize := by
                      dsimp only [full]
                      rw [List.length_append, List.length_append, hibs.2.1,
                        List.length_replicate]
                      dsimp only [List.length]
                      rw [Nat.add_assoc, Nat.add_comm 1 (w.byteSize - 1),
                        Nat.sub_add_cancel hszPos, Nat.two_mul]
                    have hEncFull :
                        mrEncode (translateTy (.tuple [.int w svs, .bool]))
                          (translateVal (.tuple [.scalar ⟨w, svs, svbits⟩, .bool b])) =
                        some full := by
                      dsimp only [translateTy, translateVal, IntType.withOverflow,
                        mrEncode, mrEncodeFields]
                      have hEncInt : encodeInt (translateIntTy w svs)
                          (decodeScalar ⟨w, svs, svbits⟩) = some ibs := hibs.1
                      rw [hEncInt]
                      dsimp only [mrEncode, translateIntTy]
                      have hstep1 : byteWriteSubslice
                          (List.replicate (2 * w.byteSize) AbstractByte.uninit) 0 ibs =
                          ibs ++ List.replicate w.byteSize AbstractByte.uninit := by
                        dsimp only [byteWriteSubslice]
                        rw [List.take_zero, List.nil_append, Nat.zero_add, hibs.2.1]
                        have hdrop : (List.replicate (2 * w.byteSize) AbstractByte.uninit).drop
                            w.byteSize = List.replicate w.byteSize AbstractByte.uninit := by
                          have h2 : 2 * w.byteSize = w.byteSize + w.byteSize := Nat.two_mul w.byteSize
                          rw [h2, list_replicate_add]
                          have hda : ∀ (l1 l2 : List AbstractByte), (l1 ++ l2).drop l1.length = l2 := by
                            intro l1 l2
                            induction l1 with
                            | nil => rfl
                            | cons _ xs ih => exact ih
                          have hdl := hda (List.replicate w.byteSize AbstractByte.uninit)
                            (List.replicate w.byteSize AbstractByte.uninit)
                          rw [List.length_replicate] at hdl
                          exact hdl
                        rw [hdrop]
                      rw [hstep1]
                      dsimp only [byteWriteSubslice, full]
                      have htake : (ibs ++ List.replicate w.byteSize AbstractByte.uninit).take
                          w.byteSize = ibs := by
                        have hta : ∀ (l1 l2 : List AbstractByte), (l1 ++ l2).take l1.length = l1 := by
                          intro l1 l2
                          induction l1 with
                          | nil => rfl
                          | cons x xs ih => dsimp only [List.cons_append, List.length, List.take]; rw [ih]
                        have htl := hta ibs (List.replicate w.byteSize AbstractByte.uninit)
                        rw [hibs.2.1] at htl
                        exact htl
                      have hdrop2 : (ibs ++ List.replicate w.byteSize AbstractByte.uninit).drop
                          (w.byteSize + 1) = List.replicate (w.byteSize - 1) AbstractByte.uninit := by
                        have hda : ∀ (l1 l2 : List AbstractByte) (k : Nat),
                            (l1 ++ l2).drop (l1.length + k) = l2.drop k := by
                          intro l1 l2 k
                          induction l1 with
                          | nil => rw [List.nil_append, List.length_nil, Nat.zero_add]
                          | cons _ xs ih =>
                            dsimp only [List.cons_append, List.length]
                            rw [Nat.succ_add]
                            exact ih
                        have hd := hda ibs (List.replicate w.byteSize AbstractByte.uninit) 1
                        rw [hibs.2.1] at hd
                        rw [hd]
                        cases hw1 : w.byteSize with
                        | zero => rw [hw1] at hszPos; cases hszPos
                        | succ m => rfl
                      dsimp only [List.length]
                      rw [htake, hdrop2]
                    refine ⟨full, hEncFull, hlenFull, ?_⟩
                    dsimp only [translateTy, translateVal, IntType.withOverflow,
                      mrDecode, mrDecodeFields, MrType.size, translateIntTy]
                    rw [hlenFull, Nat.beq_refl, if_not_true]
                    have hsub0 : byteSubslice full 0 w.byteSize = ibs := by
                      dsimp only [byteSubslice, full]
                      rw [List.append_assoc]
                      have hta : ∀ (l1 l2 : List AbstractByte), (l1 ++ l2).take l1.length = l1 := by
                        intro l1 l2
                        induction l1 with
                        | nil => rfl
                        | cons x xs ih => dsimp only [List.cons_append, List.length, List.take]; rw [ih]
                      have htl := hta ibs ([.init (if b then 1 else 0)] ++ List.replicate (w.byteSize - 1) .uninit)
                      rw [hibs.2.1] at htl
                      exact htl
                    have hsub1 : byteSubslice full w.byteSize 1 = [.init (if b then 1 else 0)] := by
                      dsimp only [byteSubslice, full]
                      rw [List.append_assoc]
                      have hda : ∀ (l1 l2 : List AbstractByte), (l1 ++ l2).drop l1.length = l2 := by
                        intro l1 l2
                        induction l1 with
                        | nil => rfl
                        | cons _ xs ih => exact ih
                      have hd := hda ibs ([.init (if b then 1 else 0)] ++ List.replicate (w.byteSize - 1) .uninit)
                      rw [hibs.2.1] at hd
                      rw [hd]
                      rfl
                    have hDecInt : decodeInt (translateIntTy w svs) ibs =
                        some (decodeScalar ⟨w, svs, svbits⟩) := by
                      have hmd := hibs.2.2
                      dsimp only [mrDecode] at hmd
                      cases hd : decodeInt (translateIntTy w svs) ibs with
                      | none => rw [hd] at hmd; cases hmd
                      | some iv =>
                        rw [hd] at hmd
                        injection hmd with hvEq
                        injection hvEq with hivEq
                        rw [hivEq]
                    dsimp only [translateIntTy] at hDecInt
                    rw [hsub0, hDecInt, hsub1]
                    cases b <;> rfl
          | _ => cases hvty
      | _ => cases hvty

/-- Decoding all-`.uninit` bytes at any non-ZST admitted type returns `none`,
causing MiniRust to raise UB on uninitialized loads. -/
theorem mrDecode_replicate_uninit_none (ty : MirTy)
    (hty : isSupportedScalarOrUnitTy ty = true)
    (hnonZst : isInhabitedZstTy ty = false) :
    mrDecode (translateTy ty)
      (List.replicate (translateTy ty).size.bytes AbstractByte.uninit) = none := by
  cases ty with
  | bool => rfl
  | int w s =>
    dsimp only [translateTy, mrDecode, MrType.size]
    rw [decodeInt_replicate_uninit (translateIntTy w s) (intWidth_byteSize_pos w)]
  | char =>
    dsimp only [translateTy, mrDecode, MrType.size]
    rw [decodeInt_replicate_uninit u32Ty (by decide)]
  | ordering => rfl
  | never => rfl
  | unit => cases hnonZst
  | vec _ | box _ | struct_ _ _ => cases hty
  | enum ety =>
    dsimp only [isSupportedScalarOrUnitTy] at hty
    dsimp only [isInhabitedZstTy, isZstEnumTy] at hnonZst
    cases hrepr : ety.tagRepr with
    | zeroSized =>
      rw [hrepr, hty] at hnonZst
      cases hnonZst
    | scalar tagW tagS =>
      dsimp only [translateTy, translateEnumTy]
      rw [hrepr]
      dsimp only [mrDecode, MrType.size]
      rw [List.length_replicate, Nat.beq_refl, if_not_true]
      dsimp only [decodeDiscriminant]
      have hsub : byteSubslice (List.replicate tagW.byteSize AbstractByte.uninit)
          0 (translateIntTy tagW tagS).size.bytes =
          List.replicate tagW.byteSize AbstractByte.uninit := by
        have h := byteSubslice_zero_eq (List.replicate tagW.byteSize AbstractByte.uninit)
        rw [List.length_replicate] at h
        exact h
      rw [hsub]
      have hdec : decodeInt (translateIntTy tagW tagS)
          (List.replicate tagW.byteSize AbstractByte.uninit) = none :=
        decodeInt_replicate_uninit (translateIntTy tagW tagS) (intWidth_byteSize_pos tagW)
      rw [hdec]
  | tuple fs =>
    dsimp only [isSupportedScalarOrUnitTy, isOverflowPairTy] at hty
    cases fs with
    | nil => cases hty
    | cons t0 rest =>
      cases t0 with
      | int w s =>
        cases rest with
        | nil => cases hty
        | cons t1 rest2 =>
          cases t1 with
          | bool =>
            cases rest2 with
            | cons _ _ => cases hty
            | nil =>
              dsimp only [translateTy, IntType.withOverflow, mrDecode, MrType.size,
                mrDecodeFields, translateIntTy]
              rw [List.length_replicate, Nat.beq_refl, if_not_true]
              have hsub : byteSubslice (List.replicate (2 * w.byteSize) AbstractByte.uninit)
                  0 w.byteSize = List.replicate w.byteSize AbstractByte.uninit := by
                dsimp only [byteSubslice]
                have h2 : 2 * w.byteSize = w.byteSize + w.byteSize := Nat.two_mul w.byteSize
                rw [h2, list_replicate_add]
                have hta : ∀ (l1 l2 : List AbstractByte), (l1 ++ l2).take l1.length = l1 := by
                  intro l1 l2
                  induction l1 with
                  | nil => rfl
                  | cons x xs ih => dsimp only [List.cons_append, List.length, List.take]; rw [ih]
                have h := hta (List.replicate w.byteSize AbstractByte.uninit)
                  (List.replicate w.byteSize AbstractByte.uninit)
                rw [List.length_replicate] at h
                exact h
              rw [hsub]
              have hd : decodeInt (translateIntTy w s)
                  (List.replicate w.byteSize AbstractByte.uninit) = none :=
                decodeInt_replicate_uninit (translateIntTy w s) (intWidth_byteSize_pos w)
              dsimp only [translateIntTy] at hd
              rw [hd]
          | _ => cases hty
      | _ => cases hty
  | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | range _ | rangeTo _ | rangeFrom _
  | option _ | unsupported =>
    cases hty

/-- Valid size and positive alignment hold for every translated type. -/
theorem translateTy_validSize_and_alignPos (ty : MirTy)
    (hty : isSupportedScalarOrUnitTy ty = true) :
    validSize (translateTy ty).size = true ∧ 0 < (translateTy ty).align.bytes := by
  cases ty with
  | bool | char | ordering | unit | never => exact ⟨by decide, by decide⟩
  | int w s =>
    dsimp only [translateTy, translateIntTy, MrType.size, MrType.align]
    cases w <;> exact ⟨by decide, by decide⟩
  | enum ety =>
    dsimp only [translateTy, translateEnumTy]
    cases ety.tagRepr with
    | zeroSized =>
      dsimp only [MrType.size, MrType.align]
      exact ⟨by decide, by decide⟩
    | scalar tagW _ =>
      dsimp only [MrType.size, MrType.align]
      cases tagW <;> exact ⟨by decide, by decide⟩
  | tuple fs =>
    dsimp only [isSupportedScalarOrUnitTy, isOverflowPairTy] at hty
    cases fs with
    | nil => cases hty
    | cons t0 rest =>
      cases t0 with
      | int w _ =>
        cases rest with
        | nil => cases hty
        | cons t1 rest2 =>
          cases t1 with
          | bool =>
            cases rest2 with
            | cons _ _ => cases hty
            | nil =>
              dsimp only [translateTy, translateIntTy, IntType.withOverflow,
                MrType.size, MrType.align]
              cases w <;> exact ⟨by decide, by decide⟩
          | _ => cases hty
      | _ => cases hty
  | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | range _ | rangeTo _ | rangeFrom _
  | option _ | vec _ | box _ | unsupported | struct_ _ _ =>
    cases hty

/-! ## State Relation (`StateRel`) and Memory Invariants -/

/-- A thin pointer `ptr` names a live, aligned, whole-object allocation in `mem`
matching `ty`'s size and alignment, with byte contents `data`. -/
def AllocLiveAt (mem : MrMemory) (ty : MrType) (ptr : ThinPtr)
    (id : AllocId) (data : List AbstractByte) : Prop :=
  ptr.allocId = some id ∧
    ∃ alloc : MrAllocation,
      listGet? mem.allocations id = some alloc ∧
      alloc.allocId = id ∧
      alloc.addr = ptr.addr ∧
      alloc.live = true ∧
      alloc.align = ty.align ∧
      ty.align.isAligned ptr.addr = true ∧
      alloc.data = data ∧
      data.length = ty.size.bytes

/-- Per-local slot relation between an Anneal `LocalSlot` and a MiniRust local
allocation in `calleeFrame.locals` and `mem`.
- When `exact = false`, uninitialized non-ZST Anneal slots permit arbitrary
  bytes in MiniRust (covering conservative `Operand.move` deinitialization).
- When `exact = true`, uninitialized non-ZST Anneal slots require all-`.uninit`
  bytes in MiniRust so MiniRust raises UB iff Anneal faults `.undefined`. -/
def SlotRel (exact : Bool) (mem : MrMemory) (ty : MirTy)
    (slot : LocalSlot) (optPtr : Option ThinPtr) : Prop :=
  match slot with
  | .dead => optPtr = none
  | .indirect _ | .partialTuple _ => False
  | .immediate optVal =>
    ∃ (ptr : ThinPtr) (id : AllocId) (data : List AbstractByte),
      optPtr = some ptr ∧
      AllocLiveAt mem (translateTy ty) ptr id data ∧
      match optVal with
      | some v =>
        checkVal v ty = true ∧
        mrDecode (translateTy ty) data = some (translateVal v)
      | none =>
        isInhabitedZstTy ty = false ∧
        (exact = true → data = List.replicate (translateTy ty).size.bytes .uninit)

/-- No duplicate keys in `LocalMap`. -/
def LocalMapNoDup : LocalMap → Prop
  | [] => True
  | (k, _) :: rest => localMapGet? k rest = none ∧ LocalMapNoDup rest

/-- Full state coupling relation between Anneal `State` and MiniRust `Machine`
after `initBlock` completes (`StateRel exact p s m`). -/
def StateRel (exact : Bool) (p : Program) (s : State)
    (m : Machine) : Prop :=
  p.pointerWidthBits = 64 ∧
  p.mirProfileVersion = 1 ∧
  s.callerMem.allocations = [] ∧
  ∃ (body : Body) (frame : FrameState) (calleeFrame callerFrame : StackFrame)
      (callerRetPtr : ThinPtr) (callerRetId : AllocId)
      (callerRetData : List AbstractByte) (retMirTy : MirTy),
    Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body ∧
    bodyAdmittedWith exact body = true ∧
    Trusted.MirSemantics.getElem? body.locals 0 = some retMirTy ∧
    s.frames = [frame] ∧
    frame.defId = p.entryDefId ∧
    frame.sysrootOp? = none ∧
    frame.locals.length = body.locals.length ∧
    frame.blockIdx < body.basicBlocks.length ∧
    m.prog = translateProg p ∧
    m.stack = [calleeFrame, callerFrame] ∧
    calleeFrame.func = translateBody body ∧
    calleeFrame.nextBlock = frame.blockIdx + 1 ∧
    calleeFrame.nextStmt = frame.stmtIdx ∧
    calleeFrame.stackPopAction = .backToCaller callerRetPtr (some 0) ∧
    callerFrame = {
      func := harnessCallerFunc (translateTy retMirTy)
      locals := [(0, callerRetPtr)]
      stackPopAction := .bottomOfStack
      nextBlock := 0
      nextStmt := 0
    } ∧
    AllocLiveAt m.mem (translateTy retMirTy) callerRetPtr callerRetId callerRetData ∧
    LocalMapNoDup calleeFrame.locals ∧
    -- Return place `_0` is always live.
    (∃ optRet, Trusted.MirSemantics.getElem? frame.locals 0 = some (.immediate optRet)) ∧
    -- Every local in `calleeFrame.locals` is in bounds and live in Anneal.
    (∀ k ptr, localMapGet? k calleeFrame.locals = some ptr →
      k < body.locals.length ∧
      ∃ optV, Trusted.MirSemantics.getElem? frame.locals k = some (.immediate optV)) ∧
    -- Per-local slot relation for every local index.
    (∀ i ty slot,
      Trusted.MirSemantics.getElem? body.locals i = some ty →
      Trusted.MirSemantics.getElem? frame.locals i = some slot →
      SlotRel exact m.mem ty slot (localMapGet? i calleeFrame.locals)) ∧
    -- Every live callee local has an allocation disjoint from `callerRetId`
    -- and pairwise disjoint from every other live callee local.
    (∀ i ptr id,
      localMapGet? i calleeFrame.locals = some ptr →
      ptr.allocId = some id →
      id ≠ callerRetId ∧
      ∀ j ptr' id',
        i ≠ j →
        localMapGet? j calleeFrame.locals = some ptr' →
        ptr'.allocId = some id' →
        id ≠ id')

/-! ## Helper Lemmas for `LocalMap` and `AllocLiveAt` -/

theorem localMapRemove_spec (k : LocalName) (m : LocalMap)
    (hnd : LocalMapNoDup m) :
    (localMapRemove k m).1 = localMapGet? k m ∧
    localMapGet? k (localMapRemove k m).2 = none ∧
    (∀ j, j ≠ k → localMapGet? j (localMapRemove k m).2 = localMapGet? j m) ∧
    LocalMapNoDup (localMapRemove k m).2 := by
  induction m with
  | nil => exact ⟨rfl, rfl, fun _ _ => rfl, True.intro⟩
  | cons p rest ih =>
    cases p with
    | mk k' ptr =>
      cases hnd with
      | intro hfresh hndRest =>
        cases ih hndRest with
        | intro h1 hrest =>
          cases hrest with
          | intro h2 hrest2 =>
            cases hrest2 with
            | intro h3 h4 =>
              dsimp only [localMapRemove, localMapGet?]
              cases hbeq : Nat.beq k' k with
              | true =>
                rw [if_true_eq_true, if_true_eq_true]
                have heq : k' = k := Nat.eq_of_beq_eq_true hbeq
                subst heq
                refine ⟨rfl, hfresh, fun j hne => ?_, hndRest⟩
                have hbeqJ : Nat.beq k' j = false := by
                  cases hb : Nat.beq k' j with
                  | false => rfl
                  | true => exact False.elim (hne (Nat.eq_of_beq_eq_true hb).symm)
                rw [hbeqJ, if_false_eq_true]
              | false =>
                rw [if_false_eq_true, if_false_eq_true]
                have hne : k' ≠ k := by
                  intro heq; subst heq; rw [Nat.beq_refl] at hbeq; cases hbeq
                refine ⟨h1, ?_, fun j hnej => ?_, ?_⟩
                · dsimp only [localMapGet?]
                  rw [hbeq, if_false_eq_true]
                  exact h2
                · dsimp only [localMapGet?]
                  cases hbeqJ : Nat.beq k' j with
                  | true => rfl
                  | false => exact h3 j hnej
                · refine ⟨?_, h4⟩
                  rw [h3 k' hne]
                  exact hfresh

theorem localMapInsert_spec (k : LocalName) (ptr : ThinPtr) (m : LocalMap)
    (hnd : LocalMapNoDup m) :
    localMapGet? k (localMapInsert k ptr m) = some ptr ∧
    (∀ j, j ≠ k → localMapGet? j (localMapInsert k ptr m) = localMapGet? j m) ∧
    LocalMapNoDup (localMapInsert k ptr m) := by
  cases localMapRemove_spec k m hnd with
  | intro _ hrest =>
    cases hrest with
    | intro h2 hrest2 =>
      cases hrest2 with
      | intro h3 h4 =>
        refine ⟨?_, fun j hne => ?_, ⟨h2, h4⟩⟩
        · dsimp only [localMapInsert, localMapGet?]
          rw [Nat.beq_refl]
          rfl
        · dsimp only [localMapInsert, localMapGet?]
          have hbeq : Nat.beq k j = false := by
            cases hb : Nat.beq k j with
            | false => rfl
            | true => exact False.elim (hne (Nat.eq_of_beq_eq_true hb).symm)
          rw [hbeq, if_false_eq_true]
          exact h3 j hne

theorem align_one_isAligned (addr : Nat) : Align.isAligned ⟨1⟩ addr = true := by
  dsimp only [Align.isAligned]
  rw [nat_mod_one]
  rfl

theorem allocLiveAt_load (mem : MrMemory) (ty : MrType) (ptr : ThinPtr)
    (id : AllocId) (data : List AbstractByte) (al : Align)
    (hlive : AllocLiveAt mem ty ptr id data)
    (hal : al.isAligned ptr.addr = true) :
    mem.load ptr ty.size al = .ok data := by
  cases hlive with
  | intro hpid hex =>
    cases hex with
    | intro alloc ha =>
      cases ha with
      | intro hget ha1 =>
        cases ha1 with
        | intro _ ha2 =>
          cases ha2 with
          | intro haddr ha3 =>
            cases ha3 with
            | intro halive ha4 =>
              cases ha4 with
              | intro _ ha5 =>
                cases ha5 with
                | intro _ ha6 =>
                  cases ha6 with
                  | intro hdata hlen =>
                    dsimp only [MrMemory.load]
                    rw [hal, if_not_true]
                    dsimp only [MrMemory.checkPtr]
                    cases hsz : Nat.beq ty.size.bytes 0 with
                    | true =>
                      rw [if_true_eq_true]
                      have hz : ty.size.bytes = 0 := Nat.eq_of_beq_eq_true hsz
                      rw [hz] at hlen
                      cases data with
                      | nil => rfl
                      | cons _ _ => cases hlen
                    | false =>
                      rw [if_false_eq_true, hpid]
                      dsimp only
                      rw [hget]
                      dsimp only
                      rw [halive, haddr]
                      have hblt : Nat.blt ptr.addr ptr.addr = false := by
                        cases hb : Nat.blt ptr.addr ptr.addr with
                        | false => rfl
                        | true => exact False.elim (Nat.lt_irrefl _ (nat_lt_of_blt_eq_true hb))
                      rw [hblt, Nat.sub_self, Nat.zero_add, hdata, hlen,
                        Nat.ble_eq_true_of_le (Nat.le_refl _),
                        if_not_true, if_false_eq_true, if_not_true]
                      dsimp only
                      rw [hget]
                      dsimp only
                      rw [hdata, ← hlen, byteSubslice_zero_eq]

theorem allocLiveAt_typedLoad (mem : MrMemory) (ty : MrType) (ptr : ThinPtr)
    (id : AllocId) (data : List AbstractByte) (al : Align)
    (hlive : AllocLiveAt mem ty ptr id data)
    (hal : al.isAligned ptr.addr = true) :
    typedLoad mem ptr ty al =
      match mrDecode ty data with
      | none =>
        .error (.ub
          "load at type but the data in memory violates the language invariant")
      | some v => .ok v := by
  dsimp only [typedLoad]
  rw [allocLiveAt_load mem ty ptr id data al hlive hal]
  rfl

theorem allocLiveAt_store (mem : MrMemory) (ty : MrType) (ptr : ThinPtr)
    (id : AllocId) (data newData : List AbstractByte) (al : Align)
    (hlive : AllocLiveAt mem ty ptr id data)
    (hal : al.isAligned ptr.addr = true)
    (hlenNew : newData.length = ty.size.bytes) :
    ∃ mem', mem.store ptr newData al = .ok mem' ∧
      AllocLiveAt mem' ty ptr id newData ∧
      ∀ ty' ptr' id' data', id' ≠ id →
        AllocLiveAt mem ty' ptr' id' data' →
        AllocLiveAt mem' ty' ptr' id' data' := by
  cases hlive with
  | intro hpid hex =>
    cases hex with
    | intro alloc ha =>
      cases ha with
      | intro hget ha1 =>
        cases ha1 with
        | intro haid ha2 =>
          cases ha2 with
          | intro haddr ha3 =>
            cases ha3 with
            | intro halive ha4 =>
              cases ha4 with
              | intro halign ha5 =>
                cases ha5 with
                | intro hptral ha6 =>
                  cases ha6 with
                  | intro hdata hlen =>
                    dsimp only [MrMemory.store]
                    rw [hal, if_not_true]
                    dsimp only [MrMemory.checkPtr]
                    rw [hlenNew]
                    cases hsz : Nat.beq ty.size.bytes 0 with
                    | true =>
                      rw [if_true_eq_true]
                      have hz : ty.size.bytes = 0 := Nat.eq_of_beq_eq_true hsz
                      have hlen0 : data.length = 0 := Eq.trans hlen hz
                      have hlenNew0 : newData.length = 0 := Eq.trans hlenNew hz
                      have hdn : data = [] := by
                        cases data with | nil => rfl | cons _ _ => cases hlen0
                      have hnn : newData = [] := by
                        cases newData with | nil => rfl | cons _ _ => cases hlenNew0
                      subst hdn; subst hnn
                      refine ⟨mem, rfl,
                        ⟨hpid, alloc, hget, haid, haddr, halive, halign, hptral, hdata, hlen⟩,
                        fun _ _ _ _ _ h => h⟩
                    | false =>
                      rw [if_false_eq_true, hpid]
                      dsimp only
                      rw [hget]
                      dsimp only
                      rw [halive, haddr]
                      have hblt : Nat.blt ptr.addr ptr.addr = false := by
                        cases hb : Nat.blt ptr.addr ptr.addr with
                        | false => rfl
                        | true => exact False.elim (Nat.lt_irrefl _ (nat_lt_of_blt_eq_true hb))
                      rw [hblt, Nat.sub_self, Nat.zero_add, hdata, hlen,
                        Nat.ble_eq_true_of_le (Nat.le_refl _),
                        if_not_true, if_false_eq_true, if_not_true]
                      dsimp only
                      rw [hget]
                      dsimp only
                      rw [hdata]
                      have hwr : byteWriteSubslice data 0 newData = newData :=
                        byteWriteSubslice_zero_eq data newData (Eq.trans hlenNew hlen.symm)
                      rw [hwr]
                      cases listSet?_some_of_get?_some mem.allocations id
                          { alloc with data := newData } alloc hget with
                      | intro allocs' hallocs' =>
                        rw [hallocs']
                        refine ⟨{ mem with allocations := allocs' }, rfl, ?_, ?_⟩
                        · refine ⟨hpid, { alloc with data := newData },
                            listGet?_set_eq _ _ _ _ hallocs', haid, haddr, halive,
                            halign, hptral, rfl, hlenNew⟩
                        · intro ty' ptr' id' data' hne hother
                          cases hother with
                          | intro hpid' hex' =>
                            cases hex' with
                            | intro alloc' ha' =>
                              refine ⟨hpid', alloc', ?_, ha'.2⟩
                              rw [listGet?_set_ne _ _ _ _ _ hallocs' (fun heq => hne heq.symm)]
                              exact ha'.1

theorem allocLiveAt_allocate (mem : MrMemory) (ty : MrType)
    (hvsz : validSize ty.size = true) (halPos : 0 < ty.align.bytes) :
    ∃ mem' ptr, mem.allocate ty.size ty.align = .ok (mem', ptr) ∧
      AllocLiveAt mem' ty ptr mem.allocations.length
        (List.replicate ty.size.bytes .uninit) ∧
      ∀ ty' ptr' id' data',
        AllocLiveAt mem ty' ptr' id' data' →
        id' ≠ mem.allocations.length ∧
        AllocLiveAt mem' ty' ptr' id' data' := by
  have hne0 : Nat.beq ty.align.bytes 0 = false := by
    cases ha : ty.align.bytes with
    | zero => rw [ha] at halPos; cases halPos
    | succ _ => rfl
  dsimp only [MrMemory.allocate]
  rw [hvsz, hne0, if_not_true, if_false_eq_true]
  let base := alignUp mem.nextAddr ty.align.bytes
  let stepBytes := if Nat.beq ty.size.bytes 0 then 1 else ty.size.bytes
  let newAlloc : MrAllocation := {
    allocId := mem.allocations.length
    addr := base
    align := ty.align
    live := true
    data := List.replicate ty.size.bytes .uninit
  }
  let mem' : MrMemory := {
    nextAddr := base + stepBytes
    allocations := mem.allocations ++ [newAlloc]
  }
  refine ⟨mem', ⟨some mem.allocations.length, base⟩, rfl, ?_, ?_⟩
  · refine ⟨rfl, newAlloc, listGet?_append_singleton mem.allocations newAlloc,
      rfl, rfl, rfl, rfl, ?_, rfl, List.length_replicate⟩
    exact alignUp_aligned mem.nextAddr ty.align.bytes halPos
  · intro ty' ptr' id' data' hother
    cases hother with
    | intro hpid' hex' =>
      cases hex' with
      | intro alloc' ha' =>
        have hlt : id' < mem.allocations.length :=
          listGet?_lt_length mem.allocations id' alloc' ha'.1
        refine ⟨Nat.ne_of_lt hlt, hpid', alloc',
          listGet?_append_left mem.allocations [newAlloc] id' alloc' ha'.1, ha'.2⟩

theorem allocLiveAt_deallocate (mem : MrMemory) (ty : MrType) (ptr : ThinPtr)
    (id : AllocId) (data : List AbstractByte)
    (hlive : AllocLiveAt mem ty ptr id data) :
    ∃ mem', mem.deallocate ptr ty.size ty.align = .ok mem' ∧
      ∀ ty' ptr' id' data', id' ≠ id →
        AllocLiveAt mem ty' ptr' id' data' →
        AllocLiveAt mem' ty' ptr' id' data' := by
  cases hlive with
  | intro hpid hex =>
    cases hex with
    | intro alloc ha =>
      cases ha with
      | intro hget ha1 =>
        cases ha1 with
        | intro _ ha2 =>
          cases ha2 with
          | intro haddr ha3 =>
            cases ha3 with
            | intro halive ha4 =>
              cases ha4 with
              | intro halign ha5 =>
                cases ha5 with
                | intro _ ha6 =>
                  cases ha6 with
                  | intro hdata hlen =>
                    dsimp only [MrMemory.deallocate]
                    rw [hpid]
                    dsimp only
                    rw [hget]
                    dsimp only
                    rw [halive, haddr, hdata, hlen, halign,
                      Nat.beq_refl, Nat.beq_refl, Nat.beq_refl,
                      if_not_true, if_not_true, if_not_true, if_not_true]
                    cases listSet?_some_of_get?_some mem.allocations id
                        { allocId := alloc.allocId, addr := ptr.addr, align := ty.align,
                          live := false, data := data } alloc hget with
                    | intro allocs' hallocs' =>
                      rw [hallocs']
                      refine ⟨{ mem with allocations := allocs' }, rfl, ?_⟩
                      intro ty' ptr' id' data' hne hother
                      cases hother with
                      | intro hpid' hex' =>
                        cases hex' with
                        | intro alloc' ha' =>
                          refine ⟨hpid', alloc', ?_, ha'.2⟩
                          rw [listGet?_set_ne _ _ _ _ _ hallocs' (fun heq => hne heq.symm)]
                          exact ha'.1

/-! ## List and `StorageLive`/`StorageDead` Frame Lemmas -/

theorem getElem?_eq_listGet? {α : Type} (xs : List α) (i : Nat) :
    Trusted.MirSemantics.getElem? xs i = listGet? xs i := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

theorem listGet?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    listGet? (xs.map f) i = (listGet? xs i).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

theorem listGet?_all {α : Type} (p : α → Bool) (xs : List α) (i : Nat) (x : α)
    (hall : xs.all p = true) (hget : listGet? xs i = some x) :
    p x = true := by
  induction xs generalizing i with
  | nil => cases hget
  | cons a as ih =>
    dsimp only [List.all] at hall
    cases ha : p a with
    | false => rw [ha] at hall; cases hall
    | true =>
      rw [ha] at hall
      cases i with
      | zero =>
        dsimp only [listGet?] at hget
        injection hget with hax
        subst hax
        exact ha
      | succ k => exact ih k hall hget

theorem listGet?_some_of_lt {α : Type} (xs : List α) (i : Nat)
    (hlt : i < xs.length) :
    ∃ x, listGet? xs i = some x := by
  induction xs generalizing i with
  | nil => cases hlt
  | cons a as ih =>
    cases i with
    | zero => exact ⟨a, rfl⟩
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ hlt)

theorem liveUninitSlot_isImmediate (ty : MirTy) :
    ∃ optV, liveUninitSlot ty = .immediate optV := by
  cases ty with
  | unit => exact ⟨some .unit, rfl⟩
  | enum ety =>
    dsimp only [liveUninitSlot]
    cases isZstEnumTy ety with
    | true => exact ⟨some (.enumVal ety 0), rfl⟩
    | false => exact ⟨none, rfl⟩
  | bool => exact ⟨none, rfl⟩
  | int _ _ => exact ⟨none, rfl⟩
  | never => exact ⟨none, rfl⟩
  | char => exact ⟨none, rfl⟩
  | ordering => exact ⟨none, rfl⟩
  | ref _ _ => exact ⟨none, rfl⟩
  | rawPtr _ _ | slice _ | str | array _ _ | range _ | rangeTo _ | rangeFrom _
  | option _ | vec _ | box _ | struct_ _ _ => exact ⟨none, rfl⟩
  | tuple _ => exact ⟨none, rfl⟩
  | unsupported => exact ⟨none, rfl⟩

theorem liveUninitSlot_slotRel (exact : Bool) (mem : MrMemory) (ty : MirTy)
    (ptr : ThinPtr) (id : AllocId)
    (hty : isSupportedScalarOrUnitTy ty = true)
    (hlive : AllocLiveAt mem (translateTy ty) ptr id
      (List.replicate (translateTy ty).size.bytes .uninit)) :
    SlotRel exact mem ty (liveUninitSlot ty) (some ptr) := by
  cases ty with
  | unit =>
    refine ⟨ptr, id, [], rfl, hlive, rfl, rfl⟩
  | enum ety =>
    dsimp only [isSupportedScalarOrUnitTy] at hty
    dsimp only [liveUninitSlot]
    cases hz : isZstEnumTy ety with
    | true =>
      have hrepr : ety.tagRepr = .zeroSized := by
        dsimp only [isZstEnumTy] at hz
        cases hr : ety.tagRepr with
        | zeroSized => rfl
        | scalar _ _ => rw [hr] at hz; cases hz
      have hlen1 : ety.discriminants.length = 1 := by
        dsimp only [enumAdmitted] at hty
        rw [hrepr] at hty
        cases h1 : !ety.discriminants.isEmpty with
        | false => rw [h1] at hty; cases hty
        | true =>
          cases h2 : Nat.blt ety.discriminants.length (Nat.pow 2 32) with
          | false => rw [h1, h2] at hty; cases hty
          | true =>
            cases h3 : ety.discriminants.all _ with
            | false => rw [h1, h2, h3] at hty; cases hty
            | true =>
              cases h4 : natListPairwiseNe ety.discriminants with
              | false => rw [h1, h2, h3, h4] at hty; cases hty
              | true =>
                rw [h1, h2, h3, h4] at hty
                exact Nat.eq_of_beq_eq_true hty
      have hcv : checkVal (.enumVal ety 0) (.enum ety) = true := by
        dsimp only [checkVal, Val.ty?]
        rw [hty, hlen1]
        have hblt01 : Nat.blt 0 1 = true := rfl
        rw [hblt01]
        have heqRefl : ∀ e : EnumTy, EnumTy.beq e e = true := by
          intro e
          cases e with
          | mk eid dw ds tr dl =>
            dsimp only [EnumTy.beq]
            have hdw : IntWidth.beq dw dw = true := by cases dw <;> rfl
            have hds : (ds == ds) = true := by cases ds <;> rfl
            have htr : EnumTagRepr.beq tr tr = true := by
              cases tr with
              | zeroSized => rfl
              | scalar tw ts =>
                dsimp only [EnumTagRepr.beq]
                have htw : IntWidth.beq tw tw = true := by cases tw <;> rfl
                have hts : (ts == ts) = true := by cases ts <;> rfl
                rw [htw, hts]; rfl
            have hdl : ∀ xs : List Nat, natListBeq xs xs = true := by
              intro xs
              induction xs with
              | nil => rfl
              | cons a as iha => dsimp only [natListBeq]; rw [Nat.beq_refl]; exact iha
            rw [Nat.beq_refl, hdw, hds, htr, hdl dl]; rfl
        exact heqRefl ety
      have hsz0 : (translateTy (.enum ety)).size.bytes = 0 := by
        dsimp only [translateTy, translateEnumTy]
        rw [hrepr]; rfl
      refine ⟨ptr, id, List.replicate (translateTy (.enum ety)).size.bytes .uninit,
        rfl, hlive, hcv, ?_⟩
      rw [hsz0]
      dsimp only [List.replicate, translateTy, translateEnumTy, translateVal]
      rw [hrepr]
      dsimp only [mrDecode, decodeDiscriminant, mrDecodeEnumVariant]
      rw [beq_self_eq_true]
      rfl
    | false =>
      refine ⟨ptr, id, List.replicate (translateTy (.enum ety)).size.bytes .uninit,
        rfl, hlive, hz, fun _ => rfl⟩
  | bool =>
    exact ⟨ptr, id, List.replicate (translateTy .bool).size.bytes .uninit,
      rfl, hlive, rfl, fun _ => rfl⟩
  | int w s =>
    exact ⟨ptr, id, List.replicate (translateTy (.int w s)).size.bytes .uninit,
      rfl, hlive, rfl, fun _ => rfl⟩
  | never =>
    exact ⟨ptr, id, List.replicate (translateTy .never).size.bytes .uninit,
      rfl, hlive, rfl, fun _ => rfl⟩
  | char =>
    exact ⟨ptr, id, List.replicate (translateTy .char).size.bytes .uninit,
      rfl, hlive, rfl, fun _ => rfl⟩
  | ordering =>
    exact ⟨ptr, id, List.replicate (translateTy .ordering).size.bytes .uninit,
      rfl, hlive, rfl, fun _ => rfl⟩
  | tuple fs =>
    exact ⟨ptr, id, List.replicate (translateTy (.tuple fs)).size.bytes .uninit,
      rfl, hlive, rfl, fun _ => rfl⟩
  | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | range _ | rangeTo _ | rangeFrom _
  | option _ | vec _ | box _ | unsupported | struct_ _ _ =>
    cases hty

theorem localMapRemove_of_none (k : LocalName) (m : LocalMap)
    (h : localMapGet? k m = none) :
    localMapRemove k m = (none, m) := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    cases p with
    | mk k' ptr =>
      dsimp only [localMapGet?, localMapRemove] at h; dsimp only [localMapGet?, localMapRemove]
      cases hbeq : Nat.beq k' k with
      | true => rw [hbeq, if_true_eq_true] at h; cases h
      | false =>
        rw [hbeq, if_false_eq_true] at h
        rw [if_false_eq_true, ih h]

theorem storageLiveFrame_fresh (frame : StackFrame) (mem : MrMemory)
    (id : LocalName) (ty : MrType)
    (hloc : listGet? frame.func.locals id = some ty)
    (hdead : localMapGet? id frame.locals = none)
    (hvsz : validSize ty.size = true) (halPos : 0 < ty.align.bytes) :
    ∃ mem' ptr,
      storageLiveFrame frame mem id =
        .ok ({ frame with locals := localMapInsert id ptr frame.locals }, mem') ∧
      AllocLiveAt mem' ty ptr mem.allocations.length
        (List.replicate ty.size.bytes .uninit) ∧
      ∀ ty' ptr' id' data',
        AllocLiveAt mem ty' ptr' id' data' →
        id' ≠ mem.allocations.length ∧
        AllocLiveAt mem' ty' ptr' id' data' := by
  dsimp only [storageLiveFrame, storageDeadFrame]
  rw [hloc, localMapRemove_of_none id frame.locals hdead]
  dsimp only
  cases allocLiveAt_allocate mem ty hvsz halPos with
  | intro mem' hrest =>
    cases hrest with
    | intro ptr hrest2 =>
      cases hrest2 with
      | intro halloc hrest3 =>
        rw [halloc]
        exact ⟨mem', ptr, rfl, hrest3⟩

theorem allocLiveAt_isAligned {mem : MrMemory} {ty : MrType} {ptr : ThinPtr}
    {id : AllocId} {data : List AbstractByte}
    (h : AllocLiveAt mem ty ptr id data) :
    ty.align.isAligned ptr.addr = true := by
  cases h.2 with
  | intro _ ha => exact ha.2.2.2.2.2.1

/-- Unpack `bodyAdmittedWith exact body = true` into its component conjuncts. -/
theorem bodyAdmittedWith_spec (exact : Bool) (body : Body)
    (h : bodyAdmittedWith exact body = true) :
    body.basicBlocks.isEmpty = false ∧
    body.argumentCount < body.locals.length ∧
    storageAnnotationsInBounds body = true ∧
    discriminantTypesValid body = true ∧
    castTypesValid body = true ∧
    body.locals.all isSupportedScalarOrUnitTy = true ∧
    body.basicBlocks.all
      (blockAdmitted exact body.argumentCount body.locals
        body.basicBlocks.length) = true := by
  dsimp only [bodyAdmittedWith] at h
  cases h1 : !body.basicBlocks.isEmpty with
  | false => rw [h1] at h; cases h
  | true =>
    cases h2 : Nat.blt body.argumentCount body.locals.length with
    | false => rw [h1, h2] at h; cases h
    | true =>
      cases h3 : storageAnnotationsInBounds body with
      | false => rw [h1, h2, h3] at h; cases h
      | true =>
        cases h4 : discriminantTypesValid body with
        | false => rw [h1, h2, h3, h4] at h; cases h
        | true =>
          cases h5 : castTypesValid body with
          | false => rw [h1, h2, h3, h4, h5] at h; cases h
          | true =>
            have hne : body.basicBlocks.isEmpty = false := by
              cases he : body.basicBlocks.isEmpty with
              | false => rfl
              | true => rw [he] at h1; cases h1
            cases exact with
            | false =>
              cases h6 : body.locals.all isSupportedScalarOrUnitTy with
              | false => rw [h1, h2, h3, h4, h5, h6] at h; cases h
              | true =>
                rw [h1, h2, h3, h4, h5, h6] at h
                exact ⟨hne, nat_lt_of_blt_eq_true h2, rfl, rfl, rfl, rfl, h⟩
            | true =>
              cases h6 : body.locals.all isExactSupportedTy with
              | false => rw [h1, h2, h3, h4, h5, h6] at h; cases h
              | true =>
                rw [h1, h2, h3, h4, h5, h6] at h
                have hsupp : body.locals.all isSupportedScalarOrUnitTy = true :=
                  list_all_imp _ _ body.locals
                    isSupportedScalarOrUnitTy_of_exact h6
                exact ⟨hne, nat_lt_of_blt_eq_true h2, rfl, rfl, rfl, hsupp, h⟩

theorem localMapRemove_inBounds (id : LocalName) (n : Nat) :
    ∀ (ls : LocalMap),
      (∀ p, p ∈ ls → p.1 < n) →
      ∀ p, p ∈ (localMapRemove id ls).2 → p.1 < n := by
  intro ls
  induction ls with
  | nil => intro _ p hp; cases hp
  | cons hd rest ih =>
    intro hb p hp
    cases hd with
    | mk k ptr =>
      dsimp only [localMapRemove] at hp
      cases hbeq : Nat.beq k id with
      | true =>
        rw [hbeq, if_true_eq_true] at hp
        exact hb p (List.Mem.tail _ hp)
      | false =>
        rw [hbeq, if_false_eq_true] at hp
        cases hp with
        | head => exact hb (k, ptr) (List.Mem.head _)
        | tail _ ht => exact ih (fun q hq => hb q (List.Mem.tail _ hq)) p ht

theorem localMapInsert_inBounds (id : LocalName) (ptr : ThinPtr)
    (n : Nat) (ls : LocalMap) (hid : id < n) (hb : ∀ p, p ∈ ls → p.1 < n) :
    ∀ p, p ∈ localMapInsert id ptr ls → p.1 < n := by
  intro p hp; dsimp only [localMapInsert] at hp
  cases hp with
  | head => exact hid
  | tail _ ht => exact localMapRemove_inBounds id n ls hb p ht

theorem localMapGet?_remove_ne (id j : LocalName) (hne : Nat.beq id j = false) :
    ∀ (ls : LocalMap),
      localMapGet? j (localMapRemove id ls).2 = localMapGet? j ls := by
  intro ls
  induction ls with
  | nil => rfl
  | cons hd rest ih =>
    cases hd with
    | mk k ptr =>
      dsimp only [localMapRemove]
      cases hki : Nat.beq k id with
      | true =>
        have hkEq : k = id := Nat.eq_of_beq_eq_true hki
        subst hkEq
        rw [if_true_eq_true]
        dsimp only [localMapGet?]
        rw [hne, if_false_eq_true]
      | false =>
        rw [if_false_eq_true]
        dsimp only [localMapGet?]
        rw [ih]

theorem localMapGet?_insert_isSome0 (id : LocalName) (ptr : ThinPtr)
    (ls : LocalMap)
    (h0 : id = 0 ∨ (localMapGet? 0 ls).isSome = true) :
    (localMapGet? 0 (localMapInsert id ptr ls)).isSome = true := by
  dsimp only [localMapInsert, localMapGet?]
  cases hb : Nat.beq id 0 with
  | true => rw [if_true_eq_true]; rfl
  | false =>
    rw [if_false_eq_true]
    cases h0 with
    | inl heq => subst heq; cases hb
    | inr his => rw [localMapGet?_remove_ne id 0 hb ls]; exact his

theorem storageDeadFrame_get0_of_ne (frame f' : StackFrame)
    (mem m' : MrMemory) (id : LocalName) (hb : Nat.beq id 0 = false)
    (h0 : (localMapGet? 0 frame.locals).isSome = true)
    (hs : storageDeadFrame frame mem id = .ok (f', m')) :
    (localMapGet? 0 f'.locals).isSome = true := by
  dsimp only [storageDeadFrame] at hs
  cases hlg : listGet? frame.func.locals id with
  | none => rw [hlg] at hs; cases hs
  | some ty =>
    rw [hlg] at hs; dsimp only at hs
    cases hrem : (localMapRemove id frame.locals).1 with
    | none =>
      rw [hrem] at hs; dsimp only at hs
      injection hs with h1; injection h1 with hf _; subst hf
      dsimp only; rw [localMapGet?_remove_ne id 0 hb frame.locals]; exact h0
    | some ptr =>
      rw [hrem] at hs; dsimp only at hs
      cases hde : mem.deallocate ptr ty.size ty.align with
      | error _ => rw [hde] at hs; cases hs
      | ok _ =>
        rw [hde] at hs; dsimp only at hs
        injection hs with h1; injection h1 with hf _; subst hf
        dsimp only; rw [localMapGet?_remove_ne id 0 hb frame.locals]; exact h0

theorem storageLiveFrame_get0 (frame f' : StackFrame)
    (mem m' : MrMemory) (id : LocalName)
    (h0 : id = 0 ∨ (localMapGet? 0 frame.locals).isSome = true)
    (hs : storageLiveFrame frame mem id = .ok (f', m')) :
    (localMapGet? 0 f'.locals).isSome = true := by
  dsimp only [storageLiveFrame] at hs
  cases hlg : listGet? frame.func.locals id with
  | none => rw [hlg] at hs; cases hs
  | some ty =>
    rw [hlg] at hs; dsimp only at hs
    cases hsd : storageDeadFrame frame mem id with
    | error _ => rw [hsd] at hs; cases hs
    | ok pr1 =>
      rw [hsd] at hs; dsimp only at hs
      cases pr1 with
      | mk f1 m1 =>
        cases hal : m1.allocate ty.size ty.align with
        | error _ => rw [hal] at hs; cases hs
        | ok pr2 =>
          rw [hal] at hs; dsimp only at hs
          cases pr2 with
          | mk _ ptr =>
            injection hs with h1; injection h1 with hf _; subst hf
            dsimp only
            cases hb : Nat.beq id 0 with
            | true =>
              exact localMapGet?_insert_isSome0 id ptr f1.locals
                (Or.inl (Nat.eq_of_beq_eq_true hb))
            | false =>
              cases h0 with
              | inl heq => subst heq; cases hb
              | inr his =>
                exact localMapGet?_insert_isSome0 id ptr f1.locals
                  (Or.inr (storageDeadFrame_get0_of_ne frame f1 mem m1 id hb his
                    hsd))

theorem list_any_false_of_all {α : Type} (p q : α → Bool) :
    ∀ xs : List α, (∀ x, p x = true → q x = false) → xs.all p = true →
    xs.any q = false
  | [], _, _ => rfl
  | x :: xs, himp, hall => by
    dsimp only [List.all] at hall; dsimp only [List.any]
    cases hp : p x with
    | false => rw [hp] at hall; cases hall
    | true =>
      rw [hp] at hall
      rw [himp x hp]
      exact list_any_false_of_all p q xs himp hall

theorem block_terminator_not_call_or_assert (exact : Bool) (argCount : Nat)
    (bodyLocals : List MirTy) (numBlocks : Nat) (bb : BasicBlock)
    (hbb : blockAdmitted exact argCount bodyLocals numBlocks bb = true) :
    (match bb.terminator with
    | .assert _ _ _ _ _ | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
    | _ => false) = false := by
  dsimp only [blockAdmitted] at hbb
  cases hc : bb.cleanup with
  | true => rw [hc] at hbb; cases hbb
  | false =>
    rw [hc] at hbb
    cases hs : bb.statements.all (stmtAdmitted exact argCount bodyLocals) with
    | false => rw [hs] at hbb; cases hbb
    | true =>
      rw [hs] at hbb
      cases ht : bb.terminator with
      | assert _ _ _ _ _ => rw [ht] at hbb; cases hbb
      | call _ _ _ _ _ => rw [ht] at hbb; cases hbb
      | sysrootCall _ _ _ _ _ => rw [ht] at hbb; cases hbb
      | goto _ | return_ | unreachable | switchInt _ _ | unwindResume
      | coreCall _ _ _ _ _ | unsupported | callNe _ _ _ | drop _ _ _ => rfl

theorem block_terminator_not_call (exact : Bool) (argCount : Nat)
    (bodyLocals : List MirTy) (numBlocks : Nat) (bb : BasicBlock)
    (hbb : blockAdmitted exact argCount bodyLocals numBlocks bb = true) :
    (match bb.terminator with
    | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
    | _ => false) = false := by
  have h := block_terminator_not_call_or_assert exact argCount bodyLocals numBlocks bb hbb
  cases ht : bb.terminator <;> first | rfl | (rw [ht] at h; cases h)

theorem assertConditionTypesValid_of_blocksAdm (exact : Bool) (body : Body)
    (h : body.basicBlocks.all
      (blockAdmitted exact body.argumentCount body.locals body.basicBlocks.length) = true) :
    assertConditionTypesValid body = true := by
  dsimp only [assertConditionTypesValid]
  exact list_all_imp _ _ body.basicBlocks (fun bb hbb => by
    have hna := block_terminator_not_call_or_assert exact body.argumentCount body.locals
      body.basicBlocks.length bb hbb
    cases ht : bb.terminator <;> first | rfl | (rw [ht] at hna; cases hna)) h

theorem callsAdmitted_of_blocksAdm (exact : Bool) (p : Program) (body : Body)
    (h : body.basicBlocks.all
      (blockAdmitted exact body.argumentCount body.locals body.basicBlocks.length) = true) :
    callsAdmitted p body = true := by
  dsimp only [callsAdmitted]
  exact list_all_imp _ _ body.basicBlocks (fun bb hbb => by
    have hnc := block_terminator_not_call exact body.argumentCount body.locals
      body.basicBlocks.length bb hbb
    cases ht : bb.terminator <;> first | rfl | (rw [ht] at hnc; cases hnc)) h

theorem allCallBodiesStaticAdmitted_of_blocksAdm (exact : Bool) (p : Program) (body : Body)
    (h : body.basicBlocks.all
      (blockAdmitted exact body.argumentCount body.locals body.basicBlocks.length) = true) :
    allCallBodiesStaticAdmitted p body = true := by
  dsimp only [allCallBodiesStaticAdmitted]
  have hnc : bodyHasAnyCall body = false :=
    list_any_false_of_all _ _ body.basicBlocks (fun bb hbb =>
      block_terminator_not_call exact body.argumentCount body.locals
        body.basicBlocks.length bb hbb) h
  rw [hnc]
  rfl

end Anneal.MiniRust
