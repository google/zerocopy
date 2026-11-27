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
import Trusted.MirSemantics.Bytes
import Trusted.MirSemantics.State
import Trusted.MirSemantics.Step
import Anneal.MiniRust.Syntax
import Anneal.MiniRust.Memory
import Anneal.MiniRust.Machine
import Anneal.MiniRust.Translate
import Anneal.MiniRust.Relation

namespace Anneal.MiniRust

open Trusted.MirAst
open Trusted.MirSemantics

/-!
# Operator, Constant, Cast, and Rvalue Correspondence (`Anneal.MiniRust.OpSim`)

Proves semantic correspondence between `Trusted.MirSemantics` expression
evaluation (`evalConstLit`, `evalUnOp`, `evalBinOp`, `evalIntToIntCast`,
`evalOperandToSlot`, `evalPrimitiveOperand`, `evalRvalue`) and `Anneal.MiniRust`
expression evaluation (`evalValue`) under `StateRel exact`.
-/

/-! ## Foundational `Nat`, `Int`, and `checkVal` Helper Lemmas -/

theorem nat_zero_mod (m : Nat) : Nat.mod 0 m = 0 := Nat.zero_mod m
theorem nat_mod_zero (a : Nat) : Nat.mod a 0 = a := Nat.mod_zero a
theorem nat_div_one (a : Nat) : Nat.div a 1 = a := Nat.div_one a

theorem ite_bool_false {α : Type} {b : Bool} (h : b = false) (x y : α) :
    (if b = true then x else y) = y := by
  subst h; rfl

theorem ite_bool_true {α : Type} {b : Bool} (h : b = true) (x y : α) :
    (if b = true then x else y) = x := by
  subst h; rfl

theorem int_negSucc_lt_zero (n : Nat) : Int.negSucc n < 0 := by
  cases n with
  | zero => exact Int.NonNeg.mk 0
  | succ k =>
    change Int.NonNeg (Int.ofNat (0 + (k + 1)))
    exact Int.NonNeg.mk (0 + (k + 1))

theorem int_lt_irrefl (a : Int) : ¬ (a < a) := by
  intro h
  cases a with
  | ofNat n =>
    exact Nat.lt_irrefl n (int_lt_of_ofNat_lt_ofNat h)
  | negSucc n =>
    cases n with
    | zero => cases h
    | succ k =>
      have h' : Int.negSucc k ≤ Int.negSucc (Nat.succ k) := h
      exact Nat.not_lt_of_ge (int_le_of_negSucc_le_negSucc h') (Nat.lt_succ_self k)

theorem int_le_of_lt {a b : Int} (h : a < b) : a ≤ b := by
  have h1 : a ≤ a + 1 := by
    cases a with
    | ofNat n => exact int_ofNat_le_ofNat (Nat.le_succ n)
    | negSucc n =>
      cases n with
      | zero => exact Int.NonNeg.mk 1
      | succ k =>
        change Int.NonNeg (Int.subNatNat (k + 2) (k + 1))
        dsimp only [Int.subNatNat]
        rw [Nat.sub_eq_zero_of_le (Nat.le_succ (k + 1))]
        exact Int.NonNeg.mk _
  exact int_le_trans h1 h

theorem int_lt_of_le_of_lt {a b c : Int} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  have hadd : a + 1 ≤ b + 1 := by
    cases a with
    | ofNat m =>
      cases b with
      | negSucc n =>
        cases m with
        | zero => cases h1
        | succ m' => cases h1
      | ofNat n =>
        exact int_ofNat_le_ofNat (Nat.succ_le_succ (int_le_of_ofNat_le_ofNat h1))
    | negSucc m =>
      cases b with
      | ofNat n =>
        cases m with
        | zero => exact int_ofNat_le_ofNat (Nat.zero_le (n + 1))
        | succ m' =>
          exact int_le_trans (int_neg_nonpos (m' + 1)) (int_ofNat_zero_le (n + 1))
      | negSucc n =>
        have hle : n ≤ m := int_le_of_negSucc_le_negSucc h1
        cases m with
        | zero =>
          cases n with
          | zero => exact int_le_refl 0
          | succ _ => cases hle
        | succ m' =>
          cases n with
          | zero => exact int_neg_nonpos (m' + 1)
          | succ n' =>
            change Int.NonNeg (Int.subNatNat (m' + 1) (n' + 1))
            dsimp only [Int.subNatNat]
            rw [Nat.sub_eq_zero_of_le (Nat.succ_le_succ (Nat.le_of_succ_le_succ hle))]
            exact Int.NonNeg.mk _
  exact int_le_trans hadd h2

theorem int_lt_or_ge (a b : Int) : a < b ∨ b ≤ a := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      cases Nat.lt_or_ge m n with
      | inl h => exact Or.inl (int_ofNat_lt_ofNat h)
      | inr h => exact Or.inr (int_ofNat_le_ofNat h)
    | negSucc n =>
      exact Or.inr (int_le_trans (int_neg_nonpos (n + 1)) (int_ofNat_zero_le m))
  | negSucc m =>
    cases b with
    | ofNat n =>
      exact Or.inl (int_lt_of_lt_of_le (int_negSucc_lt_zero m) (int_ofNat_zero_le n))
    | negSucc n =>
      cases Nat.lt_or_ge n m with
      | inl h =>
        cases m with
        | zero => cases h
        | succ m' =>
          have hle : n ≤ m' := Nat.le_of_lt_succ h
          left
          change Int.NonNeg (Int.subNatNat (m' + 1) (n + 1))
          dsimp only [Int.subNatNat]
          rw [Nat.sub_eq_zero_of_le (Nat.succ_le_succ hle)]
          exact Int.NonNeg.mk _
      | inr h =>
        right
        change Int.NonNeg (Int.subNatNat (n + 1) (m + 1))
        dsimp only [Int.subNatNat]
        rw [Nat.sub_eq_zero_of_le (Nat.succ_le_succ h)]
        exact Int.NonNeg.mk _

theorem nat_div_lt_of_le_of_ge_two {a b H : Nat} (hH : 0 < H) (ha : a ≤ H)
    (hb : 2 ≤ b) : Nat.div a b < H := by
  have hltMul : a < b * H := by
    have h2 : H < 2 * H := by
      rw [Nat.two_mul]
      exact Nat.lt_add_of_pos_right hH
    have hmul : 2 * H ≤ b * H := Nat.mul_le_mul_right H hb
    exact Nat.lt_of_le_of_lt ha (Nat.lt_of_lt_of_le h2 hmul)
  have hdiv : b * Nat.div a b ≤ a := by
    have h : b * Nat.div a b + Nat.mod a b = a := Nat.div_add_mod a b
    have hle : b * Nat.div a b ≤ b * Nat.div a b + Nat.mod a b := Nat.le_add_right _ _
    rw [h] at hle
    exact hle
  cases Nat.lt_or_ge (Nat.div a b) H with
  | inl h => exact h
  | inr hge =>
    have hbad : b * H ≤ a := Nat.le_trans (Nat.mul_le_mul_left b hge) hdiv
    exact False.elim (Nat.not_lt_of_ge hbad hltMul)

theorem enumTy_beq_refl (e : EnumTy) : EnumTy.beq e e = true := by
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
      intro xs; induction xs with
      | nil => rfl
      | cons a as iha => dsimp only [natListBeq]; rw [Nat.beq_refl]; exact iha
    rw [Nat.beq_refl, hdw, hds, htr, hdl dl]; rfl

theorem val_ty_some_elim {v : Val} {ty : MirTy} (h : v.ty? = some ty) :
    (∃ b, v = .bool b ∧ ty = .bool) ∨
    (∃ sv, v = .scalar sv ∧ sv.wf = true ∧ ty = .int sv.width sv.signed) ∨
    (v = .unit ∧ ty = .unit) ∨
    (∃ c, v = .char c ∧ ty = .char) ∨
    (∃ ord, v = .ordering ord ∧ ty = .ordering) ∨
    (∃ ety idx, v = .enumVal ety idx ∧ enumAdmitted ety = true ∧
      idx < ety.discriminants.length ∧ ty = .enum ety) ∨
    (∃ sv b, v = .tuple [.scalar sv, .bool b] ∧ sv.wf = true ∧
      ty = .tuple [.int sv.width sv.signed, .bool]) := by
  cases v with
  | bool b =>
    dsimp only [Val.ty?] at h; injection h with ht; exact Or.inl ⟨b, rfl, ht.symm⟩
  | scalar sv =>
    dsimp only [Val.ty?] at h
    cases hwf : sv.wf with
    | false => rw [hwf] at h; cases h
    | true => rw [hwf] at h; injection h with ht; exact Or.inr (Or.inl ⟨sv, rfl, hwf, ht.symm⟩)
  | unit =>
    dsimp only [Val.ty?] at h; injection h with ht; exact Or.inr (Or.inr (Or.inl ⟨rfl, ht.symm⟩))
  | char c =>
    dsimp only [Val.ty?] at h; injection h with ht; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl, ht.symm⟩)))
  | ordering ord =>
    dsimp only [Val.ty?] at h; injection h with ht; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ord, rfl, ht.symm⟩))))
  | enumVal ety idx =>
    dsimp only [Val.ty?] at h
    cases h1 : enumAdmitted ety with
    | false => rw [h1] at h; cases h
    | true =>
      cases h2 : Nat.blt idx ety.discriminants.length with
      | false => rw [h1, h2] at h; cases h
      | true =>
        rw [h1, h2] at h; injection h with ht
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ety, idx, rfl, h1, nat_lt_of_blt_eq_true h2, ht.symm⟩)))))
  | ptr _ | slicePtr _ _ | array _ | range _ _ | rangeTo _ | rangeFrom _ | optionVal _ => cases h
  | bytes _ => cases h
  | tuple fs =>
    cases fs with
    | nil => cases h
    | cons a rest =>
      cases a with
      | scalar sv =>
        cases rest with
        | nil => cases h
        | cons b r2 =>
          cases b with
          | bool bv =>
            cases r2 with
            | cons _ _ => cases h
            | nil =>
              dsimp only [Val.ty?] at h
              cases hwf : sv.wf with
              | false => rw [hwf] at h; cases h
              | true =>
                rw [hwf] at h; injection h with ht
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨sv, bv, rfl, hwf, ht.symm⟩)))))
          | _ => cases h
      | _ => cases h

theorem checkVal_int_elim {w : IntWidth} {s : Bool} {v : Val}
    (hv : checkVal v (.int w s) = true) :
    ∃ bits, v = .scalar ⟨w, s, bits⟩ ∧ truncateBits w bits = bits := by
  cases val_ty_some_elim (checkVal_ty_eq hv) with
  | inl h => cases h with | intro _ h1 => cases h1.2
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro sv h1 =>
        cases sv with
        | mk svw svs svbits =>
          injection h1.2.2 with hw hs; subst hw; subst hs
          exact ⟨svbits, h1.1, eq_of_beq h1.2.1⟩
    | inr h =>
      cases h with
      | inl h => cases h.2
      | inr h =>
        cases h with
        | inl h => cases h with | intro _ h1 => cases h1.2
        | inr h =>
          cases h with
          | inl h => cases h with | intro _ h1 => cases h1.2
          | inr h =>
            cases h with
            | inl h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2.2
            | inr h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2

theorem checkVal_bool_elim {v : Val} (hv : checkVal v .bool = true) :
    ∃ b, v = .bool b := by
  cases val_ty_some_elim (checkVal_ty_eq hv) with
  | inl h => cases h with | intro b h1 => exact ⟨b, h1.1⟩
  | inr h =>
    cases h with
    | inl h => cases h with | intro _ h1 => cases h1.2.2
    | inr h =>
      cases h with
      | inl h => cases h.2
      | inr h =>
        cases h with
        | inl h => cases h with | intro _ h1 => cases h1.2
        | inr h =>
          cases h with
          | inl h => cases h with | intro _ h1 => cases h1.2
          | inr h =>
            cases h with
            | inl h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2.2
            | inr h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2

theorem checkVal_char_elim {v : Val} (hv : checkVal v .char = true) :
    ∃ c, v = .char c := by
  cases val_ty_some_elim (checkVal_ty_eq hv) with
  | inl h => cases h with | intro _ h1 => cases h1.2
  | inr h =>
    cases h with
    | inl h => cases h with | intro _ h1 => cases h1.2.2
    | inr h =>
      cases h with
      | inl h => cases h.2
      | inr h =>
        cases h with
        | inl h => cases h with | intro c h1 => exact ⟨c, h1.1⟩
        | inr h =>
          cases h with
          | inl h => cases h with | intro _ h1 => cases h1.2
          | inr h =>
            cases h with
            | inl h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2.2
            | inr h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2

theorem checkVal_unit_elim {v : Val} (hv : checkVal v .unit = true) :
    v = .unit := by
  cases val_ty_some_elim (checkVal_ty_eq hv) with
  | inl h => cases h with | intro _ h1 => cases h1.2
  | inr h =>
    cases h with
    | inl h => cases h with | intro _ h1 => cases h1.2.2
    | inr h =>
      cases h with
      | inl h => exact h.1
      | inr h =>
        cases h with
        | inl h => cases h with | intro _ h1 => cases h1.2
        | inr h =>
          cases h with
          | inl h => cases h with | intro _ h1 => cases h1.2
          | inr h =>
            cases h with
            | inl h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2.2
            | inr h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2

theorem checkVal_ordering_elim {v : Val} (hv : checkVal v .ordering = true) :
    ∃ ord, v = .ordering ord := by
  cases val_ty_some_elim (checkVal_ty_eq hv) with
  | inl h => cases h with | intro _ h1 => cases h1.2
  | inr h =>
    cases h with
    | inl h => cases h with | intro _ h1 => cases h1.2.2
    | inr h =>
      cases h with
      | inl h => cases h.2
      | inr h =>
        cases h with
        | inl h => cases h with | intro _ h1 => cases h1.2
        | inr h =>
          cases h with
          | inl h => cases h with | intro ord h1 => exact ⟨ord, h1.1⟩
          | inr h =>
            cases h with
            | inl h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2.2
            | inr h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2

theorem checkVal_enum_elim {ety : EnumTy} {v : Val} (hv : checkVal v (.enum ety) = true) :
    ∃ idx, v = .enumVal ety idx ∧ enumAdmitted ety = true ∧ idx < ety.discriminants.length := by
  cases val_ty_some_elim (checkVal_ty_eq hv) with
  | inl h => cases h with | intro _ h1 => cases h1.2
  | inr h =>
    cases h with
    | inl h => cases h with | intro _ h1 => cases h1.2.2
    | inr h =>
      cases h with
      | inl h => cases h.2
      | inr h =>
        cases h with
        | inl h => cases h with | intro _ h1 => cases h1.2
        | inr h =>
          cases h with
          | inl h => cases h with | intro _ h1 => cases h1.2
          | inr h =>
            cases h with
            | inl h =>
              cases h with
              | intro ety' h1 =>
                cases h1 with
                | intro idx h2 =>
                  injection h2.2.2.2 with heq; subst heq
                  exact ⟨idx, h2.1, h2.2.1, h2.2.2.1⟩
            | inr h => cases h with | intro _ h1 => cases h1 with | intro _ h2 => cases h2.2.2

theorem checkVal_scalar_mk (w : IntWidth) (s : Bool) (bits : BitVec 128)
    (hwf : truncateBits w bits = bits) :
    checkVal (.scalar ⟨w, s, bits⟩) (.int w s) = true := by
  have hbeq : (truncateBits w bits == bits) = true := by
    rw [hwf]; exact beq_self_eq_true _
  dsimp only [checkVal, Val.ty?, ScalarVal.wf]
  simp only [hbeq, ite_true]
  have hw : IntWidth.beq w w = true := by cases w <;> rfl
  have hs : (s == s) = true := by cases s <;> rfl
  change (IntWidth.beq w w && (s == s)) = true
  rw [hw, hs]; rfl

theorem checkVal_overflow_pair_mk (w : IntWidth) (s : Bool) (sv : ScalarVal) (b : Bool)
    (hw : sv.width = w) (hs : sv.signed = s) (hwf : sv.wf = true) :
    checkVal (.tuple [.scalar sv, .bool b]) (.tuple [.int w s, .bool]) = true := by
  dsimp only [checkVal, Val.ty?]
  rw [hwf, hw, hs, if_true_eq_true]
  dsimp only [MirTy.beq, MirTy.beqList]
  have hwb : IntWidth.beq w w = true := by cases w <;> rfl
  have hsb : (s == s) = true := by cases s <;> rfl
  rw [hwb, hsb]; rfl

theorem checkVal_enum_mk (ety : EnumTy) (idx : Nat)
    (ha : enumAdmitted ety = true) (hlt : idx < ety.discriminants.length) :
    checkVal (.enumVal ety idx) (.enum ety) = true := by
  dsimp only [checkVal, Val.ty?]
  rw [ha, nat_blt_eq_true_of_lt hlt]
  exact enumTy_beq_refl ety

/-! ## Modularity and `truncateScalar` Bridge Lemmas -/

theorem nat_mod_mod_of_dvd {a m k : Nat} (hdvd : k = m * Nat.div k m) :
    Nat.mod (Nat.mod a k) m = Nat.mod a m := by
  have h1 : a = k * Nat.div a k + Nat.mod a k := (Nat.div_add_mod a k).symm
  have h2 : Nat.mod a m = Nat.mod (m * (Nat.div k m * Nat.div a k) + Nat.mod a k) m := by
    have hmul : k * Nat.div a k = m * (Nat.div k m * Nat.div a k) := by
      rw [← Nat.mul_assoc, ← hdvd]
    rw [← hmul, ← h1]
  rw [h2, nat_mul_add_mod_local]

theorem intWidth_pow_dvd_128 (w : IntWidth) :
    Nat.pow 2 128 = Nat.pow 2 w.bitWidth * Nat.div (Nat.pow 2 128) (Nat.pow 2 w.bitWidth) := by
  cases w <;> decide

theorem intEmodNat_mod_dvd (x : Int) (m k : Nat) (hm : 0 < m) (hposK : 0 < k)
    (hdvd : k = m * Nat.div k m) :
    Nat.mod (intEmodNat x k) m = intEmodNat x m := by
  cases x with
  | ofNat n =>
    dsimp only [intEmodNat]
    exact nat_mod_mod_of_dvd hdvd
  | negSucc n =>
    dsimp only [intEmodNat]
    have hmodEq : Nat.mod (Nat.mod (Nat.succ n) k) m = Nat.mod (Nat.succ n) m :=
      nat_mod_mod_of_dvd hdvd
    cases h1 : Nat.beq (Nat.mod (Nat.succ n) k) 0 with
    | true =>
      rw [if_true_eq_true]
      have hzK : Nat.mod (Nat.succ n) k = 0 := Nat.eq_of_beq_eq_true h1
      rw [hzK] at hmodEq
      have hzM : Nat.mod (Nat.succ n) m = 0 := hmodEq.symm
      rw [hzM, nat_zero_mod]; rfl
    | false =>
      rw [if_false_eq_true]
      have hltK : Nat.mod (Nat.succ n) k < k := Nat.mod_lt _ hposK
      have hsubAdd : (k - Nat.mod (Nat.succ n) k) + Nat.mod (Nat.succ n) k = k :=
        Nat.sub_add_cancel (Nat.le_of_lt hltK)
      cases h2 : Nat.beq (Nat.mod (Nat.succ n) m) 0 with
      | true =>
        rw [if_true_eq_true]
        have hzM : Nat.mod (Nat.succ n) m = 0 := Nat.eq_of_beq_eq_true h2
        rw [hzM] at hmodEq
        have hrkEq : Nat.mod (Nat.succ n) k = m * Nat.div (Nat.mod (Nat.succ n) k) m := by
          have h : m * Nat.div (Nat.mod (Nat.succ n) k) m + Nat.mod (Nat.mod (Nat.succ n) k) m =
              Nat.mod (Nat.succ n) k := Nat.div_add_mod (Nat.mod (Nat.succ n) k) m
          rw [hmodEq, Nat.add_zero] at h; exact h.symm
        have hdiff : k - Nat.mod (Nat.succ n) k =
            m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m) := by
          rw [Nat.mul_sub_left_distrib, ← hdvd, ← hrkEq]
        rw [hdiff]
        have hmz : Nat.mod (m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m) + 0) m =
            Nat.mod 0 m := nat_mul_add_mod_local m _ 0
        rw [Nat.add_zero] at hmz
        rw [hmz, nat_zero_mod]
      | false =>
        rw [if_false_eq_true]
        have hneM : Nat.mod (Nat.succ n) m ≠ 0 := by
          intro hz; rw [hz] at h2; cases h2
        have hltM : Nat.mod (Nat.succ n) m < m := Nat.mod_lt _ hm
        have hrkDecomp : Nat.mod (Nat.succ n) k =
            m * Nat.div (Nat.mod (Nat.succ n) k) m + Nat.mod (Nat.succ n) m := by
          have h : m * Nat.div (Nat.mod (Nat.succ n) k) m + Nat.mod (Nat.mod (Nat.succ n) k) m =
              Nat.mod (Nat.succ n) k := Nat.div_add_mod (Nat.mod (Nat.succ n) k) m
          rw [hmodEq] at h; exact h.symm
        have hqLt : Nat.div (Nat.mod (Nat.succ n) k) m < Nat.div k m := by
          cases Nat.lt_or_ge (Nat.div (Nat.mod (Nat.succ n) k) m) (Nat.div k m) with
          | inl h => exact h
          | inr hge =>
            have hmulLe : m * Nat.div k m ≤ m * Nat.div (Nat.mod (Nat.succ n) k) m :=
              Nat.mul_le_mul_left m hge
            rw [← hdvd] at hmulLe
            have hle : k ≤ Nat.mod (Nat.succ n) k := by
              rw [hrkDecomp]; exact Nat.le_trans hmulLe (Nat.le_add_right _ _)
            exact False.elim (Nat.not_lt_of_ge hle hltK)
        have hqEq : Nat.div k m =
            (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1) +
            Nat.div (Nat.mod (Nat.succ n) k) m + 1 := by
          have h1' : 1 ≤ Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m :=
            Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hqLt)
          rw [Nat.add_assoc, Nat.add_comm (Nat.div (Nat.mod (Nat.succ n) k) m) 1,
            ← Nat.add_assoc, Nat.sub_add_cancel h1', Nat.sub_add_cancel (Nat.le_of_lt hqLt)]
        have hdiff : k - Nat.mod (Nat.succ n) k =
            m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1) +
            (m - Nat.mod (Nat.succ n) m) := by
          apply Nat.add_right_cancel (m := Nat.mod (Nat.succ n) k)
          have hrearr :
              m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1) +
                (m - Nat.mod (Nat.succ n) m) +
                (m * Nat.div (Nat.mod (Nat.succ n) k) m + Nat.mod (Nat.succ n) m) =
              m * ((Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1) +
                Nat.div (Nat.mod (Nat.succ n) k) m + 1) := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
            rw [Nat.add_assoc (m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1))]
            rw [Nat.add_comm (m - Nat.mod (Nat.succ n) m)
              (m * Nat.div (Nat.mod (Nat.succ n) k) m + Nat.mod (Nat.succ n) m)]
            rw [Nat.add_assoc (m * Nat.div (Nat.mod (Nat.succ n) k) m)]
            rw [Nat.add_comm (Nat.mod (Nat.succ n) m) (m - Nat.mod (Nat.succ n) m)]
            rw [Nat.sub_add_cancel (Nat.le_of_lt hltM), ← Nat.add_assoc]
          have hrhs : m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1) +
                (m - Nat.mod (Nat.succ n) m) + Nat.mod (Nat.succ n) k = k := by
            have hstep : m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1) +
                  (m - Nat.mod (Nat.succ n) m) + Nat.mod (Nat.succ n) k =
                m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1) +
                  (m - Nat.mod (Nat.succ n) m) +
                  (m * Nat.div (Nat.mod (Nat.succ n) k) m + Nat.mod (Nat.succ n) m) :=
              congrArg (fun t => m * (Nat.div k m - Nat.div (Nat.mod (Nat.succ n) k) m - 1) +
                  (m - Nat.mod (Nat.succ n) m) + t) hrkDecomp
            rw [hstep, hrearr, ← hqEq, ← hdvd]
          rw [hsubAdd, hrhs]
        rw [hdiff, nat_mul_add_mod_local]
        have hposRm : 0 < Nat.mod (Nat.succ n) m := by
          cases hm' : Nat.mod (Nat.succ n) m with
          | zero => exact False.elim (hneM hm')
          | succ _ => exact Nat.zero_lt_succ _
        exact nat_mod_eq_of_lt (Nat.sub_lt hm hposRm)

theorem bringInBounds_eq_of_intEmodNat (it : IntType) (a b : Int)
    (heq : intEmodNat a (Nat.pow 2 it.bitWidth) =
      intEmodNat b (Nat.pow 2 it.bitWidth)) :
    it.bringInBounds a = it.bringInBounds b := by
  dsimp only [IntType.bringInBounds]
  rw [heq]

theorem bvToInt_bvOfInt_128_eq_bringInBounds (x : Int) :
    bvToInt (bvOfInt 128 x) = i128Ty.bringInBounds x := by
  dsimp only [bvToInt, bvOfInt, i128Ty, IntType.bringInBounds, IntType.bitWidth, Size.bits]
  rw [bv_toNat_ofNat, intEmod_toNat_eq_intEmodNat x (Nat.pow 2 128) (by decide),
    intEmodNat_mod_self x (Nat.pow 2 128) (by decide)]
  have hne : Nat.beq (16 * 8) 0 = false := rfl
  have hsub : 16 * 8 - 1 = 127 := rfl
  have hpow : 2 * Nat.pow 2 127 = Nat.pow 2 128 := by decide
  simp only [hne, if_false_eq_true, hsub]
  cases bool_cases (Nat.blt (intEmodNat x (Nat.pow 2 128)) (Nat.pow 2 127)) with
  | inr hblt =>
    simp only [hblt, ite_true]
    have h1 := nat_lt_of_blt_eq_true hblt
    have hlt2 : 2 * intEmodNat x (Nat.pow 2 128) < Nat.pow 2 128 := by
      have hm := Nat.mul_lt_mul_of_pos_left h1 (by decide : 0 < 2)
      rw [hpow] at hm; exact hm
    simp only [hlt2, ite_true]
  | inl hblt =>
    simp only [hblt, if_false_eq_true]
    have hge : Nat.pow 2 127 ≤ intEmodNat x (Nat.pow 2 128) := by
      cases Nat.lt_or_ge (intEmodNat x (Nat.pow 2 128)) (Nat.pow 2 127) with
      | inl h => rw [nat_blt_eq_true_of_lt h] at hblt; cases hblt
      | inr h => exact h
    have hnotlt : ¬ (2 * intEmodNat x (Nat.pow 2 128) < Nat.pow 2 128) := by
      have hm := Nat.mul_le_mul_left 2 hge
      rw [hpow] at hm; exact Nat.not_lt_of_ge hm
    simp only [hnotlt, ite_false]

theorem intWidth_canRepresent_imp_128 (w : IntWidth) (s : Bool) (x : Int)
    (h : (translateIntTy w s).canRepresent x = true) :
    (translateIntTy .i128 s).canRepresent x = true := by
  cases s with
  | false =>
    have h1 : (decide ((0 : Int) ≤ x) && decide (x < Int.ofNat (Nat.pow 2 w.bitWidth))) = true := h
    cases bool_cases (decide ((0 : Int) ≤ x)) with
    | inl hlo => rw [hlo] at h1; cases h1
    | inr hlo =>
      rw [hlo] at h1
      have hlt : x < Int.ofNat (Nat.pow 2 w.bitWidth) := of_decide_eq_true h1
      have hle : Int.ofNat (Nat.pow 2 w.bitWidth) ≤ Int.ofNat (Nat.pow 2 128) :=
        int_ofNat_le_ofNat (intWidth_pow_le_pow128 w)
      have hlt128 : decide (x < Int.ofNat (Nat.pow 2 128)) = true :=
        decide_eq_true (int_lt_of_lt_of_le hlt hle)
      change (decide ((0 : Int) ≤ x) && decide (x < Int.ofNat (Nat.pow 2 128))) = true
      rw [hlo, hlt128]; rfl
  | true =>
    have hne : Nat.beq (w.byteSize * 8) 0 = false := by cases w <;> decide
    dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal,
      translateIntTy, IntType.bitWidth, Size.bits] at h
    simp only [hne, if_false_eq_true, ite_true] at h
    cases bool_cases (decide (Neg.neg (Int.ofNat (Nat.pow 2 (w.byteSize * 8 - 1))) ≤ x)) with
    | inl hlo => rw [hlo] at h; cases h
    | inr hlo =>
      rw [hlo] at h
      have hgeW : Neg.neg (Int.ofNat (Nat.pow 2 (w.byteSize * 8 - 1))) ≤ x :=
        of_decide_eq_true hlo
      have hltW : x < Int.ofNat (Nat.pow 2 (w.byteSize * 8 - 1)) :=
        of_decide_eq_true h
      have hleHalf : Int.ofNat (Nat.pow 2 (w.byteSize * 8 - 1)) ≤ Int.ofNat (Nat.pow 2 127) :=
        int_ofNat_le_ofNat (intWidth_half_le_half128 w)
      have h1 : decide (Neg.neg (Int.ofNat (Nat.pow 2 127)) ≤ x) = true :=
        decide_eq_true (int_le_trans (int_neg_le_neg hleHalf) hgeW)
      have h2 : decide (x < Int.ofNat (Nat.pow 2 127)) = true :=
        decide_eq_true (int_lt_of_lt_of_le hltW hleHalf)
      change (decide (Neg.neg (Int.ofNat (Nat.pow 2 127)) ≤ x) &&
        decide (x < Int.ofNat (Nat.pow 2 127))) = true
      rw [h1, h2]; rfl

/-- Host 128-bit overflow check used by `evalArithOp`. -/
noncomputable def arithHostOverflow (s : Bool) (result : Int) : Bool :=
  if s then
    decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (result ≥ HPow.hPow (2 : Int) 127)
  else
    decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)

theorem decide_int_lt_eq_not_le (a b : Int) :
    decide (a < b) = !decide (b ≤ a) := by
  cases hb : decide (b ≤ a) with
  | true =>
    have hba := of_decide_eq_true hb
    cases ha : decide (a < b) with
    | false => rfl
    | true => exact False.elim (int_lt_irrefl a (int_lt_of_lt_of_le (of_decide_eq_true ha) hba))
  | false =>
    cases int_lt_or_ge a b with
    | inl hlt => rw [decide_eq_true hlt]; rfl
    | inr hge => rw [decide_eq_true hge] at hb; cases hb

theorem arithHostOverflow_eq_not_canRepresent128 (s : Bool) (x : Int) :
    arithHostOverflow s x = !(translateIntTy .i128 s).canRepresent x := by
  cases s with
  | false =>
    have hpow : HPow.hPow (2 : Int) 128 = Int.ofNat (Nat.pow 2 128) := by decide
    change (decide (x < 0) || decide (HPow.hPow (2 : Int) 128 ≤ x)) =
      !(decide ((0 : Int) ≤ x) && decide (x < Int.ofNat (Nat.pow 2 128)))
    rw [hpow, decide_int_lt_eq_not_le x 0, decide_int_lt_eq_not_le x (Int.ofNat (Nat.pow 2 128))]
    cases decide ((0 : Int) ≤ x) <;> cases decide (Int.ofNat (Nat.pow 2 128) ≤ x) <;> rfl
  | true =>
    have hpow : HPow.hPow (2 : Int) 127 = Int.ofNat (Nat.pow 2 127) := by decide
    change (decide (x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (HPow.hPow (2 : Int) 127 ≤ x)) =
      !(decide (Neg.neg (Int.ofNat (Nat.pow 2 127)) ≤ x) &&
        decide (x < Int.ofNat (Nat.pow 2 127)))
    rw [hpow, decide_int_lt_eq_not_le x (Neg.neg (Int.ofNat (Nat.pow 2 127))),
      decide_int_lt_eq_not_le x (Int.ofNat (Nat.pow 2 127))]
    cases decide (Neg.neg (Int.ofNat (Nat.pow 2 127)) ≤ x) <;>
      cases decide (Int.ofNat (Nat.pow 2 127) ≤ x) <;> rfl

/-- Master specification of `truncateScalar`: always succeeds, produces a
well-formed `ScalarVal` whose `decodeScalar` equals `bringInBounds`, and whose
combined `(arithHostOverflow s x || lossy)` flag equals
`!(translateIntTy w s).canRepresent x`. -/
theorem truncateScalar_spec (w : IntWidth) (s : Bool) (x : Int) :
    ∃ (sv : ScalarVal) (lossy : Bool),
      truncateScalar w s x = .ok (sv, lossy) ∧
      sv.width = w ∧ sv.signed = s ∧ sv.wf = true ∧
      decodeScalar sv = (translateIntTy w s).bringInBounds x ∧
      (arithHostOverflow s x || lossy) = !(translateIntTy w s).canRepresent x := by
  have hwfTrunc : ∀ b : BitVec 128,
      ScalarVal.wf ⟨w, s, truncateBits w b⟩ = true := by
    intro b
    dsimp only [ScalarVal.wf]
    have heq : truncateBits w (truncateBits w b) = truncateBits w b := by
      apply bv_eq_of_toNat_eq
      rw [truncateBits_toNat, truncateBits_toNat]
      exact nat_mod_mod_local b.toNat (Nat.pow 2 w.bitWidth) (Nat.pow_pos (by decide))
    rw [heq]; exact beq_self_eq_true _
  cases s with
  | false =>
    let raw := bvOfInt 128 x
    let trunc := truncateBits w raw
    have hrawToNat : raw.toNat = intEmodNat x (Nat.pow 2 128) := by
      dsimp only [raw, bvOfInt]
      rw [bv_toNat_ofNat, intEmod_toNat_eq_intEmodNat x (Nat.pow 2 128) (by decide),
        intEmodNat_mod_self x (Nat.pow 2 128) (by decide)]
    have htruncToNat : trunc.toNat = intEmodNat x (Nat.pow 2 w.bitWidth) := by
      dsimp only [trunc]
      rw [truncateBits_toNat, hrawToNat]
      exact intEmodNat_mod_dvd x (Nat.pow 2 w.bitWidth) (Nat.pow 2 128)
        (Nat.pow_pos (by decide)) (by decide) (intWidth_pow_dvd_128 w)
    have hdec : decodeScalar ⟨w, false, trunc⟩ = (translateIntTy w false).bringInBounds x := by
      rw [decodeScalar_eq_bringInBounds]
      apply bringInBounds_eq_of_intEmodNat
      dsimp only [translateIntTy, IntType.bitWidth, Size.bits, intEmodNat]
      rw [htruncToNat]
      exact intEmodNat_mod_self x (Nat.pow 2 (w.byteSize * 8)) (Nat.pow_pos (by decide))
    refine ⟨⟨w, false, trunc⟩, trunc != raw, rfl, rfl, rfl, hwfTrunc raw, hdec, ?_⟩
    rw [arithHostOverflow_eq_not_canRepresent128 false x]
    cases hcan : (translateIntTy w false).canRepresent x with
    | true =>
      have hcan128 := intWidth_canRepresent_imp_128 w false x hcan
      rw [hcan128]
      have hbib := bringInBounds_of_canRepresent (translateIntTy w false) x
        (intWidth_bitWidth_pos w) hcan
      have hbib128 := bringInBounds_of_canRepresent (translateIntTy .i128 false) x
        (by decide) hcan128
      have hrawEq : Int.ofNat raw.toNat = x := by rw [hrawToNat]; exact hbib128
      have htruncEq : Int.ofNat trunc.toNat = x := by rw [htruncToNat]; exact hbib
      have htoNatEq : trunc.toNat = raw.toNat := by
        have h := Eq.trans htruncEq hrawEq.symm; injection h
      have hbvEq : trunc = raw := bv_eq_of_toNat_eq htoNatEq
      rw [hbvEq]; dsimp only [bne]; rw [beq_self_eq_true]; rfl
    | false =>
      cases hcan128 : (translateIntTy .i128 false).canRepresent x with
      | false => rfl
      | true =>
        have hbib128 := bringInBounds_of_canRepresent (translateIntTy .i128 false) x
          (by decide) hcan128
        have hrawEq : Int.ofNat raw.toNat = x := by rw [hrawToNat]; exact hbib128
        cases hne : (trunc != raw) with
        | true => rfl
        | false =>
          have hbeq : (trunc == raw) = true := by
            dsimp only [bne] at hne
            cases hb : (trunc == raw) with | true => rfl | false => rw [hb] at hne; cases hne
          have heqBv : trunc = raw := eq_of_beq hbeq
          have hxEq : x = decodeScalar ⟨w, false, trunc⟩ := by
            rw [← hrawEq, ← heqBv]
            dsimp only [decodeScalar]
            have hwf : truncateBits w trunc = trunc := eq_of_beq (hwfTrunc raw)
            rw [hwf]; rfl
          have hcanTrue := canRepresent_decodeScalar w false trunc
          rw [← hxEq] at hcanTrue
          rw [hcanTrue] at hcan; cases hcan
  | true =>
    let wrapped := bvToInt (bvOfInt 128 x)
    have hwrapEq : wrapped = i128Ty.bringInBounds x :=
      bvToInt_bvOfInt_128_eq_bringInBounds x
    have hwrapCan : i128Ty.canRepresent wrapped = true := by
      rw [hwrapEq]; exact bringInBounds_canRepresent i128Ty x (by decide)
    have hnoGuard : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127)) = false := by
      have h := arithHostOverflow_eq_not_canRepresent128 true wrapped
      dsimp only [arithHostOverflow] at h
      have h128 : (translateIntTy .i128 true).canRepresent wrapped = true := hwrapCan
      rw [h128] at h; exact h
    let raw := bvOfInt 128 wrapped
    let trunc := truncateBits w raw
    have hrawToNat : raw.toNat = intEmodNat x (Nat.pow 2 128) := by
      dsimp only [raw, bvOfInt]
      rw [bv_toNat_ofNat, intEmod_toNat_eq_intEmodNat wrapped (Nat.pow 2 128) (by decide),
        intEmodNat_mod_self wrapped (Nat.pow 2 128) (by decide), hwrapEq]
      exact intEmodNat_bringInBounds i128Ty x (by decide)
    have htruncToNat : trunc.toNat = intEmodNat x (Nat.pow 2 w.bitWidth) := by
      dsimp only [trunc]
      rw [truncateBits_toNat, hrawToNat]
      exact intEmodNat_mod_dvd x (Nat.pow 2 w.bitWidth) (Nat.pow 2 128)
        (Nat.pow_pos (by decide)) (by decide) (intWidth_pow_dvd_128 w)
    have hdec : decodeScalar ⟨w, true, trunc⟩ = (translateIntTy w true).bringInBounds x := by
      rw [decodeScalar_eq_bringInBounds]
      apply bringInBounds_eq_of_intEmodNat
      dsimp only [translateIntTy, IntType.bitWidth, Size.bits, intEmodNat]
      rw [htruncToNat]
      exact intEmodNat_mod_self x (Nat.pow 2 (w.byteSize * 8)) (Nat.pow_pos (by decide))
    have htruncEqRes : truncateScalar w true x =
        .ok (ScalarVal.mk w true trunc, signExtendBits w trunc != wrapped) := by
      dsimp only [truncateScalar]
      rw [if_true_eq_true]
      change (if (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (wrapped ≥ HPow.hPow (2 : Int) 127)) = true
          then Except.error FaultKind.unsupported
          else Except.ok (ScalarVal.mk w true trunc, signExtendBits w trunc != wrapped)) = _
      rw [hnoGuard, if_false_eq_true]
    refine ⟨⟨w, true, trunc⟩, signExtendBits w trunc != wrapped,
      htruncEqRes, rfl, rfl, hwfTrunc raw, hdec, ?_⟩
    rw [arithHostOverflow_eq_not_canRepresent128 true x]
    have hseEq : signExtendBits w trunc = decodeScalar ⟨w, true, trunc⟩ := by
      dsimp only [decodeScalar]
      have hwf : truncateBits w trunc = trunc := eq_of_beq (hwfTrunc raw)
      rw [hwf]; rfl
    cases hcan : (translateIntTy w true).canRepresent x with
    | true =>
      have hcan128 := intWidth_canRepresent_imp_128 w true x hcan
      rw [hcan128]
      have hbib := bringInBounds_of_canRepresent (translateIntTy w true) x
        (intWidth_bitWidth_pos w) hcan
      have hbib128 := bringInBounds_of_canRepresent i128Ty x (by decide) hcan128
      rw [hseEq, hdec, hbib, hwrapEq, hbib128]
      dsimp only [bne]; rw [beq_self_eq_true]; rfl
    | false =>
      cases hcan128 : (translateIntTy .i128 true).canRepresent x with
      | false => rfl
      | true =>
        have hbib128 := bringInBounds_of_canRepresent i128Ty x (by decide) hcan128
        cases hne : (signExtendBits w trunc != wrapped) with
        | true => rfl
        | false =>
          have hbeq : (signExtendBits w trunc == wrapped) = true := by
            dsimp only [bne] at hne
            cases hb : (signExtendBits w trunc == wrapped) with | true => rfl | false => rw [hb] at hne; cases hne
          have heqI : decodeScalar ⟨w, true, trunc⟩ = x := by
            rw [← hseEq, eq_of_beq hbeq, hwrapEq, hbib128]
          have hcanTrue := canRepresent_decodeScalar w true trunc
          rw [heqI] at hcanTrue
          rw [hcanTrue] at hcan; cases hcan

/-! ## Helper Equalities (`Trusted.MirSemantics.Ops` vs. `Machine`) -/

theorem mrIntTdiv_eq (a b : Int) : mrIntTdiv a b = intTdiv a b := by cases a <;> cases b <;> rfl
theorem mrIntTmod_eq (a b : Int) : mrIntTmod a b = intTmod a b := by cases a <;> cases b <;> rfl
theorem mrIntShiftLeft_eq (a : Int) (s : Nat) : mrIntShiftLeft a s = intShiftLeft a s := by cases a <;> rfl
theorem mrIntShiftRight_eq (a : Int) (s : Nat) : mrIntShiftRight a s = intShiftRight a s := by cases a <;> rfl
theorem mrIntNot_eq (a : Int) : mrIntNot a = intNot a := by cases a <;> rfl

theorem signedMinInt_eq (w : IntWidth) :
    signedMinInt w = Neg.neg (Int.ofNat (Nat.pow 2 (w.bitWidth - 1))) := by
  cases w <;> decide

theorem int_canRepresent_tdiv_iff (w : IntWidth) (s : Bool) (l r : Int)
    (hl : (translateIntTy w s).canRepresent l = true)
    (hr : (translateIntTy w s).canRepresent r = true)
    (hrne : (r == 0) = false) :
    (translateIntTy w s).canRepresent (intTdiv l r) =
      !(s && (l == signedMinInt w && r == Neg.neg 1)) := by
  cases s with
  | false =>
    have h1 : (decide ((0 : Int) ≤ l) && decide (l < Int.ofNat (Nat.pow 2 w.bitWidth))) = true := hl
    have h2 : (decide ((0 : Int) ≤ r) && decide (r < Int.ofNat (Nat.pow 2 w.bitWidth))) = true := hr
    cases l with
    | negSucc m =>
      have h0 : decide ((0 : Int) ≤ Int.negSucc m) = false := rfl
      rw [h0] at h1; cases h1
    | ofNat m =>
      cases r with
      | negSucc n =>
        have h0 : decide ((0 : Int) ≤ Int.negSucc n) = false := rfl
        rw [h0] at h2; cases h2
      | ofNat n =>
        have hmLt : m < Nat.pow 2 w.bitWidth := by
          have h0 : decide ((0 : Int) ≤ Int.ofNat m) = true := decide_eq_true (int_ofNat_zero_le m)
          rw [h0] at h1
          exact int_lt_of_ofNat_lt_ofNat (of_decide_eq_true h1)
        have hdivLt : Nat.div m n < Nat.pow 2 w.bitWidth :=
          Nat.lt_of_le_of_lt (Nat.div_le_self m n) hmLt
        change (decide ((0 : Int) ≤ Int.ofNat (Nat.div m n)) &&
          decide (Int.ofNat (Nat.div m n) < Int.ofNat (Nat.pow 2 w.bitWidth))) = true
        rw [decide_eq_true (int_ofNat_zero_le _), decide_eq_true (int_ofNat_lt_ofNat hdivLt)]
        rfl
  | true =>
    have hne : Nat.beq (w.byteSize * 8) 0 = false := by cases w <;> decide
    let H := Nat.pow 2 (w.byteSize * 8 - 1)
    have hHalfPos : 0 < H := Nat.pow_pos (by decide)
    have hcanUnfold : ∀ z : Int, (translateIntTy w true).canRepresent z =
        (decide (Neg.neg (Int.ofNat H) ≤ z) && decide (z < Int.ofNat H)) := by
      intro z
      dsimp only [IntType.canRepresent, IntType.minVal, IntType.boundVal,
        translateIntTy, IntType.bitWidth, Size.bits]
      simp only [hne, if_false_eq_true, ite_true]
      rfl
    rw [hcanUnfold l] at hl
    rw [hcanUnfold r] at hr
    rw [hcanUnfold (intTdiv l r), signedMinInt_eq w]
    change (decide (Neg.neg (Int.ofNat H) ≤ intTdiv l r) &&
        decide (intTdiv l r < Int.ofNat H)) =
      !(true && (l == Neg.neg (Int.ofNat H) && r == Neg.neg 1))
    have hgeL : Neg.neg (Int.ofNat H) ≤ l ∧ l < Int.ofNat H := by
      cases hc : decide (Neg.neg (Int.ofNat H) ≤ l) with
      | false => rw [hc] at hl; cases hl
      | true => rw [hc] at hl; exact ⟨of_decide_eq_true hc, of_decide_eq_true hl⟩
    have hnegInBounds : ∀ k : Nat, k ≤ H →
        (decide (Neg.neg (Int.ofNat H) ≤ Int.neg (Int.ofNat k)) &&
          decide (Int.neg (Int.ofNat k) < Int.ofNat H)) = true := by
      intro k hk
      have hlo : Neg.neg (Int.ofNat H) ≤ Int.neg (Int.ofNat k) :=
        int_neg_le_neg (int_ofNat_le_ofNat hk)
      have hhi : Int.neg (Int.ofNat k) < Int.ofNat H :=
        int_lt_of_le_of_lt (int_neg_nonpos k) (int_ofNat_lt_ofNat hHalfPos)
      rw [decide_eq_true hlo, decide_eq_true hhi]; rfl
    have hposInBounds : ∀ k : Nat, k < H →
        (decide (Neg.neg (Int.ofNat H) ≤ Int.ofNat k) &&
          decide (Int.ofNat k < Int.ofNat H)) = true := by
      intro k hk
      have hlo : Neg.neg (Int.ofNat H) ≤ Int.ofNat k :=
        int_le_trans (int_neg_nonpos H) (int_ofNat_zero_le k)
      rw [decide_eq_true hlo, decide_eq_true (int_ofNat_lt_ofNat hk)]; rfl
    cases l with
    | ofNat m =>
      have hmLt : m < H := int_lt_of_ofNat_lt_ofNat hgeL.2
      have hneMin : (Int.ofNat m == Neg.neg (Int.ofNat H)) = false := by
        cases hH : H with
        | zero => rw [hH] at hHalfPos; cases hHalfPos
        | succ H' => rfl
      rw [hneMin]
      cases r with
      | ofNat n =>
        dsimp only [intTdiv]
        exact hposInBounds (Nat.div m n) (Nat.lt_of_le_of_lt (Nat.div_le_self m n) hmLt)
      | negSucc n =>
        dsimp only [intTdiv]
        exact hnegInBounds (Nat.div m (Nat.succ n))
          (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self m (Nat.succ n)) hmLt))
    | negSucc m =>
      have hmLe : Nat.succ m ≤ H := by
        cases hH : H with
        | zero => rw [hH] at hHalfPos; cases hHalfPos
        | succ H' =>
          have hlo := hgeL.1; rw [hH] at hlo
          exact Nat.succ_le_succ (int_le_of_negSucc_le_negSucc hlo)
      cases r with
      | ofNat n =>
        have hneM1 : (Int.ofNat n == Neg.neg 1) = false := rfl
        rw [hneM1]
        dsimp only [intTdiv]
        have hres := hnegInBounds (Nat.div (Nat.succ m) n) (Nat.le_trans (Nat.div_le_self _ _) hmLe)
        rw [Bool.and_false]
        exact hres
      | negSucc n =>
        cases n with
        | zero =>
          have hrM1 : (Int.negSucc 0 == Neg.neg 1) = true := rfl
          rw [hrM1]
          have hdiv : intTdiv (Int.negSucc m) (Int.negSucc 0) = Int.ofNat (Nat.succ m) := by
            dsimp only [intTdiv]; rw [nat_div_one]
          simp only [hdiv]
          cases Nat.eq_or_lt_of_le hmLe with
          | inl heq =>
            have hlMin : (Int.negSucc m == Neg.neg (Int.ofNat H)) = true := by
              rw [← heq]
              have hself : Int.negSucc m = Neg.neg (Int.ofNat (Nat.succ m)) := rfl
              rw [hself]; exact beq_self_eq_true _
            rw [hlMin]
            have hnotLt : decide (Int.ofNat (Nat.succ m) < Int.ofNat H) = false := by
              rw [heq]
              cases hb : decide (Int.ofNat H < Int.ofNat H) with
              | false => rfl
              | true => exact False.elim (Nat.lt_irrefl H (int_lt_of_ofNat_lt_ofNat (of_decide_eq_true hb)))
            rw [hnotLt]
            cases decide (Neg.neg (Int.ofNat H) ≤ Int.ofNat (Nat.succ m)) <;> rfl
          | inr hlt =>
            have hlNe : (Int.negSucc m == Neg.neg (Int.ofNat H)) = false := by
              cases hb : (Int.negSucc m == Neg.neg (Int.ofNat H)) with
              | false => rfl
              | true =>
                have heq := eq_of_beq hb
                cases hH : H with
                | zero => rw [hH] at hHalfPos; cases hHalfPos
                | succ H' =>
                  rw [hH] at heq hlt
                  injection heq with hmH
                  rw [hmH] at hlt
                  exact False.elim (Nat.lt_irrefl _ hlt)
            rw [hlNe]
            exact hposInBounds (Nat.succ m) hlt
        | succ n' =>
          have hneM1 : (Int.negSucc (Nat.succ n') == Neg.neg 1) = false := rfl
          rw [hneM1]
          dsimp only [intTdiv]
          have hlt := nat_div_lt_of_le_of_ge_two hHalfPos hmLe
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n')))
          have hres := hposInBounds _ hlt
          rw [Bool.and_false]
          exact hres

/-! ## Transmute Helper Lemmas -/

theorem evalTransmute_bool_to_u8 (b : Bool) :
    evalTransmute (.bool b) .bool (.int u8Ty) = .ok (.int (if b then 1 else 0)) := by
  cases b <;> rfl

theorem evalTransmute_u8_to_bool (b : Bool) :
    evalTransmute (.int (if b then 1 else 0)) (.int u8Ty) .bool = .ok (.bool b) := by
  cases b <;> rfl

theorem char_ofNat_toNat_of_isUnicodeScalar (n : Nat)
    (h : isUnicodeScalar n = true) :
    (Char.ofNat n).toNat = n := by
  dsimp only [isUnicodeScalar] at h
  cases hle : Nat.ble n 0x10ffff with
  | false => rw [hle] at h; cases h
  | true =>
    rw [hle, Bool.true_and] at h
    have hltMax : n < 0x110000 :=
      Nat.lt_succ_of_le (Nat.le_of_ble_eq_true hle)
    have hlt32 : n < Nat.pow 2 32 := Nat.lt_trans hltMax (by decide)
    have hvc : Nat.isValidChar n := by
      cases hge : Nat.ble 0xd800 n with
      | false =>
        cases Nat.lt_or_ge n 0xd800 with
        | inl hlt => exact Or.inl hlt
        | inr h1 => rw [Nat.ble_eq_true_of_le h1] at hge; cases hge
      | true =>
        rw [hge, Bool.true_and] at h
        cases hle2 : Nat.ble n 0xdfff with
        | true => rw [hle2] at h; cases h
        | false =>
          cases Nat.lt_or_ge 0xdfff n with
          | inl hgt => exact Or.inr ⟨hgt, hltMax⟩
          | inr h2 => rw [Nat.ble_eq_true_of_le h2] at hle2; cases hle2
    dsimp only [Char.ofNat, Char.ofNatAux]
    rw [dite_eq_left_of_eq_true (eq_true hvc)]
    rfl

theorem evalTransmute_i8_to_ordering (ord : MrOrd) :
    evalTransmute
      (.int (match ord with | .less => Neg.neg 1 | .equal => 0 | .greater => 1))
      (.int i8Ty) orderingTy =
      .ok (translateVal (.ordering
        (match ord with | .less => .less | .equal => .equal | .greater => .greater))) := by
  cases ord <;> rfl

/-! ## Unary, Binary, and Cast Operator Correspondence -/

/-- Helper matching `translateRvalue`'s unary operator translation. -/
def translateUnOpExpr (op : UnOp) (srcTy : MirTy) (e : ValueExpr) : ValueExpr :=
  match op, some srcTy with
  | .not, some .bool => .binOp (.rel .eq) e (.constant (.bool false) .bool)
  | .not, some (.int _ _) => .unOp (.int .bitNot) e
  | .neg, some (.int _ true) => .unOp (.int .neg) e
  | _, _ => e

theorem evalUnOp_sim (op : UnOp) (srcTy dstTy : MirTy) (v : Val)
    (hv : checkVal v srcTy = true)
    (hadm : (match op, some srcTy with
      | .not, some .bool => MirTy.beq dstTy .bool
      | .not, some (.int w s) => MirTy.beq dstTy (.int w s)
      | .neg, some (.int w true) => MirTy.beq dstTy (.int w true)
      | _, _ => false) = true) :
    ∃ res,
      Trusted.MirSemantics.evalUnOp op v = .ok res ∧
      checkVal res dstTy = true ∧
      ∀ (frame : StackFrame) (mem : MrMemory) (e : ValueExpr),
        evalValue frame mem e = .ok (translateVal v, translateTy srcTy) →
        evalValue frame mem (translateUnOpExpr op srcTy e) =
          .ok (translateVal res, translateTy dstTy) := by
  cases op with
  | ptrMetadata => cases hadm
  | not =>
    cases srcTy with
    | bool =>
      have hdst : dstTy = .bool := mirTy_eq_of_beq hadm
      subst hdst
      cases checkVal_bool_elim hv with
      | intro b hb =>
        subst hb
        refine ⟨.bool (!b), rfl, rfl, fun frame mem e he => ?_⟩
        dsimp only [translateUnOpExpr, evalValue]; rw [he]; cases b <;> rfl
    | int w s =>
      have hdst : dstTy = .int w s := mirTy_eq_of_beq hadm
      subst hdst
      cases checkVal_int_elim hv with
      | intro bits hbits =>
        cases hbits with
        | intro hveq _ =>
          subst hveq
          cases truncateScalar_spec w s (intNot (decodeScalar ⟨w, s, bits⟩)) with
          | intro res h1 =>
            cases h1 with
            | intro lossy h2 =>
              cases h2 with
              | intro htr h3 =>
                cases h3 with
                | intro hrw h4 =>
                  cases h4 with
                  | intro hrs h5 =>
                    cases h5 with
                    | intro hrwf h6 =>
                      refine ⟨.scalar res, ?_, ?_, fun frame mem e he => ?_⟩
                      · dsimp only [Trusted.MirSemantics.evalUnOp]; rw [htr]
                      · dsimp only [checkVal, Val.ty?]; rw [hrwf, hrw, hrs]
                        have hwb : IntWidth.beq w w = true := by cases w <;> rfl
                        have hsb : (s == s) = true := by cases s <;> rfl
                        change (IntWidth.beq w w && (s == s)) = true
                        rw [hwb, hsb]; rfl
                      · dsimp only [translateUnOpExpr, evalValue]; rw [he]
                        dsimp only [Anneal.MiniRust.evalUnOp, evalIntUnOp, translateVal, translateTy]
                        rw [mrIntNot_eq, h6.1]
    | _ => cases hadm
  | neg =>
    cases srcTy with
    | int w s =>
      cases s with
      | false => cases hadm
      | true =>
        have hdst : dstTy = .int w true := mirTy_eq_of_beq hadm
        subst hdst
        cases checkVal_int_elim hv with
        | intro bits hbits =>
          cases hbits with
          | intro hveq _ =>
            subst hveq
            cases truncateScalar_spec w true (Neg.neg (decodeScalar ⟨w, true, bits⟩)) with
          | intro res h1 =>
            cases h1 with
            | intro lossy h2 =>
              cases h2 with
              | intro htr h3 =>
                cases h3 with
                | intro hrw h4 =>
                  cases h4 with
                  | intro hrs h5 =>
                    cases h5 with
                    | intro hrwf h6 =>
                      refine ⟨.scalar res, ?_, ?_, fun frame mem e he => ?_⟩
                      · dsimp only [Trusted.MirSemantics.evalUnOp]; rw [htr, if_true_eq_true]
                      · dsimp only [checkVal, Val.ty?]; rw [hrwf, hrw, hrs]
                        have hwb : IntWidth.beq w w = true := by cases w <;> rfl
                        change (IntWidth.beq w w && (true == true)) = true
                        rw [hwb]; rfl
                      · dsimp only [translateUnOpExpr, evalValue]; rw [he]
                        dsimp only [Anneal.MiniRust.evalUnOp, evalIntUnOp, translateVal, translateTy]
                        rw [h6.1]
    | _ => cases hadm

theorem int_rel_sim (op : RelOp) (a b : Int) :
    (match op with
    | .lt => decide (a < b)
    | .le => decide (a ≤ b)
    | .gt => decide (a > b)
    | .ge => decide (a ≥ b)
    | .eq => a == b
    | .ne => a != b
    | .cmp => true) =
    (match op with
    | .lt => match cmpInt a b with | .less => true | _ => false
    | .le => match cmpInt a b with | .greater => false | _ => true
    | .gt => match cmpInt a b with | .greater => true | _ => false
    | .ge => match cmpInt a b with | .less => false | _ => true
    | .eq => match cmpInt a b with | .equal => true | _ => false
    | .ne => match cmpInt a b with | .equal => false | _ => true
    | .cmp => true) := by
  dsimp only [cmpInt]
  cases hlt : decide (a < b) with
  | true =>
    have hab : a < b := of_decide_eq_true hlt
    have hle : a ≤ b := int_le_of_lt hab
    have hne : a ≠ b := fun heq => by subst heq; exact int_lt_irrefl _ hab
    have hbeq : (a == b) = false := by
      cases h : (a == b) with | false => rfl | true => exact False.elim (hne (eq_of_beq h))
    have hgt : decide (b < a) = false := by
      cases h : decide (b < a) with
      | false => rfl
      | true => exact False.elim (int_lt_irrefl _ (int_lt_of_lt_of_le hab (int_le_of_lt (of_decide_eq_true h))))
    have hge : decide (b ≤ a) = false := by
      cases h : decide (b ≤ a) with
      | false => rfl
      | true => exact False.elim (int_lt_irrefl _ (int_lt_of_lt_of_le hab (of_decide_eq_true h)))
    cases op with
    | lt => rfl
    | le => exact decide_eq_true hle
    | gt => exact hgt
    | ge => exact hge
    | eq => exact hbeq
    | ne => dsimp only [bne]; rw [hbeq]; rfl
    | cmp => rfl
  | false =>
    cases heq : (a == b) with
    | true =>
      have hab : a = b := eq_of_beq heq
      subst hab
      have hnotLt : decide (a < a) = false := by
        cases h : decide (a < a) with | false => rfl | true => exact False.elim (int_lt_irrefl _ (of_decide_eq_true h))
      cases op with
      | lt => rfl
      | le => exact decide_eq_true (int_le_refl a)
      | gt => exact hnotLt
      | ge => exact decide_eq_true (int_le_refl a)
      | eq => rfl
      | ne => dsimp only [bne]; rw [heq]; rfl
      | cmp => rfl
    | false =>
      have hba : b < a := by
        cases int_lt_or_ge a b with
        | inl h => rw [decide_eq_true h] at hlt; cases hlt
        | inr hge =>
          cases int_lt_or_ge b a with
          | inl h2 => exact h2
          | inr hge2 =>
            have h := int_le_antisymm hge2 hge
            subst h; rw [beq_self_eq_true] at heq; cases heq
      have hnotLe : decide (a ≤ b) = false := by
        cases h : decide (a ≤ b) with
        | false => rfl
        | true => exact False.elim (int_lt_irrefl _ (int_lt_of_lt_of_le hba (of_decide_eq_true h)))
      cases op with
      | lt => rfl
      | le => exact hnotLe
      | gt => exact decide_eq_true hba
      | ge => exact decide_eq_true (int_le_of_lt hba)
      | eq => rfl
      | ne => dsimp only [bne]; rw [heq]; rfl
      | cmp => rfl

theorem cmpInt_eq_cmpOrderingOfInt (a b : Int) :
    (match cmpInt a b with
    | .less => OrderingVal.less
    | .equal => .equal
    | .greater => .greater) = cmpOrderingOfInt a b := by
  dsimp only [cmpInt, cmpOrderingOfInt]
  cases hlt : decide (a < b) with
  | true => rfl
  | false =>
    cases heq : (a == b) with
    | true => rw [decide_eq_true (eq_of_beq heq)]; rfl
    | false =>
      have hne : decide (a = b) = false := by
        cases h : decide (a = b) with
        | false => rfl
        | true => rw [of_decide_eq_true h, beq_self_eq_true] at heq; cases heq
      rw [hne]; rfl

theorem shift_amount_spec (r : Int) (bits : Nat) (hpos : 0 < bits) :
    (intEmod r (Int.ofNat bits)).toNat = intEmodNat r bits ∧
    (intEmod r (Int.ofNat bits) != r) = (decide (r < 0) || decide (Int.ofNat bits ≤ r)) := by
  have h1 := intEmod_toNat_eq_intEmodNat r bits hpos
  have heq : intEmod r (Int.ofNat bits) = Int.ofNat (intEmodNat r bits) := by
    cases r with
    | ofNat n => rfl
    | negSucc n =>
      dsimp only [intEmod, intEmodNat, Int.natAbs]
      have hmLt : Nat.mod n bits < bits := Nat.mod_lt n hpos
      have hsuccLe : Nat.succ (Nat.mod n bits) ≤ bits := hmLt
      have hsubEq : Int.subNatNat bits (Nat.succ (Nat.mod n bits)) =
          Int.ofNat (bits - Nat.succ (Nat.mod n bits)) := by
        dsimp only [Int.subNatNat]
        rw [Nat.sub_eq_zero_of_le hsuccLe]
      rw [hsubEq]
      cases Nat.eq_or_lt_of_le hsuccLe with
      | inl hEqB =>
        have hmod0 : Nat.mod (Nat.succ n) bits = 0 := by
          have h1' : Nat.succ n = bits * Nat.div n bits + Nat.succ (Nat.mod n bits) := by
            have hd := (Nat.div_add_mod n bits).symm
            rw [Nat.add_succ]; exact congrArg Nat.succ hd
          rw [h1', hEqB]
          have h2' : bits * Nat.div n bits + bits = bits * (Nat.div n bits + 1) + 0 := by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_zero]
          rw [h2', nat_mul_add_mod_local, nat_zero_mod]
        rw [hEqB, Nat.sub_self, hmod0]; rfl
      | inr hLtB =>
        have hmodS : Nat.mod (Nat.succ n) bits = Nat.succ (Nat.mod n bits) := by
          have h1' : Nat.succ n = bits * Nat.div n bits + Nat.succ (Nat.mod n bits) := by
            have hd := (Nat.div_add_mod n bits).symm
            rw [Nat.add_succ]; exact congrArg Nat.succ hd
          rw [h1', nat_mul_add_mod_local]
          exact nat_mod_eq_of_lt hLtB
        rw [hmodS]
        have hne : Nat.beq (Nat.succ (Nat.mod n bits)) 0 = false := rfl
        rw [hne, if_false_eq_true]
  refine ⟨h1, ?_⟩
  rw [heq]
  cases r with
  | negSucc n =>
    have hlt0 : decide (Int.negSucc n < 0) = true := decide_eq_true (int_negSucc_lt_zero n)
    rw [hlt0]; rfl
  | ofNat n =>
    have hnotLt0 : decide (Int.ofNat n < 0) = false := by
      cases h : decide (Int.ofNat n < 0) with
      | false => rfl
      | true => exact False.elim (int_lt_irrefl _ (int_lt_of_lt_of_le (of_decide_eq_true h) (int_ofNat_zero_le n)))
    rw [hnotLt0]
    cases Nat.lt_or_ge n bits with
    | inl hltN =>
      have hnotGe : decide (Int.ofNat bits ≤ Int.ofNat n) = false := by
        cases h : decide (Int.ofNat bits ≤ Int.ofNat n) with
        | false => rfl
        | true => exact False.elim (Nat.not_lt_of_ge (int_le_of_ofNat_le_ofNat (of_decide_eq_true h)) hltN)
      rw [hnotGe]; dsimp only [intEmodNat, bne]
      rw [nat_mod_eq_of_lt hltN, beq_self_eq_true]; rfl
    | inr hgeN =>
      rw [decide_eq_true (int_ofNat_le_ofNat hgeN)]; dsimp only [intEmodNat, bne]
      have hne : (Int.ofNat (Nat.mod n bits) == Int.ofNat n) = false := by
        cases h : (Int.ofNat (Nat.mod n bits) == Int.ofNat n) with
        | false => rfl
        | true =>
          have hEq := eq_of_beq h; injection hEq with hmEq
          have hlt' : n < bits := by rw [← hmEq]; exact Nat.mod_lt n hpos
          exact False.elim (Nat.not_lt_of_ge hgeN hlt')
      rw [hne]; rfl

/-- Helper for translated `BinOp` expression (avoids repeating the `match` in
theorem statements). -/
noncomputable def translateBinOpExpr (op : BinOp) (lTy : MirTy)
    (le re : ValueExpr) : ValueExpr :=
  match lTy with
  | .int _ _ =>
    match translateIntBinOp? op with
    | some iop => .binOp (.int iop) le re
    | none =>
      match translateWithOverflowOp? op with
      | some wop => .binOp (.intWithOverflow wop) le re
      | none =>
        match translateRelOp? op with
        | some .cmp => .unOp (.cast (.transmute orderingTy)) (.binOp (.rel .cmp) le re)
        | some rop => .binOp (.rel rop) le re
        | none => le
  | .bool =>
    match op with
    | .bitAnd =>
      .unOp (.cast (.transmute .bool))
        (.binOp (.int .bitAnd)
          (.unOp (.cast (.transmute (.int u8Ty))) le)
          (.unOp (.cast (.transmute (.int u8Ty))) re))
    | .bitOr =>
      .unOp (.cast (.transmute .bool))
        (.binOp (.int .bitOr)
          (.unOp (.cast (.transmute (.int u8Ty))) le)
          (.unOp (.cast (.transmute (.int u8Ty))) re))
    | .bitXor =>
      .unOp (.cast (.transmute .bool))
        (.binOp (.int .bitXor)
          (.unOp (.cast (.transmute (.int u8Ty))) le)
          (.unOp (.cast (.transmute (.int u8Ty))) re))
    | _ =>
      match translateRelOp? op with
      | some rop => .binOp (.rel rop) le re
      | none => le
  | .char =>
    match translateRelOp? op with
    | some .cmp => .unOp (.cast (.transmute orderingTy)) (.binOp (.rel .cmp) le re)
    | some rop => .binOp (.rel rop) le re
    | none => le
  | _ => le

/-- Master binary-operator correspondence theorem across all admitted `BinOp`s
on `int`, `bool`, and `char`. -/
theorem evalBinOp_sim (op : BinOp) (lTy rTy resTy : MirTy) (lv rv : Val)
    (hlv : checkVal lv lTy = true) (hrv : checkVal rv rTy = true)
    (hresTy : binOpResultTy? op lTy rTy = some resTy) :
    match Trusted.MirSemantics.evalBinOp op lv rv with
    | .ok res =>
      checkVal res resTy = true ∧
      ∀ (frame : StackFrame) (mem : MrMemory) (le re : ValueExpr),
        evalValue frame mem le = .ok (translateVal lv, translateTy lTy) →
        evalValue frame mem re = .ok (translateVal rv, translateTy rTy) →
        evalValue frame mem (translateBinOpExpr op lTy le re) =
          .ok (translateVal res, translateTy resTy)
    | .error .undefined =>
      ∀ (frame : StackFrame) (mem : MrMemory) (le re : ValueExpr),
        evalValue frame mem le = .ok (translateVal lv, translateTy lTy) →
        evalValue frame mem re = .ok (translateVal rv, translateTy rTy) →
        ∃ msg, evalValue frame mem (translateBinOpExpr op lTy le re) = .error (.ub msg)
    | .error .unsupported => False := by
  cases lTy with
  | bool =>
    cases rTy with
    | bool =>
      cases checkVal_bool_elim hlv with
      | intro lb hlb =>
        cases checkVal_bool_elim hrv with
        | intro rb hrb =>
          subst hlb; subst hrb
          cases op with
          | eq | ne | lt | le | gt | ge =>
            dsimp only [binOpResultTy?] at hresTy
            injection hresTy with hrt; subst hrt
            refine ⟨rfl, fun frame mem le re hle hre => ?_⟩
            dsimp only [translateBinOpExpr, translateRelOp?, evalValue]
            rw [hle, hre]
            cases lb <;> cases rb <;> rfl
          | bitAnd | bitOr | bitXor =>
            dsimp only [binOpResultTy?] at hresTy
            injection hresTy with hrt; subst hrt
            refine ⟨rfl, fun frame mem le re hle hre => ?_⟩
            dsimp only [translateBinOpExpr, evalValue]
            rw [hle, hre]
            dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, translateVal, translateTy]
            rw [evalTransmute_bool_to_u8 lb, evalTransmute_bool_to_u8 rb]
            cases lb <;> cases rb <;> rfl
          | _ => cases hresTy
    | _ => cases hresTy
  | char =>
    cases rTy with
    | char =>
      cases checkVal_char_elim hlv with
      | intro lc hlc =>
        cases checkVal_char_elim hrv with
        | intro rc hrc =>
          subst hlc; subst hrc
          cases op with
          | eq | ne | lt | le | gt | ge =>
            dsimp only [binOpResultTy?] at hresTy
            injection hresTy with hrt; subst hrt
            refine ⟨rfl, fun frame mem le re hle hre => ?_⟩
            dsimp only [translateBinOpExpr, translateRelOp?, evalValue]
            rw [hle, hre]
            dsimp only [translateVal, translateTy, Anneal.MiniRust.evalBinOp, evalRelOp]
            first
            | (have h := int_rel_sim .eq (Int.ofNat lc.toNat) (Int.ofNat rc.toNat); dsimp only at h; rw [h]; rfl)
            | (have h := int_rel_sim .ne (Int.ofNat lc.toNat) (Int.ofNat rc.toNat); dsimp only at h; rw [h]; rfl)
            | (have h := int_rel_sim .lt (Int.ofNat lc.toNat) (Int.ofNat rc.toNat); dsimp only at h; rw [h]; rfl)
            | (have h := int_rel_sim .le (Int.ofNat lc.toNat) (Int.ofNat rc.toNat); dsimp only at h; rw [h]; rfl)
            | (have h := int_rel_sim .gt (Int.ofNat lc.toNat) (Int.ofNat rc.toNat); dsimp only at h; rw [h]; rfl)
            | (have h := int_rel_sim .ge (Int.ofNat lc.toNat) (Int.ofNat rc.toNat); dsimp only at h; rw [h]; rfl)
          | cmp =>
            dsimp only [binOpResultTy?] at hresTy
            injection hresTy with hrt; subst hrt
            refine ⟨rfl, fun frame mem le re hle hre => ?_⟩
            dsimp only [translateBinOpExpr, translateRelOp?, evalValue]
            rw [hle, hre]
            dsimp only [translateVal, translateTy, Anneal.MiniRust.evalUnOp,
              evalCastOp, Anneal.MiniRust.evalBinOp, evalRelOp]
            have hcmp := cmpInt_eq_cmpOrderingOfInt (Int.ofNat lc.toNat) (Int.ofNat rc.toNat)
            rw [← hcmp]
            cases cmpInt (Int.ofNat lc.toNat) (Int.ofNat rc.toNat) <;> rfl
          | _ => cases hresTy
    | _ => cases hresTy
  | int w s =>
    cases rTy with
    | int rw_ rs =>
      cases checkVal_int_elim hlv with
      | intro lbits hlb =>
        cases checkVal_int_elim hrv with
        | intro rbits hrb =>
          cases hlb with
          | intro hlvEq _ =>
            cases hrb with
            | intro hrvEq _ =>
              subst hlvEq; subst hrvEq
              let lInt := decodeScalar ⟨w, s, lbits⟩
              let rInt := decodeScalar ⟨rw_, rs, rbits⟩
              have hlCan : (translateIntTy w s).canRepresent lInt = true :=
                canRepresent_decodeScalar w s lbits
              have hne0Bits : Nat.beq (translateIntTy w s).bitWidth 0 = false := by
                dsimp only [translateIntTy, IntType.bitWidth, Size.bits]
                cases w <;> decide
              have hwrSelf : (IntWidth.beq w w && (s == s)) = true := by
                have hwb : IntWidth.beq w w = true := by cases w <;> rfl
                have hsb : (s == s) = true := by cases s <;> rfl
                rw [hwb, hsb]; rfl
              cases hsh : op.isShift with
          | true =>
            dsimp only [binOpResultTy?] at hresTy
            rw [hsh, if_true_eq_true] at hresTy
            injection hresTy with hrt; subst hrt
            cases shift_amount_spec rInt w.bitWidth (intWidth_bitWidth_pos w) with
            | intro hamt hovf =>
              cases op with
              | shl =>
                cases truncateScalar_spec w s (intShiftLeft lInt (intEmod rInt (Int.ofNat w.bitWidth)).toNat) with
                | intro res h1 =>
                  cases h1 with
                  | intro lossy h2 =>
                    cases h2 with
                    | intro htr h3 =>
                      cases h3 with
                      | intro hrw h4 =>
                        cases h4 with
                        | intro hrs h5 =>
                          cases h5 with
                          | intro hrwf h6 =>
                            dsimp only [Trusted.MirSemantics.evalBinOp, evalShiftOp]
                            rw [ite_bool_true hsh, htr]
                            simp only [BinOp.isUnchecked, Bool.and_false, if_false_eq_true]
                            refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                            · dsimp only [checkVal, Val.ty?]; rw [hrwf, hrw, hrs]; exact hwrSelf
                            · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                              dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                              have hbwEq : (translateIntTy w s).bitWidth = w.bitWidth := rfl
                              rw [hne0Bits, if_false_eq_true, mrIntShiftLeft_eq, hbwEq, ← hamt, h6.1]
              | shr =>
                cases truncateScalar_spec w s (intShiftRight lInt (intEmod rInt (Int.ofNat w.bitWidth)).toNat) with
                | intro res h1 =>
                  cases h1 with
                  | intro lossy h2 =>
                    cases h2 with
                    | intro htr h3 =>
                      cases h3 with
                      | intro hrw h4 =>
                        cases h4 with
                        | intro hrs h5 =>
                          cases h5 with
                          | intro hrwf h6 =>
                            dsimp only [Trusted.MirSemantics.evalBinOp, evalShiftOp]
                            rw [ite_bool_true hsh, htr]
                            simp only [BinOp.isUnchecked, Bool.and_false, if_false_eq_true]
                            refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                            · dsimp only [checkVal, Val.ty?]; rw [hrwf, hrw, hrs]; exact hwrSelf
                            · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                              dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                              have hbwEq : (translateIntTy w s).bitWidth = w.bitWidth := rfl
                              rw [hne0Bits, if_false_eq_true, mrIntShiftRight_eq, hbwEq, ← hamt, h6.1]
              | shlUnchecked =>
                cases truncateScalar_spec w s (intShiftLeft lInt (intEmod rInt (Int.ofNat w.bitWidth)).toNat) with
                | intro res h1 =>
                  cases h1 with
                  | intro lossy h2 =>
                    cases h2 with
                    | intro htr h3 =>
                      cases h3 with
                      | intro hrw h4 =>
                        cases h4 with
                        | intro hrs h5 =>
                          cases h5 with
                          | intro hrwf h6 =>
                            dsimp only [Trusted.MirSemantics.evalBinOp, evalShiftOp]
                            rw [ite_bool_true hsh, htr, hovf]
                            simp only [BinOp.isUnchecked, Bool.and_true]
                            cases hcond : decide (rInt < 0) || decide (Int.ofNat w.bitWidth ≤ rInt) with
                            | true =>
                              rw [if_true_eq_true]
                              intro frame mem le re hle hre
                              dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                              dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                              have hc' : (decide (rInt < 0) ||
                                  decide (Int.ofNat (translateIntTy w s).bitWidth ≤ rInt)) = true := hcond
                              rw [hc', if_true_eq_true]; exact ⟨_, rfl⟩
                            | false =>
                              rw [if_false_eq_true]
                              have hrEqAmt : rInt.toNat = (intEmod rInt (Int.ofNat w.bitWidth)).toNat := by
                                rw [hamt]
                                cases hrEq : rInt with
                                | negSucc n =>
                                  rw [hrEq, decide_eq_true (int_negSucc_lt_zero n)] at hcond; cases hcond
                                | ofNat n =>
                                  rw [hrEq] at hcond
                                  have hltN : n < w.bitWidth := by
                                    cases Nat.lt_or_ge n w.bitWidth with
                                    | inl h => exact h
                                    | inr hge =>
                                      rw [decide_eq_true (int_ofNat_le_ofNat hge)] at hcond
                                      cases decide (Int.ofNat n < 0) <;> cases hcond
                                  dsimp only [intEmodNat, Int.toNat]
                                  exact (nat_mod_eq_of_lt hltN).symm
                              refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                              · dsimp only [checkVal, Val.ty?]; rw [hrwf, hrw, hrs]; exact hwrSelf
                              · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                                dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                                have hc' : (decide (rInt < 0) ||
                                    decide (Int.ofNat (translateIntTy w s).bitWidth ≤ rInt)) = false := hcond
                                rw [hc', if_false_eq_true, mrIntShiftLeft_eq, hrEqAmt, h6.1]
              | shrUnchecked =>
                cases truncateScalar_spec w s (intShiftRight lInt (intEmod rInt (Int.ofNat w.bitWidth)).toNat) with
                | intro res h1 =>
                  cases h1 with
                  | intro lossy h2 =>
                    cases h2 with
                    | intro htr h3 =>
                      cases h3 with
                      | intro hrw h4 =>
                        cases h4 with
                        | intro hrs h5 =>
                          cases h5 with
                          | intro hrwf h6 =>
                            dsimp only [Trusted.MirSemantics.evalBinOp, evalShiftOp]
                            rw [ite_bool_true hsh, htr, hovf]
                            simp only [BinOp.isUnchecked, Bool.and_true]
                            cases hcond : decide (rInt < 0) || decide (Int.ofNat w.bitWidth ≤ rInt) with
                            | true =>
                              rw [if_true_eq_true]
                              intro frame mem le re hle hre
                              dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                              dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                              have hc' : (decide (rInt < 0) ||
                                  decide (Int.ofNat (translateIntTy w s).bitWidth ≤ rInt)) = true := hcond
                              rw [hc', if_true_eq_true]; exact ⟨_, rfl⟩
                            | false =>
                              rw [if_false_eq_true]
                              have hrEqAmt : rInt.toNat = (intEmod rInt (Int.ofNat w.bitWidth)).toNat := by
                                rw [hamt]
                                cases hrEq : rInt with
                                | negSucc n =>
                                  rw [hrEq, decide_eq_true (int_negSucc_lt_zero n)] at hcond; cases hcond
                                | ofNat n =>
                                  rw [hrEq] at hcond
                                  have hltN : n < w.bitWidth := by
                                    cases Nat.lt_or_ge n w.bitWidth with
                                    | inl h => exact h
                                    | inr hge =>
                                      rw [decide_eq_true (int_ofNat_le_ofNat hge)] at hcond
                                      cases decide (Int.ofNat n < 0) <;> cases hcond
                                  dsimp only [intEmodNat, Int.toNat]
                                  exact (nat_mod_eq_of_lt hltN).symm
                              refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                              · dsimp only [checkVal, Val.ty?]; rw [hrwf, hrw, hrs]; exact hwrSelf
                              · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                                dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                                have hc' : (decide (rInt < 0) ||
                                    decide (Int.ofNat (translateIntTy w s).bitWidth ≤ rInt)) = false := hcond
                                rw [hc', if_false_eq_true, mrIntShiftRight_eq, hrEqAmt, h6.1]
              | _ => cases hsh
          | false =>
            have hsameTy : w = rw_ ∧ s = rs := by
              dsimp only [binOpResultTy?] at hresTy
              rw [hsh, if_false_eq_true] at hresTy
              cases hbeq : MirTy.beq (.int w s) (.int rw_ rs) with
              | false => rw [hbeq] at hresTy; cases hresTy
              | true =>
                have h := mirTy_eq_of_beq hbeq
                injection h with hw hs; exact ⟨hw, hs⟩
            cases hsameTy with
            | intro heqW heqS =>
              subst heqW; subst heqS
              have hsameMir : MirTy.beq (.int w s) (.int w s) = true := hwrSelf
              have hrCan : (translateIntTy w s).canRepresent rInt = true :=
                canRepresent_decodeScalar w s rbits
              cases op with
              | eq | ne | lt | le | gt | ge =>
                dsimp only [binOpResultTy?] at hresTy
                rw [ite_bool_false hsh, hsameMir, if_not_true] at hresTy
                injection hresTy with hrt; subst hrt
                dsimp only [Trusted.MirSemantics.evalBinOp]
                rw [ite_bool_false hsh, hwrSelf, if_not_true]
                refine ⟨rfl, fun frame mem le re hle hre => ?_⟩
                dsimp only [translateBinOpExpr, translateIntBinOp?, translateWithOverflowOp?,
                  translateRelOp?, evalValue]; rw [hle, hre]
                dsimp only [Anneal.MiniRust.evalBinOp, evalRelOp, translateVal, translateTy]
                first
                | (have h := int_rel_sim .eq lInt rInt; dsimp only at h; rw [h]; rfl)
                | (have h := int_rel_sim .ne lInt rInt; dsimp only at h; rw [h]; rfl)
                | (have h := int_rel_sim .lt lInt rInt; dsimp only at h; rw [h]; rfl)
                | (have h := int_rel_sim .le lInt rInt; dsimp only at h; rw [h]; rfl)
                | (have h := int_rel_sim .gt lInt rInt; dsimp only at h; rw [h]; rfl)
                | (have h := int_rel_sim .ge lInt rInt; dsimp only at h; rw [h]; rfl)
              | cmp =>
                dsimp only [binOpResultTy?] at hresTy
                rw [ite_bool_false hsh, hsameMir, if_not_true] at hresTy
                injection hresTy with hrt; subst hrt
                dsimp only [Trusted.MirSemantics.evalBinOp]
                rw [ite_bool_false hsh, hwrSelf, if_not_true]
                refine ⟨rfl, fun frame mem le re hle hre => ?_⟩
                dsimp only [translateBinOpExpr, translateIntBinOp?, translateWithOverflowOp?,
                  translateRelOp?, evalValue]; rw [hle, hre]
                dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, Anneal.MiniRust.evalBinOp,
                  evalRelOp, translateVal, translateTy]
                have hcmp := cmpInt_eq_cmpOrderingOfInt lInt rInt
                rw [← hcmp]
                cases cmpInt lInt rInt <;> rfl
              | bitAnd | bitOr | bitXor =>
                dsimp only [binOpResultTy?] at hresTy
                rw [ite_bool_false hsh, hsameMir, if_not_true] at hresTy
                injection hresTy with hrt; subst hrt
                dsimp only [Trusted.MirSemantics.evalBinOp]
                rw [ite_bool_false hsh, hwrSelf, if_not_true]
                have hlMod : intEmodNat lInt (Nat.pow 2 w.bitWidth) = (truncateBits w lbits).toNat :=
                  intEmodNat_decodeScalar w s lbits
                have hrMod : intEmodNat rInt (Nat.pow 2 w.bitWidth) = (truncateBits w rbits).toNat :=
                  intEmodNat_decodeScalar w s rbits
                have hbwEq : (translateIntTy w s).bitWidth = w.bitWidth := rfl
                have hbitHelper : ∀ n : Nat,
                    decodeScalar ⟨w, s, truncateBits w (BitVec.ofNat 128 n)⟩ =
                      (translateIntTy w s).bringInBounds (Int.ofNat n) := by
                  intro n
                  rw [decodeScalar_eq_bringInBounds]
                  apply bringInBounds_eq_of_intEmodNat
                  dsimp only [translateIntTy, IntType.bitWidth, Size.bits, intEmodNat]
                  rw [truncateBits_toNat, bv_toNat_ofNat]
                  dsimp only [IntWidth.bitWidth]
                  have h1 := nat_mod_mod_of_dvd (a := n) (intWidth_pow_dvd_128 w)
                  dsimp only [IntWidth.bitWidth] at h1
                  rw [h1]
                  exact nat_mod_mod_local n (Nat.pow 2 (w.byteSize * 8)) (Nat.pow_pos (by decide))
                have hwfBv : ∀ b : BitVec 128, truncateBits w (truncateBits w b) = truncateBits w b := by
                  intro b
                  apply bv_eq_of_toNat_eq
                  rw [truncateBits_toNat, truncateBits_toNat]
                  exact nat_mod_mod_local b.toNat (Nat.pow 2 w.bitWidth) (Nat.pow_pos (by decide))
                first
                | (refine ⟨checkVal_scalar_mk w s _ (hwfBv _), fun frame mem le re hle hre => ?_⟩
                   dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                   dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy, bvAnd]
                   rw [hbwEq, hlMod, hrMod, hbitHelper])
                | (refine ⟨checkVal_scalar_mk w s _ (hwfBv _), fun frame mem le re hle hre => ?_⟩
                   dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                   dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy, bvOr]
                   rw [hbwEq, hlMod, hrMod, hbitHelper])
                | (refine ⟨checkVal_scalar_mk w s _ (hwfBv _), fun frame mem le re hle hre => ?_⟩
                   dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                   dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy, bvXor]
                   rw [hbwEq, hlMod, hrMod, hbitHelper])
              | add | sub | mul =>
                dsimp only [binOpResultTy?] at hresTy
                rw [ite_bool_false hsh, hsameMir, if_not_true] at hresTy
                injection hresTy with hrt; subst hrt
                dsimp only [Trusted.MirSemantics.evalBinOp, evalArithOp]
                rw [ite_bool_false hsh, hwrSelf, if_not_true]
                rw [Bool.false_and, if_false_eq_true, Bool.and_false, Bool.false_and, if_false_eq_true]
                first
                | (cases truncateScalar_spec w s (lInt + rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_false, if_false_eq_true]
                     refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                     · dsimp only [checkVal, Val.ty?]; rw [h2.2.2.2.1, h2.2.1, h2.2.2.1]; exact hwrSelf
                     · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                       dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                       rw [h2.2.2.2.2.1])
                | (cases truncateScalar_spec w s (lInt - rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_false, if_false_eq_true]
                     refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                     · dsimp only [checkVal, Val.ty?]; rw [h2.2.2.2.1, h2.2.1, h2.2.2.1]; exact hwrSelf
                     · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                       dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                       rw [h2.2.2.2.2.1])
                | (cases truncateScalar_spec w s (lInt * rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_false, if_false_eq_true]
                     refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                     · dsimp only [checkVal, Val.ty?]; rw [h2.2.2.2.1, h2.2.1, h2.2.2.1]; exact hwrSelf
                     · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                       dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                       rw [h2.2.2.2.2.1])
              | addUnchecked | subUnchecked | mulUnchecked =>
                dsimp only [binOpResultTy?] at hresTy
                rw [ite_bool_false hsh, hsameMir, if_not_true] at hresTy
                injection hresTy with hrt; subst hrt
                dsimp only [Trusted.MirSemantics.evalBinOp, evalArithOp]
                rw [ite_bool_false hsh, hwrSelf, if_not_true]
                rw [Bool.false_and, if_false_eq_true, Bool.and_false, Bool.false_and, if_false_eq_true]
                first
                | (cases truncateScalar_spec w s (lInt + rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_true]
                     have hov := h2.2.2.2.2.2; dsimp only [arithHostOverflow] at hov; rw [hov]
                     cases hcan : (translateIntTy w s).canRepresent (lInt + rInt) with
                     | false =>
                       rw [if_not_false]; intro frame mem le re hle hre
                       dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                       dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                       rw [hcan, if_not_false]; exact ⟨_, rfl⟩
                     | true =>
                       rw [if_not_true]
                       refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                       · dsimp only [checkVal, Val.ty?]; rw [h2.2.2.2.1, h2.2.1, h2.2.2.1]; exact hwrSelf
                       · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                         dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                         rw [hcan, if_not_true, h2.2.2.2.2.1])
                | (cases truncateScalar_spec w s (lInt - rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_true]
                     have hov := h2.2.2.2.2.2; dsimp only [arithHostOverflow] at hov; rw [hov]
                     cases hcan : (translateIntTy w s).canRepresent (lInt - rInt) with
                     | false =>
                       rw [if_not_false]; intro frame mem le re hle hre
                       dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                       dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                       rw [hcan, if_not_false]; exact ⟨_, rfl⟩
                     | true =>
                       rw [if_not_true]
                       refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                       · dsimp only [checkVal, Val.ty?]; rw [h2.2.2.2.1, h2.2.1, h2.2.2.1]; exact hwrSelf
                       · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                         dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                         rw [hcan, if_not_true, h2.2.2.2.2.1])
                | (cases truncateScalar_spec w s (lInt * rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_true]
                     have hov := h2.2.2.2.2.2; dsimp only [arithHostOverflow] at hov; rw [hov]
                     cases hcan : (translateIntTy w s).canRepresent (lInt * rInt) with
                     | false =>
                       rw [if_not_false]; intro frame mem le re hle hre
                       dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                       dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                       rw [hcan, if_not_false]; exact ⟨_, rfl⟩
                     | true =>
                       rw [if_not_true]
                       refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                       · dsimp only [checkVal, Val.ty?]; rw [h2.2.2.2.1, h2.2.1, h2.2.2.1]; exact hwrSelf
                       · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                         dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                         rw [hcan, if_not_true, h2.2.2.2.2.1])
              | addWithOverflow | subWithOverflow | mulWithOverflow =>
                dsimp only [binOpResultTy?] at hresTy
                rw [ite_bool_false hsh, hsameMir, if_not_true] at hresTy
                injection hresTy with hrt; subst hrt
                dsimp only [Trusted.MirSemantics.evalBinOp, evalArithOp]
                rw [ite_bool_false hsh, hwrSelf, if_not_true]
                rw [Bool.false_and, if_false_eq_true, Bool.and_false, Bool.false_and, if_false_eq_true]
                first
                | (cases truncateScalar_spec w s (lInt + rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_false, if_false_eq_true]
                     have hov := h2.2.2.2.2.2; dsimp only [arithHostOverflow] at hov; rw [hov]
                     refine ⟨checkVal_overflow_pair_mk w s res _ h2.2.1 h2.2.2.1 h2.2.2.2.1,
                       fun frame mem le re hle hre => ?_⟩
                     dsimp only [translateBinOpExpr, translateIntBinOp?, translateWithOverflowOp?,
                       evalValue]; rw [hle, hre]
                     dsimp only [Anneal.MiniRust.evalBinOp, translateVal, translateTy]; rw [h2.2.2.2.2.1])
                | (cases truncateScalar_spec w s (lInt - rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_false, if_false_eq_true]
                     have hov := h2.2.2.2.2.2; dsimp only [arithHostOverflow] at hov; rw [hov]
                     refine ⟨checkVal_overflow_pair_mk w s res _ h2.2.1 h2.2.2.1 h2.2.2.2.1,
                       fun frame mem le re hle hre => ?_⟩
                     dsimp only [translateBinOpExpr, translateIntBinOp?, translateWithOverflowOp?,
                       evalValue]; rw [hle, hre]
                     dsimp only [Anneal.MiniRust.evalBinOp, translateVal, translateTy]; rw [h2.2.2.2.2.1])
                | (cases truncateScalar_spec w s (lInt * rInt) with
                   | intro res h1 => cases h1 with | intro lossy h2 =>
                     rw [h2.1]
                     simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_false, if_false_eq_true]
                     have hov := h2.2.2.2.2.2; dsimp only [arithHostOverflow] at hov; rw [hov]
                     refine ⟨checkVal_overflow_pair_mk w s res _ h2.2.1 h2.2.2.1 h2.2.2.2.1,
                       fun frame mem le re hle hre => ?_⟩
                     dsimp only [translateBinOpExpr, translateIntBinOp?, translateWithOverflowOp?,
                       evalValue]; rw [hle, hre]
                     dsimp only [Anneal.MiniRust.evalBinOp, translateVal, translateTy]; rw [h2.2.2.2.2.1])
              | div | rem =>
                dsimp only [binOpResultTy?] at hresTy
                rw [ite_bool_false hsh, hsameMir, if_not_true] at hresTy
                injection hresTy with hrt; subst hrt
                dsimp only [Trusted.MirSemantics.evalBinOp, evalArithOp]
                rw [ite_bool_false hsh, hwrSelf, if_not_true]
                rw [Bool.true_and, Bool.and_true]
                cases hr0 : (rInt == 0) with
                | true =>
                  rw [if_true_eq_true]
                  intro frame mem le re hle hre
                  dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                  dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                  rw [hr0, if_true_eq_true]; exact ⟨_, rfl⟩
                | false =>
                  rw [if_false_eq_true]
                  have hcanDiv := int_canRepresent_tdiv_iff w s lInt rInt hlCan hrCan hr0
                  cases hovf : (s && (lInt == signedMinInt w && rInt == Neg.neg 1)) with
                  | true =>
                    rw [hovf] at hcanDiv
                    rw [if_true_eq_true]
                    intro frame mem le re hle hre
                    dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                    dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                    have hnotCan : (!(!true)) = true := rfl
                    rw [hr0, if_false_eq_true, mrIntTdiv_eq, hcanDiv, hnotCan, if_true_eq_true]
                    exact ⟨_, rfl⟩
                  | false =>
                    rw [hovf] at hcanDiv
                    rw [if_false_eq_true]
                    have hnotCan : (!(!false)) = false := rfl
                    first
                    | (cases truncateScalar_spec w s (intTdiv lInt rInt) with
                       | intro res h1 => cases h1 with | intro lossy h2 =>
                         rw [h2.1]
                         simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_false, if_false_eq_true]
                         refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                         · dsimp only [checkVal, Val.ty?]; rw [h2.2.2.2.1, h2.2.1, h2.2.2.1]; exact hwrSelf
                         · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                           dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                           rw [hr0, if_false_eq_true, mrIntTdiv_eq, hcanDiv, hnotCan, if_false_eq_true, h2.2.2.2.2.1])
                    | (cases truncateScalar_spec w s (intTmod lInt rInt) with
                       | intro res h1 => cases h1 with | intro lossy h2 =>
                         rw [h2.1]
                         simp only [BinOp.isUnchecked, BinOp.isOverflowing, Bool.and_false, if_false_eq_true]
                         refine ⟨?_, fun frame mem le re hle hre => ?_⟩
                         · dsimp only [checkVal, Val.ty?]; rw [h2.2.2.2.1, h2.2.1, h2.2.2.1]; exact hwrSelf
                         · dsimp only [translateBinOpExpr, translateIntBinOp?, evalValue]; rw [hle, hre]
                           dsimp only [Anneal.MiniRust.evalBinOp, evalIntBinOp, translateVal, translateTy]
                           rw [hr0, if_false_eq_true, mrIntTdiv_eq, hcanDiv, hnotCan, if_false_eq_true, mrIntTmod_eq, h2.2.2.2.2.1])
              | shl | shr | shlUnchecked | shrUnchecked => cases hsh
              | offset =>
                dsimp only [binOpResultTy?] at hresTy
                rw [ite_bool_false hsh, hsameMir, if_not_true] at hresTy; cases hresTy
    | _ => cases hresTy
  | _ => cases hresTy

theorem evalValue_unOp (frame : StackFrame) (mem : MrMemory) (op : MrUnOp) (e : ValueExpr) :
    evalValue frame mem (.unOp op e) =
      match evalValue frame mem e with
      | .error msg => .error msg
      | .ok (v, ty) => Anneal.MiniRust.evalUnOp op v ty := rfl

theorem evalValue_constant (frame : StackFrame) (mem : MrMemory) (c : MrConstant) (ty : MrType) :
    evalValue frame mem (.constant c ty) = .ok (evalConstant c, ty) := rfl

theorem evalUnOp_cast_intToInt (targetIt : IntType) (x : Int) (oldTy : MrType) :
    Anneal.MiniRust.evalUnOp (.cast (.intToInt targetIt)) (.int x) oldTy =
      .ok (.int (targetIt.bringInBounds x), .int targetIt) := rfl

theorem evalUnOp_cast_transmute_ok (v : MrValue) (oldTy newTy : MrType) (v' : MrValue)
    (h : evalTransmute v oldTy newTy = .ok v') :
    Anneal.MiniRust.evalUnOp (.cast (.transmute newTy)) v oldTy = .ok (v', newTy) := by
  dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp]; rw [h]

theorem evalUnOp_cast_transmute_err (v : MrValue) (oldTy newTy : MrType)
    (err : EvalError) (h : evalTransmute v oldTy newTy = .error err) :
    Anneal.MiniRust.evalUnOp (.cast (.transmute newTy)) v oldTy = .error err := by
  dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp]; rw [h]

/-- Helper matching `translateRvalue`'s cast expression translation. -/
noncomputable def translateCastExpr (srcTy castTy : MirTy) (e : ValueExpr) : ValueExpr :=
  let eInt :=
    match some srcTy with
    | some .bool => .unOp (.cast (.transmute (.int u8Ty))) e
    | _ => e
  match castTy with
  | .int w s => .unOp (.cast (.intToInt (translateIntTy w s))) eInt
  | .char => .unOp (.cast (.intToInt u32Ty)) eInt
  | _ => eInt

/-- Static admission check for `evalIntToIntCast_sim`. -/
noncomputable def intToIntCastAdmitted : MirTy → MirTy → Bool
  | st, .int _ _ => isIntLikeTy st
  | .int .i8 false, .char => true
  | _, _ => false

/-- `CastKind.intToInt` correspondence (`int`/`bool`/`char` -> `int` and
`u8` -> `char`). -/
theorem evalIntToIntCast_sim (srcTy castTy : MirTy) (v : Val)
    (hv : checkVal v srcTy = true)
    (hadm : intToIntCastAdmitted srcTy castTy = true) :
    ∃ res,
      evalIntToIntCast v castTy = .ok res ∧
      checkVal res castTy = true ∧
      ∀ (frame : StackFrame) (mem : MrMemory) (e : ValueExpr),
        evalValue frame mem e = .ok (translateVal v, translateTy srcTy) →
        evalValue frame mem (translateCastExpr srcTy castTy e) =
          .ok (translateVal res, translateTy castTy) := by
  have hwfTrunc : ∀ (w : IntWidth) (b : BitVec 128),
      truncateBits w (truncateBits w b) = truncateBits w b := by
    intro w b
    apply bv_eq_of_toNat_eq
    rw [truncateBits_toNat, truncateBits_toNat]
    exact nat_mod_mod_local b.toNat (Nat.pow 2 w.bitWidth) (Nat.pow_pos (by decide))
  have hcastIntHelper : ∀ (w : IntWidth) (s : Bool) (n : Nat),
      decodeScalar ⟨w, s, truncateBits w (BitVec.ofNat 128 n)⟩ =
        (translateIntTy w s).bringInBounds (Int.ofNat n) := by
    intro w s n
    rw [decodeScalar_eq_bringInBounds]
    apply bringInBounds_eq_of_intEmodNat
    dsimp only [translateIntTy, IntType.bitWidth, Size.bits, intEmodNat]
    rw [truncateBits_toNat, bv_toNat_ofNat]
    have h1 := nat_mod_mod_of_dvd (a := n) (intWidth_pow_dvd_128 w)
    dsimp only [IntWidth.bitWidth] at h1; dsimp only [IntWidth.bitWidth]
    rw [h1]
    exact nat_mod_mod_local n (Nat.pow 2 (w.byteSize * 8)) (Nat.pow_pos (by decide))
  cases castTy with
  | int w s =>
    cases srcTy with
    | int sw ss =>
      cases checkVal_int_elim hv with
      | intro sbits hsb =>
        cases hsb with
        | intro hveq _ =>
          subst hveq
          cases ss with
          | false =>
            refine ⟨.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 (truncateBits sw sbits).toNat)⟩,
              rfl, checkVal_scalar_mk w s _ (hwfTrunc w _), fun frame mem e he => ?_⟩
            dsimp only [translateCastExpr, evalValue]; rw [he]
            dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, translateVal]
            rw [hcastIntHelper w s (truncateBits sw sbits).toNat]; rfl
          | true =>
            refine ⟨.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 (bvOfInt 128 (decodeScalar ⟨sw, true, sbits⟩)).toNat)⟩,
              rfl, checkVal_scalar_mk w s _ (hwfTrunc w _), fun frame mem e he => ?_⟩
            dsimp only [translateCastExpr, evalValue]; rw [he]
            dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, translateVal, translateTy]
            rw [hcastIntHelper w s (bvOfInt 128 (decodeScalar ⟨sw, true, sbits⟩)).toNat]
            have hbibEq : (translateIntTy w s).bringInBounds (decodeScalar ⟨sw, true, sbits⟩) =
                (translateIntTy w s).bringInBounds (Int.ofNat (bvOfInt 128 (decodeScalar ⟨sw, true, sbits⟩)).toNat) := by
              apply bringInBounds_eq_of_intEmodNat
              dsimp only [bvOfInt, intEmodNat, translateIntTy, IntType.bitWidth, Size.bits]
              rw [bv_toNat_ofNat, intEmod_toNat_eq_intEmodNat _ (Nat.pow 2 128) (Nat.pow_pos (by decide)),
                intEmodNat_mod_self _ (Nat.pow 2 128) (Nat.pow_pos (by decide))]
              exact (intEmodNat_mod_dvd _ (Nat.pow 2 (w.byteSize * 8)) (Nat.pow 2 128)
                (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)) (intWidth_pow_dvd_128 w)).symm
            rw [hbibEq]
    | bool =>
      cases checkVal_bool_elim hv with
      | intro b hb =>
        subst hb
        refine ⟨.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 (if b then 1 else 0))⟩,
          rfl, checkVal_scalar_mk w s _ (hwfTrunc w _), fun frame mem e he => ?_⟩
        dsimp only [translateCastExpr]
        rw [evalValue_unOp, evalValue_unOp, he]
        dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, translateVal, translateTy]
        rw [evalTransmute_bool_to_u8 b]
        dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp]
        rw [hcastIntHelper w s (if b then 1 else 0)]
        cases b <;> rfl
    | char =>
      cases checkVal_char_elim hv with
      | intro c hc =>
        subst hc
        refine ⟨.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 c.toNat)⟩,
          rfl, checkVal_scalar_mk w s _ (hwfTrunc w _), fun frame mem e he => ?_⟩
        dsimp only [translateCastExpr]
        rw [evalValue_unOp, he]
        dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, translateVal, translateTy]
        rw [hcastIntHelper w s c.toNat]
    | _ => cases hadm
  | char =>
    cases srcTy with
    | int sw ss =>
      cases sw with
      | i8 =>
        cases ss with
        | false =>
          cases checkVal_int_elim hv with
          | intro sbits hsb =>
            cases hsb with
            | intro hveq _ =>
              subst hveq
              have hlt256 : (truncateBits .i8 sbits).toNat < 256 := by
                rw [truncateBits_toNat]; exact Nat.mod_lt _ (by decide)
              have hle255 : Nat.ble (truncateBits .i8 sbits).toNat 255 = true :=
                Nat.ble_eq_true_of_le (Nat.le_of_lt_succ hlt256)
              have hvalid : isUnicodeScalar (truncateBits .i8 sbits).toNat = true := by
                dsimp only [isUnicodeScalar]
                have h1 : Nat.ble (truncateBits .i8 sbits).toNat 0x10ffff = true :=
                  Nat.ble_eq_true_of_le (Nat.le_of_lt (Nat.lt_trans hlt256 (by decide)))
                have h2 : Nat.ble 0xd800 (truncateBits .i8 sbits).toNat = false := by
                  cases hb : Nat.ble 0xd800 (truncateBits .i8 sbits).toNat with
                  | false => rfl
                  | true =>
                    exact False.elim (Nat.not_lt_of_ge (Nat.le_of_ble_eq_true hb)
                      (Nat.lt_trans hlt256 (by decide)))
                rw [h1, h2]; rfl
              have hlt32 : (truncateBits .i8 sbits).toNat < Nat.pow 2 32 :=
                Nat.lt_trans hlt256 (by decide)
              refine ⟨.char (Char.ofNat (truncateBits .i8 sbits).toNat), ?_, rfl,
                fun frame mem e he => ?_⟩
              · dsimp only [evalIntToIntCast, intLikeBits]
                rw [if_false_eq_true]; dsimp only
                rw [hle255, if_true_eq_true]
              · dsimp only [translateCastExpr]
                rw [evalValue_unOp, he]
                dsimp only [translateVal, translateTy]
                rw [evalUnOp_cast_intToInt]
                have hbib : u32Ty.bringInBounds (decodeScalar ⟨.i8, false, sbits⟩) =
                    Int.ofNat (truncateBits .i8 sbits).toNat := by
                  dsimp only [decodeScalar, u32Ty, IntType.bringInBounds, IntType.bitWidth,
                    Size.bits, intEmodNat]
                  rw [if_false_eq_true]; dsimp only
                  rw [nat_mod_eq_of_lt hlt32]
                rw [hbib, char_ofNat_toNat_of_isUnicodeScalar _ hvalid]
        | true => cases hadm
      | _ => cases hadm
    | _ => cases hadm
  | _ => cases hadm

/-! ## Constant Evaluation Correspondence (`evalConstLit_sim`) -/

theorem findDiscrVariant?_none_not_in (discrBits : BitVec 128) (ds : List Nat)
    (h : findDiscrVariant? discrBits ds = none) :
    ∀ x, x ∈ ds → BitVec.ofNat 128 x ≠ discrBits := by
  have haux : ∀ (xs : List Nat) (idx : Nat),
      findDiscrVariantAux idx discrBits xs = none →
      ∀ x, x ∈ xs → BitVec.ofNat 128 x ≠ discrBits := by
    intro xs
    induction xs with
    | nil => intro _ _ _ hin; cases hin
    | cons a as ih =>
      intro idx h1 x hin
      dsimp only [findDiscrVariantAux] at h1
      cases hbeq : (BitVec.ofNat 128 a == discrBits) with
      | true => rw [hbeq, if_true_eq_true] at h1; cases h1
      | false =>
        rw [hbeq, if_false_eq_true] at h1
        cases hin with
        | head => intro heq; rw [heq, beq_self_eq_true] at hbeq; cases hbeq
        | tail _ htail => exact ih (idx + 1) h1 x htail
  exact haux ds 0 h

theorem decodeDiscrBranches_none_of_not_match (bytes : List AbstractByte)
    (tagW : IntWidth) (tagS : Bool) (ety : EnumTy) (tagVal : Int) :
    ∀ (ds : List Nat),
      (∀ d, d ∈ ds → tagIntOfNat tagW tagS d ≠ tagVal) →
      decodeDiscrBranches bytes tagVal (buildEnumBranches ety tagW tagS ds) = none := by
  intro ds
  induction ds with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hno
    dsimp only [buildEnumBranches, decodeDiscrBranches]
    have hne : tagIntOfNat tagW tagS x ≠ tagVal := hno x (List.Mem.head _)
    have hcond : (decide (tagIntOfNat tagW tagS x ≤ tagVal) &&
        decide (tagVal < tagIntOfNat tagW tagS x + 1)) = false := by
      cases hc1 : decide (tagIntOfNat tagW tagS x ≤ tagVal) with
      | false => rfl
      | true =>
        cases hc2 : decide (tagVal < tagIntOfNat tagW tagS x + 1) with
        | false => rfl
        | true =>
          exact False.elim (hne (int_le_antisymm (of_decide_eq_true hc1)
            (int_lt_add_one_iff_le.mp (of_decide_eq_true hc2))))
    rw [hcond, if_false_eq_true]
    exact ih (fun d hd => hno d (List.Mem.tail _ hd))

theorem evalConstLit_sim (exact : Bool) (c : ConstOperand)
    (hadm : constAdmitted exact c = true) :
    match evalConstLit c.ty c.lit with
    | .ok v =>
      checkVal v c.ty = true ∧
      ∀ (frame : StackFrame) (mem : MrMemory),
        evalValue frame mem (translateConst c) = .ok (translateVal v, translateTy c.ty)
    | .error .undefined =>
      exact = true →
      ∀ (frame : StackFrame) (mem : MrMemory),
        ∃ msg, evalValue frame mem (translateConst c) = .error (.ub msg)
    | .error .unsupported => False := by
  cases c with
  | mk ty lit =>
    cases ty with
    | int w s =>
      cases lit with
      | scalar bits =>
        dsimp only [constAdmitted] at hadm
        have htrunc : truncateBits w bits = bits := eq_of_beq hadm
        have hne : (truncateBits w bits != bits) = false := by dsimp only [bne]; rw [hadm]; rfl
        dsimp only [evalConstLit]; rw [hne, if_false_eq_true, htrunc]
        refine ⟨checkVal_scalar_mk w s bits htrunc, fun frame mem => ?_⟩
        dsimp only [translateConst, evalValue, evalConstant, translateVal, translateTy]
      | _ => cases hadm
    | bool =>
      cases lit with
      | scalar bits =>
        dsimp only [constAdmitted] at hadm
        have htrunc : truncateBits .i8 bits = bits := eq_of_beq hadm
        have hne : (truncateBits .i8 bits != bits) = false := by dsimp only [bne]; rw [hadm]; rfl
        have hlt256 : bits.toNat < 256 := by
          rw [← htrunc, truncateBits_toNat]; exact Nat.mod_lt _ (by decide)
        dsimp only [evalConstLit]; rw [hne, if_false_eq_true, htrunc]
        cases h0 : (UInt8.ofNat bits.toNat == 0) with
        | true =>
          rw [if_true_eq_true]
          refine ⟨rfl, fun frame mem => ?_⟩
          dsimp only [translateConst]
          rw [htrunc, h0, if_true_eq_true]; rfl
        | false =>
          rw [if_false_eq_true]
          cases h1 : (UInt8.ofNat bits.toNat == 1) with
          | true =>
            rw [if_true_eq_true]
            refine ⟨rfl, fun frame mem => ?_⟩
            dsimp only [translateConst]
            rw [htrunc, h0, h1, if_false_eq_true, if_true_eq_true]; rfl
          | false =>
            rw [if_false_eq_true]
            intro _ frame mem
            dsimp only [translateConst]
            rw [htrunc, h0, h1, if_false_eq_true, if_false_eq_true]
            rw [evalValue_unOp, evalValue_constant]
            dsimp only [evalConstant]
            have hcan : u8Ty.canRepresent (Int.ofNat bits.toNat) = true := by
              change (decide ((0 : Int) ≤ Int.ofNat bits.toNat) &&
                decide (Int.ofNat bits.toNat < Int.ofNat 256)) = true
              rw [decide_eq_true (int_ofNat_zero_le _), decide_eq_true (int_ofNat_lt_ofNat hlt256)]; rfl
            have henc : mrEncode (.int u8Ty) (.int (Int.ofNat bits.toNat)) =
                some [.init (UInt8.ofNat bits.toNat)] := by
              dsimp only [mrEncode, encodeInt]
              rw [hcan, if_not_true]
              dsimp only [intEmodNat, IntType.bitWidth, Size.bits, u8Ty, Size.bytes,
                mrLeBytesOfNat, List.map]
              rw [nat_mod_eq_of_lt hlt256, nat_mod_eq_of_lt hlt256]
            have hdec : mrDecode .bool [.init (UInt8.ofNat bits.toNat)] = none := by
              dsimp only [mrDecode]
              rw [h0, h1, if_false_eq_true, if_false_eq_true]
            have hsz : (!(MrType.int u8Ty).size.bytes.beq MrType.bool.size.bytes) = false := rfl
            have htrErr : evalTransmute (.int (Int.ofNat bits.toNat)) (.int u8Ty) .bool =
                .error (.ub "transmuted value is not valid at new type") := by
              dsimp only [evalTransmute]
              rw [ite_bool_false hsz, henc]; dsimp only; rw [hdec]
            exact ⟨_, evalUnOp_cast_transmute_err _ _ _ _ htrErr⟩
      | _ => cases hadm
    | unit =>
      cases lit with
      | zeroSized => exact ⟨rfl, fun _ _ => rfl⟩
      | _ => cases hadm
    | char =>
      cases lit with
      | scalar bits =>
        dsimp only [constAdmitted] at hadm
        cases hex : exact with
        | true => rw [hex] at hadm; cases hadm
        | false =>
          rw [hex, Bool.not_false, Bool.true_and] at hadm
          have htrunc : truncateBits .i32 bits = bits := eq_of_beq hadm
          have hne : (truncateBits .i32 bits != bits) = false := by
            dsimp only [bne]; rw [hadm]; rfl
          dsimp only [evalConstLit]; rw [hne, if_false_eq_true]
          cases hu : isUnicodeScalar bits.toNat with
          | true =>
            rw [if_true_eq_true]
            refine ⟨rfl, fun frame mem => ?_⟩
            dsimp only [translateConst, evalValue, evalConstant, translateVal, translateTy]
            rw [htrunc, char_ofNat_toNat_of_isUnicodeScalar bits.toNat hu]
          | false =>
            rw [if_false_eq_true]
            intro hexT; cases hexT
      | _ => cases hadm
    | ordering =>
      cases lit with
      | scalar bits =>
        dsimp only [constAdmitted] at hadm
        have htrunc : truncateBits .i8 bits = bits := eq_of_beq hadm
        have hne : (truncateBits .i8 bits != bits) = false := by dsimp only [bne]; rw [hadm]; rfl
        dsimp only [evalConstLit]; rw [hne, if_false_eq_true]
        cases hord : orderingOfTagBits bits.toNat with
        | some ord =>
          refine ⟨rfl, fun frame mem => ?_⟩
          dsimp only [translateConst]; rw [hord]; cases ord <;> rfl
        | none =>
          intro _ frame mem
          dsimp only [translateConst]; rw [hord]
          rw [evalValue_unOp, evalValue_constant]
          dsimp only [evalConstant]
          have hcan : i8Ty.canRepresent (decodeScalar ⟨.i8, true, bits⟩) = true :=
            canRepresent_decodeScalar .i8 true bits
          have hsz : (!(MrType.int i8Ty).size.bytes.beq orderingTy.size.bytes) = false := rfl
          cases decodeInt_encodeInt i8Ty (decodeScalar ⟨.i8, true, bits⟩) (by decide) hcan with
          | intro bs hbs =>
            have henc : mrEncode (.int i8Ty) (.int (decodeScalar ⟨.i8, true, bits⟩)) = some bs := hbs.1
            have hdec : mrDecode orderingTy bs = none := by
              dsimp only [mrDecode, MrType.size, orderingTy]
              have hlen : (!bs.length.beq 1) = false := by rw [hbs.2.1]; rfl
              rw [ite_bool_false hlen]
              dsimp only [decodeDiscriminant]
              have hsub : byteSubslice bs 0 i8Ty.size.bytes = bs := by
                have h := byteSubslice_zero_eq bs; rw [hbs.2.1] at h; exact h
              rw [hsub, hbs.2.2]
              dsimp only [decodeDiscrBranches]
              have hmodEq : intEmodNat (decodeScalar ⟨.i8, true, bits⟩) 256 = bits.toNat := by
                have h := intEmodNat_decodeScalar .i8 true bits; rw [htrunc] at h; exact h
              have hnotM1 : decodeScalar ⟨.i8, true, bits⟩ ≠ Neg.neg 1 := by
                intro heq; rw [heq] at hmodEq
                have h255 : bits.toNat = 255 := hmodEq.symm
                dsimp only [orderingOfTagBits] at hord; rw [h255] at hord; cases hord
              have hnot0 : decodeScalar ⟨.i8, true, bits⟩ ≠ 0 := by
                intro heq; rw [heq] at hmodEq
                have h0 : bits.toNat = 0 := hmodEq.symm
                dsimp only [orderingOfTagBits] at hord; rw [h0] at hord; cases hord
              have hnot1 : decodeScalar ⟨.i8, true, bits⟩ ≠ 1 := by
                intro heq; rw [heq] at hmodEq
                have h1 : bits.toNat = 1 := hmodEq.symm
                dsimp only [orderingOfTagBits] at hord; rw [h1] at hord; cases hord
              have hbandFalse : ∀ k : Int, k ≠ decodeScalar ⟨.i8, true, bits⟩ →
                  (decide (k ≤ decodeScalar ⟨.i8, true, bits⟩) &&
                    decide (decodeScalar ⟨.i8, true, bits⟩ < k + 1)) = false := by
                intro k hnek
                cases hc1 : decide (k ≤ decodeScalar ⟨.i8, true, bits⟩) with
                | false => rfl
                | true =>
                  cases hc2 : decide (decodeScalar ⟨.i8, true, bits⟩ < k + 1) with
                  | false => rfl
                  | true =>
                    exact False.elim (hnek (int_le_antisymm (of_decide_eq_true hc1)
                      (int_lt_add_one_iff_le.mp (of_decide_eq_true hc2))))
              have hbm1 : (decide (Neg.neg 1 ≤ decodeScalar ⟨.i8, true, bits⟩) &&
                  decide (decodeScalar ⟨.i8, true, bits⟩ < 0)) = false :=
                hbandFalse (Neg.neg 1) (fun h => hnotM1 h.symm)
              have hb0 : (decide ((0 : Int) ≤ decodeScalar ⟨.i8, true, bits⟩) &&
                  decide (decodeScalar ⟨.i8, true, bits⟩ < 1)) = false :=
                hbandFalse 0 (fun h => hnot0 h.symm)
              have hb1 : (decide ((1 : Int) ≤ decodeScalar ⟨.i8, true, bits⟩) &&
                  decide (decodeScalar ⟨.i8, true, bits⟩ < 2)) = false :=
                hbandFalse 1 (fun h => hnot1 h.symm)
              rw [hbm1, if_false_eq_true, hb0, if_false_eq_true, hb1, if_false_eq_true]
            have htrErr : evalTransmute (.int (decodeScalar ⟨.i8, true, bits⟩))
                (.int i8Ty) orderingTy =
                .error (.ub "transmuted value is not valid at new type") := by
              dsimp only [evalTransmute]
              rw [ite_bool_false hsz, henc]; dsimp only; rw [hdec]
            exact ⟨_, evalUnOp_cast_transmute_err _ _ _ _ htrErr⟩
      | _ => cases hadm
    | enum ety =>
      cases lit with
      | rodataBytes _ | rodataRef _ _ _ _ => cases hadm
      | zeroSized =>
        dsimp only [constAdmitted] at hadm
        dsimp only [evalConstLit]; rw [hadm, if_true_eq_true]
        have hrepr : ety.tagRepr = .zeroSized ∧ enumAdmitted ety = true := by
          dsimp only [isZstEnumTy] at hadm
          cases hr : ety.tagRepr with
          | scalar _ _ => rw [hr] at hadm; cases hadm
          | zeroSized => rw [hr] at hadm; exact ⟨rfl, hadm⟩
        have hlen1 : ety.discriminants.length = 1 := by
          have ha := hrepr.2; dsimp only [enumAdmitted] at ha; rw [hrepr.1] at ha
          cases h1 : !ety.discriminants.isEmpty with
          | false => rw [h1] at ha; cases ha
          | true =>
            cases h2 : Nat.blt ety.discriminants.length (Nat.pow 2 32) with
            | false => rw [h1, h2] at ha; cases ha
            | true =>
              cases h3 : ety.discriminants.all _ with
              | false => rw [h1, h2, h3] at ha; cases ha
              | true =>
                cases h4 : natListPairwiseNe ety.discriminants with
                | false => rw [h1, h2, h3, h4] at ha; cases ha
                | true => rw [h1, h2, h3, h4] at ha; exact Nat.eq_of_beq_eq_true ha
        refine ⟨checkVal_enum_mk ety 0 hrepr.2 (by rw [hlen1]; exact Nat.zero_lt_succ 0),
          fun frame mem =>
            evalValue_translateConst_enum_zeroSized ety frame mem hrepr.1⟩
      | scalar bits =>
        dsimp only [constAdmitted] at hadm
        cases hrepr : ety.tagRepr with
        | zeroSized => rw [hrepr] at hadm; cases hadm
        | scalar tagW tagS =>
          rw [hrepr] at hadm
          cases hea : enumAdmitted ety with
          | false => rw [hea] at hadm; cases hadm
          | true =>
            rw [hea] at hadm
            dsimp only at hadm
            rw [Bool.true_and] at hadm
            have htrunc : truncateBits tagW bits = bits := eq_of_beq hadm
            have hne : (truncateBits tagW bits != bits) = false := by dsimp only [bne]; rw [hadm]; rfl
            have hcondFalse : (!true || false) = false := rfl
            dsimp only [evalConstLit]; rw [hrepr, hea]; dsimp only; rw [hne, hcondFalse, if_false_eq_true]
            cases hfind : findDiscrVariant?
                (tagBitsToDiscrBits tagW tagS ety.discrWidth bits) ety.discriminants with
            | some v =>
              cases findDiscrVariant?_lt _ _ _ hfind with
              | intro hvLt _ =>
                refine ⟨checkVal_enum_mk ety v hea hvLt, fun frame mem =>
                  evalValue_translateConst_enum_scalar ety tagW tagS bits v
                    frame mem hrepr hfind⟩
            | none =>
              intro _ frame mem
              dsimp only [translateConst]; rw [hrepr]; dsimp only; rw [hfind]
              rw [evalValue_unOp, evalValue_constant]
              dsimp only [evalConstant]
              have hcan := canRepresent_decodeScalar tagW tagS bits
              dsimp only [translateEnumTy]
              rw [hrepr]
              have hsz : (!(MrType.int (translateIntTy tagW tagS)).size.bytes.beq
                  (MrType.enum (buildEnumVariants ety tagW tagS ety.discriminants)
                    (.branch 0 (translateIntTy tagW tagS)
                      (buildEnumBranches ety tagW tagS ety.discriminants) .invalid)
                    (translateIntTy ety.discrWidth ety.discrSigned)
                    ⟨tagW.byteSize⟩ ⟨tagW.byteSize⟩).size.bytes) = false := by
                dsimp only [MrType.size, translateIntTy, Size.bytes]; rw [Nat.beq_refl]; rfl
              cases decodeInt_encodeInt (translateIntTy tagW tagS)
                  (decodeScalar ⟨tagW, tagS, bits⟩) (intWidth_bitWidth_pos tagW) hcan with
              | intro bs hbs =>
                have henc : mrEncode (.int (translateIntTy tagW tagS))
                    (.int (decodeScalar ⟨tagW, tagS, bits⟩)) = some bs := hbs.1
                have hdec : mrDecode
                    (MrType.enum (buildEnumVariants ety tagW tagS ety.discriminants)
                      (.branch 0 (translateIntTy tagW tagS)
                        (buildEnumBranches ety tagW tagS ety.discriminants) .invalid)
                      (translateIntTy ety.discrWidth ety.discrSigned)
                      ⟨tagW.byteSize⟩ ⟨tagW.byteSize⟩) bs = none := by
                  dsimp only [mrDecode, MrType.size]
                  have hlenBs : bs.length = tagW.byteSize := hbs.2.1
                  have hlen : (!bs.length.beq tagW.byteSize) = false := by
                    rw [hlenBs, Nat.beq_refl]; rfl
                  rw [ite_bool_false hlen]
                  dsimp only [decodeDiscriminant]
                  have hsub : byteSubslice bs 0 (translateIntTy tagW tagS).size.bytes = bs := by
                    have h := byteSubslice_zero_eq bs; rw [hlenBs] at h; exact h
                  rw [hsub, hbs.2.2]; dsimp only
                  have hnoMatch : ∀ d, d ∈ ety.discriminants →
                      tagIntOfNat tagW tagS d ≠ decodeScalar ⟨tagW, tagS, bits⟩ := by
                    intro d hdin heqTag
                    have hnotEq := findDiscrVariant?_none_not_in
                      (tagBitsToDiscrBits tagW tagS ety.discrWidth bits) ety.discriminants hfind d hdin
                    have hrtAll : ety.discriminants.all (fun x =>
                        tagBitsToDiscrBits tagW tagS ety.discrWidth
                          (truncateBits tagW (BitVec.ofNat 128 x)) == BitVec.ofNat 128 x) = true := by
                      dsimp only [enumAdmitted] at hea; rw [hrepr] at hea
                      cases h1 : !ety.discriminants.isEmpty with
                      | false => rw [h1] at hea; cases hea
                      | true =>
                        cases h2 : Nat.blt ety.discriminants.length (Nat.pow 2 32) with
                        | false => rw [h1, h2] at hea; cases hea
                        | true =>
                          cases h3 : ety.discriminants.all (fun x => Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth)) with
                          | false => rw [h1, h2, h3] at hea; cases hea
                          | true =>
                            cases h4 : natListPairwiseNe ety.discriminants with
                            | false => rw [h1, h2, h3, h4] at hea; cases hea
                            | true => rw [h1, h2, h3, h4] at hea; exact hea
                    have hmemAll : ∀ (p : Nat → Bool) (xs : List Nat),
                        xs.all p = true → ∀ x, x ∈ xs → p x = true := by
                      intro p xs; induction xs with
                      | nil => intro _ _ hin; cases hin
                      | cons a as iha =>
                        intro ha x hin; dsimp only [List.all] at ha
                        cases hpa : p a with
                        | false => rw [hpa] at ha; cases ha
                        | true =>
                          rw [hpa] at ha
                          cases hin with | head => exact hpa | tail _ ht => exact iha ha x ht
                    have hrtD : tagBitsToDiscrBits tagW tagS ety.discrWidth
                        (truncateBits tagW (BitVec.ofNat 128 d)) = BitVec.ofNat 128 d :=
                      eq_of_beq (hmemAll _ ety.discriminants hrtAll d hdin)
                    have hbitsEq : truncateBits tagW (BitVec.ofNat 128 d) = bits := by
                      have h1 := intEmodNat_decodeScalar tagW tagS (truncateBits tagW (BitVec.ofNat 128 d))
                      have h2 := intEmodNat_decodeScalar tagW tagS bits
                      have htrD : truncateBits tagW (truncateBits tagW (BitVec.ofNat 128 d)) =
                          truncateBits tagW (BitVec.ofNat 128 d) := by
                        apply bv_eq_of_toNat_eq
                        rw [truncateBits_toNat, truncateBits_toNat]
                        exact nat_mod_mod_local _ (Nat.pow 2 tagW.bitWidth) (Nat.pow_pos (by decide))
                      rw [htrD] at h1; rw [htrunc] at h2
                      dsimp only [tagIntOfNat] at heqTag; rw [heqTag] at h1
                      exact bv_eq_of_toNat_eq (Eq.trans h1.symm h2)
                    rw [hbitsEq] at hrtD; exact hnotEq hrtD.symm
                  rw [decodeDiscrBranches_none_of_not_match bs tagW tagS ety
                    (decodeScalar ⟨tagW, tagS, bits⟩) ety.discriminants hnoMatch]
                have htrErr : evalTransmute (.int (decodeScalar ⟨tagW, tagS, bits⟩))
                    (.int (translateIntTy tagW tagS))
                    (MrType.enum (buildEnumVariants ety tagW tagS ety.discriminants)
                      (.branch 0 (translateIntTy tagW tagS)
                        (buildEnumBranches ety tagW tagS ety.discriminants) .invalid)
                      (translateIntTy ety.discrWidth ety.discrSigned)
                      ⟨tagW.byteSize⟩ ⟨tagW.byteSize⟩) =
                    .error (.ub "transmuted value is not valid at new type") := by
                  dsimp only [evalTransmute]
                  rw [ite_bool_false hsz, henc]; dsimp only; rw [hdec]
                exact ⟨_, evalUnOp_cast_transmute_err _ _ _ _ htrErr⟩
    | _ => cases hadm

/-! ## Operand and Rvalue Evaluation Correspondence Under Frame Invariant -/

theorem getElem?_setElem?_eq {α : Type} (xs : List α) (i : Nat) (v : α)
    (xs' : List α) (h : setElem? xs i v = some xs') :
    Trusted.MirSemantics.getElem? xs' i = some v := by
  induction xs generalizing i xs' with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => dsimp only [setElem?] at h; injection h with h1; subst h1; rfl
    | succ k =>
      dsimp only [setElem?] at h
      cases hset : setElem? xs k v with
      | none => rw [hset] at h; cases h
      | some ys => rw [hset] at h; injection h with h1; subst h1; exact ih k ys hset

theorem getElem?_setElem?_ne {α : Type} (xs : List α) (i j : Nat) (v : α)
    (xs' : List α) (h : setElem? xs i v = some xs') (hne : i ≠ j) :
    Trusted.MirSemantics.getElem? xs' j = Trusted.MirSemantics.getElem? xs j := by
  induction xs generalizing i j xs' with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero =>
      dsimp only [setElem?] at h; injection h with h1; subst h1
      cases j with | zero => exact False.elim (hne rfl) | succ m => rfl
    | succ k =>
      dsimp only [setElem?] at h
      cases hset : setElem? xs k v with
      | none => rw [hset] at h; cases h
      | some ys =>
        rw [hset] at h; injection h with h1; subst h1
        cases j with
        | zero => rfl
        | succ m => exact ih k m ys hset (fun heq => hne (congrArg Nat.succ heq))

theorem setElem?_some_of_getElem?_some {α : Type} (xs : List α) (i : Nat)
    (v old : α) (h : Trusted.MirSemantics.getElem? xs i = some old) :
    ∃ xs', setElem? xs i v = some xs' ∧ xs'.length = xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => exact ⟨v :: xs, rfl, rfl⟩
    | succ k =>
      cases ih k h with
      | intro ys hys =>
        refine ⟨x :: ys, ?_, congrArg Nat.succ hys.2⟩
        dsimp only [setElem?]; rw [hys.1]

/-- Frame-level slot coupling predicate extracted from `StateRel exact`. -/
def FrameSlotsRel (exact : Bool) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mrLocals : LocalMap) (mem : MrMemory) : Prop :=
  locals.length = bodyLocals.length ∧
  (∀ i ty slot,
    Trusted.MirSemantics.getElem? bodyLocals i = some ty →
    Trusted.MirSemantics.getElem? locals i = some slot →
    SlotRel exact mem ty slot (localMapGet? i mrLocals))

/-- Operand evaluation correspondence (`evalOperandToSlot` vs.
`evalValue (translateOperand opnd)`). -/
theorem evalOperandToSlot_sim (exact : Bool) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (memS : MemoryState)
    (mrFrame : StackFrame) (mrMem : MrMemory)
    (tyOk : MirTy → Bool) (opnd : Operand) (opTy : MirTy)
    (hfnLoc : mrFrame.func.locals = bodyLocals.map translateTy)
    (hsupp : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (hrel : FrameSlotsRel exact bodyLocals locals mrFrame.locals mrMem)
    (hadm : operandAdmitted exact bodyLocals opnd = true)
    (hty : operandTy? bodyLocals opnd = some opTy) :
    match evalOperandToSlot bodyLocals locals memS tyOk opnd with
    | .ok (ty, optVal, locals', memS') =>
      ty = opTy ∧
      memS' = memS ∧
      FrameSlotsRel exact bodyLocals locals' mrFrame.locals mrMem ∧
      (exact = true → locals' = locals) ∧
      (∀ i optV, Trusted.MirSemantics.getElem? locals i = some (.immediate optV) →
        ∃ optV', Trusted.MirSemantics.getElem? locals' i = some (.immediate optV')) ∧
      match optVal with
      | some v =>
        checkVal v opTy = true ∧
        evalValue mrFrame mrMem (translateOperand opnd) =
          .ok (translateVal v, translateTy opTy)
      | none =>
        exact = true → ∃ msg, evalValue mrFrame mrMem (translateOperand opnd) = .error (.ub msg)
    | .error .undefined =>
      exact = true → ∃ msg, evalValue mrFrame mrMem (translateOperand opnd) = .error (.ub msg)
    | .error .unsupported => False := by
  cases opnd with
  | copy place =>
    dsimp only [operandAdmitted] at hadm
    cases hproj : place.projection.isEmpty with
    | false => rw [hproj] at hadm; cases hadm
    | true =>
      rw [hproj] at hadm
      dsimp only [operandTy?] at hty
      rw [hproj, if_true_eq_true] at hty
      cases hgetTy : Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [hgetTy] at hty; cases hty
      | some ty =>
        rw [hgetTy] at hty; injection hty with htyEq; subst htyEq
        have hltLen : place.localId < locals.length := by
          rw [hrel.1]; rw [getElem?_eq_listGet?] at hgetTy
          exact listGet?_lt_length bodyLocals place.localId ty hgetTy
        cases listGet?_some_of_lt locals place.localId hltLen with
        | intro slot hslot =>
          have hslot' : Trusted.MirSemantics.getElem? locals place.localId = some slot := by
            rw [getElem?_eq_listGet?]; exact hslot
          have hsr := hrel.2 place.localId ty slot hgetTy hslot'
          have htySupp : isSupportedScalarOrUnitTy ty = true := by
            rw [getElem?_eq_listGet?] at hgetTy
            exact listGet?_all isSupportedScalarOrUnitTy bodyLocals place.localId ty hsupp hgetTy
          have hmrLoc : listGet? mrFrame.func.locals place.localId = some (translateTy ty) := by
            rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hgetTy]; rfl
          dsimp only [evalOperandToSlot]; rw [hgetTy, hslot']
          cases slot with
          | dead =>
            intro _
            dsimp only [SlotRel] at hsr
            dsimp only [translateOperand, evalValue, evalPlace]
            rw [hmrLoc, hsr]; exact ⟨_, rfl⟩
          | indirect _ | partialTuple _ => cases hsr
          | immediate optVal =>
            dsimp only
            rw [hproj, if_not_true]
            refine ⟨rfl, rfl, hrel, fun _ => rfl, fun _ ov ho => ⟨ov, ho⟩, ?_⟩
            cases hsr with
            | intro ptr h1 => cases h1 with | intro id h2 => cases h2 with
              | intro data h3 => cases h3 with | intro hmap h4 => cases h4 with
                | intro hlive hval =>
                  cases optVal with
                  | some v =>
                    refine ⟨hval.1, ?_⟩
                    dsimp only [translateOperand, evalValue, evalPlace]
                    rw [hmrLoc, hmap]; dsimp only
                    rw [if_not_true]
                    rw [allocLiveAt_typedLoad mrMem (translateTy ty) ptr id data ⟨1⟩
                      hlive (align_one_isAligned ptr.addr), hval.2]
                  | none =>
                    intro hexact
                    have hrep := hval.2 hexact
                    dsimp only [translateOperand, evalValue, evalPlace]
                    rw [hmrLoc, hmap]; dsimp only
                    rw [if_not_true]
                    rw [allocLiveAt_typedLoad mrMem (translateTy ty) ptr id data ⟨1⟩
                      hlive (align_one_isAligned ptr.addr), hrep,
                      mrDecode_replicate_uninit_none ty htySupp hval.1]
                    exact ⟨_, rfl⟩
  | move place =>
    dsimp only [operandAdmitted] at hadm
    cases hproj : place.projection.isEmpty with
    | false => rw [hproj] at hadm; cases hadm
    | true =>
      rw [hproj, if_not_true] at hadm
      dsimp only [operandTy?] at hty
      rw [hproj, if_true_eq_true] at hty
      cases hgetTy : Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [hgetTy] at hty; cases hty
      | some ty =>
        rw [hgetTy] at hty hadm; injection hty with htyEq; subst htyEq
        dsimp only at hadm
        have hltLen : place.localId < locals.length := by
          rw [hrel.1]; rw [getElem?_eq_listGet?] at hgetTy
          exact listGet?_lt_length bodyLocals place.localId ty hgetTy
        cases listGet?_some_of_lt locals place.localId hltLen with
        | intro slot hslot =>
          have hslot' : Trusted.MirSemantics.getElem? locals place.localId = some slot := by
            rw [getElem?_eq_listGet?]; exact hslot
          have hsr := hrel.2 place.localId ty slot hgetTy hslot'
          have htySupp : isSupportedScalarOrUnitTy ty = true := by
            rw [getElem?_eq_listGet?] at hgetTy
            exact listGet?_all isSupportedScalarOrUnitTy bodyLocals place.localId ty hsupp hgetTy
          have hmrLoc : listGet? mrFrame.func.locals place.localId = some (translateTy ty) := by
            rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hgetTy]; rfl
          dsimp only [evalOperandToSlot]; rw [hgetTy, hslot']
          cases slot with
          | dead =>
            intro _
            dsimp only [SlotRel] at hsr
            dsimp only [translateOperand, evalValue, evalPlace]
            rw [hmrLoc, hsr]; exact ⟨_, rfl⟩
          | indirect _ | partialTuple _ => cases hsr
          | immediate optVal =>
            dsimp only
            rw [hproj, if_not_true]
            cases setElem?_some_of_getElem?_some locals place.localId (liveUninitSlot ty)
                (.immediate optVal) hslot' with
            | intro locals' hset =>
              rw [hset.1]
              cases hsr with
              | intro ptr h1 => cases h1 with | intro id h2 => cases h2 with
                | intro data h3 => cases h3 with | intro hmap h4 => cases h4 with
                  | intro hlive hval =>
                    have hrel' : FrameSlotsRel exact bodyLocals locals' mrFrame.locals mrMem := by
                      refine ⟨Eq.trans hset.2 hrel.1, fun i tyI slotI htyI hslotI => ?_⟩
                      cases hieq : Nat.beq place.localId i with
                      | true =>
                        have heq : place.localId = i := Nat.eq_of_beq_eq_true hieq; subst heq
                        rw [hgetTy] at htyI; injection htyI with hte; subst hte
                        rw [getElem?_setElem?_eq _ _ _ _ hset.1] at hslotI
                        injection hslotI with hse; subst hse
                        cases hiz : isInhabitedZstTy ty with
                        | true =>
                          have hsz0 : (translateTy ty).size.bytes = 0 := by
                            cases ty with
                            | unit => rfl
                            | enum ety =>
                              dsimp only [isInhabitedZstTy, isZstEnumTy] at hiz
                              cases hr : ety.tagRepr with
                              | scalar _ _ => rw [hr] at hiz; cases hiz
                              | zeroSized => dsimp only [translateTy, translateEnumTy]; rw [hr]; rfl
                            | _ => cases hiz
                          have hdataNil : data = [] := by
                            cases hlive.2 with
                            | intro alloc ha =>
                              have hlen := ha.2.2.2.2.2.2.2; rw [hsz0] at hlen
                              cases data with | nil => rfl | cons _ _ => cases hlen
                          subst hdataNil; rw [hmap]
                          have hliveRep : AllocLiveAt mrMem (translateTy ty) ptr id
                              (List.replicate (translateTy ty).size.bytes .uninit) := by
                            rw [hsz0]; exact hlive
                          exact liveUninitSlot_slotRel exact mrMem ty ptr id htySupp hliveRep
                        | false =>
                          have hexFalse : exact = false := by
                            cases exact with
                            | false => rfl
                            | true => rw [if_true_eq_true, hiz] at hadm; cases hadm
                          have hluNone : liveUninitSlot ty = .immediate none := by
                            cases ty with
                            | unit => cases hiz
                            | enum ety => dsimp only [isInhabitedZstTy] at hiz; dsimp only [liveUninitSlot]; rw [hiz]; rfl
                            | _ => rfl
                          rw [hluNone, hmap]
                          refine ⟨ptr, id, data, rfl, hlive, hiz, fun hexT => ?_⟩
                          rw [hexFalse] at hexT; cases hexT
                      | false =>
                        have hne : place.localId ≠ i := by
                          intro heq; subst heq; rw [Nat.beq_refl] at hieq; cases hieq
                        rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 hne] at hslotI
                        exact hrel.2 i tyI slotI htyI hslotI
                    have hexSame : exact = true → locals' = locals := by
                      intro hexT; rw [hexT, if_true_eq_true] at hadm
                      have hslotEq : liveUninitSlot ty = .immediate optVal := by
                        cases optVal with
                        | none => rw [hval.1] at hadm; cases hadm
                        | some v =>
                          cases ty with
                          | unit => rw [checkVal_unit_elim hval.1]; rfl
                          | enum ety =>
                            dsimp only [isInhabitedZstTy] at hadm
                            dsimp only [liveUninitSlot]; rw [hadm, if_true_eq_true]
                            cases checkVal_enum_elim hval.1 with
                            | intro idx hidx =>
                              have hrepr : ety.tagRepr = .zeroSized := by
                                dsimp only [isZstEnumTy] at hadm
                                cases hr : ety.tagRepr with
                                | zeroSized => rfl | scalar _ _ => rw [hr] at hadm; cases hadm
                              have hlen1 : ety.discriminants.length = 1 := by
                                have ha := hidx.2.1; dsimp only [enumAdmitted] at ha; rw [hrepr] at ha
                                cases h1' : !ety.discriminants.isEmpty with
                                | false => rw [h1'] at ha; cases ha
                                | true =>
                                  cases h2' : Nat.blt ety.discriminants.length (Nat.pow 2 32) with
                                  | false => rw [h1', h2'] at ha; cases ha
                                  | true =>
                                    cases h3' : ety.discriminants.all _ with
                                    | false => rw [h1', h2', h3'] at ha; cases ha
                                    | true =>
                                      cases h4' : natListPairwiseNe ety.discriminants with
                                      | false => rw [h1', h2', h3', h4'] at ha; cases ha
                                      | true => rw [h1', h2', h3', h4'] at ha; exact Nat.eq_of_beq_eq_true ha
                              have hidx0 : idx = 0 := by
                                have hlt := hidx.2.2; rw [hlen1] at hlt
                                cases idx with
                                | zero => rfl
                                | succ k => exact False.elim (Nat.not_lt_zero k (Nat.lt_of_succ_lt_succ hlt))
                              rw [hidx.1, hidx0]
                          | _ => cases hadm
                      have hsetId : ∀ (xs : List LocalSlot) (idx : Nat) (x : LocalSlot),
                          Trusted.MirSemantics.getElem? xs idx = some x →
                          setElem? xs idx x = some xs := by
                        intro xs; induction xs with
                        | nil => intro idx x hg; cases hg
                        | cons a as iha =>
                          intro idx x hg; cases idx with
                          | zero => dsimp only [Trusted.MirSemantics.getElem?] at hg; injection hg with hax; subst hax; rfl
                          | succ k => dsimp only [setElem?]; rw [iha k x hg]
                      have h := hset.1
                      rw [hslotEq, hsetId locals place.localId (.immediate optVal) hslot'] at h
                      injection h with hlEq; exact hlEq.symm
                    have hpresImm : ∀ i optV,
                        Trusted.MirSemantics.getElem? locals i = some (.immediate optV) →
                        ∃ optV', Trusted.MirSemantics.getElem? locals' i = some (.immediate optV') := by
                      intro i optV hi
                      cases hieq : Nat.beq place.localId i with
                      | true =>
                        have heq := Nat.eq_of_beq_eq_true hieq; subst heq
                        rw [getElem?_setElem?_eq _ _ _ _ hset.1]
                        cases liveUninitSlot_isImmediate ty with
                        | intro ov hov => exact ⟨ov, congrArg some hov⟩
                      | false =>
                        have hne : place.localId ≠ i := by
                          intro heq; subst heq; rw [Nat.beq_refl] at hieq; cases hieq
                        rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 hne]; exact ⟨optV, hi⟩
                    refine ⟨rfl, rfl, hrel', hexSame, hpresImm, ?_⟩
                    cases optVal with
                    | some v =>
                      refine ⟨hval.1, ?_⟩
                      dsimp only [translateOperand, evalValue, evalPlace]
                      rw [hmrLoc, hmap]; dsimp only
                      rw [if_not_true]
                      rw [allocLiveAt_typedLoad mrMem (translateTy ty) ptr id data ⟨1⟩
                        hlive (align_one_isAligned ptr.addr), hval.2]
                    | none =>
                      intro hexact
                      have hrep := hval.2 hexact
                      dsimp only [translateOperand, evalValue, evalPlace]
                      rw [hmrLoc, hmap]; dsimp only
                      rw [if_not_true]
                      rw [allocLiveAt_typedLoad mrMem (translateTy ty) ptr id data ⟨1⟩
                        hlive (align_one_isAligned ptr.addr), hrep,
                        mrDecode_replicate_uninit_none ty htySupp hval.1]
                      exact ⟨_, rfl⟩
  | constant c =>
    dsimp only [operandAdmitted] at hadm
    dsimp only [operandTy?] at hty
    injection hty with htyEq; subst htyEq
    have hcs := evalConstLit_sim exact c hadm
    dsimp only [evalOperandToSlot]
    cases hc : evalConstLit c.ty c.lit with
    | ok v =>
      rw [hc] at hcs
      refine ⟨rfl, rfl, hrel, fun _ => rfl, fun _ ov ho => ⟨ov, ho⟩,
        hcs.1, hcs.2 mrFrame mrMem⟩
    | error fk =>
      rw [hc] at hcs
      cases fk with
      | undefined => intro hexT; exact hcs hexT mrFrame mrMem
      | unsupported => exact hcs

/-- Primitive operand evaluation correspondence (`evalPrimitiveOperand`). -/
theorem evalPrimitiveOperand_sim (exact : Bool) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (memS : MemoryState)
    (mrFrame : StackFrame) (mrMem : MrMemory)
    (opnd : Operand) (opTy : MirTy)
    (hfnLoc : mrFrame.func.locals = bodyLocals.map translateTy)
    (hsupp : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (hrel : FrameSlotsRel exact bodyLocals locals mrFrame.locals mrMem)
    (hadm : operandAdmitted exact bodyLocals opnd = true)
    (hty : operandTy? bodyLocals opnd = some opTy)
    (hprim : isPrimitiveReadableTy opTy = true) :
    match evalPrimitiveOperand bodyLocals locals memS opnd with
    | .ok (v, locals', memS') =>
      memS' = memS ∧
      checkVal v opTy = true ∧
      FrameSlotsRel exact bodyLocals locals' mrFrame.locals mrMem ∧
      (exact = true → locals' = locals) ∧
      (∀ i optV, Trusted.MirSemantics.getElem? locals i = some (.immediate optV) →
        ∃ optV', Trusted.MirSemantics.getElem? locals' i = some (.immediate optV')) ∧
      evalValue mrFrame mrMem (translateOperand opnd) =
        .ok (translateVal v, translateTy opTy)
    | .error .undefined =>
      exact = true → ∃ msg, evalValue mrFrame mrMem (translateOperand opnd) = .error (.ub msg)
    | .error .unsupported => False := by
  have hos := evalOperandToSlot_sim exact bodyLocals locals memS mrFrame mrMem
    isPrimitiveReadableTy opnd opTy hfnLoc hsupp hrel hadm hty
  dsimp only [evalPrimitiveOperand]
  cases ho : evalOperandToSlot bodyLocals locals memS isPrimitiveReadableTy opnd with
  | error fk =>
    rw [ho] at hos
    cases fk with
    | undefined => exact hos
    | unsupported => exact hos
  | ok res =>
    rw [ho] at hos
    cases res with
    | mk ty r1 => cases r1 with | mk optVal r2 => cases r2 with
      | mk locals' memS' =>
        cases hos with
        | intro htyEq hrest =>
          subst htyEq
          dsimp only
          rw [hprim, if_not_true]
          cases optVal with
          | some v =>
            exact ⟨hrest.1, hrest.2.2.2.2.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1,
              hrest.2.2.2.2.2⟩
          | none => exact hrest.2.2.2.2

theorem ptrOffsetInbounds_zero (mem : MrMemory) (ptr : ThinPtr) :
    ptrOffsetInbounds mem ptr 0 = .ok ptr := by
  cases ptr; rfl

theorem evalDiscrBranchesMem_buildEnum (mem : MrMemory) (ptr : ThinPtr)
    (bytes : List AbstractByte) (v : Int) (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (ds : List Nat) :
    evalDiscrBranchesMem mem ptr v (buildEnumBranches ety tagW tagS ds) =
      .ok (decodeDiscrBranches bytes v (buildEnumBranches ety tagW tagS ds)) := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    dsimp only [buildEnumBranches, evalDiscrBranchesMem, decodeDiscrBranches]
    cases hc : (decide (tagIntOfNat tagW tagS d ≤ v) &&
        decide (v < tagIntOfNat tagW tagS d + 1)) with
    | true => rfl
    | false => exact ih

/-- Master `evalRvalue` correspondence theorem against MiniRust
`evalValue mrFrame mrMem (translateRvalue bodyLocals rv)`. -/
theorem evalRvalue_sim (exact : Bool) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (memS : MemoryState)
    (mrFrame : StackFrame) (mrMem : MrMemory)
    (dstTy : MirTy) (rv : Rvalue)
    (hfnLoc : mrFrame.func.locals = bodyLocals.map translateTy)
    (hsupp : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (hrel : FrameSlotsRel exact bodyLocals locals mrFrame.locals mrMem)
    (hadm : rvalueAdmitted exact bodyLocals dstTy rv = true) :
    match evalRvalue bodyLocals locals memS dstTy rv with
    | .ok (res, locals', memS') =>
      memS' = memS ∧
      checkVal res dstTy = true ∧
      FrameSlotsRel exact bodyLocals locals' mrFrame.locals mrMem ∧
      (exact = true → locals' = locals) ∧
      (∀ i optV, Trusted.MirSemantics.getElem? locals i = some (.immediate optV) →
        ∃ optV', Trusted.MirSemantics.getElem? locals' i = some (.immediate optV')) ∧
      evalValue mrFrame mrMem (translateRvalue bodyLocals rv) =
        .ok (translateVal res, translateTy dstTy)
    | .error .undefined =>
      exact = true → ∃ msg, evalValue mrFrame mrMem (translateRvalue bodyLocals rv) = .error (.ub msg)
    | .error .unsupported => False := by
  cases rv with
  | use opnd =>
    dsimp only [rvalueAdmitted] at hadm
    cases hoa : operandAdmitted exact bodyLocals opnd with
    | false => rw [hoa] at hadm; cases hadm
    | true =>
      rw [hoa, Bool.true_and] at hadm
      cases hot : operandTy? bodyLocals opnd with
      | none => rw [hot] at hadm; cases hadm
      | some srcTy =>
        rw [hot] at hadm
        have htyEq : srcTy = dstTy := mirTy_eq_of_beq hadm; subst htyEq
        have hos := evalOperandToSlot_sim exact bodyLocals locals memS mrFrame mrMem
          (fun t => MirTy.beq t srcTy) opnd srcTy hfnLoc hsupp hrel hoa hot
        dsimp only [evalRvalue, translateRvalue]
        cases ho : evalOperandToSlot bodyLocals locals memS (fun t => MirTy.beq t srcTy) opnd with
        | error fk =>
          rw [ho] at hos
          cases fk with | undefined => exact hos | unsupported => exact hos
        | ok r =>
          rw [ho] at hos
          cases r with
          | mk ty1 r1 => cases r1 with | mk optVal r2 => cases r2 with
            | mk locals' memS' =>
              cases hos with
              | intro ht1 hrest =>
                subst ht1
                dsimp only
                dsimp only at hadm
                rw [hadm, if_not_true]
                cases optVal with
                | some v =>
                  exact ⟨hrest.1, hrest.2.2.2.2.1, hrest.2.1, hrest.2.2.1,
                    hrest.2.2.2.1, hrest.2.2.2.2.2⟩
                | none => exact hrest.2.2.2.2
  | unaryOp op opnd =>
    dsimp only [rvalueAdmitted] at hadm
    cases hoa : operandAdmitted exact bodyLocals opnd with
    | false => rw [hoa] at hadm; cases hadm
    | true =>
      rw [hoa, Bool.true_and] at hadm
      cases hot : operandTy? bodyLocals opnd with
      | none => rw [hot] at hadm; cases op <;> cases hadm
      | some srcTy =>
        rw [hot] at hadm
        have hprim : isPrimitiveReadableTy srcTy = true := by
          cases op <;> cases srcTy <;> (first | rfl | cases hadm)
        have hps := evalPrimitiveOperand_sim exact bodyLocals locals memS mrFrame mrMem
          opnd srcTy hfnLoc hsupp hrel hoa hot hprim
        dsimp only [evalRvalue, translateRvalue]; rw [hot]
        cases hp : evalPrimitiveOperand bodyLocals locals memS opnd with
        | error fk =>
          rw [hp] at hps
          cases fk with
          | unsupported => exact hps
          | undefined =>
            intro hexT
            cases hps hexT with
            | intro msg hmsg =>
              cases op with
              | ptrMetadata => cases hadm
              | not =>
                cases srcTy with
                | bool => dsimp only [evalValue]; rw [hmsg]; exact ⟨msg, rfl⟩
                | int _ _ => dsimp only [evalValue]; rw [hmsg]; exact ⟨msg, rfl⟩
                | _ => cases hadm
              | neg =>
                cases srcTy with
                | int _ s =>
                  cases s with
                  | false => cases hadm
                  | true => dsimp only [evalValue]; rw [hmsg]; exact ⟨msg, rfl⟩
                | _ => cases hadm
        | ok r =>
          rw [hp] at hps
          cases r with
          | mk v r1 => cases r1 with | mk locals' memS' =>
            dsimp only
            cases evalUnOp_sim op srcTy dstTy v hps.2.1 hadm with
            | intro res hres =>
              rw [hres.1]
              exact ⟨hps.1, hres.2.1, hps.2.2.1, hps.2.2.2.1, hps.2.2.2.2.1,
                hres.2.2 mrFrame mrMem (translateOperand opnd) hps.2.2.2.2.2⟩
  | binaryOp op lhs rhs =>
    dsimp only [rvalueAdmitted] at hadm
    cases hla : operandAdmitted exact bodyLocals lhs with
    | false => rw [hla] at hadm; cases hadm
    | true =>
      cases hra : operandAdmitted exact bodyLocals rhs with
      | false => rw [hla, hra] at hadm; cases hadm
      | true =>
        rw [hla, hra, Bool.true_and, Bool.true_and] at hadm
        cases hlt : operandTy? bodyLocals lhs with
        | none => rw [hlt] at hadm; cases hadm
        | some lTy =>
          cases hrt : operandTy? bodyLocals rhs with
          | none => rw [hlt, hrt] at hadm; cases hadm
          | some rTy =>
            rw [hlt, hrt] at hadm
            dsimp only at hadm
            cases hbr : binOpResultTy? op lTy rTy with
            | none => rw [hbr] at hadm; cases hadm
            | some resTy =>
              rw [hbr] at hadm
              have hresEq : resTy = dstTy := mirTy_eq_of_beq hadm; subst hresEq
              have hlPrim : isPrimitiveReadableTy lTy = true := by
                cases lTy <;> (first | rfl | cases hbr)
              have hrPrim : isPrimitiveReadableTy rTy = true := by
                cases lTy <;> cases rTy <;> (first | rfl | cases hbr)
              have hls := evalPrimitiveOperand_sim exact bodyLocals locals memS mrFrame mrMem
                lhs lTy hfnLoc hsupp hrel hla hlt hlPrim
              have htrBinEq : translateRvalue bodyLocals (.binaryOp op lhs rhs) =
                  translateBinOpExpr op lTy (translateOperand lhs) (translateOperand rhs) := by
                dsimp only [translateRvalue, translateBinOpExpr]; rw [hlt]
                cases lTy <;> rfl
              rw [htrBinEq]
              dsimp only [evalRvalue]
              cases hpl : evalPrimitiveOperand bodyLocals locals memS lhs with
              | error fk =>
                rw [hpl] at hls
                cases fk with
                | unsupported => exact hls
                | undefined =>
                  intro hexT
                  cases hls hexT with
                  | intro msg hmsg =>
                    cases lTy with
                    | int _ _ =>
                      cases op <;> (dsimp only [translateBinOpExpr, evalValue, translateIntBinOp?, translateWithOverflowOp?, translateRelOp?]; rw [hmsg]; exact ⟨msg, rfl⟩)
                    | bool =>
                      cases op <;> (dsimp only [translateBinOpExpr, evalValue, translateRelOp?]; rw [hmsg]; exact ⟨msg, rfl⟩)
                    | char =>
                      cases op <;> (dsimp only [translateBinOpExpr, evalValue, translateRelOp?]; rw [hmsg]; exact ⟨msg, rfl⟩)
                    | _ => cases hbr
              | ok rl =>
                rw [hpl] at hls
                cases rl with
                | mk lVal rl1 => cases rl1 with | mk locals1 memS1 =>
                  have hmem1 : memS1 = memS := hls.1
                  have hrs := evalPrimitiveOperand_sim exact bodyLocals locals1 memS1 mrFrame mrMem
                    rhs rTy hfnLoc hsupp hls.2.2.1 hra hrt hrPrim
                  dsimp only
                  cases hpr : evalPrimitiveOperand bodyLocals locals1 memS1 rhs with
                  | error fk =>
                    rw [hpr] at hrs
                    cases fk with
                    | unsupported => exact hrs
                    | undefined =>
                      intro hexT
                      cases hrs hexT with
                      | intro msg hmsg =>
                        have hle := hls.2.2.2.2.2
                        cases lTy with
                        | int _ _ =>
                          cases rTy with
                          | int _ _ =>
                            cases op with
                            | offset =>
                              have hnotSh : BinOp.offset.isShift = false := rfl
                              dsimp only [binOpResultTy?] at hbr
                              rw [ite_bool_false hnotSh] at hbr
                              cases hbeq : MirTy.beq _ _ with
                              | true => rw [hbeq, if_not_true] at hbr; cases hbr
                              | false => rw [hbeq, if_not_false] at hbr; cases hbr
                            | _ =>
                              dsimp only [translateBinOpExpr, evalValue, translateIntBinOp?,
                                translateWithOverflowOp?, translateRelOp?]
                              rw [hle, hmsg]; exact ⟨msg, rfl⟩
                          | _ => cases hbr
                        | bool =>
                          cases rTy with
                          | bool =>
                            cases checkVal_bool_elim hls.2.1 with
                            | intro lb hlb =>
                              subst hlb
                              cases op with
                              | eq | ne | bitAnd | bitOr | bitXor =>
                                dsimp only [translateBinOpExpr, evalValue, translateRelOp?]
                                rw [hle, hmsg]; exact ⟨msg, rfl⟩
                              | lt | le | gt | ge | cmp =>
                                dsimp only [translateBinOpExpr, evalValue, translateRelOp?]
                                rw [hle]; dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, translateVal, translateTy]
                                rw [hmsg]; exact ⟨msg, rfl⟩
                              | _ => cases hbr
                          | _ => cases hbr
                        | char =>
                          cases rTy with
                          | char =>
                            cases checkVal_char_elim hls.2.1 with
                            | intro lc hlc =>
                              subst hlc
                              cases op with
                              | eq | ne | lt | le | gt | ge | cmp =>
                                dsimp only [translateBinOpExpr, evalValue, translateRelOp?]
                                rw [hle, hmsg]; exact ⟨msg, rfl⟩
                              | _ => cases hbr
                          | _ => cases hbr
                        | _ => cases hbr
                  | ok rr =>
                    rw [hpr] at hrs
                    cases rr with
                    | mk rVal rr1 => cases rr1 with | mk locals2 memS2 =>
                      dsimp only
                      have hbs := evalBinOp_sim op lTy rTy resTy lVal rVal hls.2.1 hrs.2.1 hbr
                      cases hbo : Trusted.MirSemantics.evalBinOp op lVal rVal with
                      | error fk =>
                        rw [hbo] at hbs
                        cases fk with
                        | unsupported => exact hbs
                        | undefined =>
                          intro _
                          exact hbs mrFrame mrMem (translateOperand lhs) (translateOperand rhs)
                            hls.2.2.2.2.2 hrs.2.2.2.2.2
                      | ok res =>
                        rw [hbo] at hbs
                        refine ⟨Eq.trans hrs.1 hmem1, hbs.1, hrs.2.2.1,
                          fun hexT => Eq.trans (hrs.2.2.2.1 hexT) (hls.2.2.2.1 hexT),
                          fun i ov hi => ?_,
                          hbs.2 mrFrame mrMem (translateOperand lhs) (translateOperand rhs)
                            hls.2.2.2.2.2 hrs.2.2.2.2.2⟩
                        cases hls.2.2.2.2.1 i ov hi with
                        | intro ov1 hov1 => exact hrs.2.2.2.2.1 i ov1 hov1
  | cast kind opnd castTy =>
    cases kind with
    | ptrToPtr | intToPtr | unsize | unsupported => cases hadm
    | intToInt =>
      dsimp only [rvalueAdmitted] at hadm
      cases hoa : operandAdmitted exact bodyLocals opnd with
      | false => rw [hoa] at hadm; cases hadm
      | true =>
        cases hct : MirTy.beq castTy dstTy with
        | false => rw [hoa, hct] at hadm; cases hadm
        | true =>
          rw [hoa, hct] at hadm
          have hdstEq : castTy = dstTy := mirTy_eq_of_beq hct; subst hdstEq
          cases hot : operandTy? bodyLocals opnd with
          | none => rw [hot] at hadm; cases castTy <;> cases hadm
          | some srcTy =>
            rw [hot] at hadm
            have hlike : isIntLikeTy srcTy = true := by
              cases castTy with
              | int _ _ => exact hadm
              | char =>
                cases srcTy with
                | int sw ss =>
                  cases sw with
                  | i8 => cases ss with | false => rfl | true => cases hadm
                  | _ => cases hadm
                | _ => cases hadm
              | _ => cases hadm
            have hos := evalOperandToSlot_sim exact bodyLocals locals memS mrFrame mrMem
              isIntLikeTy opnd srcTy hfnLoc hsupp hrel hoa hot
            dsimp only [evalRvalue, translateRvalue]; rw [hot]
            have herrCast : ∀ msg, evalValue mrFrame mrMem (translateOperand opnd) = .error (.ub msg) →
                ∃ m', evalValue mrFrame mrMem
                  (let eInt :=
                    match some srcTy with
                    | some .bool => .unOp (.cast (.transmute (.int u8Ty))) (translateOperand opnd)
                    | _ => translateOperand opnd
                  match castTy with
                  | .int w s => .unOp (.cast (.intToInt (translateIntTy w s))) eInt
                  | .char => .unOp (.cast (.intToInt u32Ty)) eInt
                  | _ => eInt) = .error (.ub m') := by
              intro msg hmsg
              cases castTy with
              | int _ _ => cases srcTy <;> (dsimp only [evalValue]; rw [hmsg]; exact ⟨msg, rfl⟩)
              | char => cases srcTy <;> (dsimp only [evalValue]; rw [hmsg]; exact ⟨msg, rfl⟩)
              | _ => cases hadm
            cases ho : evalOperandToSlot bodyLocals locals memS isIntLikeTy opnd with
            | error fk =>
              rw [ho] at hos
              cases fk with
              | unsupported => exact hos
              | undefined => intro hexT; cases hos hexT with | intro msg hmsg => exact herrCast msg hmsg
            | ok r =>
              rw [ho] at hos
              cases r with
              | mk ty1 r1 => cases r1 with | mk optVal r2 => cases r2 with
                | mk locals' memS' =>
                  cases hos with
                  | intro ht1 hrest =>
                    subst ht1; dsimp only; rw [hlike, if_not_true]
                    cases optVal with
                    | none =>
                      intro hexT
                      cases hrest.2.2.2.2 hexT with
                      | intro msg hmsg => exact herrCast msg hmsg
                    | some v =>
                      dsimp only
                      have hadmCast : intToIntCastAdmitted ty1 castTy = true := by
                        cases castTy with
                        | int _ _ => exact hadm
                        | char =>
                          cases ty1 with
                          | int sw ss =>
                            cases sw with
                            | i8 => cases ss with | false => rfl | true => cases hadm
                            | _ => cases hadm
                          | _ => cases hadm
                        | _ => cases hadm
                      cases evalIntToIntCast_sim ty1 castTy v hrest.2.2.2.2.1 hadmCast with
                      | intro res hres =>
                        rw [hres.1]
                        exact ⟨hrest.1, hres.2.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1,
                          hres.2.2 mrFrame mrMem (translateOperand opnd) hrest.2.2.2.2.2⟩
  | discriminant place =>
    dsimp only [rvalueAdmitted] at hadm
    cases hproj : place.projection.isEmpty with
    | false => rw [hproj] at hadm; cases hadm
    | true =>
      rw [hproj] at hadm
      cases hgetTy : Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [hgetTy] at hadm; cases hadm
      | some srcTy =>
        rw [hgetTy] at hadm
        have hltLen : place.localId < locals.length := by
          rw [hrel.1]; rw [getElem?_eq_listGet?] at hgetTy
          exact listGet?_lt_length bodyLocals place.localId srcTy hgetTy
        cases listGet?_some_of_lt locals place.localId hltLen with
        | intro slot hslot =>
          have hslot' : Trusted.MirSemantics.getElem? locals place.localId = some slot := by
            rw [getElem?_eq_listGet?]; exact hslot
          have hsr := hrel.2 place.localId srcTy slot hgetTy hslot'
          have hmrLoc : listGet? mrFrame.func.locals place.localId = some (translateTy srcTy) := by
            rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hgetTy]; rfl
          dsimp only [evalRvalue, translateRvalue]; rw [hgetTy, hslot']
          cases slot with
          | dead =>
            dsimp only [SlotRel] at hsr; intro _
            dsimp only [evalValue, evalPlace]; rw [hmrLoc, hsr]; exact ⟨_, rfl⟩
          | indirect _ | partialTuple _ => cases hsr
          | immediate optVal =>
            dsimp only
            rw [hproj, if_not_true]
            cases hsr with
            | intro ptr h1 => cases h1 with | intro id h2 => cases h2 with
              | intro data h3 => cases h3 with | intro hmap h4 => cases h4 with
                | intro hlive hval =>
                  cases srcTy with
                  | ordering =>
                    dsimp only at hadm; rw [Bool.true_and] at hadm
                    have hdstEq : dstTy = .int .i8 true := mirTy_eq_of_beq hadm; subst hdstEq
                    dsimp only [evalOrderingDiscriminantOfVal]
                    cases optVal with
                    | none =>
                      intro hexT; have hrep := hval.2 hexT
                      dsimp only [evalValue, evalPlace]
                      rw [hmrLoc, hmap]; dsimp only [translateTy, orderingTy]
                      rw [if_not_true]
                      dsimp only [evalDiscriminantMem]
                      rw [ptrOffsetInbounds_zero]
                      have hload := allocLiveAt_load mrMem orderingTy ptr id data ⟨1⟩
                        hlive (align_one_isAligned ptr.addr)
                      dsimp only [orderingTy, MrType.size] at hload
                      dsimp only [i8Ty]
                      rw [hload, hrep]
                      exact ⟨_, rfl⟩
                    | some v =>
                      cases checkVal_ordering_elim hval.1 with
                      | intro ord hord =>
                        subst hord
                        have hwf : truncateBits .i8 (BitVec.ofNat 128 (orderingTagBits ord)) =
                            BitVec.ofNat 128 (orderingTagBits ord) := by cases ord <;> decide
                        refine ⟨rfl, checkVal_scalar_mk .i8 true _ hwf, hrel,
                          fun _ => rfl, fun _ ov ho => ⟨ov, ho⟩, ?_⟩
                        have hdec := hval.2
                        have hevalOrd : ∀ (target : Int),
                            mrDecode orderingTy data = some (.variant target unitValue) →
                            evalDiscriminantMem mrMem ptr
                              (.branch 0 i8Ty
                                (.cons (Neg.neg 1) 0 (.known (Neg.neg 1))
                                  (.cons 0 1 (.known 0)
                                    (.cons 1 2 (.known 1) .nil)))
                                .invalid) = .ok (some target) := by
                          intro target hmd
                          dsimp only [orderingTy, mrDecode, MrType.size] at hmd
                          cases hlen1 : Nat.beq data.length 1 with
                          | false => rw [hlen1, if_not_false] at hmd; cases hmd
                          | true =>
                            rw [hlen1, if_not_true] at hmd
                            have hsub : byteSubslice data 0 i8Ty.size.bytes = data := by
                              have h := byteSubslice_zero_eq data
                              rw [Nat.eq_of_beq_eq_true hlen1] at h; exact h
                            dsimp only [decodeDiscriminant] at hmd
                            rw [hsub] at hmd
                            have hload := allocLiveAt_load mrMem orderingTy ptr id data ⟨1⟩
                              hlive (align_one_isAligned ptr.addr)
                            dsimp only [orderingTy, MrType.size] at hload
                            dsimp only [evalDiscriminantMem]
                            rw [ptrOffsetInbounds_zero]
                            dsimp only [i8Ty] at hmd; dsimp only [i8Ty]
                            rw [hload]; dsimp only
                            cases hdi : decodeInt { signed := .signed, size := ⟨1⟩ } data with
                            | none => rw [hdi] at hmd; cases hmd
                            | some tv =>
                              rw [hdi] at hmd
                              dsimp only [decodeDiscrBranches, evalDiscrBranchesMem] at hmd
                              dsimp only [decodeDiscrBranches, evalDiscrBranchesMem]
                              cases hc1 : (decide (Neg.neg 1 ≤ tv) && decide (tv < 0)) with
                              | true =>
                                rw [hc1] at hmd; rw [if_true_eq_true] at hmd; rw [if_true_eq_true]
                                dsimp only [decodeDiscriminant] at hmd
                                cases hv' : mrDecodeEnumVariant (Neg.neg 1) _ data with
                                | none => rw [hv'] at hmd; cases hmd
                                | some vv =>
                                  rw [hv'] at hmd; injection hmd with hvEq; injection hvEq with hdEq
                                  rw [← hdEq]; rfl
                              | false =>
                                rw [hc1] at hmd; rw [if_false_eq_true] at hmd; rw [if_false_eq_true]
                                cases hc2 : (decide (0 ≤ tv) && decide (tv < 1)) with
                                | true =>
                                  rw [hc2] at hmd; rw [if_true_eq_true] at hmd; rw [if_true_eq_true]
                                  dsimp only [decodeDiscriminant] at hmd
                                  cases hv' : mrDecodeEnumVariant 0 _ data with
                                  | none => rw [hv'] at hmd; cases hmd
                                  | some vv =>
                                    rw [hv'] at hmd; injection hmd with hvEq; injection hvEq with hdEq
                                    rw [← hdEq]; rfl
                                | false =>
                                  rw [hc2] at hmd; rw [if_false_eq_true] at hmd; rw [if_false_eq_true]
                                  cases hc3 : (decide (1 ≤ tv) && decide (tv < 2)) with
                                  | true =>
                                    rw [hc3] at hmd; rw [if_true_eq_true] at hmd; rw [if_true_eq_true]
                                    dsimp only [decodeDiscriminant] at hmd
                                    cases hv' : mrDecodeEnumVariant 1 _ data with
                                    | none => rw [hv'] at hmd; cases hmd
                                    | some vv =>
                                      rw [hv'] at hmd; injection hmd with hvEq; injection hvEq with hdEq
                                      rw [← hdEq]; rfl
                                  | false =>
                                    rw [hc3] at hmd; rw [if_false_eq_true] at hmd; cases hmd
                        dsimp only [evalValue, evalPlace]
                        rw [hmrLoc, hmap]; dsimp only [translateTy, orderingTy]
                        rw [if_not_true]
                        cases ord with
                        | less => rw [hevalOrd (Neg.neg 1) hdec]; rfl
                        | equal => rw [hevalOrd 0 hdec]; rfl
                        | greater => rw [hevalOrd 1 hdec]; rfl
                  | enum ety =>
                    dsimp only at hadm; rw [Bool.true_and] at hadm
                    cases hea : enumAdmitted ety with
                    | false => rw [hea] at hadm; cases hadm
                    | true =>
                      rw [hea, Bool.true_and] at hadm
                      have hdstEq : dstTy = .int ety.discrWidth ety.discrSigned := mirTy_eq_of_beq hadm
                      subst hdstEq
                      have hwfTrunc : ∀ b : BitVec 128,
                          truncateBits ety.discrWidth (truncateBits ety.discrWidth b) =
                            truncateBits ety.discrWidth b := by
                        intro b; apply bv_eq_of_toNat_eq
                        rw [truncateBits_toNat, truncateBits_toNat]
                        exact nat_mod_mod_local b.toNat (Nat.pow 2 ety.discrWidth.bitWidth) (Nat.pow_pos (by decide))
                      dsimp only [evalDiscriminantOfVal]; rw [hea, if_not_true]
                      cases hrepr : ety.tagRepr with
                      | zeroSized =>
                        have hneList : ety.discriminants.isEmpty = false := by
                          dsimp only [enumAdmitted] at hea
                          cases he : ety.discriminants.isEmpty with
                          | false => rfl | true => rw [he] at hea; cases hea
                        have hget0 : ∃ d0, Trusted.MirSemantics.getElem? ety.discriminants 0 = some d0 := by
                          cases hd : ety.discriminants with
                          | nil => rw [hd] at hneList; cases hneList
                          | cons d0 _ => exact ⟨d0, rfl⟩
                        cases hget0 with
                        | intro d0 hd0 =>
                          cases optVal with
                          | none =>
                            have hiz : isInhabitedZstTy (.enum ety) = true := by
                              dsimp only [isInhabitedZstTy, isZstEnumTy]; rw [hrepr]; exact hea
                            rw [hiz] at hval; cases hval.1
                          | some v =>
                            cases checkVal_enum_elim hval.1 with
                            | intro idx hidx =>
                              cases hidx with
                              | intro hveq hidx2 =>
                                subst hveq
                                have hlen1 : ety.discriminants.length = 1 := by
                                  dsimp only [enumAdmitted] at hea; rw [hrepr] at hea
                                  cases h1' : !ety.discriminants.isEmpty with
                                  | false => rw [h1'] at hea; cases hea
                                  | true =>
                                    cases h2' : Nat.blt ety.discriminants.length (Nat.pow 2 32) with
                                    | false => rw [h1', h2'] at hea; cases hea
                                    | true =>
                                      cases h3' : ety.discriminants.all _ with
                                      | false => rw [h1', h2', h3'] at hea; cases hea
                                      | true =>
                                        cases h4' : natListPairwiseNe ety.discriminants with
                                        | false => rw [h1', h2', h3', h4'] at hea; cases hea
                                        | true => rw [h1', h2', h3', h4'] at hea; exact Nat.eq_of_beq_eq_true hea
                                have hidx0 : idx = 0 := by
                                  have hlt := hidx2.2; rw [hlen1] at hlt
                                  cases idx with
                                  | zero => rfl
                                  | succ k => exact False.elim (Nat.not_lt_zero k (Nat.lt_of_succ_lt_succ hlt))
                                subst hidx0
                                dsimp only
                                simp only [enumTy_beq_refl, Nat.beq, Bool.and_true]
                                rw [hd0]
                                refine ⟨rfl, checkVal_scalar_mk _ _ _ (hwfTrunc _), hrel,
                                  fun _ => rfl, fun _ ov ho => ⟨ov, ho⟩, ?_⟩
                                dsimp only [evalValue, evalPlace]
                                rw [hmrLoc, hmap]; dsimp only [translateTy, translateEnumTy]
                                rw [hrepr]; dsimp only [if_not_true, evalDiscriminantMem,
                                  translateVal, discrIntOfNat]
                                rw [hd0]
                      | scalar tagW tagS =>
                        cases optVal with
                        | none =>
                          intro hexT; have hrep := hval.2 hexT
                          dsimp only [evalValue, evalPlace]
                          rw [hmrLoc, hmap]; dsimp only [translateTy, translateEnumTy]
                          rw [hrepr]; dsimp only; rw [if_not_true]
                          dsimp only [evalDiscriminantMem]
                          rw [ptrOffsetInbounds_zero]
                          have hload := allocLiveAt_load mrMem (translateEnumTy ety) ptr id data ⟨1⟩
                            hlive (align_one_isAligned ptr.addr)
                          dsimp only [translateEnumTy, MrType.size] at hload
                          rw [hrepr] at hload; dsimp only [MrType.size] at hload
                          dsimp only [translateIntTy]
                          rw [hload, hrep]
                          dsimp only [translateTy, translateEnumTy, MrType.size]
                          rw [hrepr]; dsimp only [MrType.size]
                          have hdecN : decodeInt (translateIntTy tagW tagS)
                              (List.replicate tagW.byteSize AbstractByte.uninit) = none :=
                            decodeInt_replicate_uninit (translateIntTy tagW tagS) (intWidth_byteSize_pos tagW)
                          dsimp only [translateIntTy] at hdecN
                          rw [hdecN]; exact ⟨_, rfl⟩
                        | some v =>
                          cases checkVal_enum_elim hval.1 with
                          | intro idx hidx =>
                            cases hidx with
                            | intro hveq hidx2 =>
                              subst hveq
                              cases listGet?_some_of_lt ety.discriminants idx hidx2.2 with
                              | intro d hd =>
                                have hd' : Trusted.MirSemantics.getElem? ety.discriminants idx = some d := by
                                  rw [getElem?_eq_listGet?]; exact hd
                                dsimp only
                                rw [enumTy_beq_refl ety, nat_blt_eq_true_of_lt hidx2.2,
                                  Bool.and_true, if_true_eq_true, hd']
                                refine ⟨rfl, checkVal_scalar_mk _ _ _ (hwfTrunc _), hrel,
                                  fun _ => rfl, fun _ ov ho => ⟨ov, ho⟩, ?_⟩
                                have hdec := hval.2
                                dsimp only [translateTy, translateEnumTy, translateVal] at hdec
                                rw [hrepr, hd'] at hdec
                                dsimp only [mrDecode, MrType.size] at hdec
                                have hevalEnum : evalDiscriminantMem mrMem ptr
                                    (.branch 0 (translateIntTy tagW tagS)
                                      (buildEnumBranches ety tagW tagS ety.discriminants) .invalid) =
                                    .ok (some (discrIntOfNat ety.discrWidth ety.discrSigned d)) := by
                                  cases hlenT : Nat.beq data.length tagW.byteSize with
                                  | false => rw [hlenT, if_not_false] at hdec; cases hdec
                                  | true =>
                                    rw [hlenT, if_not_true] at hdec
                                    have hsub : byteSubslice data 0 (translateIntTy tagW tagS).size.bytes = data := by
                                      have h := byteSubslice_zero_eq data
                                      rw [Nat.eq_of_beq_eq_true hlenT] at h; exact h
                                    dsimp only [decodeDiscriminant] at hdec
                                    rw [hsub] at hdec
                                    have hload := allocLiveAt_load mrMem (translateEnumTy ety) ptr id data ⟨1⟩
                                      hlive (align_one_isAligned ptr.addr)
                                    dsimp only [translateEnumTy, MrType.size] at hload
                                    rw [hrepr] at hload; dsimp only [MrType.size] at hload
                                    dsimp only [evalDiscriminantMem]
                                    rw [ptrOffsetInbounds_zero]; dsimp only
                                    have hszEq : (translateIntTy tagW tagS).size = ⟨tagW.byteSize⟩ := rfl
                                    rw [hszEq, hload]; dsimp only
                                    cases hdi : decodeInt (translateIntTy tagW tagS) data with
                                    | none => rw [hdi] at hdec; cases hdec
                                    | some tv =>
                                      rw [hdi] at hdec; dsimp only at hdec; dsimp only
                                      rw [evalDiscrBranchesMem_buildEnum mrMem ptr data tv ety tagW tagS
                                        ety.discriminants]
                                      cases hd1 : decodeDiscrBranches data tv
                                          (buildEnumBranches ety tagW tagS ety.discriminants) with
                                      | none => rw [hd1] at hdec; dsimp only at hdec; cases hdec
                                      | some optD =>
                                        cases optD with
                                        | none => rw [hd1] at hdec; dsimp only at hdec; cases hdec
                                        | some d' =>
                                          rw [hd1] at hdec; dsimp only at hdec; dsimp only
                                          cases hv' : mrDecodeEnumVariant d'
                                              (buildEnumVariants ety tagW tagS ety.discriminants) data with
                                          | none => rw [hv'] at hdec; cases hdec
                                          | some vv =>
                                            rw [hv'] at hdec; dsimp only at hdec
                                            injection hdec with hvEq; injection hvEq with hdEq; rw [hdEq]
                                dsimp only [evalValue, evalPlace]
                                rw [hmrLoc, hmap]; dsimp only [translateTy, translateEnumTy]
                                rw [hrepr]; dsimp only; rw [if_not_true]
                                rw [hevalEnum]; rfl
                  | _ => cases hadm
  | useRetag _ | ref _ _ | addressOf _ _ | fakeAddressOf _
  | aggregateTuple _ | aggregateArray _ _ | repeat_ _ _ _
  | aggregateRange _ _ _ | aggregateRangeTo _ _ | aggregateRangeFrom _ _
  | aggregateOption _ _ _ | unsupported => cases hadm

end Anneal.MiniRust
