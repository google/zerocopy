-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.SimpLemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Int.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.InitLemmas
public import Anneal.BitVec
public import Anneal.BitVecArith
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.PureLift.BvLin
public import Anneal.MirSymExec

public section

namespace Anneal.MirSymExec

open Trusted.MirAst Trusted.MirSemantics Anneal.InitLemmas Anneal.MirWp
open Anneal.MirTotal Anneal.PureLift.BvLin

/-!
# Bit-Level Symbolic Predicate Companion (`Anneal.MirSymExec.Bits`)

Pass-1-portable bit-source symbolic checker over `SymScalar` (`0`
`Classical.choice`, `0` `._unsafe_rec`; definitions are `noncomputable` only
to suppress compiler `._unsafe_rec` auxiliaries), separated from
`Anneal.MirSymExec` so the core symbolic executor keeps its strict
`["propext"]`-only axiom ceiling while bit-level proofs (`BitSrc`,
`SymScalar.bitsAre`, `SymScalar.wordBitsAre`) reuse `Anneal.BitVec`
(`["propext", "Quot.sound"]`).
-/

/-- Expected symbolic origin of a single bit in a `SymScalar`. -/
inductive BitSrc where
  | zero
  | one
  | varBit (id idx : Nat)

/-- Shorthand for bit `idx` of symbolic argument `0`. -/
abbrev BitSrc.input (idx : Nat) : BitSrc := .varBit 0 idx

/-- Total boolean equality on `BitSrc`. -/
@[expose] noncomputable def BitSrc.beq : BitSrc → BitSrc → Bool
  | .zero, .zero => true
  | .one, .one => true
  | .varBit i1 k1, .varBit i2 k2 => Nat.beq i1 i2 && Nat.beq k1 k2
  | _, _ => false

theorem BitSrc.eq_of_beq : ∀ {a b : BitSrc}, a.beq b = true → a = b
  | .zero, .zero, _ => rfl
  | .one, .one, _ => rfl
  | .varBit i1 k1, .varBit i2 k2, h => by
    dsimp only [BitSrc.beq] at h
    have hi := nat_eq_of_beq (bool_and_left h)
    have hk := nat_eq_of_beq (bool_and_right h)
    rw [hi, hk]
  | .zero, .one, h | .zero, .varBit _ _, h
  | .one, .zero, h | .one, .varBit _ _, h
  | .varBit _ _, .zero, h | .varBit _ _, .one, h => by cases h

/-- Bit `b` agrees with symbolic origin `src` under valuation `env`. -/
@[expose] noncomputable def BitSrc.Agrees (env : SymEnv) : BitSrc → Bool → Prop
  | .zero, b => b = false
  | .one, b => b = true
  | .varBit id idx, b =>
    b = match env id with
        | .scalar sv => Anneal.BitVec.getLsbD sv.bits idx
        | _ => false

/-- Convenience valuation binding symbolic variable `0` to a `BitVec 64`. -/
@[expose] noncomputable def wordEnv (x : BitVec 64) : SymEnv :=
  fun _ => .scalar ⟨.i64, false, BitVec.ofNat 128 x.toNat⟩

theorem bitSrc_agrees_wordEnv (x : BitVec 64) (i : Nat) (b : Bool) :
    (BitSrc.input i).Agrees (wordEnv x) b ↔
      (i < 64 → b = Anneal.BitVec.getLsbD x i) ∧ (64 ≤ i → b = false) := by
  dsimp only [BitSrc.Agrees, BitSrc.input, wordEnv]
  have hEq : BitVec.ofNat 128 x.toNat = BitVec.setWidth 128 x := by
    refine bv_eq_of_toNat_eq ?_
    rw [Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_setWidth]
  rw [hEq, Anneal.BitVec.getLsbD_setWidth]
  cases hi64 : Nat.decLt i 64 with
  | isTrue hLt =>
    have hLt128 : i < 128 := Nat.lt_trans hLt (by decide)
    rw [decide_eq_true hLt128, Bool.true_and]
    exact ⟨fun hb => ⟨fun _ => hb, fun hGe => False.elim (Nat.not_le_of_gt hLt hGe)⟩,
      fun h => h.1 hLt⟩
  | isFalse hGe =>
    have hGe' : 64 ≤ i := Nat.le_of_not_lt hGe
    rw [Anneal.BitVec.getLsbD_ge x hGe', Bool.and_false]
    exact ⟨fun hb => ⟨fun hLt => False.elim (hGe hLt), fun _ => hb⟩,
      fun h => h.2 hGe'⟩

theorem bitSrc_input_wordEnv (x : BitVec 64) (i : Nat) (b : Bool) :
    (BitSrc.input i).Agrees (wordEnv x) b ↔ b = Anneal.BitVec.getLsbD x i := by
  have h := bitSrc_agrees_wordEnv x i b
  cases hi : Nat.decLt i 64 with
  | isTrue hLt =>
    exact ⟨fun ha => (h.mp ha).1 hLt,
      fun hb => h.mpr ⟨fun _ => hb, fun hGe => False.elim (Nat.not_le_of_gt hLt hGe)⟩⟩
  | isFalse hGe =>
    have hGe' : 64 ≤ i := Nat.le_of_not_lt hGe
    rw [Anneal.BitVec.getLsbD_ge x hGe']
    exact ⟨fun ha => (h.mp ha).2 hGe',
      fun hb => h.mpr ⟨fun hLt => False.elim (hGe hLt), fun _ => hb⟩⟩

private theorem natBlt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases Nat.lt_or_ge a b with
  | inl hLt =>
    have hBlt : Nat.blt a b = true := (Iff.of_eq Nat.blt_eq).mpr hLt
    rw [hBlt]
    exact Eq.symm (decide_eq_true hLt)
  | inr hGe =>
    cases hb : Nat.blt a b with
    | false => exact Eq.symm (decide_eq_false (Nat.not_lt_of_ge hGe))
    | true => exact False.elim (Nat.not_lt_of_ge hGe ((Iff.of_eq Nat.blt_eq).mp hb))

private theorem intWidthModulus_eq_pow (w : IntWidth) :
    intWidthModulus w = Nat.pow 2 w.bitWidth := by
  cases w <;> rfl

private theorem intWidth_bitWidth_le_128 (w : IntWidth) : w.bitWidth ≤ 128 := by
  cases w <;> decide

private theorem two_pow_bitWidth_le_128 (w : IntWidth) :
    Nat.pow 2 w.bitWidth ≤ Nat.pow 2 128 := by
  cases w <;> decide

private theorem getLsbD_truncateBitsComp (w : IntWidth) (x : BitVec 128) (i : Nat) :
    Anneal.BitVec.getLsbD (truncateBitsComp w x) i =
      (decide (i < 128) && (decide (i < w.bitWidth) && Anneal.BitVec.getLsbD x i)) := by
  have hEq : truncateBitsComp w x =
      BitVec.setWidth 128 (BitVec.setWidth w.bitWidth x) := by
    rw [truncateBitsComp_eq]
    refine bv_eq_of_toNat_eq ?_
    rw [toNat_truncateBits, intWidthModulus_eq_pow,
      Anneal.BitVec.toNat_setWidth 128 (BitVec.setWidth w.bitWidth x),
      Anneal.BitVec.toNat_setWidth w.bitWidth x]
    have hLt : Nat.mod x.toNat (Nat.pow 2 w.bitWidth) < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (nat_two_pow_pos w.bitWidth))
        (two_pow_bitWidth_le_128 w)
    exact Eq.symm (nat_mod_eq_of_lt hLt)
  rw [hEq, Anneal.BitVec.getLsbD_setWidth, Anneal.BitVec.getLsbD_setWidth]

private theorem bnot_true : (!true) = false := rfl

private theorem bool_false_bne (b : Bool) : (false != b) = b := by cases b <;> rfl

private theorem bool_bne_false (b : Bool) : (b != false) = b := by cases b <;> rfl

private theorem bool_bne_self (b : Bool) : (b != b) = false := by cases b <;> rfl

private theorem ite_true_bool {α : Type} (t e : α) :
    (if true = true then t else e) = t :=
  ite_prop_true rfl

private theorem ite_false_bool {α : Type} (t e : α) :
    (if false = true then t else e) = e :=
  ite_prop_false (by decide)

private theorem intWidth_pow128_factor (w : IntWidth) :
    ∃ k : Nat, Nat.pow 2 128 = Nat.pow 2 w.bitWidth * k := by
  cases w with
  | i8 => exact ⟨Nat.pow 2 120, by decide⟩
  | i16 => exact ⟨Nat.pow 2 112, by decide⟩
  | i32 => exact ⟨Nat.pow 2 96, by decide⟩
  | i64 | isize => exact ⟨Nat.pow 2 64, by decide⟩
  | i128 => exact ⟨1, by decide⟩

private theorem nat_mod_mod_of_mul {n a b : Nat} :
    Nat.mod (Nat.mod n (a * b)) a = Nat.mod n a := by
  have hDm : (a * b) * Nat.div n (a * b) + Nat.mod n (a * b) = n :=
    Nat.div_add_mod n (a * b)
  have hEq : n = a * (b * Nat.div n (a * b)) + Nat.mod n (a * b) := by
    rw [← Nat.mul_assoc, hDm]
  have h1 : Nat.mod (a * (b * Nat.div n (a * b)) + Nat.mod n (a * b)) a =
      Nat.mod (Nat.mod n (a * b)) a := Nat.mul_add_mod_self_left a _ _
  rw [← hEq] at h1
  exact h1.symm

/-- Unsigned `truncateScalar` never faults and stores the truncated bits. -/
private theorem truncateScalar_unsigned_eq (w : IntWidth) (x : Int) :
    truncateScalar w false x =
      .ok (⟨w, false, truncateBits w (Trusted.MirSemantics.bvOfInt 128 x)⟩,
        truncateBits w (Trusted.MirSemantics.bvOfInt 128 x) !=
          Trusted.MirSemantics.bvOfInt 128 x) :=
  rfl

/-- Truncating a nonnegative integer keeps its low `w.bitWidth` bits. -/
private theorem toNat_truncateBits_mirBvOfInt_ofNat (w : IntWidth) (m : Nat) :
    (truncateBits w (Trusted.MirSemantics.bvOfInt 128 (Int.ofNat m))).toNat =
      Nat.mod m (Nat.pow 2 w.bitWidth) := by
  rw [toNat_truncateBits, intWidthModulus_eq_pow]
  have hB : (Trusted.MirSemantics.bvOfInt 128 (Int.ofNat m)).toNat =
      Nat.mod m (Nat.pow 2 128) := by
    change (BitVec.ofNat 128 (Nat.mod m (Nat.pow 2 128))).toNat = _
    rw [Anneal.BitVec.toNat_ofNat]
    exact nat_mod_eq_of_lt (Nat.mod_lt _ (nat_two_pow_pos 128))
  rw [hB]
  let ⟨k, hK⟩ := intWidth_pow128_factor w
  rw [hK]
  exact nat_mod_mod_of_mul

/-- Constant-fold a closed `SymScalar` expression. -/
@[expose] noncomputable def SymScalar.asConst? : SymScalar → Option ScalarVal
  | .lit sv => some ⟨sv.width, sv.signed, truncateBitsComp sv.width sv.bits⟩
  | .var _ _ _ => none
  | .unOp op arg =>
    match arg.asConst? with
    | some av =>
      match evalUnOpComp op (.scalar av) with
      | .ok (.scalar sv) => some sv
      | _ => none
    | none => none
  | .binOp op l r =>
    match l.asConst?, r.asConst? with
    | some lv, some rv =>
      match evalBinOpComp op (.scalar lv) (.scalar rv) with
      | .ok (.scalar sv) => some sv
      | _ => none
    | _, _ => none
  | .shift op l r =>
    match l.asConst?, r.asConst? with
    | some lv, some rv =>
      match evalBinOpComp op (.scalar lv) (.scalar rv) with
      | .ok (.scalar sv) => some sv
      | _ => none
    | _, _ => none
  | .cast dstW dstS src =>
    match src.asConst? with
    | some sv =>
      match evalIntToIntCastComp (.scalar sv) (.int dstW dstS) with
      | .ok (.scalar sv') => some sv'
      | _ => none
    | none => none

theorem symScalar_asConst?_sound (env : SymEnv) :
    ∀ (s : SymScalar) (sv : ScalarVal),
      s.asConst? = some sv → s.eval env = sv
  | .lit sv, out, h => by
    dsimp only [SymScalar.asConst?, SymScalar.eval] at h
    dsimp only [SymScalar.asConst?, SymScalar.eval]
    cases h
    rfl
  | .var _ _ _, _, h => by cases h
  | .unOp op arg, out, h => by
    dsimp only [SymScalar.asConst?, SymScalar.eval] at h
    dsimp only [SymScalar.asConst?, SymScalar.eval]
    cases ha : arg.asConst? with
    | none => rw [ha] at h; cases h
    | some av =>
      rw [ha] at h
      dsimp only at h
      rw [symScalar_asConst?_sound env arg av ha]
      cases he : evalUnOpComp op (.scalar av) with
      | error _ => rw [he] at h; cases h
      | ok v =>
        rw [he] at h
        cases v with
        | scalar sv => cases h; rfl
        | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
        | tuple _ | bytes _ | rangeTo _ | rangeFrom _ => cases h
  | .binOp op l r, out, h => by
    dsimp only [SymScalar.asConst?, SymScalar.eval] at h
    dsimp only [SymScalar.asConst?, SymScalar.eval]
    cases hl : l.asConst? with
    | none => rw [hl] at h; cases h
    | some lv =>
      cases hr : r.asConst? with
      | none => rw [hl, hr] at h; cases h
      | some rv =>
        rw [hl, hr] at h
        dsimp only at h
        rw [symScalar_asConst?_sound env l lv hl,
          symScalar_asConst?_sound env r rv hr]
        cases he : evalBinOpComp op (.scalar lv) (.scalar rv) with
        | error _ => rw [he] at h; cases h
        | ok v =>
          rw [he] at h
          cases v with
          | scalar sv => cases h; rfl
          | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
          | tuple _ | bytes _ | rangeTo _ | rangeFrom _ => cases h
  | .shift op l r, out, h => by
    dsimp only [SymScalar.asConst?, SymScalar.eval] at h
    dsimp only [SymScalar.asConst?, SymScalar.eval]
    cases hl : l.asConst? with
    | none => rw [hl] at h; cases h
    | some lv =>
      cases hr : r.asConst? with
      | none => rw [hl, hr] at h; cases h
      | some rv =>
        rw [hl, hr] at h
        dsimp only at h
        rw [symScalar_asConst?_sound env l lv hl,
          symScalar_asConst?_sound env r rv hr]
        cases he : evalBinOpComp op (.scalar lv) (.scalar rv) with
        | error _ => rw [he] at h; cases h
        | ok v =>
          rw [he] at h
          cases v with
          | scalar sv => cases h; rfl
          | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
          | tuple _ | bytes _ | rangeTo _ | rangeFrom _ => cases h
  | .cast dstW dstS src, out, h => by
    dsimp only [SymScalar.asConst?, SymScalar.eval] at h
    dsimp only [SymScalar.asConst?, SymScalar.eval]
    cases hs : src.asConst? with
    | none => rw [hs] at h; cases h
    | some sv =>
      rw [hs] at h
      dsimp only at h
      rw [symScalar_asConst?_sound env src sv hs]
      cases he : evalIntToIntCastComp (.scalar sv) (.int dstW dstS) with
      | error _ => rw [he] at h; cases h
      | ok v =>
        rw [he] at h
        cases v with
        | scalar sv' => cases h; rfl
        | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
        | tuple _ | bytes _ | rangeTo _ | rangeFrom _ => cases h

/-- Compute the symbolic source of bit `i` of `s` (when `0 ≤ i < 128`). -/
@[expose] noncomputable def SymScalar.bitLsb (s : SymScalar) (i : Nat) : Option BitSrc :=
  match s with
  | .lit sv =>
    if Nat.blt i (bitWidthComp sv.width) && Anneal.BitVec.getLsbD sv.bits i then
      some .one
    else
      some .zero
  | .var id w _ =>
    if Nat.blt i (bitWidthComp w) then some (.varBit id i) else some .zero
  | .unOp _ _ => none
  | .binOp .bitAnd l r =>
    if !(intWidthBeqComp l.width r.width && boolBeqComp l.signed r.signed) then none
    else if !Nat.blt i (bitWidthComp l.width) then some .zero
    else
      match SymScalar.bitLsb l i, SymScalar.bitLsb r i with
      | some .zero, _ => some .zero
      | _, some .zero => some .zero
      | some .one, some rb => some rb
      | some lb, some .one => some lb
      | some (.varBit i1 k1), some (.varBit i2 k2) =>
        if Nat.beq i1 i2 && Nat.beq k1 k2 then some (.varBit i1 k1) else none
      | _, _ => none
  | .binOp .bitOr l r =>
    if !(intWidthBeqComp l.width r.width && boolBeqComp l.signed r.signed) then none
    else if !Nat.blt i (bitWidthComp l.width) then some .zero
    else
      match SymScalar.bitLsb l i, SymScalar.bitLsb r i with
      | some .one, _ => some .one
      | _, some .one => some .one
      | some .zero, some rb => some rb
      | some lb, some .zero => some lb
      | some (.varBit i1 k1), some (.varBit i2 k2) =>
        if Nat.beq i1 i2 && Nat.beq k1 k2 then some (.varBit i1 k1) else none
      | _, _ => none
  | .binOp .bitXor l r =>
    if !(intWidthBeqComp l.width r.width && boolBeqComp l.signed r.signed) then none
    else if !Nat.blt i (bitWidthComp l.width) then some .zero
    else
      match SymScalar.bitLsb l i, SymScalar.bitLsb r i with
      | some .zero, some rb => some rb
      | some lb, some .zero => some lb
      | some .one, some .one => some .zero
      | some (.varBit i1 k1), some (.varBit i2 k2) =>
        if Nat.beq i1 i2 && Nat.beq k1 k2 then some .zero else none
      | _, _ => none
  | .binOp _ _ _ => none
  | .shift .shl l r =>
    if l.signed then none
    else
      match r.asConst? with
      | none => none
      | some rsv =>
        let amt := (intEmodComp (decodeScalarComp rsv) (Int.ofNat (bitWidthComp l.width))).toNat
        if Nat.blt i (bitWidthComp l.width) then
          if Nat.blt i amt then some .zero else SymScalar.bitLsb l (i - amt)
        else some .zero
  | .shift .shr l r =>
    if l.signed then none
    else
      match r.asConst? with
      | none => none
      | some rsv =>
        let amt := (intEmodComp (decodeScalarComp rsv) (Int.ofNat (bitWidthComp l.width))).toNat
        if Nat.blt i (bitWidthComp l.width) then
          if Nat.blt (i + amt) (bitWidthComp l.width) then SymScalar.bitLsb l (i + amt) else some .zero
        else some .zero
  | .shift _ _ _ => none
  | .cast dstW _ src =>
    if src.signed then none
    else if Nat.blt i (bitWidthComp dstW) then
      if Nat.blt i (bitWidthComp src.width) then SymScalar.bitLsb src i else some .zero
    else some .zero

private theorem bitSrc_agrees_det {env : SymEnv} {src : BitSrc} {b1 b2 : Bool}
    (h1 : src.Agrees env b1) (h2 : src.Agrees env b2) : b1 = b2 := by
  cases src with
  | zero => exact h1.trans h2.symm
  | one => exact h1.trans h2.symm
  | varBit _ _ => exact h1.trans h2.symm

private theorem bvAndComp_eq (x y : BitVec 128) :
    bvAndComp x y = Anneal.BitVec.and x y := by
  refine bv_eq_of_toNat_eq ?_
  dsimp only [bvAndComp]
  rw [Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_and]
  exact nat_mod_eq_of_lt (Anneal.NatBitwise.land_lt_two_pow x.isLt y.isLt)

private theorem bvOrComp_eq (x y : BitVec 128) :
    bvOrComp x y = Anneal.BitVec.or x y := by
  refine bv_eq_of_toNat_eq ?_
  dsimp only [bvOrComp]
  rw [Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_or]
  exact nat_mod_eq_of_lt (Anneal.NatBitwise.lor_lt_two_pow x.isLt y.isLt)

private theorem bvXorComp_eq (x y : BitVec 128) :
    bvXorComp x y = Anneal.BitVec.xor x y := by
  refine bv_eq_of_toNat_eq ?_
  dsimp only [bvXorComp]
  rw [Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_xor]
  exact nat_mod_eq_of_lt (Anneal.NatBitwise.xor_lt_two_pow x.isLt y.isLt)

/-- Soundness of `SymScalar.bitLsb`: if bit `i` (`i < 128`) reduces to
`some src`, then under every `SymEnv` the `i`-th bit of `(s.eval env).bits`
agrees with `src`. -/
theorem symScalar_bitLsb_sound (env : SymEnv) :
    ∀ (s : SymScalar) (i : Nat) (src : BitSrc),
      i < 128 → s.wf = true → s.bitLsb i = some src →
      BitSrc.Agrees env src (Anneal.BitVec.getLsbD (s.eval env).bits i)
  | .lit sv, i, src, hi, _, h => by
    dsimp only [SymScalar.bitLsb, SymScalar.eval] at h
    dsimp only [SymScalar.bitLsb, SymScalar.eval]
    rw [natBlt_eq_decide, bitWidthComp_eq] at h
    rw [getLsbD_truncateBitsComp sv.width sv.bits i, decide_eq_true hi, Bool.true_and]
    cases hB : decide (i < sv.width.bitWidth) && Anneal.BitVec.getLsbD sv.bits i with
    | false =>
      rw [hB] at h; cases h; rfl
    | true =>
      rw [hB] at h; cases h; rfl
  | .var id w sg, i, src, hi, _, h => by
    dsimp only [SymScalar.bitLsb, SymScalar.eval] at h
    dsimp only [SymScalar.bitLsb, SymScalar.eval]
    rw [natBlt_eq_decide, bitWidthComp_eq] at h
    cases hLt : decide (i < w.bitWidth) with
    | false =>
      rw [hLt] at h; cases h
      dsimp only [BitSrc.Agrees]
      cases env id with
      | scalar sv =>
        rw [getLsbD_truncateBitsComp, decide_eq_true hi, hLt, Bool.false_and, Bool.true_and]
      | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
      | tuple _ | bytes _ | rangeTo _ | rangeFrom _ =>
        exact Anneal.BitVec.getLsbD_zero 128 i
    | true =>
      rw [hLt] at h; cases h
      dsimp only [BitSrc.Agrees]
      cases env id with
      | scalar sv =>
        rw [getLsbD_truncateBitsComp, decide_eq_true hi, hLt, Bool.true_and, Bool.true_and]
      | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
      | tuple _ | bytes _ | rangeTo _ | rangeFrom _ =>
        exact Anneal.BitVec.getLsbD_zero 128 i
  | .unOp _ _, _, _, _, _, h => by cases h
  | .binOp op l r, i, src, hi, hWf, h => by
    have hWf1 := bool_and_left hWf
    have hWf2 := bool_and_left hWf1
    have hWf3 := bool_and_left hWf2
    have hWfL := bool_and_left hWf3
    have hWfR := bool_and_right hWf3
    have hL := symScalar_eval_meta env l hWfL
    have hR := symScalar_eval_meta env r hWfR
    have hTrL : truncateBitsComp l.width (l.eval env).bits = (l.eval env).bits := by
      rw [truncateBitsComp_eq, ← hL.1]
      exact beq_iff_eq.mp hL.2.2
    have hTrR : truncateBitsComp r.width (r.eval env).bits = (r.eval env).bits := by
      rw [truncateBitsComp_eq, ← hR.1]
      exact beq_iff_eq.mp hR.2.2
    cases op with
    | bitAnd =>
      dsimp only [SymScalar.bitLsb] at h
      cases hTy : intWidthBeqComp l.width r.width && boolBeqComp l.signed r.signed with
      | false => rw [hTy] at h; cases h
      | true =>
        rw [hTy] at h
        dsimp only [SymScalar.eval, evalBinOpComp]
        have hNotShift : binOpIsShiftComp .bitAnd = false := rfl
        have hSame : (!(intWidthBeqComp (l.eval env).width (r.eval env).width &&
            boolBeqComp (l.eval env).signed (r.eval env).signed)) = false := by
          rw [hL.1, hR.1, hL.2.1, hR.2.1]
          exact congrArg Bool.not hTy
        rw [natBlt_eq_decide, bitWidthComp_eq] at h
        rw [hNotShift, hSame, ite_false_bool, ite_false_bool]
        dsimp only
        rw [hL.1, hR.1, hTrL, hTrR, bvAndComp_eq,
          getLsbD_truncateBitsComp, Anneal.BitVec.getLsbD_and, decide_eq_true hi,
          Bool.true_and]
        cases hLt : decide (i < l.width.bitWidth) with
        | false =>
          rw [hLt] at h; cases h; rfl
        | true =>
          rw [hLt, bnot_true, ite_false_bool, ite_false_bool] at h
          rw [Bool.true_and]
          cases hLb : l.bitLsb i with
          | none =>
            rw [hLb] at h
            cases hRb : r.bitLsb i with
            | none => rw [hRb] at h; cases h
            | some rb =>
              cases rb with
              | zero =>
                rw [hRb] at h; cases h
                have hAg := symScalar_bitLsb_sound env r i .zero hi hWfR hRb
                dsimp only [BitSrc.Agrees] at hAg
                dsimp only [BitSrc.Agrees]
                rw [hAg, Bool.and_false]
              | one | varBit _ _ => rw [hRb] at h; cases h
          | some lb =>
            cases lb with
            | zero =>
              rw [hLb] at h; cases h
              have hAg := symScalar_bitLsb_sound env l i .zero hi hWfL hLb
              dsimp only [BitSrc.Agrees] at hAg
              dsimp only [BitSrc.Agrees]
              rw [hAg, Bool.false_and]
            | one =>
              rw [hLb] at h
              have hAgL := symScalar_bitLsb_sound env l i .one hi hWfL hLb
              dsimp only [BitSrc.Agrees] at hAgL
              rw [hAgL, Bool.true_and]
              cases hRb : r.bitLsb i with
              | none => rw [hRb] at h; cases h
              | some rb =>
                rw [hRb] at h
                cases rb with
                | zero => cases h; exact (symScalar_bitLsb_sound env r i .zero hi hWfR hRb)
                | one => cases h; exact (symScalar_bitLsb_sound env r i .one hi hWfR hRb)
                | varBit id2 k2 =>
                  cases h
                  exact symScalar_bitLsb_sound env r i (.varBit id2 k2) hi hWfR hRb
            | varBit id1 k1 =>
              rw [hLb] at h
              have hAgL := symScalar_bitLsb_sound env l i (.varBit id1 k1) hi hWfL hLb
              cases hRb : r.bitLsb i with
              | none => rw [hRb] at h; cases h
              | some rb =>
                rw [hRb] at h
                have hAgR := symScalar_bitLsb_sound env r i rb hi hWfR hRb
                cases rb with
                | zero =>
                  cases h
                  dsimp only [BitSrc.Agrees] at hAgR
                  dsimp only [BitSrc.Agrees]
                  rw [hAgR, Bool.and_false]
                | one =>
                  cases h
                  dsimp only [BitSrc.Agrees] at hAgR
                  dsimp only [BitSrc.Agrees]
                  rw [hAgR, Bool.and_true]
                  exact hAgL
                | varBit id2 k2 =>
                  dsimp only at h
                  cases hEq : Nat.beq id1 id2 && Nat.beq k1 k2 with
                  | false => rw [hEq] at h; cases h
                  | true =>
                    rw [hEq] at h; cases h
                    have hi12 := nat_eq_of_beq (bool_and_left hEq)
                    have hk12 := nat_eq_of_beq (bool_and_right hEq)
                    rw [← hi12, ← hk12] at hAgR
                    have hSameB := bitSrc_agrees_det hAgL hAgR
                    rw [← hSameB, Bool.and_self]
                    exact hAgL
    | bitOr =>
      dsimp only [SymScalar.bitLsb] at h
      cases hTy : intWidthBeqComp l.width r.width && boolBeqComp l.signed r.signed with
      | false => rw [hTy] at h; cases h
      | true =>
        rw [hTy] at h
        dsimp only [SymScalar.eval, evalBinOpComp]
        have hNotShift : binOpIsShiftComp .bitOr = false := rfl
        have hSame : (!(intWidthBeqComp (l.eval env).width (r.eval env).width &&
            boolBeqComp (l.eval env).signed (r.eval env).signed)) = false := by
          rw [hL.1, hR.1, hL.2.1, hR.2.1]
          exact congrArg Bool.not hTy
        rw [natBlt_eq_decide, bitWidthComp_eq] at h
        rw [hNotShift, hSame, ite_false_bool, ite_false_bool]
        dsimp only
        rw [hL.1, hR.1, hTrL, hTrR, bvOrComp_eq,
          getLsbD_truncateBitsComp, Anneal.BitVec.getLsbD_or, decide_eq_true hi,
          Bool.true_and]
        cases hLt : decide (i < l.width.bitWidth) with
        | false => rw [hLt] at h; cases h; rfl
        | true =>
          rw [hLt, bnot_true, ite_false_bool, ite_false_bool] at h
          rw [Bool.true_and]
          cases hLb : l.bitLsb i with
          | none =>
            rw [hLb] at h
            cases hRb : r.bitLsb i with
            | none => rw [hRb] at h; cases h
            | some rb =>
              cases rb with
              | one =>
                rw [hRb] at h; cases h
                have hAg := symScalar_bitLsb_sound env r i .one hi hWfR hRb
                dsimp only [BitSrc.Agrees] at hAg
                dsimp only [BitSrc.Agrees]
                rw [hAg, Bool.or_true]
              | zero | varBit _ _ => rw [hRb] at h; cases h
          | some lb =>
            cases lb with
            | one =>
              rw [hLb] at h; cases h
              have hAg := symScalar_bitLsb_sound env l i .one hi hWfL hLb
              dsimp only [BitSrc.Agrees] at hAg
              dsimp only [BitSrc.Agrees]
              rw [hAg, Bool.true_or]
            | zero =>
              rw [hLb] at h
              have hAgL := symScalar_bitLsb_sound env l i .zero hi hWfL hLb
              dsimp only [BitSrc.Agrees] at hAgL
              rw [hAgL, Bool.false_or]
              cases hRb : r.bitLsb i with
              | none => rw [hRb] at h; cases h
              | some rb =>
                rw [hRb] at h
                cases rb with
                | zero => cases h; exact (symScalar_bitLsb_sound env r i .zero hi hWfR hRb)
                | one => cases h; exact (symScalar_bitLsb_sound env r i .one hi hWfR hRb)
                | varBit id2 k2 =>
                  cases h
                  exact symScalar_bitLsb_sound env r i (.varBit id2 k2) hi hWfR hRb
            | varBit id1 k1 =>
              rw [hLb] at h
              have hAgL := symScalar_bitLsb_sound env l i (.varBit id1 k1) hi hWfL hLb
              cases hRb : r.bitLsb i with
              | none => rw [hRb] at h; cases h
              | some rb =>
                rw [hRb] at h
                have hAgR := symScalar_bitLsb_sound env r i rb hi hWfR hRb
                cases rb with
                | one =>
                  cases h
                  dsimp only [BitSrc.Agrees] at hAgR
                  dsimp only [BitSrc.Agrees]
                  rw [hAgR, Bool.or_true]
                | zero =>
                  cases h
                  dsimp only [BitSrc.Agrees] at hAgR
                  dsimp only [BitSrc.Agrees]
                  rw [hAgR, Bool.or_false]
                  exact hAgL
                | varBit id2 k2 =>
                  dsimp only at h
                  cases hEq : Nat.beq id1 id2 && Nat.beq k1 k2 with
                  | false => rw [hEq] at h; cases h
                  | true =>
                    rw [hEq] at h; cases h
                    have hi12 := nat_eq_of_beq (bool_and_left hEq)
                    have hk12 := nat_eq_of_beq (bool_and_right hEq)
                    rw [← hi12, ← hk12] at hAgR
                    have hSameB := bitSrc_agrees_det hAgL hAgR
                    rw [← hSameB, Bool.or_self]
                    exact hAgL
    | bitXor =>
      dsimp only [SymScalar.bitLsb] at h
      cases hTy : intWidthBeqComp l.width r.width && boolBeqComp l.signed r.signed with
      | false => rw [hTy] at h; cases h
      | true =>
        rw [hTy] at h
        dsimp only [SymScalar.eval, evalBinOpComp]
        have hNotShift : binOpIsShiftComp .bitXor = false := rfl
        have hSame : (!(intWidthBeqComp (l.eval env).width (r.eval env).width &&
            boolBeqComp (l.eval env).signed (r.eval env).signed)) = false := by
          rw [hL.1, hR.1, hL.2.1, hR.2.1]
          exact congrArg Bool.not hTy
        rw [natBlt_eq_decide, bitWidthComp_eq] at h
        rw [hNotShift, hSame, ite_false_bool, ite_false_bool]
        dsimp only
        rw [hL.1, hR.1, hTrL, hTrR, bvXorComp_eq,
          getLsbD_truncateBitsComp, Anneal.BitVec.getLsbD_xor, decide_eq_true hi,
          Bool.true_and]
        cases hLt : decide (i < l.width.bitWidth) with
        | false => rw [hLt] at h; cases h; rfl
        | true =>
          rw [hLt, bnot_true, ite_false_bool, ite_false_bool] at h
          rw [Bool.true_and]
          cases hLb : l.bitLsb i with
          | none => rw [hLb] at h; cases h
          | some lb =>
            cases hRb : r.bitLsb i with
            | none => rw [hLb, hRb] at h; cases lb <;> cases h
            | some rb =>
              rw [hLb, hRb] at h
              have hAgL := symScalar_bitLsb_sound env l i lb hi hWfL hLb
              have hAgR := symScalar_bitLsb_sound env r i rb hi hWfR hRb
              cases lb with
              | zero =>
                cases h
                dsimp only [BitSrc.Agrees] at hAgL
                rw [hAgL, bool_false_bne]
                exact hAgR
              | one =>
                cases rb with
                | zero =>
                  cases h
                  dsimp only [BitSrc.Agrees] at hAgR
                  dsimp only [BitSrc.Agrees]
                  rw [hAgR, bool_bne_false]
                  exact hAgL
                | one =>
                  cases h
                  dsimp only [BitSrc.Agrees] at hAgL hAgR
                  dsimp only [BitSrc.Agrees]
                  rw [hAgL, hAgR]
                  rfl
                | varBit _ _ => cases h
              | varBit id1 k1 =>
                cases rb with
                | zero =>
                  cases h
                  dsimp only [BitSrc.Agrees] at hAgR
                  dsimp only [BitSrc.Agrees]
                  rw [hAgR, bool_bne_false]
                  exact hAgL
                | one => cases h
                | varBit id2 k2 =>
                  dsimp only at h
                  cases hEq : Nat.beq id1 id2 && Nat.beq k1 k2 with
                  | false => rw [hEq] at h; cases h
                  | true =>
                    rw [hEq] at h; cases h
                    have hi12 := nat_eq_of_beq (bool_and_left hEq)
                    have hk12 := nat_eq_of_beq (bool_and_right hEq)
                    rw [← hi12, ← hk12] at hAgR
                    have hSameB := bitSrc_agrees_det hAgL hAgR
                    dsimp only [BitSrc.Agrees]
                    rw [← hSameB, bool_bne_self]
    | add | sub | mul | div | rem
    | addUnchecked | subUnchecked | mulUnchecked
    | addWithOverflow | subWithOverflow | mulWithOverflow
    | shl | shr | shlUnchecked | shrUnchecked
    | eq | lt | le | ne | ge | gt | cmp | offset => cases h
  | .shift op l r, i, src, hi, hWf, h => by
    have hWf1 := bool_and_left hWf
    have hWfL := bool_and_left hWf1
    have hL := symScalar_eval_meta env l hWfL
    have hTrL : truncateBitsComp (l.eval env).width (l.eval env).bits =
        (l.eval env).bits := by
      rw [truncateBitsComp_eq]
      exact beq_iff_eq.mp hL.2.2
    have hBitsLt : (l.eval env).bits.toNat < Nat.pow 2 l.width.bitWidth := by
      rw [← hTrL, truncateBitsComp_eq, toNat_truncateBits, intWidthModulus_eq_pow, hL.1]
      exact Nat.mod_lt _ (nat_two_pow_pos l.width.bitWidth)
    cases op with
    | shl =>
      dsimp only [SymScalar.bitLsb] at h
      cases hSig : l.signed with
      | true => rw [hSig] at h; cases h
      | false =>
        rw [hSig] at h
        cases hr : r.asConst? with
        | none => rw [hr] at h; cases h
        | some rsv =>
          rw [hr, natBlt_eq_decide, bitWidthComp_eq] at h
          dsimp only at h
          have hRConst := symScalar_asConst?_sound env r rsv hr
          have hLSig : (l.eval env).signed = false := hL.2.1.trans hSig
          let amt := (intEmodComp (decodeScalarComp rsv) (Int.ofNat l.width.bitWidth)).toNat
          have hDecL : decodeScalar (l.eval env) = Int.ofNat (l.eval env).bits.toNat := by
            dsimp only [decodeScalar]
            rw [hLSig, ← truncateBitsComp_eq, hTrL]
            rfl
          have hBitsEq :
              truncateBits l.width (Trusted.MirSemantics.bvOfInt 128
                  (intShiftLeft (Int.ofNat (l.eval env).bits.toNat) amt)) =
                BitVec.setWidth 128
                  (BitVec.shl (BitVec.setWidth l.width.bitWidth (l.eval env).bits) amt) := by
            refine bv_eq_of_toNat_eq ?_
            change (truncateBits l.width (Trusted.MirSemantics.bvOfInt 128
                (Int.ofNat (Nat.shiftLeft (l.eval env).bits.toNat amt)))).toNat = _
            rw [toNat_truncateBits_mirBvOfInt_ofNat, Anneal.BitVec.toNat_setWidth 128,
              Anneal.BitVec.toNat_shl, Anneal.BitVec.toNat_setWidth l.width.bitWidth,
              nat_mod_eq_of_lt hBitsLt]
            exact (nat_mod_eq_of_lt (Nat.lt_of_lt_of_le
              (Nat.mod_lt _ (nat_two_pow_pos l.width.bitWidth))
              (two_pow_bitWidth_le_128 l.width))).symm
          have hResEq :
              (evalBinOp .shl (.scalar (l.eval env)) (.scalar rsv)) =
                .ok (.scalar ⟨l.width, false,
                  BitVec.setWidth 128
                    (BitVec.shl
                      (BitVec.setWidth l.width.bitWidth (l.eval env).bits) amt)⟩) := by
            have hShift : BinOp.shl.isShift = true := rfl
            dsimp only [evalBinOp]
            rw [hShift, ite_true_bool]
            dsimp only [evalShiftOp]
            rw [hDecL, hL.1, hLSig, ← decodeScalarComp_eq, ← intEmodComp_eq,
              truncateScalar_unsigned_eq, hBitsEq]
            cases (intEmodComp (decodeScalarComp rsv) (Int.ofNat l.width.bitWidth) !=
              decodeScalarComp rsv) <;> rfl
          dsimp only [SymScalar.eval]
          rw [evalBinOpComp_eq, hRConst, hResEq]
          dsimp only
          rw [Anneal.BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
            Anneal.BitVec.getLsbD_shl, Anneal.BitVec.getLsbD_setWidth]
          cases hLtW : decide (i < l.width.bitWidth) with
          | false => rw [hLtW] at h; cases h; rfl
          | true =>
            rw [hLtW] at h
            rw [natBlt_eq_decide] at h
            cases hLtA : decide (i < amt) with
            | true =>
              rw [hLtA] at h; cases h
              have hNotGe : decide (amt ≤ i) = false :=
                decide_eq_false (Nat.not_le_of_gt (of_decide_eq_true hLtA))
              rw [hNotGe, Bool.false_and]
              rfl
            | false =>
              rw [hLtA] at h
              have hGeA : amt ≤ i := Nat.le_of_not_lt (of_decide_eq_false hLtA)
              have hSubLt : i - amt < 128 := Nat.lt_of_le_of_lt (Nat.sub_le i amt) hi
              have hLtWi : i < l.width.bitWidth := of_decide_eq_true hLtW
              have hSubLtW : i - amt < l.width.bitWidth :=
                Nat.lt_of_le_of_lt (Nat.sub_le i amt) hLtWi
              rw [decide_eq_true hGeA, decide_eq_true hSubLtW, Bool.true_and, Bool.true_and,
                Bool.true_and]
              exact symScalar_bitLsb_sound env l (i - amt) src hSubLt hWfL h
    | shr =>
      dsimp only [SymScalar.bitLsb] at h
      cases hSig : l.signed with
      | true => rw [hSig] at h; cases h
      | false =>
        rw [hSig] at h
        cases hr : r.asConst? with
        | none => rw [hr] at h; cases h
        | some rsv =>
          rw [hr, natBlt_eq_decide, bitWidthComp_eq] at h
          dsimp only at h
          have hRConst := symScalar_asConst?_sound env r rsv hr
          have hLSig : (l.eval env).signed = false := hL.2.1.trans hSig
          let amt := (intEmodComp (decodeScalarComp rsv) (Int.ofNat l.width.bitWidth)).toNat
          have hDecL : decodeScalar (l.eval env) = Int.ofNat (l.eval env).bits.toNat := by
            dsimp only [decodeScalar]
            rw [hLSig, ← truncateBitsComp_eq, hTrL]
            rfl
          have hSrLt : Nat.shiftRight (l.eval env).bits.toNat amt <
              Nat.pow 2 l.width.bitWidth := by
            have hU := (BitVec.ushr (BitVec.setWidth l.width.bitWidth (l.eval env).bits) amt).isLt
            rw [Anneal.BitVec.toNat_ushr, Anneal.BitVec.toNat_setWidth,
              nat_mod_eq_of_lt hBitsLt] at hU
            exact hU
          have hBitsEq :
              truncateBits l.width (Trusted.MirSemantics.bvOfInt 128
                  (intShiftRight (Int.ofNat (l.eval env).bits.toNat) amt)) =
                BitVec.setWidth 128
                  (BitVec.ushr (BitVec.setWidth l.width.bitWidth (l.eval env).bits) amt) := by
            refine bv_eq_of_toNat_eq ?_
            change (truncateBits l.width (Trusted.MirSemantics.bvOfInt 128
                (Int.ofNat (Nat.shiftRight (l.eval env).bits.toNat amt)))).toNat = _
            rw [toNat_truncateBits_mirBvOfInt_ofNat, Anneal.BitVec.toNat_setWidth 128,
              Anneal.BitVec.toNat_ushr, Anneal.BitVec.toNat_setWidth l.width.bitWidth,
              nat_mod_eq_of_lt hBitsLt, nat_mod_eq_of_lt hSrLt]
            exact (nat_mod_eq_of_lt (Nat.lt_of_lt_of_le hSrLt
              (two_pow_bitWidth_le_128 l.width))).symm
          have hResEq :
              (evalBinOp .shr (.scalar (l.eval env)) (.scalar rsv)) =
                .ok (.scalar ⟨l.width, false,
                  BitVec.setWidth 128
                    (BitVec.ushr
                      (BitVec.setWidth l.width.bitWidth (l.eval env).bits) amt)⟩) := by
            have hShift : BinOp.shr.isShift = true := rfl
            dsimp only [evalBinOp]
            rw [hShift, ite_true_bool]
            dsimp only [evalShiftOp]
            rw [hDecL, hL.1, hLSig, ← decodeScalarComp_eq, ← intEmodComp_eq,
              truncateScalar_unsigned_eq, hBitsEq]
            cases (intEmodComp (decodeScalarComp rsv) (Int.ofNat l.width.bitWidth) !=
              decodeScalarComp rsv) <;> rfl
          dsimp only [SymScalar.eval]
          rw [evalBinOpComp_eq, hRConst, hResEq]
          dsimp only
          rw [Anneal.BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
            Anneal.BitVec.getLsbD_ushr, Anneal.BitVec.getLsbD_setWidth]
          cases hLtW : decide (i < l.width.bitWidth) with
          | false =>
            rw [hLtW] at h; cases h
            have hNotAdd : decide (i + amt < l.width.bitWidth) = false :=
              decide_eq_false (fun hAdd =>
                (of_decide_eq_false hLtW) (Nat.lt_of_le_of_lt (Nat.le_add_right i amt) hAdd))
            rw [hNotAdd]
            rfl
          | true =>
            rw [hLtW] at h
            rw [natBlt_eq_decide] at h
            cases hLtAdd : decide (i + amt < l.width.bitWidth) with
            | false =>
              rw [hLtAdd] at h; cases h
              rfl
            | true =>
              rw [hLtAdd] at h
              have hAddLtW : i + amt < l.width.bitWidth := of_decide_eq_true hLtAdd
              have hAddLt128 : i + amt < 128 :=
                Nat.lt_of_lt_of_le hAddLtW (intWidth_bitWidth_le_128 l.width)
              rw [Bool.true_and]
              exact symScalar_bitLsb_sound env l (i + amt) src hAddLt128 hWfL h
    | add | sub | mul | div | rem
    | addUnchecked | subUnchecked | mulUnchecked
    | addWithOverflow | subWithOverflow | mulWithOverflow
    | bitAnd | bitOr | bitXor | shlUnchecked | shrUnchecked
    | eq | lt | le | ne | ge | gt | cmp | offset => cases h
  | .cast dstW dstS srcE, i, src, hi, hWf, h => by
    dsimp only [SymScalar.bitLsb] at h
    cases hSig : srcE.signed with
    | true => rw [hSig] at h; cases h
    | false =>
      rw [hSig, natBlt_eq_decide, natBlt_eq_decide, bitWidthComp_eq dstW, bitWidthComp_eq srcE.width] at h
      have hS := symScalar_eval_meta env srcE hWf
      have hSSig : (srcE.eval env).signed = false := hS.2.1.trans hSig
      dsimp only [SymScalar.eval]
      rw [evalIntToIntCastComp_eq]
      dsimp only [evalIntToIntCast, intLikeBits]
      have hTrEq : truncateBits (srcE.eval env).width (srcE.eval env).bits =
          (srcE.eval env).bits := beq_iff_eq.mp hS.2.2
      rw [hSSig, ite_false_bool]
      dsimp only
      rw [hTrEq, bv_ofNat_toNat, ← truncateBitsComp_eq, getLsbD_truncateBitsComp dstW,
        decide_eq_true hi, Bool.true_and]
      cases hLtDst : decide (i < dstW.bitWidth) with
      | false =>
        rw [hLtDst] at h; cases h; rfl
      | true =>
        rw [hLtDst] at h
        rw [Bool.true_and]
        cases hLtSrc : decide (i < srcE.width.bitWidth) with
        | false =>
          rw [hLtSrc] at h; cases h
          rw [← hTrEq, ← truncateBitsComp_eq, getLsbD_truncateBitsComp,
            decide_eq_true hi, hS.1, hLtSrc]
          rfl
        | true =>
          rw [hLtSrc] at h
          exact symScalar_bitLsb_sound env srcE i src hi hWf h

/-- `@Nat.rec` worker checking bits `0..n-1` of `s.bitLsb` against
`expected`. -/
@[expose] noncomputable def bitsAreAux (s : SymScalar) (expected : Nat → BitSrc) : Nat → Bool :=
  @Nat.rec (fun _ => Bool) true fun i ih =>
    ih &&
    match s.bitLsb i with
    | some src => BitSrc.beq src (expected i)
    | none => false

private theorem bitsAreAux_sound (s : SymScalar) (expected : Nat → BitSrc) :
    ∀ (n i : Nat), i < n → bitsAreAux s expected n = true →
      s.bitLsb i = some (expected i)
  | 0, _, hi, _ => by cases hi
  | n + 1, i, hi, h => by
    have hAnd : (bitsAreAux s expected n &&
        match s.bitLsb n with
        | some src => BitSrc.beq src (expected n)
        | none => false) = true := h
    have hPrev := bool_and_left hAnd
    have hCur := bool_and_right hAnd
    cases hEq : Nat.decEq i n with
    | isTrue he =>
      subst he
      cases hBit : s.bitLsb i with
      | none => rw [hBit] at hCur; cases hCur
      | some src =>
        rw [hBit] at hCur
        rw [BitSrc.eq_of_beq hCur]
    | isFalse hne =>
      have hiLt : i < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hne
      exact bitsAreAux_sound s expected n i hiLt hPrev

/-- Check whether the low `n` bits (`n ≤ 128`, `n ≤ s.width.bitWidth`) of `s`
agree symbolically with `expected`. -/
@[expose] noncomputable def SymScalar.bitsAre (s : SymScalar) (n : Nat)
    (expected : Nat → BitSrc) : Bool :=
  s.wf && Nat.ble n 128 && Nat.ble n (bitWidthComp s.width) && bitsAreAux s expected n

theorem SymScalar.bitsAre_sound {s : SymScalar} {n : Nat}
    {expected : Nat → BitSrc} (h : s.bitsAre n expected = true)
    (env : SymEnv) (i : Nat) (hi : i < n) :
    BitSrc.Agrees env (expected i) (Anneal.BitVec.getLsbD (s.eval env).bits i) := by
  have h1 := bool_and_left h
  have hAux := bool_and_right h
  have h2 := bool_and_left h1
  have hWf := bool_and_left h2
  have hLe128 : n ≤ 128 := Nat.ble_eq.mp (bool_and_right h2)
  have hi128 : i < 128 := Nat.lt_of_lt_of_le hi hLe128
  exact symScalar_bitLsb_sound env s i (expected i) hi128 hWf
    (bitsAreAux_sound s expected n i hi hAux)

/-- Extract the low 64 bits of evaluating an unsigned `u64` `SymScalar` at
`wordEnv x`. -/
@[expose] noncomputable def SymScalar.wordEval (s : SymScalar) (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (s.eval (wordEnv x)).bits.toNat

theorem SymScalar.wordEval_scalar_eq {s : SymScalar}
    (hW : s.width = .i64) (hS : s.signed = false) (hWf : s.wf = true)
    (x : BitVec 64) :
    Val.scalar (s.eval (wordEnv x)) =
      Val.scalar ⟨.i64, false, bvZeroExtend 128 (s.wordEval x)⟩ := by
  have hMeta := symScalar_eval_meta (wordEnv x) s hWf
  have hWid : (s.eval (wordEnv x)).width = .i64 := hMeta.1.trans hW
  have hSig : (s.eval (wordEnv x)).signed = false := hMeta.2.1.trans hS
  have hTr : truncateBits .i64 (s.eval (wordEnv x)).bits =
      (s.eval (wordEnv x)).bits := by
    rw [← hWid]
    exact beq_iff_eq.mp hMeta.2.2
  have hSv : s.eval (wordEnv x) =
      ⟨.i64, false, bvZeroExtend 128 (s.wordEval x)⟩ := by
    cases hEq : s.eval (wordEnv x) with
    | mk w sg b =>
      rw [hEq] at hWid hSig hTr
      dsimp only at hWid hSig hTr
      subst hWid; subst hSig
      dsimp only [SymScalar.wordEval]
      rw [hEq]
      have hLt : b.toNat < Nat.pow 2 64 := by
        rw [← hTr, toNat_truncateBits, intWidthModulus_eq_pow]
        exact Nat.mod_lt _ (nat_two_pow_pos 64)
      have hVecEq : b = bvZeroExtend 128 (BitVec.ofNat 64 b.toNat) := by
        refine bv_eq_of_toNat_eq ?_
        dsimp only [bvZeroExtend]
        rw [Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hLt]
        exact (nat_mod_eq_of_lt (Nat.lt_of_lt_of_le hLt
          (two_pow_bitWidth_le_128 .i64))).symm
      exact congrArg (ScalarVal.mk .i64 false) hVecEq
  exact congrArg Val.scalar hSv

/-- Check whether an unsigned `u64` `SymScalar` matches `expected` across
all 64 bits. -/
@[expose] noncomputable def SymScalar.wordBitsAre (s : SymScalar)
    (expected : Nat → BitSrc) : Bool :=
  intWidthBeqComp s.width .i64 && boolBeqComp s.signed false && s.bitsAre 64 expected

theorem SymScalar.wordBitsAre_sound {s : SymScalar}
    {expected : Nat → BitSrc} (h : s.wordBitsAre expected = true)
    (x : BitVec 64) (i : Nat) (hi : i < 64) :
    BitSrc.Agrees (wordEnv x) (expected i) (Anneal.BitVec.getLsbD (s.wordEval x) i) := by
  have hBits := bool_and_right h
  have hAg := SymScalar.bitsAre_sound hBits (wordEnv x) i hi
  dsimp only [SymScalar.wordEval]
  have hEq : BitVec.ofNat 64 (s.eval (wordEnv x)).bits.toNat =
      BitVec.setWidth 64 (s.eval (wordEnv x)).bits := by
    refine bv_eq_of_toNat_eq ?_
    rw [Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_setWidth]
  rw [hEq, Anneal.BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
  exact hAg

end Anneal.MirSymExec

end
