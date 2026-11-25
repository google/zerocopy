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
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Anneal.AiPcc.BitArith
public import Anneal.AiPcc.Tnum
public import Anneal.AiPcc.WrappedInterval

public section

namespace Anneal.AiPcc

/-!
# Reduced Product Abstract Value (`Anneal.AiPcc.ReducedProduct`)

Combines `InitDom`, `Tnum`, `WrappedInterval`, and `StridedCong` into `AbsVal`
with sound mutual domain reductions, abstract arithmetic/bitwise transfers,
alignment/overflow/bounds queries, and conditional branch refinements.
-/

/-! ### Reduced Product (`InitDom`, `Tnum`, `WrappedInterval`, `StridedCong`) -/

/-- Four-component reduced-product abstract scalar (`InitDom` × `Tnum` ×
`WrappedInterval` × `StridedCong`). -/
structure AbsVal where
  init : InitDom
  tnum : Tnum
  wi   : WrappedInterval
  sc   : StridedCong

/-- Unreachable/empty abstract value. -/
@[expose] def AbsVal.bot : AbsVal := ⟨.bot, ⟨0, 0⟩, .bot, .bot⟩

/-- Top initialized `w`-bit abstract value. -/
@[expose] def AbsVal.topInit (w : Nat) : AbsVal := ⟨.init, Tnum.top w, .top,
    .top⟩

/-- Top possibly-uninitialized `w`-bit abstract value. -/
@[expose] def AbsVal.uninit (w : Nat) : AbsVal := ⟨.uninit, Tnum.top w, .top,
    .top⟩

/-- Exact `w`-bit constant abstract value `c mod 2^w`. -/
@[expose] def AbsVal.const (w c : Nat) : AbsVal :=
  match validWidth w with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    let v := Nat.mod c M
    ⟨.init, Tnum.const w v, WrappedInterval.const M v, mkCong 8 v⟩

/-- Concretization of `AbsVal` at bitwidth `w` over `opt : Option Nat` (`none` =
uninitialized, `some x` = initialized scalar `< 2^w`). -/
@[expose] def AbsVal.denote (w : Nat) (a : AbsVal) (opt : Option Nat) : Prop :=
  let M := modPow2 w
  InitDom.denote M a.init opt ∧
  match opt with
  | none => True
  | some x => a.tnum.denote x ∧ a.wi.denote M x ∧ a.sc.denote x

/-- Fuel-bounded upward scan finding the least `k ≤ w` with `hi < 2^k`. -/
@[expose] def firstPow2BoundUp (hi w : Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun k => Nat.min k w)
    (fun _ ih k =>
      match Nat.blt hi (modPow2 k) with
      | true => Nat.min k w
      | false => ih (k + 1))
    fuel

/-- Least `k ≤ w` satisfying `hi < 2^k` (for interval-to-`Tnum` high-bit
clearing). -/
@[expose] def firstPow2Bound (w hi : Nat) : Nat :=
  firstPow2BoundUp hi w w 0

private theorem firstPow2BoundUp_zero (hi w k : Nat) :
    firstPow2BoundUp hi w 0 k = Nat.min k w := rfl

private theorem firstPow2BoundUp_succ (hi w fuel k : Nat) :
    firstPow2BoundUp hi w (fuel + 1) k =
      match Nat.blt hi (modPow2 k) with
      | true => Nat.min k w
      | false => firstPow2BoundUp hi w fuel (k + 1) := rfl

/-- Soundness of `firstPow2BoundUp`. -/
theorem firstPow2BoundUp_lt {w hi : Nat} (hLtW : hi < modPow2 w) :
    ∀ (fuel k : Nat), fuel + k = w →
      firstPow2BoundUp hi w fuel k ≤ w ∧ hi < modPow2 (firstPow2BoundUp hi w fuel k)
  | 0, k, hEq => by
    have hk : k = w := by rw [← hEq, Nat.zero_add]
    rw [firstPow2BoundUp_zero, hk]
    have hMin : Nat.min w w = w := by
      dsimp only [Nat.min]; rw [Nat.min_def, ite_eq_left (Nat.le_refl w)]
    rw [hMin]
    exact ⟨Nat.le_refl w, hLtW⟩
  | fuel' + 1, k, hEq => by
    rw [firstPow2BoundUp_succ]
    have hkLeW : k ≤ w := by rw [← hEq]; exact Nat.le_add_left k (fuel' + 1)
    cases hc : Nat.blt hi (modPow2 k) with
    | true =>
      dsimp only
      have hMin : Nat.min k w = k := by
        dsimp only [Nat.min]; rw [Nat.min_def, ite_eq_left hkLeW]
      rw [hMin]
      exact ⟨hkLeW, lt_of_blt_true hc⟩
    | false =>
      dsimp only
      have hEq' : fuel' + (k + 1) = w := by
        rw [← hEq, Nat.add_comm k 1, ← Nat.add_assoc fuel' 1 k, Nat.add_comm fuel' 1]
      exact firstPow2BoundUp_lt hLtW fuel' (k + 1) hEq'

/-- Soundness of `firstPow2Bound` when `hi < 2^w`. -/
theorem firstPow2Bound_lt {w hi : Nat} (hLtW : hi < modPow2 w) :
    firstPow2Bound w hi ≤ w ∧ hi < modPow2 (firstPow2Bound w hi) :=
  firstPow2BoundUp_lt hLtW w 0 (Nat.add_zero w)

/-- Extracts exact `x mod 8` residue when the low 3 mask bits of `t` are `0`. -/
theorem mod8_tnum_denote {t : Tnum} {x : Nat} (ht : t.denote x)
    (hMask8 : Nat.mod t.mask 8 = 0) : Nat.mod x 8 = Nat.mod t.val 8 := by
  have h8Eq : modPow2 3 = 8 := rfl
  rw [← h8Eq]
  apply nat_eq_of_bitAt
  intro k
  rw [bitAt_mod_modPow2, bitAt_mod_modPow2]
  cases hk3 : Nat.blt k 3 with
  | false => rfl
  | true =>
    have hMask0 : bitAt t.mask k = false := by
      have hMod : bitAt (Nat.mod t.mask (modPow2 3)) k = bitAt (Nat.mod 0 (modPow2 3)) k := by
        rw [h8Eq, hMask8]
      rw [bitAt_mod_modPow2, hk3, bitAt_mod_modPow2, hk3, bitAt_zero_nat] at hMod
      dsimp only at hMod
      exact hMod
    rw [tnum_denote_iff_bitAt] at ht
    exact ht.2 k hMask0

/-- Refines the low 3 `Tnum` bits from a modulus divisible by `8`. -/
theorem mod8_cong_to_tnum {w m r x : Nat} (hxLt : x < modPow2 w)
    (hc : StridedCong.denote (.cong m r) x) (hm8 : Nat.mod m 8 = 0) :
    Tnum.denote ⟨Nat.mod r 8, andNot (modPow2 w - 1) 7⟩ x := by
  have h8Eq : modPow2 3 = 8 := rfl
  have h7Eq : modPow2 3 - 1 = 7 := rfl
  rw [tnum_denote_iff_bitAt]
  refine ⟨?_, ?_⟩
  · dsimp only [Tnum.wf]
    apply nat_beq_of_eq; apply nat_eq_of_bitAt; intro k
    rw [bitAt_land, bitAt_andNot, bitAt_zero_nat, ← h8Eq, bitAt_mod_modPow2,
        ← h7Eq, bitAt_modPow2_sub_one, bitAt_modPow2_sub_one]
    cases Nat.blt k 3 <;> cases Nat.blt k w <;> cases bitAt r k <;> rfl
  · intro k hm0
    rw [bitAt_andNot] at hm0
    have hFull : Nat.mod x 8 = Nat.mod r 8 := by
      rw [← hc.2.2]
      exact (mod_mod_of_dvd hm8).symm
    cases hk3 : Nat.blt k 3 with
    | true =>
      have hBit : bitAt (Nat.mod x 8) k = bitAt (Nat.mod r 8) k := by rw [hFull]
      rw [← h8Eq, bitAt_mod_modPow2, bitAt_mod_modPow2, hk3] at hBit
      dsimp only at hBit
      rw [← h8Eq, bitAt_mod_modPow2, hk3]
      exact hBit
    | false =>
      have hkGe3 : 3 ≤ k := Nat.le_of_not_lt (fun h => by rw [blt_true_of_lt h] at hk3; nomatch hk3)
      have hGeW : w ≤ k := by
        have hPowZero : bitAt (modPow2 w - 1) k = false := by
          cases hkw : bitAt (modPow2 w - 1) k with
          | false => rfl
          | true =>
            have h70 : bitAt 7 k = false := by
              rw [← h7Eq, bitAt_modPow2_sub_one]; exact hk3
            rw [hkw, h70] at hm0; nomatch hm0
        rw [bitAt_modPow2_sub_one] at hPowZero
        exact Nat.le_of_not_lt (fun h => by rw [blt_true_of_lt h] at hPowZero; nomatch hPowZero)
      have hX0 := bitAt_zero_ge_of_lt_modPow2 hxLt k hGeW
      have hR0 : bitAt (Nat.mod r 8) k = false := by
        rw [← h8Eq, bitAt_mod_modPow2, hk3]
      rw [hX0, hR0]

/-- Tightens a non-wrapping interval lower bound `lo` upward to match `sc`
(`none` if unsatisfiable in `[lo, hi]`). -/
@[expose] def tightLoByCong (lo hi : Nat) : StridedCong → Option Nat
  | .bot => none
  | .top => some lo
  | .cong m r =>
    match Nat.ble 1 m && Nat.blt r m with
    | false => some lo
    | true =>
      let rem := Nat.mod lo m
      let lo' :=
        match Nat.ble rem r with
        | true => lo + (r - rem)
        | false => lo + (m - rem) + r
      match Nat.ble lo' hi with
      | true => some lo'
      | false => none

/-- Arithmetic lower-bound step lemma for `tightLoByCong`. -/
theorem tightLoByCong_step_le {lo x m r : Nat}
    (hmPos : 0 < m) (hLo : lo ≤ x) (hRLt : r < m) (hxMod : Nat.mod x m = r) :
    (match Nat.ble (Nat.mod lo m) r with
     | true => lo + (r - Nat.mod lo m)
     | false => lo + (m - Nat.mod lo m) + r) ≤ x := by
  have hGen : ∀ x' qx lo' qlo rem : Nat,
      rem = Nat.mod lo' m → rem < m → lo' ≤ x' →
      m * qx + r = x' → m * qlo + rem = lo' →
      (match Nat.ble rem r with
       | true => lo' + (r - rem)
       | false => lo' + (m - rem) + r) ≤ x' := by
    intro x' qx lo' qlo rem _hRemDef hRemLt hLo' hXEq hLoEq
    cases hRemR : Nat.ble rem r with
    | true =>
      have hQ : qlo ≤ qx := by
        cases Nat.lt_or_ge qx qlo with
        | inr hGe => exact hGe
        | inl hLt =>
          have h1 : x' < m * (qx + 1) := by
            rw [← hXEq, Nat.mul_succ]; exact Nat.add_lt_add_left hRLt (m * qx)
          have h2 : m * (qx + 1) ≤ lo' := by
            have hm1 := Nat.mul_le_mul_left m (hLt : qx + 1 ≤ qlo)
            exact Nat.le_trans hm1 (by rw [← hLoEq]; exact Nat.le_add_right (m * qlo) rem)
          exact False.elim (Nat.not_le_of_gt (Nat.lt_of_lt_of_le h1 h2) hLo')
      have hEqLo' : lo' + (r - rem) = m * qlo + r := by
        have hLe := Nat.le_of_ble_eq_true hRemR
        rw [← hLoEq, Nat.add_assoc (m * qlo) rem (r - rem), Nat.add_comm rem (r - rem),
            Nat.sub_add_cancel hLe]
      rw [hEqLo', ← hXEq]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left m hQ) r
    | false =>
      have hNot : ¬ (rem ≤ r) := fun h => by rw [Nat.ble_eq_true_of_le h] at hRemR; nomatch hRemR
      have hRltRem := Nat.lt_of_not_le hNot
      have hQ : qlo + 1 ≤ qx := by
        cases Nat.lt_or_ge qlo qx with
        | inl hLt => exact hLt
        | inr hGe =>
          have hXLe : x' < lo' := by
            have h1 : m * qx + r < m * qlo + rem :=
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left hRltRem (m * qx))
                (Nat.add_le_add_right (Nat.mul_le_mul_left m hGe) rem)
            rw [hXEq, hLoEq] at h1
            exact h1
          exact False.elim (Nat.not_le_of_gt hXLe hLo')
      have hEqLo' : lo' + (m - rem) + r = m * (qlo + 1) + r := by
        have h1 : lo' + (m - rem) = m * (qlo + 1) := by
          rw [← hLoEq, Nat.add_assoc, Nat.add_comm rem (m - rem),
              Nat.sub_add_cancel (Nat.le_of_lt hRemLt), ← Nat.mul_succ]
        rw [h1]
      rw [hEqLo', ← hXEq]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left m hQ) r
  have hXDiv := nat_div_add_mod x m
  rw [hxMod] at hXDiv
  exact hGen x (Nat.div x m) lo (Nat.div lo m) (Nat.mod lo m)
    rfl (Nat.mod_lt lo hmPos) hLo hXDiv (nat_div_add_mod lo m)

/-- Soundness of `tightLoByCong` when it returns `some lo'`. -/
theorem tightLoByCong_sound {lo hi x lo' : Nat} {sc : StridedCong}
    (hLo : lo ≤ x) (hSc : sc.denote x)
    (hRes : tightLoByCong lo hi sc = some lo') : lo' ≤ x := by
  cases sc with
  | bot => exact False.elim hSc
  | top => dsimp only [tightLoByCong] at hRes; injection hRes with hEq; rw [← hEq]; exact hLo
  | cong m r =>
    dsimp only [tightLoByCong] at hRes
    have hWf : (Nat.ble 1 m && Nat.blt r m) = true := by
      rw [Nat.ble_eq_true_of_le hSc.1, blt_true_of_lt hSc.2.1]; rfl
    rw [hWf] at hRes
    dsimp only at hRes
    have hLoCandLeX := tightLoByCong_step_le (lo := lo) hSc.1 hLo hSc.2.1 hSc.2.2
    cases hBle : Nat.ble _ hi with
    | false => rw [hBle] at hRes; nomatch hRes
    | true =>
      rw [hBle] at hRes
      injection hRes with hEq
      rw [← hEq]
      exact hLoCandLeX

/-- Completeness of `tightLoByCong`: returns `some` whenever a witness `x ∈ [lo,
hi]` satisfies `sc`. -/
theorem tightLoByCong_none_impossible {lo hi x : Nat} {sc : StridedCong}
    (hLo : lo ≤ x) (hHi : x ≤ hi) (hSc : sc.denote x) :
    tightLoByCong lo hi sc ≠ none := by
  intro hNone
  cases sc with
  | bot => exact hSc
  | top => dsimp only [tightLoByCong] at hNone; nomatch hNone
  | cong m r =>
    dsimp only [tightLoByCong] at hNone
    have hWf : (Nat.ble 1 m && Nat.blt r m) = true := by
      rw [Nat.ble_eq_true_of_le hSc.1, blt_true_of_lt hSc.2.1]; rfl
    rw [hWf] at hNone
    dsimp only at hNone
    have hLoCandLeX := tightLoByCong_step_le (lo := lo) hSc.1 hLo hSc.2.1 hSc.2.2
    cases hBle : Nat.ble _ hi with
    | true => rw [hBle] at hNone; nomatch hNone
    | false =>
      have hLeHi := Nat.le_trans hLoCandLeX hHi
      rw [Nat.ble_eq_true_of_le hLeHi] at hBle
      nomatch hBle

/-- Any inhabited `WrappedInterval` satisfies `WrappedInterval.wf`. -/
theorem wrappedInterval_wf_of_denote {M : Nat} {wi : WrappedInterval} {x : Nat}
    (h : wi.denote M x) : wi.wf M = true := by
  cases wi with
  | bot => exact False.elim h
  | top => rfl
  | iv lo hi =>
    dsimp only [WrappedInterval.wf]
    rw [blt_true_of_lt h.1, blt_true_of_lt h.2.1]; rfl

/-- Any inhabited `StridedCong` satisfies `StridedCong.wf`. -/
theorem stridedCong_wf_of_denote {c : StridedCong} {x : Nat}
    (h : c.denote x) : c.wf = true := by
  cases c with
  | bot => exact False.elim h
  | top => rfl
  | cong m r =>
    dsimp only [StridedCong.wf]
    rw [Nat.ble_eq_true_of_le h.1, blt_true_of_lt h.2.1]; rfl

/-- Tests whether a `WrappedInterval` is `.bot`. -/
@[expose] def WrappedInterval.isBot : WrappedInterval → Bool
  | .bot => true
  | _ => false

/-- Tests whether a `StridedCong` is `.bot`. -/
@[expose] def StridedCong.isBot : StridedCong → Bool
  | .bot => true
  | _ => false

/-- An inhabited `WrappedInterval` is not `.bot`. -/
theorem wrappedInterval_not_isBot {M : Nat} {wi : WrappedInterval} {x : Nat}
    (h : wi.denote M x) : wi.isBot = false := by
  cases wi with
  | bot => exact False.elim h
  | top => rfl
  | iv _ _ => rfl

/-- An inhabited `StridedCong` is not `.bot`. -/
theorem stridedCong_not_isBot {sc : StridedCong} {x : Nat}
    (h : sc.denote x) : sc.isBot = false := by
  cases sc with
  | bot => exact False.elim h
  | top => rfl
  | cong _ _ => rfl

/-- Reduction stage 1 (`Tnum → WrappedInterval`): intersects `wi` with `[t.val,
t.val + t.mask]` while preserving `.top` on full-ring `Tnum.top`. -/
@[expose] def reduceStageWi1 (M : Nat) (t : Tnum) (wi : WrappedInterval) :
    WrappedInterval :=
  match Nat.blt (t.val + t.mask) M with
  | false => wi
  | true =>
    match Nat.beq t.val 0 && Nat.beq t.mask (M - 1) with
    | true => wi
    | false => WrappedInterval.meet M wi (.iv t.val (t.val + t.mask))

/-- Soundness of `reduceStageWi1`. -/
theorem reduceStageWi1_sound {M : Nat} {t : Tnum} {wi : WrappedInterval} {x : Nat}
    (hM : 0 < M) (hxLt : x < M) (ht : t.denote x) (hwi : wi.denote M x) :
    (reduceStageWi1 M t wi).denote M x := by
  dsimp only [reduceStageWi1]
  cases hBnd : Nat.blt (t.val + t.mask) M with
  | false => exact hwi
  | true =>
    cases hFull : Nat.beq t.val 0 && Nat.beq t.mask (M - 1) with
    | true => exact hwi
    | false =>
      have hSumLt := lt_of_blt_true hBnd
      have hBnds := tnum_bounds ht
      have hLoLt : t.val < M := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSumLt
      have hBle : Nat.ble t.val (t.val + t.mask) = true :=
        Nat.ble_eq_true_of_le (Nat.le_add_right _ _)
      have hIv : WrappedInterval.denote M (.iv t.val (t.val + t.mask)) x := by
        refine ⟨hLoLt, hSumLt, hxLt, ?_⟩
        rw [hBle]
        exact hBnds
      exact wrappedInterval_meet_sound hM hwi hIv

/-- Reduction stage 2 (`WrappedInterval → Tnum`): singleton interval meet and
high-bit `capPow2` clearing. -/
@[expose] def reduceStageT1 (w : Nat) (t : Tnum) (wi1 : WrappedInterval) :
    Option Tnum :=
  match wi1 with
  | .iv lo hi =>
    match Nat.ble lo hi with
    | true =>
      match Nat.beq lo hi with
      | true => Tnum.meet t (Tnum.const w lo)
      | false => some (Tnum.capPow2 (firstPow2Bound w hi) t)
    | false => some t
  | _ => some t

/-- Soundness of `reduceStageT1`. -/
theorem reduceStageT1_sound {w : Nat} {t : Tnum} {wi1 : WrappedInterval} {x : Nat}
    (hxLt : x < modPow2 w) (ht : t.denote x) (hwi : wi1.denote (modPow2 w) x) :
    ∃ t1, reduceStageT1 w t wi1 = some t1 ∧ t1.denote x := by
  dsimp only [reduceStageT1]
  cases hWi : wi1 with
  | bot => rw [hWi] at hwi; exact False.elim hwi
  | top => exact ⟨t, rfl, ht⟩
  | iv lo hi =>
    dsimp only
    rw [hWi] at hwi
    cases hBle : Nat.ble lo hi with
    | false => dsimp only; exact ⟨t, rfl, ht⟩
    | true =>
      dsimp only
      dsimp only [WrappedInterval.denote] at hwi
      rw [hBle] at hwi
      cases hEq : Nat.beq lo hi with
      | true =>
        dsimp only
        have hLoHi : lo = hi := Nat.eq_of_beq_eq_true hEq
        have hxLo : x = lo := Nat.le_antisymm (by rw [hLoHi]; exact hwi.2.2.2.2) hwi.2.2.2.1
        have hConst := tnum_const_sound (w := w) (x := lo) (by rw [← hxLo]; exact hxLt)
        have hConstX : (Tnum.const w lo).denote x := by rw [hxLo]; exact hConst
        have hNeNone := tnum_meet_none_impossible ht hConstX
        cases hRes : Tnum.meet t (Tnum.const w lo) with
        | none => exact False.elim (hNeNone hRes)
        | some res => exact ⟨res, rfl, tnum_meet_sound ht hConstX hRes⟩
      | false =>
        dsimp only
        have hPow := firstPow2Bound_lt hwi.2.1
        have hxHiLt : x < modPow2 (firstPow2Bound w hi) := Nat.lt_of_le_of_lt hwi.2.2.2.2 hPow.2
        exact ⟨Tnum.capPow2 (firstPow2Bound w hi) t, rfl, tnum_capPow2_sound ht hxHiLt⟩

/-- Reduction stage 3 (`Tnum → StridedCong`): propagates known low-3-bit residue
into `StridedCong`. -/
@[expose] def reduceStageSc1 (w : Nat) (t1 : Tnum) (sc : StridedCong) :
    StridedCong :=
  match Nat.ble 3 w && Nat.beq (Nat.mod t1.mask 8) 0 with
  | true => StridedCong.meet sc (mkCong 8 t1.val)
  | false => sc

/-- Soundness of `reduceStageSc1`. -/
theorem reduceStageSc1_sound {w : Nat} {t1 : Tnum} {sc : StridedCong} {x : Nat}
    (ht1 : t1.denote x) (hsc : sc.denote x) :
    (reduceStageSc1 w t1 sc).denote x := by
  dsimp only [reduceStageSc1]
  cases hm8 : Nat.ble 3 w && Nat.beq (Nat.mod t1.mask 8) 0 with
  | false => exact hsc
  | true =>
    have hM8 := Nat.eq_of_beq_eq_true (bool_and_true_right hm8)
    have hMod8 := mod8_tnum_denote ht1 hM8
    exact stridedCong_meet_sound hsc (mkCong_denote (Nat.zero_lt_succ 7) hMod8)

/-- Reduction stage 4 (`StridedCong → Tnum`): propagates mod-`8` congruence into
low 3 `Tnum` bits. -/
@[expose] def reduceStageT2 (w : Nat) (t1 : Tnum) (sc1 : StridedCong) : Option
    Tnum :=
  match Nat.ble 3 w, sc1 with
  | true, .cong m r =>
    match Nat.beq (Nat.mod m 8) 0 with
    | true => Tnum.meet t1 ⟨Nat.mod r 8, andNot (modPow2 w - 1) 7⟩
    | false => some t1
  | _, _ => some t1

/-- Soundness of `reduceStageT2`. -/
theorem reduceStageT2_sound {w : Nat} {t1 : Tnum} {sc1 : StridedCong} {x : Nat}
    (hxLt : x < modPow2 w) (ht1 : t1.denote x) (hsc : sc1.denote x) :
    ∃ t2, reduceStageT2 w t1 sc1 = some t2 ∧ t2.denote x := by
  dsimp only [reduceStageT2]
  cases hw3 : Nat.ble 3 w with
  | false => dsimp only; exact ⟨t1, rfl, ht1⟩
  | true =>
    cases hSc : sc1 with
    | bot => rw [hSc] at hsc; exact False.elim hsc
    | top => dsimp only; exact ⟨t1, rfl, ht1⟩
    | cong m r =>
      dsimp only
      cases hm8 : Nat.beq (Nat.mod m 8) 0 with
      | false => dsimp only; exact ⟨t1, rfl, ht1⟩
      | true =>
        dsimp only
        have hScC : StridedCong.denote (.cong m r) x := by rw [← hSc]; exact hsc
        have hT8 := mod8_cong_to_tnum hxLt hScC (Nat.eq_of_beq_eq_true hm8)
        have hNeNone := tnum_meet_none_impossible ht1 hT8
        cases hRes : Tnum.meet t1 ⟨Nat.mod r 8, andNot (modPow2 w - 1) 7⟩ with
        | none => exact False.elim (hNeNone hRes)
        | some res => exact ⟨res, rfl, tnum_meet_sound ht1 hT8 hRes⟩

/-- Reduction stage 5 (`StridedCong → WrappedInterval`): tightens non-straddling
interval lower bounds modulo stride. -/
@[expose] def reduceStageWi2 (wi1 : WrappedInterval) (sc1 : StridedCong) :
    WrappedInterval :=
  match wi1 with
  | .iv lo hi =>
    match Nat.ble lo hi with
    | true =>
      match tightLoByCong lo hi sc1 with
      | none => .bot
      | some lo' => .iv lo' hi
    | false => wi1
  | _ => wi1

/-- Soundness of `reduceStageWi2`. -/
theorem reduceStageWi2_sound {M : Nat} {wi1 : WrappedInterval} {sc1 : StridedCong} {x : Nat}
    (hwi : wi1.denote M x) (hsc : sc1.denote x) :
    (reduceStageWi2 wi1 sc1).denote M x := by
  dsimp only [reduceStageWi2]
  cases hWi : wi1 with
  | bot => rw [hWi] at hwi; exact False.elim hwi
  | top => dsimp only; rw [hWi] at hwi; exact hwi
  | iv lo hi =>
    dsimp only
    rw [hWi] at hwi
    cases hBle : Nat.ble lo hi with
    | false => dsimp only; exact hwi
    | true =>
      dsimp only
      dsimp only [WrappedInterval.denote] at hwi
      rw [hBle] at hwi
      have hNeNone := tightLoByCong_none_impossible hwi.2.2.2.1 hwi.2.2.2.2 hsc
      cases hRes : tightLoByCong lo hi sc1 with
      | none => exact False.elim (hNeNone hRes)
      | some lo' =>
        dsimp only
        have hLo'Le := tightLoByCong_sound hwi.2.2.2.1 hsc hRes
        have hLo'Hi : lo' ≤ hi := Nat.le_trans hLo'Le hwi.2.2.2.2
        have hLo'LtM : lo' < M := Nat.lt_of_le_of_lt hLo'Hi hwi.2.1
        refine ⟨hLo'LtM, hwi.2.1, hwi.2.2.1, ?_⟩
        rw [Nat.ble_eq_true_of_le hLo'Hi]
        exact ⟨hLo'Le, hwi.2.2.2.2⟩

/-- Five-stage mutual domain reduction across `InitDom`, `Tnum`,
`WrappedInterval`, and `StridedCong`. -/
@[expose] def reduceAbsVal (w : Nat) (v : AbsVal) : AbsVal :=
  match validWidth w with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    match v.init with
    | .bot => AbsVal.bot
    | .uninit => v
    | .init =>
      match v.wi.isBot || v.sc.isBot with
      | true => AbsVal.bot
      | false =>
        match v.tnum.wf && v.wi.wf M && v.sc.wf with
        | false => AbsVal.bot
        | true =>
          let wi1 := reduceStageWi1 M v.tnum v.wi
          match wi1.isBot with
          | true => AbsVal.bot
          | false =>
            match reduceStageT1 w v.tnum wi1 with
            | none => AbsVal.bot
            | some t1 =>
              let sc1 := reduceStageSc1 w t1 v.sc
              match sc1.isBot with
              | true => AbsVal.bot
              | false =>
                match reduceStageT2 w t1 sc1 with
                | none => AbsVal.bot
                | some t2 =>
                  let wi2 := reduceStageWi2 (reduceStageWi1 M t2 wi1) sc1
                  match wi2.isBot with
                  | true => AbsVal.bot
                  | false => ⟨.init, t2, wi2, sc1⟩

/-- Soundness of `reduceAbsVal`. -/
theorem reduceAbsVal_sound {w : Nat} (hw : validWidth w = true) {v : AbsVal} {opt : Option Nat}
    (hv : AbsVal.denote w v opt) : AbsVal.denote w (reduceAbsVal w v) opt := by
  dsimp only [reduceAbsVal]
  rw [hw]
  dsimp only
  let M := modPow2 w
  have hM : 0 < M := modPow2_pos w
  cases hInit : v.init with
  | bot =>
    dsimp only [AbsVal.denote] at hv
    rw [hInit] at hv
    exact False.elim hv.1
  | uninit => exact hv
  | init =>
    dsimp only [AbsVal.denote] at hv
    rw [hInit] at hv
    cases hv.1 with
    | intro x hx =>
      have hxEq : opt = some x := hx.1
      have hxLt : x < M := hx.2
      rw [hxEq] at hv; rw [hxEq]
      have hT : v.tnum.denote x := hv.2.1
      have hWi : v.wi.denote M x := hv.2.2.1
      have hSc : v.sc.denote x := hv.2.2.2
      have hBotPair : (v.wi.isBot || v.sc.isBot) = false := by
        rw [wrappedInterval_not_isBot hWi, stridedCong_not_isBot hSc]; rfl
      have hWfs : (v.tnum.wf && v.wi.wf M && v.sc.wf) = true := by
        rw [hT.1, wrappedInterval_wf_of_denote hWi, stridedCong_wf_of_denote hSc]; rfl
      rw [hBotPair, hWfs]
      dsimp only
      let wi1 := reduceStageWi1 M v.tnum v.wi
      have hwi1 : wi1.denote M x := reduceStageWi1_sound hM hxLt hT hWi
      rw [wrappedInterval_not_isBot hwi1]
      dsimp only
      have hT1Ex := reduceStageT1_sound hxLt hT hwi1
      cases hT1C : reduceStageT1 w v.tnum wi1 with
      | none => cases hT1Ex with | intro t1 ht1 => rw [hT1C] at ht1; nomatch ht1.1
      | some t1 =>
        dsimp only
        have ht1Den : t1.denote x := by
          cases hT1Ex with | intro t1' ht1 =>
            rw [hT1C] at ht1; injection ht1.1 with hEq; rw [hEq]; exact ht1.2
        let sc1 := reduceStageSc1 w t1 v.sc
        have hsc1 : sc1.denote x := reduceStageSc1_sound ht1Den hSc
        rw [stridedCong_not_isBot hsc1]
        dsimp only
        have hT2Ex := reduceStageT2_sound hxLt ht1Den hsc1
        cases hT2C : reduceStageT2 w t1 sc1 with
        | none => cases hT2Ex with | intro t2 ht2 => rw [hT2C] at ht2; nomatch ht2.1
        | some t2 =>
          dsimp only
          have ht2Den : t2.denote x := by
            cases hT2Ex with | intro t2' ht2 =>
              rw [hT2C] at ht2; injection ht2.1 with hEq; rw [hEq]; exact ht2.2
          let wi2 := reduceStageWi2 (reduceStageWi1 M t2 wi1) sc1
          have hwi2 : wi2.denote M x :=
            reduceStageWi2_sound (reduceStageWi1_sound hM hxLt ht2Den hwi1) hsc1
          rw [wrappedInterval_not_isBot hwi2]
          dsimp only [AbsVal.denote]
          exact ⟨⟨x, rfl, hxLt⟩, ht2Den, hwi2, hsc1⟩

/-- Componentwise decidable inclusion check `a ⊑ b` on `AbsVal`. -/
@[expose] def AbsVal.le (w : Nat) (a b : AbsVal) : Bool :=
  let M := modPow2 w
  match InitDom.le a.init b.init with
  | false => false
  | true =>
    match a.init with
    | .bot => true
    | .uninit =>
      -- b.init must also be .uninit since InitDom.le .uninit b.init = true
      Tnum.le a.tnum b.tnum && WrappedInterval.le M a.wi b.wi && StridedCong.le a.sc b.sc
    | .init =>
      match b.init with
      | .init => Tnum.le a.tnum b.tnum && WrappedInterval.le M a.wi b.wi && StridedCong.le a.sc b.sc
      | .uninit =>
        Tnum.le a.tnum b.tnum && WrappedInterval.le M a.wi b.wi &&
          StridedCong.le a.sc b.sc
      | .bot => false

/-- Soundness of `AbsVal.le`. -/
theorem absVal_le_sound {w : Nat} {a b : AbsVal} {opt : Option Nat}
    (hLe : AbsVal.le w a b = true) (ha : a.denote w opt) : b.denote w opt := by
  have hM : 0 < modPow2 w := modPow2_pos w
  dsimp only [AbsVal.le] at hLe
  cases hILe : InitDom.le a.init b.init with
  | false => rw [hILe] at hLe; nomatch hLe
  | true =>
    rw [hILe] at hLe
    dsimp only at hLe
    have hInitB := initDom_le_sound (modPow2 w) hILe ha.1
    cases haInit : a.init with
    | bot => dsimp only [AbsVal.denote] at ha; rw [haInit] at ha; exact False.elim ha.1
    | uninit =>
      rw [haInit] at hLe
      dsimp only at hLe
      have h12 := bool_and_true_left hLe
      refine ⟨hInitB, ?_⟩
      cases opt with
      | none => exact True.intro
      | some x =>
        have hax := ha.2
        exact ⟨tnum_le_sound (bool_and_true_left h12) hax.1,
               wrappedInterval_le_sound hM (bool_and_true_right h12) hax.2.1,
               stridedCong_le_sound (bool_and_true_right hLe) hax.2.2⟩
    | init =>
      rw [haInit] at hLe
      dsimp only [AbsVal.denote] at ha
      rw [haInit] at ha
      cases ha.1 with
      | intro x hx =>
        rw [hx.1] at hInitB; rw [hx.1]
        cases hbInit : b.init with
        | bot => rw [hbInit] at hLe; nomatch hLe
        | init =>
          rw [hbInit] at hLe
          dsimp only at hLe
          have h12 := bool_and_true_left hLe
          refine ⟨hInitB, ?_⟩
          have hax := ha.2
          rw [hx.1] at hax
          exact ⟨tnum_le_sound (bool_and_true_left h12) hax.1,
                 wrappedInterval_le_sound hM (bool_and_true_right h12) hax.2.1,
                 stridedCong_le_sound (bool_and_true_right hLe) hax.2.2⟩
        | uninit =>
          rw [hbInit] at hLe
          dsimp only at hLe
          have h12 := bool_and_true_left hLe
          refine ⟨hInitB, ?_⟩
          have hax := ha.2
          rw [hx.1] at hax
          exact ⟨tnum_le_sound (bool_and_true_left h12) hax.1,
                 wrappedInterval_le_sound hM (bool_and_true_right h12) hax.2.1,
                 stridedCong_le_sound (bool_and_true_right hLe) hax.2.2⟩

/-- Componentwise join followed by `reduceAbsVal` on `AbsVal`. -/
@[expose] def AbsVal.join (w : Nat) (a b : AbsVal) : AbsVal :=
  let M := modPow2 w
  match a.init, b.init with
  | .bot, _ => b
  | _, .bot => a
  | _, _ =>
    reduceAbsVal w
      ⟨InitDom.join a.init b.init,
       Tnum.join a.tnum b.tnum,
       WrappedInterval.join M a.wi b.wi,
       StridedCong.join a.sc b.sc⟩

/-- Left upper-bound soundness of `AbsVal.join`. -/
theorem absVal_join_sound_left {w : Nat} (hw : validWidth w = true)
    (a b : AbsVal) {opt : Option Nat}
    (ha : a.denote w opt) : (AbsVal.join w a b).denote w opt := by
  have hM : 0 < modPow2 w := modPow2_pos w
  dsimp only [AbsVal.join]
  cases haInit : a.init with
  | bot => dsimp only [AbsVal.denote] at ha; rw [haInit] at ha; exact False.elim ha.1
  | init =>
    cases hbInit : b.init with
    | bot => exact ha
    | init =>
      apply reduceAbsVal_sound hw
      dsimp only [AbsVal.denote]
      dsimp only [InitDom.join]
      dsimp only [AbsVal.denote] at ha
      rw [haInit] at ha
      refine ⟨ha.1, ?_⟩
      cases ha.1 with | intro x hx =>
        rw [hx.1] at ha; rw [hx.1]
        exact ⟨tnum_join_sound_left ha.2.1,
               wrappedInterval_join_sound_left hM a.wi b.wi ha.2.2.1,
               stridedCong_join_sound_left ha.2.2.2⟩
    | uninit =>
      apply reduceAbsVal_sound hw
      dsimp only [AbsVal.denote]
      dsimp only [InitDom.join]
      dsimp only [AbsVal.denote] at ha
      rw [haInit] at ha
      cases ha.1 with | intro x hx =>
        rw [hx.1] at ha; rw [hx.1]
        refine ⟨hx.2, tnum_join_sound_left ha.2.1,
                wrappedInterval_join_sound_left hM a.wi b.wi ha.2.2.1,
                stridedCong_join_sound_left ha.2.2.2⟩
  | uninit =>
    cases hbInit : b.init with
    | bot => exact ha
    | init =>
      apply reduceAbsVal_sound hw
      dsimp only [AbsVal.denote]
      dsimp only [InitDom.join]
      dsimp only [AbsVal.denote] at ha
      rw [haInit] at ha
      refine ⟨ha.1, ?_⟩
      cases opt with
      | none => exact True.intro
      | some x =>
        exact ⟨tnum_join_sound_left ha.2.1,
               wrappedInterval_join_sound_left hM a.wi b.wi ha.2.2.1,
               stridedCong_join_sound_left ha.2.2.2⟩
    | uninit =>
      apply reduceAbsVal_sound hw
      dsimp only [AbsVal.denote]
      dsimp only [InitDom.join]
      dsimp only [AbsVal.denote] at ha
      rw [haInit] at ha
      refine ⟨ha.1, ?_⟩
      cases opt with
      | none => exact True.intro
      | some x =>
        exact ⟨tnum_join_sound_left ha.2.1,
               wrappedInterval_join_sound_left hM a.wi b.wi ha.2.2.1,
               stridedCong_join_sound_left ha.2.2.2⟩

/-- Right upper-bound soundness of `AbsVal.join`. -/
theorem absVal_join_sound_right {w : Nat} (hw : validWidth w = true)
    (a b : AbsVal) {opt : Option Nat}
    (hb : b.denote w opt) : (AbsVal.join w a b).denote w opt := by
  have hM : 0 < modPow2 w := modPow2_pos w
  dsimp only [AbsVal.join]
  cases haInit : a.init with
  | bot => exact hb
  | init =>
    cases hbInit : b.init with
    | bot => dsimp only [AbsVal.denote] at hb; rw [hbInit] at hb; exact False.elim hb.1
    | init =>
      apply reduceAbsVal_sound hw
      dsimp only [AbsVal.denote]
      dsimp only [InitDom.join]
      dsimp only [AbsVal.denote] at hb
      rw [hbInit] at hb
      refine ⟨hb.1, ?_⟩
      cases hb.1 with | intro x hx =>
        rw [hx.1] at hb; rw [hx.1]
        exact ⟨tnum_join_sound_right hb.2.1,
               wrappedInterval_join_sound_right hM a.wi b.wi hb.2.2.1,
               stridedCong_join_sound_right hb.2.2.2⟩
    | uninit =>
      apply reduceAbsVal_sound hw
      dsimp only [AbsVal.denote]
      dsimp only [InitDom.join]
      dsimp only [AbsVal.denote] at hb
      rw [hbInit] at hb
      refine ⟨hb.1, ?_⟩
      cases opt with
      | none => exact True.intro
      | some x =>
        exact ⟨tnum_join_sound_right hb.2.1,
               wrappedInterval_join_sound_right hM a.wi b.wi hb.2.2.1,
               stridedCong_join_sound_right hb.2.2.2⟩
  | uninit =>
    cases hbInit : b.init with
    | bot => dsimp only [AbsVal.denote] at hb; rw [hbInit] at hb; exact False.elim hb.1
    | init =>
      apply reduceAbsVal_sound hw
      dsimp only [AbsVal.denote]
      dsimp only [InitDom.join]
      dsimp only [AbsVal.denote] at hb
      rw [hbInit] at hb
      cases hb.1 with | intro x hx =>
        rw [hx.1] at hb; rw [hx.1]
        refine ⟨hx.2, tnum_join_sound_right hb.2.1,
                wrappedInterval_join_sound_right hM a.wi b.wi hb.2.2.1,
                stridedCong_join_sound_right hb.2.2.2⟩
    | uninit =>
      apply reduceAbsVal_sound hw
      dsimp only [AbsVal.denote]
      dsimp only [InitDom.join]
      dsimp only [AbsVal.denote] at hb
      rw [hbInit] at hb
      refine ⟨hb.1, ?_⟩
      cases opt with
      | none => exact True.intro
      | some x =>
        exact ⟨tnum_join_sound_right hb.2.1,
               wrappedInterval_join_sound_right hM a.wi b.wi hb.2.2.1,
               stridedCong_join_sound_right hb.2.2.2⟩

/-! ### Abstract Queries, Transfers, and Branch Refinements -/


/-- True iff `a.init = .init` (definitely initialized). -/
@[expose] def AbsVal.isInit (a : AbsVal) : Bool :=
  match a.init with
  | .init => true
  | _ => false

/-- Unpacks `AbsVal.denote w a (some x)` into its four domain conjuncts. -/
theorem absVal_some_elim {w : Nat} {a : AbsVal} {x : Nat}
    (h : AbsVal.denote w a (some x)) :
    x < modPow2 w ∧ a.tnum.denote x ∧ a.wi.denote (modPow2 w) x ∧ a.sc.denote x := by
  dsimp only [AbsVal.denote] at h
  cases hi : a.init with
  | bot => rw [hi] at h; exact False.elim h.1
  | uninit => rw [hi] at h; exact ⟨h.1, h.2⟩
  | init =>
    rw [hi] at h
    dsimp only [InitDom.denote] at h
    cases h.1 with
    | intro x' hx' =>
      injection hx'.1 with hEq
      rw [← hEq] at hx'
      exact ⟨hx'.2, h.2⟩

/-- `a.isInit = true` guarantees `opt = some x` with `x < 2^w`. -/
theorem absVal_init_of_isInit {w : Nat} {a : AbsVal} {opt : Option Nat}
    (hInit : a.isInit = true) (h : a.denote w opt) :
    ∃ x : Nat, opt = some x ∧ x < modPow2 w ∧
      a.tnum.denote x ∧ a.wi.denote (modPow2 w) x ∧ a.sc.denote x := by
  dsimp only [AbsVal.isInit] at hInit
  dsimp only [AbsVal.denote] at h
  cases hi : a.init with
  | bot => rw [hi] at hInit; nomatch hInit
  | uninit => rw [hi] at hInit; nomatch hInit
  | init =>
    rw [hi] at h
    dsimp only [InitDom.denote] at h
    cases h.1 with
    | intro x hx =>
      rw [hx.1] at h
      exact ⟨x, hx.1, hx.2, h.2⟩

/-- `AbsVal.topInit w` denotes every initialized `x < 2^w`. -/
theorem absVal_topInit_sound {w x : Nat} (hx : x < modPow2 w) :
    (AbsVal.topInit w).denote w (some x) := by
  dsimp only [AbsVal.topInit, AbsVal.denote, InitDom.denote,
    WrappedInterval.denote, StridedCong.denote]
  exact ⟨⟨x, rfl, hx⟩, tnum_top_sound hx, hx, True.intro⟩

/-- `AbsVal.uninit w` denotes `none`. -/
theorem absVal_uninit_sound_none {w : Nat} : (AbsVal.uninit w).denote w none :=
  ⟨True.intro, True.intro⟩

/-- `AbsVal.uninit w` denotes every initialized `some x` with `x < 2^w`. -/
theorem absVal_uninit_sound_some {w x : Nat} (hx : x < modPow2 w) :
    (AbsVal.uninit w).denote w (some x) := by
  dsimp only [AbsVal.uninit, AbsVal.denote, InitDom.denote,
    WrappedInterval.denote, StridedCong.denote]
  exact ⟨hx, tnum_top_sound hx, hx, True.intro⟩

/-- Soundness of `AbsVal.const w c`. -/
theorem absVal_const_sound {w c : Nat} (hw : validWidth w = true) :
    (AbsVal.const w c).denote w (some (wrapVal w c)) := by
  let _ := hw
  dsimp only [AbsVal.const]
  rw [hw]
  dsimp only [AbsVal.denote, InitDom.denote]
  have hM : 0 < modPow2 w := modPow2_pos w
  have hvLt : wrapVal w c < modPow2 w := nat_mod_lt c hM
  refine ⟨⟨wrapVal w c, rfl, hvLt⟩, tnum_const_sound hvLt, ?_, ?_⟩
  · dsimp only [WrappedInterval.const]
    cases hb : Nat.beq (modPow2 w) 0 with
    | true => have hz := Nat.eq_of_beq_eq_true hb; rw [hz] at hM; nomatch hM
    | false =>
      dsimp only [WrappedInterval.denote, wrapVal]
      have hvMod : Nat.mod (Nat.mod c (modPow2 w)) (modPow2 w) = wrapVal w c :=
        nat_mod_eq_of_lt hvLt
      rw [hvMod, Nat.ble_eq_true_of_le (Nat.le_refl _)]
      exact ⟨hvLt, hvLt, hvLt, Nat.le_refl _, Nat.le_refl _⟩
  · exact mkCong_denote (Nat.zero_lt_succ 7) rfl

/-- Helper constructing `WrappedInterval.denote M (.iv lo hi) x` for
non-straddling `lo ≤ x ≤ hi`. -/
theorem wrapped_denote_iv_of_le {M lo hi x : Nat}
    (hLo : lo < M) (hHi : hi < M) (hLe : lo ≤ hi) (hxLo : lo ≤ x) (hxHi : x ≤ hi) :
    WrappedInterval.denote M (.iv lo hi) x := by
  dsimp only [WrappedInterval.denote]
  rw [Nat.ble_eq_true_of_le hLe]
  exact ⟨hLo, hHi, Nat.lt_of_le_of_lt hxHi hHi, hxLo, hxHi⟩

/-- Decidable guard checking `8`-byte alignment (`x mod 8 = 0`) on an
initialized `AbsVal`. -/
@[expose] def AbsVal.isAligned8 (a : AbsVal) : Bool :=
  match a.init with
  | .init =>
    match a.sc with
    | .cong m r => Nat.ble 1 m && Nat.beq (Nat.mod m 8) 0 && Nat.beq (Nat.mod r 8) 0
    | _ => false
  | _ => false

/-- Soundness of `AbsVal.isAligned8`. -/
theorem absVal_isAligned8_sound {w : Nat} {a : AbsVal} {opt : Option Nat}
    (hAl : a.isAligned8 = true) (ha : a.denote w opt) :
    ∃ x : Nat, opt = some x ∧ x < modPow2 w ∧ Nat.mod x 8 = 0 ∧ a.denote w (some x) := by
  dsimp only [AbsVal.isAligned8] at hAl
  cases hi : a.init with
  | bot => rw [hi] at hAl; nomatch hAl
  | uninit => rw [hi] at hAl; nomatch hAl
  | init =>
    have hIsInit : a.isInit = true := by dsimp only [AbsVal.isInit]; rw [hi]
    have hEx := absVal_init_of_isInit hIsInit ha
    cases hEx with
    | intro x hx =>
      rw [hi] at hAl
      cases hSc : a.sc with
      | bot => rw [hSc] at hAl; nomatch hAl
      | top => rw [hSc] at hAl; nomatch hAl
      | cong m r =>
        rw [hSc] at hAl
        have h12 := bool_and_true_left hAl
        have hmDvd := Nat.eq_of_beq_eq_true (bool_and_true_right h12)
        have hr8 := Nat.eq_of_beq_eq_true (bool_and_true_right hAl)
        have hScx := hx.2.2.2.2
        rw [hSc] at hScx
        have hMod8 : Nat.mod x 8 = 0 := by
          rw [← mod_mod_of_dvd hmDvd, hScx.2.2, hr8]
        have haSome : a.denote w (some x) := by rw [← hx.1]; exact ha
        exact ⟨x, hx.1, hx.2.1, hMod8, haSome⟩

/-- Decidable guard certifying `x + imm < 2^w` (no unsigned constant-addition
overflow). -/
@[expose] def AbsVal.noOverflowAddConst (w : Nat) (a : AbsVal) (imm : Nat) :
    Bool :=
  match validWidth w, a.init, a.wi with
  | true, .init, .iv lo hi => Nat.ble lo hi && Nat.blt (hi + imm) (modPow2 w)
  | _, _, _ => false

/-- Soundness of `AbsVal.noOverflowAddConst`. -/
theorem absVal_noOverflowAddConst_sound {w : Nat} {a : AbsVal} {imm : Nat} {opt : Option Nat}
    (hOk : a.noOverflowAddConst w imm = true) (ha : a.denote w opt) :
    ∃ x : Nat, opt = some x ∧ x + imm < modPow2 w ∧ a.denote w (some x) := by
  dsimp only [AbsVal.noOverflowAddConst] at hOk
  cases hw : validWidth w with
  | false => rw [hw] at hOk; nomatch hOk
  | true =>
    cases hiInit : a.init with
    | bot => rw [hw, hiInit] at hOk; nomatch hOk
    | uninit => rw [hw, hiInit] at hOk; nomatch hOk
    | init =>
      have hIsInit : a.isInit = true := by dsimp only [AbsVal.isInit]; rw [hiInit]
      have hEx := absVal_init_of_isInit hIsInit ha
      cases hEx with
      | intro x hx =>
        cases hWi : a.wi with
        | bot => rw [hw, hiInit, hWi] at hOk; nomatch hOk
        | top => rw [hw, hiInit, hWi] at hOk; nomatch hOk
        | iv lo hi =>
          rw [hw, hiInit, hWi] at hOk
          dsimp only at hOk
          have hLe : lo ≤ hi := Nat.le_of_ble_eq_true (bool_and_true_left hOk)
          have hLt : hi + imm < modPow2 w := lt_of_blt_true (bool_and_true_right hOk)
          have hWix := hx.2.2.2.1
          rw [hWi] at hWix
          dsimp only [WrappedInterval.denote] at hWix
          rw [Nat.ble_eq_true_of_le hLe] at hWix
          have hxImm : x + imm < modPow2 w :=
            Nat.lt_of_le_of_lt (Nat.add_le_add_right hWix.2.2.2.2 imm) hLt
          have haSome : a.denote w (some x) := by rw [← hx.1]; exact ha
          exact ⟨x, hx.1, hxImm, haSome⟩

/-- Decidable guard certifying `x + y < 2^w` (discharging `BinOp.addUnchecked`
UB). -/
@[expose] def AbsVal.noOverflowAdd (w : Nat) (a b : AbsVal) : Bool :=
  match validWidth w, a.init, b.init, a.wi, b.wi with
  | true, .init, .init, .iv lo1 hi1, .iv lo2 hi2 =>
    Nat.ble lo1 hi1 && Nat.ble lo2 hi2 && Nat.blt (hi1 + hi2) (modPow2 w)
  | _, _, _, _, _ => false

/-- Soundness of `AbsVal.noOverflowAdd`. -/
theorem absVal_noOverflowAdd_sound {w : Nat} {a b : AbsVal} {optA optB : Option Nat}
    (hOk : AbsVal.noOverflowAdd w a b = true) (ha : a.denote w optA) (hb : b.denote w optB) :
    ∃ x y : Nat, optA = some x ∧ optB = some y ∧ x + y < modPow2 w ∧
      a.denote w (some x) ∧ b.denote w (some y) := by
  dsimp only [AbsVal.noOverflowAdd] at hOk
  cases hw : validWidth w with
  | false => rw [hw] at hOk; nomatch hOk
  | true =>
    cases hai : a.init with
    | bot => rw [hw, hai] at hOk; nomatch hOk
    | uninit => rw [hw, hai] at hOk; nomatch hOk
    | init =>
      cases hbi : b.init with
      | bot => rw [hw, hai, hbi] at hOk; nomatch hOk
      | uninit => rw [hw, hai, hbi] at hOk; nomatch hOk
      | init =>
        have hExA := absVal_init_of_isInit (by dsimp only [AbsVal.isInit]; rw [hai]) ha
        have hExB := absVal_init_of_isInit (by dsimp only [AbsVal.isInit]; rw [hbi]) hb
        cases hExA with
        | intro x hx =>
          cases hExB with
          | intro y hy =>
            cases hWia : a.wi with
            | bot => rw [hw, hai, hbi, hWia] at hOk; nomatch hOk
            | top => rw [hw, hai, hbi, hWia] at hOk; nomatch hOk
            | iv lo1 hi1 =>
              cases hWib : b.wi with
              | bot => rw [hw, hai, hbi, hWia, hWib] at hOk; nomatch hOk
              | top => rw [hw, hai, hbi, hWia, hWib] at hOk; nomatch hOk
              | iv lo2 hi2 =>
                rw [hw, hai, hbi, hWia, hWib] at hOk
                dsimp only at hOk
                have h12 := bool_and_true_left hOk
                have hLe1 := Nat.le_of_ble_eq_true (bool_and_true_left h12)
                have hLe2 := Nat.le_of_ble_eq_true (bool_and_true_right h12)
                have hLt := lt_of_blt_true (bool_and_true_right hOk)
                have hWix := hx.2.2.2.1; rw [hWia] at hWix
                dsimp only [WrappedInterval.denote] at hWix
                rw [Nat.ble_eq_true_of_le hLe1] at hWix
                have hWiy := hy.2.2.2.1; rw [hWib] at hWiy
                dsimp only [WrappedInterval.denote] at hWiy
                rw [Nat.ble_eq_true_of_le hLe2] at hWiy
                have hSum : x + y < modPow2 w :=
                  Nat.lt_of_le_of_lt (Nat.add_le_add hWix.2.2.2.2 hWiy.2.2.2.2) hLt
                exact ⟨x, y, hx.1, hy.1, hSum,
                  by rw [← hx.1]; exact ha, by rw [← hy.1]; exact hb⟩

/-- Modular `w`-bit addition transfer on `AbsVal`. -/
@[expose] def AbsVal.addWrap (w : Nat) (a b : AbsVal) : AbsVal :=
  match validWidth w && a.isInit && b.isInit with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    reduceAbsVal w
      ⟨.init,
       Tnum.add w a.tnum b.tnum,
       WrappedInterval.add M a.wi b.wi,
       StridedCong.wrapAdd M a.sc b.sc⟩

/-- Soundness of `AbsVal.addWrap`. -/
theorem absVal_addWrap_sound {w x y : Nat} {a b : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hb : b.denote w (some y))
    (hai : a.isInit = true) (hbi : b.isInit = true) :
    (AbsVal.addWrap w a b).denote w (some (wrapVal w (x + y))) := by
  dsimp only [AbsVal.addWrap]
  rw [hw, hai, hbi]
  apply reduceAbsVal_sound hw
  have hM : 0 < modPow2 w := modPow2_pos w
  have haE := absVal_some_elim ha
  have hbE := absVal_some_elim hb
  have hWrapLt : wrapVal w (x + y) < modPow2 w := nat_mod_lt (x + y) hM
  dsimp only [AbsVal.denote]
  refine ⟨⟨wrapVal w (x + y), rfl, hWrapLt⟩, ?_, ?_, ?_⟩
  · exact tnum_add_sound haE.2.1 hbE.2.1
  · exact wrappedInterval_add_sound hM haE.2.2.1 hbE.2.2.1
  · exact stridedCong_wrapAdd_sound haE.2.2.2 hbE.2.2.2

/-- Modular `w`-bit constant-addition transfer on `AbsVal`. -/
@[expose] def AbsVal.addConstWrap (w : Nat) (a : AbsVal) (imm : Nat) : AbsVal :=
  let M := modPow2 w
  match validWidth w && a.isInit && Nat.blt imm M with
  | false => AbsVal.bot
  | true =>
    reduceAbsVal w
      ⟨.init,
       Tnum.add w a.tnum (Tnum.const w imm),
       WrappedInterval.add M a.wi (WrappedInterval.const M imm),
       StridedCong.addConst M a.sc imm⟩

/-- Soundness of `AbsVal.addConstWrap`. -/
theorem absVal_addConstWrap_sound {w x imm : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hImm : imm < modPow2 w) :
    (AbsVal.addConstWrap w a imm).denote w (some (wrapVal w (x + imm))) := by
  dsimp only [AbsVal.addConstWrap]
  rw [hw, hai, blt_true_of_lt hImm]
  apply reduceAbsVal_sound hw
  have hM : 0 < modPow2 w := modPow2_pos w
  have haE := absVal_some_elim ha
  have hc : (AbsVal.const w imm).denote w (some (wrapVal w imm)) := absVal_const_sound hw
  have hcE := absVal_some_elim hc
  have hImmMod : wrapVal w imm = imm := nat_mod_eq_of_lt hImm
  rw [hImmMod] at hcE
  dsimp only [AbsVal.const, wrapVal] at hcE
  have hImmModRaw : Nat.mod imm (modPow2 w) = imm := nat_mod_eq_of_lt hImm
  rw [hw, hImmModRaw] at hcE
  dsimp only at hcE
  have hWrapLt : wrapVal w (x + imm) < modPow2 w := nat_mod_lt (x + imm) hM
  dsimp only [AbsVal.denote]
  refine ⟨⟨wrapVal w (x + imm), rfl, hWrapLt⟩, ?_, ?_, ?_⟩
  · exact tnum_add_sound haE.2.1 hcE.2.1
  · exact wrappedInterval_add_sound hM haE.2.2.1 hcE.2.2.1
  · exact stridedCong_addConst_sound haE.2.2.2

/-- Modular `w`-bit constant-subtraction transfer on `AbsVal`. -/
@[expose] def AbsVal.subConstWrap (w : Nat) (a : AbsVal) (imm : Nat) : AbsVal :=
  let M := modPow2 w
  match validWidth w && a.isInit && Nat.blt imm M with
  | false => AbsVal.bot
  | true =>
    reduceAbsVal w
      ⟨.init,
       Tnum.sub w a.tnum (Tnum.const w imm),
       WrappedInterval.sub M a.wi (WrappedInterval.const M imm),
       StridedCong.subConst M a.sc imm⟩

/-- Soundness of `AbsVal.subConstWrap`. -/
theorem absVal_subConstWrap_sound {w x imm : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hImm : imm < modPow2 w) :
    (AbsVal.subConstWrap w a imm).denote w (some (wrapVal w (modPow2 w + x - imm))) := by
  dsimp only [AbsVal.subConstWrap]
  rw [hw, hai, blt_true_of_lt hImm]
  apply reduceAbsVal_sound hw
  have hM : 0 < modPow2 w := modPow2_pos w
  have haE := absVal_some_elim ha
  have hc : (AbsVal.const w imm).denote w (some (wrapVal w imm)) := absVal_const_sound hw
  have hcE := absVal_some_elim hc
  have hImmMod : wrapVal w imm = imm := nat_mod_eq_of_lt hImm
  rw [hImmMod] at hcE
  dsimp only [AbsVal.const, wrapVal] at hcE
  have hImmModRaw : Nat.mod imm (modPow2 w) = imm := nat_mod_eq_of_lt hImm
  rw [hw, hImmModRaw] at hcE
  dsimp only at hcE
  have hWrapLt : wrapVal w (modPow2 w + x - imm) < modPow2 w := nat_mod_lt _ hM
  dsimp only [AbsVal.denote]
  refine ⟨⟨wrapVal w (modPow2 w + x - imm), rfl, hWrapLt⟩, ?_, ?_, ?_⟩
  · exact tnum_sub_sound haE.2.1 hcE.2.1 hImm
  · exact wrappedInterval_sub_sound hM haE.2.2.1 hcE.2.2.1
  · exact stridedCong_subConst_sound haE.2.2.2 hImm

/-- Refines `a` under unsigned branch condition `x ≤ bound`. -/
@[expose] def AbsVal.refineUleConst (w : Nat) (a : AbsVal) (bound : Nat) :
    AbsVal :=
  match validWidth w && a.isInit with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    match Nat.blt bound M with
    | false => a
    | true =>
      reduceAbsVal w ⟨.init, a.tnum, WrappedInterval.meet M a.wi (.iv 0 bound), a.sc⟩

/-- Soundness of `AbsVal.refineUleConst`. -/
theorem absVal_refineUleConst_sound {w x bound : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hBle : x ≤ bound) :
    (AbsVal.refineUleConst w a bound).denote w (some x) := by
  dsimp only [AbsVal.refineUleConst]
  rw [hw, hai]
  cases hB : Nat.blt bound (modPow2 w) with
  | false => exact ha
  | true =>
    dsimp only
    apply reduceAbsVal_sound hw
    have haE := absVal_some_elim ha
    have hBoundLt : bound < modPow2 w := lt_of_blt_true hB
    have hIv : WrappedInterval.denote (modPow2 w) (.iv 0 bound) x :=
      wrapped_denote_iv_of_le (modPow2_pos w) hBoundLt (Nat.zero_le bound) (Nat.zero_le x) hBle
    exact ⟨⟨x, rfl, haE.1⟩, haE.2.1,
      wrappedInterval_meet_sound (modPow2_pos w) haE.2.2.1 hIv, haE.2.2.2⟩

/-- Refines `a` under unsigned branch condition `bound < x`. -/
@[expose] def AbsVal.refineUgtConst (w : Nat) (a : AbsVal) (bound : Nat) :
    AbsVal :=
  match validWidth w && a.isInit with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    match Nat.blt (bound + 1) M with
    | false => AbsVal.bot
    | true =>
      reduceAbsVal w ⟨.init, a.tnum, WrappedInterval.meet M a.wi (.iv (bound + 1) (M - 1)), a.sc⟩

/-- Soundness of `AbsVal.refineUgtConst`. -/
theorem absVal_refineUgtConst_sound {w x bound : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hGt : bound < x) :
    (AbsVal.refineUgtConst w a bound).denote w (some x) := by
  dsimp only [AbsVal.refineUgtConst]
  rw [hw, hai]
  have haE := absVal_some_elim ha
  have hM : 0 < modPow2 w := modPow2_pos w
  cases hB : Nat.blt (bound + 1) (modPow2 w) with
  | false =>
    have hGe : modPow2 w ≤ bound + 1 :=
      Nat.le_of_not_lt (fun h => by rw [blt_true_of_lt h] at hB; nomatch hB)
    exact False.elim (Nat.not_le_of_gt haE.1 (Nat.le_trans hGe hGt))
  | true =>
    dsimp only
    apply reduceAbsVal_sound hw
    have hLoLt : bound + 1 < modPow2 w := lt_of_blt_true hB
    have hHiLt : modPow2 w - 1 < modPow2 w := Nat.sub_lt hM (Nat.zero_lt_succ 0)
    have hSub1 : ∀ u v : Nat, u < v → u ≤ v - 1 := fun u v h => by
      have h1 := Nat.sub_le_sub_right h 1
      rw [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h1; exact h1
    have hLe : bound + 1 ≤ modPow2 w - 1 := hSub1 _ _ hLoLt
    have hxHi : x ≤ modPow2 w - 1 := hSub1 _ _ haE.1
    have hIv : WrappedInterval.denote (modPow2 w) (.iv (bound + 1) (modPow2 w - 1)) x :=
      wrapped_denote_iv_of_le hLoLt hHiLt hLe hGt hxHi
    exact ⟨⟨x, rfl, haE.1⟩, haE.2.1, wrappedInterval_meet_sound hM haE.2.2.1 hIv, haE.2.2.2⟩

/-- Refines `a` under unsigned register comparison `x < y`. -/
@[expose] def AbsVal.refineBltReg (w : Nat) (a b : AbsVal) : AbsVal :=
  match validWidth w && a.isInit && b.isInit with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    match b.wi with
    | .iv lo2 hi2 =>
      match Nat.ble lo2 hi2 && Nat.blt hi2 M with
      | false => a
      | true =>
        match hi2 with
        | 0 => AbsVal.bot
        | h' + 1 =>
          reduceAbsVal w ⟨.init, a.tnum, WrappedInterval.meet M a.wi (.iv 0 h'), a.sc⟩
    | _ => a

/-- Soundness of `AbsVal.refineBltReg`. -/
theorem absVal_refineBltReg_sound {w x y : Nat} {a b : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hb : b.denote w (some y))
    (hai : a.isInit = true) (hbi : b.isInit = true) (hLt : x < y) :
    (AbsVal.refineBltReg w a b).denote w (some x) := by
  dsimp only [AbsVal.refineBltReg]
  rw [hw, hai, hbi]
  have haE := absVal_some_elim ha
  have hbE := absVal_some_elim hb
  have hM : 0 < modPow2 w := modPow2_pos w
  cases hWiB : b.wi with
  | bot => exact ha
  | top => exact ha
  | iv lo2 hi2 =>
    dsimp only
    have hWib := hbE.2.2.1
    rw [hWiB] at hWib
    cases hCheck : Nat.ble lo2 hi2 && Nat.blt hi2 (modPow2 w) with
    | false => exact ha
    | true =>
      dsimp only
      have hBle := bool_and_true_left hCheck
      have hHiLt := lt_of_blt_true (bool_and_true_right hCheck)
      dsimp only [WrappedInterval.denote] at hWib
      rw [hBle] at hWib
      have hyHi : y ≤ hi2 := hWib.2.2.2.2
      cases hi2 with
      | zero => exact False.elim (Nat.not_lt_zero x (Nat.lt_of_lt_of_le hLt hyHi))
      | succ h' =>
        dsimp only
        apply reduceAbsVal_sound hw
        have hxLe : x ≤ h' := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hyHi)
        have h'Lt : h' < modPow2 w := Nat.lt_trans (Nat.lt_succ_self h') hHiLt
        have hIv := wrapped_denote_iv_of_le hM h'Lt (Nat.zero_le h') (Nat.zero_le x) hxLe
        exact ⟨⟨x, rfl, haE.1⟩, haE.2.1, wrappedInterval_meet_sound hM haE.2.2.1 hIv, haE.2.2.2⟩

/-- Refines `a` under unsigned register comparison `y ≤ x`. -/
@[expose] def AbsVal.refineBgeReg (w : Nat) (a b : AbsVal) : AbsVal :=
  match validWidth w && a.isInit && b.isInit with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    match b.wi with
    | .iv lo2 hi2 =>
      match Nat.ble lo2 hi2 && Nat.blt lo2 M with
      | false => a
      | true =>
        reduceAbsVal w ⟨.init, a.tnum, WrappedInterval.meet M a.wi (.iv lo2 (M - 1)), a.sc⟩
    | _ => a

/-- Soundness of `AbsVal.refineBgeReg`. -/
theorem absVal_refineBgeReg_sound {w x y : Nat} {a b : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hb : b.denote w (some y))
    (hai : a.isInit = true) (hbi : b.isInit = true) (hGe : y ≤ x) :
    (AbsVal.refineBgeReg w a b).denote w (some x) := by
  dsimp only [AbsVal.refineBgeReg]
  rw [hw, hai, hbi]
  have haE := absVal_some_elim ha
  have hbE := absVal_some_elim hb
  have hM : 0 < modPow2 w := modPow2_pos w
  cases hWiB : b.wi with
  | bot => exact ha
  | top => exact ha
  | iv lo2 hi2 =>
    dsimp only
    have hWib := hbE.2.2.1
    rw [hWiB] at hWib
    cases hCheck : Nat.ble lo2 hi2 && Nat.blt lo2 (modPow2 w) with
    | false => exact ha
    | true =>
      dsimp only
      apply reduceAbsVal_sound hw
      have hBle := bool_and_true_left hCheck
      have hLoLt := lt_of_blt_true (bool_and_true_right hCheck)
      dsimp only [WrappedInterval.denote] at hWib
      rw [hBle] at hWib
      have hSub1 : ∀ u v : Nat, u < v → u ≤ v - 1 := fun u v h => by
        have h1 := Nat.sub_le_sub_right h 1
        rw [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h1; exact h1
      have hHiLt := Nat.sub_lt hM (Nat.zero_lt_succ 0)
      have hLoLe : lo2 ≤ modPow2 w - 1 := hSub1 _ _ hLoLt
      have hxHi : x ≤ modPow2 w - 1 := hSub1 _ _ haE.1
      have hLoX : lo2 ≤ x := Nat.le_trans hWib.2.2.2.1 hGe
      have hIv := wrapped_denote_iv_of_le hLoLt hHiLt hLoLe hLoX hxHi
      dsimp only [AbsVal.denote, InitDom.denote]
      exact ⟨⟨x, rfl, haE.1⟩, haE.2.1, wrappedInterval_meet_sound hM haE.2.2.1 hIv, haE.2.2.2⟩

/-! ### Additional Unsigned Arithmetic, Bitwise, Shift, and Cmp Transfers -/

private theorem land_lt_modPow2 {w x y : Nat}
    (hx : x < modPow2 w) : Nat.land x y < modPow2 w :=
  lt_modPow2_of_bitAt_zero (fun k hk => by
    rw [bitAt_land, bitAt_zero_ge_of_lt_modPow2 hx k hk]; rfl)

private theorem lor_lt_modPow2 {w x y : Nat}
    (hx : x < modPow2 w) (hy : y < modPow2 w) : Nat.lor x y < modPow2 w :=
  lt_modPow2_of_bitAt_zero (fun k hk => by
    rw [bitAt_lor, bitAt_zero_ge_of_lt_modPow2 hx k hk,
        bitAt_zero_ge_of_lt_modPow2 hy k hk]; rfl)

private theorem xor_lt_modPow2 {w x y : Nat}
    (hx : x < modPow2 w) (hy : y < modPow2 w) : Nat.xor x y < modPow2 w :=
  lt_modPow2_of_bitAt_zero (fun k hk => by
    rw [bitAt_xor, bitAt_zero_ge_of_lt_modPow2 hx k hk,
        bitAt_zero_ge_of_lt_modPow2 hy k hk]; rfl)

private theorem shiftRight_lt_modPow2 {w x s : Nat}
    (hx : x < modPow2 w) : Nat.shiftRight x s < modPow2 w :=
  lt_modPow2_of_bitAt_zero (fun k hk => by
    rw [bitAt_shiftRight]
    exact bitAt_zero_ge_of_lt_modPow2 hx (k + s)
      (Nat.le_trans hk (Nat.le_add_right k s)))

/-- Extracts a singleton concrete value when `a` is initialized and either
`a.wi = .iv lo hi` with `lo = hi` or `a.tnum.mask = 0`. -/
@[expose] def AbsVal.exactVal? (w : Nat) (a : AbsVal) : Option Nat :=
  match validWidth w, a.init with
  | true, .init =>
    if Nat.beq a.tnum.mask 0 && Nat.blt a.tnum.val (modPow2 w) then
      some a.tnum.val
    else
      match a.wi with
      | .iv lo hi =>
        if Nat.beq lo hi && Nat.blt lo (modPow2 w) then some lo else none
      | _ => none
  | _, _ => none

/-- Soundness of `AbsVal.exactVal?`: every concrete denotation equals `c`. -/
theorem absVal_exactVal?_sound {w c : Nat} {a : AbsVal} {opt : Option Nat}
    (hEx : a.exactVal? w = some c) (ha : a.denote w opt) :
    opt = some c ∧ c < modPow2 w := by
  dsimp only [AbsVal.exactVal?] at hEx
  cases hw : validWidth w with
  | false => rw [hw] at hEx; nomatch hEx
  | true =>
    cases hai : a.init with
    | bot => rw [hw, hai] at hEx; nomatch hEx
    | uninit => rw [hw, hai] at hEx; nomatch hEx
    | init =>
      rw [hw, hai] at hEx
      dsimp only at hEx
      have hIsInit : a.isInit = true := by dsimp only [AbsVal.isInit]; rw [hai]
      have hInit := absVal_init_of_isInit hIsInit ha
      cases hInit with
      | intro x hx =>
        cases hTm : Nat.beq a.tnum.mask 0 && Nat.blt a.tnum.val (modPow2 w) with
        | true =>
          rw [hTm] at hEx
          injection hEx with hC
          subst hC
          have hM0 := Nat.eq_of_beq_eq_true (bool_and_true_left hTm)
          have hVLt := lt_of_blt_true (bool_and_true_right hTm)
          have hTd := hx.2.2.1
          rw [tnum_denote_iff_bitAt] at hTd
          have hxEq : x = a.tnum.val := by
            apply nat_eq_of_bitAt; intro k
            apply hTd.2 k
            rw [hM0, bitAt_zero_nat]
          rw [hxEq] at hx
          exact ⟨hx.1, hVLt⟩
        | false =>
          rw [hTm] at hEx
          cases hWi : a.wi with
          | bot => rw [hWi] at hEx; nomatch hEx
          | top => rw [hWi] at hEx; nomatch hEx
          | iv lo hi =>
            rw [hWi] at hEx
            dsimp only at hEx
            cases hEq : Nat.beq lo hi && Nat.blt lo (modPow2 w) with
            | false => rw [hEq] at hEx; nomatch hEx
            | true =>
              rw [hEq] at hEx
              injection hEx with hC
              subst hC
              have hLoHi := Nat.eq_of_beq_eq_true (bool_and_true_left hEq)
              have hLoLt := lt_of_blt_true (bool_and_true_right hEq)
              have hWix := hx.2.2.2.1
              rw [hWi, ← hLoHi] at hWix
              dsimp only [WrappedInterval.denote] at hWix
              rw [Nat.ble_eq_true_of_le (Nat.le_refl lo)] at hWix
              have hxEq : x = lo := Nat.le_antisymm hWix.2.2.2.2 hWix.2.2.2.1
              rw [hxEq] at hx
              exact ⟨hx.1, hLoLt⟩

/-- Sufficient check guaranteeing unsigned subtraction `x - y` never underflows
(`y ≤ x`). -/
@[expose] def AbsVal.noUnderflowSub (w : Nat) (a b : AbsVal) : Bool :=
  match validWidth w, a.init, b.init, a.wi, b.wi with
  | true, .init, .init, .iv lo1 hi1, .iv lo2 hi2 =>
    Nat.ble lo1 hi1 && Nat.ble lo2 hi2 && Nat.ble hi2 lo1
  | _, _, _, _, _ => false

/-- Soundness of `AbsVal.noUnderflowSub`. -/
theorem absVal_noUnderflowSub_sound {w : Nat} {a b : AbsVal}
    {optA optB : Option Nat}
    (hOk : AbsVal.noUnderflowSub w a b = true)
    (ha : a.denote w optA) (hb : b.denote w optB) :
    ∃ x y : Nat, optA = some x ∧ optB = some y ∧ y ≤ x ∧
      a.denote w (some x) ∧ b.denote w (some y) := by
  dsimp only [AbsVal.noUnderflowSub] at hOk
  cases hw : validWidth w with
  | false => rw [hw] at hOk; nomatch hOk
  | true =>
    cases hai : a.init with
    | bot => rw [hw, hai] at hOk; nomatch hOk
    | uninit => rw [hw, hai] at hOk; nomatch hOk
    | init =>
      cases hbi : b.init with
      | bot => rw [hw, hai, hbi] at hOk; nomatch hOk
      | uninit => rw [hw, hai, hbi] at hOk; nomatch hOk
      | init =>
        have hExA := absVal_init_of_isInit (by dsimp only [AbsVal.isInit]; rw [hai]) ha
        have hExB := absVal_init_of_isInit (by dsimp only [AbsVal.isInit]; rw [hbi]) hb
        cases hExA with
        | intro x hx =>
          cases hExB with
          | intro y hy =>
            cases hWia : a.wi with
            | bot => rw [hw, hai, hbi, hWia] at hOk; nomatch hOk
            | top => rw [hw, hai, hbi, hWia] at hOk; nomatch hOk
            | iv lo1 hi1 =>
              cases hWib : b.wi with
              | bot => rw [hw, hai, hbi, hWia, hWib] at hOk; nomatch hOk
              | top => rw [hw, hai, hbi, hWia, hWib] at hOk; nomatch hOk
              | iv lo2 hi2 =>
                rw [hw, hai, hbi, hWia, hWib] at hOk
                dsimp only at hOk
                have h12 := bool_and_true_left hOk
                have hLe1 := Nat.le_of_ble_eq_true (bool_and_true_left h12)
                have hLe2 := Nat.le_of_ble_eq_true (bool_and_true_right h12)
                have hHi2Lo1 := Nat.le_of_ble_eq_true (bool_and_true_right hOk)
                have hWix := hx.2.2.2.1; rw [hWia] at hWix
                dsimp only [WrappedInterval.denote] at hWix
                rw [Nat.ble_eq_true_of_le hLe1] at hWix
                have hWiy := hy.2.2.2.1; rw [hWib] at hWiy
                dsimp only [WrappedInterval.denote] at hWiy
                rw [Nat.ble_eq_true_of_le hLe2] at hWiy
                have hyx : y ≤ x :=
                  Nat.le_trans hWiy.2.2.2.2 (Nat.le_trans hHi2Lo1 hWix.2.2.2.1)
                exact ⟨x, y, hx.1, hy.1, hyx,
                  by rw [← hx.1]; exact ha, by rw [← hy.1]; exact hb⟩

/-- Sufficient check guaranteeing an unsigned shift amount `y < w`. -/
@[expose] def AbsVal.shiftInBounds (w rhsW : Nat) (b : AbsVal) : Bool :=
  match validWidth w, validWidth rhsW, b.init, b.wi with
  | true, true, .init, .iv lo hi => Nat.ble lo hi && Nat.blt hi w
  | _, _, _, _ => false

/-- Soundness of `AbsVal.shiftInBounds`. -/
theorem absVal_shiftInBounds_sound {w rhsW : Nat} {b : AbsVal} {opt : Option Nat}
    (hOk : AbsVal.shiftInBounds w rhsW b = true) (hb : b.denote rhsW opt) :
    ∃ y : Nat, opt = some y ∧ y < w ∧ b.denote rhsW (some y) := by
  dsimp only [AbsVal.shiftInBounds] at hOk
  cases hw : validWidth w with
  | false => rw [hw] at hOk; nomatch hOk
  | true =>
    cases hrw : validWidth rhsW with
    | false => rw [hw, hrw] at hOk; nomatch hOk
    | true =>
      cases hbi : b.init with
      | bot => rw [hw, hrw, hbi] at hOk; nomatch hOk
      | uninit => rw [hw, hrw, hbi] at hOk; nomatch hOk
      | init =>
        have hEx := absVal_init_of_isInit (by dsimp only [AbsVal.isInit]; rw [hbi]) hb
        cases hEx with
        | intro y hy =>
          cases hWi : b.wi with
          | bot => rw [hw, hrw, hbi, hWi] at hOk; nomatch hOk
          | top => rw [hw, hrw, hbi, hWi] at hOk; nomatch hOk
          | iv lo hi =>
            rw [hw, hrw, hbi, hWi] at hOk
            dsimp only at hOk
            have hLe := Nat.le_of_ble_eq_true (bool_and_true_left hOk)
            have hHiLt := lt_of_blt_true (bool_and_true_right hOk)
            have hWiy := hy.2.2.2.1; rw [hWi] at hWiy
            dsimp only [WrappedInterval.denote] at hWiy
            rw [Nat.ble_eq_true_of_le hLe] at hWiy
            have hyLt : y < w := Nat.lt_of_le_of_lt hWiy.2.2.2.2 hHiLt
            exact ⟨y, hy.1, hyLt, by rw [← hy.1]; exact hb⟩

/-- Sufficient check guaranteeing a divisor is strictly positive (`0 < y`). -/
@[expose] def AbsVal.nonzeroDiv (w : Nat) (b : AbsVal) : Bool :=
  match validWidth w, b.init, b.wi with
  | true, .init, .iv lo hi => Nat.ble 1 lo && Nat.ble lo hi
  | _, _, _ => false

/-- Soundness of `AbsVal.nonzeroDiv`. -/
theorem absVal_nonzeroDiv_sound {w : Nat} {b : AbsVal} {opt : Option Nat}
    (hOk : AbsVal.nonzeroDiv w b = true) (hb : b.denote w opt) :
    ∃ y : Nat, opt = some y ∧ 0 < y ∧ b.denote w (some y) := by
  dsimp only [AbsVal.nonzeroDiv] at hOk
  cases hw : validWidth w with
  | false => rw [hw] at hOk; nomatch hOk
  | true =>
    cases hbi : b.init with
    | bot => rw [hw, hbi] at hOk; nomatch hOk
    | uninit => rw [hw, hbi] at hOk; nomatch hOk
    | init =>
      have hEx := absVal_init_of_isInit (by dsimp only [AbsVal.isInit]; rw [hbi]) hb
      cases hEx with
      | intro y hy =>
        cases hWi : b.wi with
        | bot => rw [hw, hbi, hWi] at hOk; nomatch hOk
        | top => rw [hw, hbi, hWi] at hOk; nomatch hOk
        | iv lo hi =>
          rw [hw, hbi, hWi] at hOk
          dsimp only at hOk
          have h1Lo := Nat.le_of_ble_eq_true (bool_and_true_left hOk)
          have hLe := Nat.le_of_ble_eq_true (bool_and_true_right hOk)
          have hWiy := hy.2.2.2.1; rw [hWi] at hWiy
          dsimp only [WrappedInterval.denote] at hWiy
          rw [Nat.ble_eq_true_of_le hLe] at hWiy
          have hyPos : 0 < y := Nat.lt_of_lt_of_le h1Lo hWiy.2.2.2.1
          exact ⟨y, hy.1, hyPos, by rw [← hy.1]; exact hb⟩

/-- Modular subtraction transfer on `AbsVal`. -/
@[expose] def AbsVal.subWrap (w : Nat) (a b : AbsVal) : AbsVal :=
  match validWidth w && a.isInit && b.isInit with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    reduceAbsVal w
      ⟨.init,
       Tnum.sub w a.tnum b.tnum,
       WrappedInterval.sub M a.wi b.wi,
       StridedCong.wrapSub M a.sc b.sc⟩

/-- Soundness of `AbsVal.subWrap`. -/
theorem absVal_subWrap_sound {w x y : Nat} {a b : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hb : b.denote w (some y))
    (hai : a.isInit = true) (hbi : b.isInit = true) :
    (AbsVal.subWrap w a b).denote w (some (wrapVal w (modPow2 w + x - y))) := by
  dsimp only [AbsVal.subWrap]
  rw [hw, hai, hbi]
  apply reduceAbsVal_sound hw
  have hM : 0 < modPow2 w := modPow2_pos w
  have haE := absVal_some_elim ha
  have hbE := absVal_some_elim hb
  have hWrapLt : wrapVal w (modPow2 w + x - y) < modPow2 w := nat_mod_lt _ hM
  dsimp only [AbsVal.denote]
  refine ⟨⟨wrapVal w (modPow2 w + x - y), rfl, hWrapLt⟩, ?_, ?_, ?_⟩
  · exact tnum_sub_sound haE.2.1 hbE.2.1 hbE.1
  · exact wrappedInterval_sub_sound hM haE.2.2.1 hbE.2.2.1
  · exact stridedCong_wrapSub_sound haE.2.2.2 hbE.2.2.2 hbE.1

/-- Bitwise AND transfer on `AbsVal` (automatically propagating known-bit bounds
and alignment into `WrappedInterval` and `StridedCong` via `reduceAbsVal`). -/
@[expose] def AbsVal.bitAnd (w : Nat) (a b : AbsVal) : AbsVal :=
  match validWidth w && a.isInit && b.isInit with
  | false => AbsVal.bot
  | true =>
    reduceAbsVal w ⟨.init, Tnum.bitwiseAnd a.tnum b.tnum, .top, .top⟩

/-- Soundness of `AbsVal.bitAnd`. -/
theorem absVal_bitAnd_sound {w x y : Nat} {a b : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hb : b.denote w (some y))
    (hai : a.isInit = true) (hbi : b.isInit = true) :
    (AbsVal.bitAnd w a b).denote w (some (Nat.land x y)) := by
  dsimp only [AbsVal.bitAnd]
  rw [hw, hai, hbi]
  apply reduceAbsVal_sound hw
  have haE := absVal_some_elim ha
  have hbE := absVal_some_elim hb
  have hLt : Nat.land x y < modPow2 w := land_lt_modPow2 haE.1
  dsimp only [AbsVal.denote, WrappedInterval.denote, StridedCong.denote]
  exact ⟨⟨Nat.land x y, rfl, hLt⟩, tnum_bitwiseAnd_sound haE.2.1 hbE.2.1, hLt, True.intro⟩

/-- Bitwise OR transfer on `AbsVal`. -/
@[expose] def AbsVal.bitOr (w : Nat) (a b : AbsVal) : AbsVal :=
  match validWidth w && a.isInit && b.isInit with
  | false => AbsVal.bot
  | true =>
    reduceAbsVal w ⟨.init, Tnum.bitwiseOr a.tnum b.tnum, .top, .top⟩

/-- Soundness of `AbsVal.bitOr`. -/
theorem absVal_bitOr_sound {w x y : Nat} {a b : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hb : b.denote w (some y))
    (hai : a.isInit = true) (hbi : b.isInit = true) :
    (AbsVal.bitOr w a b).denote w (some (Nat.lor x y)) := by
  dsimp only [AbsVal.bitOr]
  rw [hw, hai, hbi]
  apply reduceAbsVal_sound hw
  have haE := absVal_some_elim ha
  have hbE := absVal_some_elim hb
  have hLt : Nat.lor x y < modPow2 w := lor_lt_modPow2 haE.1 hbE.1
  dsimp only [AbsVal.denote, WrappedInterval.denote, StridedCong.denote]
  exact ⟨⟨Nat.lor x y, rfl, hLt⟩, tnum_bitwiseOr_sound haE.2.1 hbE.2.1, hLt, True.intro⟩

/-- Bitwise XOR transfer on `AbsVal`. -/
@[expose] def AbsVal.bitXor (w : Nat) (a b : AbsVal) : AbsVal :=
  match validWidth w && a.isInit && b.isInit with
  | false => AbsVal.bot
  | true =>
    reduceAbsVal w ⟨.init, Tnum.bitwiseXor a.tnum b.tnum, .top, .top⟩

/-- Soundness of `AbsVal.bitXor`. -/
theorem absVal_bitXor_sound {w x y : Nat} {a b : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hb : b.denote w (some y))
    (hai : a.isInit = true) (hbi : b.isInit = true) :
    (AbsVal.bitXor w a b).denote w (some (Nat.xor x y)) := by
  dsimp only [AbsVal.bitXor]
  rw [hw, hai, hbi]
  apply reduceAbsVal_sound hw
  have haE := absVal_some_elim ha
  have hbE := absVal_some_elim hb
  have hLt : Nat.xor x y < modPow2 w := xor_lt_modPow2 haE.1 hbE.1
  dsimp only [AbsVal.denote, WrappedInterval.denote, StridedCong.denote]
  exact ⟨⟨Nat.xor x y, rfl, hLt⟩, tnum_bitwiseXor_sound haE.2.1 hbE.2.1, hLt, True.intro⟩

/-- Constant-amount left-shift transfer on `AbsVal`. -/
@[expose] def AbsVal.shlConst (w s : Nat) (a : AbsVal) : AbsVal :=
  match validWidth w && a.isInit with
  | false => AbsVal.bot
  | true =>
    reduceAbsVal w ⟨.init, Tnum.shl w s a.tnum, .top, .top⟩

/-- Soundness of `AbsVal.shlConst`. -/
theorem absVal_shlConst_sound {w s x : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true) :
    (AbsVal.shlConst w s a).denote w (some (wrapVal w (Nat.shiftLeft x s))) := by
  dsimp only [AbsVal.shlConst]
  rw [hw, hai]
  apply reduceAbsVal_sound hw
  have haE := absVal_some_elim ha
  have hLt : wrapVal w (Nat.shiftLeft x s) < modPow2 w := nat_mod_lt _ (modPow2_pos w)
  dsimp only [AbsVal.denote, WrappedInterval.denote, StridedCong.denote]
  exact ⟨⟨wrapVal w (Nat.shiftLeft x s), rfl, hLt⟩, tnum_shl_sound haE.2.1, hLt, True.intro⟩

/-- Constant-amount logical right-shift transfer on `AbsVal`. -/
@[expose] def AbsVal.shrConst (w s : Nat) (a : AbsVal) : AbsVal :=
  match validWidth w && a.isInit with
  | false => AbsVal.bot
  | true =>
    reduceAbsVal w ⟨.init, Tnum.shr s a.tnum, .top, .top⟩

/-- Soundness of `AbsVal.shrConst`. -/
theorem absVal_shrConst_sound {w s x : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true) :
    (AbsVal.shrConst w s a).denote w (some (Nat.shiftRight x s)) := by
  dsimp only [AbsVal.shrConst]
  rw [hw, hai]
  apply reduceAbsVal_sound hw
  have haE := absVal_some_elim ha
  have hLt : Nat.shiftRight x s < modPow2 w := shiftRight_lt_modPow2 haE.1
  dsimp only [AbsVal.denote, WrappedInterval.denote, StridedCong.denote]
  exact ⟨⟨Nat.shiftRight x s, rfl, hLt⟩, tnum_shr_sound haE.2.1, hLt, True.intro⟩

/-- Refines `a` under the guard `x = c`. -/
@[expose] def AbsVal.refineEqConst (w : Nat) (a : AbsVal) (c : Nat) : AbsVal :=
  match validWidth w && a.isInit && Nat.blt c (modPow2 w) with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    match Tnum.meet a.tnum (Tnum.const w c) with
    | none => AbsVal.bot
    | some tm =>
      reduceAbsVal w ⟨.init, tm, WrappedInterval.meet M a.wi (.iv c c), a.sc⟩

/-- Soundness of `AbsVal.refineEqConst`. -/
theorem absVal_refineEqConst_sound {w x c : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hEq : x = c) :
    (AbsVal.refineEqConst w a c).denote w (some x) := by
  subst hEq
  have haE := absVal_some_elim ha
  dsimp only [AbsVal.refineEqConst]
  rw [hw, hai, blt_true_of_lt haE.1]
  have hTc : (Tnum.const w x).denote x := tnum_const_sound haE.1
  cases hM : Tnum.meet a.tnum (Tnum.const w x) with
  | none => exact False.elim (tnum_meet_none_impossible haE.2.1 hTc hM)
  | some tm =>
    dsimp only
    apply reduceAbsVal_sound hw
    have hIv : WrappedInterval.denote (modPow2 w) (.iv x x) x :=
      wrapped_denote_iv_of_le haE.1 haE.1 (Nat.le_refl x) (Nat.le_refl x) (Nat.le_refl x)
    exact ⟨⟨x, rfl, haE.1⟩, tnum_meet_sound haE.2.1 hTc hM,
           wrappedInterval_meet_sound (modPow2_pos w) haE.2.2.1 hIv, haE.2.2.2⟩

/-- Decides `x = y` (`some true` or `some false`) when `a` and `b` force it. -/
@[expose] def AbsVal.decideEq? (w : Nat) (a b : AbsVal) : Option Bool :=
  match a.exactVal? w, b.exactVal? w with
  | some x, some y => some (Nat.beq x y)
  | _, _ =>
    match validWidth w && a.isInit && b.isInit with
    | false => none
    | true =>
      match Tnum.meet a.tnum b.tnum with
      | none => some false
      | some _ =>
        match WrappedInterval.meet (modPow2 w) a.wi b.wi with
        | .bot => some false
        | _ => none

/-- Soundness of `AbsVal.decideEq?`. -/
theorem absVal_decideEq?_sound {w x y : Nat} {a b : AbsVal} {r : Bool}
    (hDec : AbsVal.decideEq? w a b = some r)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    Nat.beq x y = r := by
  dsimp only [AbsVal.decideEq?] at hDec
  cases hExA : a.exactVal? w with
  | some cx =>
    cases hExB : b.exactVal? w with
    | some cy =>
      rw [hExA, hExB] at hDec
      injection hDec with hR
      have hAx := absVal_exactVal?_sound hExA ha
      have hBy := absVal_exactVal?_sound hExB hb
      injection hAx.1 with hxEq
      injection hBy.1 with hyEq
      rw [hxEq, hyEq, hR]
    | none =>
      rw [hExA, hExB] at hDec
      dsimp only at hDec
      cases hCond : validWidth w && a.isInit && b.isInit with
      | false => rw [hCond] at hDec; nomatch hDec
      | true =>
        rw [hCond] at hDec
        dsimp only at hDec
        have haE := absVal_some_elim ha
        have hbE := absVal_some_elim hb
        cases hTm : Tnum.meet a.tnum b.tnum with
        | none =>
          rw [hTm] at hDec
          injection hDec with hR
          rw [← hR]
          cases hEq : Nat.beq x y with
          | false => rfl
          | true =>
            have hxy := Nat.eq_of_beq_eq_true hEq
            subst hxy
            exact False.elim (tnum_meet_none_impossible haE.2.1 hbE.2.1 hTm)
        | some tm =>
          rw [hTm] at hDec
          cases hWm : WrappedInterval.meet (modPow2 w) a.wi b.wi with
          | bot =>
            rw [hWm] at hDec
            injection hDec with hR
            rw [← hR]
            cases hEq : Nat.beq x y with
            | false => rfl
            | true =>
              have hxy := Nat.eq_of_beq_eq_true hEq
              subst hxy
              have hBot := wrappedInterval_meet_sound (modPow2_pos w) haE.2.2.1 hbE.2.2.1
              rw [hWm] at hBot
              exact False.elim hBot
          | top => rw [hWm] at hDec; nomatch hDec
          | iv _ _ => rw [hWm] at hDec; nomatch hDec
  | none =>
    rw [hExA] at hDec
    dsimp only at hDec
    cases hCond : validWidth w && a.isInit && b.isInit with
    | false => rw [hCond] at hDec; nomatch hDec
    | true =>
      rw [hCond] at hDec
      dsimp only at hDec
      have haE := absVal_some_elim ha
      have hbE := absVal_some_elim hb
      cases hTm : Tnum.meet a.tnum b.tnum with
      | none =>
        rw [hTm] at hDec
        injection hDec with hR
        rw [← hR]
        cases hEq : Nat.beq x y with
        | false => rfl
        | true =>
          have hxy := Nat.eq_of_beq_eq_true hEq
          subst hxy
          exact False.elim (tnum_meet_none_impossible haE.2.1 hbE.2.1 hTm)
      | some tm =>
        rw [hTm] at hDec
        cases hWm : WrappedInterval.meet (modPow2 w) a.wi b.wi with
        | bot =>
          rw [hWm] at hDec
          injection hDec with hR
          rw [← hR]
          cases hEq : Nat.beq x y with
          | false => rfl
          | true =>
            have hxy := Nat.eq_of_beq_eq_true hEq
            subst hxy
            have hBot := wrappedInterval_meet_sound (modPow2_pos w) haE.2.2.1 hbE.2.2.1
            rw [hWm] at hBot
            exact False.elim hBot
        | top => rw [hWm] at hDec; nomatch hDec
        | iv _ _ => rw [hWm] at hDec; nomatch hDec

/-- Decides `x ≤ y` when non-wrapping intervals of `a` and `b` separate them. -/
@[expose] def AbsVal.decideLe? (w : Nat) (a b : AbsVal) : Option Bool :=
  match validWidth w, a.init, b.init, a.wi, b.wi with
  | true, .init, .init, .iv lo1 hi1, .iv lo2 hi2 =>
    if Nat.ble lo1 hi1 && Nat.ble lo2 hi2 then
      if Nat.ble hi1 lo2 then some true
      else if Nat.blt hi2 lo1 then some false
      else none
    else none
  | _, _, _, _, _ => none

/-- Soundness of `AbsVal.decideLe?`. -/
theorem absVal_decideLe?_sound {w x y : Nat} {a b : AbsVal} {r : Bool}
    (hDec : AbsVal.decideLe? w a b = some r)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    Nat.ble x y = r := by
  dsimp only [AbsVal.decideLe?] at hDec
  cases hw : validWidth w with
  | false => rw [hw] at hDec; nomatch hDec
  | true =>
    cases hai : a.init with
    | bot => rw [hw, hai] at hDec; nomatch hDec
    | uninit => rw [hw, hai] at hDec; nomatch hDec
    | init =>
      cases hbi : b.init with
      | bot => rw [hw, hai, hbi] at hDec; nomatch hDec
      | uninit => rw [hw, hai, hbi] at hDec; nomatch hDec
      | init =>
        cases hWia : a.wi with
        | bot => rw [hw, hai, hbi, hWia] at hDec; nomatch hDec
        | top => rw [hw, hai, hbi, hWia] at hDec; nomatch hDec
        | iv lo1 hi1 =>
          cases hWib : b.wi with
          | bot => rw [hw, hai, hbi, hWia, hWib] at hDec; nomatch hDec
          | top => rw [hw, hai, hbi, hWia, hWib] at hDec; nomatch hDec
          | iv lo2 hi2 =>
            rw [hw, hai, hbi, hWia, hWib] at hDec
            dsimp only at hDec
            cases hNonWrap : Nat.ble lo1 hi1 && Nat.ble lo2 hi2 with
            | false => rw [hNonWrap] at hDec; nomatch hDec
            | true =>
              rw [hNonWrap] at hDec
              have haE := absVal_some_elim ha
              have hbE := absVal_some_elim hb
              have hWix := haE.2.2.1; rw [hWia] at hWix
              dsimp only [WrappedInterval.denote] at hWix
              rw [bool_and_true_left hNonWrap] at hWix
              have hWiy := hbE.2.2.1; rw [hWib] at hWiy
              dsimp only [WrappedInterval.denote] at hWiy
              rw [bool_and_true_right hNonWrap] at hWiy
              cases hT : Nat.ble hi1 lo2 with
              | true =>
                rw [hT] at hDec
                injection hDec with hR
                rw [← hR]
                exact Nat.ble_eq_true_of_le
                  (Nat.le_trans hWix.2.2.2.2
                    (Nat.le_trans (Nat.le_of_ble_eq_true hT) hWiy.2.2.2.1))
              | false =>
                rw [hT] at hDec
                cases hF : Nat.blt hi2 lo1 with
                | false => rw [hF] at hDec; nomatch hDec
                | true =>
                  rw [hF] at hDec
                  injection hDec with hR
                  rw [← hR]
                  have hGt : y < x :=
                    Nat.lt_of_le_of_lt hWiy.2.2.2.2
                      (Nat.lt_of_lt_of_le (lt_of_blt_true hF) hWix.2.2.2.1)
                  cases hBle : Nat.ble x y with
                  | false => rfl
                  | true =>
                    exact False.elim
                      (Nat.not_le_of_gt hGt (Nat.le_of_ble_eq_true hBle))

/-- Decides `x < y` when non-wrapping intervals of `a` and `b` separate them. -/
@[expose] def AbsVal.decideLt? (w : Nat) (a b : AbsVal) : Option Bool :=
  match validWidth w, a.init, b.init, a.wi, b.wi with
  | true, .init, .init, .iv lo1 hi1, .iv lo2 hi2 =>
    if Nat.ble lo1 hi1 && Nat.ble lo2 hi2 then
      if Nat.blt hi1 lo2 then some true
      else if Nat.ble hi2 lo1 then some false
      else none
    else none
  | _, _, _, _, _ => none

/-- Soundness of `AbsVal.decideLt?`. -/
theorem absVal_decideLt?_sound {w x y : Nat} {a b : AbsVal} {r : Bool}
    (hDec : AbsVal.decideLt? w a b = some r)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    Nat.blt x y = r := by
  dsimp only [AbsVal.decideLt?] at hDec
  cases hw : validWidth w with
  | false => rw [hw] at hDec; nomatch hDec
  | true =>
    cases hai : a.init with
    | bot => rw [hw, hai] at hDec; nomatch hDec
    | uninit => rw [hw, hai] at hDec; nomatch hDec
    | init =>
      cases hbi : b.init with
      | bot => rw [hw, hai, hbi] at hDec; nomatch hDec
      | uninit => rw [hw, hai, hbi] at hDec; nomatch hDec
      | init =>
        cases hWia : a.wi with
        | bot => rw [hw, hai, hbi, hWia] at hDec; nomatch hDec
        | top => rw [hw, hai, hbi, hWia] at hDec; nomatch hDec
        | iv lo1 hi1 =>
          cases hWib : b.wi with
          | bot => rw [hw, hai, hbi, hWia, hWib] at hDec; nomatch hDec
          | top => rw [hw, hai, hbi, hWia, hWib] at hDec; nomatch hDec
          | iv lo2 hi2 =>
            rw [hw, hai, hbi, hWia, hWib] at hDec
            dsimp only at hDec
            cases hNonWrap : Nat.ble lo1 hi1 && Nat.ble lo2 hi2 with
            | false => rw [hNonWrap] at hDec; nomatch hDec
            | true =>
              rw [hNonWrap] at hDec
              have haE := absVal_some_elim ha
              have hbE := absVal_some_elim hb
              have hWix := haE.2.2.1; rw [hWia] at hWix
              dsimp only [WrappedInterval.denote] at hWix
              rw [bool_and_true_left hNonWrap] at hWix
              have hWiy := hbE.2.2.1; rw [hWib] at hWiy
              dsimp only [WrappedInterval.denote] at hWiy
              rw [bool_and_true_right hNonWrap] at hWiy
              cases hT : Nat.blt hi1 lo2 with
              | true =>
                rw [hT] at hDec
                injection hDec with hR
                rw [← hR]
                exact blt_true_of_lt
                  (Nat.lt_of_le_of_lt hWix.2.2.2.2
                    (Nat.lt_of_lt_of_le (lt_of_blt_true hT) hWiy.2.2.2.1))
              | false =>
                rw [hT] at hDec
                cases hF : Nat.ble hi2 lo1 with
                | false => rw [hF] at hDec; nomatch hDec
                | true =>
                  rw [hF] at hDec
                  injection hDec with hR
                  rw [← hR]
                  have hGe : y ≤ x :=
                    Nat.le_trans hWiy.2.2.2.2
                      (Nat.le_trans (Nat.le_of_ble_eq_true hF) hWix.2.2.2.1)
                  cases hBlt : Nat.blt x y with
                  | false => rfl
                  | true =>
                    exact False.elim
                      (Nat.not_le_of_gt (lt_of_blt_true hBlt) hGe)

/-! ### Signed Biased-Coordinate Helpers, Bounds, Comparisons, and Refinements -/

/-- Half-modulus `2^(w - 1)` for signed `w`-bit two's-complement coordinates. -/
@[expose] def halfModPow2 (w : Nat) : Nat :=
  modPow2 (w - 1)

/-- Signed-order bijection `x ↦ (x + 2^(w-1)) mod 2^w`, mapping signed two's
complement `[-2^(w-1), 2^(w-1) - 1]` monotonically onto `[0, 2^w - 1]`. -/
@[expose] def signedBias (w x : Nat) : Nat :=
  wrapVal w (x + halfModPow2 w)

/-- For `1 ≤ w ≤ 128`, `modPow2 w = halfModPow2 w + halfModPow2 w`. -/
theorem modPow2_eq_half_add_half {w : Nat} (hw : validWidth w = true) :
    modPow2 w = halfModPow2 w + halfModPow2 w := by
  have h1 : 1 ≤ w := Nat.le_of_ble_eq_true (bool_and_true_left hw)
  have hwEq : (w - 1) + 1 = w := Nat.sub_add_cancel h1
  have hSucc := modPow2_succ (w - 1)
  rw [hwEq, Nat.two_mul] at hSucc
  exact hSucc

/-- `0 < halfModPow2 w`. -/
theorem halfModPow2_pos (w : Nat) : 0 < halfModPow2 w :=
  modPow2_pos (w - 1)

/-- `halfModPow2 w < modPow2 w` for every valid width. -/
theorem halfModPow2_lt_modPow2 {w : Nat} (hw : validWidth w = true) :
    halfModPow2 w < modPow2 w := by
  rw [modPow2_eq_half_add_half hw]
  exact Nat.lt_add_of_pos_right (halfModPow2_pos w)

/-- `signedBias w x < modPow2 w`. -/
theorem signedBias_lt {w : Nat} (x : Nat) : signedBias w x < modPow2 w :=
  nat_mod_lt _ (modPow2_pos w)

/-- `signedBias w x = x + halfModPow2 w` when `x < halfModPow2 w`. -/
theorem signedBias_of_lt_half {w x : Nat} (hw : validWidth w = true)
    (hLt : x < halfModPow2 w) :
    signedBias w x = x + halfModPow2 w := by
  dsimp only [signedBias, wrapVal]
  have hSumLt : x + halfModPow2 w < modPow2 w := by
    rw [modPow2_eq_half_add_half hw]
    exact Nat.add_lt_add_right hLt (halfModPow2 w)
  exact nat_mod_eq_of_lt hSumLt

/-- `signedBias w x = x - halfModPow2 w` for `halfModPow2 w ≤ x < modPow2 w`. -/
theorem signedBias_of_ge_half {w x : Nat} (hw : validWidth w = true)
    (hGe : halfModPow2 w ≤ x) (hLt : x < modPow2 w) :
    signedBias w x = x - halfModPow2 w := by
  dsimp only [signedBias, wrapVal]
  have hM := modPow2_eq_half_add_half hw
  have hEq : x + halfModPow2 w = modPow2 w + (x - halfModPow2 w) := by
    rw [hM, Nat.add_assoc (halfModPow2 w) (halfModPow2 w) (x - halfModPow2 w),
        Nat.add_comm (halfModPow2 w) (x - halfModPow2 w),
        Nat.sub_add_cancel hGe, Nat.add_comm]
  have hSubLt : x - halfModPow2 w < modPow2 w :=
    Nat.lt_of_le_of_lt (Nat.sub_le x (halfModPow2 w)) hLt
  rw [hEq, nat_add_mod_self_left, nat_mod_eq_of_lt hSubLt]

/-- Adding `halfModPow2 w` twice mod `modPow2 w` is identity on `[0, 2^w)`. -/
theorem signedBias_inv {w x : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) :
    Nat.mod (halfModPow2 w + signedBias w x) (modPow2 w) = x := by
  dsimp only [signedBias, wrapVal]
  have hM : 0 < modPow2 w := modPow2_pos w
  rw [mod_add_mod_right (halfModPow2 w) (x + halfModPow2 w) (modPow2 w) hM]
  have hRe : halfModPow2 w + (x + halfModPow2 w) = modPow2 w + x := by
    rw [modPow2_eq_half_add_half hw, Nat.add_comm x (halfModPow2 w),
        ← Nat.add_assoc (halfModPow2 w) (halfModPow2 w) x]
  rw [hRe, nat_add_mod_self_left, nat_mod_eq_of_lt hx]

/-- Shifting both endpoints of a modular arc by `+k mod M` keeps `wrapSpan`. -/
theorem wrapSpan_shift {M lo hi k : Nat} (hM : 0 < M)
    (hLo : lo < M) (hHi : hi < M) :
    wrapSpan M (Nat.mod (lo + k) M) (Nat.mod (hi + k) M) = wrapSpan M lo hi := by
  let s := wrapSpan M lo hi
  have hsLt : s < M := wrapSpan_lt hLo hHi
  have hLo'Lt : Nat.mod (lo + k) M < M := nat_mod_lt _ hM
  have hSpan := wrapped_span_of_add_lt hM hLo'Lt hsLt
  have hHiEq : Nat.mod (Nat.mod (lo + k) M + s) M = Nat.mod (hi + k) M := by
    rw [mod_add_mod_left (lo + k) s M hM,
        Nat.add_assoc lo k s, Nat.add_comm k s, ← Nat.add_assoc lo s k,
        ← mod_add_mod_left (lo + s) k M hM,
        wrapped_hi_eq_mod_lo_span hLo hHi]
  have hEq := hSpan.2
  rw [hHiEq] at hEq
  exact hEq

/-- Extracts biased signed bounds `(sLo, sHi)` with `sLo ≤ sHi < 2^w`
from an initialized `AbsVal` whose wrapped interval does not straddle the signed
overflow boundary `2^(w-1) - 1 -> 2^(w-1)`. -/
@[expose] def AbsVal.signedBounds? (w : Nat) (a : AbsVal) : Option (Nat × Nat) :=
  match validWidth w, a.init, a.wi with
  | true, .init, .iv lo hi =>
    let M := modPow2 w
    if Nat.blt lo M && Nat.blt hi M then
      let sLo := signedBias w lo
      let sHi := signedBias w hi
      if Nat.ble sLo sHi then some (sLo, sHi) else none
    else none
  | _, _, _ => none

/-- Soundness of `AbsVal.signedBounds?`. -/
theorem absVal_signedBounds?_sound {w x sLo sHi : Nat} {a : AbsVal}
    (hB : a.signedBounds? w = some (sLo, sHi))
    (ha : a.denote w (some x)) :
    validWidth w = true ∧ sLo ≤ signedBias w x ∧ signedBias w x ≤ sHi ∧
      sHi < modPow2 w := by
  dsimp only [AbsVal.signedBounds?] at hB
  cases hw : validWidth w with
  | false => rw [hw] at hB; nomatch hB
  | true =>
    cases hai : a.init with
    | bot | uninit => rw [hw, hai] at hB; nomatch hB
    | init =>
      cases hWi : a.wi with
      | bot | top => rw [hw, hai, hWi] at hB; nomatch hB
      | iv lo hi =>
        rw [hw, hai, hWi] at hB
        dsimp only at hB
        cases hIn : Nat.blt lo (modPow2 w) && Nat.blt hi (modPow2 w) with
        | false => rw [hIn] at hB; nomatch hB
        | true =>
          rw [hIn] at hB
          cases hBle : Nat.ble (signedBias w lo) (signedBias w hi) with
          | false => rw [hBle] at hB; nomatch hB
          | true =>
            rw [hBle] at hB
            injection hB with hPair
            have hsLoEq : sLo = signedBias w lo := (congrArg Prod.fst hPair).symm
            have hsHiEq : sHi = signedBias w hi := (congrArg Prod.snd hPair).symm
            subst hsLoEq; subst hsHiEq
            have hM : 0 < modPow2 w := modPow2_pos w
            have hLoLt : lo < modPow2 w := lt_of_blt_true (bool_and_true_left hIn)
            have hHiLt : hi < modPow2 w := lt_of_blt_true (bool_and_true_right hIn)
            have hLe : signedBias w lo ≤ signedBias w hi := Nat.le_of_ble_eq_true hBle
            have haE := absVal_some_elim ha
            have hWix := haE.2.2.1; rw [hWi] at hWix
            cases (wrapped_denote_iff_offset hLoLt hHiLt haE.1).1 hWix with
            | intro d hd =>
              have hSpanEq : wrapSpan (modPow2 w) lo hi = signedBias w hi - signedBias w lo := by
                have hSh := wrapSpan_shift (k := halfModPow2 w) hM hLoLt hHiLt
                dsimp only [signedBias, wrapVal] at hBle
                dsimp only [signedBias, wrapVal]
                dsimp only [wrapSpan] at hSh
                rw [hBle] at hSh
                exact hSh.symm
              have hdLe : d ≤ signedBias w hi - signedBias w lo := by
                rw [← hSpanEq]; exact hd.1
              have hSumLe : signedBias w lo + d ≤ signedBias w hi := by
                have h1 := Nat.add_le_add_left hdLe (signedBias w lo)
                rw [Nat.add_comm (signedBias w lo) (signedBias w hi - signedBias w lo),
                    Nat.sub_add_cancel hLe] at h1
                exact h1
              have hSumLt : signedBias w lo + d < modPow2 w :=
                Nat.lt_of_le_of_lt hSumLe (signedBias_lt hi)
              have hBiasX : signedBias w x = signedBias w lo + d := by
                dsimp only [signedBias, wrapVal]
                rw [hd.2, mod_add_mod_left (lo + d) (halfModPow2 w) (modPow2 w) hM,
                    Nat.add_assoc lo d (halfModPow2 w), Nat.add_comm d (halfModPow2 w),
                    ← Nat.add_assoc lo (halfModPow2 w) d,
                    ← mod_add_mod_left (lo + halfModPow2 w) d (modPow2 w) hM]
                exact nat_mod_eq_of_lt hSumLt
              rw [hBiasX]
              exact ⟨rfl, Nat.le_add_right _ d, hSumLe, signedBias_lt hi⟩

/-- Sufficient check certifying that signed `w`-bit addition never overflows
`[-2^(w-1), 2^(w-1))` (`H ≤ bias(x) + bias(y) < 3 * H`). -/
@[expose] def AbsVal.noSignedOverflowAdd (w : Nat) (a b : AbsVal) : Bool :=
  match a.signedBounds? w, b.signedBounds? w with
  | some (sLo1, sHi1), some (sLo2, sHi2) =>
    let H := halfModPow2 w
    Nat.ble H (sLo1 + sLo2) && Nat.blt (sHi1 + sHi2) (3 * H)
  | _, _ => false

/-- Soundness of `AbsVal.noSignedOverflowAdd`. -/
theorem absVal_noSignedOverflowAdd_sound {w x y : Nat} {a b : AbsVal}
    (hOk : AbsVal.noSignedOverflowAdd w a b = true)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    halfModPow2 w ≤ signedBias w x + signedBias w y ∧
      signedBias w x + signedBias w y < 3 * halfModPow2 w := by
  dsimp only [AbsVal.noSignedOverflowAdd] at hOk
  cases hA : a.signedBounds? w with
  | none => rw [hA] at hOk; nomatch hOk
  | some p1 =>
    cases p1 with | mk sLo1 sHi1 =>
    cases hB : b.signedBounds? w with
    | none => rw [hA, hB] at hOk; nomatch hOk
    | some p2 =>
      cases p2 with | mk sLo2 sHi2 =>
      rw [hA, hB] at hOk
      dsimp only at hOk
      have h1 := absVal_signedBounds?_sound hA ha
      have h2 := absVal_signedBounds?_sound hB hb
      have hLo := Nat.le_of_ble_eq_true (bool_and_true_left hOk)
      have hHi := lt_of_blt_true (bool_and_true_right hOk)
      exact ⟨Nat.le_trans hLo (Nat.add_le_add h1.2.1 h2.2.1),
        Nat.lt_of_le_of_lt (Nat.add_le_add h1.2.2.1 h2.2.2.1) hHi⟩

/-- Sufficient check certifying that signed `w`-bit subtraction never overflows
`[-2^(w-1), 2^(w-1))` (`bias(y) ≤ bias(x) + H ∧ bias(x) < bias(y) + H`). -/
@[expose] def AbsVal.noSignedOverflowSub (w : Nat) (a b : AbsVal) : Bool :=
  match a.signedBounds? w, b.signedBounds? w with
  | some (sLo1, sHi1), some (sLo2, sHi2) =>
    let H := halfModPow2 w
    Nat.ble sHi2 (sLo1 + H) && Nat.blt sHi1 (sLo2 + H)
  | _, _ => false

/-- Soundness of `AbsVal.noSignedOverflowSub`. -/
theorem absVal_noSignedOverflowSub_sound {w x y : Nat} {a b : AbsVal}
    (hOk : AbsVal.noSignedOverflowSub w a b = true)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    signedBias w y ≤ signedBias w x + halfModPow2 w ∧
      signedBias w x < signedBias w y + halfModPow2 w := by
  dsimp only [AbsVal.noSignedOverflowSub] at hOk
  cases hA : a.signedBounds? w with
  | none => rw [hA] at hOk; nomatch hOk
  | some p1 =>
    cases p1 with | mk sLo1 sHi1 =>
    cases hB : b.signedBounds? w with
    | none => rw [hA, hB] at hOk; nomatch hOk
    | some p2 =>
      cases p2 with | mk sLo2 sHi2 =>
      rw [hA, hB] at hOk
      dsimp only at hOk
      have h1 := absVal_signedBounds?_sound hA ha
      have h2 := absVal_signedBounds?_sound hB hb
      have hC1 := Nat.le_of_ble_eq_true (bool_and_true_left hOk)
      have hC2 := lt_of_blt_true (bool_and_true_right hOk)
      exact ⟨Nat.le_trans h2.2.2.1 (Nat.le_trans hC1 (Nat.add_le_add_right h1.2.1 _)),
        Nat.lt_of_le_of_lt h1.2.2.1 (Nat.lt_of_lt_of_le hC2 (Nat.add_le_add_right h2.2.1 _))⟩

/-- Sufficient check certifying that signed `w`-bit division/remainder neither
divides by zero (`bias(y) ≠ H`) nor computes `INT_MIN / -1`
(`¬(bias(x) = 0 ∧ bias(y) = H - 1)`). -/
@[expose] def AbsVal.safeSignedDiv (w : Nat) (a b : AbsVal) : Bool :=
  match b.signedBounds? w with
  | some (sLo2, sHi2) =>
    let H := halfModPow2 w
    if Nat.blt H sLo2 then true
    else if Nat.blt sHi2 H then
      Nat.blt sHi2 (H - 1) ||
        match a.signedBounds? w with
        | some (sLo1, _) => Nat.blt 0 sLo1
        | none => false
    else false
  | none => false

/-- Soundness of `AbsVal.safeSignedDiv`. -/
theorem absVal_safeSignedDiv_sound {w x y : Nat} {a b : AbsVal}
    (hOk : AbsVal.safeSignedDiv w a b = true)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    signedBias w y ≠ halfModPow2 w ∧
      ¬ (signedBias w x = 0 ∧ signedBias w y = halfModPow2 w - 1) := by
  dsimp only [AbsVal.safeSignedDiv] at hOk
  cases hB : b.signedBounds? w with
  | none => rw [hB] at hOk; nomatch hOk
  | some p2 =>
    cases p2 with | mk sLo2 sHi2 =>
    rw [hB] at hOk
    dsimp only at hOk
    have h2 := absVal_signedBounds?_sound hB hb
    cases hPos : Nat.blt (halfModPow2 w) sLo2 with
    | true =>
      have hGtH : halfModPow2 w < signedBias w y :=
        Nat.lt_of_lt_of_le (lt_of_blt_true hPos) h2.2.1
      refine ⟨fun hEq => Nat.not_lt_of_ge (Nat.le_of_eq hEq) hGtH, ?_⟩
      intro hPair
      have hLeH : signedBias w y ≤ halfModPow2 w := by
        rw [hPair.2]; exact Nat.sub_le _ 1
      exact Nat.not_lt_of_ge hLeH hGtH
    | false =>
      rw [hPos] at hOk
      cases hNeg : Nat.blt sHi2 (halfModPow2 w) with
      | false => rw [hNeg] at hOk; nomatch hOk
      | true =>
        rw [hNeg] at hOk
        have hLtH : signedBias w y < halfModPow2 w :=
          Nat.lt_of_le_of_lt h2.2.2.1 (lt_of_blt_true hNeg)
        refine ⟨fun hEq => Nat.not_lt_of_ge (Nat.le_of_eq hEq.symm) hLtH, ?_⟩
        intro hPair
        cases hLtM1 : Nat.blt sHi2 (halfModPow2 w - 1) with
        | true =>
          have hLt := Nat.lt_of_le_of_lt h2.2.2.1 (lt_of_blt_true hLtM1)
          rw [hPair.2] at hLt
          exact Nat.lt_irrefl _ hLt
        | false =>
          rw [hLtM1] at hOk
          cases hA : a.signedBounds? w with
          | none => rw [hA] at hOk; nomatch hOk
          | some p1 =>
            cases p1 with | mk sLo1 sHi1 =>
            rw [hA] at hOk
            have h1 := absVal_signedBounds?_sound hA ha
            have hPosX : 0 < signedBias w x :=
              Nat.lt_of_lt_of_le (lt_of_blt_true hOk) h1.2.1
            rw [hPair.1] at hPosX
            nomatch hPosX

/-- Decides signed `decode(x) ≤ decode(y)` via `signedBias`. -/
@[expose] def AbsVal.decideSle? (w : Nat) (a b : AbsVal) : Option Bool :=
  match a.signedBounds? w, b.signedBounds? w with
  | some (sLo1, sHi1), some (sLo2, sHi2) =>
    if Nat.ble sHi1 sLo2 then some true
    else if Nat.blt sHi2 sLo1 then some false
    else none
  | _, _ => none

/-- Soundness of `AbsVal.decideSle?`. -/
theorem absVal_decideSle?_sound {w x y : Nat} {a b : AbsVal} {r : Bool}
    (hDec : AbsVal.decideSle? w a b = some r)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    Nat.ble (signedBias w x) (signedBias w y) = r := by
  dsimp only [AbsVal.decideSle?] at hDec
  cases hA : a.signedBounds? w with
  | none => rw [hA] at hDec; nomatch hDec
  | some p1 =>
    cases p1 with | mk sLo1 sHi1 =>
    cases hB : b.signedBounds? w with
    | none => rw [hA, hB] at hDec; nomatch hDec
    | some p2 =>
      cases p2 with | mk sLo2 sHi2 =>
      rw [hA, hB] at hDec
      dsimp only at hDec
      have h1 := absVal_signedBounds?_sound hA ha
      have h2 := absVal_signedBounds?_sound hB hb
      cases hT : Nat.ble sHi1 sLo2 with
      | true =>
        rw [hT] at hDec
        injection hDec with hR; subst hR
        exact Nat.ble_eq_true_of_le
          (Nat.le_trans h1.2.2.1 (Nat.le_trans (Nat.le_of_ble_eq_true hT) h2.2.1))
      | false =>
        rw [hT] at hDec
        cases hF : Nat.blt sHi2 sLo1 with
        | false => rw [hF] at hDec; nomatch hDec
        | true =>
          rw [hF] at hDec
          injection hDec with hR; subst hR
          have hGt : signedBias w y < signedBias w x :=
            Nat.lt_of_le_of_lt h2.2.2.1
              (Nat.lt_of_lt_of_le (lt_of_blt_true hF) h1.2.1)
          cases hBle : Nat.ble (signedBias w x) (signedBias w y) with
          | false => rfl
          | true =>
            exact False.elim (Nat.not_le_of_gt hGt (Nat.le_of_ble_eq_true hBle))

/-- Decides signed `decode(x) < decode(y)` via `signedBias`. -/
@[expose] def AbsVal.decideSlt? (w : Nat) (a b : AbsVal) : Option Bool :=
  match a.signedBounds? w, b.signedBounds? w with
  | some (sLo1, sHi1), some (sLo2, sHi2) =>
    if Nat.blt sHi1 sLo2 then some true
    else if Nat.ble sHi2 sLo1 then some false
    else none
  | _, _ => none

/-- Soundness of `AbsVal.decideSlt?`. -/
theorem absVal_decideSlt?_sound {w x y : Nat} {a b : AbsVal} {r : Bool}
    (hDec : AbsVal.decideSlt? w a b = some r)
    (ha : a.denote w (some x)) (hb : b.denote w (some y)) :
    Nat.blt (signedBias w x) (signedBias w y) = r := by
  dsimp only [AbsVal.decideSlt?] at hDec
  cases hA : a.signedBounds? w with
  | none => rw [hA] at hDec; nomatch hDec
  | some p1 =>
    cases p1 with | mk sLo1 sHi1 =>
    cases hB : b.signedBounds? w with
    | none => rw [hA, hB] at hDec; nomatch hDec
    | some p2 =>
      cases p2 with | mk sLo2 sHi2 =>
      rw [hA, hB] at hDec
      dsimp only at hDec
      have h1 := absVal_signedBounds?_sound hA ha
      have h2 := absVal_signedBounds?_sound hB hb
      cases hT : Nat.blt sHi1 sLo2 with
      | true =>
        rw [hT] at hDec
        injection hDec with hR; subst hR
        exact blt_true_of_lt
          (Nat.lt_of_le_of_lt h1.2.2.1
            (Nat.lt_of_lt_of_le (lt_of_blt_true hT) h2.2.1))
      | false =>
        rw [hT] at hDec
        cases hF : Nat.ble sHi2 sLo1 with
        | false => rw [hF] at hDec; nomatch hDec
        | true =>
          rw [hF] at hDec
          injection hDec with hR; subst hR
          have hGe : signedBias w y ≤ signedBias w x :=
            Nat.le_trans h2.2.2.1
              (Nat.le_trans (Nat.le_of_ble_eq_true hF) h1.2.1)
          cases hBlt : Nat.blt (signedBias w x) (signedBias w y) with
          | false => rfl
          | true =>
            exact False.elim (Nat.not_le_of_gt (lt_of_blt_true hBlt) hGe)

/-- Refines `a` under signed branch condition `decode(x) ≤ decode(boundBits)`
by intersecting `a.wi` with `.iv (halfModPow2 w) boundBits`. -/
@[expose] def AbsVal.refineSleConst (w : Nat) (a : AbsVal) (boundBits : Nat) :
    AbsVal :=
  match validWidth w && a.isInit && Nat.blt boundBits (modPow2 w) with
  | false => a
  | true =>
    let M := modPow2 w
    let H := halfModPow2 w
    reduceAbsVal w ⟨.init, a.tnum, WrappedInterval.meet M a.wi (.iv H boundBits), a.sc⟩

/-- Soundness of `AbsVal.refineSleConst`. -/
theorem absVal_refineSleConst_sound {w x boundBits : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hBLt : boundBits < modPow2 w)
    (hSle : signedBias w x ≤ signedBias w boundBits) :
    (AbsVal.refineSleConst w a boundBits).denote w (some x) := by
  dsimp only [AbsVal.refineSleConst]
  rw [hw, hai, blt_true_of_lt hBLt]
  apply reduceAbsVal_sound hw
  have haE := absVal_some_elim ha
  have hM : 0 < modPow2 w := modPow2_pos w
  have hHLt : halfModPow2 w < modPow2 w := halfModPow2_lt_modPow2 hw
  have hIv : WrappedInterval.denote (modPow2 w) (.iv (halfModPow2 w) boundBits) x := by
    rw [wrapped_denote_iff_offset hHLt hBLt haE.1]
    refine ⟨signedBias w x, ?_, (signedBias_inv hw haE.1).symm⟩
    have hSh := wrapSpan_shift (k := halfModPow2 w) hM hHLt hBLt
    have hHShift : Nat.mod (halfModPow2 w + halfModPow2 w) (modPow2 w) = 0 := by
      rw [← modPow2_eq_half_add_half hw, nat_mod_self]
    rw [hHShift] at hSh
    dsimp only [wrapSpan] at hSh
    rw [Nat.ble_eq_true_of_le (Nat.zero_le _), Nat.sub_zero] at hSh
    dsimp only at hSh
    dsimp only [wrapSpan]
    rw [← hSh]
    exact hSle
  exact ⟨⟨x, rfl, haE.1⟩, haE.2.1,
    wrappedInterval_meet_sound hM haE.2.2.1 hIv, haE.2.2.2⟩

/-- Refines `a` under signed branch condition `decode(boundBits) < decode(x)`
by intersecting `a.wi` with `.iv (wrapVal w (boundBits + 1)) (H - 1)`
(or `.bot` when `boundBits == halfModPow2 w - 1`, i.e., `INT_MAX`). -/
@[expose] def AbsVal.refineSgtConst (w : Nat) (a : AbsVal) (boundBits : Nat) :
    AbsVal :=
  match validWidth w && a.isInit && Nat.blt boundBits (modPow2 w) with
  | false => a
  | true =>
    let M := modPow2 w
    let H := halfModPow2 w
    if Nat.beq boundBits (H - 1) then
      AbsVal.bot
    else
      let lo := wrapVal w (boundBits + 1)
      reduceAbsVal w ⟨.init, a.tnum, WrappedInterval.meet M a.wi (.iv lo (H - 1)), a.sc⟩

/-- Soundness of `AbsVal.refineSgtConst`. -/
theorem absVal_refineSgtConst_sound {w x boundBits : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true)
    (hBLt : boundBits < modPow2 w)
    (hSgt : signedBias w boundBits < signedBias w x) :
    (AbsVal.refineSgtConst w a boundBits).denote w (some x) := by
  dsimp only [AbsVal.refineSgtConst]
  rw [hw, hai, blt_true_of_lt hBLt]
  have haE := absVal_some_elim ha
  have hM : 0 < modPow2 w := modPow2_pos w
  have hHPos : 0 < halfModPow2 w := halfModPow2_pos w
  have hHLt : halfModPow2 w < modPow2 w := halfModPow2_lt_modPow2 hw
  have hHiLt : halfModPow2 w - 1 < modPow2 w :=
    Nat.lt_trans (Nat.sub_lt hHPos (Nat.zero_lt_succ 0)) hHLt
  have hHiBias : signedBias w (halfModPow2 w - 1) = modPow2 w - 1 := by
    rw [signedBias_of_lt_half hw (Nat.sub_lt hHPos (Nat.zero_lt_succ 0)),
        modPow2_eq_half_add_half hw,
        Nat.add_comm (halfModPow2 w - 1) (halfModPow2 w),
        Nat.add_sub_assoc hHPos (halfModPow2 w)]
  have hBNotMax : Nat.beq boundBits (halfModPow2 w - 1) = false := by
    cases hEq : Nat.beq boundBits (halfModPow2 w - 1) with
    | false => rfl
    | true =>
      have hBEq := Nat.eq_of_beq_eq_true hEq
      rw [hBEq, hHiBias] at hSgt
      have hLe : signedBias w x ≤ modPow2 w - 1 := Nat.le_pred_of_lt (signedBias_lt x)
      exact False.elim (Nat.not_le_of_gt hSgt hLe)
  rw [hBNotMax]
  change AbsVal.denote w
    (reduceAbsVal w
      ⟨.init, a.tnum, WrappedInterval.meet (modPow2 w) a.wi
        (.iv (wrapVal w (boundBits + 1)) (halfModPow2 w - 1)), a.sc⟩)
    (some x)
  apply reduceAbsVal_sound hw
  let lo := wrapVal w (boundBits + 1)
  have hLoLt : lo < modPow2 w := nat_mod_lt _ hM
  have hBiasBLt : signedBias w boundBits + 1 < modPow2 w :=
    Nat.lt_of_le_of_lt hSgt (signedBias_lt x)
  have hLoBias : signedBias w lo = signedBias w boundBits + 1 := by
    dsimp only [lo, signedBias, wrapVal]
    rw [mod_add_mod_left (boundBits + 1) (halfModPow2 w) (modPow2 w) hM,
        Nat.add_assoc boundBits 1 (halfModPow2 w), Nat.add_comm 1 (halfModPow2 w),
        ← Nat.add_assoc boundBits (halfModPow2 w) 1,
        ← mod_add_mod_left (boundBits + halfModPow2 w) 1 (modPow2 w) hM]
    exact nat_mod_eq_of_lt hBiasBLt
  have hIv : WrappedInterval.denote (modPow2 w) (.iv lo (halfModPow2 w - 1)) x := by
    rw [wrapped_denote_iff_offset hLoLt hHiLt haE.1]
    refine ⟨signedBias w x - (signedBias w boundBits + 1), ?_, ?_⟩
    · have hSh := wrapSpan_shift (k := halfModPow2 w) hM hLoLt hHiLt
      have hLoBiasEq : Nat.mod (lo + halfModPow2 w) (modPow2 w) = signedBias w boundBits + 1 :=
        hLoBias
      have hHiBiasEq : Nat.mod ((halfModPow2 w - 1) + halfModPow2 w) (modPow2 w) = modPow2 w - 1 :=
        hHiBias
      rw [hLoBiasEq, hHiBiasEq] at hSh
      dsimp only [wrapSpan] at hSh
      have hLeMax : signedBias w boundBits + 1 ≤ modPow2 w - 1 := Nat.le_pred_of_lt hBiasBLt
      rw [Nat.ble_eq_true_of_le hLeMax] at hSh
      dsimp only at hSh
      dsimp only [wrapSpan]
      rw [← hSh]
      exact Nat.sub_le_sub_right (Nat.le_pred_of_lt (signedBias_lt x)) _
    · have hBiasEq :
          Nat.mod (lo + (signedBias w x - (signedBias w boundBits + 1)) + halfModPow2 w) (modPow2 w) =
            signedBias w x := by
        rw [Nat.add_assoc lo _ (halfModPow2 w),
            Nat.add_comm (signedBias w x - (signedBias w boundBits + 1)) (halfModPow2 w),
            ← Nat.add_assoc lo (halfModPow2 w) _,
            ← mod_add_mod_left (lo + halfModPow2 w) _ (modPow2 w) hM]
        have hLoB : Nat.mod (lo + halfModPow2 w) (modPow2 w) = signedBias w boundBits + 1 :=
          hLoBias
        rw [hLoB, Nat.add_comm (signedBias w boundBits + 1) _,
            Nat.sub_add_cancel hSgt, nat_mod_eq_of_lt (signedBias_lt x)]
      have hBack := congrArg (fun z => Nat.mod (halfModPow2 w + z) (modPow2 w)) hBiasEq
      rw [signedBias_inv hw haE.1] at hBack
      have hLhs :
          Nat.mod (halfModPow2 w +
            Nat.mod (lo + (signedBias w x - (signedBias w boundBits + 1)) + halfModPow2 w)
              (modPow2 w)) (modPow2 w) =
          Nat.mod (lo + (signedBias w x - (signedBias w boundBits + 1))) (modPow2 w) := by
        rw [mod_add_mod_right _ _ (modPow2 w) hM,
            Nat.add_comm (lo + (signedBias w x - (signedBias w boundBits + 1))) (halfModPow2 w),
            ← Nat.add_assoc (halfModPow2 w) (halfModPow2 w) _,
            ← modPow2_eq_half_add_half hw, nat_add_mod_self_left]
      rw [hLhs] at hBack
      exact hBack.symm
  exact ⟨⟨x, rfl, haE.1⟩, haE.2.1,
    wrappedInterval_meet_sound hM haE.2.2.1 hIv, haE.2.2.2⟩

/-- Bitwise complement transfer on `AbsVal` (`x ↦ x ^^^ (2^w - 1)`). -/
@[expose] def AbsVal.bitNot (w : Nat) (a : AbsVal) : AbsVal :=
  AbsVal.bitXor w a (AbsVal.const w (modPow2 w - 1))

/-- Soundness of `AbsVal.bitNot`. -/
theorem absVal_bitNot_sound {w x : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x)) (hai : a.isInit = true) :
    (AbsVal.bitNot w a).denote w (some (Nat.xor x (modPow2 w - 1))) := by
  have hMaxLt : modPow2 w - 1 < modPow2 w := Nat.sub_lt (modPow2_pos w) (Nat.zero_lt_succ 0)
  have hc : (AbsVal.const w (modPow2 w - 1)).denote w (some (modPow2 w - 1)) := by
    have h := absVal_const_sound (w := w) (c := modPow2 w - 1) hw
    dsimp only [wrapVal] at h
    rw [nat_mod_eq_of_lt hMaxLt] at h
    exact h
  have hci : (AbsVal.const w (modPow2 w - 1)).isInit = true := by
    dsimp only [AbsVal.const, AbsVal.isInit]; rw [hw]
  exact absVal_bitXor_sound hw ha hc hai hci

end Anneal.AiPcc

end
