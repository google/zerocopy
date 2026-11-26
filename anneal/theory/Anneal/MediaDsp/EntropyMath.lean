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
public import Init.Data.List.Basic
public import Anneal.InitLemmas

public section

/-!
# H.264 CABAC & AV1 (`rav1d`) MSAC Integer Arithmetic-Coding Core Math

Zero-duplication, 0-TCB, Pass-1-pure (`prelude` + locked `Init.*` +
`Anneal.InitLemmas`, zero `._unsafe_rec`, zero `omega`,
axioms `⊆ [propext, Quot.sound]`, zero `Classical.choice`)
range-coding invariant and renormalization theory shared across two
primary video entropy decoders:

1. **ITU-T H.264 §9.3.3.2 CABAC Binary Arithmetic Decoder (`CabacState`,
   `CabacInv`, `cabacSplitBin`, `cabacRenormStep`, `cabacRenorm`):**
   - `CabacInv st`: `256 ≤ st.range ∧ st.range ≤ 510 ∧ st.offset < st.range`.
   - `cabacSplitBin_preserves`: MPS/LPS interval split with `2 ≤ rLps ≤ 240`
     preserves `CabacPreRenorm` (`2 ≤ range' ≤ 510 ∧ offset' < range'`) in
     both MPS and LPS branches.
   - `cabacRenormStep_preserves`: doubling `(range, offset)` with incoming bit
     `b < 2` when `range < 256` preserves `range' ≤ 510` and `offset' < range'`.
   - `cabacRenorm_sound` (`@Nat.rec` fuel `7`): for every `2 ≤ range ≤ 510`
     and `offset < range`, `cabacRenorm` terminates in at most `7` bit shifts
     restoring `CabacInv` (`256 ≤ range' ≤ 510 ∧ offset' < range'`), enabling
     multi-bin decode composition.
2. **AV1 (`rav1d`) MSAC 15-Bit Multi-Symbol Arithmetic Decoder (`MsacState`,
   `MsacInv`, `msacSplitVal`, `msacRenormStep`, `msacRenorm`):**
   - `MsacInv st`: `32768 ≤ st.rng ∧ st.rng < 65536 ∧ st.dif < st.rng`.
   - `msacSplitVal rng cdfProb remSyms`: exact AV1 §8.2.6 scaled CDF split
     `(((rng >> 8) * (cdfProb >> 6)) >> 1) + 4 * remSyms` (`EC_PROB_SHIFT = 6`,
     `EC_MIN_PROB = 4`) satisfying `msacSplitVal ≤ rng` (for `32768 ≤ rng`,
     `cdfProb < 32768`, `remSyms ≤ 16`), monotonicity in `(cdfProb, remSyms)`,
     and strict `≥ 4` sub-range separation between consecutive symbols (directly
     discharging `1 ≤ rng'` for `msacRenorm_sound`).
   - `msacRenorm_sound` (`@Nat.rec` fuel `15`): for every `1 ≤ rng < 65536`
     and `dif < rng`, `msacRenorm` restores `32768 ≤ rng' < 65536` and
     `dif' < rng'` in at most `15` bit shifts.
-/

namespace Anneal.MediaDsp.EntropyMath

open Anneal.InitLemmas

private theorem pow2_zero : HPow.hPow (2 : Nat) 0 = 1 := rfl

private theorem ble_true_iff_le :
    ∀ a b : Nat, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | _ + 1, 0 =>
    ⟨fun h => Bool.noConfusion h,
     fun h => False.elim (Nat.not_succ_le_zero _ h)⟩
  | a + 1, b + 1 => by
    dsimp only [Nat.ble]
    exact ⟨fun h => Nat.succ_le_succ ((ble_true_iff_le a b).mp h),
           fun h => (ble_true_iff_le a b).mpr (Nat.le_of_succ_le_succ h)⟩

private theorem blt_true_iff_lt (a b : Nat) : Nat.blt a b = true ↔ a < b :=
  ble_true_iff_le (a + 1) b

private theorem blt_false_iff_ge (a b : Nat) : Nat.blt a b = false ↔ b ≤ a := by
  constructor
  · intro hf
    cases Nat.lt_or_ge a b with
    | inl hlt =>
      have ht := (blt_true_iff_lt a b).mpr hlt
      rw [hf] at ht
      exact Bool.noConfusion ht
    | inr hge => exact hge
  · intro hge
    cases hb : Nat.blt a b with
    | false => rfl
    | true =>
      exact False.elim (Nat.not_lt_of_ge hge ((blt_true_iff_lt a b).mp hb))

private theorem nat_lt_of_add_lt_add_right {a b c : Nat} (h : a + c < b + c) :
    a < b := by
  have hle : a + 1 + c ≤ b + c := by
    rw [Nat.add_assoc, Nat.add_comm 1 c, ← Nat.add_assoc]
    exact h
  exact Nat.le_of_add_le_add_right hle

private theorem nat_div_le_div_right {a b : Nat} (c : Nat) (hab : a ≤ b) :
    HDiv.hDiv a c ≤ HDiv.hDiv b c := by
  cases c with
  | zero =>
    rw [Nat.div_zero, Nat.div_zero]
    exact Nat.le_refl 0
  | succ c' =>
    have hpos : 0 < Nat.succ c' := Nat.zero_lt_succ c'
    have h1 : Nat.succ c' * HDiv.hDiv a (Nat.succ c') ≤ a := by
      have hle := Nat.le_add_right
        (Nat.succ c' * HDiv.hDiv a (Nat.succ c')) (HMod.hMod a (Nat.succ c'))
      rw [Nat.div_add_mod] at hle
      exact hle
    have h2 : HDiv.hDiv a (Nat.succ c') * Nat.succ c' ≤ b := by
      rw [Nat.mul_comm]
      exact Nat.le_trans h1 hab
    exact (Nat.le_div_iff_mul_le hpos).mpr h2

/-! ## Part 1: H.264 §9.3.3.2 CABAC State, Bin Split & Renormalization -/

/-- H.264 CABAC decoder engine registers `(codIRange, codIOffset)`. -/
structure CabacState where
  /-- Current interval width `codIRange` (`[256, 510]` normalized). -/
  range : Nat
  /-- Current arithmetic code offset `codIOffset` (`< range`). -/
  offset : Nat

/-- Normalized H.264 CABAC state invariant
(`256 ≤ range ≤ 510 ∧ offset < range`). -/
@[expose] def CabacInv (st : CabacState) : Prop :=
  256 ≤ st.range ∧ st.range ≤ 510 ∧ st.offset < st.range

/-- Pre-renormalization CABAC invariant (`2 ≤ range ≤ 510 ∧ offset < range`). -/
@[expose] def CabacPreRenorm (st : CabacState) : Prop :=
  2 ≤ st.range ∧ st.range ≤ 510 ∧ st.offset < st.range

/-- One H.264 CABAC regular-bin split step given `rLps`
(returns `(isLps, st')`).
- If `offset < range - rLps` (MPS): `range' = range - rLps`, `offset' = offset`.
- Otherwise (LPS): `range' = rLps`, `offset' = offset - (range - rLps)`. -/
@[expose] def cabacSplitBin (st : CabacState) (rLps : Nat) :
    Bool × CabacState :=
  let rMps := st.range - rLps
  if Nat.blt st.offset rMps then
    (false, { range := rMps, offset := st.offset })
  else
    (true, { range := rLps, offset := st.offset - rMps })

/-- Every valid CABAC regular-bin split (`2 ≤ rLps ≤ 240`, `st` normalized)
preserves `CabacPreRenorm` in BOTH the MPS and LPS branches (since
`rMps = range - rLps ≥ 256 - 240 = 16 ≥ 2`). -/
theorem cabacSplitBin_preserves {st : CabacState} {rLps : Nat}
    (hInv : CabacInv st) (hLo : 2 ≤ rLps) (hHi : rLps ≤ 240) :
    CabacPreRenorm (cabacSplitBin st rLps).2 := by
  unfold cabacSplitBin
  dsimp only
  have hrGe : 256 ≤ st.range := hInv.1
  have hrLe : st.range ≤ 510 := hInv.2.1
  have hoff : st.offset < st.range := hInv.2.2
  have hLpsLe : rLps ≤ st.range :=
    Nat.le_trans hHi (Nat.le_trans (by decide : 240 ≤ 256) hrGe)
  have hMpsGe : 16 ≤ st.range - rLps := by
    have h1 : 16 + rLps ≤ 256 := Nat.add_le_add_left hHi 16
    have h2 : 16 + rLps ≤ st.range := Nat.le_trans h1 hrGe
    have h3 : 16 + rLps ≤ (st.range - rLps) + rLps := by
      rw [Nat.sub_add_cancel hLpsLe]
      exact h2
    exact Nat.le_of_add_le_add_right h3
  cases hb : Nat.blt st.offset (st.range - rLps) with
  | true =>
    have hlt : st.offset < st.range - rLps := (blt_true_iff_lt _ _).mp hb
    change CabacPreRenorm { range := st.range - rLps, offset := st.offset }
    refine ⟨Nat.le_trans (by decide : 2 ≤ 16) hMpsGe, ?_, hlt⟩
    exact Nat.le_trans (Nat.sub_le st.range rLps) hrLe
  | false =>
    have hge : st.range - rLps ≤ st.offset := (blt_false_iff_ge _ _).mp hb
    change CabacPreRenorm
      { range := rLps, offset := st.offset - (st.range - rLps) }
    refine ⟨hLo, Nat.le_trans hHi (by decide : 240 ≤ 510), ?_⟩
    have hsum : (st.offset - (st.range - rLps)) + (st.range - rLps) <
        rLps + (st.range - rLps) := by
      rw [Nat.sub_add_cancel hge, Nat.add_comm rLps, Nat.sub_add_cancel hLpsLe]
      exact hoff
    exact nat_lt_of_add_lt_add_right hsum

/-- One CABAC renormalization bit-shift step: shifts `range` left by 1 and
pulls one bit `b` into `offset`. -/
@[expose] def cabacRenormStep (st : CabacState) (bit : Nat) : CabacState :=
  { range := st.range * 2, offset := st.offset * 2 + bit }

/-- A single CABAC renormalization step when `range < 256` and `bit < 2`
doubles `range`, preserves `range' ≤ 510`, and preserves `offset' < range'`. -/
theorem cabacRenormStep_preserves {st : CabacState} {bit : Nat}
    (hRange : st.range < 256) (hOff : st.offset < st.range) (hBit : bit < 2) :
    (cabacRenormStep st bit).range ≤ 510 ∧
    (cabacRenormStep st bit).offset < (cabacRenormStep st bit).range := by
  unfold cabacRenormStep
  dsimp only
  constructor
  · exact Nat.mul_le_mul_right 2 (Nat.le_of_lt_succ hRange)
  · have h1 : st.offset * 2 + bit < st.offset * 2 + 2 :=
      Nat.add_lt_add_left hBit _
    have h2 : st.offset * 2 + 2 = (st.offset + 1) * 2 := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right 2 hOff)

/-- Iterative H.264 CABAC renormalization loop using `@Nat.rec` (`0`
`._unsafe_rec`) consuming bits from a bit stream `bits` (defaulting to `0` on
empty) until `256 ≤ range`. -/
@[expose] def cabacRenormAux (fuel : Nat) (st : CabacState) (bits : List Nat) :
    CabacState × List Nat :=
  @Nat.rec (fun _ => CabacState → List Nat → CabacState × List Nat)
    (fun s bs => (s, bs))
    (fun _ ih s bs =>
      if Nat.blt s.range 256 then
        match bs with
        | [] => ih (cabacRenormStep s 0) []
        | b :: rest => ih (cabacRenormStep s (HMod.hMod b 2)) rest
      else
        (s, bs))
    fuel st bits

/-- Step equation for `cabacRenormAux`. -/
theorem cabacRenormAux_succ (fuel : Nat) (st : CabacState) (bits : List Nat) :
    cabacRenormAux (fuel + 1) st bits =
      if Nat.blt st.range 256 then
        match bits with
        | [] => cabacRenormAux fuel (cabacRenormStep st 0) []
        | b :: rest =>
          cabacRenormAux fuel (cabacRenormStep st (HMod.hMod b 2)) rest
      else
        (st, bits) :=
  rfl

/-- Canonical 7-step H.264 CABAC renormalization (`RenormD`, §9.3.3.2.2). -/
@[expose] def cabacRenorm (st : CabacState) (bits : List Nat) :
    CabacState × List Nat :=
  cabacRenormAux 7 st bits

/-- General fuel-indexed renormalization soundness: if `256 ≤ range * 2^fuel`,
`range ≤ 510`, and `offset < range`, then `cabacRenormAux fuel` terminates with
`CabacInv` (`256 ≤ range' ≤ 510` and `offset' < range'`). -/
theorem cabacRenormAux_sound :
    ∀ (fuel : Nat) (st : CabacState) (bits : List Nat),
      256 ≤ st.range * HPow.hPow (2 : Nat) fuel →
      st.range ≤ 510 →
      st.offset < st.range →
      CabacInv (cabacRenormAux fuel st bits).1
  | 0, st, _, hGe, hLe, hOff => by
    rw [pow2_zero, Nat.mul_one] at hGe
    exact ⟨hGe, hLe, hOff⟩
  | fuel + 1, st, bits, hGe, hLe, hOff => by
    rw [cabacRenormAux_succ]
    cases hblt : Nat.blt st.range 256 with
    | false =>
      have hge256 : 256 ≤ st.range := (blt_false_iff_ge st.range 256).mp hblt
      exact ⟨hge256, hLe, hOff⟩
    | true =>
      have hlt256 : st.range < 256 := (blt_true_iff_lt st.range 256).mp hblt
      have hMul : st.range * HPow.hPow (2 : Nat) (fuel + 1) =
          (st.range * 2) * HPow.hPow (2 : Nat) fuel := by
        rw [Nat.pow_succ, Nat.mul_comm (HPow.hPow (2 : Nat) fuel) 2,
            ← Nat.mul_assoc]
      rw [hMul] at hGe
      cases bits with
      | nil =>
        have hs := cabacRenormStep_preserves hlt256 hOff (by decide : 0 < 2)
        exact cabacRenormAux_sound fuel (cabacRenormStep st 0) [] hGe hs.1 hs.2
      | cons b rest =>
        have hbit : HMod.hMod b 2 < 2 := Nat.mod_lt b (by decide)
        have hs := cabacRenormStep_preserves hlt256 hOff hbit
        exact cabacRenormAux_sound fuel
          (cabacRenormStep st (HMod.hMod b 2)) rest hGe hs.1 hs.2

/-- H.264 CABAC §9.3.3.2.2 RenormD theorem: ANY pre-renorm state
(`2 ≤ range ≤ 510`, `offset < range`) is restored to `CabacInv`
(`256 ≤ range' ≤ 510 ∧ offset' < range'`) in at most `7` shifts
(`2 * 2^7 = 256`). -/
theorem cabacRenorm_sound {st : CabacState} (bits : List Nat)
    (hPre : CabacPreRenorm st) :
    CabacInv (cabacRenorm st bits).1 := by
  have hGe : 256 ≤ st.range * HPow.hPow (2 : Nat) 7 :=
    Nat.mul_le_mul_right (HPow.hPow (2 : Nat) 7) hPre.1
  exact cabacRenormAux_sound 7 st bits hGe hPre.2.1 hPre.2.2

/-! ## Part 2: AV1 (`rav1d`) MSAC 15-Bit Range Coder & CDF Split Math -/

/-- AV1 `rav1d` MSAC decoder register state `(rng, dif)` over 16-bit range. -/
structure MsacState where
  /-- Current 16-bit range (`[32768, 65536)` normalized). -/
  rng : Nat
  /-- Current range offset (`< rng`). -/
  dif : Nat

/-- Normalized AV1 MSAC state invariant (`32768 ≤ rng < 65536 ∧ dif < rng`). -/
@[expose] def MsacInv (st : MsacState) : Prop :=
  32768 ≤ st.rng ∧ st.rng < 65536 ∧ st.dif < st.rng

/-- Exact AV1 §8.2.6 / `rav1d` MSAC CDF symbol split point:
`(((rng >> 8) * (cdfProb >> 6)) >> 1) + 4 * remSyms`
(`EC_PROB_SHIFT = 6`, `EC_MIN_PROB = 4`) for 15-bit CDF entry `cdfProb` and
`remSyms` remaining symbols in the alphabet (`remSyms = N - i`). -/
@[expose] def msacSplitVal (rng cdfProb remSyms : Nat) : Nat :=
  HDiv.hDiv (HDiv.hDiv rng 256 * HDiv.hDiv cdfProb 64) 2 + 4 * remSyms

/-- For any normalized range `32768 ≤ rng`, proper 15-bit CDF entry
`cdfProb < 32768`, and AV1 alphabet remainder `remSyms ≤ 16`,
`msacSplitVal rng cdfProb remSyms ≤ rng`. -/
theorem msacSplitVal_le_rng {rng cdfProb remSyms : Nat}
    (hRng : 32768 ≤ rng) (hCdf : cdfProb < 32768) (hRem : remSyms ≤ 16) :
    msacSplitVal rng cdfProb remSyms ≤ rng := by
  unfold msacSplitVal
  have hqLo : 128 ≤ HDiv.hDiv rng 256 := nat_div_le_div_right 256 hRng
  have hcHi : HDiv.hDiv cdfProb 64 ≤ 511 :=
    nat_div_le_div_right 64 (Nat.le_of_lt_succ hCdf)
  have hProd : HDiv.hDiv rng 256 * HDiv.hDiv cdfProb 64 ≤
      HDiv.hDiv rng 256 * 511 :=
    Nat.mul_le_mul_left (HDiv.hDiv rng 256) hcHi
  have hDiv : HDiv.hDiv (HDiv.hDiv rng 256 * HDiv.hDiv cdfProb 64) 2 ≤
      HDiv.hDiv (HDiv.hDiv rng 256 * 511) 2 :=
    nat_div_le_div_right 2 hProd
  have hMin : 4 * remSyms ≤ 64 := Nat.mul_le_mul_left 4 hRem
  have hHalf :
      HDiv.hDiv (HDiv.hDiv rng 256 * 511) 2 + 64 ≤ HDiv.hDiv rng 256 * 256 := by
    have h2div : 2 * HDiv.hDiv (HDiv.hDiv rng 256 * 511) 2 ≤
        HDiv.hDiv rng 256 * 511 := by
      have hle := Nat.le_add_right
        (2 * HDiv.hDiv (HDiv.hDiv rng 256 * 511) 2)
        (HMod.hMod (HDiv.hDiv rng 256 * 511) 2)
      rw [Nat.div_add_mod] at hle
      exact hle
    have hDbl :
        2 * (HDiv.hDiv (HDiv.hDiv rng 256 * 511) 2 + 64) ≤
          2 * (HDiv.hDiv rng 256 * 256) := by
      rw [Nat.mul_add]
      have h1 : 2 * HDiv.hDiv (HDiv.hDiv rng 256 * 511) 2 + 2 * 64 ≤
          HDiv.hDiv rng 256 * 511 + HDiv.hDiv rng 256 :=
        Nat.add_le_add h2div hqLo
      have h2 : HDiv.hDiv rng 256 * 511 + HDiv.hDiv rng 256 =
          2 * (HDiv.hDiv rng 256 * 256) := by
        have ha : HDiv.hDiv rng 256 * 511 + HDiv.hDiv rng 256 =
            HDiv.hDiv rng 256 * 512 :=
          (Nat.mul_succ (HDiv.hDiv rng 256) 511).symm
        rw [ha, Nat.mul_comm 2, Nat.mul_assoc]
      rw [← h2]
      exact h1
    exact Nat.le_of_mul_le_mul_left hDbl (by decide : 0 < 2)
  have hQ256 : HDiv.hDiv rng 256 * 256 ≤ rng := by
    rw [Nat.mul_comm]
    have hle := Nat.le_add_right (256 * HDiv.hDiv rng 256) (HMod.hMod rng 256)
    rw [Nat.div_add_mod] at hle
    exact hle
  exact Nat.le_trans (Nat.add_le_add hDiv hMin) (Nat.le_trans hHalf hQ256)

/-- `msacSplitVal` is monotone in both `cdfProb` and `remSyms`: for any
monotone CDF table `c₁ ≤ c₂` and `r₁ ≤ r₂`, the split points satisfy
`msacSplitVal rng c₁ r₁ ≤ msacSplitVal rng c₂ r₂`. -/
theorem msacSplitVal_mono (rng : Nat) {c₁ c₂ r₁ r₂ : Nat}
    (hc : c₁ ≤ c₂) (hr : r₁ ≤ r₂) :
    msacSplitVal rng c₁ r₁ ≤ msacSplitVal rng c₂ r₂ := by
  unfold msacSplitVal
  have h1 : HDiv.hDiv (HDiv.hDiv rng 256 * HDiv.hDiv c₁ 64) 2 ≤
      HDiv.hDiv (HDiv.hDiv rng 256 * HDiv.hDiv c₂ 64) 2 :=
    nat_div_le_div_right 2
      (Nat.mul_le_mul_left (HDiv.hDiv rng 256) (nat_div_le_div_right 64 hc))
  exact Nat.add_le_add h1 (Nat.mul_le_mul_left 4 hr)

/-- Strict minimum-probability separation (`EC_MIN_PROB = 4`): for any
non-decreasing pair `c₁ ≤ c₂`, stepping `remSyms` from `r` to `r + 1` separates
adjacent split points by at least `4`, guaranteeing every symbol sub-range has
width `≥ 4 ≥ 1` for `msacRenorm_sound`. -/
theorem msacSplitVal_step_gap (rng : Nat) {c₁ c₂ : Nat} (r : Nat)
    (hc : c₁ ≤ c₂) :
    msacSplitVal rng c₁ r + 4 ≤ msacSplitVal rng c₂ (r + 1) := by
  have hm := msacSplitVal_mono rng hc (Nat.le_refl r)
  have hEq : msacSplitVal rng c₂ (r + 1) = msacSplitVal rng c₂ r + 4 := by
    unfold msacSplitVal
    rw [Nat.mul_succ, Nat.add_assoc]
  rw [hEq]
  exact Nat.add_le_add_right hm 4

/-- `msacSplitVal rng 0 remSyms = 4 * remSyms`. -/
theorem msacSplitVal_zero (rng remSyms : Nat) :
    msacSplitVal rng 0 remSyms = 4 * remSyms := by
  unfold msacSplitVal
  rw [Nat.zero_div, Nat.mul_zero, Nat.zero_div, Nat.zero_add]

/-- One AV1 MSAC 1-bit renormalization shift step. -/
@[expose] def msacRenormStep (st : MsacState) (bit : Nat) : MsacState :=
  { rng := st.rng * 2, dif := st.dif * 2 + bit }

/-- A single MSAC renormalization shift when `rng < 32768`, `dif < rng`, and
`bit < 2` preserves `rng' < 65536` and `dif' < rng'`. -/
theorem msacRenormStep_preserves {st : MsacState} {bit : Nat}
    (hRng : st.rng < 32768) (hDif : st.dif < st.rng) (hBit : bit < 2) :
    (msacRenormStep st bit).rng < 65536 ∧
    (msacRenormStep st bit).dif < (msacRenormStep st bit).rng := by
  unfold msacRenormStep
  dsimp only
  constructor
  · exact Nat.mul_lt_mul_of_pos_right hRng (by decide : 0 < 2)
  · have h1 : st.dif * 2 + bit < st.dif * 2 + 2 := Nat.add_lt_add_left hBit _
    have h2 : st.dif * 2 + 2 = (st.dif + 1) * 2 := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right 2 hDif)

/-- Iterative AV1 MSAC bit-renormalization loop (`@Nat.rec`, `0`
`._unsafe_rec`) restoring `32768 ≤ rng < 65536`. -/
@[expose] def msacRenormAux (fuel : Nat) (st : MsacState) (bits : List Nat) :
    MsacState × List Nat :=
  @Nat.rec (fun _ => MsacState → List Nat → MsacState × List Nat)
    (fun s bs => (s, bs))
    (fun _ ih s bs =>
      if Nat.blt s.rng 32768 then
        match bs with
        | [] => ih (msacRenormStep s 0) []
        | b :: rest => ih (msacRenormStep s (HMod.hMod b 2)) rest
      else
        (s, bs))
    fuel st bits

/-- Step equation for `msacRenormAux`. -/
theorem msacRenormAux_succ (fuel : Nat) (st : MsacState) (bits : List Nat) :
    msacRenormAux (fuel + 1) st bits =
      if Nat.blt st.rng 32768 then
        match bits with
        | [] => msacRenormAux fuel (msacRenormStep st 0) []
        | b :: rest =>
          msacRenormAux fuel (msacRenormStep st (HMod.hMod b 2)) rest
      else
        (st, bits) :=
  rfl

/-- Canonical 15-shift AV1 MSAC renormalization (`msac_renorm`). -/
@[expose] def msacRenorm (st : MsacState) (bits : List Nat) :
    MsacState × List Nat :=
  msacRenormAux 15 st bits

/-- General fuel-indexed MSAC renormalization soundness. -/
theorem msacRenormAux_sound :
    ∀ (fuel : Nat) (st : MsacState) (bits : List Nat),
      32768 ≤ st.rng * HPow.hPow (2 : Nat) fuel →
      st.rng < 65536 →
      st.dif < st.rng →
      MsacInv (msacRenormAux fuel st bits).1
  | 0, st, _, hGe, hLt, hDif => by
    rw [pow2_zero, Nat.mul_one] at hGe
    exact ⟨hGe, hLt, hDif⟩
  | fuel + 1, st, bits, hGe, hLt, hDif => by
    rw [msacRenormAux_succ]
    cases hblt : Nat.blt st.rng 32768 with
    | false =>
      exact ⟨(blt_false_iff_ge st.rng 32768).mp hblt, hLt, hDif⟩
    | true =>
      have hlt : st.rng < 32768 := (blt_true_iff_lt st.rng 32768).mp hblt
      have hMul : st.rng * HPow.hPow (2 : Nat) (fuel + 1) =
          (st.rng * 2) * HPow.hPow (2 : Nat) fuel := by
        rw [Nat.pow_succ, Nat.mul_comm (HPow.hPow (2 : Nat) fuel) 2,
            ← Nat.mul_assoc]
      rw [hMul] at hGe
      cases bits with
      | nil =>
        have hs := msacRenormStep_preserves hlt hDif (by decide : 0 < 2)
        exact msacRenormAux_sound fuel (msacRenormStep st 0) [] hGe hs.1 hs.2
      | cons b rest =>
        have hbit : HMod.hMod b 2 < 2 := Nat.mod_lt b (by decide)
        have hs := msacRenormStep_preserves hlt hDif hbit
        exact msacRenormAux_sound fuel
          (msacRenormStep st (HMod.hMod b 2)) rest hGe hs.1 hs.2

/-- AV1 `rav1d` MSAC renormalization theorem: ANY non-degenerate state
(`1 ≤ rng < 65536`, `dif < rng`) is restored to `MsacInv`
(`32768 ≤ rng' < 65536 ∧ dif' < rng'`) in at most `15` shifts
(`1 * 2^15 = 32768`). -/
theorem msacRenorm_sound {st : MsacState} (bits : List Nat)
    (hPos : 1 ≤ st.rng) (hLt : st.rng < 65536) (hDif : st.dif < st.rng) :
    MsacInv (msacRenorm st bits).1 := by
  have hGe : 32768 ≤ st.rng * HPow.hPow (2 : Nat) 15 :=
    Nat.mul_le_mul_right (HPow.hPow (2 : Nat) 15) hPos
  exact msacRenormAux_sound 15 st bits hGe hLt hDif

end Anneal.MediaDsp.EntropyMath

end
