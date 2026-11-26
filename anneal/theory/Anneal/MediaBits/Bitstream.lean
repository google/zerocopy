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
public import Anneal.InitLemmas
public import Anneal.NatBitwise

public section

/-!
# Bit-Slice, Leading-Zero Exp-Golomb, LEB128, and Packed-Lane Lemmas

Zero-duplication 0-TCB extension to merged `Anneal.MediaBits` (`Rbsp` +
`BitCursor`) and `Anneal.LeBytes`, providing concrete word- and byte-level
codec lemmas reused across FFmpeg H.264 (`decode_ue_golomb_u32`,
`read_ue_golomb`, SWAR/YUV pixel unpacking), AV1 `rav1d` (OBU unsigned LEB128),
and MP4/PSSH demuxing:

1. **Bit-Slice & Packed-Lane Extraction (`bitSlice`, `byteLane`,
   `pixel10Lane`):** exact bounds, zero-width/full-width identities, adjacent
   slice concatenation (`bitSlice_adjacent`), shift/scale laws, and
   `byte_decomp` (reusable in SWAR zero-byte detection and YUV lane packing).
2. **Bitwise Mask & Shift-OR Identities:** `nat_land_two_pow_sub_one_eq_mod`,
   `nat_land_seven`, `nat_land_one`, `nat_land_127`, `nat_land_255`, and
   `nat_lor_mul_two_add_bit`.
3. **Word-Level Leading-Zero Count (`clzN`) & Exp-Golomb (`decodeUeWord` /
   `encodeUeWord`):** `@Nat.rec` `clzN w x` with `clzN_le`, `clzN_zero`,
   `clzN_lt_of_pos`, `clzN_pow2_bounds`, and `decodeUeWord_encodeUeWord`.
4. **AV1 OBU Unsigned LEB128 (`encodeLeb128` / `decodeLeb128`):**
   7-bit-payload continuation-bit (`0x80`) varint codec with exact `PutGet`
   round-trip (`decodeLeb128_encodeLeb128`) and decoded value range bounds.
5. **Big-Endian & Little-Endian `Nat`-Byte Word Unpacking (`beU16Nat`,
   `beU32Nat`, `beU64Nat`, `leU32Nat`):** exact bounds, byte-lane round-trip
   identities, and injectivity for MP4/PSSH box headers.

Operations use `HPow.hPow`, `HDiv.hDiv`, and `HMod.hMod` so every statement
satisfies `TrustedBoundary.allowedTheorySyntaxKinds` while matching standard
`/`, `%`, `^` lemmas under `rw`. All recursive definitions use `@Nat.rec`
(`0` `._unsafe_rec`, `0` `noncomputable`, `0` `omega`, `0` `bv_decide`,
`0` `by_cases`), with axioms `⊆ [propext, Quot.sound]` (`0` `Classical.choice`).
-/

namespace Anneal.MediaBits.Bitstream

open Anneal.InitLemmas

/-! ## Part 0: Local Power-of-Two & Modular Arithmetic Helpers -/

private theorem pow2_zero : HPow.hPow (2 : Nat) 0 = 1 := rfl

private theorem pow2_succ_eq (n : Nat) :
    HPow.hPow (2 : Nat) (n + 1) = HPow.hPow (2 : Nat) n * 2 :=
  Nat.pow_succ 2 n

private theorem pow2_succ_add (n : Nat) :
    HPow.hPow (2 : Nat) (n + 1) =
      HPow.hPow (2 : Nat) n + HPow.hPow (2 : Nat) n := by
  rw [pow2_succ_eq, Nat.mul_two]

private theorem pow2_pos (n : Nat) : 0 < HPow.hPow (2 : Nat) n :=
  nat_two_pow_pos n

private theorem pow2_add_eq (a b : Nat) :
    HPow.hPow (2 : Nat) (a + b) =
      HPow.hPow (2 : Nat) a * HPow.hPow (2 : Nat) b := by
  induction b with
  | zero => rw [Nat.add_zero, pow2_zero, Nat.mul_one]
  | succ k ih =>
    rw [Nat.add_succ, pow2_succ_eq, pow2_succ_eq, ih, Nat.mul_assoc]

private theorem pow2_le_of_le {a b : Nat} (h : a ≤ b) :
    HPow.hPow (2 : Nat) a ≤ HPow.hPow (2 : Nat) b :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

private theorem nat_mod_mul_split_pos (v a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    HMod.hMod v (a * b) =
      HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b := by
  have hq : HDiv.hDiv v a =
      b * HDiv.hDiv (HDiv.hDiv v a) b + HMod.hMod (HDiv.hDiv v a) b :=
    Eq.symm (Nat.div_add_mod (HDiv.hDiv v a) b)
  have hv : v = HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b +
      (a * b) * HDiv.hDiv (HDiv.hDiv v a) b := by
    have h1 : v = a * HDiv.hDiv v a + HMod.hMod v a :=
      Eq.symm (Nat.div_add_mod v a)
    rw [hq, Nat.mul_add, ← Nat.mul_assoc] at h1
    rw [Nat.add_comm (a * b * HDiv.hDiv (HDiv.hDiv v a) b)
          (a * HMod.hMod (HDiv.hDiv v a) b),
        Nat.add_assoc,
        Nat.add_comm (a * b * HDiv.hDiv (HDiv.hDiv v a) b) (HMod.hMod v a),
        ← Nat.add_assoc,
        Nat.add_comm (a * HMod.hMod (HDiv.hDiv v a) b) (HMod.hMod v a)] at h1
    exact h1
  have hlt : HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b < a * b := by
    have hma : HMod.hMod v a < a := Nat.mod_lt v ha
    have hmb : HMod.hMod (HDiv.hDiv v a) b < b := Nat.mod_lt (HDiv.hDiv v a) hb
    have h1 : HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b <
        a + a * HMod.hMod (HDiv.hDiv v a) b :=
      Nat.add_lt_add_right hma (a * HMod.hMod (HDiv.hDiv v a) b)
    have h2 : a + a * HMod.hMod (HDiv.hDiv v a) b =
        a * (HMod.hMod (HDiv.hDiv v a) b + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left a hmb)
  have hm := congrArg (fun z => HMod.hMod z (a * b)) hv
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt] at hm
  exact hm

private theorem nat_div_two_mul_add_bit (q b : Nat) (hb : b < 2) :
    HDiv.hDiv (q * 2 + b) 2 = q := by
  have h1 : q * 2 + b = b + 2 * q := by
    rw [Nat.mul_comm q 2, Nat.add_comm]
  rw [h1, Nat.add_mul_div_left b q (by decide : 0 < 2),
      Nat.div_eq_of_lt hb, Nat.zero_add]

private theorem nat_mod_two_mul_add_bit (q b : Nat) (hb : b < 2) :
    HMod.hMod (q * 2 + b) 2 = b := by
  have h1 : q * 2 + b = b + 2 * q := by
    rw [Nat.mul_comm q 2, Nat.add_comm]
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

private theorem nat_sub_one_div_two_pow (w : Nat) :
    HDiv.hDiv (HPow.hPow (2 : Nat) (w + 1) - 1) 2 =
      HPow.hPow (2 : Nat) w - 1 := by
  have hpos : 0 < HPow.hPow (2 : Nat) w := pow2_pos w
  have heq : HPow.hPow (2 : Nat) (w + 1) - 1 =
      (HPow.hPow (2 : Nat) w - 1) * 2 + 1 := by
    rw [pow2_succ_eq]
    have hm : HPow.hPow (2 : Nat) w = (HPow.hPow (2 : Nat) w - 1) + 1 :=
      (Nat.sub_add_cancel hpos).symm
    have h2 : ((HPow.hPow (2 : Nat) w - 1) + 1) * 2 =
        (HPow.hPow (2 : Nat) w - 1) * 2 + 2 := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hm, h2]
    rfl
  rw [heq]
  exact nat_div_two_mul_add_bit (HPow.hPow (2 : Nat) w - 1) 1 (by decide)

private theorem nat_sub_one_mod_two_pow (w : Nat) :
    HMod.hMod (HPow.hPow (2 : Nat) (w + 1) - 1) 2 = 1 := by
  have hpos : 0 < HPow.hPow (2 : Nat) w := pow2_pos w
  have heq : HPow.hPow (2 : Nat) (w + 1) - 1 =
      (HPow.hPow (2 : Nat) w - 1) * 2 + 1 := by
    rw [pow2_succ_eq]
    have hm : HPow.hPow (2 : Nat) w = (HPow.hPow (2 : Nat) w - 1) + 1 :=
      (Nat.sub_add_cancel hpos).symm
    have h2 : ((HPow.hPow (2 : Nat) w - 1) + 1) * 2 =
        (HPow.hPow (2 : Nat) w - 1) * 2 + 2 := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hm, h2]
    rfl
  rw [heq]
  exact nat_mod_two_mul_add_bit (HPow.hPow (2 : Nat) w - 1) 1 (by decide)

/-! ## Part 1: Bit-Slice & Packed-Lane Extraction -/

/-- Extract the `w`-bit unsigned field starting at bit offset `lo` of `x`,
i.e. `(x / 2^lo) % 2^w`. -/
@[expose] def bitSlice (x lo w : Nat) : Nat :=
  HMod.hMod (HDiv.hDiv x (HPow.hPow (2 : Nat) lo)) (HPow.hPow (2 : Nat) w)

/-- Extract byte `k` (8 bits at offset `8 * k`) of `x`. -/
@[expose] def byteLane (x k : Nat) : Nat :=
  bitSlice x (8 * k) 8

/-- Extract 10-bit pixel lane `k` (at offset `10 * k`) of a packed word `x`. -/
@[expose] def pixel10Lane (x k : Nat) : Nat :=
  bitSlice x (10 * k) 10

/-- Every `w`-bit slice is strictly below `2^w`. -/
theorem bitSlice_lt (x lo w : Nat) : bitSlice x lo w < HPow.hPow (2 : Nat) w :=
  Nat.mod_lt _ (pow2_pos w)

/-- Every extracted byte lane is strictly below `256`. -/
theorem byteLane_lt (x k : Nat) : byteLane x k < 256 :=
  bitSlice_lt x (8 * k) 8

/-- Every extracted 10-bit pixel lane is strictly below `1024`. -/
theorem pixel10Lane_lt (x k : Nat) : pixel10Lane x k < 1024 :=
  bitSlice_lt x (10 * k) 10

/-- A zero-width bit slice is always `0`. -/
theorem bitSlice_zero_width (x lo : Nat) : bitSlice x lo 0 = 0 :=
  Nat.mod_one _

/-- Any bit slice of `0` is `0`. -/
theorem bitSlice_zero_val (lo w : Nat) : bitSlice 0 lo w = 0 := by
  unfold bitSlice
  rw [Nat.zero_div, Nat.zero_mod]

/-- Taking the low `w` bits of a value already `< 2^w` returns `x`. -/
theorem bitSlice_full_of_lt {x w : Nat} (hx : x < HPow.hPow (2 : Nat) w) :
    bitSlice x 0 w = x := by
  unfold bitSlice
  rw [pow2_zero, Nat.div_one, Nat.mod_eq_of_lt hx]

/-- Shifting a value by `2^lo` and adding a low part `< 2^lo` preserves the
high `w`-bit slice at offset `lo`. -/
theorem bitSlice_shift_add {hi low lo w : Nat}
    (hlow : low < HPow.hPow (2 : Nat) lo) :
    bitSlice (low + HPow.hPow (2 : Nat) lo * hi) lo w =
      HMod.hMod hi (HPow.hPow (2 : Nat) w) := by
  unfold bitSlice
  rw [Nat.add_mul_div_left low hi (pow2_pos lo), Nat.div_eq_of_lt hlow,
      Nat.zero_add]

/-- Shifting a value by `2^lo` and adding a low part `< 2^lo` preserves the
low `lo`-bit slice at offset `0`. -/
theorem bitSlice_low_of_shift_add {hi low lo : Nat}
    (hlow : low < HPow.hPow (2 : Nat) lo) :
    bitSlice (low + HPow.hPow (2 : Nat) lo * hi) 0 lo = low := by
  unfold bitSlice
  rw [pow2_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]

/-- Splitting a `(w₁ + w₂)`-bit slice at `lo` into its adjacent low `w₁`-bit
and high `w₂`-bit slices. -/
theorem bitSlice_adjacent (x lo w₁ w₂ : Nat) :
    bitSlice x lo (w₁ + w₂) =
      bitSlice x lo w₁ + HPow.hPow (2 : Nat) w₁ * bitSlice x (lo + w₁) w₂ := by
  unfold bitSlice
  rw [pow2_add_eq w₁ w₂,
      nat_mod_mul_split_pos (HDiv.hDiv x (HPow.hPow (2 : Nat) lo))
        (HPow.hPow (2 : Nat) w₁) (HPow.hPow (2 : Nat) w₂)
        (pow2_pos w₁) (pow2_pos w₂),
      Nat.div_div_eq_div_mul, ← pow2_add_eq lo w₁]

/-- Scaling by `2^s` shifts slice coordinates by `s`. -/
theorem bitSlice_mul_pow2 (x s lo w : Nat) :
    bitSlice (x * HPow.hPow (2 : Nat) s) (lo + s) w = bitSlice x lo w := by
  unfold bitSlice
  rw [pow2_add_eq lo s,
      Nat.mul_comm (HPow.hPow (2 : Nat) lo) (HPow.hPow (2 : Nat) s),
      ← Nat.div_div_eq_div_mul, Nat.mul_comm x (HPow.hPow (2 : Nat) s),
      Nat.mul_div_cancel_left x (pow2_pos s)]

/-- Dividing by `2^s` shifts slice coordinates upward by `s`. -/
theorem bitSlice_div_pow2 (x s lo w : Nat) :
    bitSlice (HDiv.hDiv x (HPow.hPow (2 : Nat) s)) lo w =
      bitSlice x (s + lo) w := by
  unfold bitSlice
  rw [Nat.div_div_eq_div_mul, ← pow2_add_eq s lo]

/-- Decompose any natural `z` around radix position `P` into high part,
byte `(z / P) % 256`, and low part `z % P` (reusable in SWAR byte-lane
proofs). -/
theorem byte_decomp (z P : Nat) :
    z = (P * 256) * HDiv.hDiv (HDiv.hDiv z P) 256 +
        (HMod.hMod (HDiv.hDiv z P) 256 * P + HMod.hMod z P) := by
  have hq : HDiv.hDiv z P =
      256 * HDiv.hDiv (HDiv.hDiv z P) 256 + HMod.hMod (HDiv.hDiv z P) 256 :=
    Eq.symm (Nat.div_add_mod (HDiv.hDiv z P) 256)
  have hz : z = P * HDiv.hDiv z P + HMod.hMod z P :=
    Eq.symm (Nat.div_add_mod z P)
  rw [hq, Nat.mul_add, ← Nat.mul_assoc,
      Nat.mul_comm P (HMod.hMod (HDiv.hDiv z P) 256), Nat.add_assoc] at hz
  exact hz

/-! ## Part 2: Bitwise Masking & Shift-OR Identities -/

/-- Bitwise AND with low-`w`-bit mask `2^w - 1` equals `n % 2^w`. -/
theorem nat_land_two_pow_sub_one_eq_mod (w : Nat) :
    ∀ n : Nat,
      Nat.land n (HPow.hPow (2 : Nat) w - 1) =
        HMod.hMod n (HPow.hPow (2 : Nat) w) := by
  induction w with
  | zero =>
    intro n
    rw [pow2_zero, Nat.mod_one, Anneal.NatBitwise.land_eq_bitwise,
        Anneal.NatBitwise.unfold_eq]
    cases n with
    | zero => rfl
    | succ _ =>
      rw [ite_false_of (fun h => nomatch h), ite_true_of rfl]
      rfl
  | succ w ih =>
    intro n
    rw [Anneal.NatBitwise.land_eq_bitwise, Anneal.NatBitwise.unfold_eq]
    cases n with
    | zero =>
      rw [ite_true_of rfl, Nat.zero_mod]
      rfl
    | succ n' =>
      have hmaskPos : 0 < HPow.hPow (2 : Nat) (w + 1) - 1 := by
        have h2 : 2 ≤ HPow.hPow (2 : Nat) (w + 1) := by
          rw [pow2_succ_add]
          exact Nat.add_le_add (pow2_pos w) (pow2_pos w)
        exact Nat.sub_pos_of_lt h2
      have hmaskNe : HPow.hPow (2 : Nat) (w + 1) - 1 ≠ 0 :=
        Nat.ne_of_gt hmaskPos
      rw [ite_false_of (fun h => nomatch h), ite_false_of hmaskNe]
      dsimp only
      have hdivM : Nat.div (HPow.hPow (2 : Nat) (w + 1) - 1) 2 =
          HPow.hPow (2 : Nat) w - 1 :=
        nat_sub_one_div_two_pow w
      have hmodM : Nat.mod (HPow.hPow (2 : Nat) (w + 1) - 1) 2 = 1 :=
        nat_sub_one_mod_two_pow w
      rw [hdivM, hmodM, ← Anneal.NatBitwise.land_eq_bitwise,
          ih (Nat.div (Nat.succ n') 2)]
      have hsplit : HMod.hMod (Nat.succ n') (HPow.hPow (2 : Nat) (w + 1)) =
          HMod.hMod (Nat.succ n') 2 +
            2 * HMod.hMod (HDiv.hDiv (Nat.succ n') 2)
              (HPow.hPow (2 : Nat) w) := by
        have hp : HPow.hPow (2 : Nat) (w + 1) = 2 * HPow.hPow (2 : Nat) w := by
          rw [pow2_succ_eq, Nat.mul_comm]
        rw [hp]
        exact nat_mod_mul_split_pos (Nat.succ n') 2 (HPow.hPow (2 : Nat) w)
          (by decide) (pow2_pos w)
      rw [hsplit]
      have hmod2 : HMod.hMod (Nat.succ n') 2 < 2 := Nat.mod_lt _ (by decide)
      cases hbit : Nat.mod (Nat.succ n') 2 with
      | zero =>
        have hbit' : HMod.hMod (Nat.succ n') 2 = 0 := hbit
        rw [hbit', Nat.zero_add, Nat.two_mul]
        rfl
      | succ b' =>
        cases b' with
        | zero =>
          have hbit' : HMod.hMod (Nat.succ n') 2 = 1 := hbit
          rw [hbit', Nat.two_mul, Nat.add_comm 1]
          rfl
        | succ b'' =>
          have hbit' : HMod.hMod (Nat.succ n') 2 = b'' + 2 := hbit
          rw [hbit'] at hmod2
          have hge : 2 ≤ b'' + 2 := Nat.le_add_left 2 b''
          exact False.elim (Nat.not_lt_of_ge hge hmod2)

/-- Low-3-bit mask identity (`n &&& 7 = n % 8`), used for byte-bit offsets. -/
theorem nat_land_seven (n : Nat) : Nat.land n 7 = HMod.hMod n 8 :=
  nat_land_two_pow_sub_one_eq_mod 3 n

/-- Low-1-bit mask identity (`n &&& 1 = n % 2`), used for parity/bit reads. -/
theorem nat_land_one (n : Nat) : Nat.land n 1 = HMod.hMod n 2 :=
  nat_land_two_pow_sub_one_eq_mod 1 n

/-- Low-7-bit mask identity (`n &&& 127 = n % 128`), used in AV1 LEB128. -/
theorem nat_land_127 (n : Nat) : Nat.land n 127 = HMod.hMod n 128 :=
  nat_land_two_pow_sub_one_eq_mod 7 n

/-- Low-8-bit mask identity (`n &&& 255 = n % 256`), used in byte packing. -/
theorem nat_land_255 (n : Nat) : Nat.land n 255 = HMod.hMod n 256 :=
  nat_land_two_pow_sub_one_eq_mod 8 n

/-- Shifting `acc` left by 1 bit and OR-ing in a single bit `b < 2` equals
`acc * 2 + b` (reusable in H.264 Exp-Golomb and bit-reader loops). -/
theorem nat_lor_mul_two_add_bit (acc b : Nat) (hb : b < 2) :
    Nat.lor (acc * 2) b = acc * 2 + b := by
  cases b with
  | zero =>
    rw [Nat.add_zero, Anneal.NatBitwise.lor_eq_bitwise,
        Anneal.NatBitwise.unfold_eq]
    cases acc with
    | zero => rfl
    | succ a' =>
      have hne : Nat.succ a' * 2 ≠ 0 := by
        rw [Nat.succ_mul]
        exact fun h => nomatch h
      rw [ite_false_of hne, ite_true_of rfl]
      rfl
  | succ b' =>
    cases b' with
    | zero =>
      rw [Anneal.NatBitwise.lor_eq_bitwise, Anneal.NatBitwise.unfold_eq]
      cases acc with
      | zero => rfl
      | succ a' =>
        have hne : Nat.succ a' * 2 ≠ 0 := by
          rw [Nat.succ_mul]
          exact fun h => nomatch h
        rw [ite_false_of hne, ite_false_of (fun h => nomatch h)]
        dsimp only
        have hd : Nat.div (Nat.succ a' * 2) 2 = Nat.succ a' := by
          change HDiv.hDiv (Nat.succ a' * 2) 2 = Nat.succ a'
          rw [Nat.mul_comm]
          exact Nat.mul_div_cancel_left (Nat.succ a') (by decide)
        have hm : Nat.mod (Nat.succ a' * 2) 2 = 0 := by
          change HMod.hMod (Nat.succ a' * 2) 2 = 0
          rw [Nat.mul_comm]
          exact Nat.mul_mod_right 2 (Nat.succ a')
        rw [hd, hm]
        have hrec : Nat.bitwise or (Nat.succ a') 0 = Nat.succ a' := by
          rw [Anneal.NatBitwise.unfold_eq, ite_false_of (fun h => nomatch h),
              ite_true_of rfl]
          rfl
        rw [hrec]
        change (if or false true = true then _ else _) = _
        rw [Nat.mul_two]
        rfl
    | succ b'' =>
      have hge : 2 ≤ b'' + 2 := Nat.le_add_left 2 b''
      exact False.elim (Nat.not_lt_of_ge hge hb)

/-! ## Part 3: Word-Level Leading-Zero Count (`clzN`) & Exp-Golomb Words -/

/-- Number of leading zero bits of `x` viewed as a `w`-bit unsigned word
(`x < 2^w`), defined structurally via `@Nat.rec` (`0` `._unsafe_rec`). Returns
`w` when `x = 0`; does not mask `x % 2^w`, so returns `0` whenever `w > 0` and
`2^(w - 1) ≤ x`. -/
@[expose] def clzN (w x : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun k ih => if Nat.ble (HPow.hPow (2 : Nat) k) x then 0 else ih + 1)
    w

/-- Base equation `clzN 0 x = 0`. -/
theorem clzN_zero_width (x : Nat) : clzN 0 x = 0 := rfl

/-- Step equation for `clzN (w + 1) x`. -/
theorem clzN_succ (w x : Nat) :
    clzN (w + 1) x =
      if Nat.ble (HPow.hPow (2 : Nat) w) x then 0 else clzN w x + 1 := rfl

/-- `clzN w x` never exceeds the word width `w`. -/
theorem clzN_le (w x : Nat) : clzN w x ≤ w := by
  induction w with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    rw [clzN_succ]
    cases Nat.ble (HPow.hPow (2 : Nat) k) x with
    | true => exact Nat.zero_le _
    | false => exact Nat.succ_le_succ ih

/-- `clzN w 0 = w` for every width `w`. -/
theorem clzN_zero (w : Nat) : clzN w 0 = w := by
  induction w with
  | zero => rfl
  | succ k ih =>
    rw [clzN_succ]
    have hble : Nat.ble (HPow.hPow (2 : Nat) k) 0 = false := by
      cases h : HPow.hPow (2 : Nat) k with
      | zero =>
        have hp := pow2_pos k
        rw [h] at hp
        exact False.elim (Nat.not_lt_zero 0 hp)
      | succ _ => rfl
    rw [hble]
    change clzN k 0 + 1 = k + 1
    rw [ih]

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

private theorem ble_false_iff_lt (a b : Nat) :
    Nat.ble a b = false ↔ b < a := by
  constructor
  · intro hf
    cases Nat.lt_or_ge b a with
    | inl hlt => exact hlt
    | inr hge =>
      have ht := (ble_true_iff_le a b).mpr hge
      rw [hf] at ht
      exact Bool.noConfusion ht
  · intro hlt
    cases hb : Nat.ble a b with
    | false => rfl
    | true =>
      exact False.elim (Nat.not_lt_of_ge ((ble_true_iff_le a b).mp hb) hlt)

/-- If the MSB of a `w + 1`-bit word is set (`2^w ≤ x`),
`clzN (w + 1) x = 0`. -/
theorem clzN_eq_zero_of_msb {w x : Nat} (h : HPow.hPow (2 : Nat) w ≤ x) :
    clzN (w + 1) x = 0 := by
  rw [clzN_succ, (ble_true_iff_le _ _).mpr h]
  rfl

/-- Every nonzero word `0 < x` has `clzN w x < w` whenever `w > 0`. -/
theorem clzN_lt_of_pos : ∀ {w x : Nat}, 0 < w → 0 < x → clzN w x < w
  | 0, _, hw, _ => False.elim (Nat.not_lt_zero 0 hw)
  | 1, x, _, hx => by
    rw [clzN_succ, pow2_zero, (ble_true_iff_le 1 x).mpr hx]
    exact Nat.zero_lt_one
  | k + 2, x, _, hx => by
    rw [clzN_succ]
    cases Nat.ble (HPow.hPow (2 : Nat) (k + 1)) x with
    | true => exact Nat.zero_lt_succ _
    | false =>
      exact Nat.succ_lt_succ (clzN_lt_of_pos (Nat.zero_lt_succ k) hx)

/-- Tight power-of-two sandwich for any nonzero `w`-bit word `0 < x < 2^w`:
`2^(w - 1 - clzN w x) ≤ x < 2^(w - clzN w x)`. -/
theorem clzN_pow2_bounds :
    ∀ {w x : Nat}, 0 < x → x < HPow.hPow (2 : Nat) w →
      HPow.hPow (2 : Nat) (w - 1 - clzN w x) ≤ x ∧
        x < HPow.hPow (2 : Nat) (w - clzN w x)
  | 0, x, hx, hlt => by
    rw [pow2_zero] at hlt
    have h0 : x = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
    rw [h0] at hx
    exact False.elim (Nat.not_lt_zero 0 hx)
  | w + 1, x, hx, hlt => by
    rw [clzN_succ]
    cases hb : Nat.ble (HPow.hPow (2 : Nat) w) x with
    | true =>
      have hge : HPow.hPow (2 : Nat) w ≤ x := (ble_true_iff_le _ _).mp hb
      change HPow.hPow (2 : Nat) (w + 1 - 1 - 0) ≤ x ∧
        x < HPow.hPow (2 : Nat) (w + 1 - 0)
      rw [Nat.add_sub_cancel, Nat.sub_zero, Nat.sub_zero]
      exact ⟨hge, hlt⟩
    | false =>
      have hltW : x < HPow.hPow (2 : Nat) w := (ble_false_iff_lt _ _).mp hb
      have ih := clzN_pow2_bounds (w := w) (x := x) hx hltW
      change HPow.hPow (2 : Nat) (w + 1 - 1 - (clzN w x + 1)) ≤ x ∧
        x < HPow.hPow (2 : Nat) (w + 1 - (clzN w x + 1))
      rw [Nat.add_sub_cancel, Nat.succ_sub_succ]
      have hsub : w - (clzN w x + 1) = w - 1 - clzN w x := by
        rw [Nat.sub_sub, Nat.add_comm 1 (clzN w x)]
      rw [hsub]
      exact ih

/-- Pack an Exp-Golomb code number `v` (with `lz` leading zeros where
`2^lz ≤ v + 1 < 2^(lz + 1)`) into the top `2 * lz + 1` bits of a `w`-bit
MSB-aligned cache word with arbitrary `w - (2 * lz + 1)`-bit trailer `trail`. -/
@[expose] def encodeUeWord (w lz v trail : Nat) : Nat :=
  (v + 1) * HPow.hPow (2 : Nat) (w - (2 * lz + 1)) + trail

/-- Word-level H.264 unsigned Exp-Golomb decoder matching
`get_ue_golomb_long` / `decode_ue_golomb_u32`: returns `(bitsConsumed, codeNum)`
from an MSB-aligned `w`-bit cache word `word` (intended for well-formed inputs
satisfying `2 * clzN w word + 1 ≤ w`; otherwise `w - len` saturates to `0` in
`Nat`). -/
@[expose] def decodeUeWord (w word : Nat) : Nat × Nat :=
  let lz := clzN w word
  let len := 2 * lz + 1
  let codePlusOne := HDiv.hDiv word (HPow.hPow (2 : Nat) (w - len))
  (len, codePlusOne - 1)

/-- Exact inverse theorem for word-level H.264 Exp-Golomb decoding: for any
`w`-bit word carrying `encodeUeWord w lz v trail` with
`2^lz ≤ v + 1 < 2^(lz + 1)`,
`2 * lz + 1 ≤ w`, and `trail < 2^(w - (2 * lz + 1))`, `decodeUeWord w` recovers
exactly `(2 * lz + 1, v)` regardless of the trailing bits `trail`. -/
theorem decodeUeWord_encodeUeWord {w lz v trail : Nat}
    (hLen : 2 * lz + 1 ≤ w)
    (hLo : HPow.hPow (2 : Nat) lz ≤ v + 1)
    (hHi : v + 1 < HPow.hPow (2 : Nat) (lz + 1))
    (hTrail : trail < HPow.hPow (2 : Nat) (w - (2 * lz + 1))) :
    decodeUeWord w (encodeUeWord w lz v trail) = (2 * lz + 1, v) := by
  have hShift : w - (2 * lz + 1) + lz = w - 1 - lz := by
    have h1 : w - (2 * lz + 1) + (2 * lz + 1) = w := Nat.sub_add_cancel hLen
    have h2 : 2 * lz + 1 = lz + (lz + 1) := by
      rw [Nat.two_mul, Nat.add_assoc]
    have h3 : (w - (2 * lz + 1) + lz) + (lz + 1) = w := by
      rw [Nat.add_assoc, ← h2]
      exact h1
    have h4 : w - 1 - lz = w - (lz + 1) := by
      rw [Nat.sub_sub, Nat.add_comm 1 lz]
    rw [h4]
    exact (Nat.add_sub_cancel (w - (2 * lz + 1) + lz) (lz + 1)).symm.trans
      (congrArg (fun x => x - (lz + 1)) h3)
  have hShiftHi : w - (2 * lz + 1) + (lz + 1) = w - lz := by
    have h1 : w - (2 * lz + 1) + (2 * lz + 1) = w := Nat.sub_add_cancel hLen
    have h2 : 2 * lz + 1 = (lz + 1) + lz := by
      rw [Nat.two_mul, Nat.add_assoc, Nat.add_comm lz (lz + 1)]
    have h3 : (w - (2 * lz + 1) + (lz + 1)) + lz = w := by
      rw [Nat.add_assoc, ← h2]
      exact h1
    exact (Nat.add_sub_cancel (w - (2 * lz + 1) + (lz + 1)) lz).symm.trans
      (congrArg (fun x => x - lz) h3)
  let rem := w - (2 * lz + 1)
  let word := encodeUeWord w lz v trail
  have hWordGe : HPow.hPow (2 : Nat) (w - 1 - lz) ≤ word := by
    have hm : HPow.hPow (2 : Nat) lz * HPow.hPow (2 : Nat) rem ≤
        (v + 1) * HPow.hPow (2 : Nat) rem :=
      Nat.mul_le_mul_right (HPow.hPow (2 : Nat) rem) hLo
    have hp : HPow.hPow (2 : Nat) lz * HPow.hPow (2 : Nat) rem =
        HPow.hPow (2 : Nat) (w - 1 - lz) := by
      rw [← pow2_add_eq lz rem, Nat.add_comm lz rem]
      exact congrArg (HPow.hPow (2 : Nat)) hShift
    rw [hp] at hm
    exact Nat.le_trans hm (Nat.le_add_right _ trail)
  have hWordLt : word < HPow.hPow (2 : Nat) (w - lz) := by
    have hstep : (v + 1) * HPow.hPow (2 : Nat) rem + trail <
        (v + 1) * HPow.hPow (2 : Nat) rem + HPow.hPow (2 : Nat) rem :=
      Nat.add_lt_add_left hTrail _
    have hsucc : (v + 1) * HPow.hPow (2 : Nat) rem + HPow.hPow (2 : Nat) rem =
        (v + 1 + 1) * HPow.hPow (2 : Nat) rem := by
      rw [Nat.add_mul (v + 1) 1 (HPow.hPow (2 : Nat) rem), Nat.one_mul]
    rw [hsucc] at hstep
    have hle : (v + 1 + 1) * HPow.hPow (2 : Nat) rem ≤
        HPow.hPow (2 : Nat) (lz + 1) * HPow.hPow (2 : Nat) rem :=
      Nat.mul_le_mul_right (HPow.hPow (2 : Nat) rem) hHi
    have hp : HPow.hPow (2 : Nat) (lz + 1) * HPow.hPow (2 : Nat) rem =
        HPow.hPow (2 : Nat) (w - lz) := by
      rw [← pow2_add_eq (lz + 1) rem, Nat.add_comm (lz + 1) rem]
      exact congrArg (HPow.hPow (2 : Nat)) hShiftHi
    rw [hp] at hle
    exact Nat.lt_of_lt_of_le hstep hle
  have hWordPos : 0 < word := Nat.lt_of_lt_of_le (pow2_pos (w - 1 - lz)) hWordGe
  have hWordLtW : word < HPow.hPow (2 : Nat) w :=
    Nat.lt_of_lt_of_le hWordLt (pow2_le_of_le (Nat.sub_le w lz))
  have hClzBounds := clzN_pow2_bounds hWordPos hWordLtW
  have hClzEq : clzN w word = lz := by
    cases Nat.lt_or_ge (clzN w word) lz with
    | inl hlt =>
      have hge1 : w - lz ≤ w - 1 - clzN w word := by
        have h2 : w - lz ≤ w - (clzN w word + 1) := Nat.sub_le_sub_left hlt w
        have h3 : w - 1 - clzN w word = w - (clzN w word + 1) := by
          rw [Nat.sub_sub, Nat.add_comm 1 (clzN w word)]
        rw [h3]
        exact h2
      have hcontra := Nat.lt_of_lt_of_le hWordLt (pow2_le_of_le hge1)
      exact False.elim (Nat.not_lt_of_ge hClzBounds.1 hcontra)
    | inr hge =>
      cases Nat.eq_or_lt_of_le hge with
      | inl heq => exact heq.symm
      | inr hgt =>
        have hge2 : w - clzN w word ≤ w - 1 - lz := by
          have h2 : w - clzN w word ≤ w - (lz + 1) := Nat.sub_le_sub_left hgt w
          have h3 : w - 1 - lz = w - (lz + 1) := by
            rw [Nat.sub_sub, Nat.add_comm 1 lz]
          rw [h3]
          exact h2
        have hcontra := Nat.lt_of_lt_of_le hClzBounds.2 (pow2_le_of_le hge2)
        exact False.elim (Nat.not_lt_of_ge hWordGe hcontra)
  unfold decodeUeWord
  dsimp only
  rw [hClzEq]
  have hDiv : HDiv.hDiv word (HPow.hPow (2 : Nat) rem) = v + 1 := by
    have hcomm : word = trail + HPow.hPow (2 : Nat) rem * (v + 1) := by
      dsimp only [word, encodeUeWord]
      rw [Nat.mul_comm (v + 1) (HPow.hPow (2 : Nat) rem), Nat.add_comm]
    rw [hcomm, Nat.add_mul_div_left trail (v + 1) (pow2_pos rem),
        Nat.div_eq_of_lt hTrail, Nat.zero_add]
  change (2 * lz + 1, HDiv.hDiv word (HPow.hPow (2 : Nat) rem) - 1) =
    (2 * lz + 1, v)
  rw [hDiv, Nat.add_sub_cancel]

/-! ## Part 4: AV1 (`rav1d`) Unsigned LEB128 Codec -/

/-- Encode `v : Nat` into an AV1 unsigned LEB128 byte list of at most `fuel`
bytes (`7`-bit little-endian chunks with continuation bit `0x80` on every
non-final byte), defined via `@Nat.rec` (`0` `._unsafe_rec`). -/
@[expose] def encodeLeb128Aux (fuel v : Nat) : List Nat :=
  @Nat.rec (fun _ => Nat → List Nat)
    (fun _ => [])
    (fun _ ih cur =>
      if Nat.blt cur 128 then
        [cur]
      else
        (HMod.hMod cur 128 + 128) :: ih (HDiv.hDiv cur 128))
    fuel v

/-- Step unfolding equation for `encodeLeb128Aux`. -/
theorem encodeLeb128Aux_succ (fuel v : Nat) :
    encodeLeb128Aux (fuel + 1) v =
      if Nat.blt v 128 then
        [v]
      else
        (HMod.hMod v 128 + 128) :: encodeLeb128Aux fuel (HDiv.hDiv v 128) :=
  rfl

/-- Canonical AV1 OBU LEB128 encoder (up to 8 bytes, covering `0 ≤ v < 2^56`,
strictly subsuming AV1's `0 ≤ v < 2^32` OBU size range). -/
@[expose] def encodeLeb128 (v : Nat) : List Nat :=
  encodeLeb128Aux 8 v

/-- Decode an AV1 unsigned LEB128 prefix of at most `maxBytes` bytes from byte
stream `bs`, returning `some (value, remainingBytes)` or `none` if truncated or
exceeding `maxBytes` bytes. Uses `@Nat.rec` (`0` `._unsafe_rec`). -/
@[expose] def decodeLeb128Aux (maxBytes : Nat) (bs : List Nat) :
    Option (Nat × List Nat) :=
  @Nat.rec (fun _ => List Nat → Option (Nat × List Nat))
    (fun _ => none)
    (fun _ ih xs =>
      match xs with
      | [] => none
      | b :: rest =>
        if Nat.blt b 128 then
          some (b, rest)
        else
          match ih rest with
          | none => none
          | some (hi, tail) => some (HMod.hMod b 128 + 128 * hi, tail))
    maxBytes bs

/-- Step unfolding equation for `decodeLeb128Aux` on a cons stream. -/
theorem decodeLeb128Aux_succ_cons (k b : Nat) (rest : List Nat) :
    decodeLeb128Aux (k + 1) (b :: rest) =
      if Nat.blt b 128 then
        some (b, rest)
      else
        match decodeLeb128Aux k rest with
        | none => none
        | some (hi, tail) => some (HMod.hMod b 128 + 128 * hi, tail) :=
  rfl

/-- Canonical AV1 OBU LEB128 decoder (maximum 8 bytes per AV1 §4.10.5). -/
@[expose] def decodeLeb128 (bs : List Nat) : Option (Nat × List Nat) :=
  decodeLeb128Aux 8 bs

private theorem blt_true_iff_lt (a b : Nat) :
    Nat.blt a b = true ↔ a < b :=
  ble_true_iff_le (a + 1) b

private theorem blt_false_iff_ge (a b : Nat) :
    Nat.blt a b = false ↔ b ≤ a := by
  constructor
  · intro hf
    exact Nat.le_of_lt_succ ((ble_false_iff_lt (a + 1) b).mp hf)
  · intro hge
    exact (ble_false_iff_lt (a + 1) b).mpr (Nat.lt_succ_of_le hge)

/-- Exact `PutGet` round-trip for `encodeLeb128Aux` / `decodeLeb128Aux`
preserving arbitrary trailing bytes `rest`, for every `0 < fuel` and
`v < 2^(7 * fuel)`. -/
theorem decodeLeb128Aux_encodeLeb128Aux (fuel : Nat) :
    ∀ (v : Nat) (rest : List Nat),
      0 < fuel →
      v < HPow.hPow (2 : Nat) (7 * fuel) →
      decodeLeb128Aux fuel (encodeLeb128Aux fuel v ++ rest) =
        some (v, rest) := by
  induction fuel with
  | zero =>
    intro _ _ hfuel _
    exact False.elim (Nat.not_lt_zero 0 hfuel)
  | succ fuel ih =>
    intro v rest _ hv
    rw [encodeLeb128Aux_succ]
    cases hlt : Nat.blt v 128 with
    | true =>
      change decodeLeb128Aux (fuel + 1) ([v] ++ rest) = some (v, rest)
      rw [List.cons_append, List.nil_append, decodeLeb128Aux_succ_cons, hlt]
      rfl
    | false =>
      have hge : 128 ≤ v := (blt_false_iff_ge v 128).mp hlt
      have hdiv : HDiv.hDiv v 128 < HPow.hPow (2 : Nat) (7 * fuel) := by
        have hp : HPow.hPow (2 : Nat) (7 * (fuel + 1)) =
            HPow.hPow (2 : Nat) (7 * fuel) * 128 := by
          rw [Nat.mul_succ, pow2_add_eq]
        rw [hp] at hv
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 128)).mpr hv
      cases fuel with
      | zero =>
        rw [Nat.mul_zero, pow2_zero] at hdiv
        have hd0 : HDiv.hDiv v 128 = 0 :=
          Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hdiv)
        have hlt128 : v < 128 := by
          have := Nat.div_add_mod v 128
          rw [hd0, Nat.mul_zero, Nat.zero_add] at this
          rw [← this]
          exact Nat.mod_lt v (by decide)
        exact False.elim (Nat.not_lt_of_ge hge hlt128)
      | succ fuel' =>
        have hih := ih (HDiv.hDiv v 128) rest (Nat.zero_lt_succ fuel') hdiv
        have hbyte : Nat.blt (HMod.hMod v 128 + 128) 128 = false :=
          (blt_false_iff_ge _ 128).mpr (Nat.le_add_left 128 _)
        change decodeLeb128Aux (fuel' + 2)
          (((HMod.hMod v 128 + 128) ::
            encodeLeb128Aux (fuel' + 1) (HDiv.hDiv v 128)) ++ rest) =
          some (v, rest)
        rw [List.cons_append, decodeLeb128Aux_succ_cons, hbyte]
        change (match decodeLeb128Aux (fuel' + 1)
            (encodeLeb128Aux (fuel' + 1) (HDiv.hDiv v 128) ++ rest) with
          | none => none
          | some (hi, tail) =>
            some (HMod.hMod (HMod.hMod v 128 + 128) 128 + 128 * hi, tail)) =
          some (v, rest)
        rw [hih]
        dsimp only
        have hmod :
            HMod.hMod (HMod.hMod v 128 + 128) 128 = HMod.hMod v 128 := by
          rw [Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (Nat.mod_lt v (by decide))
        rw [hmod, Nat.add_comm (HMod.hMod v 128), Nat.div_add_mod]

/-- Exact AV1 OBU LEB128 round-trip for every `v < 2^56` (strictly subsuming
AV1's 32-bit OBU size limit `v < 2^32`). -/
theorem decodeLeb128_encodeLeb128 (v : Nat) (rest : List Nat)
    (hv : v < HPow.hPow (2 : Nat) 56) :
    decodeLeb128 (encodeLeb128 v ++ rest) = some (v, rest) :=
  decodeLeb128Aux_encodeLeb128Aux 8 v rest (by decide) hv

/-- Every value decoded by `decodeLeb128Aux maxBytes` is strictly below
`2^(7 * maxBytes)`. -/
theorem decodeLeb128Aux_lt :
    ∀ {maxBytes : Nat} {bs rest : List Nat} {v : Nat},
      decodeLeb128Aux maxBytes bs = some (v, rest) →
      v < HPow.hPow (2 : Nat) (7 * maxBytes)
  | 0, _, _, _, h => by nomatch h
  | k + 1, [], _, _, h => by nomatch h
  | k + 1, b :: xs, rest, v, h => by
    rw [decodeLeb128Aux_succ_cons] at h
    cases hlt : Nat.blt b 128 with
    | true =>
      rw [hlt] at h
      injection h with hp
      injection hp with hbv _
      subst hbv
      have hb : b < 128 := (blt_true_iff_lt b 128).mp hlt
      have hp : 128 ≤ HPow.hPow (2 : Nat) (7 * (k + 1)) := by
        have h7 : 7 ≤ 7 * (k + 1) := by
          rw [Nat.mul_succ]
          exact Nat.le_add_left 7 (7 * k)
        exact pow2_le_of_le h7
      exact Nat.lt_of_lt_of_le hb hp
    | false =>
      rw [hlt] at h
      change (match decodeLeb128Aux k xs with
        | none => none
        | some (hi, tail) => some (HMod.hMod b 128 + 128 * hi, tail)) =
        some (v, rest) at h
      cases hd : decodeLeb128Aux k xs with
      | none => rw [hd] at h; nomatch h
      | some p =>
        rw [hd] at h
        injection h with hp
        injection hp with hv _
        subst hv
        have hhi : p.1 < HPow.hPow (2 : Nat) (7 * k) := decodeLeb128Aux_lt hd
        have hm : HMod.hMod b 128 < 128 := Nat.mod_lt b (by decide)
        have h1 : HMod.hMod b 128 + 128 * p.1 < 128 + 128 * p.1 :=
          Nat.add_lt_add_right hm (128 * p.1)
        have h2 : 128 + 128 * p.1 = 128 * (p.1 + 1) := by
          rw [Nat.mul_succ, Nat.add_comm]
        rw [h2] at h1
        have h3 : 128 * (p.1 + 1) ≤ 128 * HPow.hPow (2 : Nat) (7 * k) :=
          Nat.mul_le_mul_left 128 hhi
        have h4 : 128 * HPow.hPow (2 : Nat) (7 * k) =
            HPow.hPow (2 : Nat) (7 * (k + 1)) := by
          rw [Nat.mul_succ, Nat.add_comm (7 * k) 7, pow2_add_eq]
        rw [h4] at h3
        exact Nat.lt_of_lt_of_le h1 h3

/-! ## Part 5: MP4/PSSH Big-Endian & Little-Endian `Nat`-Byte Word Unpacking -/

/-- Unpack two big-endian `Nat` bytes into a 16-bit integer. -/
@[expose] def beU16Nat (b0 b1 : Nat) : Nat :=
  b0 * 256 + b1

/-- Unpack four big-endian `Nat` bytes into a 32-bit integer (MP4 box size &
FourCC header). -/
@[expose] def beU32Nat (b0 b1 b2 b3 : Nat) : Nat :=
  ((b0 * 256 + b1) * 256 + b2) * 256 + b3

/-- Unpack four little-endian `Nat` bytes into a 32-bit integer. -/
@[expose] def leU32Nat (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + 256 * (b1 + 256 * (b2 + 256 * b3))

/-- Unpack eight big-endian `Nat` bytes into a 64-bit integer (MP4 extended
64-bit box size). -/
@[expose] def beU64Nat (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  beU32Nat b0 b1 b2 b3 * HPow.hPow (2 : Nat) 32 + beU32Nat b4 b5 b6 b7

/-- `beU16Nat` on valid bytes is strictly below `2^16`. -/
theorem beU16Nat_lt {b0 b1 : Nat} (h0 : b0 < 256) (h1 : b1 < 256) :
    beU16Nat b0 b1 < HPow.hPow (2 : Nat) 16 := by
  unfold beU16Nat
  have ha : b0 * 256 + b1 < b0 * 256 + 256 := Nat.add_lt_add_left h1 _
  have hb : b0 * 256 + 256 = (b0 + 1) * 256 := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hb] at ha
  exact Nat.lt_of_lt_of_le ha (Nat.mul_le_mul_right 256 h0)

/-- `beU32Nat` on valid bytes is strictly below `2^32`. -/
theorem beU32Nat_lt {b0 b1 b2 b3 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    beU32Nat b0 b1 b2 b3 < HPow.hPow (2 : Nat) 32 := by
  have hhi : beU16Nat b0 b1 < HPow.hPow (2 : Nat) 16 := beU16Nat_lt h0 h1
  have hlo : beU16Nat b2 b3 < HPow.hPow (2 : Nat) 16 := beU16Nat_lt h2 h3
  have heq : beU32Nat b0 b1 b2 b3 =
      beU16Nat b0 b1 * HPow.hPow (2 : Nat) 16 + beU16Nat b2 b3 := by
    unfold beU32Nat beU16Nat
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  rw [heq]
  have ha : beU16Nat b0 b1 * HPow.hPow (2 : Nat) 16 + beU16Nat b2 b3 <
      beU16Nat b0 b1 * HPow.hPow (2 : Nat) 16 + HPow.hPow (2 : Nat) 16 :=
    Nat.add_lt_add_left hlo _
  have hb : beU16Nat b0 b1 * HPow.hPow (2 : Nat) 16 + HPow.hPow (2 : Nat) 16 =
      (beU16Nat b0 b1 + 1) * HPow.hPow (2 : Nat) 16 := by
    rw [Nat.add_mul (beU16Nat b0 b1) 1 (HPow.hPow (2 : Nat) 16), Nat.one_mul]
  rw [hb] at ha
  exact Nat.lt_of_lt_of_le ha
    (Nat.mul_le_mul_right (HPow.hPow (2 : Nat) 16) hhi)

/-- `beU32Nat` equals nested `256`-radix Horner form (and `leU32Nat`
reversed). -/
theorem beU32Nat_eq_leU32Nat_rev (b0 b1 b2 b3 : Nat) :
    beU32Nat b0 b1 b2 b3 = leU32Nat b3 b2 b1 b0 := by
  unfold beU32Nat leU32Nat
  have h1 : (b0 * 256 + b1) * 256 = 256 * (b1 + 256 * b0) := by
    rw [Nat.mul_comm (b0 * 256 + b1) 256, Nat.mul_comm b0 256,
        Nat.add_comm (256 * b0) b1]
  have h2 : ((b0 * 256 + b1) * 256 + b2) * 256 =
      256 * (b2 + 256 * (b1 + 256 * b0)) := by
    rw [h1, Nat.mul_comm _ 256, Nat.add_comm _ b2]
  rw [h2, Nat.add_comm _ b3]

/-- `leU32Nat` on valid bytes is strictly below `2^32`. -/
theorem leU32Nat_lt {b0 b1 b2 b3 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    leU32Nat b0 b1 b2 b3 < HPow.hPow (2 : Nat) 32 := by
  rw [← beU32Nat_eq_leU32Nat_rev]
  exact beU32Nat_lt h3 h2 h1 h0

/-- `beU64Nat` on valid bytes is strictly below `2^64`. -/
theorem beU64Nat_lt {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    beU64Nat b0 b1 b2 b3 b4 b5 b6 b7 < HPow.hPow (2 : Nat) 64 := by
  unfold beU64Nat
  have hhi := beU32Nat_lt h0 h1 h2 h3
  have hlo := beU32Nat_lt h4 h5 h6 h7
  have ha : beU32Nat b0 b1 b2 b3 * HPow.hPow (2 : Nat) 32 +
        beU32Nat b4 b5 b6 b7 <
      beU32Nat b0 b1 b2 b3 * HPow.hPow (2 : Nat) 32 +
        HPow.hPow (2 : Nat) 32 :=
    Nat.add_lt_add_left hlo _
  have hb : beU32Nat b0 b1 b2 b3 * HPow.hPow (2 : Nat) 32 +
        HPow.hPow (2 : Nat) 32 =
      (beU32Nat b0 b1 b2 b3 + 1) * HPow.hPow (2 : Nat) 32 := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hb] at ha
  exact Nat.lt_of_lt_of_le ha
    (Nat.mul_le_mul_right (HPow.hPow (2 : Nat) 32) hhi)

/-- Byte-lane extraction recovers every byte of `beU32Nat` in big-endian
order. -/
theorem byteLane_beU32Nat {b0 b1 b2 b3 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    byteLane (beU32Nat b0 b1 b2 b3) 3 = b0 ∧
    byteLane (beU32Nat b0 b1 b2 b3) 2 = b1 ∧
    byteLane (beU32Nat b0 b1 b2 b3) 1 = b2 ∧
    byteLane (beU32Nat b0 b1 b2 b3) 0 = b3 := by
  have heq : beU32Nat b0 b1 b2 b3 = b3 + 256 * (b2 + 256 * (b1 + 256 * b0)) :=
    beU32Nat_eq_leU32Nat_rev b0 b1 b2 b3
  have hlane0 : byteLane (beU32Nat b0 b1 b2 b3) 0 = b3 := by
    rw [heq]
    exact bitSlice_low_of_shift_add (lo := 8) h3
  have hd1 : HDiv.hDiv (beU32Nat b0 b1 b2 b3) 256 =
      b2 + 256 * (b1 + 256 * b0) := by
    rw [heq, Nat.add_mul_div_left _ _ (by decide : 0 < 256),
        Nat.div_eq_of_lt h3, Nat.zero_add]
  have hlane1 : byteLane (beU32Nat b0 b1 b2 b3) 1 = b2 := by
    unfold byteLane bitSlice
    change HMod.hMod (HDiv.hDiv (beU32Nat b0 b1 b2 b3) 256) 256 = b2
    rw [hd1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  have hd2 : HDiv.hDiv (beU32Nat b0 b1 b2 b3) (HPow.hPow (2 : Nat) 16) =
      b1 + 256 * b0 := by
    have hp : HPow.hPow (2 : Nat) 16 = 256 * 256 := rfl
    rw [hp, ← Nat.div_div_eq_div_mul, hd1,
        Nat.add_mul_div_left _ _ (by decide : 0 < 256),
        Nat.div_eq_of_lt h2, Nat.zero_add]
  have hlane2 : byteLane (beU32Nat b0 b1 b2 b3) 2 = b1 := by
    unfold byteLane bitSlice
    change HMod.hMod
      (HDiv.hDiv (beU32Nat b0 b1 b2 b3) (HPow.hPow (2 : Nat) 16)) 256 = b1
    rw [hd2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have hd3 :
      HDiv.hDiv (beU32Nat b0 b1 b2 b3) (HPow.hPow (2 : Nat) 24) = b0 := by
    have hp : HPow.hPow (2 : Nat) 24 = HPow.hPow (2 : Nat) 16 * 256 := rfl
    rw [hp, ← Nat.div_div_eq_div_mul, hd2,
        Nat.add_mul_div_left _ _ (by decide : 0 < 256),
        Nat.div_eq_of_lt h1, Nat.zero_add]
  have hlane3 : byteLane (beU32Nat b0 b1 b2 b3) 3 = b0 := by
    unfold byteLane bitSlice
    change HMod.hMod
      (HDiv.hDiv (beU32Nat b0 b1 b2 b3) (HPow.hPow (2 : Nat) 24)) 256 = b0
    rw [hd3, Nat.mod_eq_of_lt h0]
  exact ⟨hlane3, hlane2, hlane1, hlane0⟩

/-- `beU32Nat` is injective on valid 4-byte tuples (MP4 box size & FourCC
uniqueness). -/
theorem beU32Nat_injective {a0 a1 a2 a3 b0 b1 b2 b3 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (heq : beU32Nat a0 a1 a2 a3 = beU32Nat b0 b1 b2 b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have ha := byteLane_beU32Nat ha0 ha1 ha2 ha3
  have hb := byteLane_beU32Nat hb0 hb1 hb2 hb3
  rw [heq] at ha
  exact ⟨ha.1.symm.trans hb.1, ha.2.1.symm.trans hb.2.1,
         ha.2.2.1.symm.trans hb.2.2.1, ha.2.2.2.symm.trans hb.2.2.2⟩

end Anneal.MediaBits.Bitstream

end
