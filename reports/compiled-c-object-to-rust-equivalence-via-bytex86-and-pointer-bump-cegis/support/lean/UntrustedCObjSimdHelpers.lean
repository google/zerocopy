-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Omega
import ByteX86Gcc
import RustFfiSpecs
import UntrustedCObjHints

/-!
# `UntrustedCObjSimdHelpers`

Reusable O(1) `execByteInstr` step lemmas, `64/128/256`-bit memory byte/word
accessors, `UpperYmmClean` preservation lemmas, and exact lane-sum algebra for
SSE2 / VEX-128 / AVX2 (`256`-bit) dot-product and streaming XOR proofs (`0`
`sorry`, `0` `isPartial`).
-/

namespace UntrustedCObjSimdHelpers

open ByteX86Gcc
open RustFfiSpecs
open UntrustedCObjHints

/-! ## Section 1: Upper-YMM Cleanliness & YMM Update Helpers -/

theorem writeXmm128_true_eq (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128) :
    writeXmm128 true ymms r v = ymmUpd ymms r (0#128 ++ v) := by
  dsimp only [writeXmm128]
  congr 1
  unfold BitVec.zeroExtend
  exact setWidth_eq_zero_append (m := 128) v

theorem writeXmm128_false_lo (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128) :
    BitVec.extractLsb' 0 128 (writeXmm128 false ymms r v r) = v := by
  dsimp only [writeXmm128]
  rw [ymmUpd_eq, extractLsb_append_right_off _ _ (by decide), extractLsb_self]

theorem writeXmm128_false_hi (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128) :
    BitVec.extractLsb' 128 128 (writeXmm128 false ymms r v r) =
      BitVec.extractLsb' 128 128 (ymms r) := by
  dsimp only [writeXmm128]
  rw [ymmUpd_eq, extractLsb_append_left _ _ (by decide), extractLsb_self]

theorem writeXmm128_ne (isVex : Bool) (ymms : YmmIdx → BitVec 256) {r r' : YmmIdx}
    (h : r' ≠ r) (v : BitVec 128) :
    writeXmm128 isVex ymms r v r' = ymms r' := by
  cases isVex <;> dsimp only [writeXmm128] <;> exact ymmUpd_ne ymms h _

theorem writeXmm128_false_preserves_hi (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128) :
    ∀ idx : YmmIdx, BitVec.extractLsb' 128 128 (writeXmm128 false ymms r v idx) =
      BitVec.extractLsb' 128 128 (ymms idx) := by
  intro idx
  by_cases h : idx = r
  · subst h; exact writeXmm128_false_hi ymms idx v
  · rw [writeXmm128_ne false ymms h v]

theorem writeXmm128_true_preserves_clean (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128)
    (hc : ∀ idx : YmmIdx, BitVec.extractLsb' 128 128 (ymms idx) = 0#128) :
    ∀ idx : YmmIdx, BitVec.extractLsb' 128 128 (writeXmm128 true ymms r v idx) = 0#128 := by
  intro idx
  by_cases h : idx = r
  · subst h
    rw [writeXmm128_true_eq, ymmUpd_eq, extractLsb_append_left _ _ (by decide), extractLsb_self]
  · rw [writeXmm128_ne true ymms h v]; exact hc idx

theorem vzeroUpperAll_clean (ymms : YmmIdx → BitVec 256) :
    ∀ idx : YmmIdx, BitVec.extractLsb' 128 128 (vzeroUpperAll ymms idx) = 0#128 := by
  intro idx
  unfold vzeroUpperAll BitVec.zeroExtend
  rw [setWidth_eq_zero_append (m := 128), extractLsb_append_left _ _ (by decide), extractLsb_self]

theorem vzeroUpperAll_lo (ymms : YmmIdx → BitVec 256) (idx : YmmIdx) :
    BitVec.extractLsb' 0 128 (vzeroUpperAll ymms idx) = BitVec.extractLsb' 0 128 (ymms idx) := by
  unfold vzeroUpperAll BitVec.zeroExtend
  rw [setWidth_eq_zero_append (m := 128), extractLsb_append_right_off _ _ (by decide), extractLsb_self]

theorem extract_lo128_zeroExtend256 (v : BitVec 128) :
    BitVec.extractLsb' 0 128 (v.zeroExtend 256) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  unfold BitVec.zeroExtend
  simp [hi, show i < 256 by omega]

theorem extract_lo128_append (hi lo : BitVec 128) :
    BitVec.extractLsb' 0 128 (hi ++ lo) = lo := by
  rw [extractLsb_append_right_off _ _ (by decide), extractLsb_self]

theorem extract_hi128_append (hi lo : BitVec 128) :
    BitVec.extractLsb' 128 128 (hi ++ lo) = hi := by
  rw [extractLsb_append_left _ _ (by decide), extractLsb_self]

/-! ## Section 2: `64 / 128 / 256`-Bit Memory & Lane Extraction Lemmas -/

theorem readMem64_byte_at (m : ByteMem) (p : BitVec 64) (j : Nat) (hj : j < 8) :
    byteOf64 (readMem64 m p) j = m (p + BitVec.ofNat 64 j) := by
  unfold readMem64 pack8Bytes byteOf64
  match j with
  | 0 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_self]
  | 1 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_left _ _ (by decide), extractLsb_self]
  | 2 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_left _ _ (by decide),
        extractLsb_self]
  | 3 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_left _ _ (by decide), extractLsb_self]
  | 4 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_left _ _ (by decide),
        extractLsb_self]
  | 5 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_left _ _ (by decide), extractLsb_self]
  | 6 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_left _ _ (by decide),
        extractLsb_self]
  | 7 =>
    rw [extractLsb_append_left _ _ (by decide), extractLsb_self]
  | _ + 8 => omega

theorem readMem128_byte_at (m : ByteMem) (p : BitVec 64) (i : Fin 16) :
    getByte128 (readMem128 m p) i = m (p + BitVec.ofNat 64 i.val) := by
  unfold readMem128 getByte128
  by_cases h8 : i.val < 8
  · rw [extractLsb_append_right_off _ _ (by omega)]
    exact readMem64_byte_at m p i.val h8
  · have hge : 64 ≤ i.val * 8 := by omega
    rw [extractLsb_append_left _ _ hge]
    have hsub : i.val * 8 - 64 = (i.val - 8) * 8 := by omega
    rw [hsub]
    have hb := readMem64_byte_at m (p + 8#64) (i.val - 8) (by omega)
    unfold byteOf64 at hb
    rw [hb]
    congr 1
    change p + BitVec.ofNat 64 8 + BitVec.ofNat 64 (i.val - 8) = p + BitVec.ofNat 64 i.val
    rw [bv64_add_ofNat_assoc]; congr 2; omega

theorem readMem256_byte_at (m : ByteMem) (p : BitVec 64) (i : Fin 32) :
    getByte256 (readMem256 m p) i = m (p + BitVec.ofNat 64 i.val) := by
  unfold readMem256 getByte256
  by_cases h16 : i.val < 16
  · rw [extractLsb_append_right_off _ _ (by omega)]
    exact readMem128_byte_at m p ⟨i.val, h16⟩
  · have hge : 128 ≤ i.val * 8 := by omega
    rw [extractLsb_append_left _ _ hge]
    have hsub : i.val * 8 - 128 = (i.val - 16) * 8 := by omega
    rw [hsub]
    have hb := readMem128_byte_at m (p + 16#64) ⟨i.val - 16, by omega⟩
    have hptr : p + 16#64 + BitVec.ofNat 64 (i.val - 16) = p + BitVec.ofNat 64 i.val := by
      change p + BitVec.ofNat 64 16 + BitVec.ofNat 64 (i.val - 16) = p + BitVec.ofNat 64 i.val
      rw [bv64_add_ofNat_assoc, show 16 + (i.val - 16) = i.val by omega]
    exact Eq.trans hb (congrArg m hptr)

theorem writeMem128_at_offset (m : ByteMem) (p : BitVec 64) (v : BitVec 128) (j : Nat) (hj : j < 16) :
    writeMem128 m p v (p + BitVec.ofNat 64 j) = getByte128 v ⟨j, hj⟩ := by
  unfold writeMem128 getByte128
  by_cases h8 : j < 8
  · rw [writeMem64_byte_ne _ (p + 8#64) (p + BitVec.ofNat 64 j) _ (fun k hk => by
          change p + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 8 + BitVec.ofNat 64 k
          rw [bv64_add_ofNat_assoc]
          exact bv64_add_small_ne p (by omega) (by omega) (by omega)),
        writeMem64_at_offset m p _ j h8]
    unfold byteOf64
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [hb, show j * 8 + b < 64 by omega]
  · have hptr : p + BitVec.ofNat 64 j = (p + 8#64) + BitVec.ofNat 64 (j - 8) := by
      change p + BitVec.ofNat 64 j = p + BitVec.ofNat 64 8 + BitVec.ofNat 64 (j - 8)
      rw [bv64_add_ofNat_assoc]; congr 2; omega
    rw [hptr, writeMem64_at_offset _ (p + 8#64) _ (j - 8) (by omega)]
    unfold byteOf64
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have hidx : 64 + ((j - 8) * 8 + b) = j * 8 + b := by omega
    simp [hb, show (j - 8) * 8 + b < 64 by omega, hidx]

theorem writeMem256_at_offset (m : ByteMem) (p : BitVec 64) (v : BitVec 256) (j : Nat) (hj : j < 32) :
    writeMem256 m p v (p + BitVec.ofNat 64 j) = getByte256 v ⟨j, hj⟩ := by
  unfold writeMem256 getByte256
  by_cases h16 : j < 16
  · rw [writeMem128_byte_ne _ (p + 16#64) (p + BitVec.ofNat 64 j) _ (fun k hk => by
          change p + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 16 + BitVec.ofNat 64 k
          rw [bv64_add_ofNat_assoc]
          exact bv64_add_small_ne p (by omega) (by omega) (by omega)),
        writeMem128_at_offset m p _ j h16]
    unfold getByte128
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [hb, show j * 8 + b < 128 by omega]
  · have hptr : p + BitVec.ofNat 64 j = (p + 16#64) + BitVec.ofNat 64 (j - 16) := by
      change p + BitVec.ofNat 64 j = p + BitVec.ofNat 64 16 + BitVec.ofNat 64 (j - 16)
      rw [bv64_add_ofNat_assoc]; congr 2; omega
    rw [hptr, writeMem128_at_offset _ (p + 16#64) _ (j - 16) (by omega)]
    unfold getByte128
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have hidx : 128 + ((j - 16) * 8 + b) = j * 8 + b := by omega
    simp [hb, show (j - 16) * 8 + b < 128 by omega, hidx]

theorem getByte128_packBytes128 (f : Fin 16 → BitVec 8) (i : Fin 16) :
    getByte128 (packBytes128 f) i = f i := by
  rcases i with ⟨v, hv⟩
  unfold getByte128 packBytes128
  dsimp only
  match v with
  | 0  => rw [Nat.zero_mul]; (repeat rw [extractLsb_append_right_off _ _ (by decide)]); exact extractLsb_self _
  | 1  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 2  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 3  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 4  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 5  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 6  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 7  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 8  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 9  => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 10 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 11 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 12 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 13 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 14 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 15 => rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | _ + 16 => omega

theorem getByte256_packBytes256 (f : Fin 32 → BitVec 8) (i : Fin 32) :
    getByte256 (packBytes256 f) i = f i := by
  unfold getByte256 packBytes256
  by_cases h16 : i.val < 16
  · rw [extractLsb_append_right_off _ _ (by omega)]
    exact getByte128_packBytes128 (fun j => f ⟨j.val, by omega⟩) ⟨i.val, h16⟩
  · rw [extractLsb_append_left _ _ (by omega)]
    have hsub : i.val * 8 - 128 = (i.val - 16) * 8 := by omega
    rw [hsub]
    have h := getByte128_packBytes128 (fun j => f ⟨j.val + 16, by omega⟩) ⟨i.val - 16, by omega⟩
    exact Eq.trans h (congrArg f (Fin.ext (by dsimp; omega)))

theorem getWord128_packWords128 (f : Fin 8 → BitVec 16) (i : Fin 8) :
    getWord128 (packWords128 f) i = f i := by
  rcases i with ⟨v, hv⟩
  unfold getWord128 packWords128
  dsimp only
  match v with
  | 0 => rw [Nat.zero_mul]; (repeat rw [extractLsb_append_right_off _ _ (by decide)]); exact extractLsb_self _
  | 1 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 2 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 3 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 4 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 5 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 6 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 7 => rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | _ + 8 => omega

theorem getDword128_packDwords128 (f : Fin 4 → BitVec 32) (i : Fin 4) :
    getDword128 (packDwords128 f) i = f i := by
  rcases i with ⟨v, hv⟩
  unfold getDword128 packDwords128
  dsimp only
  match v with
  | 0 => rw [Nat.zero_mul]; (repeat rw [extractLsb_append_right_off _ _ (by decide)]); exact extractLsb_self _
  | 1 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 2 => repeat first | rw [extractLsb_append_right_off _ _ (by decide)] | rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | 3 => rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | _ + 4 => omega

theorem getQword128_packQwords128 (f : Fin 2 → BitVec 64) (i : Fin 2) :
    getQword128 (packQwords128 f) i = f i := by
  rcases i with ⟨v, hv⟩
  unfold getQword128 packQwords128
  dsimp only
  match v with
  | 0 => rw [Nat.zero_mul, extractLsb_append_right_off _ _ (by decide)]; exact extractLsb_self _
  | 1 => rw [extractLsb_append_left _ _ (by decide)]; exact extractLsb_self _
  | _ + 2 => omega

theorem readMem128_word_at (m : ByteMem) (p : BitVec 64) (i : Fin 8) :
    getWord128 (readMem128 m p) i = readMem16 m (p + BitVec.ofNat 64 (2 * i.val)) := by
  have hb0 := readMem128_byte_at m p ⟨2 * i.val, by omega⟩
  have hb1 := readMem128_byte_at m p ⟨2 * i.val + 1, by omega⟩
  unfold getByte128 at hb0 hb1
  dsimp only at hb0 hb1
  unfold readMem16 getWord128
  have hptr : p + BitVec.ofNat 64 (2 * i.val) + 1#64 = p + BitVec.ofNat 64 (2 * i.val + 1) := by
    change p + BitVec.ofNat 64 (2 * i.val) + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (2 * i.val + 1)
    rw [bv64_add_ofNat_assoc]
  have h0 : p + BitVec.ofNat 64 (2 * i.val) + 0#64 = p + BitVec.ofNat 64 (2 * i.val) := BitVec.add_zero _
  rw [hptr, h0, ← hb0, ← hb1]
  have hs := append_extractLsb_split (a := 8) (b := 8) (by decide) (2 * i.val * 8) (by omega) (readMem128 m p)
  have h1 : 2 * i.val * 8 + 8 = (2 * i.val + 1) * 8 := by omega
  have h2 : i.val * 16 = 2 * i.val * 8 := by omega
  rw [h1] at hs
  rw [h2]
  exact hs.symm

theorem readMem64_word_at (m : ByteMem) (p : BitVec 64) (i : Fin 4) :
    BitVec.extractLsb' (i.val * 16) 16 (readMem64 m p) = readMem16 m (p + BitVec.ofNat 64 (2 * i.val)) := by
  have hb0 := readMem64_byte_at m p (2 * i.val) (by omega)
  have hb1 := readMem64_byte_at m p (2 * i.val + 1) (by omega)
  unfold byteOf64 at hb0 hb1
  unfold readMem16
  have hptr : p + BitVec.ofNat 64 (2 * i.val) + 1#64 = p + BitVec.ofNat 64 (2 * i.val + 1) := by
    change p + BitVec.ofNat 64 (2 * i.val) + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (2 * i.val + 1)
    rw [bv64_add_ofNat_assoc]
  have h0 : p + BitVec.ofNat 64 (2 * i.val) + 0#64 = p + BitVec.ofNat 64 (2 * i.val) := BitVec.add_zero _
  rw [hptr, h0, ← hb0, ← hb1]
  have hs := append_extractLsb_split (a := 8) (b := 8) (by decide) (2 * i.val * 8) (by omega) (readMem64 m p)
  have h1 : 2 * i.val * 8 + 8 = (2 * i.val + 1) * 8 := by omega
  have h2 : i.val * 16 = 2 * i.val * 8 := by omega
  rw [h1] at hs
  rw [h2]
  exact hs.symm

theorem xor128_splat_byte_at (m : ByteMem) (p : BitVec 64) (key : BitVec 8) (i : Fin 16) :
    getByte128 (packBytes128 (fun _ => key) ^^^ readMem128 m p) i =
      m (p + BitVec.ofNat 64 i.val) ^^^ key := by
  have h1 : getByte128 (packBytes128 (fun _ => key) ^^^ readMem128 m p) i =
      getByte128 (packBytes128 (fun _ => key)) i ^^^ getByte128 (readMem128 m p) i := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    unfold getByte128; simp [hb]
  rw [h1, getByte128_packBytes128, readMem128_byte_at, BitVec.xor_comm]

theorem xor256_splat_byte_at (m : ByteMem) (p : BitVec 64) (key : BitVec 8) (i : Fin 32) :
    getByte256 ((BitVec.extractLsb' 128 128 (packBytes256 (fun _ => key)) ^^^
                 BitVec.extractLsb' 128 128 (readMem256 m p)) ++
                (BitVec.extractLsb' 0 128 (packBytes256 (fun _ => key)) ^^^
                 BitVec.extractLsb' 0 128 (readMem256 m p))) i =
      m (p + BitVec.ofNat 64 i.val) ^^^ key := by
  have h1 : ((BitVec.extractLsb' 128 128 (packBytes256 (fun _ => key)) ^^^
              BitVec.extractLsb' 128 128 (readMem256 m p)) ++
             (BitVec.extractLsb' 0 128 (packBytes256 (fun _ => key)) ^^^
              BitVec.extractLsb' 0 128 (readMem256 m p))) =
            packBytes256 (fun _ => key) ^^^ readMem256 m p := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    rw [BitVec.getLsbD_append]
    by_cases h128 : b < 128
    · simp [h128, hb]
    · have hsub : b - 128 < 128 := by omega
      have hadd : 128 + (b - 128) = b := by omega
      simp [h128, hsub, hadd]
  rw [h1]
  have h2 : getByte256 (packBytes256 (fun _ => key) ^^^ readMem256 m p) i =
      getByte256 (packBytes256 (fun _ => key)) i ^^^ getByte256 (readMem256 m p) i := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    unfold getByte256; simp [hb]
  rw [h2, getByte256_packBytes256, readMem256_byte_at, BitVec.xor_comm]

theorem xor64_byte_at (a b : BitVec 64) (j : Nat) (_hj : j < 8) :
    byteOf64 (a ^^^ b) j = byteOf64 a j ^^^ byteOf64 b j := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  unfold byteOf64; simp [hk]

/-! ## Section 3: Exact `pmullw`/`pmulhuw` & Horizontal Dword Sum Algebra -/

def sumDwords128 (v : BitVec 128) : BitVec 32 :=
  getDword128 v ⟨0, by decide⟩ + getDword128 v ⟨1, by decide⟩ +
  getDword128 v ⟨2, by decide⟩ + getDword128 v ⟨3, by decide⟩

def sumDwords256 (v : BitVec 256) : BitVec 32 :=
  sumDwords128 (BitVec.extractLsb' 0 128 v) + sumDwords128 (BitVec.extractLsb' 128 128 v)

theorem sumDwords128_zero : sumDwords128 0#128 = 0#32 := rfl
theorem sumDwords256_zero : sumDwords256 0#256 = 0#32 := rfl

theorem sumDwords128_packDwords128 (f : Fin 4 → BitVec 32) :
    sumDwords128 (packDwords128 f) =
      f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ := by
  unfold sumDwords128
  rw [getDword128_packDwords128, getDword128_packDwords128,
      getDword128_packDwords128, getDword128_packDwords128]

theorem bv32_add_assoc4 (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    (a0 + b0) + (a1 + b1) + (a2 + b2) + (a3 + b3) =
      (a0 + a1 + a2 + a3) + (b0 + b1 + b2 + b3) := by
  have hc := BitVec.add_comm (n := 32)
  have ha := BitVec.add_assoc (n := 32)
  calc (a0 + b0) + (a1 + b1) + (a2 + b2) + (a3 + b3)
    _ = ((a0 + a1) + (b0 + b1)) + (a2 + b2) + (a3 + b3) := by
        congr 2
        rw [ha, ← ha b0 a1 b1, hc b0 a1, ha a1 b0 b1, ← ha]
    _ = (((a0 + a1) + a2) + ((b0 + b1) + b2)) + (a3 + b3) := by
        congr 1
        rw [ha, ← ha (b0 + b1) a2 b2, hc (b0 + b1) a2, ha a2 (b0 + b1) b2, ← ha]
    _ = (a0 + a1 + a2 + a3) + (b0 + b1 + b2 + b3) := by
        rw [ha, ← ha ((b0 + b1) + b2) a3 b3, hc ((b0 + b1) + b2) a3, ha a3 ((b0 + b1) + b2) b3, ← ha]

theorem sumDwords128_paddd (a b : BitVec 128) :
    sumDwords128 (packDwords128 fun i => getDword128 a i + getDword128 b i) =
      sumDwords128 a + sumDwords128 b := by
  rw [sumDwords128_packDwords128]
  unfold sumDwords128
  exact bv32_add_assoc4 _ _ _ _ _ _ _ _

theorem sumDwords256_append (hi lo : BitVec 128) :
    sumDwords256 (hi ++ lo) = sumDwords128 lo + sumDwords128 hi := by
  unfold sumDwords256
  rw [extract_lo128_append, extract_hi128_append]

theorem sumDwords256_vpaddd (a b : BitVec 256) :
    sumDwords256
      ((packDwords128 fun i => getDword128 (BitVec.extractLsb' 128 128 a) i +
                               getDword128 (BitVec.extractLsb' 128 128 b) i) ++
       (packDwords128 fun i => getDword128 (BitVec.extractLsb' 0 128 a) i +
                               getDword128 (BitVec.extractLsb' 0 128 b) i)) =
      sumDwords256 a + sumDwords256 b := by
  rw [sumDwords256_append, sumDwords128_paddd, sumDwords128_paddd]
  unfold sumDwords256
  have ha := BitVec.add_assoc (n := 32)
  have hc := BitVec.add_comm (n := 32)
  rw [ha, ← ha (sumDwords128 (BitVec.extractLsb' 0 128 b)), hc (sumDwords128 (BitVec.extractLsb' 0 128 b)),
      ha (sumDwords128 (BitVec.extractLsb' 128 128 a)), ← ha]

theorem sumDwords256_perm2i128_add (a b : BitVec 256) :
    sumDwords256 (perm2i128Eval a b 0x31#8) + sumDwords256 (perm2i128Eval a b 0x20#8) =
      sumDwords256 a + sumDwords256 b := by
  have h31 : perm2i128Eval a b 0x31#8 =
      BitVec.extractLsb' 128 128 b ++ BitVec.extractLsb' 128 128 a := rfl
  have h20 : perm2i128Eval a b 0x20#8 =
      BitVec.extractLsb' 0 128 b ++ BitVec.extractLsb' 0 128 a := rfl
  rw [h31, h20, sumDwords256_append, sumDwords256_append]
  unfold sumDwords256
  have ha := BitVec.add_assoc (n := 32)
  have hc := BitVec.add_comm (n := 32)
  rw [hc (sumDwords128 (BitVec.extractLsb' 128 128 a) + sumDwords128 (BitVec.extractLsb' 128 128 b))]
  rw [ha, ← ha (sumDwords128 (BitVec.extractLsb' 0 128 b)), hc (sumDwords128 (BitVec.extractLsb' 0 128 b)),
      ha (sumDwords128 (BitVec.extractLsb' 128 128 a)), ← ha]

theorem nat_mul_pow2_or_eq_add (q : Nat) :
    ∀ (k r : Nat), r < 2 ^ k → ((q * 2 ^ k) ||| r) = q * 2 ^ k + r := by
  intro k
  induction k with
  | zero =>
    intro r hr
    have hr0 : r = 0 := by omega
    subst hr0; simp
  | succ m ih =>
    intro r hr
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
    have hmul : q * 2 ^ (m + 1) = 2 * (q * 2 ^ m) := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (q * 2 ^ m) 2]
    have hmod_or : ((2 * (q * 2 ^ m)) ||| r) % 2 = r % 2 := by
      have htb := Nat.testBit_or (2 * (q * 2 ^ m)) r 0
      rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at htb
      have hev : (2 * (q * 2 ^ m)) % 2 = 0 := Nat.mul_mod_right 2 _
      rw [hev] at htb
      simp only [show decide (0 = 1) = false from rfl, Bool.false_or] at htb
      have hlt2 : ((2 * (q * 2 ^ m)) ||| r) % 2 < 2 := Nat.mod_lt _ (by decide)
      have hr2 : r % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases hr1 : r % 2 = 1
      · have h1 : decide (((2 * (q * 2 ^ m)) ||| r) % 2 = 1) = true := by rw [htb]; simp [hr1]
        have h1' : ((2 * (q * 2 ^ m)) ||| r) % 2 = 1 := of_decide_eq_true h1
        omega
      · have h0 : decide (((2 * (q * 2 ^ m)) ||| r) % 2 = 1) = false := by rw [htb]; simp [hr1]
        have h0' : ((2 * (q * 2 ^ m)) ||| r) % 2 ≠ 1 := of_decide_eq_false h0
        omega
    have hdiv_or : ((2 * (q * 2 ^ m)) ||| r) / 2 = (q * 2 ^ m) ||| (r / 2) := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [← Nat.testBit_succ, Nat.testBit_or, Nat.testBit_or]
      have hl : (2 * (q * 2 ^ m)).testBit (i + 1) = (q * 2 ^ m).testBit i := by
        rw [Nat.testBit_succ, Nat.mul_div_right _ (by decide)]
      rw [hl, Nat.testBit_succ]
    have hdm1 := Nat.div_add_mod ((2 * (q * 2 ^ m)) ||| r) 2
    have hdm2 := Nat.div_add_mod r 2
    have hih := ih (r / 2) (by rw [hpow] at hr; omega)
    rw [hmul, ← hdm1, hdiv_or, hmod_or, hih]
    omega

theorem u16_mul_split_pack (a b : BitVec 16) :
    BitVec.ofNat 16 ((a.toNat * b.toNat) / 65536) ++ (a * b) =
      a.zeroExtend 32 * b.zeroExtend 32 := by
  apply BitVec.eq_of_toNat_eq
  unfold BitVec.zeroExtend
  have ha := a.isLt
  have hb := b.isLt
  have hprod : a.toNat * b.toNat < 2 ^ 32 := by
    have h1 : a.toNat * b.toNat ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.lt_of_le_of_lt h1 (by decide)
  have hhi : (a.toNat * b.toNat) / 65536 < 65536 := by omega
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_setWidth,
             Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt (Nat.lt_trans ha (by decide : 2 ^ 16 < 2 ^ 32)),
      Nat.mod_eq_of_lt (Nat.lt_trans hb (by decide : 2 ^ 16 < 2 ^ 32)),
      Nat.mod_eq_of_lt hprod]
  have hlt := Nat.mod_lt (a.toNat * b.toNat) (by decide : 0 < 2 ^ 16)
  rw [nat_mul_pow2_or_eq_add ((a.toNat * b.toNat) / 65536) 16 ((a.toNat * b.toNat) % 2 ^ 16) hlt]
  have hpow : (2 ^ 16 : Nat) = 65536 := rfl
  rw [hpow, Nat.mul_comm _ 65536, Nat.div_add_mod]

theorem getDword128_packWords128 (f : Fin 8 → BitVec 16) (i : Fin 4) :
    getDword128 (packWords128 f) i = f ⟨2 * i.val + 1, by omega⟩ ++ f ⟨2 * i.val, by omega⟩ := by
  have hw0 := getWord128_packWords128 f ⟨2 * i.val, by omega⟩
  have hw1 := getWord128_packWords128 f ⟨2 * i.val + 1, by omega⟩
  unfold getWord128 at hw0 hw1
  dsimp only at hw0 hw1
  unfold getDword128
  rw [← hw0, ← hw1]
  have hs := append_extractLsb_split (a := 16) (b := 16) (by decide) (2 * i.val * 16) (by omega) (packWords128 f)
  have h1 : 2 * i.val * 16 + 16 = (2 * i.val + 1) * 16 := by omega
  have h2 : i.val * 32 = 2 * i.val * 16 := by omega
  rw [h1] at hs
  rw [h2]
  exact hs.symm

theorem sumDwords128_unpack_mul_pair (x y : BitVec 128) :
    let lo := pmullw128 x y
    let hi := pmulhuw128 x y
    sumDwords128 (unpack128 .hwd lo hi) + sumDwords128 (unpack128 .lwd lo hi) =
      (getWord128 x ⟨0, by decide⟩).zeroExtend 32 * (getWord128 y ⟨0, by decide⟩).zeroExtend 32 +
      (getWord128 x ⟨1, by decide⟩).zeroExtend 32 * (getWord128 y ⟨1, by decide⟩).zeroExtend 32 +
      (getWord128 x ⟨2, by decide⟩).zeroExtend 32 * (getWord128 y ⟨2, by decide⟩).zeroExtend 32 +
      (getWord128 x ⟨3, by decide⟩).zeroExtend 32 * (getWord128 y ⟨3, by decide⟩).zeroExtend 32 +
      (getWord128 x ⟨4, by decide⟩).zeroExtend 32 * (getWord128 y ⟨4, by decide⟩).zeroExtend 32 +
      (getWord128 x ⟨5, by decide⟩).zeroExtend 32 * (getWord128 y ⟨5, by decide⟩).zeroExtend 32 +
      (getWord128 x ⟨6, by decide⟩).zeroExtend 32 * (getWord128 y ⟨6, by decide⟩).zeroExtend 32 +
      (getWord128 x ⟨7, by decide⟩).zeroExtend 32 * (getWord128 y ⟨7, by decide⟩).zeroExtend 32 := by
  dsimp only [unpack128, pmullw128, pmulhuw128, sumDwords128]
  repeat rw [getDword128_packWords128]
  dsimp only
  simp only [show ((2 * 0 + 1) % 2 == 0) = false from rfl, show ((2 * 0) % 2 == 0) = true from rfl,
             ite_true, Bool.false_eq_true, ite_false]
  repeat rw [getWord128_packWords128]
  repeat rw [u16_mul_split_pack]
  rw [BitVec.add_comm]
  simp only [BitVec.add_assoc]

theorem getWord128_unpack_lbw_zero (a : BitVec 128) (i : Fin 8) :
    getWord128 (unpack128 .lbw a 0#128) i = (getByte128 a ⟨i.val, by omega⟩).zeroExtend 16 := by
  unfold unpack128 getWord128
  let f : Fin 16 → BitVec 8 := fun j => if j.val % 2 == 0 then getByte128 a ⟨j.val / 2, by omega⟩ else getByte128 0#128 ⟨j.val / 2, by omega⟩
  change BitVec.extractLsb' (i.val * 16) 16 (packBytes128 f) = _
  have hs := append_extractLsb_split (a := 8) (b := 8) (by decide) (i.val * 16) (by omega) (packBytes128 f)
  rw [← hs]
  have hb0 : BitVec.extractLsb' (2 * i.val * 8) 8 (packBytes128 f) = f ⟨2 * i.val, by omega⟩ :=
    getByte128_packBytes128 f ⟨2 * i.val, by omega⟩
  have hb1 : BitVec.extractLsb' ((2 * i.val + 1) * 8) 8 (packBytes128 f) = f ⟨2 * i.val + 1, by omega⟩ :=
    getByte128_packBytes128 f ⟨2 * i.val + 1, by omega⟩
  have h1 : i.val * 16 = (2 * i.val) * 8 := by omega
  have h2 : i.val * 16 + 8 = (2 * i.val + 1) * 8 := by omega
  rw [h2, h1, hb0, hb1]
  dsimp only [f]
  have hm0 : ((2 * i.val) % 2 == 0) = true := by simp
  have hm1 : ((2 * i.val + 1) % 2 == 0) = false := by simp
  have hd0 : (2 * i.val) / 2 = i.val := by omega
  rw [hm0, hm1]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  have hz : getByte128 0#128 ⟨(2 * i.val + 1) / 2, by omega⟩ = 0#8 := by
    unfold getByte128; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp
  rw [hz]
  have hfi : (⟨(2 * i.val) / 2, by omega⟩ : Fin 16) = ⟨i.val, by omega⟩ := Fin.ext hd0
  rw [hfi]
  unfold BitVec.zeroExtend
  rw [setWidth_eq_zero_append (m := 8)]

theorem getWord128_unpack_hbw_zero (a : BitVec 128) (i : Fin 8) :
    getWord128 (unpack128 .hbw a 0#128) i = (getByte128 a ⟨8 + i.val, by omega⟩).zeroExtend 16 := by
  unfold unpack128 getWord128
  let f : Fin 16 → BitVec 8 := fun j => if j.val % 2 == 0 then getByte128 a ⟨8 + j.val / 2, by omega⟩ else getByte128 0#128 ⟨8 + j.val / 2, by omega⟩
  change BitVec.extractLsb' (i.val * 16) 16 (packBytes128 f) = _
  have hs := append_extractLsb_split (a := 8) (b := 8) (by decide) (i.val * 16) (by omega) (packBytes128 f)
  rw [← hs]
  have hb0 : BitVec.extractLsb' (2 * i.val * 8) 8 (packBytes128 f) = f ⟨2 * i.val, by omega⟩ :=
    getByte128_packBytes128 f ⟨2 * i.val, by omega⟩
  have hb1 : BitVec.extractLsb' ((2 * i.val + 1) * 8) 8 (packBytes128 f) = f ⟨2 * i.val + 1, by omega⟩ :=
    getByte128_packBytes128 f ⟨2 * i.val + 1, by omega⟩
  have h1 : i.val * 16 = (2 * i.val) * 8 := by omega
  have h2 : i.val * 16 + 8 = (2 * i.val + 1) * 8 := by omega
  rw [h2, h1, hb0, hb1]
  dsimp only [f]
  have hm0 : ((2 * i.val) % 2 == 0) = true := by simp
  have hm1 : ((2 * i.val + 1) % 2 == 0) = false := by simp
  have hd0 : 8 + (2 * i.val) / 2 = 8 + i.val := by omega
  rw [hm0, hm1]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  have hz : getByte128 0#128 ⟨8 + (2 * i.val + 1) / 2, by omega⟩ = 0#8 := by
    unfold getByte128; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp
  rw [hz]
  have hfi : (⟨8 + (2 * i.val) / 2, by omega⟩ : Fin 16) = ⟨8 + i.val, by omega⟩ := Fin.ext hd0
  rw [hfi]
  unfold BitVec.zeroExtend
  rw [setWidth_eq_zero_append (m := 8)]

theorem zext8_16_32_eq (b : BitVec 8) : (b.zeroExtend 16).zeroExtend 32 = b.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  unfold BitVec.zeroExtend
  by_cases h16 : i < 16
  · simp [hi]
  · simp [hi]

theorem horiz_reduce_128_eq (v : BitVec 128) :
    let v1 := packDwords128 fun i => getDword128 v i + getDword128 (psrldq128 v 8#8) i
    let v2 := packDwords128 fun i => getDword128 v1 i + getDword128 (psrldq128 v1 4#8) i
    BitVec.extractLsb' 0 32 v2 = sumDwords128 v := by
  dsimp only
  have hsh8 : ∀ (x : BitVec 128) (k : Fin 2),
      getDword128 (psrldq128 x 8#8) ⟨k.val, by omega⟩ = getDword128 x ⟨k.val + 2, by omega⟩ := by
    intro x k
    unfold psrldq128 getDword128
    have hge : ((8#8 : BitVec 8).toNat ≥ 16) = false := by decide
    simp only [hge, Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h64 : (8#8 : BitVec 8).toNat * 8 = 64 := rfl
    rw [h64]
    have hsum : 64 + (k.val * 32 + b) = (k.val + 2) * 32 + b := by omega
    simp [hb, hsum]
  have hsh4 : ∀ (x : BitVec 128),
      getDword128 (psrldq128 x 4#8) ⟨0, by decide⟩ = getDword128 x ⟨1, by decide⟩ := by
    intro x
    unfold psrldq128 getDword128
    have hge : ((4#8 : BitVec 8).toNat ≥ 16) = false := by decide
    simp only [hge, Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h32 : (4#8 : BitVec 8).toNat * 8 = 32 := rfl
    rw [h32]; simp [hb]
  change getDword128 (packDwords128 _) ⟨0, by decide⟩ = sumDwords128 v
  rw [getDword128_packDwords128, hsh4, getDword128_packDwords128, getDword128_packDwords128]
  rw [hsh8 v ⟨0, by decide⟩, hsh8 v ⟨1, by decide⟩]
  dsimp only
  unfold sumDwords128
  have ha := BitVec.add_assoc (n := 32)
  have hc := BitVec.add_comm (n := 32)
  rw [ha, ← ha (getDword128 v ⟨2, by decide⟩), hc (getDword128 v ⟨2, by decide⟩),
      ha (getDword128 v ⟨1, by decide⟩), ← ha, ← ha]

theorem rustDotU8U16From_add (m : ByteMem) (pa pb : BitVec 64) (n : Nat) (s0 s1 : BitVec 32) :
    rustDotU8U16From m pa pb n (s0 + s1) = s0 + rustDotU8U16From m pa pb n s1 := by
  induction n generalizing pa pb s0 s1 with
  | zero => rw [rustDotU8U16From_zero, rustDotU8U16From_zero]
  | succ k ih =>
    rw [rustDotU8U16From_succ, rustDotU8U16From_succ]
    unfold dotStepU8U16
    rw [BitVec.add_assoc, ih]

theorem rustDotU8U16From_split (m : ByteMem) (pa pb : BitVec 64) (n1 n2 : Nat) (s : BitVec 32) :
    rustDotU8U16From m pa pb (n1 + n2) s =
      rustDotU8U16From m (pa + BitVec.ofNat 64 n1) (pb + BitVec.ofNat 64 (2 * n1)) n2
        (rustDotU8U16From m pa pb n1 s) := by
  induction n1 generalizing pa pb s with
  | zero =>
    rw [Nat.zero_add, rustDotU8U16From_zero]
    have h0 : BitVec.ofNat 64 0 = 0#64 := rfl
    rw [Nat.mul_zero, h0, BitVec.add_zero, BitVec.add_zero]
  | succ k ih =>
    rw [Nat.succ_add, rustDotU8U16From_succ, rustDotU8U16From_succ, ih]
    congr 1
    · change pa + BitVec.ofNat 64 1 + BitVec.ofNat 64 k = pa + BitVec.ofNat 64 (k + 1)
      rw [bv64_add_ofNat_assoc]; congr 2; omega
    · change pb + BitVec.ofNat 64 2 + BitVec.ofNat 64 (2 * k) = pb + BitVec.ofNat 64 (2 * (k + 1))
      rw [bv64_add_ofNat_assoc]; congr 2; omega


/-! ## Section 4: Masking/Guard Lemmas, `extend`/`vpmulld` Algebra, & O(1) SIMD `exec_*` Lemmas -/

theorem bv64_and_mask_toNat (x : BitVec 64) (k : Nat) (_hk : k < 64) :
    (x &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ k)).toNat = (x.toNat / 2 ^ k) * 2 ^ k := by
  have h1 : x &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ k) = (x >>> k) <<< k := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases hlt : i < k
    · have hzero : (BitVec.ofNat 64 (2 ^ 64 - 2 ^ k)).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]
        have hlt2 : 2 ^ 64 - 2 ^ k < 2 ^ 64 := by
          have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
          omega
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hd : (2 ^ 64 - 2 ^ k) / 2 ^ i = 2 ^ (64 - i) - 2 ^ (k - i) := by
          have hmul : 2 ^ 64 - 2 ^ k = (2 ^ (64 - i) - 2 ^ (k - i)) * 2 ^ i := by
            rw [Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
            rw [show 64 - i + i = 64 by omega, show k - i + i = k by omega]
          rw [hmul, Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]
        rw [hd]
        have heven : 2 ∣ (2 ^ (64 - i) - 2 ^ (k - i)) := by
          have ha : 2 ^ (64 - i) = 2 * 2 ^ (64 - i - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          have hb : 2 ^ (k - i) = 2 * 2 ^ (k - i - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          rw [ha, hb, ← Nat.mul_sub_left_distrib]
          exact Nat.dvd_mul_right 2 _
        rcases heven with ⟨q, hq⟩
        rw [hq]
        have hmod : (1 &&& (2 * q)) = 0 := by
          rw [Nat.and_comm, Nat.and_one_is_mod, Nat.mul_mod_right]
        rw [hmod]; simp
      simp [hlt, hzero]
    · have hone : (BitVec.ofNat 64 (2 ^ 64 - 2 ^ k)).getLsbD i = true := by
        rw [BitVec.getLsbD_ofNat]
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have h2 : 2 ^ 64 - 2 ^ k = (2 ^ (64 - i) - 1) * 2 ^ i + (2 ^ i - 2 ^ k) := by
          have hpow1 : 2 ^ (64 - i) * 2 ^ i = 2 ^ 64 := by
            rw [← Nat.pow_add, show 64 - i + i = 64 by omega]
          have hle2 : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
          have hle3 : 2 ^ i ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
          have hle4 : 2 ^ k ≤ 2 ^ 64 := Nat.le_trans hle2 hle3
          rw [Nat.sub_mul, Nat.one_mul, hpow1]
          omega
        have hrem : 2 ^ i - 2 ^ k < 2 ^ i := by
          have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
          have hle2 : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        rw [h2, Nat.mul_comm _ (2 ^ i), Nat.mul_add_div (Nat.pow_pos (by decide)),
            Nat.div_eq_of_lt hrem, Nat.add_zero]
        have hodd : 2 ^ (64 - i) - 1 = 2 * (2 ^ (64 - i - 1) - 1) + 1 := by
          have ha : 2 ^ (64 - i) = 2 * 2 ^ (64 - i - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          have hp : 1 ≤ 2 ^ (64 - i - 1) := Nat.pow_pos (by decide)
          omega
        rw [hodd]
        have hmod : (1 &&& (2 * (2 ^ (64 - i - 1) - 1) + 1)) = 1 := by
          rw [Nat.and_comm, Nat.and_one_is_mod, Nat.mul_add_mod]
        rw [hmod]; simp [hi]
      have hge : k ≤ i := by omega
      have hsum : k + (i - k) = i := by omega
      simp [hlt, hone, hi, hsum]
  rw [h1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hlt64 := x.isLt
  have hle : (x.toNat / 2 ^ k) * 2 ^ k ≤ x.toNat := by
    rw [Nat.mul_comm]; exact Nat.mul_div_le x.toNat (2 ^ k)
  exact Nat.mod_eq_of_lt (by omega)

theorem bv64_and_neg32_toNat (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFFFE0#64).toNat = (x.toNat / 32) * 32 :=
  bv64_and_mask_toNat x 5 (by decide)

theorem bv64_and_neg16_toNat (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFFFF0#64).toNat = (x.toNat / 16) * 16 :=
  bv64_and_mask_toNat x 4 (by decide)

theorem bv64_and_neg8_toNat (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFFFF8#64).toNat = (x.toNat / 8) * 8 :=
  bv64_and_mask_toNat x 3 (by decide)

theorem bv64_test_lo8_mask (x : BitVec 64) (m : Nat) (hm : m < 8) :
    ((BitVec.extractLsb' 0 8 x) &&& BitVec.ofNat 8 (2 ^ m - 1) == 0#8) = decide (x.toNat % 2 ^ m = 0) := by
  have hmod : ((BitVec.extractLsb' 0 8 x) &&& BitVec.ofNat 8 (2 ^ m - 1)).toNat = x.toNat % 2 ^ m := by
    rw [BitVec.toNat_and, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
    have hm8 : 2 ^ m - 1 < 2 ^ 8 := by
      have h1 : 2 ^ m ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ 7 < 2 ^ 8 := by decide
      omega
    rw [Nat.mod_eq_of_lt hm8, Nat.and_two_pow_sub_one_eq_mod]
    have hdiv : 2 ^ m ∣ 2 ^ 8 := Nat.pow_dvd_pow 2 (by omega)
    rcases hdiv with ⟨q, hq⟩
    rw [hq, Nat.mod_mul_right_mod]
  cases h : ((BitVec.extractLsb' 0 8 x) &&& BitVec.ofNat 8 (2 ^ m - 1) == 0#8)
  · have hne : (BitVec.extractLsb' 0 8 x) &&& BitVec.ofNat 8 (2 ^ m - 1) ≠ 0#8 := by
      intro heq; rw [heq] at h; simp at h
    have hnz : x.toNat % 2 ^ m ≠ 0 := by
      intro hz; apply hne; apply BitVec.eq_of_toNat_eq; rw [hmod, hz]; rfl
    simp [hnz]
  · have heq := eq_of_beq h
    have hz : x.toNat % 2 ^ m = 0 := by rw [← hmod, heq]; rfl
    simp [hz]

theorem bv64_test_lo8_15_eq (x : BitVec 64) :
    (BitVec.extractLsb' 0 8 x &&& 0x0F#8 == 0#8) = decide (x.toNat % 16 = 0) :=
  bv64_test_lo8_mask x 4 (by decide)

theorem bv64_test_lo8_7_eq (x : BitVec 64) :
    (BitVec.extractLsb' 0 8 x &&& 0x07#8 == 0#8) = decide (x.toNat % 8 = 0) :=
  bv64_test_lo8_mask x 3 (by decide)

theorem bv64_sub1_cmp_be (n : BitVec 64) (k : Nat) (hn : 0 < n.toNat) (hk : k < 2 ^ 64) :
    (decide ((n + 0xFFFFFFFFFFFFFFFF#64).toNat < k) ||
      ((n + 0xFFFFFFFFFFFFFFFF#64) - BitVec.ofNat 64 k == 0#64)) = decide (n.toNat ≤ k + 1) := by
  have hneg1 : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = -1#64 := rfl
  rw [hneg1, ← BitVec.sub_eq_add_neg]
  have hsub1 : (n - 1#64).toNat = n.toNat - 1 := by
    rw [bv64_sub_toNat_of_le (by exact hn)]; rfl
  have hktn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  by_cases hlt : n.toNat - 1 < k
  · have h1 : decide ((n - 1#64).toNat < k) = true := by rw [hsub1]; simp [hlt]
    have h2 : decide (n.toNat ≤ k + 1) = true := by simp [show n.toNat ≤ k + 1 by omega]
    rw [h1, h2]; rfl
  · by_cases heq : n.toNat - 1 = k
    · have hbv : n - 1#64 = BitVec.ofNat 64 k := by
        apply BitVec.eq_of_toNat_eq; rw [hsub1, hktn, heq]
      have h2 : decide (n.toNat ≤ k + 1) = true := by simp [show n.toNat ≤ k + 1 by omega]
      rw [hbv, cmp_sub_self_zero, h2]; simp
    · have h1 : decide ((n - 1#64).toNat < k) = false := by rw [hsub1]; simp [hlt]
      have hne : n - 1#64 ≠ BitVec.ofNat 64 k := by
        intro h; have ht := congrArg BitVec.toNat h; rw [hsub1, hktn] at ht; exact heq ht
      have h2 : decide (n.toNat ≤ k + 1) = false := by simp [show ¬ n.toNat ≤ k + 1 by omega]
      rw [h1, cmp_sub_zero_false_of_ne hne, h2]; rfl

theorem bv64_shl1_toNat {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    x <<< 1 = BitVec.ofNat 64 (2 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have h2 : (2 ^ 1 : Nat) = 2 := rfl
  rw [h2, Nat.mul_comm, Nat.mod_eq_of_lt h]

/-! ### Exact `vpmovzxbw` / `vpmovzxwd` / `vpmulld` / `vpsrlq 0x20` & 8-Elem Dot Helpers -/

def sumLo2Dwords128 (v : BitVec 128) : BitVec 32 :=
  getDword128 v ⟨0, by decide⟩ + getDword128 v ⟨1, by decide⟩

theorem sumLo2Dwords128_paddd (a b : BitVec 128) :
    sumLo2Dwords128 (packDwords128 fun i => getDword128 a i + getDword128 b i) =
      sumLo2Dwords128 a + sumLo2Dwords128 b := by
  unfold sumLo2Dwords128
  rw [getDword128_packDwords128, getDword128_packDwords128]
  have ha := BitVec.add_assoc (n := 32)
  have hc := BitVec.add_comm (n := 32)
  rw [ha, ← ha (getDword128 b ⟨0, by decide⟩), hc (getDword128 b ⟨0, by decide⟩),
      ha (getDword128 a ⟨1, by decide⟩), ← ha]

theorem sumLo2Dwords128_fold8_eq (v : BitVec 128) :
    sumLo2Dwords128 (packDwords128 fun i => getDword128 v i + getDword128 (psrldq128 v 8#8) i) =
      sumDwords128 v := by
  unfold sumLo2Dwords128 sumDwords128
  rw [getDword128_packDwords128, getDword128_packDwords128]
  have hsh8 : ∀ k : Fin 2, getDword128 (psrldq128 v 8#8) ⟨k.val, by omega⟩ =
      getDword128 v ⟨k.val + 2, by omega⟩ := by
    intro k; unfold psrldq128 getDword128
    have hge : ((8#8 : BitVec 8).toNat ≥ 16) = false := by decide
    simp only [hge, Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h64 : (8#8 : BitVec 8).toNat * 8 = 64 := rfl
    rw [h64]; have hsum : 64 + (k.val * 32 + b) = (k.val + 2) * 32 + b := by omega
    simp [hb, hsum]
  rw [hsh8 ⟨0, by decide⟩, hsh8 ⟨1, by decide⟩]
  dsimp only
  have ha := BitVec.add_assoc (n := 32)
  have hc := BitVec.add_comm (n := 32)
  rw [ha, ← ha (getDword128 v ⟨2, by decide⟩), hc (getDword128 v ⟨2, by decide⟩),
      ha (getDword128 v ⟨1, by decide⟩), ← ha, ← ha]

theorem sumLo2Dwords128_zext32 (x : BitVec 32) :
    sumLo2Dwords128 ((x.zeroExtend 64).zeroExtend 128) = x := by
  unfold sumLo2Dwords128 getDword128
  have h0 : BitVec.extractLsb' (0 * 32) 32 ((x.zeroExtend 64).zeroExtend 128) = x := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; unfold BitVec.zeroExtend
    simp [hi, show i < 128 by omega]
  have h1 : BitVec.extractLsb' (1 * 32) 32 ((x.zeroExtend 64).zeroExtend 128) = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; unfold BitVec.zeroExtend
    simp [hi]
  rw [h0, h1, BitVec.add_zero]

theorem fold_psrlq32_eq_sumLo2 (v : BitVec 128) :
    BitVec.extractLsb' 0 32
      (packDwords128 fun i => getDword128 v i + getDword128 (psrlqImm128 v 0x20#8) i) =
      sumLo2Dwords128 v := by
  change getDword128 (packDwords128 _) ⟨0, by decide⟩ = sumLo2Dwords128 v
  rw [getDword128_packDwords128]
  unfold sumLo2Dwords128
  congr 1
  unfold psrlqImm128 getDword128
  have hge : ((0x20#8 : BitVec 8).toNat ≥ 64) = false := by decide
  simp only [hge, Bool.false_eq_true, ite_false]
  have hq := getQword128_packQwords128 (fun i => getQword128 v i >>> (0x20#8 : BitVec 8).toNat) ⟨0, by decide⟩
  unfold getQword128 at hq
  dsimp only at hq
  have h0 : BitVec.extractLsb' (0 * 32) 32 (packQwords128 fun i => getQword128 v i >>> (0x20#8 : BitVec 8).toNat) =
      BitVec.extractLsb' 0 32 (BitVec.extractLsb' (0 * 64) 64 (packQwords128 fun i => getQword128 v i >>> (0x20#8 : BitVec 8).toNat)) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  rw [h0]
  unfold getQword128
  rw [hq]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h32 : (0x20#8 : BitVec 8).toNat = 32 := rfl
  rw [h32]
  simp [hi, show 32 + i < 64 by omega]

theorem getDword128_pmulld (a b : BitVec 128) (i : Fin 4) :
    getDword128 (pmulld128 a b) i = getDword128 a i * getDword128 b i := by
  unfold pmulld128; exact getDword128_packDwords128 _ i

theorem getWord128_packWords256_lo (f : Fin 16 → BitVec 16) (i : Fin 8) :
    getWord128 (BitVec.extractLsb' 0 128 (packWords256 f)) i = f ⟨i.val, by omega⟩ := by
  unfold packWords256
  rw [extract_lo128_append, getWord128_packWords128]

theorem getWord128_packWords256_hi (f : Fin 16 → BitVec 16) (i : Fin 8) :
    getWord128 (BitVec.extractLsb' 128 128 (packWords256 f)) i = f ⟨8 + i.val, by omega⟩ := by
  unfold packWords256
  rw [extract_hi128_append, getWord128_packWords128]
  congr 1; apply Fin.ext; dsimp; omega

theorem readMem256_lo128 (m : ByteMem) (p : BitVec 64) :
    BitVec.extractLsb' 0 128 (readMem256 m p) = readMem128 m p := by
  unfold readMem256; exact extract_lo128_append _ _

theorem readMem256_hi128 (m : ByteMem) (p : BitVec 64) :
    BitVec.extractLsb' 128 128 (readMem256 m p) = readMem128 m (p + 16#64) := by
  unfold readMem256; exact extract_hi128_append _ _

theorem getByte128_psrldq8 (v : BitVec 128) (i : Fin 8) :
    getByte128 (psrldq128 v 8#8) ⟨i.val, by omega⟩ = getByte128 v ⟨8 + i.val, by omega⟩ := by
  unfold psrldq128 getByte128
  have hge : ((8#8 : BitVec 8).toNat ≥ 16) = false := by decide
  simp only [hge, Bool.false_eq_true, ite_false]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have h64 : (8#8 : BitVec 8).toNat * 8 = 64 := rfl
  rw [h64]; have hsum : 64 + (i.val * 8 + b) = (8 + i.val) * 8 + b := by omega
  simp [hb, hsum]

theorem psrlq32_lo64_eq (v : BitVec 128) :
    BitVec.extractLsb' 0 64 (psrlqImm128 v 0x20#8) =
      (BitVec.extractLsb' 0 64 v) >>> 32 := by
  unfold psrlqImm128
  have hge : ((0x20#8 : BitVec 8).toNat ≥ 64) = false := by decide
  simp only [hge, Bool.false_eq_true, ite_false]
  have hq := getQword128_packQwords128 (fun i => getQword128 v i >>> (0x20#8 : BitVec 8).toNat) ⟨0, by decide⟩
  unfold getQword128 at hq
  exact hq

theorem extract_lo64_zext128 (q : BitVec 64) :
    BitVec.extractLsb' 0 64 (q.zeroExtend 128) = q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; unfold BitVec.zeroExtend
  simp [hi, show i < 128 by omega]

theorem extract_lo64_packWords128_word (f : Fin 8 → BitVec 16) (k : Fin 4) :
    BitVec.extractLsb' (k.val * 16) 16 (BitVec.extractLsb' 0 64 (packWords128 f)) =
      f ⟨k.val, by omega⟩ := by
  have h1 : BitVec.extractLsb' (k.val * 16) 16 (BitVec.extractLsb' 0 64 (packWords128 f)) =
      getWord128 (packWords128 f) ⟨k.val, by omega⟩ := by
    unfold getWord128; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi, show k.val * 16 + i < 64 by omega]
  rw [h1, getWord128_packWords128]

theorem extract_lo64_shr32_byte (q : BitVec 64) (k : Fin 4) :
    BitVec.extractLsb' (k.val * 8) 8 (q >>> 32) = byteOf64 q (4 + k.val) := by
  unfold byteOf64; apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hsum : 32 + (k.val * 8 + i) = (4 + k.val) * 8 + i := by omega
  simp [hi, hsum]

theorem extract_lo64_shr32_word (q : BitVec 64) (k : Fin 2) :
    BitVec.extractLsb' (k.val * 16) 16 (q >>> 32) = BitVec.extractLsb' ((2 + k.val) * 16) 16 q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hsum : 32 + (k.val * 16 + i) = (2 + k.val) * 16 + i := by omega
  simp [hi, hsum]

theorem rustDotU8U16From_8 (m : ByteMem) (pa pb : BitVec 64) (acc : BitVec 32) :
    rustDotU8U16From m pa pb 8 acc =
      acc +
        ((m (pa + 0#64)).zeroExtend 32 * (readMem16 m (pb + 0#64)).zeroExtend 32 +
         (m (pa + 1#64)).zeroExtend 32 * (readMem16 m (pb + 2#64)).zeroExtend 32 +
         (m (pa + 2#64)).zeroExtend 32 * (readMem16 m (pb + 4#64)).zeroExtend 32 +
         (m (pa + 3#64)).zeroExtend 32 * (readMem16 m (pb + 6#64)).zeroExtend 32 +
         (m (pa + 4#64)).zeroExtend 32 * (readMem16 m (pb + 8#64)).zeroExtend 32 +
         (m (pa + 5#64)).zeroExtend 32 * (readMem16 m (pb + 10#64)).zeroExtend 32 +
         (m (pa + 6#64)).zeroExtend 32 * (readMem16 m (pb + 12#64)).zeroExtend 32 +
         (m (pa + 7#64)).zeroExtend 32 * (readMem16 m (pb + 14#64)).zeroExtend 32) := by
  have hp : ∀ (p : BitVec 64) (a b : Nat), p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) :=
    bv64_add_ofNat_assoc
  rw [rustDotU8U16From_succ, rustDotU8U16From_succ, rustDotU8U16From_succ, rustDotU8U16From_succ,
      rustDotU8U16From_succ, rustDotU8U16From_succ, rustDotU8U16From_succ, rustDotU8U16From_succ,
      rustDotU8U16From_zero]
  unfold dotStepU8U16
  have ha0 : m pa = m (pa + 0#64) := congrArg m (BitVec.add_zero pa).symm
  have hb0 : readMem16 m pb = readMem16 m (pb + 0#64) := congrArg (readMem16 m) (BitVec.add_zero pb).symm
  rw [hp pa 1 1, hp pa 2 1, hp pa 3 1, hp pa 4 1, hp pa 5 1, hp pa 6 1]
  rw [hp pb 2 2, hp pb 4 2, hp pb 6 2, hp pb 8 2, hp pb 10 2, hp pb 12 2]
  rw [ha0, hb0]
  simp only [BitVec.add_assoc]

/-! ### O(1) `execByteInstr` Lemmas for Stack, High-Byte, & SIMD Instructions -/

theorem exec_push64 (src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.push64 src) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs .rsp (s.regs .rsp - 8#64),
               mem := writeMem64 s.mem (s.regs .rsp - 8#64) (s.regs src) } := rfl

theorem exec_leave64 (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr .leave64 nr ch s =
      { s with rip := nr,
               regs := regUpd (regUpd s.regs .rsp (s.regs .rbp + 8#64)) .rbp (readMem64 s.mem (s.regs .rbp)) } := rfl

theorem exec_mov8Store_hi8_lo8 (r : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.mov8Store (.reg8 (.hi8 r)) (.lo8 r)) nr ch s =
      { s with rip := nr,
               regs := writeSubReg8 s.regs (.hi8 r) (readSubReg8 s.regs (.lo8 r)) } := rfl

theorem exec_alu8RegRm_xor_lo8_mem (dst : Reg) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.alu8RegRm .xor (.lo8 dst) (.mem8 a)) nr ch s =
      { s with rip := nr,
               regs := writeSubReg8 s.regs (.lo8 dst) (BitVec.extractLsb' 0 8 (s.regs dst) ^^^ s.mem (evalByteAddr s nr a)),
               flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 8 (s.regs dst)) (s.mem (evalByteAddr s nr a)) s.flags ch.flags).2 } := rfl

theorem exec_simdMovLoad_legacy128_mem (dst : YmmIdx) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovLoad .legacy128 dst (.mem a)) nr ch s =
      { s with rip := nr, ymms := writeXmm128 false s.ymms dst (readMem128 s.mem (evalByteAddr s nr a)) } := rfl

theorem exec_simdMovLoad_legacy128_reg (dst src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovLoad .legacy128 dst (.reg src)) nr ch s =
      { s with rip := nr, ymms := writeXmm128 false s.ymms dst (BitVec.extractLsb' 0 128 (s.ymms src)) } := rfl

theorem exec_simdMovLoad_vex128_mem (dst : YmmIdx) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovLoad .vex128 dst (.mem a)) nr ch s =
      { s with rip := nr, ymms := writeXmm128 true s.ymms dst (readMem128 s.mem (evalByteAddr s nr a)) } := rfl

theorem exec_simdMovLoad_vex128_reg (dst src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovLoad .vex128 dst (.reg src)) nr ch s =
      { s with rip := nr, ymms := writeXmm128 true s.ymms dst (BitVec.extractLsb' 0 128 (s.ymms src)) } := rfl

theorem exec_simdMovLoad_vex256_mem (dst : YmmIdx) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovLoad .vex256 dst (.mem a)) nr ch s =
      { s with rip := nr, ymms := ymmUpd s.ymms dst (readMem256 s.mem (evalByteAddr s nr a)) } := rfl

theorem exec_simdMovStore_vex128_mem (a : X64Addr) (src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovStore .vex128 (.mem a) src) nr ch s =
      { s with rip := nr, mem := writeMem128 s.mem (evalByteAddr s nr a) (BitVec.extractLsb' 0 128 (s.ymms src)) } := rfl

theorem exec_simdMovStore_vex256_mem (a : X64Addr) (src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovStore .vex256 (.mem a) src) nr ch s =
      { s with rip := nr, mem := writeMem256 s.mem (evalByteAddr s nr a) (s.ymms src) } := rfl

theorem exec_simdMovqLoad_vex_mem (dst : YmmIdx) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovqLoad true dst (.mem a)) nr ch s =
      { s with rip := nr, ymms := writeXmm128 true s.ymms dst ((readMem64 s.mem (evalByteAddr s nr a)).zeroExtend 128) } := rfl

theorem exec_simdMovqStore_vex_mem (a : X64Addr) (src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovqStore true (.mem a) src) nr ch s =
      { s with rip := nr, mem := writeMem64 s.mem (evalByteAddr s nr a) (BitVec.extractLsb' 0 64 (s.ymms src)) } := rfl

theorem exec_simdMovGprToX_vex32_reg (dst : YmmIdx) (src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovGprToX true false dst (.reg src)) nr ch s =
      { s with rip := nr, ymms := writeXmm128 true s.ymms dst (((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64).zeroExtend 128) } := rfl

theorem exec_simdMovXToGpr_s32_reg (isVex : Bool) (dst : Reg) (src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdMovXToGpr isVex false (.reg dst) src) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.ymms src)).zeroExtend 64) } := by
  dsimp only [execByteInstr, writeByteRm, writeRegSz]
  rw [ifFalse (by decide)]
  dsimp only
  congr 2; congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem exec_simdBitwise_legacy128_xor_self (r : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdBitwise .legacy128 .xor r r (.reg r)) nr ch s =
      { s with rip := nr, ymms := writeXmm128 false s.ymms r 0#128 } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256, BitVec.xor_self]

theorem exec_simdBitwise_vex128_xor_self (r : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdBitwise .vex128 .xor r r (.reg r)) nr ch s =
      { s with rip := nr, ymms := writeXmm128 true s.ymms r 0#128 } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256, BitVec.xor_self]

theorem exec_simdBitwise_vex128_xor_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdBitwise .vex128 .xor dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst (BitVec.extractLsb' 0 128 (s.ymms s1) ^^^ BitVec.extractLsb' 0 128 (s.ymms s2)) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdBitwise_vex128_xor_mem (dst s1 : YmmIdx) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdBitwise .vex128 .xor dst s1 (.mem a)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst (BitVec.extractLsb' 0 128 (s.ymms s1) ^^^ readMem128 s.mem (evalByteAddr s nr a)) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdBitwise_vex256_xor_mem (dst s1 : YmmIdx) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdBitwise .vex256 .xor dst s1 (.mem a)) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms dst
                 ((BitVec.extractLsb' 128 128 (s.ymms s1) ^^^ BitVec.extractLsb' 128 128 (readMem256 s.mem (evalByteAddr s nr a))) ++
                  (BitVec.extractLsb' 0 128 (s.ymms s1) ^^^ BitVec.extractLsb' 0 128 (readMem256 s.mem (evalByteAddr s nr a)))) } := rfl

theorem exec_simdAdd_legacy128_e32_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdAdd .legacy128 .e32 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 false s.ymms dst
                 (packDwords128 fun i => getDword128 (BitVec.extractLsb' 0 128 (s.ymms s1)) i +
                                         getDword128 (BitVec.extractLsb' 0 128 (s.ymms s2)) i) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdAdd_vex128_e32_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdAdd .vex128 .e32 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst
                 (packDwords128 fun i => getDword128 (BitVec.extractLsb' 0 128 (s.ymms s1)) i +
                                         getDword128 (BitVec.extractLsb' 0 128 (s.ymms s2)) i) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdAdd_vex256_e32_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdAdd .vex256 .e32 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms dst
                 ((packDwords128 fun i => getDword128 (BitVec.extractLsb' 128 128 (s.ymms s1)) i +
                                          getDword128 (BitVec.extractLsb' 128 128 (s.ymms s2)) i) ++
                  (packDwords128 fun i => getDword128 (BitVec.extractLsb' 0 128 (s.ymms s1)) i +
                                          getDword128 (BitVec.extractLsb' 0 128 (s.ymms s2)) i)) } := rfl

theorem exec_simdUnpack_legacy128_reg (op : VecUnpackOp) (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdUnpack .legacy128 op dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 false s.ymms dst
                 (unpack128 op (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdUnpack_vex128_reg (op : VecUnpackOp) (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdUnpack .vex128 op dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst
                 (unpack128 op (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdUnpack_vex256_reg (op : VecUnpackOp) (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdUnpack .vex256 op dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms dst
                 (unpack128 op (BitVec.extractLsb' 128 128 (s.ymms s1)) (BitVec.extractLsb' 128 128 (s.ymms s2)) ++
                  unpack128 op (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := rfl

theorem exec_simdExtend_vex128_zxbw_reg (dst src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdExtend .vex128 .zxbw dst (.reg src)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst
                 (packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 (s.ymms src))).zeroExtend 16) } := rfl

theorem exec_simdExtend_vex128_zxwd_reg (dst src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdExtend .vex128 .zxwd dst (.reg src)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst
                 (packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 (s.ymms src))).zeroExtend 32) } := rfl

theorem exec_simdExtend_vex256_zxbw_reg (dst src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdExtend .vex256 .zxbw dst (.reg src)) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms dst
                 (packWords256 fun i => (getByte128 (BitVec.extractLsb' 0 128 (s.ymms src)) i).zeroExtend 16) } := rfl

theorem exec_simdBroadcastB_vex128_reg (dst src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdBroadcastB .vex128 dst (.reg src)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst (packBytes128 fun _ => BitVec.extractLsb' 0 8 (s.ymms src)) } := rfl

theorem exec_simdBroadcastB_vex256_reg (dst src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdBroadcastB .vex256 dst (.reg src)) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms dst (packBytes256 fun _ => BitVec.extractLsb' 0 8 (s.ymms src)) } := rfl

theorem exec_simdPmullw_legacy128_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPmullw .legacy128 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 false s.ymms dst
                 (pmullw128 (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdPmullw_vex128_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPmullw .vex128 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst
                 (pmullw128 (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdPmullw_vex256_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPmullw .vex256 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms dst
                 (pmullw128 (BitVec.extractLsb' 128 128 (s.ymms s1)) (BitVec.extractLsb' 128 128 (s.ymms s2)) ++
                  pmullw128 (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := rfl

theorem exec_simdPmulhuw_legacy128_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPmulhuw .legacy128 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 false s.ymms dst
                 (pmulhuw128 (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdPmulhuw_vex128_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPmulhuw .vex128 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst
                 (pmulhuw128 (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdPmulhuw_vex256_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPmulhuw .vex256 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms dst
                 (pmulhuw128 (BitVec.extractLsb' 128 128 (s.ymms s1)) (BitVec.extractLsb' 128 128 (s.ymms s2)) ++
                  pmulhuw128 (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := rfl

theorem exec_simdPmulld_vex128_reg (dst s1 s2 : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPmulld .vex128 dst s1 (.reg s2)) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst
                 (pmulld128 (BitVec.extractLsb' 0 128 (s.ymms s1)) (BitVec.extractLsb' 0 128 (s.ymms s2))) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdPsrldq_legacy128 (dst src : YmmIdx) (imm : BitVec 8) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPsrldq .legacy128 dst src imm) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 false s.ymms dst (psrldq128 (BitVec.extractLsb' 0 128 (s.ymms src)) imm) } := rfl

theorem exec_simdPsrldq_vex128 (dst src : YmmIdx) (imm : BitVec 8) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPsrldq .vex128 dst src imm) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst (psrldq128 (BitVec.extractLsb' 0 128 (s.ymms src)) imm) } := rfl

theorem exec_simdPsrlqImm_vex128 (dst src : YmmIdx) (imm : BitVec 8) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPsrlqImm .vex128 dst src imm) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst (psrlqImm128 (BitVec.extractLsb' 0 128 (s.ymms src)) imm) } := rfl

theorem exec_simdPshuflw_vex128_reg (dst src : YmmIdx) (imm : BitVec 8) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPshuflw .vex128 dst (.reg src) imm) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst (pshuflw128 (BitVec.extractLsb' 0 128 (s.ymms src)) imm) } := by
  dsimp only [execByteInstr, applyByte128Or256, readByteModeRhs, readByteXmm128]
  rw [extract_lo128_zeroExtend256]

theorem exec_simdExtract128_hi_reg (dst src : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdExtract128 (.reg dst) src 0x01#8) nr ch s =
      { s with rip := nr,
               ymms := writeXmm128 true s.ymms dst (BitVec.extractLsb' 128 128 (s.ymms src)) } := rfl

theorem exec_simdPerm2i128_reg (dst s1 s2 : YmmIdx) (imm : BitVec 8) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdPerm2i128 dst s1 (.reg s2) imm) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms dst (perm2i128Eval (s.ymms s1) (s.ymms s2) imm) } := rfl

theorem bv64_sub8_sub8_eq_sub16 (rsp : BitVec 64) (h : 16 ≤ rsp.toNat) :
    (rsp - 8#64) - 8#64 = rsp - 16#64 := by
  apply BitVec.eq_of_toNat_eq
  have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
  have hs1 : (rsp - 8#64).toNat = rsp.toNat - 8 := by
    rw [bv64_sub_toNat_of_le (by rw [h8]; omega), h8]
  rw [bv64_sub_toNat_of_le (by rw [hs1, h8]; omega), hs1,
      bv64_sub_toNat_of_le (by rw [h16]; exact h), h8, h16]
  omega

theorem bv64_sub8_add_neg8_eq_sub16 (rsp : BitVec 64) (h : 16 ≤ rsp.toNat) :
    (rsp - 8#64) + 0xfffffffffffffff8#64 = rsp - 16#64 := by
  have hneg : (0xfffffffffffffff8#64 : BitVec 64) = -8#64 := rfl
  rw [hneg, ← BitVec.sub_eq_add_neg]
  exact bv64_sub8_sub8_eq_sub16 rsp h

end UntrustedCObjSimdHelpers
