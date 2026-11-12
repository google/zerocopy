-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.Lemmas

namespace Endianness

/-- A finite conjunction supplies one checked proposition for each index. -/
def CheckRange : Nat → (Nat → Prop) → Prop
  | 0, _ => True
  | n + 1, p => p 0 ∧ CheckRange n (fun i => p (i + 1))

theorem checkRange_sound (n : Nat) (p : Nat → Prop)
    (checked : CheckRange n p) : ∀ i, i < n → p i := by
  induction n generalizing p with
  | zero =>
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    intro i hi
    cases i with
    | zero => exact checked.1
    | succ i => exact ih _ checked.2 i (Nat.lt_of_succ_lt_succ hi)

/-- The bit within each byte stays fixed while the byte order reverses. -/
def reverseByteIndex (bits i : Nat) : Nat :=
  8 * (bits / 8 - 1 - i / 8) + i % 8

/-- Reversal discards bits above the selected width. -/
def ByteReversal (bits : Nat) (input output : BitVec 64) : Prop :=
  ∀ i, i < 64 → output.getLsbD i =
    if i < bits then input.getLsbD (reverseByteIndex bits i) else false

def swap8 (x : BitVec 64) : BitVec 64 := x &&& 0xff

def swap16 (x : BitVec 64) : BitVec 64 :=
  let v := x &&& 0xffff
  ((v &&& 0x00ff) <<< (8 : Nat)) ||| ((v &&& 0xff00) >>> (8 : Nat))

def swap32 (x : BitVec 64) : BitVec 64 :=
  let v := x &&& 0xffff_ffff
  ((v &&& 0x0000_00ff) <<< (24 : Nat)) |||
  ((v &&& 0x0000_ff00) <<< (8 : Nat)) |||
  ((v &&& 0x00ff_0000) >>> (8 : Nat)) |||
  ((v &&& 0xff00_0000) >>> (24 : Nat))

def swap64 (x : BitVec 64) : BitVec 64 :=
  ((x &&& 0x0000_0000_0000_00ff) <<< (56 : Nat)) |||
  ((x &&& 0x0000_0000_0000_ff00) <<< (40 : Nat)) |||
  ((x &&& 0x0000_0000_00ff_0000) <<< (24 : Nat)) |||
  ((x &&& 0x0000_0000_ff00_0000) <<< (8 : Nat)) |||
  ((x &&& 0x0000_00ff_0000_0000) >>> (8 : Nat)) |||
  ((x &&& 0x0000_ff00_0000_0000) >>> (24 : Nat)) |||
  ((x &&& 0x00ff_0000_0000_0000) >>> (40 : Nat)) |||
  ((x &&& 0xff00_0000_0000_0000) >>> (56 : Nat))

theorem swap8_exact (x : BitVec 64) : ByteReversal 8 x (swap8 x) := by
  unfold ByteReversal
  apply checkRange_sound 64
  simp [CheckRange, swap8, reverseByteIndex]

theorem swap16_exact (x : BitVec 64) : ByteReversal 16 x (swap16 x) := by
  unfold ByteReversal
  apply checkRange_sound 64
  simp [CheckRange, swap16, reverseByteIndex]

theorem swap32_exact (x : BitVec 64) : ByteReversal 32 x (swap32 x) := by
  unfold ByteReversal
  apply checkRange_sound 64
  simp [CheckRange, swap32, reverseByteIndex]

theorem swap64_exact (x : BitVec 64) : ByteReversal 64 x (swap64 x) := by
  unfold ByteReversal
  apply checkRange_sound 64
  simp [CheckRange, swap64, reverseByteIndex]

theorem swap8_bits (x : BitVec 64) (i : Nat) :
    (swap8 x).getLsbD i =
      if i < 8 then x.getLsbD (reverseByteIndex 8 i) else false :=
  if hi : i < 64 then swap8_exact x i hi else
    have hb : ¬ i < 8 := fun h => hi (Nat.lt_of_lt_of_le h (by decide))
    by simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi), hb]

theorem swap16_bits (x : BitVec 64) (i : Nat) :
    (swap16 x).getLsbD i =
      if i < 16 then x.getLsbD (reverseByteIndex 16 i) else false :=
  if hi : i < 64 then swap16_exact x i hi else
    have hb : ¬ i < 16 := fun h => hi (Nat.lt_of_lt_of_le h (by decide))
    by simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi), hb]

theorem swap32_bits (x : BitVec 64) (i : Nat) :
    (swap32 x).getLsbD i =
      if i < 32 then x.getLsbD (reverseByteIndex 32 i) else false :=
  if hi : i < 64 then swap32_exact x i hi else
    have hb : ¬ i < 32 := fun h => hi (Nat.lt_of_lt_of_le h (by decide))
    by simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi), hb]

theorem swap64_bits (x : BitVec 64) (i : Nat) :
    (swap64 x).getLsbD i =
      if i < 64 then x.getLsbD (reverseByteIndex 64 i) else false :=
  if hi : i < 64 then swap64_exact x i hi else
    have hb : ¬ i < 64 := fun h => hi (Nat.lt_of_lt_of_le h (by decide))
    by simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi), hb]

theorem swap8_involutive (x : BitVec 64) :
    swap8 (swap8 x) = x &&& 0xff := by
  apply BitVec.eq_of_getLsbD_eq
  apply checkRange_sound 64
  simp only [CheckRange, swap8_bits]
  simp [reverseByteIndex]

theorem swap16_involutive (x : BitVec 64) :
    swap16 (swap16 x) = x &&& 0xffff := by
  apply BitVec.eq_of_getLsbD_eq
  apply checkRange_sound 64
  simp only [CheckRange, swap16_bits]
  simp [reverseByteIndex]

theorem swap32_involutive (x : BitVec 64) :
    swap32 (swap32 x) = x &&& 0xffff_ffff := by
  apply BitVec.eq_of_getLsbD_eq
  apply checkRange_sound 64
  simp only [CheckRange, swap32_bits]
  simp [reverseByteIndex]

theorem swap64_involutive (x : BitVec 64) :
    swap64 (swap64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  apply checkRange_sound 64
  simp only [CheckRange, swap64_bits]
  simp [reverseByteIndex]

theorem maskedIdentity16_rejected :
    ¬ ByteReversal 16 (1#64) ((1#64) &&& 0xffff) := by
  intro h
  have bit := h 0 (by decide)
  simp [reverseByteIndex] at bit

theorem constantZero16_rejected :
    ¬ ByteReversal 16 (1#64) (0#64) := by
  intro h
  have bit := h 8 (by decide)
  simp [reverseByteIndex] at bit

end Endianness
