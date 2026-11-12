-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.Lemmas
import Init.Omega

namespace Endianness

set_option maxRecDepth 2048

def CheckRange : Nat → (Nat → Prop) → Prop
  | 0, _ => True
  | n + 1, p => p n ∧ CheckRange n p

theorem checkRange_sound (n : Nat) (p : Nat → Prop)
    (checked : CheckRange n p) : ∀ i, i < n → p i := by
  induction n with
  | zero =>
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact ih checked.2 i hlt
    · exact checked.1

def reverseByteIndex (bits i : Nat) : Nat :=
  8 * (bits / 8 - 1 - i / 8) + i % 8

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

theorem getLsbD_and_mask (x m : BitVec 64) (i : Nat) :
    (x &&& m).getLsbD i = (bif m.getLsbD i then x.getLsbD i else false) := by
  rw [BitVec.getLsbD_and]
  cases m.getLsbD i <;> simp

theorem getLsbD_laneL_first (x m : BitVec 64) (s i : Nat) :
    ((x &&& m) <<< s).getLsbD i =
      (bif decide (i < 64) && !decide (i < s) && m.getLsbD (i - s) then
        x.getLsbD (i - s)
      else false) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  cases (decide (i < 64) && !decide (i < s)) <;> cases m.getLsbD (i - s) <;>
    cases x.getLsbD (i - s) <;> rfl

theorem getLsbD_or_laneL (rest : Bool) (x m : BitVec 64) (s i : Nat) :
    (rest || ((x &&& m) <<< s).getLsbD i) =
      (bif decide (i < 64) && !decide (i < s) && m.getLsbD (i - s) then
        (rest || x.getLsbD (i - s))
      else rest) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  cases (decide (i < 64) && !decide (i < s)) <;> cases m.getLsbD (i - s) <;>
    cases x.getLsbD (i - s) <;> cases rest <;> rfl

theorem getLsbD_or_laneR (rest : Bool) (x m : BitVec 64) (s i : Nat) :
    (rest || ((x &&& m) >>> s).getLsbD i) =
      (bif m.getLsbD (s + i) then
        (rest || x.getLsbD (s + i))
      else rest) := by
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and]
  cases m.getLsbD (s + i) <;> cases x.getLsbD (s + i) <;> cases rest <;> rfl

theorem swap8_exact (x : BitVec 64) : ByteReversal 8 x (swap8 x) := by
  intro i hi
  rw [swap8, getLsbD_and_mask]
  revert i hi
  apply checkRange_sound 64
  repeat' first | exact True.intro | refine ⟨Eq.symm rfl, ?_⟩

theorem swap16_exact (x : BitVec 64) : ByteReversal 16 x (swap16 x) := by
  intro i hi
  rw [swap16, BitVec.and_assoc, BitVec.and_assoc, BitVec.getLsbD_or,
    getLsbD_laneL_first, getLsbD_or_laneR]
  revert i hi
  apply checkRange_sound 64
  repeat' first | exact True.intro | refine ⟨Eq.symm rfl, ?_⟩

theorem swap32_exact (x : BitVec 64) : ByteReversal 32 x (swap32 x) := by
  intro i hi
  rw [swap32, BitVec.and_assoc, BitVec.and_assoc, BitVec.and_assoc, BitVec.and_assoc,
    BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    getLsbD_laneL_first, getLsbD_or_laneL, getLsbD_or_laneR, getLsbD_or_laneR]
  revert i hi
  apply checkRange_sound 64
  repeat' first | exact True.intro | refine ⟨Eq.symm rfl, ?_⟩

theorem swap64_exact (x : BitVec 64) : ByteReversal 64 x (swap64 x) := by
  intro i hi
  rw [swap64, BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    getLsbD_laneL_first, getLsbD_or_laneL, getLsbD_or_laneL, getLsbD_or_laneL,
    getLsbD_or_laneR, getLsbD_or_laneR, getLsbD_or_laneR, getLsbD_or_laneR]
  revert i hi
  apply checkRange_sound 64
  repeat' first | exact True.intro | refine ⟨Eq.symm rfl, ?_⟩

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

theorem reverseByteIndex_involutive (bits i : Nat) (hb : bits % 8 = 0) (hi : i < bits) :
    reverseByteIndex bits (reverseByteIndex bits i) = i ∧ reverseByteIndex bits i < bits := by
  unfold reverseByteIndex
  omega

theorem mask16_bits (i : Nat) (hi : i < 64) :
    (0xffff : BitVec 64).getLsbD i = decide (i < 16) := by
  revert i hi
  apply checkRange_sound 64
  repeat' first | exact True.intro | refine ⟨rfl, ?_⟩

theorem mask32_bits (i : Nat) (hi : i < 64) :
    (0xffff_ffff : BitVec 64).getLsbD i = decide (i < 32) := by
  revert i hi
  apply checkRange_sound 64
  repeat' first | exact True.intro | refine ⟨rfl, ?_⟩

theorem swap8_involutive (x : BitVec 64) :
    swap8 (swap8 x) = x &&& 0xff := by
  rw [swap8, swap8, BitVec.and_assoc, BitVec.and_self]

theorem swap16_involutive (x : BitVec 64) :
    swap16 (swap16 x) = x &&& 0xffff := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [swap16_bits, swap16_bits, BitVec.getLsbD_and, mask16_bits i hi]
  by_cases hlt : i < 16
  · have ⟨hinv, hbound⟩ := reverseByteIndex_involutive 16 i rfl hlt
    simp [hlt, hbound, hinv]
  · simp [hlt]

theorem swap32_involutive (x : BitVec 64) :
    swap32 (swap32 x) = x &&& 0xffff_ffff := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [swap32_bits, swap32_bits, BitVec.getLsbD_and, mask32_bits i hi]
  by_cases hlt : i < 32
  · have ⟨hinv, hbound⟩ := reverseByteIndex_involutive 32 i rfl hlt
    simp [hlt, hbound, hinv]
  · simp [hlt]

theorem swap64_involutive (x : BitVec 64) :
    swap64 (swap64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ⟨hinv, hbound⟩ := reverseByteIndex_involutive 64 i rfl hi
  rw [swap64_bits, swap64_bits]
  simp [hi, hbound, hinv]

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
