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
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with
    | inl h => subst h; exact checked.1
    | inr h => exact ih checked.2 i h

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

theorem swap8_exact (x : BitVec 64) : ByteReversal 8 x (swap8 x) := by
  intro i hi
  simp only [swap8, BitVec.getLsbD_and]
  revert i hi
  apply checkRange_sound 64
  simp only [CheckRange, reverseByteIndex, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge,
    BitVec.reduceGetElem, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.zero_lt_succ,
    Bool.and_true, Bool.and_false, ↓reduceIte, eq_self, and_self]

theorem swap16_exact (x : BitVec 64) : ByteReversal 16 x (swap16 x) := by
  intro i hi
  simp only [swap16, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  revert i hi
  apply checkRange_sound 64
  simp only [CheckRange, reverseByteIndex, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge,
    BitVec.reduceGetElem, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.zero_lt_succ, Nat.sub_eq_zero_of_le,
    decide_true, decide_false, Bool.not_true, Bool.not_false,
    Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
    Bool.or_false, Bool.false_or, ↓reduceIte, eq_self, and_self]

theorem swap32_exact (x : BitVec 64) : ByteReversal 32 x (swap32 x) := by
  intro i hi
  simp only [swap32, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  revert i hi
  apply checkRange_sound 64
  simp only [CheckRange, reverseByteIndex, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge,
    BitVec.reduceGetElem, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.zero_lt_succ, Nat.sub_eq_zero_of_le,
    decide_true, decide_false, Bool.not_true, Bool.not_false,
    Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
    Bool.or_false, Bool.false_or, ↓reduceIte, eq_self, and_self]

theorem swap64_exact (x : BitVec 64) : ByteReversal 64 x (swap64 x) := by
  intro i hi
  simp only [swap64, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, ↓reduceIte]
  revert i hi
  apply checkRange_sound 64
  simp only [CheckRange, reverseByteIndex, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge,
    BitVec.reduceGetElem, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.zero_lt_succ, Nat.sub_eq_zero_of_le,
    decide_true, decide_false, Bool.not_true, Bool.not_false,
    Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
    Bool.or_false, Bool.false_or, ↓reduceIte, eq_self, and_self]

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
  intro i hi
  simp only [swap8_bits, BitVec.getLsbD_and]
  revert i hi
  apply checkRange_sound 64
  simp only [CheckRange, reverseByteIndex, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge,
    BitVec.reduceGetElem, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.zero_lt_succ,
    Bool.and_true, Bool.and_false, ↓reduceIte, eq_self, and_self]

theorem swap16_involutive (x : BitVec 64) :
    swap16 (swap16 x) = x &&& 0xffff := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [swap16_bits, BitVec.getLsbD_and]
  revert i hi
  apply checkRange_sound 64
  simp only [CheckRange, reverseByteIndex, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge,
    BitVec.reduceGetElem, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.zero_lt_succ,
    Bool.and_true, Bool.and_false, ↓reduceIte, eq_self, and_self]

theorem swap32_involutive (x : BitVec 64) :
    swap32 (swap32 x) = x &&& 0xffff_ffff := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [swap32_bits, BitVec.getLsbD_and]
  revert i hi
  apply checkRange_sound 64
  simp only [CheckRange, reverseByteIndex, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge,
    BitVec.reduceGetElem, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.zero_lt_succ,
    Bool.and_true, Bool.and_false, ↓reduceIte, eq_self, and_self]

theorem swap64_involutive (x : BitVec 64) :
    swap64 (swap64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [swap64_bits, hi, ↓reduceIte]
  revert i hi
  apply checkRange_sound 64
  simp only [CheckRange, reverseByteIndex, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.zero_lt_succ, ↓reduceIte, eq_self, and_self]

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
