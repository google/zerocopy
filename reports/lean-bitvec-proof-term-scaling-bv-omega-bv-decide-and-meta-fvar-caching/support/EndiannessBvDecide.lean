-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Std.Tactic.BVDecide

namespace Endianness

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

theorem swap8_involutive (x : BitVec 64) :
    swap8 (swap8 x) = x &&& 0xff := by
  unfold swap8
  bv_decide

theorem swap16_involutive (x : BitVec 64) :
    swap16 (swap16 x) = x &&& 0xffff := by
  unfold swap16
  bv_decide

theorem swap32_involutive (x : BitVec 64) :
    swap32 (swap32 x) = x &&& 0xffff_ffff := by
  unfold swap32
  bv_decide

theorem swap64_involutive (x : BitVec 64) :
    swap64 (swap64 x) = x := by
  unfold swap64
  bv_decide

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
