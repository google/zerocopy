/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Std.Tactic
@[expose] public section

/-!
Integer byte sequences, independently of any machine word width or backend.
These definitions specify numerical byte order. Connecting them to Rust methods
requires separate evidence about those methods and their translation.
-/

namespace Rust.Bytes

/-- An unsigned eight-bit digit. -/
abbrev Byte := BitVec 8

/-- Reads a byte sequence with its least significant byte first. -/
def decodeLE : List Byte → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeLE rest

/-- Reads a byte sequence with its most significant byte first. -/
def decodeBE (bytes : List Byte) : Nat := decodeLE bytes.reverse

/-- Writes exactly `count` bytes, keeping the low `8 * count` bits of `n`. -/
def encodeLE : (count : Nat) → Nat → List Byte
  | 0, _ => []
  | count + 1, n => BitVec.ofNat 8 n :: encodeLE count (n / 256)

/-- Writes exactly `count` bytes with the most significant byte first. -/
def encodeBE (count n : Nat) : List Byte := (encodeLE count n).reverse

@[simp] theorem decodeLE_nil : decodeLE [] = 0 := rfl

@[simp] theorem decodeLE_cons (byte : Byte) (rest : List Byte) :
    decodeLE (byte :: rest) = byte.toNat + 256 * decodeLE rest := rfl

@[simp] theorem encodeLE_zero (n : Nat) : encodeLE 0 n = [] := rfl

@[simp] theorem encodeLE_succ (count n : Nat) :
    encodeLE (count + 1) n = BitVec.ofNat 8 n :: encodeLE count (n / 256) := rfl

theorem byte_lt_256 (byte : Byte) : byte.toNat < 256 := byte.isLt

@[simp] theorem length_encodeLE (count n : Nat) : (encodeLE count n).length = count := by
  induction count generalizing n with
  | zero => rfl
  | succ count ih => simp [ih]

@[simp] theorem length_encodeBE (count n : Nat) : (encodeBE count n).length = count := by
  simp [encodeBE]

/-- Expresses the byte-width bound in the bit-width form used by `BitVec`. -/
theorem radix_pow_eq_two_pow (count : Nat) : 256 ^ count = 2 ^ (8 * count) := by
  rw [Nat.pow_mul]

/-- A sequence of `count` bytes always fits in an unsigned `8 * count`-bit integer. -/
theorem decodeLE_lt (bytes : List Byte) : decodeLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp
  | cons byte rest ih =>
    have hb := byte_lt_256 byte
    simp only [decodeLE_cons, List.length_cons, Nat.pow_succ]
    omega

theorem decodeBE_lt (bytes : List Byte) : decodeBE bytes < 256 ^ bytes.length := by
  simpa [decodeBE] using decodeLE_lt bytes.reverse

/-- Writing and then reading keeps precisely the representable low bits. -/
@[simp] theorem decodeLE_encodeLE (count n : Nat) :
    decodeLE (encodeLE count n) = n % 256 ^ count := by
  induction count generalizing n with
  | zero => simp [Nat.mod_one]
  | succ count ih =>
    simp only [encodeLE_succ, decodeLE_cons, BitVec.toNat_ofNat, ih]
    change n % 256 + 256 * (n / 256 % 256 ^ count) = n % 256 ^ (count + 1)
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ count) 256, Nat.mod_mul]

@[simp] theorem decodeBE_encodeBE (count n : Nat) :
    decodeBE (encodeBE count n) = n % 256 ^ count := by
  simp [decodeBE, encodeBE]

/-- Every byte sequence is recovered by writing its value at its original length. -/
@[simp] theorem encodeLE_decodeLE (bytes : List Byte) :
    encodeLE bytes.length (decodeLE bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have hb := byte_lt_256 byte
    have low : BitVec.ofNat 8 (byte.toNat + 256 * decodeLE rest) = byte := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      change (byte.toNat + 256 * decodeLE rest) % 256 = byte.toNat
      simp [Nat.mod_eq_of_lt hb]
    have high : (byte.toNat + 256 * decodeLE rest) / 256 = decodeLE rest := by
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb, Nat.zero_add]
    simp only [List.length_cons, decodeLE_cons, encodeLE_succ, low, high, ih]

@[simp] theorem encodeBE_decodeBE (bytes : List Byte) :
    encodeBE bytes.length (decodeBE bytes) = bytes := by
  have h := encodeLE_decodeLE bytes.reverse
  simpa [encodeBE, decodeBE] using congrArg List.reverse h

/-- No truncation occurs when the input already fits in the requested width. -/
theorem decodeLE_encodeLE_of_lt (count n : Nat) (h : n < 256 ^ count) :
    decodeLE (encodeLE count n) = n := by
  rw [decodeLE_encodeLE, Nat.mod_eq_of_lt h]

theorem decodeBE_encodeBE_of_lt (count n : Nat) (h : n < 256 ^ count) :
    decodeBE (encodeBE count n) = n := by
  rw [decodeBE_encodeBE, Nat.mod_eq_of_lt h]

end Rust.Bytes
