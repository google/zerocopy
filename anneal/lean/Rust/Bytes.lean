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
This module specifies integer byte order with base-256 arithmetic. A byte is an
unsigned eight-bit digit; a sequence is a `List`, whose order describes byte
positions rather than a particular memory allocation or host endianness.

Encoding always produces the requested number of bytes. If the natural-number
input is too large, it keeps the low bits; if it is small, it supplies zero bytes
to fill the width. The two round-trip directions therefore have different
claims: decoding an encoding truncates the integer to that width, whereas
encoding a decoded sequence at its original length recovers every byte.

These definitions and proofs do not depend on machine integer types or Aeneas.
A consumer must separately show that its Rust operations implement this byte
order, with the intended width and memory-access conditions.
-/

namespace Rust.Bytes

/-- An unsigned eight-bit digit; `BitVec` already guarantees its value is below 256. -/
abbrev Byte := BitVec 8

/--
Reads little-endian digits: the head contributes units and the remainder is
multiplied by 256. For example, bytes `[0x34, 0x12]` represent `0x1234`.
-/
def decodeLE : List Byte → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeLE rest

/--
Reads big-endian digits by reversing their positions before little-endian
decoding. Both byte orders can then share the same arithmetic proofs.
-/
def decodeBE (bytes : List Byte) : Nat := decodeLE bytes.reverse

/--
Writes exactly `count` little-endian bytes, keeping the low `8 * count` bits of
`n`. Each step writes the current low byte and divides by 256 for the next step.
The output width, rather than the input value, controls when recursion stops.
-/
def encodeLE : (count : Nat) → Nat → List Byte
  | 0, _ => []
  | count + 1, n => BitVec.ofNat 8 n :: encodeLE count (n / 256)

/-- Writes the same fixed-width digits as `encodeLE`, in big-endian order. -/
def encodeBE (count n : Nat) : List Byte := (encodeLE count n).reverse

-- Register the recursive equations as simplification rules. `rfl` checks that
-- each equation is exactly the corresponding definition; the later theorems
-- provide the length, bounds, and inverse laws consumers normally need.
@[simp] theorem decodeLE_nil : decodeLE [] = 0 := rfl

@[simp] theorem decodeLE_cons (byte : Byte) (rest : List Byte) :
    decodeLE (byte :: rest) = byte.toNat + 256 * decodeLE rest := rfl

@[simp] theorem encodeLE_zero (n : Nat) : encodeLE 0 n = [] := rfl

@[simp] theorem encodeLE_succ (count n : Nat) :
    encodeLE (count + 1) n = BitVec.ofNat 8 n :: encodeLE count (n / 256) := rfl

/-- Exposes the digit bound as natural-number arithmetic for the proofs below. -/
theorem byte_lt_256 (byte : Byte) : byte.toNat < 256 := byte.isLt

/-- The encoder preserves its requested width, including zero and leading zero bytes. -/
@[simp] theorem length_encodeLE (count n : Nat) : (encodeLE count n).length = count := by
  -- The recursive input is `n / 256`, so the induction hypothesis must work
  -- for every input value, not just the original `n`.
  induction count generalizing n with
  | zero => rfl
  | succ count ih => simp [ih]

/-- Reversing the digits changes byte order without changing the encoded width. -/
@[simp] theorem length_encodeBE (count n : Nat) : (encodeBE count n).length = count := by
  simp [encodeBE]

/--
Converts the base-256 bound for `count` bytes to the bit-width bound used by
`BitVec`. This lets consumers connect these laws to fixed-width integer carriers.
-/
theorem radix_pow_eq_two_pow (count : Nat) : 256 ^ count = 2 ^ (8 * count) := by
  rw [Nat.pow_mul]

/-- A sequence of `count` bytes always fits in an unsigned `8 * count`-bit integer. -/
theorem decodeLE_lt (bytes : List Byte) : decodeLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp
  | cons byte rest ih =>
    -- The low digit is below 256 and the remaining digits fit their shorter
    -- width. After exposing one recursive step, `omega` combines these bounds.
    have hb := byte_lt_256 byte
    simp only [decodeLE_cons, List.length_cons, Nat.pow_succ]
    omega

/-- The representable bound depends on width, not on the order of the digits. -/
theorem decodeBE_lt (bytes : List Byte) : decodeBE bytes < 256 ^ bytes.length := by
  simpa [decodeBE] using decodeLE_lt bytes.reverse

/--
Writing and then reading keeps exactly the representable low bits. This law
holds even when `n` does not fit: overflow means truncation, not decoder failure.
-/
@[simp] theorem decodeLE_encodeLE (count n : Nat) :
    decodeLE (encodeLE count n) = n % 256 ^ count := by
  induction count generalizing n with
  | zero => simp [Nat.mod_one]
  | succ count ih =>
    -- Split the integer into its low digit and quotient. The induction
    -- hypothesis truncates the quotient; `Nat.mod_mul` combines the two pieces
    -- into reduction modulo the capacity of the complete byte sequence.
    simp only [encodeLE_succ, decodeLE_cons, BitVec.toNat_ofNat, ih]
    change n % 256 + 256 * (n / 256 % 256 ^ count) = n % 256 ^ (count + 1)
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ count) 256, Nat.mod_mul]

/-- Big-endian writing has the same truncation behavior as little-endian writing. -/
@[simp] theorem decodeBE_encodeBE (count n : Nat) :
    decodeBE (encodeBE count n) = n % 256 ^ count := by
  simp [decodeBE, encodeBE]

/--
Writing a sequence's decoded value at its original length recovers every byte.
The width matters: it retains leading zeros that the numerical value alone
cannot distinguish. No input-size premise is needed, since each digit fits.
-/
@[simp] theorem encodeLE_decodeLE (bytes : List Byte) :
    encodeLE bytes.length (decodeLE bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have hb := byte_lt_256 byte
    -- Modulo 256 recovers the head byte; division by 256 recovers the decoded
    -- tail. The digit bound rules out a carry from the head into that tail.
    have low : BitVec.ofNat 8 (byte.toNat + 256 * decodeLE rest) = byte := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      change (byte.toNat + 256 * decodeLE rest) % 256 = byte.toNat
      simp [Nat.mod_eq_of_lt hb]
    have high : (byte.toNat + 256 * decodeLE rest) / 256 = decodeLE rest := by
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb, Nat.zero_add]
    simp only [List.length_cons, decodeLE_cons, encodeLE_succ, low, high, ih]

/-- Reversing both sides transfers exact byte recovery to big-endian sequences. -/
@[simp] theorem encodeBE_decodeBE (bytes : List Byte) :
    encodeBE bytes.length (decodeBE bytes) = bytes := by
  have h := encodeLE_decodeLE bytes.reverse
  simpa [encodeBE, decodeBE] using congrArg List.reverse h

/--
An integer that already fits is recovered exactly. This is the specialization
used when a Rust input type guarantees the requested unsigned width.
-/
theorem decodeLE_encodeLE_of_lt (count n : Nat) (h : n < 256 ^ count) :
    decodeLE (encodeLE count n) = n := by
  rw [decodeLE_encodeLE, Nat.mod_eq_of_lt h]

/-- A representable input is also recovered exactly with big-endian encoding. -/
theorem decodeBE_encodeBE_of_lt (count n : Nat) (h : n < 256 ^ count) :
    decodeBE (encodeBE count n) = n := by
  rw [decodeBE_encodeBE, Nat.mod_eq_of_lt h]

end Rust.Bytes
