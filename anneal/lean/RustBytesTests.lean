/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust.Bytes

open Rust.Bytes

/-!
These examples pin down observable byte order, width, and truncation, then
exercise the universal laws as a consumer would. They do not extract a Rust
method or prove any memory access safe. Those connections belong to frontend
contracts; this package checks the mathematical byte operations alone.

In these examples, `0x34#8` is an eight-bit `BitVec` literal. `by decide` asks
Lean to compute the concrete proposition and check a proof of the result.
-/

-- Zero-width encoding discards the input; empty sequences decode to zero.
example : encodeLE 0 65535 = [] := by decide
example : encodeBE 0 65535 = [] := by decide
example : decodeLE [] = 0 := by decide
example : decodeBE [] = 0 := by decide

-- Distinct bytes make an accidental reversal visible. Both orders are checked
-- at the two widths used by the initial unsigned-integer consumers.
example : encodeLE 2 0x1234 = [0x34#8, 0x12#8] := by decide
example : encodeBE 2 0x1234 = [0x12#8, 0x34#8] := by decide
example : encodeLE 4 0x12345678 = [0x78#8, 0x56#8, 0x34#8, 0x12#8] := by decide
example : encodeBE 4 0x12345678 = [0x12#8, 0x34#8, 0x56#8, 0x78#8] := by decide
example : decodeLE [0x34#8, 0x12#8] = 0x1234 := by decide
example : decodeBE [0x12#8, 0x34#8] = 0x1234 := by decide

-- Check the largest two-byte integer and the first values that overflow two
-- and four bytes. The value one checks that encoding retains the full width,
-- placing its zero bytes at the end appropriate to each byte order.
example : encodeLE 2 65535 = [255#8, 255#8] := by decide
example : encodeLE 2 65536 = [0#8, 0#8] := by decide
example : encodeBE 4 4294967296 = [0#8, 0#8, 0#8, 0#8] := by decide
example : encodeLE 4 1 = [1#8, 0#8, 0#8, 0#8] := by decide
example : encodeBE 4 1 = [0#8, 0#8, 0#8, 1#8] := by decide

-- Use the general theorems directly, without unfolding or recomputing their
-- definitions. This checks their interfaces as well as the concrete examples.
example (count n : Nat) : decodeLE (encodeLE count n) = n % 256 ^ count :=
  decodeLE_encodeLE count n
example (count n : Nat) (h : n < 256 ^ count) :
    decodeBE (encodeBE count n) = n := decodeBE_encodeBE_of_lt count n h
example (bytes : List Byte) : encodeBE bytes.length (decodeBE bytes) = bytes :=
  encodeBE_decodeBE bytes

example (count : Nat) : 256 ^ count = 2 ^ (8 * count) := radix_pow_eq_two_pow count

-- Expose representative proof dependencies for inspection. `RustTests` audits
-- every declaration owned by `Rust.Bytes`, so these printed names are not the
-- enforced coverage boundary.
#print axioms radix_pow_eq_two_pow
#print axioms byte_lt_256
#print axioms decodeLE_lt
#print axioms decodeBE_lt
#print axioms decodeLE_encodeLE
#print axioms decodeBE_encodeBE
#print axioms encodeLE_decodeLE
#print axioms encodeBE_decodeBE
