/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust.Bytes

open Rust.Bytes

-- Zero-width encoding discards the input; empty sequences decode to zero.
example : encodeLE 0 65535 = [] := by decide
example : encodeBE 0 65535 = [] := by decide
example : decodeLE [] = 0 := by decide
example : decodeBE [] = 0 := by decide

-- Explicit byte order for the pilot integer widths.
example : encodeLE 2 0x1234 = [0x34#8, 0x12#8] := by decide
example : encodeBE 2 0x1234 = [0x12#8, 0x34#8] := by decide
example : encodeLE 4 0x12345678 = [0x78#8, 0x56#8, 0x34#8, 0x12#8] := by decide
example : encodeBE 4 0x12345678 = [0x12#8, 0x34#8, 0x56#8, 0x78#8] := by decide
example : decodeLE [0x34#8, 0x12#8] = 0x1234 := by decide
example : decodeBE [0x12#8, 0x34#8] = 0x1234 := by decide

-- Width boundaries, truncation, and significant leading zero bytes.
example : encodeLE 2 65535 = [255#8, 255#8] := by decide
example : encodeLE 2 65536 = [0#8, 0#8] := by decide
example : encodeBE 4 4294967296 = [0#8, 0#8, 0#8, 0#8] := by decide
example : encodeLE 4 1 = [1#8, 0#8, 0#8, 0#8] := by decide
example : encodeBE 4 1 = [0#8, 0#8, 0#8, 1#8] := by decide

-- Universal laws are also usable without unfolding the definitions.
example (count n : Nat) : decodeLE (encodeLE count n) = n % 256 ^ count :=
  decodeLE_encodeLE count n
example (count n : Nat) (h : n < 256 ^ count) :
    decodeBE (encodeBE count n) = n := decodeBE_encodeBE_of_lt count n h
example (bytes : List Byte) : encodeBE bytes.length (decodeBE bytes) = bytes :=
  encodeBE_decodeBE bytes

example (count : Nat) : 256 ^ count = 2 ^ (8 * count) := radix_pow_eq_two_pow count

#print axioms radix_pow_eq_two_pow
#print axioms byte_lt_256
#print axioms decodeLE_lt
#print axioms decodeBE_lt
#print axioms decodeLE_encodeLE
#print axioms decodeBE_encodeBE
#print axioms encodeLE_decodeLE
#print axioms encodeBE_decodeBE
