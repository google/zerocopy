-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteWf

/-!
# Negative Refutations for `Trusted.MirSemantics.Bytes` Validity Guards

Exercises every scalar-validity, constant-width, type-check, padding-uninit,
byte-length, uninitialized-byte, and `validUtf8Go` RFC 3629 UTF-8 state
machine guard in `Trusted/MirSemantics/Bytes.lean`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Guard `bytes_invalid_bool_value`: a 1-byte `bool` scalar whose value is
`2` (neither `0` nor `1`) faults with `.undefined`. -/
theorem refute_bytes_invalid_bool_value :
    ReachesResult (mkConstRetProg .bool 2) queryEmpty (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .bool 2) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_invalid_char_surrogate`: a `char` constant holding surrogate
code point `0xD800` faults with `.undefined` rather than passing through
`Char.ofNat`. -/
theorem refute_bytes_invalid_char_surrogate :
    ReachesResult (mkConstRetProg .char 0xd800) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .char 0xd800) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_invalid_ordering_tag`: a `core::cmp::Ordering` constant with
tag `2` (outside `{-1_i8, 0, 1}`) faults with `.undefined`. -/
theorem refute_bytes_invalid_ordering_tag :
    ReachesResult (mkConstRetProg .ordering 2) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .ordering 2) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_invalid_enum_tag`: a `ReprU8 { A = 10, B = 20 }` constant
with tag `1` faults with `.undefined`. -/
theorem refute_bytes_invalid_enum_tag :
    ReachesResult (mkConstRetProg (.enum reprU8EnumTy) 1) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg (.enum reprU8EnumTy) 1) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program `StorageLive(_1: u32); _0 = copy _1; return`, used to test indirect
uninitialized-byte reads after `forceAllocation`. -/
noncomputable def progIndirectUninitRead : Program :=
  mkSingleBlockProg 0 [u32Ty, u32Ty]
    [.storageLive 1, .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `bytes_uninit_memory_read`: reading uninitialized bytes from an
indirect stack allocation via `initBytes?` / `decodeVal` / `loadIndirect`
faults with `.undefined`. -/
theorem refute_bytes_uninit_memory_read :
    (match initState progIndirectUninitRead queryEmpty with
     | .ok s₀ =>
       match evalStep progIndirectUninitRead 0 s₀ with
       | .step s₁ =>
         match forceAllocation progIndirectUninitRead s₁ 1 with
         | .ok (s₂, _) =>
           evalStep progIndirectUninitRead 0 s₂ = .fault .undefined
         | .error _ => False
       | _ => False
     | .error _ => False) :=
  rfl

/-- Guard `bytes_const_int_width_overflow`: a `u8` constant whose raw bit
pattern `256` exceeds 8 bits faults with `.unsupported`. -/
theorem refute_bytes_const_int_width_overflow :
    ReachesResult (mkConstRetProg u8Ty 256) queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg u8Ty 256) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_const_bool_width_overflow`: a `bool` constant whose raw bit
pattern `257` exceeds 1 byte (even though its low byte is `1`) faults with
`.unsupported`. -/
theorem refute_bytes_const_bool_width_overflow :
    ReachesResult (mkConstRetProg .bool 257) queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg .bool 257) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_const_char_width_overflow` (lockstep fault classification):
a `char` constant whose raw bit pattern `2^32 + 65` exceeds 4 bytes faults
with `.unsupported` rather than `.undefined`. -/
theorem refute_bytes_const_char_width_overflow :
    ReachesResult (mkConstRetProg .char (Nat.pow 2 32 + 65)) queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg .char (Nat.pow 2 32 + 65)) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_const_ordering_width_overflow` (lockstep fault classification):
an `Ordering` constant whose raw bit pattern `256` exceeds 1 byte faults with
`.unsupported` rather than `.undefined`. -/
theorem refute_bytes_const_ordering_width_overflow :
    ReachesResult (mkConstRetProg .ordering 256) queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg .ordering 256) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program assigning a `ConstLit.zeroSized` literal to a scalar-tagged enum
local. -/
noncomputable def progZeroSizedScalarEnumConst : Program :=
  mkSingleBlockProg 0 [.enum reprU8EnumTy]
    [.assign ⟨0, []⟩ (.use (.constant ⟨.enum reprU8EnumTy, .zeroSized⟩))]

/-- Guard `bytes_const_zst_enum_requires_zst`: `ConstLit.zeroSized` at a
scalar-tagged enum faults with `.unsupported`. -/
theorem refute_bytes_const_zst_enum_requires_zst :
    ReachesResult progZeroSizedScalarEnumConst queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed progZeroSizedScalarEnumConst queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_const_scalar_enum_width_overflow`: a `ReprU8` constant whose
raw bit pattern `266` (`256 + 10`) exceeds its 1-byte tag width faults with
`.unsupported`. -/
theorem refute_bytes_const_scalar_enum_width_overflow :
    ReachesResult (mkConstRetProg (.enum reprU8EnumTy) 266) queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg (.enum reprU8EnumTy) 266) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_const_mismatched_lit_kind`: a `ConstLit.scalar` literal at
`.unit` faults with `.unsupported`. -/
theorem refute_bytes_const_mismatched_lit_kind :
    ReachesResult (mkConstRetProg .unit 0) queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg .unit 0) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_encode_val_checks_type`: `encodeVal` rejects a non-canonical
`u8` scalar (`bits = 256`) with `.unsupported`. -/
theorem refute_bytes_encode_val_checks_type :
    encodeVal .big u8Ty (u8Val 256) = .error .unsupported :=
  rfl

/-- Guard `bytes_encode_overflow_pair_padding_uninit`: `encodeVal` leaves the
tail padding bytes of an overflow pair `(u32, bool)` uninitialized rather than
zero-filled. -/
theorem refute_bytes_encode_overflow_pair_padding_uninit :
    encodeVal .big (.tuple [u32Ty, .bool]) (.tuple [u32Val 0, .bool false]) =
      .ok [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
           .init 0 none, .uninit, .uninit, .uninit] :=
  rfl

/-- Guard `bytes_decode_never_returns_uninit`: `decodeVal` for uninhabited
`.never` returns `.ok none` so no valid value can be materialized. -/
theorem refute_bytes_decode_never_returns_uninit :
    decodeVal .big .never [] = .ok none :=
  rfl

/-- Guard `bytes_decode_length_mismatch`: `decodeVal` rejects a byte slice
whose length disagrees with `layoutOfTy u32Ty` (`1 ≠ 4`) with `.unsupported`.
-/
theorem refute_bytes_decode_length_mismatch :
    decodeVal .big u32Ty [.init 0 none] = .error .unsupported :=
  rfl

/-- Guard `bytes_decode_overflow_pair_length_mismatch`: `decodeVal` rejects a
byte slice whose length disagrees with `overflowPairLayout .i32` (`5 ≠ 8`) with
`.unsupported`. -/
theorem refute_bytes_decode_overflow_pair_length_mismatch :
    decodeVal .big (.tuple [u32Ty, .bool]) (List.replicate 5 (.init 0 none)) =
      .error .unsupported :=
  rfl

/-- Guard `bytes_decode_overflow_pair_uninit_bool`: `decodeVal` returns
`.ok none` when the `bool` byte of a `(u32, bool)` overflow pair is `.uninit`.
-/
theorem refute_bytes_decode_overflow_pair_uninit_bool :
    decodeVal .big (.tuple [u32Ty, .bool])
      [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
       .uninit, .uninit, .uninit, .uninit] = .ok none :=
  rfl

/-- Single-variant zero-sized enum (`tagRepr := .zeroSized`). -/
noncomputable def zstScalarLitEnumTy : EnumTy := {
  id := 77
  discrWidth := .i8
  discrSigned := false
  tagRepr := .zeroSized
  discriminants := [0]
}

/-- Program assigning a `ConstLit.scalar` literal to a `.zeroSized` enum
local. -/
noncomputable def progScalarLitOnZstEnum : Program :=
  mkSingleBlockProg 0 [.enum zstScalarLitEnumTy]
    [.assign ⟨0, []⟩
      (.use (.constant ⟨.enum zstScalarLitEnumTy,
                        .scalar (BitVec.ofNat 128 5)⟩))]

/-- Guard `bytes_const_scalar_lit_on_zst_enum`: `evalConstLit` rejects a
`ConstLit.scalar` literal on a `.zeroSized` enum with `.unsupported`. -/
theorem refute_bytes_const_scalar_lit_on_zst_enum :
    ReachesResult progScalarLitOnZstEnum queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progScalarLitOnZstEnum queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_utf8_two_byte_lead_min`: an overlong two-byte encoding (lead
`0xC0` or `0xC1`) is rejected, while the shortest two-byte encodings `U+0080`
and `U+07FF` are accepted. -/
theorem refute_bytes_utf8_two_byte_lead_min :
    validUtf8Bytes [0xC1, 0xBF] = false ∧
    validUtf8Bytes [0xC2, 0x80] = true ∧
    validUtf8Bytes [0xDF, 0xBF] = true :=
  ⟨rfl, rfl, rfl⟩

/-- Guard `bytes_utf8_e0_overlong`: the overlong three-byte encoding of `U+07FF`
(`E0 9F BF`) is rejected, while `U+0800` (`E0 A0 80`) is accepted. -/
theorem refute_bytes_utf8_e0_overlong :
    validUtf8Bytes [0xE0, 0x9F, 0xBF] = false ∧
    validUtf8Bytes [0xE0, 0xA0, 0x80] = true :=
  ⟨rfl, rfl⟩

/-- Guard `bytes_utf8_ed_surrogate`: the UTF-16 surrogate `U+D800` (`ED A0 80`)
is rejected, while its neighbors `U+D7FF` (`ED 9F BF`) and `U+E000` (`EE 80 80`)
are accepted. -/
theorem refute_bytes_utf8_ed_surrogate :
    validUtf8Bytes [0xED, 0xA0, 0x80] = false ∧
    validUtf8Bytes [0xED, 0x9F, 0xBF] = true ∧
    validUtf8Bytes [0xEE, 0x80, 0x80] = true :=
  ⟨rfl, rfl, rfl⟩

/-- Guard `bytes_utf8_f0_overlong`: the overlong four-byte encoding of `U+FFFF`
(`F0 8F BF BF`) is rejected, while `U+10000` (`F0 90 80 80`) and `U+1F600`
(`F0 9F 98 80`) are accepted. -/
theorem refute_bytes_utf8_f0_overlong :
    validUtf8Bytes [0xF0, 0x8F, 0xBF, 0xBF] = false ∧
    validUtf8Bytes [0xF0, 0x90, 0x80, 0x80] = true ∧
    validUtf8Bytes [0xF0, 0x9F, 0x98, 0x80] = true :=
  ⟨rfl, rfl, rfl⟩

/-- Guard `bytes_utf8_f4_max`: `U+110000` (`F4 90 80 80`), one past the largest
code point, is rejected, while `U+10FFFF` (`F4 8F BF BF`) is accepted. -/
theorem refute_bytes_utf8_f4_max :
    validUtf8Bytes [0xF4, 0x90, 0x80, 0x80] = false ∧
    validUtf8Bytes [0xF4, 0x8F, 0xBF, 0xBF] = true :=
  ⟨rfl, rfl⟩

/-- Guard `bytes_utf8_invalid_lead`: a lone continuation byte (`80`) and the
never-valid leads `F5` and `FF` are rejected. -/
theorem refute_bytes_utf8_invalid_lead :
    validUtf8Bytes [0x80] = false ∧
    validUtf8Bytes [0xF5, 0x80, 0x80, 0x80] = false ∧
    validUtf8Bytes [0xFF] = false :=
  ⟨rfl, rfl, rfl⟩

/-- Guard `bytes_utf8_truncated`: a three-byte sequence cut short (`E2 82`) is
rejected, while the complete `U+20AC` (`E2 82 AC`) is accepted. -/
theorem refute_bytes_utf8_truncated :
    validUtf8Bytes [0xE2, 0x82] = false ∧
    validUtf8Bytes [0xE2, 0x82, 0xAC] = true :=
  ⟨rfl, rfl⟩

/-- Guard `bytes_utf8_continuation_hi`: a continuation byte above `0xBF`
(`C2 C0`) is rejected. -/
theorem refute_bytes_utf8_continuation_hi :
    validUtf8Bytes [0xC2, 0xC0] = false ∧
    validUtf8Bytes [0xC2, 0xBF] = true :=
  ⟨rfl, rfl⟩

/-- Guard `bytes_utf8_continuation_lo`: an ASCII byte in a continuation position
(`C2 7F`) is rejected. -/
theorem refute_bytes_utf8_continuation_lo :
    validUtf8Bytes [0xC2, 0x7F] = false ∧
    validUtf8Bytes [0xC2, 0x80] = true :=
  ⟨rfl, rfl⟩

end GuardMutation
