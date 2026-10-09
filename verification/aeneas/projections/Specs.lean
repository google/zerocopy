/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import SpecPrelude
public import SpecsSyntax
public import Models
public import TraitLaws
@[expose] public section

open Aeneas Aeneas.Std
open Zerocopy.Proofs
namespace Zerocopy.Specs

check_model_inputs Zerocopy.byteorder.verification.read_u16_le with 0 type parameters
aeneas_spec_begin
spec read_u16_le_spec
  for @Zerocopy.byteorder.verification.read_u16_le with 0 type parameters
  ensures n => (n : Nat) = Rust.Bytes.decodeLE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.read_u16_le_spec for Zerocopy.byteorder.verification.read_u16_le with 1

check_model_inputs Zerocopy.byteorder.verification.write_u16_le with 0 type parameters
aeneas_spec_begin
spec write_u16_le_spec
  for @Zerocopy.byteorder.verification.write_u16_le with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeLE 2 (n : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_u16_le_spec for Zerocopy.byteorder.verification.write_u16_le with 1

check_model_inputs Zerocopy.byteorder.verification.set_u16_le with 0 type parameters
aeneas_spec_begin
spec set_u16_le_spec
  for @Zerocopy.byteorder.verification.set_u16_le with 0 type parameters
  ensures r => r = n
aeneas_spec_end
check_spec_binding Zerocopy.Specs.set_u16_le_spec for Zerocopy.byteorder.verification.set_u16_le with 2

check_model_inputs Zerocopy.byteorder.verification.read_u16_be with 0 type parameters
aeneas_spec_begin
spec read_u16_be_spec
  for @Zerocopy.byteorder.verification.read_u16_be with 0 type parameters
  ensures n => (n : Nat) = Rust.Bytes.decodeBE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.read_u16_be_spec for Zerocopy.byteorder.verification.read_u16_be with 1

check_model_inputs Zerocopy.byteorder.verification.write_u16_be with 0 type parameters
aeneas_spec_begin
spec write_u16_be_spec
  for @Zerocopy.byteorder.verification.write_u16_be with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeBE 2 (n : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_u16_be_spec for Zerocopy.byteorder.verification.write_u16_be with 1

check_model_inputs Zerocopy.byteorder.verification.set_u16_be with 0 type parameters
aeneas_spec_begin
spec set_u16_be_spec
  for @Zerocopy.byteorder.verification.set_u16_be with 0 type parameters
  ensures r => r = n
aeneas_spec_end
check_spec_binding Zerocopy.Specs.set_u16_be_spec for Zerocopy.byteorder.verification.set_u16_be with 2

check_model_inputs Zerocopy.byteorder.verification.read_u32_le with 0 type parameters
aeneas_spec_begin
spec read_u32_le_spec
  for @Zerocopy.byteorder.verification.read_u32_le with 0 type parameters
  ensures n => (n : Nat) = Rust.Bytes.decodeLE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.read_u32_le_spec for Zerocopy.byteorder.verification.read_u32_le with 1

check_model_inputs Zerocopy.byteorder.verification.write_u32_le with 0 type parameters
aeneas_spec_begin
spec write_u32_le_spec
  for @Zerocopy.byteorder.verification.write_u32_le with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeLE 4 (n : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_u32_le_spec for Zerocopy.byteorder.verification.write_u32_le with 1

check_model_inputs Zerocopy.byteorder.verification.set_u32_le with 0 type parameters
aeneas_spec_begin
spec set_u32_le_spec
  for @Zerocopy.byteorder.verification.set_u32_le with 0 type parameters
  ensures r => r = n
aeneas_spec_end
check_spec_binding Zerocopy.Specs.set_u32_le_spec for Zerocopy.byteorder.verification.set_u32_le with 2

check_model_inputs Zerocopy.byteorder.verification.read_u32_be with 0 type parameters
aeneas_spec_begin
spec read_u32_be_spec
  for @Zerocopy.byteorder.verification.read_u32_be with 0 type parameters
  ensures n => (n : Nat) = Rust.Bytes.decodeBE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.read_u32_be_spec for Zerocopy.byteorder.verification.read_u32_be with 1

check_model_inputs Zerocopy.byteorder.verification.write_u32_be with 0 type parameters
aeneas_spec_begin
spec write_u32_be_spec
  for @Zerocopy.byteorder.verification.write_u32_be with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeBE 4 (n : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_u32_be_spec for Zerocopy.byteorder.verification.write_u32_be with 1

check_model_inputs Zerocopy.byteorder.verification.set_u32_be with 0 type parameters
aeneas_spec_begin
spec set_u32_be_spec
  for @Zerocopy.byteorder.verification.set_u32_be with 0 type parameters
  ensures r => r = n
aeneas_spec_end
check_spec_binding Zerocopy.Specs.set_u32_be_spec for Zerocopy.byteorder.verification.set_u32_be with 2

check_model_inputs Zerocopy.trait_checks.byte_codec_roundtrip with 1 type parameters
aeneas_spec_begin
spec byte_codec_roundtrip_spec
  for @Zerocopy.trait_checks.byte_codec_roundtrip with 1 type parameters
  ensures result => result = byte
aeneas_spec_end
check_spec_binding Zerocopy.Specs.byte_codec_roundtrip_spec for Zerocopy.trait_checks.byte_codec_roundtrip with 3

check_model_inputs Zerocopy.trait_checks.forwarded_byte_codec with 0 type parameters
aeneas_spec_begin
spec forwarded_byte_codec_spec
  for @Zerocopy.trait_checks.forwarded_byte_codec with 0 type parameters
  ensures result => result = byte
aeneas_spec_end
check_spec_binding Zerocopy.Specs.forwarded_byte_codec_spec for Zerocopy.trait_checks.forwarded_byte_codec with 1

check_model_inputs Zerocopy.trait_checks.check_array_into_bytes with 0 type parameters
aeneas_spec_begin
spec array_into_bytes_spec
  for @Zerocopy.trait_checks.check_array_into_bytes with 0 type parameters
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Bool 3#usize)
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array U8 3#usize)
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Unit 4#usize)
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Bool 0#usize)
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation
    (Aeneas.Std.Array (Aeneas.Std.Array Bool 2#usize) 3#usize)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.array_into_bytes_spec for Zerocopy.trait_checks.check_array_into_bytes with 0

check_model_inputs Zerocopy.util.bytewrite.exact with 0 type parameters
aeneas_spec_begin
spec write_exact_spec
  for @Zerocopy.util.bytewrite.exact with 0 type parameters
  ensures(raw) out => out.1 = decide (src.val.length = dst.val.length) ∧
    out.2.val = if src.val.length = dst.val.length then src.val else dst.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_exact_spec for Zerocopy.util.bytewrite.exact with 2

check_model_inputs Zerocopy.util.bytewrite.prefix with 0 type parameters
aeneas_spec_begin
spec write_prefix_spec
  for @Zerocopy.util.bytewrite.prefix with 0 type parameters
  ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then src.val ++ dst.val.drop src.val.length else dst.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_prefix_spec for Zerocopy.util.bytewrite.prefix with 2

check_model_inputs Zerocopy.util.bytewrite.suffix with 0 type parameters
aeneas_spec_begin
spec write_suffix_spec
  for @Zerocopy.util.bytewrite.suffix with 0 type parameters
  ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then dst.val.take (dst.val.length - src.val.length) ++ src.val else dst.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_suffix_spec for Zerocopy.util.bytewrite.suffix with 2

check_model_inputs Zerocopy.util.bytewrite.be_word_prefix with 0 type parameters
aeneas_spec_begin
spec write_be_word_prefix_spec
  for @Zerocopy.util.bytewrite.be_word_prefix with 0 type parameters
  ensures(raw) out => out.1 = decide (2 ≤ dst.val.length) ∧
    out.2.val.map (fun byte => byte.bv) = if 2 ≤ dst.val.length
      then Rust.Bytes.encodeBE 2 n.val ++ (dst.val.drop 2).map (fun byte => byte.bv)
      else dst.val.map (fun byte => byte.bv)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_be_word_prefix_spec for Zerocopy.util.bytewrite.be_word_prefix with 2

check_model_inputs Zerocopy.util.padding_needed_for with 0 type parameters
aeneas_spec_begin
spec padding_lt_alignment
  for @Zerocopy.util.padding_needed_for with 0 type parameters
  ensures p => (p : Nat) < (align : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.padding_lt_alignment for Zerocopy.util.padding_needed_for with 2

check_model_inputs Zerocopy.util.round_down_to_next_multiple_of_alignment with 0 type parameters
aeneas_spec_begin
spec round_down_spec
  for @Zerocopy.util.round_down_to_next_multiple_of_alignment with 0 type parameters
  requires h : (align : Nat).isPowerOfTwo
  ensures m => (m : Nat) ≤ (n : Nat) ∧ (m : Nat) % (align : Nat) = 0
aeneas_spec_end
check_spec_binding Zerocopy.Specs.round_down_spec for Zerocopy.util.round_down_to_next_multiple_of_alignment with 2

check_model_inputs Zerocopy.util.max with 0 type parameters
aeneas_spec_begin
spec max_spec
  for @Zerocopy.util.max with 0 type parameters
  ensures r => (r : Nat) = Nat.max (a : Nat) (b : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.max_spec for Zerocopy.util.max with 2

check_model_inputs Zerocopy.util.min with 0 type parameters
aeneas_spec_begin
spec min_spec
  for @Zerocopy.util.min with 0 type parameters
  ensures r => (r : Nat) = Nat.min (a : Nat) (b : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.min_spec for Zerocopy.util.min with 2

check_model_inputs Zerocopy.util.owned_transmute.to_bytes with 0 type parameters
aeneas_spec_begin
spec owned_transmute_to_bytes_spec
  for @Zerocopy.util.owned_transmute.to_bytes with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeLE 4 (value : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.owned_transmute_to_bytes_spec for Zerocopy.util.owned_transmute.to_bytes with 1

check_model_inputs Zerocopy.util.owned_transmute.from_bytes with 0 type parameters
aeneas_spec_begin
spec owned_transmute_from_bytes_spec
  for @Zerocopy.util.owned_transmute.from_bytes with 0 type parameters
  ensures value => (value : Nat) = Rust.Bytes.decodeLE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.owned_transmute_from_bytes_spec for Zerocopy.util.owned_transmute.from_bytes with 1

check_model_inputs Zerocopy.util.owned_transmute.checked_bool with 0 type parameters
aeneas_spec_begin
spec owned_transmute_bool_spec
  for @Zerocopy.util.owned_transmute.checked_bool with 0 type parameters
  ensures output => match output with
    | none => 2 ≤ (byte : Nat)
    | some value => (byte : Nat) < 2 ∧ value = decide ((byte : Nat) = 1)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.owned_transmute_bool_spec for Zerocopy.util.owned_transmute.checked_bool with 1

check_model_inputs Zerocopy.util.owned_transmute.round_trip_checks with 0 type parameters
aeneas_spec_begin
spec owned_transmute_round_trip_checks_spec
  for @Zerocopy.util.owned_transmute.round_trip_checks with 0 type parameters
  ensures _ => True
aeneas_spec_end
check_spec_binding Zerocopy.Specs.owned_transmute_round_trip_checks_spec for Zerocopy.util.owned_transmute.round_trip_checks with 1

check_model_inputs Zerocopy.util.safety_checks.checked_bool with 0 type parameters
aeneas_spec_begin
spec checked_bool_spec
  for @Zerocopy.util.safety_checks.checked_bool with 0 type parameters
  ensures(raw) r => r = if byte.val < 2 then some (decide (byte.val = 1)) else none
aeneas_spec_end
check_spec_binding Zerocopy.Specs.checked_bool_spec for Zerocopy.util.safety_checks.checked_bool with 1

check_model_inputs Zerocopy.util.safety_checks.checked_copy with 0 type parameters
aeneas_spec_begin
spec checked_copy_spec
  for @Zerocopy.util.safety_checks.checked_copy with 0 type parameters
  ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then src.val ++ dst.val.drop src.val.length else dst.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.checked_copy_spec for Zerocopy.util.safety_checks.checked_copy with 2

check_model_inputs Zerocopy.util.safety_checks.checked_nonzero with 0 type parameters
aeneas_spec_begin
spec checked_nonzero_spec
  for @Zerocopy.util.safety_checks.checked_nonzero with 0 type parameters
  ensures(raw) r => match r with
    | none => n.val = 0
    | some value => value.val = n ∧ 0 < value.val.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.checked_nonzero_spec for Zerocopy.util.safety_checks.checked_nonzero with 1

check_model_inputs Zerocopy.util.safety_checks.checked_bool_pair with 0 type parameters
aeneas_spec_begin
spec checked_bool_pair_spec
  for @Zerocopy.util.safety_checks.checked_bool_pair with 0 type parameters
  ensures(raw) r => match r with
    | none => ∃ byte ∈ bytes.val, 2 ≤ byte.val
    | some values => values.val = bytes.val.map (fun byte => decide (byte.val = 1)) ∧
        ∀ byte ∈ bytes.val, byte.val < 2
aeneas_spec_end
check_spec_binding Zerocopy.Specs.checked_bool_pair_spec for Zerocopy.util.safety_checks.checked_bool_pair with 1

check_model_inputs Zerocopy.util.safety_checks.bool_slice_valid with 0 type parameters
aeneas_spec_begin
spec bool_slice_valid_spec
  for @Zerocopy.util.safety_checks.bool_slice_valid with 0 type parameters
  ensures(raw) r => r = decide (∀ byte ∈ bytes.val, byte.val < 2)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.bool_slice_valid_spec for Zerocopy.util.safety_checks.bool_slice_valid with 1

check_model_inputs Zerocopy.util.validity.bool_encoding with 0 type parameters
aeneas_spec_begin
spec bool_encoding_spec
  for @Zerocopy.util.validity.bool_encoding with 0 type parameters
  ensures(raw) r => r = decide (byte.val = 0 ∨ byte.val = 1)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.bool_encoding_spec for Zerocopy.util.validity.bool_encoding with 1

check_model_inputs Zerocopy.util.validity.nonzero_encoding with 0 type parameters
aeneas_spec_begin
spec nonzero_encoding_spec
  for @Zerocopy.util.validity.nonzero_encoding with 0 type parameters
  ensures(raw) r => r = decide (n.val ≠ 0)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.nonzero_encoding_spec for Zerocopy.util.validity.nonzero_encoding with 1

end Zerocopy.Specs
