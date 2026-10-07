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

end Zerocopy.Specs
