/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredContracts
public import Specs
public import BytesAdapter
public import Obligations.Byteorder
@[expose] public section

/-!
These implications inspect an arbitrary execution outcome and use only its
supplied mathematical contract. Total scalar-array decoding covers every raw
input. The recovered observations are the separately stated positional sums,
complete numeric byte lists and exact setter results.
-/

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

theorem byteorder_decode_u16_le (bytes : Aeneas.Std.Array U8 2#usize) :
    Rust.Bytes.decodeLE (bytes.val.map U8.bv) = bytes.val[0]!.val + 256 * (bytes.val[1]!.val) := by
  obtain ⟨b0, b1, same⟩ := List.length_eq_two.mp
    (show bytes.val.length = 2 by simp)
  simp [same, Rust.Bytes.decodeLE]

@[contract_simps] theorem required_read_u16_le (bytes : Aeneas.Std.Array U8 2#usize)
    (run : Result U16) (provided : Specs.read_u16_le_spec_contract bytes run) :
    Obligations.read_u16_le_spec_contract bytes run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes))
  rintro output ⟨value, decoded, facts⟩
  have same := (decodeUScalar_iff output value).mp decoded
  change value.value = Rust.Bytes.decodeLE _ at facts
  rw [decodedArray_bytes_eq bytes (unsignedArray bytes) (decodeArray_unsigned bytes)] at facts
  change output.val = _
  rw [same, facts]
  exact byteorder_decode_u16_le bytes

@[contract_simps] theorem required_write_u16_le (n : U16)
    (run : Result (Aeneas.Std.Array U8 2#usize)) (provided : Specs.write_u16_le_spec_contract n run) :
    Obligations.write_u16_le_spec_contract n run := by
  apply WP.spec_mono (provided (unsignedWord n) rfl)
  rintro output ⟨value, decoded, facts⟩
  change value.val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) =
    Rust.Bytes.encodeLE 2 n.val at facts
  rw [decodedArray_bytes_eq output value decoded] at facts
  have digits := congrArg (List.map BitVec.toNat) facts
  change output.val.map UScalar.val = _
  simpa [List.map_map, Function.comp_def, Rust.Bytes.encodeBE,
    Rust.Bytes.encodeLE, BitVec.toNat_ofNat, Nat.div_div_eq_div_mul] using digits

@[contract_simps] theorem required_set_u16_le (bytes : Aeneas.Std.Array U8 2#usize) (n : U16)
    (run : Result U16) (provided : Specs.set_u16_le_spec_contract bytes n run) :
    Obligations.set_u16_le_spec_contract bytes n run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes)
    (unsignedWord n) rfl)
  rintro output ⟨value, decoded, facts⟩
  apply UScalar.eq_of_val_eq
  have same := (decodeUScalar_iff output value).mp decoded
  rw [same]
  exact congrArg UnsignedWord.value facts

theorem byteorder_decode_u16_be (bytes : Aeneas.Std.Array U8 2#usize) :
    Rust.Bytes.decodeBE (bytes.val.map U8.bv) = bytes.val[1]!.val + 256 * (bytes.val[0]!.val) := by
  obtain ⟨b0, b1, same⟩ := List.length_eq_two.mp
    (show bytes.val.length = 2 by simp)
  simp [same, Rust.Bytes.decodeBE, Rust.Bytes.decodeLE]

@[contract_simps] theorem required_read_u16_be (bytes : Aeneas.Std.Array U8 2#usize)
    (run : Result U16) (provided : Specs.read_u16_be_spec_contract bytes run) :
    Obligations.read_u16_be_spec_contract bytes run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes))
  rintro output ⟨value, decoded, facts⟩
  have same := (decodeUScalar_iff output value).mp decoded
  change value.value = Rust.Bytes.decodeBE _ at facts
  rw [decodedArray_bytes_eq bytes (unsignedArray bytes) (decodeArray_unsigned bytes)] at facts
  change output.val = _
  rw [same, facts]
  exact byteorder_decode_u16_be bytes

@[contract_simps] theorem required_write_u16_be (n : U16)
    (run : Result (Aeneas.Std.Array U8 2#usize)) (provided : Specs.write_u16_be_spec_contract n run) :
    Obligations.write_u16_be_spec_contract n run := by
  apply WP.spec_mono (provided (unsignedWord n) rfl)
  rintro output ⟨value, decoded, facts⟩
  change value.val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) =
    Rust.Bytes.encodeBE 2 n.val at facts
  rw [decodedArray_bytes_eq output value decoded] at facts
  have digits := congrArg (List.map BitVec.toNat) facts
  change output.val.map UScalar.val = _
  simpa [List.map_map, Function.comp_def, Rust.Bytes.encodeBE,
    Rust.Bytes.encodeLE, BitVec.toNat_ofNat, Nat.div_div_eq_div_mul] using digits

@[contract_simps] theorem required_set_u16_be (bytes : Aeneas.Std.Array U8 2#usize) (n : U16)
    (run : Result U16) (provided : Specs.set_u16_be_spec_contract bytes n run) :
    Obligations.set_u16_be_spec_contract bytes n run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes)
    (unsignedWord n) rfl)
  rintro output ⟨value, decoded, facts⟩
  apply UScalar.eq_of_val_eq
  have same := (decodeUScalar_iff output value).mp decoded
  rw [same]
  exact congrArg UnsignedWord.value facts

theorem byteorder_decode_u32_le (bytes : Aeneas.Std.Array U8 4#usize) :
    Rust.Bytes.decodeLE (bytes.val.map U8.bv) = bytes.val[0]!.val + 256 * (bytes.val[1]!.val + 256 * (bytes.val[2]!.val + 256 * (bytes.val[3]!.val))) := by
  obtain ⟨b0, b1, b2, b3, same⟩ := List.length_eq_four.mp
    (show bytes.val.length = 4 by simp)
  simp [same, Rust.Bytes.decodeLE]

@[contract_simps] theorem required_read_u32_le (bytes : Aeneas.Std.Array U8 4#usize)
    (run : Result U32) (provided : Specs.read_u32_le_spec_contract bytes run) :
    Obligations.read_u32_le_spec_contract bytes run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes))
  rintro output ⟨value, decoded, facts⟩
  have same := (decodeUScalar_iff output value).mp decoded
  change value.value = Rust.Bytes.decodeLE _ at facts
  rw [decodedArray_bytes_eq bytes (unsignedArray bytes) (decodeArray_unsigned bytes)] at facts
  change output.val = _
  rw [same, facts]
  exact byteorder_decode_u32_le bytes

@[contract_simps] theorem required_write_u32_le (n : U32)
    (run : Result (Aeneas.Std.Array U8 4#usize)) (provided : Specs.write_u32_le_spec_contract n run) :
    Obligations.write_u32_le_spec_contract n run := by
  apply WP.spec_mono (provided (unsignedWord n) rfl)
  rintro output ⟨value, decoded, facts⟩
  change value.val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) =
    Rust.Bytes.encodeLE 4 n.val at facts
  rw [decodedArray_bytes_eq output value decoded] at facts
  have digits := congrArg (List.map BitVec.toNat) facts
  change output.val.map UScalar.val = _
  simpa [List.map_map, Function.comp_def, Rust.Bytes.encodeBE,
    Rust.Bytes.encodeLE, BitVec.toNat_ofNat, Nat.div_div_eq_div_mul] using digits

@[contract_simps] theorem required_set_u32_le (bytes : Aeneas.Std.Array U8 4#usize) (n : U32)
    (run : Result U32) (provided : Specs.set_u32_le_spec_contract bytes n run) :
    Obligations.set_u32_le_spec_contract bytes n run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes)
    (unsignedWord n) rfl)
  rintro output ⟨value, decoded, facts⟩
  apply UScalar.eq_of_val_eq
  have same := (decodeUScalar_iff output value).mp decoded
  rw [same]
  exact congrArg UnsignedWord.value facts

theorem byteorder_decode_u32_be (bytes : Aeneas.Std.Array U8 4#usize) :
    Rust.Bytes.decodeBE (bytes.val.map U8.bv) = bytes.val[3]!.val + 256 * (bytes.val[2]!.val + 256 * (bytes.val[1]!.val + 256 * (bytes.val[0]!.val))) := by
  obtain ⟨b0, b1, b2, b3, same⟩ := List.length_eq_four.mp
    (show bytes.val.length = 4 by simp)
  simp [same, Rust.Bytes.decodeBE, Rust.Bytes.decodeLE]

@[contract_simps] theorem required_read_u32_be (bytes : Aeneas.Std.Array U8 4#usize)
    (run : Result U32) (provided : Specs.read_u32_be_spec_contract bytes run) :
    Obligations.read_u32_be_spec_contract bytes run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes))
  rintro output ⟨value, decoded, facts⟩
  have same := (decodeUScalar_iff output value).mp decoded
  change value.value = Rust.Bytes.decodeBE _ at facts
  rw [decodedArray_bytes_eq bytes (unsignedArray bytes) (decodeArray_unsigned bytes)] at facts
  change output.val = _
  rw [same, facts]
  exact byteorder_decode_u32_be bytes

@[contract_simps] theorem required_write_u32_be (n : U32)
    (run : Result (Aeneas.Std.Array U8 4#usize)) (provided : Specs.write_u32_be_spec_contract n run) :
    Obligations.write_u32_be_spec_contract n run := by
  apply WP.spec_mono (provided (unsignedWord n) rfl)
  rintro output ⟨value, decoded, facts⟩
  change value.val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) =
    Rust.Bytes.encodeBE 4 n.val at facts
  rw [decodedArray_bytes_eq output value decoded] at facts
  have digits := congrArg (List.map BitVec.toNat) facts
  change output.val.map UScalar.val = _
  simpa [List.map_map, Function.comp_def, Rust.Bytes.encodeBE,
    Rust.Bytes.encodeLE, BitVec.toNat_ofNat, Nat.div_div_eq_div_mul] using digits

@[contract_simps] theorem required_set_u32_be (bytes : Aeneas.Std.Array U8 4#usize) (n : U32)
    (run : Result U32) (provided : Specs.set_u32_be_spec_contract bytes n run) :
    Obligations.set_u32_be_spec_contract bytes n run := by
  apply WP.spec_mono (provided (unsignedArray bytes) (decodeArray_unsigned bytes)
    (unsignedWord n) rfl)
  rintro output ⟨value, decoded, facts⟩
  apply UScalar.eq_of_val_eq
  have same := (decodeUScalar_iff output value).mp decoded
  rw [same]
  exact congrArg UnsignedWord.value facts

end Zerocopy.Proofs
