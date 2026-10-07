/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import BytesAdapter
@[expose] public section

/-!
The raw lemmas check the extracted constructors, accessors and setters. The
canonical proofs then transport those facts through the ordinary scalar and
array decoders without adding input restrictions.
-/

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs.Raw

theorem read_u16_le (bytes : Aeneas.Std.Array U8 2#usize) :
    byteorder.verification.read_u16_le bytes
      ⦃ output => output.val = Rust.Bytes.decodeLE (bytes.val.map U8.bv) ⦄ := by
  simp only [byteorder.verification.read_u16_le, byteorder.U16.from_bytes,
    byteorder.U16.get, byteorder.LittleEndian.Insts.ZerocopyByteorderByteOrder.ORDER, bind_ok, WP.spec_ok]
  simp only [core.num.U16.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  exact Rust.Bytes.AeneasAdapter.fromLEBytes_toNat _

theorem write_u16_le (n : U16) :
    byteorder.verification.write_u16_le n
      ⦃ output => output.val.map U8.bv = Rust.Bytes.encodeLE 2 n.val ⦄ := by
  have digits : (core.num.U16.to_le_bytes n).val.map U8.bv = n.bv.toLEBytes := by
    simp only [core.num.U16.to_le_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  simp only [byteorder.verification.write_u16_le, byteorder.U16.new,
    core.convert.IntoFrom.into, ArrayU82.Insts.CoreConvertFromU16.from,
    byteorder.LittleEndian.Insts.ZerocopyByteorderByteOrder.ORDER, lift, bind_ok, WP.spec_ok]
  rw [digits]
  exact Rust.Bytes.AeneasAdapter.toLEBytes_eq_encodeLE (by decide) n.bv

theorem set_u16_le (bytes : Aeneas.Std.Array U8 2#usize) (n : U16) :
    byteorder.verification.set_u16_le bytes n ⦃ output => output = n ⦄ := by
  have digits : (core.num.U16.to_le_bytes n).val.map U8.bv = n.bv.toLEBytes := by
    simp only [core.num.U16.to_le_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  simp only [byteorder.verification.set_u16_le, byteorder.U16.from_bytes,
    byteorder.U16.set, byteorder.U16.new, byteorder.U16.get,
    byteorder.LittleEndian.Insts.ZerocopyByteorderByteOrder.ORDER, lift, bind_ok, WP.spec_ok]
  apply UScalar.eq_of_val_eq
  change (BitVec.fromLEBytes ((core.num.U16.to_le_bytes n).val.map U8.bv)).toNat = n.bv.toNat
  rw [digits, Rust.Bytes.AeneasAdapter.fromLEBytes_toNat]
  exact Rust.Bytes.AeneasAdapter.decodeLE_toLEBytes (by decide) n.bv

theorem read_u16_be (bytes : Aeneas.Std.Array U8 2#usize) :
    byteorder.verification.read_u16_be bytes
      ⦃ output => output.val = Rust.Bytes.decodeBE (bytes.val.map U8.bv) ⦄ := by
  simp only [byteorder.verification.read_u16_be, byteorder.U16.from_bytes,
    byteorder.U16.get, byteorder.BigEndian.Insts.ZerocopyByteorderByteOrder.ORDER, bind_ok, WP.spec_ok]
  simp only [core.num.U16.from_be_bytes, UScalar.val, BitVec.toNat_cast]
  exact Rust.Bytes.AeneasAdapter.fromBEBytes_toNat _

theorem write_u16_be (n : U16) :
    byteorder.verification.write_u16_be n
      ⦃ output => output.val.map U8.bv = Rust.Bytes.encodeBE 2 n.val ⦄ := by
  have digits : (core.num.U16.to_be_bytes n).val.map U8.bv = n.bv.toBEBytes := by
    simp only [core.num.U16.to_be_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  simp only [byteorder.verification.write_u16_be, byteorder.U16.new,
    core.convert.IntoFrom.into, ArrayU82.Insts.CoreConvertFromU16.from,
    byteorder.BigEndian.Insts.ZerocopyByteorderByteOrder.ORDER, lift, bind_ok, WP.spec_ok]
  rw [digits]
  exact Rust.Bytes.AeneasAdapter.toBEBytes_eq_encodeBE (by decide) n.bv

theorem set_u16_be (bytes : Aeneas.Std.Array U8 2#usize) (n : U16) :
    byteorder.verification.set_u16_be bytes n ⦃ output => output = n ⦄ := by
  have digits : (core.num.U16.to_be_bytes n).val.map U8.bv = n.bv.toBEBytes := by
    simp only [core.num.U16.to_be_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  simp only [byteorder.verification.set_u16_be, byteorder.U16.from_bytes,
    byteorder.U16.set, byteorder.U16.new, byteorder.U16.get,
    byteorder.BigEndian.Insts.ZerocopyByteorderByteOrder.ORDER, lift, bind_ok, WP.spec_ok]
  apply UScalar.eq_of_val_eq
  change (BitVec.fromBEBytes ((core.num.U16.to_be_bytes n).val.map U8.bv)).toNat = n.bv.toNat
  rw [digits, Rust.Bytes.AeneasAdapter.fromBEBytes_toNat]
  exact Rust.Bytes.AeneasAdapter.decodeBE_toBEBytes (by decide) n.bv

theorem read_u32_le (bytes : Aeneas.Std.Array U8 4#usize) :
    byteorder.verification.read_u32_le bytes
      ⦃ output => output.val = Rust.Bytes.decodeLE (bytes.val.map U8.bv) ⦄ := by
  simp only [byteorder.verification.read_u32_le, byteorder.U32.from_bytes,
    byteorder.U32.get, byteorder.LittleEndian.Insts.ZerocopyByteorderByteOrder.ORDER, bind_ok, WP.spec_ok]
  simp only [core.num.U32.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  exact Rust.Bytes.AeneasAdapter.fromLEBytes_toNat _

theorem write_u32_le (n : U32) :
    byteorder.verification.write_u32_le n
      ⦃ output => output.val.map U8.bv = Rust.Bytes.encodeLE 4 n.val ⦄ := by
  have digits : (core.num.U32.to_le_bytes n).val.map U8.bv = n.bv.toLEBytes := by
    simp only [core.num.U32.to_le_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  simp only [byteorder.verification.write_u32_le, byteorder.U32.new,
    core.convert.IntoFrom.into, ArrayU84.Insts.CoreConvertFromU32.from,
    byteorder.LittleEndian.Insts.ZerocopyByteorderByteOrder.ORDER, lift, bind_ok, WP.spec_ok]
  rw [digits]
  exact Rust.Bytes.AeneasAdapter.toLEBytes_eq_encodeLE (by decide) n.bv

theorem set_u32_le (bytes : Aeneas.Std.Array U8 4#usize) (n : U32) :
    byteorder.verification.set_u32_le bytes n ⦃ output => output = n ⦄ := by
  have digits : (core.num.U32.to_le_bytes n).val.map U8.bv = n.bv.toLEBytes := by
    simp only [core.num.U32.to_le_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  simp only [byteorder.verification.set_u32_le, byteorder.U32.from_bytes,
    byteorder.U32.set, byteorder.U32.new, byteorder.U32.get,
    byteorder.LittleEndian.Insts.ZerocopyByteorderByteOrder.ORDER, lift, bind_ok, WP.spec_ok]
  apply UScalar.eq_of_val_eq
  change (BitVec.fromLEBytes ((core.num.U32.to_le_bytes n).val.map U8.bv)).toNat = n.bv.toNat
  rw [digits, Rust.Bytes.AeneasAdapter.fromLEBytes_toNat]
  exact Rust.Bytes.AeneasAdapter.decodeLE_toLEBytes (by decide) n.bv

theorem read_u32_be (bytes : Aeneas.Std.Array U8 4#usize) :
    byteorder.verification.read_u32_be bytes
      ⦃ output => output.val = Rust.Bytes.decodeBE (bytes.val.map U8.bv) ⦄ := by
  simp only [byteorder.verification.read_u32_be, byteorder.U32.from_bytes,
    byteorder.U32.get, byteorder.BigEndian.Insts.ZerocopyByteorderByteOrder.ORDER, bind_ok, WP.spec_ok]
  simp only [core.num.U32.from_be_bytes, UScalar.val, BitVec.toNat_cast]
  exact Rust.Bytes.AeneasAdapter.fromBEBytes_toNat _

theorem write_u32_be (n : U32) :
    byteorder.verification.write_u32_be n
      ⦃ output => output.val.map U8.bv = Rust.Bytes.encodeBE 4 n.val ⦄ := by
  have digits : (core.num.U32.to_be_bytes n).val.map U8.bv = n.bv.toBEBytes := by
    simp only [core.num.U32.to_be_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  simp only [byteorder.verification.write_u32_be, byteorder.U32.new,
    core.convert.IntoFrom.into, ArrayU84.Insts.CoreConvertFromU32.from,
    byteorder.BigEndian.Insts.ZerocopyByteorderByteOrder.ORDER, lift, bind_ok, WP.spec_ok]
  rw [digits]
  exact Rust.Bytes.AeneasAdapter.toBEBytes_eq_encodeBE (by decide) n.bv

theorem set_u32_be (bytes : Aeneas.Std.Array U8 4#usize) (n : U32) :
    byteorder.verification.set_u32_be bytes n ⦃ output => output = n ⦄ := by
  have digits : (core.num.U32.to_be_bytes n).val.map U8.bv = n.bv.toBEBytes := by
    simp only [core.num.U32.to_be_bytes, Array.from_val, List.map_map,
      ↓U8.bv_UScalar_mk, List.map_id]
  simp only [byteorder.verification.set_u32_be, byteorder.U32.from_bytes,
    byteorder.U32.set, byteorder.U32.new, byteorder.U32.get,
    byteorder.BigEndian.Insts.ZerocopyByteorderByteOrder.ORDER, lift, bind_ok, WP.spec_ok]
  apply UScalar.eq_of_val_eq
  change (BitVec.fromBEBytes ((core.num.U32.to_be_bytes n).val.map U8.bv)).toNat = n.bv.toNat
  rw [digits, Rust.Bytes.AeneasAdapter.fromBEBytes_toNat]
  exact Rust.Bytes.AeneasAdapter.decodeBE_toBEBytes (by decide) n.bv

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs

theorem read_u16_le_spec : Specs.read_u16_le_spec := by
  intro bytes value decoded
  apply WP.spec_mono (Raw.read_u16_le bytes)
  intro output facts
  refine ⟨unsignedWord output, rfl, ?_⟩
  change output.val = Rust.Bytes.decodeLE _
  rw [decodedArray_bytes_eq bytes value decoded]
  exact facts

theorem write_u16_le_spec : Specs.write_u16_le_spec := by
  intro n value decoded
  have same := (decodeUScalar_iff n value).mp decoded
  apply WP.spec_mono (Raw.write_u16_le n)
  intro output facts
  refine ⟨unsignedArray output, decodeArray_unsigned output, ?_⟩
  change (unsignedArray output).val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) =
    Rust.Bytes.encodeLE 2 value.value
  rw [decodedArray_bytes_eq output (unsignedArray output) (decodeArray_unsigned output)]
  rw [← same]
  exact facts

theorem set_u16_le_spec : Specs.set_u16_le_spec := by
  intro bytes n _ _ value decoded
  apply WP.spec_mono (Raw.set_u16_le bytes n)
  intro output facts
  subst output
  refine ⟨unsignedWord n, rfl, ?_⟩
  exact Option.some.inj decoded

theorem read_u16_be_spec : Specs.read_u16_be_spec := by
  intro bytes value decoded
  apply WP.spec_mono (Raw.read_u16_be bytes)
  intro output facts
  refine ⟨unsignedWord output, rfl, ?_⟩
  change output.val = Rust.Bytes.decodeBE _
  rw [decodedArray_bytes_eq bytes value decoded]
  exact facts

theorem write_u16_be_spec : Specs.write_u16_be_spec := by
  intro n value decoded
  have same := (decodeUScalar_iff n value).mp decoded
  apply WP.spec_mono (Raw.write_u16_be n)
  intro output facts
  refine ⟨unsignedArray output, decodeArray_unsigned output, ?_⟩
  change (unsignedArray output).val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) =
    Rust.Bytes.encodeBE 2 value.value
  rw [decodedArray_bytes_eq output (unsignedArray output) (decodeArray_unsigned output)]
  rw [← same]
  exact facts

theorem set_u16_be_spec : Specs.set_u16_be_spec := by
  intro bytes n _ _ value decoded
  apply WP.spec_mono (Raw.set_u16_be bytes n)
  intro output facts
  subst output
  refine ⟨unsignedWord n, rfl, ?_⟩
  exact Option.some.inj decoded

theorem read_u32_le_spec : Specs.read_u32_le_spec := by
  intro bytes value decoded
  apply WP.spec_mono (Raw.read_u32_le bytes)
  intro output facts
  refine ⟨unsignedWord output, rfl, ?_⟩
  change output.val = Rust.Bytes.decodeLE _
  rw [decodedArray_bytes_eq bytes value decoded]
  exact facts

theorem write_u32_le_spec : Specs.write_u32_le_spec := by
  intro n value decoded
  have same := (decodeUScalar_iff n value).mp decoded
  apply WP.spec_mono (Raw.write_u32_le n)
  intro output facts
  refine ⟨unsignedArray output, decodeArray_unsigned output, ?_⟩
  change (unsignedArray output).val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) =
    Rust.Bytes.encodeLE 4 value.value
  rw [decodedArray_bytes_eq output (unsignedArray output) (decodeArray_unsigned output)]
  rw [← same]
  exact facts

theorem set_u32_le_spec : Specs.set_u32_le_spec := by
  intro bytes n _ _ value decoded
  apply WP.spec_mono (Raw.set_u32_le bytes n)
  intro output facts
  subst output
  refine ⟨unsignedWord n, rfl, ?_⟩
  exact Option.some.inj decoded

theorem read_u32_be_spec : Specs.read_u32_be_spec := by
  intro bytes value decoded
  apply WP.spec_mono (Raw.read_u32_be bytes)
  intro output facts
  refine ⟨unsignedWord output, rfl, ?_⟩
  change output.val = Rust.Bytes.decodeBE _
  rw [decodedArray_bytes_eq bytes value decoded]
  exact facts

theorem write_u32_be_spec : Specs.write_u32_be_spec := by
  intro n value decoded
  have same := (decodeUScalar_iff n value).mp decoded
  apply WP.spec_mono (Raw.write_u32_be n)
  intro output facts
  refine ⟨unsignedArray output, decodeArray_unsigned output, ?_⟩
  change (unsignedArray output).val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) =
    Rust.Bytes.encodeBE 4 value.value
  rw [decodedArray_bytes_eq output (unsignedArray output) (decodeArray_unsigned output)]
  rw [← same]
  exact facts

theorem set_u32_be_spec : Specs.set_u32_be_spec := by
  intro bytes n _ _ value decoded
  apply WP.spec_mono (Raw.set_u32_be bytes n)
  intro output facts
  subst output
  refine ⟨unsignedWord n, rfl, ?_⟩
  exact Option.some.inj decoded

end Zerocopy.Proofs
