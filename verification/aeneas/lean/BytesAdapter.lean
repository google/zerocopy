/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas.Data.BitVec
public import Rust.Bytes
public import ModelLemmas
@[expose] public section

/-!
These proved adapters connect the shared numerical byte model to the pinned
Aeneas byte primitives and recursively decoded scalar arrays. They add no
Rust/compiler correspondence assumptions.
-/

namespace Rust.Bytes.AeneasAdapter

theorem fromLEBytes_toNat (bytes : List Rust.Bytes.Byte) :
    (BitVec.fromLEBytes bytes).toNat = Rust.Bytes.decodeLE bytes := by
  induction bytes with
  | nil => simp [BitVec.fromLEBytes, Rust.Bytes.decodeLE]
  | cons byte rest ih =>
    have hwidth : 2 ^ (8 * (byte :: rest).length) = 256 * 256 ^ rest.length := by
      rw [← Rust.Bytes.radix_pow_eq_two_pow]
      simp [Nat.pow_succ, Nat.mul_comm]
    have hb := Rust.Bytes.byte_lt_256 byte
    have hr := Rust.Bytes.decodeLE_lt rest
    have hp : 0 < 256 ^ rest.length := Nat.pow_pos (by decide)
    simp only [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ih, hwidth]
    rw [Nat.mod_eq_of_lt (by omega : byte.toNat < 256 * 256 ^ rest.length),
      Nat.mod_eq_of_lt (by omega : Rust.Bytes.decodeLE rest < 256 * 256 ^ rest.length),
      Nat.mod_eq_of_lt (by omega : Rust.Bytes.decodeLE rest * 2 ^ 8 < 256 * 256 ^ rest.length)]
    rw [Nat.or_comm, Nat.mul_comm (Rust.Bytes.decodeLE rest) (2 ^ 8),
      ← Nat.two_pow_add_eq_or_of_lt (show byte.toNat < 2 ^ 8 from hb)]
    simp only [Rust.Bytes.decodeLE_cons, Nat.reducePow]
    omega

theorem fromBEBytes_toNat (bytes : List Rust.Bytes.Byte) :
    (BitVec.fromBEBytes bytes).toNat = Rust.Bytes.decodeBE bytes := by
  simp only [BitVec.fromBEBytes, BitVec.toNat_cast, fromLEBytes_toNat,
    Rust.Bytes.decodeBE]

/-- For a whole number of bytes, Aeneas's emitted bytes recover the value. -/
theorem decodeLE_toLEBytes {width : Nat} (h : width % 8 = 0) (value : BitVec width) :
    Rust.Bytes.decodeLE value.toLEBytes = value.toNat := by
  have result := congrArg BitVec.toNat (BitVec.fromLEBytes_toLEBytes h value)
  simpa only [fromLEBytes_toNat, BitVec.toNat_cast] using result

theorem decodeBE_toBEBytes {width : Nat} (h : width % 8 = 0) (value : BitVec width) :
    Rust.Bytes.decodeBE value.toBEBytes = value.toNat := by
  simp only [BitVec.toBEBytes, Rust.Bytes.decodeBE, List.reverse_reverse]
  exact decodeLE_toLEBytes h value

/-- Aeneas and the shared model write the same bytes for every byte-aligned width. -/
theorem toLEBytes_eq_encodeLE {width : Nat} (h : width % 8 = 0) (value : BitVec width) :
    value.toLEBytes = Rust.Bytes.encodeLE (width / 8) value.toNat := by
  have hlength : value.toLEBytes.length = width / 8 := by
    rw [BitVec.toLEBytes_length]
    omega
  calc
    value.toLEBytes = Rust.Bytes.encodeLE value.toLEBytes.length
        (Rust.Bytes.decodeLE value.toLEBytes) := (Rust.Bytes.encodeLE_decodeLE _).symm
    _ = Rust.Bytes.encodeLE (width / 8) value.toNat := by
      rw [hlength, decodeLE_toLEBytes h]

theorem toBEBytes_eq_encodeBE {width : Nat} (h : width % 8 = 0) (value : BitVec width) :
    value.toBEBytes = Rust.Bytes.encodeBE (width / 8) value.toNat := by
  rw [BitVec.toBEBytes, Rust.Bytes.encodeBE, toLEBytes_eq_encodeLE h]

end Rust.Bytes.AeneasAdapter

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

/-- Scalar list decoding accepts every finite scalar and preserves its value. -/
theorem decodeList_unsigned {ty : UScalarTy} (raw : List (UScalar ty)) :
    decodeList (modelUScalar ty).decode raw = some (raw.map unsignedWord) := by
  induction raw with
  | nil => rfl
  | cons head tail ih => simp [decodeList, ih]

/-- The mathematical witness for every raw scalar array, at its original length. -/
def unsignedArray {ty : UScalarTy} {count : Usize} (raw : Aeneas.Std.Array (UScalar ty) count) :
    ArrayValue (UnsignedWord ty) count :=
  ⟨raw.val.map unsignedWord, by simpa only [List.length_map] using raw.property⟩

theorem decodeArray_unsigned {ty : UScalarTy} {count : Usize}
    (raw : Aeneas.Std.Array (UScalar ty) count) :
    (modelArray count).decode raw = some (unsignedArray raw) := by
  apply (decodeArray_iff (modelUScalar ty) count raw (unsignedArray raw)).mpr
  exact decodeList_unsigned raw.val

theorem u8_ofNat_val (raw : U8) : BitVec.ofNat 8 raw.val = raw.bv := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, UScalar.val]
  exact Nat.mod_eq_of_lt raw.bv.isLt

/-- The decoded array retains every byte used by the numerical specification. -/
theorem decodedArray_bytes_eq {count : Usize} (raw : Aeneas.Std.Array U8 count)
    (value : ArrayValue (UnsignedWord .U8) count)
    (decoded : (modelArray count).decode raw = some value) :
    value.val.map (fun byte => BitVec.ofNat 8 (byte : Nat)) = raw.val.map U8.bv := by
  have same : raw.val.map unsignedWord = value.val :=
    Option.some.inj ((decodeList_unsigned raw.val).symm.trans
      ((decodeArray_iff (modelUScalar .U8) count raw value).mp decoded))
  simp only [← same, bind_pure_comp]
  simp only [Functor.map, List.map_map]
  apply List.map_congr_left
  intro byte _
  exact u8_ofNat_val byte

end Zerocopy.Proofs
