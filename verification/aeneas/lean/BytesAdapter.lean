/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustAeneas.Bytes
public import ModelLemmas
@[expose] public section

/-!
These adapters preserve byte values through zerocopy's scalar-array decoders.
The generic numerical byte bridges live in the shared Aeneas companion package.
Rust/compiler correspondence remains a separate obligation.
-/

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
