/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustRepresentation
import all RustModel
import all ModelPrelude
import all Rust.Storage
import all RustAeneas.Storage
@[expose] public section

/-!
Source realizability is conditional on mathematical admission. It supplies a
physical representation of that particular raw value, without imposing a
default value or a unique representation. An uninhabited raw carrier therefore
needs no invented source value. These existence laws leave initialization and
Rust layout correspondence as separate obligations.
-/

namespace Rust.Storage

/-- Integer encoding supplies a representation for every fixed-width word. -/
theorem integerDecoder_realizable (byteSize : Nat) (endian : Rust.Bytes.Endian)
    (word : BitVec (8 * byteSize)) :
    ∃ bytes, (integerDecoder byteSize endian).run bytes = some word := by
  have bound : word.toNat < 256 ^ byteSize := by
    rw [Rust.Bytes.radix_pow_eq_two_pow]
    exact word.isLt
  cases endian with
  | little =>
    refine ⟨(Rust.Bytes.encodeLE byteSize word.toNat).map AMByte.init, ?_⟩
    rw [integerDecoder_run_map _ _ _ (Rust.Bytes.length_encodeLE _ _)]
    simp only [Rust.Bytes.decode, Rust.Bytes.decodeLE_encodeLE_of_lt _ _ bound]
    congr 1
    simp
  | big =>
    refine ⟨(Rust.Bytes.encodeBE byteSize word.toNat).map AMByte.init, ?_⟩
    rw [integerDecoder_run_map _ _ _ (Rust.Bytes.length_encodeBE _ _)]
    simp only [Rust.Bytes.decode, Rust.Bytes.decodeBE_encodeBE_of_lt _ _ bound]
    congr 1
    simp

namespace BitDecoder

/-- A mapped decoder realizes an output whenever one realized input maps to it. -/
theorem map_realizable (decoder : BitDecoder Raw) (f : Raw → Other)
    (raw : Raw) (h : ∃ bytes, decoder.run bytes = some raw) :
    ∃ bytes, (decoder.map f).run bytes = some (f raw) := by
  obtain ⟨bytes, accepted⟩ := h
  exact ⟨bytes, by rw [run_map, accepted]; rfl⟩

/-- Filtering preserves an existing representation when the value passes. -/
theorem filterMap_realizable (decoder : BitDecoder Raw) (f : Raw → Option Other)
    (raw : Raw) (other : Other) (h : ∃ bytes, decoder.run bytes = some raw)
    (passes : f raw = some other) :
    ∃ bytes, (decoder.filterMap f).run bytes = some other := by
  obtain ⟨bytes, accepted⟩ := h
  exact ⟨bytes, by rw [run_filterMap, accepted]; exact passes⟩

end BitDecoder

/-- Concatenate one witness per admitted element. Recursion follows the value
list, so empty arrays and zero-sized elements require no inhabited carrier. -/
theorem arrayDecode_realizable (element : BitDecoder Raw) (admitted : Raw → Prop)
    (realizable : ∀ raw, admitted raw → ∃ bytes, element.run bytes = some raw)
    (raws : List Raw) (valid : ∀ raw ∈ raws, admitted raw) :
    ∃ bytes, bytes.length = raws.length * element.byteSize ∧
      arrayDecode element raws.length bytes = some ⟨raws, rfl⟩ := by
  induction raws with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons raw raws ih =>
    obtain ⟨head, headAccepted⟩ := realizable raw (valid raw (by simp))
    have headWidth := BitDecoder.run_length element head raw headAccepted
    obtain ⟨tail, tailWidth, tailAccepted⟩ := ih
      (fun raw member => valid raw (by simp [member]))
    refine ⟨head ++ tail, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, headWidth, tailWidth, Nat.succ_mul]
      omega
    · simp only [List.length_cons, arrayDecode, ← headWidth, List.take_left, List.drop_left,
        headAccepted, tailAccepted]
      rfl

end Rust.Storage

open Aeneas.Std Rust.Storage
namespace AeneasSpecs

theorem RustModel.realizableRepresentation_exists {Raw : Type u} [m : RustModel Raw]
    (realizable : RustModel.realizableRepresentation Raw)
    (decoder : BitDecoder Raw) (available : m.representation = some decoder)
    (raw : Raw) (valid : isValid raw) : ∃ bytes, decoder.run bytes = some raw := by
  exact m.realizable_fixed decoder available realizable raw valid

theorem realizableUScalar (ty : UScalarTy) :
    RustModel.realizableRepresentation (UScalar ty) := by
  intro raw _
  obtain ⟨bytes, accepted⟩ := integerDecoder_realizable (ty.numBits / 8) .little
    (raw.bv.cast (AeneasAdapter.unsigned_byte_width ty).symm)
  refine ⟨bytes, ?_⟩
  change ((integerDecoder _ _).map _).run bytes = _
  rw [BitDecoder.run_map, accepted]
  simp

theorem realizableIScalar (ty : IScalarTy) :
    RustModel.realizableRepresentation (IScalar ty) := by
  intro raw _
  obtain ⟨bytes, accepted⟩ := integerDecoder_realizable (ty.numBits / 8) .little
    (raw.bv.cast (AeneasAdapter.signed_byte_width ty).symm)
  refine ⟨bytes, ?_⟩
  change ((integerDecoder _ _).map _).run bytes = _
  rw [BitDecoder.run_map, accepted]
  simp

theorem realizableBool : RustModel.realizableRepresentation Bool := by
  intro raw _
  cases raw
  · exact ⟨[AMByte.init 0], boolDecoder_run_zero⟩
  · exact ⟨[AMByte.init 1], boolDecoder_run_one⟩

theorem realizableUnit : RustModel.realizableRepresentation Unit := by
  intro raw _
  cases raw
  exact ⟨[], unitDecoder_run_nil⟩

theorem realizablePhantomData (T : Type) :
    RustModel.realizableRepresentation (Zerocopy.core.marker.PhantomData T) := by
  intro raw _
  rw [phantomData_eq_mk T raw]
  exact ⟨[], emptyDecoder_run_nil _⟩

theorem realizableChar : RustModel.realizableRepresentation Char := by
  intro raw _
  obtain ⟨bytes, accepted⟩ := integerDecoder_realizable 4 .little
    (BitVec.ofNat 32 raw.val.toNat)
  refine ⟨bytes, ?_⟩
  change ((integerDecoder 4 .little).filterMap _).run bytes = _
  rw [BitDecoder.run_filterMap, accepted]
  have word : UInt32.ofNat (BitVec.ofNat 32 raw.val.toNat).toNat = raw.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt32.toNat_lt raw.val)]
    exact UInt32.ofNat_toNat
  have valid : _root_.isValidChar raw.val := by
    simpa only [_root_.isValidChar, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat,
      UInt32.isValidChar, Nat.isValidChar] using raw.valid
  simp only [Option.bind_some, word, dif_pos valid]

theorem realizableOptionNonZeroUScalar (ty : UScalarTy) (Inner : Type) :
    RustModel.realizableRepresentation (Option (core.num.nonzero.NonZero (UScalar ty) Inner)) := by
  intro raw valid
  cases raw with
  | none =>
    obtain ⟨bytes, accepted⟩ := RustModel.realizableRepresentation_exists
      (realizableUScalar ty) (uScalarBitDecoder ty) rfl ⟨0⟩ ⟨_, rfl⟩
    exact ⟨bytes, by rw [BitDecoder.run_map, accepted]; rfl⟩
  | some raw =>
    have nonzero : raw.val.val ≠ 0 := by
      obtain ⟨value, accepted⟩ := valid
      by_cases positive : 0 < raw.val.val
      · omega
      · simp [RustModel.decode, positive] at accepted
    obtain ⟨bytes, accepted⟩ := RustModel.realizableRepresentation_exists
      (realizableUScalar ty) (uScalarBitDecoder ty) rfl raw.val ⟨_, rfl⟩
    exact ⟨bytes, by rw [BitDecoder.run_map, accepted]; simp [nonzero]⟩

theorem realizableOptionNonZeroIScalar (ty : IScalarTy) (Inner : Type) :
    RustModel.realizableRepresentation (Option (core.num.nonzero.NonZero (IScalar ty) Inner)) := by
  intro raw valid
  cases raw with
  | none =>
    obtain ⟨bytes, accepted⟩ := RustModel.realizableRepresentation_exists
      (realizableIScalar ty) (iScalarBitDecoder ty) rfl ⟨0⟩ ⟨_, rfl⟩
    exact ⟨bytes, by rw [BitDecoder.run_map, accepted]; simp only [Option.map_some, IScalar.val, BitVec.toInt_ofNat, Int.natCast_zero, Int.zero_bmod, ite_true]⟩
  | some raw =>
    have nonzero : raw.val.val ≠ 0 := by
      obtain ⟨value, accepted⟩ := valid
      by_contra zero
      simp [RustModel.decode, zero] at accepted
    obtain ⟨bytes, accepted⟩ := RustModel.realizableRepresentation_exists
      (realizableIScalar ty) (iScalarBitDecoder ty) rfl raw.val ⟨_, rfl⟩
    exact ⟨bytes, by rw [BitDecoder.run_map, accepted]; simp [nonzero]⟩

theorem realizableNonZeroUScalar (ty : UScalarTy) (Inner : Type) :
    RustModel.realizableRepresentation (core.num.nonzero.NonZero (UScalar ty) Inner) := by
  intro raw valid
  have nonzero : raw.val.val ≠ 0 := by
    obtain ⟨value, accepted⟩ := valid
    by_cases positive : 0 < raw.val.val
    · omega
    · simp [RustModel.decode, positive] at accepted
  obtain ⟨bytes, accepted⟩ := RustModel.realizableRepresentation_exists
    (realizableUScalar ty) (uScalarBitDecoder ty) rfl raw.val ⟨_, rfl⟩
  refine ⟨bytes, ?_⟩
  change ((uScalarBitDecoder ty).filterMap _).run bytes = _
  rw [BitDecoder.run_filterMap, accepted]
  simp only [Option.bind_some, nonzero, ↓reduceIte]

theorem realizableNonZeroIScalar (ty : IScalarTy) (Inner : Type) :
    RustModel.realizableRepresentation (core.num.nonzero.NonZero (IScalar ty) Inner) := by
  intro raw valid
  have nonzero : raw.val.val ≠ 0 := by
    obtain ⟨value, accepted⟩ := valid
    by_contra zero
    simp [RustModel.decode, zero] at accepted
  obtain ⟨bytes, accepted⟩ := RustModel.realizableRepresentation_exists
    (realizableIScalar ty) (iScalarBitDecoder ty) rfl raw.val ⟨_, rfl⟩
  refine ⟨bytes, ?_⟩
  change ((iScalarBitDecoder ty).filterMap _).run bytes = _
  rw [BitDecoder.run_filterMap, accepted]
  simp only [Option.bind_some, nonzero, ↓reduceIte]

/-- A transparent wrapper reuses its payload's bytes at the same metadata.
Both inverse laws ensure that every admitted wrapper is in the image of wrapping. -/
theorem RustModel.realizable_of_wrapper {A B : Type} [ma : RustModel A] [mb : RustModel B]
    (wrap : A → B) (unwrap : B → A)
    (leftInverse : ∀ raw, unwrap (wrap raw) = raw)
    (rightInverse : ∀ raw, wrap (unwrap raw) = raw)
    (storage : mb.storage = wrapperStorage wrap unwrap leftInverse)
    (validChild : ∀ raw, isValid raw → isValid (unwrap raw))
    (child : RustModel.realizableRepresentation A) :
    RustModel.realizableRepresentation B := by
  cases stored : ma.storage with
  | none => simp [RustModel.realizableRepresentation, stored] at child
  | some physical =>
    simp only [RustModel.realizableRepresentation, stored] at child
    simp only [RustModel.realizableRepresentation, storage, wrapperStorage, stored, Option.map_some]
    cases physical with
    | fixed decoder =>
      intro raw valid
      obtain ⟨bytes, accepted⟩ := child (unwrap raw) (validChild raw valid)
      exact ⟨bytes, by rw [BitDecoder.run_map, accepted]; simp [rightInverse]⟩
    | indexed metadata equality decoder =>
      intro raw valid
      obtain ⟨bytes, accepted⟩ := child (unwrap raw) (validChild raw valid)
      refine ⟨bytes, ?_⟩
      rw [StorageDecoder.run_map]
      simp only [StorageDecoder.map]
      rw [accepted]
      simp [rightInverse]

theorem realizableManuallyDrop (T : Type) [ma : RustModel T]
    (child : RustModel.realizableRepresentation T) :
    RustModel.realizableRepresentation (core.mem.manually_drop.ManuallyDrop T) :=
  RustModel.realizable_of_wrapper _ (·.value) (by intro raw; rfl) (by rintro ⟨raw⟩; rfl) rfl
    (fun _ valid => valid) child

theorem realizableCell (T : Type) [ma : RustModel T]
    (child : RustModel.realizableRepresentation T) :
    RustModel.realizableRepresentation (core.cell.Cell T) :=
  RustModel.realizable_of_wrapper _ (·.value) (by intro raw; rfl) (by rintro ⟨raw⟩; rfl) rfl
    (fun _ valid => valid) child

theorem realizableUnsafeCell (T : Type) [ma : RustModel T]
    (child : RustModel.realizableRepresentation T) :
    RustModel.realizableRepresentation (core.cell.UnsafeCell T) :=
  RustModel.realizable_of_wrapper _ (·.value) (by intro raw; rfl) (by rintro ⟨raw⟩; rfl) rfl
    (fun _ valid => valid) child

theorem realizableWrapping (T : Type) [ma : RustModel T]
    (child : RustModel.realizableRepresentation T) :
    RustModel.realizableRepresentation (Zerocopy.core.num.wrapping.Wrapping T) :=
  RustModel.realizable_of_wrapper _ (·._0) (by intro raw; rfl) (by rintro ⟨raw⟩; rfl) rfl
    (fun _ valid => valid) child

/-- Successful list decoding admits every stored element with the same provider. -/
theorem decodeList_valid {α : Type u} [ma : RustModel α]
    (raws : List α) (values : List ma.Model) (accepted : decodeList ma.decode raws = some values) :
    ∀ raw ∈ raws, isValid raw := by
  induction raws generalizing values with
  | nil => simp
  | cons head tail ih =>
    cases decodedHead : ma.decode head with
    | none => simp [decodeList, decodedHead] at accepted
    | some value =>
      cases decodedTail : decodeList ma.decode tail with
      | none => simp [decodeList, decodedHead, decodedTail] at accepted
      | some values =>
        intro raw member
        rcases List.mem_cons.mp member with same | member
        · subst raw; exact ⟨value, decodedHead⟩
        · exact ih _ decodedTail raw member

/-- Element admission constructs list admission without choosing a default. -/
theorem decodeList_exists {α : Type u} [ma : RustModel α]
    (raws : List α) (valid : ∀ raw ∈ raws, isValid raw) :
    ∃ values, decodeList ma.decode raws = some values := by
  induction raws with
  | nil => exact ⟨[], rfl⟩
  | cons raw raws ih =>
    obtain ⟨value, head⟩ := valid raw (by simp)
    obtain ⟨values, tail⟩ := ih (fun raw member => valid raw (by simp [member]))
    exact ⟨value :: values, by simp [decodeList, head, tail]⟩

theorem RustModel.valid_array {α : Type u} [ma : RustModel α] {n : Usize}
    (raw : Aeneas.Std.Array α n) (valid : ∀ item ∈ raw.val, isValid item) : isValid raw := by
  obtain ⟨values, decoded⟩ := decodeList_exists raw.val valid
  unfold isValid
  dsimp only [RustModel.decode]
  split
  · rename_i rejected
    rw [decoded] at rejected
    contradiction
  · exact ⟨_, rfl⟩

/-- Restricting mathematical admission preserves existing physical witnesses. -/
theorem PhysicalStorage.realizable_mono (physical : PhysicalStorage Raw)
    (source destination : Raw → Prop) (realizable : physical.Realizable source)
    (preserves : ∀ raw, destination raw → source raw) : physical.Realizable destination := by
  cases physical <;> exact fun raw valid => realizable raw (preserves raw valid)

/-- Arrays compose representations of admitted children. Indexed children use
an explicit metadata list, retaining every element boundary even at size zero. -/
theorem PhysicalStorage.realizable_array (physical : PhysicalStorage α) (n : Usize)
    (valid : α → Prop) (realizable : physical.Realizable valid) :
    (physical.array n).Realizable (fun raw => ∀ item ∈ raw.val, valid item) := by
  cases physical with
  | fixed decoder =>
    intro raw all
    obtain ⟨bytes, width, physical⟩ := arrayDecode_realizable decoder valid realizable raw.val all
    refine ⟨bytes, ?_⟩
    rw [BitDecoder.run_map]
    have rawLength : raw.val.length = n.val := raw.property
    have decoded : arrayDecode decoder n.val bytes = some ⟨raw.val, rawLength⟩ := by
      have transport (count : Nat) (h : raw.val.length = count) :
          arrayDecode decoder count bytes = some ⟨raw.val, h⟩ := by
        cases h
        exact physical
      exact transport n.val rawLength
    have fromRaw : Aeneas.Std.Array.from raw.val rawLength = raw :=
      Aeneas.Std.Array.ext _ _ (Aeneas.Std.Array.from_val _ _)
    simp only [rawLength] at width
    simp [BitDecoder.run, arrayDecoder, width, decoded, fromRaw]
  | indexed metadata equality decoder =>
    intro raw all
    obtain ⟨bytes, accepted⟩ := decoder.sequence_realizable valid realizable
      (raw.val.map decoder.metadata) raw.val rfl all
    refine ⟨bytes, ?_⟩
    rw [StorageDecoder.run_map, StorageDecoder.run_restrict]
    simp only [StorageDecoder.map]
    rw [accepted]
    simp only [raw.property, ↓reduceDIte, Option.bind_some, Option.map_some]
    congr 1
    exact Aeneas.Std.Array.ext _ _ (Aeneas.Std.Array.from_val _ _)

/-- Slice realizability retains the raw slice's actual count. Indexed children
compose their own metadata without claiming a nested-DST Rust layout. -/
theorem PhysicalStorage.realizable_slice (physical : PhysicalStorage α)
    (valid : α → Prop) (realizable : physical.Realizable valid) :
    physical.slice.Realizable (fun raw => ∀ item ∈ raw.val, valid item) := by
  cases physical with
  | fixed decoder =>
    intro raw all
    obtain ⟨bytes, accepted⟩ := arrayDecoder_realizable decoder valid realizable raw.val all
    refine ⟨bytes, ?_⟩
    rw [RustModel.sliceStorageDecoder_run]
    dsimp only [RustModel.sliceStorageDecoder]
    have rawCount : raw.val.length = raw.len.val := by simp
    have transport (count : Nat) (h : raw.val.length = count) :
        (arrayDecoder decoder count).run bytes = some ⟨raw.val, h⟩ := by
      cases h
      exact accepted
    rw [transport raw.len.val rawCount]
    simp only [Option.map_some]
    congr 1
    exact Slice.ext _ _ (Slice.from_val _ _)
  | indexed metadata equality decoder =>
    intro raw all
    obtain ⟨bytes, accepted⟩ := decoder.sequence_realizable valid realizable
      (raw.val.map decoder.metadata) raw.val rfl all
    refine ⟨bytes, ?_⟩
    rw [StorageDecoder.run_map, StorageDecoder.run_restrict]
    simp only [StorageDecoder.map]
    rw [accepted]
    simp only [raw.property, ↓reduceDIte, Option.bind_some, Option.map_some]
    congr 1
    exact Slice.ext _ _ (Slice.from_val _ _)

theorem RustModel.realizable_array (α : Type u) [ma : RustModel α] (n : Usize)
    (element : RustModel.realizableRepresentation α) :
    @RustModel.realizableRepresentation (Aeneas.Std.Array α n) (@modelArray α n ma) := by
  cases stored : ma.storage with
  | none => simp [RustModel.realizableRepresentation, stored] at element
  | some physical =>
    simp only [RustModel.realizableRepresentation, RustModel.storage, stored, Option.map_some]
    apply (physical.array n).realizable_mono _ _ (physical.realizable_array n isValid
      (by simpa [RustModel.realizableRepresentation, stored] using element))
    intro raw valid
    obtain ⟨value, accepted⟩ := valid
    dsimp only [RustModel.decode] at accepted
    split at accepted
    · contradiction
    · rename_i values decoded
      exact decodeList_valid raw.val values decoded

/-- Slice admission follows from admission of every stored element. -/
theorem RustModel.valid_slice {α : Type u} [ma : RustModel α]
    (raw : Slice α) (valid : ∀ item ∈ raw.val, isValid item) : isValid raw := by
  obtain ⟨values, decoded⟩ := decodeList_exists raw.val valid
  unfold isValid
  dsimp only [RustModel.decode]
  split
  · rename_i rejected
    rw [decoded] at rejected
    contradiction
  · exact ⟨_, rfl⟩

theorem RustModel.realizable_slice (α : Type u) [ma : RustModel α]
    (element : RustModel.realizableRepresentation α) :
    @RustModel.realizableRepresentation (Slice α) (@modelSlice α ma) := by
  cases stored : ma.storage with
  | none => simp [RustModel.realizableRepresentation, stored] at element
  | some physical =>
    simp only [RustModel.realizableRepresentation, RustModel.storage, stored, Option.map_some]
    apply physical.slice.realizable_mono _ _ (physical.realizable_slice isValid
      (by simpa [RustModel.realizableRepresentation, stored] using element))
    intro raw valid
    obtain ⟨value, accepted⟩ := valid
    dsimp only [RustModel.decode] at accepted
    split at accepted
    · contradiction
    · rename_i values decoded
      exact decodeList_valid raw.val values decoded

end AeneasSpecs
