/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Rust.Bytes
@[expose] public section

/-!
This module describes byte initialization and fixed-size decoding as pure values.
A successful decoder run must have the specified width. Initialization is a
separate law: a decoder may accept uninitialized bytes, but then cannot satisfy
`BitDecoder.Initialized`.

Array decoding applies the element decoder to consecutive, equal-size chunks.
Recursion counts elements, so zero-length arrays and zero-sized elements need no
special size arithmetic. For a Rust array interpretation, the consumer must
justify the Rust Reference layout bridge: array size is `n * size(T)`, alignment
is that of `T`, and element `k` starts at `k * size(T)`, with no inter-element
padding. Element padding is initialized only when the element's law proves it.
These mathematical laws alone do not prove a physical Rust implementation.
-/

namespace Rust.Storage

/-- An abstract-machine byte may lack an initialized value. -/
inductive AMByte where
  | uninit
  | init (byte : Rust.Bytes.Byte)
  deriving DecidableEq, Repr

/-- Every byte has an initialized value, including any element padding. -/
def Initialized (bytes : List AMByte) : Prop :=
  ∀ byte ∈ bytes, ∃ value, byte = AMByte.init value

@[simp] theorem initialized_nil : Initialized [] := by
  simp [Initialized]

@[simp] theorem initialized_cons (byte : AMByte) (bytes : List AMByte) :
    Initialized (byte :: bytes) ↔ (∃ value, byte = AMByte.init value) ∧ Initialized bytes := by
  simp [Initialized]

@[simp] theorem initialized_append (left right : List AMByte) :
    Initialized (left ++ right) ↔ Initialized left ∧ Initialized right := by
  simp [Initialized, or_imp, forall_and]

/-- Collect byte values, rejecting the entire representation if any byte is uninitialized. -/
def collectInitialized : List AMByte → Option (List Rust.Bytes.Byte)
  | [] => some []
  | AMByte.uninit :: _ => none
  | AMByte.init byte :: rest => (collectInitialized rest).map (byte :: ·)

/-- Collection loses neither positions nor byte values. -/
theorem collectInitialized_eq_some_iff (bytes : List AMByte) (values : List Rust.Bytes.Byte) :
    collectInitialized bytes = some values ↔ bytes = values.map AMByte.init := by
  induction bytes generalizing values with
  | nil => cases values <;> simp [collectInitialized]
  | cons byte rest ih =>
    cases byte with
    | uninit => cases values <;> simp [collectInitialized]
    | init byte =>
      cases values with
      | nil => simp [collectInitialized]
      | cons value values =>
        cases h : collectInitialized rest with
        | none => simp [collectInitialized, ← ih, h]
        | some tail => simp [collectInitialized, ← ih, h]

@[simp] theorem collectInitialized_map (values : List Rust.Bytes.Byte) :
    collectInitialized (values.map AMByte.init) = some values :=
  (collectInitialized_eq_some_iff _ _).mpr rfl

theorem collectInitialized_length (bytes : List AMByte) (values : List Rust.Bytes.Byte)
    (h : collectInitialized bytes = some values) : values.length = bytes.length := by
  rw [(collectInitialized_eq_some_iff _ _).mp h, List.length_map]

/-- Exactly the fully initialized representations can be collected. -/
theorem collectInitialized_complete (bytes : List AMByte) :
    (∃ values, collectInitialized bytes = some values) ↔ Initialized bytes := by
  induction bytes with
  | nil => simp [collectInitialized]
  | cons byte rest ih =>
    cases byte with
    | uninit => simp [collectInitialized]
    | init byte =>
      simp only [initialized_cons, AMByte.init.injEq, exists_eq', true_and]
      constructor
      · rintro ⟨values, h⟩
        cases tail : collectInitialized rest with
        | none => simp [collectInitialized, tail] at h
        | some values => exact ih.mp ⟨values, tail⟩
      · intro initialized
        obtain ⟨values, h⟩ := ih.mpr initialized
        exact ⟨byte :: values, by simp [collectInitialized, h]⟩

/-- Decoding behavior and its fixed representation width; validity laws are separate. -/
structure BitDecoder (Raw : Type u) where
  byteSize : Nat
  decode : List AMByte → Option Raw

namespace BitDecoder

/-- Reject a width mismatch before invoking the decoder. -/
def run (decoder : BitDecoder Raw) (bytes : List AMByte) : Option Raw :=
  if bytes.length = decoder.byteSize then decoder.decode bytes else none

/-- Successful decoding requires every representation byte to be initialized. -/
def Initialized (decoder : BitDecoder Raw) : Prop :=
  ∀ bytes raw, decoder.run bytes = some raw → Rust.Storage.Initialized bytes

/-- Every successful run has the decoder's specified width. -/
theorem run_length (decoder : BitDecoder Raw) (bytes : List AMByte) (raw : Raw)
    (h : decoder.run bytes = some raw) : bytes.length = decoder.byteSize := by
  by_cases width : bytes.length = decoder.byteSize
  · exact width
  · simp [run, width] at h

/-- Width mismatches fail even if `decode` itself would accept them. -/
theorem run_eq_none_of_length_ne (decoder : BitDecoder Raw) (bytes : List AMByte)
    (h : bytes.length ≠ decoder.byteSize) : decoder.run bytes = none := by
  simp [run, h]

/-- Change decoded values while retaining the same accepted byte representations. -/
def map (decoder : BitDecoder Raw) (f : Raw → Other) : BitDecoder Other where
  byteSize := decoder.byteSize
  decode bytes := (decoder.decode bytes).map f

@[simp] theorem run_map (decoder : BitDecoder Raw) (f : Raw → Other) (bytes : List AMByte) :
    (decoder.map f).run bytes = (decoder.run bytes).map f := by
  simp only [map, run]
  split <;> rfl

/-- Mapping decoded values preserves the initialization law. -/
theorem map_initialized (decoder : BitDecoder Raw) (f : Raw → Other)
    (h : decoder.Initialized) : (decoder.map f).Initialized := by
  intro bytes raw accepted
  rw [run_map] at accepted
  cases result : decoder.run bytes with
  | none => simp [result] at accepted
  | some value => exact h bytes value result

/-- A validity check may reject a decoded value, while preserving outer decoding failures. -/
def filterMap (decoder : BitDecoder Raw) (f : Raw → Option Other) : BitDecoder Other where
  byteSize := decoder.byteSize
  decode bytes := (decoder.decode bytes).bind f

@[simp] theorem run_filterMap (decoder : BitDecoder Raw) (f : Raw → Option Other)
    (bytes : List AMByte) :
    (decoder.filterMap f).run bytes = (decoder.run bytes).bind f := by
  simp only [filterMap, run]
  split <;> rfl

/-- Rejecting some values cannot introduce representations with uninitialized bytes. -/
theorem filterMap_initialized (decoder : BitDecoder Raw) (f : Raw → Option Other)
    (h : decoder.Initialized) : (decoder.filterMap f).Initialized := by
  intro bytes raw accepted
  rw [run_filterMap] at accepted
  cases result : decoder.run bytes with
  | none => simp [result] at accepted
  | some value => exact h bytes value result

end BitDecoder

/-- Decode every fully initialized integer representation at an explicit width and byte order.
The carrier is unsigned bits; signed and restricted values use value adapters. Width and
endianness are mathematical inputs, whose correspondence to Rust needs separate evidence. -/
def integerDecoder (byteSize : Nat) (endian : Rust.Bytes.Endian) :
    BitDecoder (BitVec (8 * byteSize)) where
  byteSize := byteSize
  decode bytes := (collectInitialized bytes).map (fun values =>
    BitVec.ofNat (8 * byteSize) (Rust.Bytes.decode endian values))

theorem integerDecoder_initialized (byteSize : Nat) (endian : Rust.Bytes.Endian) :
    (integerDecoder byteSize endian).Initialized := by
  intro bytes word accepted
  have width := BitDecoder.run_length _ _ _ accepted
  simp only [BitDecoder.run, width, ↓reduceIte, integerDecoder] at accepted
  cases collected : collectInitialized bytes with
  | none => simp [collected] at accepted
  | some values => exact (collectInitialized_complete bytes).mp ⟨values, collected⟩

/-- Every initialized representation of the specified width has an integer value. -/
theorem integerDecoder_complete (byteSize : Nat) (endian : Rust.Bytes.Endian)
    (bytes : List AMByte) (width : bytes.length = byteSize) (initialized : Initialized bytes) :
    ∃ word, (integerDecoder byteSize endian).run bytes = some word := by
  obtain ⟨values, collected⟩ := (collectInitialized_complete bytes).mpr initialized
  exact ⟨BitVec.ofNat (8 * byteSize) (Rust.Bytes.decode endian values),
    by simp [BitDecoder.run, integerDecoder, width, collected]⟩

/-- Once the width guard holds, integer decoding preserves the exact digit value.
The byte bound proves that the fixed-width carrier does not truncate that value. -/
theorem integerDecoder_run_map (byteSize : Nat) (endian : Rust.Bytes.Endian)
    (values : List Rust.Bytes.Byte) (width : values.length = byteSize) :
    (integerDecoder byteSize endian).run (values.map AMByte.init) =
      some (BitVec.ofNat (8 * byteSize) (Rust.Bytes.decode endian values)) := by
  simp [BitDecoder.run, integerDecoder, width]

theorem integerDecoder_value (byteSize : Nat) (endian : Rust.Bytes.Endian)
    (values : List Rust.Bytes.Byte) (width : values.length = byteSize) :
    (BitVec.ofNat (8 * byteSize) (Rust.Bytes.decode endian values)).toNat =
      Rust.Bytes.decode endian values := by
  have bound := Rust.Bytes.decode_lt endian values
  rw [width] at bound
  exact Nat.mod_eq_of_lt bound

@[simp] theorem integerDecoder_run_zeros (byteSize : Nat) (endian : Rust.Bytes.Endian) :
    (integerDecoder byteSize endian).run (List.replicate byteSize (AMByte.init 0)) =
      some (0 : BitVec (8 * byteSize)) := by
  have h := integerDecoder_run_map byteSize endian (List.replicate byteSize 0) (by simp)
  rw [Rust.Bytes.decode_replicate_zero] at h
  simpa only [List.map_replicate, BitVec.ofNat_eq_ofNat] using h

/-- A zero-byte representation requires an explicit value. Size zero or an `Inhabited`
instance alone does not justify a Rust value or any state that its validity requires. -/
def emptyDecoder (value : Raw) : BitDecoder Raw where
  byteSize := 0
  decode
    | [] => some value
    | _ => none

@[simp] theorem emptyDecoder_run_nil (value : Raw) : (emptyDecoder value).run [] = some value := rfl

theorem emptyDecoder_initialized (value : Raw) : (emptyDecoder value).Initialized := by
  intro bytes raw accepted
  have width := BitDecoder.run_length _ _ _ accepted
  have empty : bytes = [] := List.length_eq_zero_iff.mp width
  simp [empty]

/-- The supplied value makes empty storage complete; no representation bytes create it. -/
theorem emptyDecoder_complete (value : Raw) (bytes : List AMByte)
    (width : bytes.length = 0) : (emptyDecoder value).run bytes = some value := by
  have empty := List.length_eq_zero_iff.mp width
  simp [empty]

/-- Rust booleans accept exactly the initialized bytes zero and one. -/
def boolDecoder : BitDecoder Bool where
  byteSize := 1
  decode
    | [AMByte.init byte] =>
      if byte = 0 then some false else if byte = 1 then some true else none
    | _ => none

/-- Every initialized eight-bit value is a valid byte. -/
def byteDecoder : BitDecoder Rust.Bytes.Byte where
  byteSize := 1
  decode
    | [AMByte.init byte] => some byte
    | _ => none

/-- Unit occupies no bytes. -/
def unitDecoder : BitDecoder Unit := emptyDecoder ()

theorem boolDecoder_initialized : boolDecoder.Initialized := by
  intro bytes raw h
  have width := BitDecoder.run_length boolDecoder bytes raw h
  cases bytes with
  | nil => simp [boolDecoder] at width
  | cons byte bytes =>
    cases bytes with
    | cons _ _ => simp [boolDecoder] at width
    | nil =>
      cases byte with
      | uninit => simp [BitDecoder.run, boolDecoder] at h
      | init value => simp [Initialized]

theorem byteDecoder_initialized : byteDecoder.Initialized := by
  intro bytes raw h
  have width := BitDecoder.run_length byteDecoder bytes raw h
  cases bytes with
  | nil => simp [byteDecoder] at width
  | cons byte bytes =>
    cases bytes with
    | cons _ _ => simp [byteDecoder] at width
    | nil =>
      cases byte with
      | uninit => simp [BitDecoder.run, byteDecoder] at h
      | init value => simp [Initialized]

theorem unitDecoder_initialized : unitDecoder.Initialized := by
  intro bytes raw h
  have width := BitDecoder.run_length unitDecoder bytes raw h
  have empty : bytes = [] := List.length_eq_zero_iff.mp width
  simp [empty]

@[simp] theorem boolDecoder_run_zero : boolDecoder.run [AMByte.init 0] = some false := by
  decide

@[simp] theorem boolDecoder_run_one : boolDecoder.run [AMByte.init 1] = some true := by
  decide

@[simp] theorem boolDecoder_run_two : boolDecoder.run [AMByte.init 2] = none := by
  decide

@[simp] theorem boolDecoder_run_uninit : boolDecoder.run [AMByte.uninit] = none := by
  decide

@[simp] theorem byteDecoder_run_init (byte : Rust.Bytes.Byte) :
    byteDecoder.run [AMByte.init byte] = some byte := by
  simp [BitDecoder.run, byteDecoder]

@[simp] theorem byteDecoder_run_uninit : byteDecoder.run [AMByte.uninit] = none := by
  decide

@[simp] theorem unitDecoder_run_nil : unitDecoder.run [] = some () := by
  decide

/-- Consume exactly `n` chunks, requiring the final remainder to be empty. -/
def arrayDecode (element : BitDecoder Raw) :
    (n : Nat) → List AMByte → Option { values : List Raw // values.length = n }
  | 0, bytes => if bytes = [] then some ⟨[], rfl⟩ else none
  | n + 1, bytes => do
      let value ← element.run (bytes.take element.byteSize)
      let values ← arrayDecode element n (bytes.drop element.byteSize)
      return ⟨value :: values.val, by simp [values.property]⟩

/-- Decode an array from contiguous element representations. -/
def arrayDecoder (element : BitDecoder Raw) (n : Nat) :
    BitDecoder { values : List Raw // values.length = n } where
  byteSize := n * element.byteSize
  decode := arrayDecode element n

theorem arrayDecode_initialized (element : BitDecoder Raw)
    (he : element.Initialized) (n : Nat) (bytes : List AMByte)
    (values : { values : List Raw // values.length = n })
    (h : arrayDecode element n bytes = some values) : Initialized bytes := by
  induction n generalizing bytes with
  | zero =>
    simp only [arrayDecode] at h
    split at h
    · rename_i empty
      simp [empty]
    · contradiction
  | succ n ih =>
    simp only [arrayDecode] at h
    cases first : element.run (bytes.take element.byteSize) with
    | none => simp [first] at h
    | some value =>
      cases rest : arrayDecode element n (bytes.drop element.byteSize) with
      | none => simp [first, rest] at h
      | some tail =>
        have head_initialized := he _ _ first
        have tail_initialized := ih _ tail rest
        have both : Initialized (bytes.take element.byteSize ++ bytes.drop element.byteSize) :=
          (initialized_append _ _).mpr ⟨head_initialized, tail_initialized⟩
        simpa using both

/-- Arrays inherit initialization from the accepted element representations. -/
theorem arrayDecoder_initialized (element : BitDecoder Raw)
    (he : element.Initialized) (n : Nat) : (arrayDecoder element n).Initialized := by
  intro bytes values h
  have width := BitDecoder.run_length (arrayDecoder element n) bytes values h
  simp only [BitDecoder.run, width, ↓reduceIte, arrayDecoder] at h
  exact arrayDecode_initialized element he n bytes values h

/-- A successful array run consumes exactly its total representation width. -/
theorem arrayDecoder_run_length (element : BitDecoder Raw) (n : Nat)
    (bytes : List AMByte) (values : { values : List Raw // values.length = n })
    (h : (arrayDecoder element n).run bytes = some values) :
    bytes.length = n * element.byteSize :=
  BitDecoder.run_length (arrayDecoder element n) bytes values h

/-- The decoder's output carries the required number of elements. -/
theorem arrayDecoder_output_length (element : BitDecoder Raw) (n : Nat)
    (bytes : List AMByte) (values : { values : List Raw // values.length = n })
    (_h : (arrayDecoder element n).run bytes = some values) : values.val.length = n :=
  values.property

end Rust.Storage
