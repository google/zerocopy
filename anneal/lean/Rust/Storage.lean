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
This module describes numeric byte initialization and fixed-size or metadata-indexed
decoding as pure values. Numeric bytes do not encode pointer provenance.
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

/-- Every initialized one-byte representation has a byte value. -/
theorem byteDecoder_complete (bytes : List AMByte) (width : bytes.length = 1)
    (initialized : Initialized bytes) : ∃ byte, byteDecoder.run bytes = some byte := by
  cases bytes with
  | nil => simp at width
  | cons byte bytes =>
    cases bytes with
    | cons _ _ => simp at width
    | nil =>
      cases byte with
      | uninit => simp [Initialized] at initialized
      | init byte => exact ⟨byte, rfl⟩

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

/-- Fixed array completeness follows from completeness of every element.
Only fully initialized inputs are covered; the proof never fills missing bytes. -/
theorem arrayDecoder_complete (element : BitDecoder Raw)
    (complete : ∀ bytes, bytes.length = element.byteSize → Initialized bytes →
      ∃ raw, element.run bytes = some raw)
    (n : Nat) (bytes : List AMByte) (width : bytes.length = n * element.byteSize)
    (initialized : Initialized bytes) : ∃ values, (arrayDecoder element n).run bytes = some values := by
  induction n generalizing bytes with
  | zero =>
    have empty : bytes = [] := List.length_eq_zero_iff.mp (by simpa using width)
    subst bytes
    exact ⟨⟨[], rfl⟩, by simp [BitDecoder.run, arrayDecoder, arrayDecode]⟩
  | succ n ih =>
    have sizeBound : element.byteSize ≤ bytes.length := by
      rw [Nat.succ_mul] at width
      omega
    have headWidth : (bytes.take element.byteSize).length = element.byteSize := by
      simp [List.length_take, Nat.min_eq_left sizeBound]
    have tailWidth : (bytes.drop element.byteSize).length = n * element.byteSize := by
      simp only [List.length_drop]
      rw [Nat.succ_mul] at width
      omega
    have both : Initialized (bytes.take element.byteSize ++ bytes.drop element.byteSize) := by
      simpa using initialized
    obtain ⟨head, acceptedHead⟩ := complete _ headWidth ((initialized_append _ _).mp both).1
    obtain ⟨tail, acceptedTail⟩ := ih _ tailWidth ((initialized_append _ _).mp both).2
    have tailDecode : arrayDecode element n (bytes.drop element.byteSize) = some tail := by
      simpa [BitDecoder.run, arrayDecoder, tailWidth] using acceptedTail
    exact ⟨⟨head :: tail.val, by simp [tail.property]⟩,
      by
        simp only [BitDecoder.run, arrayDecoder]
        rw [if_pos width]
        simp only [arrayDecode, acceptedHead, tailDecode]
        rfl⟩

/-- A physical decoder at explicit metadata. `metadata` observes the decoded raw
value; `run` checks that observation against the requested metadata. Size need
not identify metadata: zero-sized slices and padded layouts may share a width.
These numeric bytes do not represent pointer provenance or pointer validity. -/
structure StorageDecoder (Metadata : Type v) (Raw : Type u) where
  byteSize : Metadata → Nat
  metadata : Raw → Metadata
  decode : Metadata → List AMByte → Option Raw

namespace StorageDecoder

/-- Width and returned metadata are checked before a decoded value is exposed. -/
def run [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (metadata : Metadata) (bytes : List AMByte) : Option Raw :=
  if bytes.length = decoder.byteSize metadata then do
    let raw ← decoder.decode metadata bytes
    if decoder.metadata raw = metadata then some raw else none
  else none

/-- The complete successful-run contract, including the underlying decode. -/
theorem run_eq_some_iff [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (metadata : Metadata) (bytes : List AMByte) (raw : Raw) :
    decoder.run metadata bytes = some raw ↔
      bytes.length = decoder.byteSize metadata ∧
      decoder.decode metadata bytes = some raw ∧ decoder.metadata raw = metadata := by
  by_cases width : bytes.length = decoder.byteSize metadata
  · cases decoded : decoder.decode metadata bytes with
    | none => simp [run, width, decoded]
    | some value =>
      by_cases agrees : decoder.metadata value = metadata
      · simp [run, width, decoded, agrees]
        intro equality
        subst raw
        exact agrees
      · simp [run, width, decoded, agrees]
        intro equality
        subst raw
        exact agrees
  · simp [run, width]

/-- Accepted representations have exactly the requested layout size. -/
theorem run_length [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (metadata : Metadata) (bytes : List AMByte) (raw : Raw)
    (accepted : decoder.run metadata bytes = some raw) :
    bytes.length = decoder.byteSize metadata :=
  ((decoder.run_eq_some_iff metadata bytes raw).mp accepted).1

/-- Returned metadata cannot disagree even when widths coincide. -/
theorem run_metadata [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (metadata : Metadata) (bytes : List AMByte) (raw : Raw)
    (accepted : decoder.run metadata bytes = some raw) : decoder.metadata raw = metadata :=
  ((decoder.run_eq_some_iff metadata bytes raw).mp accepted).2.2

/-- Every language-valid representation is initialized, independently of any
mathematical decoder. This is the representation obligation used by IntoBytes. -/
def Initialized [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw) : Prop :=
  ∀ metadata bytes raw, decoder.run metadata bytes = some raw → Rust.Storage.Initialized bytes

/-- Compose language validity with a mathematical decoder, retaining both failures. -/
def runWith [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) (metadata : Metadata) (bytes : List AMByte) : Option Model :=
  (decoder.run metadata bytes).bind decodeModel

theorem runWith_eq_some_iff [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) (metadata : Metadata) (bytes : List AMByte) (value : Model) :
    decoder.runWith decodeModel metadata bytes = some value ↔
      ∃ raw, decoder.run metadata bytes = some raw ∧ decodeModel raw = some value := by
  cases decoded : decoder.run metadata bytes <;> simp [runWith, decoded]

/-- Every initialized representation of the requested width admits both a
language value and a mathematical value. This is stronger than language-only
completeness; supplying it does not establish the other FromBytes clauses. -/
def CompleteWith [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) : Prop :=
  ∀ metadata bytes, bytes.length = decoder.byteSize metadata → Rust.Storage.Initialized bytes →
    ∃ value, decoder.runWith decodeModel metadata bytes = some value

theorem completeWith_iff [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) : decoder.CompleteWith decodeModel ↔
      ∀ metadata bytes, bytes.length = decoder.byteSize metadata → Rust.Storage.Initialized bytes →
        ∃ raw value, decoder.run metadata bytes = some raw ∧ decodeModel raw = some value := by
  simp only [CompleteWith, runWith_eq_some_iff]
  constructor
  · intro h metadata bytes width initialized
    obtain ⟨value, raw, language, model⟩ := h metadata bytes width initialized
    exact ⟨raw, value, language, model⟩
  · intro h metadata bytes width initialized
    obtain ⟨raw, value, language, model⟩ := h metadata bytes width initialized
    exact ⟨value, raw, language, model⟩

/-- Owned byte-cast admission over an arbitrary represented byte list. Source
initialization and destination completeness compose at equal requested widths;
no source encoder or physical Rust transmute correspondence is assumed. -/
theorem cast_complete [DecidableEq SourceMetadata] [DecidableEq Metadata]
    (source : StorageDecoder SourceMetadata SourceRaw) (destination : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) (sourceInitialized : source.Initialized)
    (destinationComplete : destination.CompleteWith decodeModel)
    (sourceMetadata : SourceMetadata) (metadata : Metadata) (bytes : List AMByte) (raw : SourceRaw)
    (accepted : source.run sourceMetadata bytes = some raw)
    (sameWidth : source.byteSize sourceMetadata = destination.byteSize metadata) :
    ∃ value, destination.runWith decodeModel metadata bytes = some value :=
  destinationComplete metadata bytes
    ((source.run_length sourceMetadata bytes raw accepted).trans sameWidth)
    (sourceInitialized sourceMetadata bytes raw accepted)

/-- Adapt raw values while explicitly preserving their metadata observation. -/
def map (decoder : StorageDecoder Metadata Raw) (f : Raw → Other)
    (metadataOther : Other → Metadata)
    (_preserves : ∀ raw, metadataOther (f raw) = decoder.metadata raw) : StorageDecoder Metadata Other where
  byteSize := decoder.byteSize
  metadata := metadataOther
  decode metadata bytes := (decoder.decode metadata bytes).map f

@[simp] theorem run_map [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (f : Raw → Other) (metadataOther : Other → Metadata)
    (preserves : ∀ raw, metadataOther (f raw) = decoder.metadata raw)
    (metadata : Metadata) (bytes : List AMByte) :
    (decoder.map f metadataOther preserves).run metadata bytes =
      (decoder.run metadata bytes).map f := by
  unfold run map
  split
  · cases decoded : decoder.decode metadata bytes <;> simp [decoded, preserves]
  · rfl

theorem map_initialized [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (f : Raw → Other) (metadataOther : Other → Metadata)
    (preserves : ∀ raw, metadataOther (f raw) = decoder.metadata raw)
    (initialized : decoder.Initialized) : (decoder.map f metadataOther preserves).Initialized := by
  intro metadata bytes value accepted
  rw [run_map] at accepted
  cases language : decoder.run metadata bytes with
  | none => simp [language] at accepted
  | some raw => exact initialized metadata bytes raw language

end StorageDecoder

/-- Fixed-width decoding is the Unit-metadata case, with no metadata inferred
from bytes. The compatibility API uses the same width guard and validity domain. -/
def BitDecoder.asStorageDecoder (decoder : BitDecoder Raw) : StorageDecoder Unit Raw where
  byteSize _ := decoder.byteSize
  metadata _ := ()
  decode _ := decoder.decode

@[simp] theorem BitDecoder.run_asStorageDecoder (decoder : BitDecoder Raw) (bytes : List AMByte) :
    decoder.asStorageDecoder.run () bytes = decoder.run bytes := by
  simp only [asStorageDecoder, StorageDecoder.run, run]
  split
  · cases decoder.decode bytes <;> rfl
  · rfl

theorem BitDecoder.asStorageDecoder_initialized (decoder : BitDecoder Raw)
    (initialized : decoder.Initialized) : decoder.asStorageDecoder.Initialized := by
  intro metadata bytes raw accepted
  cases metadata
  exact initialized bytes raw (by simpa using accepted)

/-- A slice's element count is explicit metadata. Chunk decoding reuses array
recursion, including for zero-sized elements, and returns the same count. -/
def sliceDecoder (element : BitDecoder Raw) : StorageDecoder Nat (List Raw) where
  byteSize count := count * element.byteSize
  metadata := List.length
  decode count bytes := (arrayDecode element count bytes).map Subtype.val

@[simp] theorem sliceDecoder_run (element : BitDecoder Raw) (count : Nat) (bytes : List AMByte) :
    (sliceDecoder element).run count bytes = ((arrayDecoder element count).run bytes).map Subtype.val := by
  simp only [StorageDecoder.run, sliceDecoder, BitDecoder.run, arrayDecoder]
  split
  · cases decoded : arrayDecode element count bytes with
    | none => rfl
    | some values => simp [values.property]
  · rfl

theorem sliceDecoder_initialized (element : BitDecoder Raw) (initialized : element.Initialized) :
    (sliceDecoder element).Initialized := by
  intro count bytes raw accepted
  rw [sliceDecoder_run] at accepted
  cases language : (arrayDecoder element count).run bytes with
  | none => simp [language] at accepted
  | some values => exact arrayDecoder_initialized element initialized count bytes values language

end Rust.Storage
