/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
import Rust.Storage

namespace Rust.Storage.Tests

-- Nonempty arrays preserve element order and byte values.
example : (arrayDecoder boolDecoder 3).run
    [AMByte.init 0, AMByte.init 1, AMByte.init 0] =
    some ⟨[false, true, false], rfl⟩ := by decide

example : (arrayDecoder byteDecoder 3).run
    [AMByte.init 0, AMByte.init 2, AMByte.init 255] =
    some ⟨[0, 2, 255], rfl⟩ := by decide

-- Empty arrays accept no representation bytes, regardless of the element width.
example : (arrayDecoder boolDecoder 0).run [] = some ⟨[], rfl⟩ := by decide
example : (arrayDecoder byteDecoder 0).run [] = some ⟨[], rfl⟩ := by decide
example : (arrayDecoder unitDecoder 0).run [] = some ⟨[], rfl⟩ := by decide
example : (arrayDecoder boolDecoder 0).run [AMByte.init 0] = none := by decide

-- Positive counts of zero-sized elements decode empty chunks repeatedly.
example : (arrayDecoder unitDecoder 3).run [] = some ⟨[(), (), ()], rfl⟩ := by decide
example : (arrayDecoder unitDecoder 3).run [AMByte.init 0] = none := by decide
example : (arrayDecoder unitDecoder 3).decode [AMByte.init 0] = none := by decide

-- The outer width guard rejects both extra and short representations.
example : (arrayDecoder boolDecoder 2).run
    [AMByte.init 0, AMByte.init 1, AMByte.init 0] = none := by decide
example : (arrayDecoder boolDecoder 2).run [AMByte.init 0] = none := by decide

-- The recursive decoder also enforces the final remainder and each chunk's width.
example : (arrayDecoder boolDecoder 2).decode
    [AMByte.init 0, AMByte.init 1, AMByte.init 0] = none := by decide
example : (arrayDecoder boolDecoder 2).decode [AMByte.init 0] = none := by decide

-- A failure in a later element propagates despite earlier success.
example : (arrayDecoder boolDecoder 2).run [AMByte.init 0, AMByte.init 2] = none := by decide
example : (arrayDecoder boolDecoder 2).run [AMByte.init 1, AMByte.uninit] = none := by decide
example : (arrayDecoder byteDecoder 2).run [AMByte.init 255, AMByte.uninit] = none := by decide

-- Initialization is inherited only when an element law is supplied.
example : (arrayDecoder boolDecoder 3).Initialized :=
  arrayDecoder_initialized boolDecoder boolDecoder_initialized 3
example : (arrayDecoder byteDecoder 3).Initialized :=
  arrayDecoder_initialized byteDecoder byteDecoder_initialized 3
example : (arrayDecoder unitDecoder 3).Initialized :=
  arrayDecoder_initialized unitDecoder unitDecoder_initialized 3

-- A decoder may accept an uninitialized byte, but cannot claim the law.
def badDecoder : BitDecoder Unit where
  byteSize := 1
  decode _ := some ()

example : badDecoder.run [AMByte.uninit] = some () := by decide
example : ¬ badDecoder.Initialized := by
  intro h
  have impossible := h [AMByte.uninit] () (by decide)
  simp [Initialized] at impossible

-- The width guard remains effective for deliberately permissive decoders.
example : badDecoder.run [] = none := by decide
example : badDecoder.run [AMByte.uninit, AMByte.uninit] = none := by decide

-- Mapping values retains byte width and initialization for an adapter.
example : (byteDecoder.map (fun byte => byte.toNat)).run [AMByte.init 255] = some 255 := by decide
example : (byteDecoder.map (fun byte => byte.toNat)).Initialized :=
  BitDecoder.map_initialized byteDecoder _ byteDecoder_initialized

-- Integer width and byte order are explicit; the same decoder covers all widths.
example : (integerDecoder 2 .little).run [AMByte.init 0x34, AMByte.init 0x12] =
    some 0x1234 := by decide
example : (integerDecoder 2 .big).run [AMByte.init 0x34, AMByte.init 0x12] =
    some 0x3412 := by decide
example : (integerDecoder 16 .little).run (List.replicate 16 (AMByte.init 255)) =
    some (BitVec.ofNat 128 (2 ^ 128 - 1)) := by decide
example : (integerDecoder 2 .little).run [AMByte.init 0] = none := by decide
example : (integerDecoder 2 .big).run [AMByte.init 0, AMByte.init 0, AMByte.init 0] =
    none := by decide
example : (integerDecoder 2 .little).run [AMByte.init 0, AMByte.uninit] = none := by decide
example : (integerDecoder 2 .big).run [AMByte.uninit, AMByte.init 255] = none := by decide
example (count : Nat) (endian : Rust.Bytes.Endian) :
    (integerDecoder count endian).Initialized := integerDecoder_initialized count endian
example (count : Nat) (endian : Rust.Bytes.Endian) :
    (integerDecoder count endian).run (List.replicate count (AMByte.init 0)) = some 0 :=
  integerDecoder_run_zeros count endian
example (count : Nat) (endian : Rust.Bytes.Endian) (bytes : List AMByte)
    (width : bytes.length = count) (initialized : Initialized bytes) :
    ∃ word, (integerDecoder count endian).run bytes = some word :=
  integerDecoder_complete count endian bytes width initialized

-- A restricted value uses partial mapping; zero remains rejected by that restriction.
def nonzeroWord (word : BitVec 16) : Option { value : BitVec 16 // value ≠ 0 } :=
  if zero : word = 0 then none else some ⟨word, zero⟩

example : ((integerDecoder 2 .little).filterMap nonzeroWord).run
    [AMByte.init 0, AMByte.init 0] = none := by decide
example : ((integerDecoder 2 .little).filterMap nonzeroWord).run
    [AMByte.init 1, AMByte.init 0] = some ⟨1, by decide⟩ := by decide
example : ((integerDecoder 2 .little).filterMap nonzeroWord).Initialized :=
  BitDecoder.filterMap_initialized _ _ (integerDecoder_initialized _ _)

-- For optional nonzero values, zero is a successful decode of the inner `none`.
example : ((integerDecoder 2 .little).map nonzeroWord).run
    [AMByte.init 0, AMByte.init 0] = some none := by decide
example : ((integerDecoder 2 .little).map nonzeroWord).run
    [AMByte.init 1, AMByte.init 0] = some (some ⟨1, by decide⟩) := by decide
example : ((integerDecoder 2 .little).map nonzeroWord).run
    [AMByte.init 0, AMByte.uninit] = none := by decide
example : ((integerDecoder 2 .little).map nonzeroWord).Initialized :=
  BitDecoder.map_initialized _ _ (integerDecoder_initialized _ _)

-- A general decoder may accept uninitialized padding after a valid payload.
def paddedByteDecoder : BitDecoder Rust.Bytes.Byte where
  byteSize := 2
  decode
    | [AMByte.init value, _] => some value
    | _ => none

example : paddedByteDecoder.run [AMByte.init 42, AMByte.uninit] = some 42 := by decide
example : ¬ paddedByteDecoder.Initialized := by
  intro initialized
  have impossible := initialized _ _ (by decide :
    paddedByteDecoder.run [AMByte.init 42, AMByte.uninit] = some 42)
  simp [Initialized] at impossible

-- Empty storage cannot produce a value of an uninhabited type.
inductive Void : Type

def voidDecoder : BitDecoder Void where
  byteSize := 0
  decode _ := none

example (decoder : BitDecoder Void) (bytes : List AMByte) : decoder.run bytes = none := by
  cases result : decoder.run bytes with
  | none => rfl
  | some value => cases value

example : voidDecoder.run [] = none := rfl
example : (arrayDecoder voidDecoder 0).run [] = some ⟨[], rfl⟩ := rfl
example : (arrayDecoder voidDecoder 1).run [] = none := by decide

-- A state-dependent zero-byte type needs evidence of its state even though Unit is inhabited.
def statefulZstDecoder (live : Bool) : BitDecoder { _value : Unit // live = true } where
  byteSize := 0
  decode bytes := if valid : live = true then (emptyDecoder ⟨(), valid⟩).decode bytes else none

example : (statefulZstDecoder true).run [] = some ⟨(), rfl⟩ := by decide
example : (statefulZstDecoder false).run [] = none := by decide
example : (arrayDecoder (statefulZstDecoder false) 0).run [] = some ⟨[], rfl⟩ := by decide
example : (arrayDecoder (statefulZstDecoder false) 1).run [] = none := by decide
example : (emptyDecoder false).run [] = some false := rfl
example : (emptyDecoder false).run [AMByte.uninit] = none := by decide

#print axioms integerDecoder_initialized
#print axioms integerDecoder_complete
#print axioms integerDecoder_value
#print axioms integerDecoder_run_zeros
#print axioms BitDecoder.filterMap_initialized
#print axioms emptyDecoder_initialized

#print axioms arrayDecoder_initialized
#print axioms arrayDecoder_run_length
#print axioms arrayDecoder_output_length

-- Metadata is supplied independently of width, with agreement checked on output.
example : boolDecoder.asStorageDecoder.run () [AMByte.init 1] = some true := by decide
example : boolDecoder.asStorageDecoder.run () [AMByte.init 2] = none := by decide
example (bytes : List AMByte) : byteDecoder.asStorageDecoder.run () bytes = byteDecoder.run bytes :=
  BitDecoder.run_asStorageDecoder _ _

example : (sliceDecoder boolDecoder).run 2 [AMByte.init 1, AMByte.init 0] = some [true, false] := by decide
example : (sliceDecoder boolDecoder).run 1 [AMByte.init 1, AMByte.init 0] = none := by decide
example : (sliceDecoder boolDecoder).run 2 [AMByte.init 1, AMByte.init 2] = none := by decide
example : (sliceDecoder unitDecoder).run 0 [] = some [] := by decide
example : (sliceDecoder unitDecoder).run 3 [] = some [(), (), ()] := by decide
example : (sliceDecoder unitDecoder).run 3 [AMByte.init 0] = none := by decide
example : (sliceDecoder (statefulZstDecoder false)).run 1 [] = none := by decide
example : (sliceDecoder (statefulZstDecoder false)).run 0 [] = some [] := by decide
example : (sliceDecoder boolDecoder).Initialized := sliceDecoder_initialized _ boolDecoder_initialized

-- These synthetic layouts share a padded width for multiple metadata values.
-- The example establishes no Rust representation or ABI for a particular type.
def plateauDecoder : StorageDecoder Nat Nat where
  byteSize count := (count + 3) / 4 * 4
  metadata := id
  decode count _ := some count

example : plateauDecoder.byteSize 1 = plateauDecoder.byteSize 2 := by decide
example : plateauDecoder.run 1 (List.replicate 4 (AMByte.init 0)) = some 1 := by decide
example : plateauDecoder.run 2 (List.replicate 4 (AMByte.init 0)) = some 2 := by decide
example : plateauDecoder.run 2 (List.replicate 3 (AMByte.init 0)) = none := by decide

def wrongMetadataDecoder : StorageDecoder Nat Nat where
  byteSize _ := 0
  metadata := id
  decode _ _ := some 0

example : wrongMetadataDecoder.decode 3 [] = some 0 := rfl
example : wrongMetadataDecoder.run 3 [] = none := by decide
example : wrongMetadataDecoder.run 0 [] = some 0 := by decide

-- Mathematical rejection cannot reduce the independent initialization obligation.
example : ¬ badDecoder.asStorageDecoder.Initialized := by
  intro initialized
  have impossible := initialized () [AMByte.uninit] () (by decide)
  simp [Initialized] at impossible
example : badDecoder.asStorageDecoder.runWith (fun _ => (none : Option Unit)) () [AMByte.uninit] = none := by decide

-- Strong completeness demands a mathematical value as well as a language value.
example : unitDecoder.asStorageDecoder.CompleteWith (fun raw => some raw) := by
  intro metadata bytes width initialized
  cases metadata
  have empty : bytes = [] := List.length_eq_zero_iff.mp width
  subst bytes
  exact ⟨(), rfl⟩
example : ¬ unitDecoder.asStorageDecoder.CompleteWith (fun _ => (none : Option Unit)) := by
  intro complete
  obtain ⟨value, accepted⟩ := complete () [] rfl initialized_nil
  simp [StorageDecoder.runWith] at accepted

#print axioms StorageDecoder.run_eq_some_iff
#print axioms sliceDecoder_initialized
#print axioms StorageDecoder.completeWith_iff

-- Every represented initialized 32-bit word admits a four-byte array model.
-- This tests the owned byte-cast law without introducing an encoder authority.
theorem fourBytes_complete : (arrayDecoder byteDecoder 4).asStorageDecoder.CompleteWith some := by
  intro metadata bytes width initialized
  cases metadata
  obtain ⟨values, accepted⟩ := arrayDecoder_complete byteDecoder byteDecoder_complete 4 bytes width initialized
  exact ⟨values, by simpa [StorageDecoder.runWith] using accepted⟩

example (bytes : List AMByte) (word : BitVec 32)
    (accepted : (integerDecoder 4 .little).run bytes = some word) :
    ∃ values, (arrayDecoder byteDecoder 4).asStorageDecoder.runWith some () bytes = some values :=
  StorageDecoder.cast_complete (integerDecoder 4 .little).asStorageDecoder
    (arrayDecoder byteDecoder 4).asStorageDecoder some
    (BitDecoder.asStorageDecoder_initialized _ (integerDecoder_initialized _ _))
    fourBytes_complete () () bytes word (by simpa using accepted) rfl

example : (integerDecoder 4 .little).asStorageDecoder.run ()
    [AMByte.init 2, AMByte.init 0, AMByte.init 0, AMByte.init 0] = some 2 := by decide
example : (arrayDecoder byteDecoder 4).asStorageDecoder.runWith some ()
    [AMByte.init 2, AMByte.init 0, AMByte.init 0, AMByte.init 0] = some ⟨[2, 0, 0, 0], rfl⟩ := by decide

-- Equal width and initialized source storage cannot replace destination completeness.
example : (integerDecoder 1 .little).asStorageDecoder.run () [AMByte.init 2] = some 2 := by decide
example : boolDecoder.asStorageDecoder.runWith some () [AMByte.init 2] = none := by decide
example : ¬ boolDecoder.asStorageDecoder.CompleteWith some := by
  intro complete
  obtain ⟨value, accepted⟩ := complete () [AMByte.init 2] rfl (by simp [Initialized])
  have invalid : boolDecoder.asStorageDecoder.runWith some () [AMByte.init 2] = none := by decide
  rw [invalid] at accepted
  contradiction

#print axioms arrayDecoder_complete
#print axioms StorageDecoder.cast_complete

end Rust.Storage.Tests
