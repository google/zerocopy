/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import TransmuteModel
@[expose] public section
open Aeneas.Std Rust.Storage AeneasSpecs
namespace TransmuteModelTests

-- One raw value has many byte representations. No encoder can designate one
-- of them as the only behavior of a byte-observing cast.
@[reducible] def ambiguousSource : RustModel Unit where
  Model := Unit
  decode := some
  storage := some (.fixed (byteDecoder.map fun _ => ()))

@[reducible] def byteDestination : RustModel Rust.Bytes.Byte where
  Model := Rust.Bytes.Byte
  decode := some
  storage := some (.fixed byteDecoder)

theorem ambiguous_source_initialized : @RustModel.initializedRepresentation Unit ambiguousSource :=
  BitDecoder.map_initialized _ _ byteDecoder_initialized

theorem ambiguous_source_realizable : @RustModel.realizableRepresentation Unit ambiguousSource := by
  intro raw _
  cases raw
  exact ⟨[.init 0], rfl⟩

theorem byte_destination_complete :
    @RustModel.completeRepresentation Rust.Bytes.Byte byteDestination := by
  intro bytes width initialized
  obtain ⟨byte, accepted⟩ := byteDecoder_complete bytes width initialized
  exact ⟨byte, byte, accepted, rfl⟩

-- Both outcomes are included while the mathematical and physical decoders stay fixed.
theorem chooses_zero :
    (ambiguousSource.withChoice (fun _ => [.init 0])).transmuteCopyResult byteDestination () =
      .ok 0 := by
  exact RustModel.transmuteCopyResult_covers ambiguousSource byteDestination ()
    _ _ rfl rfl rfl [.init 0] 0 0 rfl rfl rfl

theorem chooses_one :
    (ambiguousSource.withChoice (fun _ => [.init 1])).transmuteCopyResult byteDestination () =
      .ok 1 := by
  exact RustModel.transmuteCopyResult_covers ambiguousSource byteDestination ()
    _ _ rfl rfl rfl [.init 1] 1 1 rfl rfl rfl

example : (0 : Rust.Bytes.Byte) ≠ 1 := by decide

-- Every preference succeeds, including an invalid empty preference; this does
-- not identify the fallback witness with either of the two demonstrated choices.
example (choose : Unit → List AMByte) :
    ∃ dst value,
      (ambiguousSource.withChoice choose).transmuteCopyResult byteDestination () = .ok dst ∧
      byteDestination.decode dst = some value ∧
      (ambiguousSource.withChoice choose).byteCastWith byteDestination () dst := by
  exact RustModel.transmuteCopyResult_admitted _ _ () ambiguous_source_initialized
    ambiguous_source_realizable byte_destination_complete rfl ⟨(), rfl⟩

@[reducible] def rejectsAllSource : RustModel Unit where
  Model := Unit
  decode := some
  storage := some (.fixed { byteSize := 1, decode := fun _ => none })

example : @RustModel.initializedRepresentation Unit rejectsAllSource := by
  intro bytes raw accepted
  simp [BitDecoder.run] at accepted

example : ¬ @RustModel.realizableRepresentation Unit rejectsAllSource := by
  intro realizable
  obtain ⟨bytes, accepted⟩ := realizable () ⟨(), rfl⟩
  simp [BitDecoder.run] at accepted

example : rejectsAllSource.transmuteCopyResult byteDestination () = .fail .undef := by
  have hs : rejectsAllSource.representation = some { byteSize := 1, decode := fun _ => none } := rfl
  have hd : byteDestination.representation = some byteDecoder := rfl
  have impossible (bytes : List AMByte) : ¬ rejectsAllSource.represented () bytes := by
    simp [RustModel.represented, hs, BitDecoder.run]
  have selected : rejectsAllSource.selectedBytes () = .fail .undef := by
    simp [RustModel.selectedBytes, impossible]
  simp [RustModel.transmuteCopyResult, hs, hd, selected, byteDecoder]

-- Empty Rust types require no invented value and no global Inhabited premise.
@[reducible] def emptySource : RustModel Empty where
  Model := Empty
  decode raw := nomatch raw
  storage := some (.fixed { byteSize := 0, decode := fun _ => none })

example : @RustModel.realizableRepresentation Empty emptySource := by
  intro raw
  exact nomatch raw

example : @RustModel.initializedRepresentation Empty emptySource := by
  intro bytes raw
  exact nomatch raw

example : ¬ @RustModel.completeRepresentation Empty emptySource := by
  intro complete
  obtain ⟨raw, _, _, _⟩ := complete [] rfl (by simp)
  exact nomatch raw

-- Destination language validity is checked even when a caller asks only True.
@[reducible] def boolDestination : RustModel Bool where
  Model := Bool
  decode := some
  storage := some (.fixed boolDecoder)

theorem rejects_invalid_bool :
    (ambiguousSource.withChoice (fun _ => [.init 2])).transmuteCopyResult boolDestination () =
      .fail .undef := by
  apply RustModel.transmuteCopyResult_rejects_physical
    (ambiguousSource.withChoice (fun _ => [.init 2])) boolDestination () _ _ rfl rfl rfl [.init 2]
  · exact ambiguousSource.selectedBytes_withChoice () [.init 2] (by rfl)
  · decide

example : ¬ WP.spec
    ((ambiguousSource.withChoice (fun _ => [.init 2])).transmuteCopyResult boolDestination ())
    (fun _ => True) := by
  rw [rejects_invalid_bool]
  simp

-- A physical success cannot bypass the destination's mathematical decoder.
@[reducible] def rejectsModelDestination : RustModel Rust.Bytes.Byte where
  Model := Unit
  decode := fun _ => none
  storage := some (.fixed byteDecoder)

example :
    (ambiguousSource.withChoice (fun _ => [.init 0])).transmuteCopyResult rejectsModelDestination () =
      .fail .undef := by
  apply RustModel.transmuteCopyResult_rejects_model
    (ambiguousSource.withChoice (fun _ => [.init 0])) rejectsModelDestination () _ _ rfl rfl rfl [.init 0] 0
  · exact ambiguousSource.selectedBytes_withChoice () [.init 0] (by rfl)
  · rfl
  · rfl

example :
    ambiguousSource.transmuteCopyResult modelUnit () = .fail .undef := by
  have hs : ambiguousSource.representation = some (byteDecoder.map fun _ => ()) := rfl
  have hd : modelUnit.representation = some unitDecoder := rfl
  simp [RustModel.transmuteCopyResult, hs, hd, BitDecoder.map, byteDecoder, unitDecoder, emptyDecoder]

example (choose : Unit → List AMByte) :
    (modelManuallyDrop Unit (ma := ambiguousSource.withChoice choose)).representationChoice ⟨()⟩ =
      choose () := rfl

#print axioms RustModel.transmuteCopyResult_admitted
#print axioms RustModel.transmuteCopyResult_covers
end TransmuteModelTests
