/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
import all RustModel

/-!
These model tests use explicit metadata and numeric byte representations.
They prove decoder behavior, not a Rust ABI identity, pointer reconstruction,
or the full contract of any unsafe trait or byte-cast implementation.
-/
open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace IndexedStorageTests

example : (modelBool).decodeStorageResult boolDecoder.asStorageDecoder () [AMByte.init 1] = .ok true := by
  rw [RustModel.decodeStorageResult_as_runWith]
  rfl
example : (modelBool).decodeStorageResult boolDecoder.asStorageDecoder () [AMByte.init 2] = .fail .undef := by
  rw [RustModel.decodeStorageResult_as_runWith]
  rfl
example : (modelBool).decodeStorageResult boolDecoder.asStorageDecoder () [AMByte.uninit] = .fail .undef := by
  rw [RustModel.decodeStorageResult_as_runWith]
  rfl
example : (modelBool).decodeStorageResult boolDecoder.asStorageDecoder () [] = .fail .undef := by
  rw [RustModel.decodeStorageResult_as_runWith]
  rfl

-- The native slice adapter preserves every explicit count and the array domain.
example (count : Usize) (bytes : List AMByte)
    (values : { values : List Bool // values.length = count.val })
    (accepted : (arrayDecoder boolDecoder count.val).run bytes = some values) :
    RustModel.decodeStorageBitsResult (RustModel.sliceStorageDecoder boolDecoder) count bytes =
      .ok (Slice.from values.val (by rw [values.property]; scalar_tac)) := by
  rw [RustModel.decodeStorageBitsResult, RustModel.sliceStorageDecoder_run, accepted]
  rfl
example : (RustModel.sliceStorageDecoder boolDecoder).Initialized :=
  RustModel.sliceStorageDecoder_initialized _ boolDecoder_initialized

-- Equal zero-byte widths support every usize count without guessing that count.
example (count : Usize) : ∃ raw,
    RustModel.decodeStorageBitsResult (RustModel.sliceStorageDecoder unitDecoder) count [] = .ok raw := by
  obtain ⟨values, accepted⟩ := arrayDecoder_complete unitDecoder
    (fun bytes width _ => ⟨(), emptyDecoder_complete () bytes width⟩) count.val []
    (by simp [unitDecoder, emptyDecoder]) initialized_nil
  rw [RustModel.decodeStorageBitsResult, RustModel.sliceStorageDecoder_run, accepted]
  exact ⟨_, rfl⟩
example (count : Usize) (bytes : List AMByte) (raw : Slice Unit)
    (accepted : (RustModel.sliceStorageDecoder unitDecoder).run count bytes = some raw) :
    raw.len = count := StorageDecoder.run_metadata _ _ _ _ accepted

-- A mathematical decoder cannot conceal an invalid language representation.
@[reducible] def rejectsAll : RustModel Unit where
  Model := Unit
  decode _ := none

example : rejectsAll.decodeStorageResult unitDecoder.asStorageDecoder () [] = .fail .undef := by
  rw [RustModel.decodeStorageResult_as_runWith]
  rfl
example : RustModel.decodeStorageBitsResult unitDecoder.asStorageDecoder () [] = .ok () := rfl
example : unitDecoder.asStorageDecoder.Initialized :=
  BitDecoder.asStorageDecoder_initialized _ unitDecoder_initialized
example : ¬ unitDecoder.asStorageDecoder.CompleteWith rejectsAll.decode := by
  intro complete
  obtain ⟨value, accepted⟩ := complete () [] rfl initialized_nil
  simp [StorageDecoder.runWith] at accepted

-- An uninitialized representation remains forbidden for the initialization law,
-- even if the mathematical decoder rejects every returned raw value.
def acceptsUninit : StorageDecoder Unit Unit where
  byteSize _ := 1
  metadata _ := ()
  decode _ _ := some ()

example : rejectsAll.decodeStorageResult acceptsUninit () [AMByte.uninit] = .fail .undef := by
  rw [RustModel.decodeStorageResult_as_runWith]
  rfl
example : ¬ acceptsUninit.Initialized := by
  intro initialized
  have impossible := initialized () [AMByte.uninit] () rfl
  simp [Initialized] at impossible

-- The checked metadata observation applies even to zero-width representations.
def wrongCount : StorageDecoder Nat Nat where
  byteSize _ := 0
  metadata := id
  decode _ _ := some 0

example : RustModel.decodeStorageBitsResult wrongCount 3 [] = .fail .undef := rfl
example : modelNat.decodeStorageResult wrongCount 3 [] = .fail .undef := by
  rw [RustModel.decodeStorageResult_as_runWith]
  rfl

-- A vacuous postcondition cannot admit language-invalid byte construction.
example : ¬ WP.spec
    (modelBool.decodeStorageResult boolDecoder.asStorageDecoder () [AMByte.init 2])
    (fun _ => True) := by
  rw [RustModel.decodeStorageResult_as_runWith]
  change ¬ WP.spec (.fail .undef : Result Bool) (fun _ => True)
  simp
example : ¬ WP.dspec (modelNat.decodeStorageResult wrongCount 3 []) (fun _ => True) := by
  rw [RustModel.decodeStorageResult_as_runWith]
  change ¬ WP.dspec (.fail .undef : Result Nat) (fun _ => True)
  simp

#print axioms RustModel.decodeStorageResult_as_runWith
#print axioms RustModel.decodeStorageResult_eq_ok_iff
#print axioms RustModel.sliceStorageDecoder_initialized

end IndexedStorageTests
