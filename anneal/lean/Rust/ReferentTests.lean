/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
import Rust.Referent

/-!
These examples check the boundary of the byte-domain rules. In particular,
neither initialization nor an empty safe domain supplies a mathematical value.
The final example explains why transfer composition requires equal intermediate
widths even though each individual transfer is conditional on equal widths.
-/

namespace Rust.Referent.Tests

open Rust.Storage

def safeBool : List AMByte → Prop :=
  Safe boolDecoder.asStorageDecoder (fun value => some value) ()

theorem two_initialized : Initialized [AMByte.init 2] := by
  simp [Initialized]

theorem two_not_safe_bool : ¬safeBool [AMByte.init 2] := by
  rintro ⟨raw, _, accepted, _⟩
  rw [BitDecoder.run_asStorageDecoder, boolDecoder_run_two] at accepted
  contradiction

/-- A byte has an initialized value even when it is not a valid boolean. -/
theorem initialization_does_not_imply_safety :
    ¬Transfer 1 safeBool .initialized 1 safeBool .safe := by
  intro transfer
  exact two_not_safe_bool (transfer rfl [AMByte.init 2] ⟨rfl, two_initialized⟩).2

example : Transfer 1 safeBool .safe 1 safeBool .initialized :=
  safe_to_initialized boolDecoder.asStorageDecoder (fun value => some value)
    (boolDecoder.asStorageDecoder_initialized boolDecoder_initialized) () 1 safeBool

example : Transfer 1 safeBool .initialized 1 safeBool .initialized :=
  initialized_identity 1 1 safeBool safeBool

example (state : State) : Transfer 1 safeBool state 1 safeBool .uninit :=
  to_uninit 1 1 safeBool safeBool state

def safeByte : List AMByte → Prop :=
  Safe byteDecoder.asStorageDecoder (fun value => some value) ()

theorem byte_complete :
    byteDecoder.asStorageDecoder.CompleteWith (fun value => some value) := by
  intro metadata bytes width initialized
  cases metadata
  obtain ⟨value, accepted⟩ := byteDecoder_complete bytes width initialized
  exact ⟨value, by simp [StorageDecoder.runWith, accepted]⟩

example : Transfer 1 safeBool .initialized 1 safeByte .safe :=
  initialized_to_safe byteDecoder.asStorageDecoder (fun value => some value)
    byte_complete () 1 safeBool

example : Transfer 1 safeBool .safe 1 safeByte .safe :=
  transfer_trans 1 1 1 safeBool safeBool safeByte .safe .initialized .safe
    (safe_to_initialized boolDecoder.asStorageDecoder (fun value => some value)
      (boolDecoder.asStorageDecoder_initialized boolDecoder_initialized) () 1 safeBool)
    (initialized_to_safe byteDecoder.asStorageDecoder (fun value => some value)
      byte_complete () 1 safeBool) rfl

example : Transfer 1 safeBool .safe 1 (fun bytes => safeBool bytes ∨ safeByte bytes) .safe :=
  safe_transfer_of_implication 1 1 _ _ (fun _ _ admitted => Or.inl admitted)

/-- A zero-byte layout does not create a value of an empty type. -/
def noValueDecoder : StorageDecoder Unit Empty where
  byteSize _ := 0
  metadata value := nomatch value
  decode _ _ := none

def noValueModel (value : Empty) : Option Empty := nomatch value

theorem no_value_safe_empty (bytes : List AMByte) :
    ¬Safe noValueDecoder noValueModel () bytes := by
  rintro ⟨raw, _⟩
  exact nomatch raw

/-- An empty source domain entails every destination predicate, vacuously. -/
theorem no_value_safe_transfer (width : Nat) (destination : List AMByte → Prop) :
    Transfer 0 (Safe noValueDecoder noValueModel ()) .safe width destination .safe := by
  intro _ bytes admitted
  exact False.elim (no_value_safe_empty bytes admitted.2)

/-- Completeness still needs a decoded value for the initialized empty list. -/
theorem no_value_not_complete : ¬noValueDecoder.CompleteWith noValueModel := by
  intro complete
  obtain ⟨value, _⟩ := complete () [] rfl initialized_nil
  exact nomatch value

example : Initialized
    (([AMByte.init 0, AMByte.init 1, AMByte.init 2].drop 1).take 1) :=
  initialized_subrange _ (by simp [Initialized]) 1 1

example : Initialized
    ([AMByte.init 0, AMByte.init 1].take 1 ++ [AMByte.init 2] ++
      [AMByte.init 0, AMByte.init 1].drop (1 + 1)) :=
  initialized_replace _ _ (by simp [Initialized]) (by simp [Initialized]) 1 1

/-- Both premises hold because their widths differ. The conclusion has equal
widths and fails on a one-byte list, so unconditional transitivity is false. -/
theorem intermediate_width_is_necessary :
    Transfer 1 (fun _ => True) .safe 0 (fun _ => False) .safe ∧
    Transfer 0 (fun _ => False) .safe 1 (fun _ => False) .safe ∧
    ¬Transfer 1 (fun _ => True) .safe 1 (fun _ => False) .safe := by
  refine ⟨?_, ?_, ?_⟩
  · intro impossible
    omega
  · intro impossible
    omega
  · intro transfer
    exact (transfer rfl [AMByte.init 2] ⟨rfl, trivial⟩).2

#print axioms safe_to_initialized
#print axioms initialized_to_safe
#print axioms initialized_identity
#print axioms to_uninit
#print axioms transfer_trans
#print axioms initialized_subrange
#print axioms initialized_replace
#print axioms intermediate_width_is_necessary
#print axioms no_value_not_complete

end Rust.Referent.Tests
