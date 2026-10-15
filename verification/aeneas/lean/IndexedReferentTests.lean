/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
import all IndexedReferent
import all RustModel

/-!
These examples check retained numeric byte domains and metadata. They do not
execute native pointer operations or prove Rust layout correspondence.
-/

open Aeneas Aeneas.Std AeneasSpecs Rust.Storage AeneasSpecs.IndexedReferent
namespace IndexedReferentTests

def unitView : StorageView modelUnit := ⟨.fixed unitDecoder, rfl⟩

example : unitView.Metadata = Unit := rfl
example : unitView.decoder.Initialized := unitView.initialized unitDecoder_initialized

theorem unit_complete : unitView.decoder.CompleteWith modelUnit.decode := by
  intro metadata bytes width _
  cases metadata
  have empty : bytes = [] := List.length_eq_zero_iff.mp width
  subst bytes
  exact ⟨(), rfl⟩

example : transferAt unitView () unitView () .initialized .safe :=
  initialized_to_safe unitView () unitView () unit_complete

def unitSliceView : StorageView (modelSlice (α := Unit)) :=
  ⟨PhysicalStorage.slice (.fixed unitDecoder), rfl⟩

example : unitSliceView.Metadata = Usize := rfl

example : unitSliceView.decoder.byteSize (0#usize) =
    unitSliceView.decoder.byteSize (1#usize) := rfl

theorem unit_slice_safe (count : Usize) : safeAt unitSliceView count [] := by
  obtain ⟨values, accepted⟩ := arrayDecoder_complete unitDecoder
    (fun bytes width _ => ⟨(), emptyDecoder_complete () bytes width⟩) count.val []
    (by simp [unitDecoder, emptyDecoder]) initialized_nil
  have physical : unitSliceView.decoder.run count [] =
      some (Slice.from values.val (by rw [values.property]; scalar_tac)) := by
    change (RustModel.sliceStorageDecoder unitDecoder).run count [] = _
    rw [RustModel.sliceStorageDecoder_run, accepted]
    rfl
  refine ⟨_, ⟨values.val, by rw [values.property]; scalar_tac⟩, physical, ?_⟩
  have decode_some (raws : List Unit) : decodeList (some : Unit → Option Unit) raws = some raws := by
    induction raws with
    | nil => rfl
    | cons raw raws ih => simp [decodeList, ih]
  change (@modelSlice Unit modelUnit).decode _ = _
  simp only [RustModel.decode]
  have decoded : decodeList (some : Unit → Option Unit)
      (Slice.from values.val (by rw [values.property]; scalar_tac)).val = some values.val := by
    rw [Slice.from_val]
    exact decode_some _
  split
  · rename_i rejected
    have impossible := rejected.symm.trans decoded
    contradiction
  · rename_i output acceptedModel
    have same : output = values.val := Option.some.inj (acceptedModel.symm.trans decoded)
    subst output
    rfl

-- Two distinct counts have equal width. Transfer uses the explicit pair,
-- rather than concluding that their metadata or decoded values are equal.
theorem unit_slice_transfer (sourceCount destinationCount : Usize) :
    transferAt unitSliceView sourceCount unitSliceView destinationCount .safe .safe := by
  intro _ bytes admitted
  have zero : unitSliceView.decoder.byteSize sourceCount = 0 := by
    change sourceCount.val * 0 = 0
    exact Nat.mul_zero _
  have empty : bytes = [] := List.length_eq_zero_iff.mp (admitted.1.trans zero)
  subst bytes
  refine ⟨?_, unit_slice_safe destinationCount⟩
  change 0 = destinationCount.val * 0
  simp

example : transferAt unitSliceView (0#usize) unitSliceView (1#usize) .safe .initialized :=
  safe_to_initialized unitSliceView (0#usize) unitSliceView (1#usize)
    (RustModel.sliceStorageDecoder_initialized _ unitDecoder_initialized)

example : transferAt unitSliceView (0#usize) unitSliceView (2#usize) .safe .safe :=
  transfer_trans unitSliceView (0#usize) unitSliceView (1#usize) unitSliceView (2#usize)
    .safe .safe .safe (unit_slice_transfer _ _) (unit_slice_transfer _ _) rfl

example (count : Usize) : transferAt unitView () unitSliceView count .initialized .safe := by
  apply initialized_to_safe_at
  intro bytes width _
  have zero : unitSliceView.decoder.byteSize count = 0 := by
    change count.val * 0 = 0
    exact Nat.mul_zero _
  have empty : bytes = [] := List.length_eq_zero_iff.mp (width.trans zero)
  subst bytes
  exact unit_slice_safe count

example (raw : Slice Unit) :
    (unitSliceView.physical.map (fun value => (value, ())) Prod.fst (fun _ => rfl)).decoder.metadata
        (raw, ()) = unitSliceView.physical.mapMetadata (fun value => (value, ())) Prod.fst
          (fun _ => rfl) (unitSliceView.physical.decoder.metadata raw) :=
  unitSliceView.physical.map_metadata _ _ _ raw

def emptyBits : BitDecoder Empty where
  byteSize := 0
  decode _ := none

@[reducible] def emptyMeaning : RustModel Empty where
  Model := Empty
  decode raw := nomatch raw
  storage := some (.fixed emptyBits)

@[reducible] def emptySliceMeaning : RustModel (Slice Empty) := @modelSlice Empty emptyMeaning

def emptySliceView : StorageView emptySliceMeaning :=
  ⟨PhysicalStorage.slice (.fixed emptyBits), rfl⟩

theorem empty_zero_safe : safeAt emptySliceView (0#usize) [] := by
  refine ⟨Slice.from [] (by scalar_tac), ⟨[], by scalar_tac⟩, ?_, rfl⟩
  rfl

theorem empty_one_unsafe : ¬ safeAt emptySliceView (1#usize) [] := by
  rintro ⟨raw, _, accepted, _⟩
  have metadata := emptySliceView.decoder.run_metadata (1#usize) [] raw accepted
  change raw.len = (1#usize) at metadata
  have empty : raw.val = [] := by
    cases elements : raw.val with
    | nil => rfl
    | cons value _ => nomatch value
  have length := congrArg UScalar.val metadata
  simp [empty] at length

-- Both widths are zero, but count one requires an Empty inhabitant.
example : ¬ transferAt emptySliceView (0#usize) emptySliceView (1#usize) .safe .safe := by
  intro transfer
  exact empty_one_unsafe (transfer rfl [] ⟨rfl, empty_zero_safe⟩).2

example : ¬ Nonempty (StorageView modelNat) := StorageView.absent rfl

-- Existing computation contracts retain forbidden execution even for a
-- vacuous postcondition. A metadata-indexed referent view does not alter them.
example : ¬ WP.spec (.fail .undef : Result Unit) (fun _ => True) := by simp
example : ¬ WP.dspec (.fail .undef : Result Unit) (fun _ => True) := by simp

#print axioms safe_to_initialized
#print axioms initialized_to_safe
#print axioms transfer_trans
#print axioms empty_one_unsafe

end IndexedReferentTests
