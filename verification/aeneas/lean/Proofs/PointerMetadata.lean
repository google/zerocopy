/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/


module
public import Proofs
public import RequiredModelContracts.PointerMetadata
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw.PointerMetadata

/- The wrapper unfolds to the extracted concrete trait method. These proofs
retain that call, rather than substitute a second arithmetic implementation. -/
theorem pointer_metadata_unit_from_elem_count_spec (elems : Usize) :
    Zerocopy.pointer_metadata_unit_from_elem_count elems ⦃ result => result = () ⦄ := by
  simp [Zerocopy.pointer_metadata_unit_from_elem_count,
    Tuple.Insts.ZerocopyPointerMetadata.from_elem_count, WP.spec_ok]

theorem pointer_metadata_unit_to_elem_count_spec :
    Zerocopy.pointer_metadata_unit_to_elem_count ⦃ result => result.val = 0 ⦄ := by
  simp [Zerocopy.pointer_metadata_unit_to_elem_count,
    Tuple.Insts.ZerocopyPointerMetadata.to_elem_count, WP.spec_ok]

theorem pointer_metadata_usize_from_elem_count_spec (elems : Usize) :
    Zerocopy.pointer_metadata_usize_from_elem_count elems ⦃ result => result = elems ⦄ := by
  simp [Zerocopy.pointer_metadata_usize_from_elem_count,
    Usize.Insts.ZerocopyPointerMetadata.from_elem_count, WP.spec_ok]

theorem pointer_metadata_usize_to_elem_count_spec (metadata : Usize) :
    Zerocopy.pointer_metadata_usize_to_elem_count metadata ⦃ result => result = metadata ⦄ := by
  simp [Zerocopy.pointer_metadata_usize_to_elem_count,
    Usize.Insts.ZerocopyPointerMetadata.to_elem_count, WP.spec_ok]

theorem pointer_metadata_unit_size_for_metadata_spec (runtime_layout : layout.DstLayout) :
    Zerocopy.pointer_metadata_unit_size_for_metadata runtime_layout ⦃ result =>
      result = match runtime_layout.size_info with
        | .Sized size => some size
        | .SliceDst _ => none ⦄ := by
  unfold Zerocopy.pointer_metadata_unit_size_for_metadata
    Tuple.Insts.ZerocopyPointerMetadata.size_for_metadata
  cases runtime_layout.size_info <;> simp [WP.spec_ok]

theorem pointer_metadata_usize_size_for_metadata_spec (metadata : Usize)
    (runtime_layout : layout.DstLayout)
    (positive : match runtime_layout.size_info with
      | .Sized _ => True
      | .SliceDst tail => 0 < tail.size_rounding_align_and_phase._0.val.val) :
    Zerocopy.pointer_metadata_usize_size_for_metadata metadata runtime_layout ⦃ result =>
      result.map UScalar.val = match runtime_layout.size_info with
        | .Sized _ => none
        | .SliceDst tail => (trailingFormula tail).checkedSize Usize.max metadata.val ⦄ := by
  unfold Zerocopy.pointer_metadata_usize_size_for_metadata
    Usize.Insts.ZerocopyPointerMetadata.size_for_metadata
  cases info : runtime_layout.size_info with
  | Sized size => simp [WP.spec_ok]
  | SliceDst tail =>
    simp only [info] at positive
    exact Zerocopy.Proofs.Raw.size_for_elems_spec tail metadata positive

end Zerocopy.Proofs.Raw.PointerMetadata

namespace Zerocopy.Proofs
open AeneasSpecs

theorem pointer_metadata_unit_from_elem_count_spec : Specs.pointer_metadata_unit_from_elem_count_spec := by
  unfold Specs.pointer_metadata_unit_from_elem_count_spec
  representation_simps
  intro elems
  apply WP.spec_mono (Raw.PointerMetadata.pointer_metadata_unit_from_elem_count_spec elems)
  intro result _facts
  exact ⟨result, rfl⟩
register_spec_step pointer_metadata_unit_from_elem_count_spec

theorem pointer_metadata_unit_to_elem_count_spec : Specs.pointer_metadata_unit_to_elem_count_spec := by
  unfold Specs.pointer_metadata_unit_to_elem_count_spec
  representation_simps
  exact Raw.PointerMetadata.pointer_metadata_unit_to_elem_count_spec
register_spec_step pointer_metadata_unit_to_elem_count_spec

theorem pointer_metadata_usize_from_elem_count_spec : Specs.pointer_metadata_usize_from_elem_count_spec := by
  unfold Specs.pointer_metadata_usize_from_elem_count_spec
  representation_simps
  intro elems
  exact Raw.PointerMetadata.pointer_metadata_usize_from_elem_count_spec elems
register_spec_step pointer_metadata_usize_from_elem_count_spec

theorem pointer_metadata_usize_to_elem_count_spec : Specs.pointer_metadata_usize_to_elem_count_spec := by
  unfold Specs.pointer_metadata_usize_to_elem_count_spec
  representation_simps
  intro metadata
  exact Raw.PointerMetadata.pointer_metadata_usize_to_elem_count_spec metadata
register_spec_step pointer_metadata_usize_to_elem_count_spec

theorem pointer_metadata_unit_size_for_metadata_spec : Specs.pointer_metadata_unit_size_for_metadata_spec := by
  unfold Specs.pointer_metadata_unit_size_for_metadata_spec
  representation_simps
  intro runtime_layout _valid
  exact Raw.PointerMetadata.pointer_metadata_unit_size_for_metadata_spec runtime_layout
register_spec_step pointer_metadata_unit_size_for_metadata_spec

theorem pointer_metadata_usize_size_for_metadata_spec : Specs.pointer_metadata_usize_size_for_metadata_spec := by
  unfold Specs.pointer_metadata_usize_size_for_metadata_spec
  representation_simps
  intro metadata runtime_layout valid
  have positive : match runtime_layout.size_info with
      | .Sized _ => True
      | .SliceDst tail => 0 < tail.size_rounding_align_and_phase._0.val.val := by
    cases info : runtime_layout.size_info with
    | Sized size => trivial
    | SliceDst tail => simpa only [info] using valid.2
  exact Raw.PointerMetadata.pointer_metadata_usize_size_for_metadata_spec
    metadata runtime_layout positive
register_spec_step pointer_metadata_usize_size_for_metadata_spec

end Zerocopy.Proofs
