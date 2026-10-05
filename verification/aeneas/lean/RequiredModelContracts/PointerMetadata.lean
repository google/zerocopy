/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/


module
public import Obligations.PointerMetadata
public import RequiredModelContracts
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

/- Every adapter consumes the supplied contract for the same arbitrary run.
No canonical implementation theorem is used to repair a weak specification. -/
@[contract_simps] theorem required_pointer_metadata_unit_from_elem_count (elems : Usize)
    (run : Result Unit)
    (provided : Specs.pointer_metadata_unit_from_elem_count_spec_contract elems run) :
    Obligations.pointer_metadata_unit_from_elem_count_spec_contract elems run := by
  apply WP.spec_mono (provided (unsignedWord elems) rfl)
  rintro result ⟨_value, _decoded, facts⟩
  exact facts

@[contract_simps] theorem required_pointer_metadata_unit_to_elem_count (run : Result Usize)
    (provided : Specs.pointer_metadata_unit_to_elem_count_spec_contract run) :
    Obligations.pointer_metadata_unit_to_elem_count_spec_contract run := by
  apply WP.spec_mono provided
  rintro result ⟨_value, _decoded, facts⟩
  exact facts

@[contract_simps] theorem required_pointer_metadata_usize_from_elem_count (elems : Usize)
    (run : Result Usize)
    (provided : Specs.pointer_metadata_usize_from_elem_count_spec_contract elems run) :
    Obligations.pointer_metadata_usize_from_elem_count_spec_contract elems run := by
  apply WP.spec_mono (provided (unsignedWord elems) rfl)
  rintro result ⟨_value, _decoded, facts⟩
  exact congrArg UScalar.val facts

@[contract_simps] theorem required_pointer_metadata_usize_to_elem_count (metadata : Usize)
    (run : Result Usize)
    (provided : Specs.pointer_metadata_usize_to_elem_count_spec_contract metadata run) :
    Obligations.pointer_metadata_usize_to_elem_count_spec_contract metadata run := by
  apply WP.spec_mono (provided (unsignedWord metadata) rfl)
  rintro result ⟨_value, _decoded, facts⟩
  exact congrArg UScalar.val facts

@[contract_simps] theorem required_pointer_metadata_unit_size_for_metadata (runtime_layout : layout.DstLayout) (run : Result (Option Usize))
    (provided : Specs.pointer_metadata_unit_size_for_metadata_spec_contract runtime_layout run) :
    Obligations.pointer_metadata_unit_size_for_metadata_spec_contract runtime_layout run := by
  intro valid
  obtain ⟨value, decoded⟩ := (layout_valid_iff runtime_layout).mpr valid
  apply WP.spec_mono (provided value decoded)
  rintro result ⟨_value, _decoded, facts⟩
  cases info : runtime_layout.size_info with
  | Sized bytes =>
    simp only [info] at facts ⊢
    exact ⟨bytes, facts, rfl⟩
  | SliceDst tail => simpa only [info] using facts

@[contract_simps] theorem required_pointer_metadata_usize_size_for_metadata (metadata : Usize)
    (runtime_layout : layout.DstLayout) (run : Result (Option Usize))
    (provided : Specs.pointer_metadata_usize_size_for_metadata_spec_contract metadata runtime_layout run) :
    Obligations.pointer_metadata_usize_size_for_metadata_spec_contract metadata runtime_layout run := by
  intro valid
  obtain ⟨value, decoded⟩ := (layout_valid_iff runtime_layout).mpr valid
  apply WP.spec_mono (provided (unsignedWord metadata) rfl value decoded)
  rintro result ⟨_value, _decoded, facts⟩
  cases info : runtime_layout.size_info with
  | Sized bytes =>
    simp only [info] at facts ⊢
    cases result <;> simp_all
  | SliceDst tail =>
    simp only [info] at facts ⊢
    cases result with
    | none =>
      simp only [Option.map_none, LayoutMath.Formula.checkedSize] at facts
      split at facts <;> simp_all
    | some size =>
      simp only [Option.map_some, LayoutMath.Formula.checkedSize] at facts
      split at facts <;> simp_all

end Zerocopy.Proofs
