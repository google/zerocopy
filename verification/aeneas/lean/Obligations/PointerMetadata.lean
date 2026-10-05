/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/


module
public import LayoutModel
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Obligations
open Zerocopy.Proofs
set_option linter.unusedVariables false

/- Concrete wrappers call the actual trait implementations. These expectations
retain their complete raw domain and distinguish overflow from execution
failure, without using an extracted operation to define the expected result. -/
def pointer_metadata_unit_from_elem_count_spec_contract (elems : Usize)
    (run : Result Unit) : Prop := run ⦃ result => result = () ⦄
def pointer_metadata_unit_from_elem_count_spec : Prop := ∀ elems,
  pointer_metadata_unit_from_elem_count_spec_contract elems
    (pointer_metadata_unit_from_elem_count elems)

def pointer_metadata_unit_to_elem_count_spec_contract (run : Result Usize) : Prop := run ⦃ result => result.val = 0 ⦄
def pointer_metadata_unit_to_elem_count_spec : Prop :=
  pointer_metadata_unit_to_elem_count_spec_contract pointer_metadata_unit_to_elem_count

def pointer_metadata_usize_from_elem_count_spec_contract (elems : Usize)
    (run : Result Usize) : Prop := run ⦃ result => result.val = elems.val ⦄
def pointer_metadata_usize_from_elem_count_spec : Prop := ∀ elems,
  pointer_metadata_usize_from_elem_count_spec_contract elems
    (pointer_metadata_usize_from_elem_count elems)

def pointer_metadata_usize_to_elem_count_spec_contract (metadata : Usize)
    (run : Result Usize) : Prop := run ⦃ result => result.val = metadata.val ⦄
def pointer_metadata_usize_to_elem_count_spec : Prop := ∀ metadata,
  pointer_metadata_usize_to_elem_count_spec_contract metadata
    (pointer_metadata_usize_to_elem_count metadata)

def pointer_metadata_unit_size_for_metadata_spec_contract (runtime_layout : layout.DstLayout) (run : Result (Option Usize)) : Prop :=
  layoutValid runtime_layout → run ⦃ result =>
    match runtime_layout.size_info with
    | .Sized bytes => ∃ size, result = some size ∧ size.val = bytes.val
    | .SliceDst _ => result = none ⦄
def pointer_metadata_unit_size_for_metadata_spec : Prop := ∀ runtime_layout,
  pointer_metadata_unit_size_for_metadata_spec_contract runtime_layout
    (pointer_metadata_unit_size_for_metadata runtime_layout)

def pointer_metadata_usize_size_for_metadata_spec_contract (metadata : Usize)
    (runtime_layout : layout.DstLayout) (run : Result (Option Usize)) : Prop :=
  layoutValid runtime_layout → run ⦃ result =>
    match runtime_layout.size_info with
    | .Sized _ => result = none
    | .SliceDst tail => match result with
      | none => Usize.max < (trailingFormula tail).size metadata.val
      | some size => size.val = (trailingFormula tail).size metadata.val ∧
        (trailingFormula tail).size metadata.val ≤ Usize.max ⦄
def pointer_metadata_usize_size_for_metadata_spec : Prop := ∀ metadata runtime_layout,
  pointer_metadata_usize_size_for_metadata_spec_contract metadata runtime_layout
    (pointer_metadata_usize_size_for_metadata metadata runtime_layout)

end Zerocopy.Obligations
