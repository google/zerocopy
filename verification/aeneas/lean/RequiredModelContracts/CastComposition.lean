/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Obligations.CastComposition
public import RequiredModelContracts.CastPlan
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

/- Recover all decoder witnesses from the independently stated raw domain,
then consume the supplied contract for the same arbitrary execution outcome.
This adapter does not use the implementation proof or execute the harness.
-/
@[contract_simps] theorem required_cast_composition_check
    (src dst : layout.DstLayout) (src_align : NonZeroUsize) (src_phase : Usize)
    (dst_align : NonZeroUsize) (dst_phase src_meta : Usize) (run : Result Unit)
    (provided : Specs.cast_composition_check_spec_contract
      src dst src_align src_phase dst_align dst_phase src_meta run) :
    Obligations.cast_composition_check_spec_contract
      src dst src_align src_phase dst_align dst_phase src_meta run := by
  intro src_positive dst_positive src_canonical dst_canonical src_align_positive dst_align_positive
  obtain ⟨src_value, src_decoded⟩ := layout_admitted_of_canonical src src_positive src_canonical
  obtain ⟨dst_value, dst_decoded⟩ := layout_admitted_of_canonical dst dst_positive dst_canonical
  let src_align_value : NonZeroUsizeValue := ⟨unsignedWord src_align.val, src_align_positive⟩
  let dst_align_value : NonZeroUsizeValue := ⟨unsignedWord dst_align.val, dst_align_positive⟩
  have src_align_decoded := (decodeNonZeroUScalar_iff src_align src_align_value).mpr rfl
  have dst_align_decoded := (decodeNonZeroUScalar_iff dst_align dst_align_value).mpr rfl
  apply WP.spec_mono (provided src_value src_decoded dst_value dst_decoded
    src_align_value src_align_decoded (unsignedWord src_phase) rfl
    dst_align_value dst_align_decoded (unsignedWord dst_phase) rfl (unsignedWord src_meta) rfl)
  rintro result ⟨_value, _decoded, _facts⟩
  trivial

end Zerocopy.Proofs
