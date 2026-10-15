/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import RustRepresentation
@[expose] public section

/-!
The production default method calls the guarded zero constructor with its
retained semantic provider. Its enclosing FromZeros dictionary supplies zero
admission; the returned raw value must also decode through that same provider.
This proof does not infer that a moved raw value retains initialized padding.
-/

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

theorem new_zeroed_spec : Specs.new_zeroed_spec := by
  intro Self meaning dictionary law
  obtain ⟨raw, value, constructed, decoded⟩ := meaning.zeroedResult_admitted
    (@TraitLaws.from_zeros_valid.holds Self dictionary meaning law)
  change meaning.zeroedResult ⦃ output =>
    ∃ mathematical, meaning.decode output = some mathematical ∧ meaning.zeroedResult = .ok output ⦄
  rw [constructed]
  exact ⟨value, decoded, rfl⟩

end Zerocopy.Proofs
