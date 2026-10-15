/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
@[expose] public section

/-!
The admission proof, checked before extraction, establishes that the retained
conditional drops cannot execute a destructor. This theorem then checks the
ordinary value behavior against both golden and live function definitions.
The same decoded witness passes through the call; no inhabitedness assumption
or restriction on the generic type's destructor is introduced.
-/

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

theorem move_through_call_spec : Specs.move_through_call_spec := by
  intro T value provider mathematical decoded
  exact WP.spec.ret ⟨mathematical, decoded, rfl⟩

end Zerocopy.Proofs
