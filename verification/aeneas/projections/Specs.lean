/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import SpecPrelude
public import SpecsSyntax
public import Models
@[expose] public section

open Aeneas Aeneas.Std
open Zerocopy.Proofs
namespace Zerocopy.Specs

check_model_inputs Zerocopy.util.padding_needed_for with 0 type parameters
aeneas_spec_begin
spec padding_lt_alignment
  for @Zerocopy.util.padding_needed_for with 0 type parameters
  ensures p => (p : Nat) < (align : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.padding_lt_alignment for Zerocopy.util.padding_needed_for with 2

check_model_inputs Zerocopy.util.round_down_to_next_multiple_of_alignment with 0 type parameters
aeneas_spec_begin
spec round_down_spec
  for @Zerocopy.util.round_down_to_next_multiple_of_alignment with 0 type parameters
  requires h : (align : Nat).isPowerOfTwo
  ensures m => (m : Nat) ≤ (n : Nat) ∧ (m : Nat) % (align : Nat) = 0
aeneas_spec_end
check_spec_binding Zerocopy.Specs.round_down_spec for Zerocopy.util.round_down_to_next_multiple_of_alignment with 2

check_model_inputs Zerocopy.util.max with 0 type parameters
aeneas_spec_begin
spec max_spec
  for @Zerocopy.util.max with 0 type parameters
  ensures r => (r : Nat) = Nat.max (a : Nat) (b : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.max_spec for Zerocopy.util.max with 2

check_model_inputs Zerocopy.util.min with 0 type parameters
aeneas_spec_begin
spec min_spec
  for @Zerocopy.util.min with 0 type parameters
  ensures r => (r : Nat) = Nat.min (a : Nat) (b : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.min_spec for Zerocopy.util.min with 2

end Zerocopy.Specs
