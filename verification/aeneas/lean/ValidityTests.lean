/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ValidityStructuralTests
public import ValidityFallback
@[expose] public section

open Lean Aeneas Aeneas.Std AeneasSpecs ValidityStructuralTests
namespace ValidityTests

structure Late where
  val : Nat
/-- error: Structural validity and invariants must elaborate before importing ValidityFallback -/
#guard_msgs in
discard_validity_fixture derive_model_validity Late with 0 type parameters
/-- error: Structural validity and invariants must elaborate before importing ValidityFallback -/
#guard_msgs in
discard_validity_fixture aeneas_invariant late_valid for Late with 0 type parameters := fun _ => True

-- Fallback must not hide a backward reconstruction inside a successful payload.
def backward_model : Result (Nat × (Child → Result Child)) := .ok (0, fun _ => .ok ⟨0⟩)
/-- error: Unsupported escaping function or backward reconstruction in validity carrier -/
#guard_msgs in
discard_validity_fixture check_model_validity_inputs backward_model with 0 type parameters

def callback_model (f : Nat → Nat) : Result Nat := .ok (f 0)
/-- error: Unsupported escaping function or backward reconstruction in validity carrier -/
#guard_msgs in
discard_validity_fixture check_model_validity_inputs callback_model with 0 type parameters

section
local instance (priority := 2000) : IsValid (Option Child) := ⟨fun _ => True⟩
def conflicting_option : Result (Option Child) := .ok (.some ⟨0⟩)
/-- error: Conflicting canonical validity instance for Option Child -/
#guard_msgs in
discard_validity_fixture check_model_validity_inputs conflicting_option with 0 type parameters
end

section
local instance (priority := 2000) : IsValid
    (core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner) := ⟨fun _ => True⟩
/-- error: Conflicting canonical validity instance for core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner -/
#guard_msgs in
discard_validity_fixture check_model_validity_inputs native_model with 0 type parameters
end

-- Equivalent dictionary values are permitted, regardless of provider identity.
section
local instance (priority := 2000) : IsValid Nat := ⟨fun _ => True⟩
def equivalent_nat (x : Nat) : Result Nat := .ok x
check_model_validity_inputs equivalent_nat with 0 type parameters
end

section
attribute [-instance] validOption
def removed_option : Result (Option Child) := .ok (.some ⟨0⟩)
/-- error: Conflicting canonical validity instance for Option Child -/
#guard_msgs in
discard_validity_fixture check_model_validity_inputs removed_option with 0 type parameters
attribute [instance] validOption
end

end ValidityTests
