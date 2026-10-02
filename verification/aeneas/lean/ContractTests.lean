/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Contracts
@[expose] public section
open Aeneas Aeneas.Std
namespace ContractTests

-- Omitted requirements mean True; a successful result is still required.
contract identity_spec (x : Nat)
  for Result.ok x
  ensures ret => ret = x
  proof:
    exact WP.spec.ret rfl

-- Named requirements are available without introductions in the proof body.
contract transitive_spec (x y z : Nat)
  for Result.ok x
  requires hxy : x = y
  requires hyz : y = z
  ensures ret => ret = z
  proof:
    exact WP.spec.ret (hxy.trans hyz)

-- Reuse Aeneas's tuple-aware binders for returns and mutable post-states.
contract tuple_spec (x : Nat)
  for Result.ok (x, x + 1)
  ensures ret x' => ret = x ∧ x' = x + 1
  proof:
    simp

partial contract diverging_spec
  for (Result.div : Result Nat)
  ensures _ => False
  proof:
    exact WP.dspec.div _

partial contract partial_identity_spec (x : Nat)
  for Result.ok x
  ensures ret => ret = x
  proof:
    exact WP.dspec.ret rfl

-- These independently written types pin the macro's quantifiers and outcomes.
example : ∀ x : Nat, WP.spec (Result.ok x) (fun ret => ret = x) := identity_spec
example : ∀ x y z : Nat, x = y → y = z →
    WP.spec (Result.ok x) (fun ret => ret = z) := transitive_spec
example : ∀ x : Nat, WP.spec (Result.ok (x, x + 1))
    (fun (ret, x') => ret = x ∧ x' = x + 1) := tuple_spec
example : WP.dspec (Result.div : Result Nat) (fun _ => False) := diverging_spec
example : ∀ x : Nat, WP.dspec (Result.ok x) (fun ret => ret = x) := partial_identity_spec

theorem panic_rejected :
    ¬ WP.spec (Result.fail Error.panic : Result Nat) (fun _ => True) := by simp

theorem divergence_rejected :
    ¬ WP.spec (Result.div : Result Nat) (fun _ => True) := by simp

-- Partial correctness must reject panic and incorrect successful returns too.
theorem partial_panic_rejected :
    ¬ WP.dspec (Result.fail Error.panic : Result Nat) (fun _ => True) := by simp

theorem partial_wrong_return_rejected :
    ¬ WP.dspec (Result.ok 0) (fun ret : Nat => ret = 1) := by simp

end ContractTests
