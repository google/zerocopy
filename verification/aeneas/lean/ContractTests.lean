/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelPrelude
@[expose] public section

/-!
These kernel-checked examples explain Aeneas's native total and partial
contracts independently of our spec macro. They pin successful results, tuple
postconditions, panic rejection, and divergence behavior. The independently
written theorem types prevent a change in syntax from silently changing the
claim. Total contracts require successful execution even for a True
postcondition. Partial contracts may diverge, but still reject panic.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace ContractTests

-- Omitted requirements mean True; a successful result is still required.
theorem identity_spec (x : Nat) :
    Result.ok x
      ⦃ ret => ret = x ⦄ := by
  exact WP.spec.ret rfl

-- Named requirements are available without introductions in the proof body.
theorem transitive_spec (x y z : Nat)
    (hxy : x = y)
    (hyz : y = z) :
    Result.ok x
      ⦃ ret => ret = z ⦄ := by
  exact WP.spec.ret (hxy.trans hyz)

-- Reuse Aeneas's tuple-aware binders for returns and mutable post-states.
theorem tuple_spec (x : Nat) :
    Result.ok (x, x + 1)
      ⦃ ret x' => ret = x ∧ x' = x + 1 ⦄ := by
  simp

theorem diverging_spec :
    (Result.div : Result Nat)
      ⦃ _ => False ⦄div := by
  exact WP.dspec.div _

theorem partial_identity_spec (x : Nat) :
    Result.ok x
      ⦃ ret => ret = x ⦄div := by
  exact WP.dspec.ret rfl

-- These independently written types pin the exported theorem types and outcomes.
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

-- A generic identity shares one explicit dictionary and the same witness on
-- input and output, even when the dictionary rejects some representations.
theorem modeled_identity {Raw : Type} (provider : RustModel Raw) (raw : Raw)
    (value : provider.Model) (h : provider.decode raw = some value) :
    WP.spec (Result.ok raw) (fun out =>
      ∃ decoded, provider.decode out = some decoded ∧ decoded = value) :=
  WP.spec.ret ⟨value, h, rfl⟩

-- A dependent ghost retains its exact domain in mathematical input scope.
theorem modeled_position {Raw : Type} (provider : RustModel Raw)
    (length : provider.Model → Nat) (raw : Raw) (value : provider.Model)
    (h : provider.decode raw = some value) (position : Fin (length value)) :
    WP.spec (Result.ok raw) (fun out =>
      ∃ decoded, provider.decode out = some decoded ∧ position.val < length decoded) :=
  WP.spec.ret ⟨value, h, position.isLt⟩

-- An accepted execution cannot return a decoder-rejected representation, even
-- when its authored postcondition contributes no information.
theorem rejected_output_rejected {Raw : Type} (provider : RustModel Raw)
    (raw : Raw) (h : provider.decode raw = none) :
    ¬ WP.spec (Result.ok raw) (fun out =>
      ∃ decoded, provider.decode out = some decoded ∧ True) := by
  simp [WP.spec_ok, h]

theorem partial_rejected_output_rejected {Raw : Type} (provider : RustModel Raw)
    (raw : Raw) (h : provider.decode raw = none) :
    ¬ WP.dspec (Result.ok raw) (fun out =>
      ∃ decoded, provider.decode out = some decoded ∧ True) := by
  simp [h]

-- Rust absence and Rust errors remain successful decoded constructor cases.
example : (@modelOption Usize (modelUScalar .Usize)).decode none = some none := rfl
example : (@modelRustResult Usize Unit (modelUScalar .Usize) modelUnit).decode
    (.Err ()) = some (.Err ()) := rfl

end ContractTests
