/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredContracts
public import MathViews
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs AeneasContracts
namespace RequiredContractTests
set_option linter.unusedSimpArgs false

def identity (x : Nat) : Result Nat := .ok x

-- The independent family uses only the supplied outcome. Its concrete alias
-- specializes to the operation, whose implementation satisfies this promise.
def expected_contract (x : Nat) (run : Result Nat) : Prop :=
  WP.spec run (fun output => output = x)
def expected : Prop := ∀ x : Nat, expected_contract x (identity x)
theorem identity_correct : expected := by
  intro x
  exact WP.spec.ret rfl

spec strict for identity with 0 type parameters
  ensures output => output = x
spec weak for identity with 0 type parameters
  ensures output => True
theorem weak_correct : weak := by
  simp [weak, weak_contract, identity, RustModel.decode, modelNat]

-- Both concrete propositions are true, but the weak post permits a wrong
-- arbitrary outcome. A second proof of identity cannot supply adequacy.
theorem weak_post_rejected : ¬ (contract_adequacy% weak implies expected) := by
  intro adequate
  have accepted : weak_contract 0 (.ok 1) := by
    simp [weak_contract, RustModel.decode, modelNat]
  have wrong := adequate 0 (.ok 1) accepted
  simp [expected_contract] at wrong

partial spec partial_identity for identity with 0 type parameters
  ensures output => output = x
theorem partial_total_rejected :
    ¬ (contract_adequacy% partial_identity implies expected) := by
  intro adequate
  have accepted : partial_identity_contract 0 .div := by
    intro math decoded
    exact WP.dspec.div _
  have wrong := adequate 0 .div accepted
  simp [expected_contract] at wrong

spec false_ghost (impossible : False) for identity with 0 type parameters
  ensures output => output = x
theorem false_ghost_rejected :
    ¬ (contract_adequacy% false_ghost implies expected) := by
  intro adequate
  have accepted : false_ghost_contract 0 (.ok 1) := by
    intro math decoded impossible
    exact impossible.elim
  have wrong := adequate 0 (.ok 1) accepted
  simp [expected_contract] at wrong

spec fin_zero_ghost (position : Fin 0) for identity with 0 type parameters
  ensures output => output = x
theorem fin_zero_ghost_rejected :
    ¬ (contract_adequacy% fin_zero_ghost implies expected) := by
  intro adequate
  have accepted : fin_zero_ghost_contract 0 (.ok 1) := by
    intro math decoded position
    exact Fin.elim0 position
  have wrong := adequate 0 (.ok 1) accepted
  simp [expected_contract] at wrong

-- A true concrete alias must still specialize its own independent family.
def mismatched_contract (x : Nat) (run : Result Nat) : Prop :=
  WP.spec run (fun output => output = x + 1)
def mismatched : Prop := ∀ x : Nat, expected_contract x (identity x)
example : mismatched := identity_correct
/-- error: Independent proposition RequiredContractTests.mismatched does not specialize its arbitrary-outcome family -/
#guard_msgs in
#check (contract_adequacy% strict implies mismatched)

end RequiredContractTests

namespace GenericUniverseTest
universe u
-- Preserve both universe polymorphism and implicit original type arguments.
def identity {T : Type u} (x : T) : Result T := .ok x
spec identity_spec for @identity with 1 type parameters
  ensures(raw) r => r = x
theorem identity_proof : identity_spec := by
  intro T x provider math decoded
  exact ⟨math, decoded, rfl⟩
def identity_required_contract (T : Type u) (x : T) (run : Result T) : Prop :=
  ∀ [_m : RustModel T], isValid x →
    WP.spec run (fun r => isValid r ∧ r = x)
def identity_required : Prop := ∀ (T : Type u) (x : T),
  identity_required_contract T x (@identity T x)
check_contract identity_required using identity_proof
end GenericUniverseTest
