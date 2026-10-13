/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import SpecsSyntax
@[expose] public section

/-!
These tests use small dictionaries so the expected propositions are visible.
The examples check the expansion independently of a Rust function's proof:
unused bounds still supply their laws, and a child supplies the law for its
actual parent dictionary. Implementation checks must reject extra premises and
proofs about a different dictionary, even when that other proof is correct.
-/
open Lean Elab Term Aeneas Aeneas.Std AeneasSpecs
namespace TraitLawsTests

structure Alignment (Self : Type) where
  alignment : Nat

structure Child (Self : Type) where
  parent : Alignment Self

trait_dictionary @Alignment
trait_dictionary @Child
trait_invariant aligned for @Alignment with 1 type parameters where self =>
  self.alignment = 1

def readAlignment {T : Type} (dictionary : Alignment T) : Result Nat :=
  .ok dictionary.alignment

def readParent {T : Type} (dictionary : Child T) : Result Nat :=
  .ok dictionary.parent.alignment

def unused {T : Type} (_dictionary : Alignment T) (n : Nat) : Result Nat := .ok n

check_model_inputs readAlignment with 1 type parameters
spec read_spec for @readAlignment with 1 type parameters
  ensures result => result = 1
spec child_spec for @readParent with 1 type parameters
  ensures result => result = 1
spec unused_spec for @unused with 1 type parameters
  ensures result => result = n

-- Check the complete generated domain, not only a proof on one dictionary.
example : read_spec = (∀ (T : Type) (dictionary : Alignment T) [_meaning : RustModel T]
    [_law : aligned T dictionary],
    readAlignment dictionary ⦃ r => ∃ decoded : Nat,
      RustModel.decode r = some decoded ∧ decoded = 1 ⦄) := rfl

example : child_spec = (∀ (T : Type) (dictionary : Child T) [_meaning : RustModel T]
    [_law : aligned T dictionary.parent],
    readParent dictionary ⦃ r => ∃ decoded : Nat,
      RustModel.decode r = some decoded ∧ decoded = 1 ⦄) := rfl

example : unused_spec = (∀ (T : Type) (dictionary : Alignment T) (n : Nat)
    [_meaning : RustModel T] [_law : aligned T dictionary], ∀ decoded : Nat,
    RustModel.decode n = some decoded →
      unused dictionary n ⦃ r => ∃ result : Nat,
        RustModel.decode r = some result ∧ result = decoded ⦄) := rfl

def good : Alignment Unit := ⟨1⟩
def other : Alignment Unit := ⟨2⟩
theorem good_law : aligned Unit good := ⟨rfl⟩

-- The law is inhabited for a valid dictionary, but excludes an invalid one.
-- This kernel theorem keeps the negative checker tests from testing a vacuous
-- registry convention whose law accepts every implementation.
theorem other_has_no_law : ¬ aligned Unit other := by
  intro evidence
  exact (by decide : (2 : Nat) ≠ 1) (@aligned.holds Unit other evidence)
check_trait_law @aligned for @good using @good_law

def forward {T : Type} (dictionary : Alignment T) : Alignment T := dictionary
theorem forward_law (T : Type) (dictionary : Alignment T)
    [law : aligned T dictionary] : aligned T (@forward T dictionary) := law
check_trait_law @aligned for @forward using @forward_law

-- This tempting theorem proves nothing about an implementation: it assumes
-- exactly the conclusion. The checker must not accept that extra premise.
theorem assumed_law (law : aligned Unit other) : aligned Unit other := law

/-- Test rejection without depending on pretty-printer formatting. -/
private meta def rejects (action : TermElabM Unit) : TermElabM Unit := do
  let rejected ← try action; pure false catch _ => pure true
  unless rejected do throwError "Expected the trait-law checker to reject this declaration"

run_elab do
  let expected ← traitImplementationObligation `TraitLawsTests.aligned `TraitLawsTests.other
  -- Construct the expected telescope outside the rejection handler: a broken
  -- registry or obligation generator must fail the test, not count as rejection.
  rejects do
    unless ← Meta.isDefEq (← getConstInfo `TraitLawsTests.good_law).type expected do
      throwError "Different dictionary"
run_elab do
  let expected ← traitImplementationObligation `TraitLawsTests.aligned `TraitLawsTests.other
  rejects do
    unless ← Meta.isDefEq (← getConstInfo `TraitLawsTests.assumed_law).type expected do
      throwError "Extra premise"

end TraitLawsTests
