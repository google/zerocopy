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

-- A predicate can inspect its actual generic model. Only Self is captured;
-- the unrelated Rust parameter does not become an extra law index.
structure Represented (Self Ignored : Type) where
  marker : Unit
trait_dictionary @Represented
trait_invariant represented for @Represented with 2 type parameters where self =>
  ∀ value : Self, RustModel.decode value = RustModel.decode value

example (T U : Type) (dictionary : Represented T U) [meaning : RustModel T] :
    @represented T U dictionary meaning := ⟨fun _ => rfl⟩

structure ByteLike (Self : Type) where
  marker : Unit
trait_dictionary @ByteLike
trait_invariant byteLike for @ByteLike with 1 type parameters where self =>
  ∀ value : Self, RustModel.decode value = RustModel.decode value

def modelDependentUnused {T : Type} (_dictionary : ByteLike T) (n : Nat) : Result Nat := .ok n
spec modeled_unused_spec for @modelDependentUnused with 1 type parameters
  ensures result => result = n
example : modeled_unused_spec = (∀ (T : Type) (dictionary : ByteLike T) (n : Nat)
    [meaning : RustModel T] [_law : @byteLike T dictionary meaning], ∀ decoded : Nat,
    RustModel.decode n = some decoded →
      modelDependentUnused dictionary n ⦃ r => ∃ result : Nat,
        RustModel.decode r = some result ∧ result = decoded ⦄) := rfl

def arrayDictionary {T : Type} (N : Usize) (_dictionary : ByteLike T) :
    ByteLike (Aeneas.Std.Array T N) := ⟨()⟩
theorem array_dictionary_law (T : Type) (N : Usize) (dictionary : ByteLike T)
    [meaning : RustModel T] [_law : @byteLike T dictionary meaning] :
    @byteLike (Aeneas.Std.Array T N) (@arrayDictionary T N dictionary)
      (@modelArray T N meaning) := ⟨fun _ => rfl⟩
check_trait_law @byteLike for @arrayDictionary using @array_dictionary_law

-- A different provider and an implementation's own output law both change
-- the proof's exact domain, even when the predicate happens to be provable.
@[reducible] def alternateArrayModel (T : Type) (N : Usize) : RustModel (Aeneas.Std.Array T N) where
  Model := Aeneas.Std.Array T N
  «decode» := some
theorem wrong_provider (T : Type) (N : Usize) (dictionary : ByteLike T)
    [meaning : RustModel T] [_law : @byteLike T dictionary meaning] :
    @byteLike (Aeneas.Std.Array T N) (@arrayDictionary T N dictionary)
      (alternateArrayModel T N) :=
  @byteLike.mk (Aeneas.Std.Array T N) (@arrayDictionary T N dictionary)
    (alternateArrayModel T N) (fun value =>
      Eq.refl (@RustModel.decode _ (alternateArrayModel T N) value))
theorem self_law_premise (T : Type) (N : Usize) (dictionary : ByteLike T)
    [meaning : RustModel T] [_law : @byteLike T dictionary meaning]
    [own : @byteLike (Aeneas.Std.Array T N) (@arrayDictionary T N dictionary)
      (@modelArray T N meaning)] :
    @byteLike (Aeneas.Std.Array T N) (@arrayDictionary T N dictionary)
      (@modelArray T N meaning) := own
theorem mismatched_const (T : Type) (N : Usize) (dictionary : ByteLike T)
    [meaning : RustModel T] [_law : @byteLike T dictionary meaning] :
    @byteLike (Aeneas.Std.Array T 0#usize) (@arrayDictionary T 0#usize dictionary)
      (@modelArray T 0#usize meaning) := by
  -- Retain N in the telescope while proving only the wrong fixed application.
  have _ := N
  exact ⟨fun _ => rfl⟩
theorem omitted_const (T : Type) (dictionary : ByteLike T)
    [meaning : RustModel T] [_law : @byteLike T dictionary meaning] :
    @byteLike (Aeneas.Std.Array T 0#usize) (@arrayDictionary T 0#usize dictionary)
      (@modelArray T 0#usize meaning) := ⟨fun _ => rfl⟩
run_elab do
  let expected ← traitImplementationObligation `TraitLawsTests.byteLike
    `TraitLawsTests.arrayDictionary
  for proof in #[`TraitLawsTests.wrong_provider, `TraitLawsTests.self_law_premise,
      `TraitLawsTests.omitted_const, `TraitLawsTests.mismatched_const] do
    rejects do
      unless ← Meta.isDefEq (← getConstInfo proof).type expected do
        throwError "Wrong provider, const, or extra output-law premise"

run_elab do
  let original := #[Json.mkObj [("index", toJson (0 : Nat)), ("name", toJson "N"),
    ("type", toJson "usize")]]
  checkTraitImplementationNativeParameters `TraitLawsTests.arrayDictionary 1 1 1 original
  rejects do
    checkTraitImplementationNativeParameters `TraitLawsTests.arrayDictionary 1 0 1 #[]
  rejects do
    checkTraitImplementationNativeParameters `TraitLawsTests.arrayDictionary 1 1 1
      #[Json.mkObj [("index", toJson (0 : Nat)), ("name", toJson "Wrong"),
        ("type", toJson "usize")]]

inductive MissingModel where
  | value
def missingModelDictionary : ByteLike MissingModel := ⟨()⟩
run_elab do
  rejects do
    let _ ← traitImplementationObligation `TraitLawsTests.byteLike
      `TraitLawsTests.missingModelDictionary
  let some registration ← traitDictionary? (mkConst `TraitLawsTests.Represented)
    | throwError "Missing test registration"
  unless registration.modelParameters == #[0] do
    throwError "Model-independent parameter was captured"
  checkTraitLawModelParameters registration 2
  rejects do
    checkTraitLawModelParameters {registration with modelParameters := #[1]} 2

end TraitLawsTests
