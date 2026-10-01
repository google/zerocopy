/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelTests
public import SpecsSyntax
@[expose] public section

/-!
These independent expansions pin what the authored clause syntax means after
elaboration: original raw execution, dictionary placement, interleaved decoded
witnesses and equations, clause scopes, shared result admission, and total versus
partial correctness. Several examples use competing ghost instances or raw-only
postconditions to ensure those conveniences cannot change provider selection or
remove the obligation to decode a successful return.
-/

open Lean Aeneas Aeneas.Std AeneasSpecs
namespace SpecsSyntaxTests
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- Ordinary Rust assertion harnesses return Unit. The provider lookup reduces
-- that abbreviation to PUnit.{1}; this regression checks the actual function
-- signature, macro expansion, and returned-value decoding together.
def unitAssertionRoot (x : Usize) : Result Unit := do
  massert (x = x)
  .ok ()
check_model_inputs unitAssertionRoot with 0 type parameters
spec unit_assertion_root_spec for unitAssertionRoot with 0 type parameters
  ensures(raw) _ => True

example : unit_assertion_root_spec := by
  intro x decoded hdecoded
  simp [unitAssertionRoot, massert, WP.spec_ok, RustModel.decode, modelUnit]

example : ¬ (Result.fail .panic : Result Unit) ⦃ _ => True ⦄ := by
  simp

-- Bypass the grammar's nonempty-post rule by constructing syntax directly.
-- The elaborator must reject this too, rather than trusting every producer of
-- syntax or silently removing execution and output-decoding obligations.
local macro "empty_spec_body_for_test%" : term => do
  let posts : Array (TSyntax `specPostcondition) := #[]
  `(aeneas_spec_body% unitAssertionRoot with 0 mode% 0
    ghosts% requires% posts% $posts:specPostcondition*)
/-- error: An Aeneas specification must contain at least one ensures clause -/
#guard_msgs in
#check empty_spec_body_for_test%

-- These are authored spec expansions, not only tests of upstream WP. A True
-- post must still reject forbidden execution in both supported modes.
def forbiddenReturn : Result Unit := .fail .undef
spec forbidden_total for forbiddenReturn with 0 type parameters
  ensures _ => True
partial spec forbidden_partial for forbiddenReturn with 0 type parameters
  ensures _ => True
example : ¬forbidden_total := by simp [forbidden_total, forbiddenReturn]
example : ¬forbidden_partial := by simp [forbidden_partial, forbiddenReturn]

def identity (α : Type u) (x : α) : Result α := .ok x
spec identity_spec for @identity with 1 type parameters
  ensures y => y = x
  ensures(raw) y => y = x
check_spec_binding identity_spec for identity with 2
theorem identity_proof : identity_spec := by
  intro α x m mx hx
  simp only [identity, Result.ok]
  exact ⟨mx, hx, rfl, rfl⟩

def sequenceIdentity (xs : List Nat) : Result (List Nat) := .ok xs
spec dependent_spec (position : Fin xs.length) for sequenceIdentity with 0 type parameters
  requires h : position.val < xs.length
  requires(raw) hr : position.val < xs.length
  ensures ys => ys = xs ∧ h = h
  ensures(raw) ys => ys = xs ∧ hr = hr
check_spec_binding dependent_spec for sequenceIdentity with 1

-- The output interpretation is fixed before the competing ghost exists.
def nativeIdentity (x : Nat) : Result Nat := .ok x
spec fixed_provider_spec [evil : RustModel Nat] for nativeIdentity with 0 type parameters
  ensures(raw) y => y = x
example : fixed_provider_spec := by
  intro x mx hx evil
  change some x = some mx at hx
  cases hx
  exact ⟨x, rfl, rfl⟩

-- Independently authored expansions pin the scopes and upstream WP modes.
def wordIdentity (x : Usize) : Result Usize := .ok x
spec word_math for wordIdentity with 0 type parameters
  requires h : x.value < 5
  ensures y => y.value = x.value
spec word_raw for wordIdentity with 0 type parameters
  requires(raw) h : x.val < 5
  ensures(raw) y => y.val = x.val
partial spec word_partial for wordIdentity with 0 type parameters
  ensures y => y.value = x.value
spec word_mixed for wordIdentity with 0 type parameters
  requires h : x.value < 5
  requires(raw) hr : x.val < 5
  ensures y => y.value = x.value ∧ h = h
  ensures(raw) y => y.val = x.val ∧ hr = hr

example : word_math =
    (∀ raw : Usize, ∀ math : UnsignedWord .Usize,
      (modelUScalar .Usize).decode raw = some math →
      (h : math.value < 5) →
      WP.spec (wordIdentity raw) (fun rawOutput =>
        ∃ output : UnsignedWord .Usize,
          (modelUScalar .Usize).decode rawOutput = some output ∧ output.value = math.value)) := rfl
example : word_raw =
    (∀ raw : Usize, ∀ math : UnsignedWord .Usize,
      (modelUScalar .Usize).decode raw = some math →
      (h : raw.val < 5) →
      WP.spec (wordIdentity raw) (fun rawOutput =>
        ∃ output : UnsignedWord .Usize,
          (modelUScalar .Usize).decode rawOutput = some output ∧ rawOutput.val = raw.val)) := rfl
example : word_partial =
    (∀ raw : Usize, ∀ math : UnsignedWord .Usize,
      (modelUScalar .Usize).decode raw = some math →
      WP.dspec (wordIdentity raw) (fun rawOutput =>
        ∃ output : UnsignedWord .Usize,
          (modelUScalar .Usize).decode rawOutput = some output ∧ output.value = math.value)) := rfl
example : word_mixed =
    (∀ raw : Usize, ∀ math : UnsignedWord .Usize,
      (modelUScalar .Usize).decode raw = some math →
      (h : math.value < 5) → (hr : raw.val < 5) →
      WP.spec (wordIdentity raw) (fun rawOutput =>
        ∃ output : UnsignedWord .Usize,
          (modelUScalar .Usize).decode rawOutput = some output ∧
          (output.value = math.value ∧ h = h) ∧ (rawOutput.val = raw.val ∧ hr = hr))) := rfl

-- A generic ghost cannot change the original generated dictionary either.
spec generic_fixed [evil : RustModel α] for @identity with 1 type parameters
  ensures(raw) y => y = x
example : generic_fixed := by
  intro α x original math decoded evil
  exact ⟨math, decoded, rfl⟩

-- Every source generic receives a dictionary, even if unused or result-only.
def unused (α : Type) (x : Nat) : Result Nat := .ok x
spec unused_spec for @unused with 1 type parameters
  ensures y => y = x
example : unused_spec =
    (∀ α : Type, ∀ raw : Nat, ∀ _dictionary : RustModel α,
      ∀ math : Nat, some raw = some math →
      WP.spec (unused α raw) (fun rawOutput => ∃ output : Nat,
        some rawOutput = some output ∧ output = math)) := rfl

def resultOnly (T : Type u) : Result (Option T) := .ok none
spec result_only for @resultOnly with 1 type parameters
  ensures result => result = none
example : result_only := by
  intro T m
  exact ⟨none, rfl, rfl⟩

-- A restrictive supplied interpretation controls both sides of identity.
abbrev positiveOnly : RustModel Nat := ⟨Unit, fun x => if 0 < x then some () else none⟩
example : positiveOnly.decode 0 = none := rfl
example : positiveOnly.decode 1 = some () := rfl
example : WP.spec (identity Nat 1) (fun raw => ∃ value : Unit,
    positiveOnly.decode raw = some value ∧ value = () ∧ raw = 1) :=
  @identity_proof Nat 1 positiveOnly () rfl

-- Concrete function instantiations are supported after Models has supplied
-- every nominal provider. This is distinct from applying a generic Fields
-- family to an undecoded concrete child during ModelShapes.
def concreteBoxIdentity (x : ModelTests.Box ModelTests.Child) :
    Result (ModelTests.Box ModelTests.Child) := .ok x
check_model_inputs concreteBoxIdentity with 0 type parameters
spec concrete_box_identity for concreteBoxIdentity with 0 type parameters
  ensures result => result = x
  ensures(raw) result => result = x
example : concrete_box_identity := by
  intro raw math decoded
  exact ⟨math, decoded, rfl, rfl⟩

def childIdentity (x : ModelTests.Child) : Result ModelTests.Child := .ok x
spec model_dependent_ghost (position : Fin x.value) (constraint : x.positive = x.positive)
    for childIdentity with 0 type parameters
  ensures y => y.value = x.value

-- Native pair projections retain bounded word carriers and Nat coercions.
def pairWords (x : Usize) : Result (Usize × Usize) := .ok (x, x)
spec pair_words for pairWords with 0 type parameters
  ensures (a, b) => (a : Nat) = (x : Nat) ∧ (b : Nat) = (x : Nat)

-- A function-valued payload is rejected before any ghost or clause elaborates.
def escapingOutput (x : Nat) : Result (Nat → Nat) := .ok (fun y => y)
/-- error: Unsupported escaping function or backward reconstruction in model carrier -/
#guard_msgs in
discard_model_fixture spec escaping for escapingOutput with 0 type parameters ensures y => True

/-- error: An Aeneas fence must contain exactly one spec declaration -/
#guard_msgs in
discard_model_fixture aeneas_spec_begin
 def injected : Nat := 0
aeneas_spec_end

def rejectedReturn (x : Nat) : Result
    (core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner) := .ok ⟨0#usize⟩
spec rejected_total for rejectedReturn with 0 type parameters ensures result => True
partial spec rejected_partial for rejectedReturn with 0 type parameters ensures result => True
example : ¬rejected_total := by
  intro contract
  have h := contract 0 0 rfl
  simp [rejectedReturn, WP.spec, WP.dspec, RustModel.decode, modelNonZeroUScalar] at h
example : ¬rejected_partial := by
  intro contract
  have h := contract 0 0 rfl
  simp [rejectedReturn, WP.spec, WP.dspec, RustModel.decode, modelNonZeroUScalar] at h

-- Five generic raw arguments exercise arbitrary-arity witness elimination.
-- Only the original raw telescope is passed to the extracted function.
def fiveInputs (T : Type u) (a b c d e : T) : Result T := .ok a
spec five_inputs_raw for @fiveInputs with 1 type parameters
  requires(raw) accepted : True
  ensures(raw) result => result = a
check_spec_binding five_inputs_raw for fiveInputs with 6
example : five_inputs_raw.{u} =
    (∀ T : Type u, ∀ a b c d e : T, ∀ [m : RustModel T],
      ∀ ma : m.Model, m.decode a = some ma →
      ∀ mb : m.Model, m.decode b = some mb →
      ∀ mc : m.Model, m.decode c = some mc →
      ∀ md : m.Model, m.decode d = some md →
      ∀ me : m.Model, m.decode e = some me →
      (accepted : True) →
      WP.spec (fiveInputs T a b c d e) (fun rawOutput =>
        ∃ output : m.Model, m.decode rawOutput = some output ∧ rawOutput = a)) := rfl
example : five_inputs_raw.{u} =
    (∀ T : Type u, ∀ a b c d e : T, ∀ [m : RustModel T],
      isValid a → isValid b → isValid c → isValid d → isValid e →
      (accepted : True) →
      WP.spec (fiveInputs T a b c d e) (fun rawOutput => isValid rawOutput ∧ rawOutput = a)) := by
  apply propext
  simp only [five_inputs_raw, isValid, forall_exists_index, WP.spec_equiv_exists, exists_and_left, exists_and_right]

-- Two words also pin alternating witness/equation order independently of the
-- generic dictionary case above.
def pairFunction (a b : Nat) : Result (Nat × Nat) := .ok (a, b)
spec pair_words_interleaved for pairFunction with 0 type parameters
  ensures(raw) result => result = (a, b)
example : pair_words_interleaved =
    (∀ a b : Nat, ∀ ma : Nat, some a = some ma →
      ∀ mb : Nat, some b = some mb →
      WP.spec (pairFunction a b) (fun rawOutput => ∃ output : Nat × Nat,
        (modelProd : RustModel (Nat × Nat)).decode rawOutput = some output ∧ rawOutput = (a, b))) := rfl
@[aeneas_spec] abbrev swapped : Prop := ∀ a b : Nat,
  WP.spec (pairFunction b a) (fun _ => True)
/-- error: Specification SpecsSyntaxTests.swapped model input 1 is not its original bound variable -/
#guard_msgs in
check_spec_binding swapped for pairFunction with 2

/-- error: Specification binder x shadows an original input or an earlier binder -/
#guard_msgs in
discard_model_fixture spec shadows (x : Nat) for nativeIdentity with 0 type parameters
  ensures y => True

/-- error: Specification binder h shadows an original input or an earlier binder -/
#guard_msgs in
discard_model_fixture spec duplicate_requires for nativeIdentity with 0 type parameters
  requires h : True
  requires(raw) h : True
  ensures y => True

end SpecsSyntaxTests
