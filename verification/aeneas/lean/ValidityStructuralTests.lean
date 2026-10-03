/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ValidityNative
public import DeriveValidity
@[expose] public section

open Lean Aeneas Aeneas.Std AeneasSpecs
namespace ValidityStructuralTests
set_option linter.unusedVariables false

-- Rejecting a declaration must not export Lean's error-recovery placeholder.
syntax (name := discardedValidityFixture) "discard_validity_fixture " command : command
@[command_elab discardedValidityFixture] meta def discardValidityFixture :
    Lean.Elab.Command.CommandElab := fun stx =>
  Lean.withoutModifyingEnv (Lean.Elab.Command.elabCommand stx[1])

structure Child where
  val : Nat

aeneas_invariant_begin
 aeneas_invariant child_valid for Child with 0 type parameters := fun self => 0 < self.val
aeneas_invariant_end
derive_model_validity Child with 0 type parameters
check_invariant_binding child_valid for Child with 0 type parameters

example (n : Nat) : @isValid Child Child.aeneasValid ⟨n⟩ =
    ((True ∧ True) ∧ 0 < n) := rfl
example : ¬isValid (Child.mk 0) := by
  change ¬((True ∧ True) ∧ 0 < (0 : Nat))
  simp

structure Parent where
  child : Child
derive_model_validity Parent with 0 type parameters
example (n : Nat) : isValid (Parent.mk ⟨n⟩) ↔ 0 < n := by
  change (((True ∧ True) ∧ 0 < n) ∧ True) ↔ 0 < n
  simp

structure Box (valid_0 : Type u) where
  val : valid_0
aeneas_invariant box_valid for Box with 1 type parameters :=
  fun self => isValid (α := valid_0) self.val
derive_model_validity Box with 1 type parameters
check_invariant_binding box_valid for Box with 1 type parameters
example (α : Type u) (P : α → Prop) (x : α) :
    @isValid (Box α) (@Box.aeneasValid α ⟨P⟩) ⟨x⟩ ↔ P x := by
  change ((P x ∧ True) ∧ P x) ↔ P x
  simp

structure Nested (α : Type u) where
  values : Option (List α)
derive_model_validity Nested with 1 type parameters
example (α : Type u) (P : α → Prop) (xs : Option (List α)) :
    @isValid (Nested α) (@Nested.aeneasValid α ⟨P⟩) ⟨xs⟩ =
      ((∀ ys ∈ xs, ∀ x ∈ ys, P x) ∧ True) := rfl

inductive Choice (α : Type u) where
  | one : α → Choice α
  | none : Choice α
derive_model_validity Choice with 1 type parameters
example (α : Type u) (P : α → Prop) (x : α) :
    @isValid (Choice α) (@Choice.aeneasValid α ⟨P⟩) (.one x) = (P x ∧ True) := rfl
example (α : Type u) (P : α → Prop) :
    @isValid (Choice α) (@Choice.aeneasValid α ⟨P⟩) .none = True := rfl

abbrev ChildAlias := Child
example : (inferInstance : IsValid ChildAlias) = Child.aeneasValid := rfl

structure SameShape where
  val : Nat
derive_model_validity SameShape with 0 type parameters
run_meta do
  if ← Lean.Meta.isDefEq (Lean.mkConst ``Child) (Lean.mkConst ``SameShape) then
    throwError "Distinct nominal carriers were flattened"

example (α : Type u) (P : α → Prop) (n : Usize) (xs : Aeneas.Std.Array α n) :
    @isValid (Aeneas.Std.Array α n) (@validArray α n ⟨P⟩) xs = (∀ x ∈ xs.val, P x) := rfl

-- All expected dictionaries are chosen before any mathematical ghosts exist.
def nested_model (α : Type u) (x : Nested α) : Result (Option (Choice α)) := .ok .none
check_model_validity_inputs nested_model with 1 type parameters
def native_model (x : core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner) :
    Result (core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner) := .ok x
check_model_validity_inputs native_model with 0 type parameters
def array_model (x : Aeneas.Std.Array Child (Usize.ofNat 2)) :
    Result (Aeneas.Std.Array Child (Usize.ofNat 2)) := .ok x
check_model_validity_inputs array_model with 0 type parameters

structure Missing where
  val : Nat
structure MissingParent where
  child : Missing
/-- error: failed to synthesize
  IsValid Missing

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
discard_validity_fixture derive_model_validity MissingParent with 0 type parameters

structure SelfReference where
  val : Nat
/-- error: failed to synthesize instance of type class
  IsValid SelfReference

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
discard_validity_fixture aeneas_invariant self_valid for SelfReference with 0 type parameters := fun self => isValid self

/-- error: An Aeneas type fence must contain exactly one invariant declaration -/
#guard_msgs in
discard_validity_fixture aeneas_invariant_begin
 def injected : Nat := 0
aeneas_invariant_end

structure Unattached where
  val : Nat
aeneas_invariant unattached_valid for Unattached with 0 type parameters := fun _ => True
/-- error: Missing registered derived validity instance for ValidityStructuralTests.Unattached -/
#guard_msgs in
discard_validity_fixture check_invariant_binding unattached_valid for Unattached with 0 type parameters

structure Detached where
  val : Nat
aeneas_invariant detached_valid for Detached with 0 type parameters := fun self => 0 < self.val
@[reducible] instance Detached.aeneasValid : IsValid Detached := ⟨fun _ => True⟩
/-- error: Authored invariant is absent from derived validity for ValidityStructuralTests.Detached -/
#guard_msgs in
discard_validity_fixture check_invariant_binding detached_valid for Detached with 0 type parameters

/-- error: Missing or ambiguous invariant binding for ValidityStructuralTests.unregistered -/
#guard_msgs in
discard_validity_fixture run_meta do
  let _ ← invariantBinding `ValidityStructuralTests.unregistered

end ValidityStructuralTests
