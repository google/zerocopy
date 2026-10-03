/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import SpecsSyntax
public import ValidityFallback
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace SpecsSyntaxTests

-- Several probes intentionally retain unused Rust and instance binders.
set_option linter.unusedVariables false

-- Failed declaration elaboration may create a recovery declaration. Preserve
-- diagnostics while keeping rejected fixtures out of the imported environment.
syntax (name := discardedSpecFixture) "discard_spec_fixture " command : command
@[command_elab discardedSpecFixture] meta def discardSpecFixture :
    Lean.Elab.Command.CommandElab := fun stx =>
  Lean.withoutModifyingEnv (Lean.Elab.Command.elabCommand stx[1])

-- The original prefix comes solely from the model, including its authored names.
def identity (x : Nat) : Result Nat := .ok x
def transitive (x y z : Nat) : Result Nat := .ok x
def pair (n : Nat) : Result (Nat × Nat) := .ok (n, n + 1)
def pairCaller (n : Nat) : Result Nat := do let out ← pair n; Result.ok out.1
def diverging : Result Nat := .div
def panicking : Result Nat := .fail Error.panic
def zero : Result Nat := .ok 0

aeneas_spec_begin
spec identity_spec for @identity with 0 type parameters
  ensures out => out = x
aeneas_spec_end

theorem identity_proof : identity_spec := by
  intro x
  exact WP.spec.ret rfl

spec transitive_spec for @transitive with 0 type parameters
  requires hxy : x = y
  requires hyz : y = z
  ensures out => out = z

theorem transitive_proof : transitive_spec := by
  intro x y z hxy hyz
  exact WP.spec.ret (hxy.trans hyz)

spec tuple_spec for @pair with 0 type parameters
  ensures out state => out = n ∧ state = n + 1

theorem tuple_proof : tuple_spec := by intro n; simp [pair]

spec tuple_pattern for @pair with 0 type parameters
  ensures (out, state) => out = n ∧ state = n + 1
example : tuple_pattern := tuple_proof
spec grouped_tuple for @pair with 0 type parameters
  ensures (out state : Nat) => out = n ∧ state = n + 1
example : grouped_tuple := tuple_proof

partial spec diverging_spec for @diverging with 0 type parameters
  ensures _ => False
theorem diverging_proof : diverging_spec := WP.dspec.div _

partial spec partial_identity for @identity with 0 type parameters
  ensures out => out = x
theorem partial_identity_proof : partial_identity := by
  intro x
  exact WP.dspec.ret rfl

-- Independent propositions pin the introduced signature and simplification of
-- trivial Nat/product predicates, as well as requirement and tuple semantics.
example : identity_spec = (∀ x : Nat,
    WP.spec (identity x) (fun out => out = x)) := rfl
example : transitive_spec = (∀ x y z : Nat, x = y → y = z →
    WP.spec (transitive x y z) (fun out => out = z)) := rfl
example : tuple_spec = (∀ n : Nat, WP.spec (pair n)
    (fun (out, state) => out = n ∧ state = n + 1)) := rfl
example : diverging_spec = WP.dspec diverging (fun _ => False) := rfl
example : partial_identity = (∀ x : Nat,
    WP.dspec (identity x) (fun out => out = x)) := rfl

spec panic for @panicking with 0 type parameters ensures _ => True
spec total_diverging for @diverging with 0 type parameters ensures _ => True
partial spec partial_panic for @panicking with 0 type parameters ensures _ => True
spec wrong_return for @zero with 0 type parameters ensures out => out = 1
partial spec partial_wrong_return for @zero with 0 type parameters
  ensures out => out = 1

theorem panic_rejected : ¬ panic := by simp [panic, panicking]
theorem divergence_rejected : ¬ total_diverging := by simp [total_diverging, diverging]
theorem partial_panic_rejected : ¬ partial_panic := by simp [partial_panic, panicking]
theorem wrong_return_rejected : ¬ wrong_return := by simp [wrong_return, zero]
theorem partial_wrong_return_rejected : ¬ partial_wrong_return := by
  simp [partial_wrong_return, zero]

-- The native step adapter remains a theorem with the expanded specification.
spec pair_spec for @pair with 0 type parameters
  refines Prod.fst to n
  ensures out => out.2 = n + 1
theorem pair_proof : pair_spec := by
  intro n
  exact WP.spec.ret ⟨rfl, rfl⟩
register_spec_step pair_proof

spec pair_caller for @pairCaller with 0 type parameters refines id to n

theorem pair_caller_proof : pair_caller := by
  intro n
  unfold pairCaller
  step*
  all_goals simp_all

example : pair_spec = (∀ n : Nat, WP.spec (pair n)
    (fun out => out.1 = n ∧ out.2 = n + 1)) := rfl
example : pair_caller = (∀ n : Nat,
    WP.spec (pairCaller n) (fun out => out = n)) := rfl

partial spec partial_view for @identity with 0 type parameters
  refines Nat.succ to x + 1
partial spec diverging_view for @diverging with 0 type parameters
  refines Nat.succ to 0 ensures out => out = 9

example : partial_view = (∀ x : Nat,
    WP.dspec (identity x) (fun out => Nat.succ out = x + 1)) := rfl
example : diverging_view = WP.dspec diverging
    (fun out => Nat.succ out = 0 ∧ out = 9) := rfl

-- Uniform dictionary binders include unused and result-only type parameters.
def generic (T : Type u) (x : T) : Result T := .ok x
def implicitGeneric {T : Type u} (x : T) : Result T := .ok x
def unused (T : Type u) (x : Nat) : Result Nat := .ok x
def resultOnly (T : Type u) : Result (Option T) := .ok none
def concreteContainers (xs : Option (List Nat)) : Result (Option (List Nat)) := .ok xs
def nested (T : Type u) (x : Option (List T)) : Result (Option (List T)) := .ok x

spec generic_spec for @generic with 1 type parameters ensures out => out = x
spec implicit_generic_spec for @implicitGeneric with 1 type parameters ensures out => out = x
spec unused_spec for @unused with 1 type parameters ensures out => out = x
spec result_only_spec for @resultOnly with 1 type parameters ensures out => out = none
spec concrete_containers for @concreteContainers with 0 type parameters ensures out => out = xs
spec nested_spec for @nested with 1 type parameters ensures out => out = x

example : generic_spec.{u} = (∀ (T : Type u) (x : T) [IsValid T],
    isValid x → WP.spec (generic T x) (fun out => isValid out ∧ out = x)) := rfl
example : implicit_generic_spec.{u} = (∀ (T : Type u) (x : T) [IsValid T],
    isValid x → WP.spec (@implicitGeneric T x) (fun out => isValid out ∧ out = x)) := rfl
example : unused_spec.{u} = (∀ (T : Type u) (x : Nat) [IsValid T],
    WP.spec (unused T x) (fun out => out = x)) := rfl
example : result_only_spec.{u} = (∀ (T : Type u) [IsValid T],
    WP.spec (resultOnly T) (fun out => isValid out ∧ out = none)) := rfl
example : concrete_containers = (∀ xs : Option (List Nat),
    WP.spec (concreteContainers xs) (fun out => out = xs)) := rfl
example : nested_spec.{u} = (∀ (T : Type u) (x : Option (List T)) [IsValid T],
    isValid x → WP.spec (nested T x) (fun out => isValid out ∧ out = x)) := rfl

theorem generic_proof : generic_spec := by
  intro T x validity hx
  exact WP.spec.ret ⟨hx, rfl⟩
register_spec_step generic_proof
example : unused_spec := by intro T x validity; exact WP.spec.ret rfl
example : result_only_spec := by
  intro T validity
  exact WP.spec.ret ⟨by simp, rfl⟩
example : nested_spec := by intro T x validity hx; exact WP.spec.ret ⟨hx, rfl⟩

-- A conditional theorem admits arbitrary predicates, even False. Distinct
-- predicates over the same carrier are preserved by explicit dictionaries.
abbrev positiveNat : IsValid Nat := ⟨fun x => 0 < x⟩
abbrev noNat : IsValid Nat := ⟨fun _ => False⟩
example : IsValid.isValid (self := positiveNat) 3 →
    WP.spec (generic Nat 3) (fun out => IsValid.isValid (self := positiveNat) out ∧ out = 3) :=
  @generic_proof Nat 3 positiveNat
example : IsValid.isValid (self := noNat) 3 →
    WP.spec (generic Nat 3) (fun out => IsValid.isValid (self := noNat) out ∧ out = 3) :=
  @generic_proof Nat 3 noNat

-- The callee's output validity is enough to discharge the caller's automatic
-- obligation; the caller forwards its supplied dictionary through native step.
def genericCaller (T : Type u) (x : T) : Result T := do
  let out ← generic T x
  Result.ok out
spec generic_caller for @genericCaller with 1 type parameters ensures out => out = x
example : generic_caller := by
  intro T x validity hx
  unfold genericCaller
  step*

-- Freeze automatic dictionaries before mathematical ghosts: an authored local
-- instance changes authored isValid references, but cannot change Rust validity.
spec frozen_generic [ghost : IsValid T] for @generic with 1 type parameters
  ensures out => out = x
example : frozen_generic.{u} = (∀ (T : Type u) (x : T) [rust : IsValid T]
    [ghost : IsValid T], IsValid.isValid (self := rust) x →
    WP.spec (generic T x) (fun out => IsValid.isValid (self := rust) out ∧ out = x)) := rfl
example : frozen_generic := by
  intro T x rust ghost hx
  exact WP.spec.ret ⟨hx, rfl⟩

spec frozen_authored [ghost : IsValid T] for @generic with 1 type parameters
  ensures out => isValid out
example : frozen_authored.{u} = (∀ (T : Type u) (x : T) [rust : IsValid T]
    [ghost : IsValid T], IsValid.isValid (self := rust) x →
    WP.spec (generic T x) (fun out => IsValid.isValid (self := rust) out ∧
      IsValid.isValid (self := ghost) out)) := rfl

-- Runtime validity is about the raw successful payload, before tuple patterns
-- or a projection view. A True postcondition and constant view cannot hide it.
structure Positive where
  value : Nat
instance validPositive : IsValid Positive := ⟨fun x => 0 < x.value⟩
def invalid : Result Positive := .ok ⟨0⟩
def invalidPair : Result (Positive × Nat) := .ok (⟨0⟩, 1)
def positiveDiverging : Result Positive := .div
def valid : Result Positive := .ok ⟨1⟩
def positiveIdentity (self : Positive) : Result Positive := .ok self
spec invalid_true for @invalid with 0 type parameters ensures _ => True
spec invalid_view for @invalid with 0 type parameters refines (fun _ => 0 : Positive → Nat) to 0
partial spec partial_invalid for @invalid with 0 type parameters ensures _ => True
spec invalid_pattern for @invalidPair with 0 type parameters
  ensures (out, state) => state = 1
partial spec positive_diverging for @positiveDiverging with 0 type parameters ensures _ => False
spec valid_true for @valid with 0 type parameters ensures _ => True
spec positive_identity (ghost : Positive) for @positiveIdentity with 0 type parameters
  requires h : self = ghost ensures out => out = ghost

example : ¬ invalid_true := by simp [invalid_true, invalid]
example : ¬ invalid_view := by simp [invalid_view, invalid]
example : ¬ partial_invalid := by simp [partial_invalid, invalid]
example : ¬ invalid_pattern := by simp [invalid_pattern, invalidPair]
example : positive_diverging := WP.dspec.div _
example : valid_true := by simp [valid_true, valid]
example : positive_identity = (∀ (self : Positive) (ghost : Positive),
    isValid self → self = ghost → WP.spec (positiveIdentity self)
      (fun out => isValid out ∧ out = ghost)) := rfl
example : positive_identity := by
  intro self ghost hvalid heq
  exact WP.spec.ret ⟨hvalid, heq⟩

-- A frozen Rust Result dictionary must retain validity in both payload arms.
abbrev PositiveResult := core.result.Result Positive Positive
def invalidRustOk : Result PositiveResult := .ok (.Ok ⟨0⟩)
def invalidRustErr : Result PositiveResult := .ok (.Err ⟨0⟩)
def validRustErr : Result PositiveResult := .ok (.Err ⟨1⟩)
spec invalid_rust_ok for @invalidRustOk with 0 type parameters ensures _ => True
spec invalid_rust_view for @invalidRustOk with 0 type parameters
  refines (fun _ => 0 : PositiveResult → Nat) to 0
spec invalid_rust_err for @invalidRustErr with 0 type parameters ensures _ => True
spec valid_rust_err for @validRustErr with 0 type parameters ensures _ => True
example : ¬ invalid_rust_ok := by
  simp [invalid_rust_ok, invalidRustOk, isValid, IsValid.isValid]
example : ¬ invalid_rust_view := by
  simp [invalid_rust_view, invalidRustOk, isValid, IsValid.isValid]
example : ¬ invalid_rust_err := by
  simp [invalid_rust_err, invalidRustErr, isValid, IsValid.isValid]
example : valid_rust_err := by
  simp [valid_rust_err, validRustErr, isValid, IsValid.isValid]

-- Concrete native step uses the fixed canonical predicate too.
spec positive_plain for @positiveIdentity with 0 type parameters
  ensures out => out = self
theorem positive_proof : positive_plain := by
  intro self hvalid
  exact WP.spec.ret ⟨hvalid, rfl⟩
register_spec_step positive_proof

def positiveCaller (self : Positive) : Result Positive := do
  let out ← positiveIdentity self
  Result.ok out
spec positive_caller for @positiveCaller with 0 type parameters ensures out => out = self
example : positive_caller := by
  intro self hvalid
  unfold positiveCaller
  step*

-- No validity premise is imposed on the ghost. Requirements can depend on
-- earlier named requirements without altering the original call prefix.
spec dependent_requirements (ghost : Nat) for @identity with 0 type parameters
  requires h : x = ghost
  requires hh : h = h
  ensures out => out = ghost
example : dependent_requirements := by
  intro x ghost h hh
  exact WP.spec.ret h

check_spec_binding generic_spec for generic with 2
check_spec_binding positive_identity for positiveIdentity with 1
check_spec_binding pair_spec for pair with 1

-- Generated syntax cannot substitute, coerce, or swap the model inputs. The
-- retained expression audit also rejects deliberately malformed declarations.
def binary (x y : Nat) : Result Nat := .ok (x + y)
def acceptsInt (x : Int) : Result Int := .ok x
@[aeneas_spec] abbrev swapped_inputs : Prop :=
  ∀ x y : Nat, WP.spec (binary y x) (fun _ => True)
@[aeneas_spec] abbrev coerced_input : Prop :=
  ∀ x : Nat, WP.spec (acceptsInt x) (fun _ => True)
@[aeneas_spec] abbrev substituted_input : Prop :=
  ∀ x : Nat, WP.spec (identity 0) (fun out => out = x)

/-- error: Specification SpecsSyntaxTests.swapped_inputs model input 1 is not its original bound variable -/
#guard_msgs in
check_spec_binding swapped_inputs for binary with 2
/-- error: Specification SpecsSyntaxTests.coerced_input model input 1 is not its original bound variable -/
#guard_msgs in
check_spec_binding coerced_input for acceptsInt with 1
/-- error: Specification SpecsSyntaxTests.substituted_input model input 1 is not its original bound variable -/
#guard_msgs in
check_spec_binding substituted_input for identity with 1

/-- error: Specification binder x shadows an original input or an earlier binder -/
#guard_msgs in
discard_spec_fixture spec shadowed_input (x : Nat) for @identity with 0 type parameters ensures _ => True
/-- error: Specification binder x shadows an original input or an earlier binder -/
#guard_msgs in
discard_spec_fixture spec shadowed_requirement for @identity with 0 type parameters
  requires x : True ensures _ => True
/-- error: Specification binder ghost shadows an original input or an earlier binder -/
#guard_msgs in
discard_spec_fixture spec duplicate_ghost (ghost ghost : Nat) for @identity with 0 type parameters ensures _ => True
/-- error: A specification must name a bare model constant -/
#guard_msgs in
discard_spec_fixture spec applied_call for binary 0 1 with 0 type parameters ensures _ => True
/-- error: The supplied Rust type-parameter count omits a model type parameter -/
#guard_msgs in
discard_spec_fixture spec missing_generic for @generic with 0 type parameters ensures _ => True
/-- error: Rust type parameters must be the original model's Type-valued prefix -/
#guard_msgs in
discard_spec_fixture spec too_many_generics for @identity with 1 type parameters ensures _ => True
/-- error: Specification SpecsSyntaxTests.identity_spec does not call the expected model SpecsSyntaxTests.binary -/
#guard_msgs in
check_spec_binding identity_spec for binary with 1
/-- error: Specification SpecsSyntaxTests.generic_spec does not bind exactly 1 model inputs -/
#guard_msgs in
check_spec_binding generic_spec for generic with 1
/-- error: An Aeneas fence must contain exactly one spec declaration -/
#guard_msgs in
aeneas_spec_begin
open Nat
aeneas_spec_end

end SpecsSyntaxTests
