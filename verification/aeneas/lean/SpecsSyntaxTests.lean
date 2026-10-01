/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import SpecsSyntax
@[expose] public section
open Aeneas Aeneas.Std
namespace SpecsSyntaxTests

aeneas_spec_begin
spec identity (x : Nat)
  for Result.ok x
  ensures out => out = x
aeneas_spec_end

theorem identity_proof : identity := by
  intro x
  exact WP.spec.ret rfl

spec transitive (x y z : Nat)
  for Result.ok x
  requires hxy : x = y
  requires hyz : y = z
  ensures out => out = z

theorem transitive_proof : transitive := by
  intro x y z hxy hyz
  exact WP.spec.ret (hxy.trans hyz)

spec tuple (x : Nat)
  for Result.ok (x, x + 1)
  ensures out state => out = x ∧ state = x + 1

theorem tuple_proof : tuple := by intro x; simp

partial spec diverging
  for (Result.div : Result Nat)
  ensures _ => False

theorem diverging_proof : diverging := WP.dspec.div _

partial spec partial_identity (x : Nat)
  for Result.ok x
  ensures out => out = x

theorem partial_identity_proof : partial_identity := by
  intro x
  exact WP.dspec.ret rfl

-- Independently written propositions pin binders, requirements, and outcomes.
example : identity = (∀ x : Nat, WP.spec (Result.ok x) (fun out => out = x)) := rfl
example : transitive = (∀ x y z : Nat, x = y → y = z →
    WP.spec (Result.ok x) (fun out => out = z)) := rfl
example : tuple = (∀ x : Nat, WP.spec (Result.ok (x, x + 1))
    (fun (out, state) => out = x ∧ state = x + 1)) := rfl
example : diverging = WP.dspec (Result.div : Result Nat) (fun _ => False) := rfl
example : partial_identity = (∀ x : Nat,
    WP.dspec (Result.ok x) (fun out => out = x)) := rfl

spec panic
  for (Result.fail Error.panic : Result Nat)
  ensures _ => True
spec total_diverging
  for (Result.div : Result Nat)
  ensures _ => True
partial spec partial_panic
  for (Result.fail Error.panic : Result Nat)
  ensures _ => True
spec wrong_return
  for Result.ok (0 : Nat)
  ensures out => out = 1

partial spec partial_wrong_return
  for Result.ok (0 : Nat)
  ensures out => out = 1

theorem partial_wrong_return_rejected : ¬ partial_wrong_return := by
  simp [partial_wrong_return]

theorem panic_rejected : ¬ panic := by simp [panic]
theorem divergence_rejected : ¬ total_diverging := by simp [total_diverging]
theorem partial_panic_rejected : ¬ partial_panic := by simp [partial_panic]
theorem wrong_return_rejected : ¬ wrong_return := by simp [wrong_return]

-- A transparent named specification remains compatible with upstream step.
def pair (n : Nat) : Result (Nat × Nat) := .ok (n, n + 1)
spec pair_spec (n : Nat)
  for pair n
  refines Prod.fst to n
  ensures out => out.2 = n + 1
theorem pair_proof : pair_spec := by
  intro n
  exact WP.spec.ret ⟨rfl, rfl⟩
register_spec_step pair_proof

spec pair_caller (n : Nat)
  for (do let out ← pair n; Result.ok out.1)
  refines id to n

theorem pair_caller_proof : pair_caller := by
  intro n
  step*
  simp_all

example : pair_spec = (∀ n : Nat, WP.spec (pair n)
    (fun out => out.1 = n ∧ out.2 = n + 1)) := rfl
example : pair_caller = (∀ n : Nat,
    WP.spec (do let out ← pair n; Result.ok out.1) (fun out => out = n)) := rfl

partial spec partial_view (n : Nat)
  for Result.ok n
  refines Nat.succ to n + 1
partial spec diverging_view
  for (Result.div : Result Nat)
  refines Nat.succ to 0
  ensures out => out = 9

example : partial_view = (∀ n : Nat,
    WP.dspec (Result.ok n) (fun out => Nat.succ out = n + 1)) := rfl
example : diverging_view = WP.dspec (Result.div : Result Nat)
    (fun out => Nat.succ out = 0 ∧ out = 9) := rfl

-- Binding checks inspect elaborated arguments, including implicit coercions.
def unary (x : Nat) : Result Nat := .ok x
def binary (x y : Nat) : Result Nat := .ok (x + y)
def generic (α : Type) (x : α) : Result α := .ok x
def acceptsInt (x : Int) : Result Int := .ok x

spec bound_unary (x : Nat) (ghost : Nat)
  for unary x
  requires h : x = ghost
  ensures out => out = ghost
check_spec_binding bound_unary for unary with 1

spec bound_generic (α : Type) (x : α)
  for generic α x
  ensures out => out = x
check_spec_binding bound_generic for generic with 2

partial spec bound_partial (x : Nat)
  for unary x
  refines Nat.succ to x + 1
check_spec_binding bound_partial for unary with 1

spec coerced_input (x : Nat)
  for acceptsInt x
  ensures _ => True
/-- error: Specification SpecsSyntaxTests.coerced_input model input 1 is not its original bound variable -/
#guard_msgs in
check_spec_binding coerced_input for acceptsInt with 1

spec swapped_inputs (x y : Nat)
  for binary y x
  ensures _ => True
/-- error: Specification SpecsSyntaxTests.swapped_inputs model input 1 is not its original bound variable -/
#guard_msgs in
check_spec_binding swapped_inputs for binary with 2

spec substituted_input (x : Nat)
  for unary 0
  ensures out => out = x
/-- error: Specification SpecsSyntaxTests.substituted_input model input 1 is not its original bound variable -/
#guard_msgs in
check_spec_binding substituted_input for unary with 1

spec shadowed_input (x : Nat) (x : Nat)
  for unary x
  ensures _ => True
/-- error: Specification SpecsSyntaxTests.shadowed_input model input 1 is not its original bound variable -/
#guard_msgs in
check_spec_binding shadowed_input for unary with 1

/-- error: Specification SpecsSyntaxTests.bound_unary does not call the expected model SpecsSyntaxTests.binary -/
#guard_msgs in
check_spec_binding bound_unary for binary with 1

/-- error: Specification SpecsSyntaxTests.bound_generic does not bind exactly 1 model inputs -/
#guard_msgs in
check_spec_binding bound_generic for generic with 1

/-- error: An Aeneas fence must contain exactly one spec declaration -/
#guard_msgs in
aeneas_spec_begin
open Nat
aeneas_spec_end

end SpecsSyntaxTests
