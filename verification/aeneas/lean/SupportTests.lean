/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public import Loops
public import RequiredContracts
@[expose] public section
open Aeneas Aeneas.Std AeneasContracts AeneasSpecs
namespace SupportTests

-- Use upstream checked-operation registrations, including overflow branches.
theorem add_spec (x y : Usize) :
    lift (x.checked_add y)
      ⦃ out => out.map UScalar.val =
        if x.val + y.val ≤ Usize.max then some (x.val + y.val) else none ⦄ := by
  step as ⟨out, hout⟩
  cases out <;> simp_all only [Option.map_none, Option.map_some]
  all_goals scalar_tac +split

theorem sub_spec (x y : Usize) :
    lift (x.checked_sub y)
      ⦃ out => out.map UScalar.val =
        if y ≤ x then some (x.val - y.val) else none ⦄ := by
  step as ⟨out, hout⟩
  cases out <;> simp_all only [Option.map_none, Option.map_some]
  all_goals scalar_tac +split

theorem mul_spec (x y : Usize) :
    lift (x.checked_mul y)
      ⦃ out => out.map UScalar.val =
        if x.val * y.val ≤ Usize.max then some (x.val * y.val) else none ⦄ := by
  step as ⟨out, hout⟩
  cases out <;> simp_all only [Option.map_none, Option.map_some]
  all_goals scalar_tac +split

def pair (n : Nat) : Result (Nat × Nat) := .ok (n, n + 1)

theorem pair_view_spec (n : Nat) :
    pair n
      ⦃ r => Prod.fst r = n ∧ r.2 = n + 1 ⦄ := by
  exact WP.spec.ret ⟨rfl, rfl⟩

attribute [step] pair_view_spec

-- A caller uses the view theorem through Aeneas's existing spec registry.
theorem pair_caller_spec (n : Nat) :
    (do let r ← pair n; Result.ok r.1)
      ⦃ r => id r = n ⦄ := by
  step*
  simp_all

theorem diverging_view_spec :
    (Result.div : Result Nat)
      ⦃ r => Nat.succ r = 0 ∧ r = 9 ⦄div := by
  exact WP.dspec.div _

theorem partial_view_spec (n : Nat) :
    Result.ok n
      ⦃ r => Nat.succ r = n + 1 ⦄div := by
  exact WP.dspec.ret rfl

-- The independent family compares every outcome, even though `pair` itself
-- happens to return the expected pair for every input.
spec pair_inline for pair with 0 type parameters
  ensures (first, second) => first = n ∧ second = n + 1

theorem pair_inline_proof : pair_inline := by
  intro n math decoded
  change some n = some math at decoded
  cases decoded
  exact ⟨(n, n + 1), rfl, rfl, rfl⟩

def pair_required_contract (n : Nat) (run : Result (Nat × Nat)) : Prop :=
  ∃ r, run = .ok r ∧ r.1 = n ∧ r.2 = n + 1

def pair_required : Prop := ∀ n : Nat, pair_required_contract n (pair n)

@[contract_simps] theorem pair_required_bridge (n : Nat) (run : Result (Nat × Nat))
    (provided : pair_inline_contract n run) : pair_required_contract n run := by
  obtain ⟨out, success, math, decoded, first, second⟩ :=
    (WP.spec_equiv_exists _ _).mp (provided n rfl)
  have same : out = math := by
    simpa [RustModel.decode, modelProd] using decoded
  cases same
  exact ⟨out, success, first, second⟩

check_contract pair_required using pair_inline_proof

-- An alias still names its own independent family and canonical inline proof.
def pair_required_again_contract := pair_required_contract
def pair_required_again : Prop := pair_required
@[contract_simps] theorem pair_required_again_bridge
    (n : Nat) (run : Result (Nat × Nat)) (provided : pair_inline_contract n run) :
    pair_required_again_contract n run := pair_required_bridge n run provided
check_contract pair_required_again using pair_inline_proof

example : ∀ n : Nat, WP.spec (do let r ← pair n; Result.ok r.1)
    (fun r => r = n) := pair_caller_spec
example : WP.dspec (Result.div : Result Nat)
    (fun r => Nat.succ r = 0 ∧ r = 9) := diverging_view_spec
example : ∀ n : Nat, WP.dspec (Result.ok n)
    (fun r => Nat.succ r = n + 1) := partial_view_spec

def counterBody (n : Usize) (s : Nat × Usize) :
    Result (ControlFlow (Nat × Usize) Nat) := do
  if s.2 < n then
    let j ← s.2 + 1#usize
    .ok (.cont (s.1 + 1, j))
  else .ok (.done s.1)

theorem counter_spec (n i : Usize) (hi : i ≤ n) :
    loop (counterBody n) (i.val, i) ⦃ out => out = n.val ∧ True ⦄ := by
  apply indexed_loop_spec n.val id (fun i => i) (fun _ => True)
  · intro state idx hidx hv _
    unfold counterBody
    simp only [UScalar.lt_equiv]
    split
    · rename_i hlt
      step as ⟨j, hj⟩
      simp_all [id]
    · rename_i hdone
      exact WP.spec.ret ⟨by scalar_tac, hv, trivial⟩
  · exact (UScalar.le_equiv _ _).mp hi
  · rfl
  · trivial

end SupportTests
