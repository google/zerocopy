/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Anneal
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Aeneas.Std

namespace SpecificationHoldsTests

-- Anneal originally checked a three-constructor result: success must satisfy
-- the postcondition, while panic and divergence must be rejected. Repeating
-- that original definition here makes this an independent migration check.
inductive HistoricalResult (α : Type) where
  | ok (value : α)
  | fail (error : Error)
  | div

def HistoricalResult.embed {α : Type} : HistoricalResult α → Result α
  | .ok value => .ok value
  | .fail error => .fail error
  | .div => .div

def historicalSpecification {α : Type}
    (result : HistoricalResult α) (post : α → Prop) : Prop :=
  match result with
  | .ok value => post value
  | .fail _ => False
  | .div => False

theorem historical_equivalence {α : Type}
    (result : HistoricalResult α) (post : α → Prop) :
    historicalSpecification result post ↔ Anneal.SpecificationHolds result.embed post := by
  cases result <;>
    simp [historicalSpecification, HistoricalResult.embed, Anneal.SpecificationHolds,
      WP.spec_ok, WP.spec_fail, WP.spec_div]

-- Aeneas now represents failure as an effect with an impossible continuation.
-- Show that this representation still covers exactly the three historical
-- outcomes. A new effect would leave an unproved case in this exhaustive proof.
theorem every_result_is_historical {α : Type} (result : Result α) :
    ∃ historical : HistoricalResult α, result = historical.embed := by
  cases result with
  | ret value => exact ⟨.ok value, rfl⟩
  | div => exact ⟨.div, rfl⟩
  | vis effect continuation =>
    cases effect with
    | fail error =>
      refine ⟨.fail error, ?_⟩
      change Result.vis (.fail error) continuation = Result.fail error
      rw [Result.fail_eq_vis]
      apply congrArg (Result.vis (.fail error))
      funext impossible
      exact PEmpty.elim impossible

-- Exercise the unfolding interface that existing user proofs use as well.
example {α : Type} (value : α) (post : α → Prop) :
    Anneal.SpecificationHolds (.ok value) post ↔ post value := by
  unfold Anneal.SpecificationHolds
  simp

example {α : Type} (error : Error) :
    ¬ Anneal.SpecificationHolds (.fail error : Result α) (fun _ => True) := by
  unfold Anneal.SpecificationHolds
  simp

example {α : Type} :
    ¬ Anneal.SpecificationHolds (.div : Result α) (fun _ => True) := by
  unfold Anneal.SpecificationHolds
  simp

-- The equivalence must not depend on Anneal's trusted ABI/pointer premises,
-- or on an unfinished proof. Only Lean's usual logical axioms are allowed.
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for theoremName in #[`SpecificationHoldsTests.historical_equivalence,
      `SpecificationHoldsTests.every_result_is_historical] do
    for assumption in ← Lean.collectAxioms theoremName do
      unless allowed.contains assumption do
        throwError "Result-equivalence theorem {theoremName} depends on forbidden axiom {assumption}"

end SpecificationHoldsTests
