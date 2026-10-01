/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelPrelude
public meta import Lean
import all Init.Data.Nat.Power2.Basic
@[expose] public section

open Lean Elab Tactic Aeneas.Std
namespace AeneasSpecs

/-- An exposed theorem avoids requiring clients to unfold the predicate's
private defining module while constructing ordinary mathematical values. -/
theorem model_power_of_two (n : Nat) : (2 ^ n).isPowerOfTwo := ⟨n, rfl⟩

/-- Standard logarithm bounds, in a form usable by native arithmetic automation. -/
theorem model_log2_bounds (n : Nat) (positive : 0 < n) :
    2 ^ Nat.log2 n ≤ n ∧ n < 2 * 2 ^ Nat.log2 n := by
  have lower := Nat.log2_self_le (n := n) (by omega)
  have upper := Nat.lt_log2_self (n := n)
  rw [Nat.pow_succ] at upper
  omega

grind_pattern model_log2_bounds => Nat.log2 n

/-- Complete omitted proofs at a construction site. Data goals are never solved
by this tactic; ordinary elaboration and unification may already infer data. -/
elab "complete_model_proofs" : tactic => withCurrHeartbeats do
  let options ← getOptions
  let configured := maxHeartbeats.get options
  let budget := if configured == 0 then 100000 else min configured 100000
  withOptions (fun o => maxHeartbeats.set o budget) do
    for goal in (← getGoals) do
      goal.withContext do
        unless (← Meta.isProp (← goal.getType)) do
          Meta.throwTacticEx `complete_model_proofs goal
            "Supply the omitted data value; automatic model completion only proves propositions"
    try
      evalTactic (← `(tactic| all_goals first
        | assumption
        | exact model_power_of_two _
        | exact ⟨_, rfl⟩
        | omega
        | grind only [NonZeroUnsignedWord.positive, UnsignedWord.bound,
            model_log2_bounds, UScalar.max, Usize.max, Usize.numBits,
            UScalarTy.Usize_numBits_eq]))
    catch error =>
      -- An automation failure is a compilation failure, including in decode?.
      -- Preserve interruption/heartbeat errors and their original diagnostics.
      if error.isInterrupt || error.isMaxHeartbeat then throw error
      Meta.throwTacticEx `complete_model_proofs (← getMainGoal)
        m!"Could not prove the omitted model constraint. Supply an explicit field proof.
{error.toMessageData}"

/-- The explicit entry point outside a decoder; decoder bodies use the same rule. -/
macro "model_value " value:term : term =>
  `(by
    refine' $value
    complete_model_proofs)

end AeneasSpecs
