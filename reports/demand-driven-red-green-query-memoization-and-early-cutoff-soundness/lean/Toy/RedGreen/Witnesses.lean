/-
Toy.RedGreen.Witnesses
======================

Non-vacuity theorems for the cards `incremental-fetch-agrees`,
`every-replay-order-is-value-sound` and
`early-cutoff-agrees-with-reexecution`: concrete instances satisfying all
hypotheses of each theorem simultaneously.  All fully proved.
-/
import Toy.RedGreen.Basic
import Toy.RedGreen.Lemmas
import Toy.RedGreen.Examples
import Toy.RedGreen.DefExamples
import Toy.RedGreen.ValueSound
import Toy.RedGreen.Minimal

namespace Toy.RedGreen

/-- **Non-vacuity of `fetch_agrees_with_eval_of_ordered_replay`.**  Example C
satisfies every hypothesis (ordered replay, same code, identity fingerprints,
a database recorded from scratch in the old state), for either cutoff mode.
The instance exercises a changed recorded dependency (`guard`), a recorded
dependency that becomes dead (`risky`), and a code-level cycle that is live in
neither state; the incremental fetch returns the from-scratch value. -/
theorem fetch_agrees_with_eval_nonvacuous (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesC = rulesC ∧ FpInjective fpId ∧
    DBConsistent rulesC fpId oldD odbC ∧
    (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).1 = .val 0 ∧
    eval rulesC newD 6 (.inl .top) = .val 0 :=
  ⟨rfl, rfl, fpId_injective, recordAll_consistent rulesC fpId oldD 10, by cases c <;> decide,
    by decide⟩

/-- **Non-vacuity of the revision theorems
`fetch_agrees_with_eval_during_revision_of_ordered_replay`,
`fetch_eventually_eq_eval_during_revision_of_ordered_replay` and
`fetch_eventually_finishes_during_revision_of_terminates`.**  In example C,
for either cutoff mode: after fetching `top`, the working database is
reachable; every hypothesis holds for `k = risky` (including termination of
`risky` in the new state), and fetching `risky` from it (which now fetches the
already-validated `top`) returns the from-scratch value. -/
theorem fetch_during_revision_nonvacuous (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesC = rulesC ∧ FpInjective fpId ∧
    DBConsistent rulesC fpId oldD odbC ∧
    Reachable ⟨.ordered, c⟩ rulesC fpId newD (start odbC)
      (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).2 ∧
    Terminates rulesC newD (.inl .risky) ∧
    (fetch ⟨.ordered, c⟩ rulesC fpId newD 6
      (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).2 (.inl .risky)).1 =
      eval rulesC newD 6 (.inl .risky) ∧
    eval rulesC newD 6 (.inl .risky) = .val 0 :=
  ⟨rfl, rfl, fpId_injective, recordAll_consistent rulesC fpId oldD 10,
    .step 6 (.inl QK.top) .refl, (terminates_example_dead_code_cycle .risky).2,
    by cases c <;> decide, by decide⟩

/-- **Non-vacuity of `fetch_simulation_invariant`.**  In example C, for either
cutoff mode, the working database left by fetching `top` (in which `top` has
been re-executed and holds a `done` slot) satisfies `Inv`, together with
ordered replay and collision-free fingerprints. -/
theorem fetch_simulation_invariant_nonvacuous (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ FpInjective fpId ∧
    Inv rulesC fpId oldD newD (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).2 ∧
    (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).2 .top =
      .done ⟨[(.inl .guard, 0)], 0⟩ true :=
  ⟨rfl, fpId_injective,
    inv_of_reachable ⟨.ordered, c⟩ rulesC fpId fpId_injective oldD newD _ _
      (inv_start rulesC fpId oldD newD odbC (recordAll_consistent rulesC fpId oldD 10))
      (.step 6 (.inl QK.top) .refl),
    by cases c <;> decide⟩

/-- **Non-vacuity of `fetch_value_sound_of_any_replay`.**  In example K, for
every replay order and cutoff mode: after fetching `a`, the working database is
reachable, every hypothesis holds, and fetching `top` from it returns a value,
namely the from-scratch value `2`. -/
theorem fetch_value_sound_nonvacuous (r : Replay) (c : Bool) :
    rulesK = rulesK ∧ FpInjective fpId ∧ DBConsistent rulesK fpId oldK odbK ∧
    Reachable ⟨r, c⟩ rulesK fpId newK (start odbK)
      (fetch ⟨r, c⟩ rulesK fpId newK 6 (start odbK) (.inl .a)).2 ∧
    (fetch ⟨r, c⟩ rulesK fpId newK 6
      (fetch ⟨r, c⟩ rulesK fpId newK 6 (start odbK) (.inl .a)).2 (.inl .top)).1 = .val 2 ∧
    eval rulesK newK 6 (.inl .top) = .val 2 := by
  refine ⟨rfl, fpId_injective, recordAll_consistent rulesK fpId oldK 10,
    .step 6 (.inl Q3.a) .refl, ?_, by decide⟩
  cases r <;> cases c <;> decide

/-- **Non-vacuity of `early_cutoff_agrees_with_reexecution_of_ordered_replay`.**
Example K satisfies every hypothesis, and early cutoff is actually exercised:
`a` is re-executed and reproduces its fingerprint, so with early cutoff `top`
is marked green while without it `top` is re-executed; both return `2` (the
working databases differ in `top`'s slot). -/
theorem early_cutoff_agrees_nonvacuous :
    (Replay.ordered = .ordered) ∧ rulesK = rulesK ∧ FpInjective fpId ∧
    DBConsistent rulesK fpId oldK odbK ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).1 = .val 2 ∧
    (fetch ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).1 = .val 2 ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .top = .done eK false ∧
    (fetch ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .top = .done eK true :=
  ⟨rfl, rfl, fpId_injective, recordAll_consistent rulesK fpId oldK 10, by decide, by decide,
    by decide, by decide⟩

end Toy.RedGreen
