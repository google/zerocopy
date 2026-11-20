/-
Toy.RedGreen.Replay
===================

Card `ordered-replay-necessary`: replaying recorded dependencies out of order,
or checking every recorded dependency past the first changed one (a
sequential model of checking all recorded edges), can execute a dependency
that the new inputs have made dead.  If that dependency panics, the
incremental fetch panics; if it closes a cycle that is dead in both states,
the incremental fetch is `stuck` at every fuel.  In both cases from-scratch
evaluation returns `0`.  (No replay order returns a wrong value: see
`Toy.RedGreen.ValueSound`.)

Also the replay-order counterexample for card
`early-cutoff-agrees-with-reexecution`.

All fully proved.
-/
import Toy.RedGreen.Basic
import Toy.RedGreen.Lemmas
import Toy.RedGreen.Examples
import Toy.RedGreen.DefExamples

namespace Toy.RedGreen

/-! ## Panic variant (example D) -/

/-- **Out-of-order replay executes a dead dependency that panics.**  In example
D all hypotheses of `fetch_agrees_with_eval_of_ordered_replay` other than
ordered replay hold (same code, identity fingerprints, a database recorded
from scratch in the old state).  The recorded dependency `risky` of `top` is
dead in the new state and panics there.  From scratch, `top` evaluates to `0`;
with reversed replay (early cutoff on or off) the incremental fetch panics. -/
theorem reversed_replay_executes_dead_dependency_and_panics (c : Bool) :
    rulesD = rulesD ∧ FpInjective fpId ∧ DBConsistent rulesD fpId oldD odbD ∧
    odbD .top = some ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ ∧
    (rulesD .top).runT (eval rulesD newD 3) fpId = (.val 0, [(.inl .guard, 0)]) ∧
    eval rulesD newD 2 (.inl .risky) = .panic ∧
    eval rulesD newD 3 (.inl .top) = .val 0 ∧
    (fetch ⟨.reversed, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .panic ∧
    ¬ AgreesWithEval ⟨.reversed, c⟩ rulesD fpId newD (start odbD) (.inl .top) :=
  ⟨rfl, fpId_injective, dbConsistent_example, odbD_top, by decide, by decide, by decide,
    by cases c <;> decide,
    not_agrees_of_wrong_outcome 6 3 .panic (by cases c <;> decide) (by decide) (by decide)
      (by decide)⟩

/-- **Checking all recorded dependencies executes a dead dependency that
panics.**  Same instance as `reversed_replay_executes_dead_dependency_and_panics`,
with exhaustive replay (every recorded dependency is checked even after
`guard` has changed). -/
theorem exhaustive_replay_executes_dead_dependency_and_panics (c : Bool) :
    rulesD = rulesD ∧ FpInjective fpId ∧ DBConsistent rulesD fpId oldD odbD ∧
    odbD .top = some ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ ∧
    (rulesD .top).runT (eval rulesD newD 3) fpId = (.val 0, [(.inl .guard, 0)]) ∧
    eval rulesD newD 2 (.inl .risky) = .panic ∧
    eval rulesD newD 3 (.inl .top) = .val 0 ∧
    (fetch ⟨.exhaustive, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .panic ∧
    ¬ AgreesWithEval ⟨.exhaustive, c⟩ rulesD fpId newD (start odbD) (.inl .top) :=
  ⟨rfl, fpId_injective, dbConsistent_example, odbD_top, by decide, by decide, by decide,
    by cases c <;> decide,
    not_agrees_of_wrong_outcome 6 3 .panic (by cases c <;> decide) (by decide) (by decide)
      (by decide)⟩

/-! ## Divergence variant (example C) -/

theorem start_odbC_top :
    start odbC .top = .old ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ := by decide
theorem start_odbC_risky : start odbC .risky = .old ⟨[(.inr .x, 5)], 20⟩ := by decide
theorem newD_x : newD .x = 0 := rfl

/-- In example C, reversed replay of `top` is `stuck` at every fuel: it checks
`risky` first, re-executes it, and `risky` fetches `top` again. -/
theorem fetch_reversed_C_stuck (c : Bool) :
    ∀ m, (fetch ⟨.reversed, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 = .stuck := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m, ih with
    | 0, _ => rfl
    | 1, _ => cases c <;> decide
    | 2, _ => cases c <;> decide
    | j + 3, ih =>
      have ih' := ih (j + 1) (by omega)
      cases hF : fetch ⟨.reversed, c⟩ rulesC fpId newD (j + 1) (start odbC) (.inl .top) with
      | mk o db' =>
        rw [hF] at ih'
        simp only at ih'
        subst ih'
        simp [fetch, start_odbC_top, start_odbC_risky, markGreen, checkDeps, changedAt, exec,
          Prog.runSt, rulesC, fpId, newD_x, ↓hF]

/-- The working database of example C after exhaustive replay has
re-executed `guard`. -/
def dbC_guardDone : DB QK IK Nat Nat :=
  (start odbC).set .guard (.done ⟨[(.inr .x, 0)], 0⟩ true)

theorem dbC_guardDone_top :
    dbC_guardDone .top = .old ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ := by decide
theorem dbC_guardDone_guard :
    dbC_guardDone .guard = .done ⟨[(.inr .x, 0)], 0⟩ true := by decide
theorem dbC_guardDone_risky :
    dbC_guardDone .risky = .old ⟨[(.inr .x, 5)], 20⟩ := by decide

theorem fetch_exhaustive_C_guardDone_stuck (c : Bool) :
    ∀ m, (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m dbC_guardDone (.inl .top)).1 = .stuck := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m, ih with
    | 0, _ => rfl
    | 1, _ => cases c <;> decide
    | 2, _ => cases c <;> decide
    | j + 3, ih =>
      have ih' := ih (j + 1) (by omega)
      cases hF : fetch ⟨.exhaustive, c⟩ rulesC fpId newD (j + 1) dbC_guardDone (.inl .top) with
      | mk o db' =>
        rw [hF] at ih'
        simp only at ih'
        subst ih'
        cases c <;>
          simp [fetch, dbC_guardDone_top, dbC_guardDone_guard, dbC_guardDone_risky,
            markGreen, checkDeps, changedAt, reexecutedIn, exec, Prog.runSt, rulesC, fpId,
            newD_x, ↓hF]

/-- In example C, exhaustive replay of `top` is `stuck` at every fuel: it
re-executes `guard` (changed), keeps checking, re-executes `risky`, and
`risky` fetches `top` again. -/
theorem fetch_exhaustive_C_stuck (c : Bool) :
    ∀ m, (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 = .stuck := by
  intro m
  match m with
  | 0 => rfl
  | 1 => cases c <;> decide
  | 2 => cases c <;> decide
  | j + 3 =>
    have hstep : fetch ⟨.exhaustive, c⟩ rulesC fpId newD (j + 2) (start odbC) (.inl .guard) =
        (.val 0, dbC_guardDone) := by
      have hguard : start odbC .guard = .old ⟨[(.inr .x, 5)], 1⟩ := by decide
      cases c <;>
        simp [fetch, hguard, markGreen, checkDeps, changedAt, reexecutedIn, exec, Prog.runSt,
          rulesC, fpId, newD_x, dbC_guardDone]
    have ih' := fetch_exhaustive_C_guardDone_stuck c (j + 1)
    cases hF : fetch ⟨.exhaustive, c⟩ rulesC fpId newD (j + 1) dbC_guardDone (.inl .top) with
    | mk o db' =>
      rw [hF] at ih'
      simp only at ih'
      subst ih'
      have hstep2 : fetch ⟨.exhaustive, c⟩ rulesC fpId newD (j + 2) dbC_guardDone (.inl .risky) =
          (.stuck, db') := by
        cases c <;>
          simp [fetch, dbC_guardDone_risky, markGreen, checkDeps, changedAt, reexecutedIn,
            exec, Prog.runSt, rulesC, fpId, newD_x, ↓hF]
      cases c <;> (
        rw [fetch]
        simp [start_odbC_top, markGreen, checkDeps, hstep, hstep2, changedAt, reexecutedIn, fpId])

/-- **Out-of-order replay diverges on a dead code-level cycle.**  In example C
the code contains the cycle `top → risky → top`, but it is live in neither
state: every query terminates in the old and in the new state, and from
scratch `top` evaluates to `0` in the new state.  All hypotheses of the
theorems of card `incremental-fetch-agrees` other than ordered replay hold
(with `db` the start database).  With reversed replay (early cutoff on or off)
the incremental fetch of `top` is `stuck` at every fuel, so agreement,
eventual equality and termination transfer all fail. -/
theorem reversed_replay_diverges_on_dead_code_cycle (c : Bool) :
    rulesC = rulesC ∧ FpInjective fpId ∧ DBConsistent rulesC fpId oldD odbC ∧
    Reachable ⟨.reversed, c⟩ rulesC fpId newD (start odbC) (start odbC) ∧
    (∀ q, Terminates rulesC oldD (.inl q) ∧ Terminates rulesC newD (.inl q)) ∧
    eval rulesC newD 3 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.reversed, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 = .stuck) ∧
    ¬ AgreesWithEval ⟨.reversed, c⟩ rulesC fpId newD (start odbC) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.reversed, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 =
        eval rulesC newD m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
        (fetch ⟨.reversed, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 ≠ .stuck) :=
  ⟨rfl, fpId_injective, recordAll_consistent rulesC fpId oldD 10, .refl,
    terminates_example_dead_code_cycle, by decide, fetch_reversed_C_stuck c,
    not_agrees_of_stuck 3 (by decide) (fetch_reversed_C_stuck c 3),
    not_eventually_eq_of_stuck 3 (by decide) (fetch_reversed_C_stuck c),
    not_eventually_finishes_of_stuck (fetch_reversed_C_stuck c)⟩

/-- **Checking all recorded dependencies diverges on a dead code-level
cycle.**  Same instance, exhaustive replay: the incremental fetch of `top` is
`stuck` at every fuel (early cutoff on or off). -/
theorem exhaustive_replay_diverges_on_dead_code_cycle (c : Bool) :
    rulesC = rulesC ∧ FpInjective fpId ∧ DBConsistent rulesC fpId oldD odbC ∧
    Reachable ⟨.exhaustive, c⟩ rulesC fpId newD (start odbC) (start odbC) ∧
    (∀ q, Terminates rulesC oldD (.inl q) ∧ Terminates rulesC newD (.inl q)) ∧
    eval rulesC newD 3 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 = .stuck) ∧
    ¬ AgreesWithEval ⟨.exhaustive, c⟩ rulesC fpId newD (start odbC) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 =
        eval rulesC newD m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
        (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 ≠ .stuck) :=
  ⟨rfl, fpId_injective, recordAll_consistent rulesC fpId oldD 10, .refl,
    terminates_example_dead_code_cycle, by decide, fetch_exhaustive_C_stuck c,
    not_agrees_of_stuck 3 (by decide) (fetch_exhaustive_C_stuck c 3),
    not_eventually_eq_of_stuck 3 (by decide) (fetch_exhaustive_C_stuck c),
    not_eventually_finishes_of_stuck (fetch_exhaustive_C_stuck c)⟩

/-! ## Replay order and early cutoff (example R) -/

/-- **Without ordered replay the two cutoff modes disagree.**  Example R: all
hypotheses of `early_cutoff_agrees_with_reexecution_of_ordered_replay` other
than ordered replay hold (same code, identity fingerprints, a database
recorded from scratch).  With reversed replay, early cutoff checks `a` first,
finds its fingerprint reproduced, goes on to the dead `risky` and panics;
without early cutoff the re-executed `a` counts as changed, so `top` is
re-executed and returns `0`. -/
theorem reversed_replay_breaks_early_cutoff_agreement :
    rulesR = rulesR ∧ FpInjective fpId ∧ DBConsistent rulesR fpId oldD odbR ∧
    (fetch ⟨.reversed, true⟩ rulesR fpId newD 8 (start odbR) (.inl .top)).1 = .panic ∧
    (fetch ⟨.reversed, false⟩ rulesR fpId newD 8 (start odbR) (.inl .top)).1 = .val 0 ∧
    ¬ (∀ m₁ m₂,
      (fetch ⟨.reversed, true⟩ rulesR fpId newD m₁ (start odbR) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.reversed, false⟩ rulesR fpId newD m₂ (start odbR) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.reversed, true⟩ rulesR fpId newD m₁ (start odbR) (.inl .top)).1 =
        (fetch ⟨.reversed, false⟩ rulesR fpId newD m₂ (start odbR) (.inl .top)).1) :=
  ⟨rfl, fpId_injective, recordAll_consistent rulesR fpId oldD 10,
    by decide, by decide, fun h => absurd (h 8 8 (by decide) (by decide)) (by decide)⟩

/-! ## Positive control -/

/-- **Positive control.**  On the same two instances, ordered replay (early
cutoff on or off) returns the from-scratch value `0`, and in example D leaves
the dead dependency `risky` untouched. -/
theorem ordered_replay_returns_from_scratch_value_on_dead_dependency (c : Bool) :
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .val 0 ∧
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).2 .risky =
      start odbD .risky ∧
    (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).1 = .val 0 := by
  cases c <;> decide

end Toy.RedGreen
