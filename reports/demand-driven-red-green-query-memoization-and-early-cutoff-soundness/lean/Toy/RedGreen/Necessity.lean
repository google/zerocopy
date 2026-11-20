/-
Toy.RedGreen.Necessity
======================

Cards `fingerprint-collision-breaks-reuse`, `untracked-change-breaks-reuse`,
`inconsistent-database-breaks-reuse` (tightness of the hypotheses of the
agreement, value-soundness and early-cutoff theorems), and
`cyclic-new-state-both-diverge` (termination of the new state is not a
hypothesis of agreement; it is needed only for termination transfer).  Also the
divergence counterexamples that refute termination transfer and eventual
equality when collision-freedom, unchanged code, database consistency or
reachability is dropped.

All fully proved.
-/
import Toy.RedGreen.Basic
import Toy.RedGreen.Lemmas
import Toy.RedGreen.Examples
import Toy.RedGreen.DefExamples
import Toy.RedGreen.Frame
import Toy.RedGreen.ValueSound

namespace Toy.RedGreen

/-! ## Fingerprint collisions -/

/-- **A fingerprint collision reuses a stale result.**  Example H: `top`
returns input `x`, which changes from `1` to `3`; parity fingerprints collide
on `1` and `3`.  Ordered replay (early cutoff on or off), the same code, a
database recorded from scratch in the old state: all other hypotheses of
`fetch_agrees_with_eval_of_ordered_replay` and of
`fetch_value_sound_of_any_replay` hold.  The incremental fetch marks `top`
green and returns the stale `1`; from scratch it is `3` at every fuel at which
it finishes. -/
theorem fp_collision_reuses_stale_result (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesH = rulesH ∧
    DBConsistent rulesH fpParity oldH odbH ∧ ¬ FpInjective fpParity ∧
    (fetch ⟨.ordered, c⟩ rulesH fpParity newH 4 (start odbH) (.inl .top)).1 = .val 1 ∧
    eval rulesH newH 2 (.inl .top) = .val 3 ∧
    (∀ n, eval rulesH newH n (.inl .top) ≠ .val 1) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesH fpParity newH (start odbH) (.inl .top) :=
  ⟨rfl, rfl, recordAll_consistent rulesH fpParity oldH 10, fpParity_not_injective,
    by cases c <;> decide, by decide,
    eval_ne_of_eval_eq rulesH newH (.inl .top) (n₀ := 2) (o₀ := .val 3) (o := .val 1) (by decide) (by decide) (by decide)
      (by decide),
    not_agrees_of_wrong_outcome 4 2 (.val 1) (by cases c <;> decide) (by decide) (by decide)
      (by decide)⟩

/-- **A collision on a re-executed query breaks early cutoff.**  Example S:
input fingerprints do not collide (`1 ↦ 1`, `2 ↦ 2`) but `a`'s old and new
results `11`, `12` collide under `fpSat`.  All other hypotheses of
`early_cutoff_agrees_with_reexecution_of_ordered_replay` hold.  With early
cutoff `top` is marked green and returns the stale `11`; without it `top` is
re-executed and returns `12` (the from-scratch value). -/
theorem fp_collision_breaks_early_cutoff :
    (Replay.ordered = .ordered) ∧ rulesS = rulesS ∧
    DBConsistent rulesS fpSat oldS odbS ∧ ¬ FpInjective fpSat ∧
    (fetch ⟨.ordered, true⟩ rulesS fpSat newS 6 (start odbS) (.inl .top)).1 = .val 11 ∧
    (fetch ⟨.ordered, false⟩ rulesS fpSat newS 6 (start odbS) (.inl .top)).1 = .val 12 ∧
    eval rulesS newS 3 (.inl .top) = .val 12 ∧
    ¬ (∀ m₁ m₂,
      (fetch ⟨.ordered, true⟩ rulesS fpSat newS m₁ (start odbS) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, false⟩ rulesS fpSat newS m₂ (start odbS) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, true⟩ rulesS fpSat newS m₁ (start odbS) (.inl .top)).1 =
        (fetch ⟨.ordered, false⟩ rulesS fpSat newS m₂ (start odbS) (.inl .top)).1) :=
  ⟨rfl, rfl, recordAll_consistent rulesS fpSat oldS 10, fpSat_not_injective, by decide, by decide,
    by decide, fun h => absurd (h 6 6 (by decide) (by decide)) (by decide)⟩

theorem start_odbFpLoop_top :
    start odbFpLoop .top = .old ⟨[(.inr .x, 1), (.inl .a, 0)], 20⟩ := by decide
theorem start_odbFpLoop_a : start odbFpLoop .a = .old ⟨[(.inr .y, 0)], 20⟩ := by decide
theorem newFpLoop_x : newFpLoop .x = 3 := rfl
theorem newFpLoop_y : newFpLoop .y = 1 := rfl

theorem fetch_fpLoop_stuck (c : Bool) :
    ∀ m, (fetch ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop m (start odbFpLoop) (.inl .top)).1 =
      .stuck := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m, ih with
    | 0, _ => rfl
    | 1, _ => cases c <;> decide
    | 2, _ => cases c <;> decide
    | j + 3, ih =>
      have ih' := ih (j + 1) (by omega)
      cases hF : fetch ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop (j + 1) (start odbFpLoop)
          (.inl .top) with
      | mk o db' =>
        rw [hF] at ih'; simp only at ih'; subst ih'
        cases c <;>
          simp [fetch, start_odbFpLoop_top, start_odbFpLoop_a, markGreen, checkDeps, changedAt,
            reexecutedIn, exec, Prog.runSt, rulesFpLoop, fpParity, newFpLoop_x, newFpLoop_y, ↓hF]

/-- **A fingerprint collision can make the incremental fetch diverge although
the new state terminates.**  Under parity fingerprints the change `x : 1 → 3`
is invisible, so `top` replays its old trace and fetches `a`, which in the new
state (`y = 1`) fetches `top`: the incremental fetch is `stuck` at every fuel,
while from scratch `top = 0`.  All other hypotheses of the theorems of card
`incremental-fetch-agrees` hold (with `db` the start database); agreement,
eventual equality and termination transfer all fail. -/
theorem fp_collision_diverges_although_new_state_terminates (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesFpLoop = rulesFpLoop ∧
    ¬ FpInjective fpParity ∧ DBConsistent rulesFpLoop fpParity oldFpLoop odbFpLoop ∧
    Reachable ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop (start odbFpLoop) (start odbFpLoop) ∧
    Terminates rulesFpLoop newFpLoop (.inl .top) ∧
    eval rulesFpLoop newFpLoop 2 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop m (start odbFpLoop) (.inl .top)).1 =
      .stuck) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop (start odbFpLoop) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop m (start odbFpLoop) (.inl .top)).1 =
        eval rulesFpLoop newFpLoop m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop m (start odbFpLoop) (.inl .top)).1 ≠
        .stuck) :=
  ⟨rfl, rfl, fpParity_not_injective, recordAll_consistent rulesFpLoop fpParity oldFpLoop 10, .refl,
    ⟨2, by decide⟩, by decide, fetch_fpLoop_stuck c,
    not_agrees_of_stuck 2 (by decide) (fetch_fpLoop_stuck c 2),
    not_eventually_eq_of_stuck 2 (by decide) (fetch_fpLoop_stuck c),
    not_eventually_finishes_of_stuck (fetch_fpLoop_stuck c)⟩

/-! ## Untracked changes between revisions -/

theorem rulesN_ne : rulesN 0 ≠ rulesN 1 := by
  intro h
  have h' : eval (rulesN 0) newN 6 (.inl .top) = eval (rulesN 1) newN 6 (.inl .top) := by rw [h]
  revert h'
  decide

theorem rulesM_ne : rulesM 0 ≠ rulesM 1 := by
  intro h
  have h' : eval (rulesM 0) newM 6 (.inl .top) = eval (rulesM 1) newM 6 (.inl .top) := by rw [h]
  revert h'
  decide

/-- **An untracked parameter change makes the incremental result match
neither rule set.**  Example N: the query code depends on a revision-wide
parameter that is not a tracked input (`0` when the database was recorded, `1`
in the current revision), so the code that produced the database (`rulesN 0`)
differs from the code that runs now (`rulesN 1`).  Ordered replay (early cutoff
on or off), identity fingerprints, a database recorded from scratch by
`rulesN 0` in the old state: all hypotheses of
`fetch_agrees_with_eval_of_ordered_replay` except unchanged code hold.  In the
new input state, `rulesN 1` (the current code) gives `top = 111`, and
`rulesN 0` (the code that produced the database) gives `top = 1`; the
incremental fetch returns `101`, which neither rule set produces at any fuel:
it combines a reused `a` computed by `rulesN 0` with a re-executed `top`
computed by `rulesN 1`. -/
theorem ambient_dependent_code_matches_no_from_scratch_eval (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧
    DBConsistent (rulesN 0) fpId oldN odbN ∧ FpInjective fpId ∧ rulesN 0 ≠ rulesN 1 ∧
    eval (rulesN 0) newN 6 (.inl .top) = .val 1 ∧
    eval (rulesN 1) newN 6 (.inl .top) = .val 111 ∧
    (fetch ⟨.ordered, c⟩ (rulesN 1) fpId newN 6 (start odbN) (.inl .top)).1 = .val 101 ∧
    (∀ n, eval (rulesN 0) newN n (.inl .top) ≠ .val 101) ∧
    (∀ n, eval (rulesN 1) newN n (.inl .top) ≠ .val 101) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ (rulesN 1) fpId newN (start odbN) (.inl .top) :=
  ⟨rfl, recordAll_consistent (rulesN 0) fpId oldN 10, fpId_injective, rulesN_ne,
    by decide, by decide, by cases c <;> decide,
    eval_ne_of_eval_eq (rulesN 0) newN (.inl .top) (n₀ := 6) (o₀ := .val 1) (o := .val 101) (by decide) (by decide) (by decide)
      (by decide),
    eval_ne_of_eval_eq (rulesN 1) newN (.inl .top) (n₀ := 6) (o₀ := .val 111) (o := .val 101) (by decide) (by decide) (by decide)
      (by decide),
    not_agrees_of_wrong_outcome 6 6 (.val 101) (by cases c <;> decide) (by decide) (by decide)
      (by decide)⟩

/-- **Scope of example N: this is not per-call non-determinism.**  If the
parameter is chosen per query execution — `a` (and `b`) executed with `0`,
`top` executed with `1` — from-scratch evaluation in the new state gives `101`,
the incremental result of `ambient_dependent_code_matches_no_from_scratch_eval`.
So under a per-call model of non-determinism `101` is a valid outcome; example
N refutes only the revision-wide-parameter reading. -/
theorem per_query_parameter_choice_gives_101 :
    eval (fun q : Q3 => match q with
      | .top => rulesN 1 .top
      | .a => rulesN 0 .a
      | .b => rulesN 0 .b) newN 6 (.inl Q3.top) = .val 101 := by
  decide

/-- **An untracked parameter change breaks early cutoff.**  Example M: `top`
returns `a + noise`; the database was recorded by `rulesM 0`, the revision runs
`rulesM 1`.  All other hypotheses of
`early_cutoff_agrees_with_reexecution_of_ordered_replay` hold.  `a` is
re-executed and reproduces its fingerprint, so with early cutoff `top` is
marked green and returns `0` (recorded by `rulesM 0`); without it `top` is
re-executed by `rulesM 1` and returns `1`. -/
theorem ambient_dependent_code_breaks_early_cutoff :
    (Replay.ordered = .ordered) ∧
    DBConsistent (rulesM 0) fpId oldM odbM ∧ FpInjective fpId ∧ rulesM 0 ≠ rulesM 1 ∧
    (fetch ⟨.ordered, true⟩ (rulesM 1) fpId newM 6 (start odbM) (.inl .top)).1 = .val 0 ∧
    (fetch ⟨.ordered, false⟩ (rulesM 1) fpId newM 6 (start odbM) (.inl .top)).1 = .val 1 ∧
    ¬ (∀ m₁ m₂,
      (fetch ⟨.ordered, true⟩ (rulesM 1) fpId newM m₁ (start odbM) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, false⟩ (rulesM 1) fpId newM m₂ (start odbM) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, true⟩ (rulesM 1) fpId newM m₁ (start odbM) (.inl .top)).1 =
        (fetch ⟨.ordered, false⟩ (rulesM 1) fpId newM m₂ (start odbM) (.inl .top)).1) :=
  ⟨rfl, recordAll_consistent (rulesM 0) fpId oldM 10, fpId_injective, rulesM_ne, by decide,
    by decide, fun h => absurd (h 6 6 (by decide) (by decide)) (by decide)⟩

theorem start_odbOldLoop_top : start odbOldLoop .top = .old ⟨[(.inl .a, 0)], 0⟩ := by decide
theorem start_odbOldLoop_a : start odbOldLoop .a = .old ⟨[(.inr .x, 0)], 0⟩ := by decide

theorem fetch_sameLoop_stuck (c : Bool) :
    ∀ m, (fetch ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) m (start odbOldLoop) (.inl .top)).1 =
      .stuck := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m, ih with
    | 0, _ => rfl
    | 1, _ => cases c <;> decide
    | 2, _ => cases c <;> decide
    | j + 3, ih =>
      have ih' := ih (j + 1) (by omega)
      cases hF : fetch ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) (j + 1) (start odbOldLoop)
          (.inl .top) with
      | mk o db' =>
        rw [hF] at ih'; simp only at ih'; subst ih'
        cases c <;>
          simp [fetch, start_odbOldLoop_top, start_odbOldLoop_a, markGreen, checkDeps, changedAt,
            reexecutedIn, exec, Prog.runSt, rulesNewLoop, fpId, inpXY, ↓hF]

/-- **A code change between revisions can make the incremental fetch diverge
although the new state terminates.**  The database was recorded by
`rulesOldLoop` (`top` returns `a`); the current code `rulesNewLoop` has
`top := 0` and `a := top`.  Replaying `top`'s old trace fetches `a`, whose new
code fetches `top`: the incremental fetch is `stuck` at every fuel, while from
scratch `top = 0`.  All other hypotheses of the theorems of card
`incremental-fetch-agrees` hold. -/
theorem untracked_code_change_diverges_although_new_state_terminates (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesOldLoop ≠ rulesNewLoop ∧
    FpInjective fpId ∧ DBConsistent rulesOldLoop fpId (inpXY 0 0) odbOldLoop ∧
    Reachable ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) (start odbOldLoop) (start odbOldLoop) ∧
    Terminates rulesNewLoop (inpXY 1 0) (.inl .top) ∧
    eval rulesNewLoop (inpXY 1 0) 1 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) m (start odbOldLoop) (.inl .top)).1 =
      .stuck) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) (start odbOldLoop) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) m (start odbOldLoop) (.inl .top)).1 =
        eval rulesNewLoop (inpXY 1 0) m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) m (start odbOldLoop) (.inl .top)).1 ≠
        .stuck) := by
  refine ⟨rfl, ?_, fpId_injective, recordAll_consistent rulesOldLoop fpId (inpXY 0 0) 10, .refl,
    ⟨1, by decide⟩, by decide, fetch_sameLoop_stuck c,
    not_agrees_of_stuck 1 (by decide) (fetch_sameLoop_stuck c 1),
    not_eventually_eq_of_stuck 1 (by decide) (fetch_sameLoop_stuck c),
    not_eventually_finishes_of_stuck (fetch_sameLoop_stuck c)⟩
  intro h
  have h' : eval rulesOldLoop (inpXY 1 0) 1 (.inl .top) =
      eval rulesNewLoop (inpXY 1 0) 1 (.inl .top) := by rw [h]
  revert h'; decide

/-! ## Inconsistent database -/

/-- **An inconsistent database reuses a wrong result.**  Example B: the entry
for `top` has the right trace but the wrong result `99`, so `odbB` is
consistent with no input state.  Ordered replay (early cutoff on or off),
identity fingerprints, the same code: all other hypotheses of
`fetch_agrees_with_eval_of_ordered_replay` and of
`fetch_value_sound_of_any_replay` hold.  The input does not change between the
two states; every recorded dependency is unchanged, so the incremental fetch
returns the recorded `99`; from scratch `top` is `0`. -/
theorem inconsistent_db_reuses_wrong_result (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesB = rulesB ∧ FpInjective fpId ∧
    (∀ oldInp, ¬ DBConsistent rulesB fpId oldInp odbB) ∧
    (fetch ⟨.ordered, c⟩ rulesB fpId oldB 6 (start odbB) (.inl .top)).1 = .val 99 ∧
    eval rulesB oldB 3 (.inl .top) = .val 0 ∧
    (∀ n, eval rulesB oldB n (.inl .top) ≠ .val 99) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesB fpId oldB (start odbB) (.inl .top) :=
  ⟨rfl, rfl, fpId_injective, odbB_not_consistent, by cases c <;> decide, by decide,
    eval_ne_of_eval_eq rulesB oldB (.inl .top) (n₀ := 3) (o₀ := .val 0) (o := .val 99) (by decide) (by decide) (by decide)
      (by decide),
    not_agrees_of_wrong_outcome 6 3 (.val 99) (by cases c <;> decide) (by decide) (by decide)
      (by decide)⟩

/-- **An inconsistent database breaks early cutoff.**  Same database, input
`x : 1 → 3`: `a` is re-executed and reproduces its fingerprint, so with early
cutoff the wrong recorded `99` is reused; without it `top` is re-executed and
returns `0`. -/
theorem inconsistent_db_breaks_early_cutoff :
    (Replay.ordered = .ordered) ∧ rulesB = rulesB ∧ FpInjective fpId ∧
    (∀ oldInp, ¬ DBConsistent rulesB fpId oldInp odbB) ∧
    (fetch ⟨.ordered, true⟩ rulesB fpId newB 6 (start odbB) (.inl .top)).1 = .val 99 ∧
    (fetch ⟨.ordered, false⟩ rulesB fpId newB 6 (start odbB) (.inl .top)).1 = .val 0 ∧
    ¬ (∀ m₁ m₂,
      (fetch ⟨.ordered, true⟩ rulesB fpId newB m₁ (start odbB) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, false⟩ rulesB fpId newB m₂ (start odbB) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, true⟩ rulesB fpId newB m₁ (start odbB) (.inl .top)).1 =
        (fetch ⟨.ordered, false⟩ rulesB fpId newB m₂ (start odbB) (.inl .top)).1) :=
  ⟨rfl, rfl, fpId_injective, odbB_not_consistent, by decide, by decide,
    fun h => absurd (h 6 6 (by decide) (by decide)) (by decide)⟩

theorem fetch_odbLoop_stuck (c : Bool) :
    ∀ m, (fetch ⟨.ordered, c⟩ rulesZ fpId newD m (start odbLoop) (.inl .top)).1 = .stuck := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih =>
    cases hF : fetch ⟨.ordered, c⟩ rulesZ fpId newD n (start odbLoop) (.inl .top) with
    | mk o db' =>
      rw [hF] at ih; simp only at ih; subst ih
      simp [fetch, start, odbLoop, markGreen, checkDeps, ↓hF]

/-- **An inconsistent database can make the incremental fetch diverge although
the new state terminates.**  Every entry of `odbLoop` records `top` as its only
dependency (no input state produces such entries for `rulesZ`, whose queries
fetch nothing); replaying `top` fetches `top`: `stuck` at every fuel, while
from scratch `top = 0`.  All other hypotheses of the theorems of card
`incremental-fetch-agrees` hold. -/
theorem inconsistent_db_diverges_although_new_state_terminates (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesZ = rulesZ ∧ FpInjective fpId ∧
    (∀ oldInp, ¬ DBConsistent rulesZ fpId oldInp odbLoop) ∧
    Reachable ⟨.ordered, c⟩ rulesZ fpId newD (start odbLoop) (start odbLoop) ∧
    Terminates rulesZ newD (.inl .top) ∧
    eval rulesZ newD 1 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesZ fpId newD m (start odbLoop) (.inl .top)).1 = .stuck) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesZ fpId newD (start odbLoop) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.ordered, c⟩ rulesZ fpId newD m (start odbLoop) (.inl .top)).1 =
        eval rulesZ newD m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
        (fetch ⟨.ordered, c⟩ rulesZ fpId newD m (start odbLoop) (.inl .top)).1 ≠ .stuck) := by
  refine ⟨rfl, rfl, fpId_injective, ?_, .refl, ⟨1, by decide⟩, by decide, fetch_odbLoop_stuck c,
    not_agrees_of_stuck 1 (by decide) (fetch_odbLoop_stuck c 1),
    not_eventually_eq_of_stuck 1 (by decide) (fetch_odbLoop_stuck c),
    not_eventually_finishes_of_stuck (fetch_odbLoop_stuck c)⟩
  intro oldInp h
  have hgood : EntryConsistent rulesZ fpId oldInp .top ⟨[], 0⟩ := ⟨1, rfl⟩
  exact absurd (entryConsistent_unique rulesZ fpId oldInp .top (h .top _ rfl) hgood) (by decide)

/-! ## Cycles -/

theorem start_odbL_top : start odbL .top = .old ⟨[(.inr .x, 1)], 1⟩ := by decide

/-- In example L, ordered replay of `top` is `stuck` at every fuel. -/
theorem fetch_L_stuck (c : Bool) :
    ∀ m, (fetch ⟨.ordered, c⟩ rulesL fpId newL m (start odbL) (.inl .top)).1 = .stuck := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m, ih with
    | 0, _ => rfl
    | 1, _ => cases c <;> decide
    | j + 2, ih =>
      have ih' := ih (j + 1) (by omega)
      cases hF : fetch ⟨.ordered, c⟩ rulesL fpId newL (j + 1) (start odbL) (.inl .top) with
      | mk o db' =>
        rw [hF] at ih'
        simp only at ih'
        subst ih'
        simp [fetch, start_odbL_top, markGreen, checkDeps, changedAt, exec, Prog.runSt, rulesL,
          fpId, newL_x, ↓hF]

/-- **A cyclic new state makes both sides diverge, and agreement still
holds.**  Example L: `top` fetches itself when `x = 0`.  The database is
recorded from scratch in the old state (`x = 1`, where `top` terminates);
fingerprints are collision-free; replay is ordered; the code is unchanged.  In
the new state (`x = 0`) `top` does not terminate, from-scratch evaluation and
the incremental fetch (early cutoff on or off) are both `stuck` at every fuel,
and therefore `AgreesWithEval` holds.  So termination of the new state is not
a hypothesis of the agreement theorems; dropping it only defeats
`fetch_eventually_finishes_during_revision_of_terminates`. -/
theorem cyclic_new_state_both_diverge (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesL = rulesL ∧
    FpInjective fpId ∧ DBConsistent rulesL fpId oldL odbL ∧
    Reachable ⟨.ordered, c⟩ rulesL fpId newL (start odbL) (start odbL) ∧
    Terminates rulesL oldL (.inl .top) ∧ ¬ Terminates rulesL newL (.inl .top) ∧
    (∀ m, eval rulesL newL m (.inl .top) = .stuck) ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesL fpId newL m (start odbL) (.inl .top)).1 = .stuck) ∧
    AgreesWithEval ⟨.ordered, c⟩ rulesL fpId newL (start odbL) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesL fpId newL m (start odbL) (.inl .top)).1 ≠ .stuck) :=
  ⟨rfl, rfl, fpId_injective, recordAll_consistent rulesL fpId oldL 10, .refl, ⟨2, by decide⟩,
    terminates_example_live_cycle, eval_L_stuck, fetch_L_stuck c,
    ⟨fun m hm => absurd (fetch_L_stuck c m) hm, fun n hn => absurd (eval_L_stuck n) hn⟩,
    not_eventually_finishes_of_stuck (fetch_L_stuck c)⟩

/-! ## Working databases outside the revision -/

/-- A working database that the algorithm does not produce from `start odbD`:
`top` holds a `done` slot with its old-state entry. -/
def staleDbD : DB QK IK Nat Nat :=
  fun q => if q = .top then .done ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ true else start odbD q

/-- **Reachability is needed: a stale `done` slot returns a wrong result.**
The working database `staleDbD` violates `Inv` (a `done` slot holds an entry
valid only in the old state) and is therefore not reachable from `start odbD`
(every reachable database satisfies `Inv`, `inv_of_reachable`).  Every other
hypothesis of `fetch_agrees_with_eval_during_revision_of_ordered_replay` and of
`fetch_value_sound_of_any_replay` holds, and the incremental fetch returns the
stale `20`, which from-scratch evaluation never returns.  This is also the
counterexample for dropping `Inv` from `fetch_simulation_invariant` (at fuel
`6`, its second conjunct fails). -/
theorem stale_done_slot_returns_wrong_result (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesD = rulesD ∧ FpInjective fpId ∧
    DBConsistent rulesD fpId oldD odbD ∧
    ¬ Inv rulesD fpId oldD newD staleDbD ∧
    ¬ Reachable ⟨.ordered, c⟩ rulesD fpId newD (start odbD) staleDbD ∧
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 staleDbD (.inl .top)).1 = .val 20 ∧
    eval rulesD newD 3 (.inl .top) = .val 0 ∧
    (∀ n, eval rulesD newD n (.inl .top) ≠ .val 20) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesD fpId newD staleDbD (.inl .top) := by
  have hninv : ¬ Inv rulesD fpId oldD newD staleDbD :=
    fun h => entryConsistent_rejects_other_state (h .top)
  refine ⟨rfl, rfl, fpId_injective, dbConsistent_example, hninv, fun h => hninv ?_,
    by cases c <;> decide, by decide,
    eval_ne_of_eval_eq rulesD newD (.inl .top) (n₀ := 3) (o₀ := .val 0) (o := .val 20) (by decide) (by decide) (by decide)
      (by decide),
    not_agrees_of_wrong_outcome 6 3 (.val 20) (by cases c <;> decide) (by decide) (by decide)
      (by decide)⟩
  exact inv_of_reachable ⟨.ordered, c⟩ rulesD fpId fpId_injective oldD newD _ _
    (inv_start rulesD fpId oldD newD odbD dbConsistent_example) h

theorem fetch_loopDb_stuck (c : Bool) :
    ∀ m, (fetch ⟨.ordered, c⟩ rulesZ fpId newD m loopDb (.inl .top)).1 = .stuck := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih =>
    cases hF : fetch ⟨.ordered, c⟩ rulesZ fpId newD n loopDb (.inl .top) with
    | mk o db' =>
      rw [hF] at ih; simp only at ih; subst ih
      simp [fetch, loopDb, markGreen, checkDeps, ↓hF]

/-- **Reachability is needed: an unreachable working database can make the
fetch diverge.**  Starting from the empty (hence consistent) database, the
working database `loopDb` (an `old` slot for every query, recording `top` as
its only dependency) is not reachable: fetches never create `old` slots.
Every other hypothesis of the revision theorems of card
`incremental-fetch-agrees` holds, `top` terminates from scratch (`= 0`), and
the incremental fetch from `loopDb` is `stuck` at every fuel. -/
theorem unreachable_db_diverges_although_new_state_terminates (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesZ = rulesZ ∧ FpInjective fpId ∧
    DBConsistent rulesZ fpId oldD odbEmpty ∧
    ¬ Reachable ⟨.ordered, c⟩ rulesZ fpId newD (start odbEmpty) loopDb ∧
    Terminates rulesZ newD (.inl .top) ∧
    eval rulesZ newD 1 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesZ fpId newD m loopDb (.inl .top)).1 = .stuck) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesZ fpId newD loopDb (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.ordered, c⟩ rulesZ fpId newD m loopDb (.inl .top)).1 =
        eval rulesZ newD m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.ordered, c⟩ rulesZ fpId newD m loopDb (.inl .top)).1 ≠ .stuck) := by
  refine ⟨rfl, rfl, fpId_injective, (fun _ _ h => by cases h), ?_, ⟨1, by decide⟩, by decide,
    fetch_loopDb_stuck c,
    not_agrees_of_stuck 1 (by decide) (fetch_loopDb_stuck c 1),
    not_eventually_eq_of_stuck 1 (by decide) (fetch_loopDb_stuck c),
    not_eventually_finishes_of_stuck (fetch_loopDb_stuck c)⟩
  intro h
  have := reachable_noNewOld ⟨.ordered, c⟩ rulesZ fpId newD _ _ h Q3.top ⟨[(.inl .top, 0)], 0⟩ rfl
  cases this

end Toy.RedGreen
