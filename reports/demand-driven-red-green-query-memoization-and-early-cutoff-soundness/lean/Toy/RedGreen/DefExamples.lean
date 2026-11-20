/-
Toy.RedGreen.DefExamples
========================

Positive and negative examples for every core definition.  All fully proved.
-/
import Toy.RedGreen.Basic
import Toy.RedGreen.Lemmas
import Toy.RedGreen.Frame
import Toy.RedGreen.Examples
import Toy.RedGreen.ExecLog

namespace Toy.RedGreen

/-! ## `Prog`, `Prog.run`, `eval` -/

/-- Positive: in the old state of example D (`x = 5`), `top` fetches `guard = 1`
and then `risky = 100 / 5`. -/
theorem eval_example_value : eval rulesD oldD 4 (.inl .top) = .val 20 := by decide

/-- Negative (panics propagate): in the new state (`x = 0`), `risky` panics. -/
theorem eval_example_panic : eval rulesD newD 2 (.inl .risky) = .panic := by decide

/-- Negative (dynamic dependencies): in the new state, `top` does not fetch the
panicking `risky`, so it evaluates to `0` rather than panicking. -/
theorem eval_example_dead_dependency_not_evaluated : eval rulesD newD 3 (.inl .top) = .val 0 := by
  decide

theorem newL_x : newL .x = 0 := rfl

/-- Negative (cycles): in the new state of example L, `top` fetches itself and
evaluation is `stuck` at every fuel. -/
theorem eval_L_stuck : ∀ m, eval rulesL newL m (.inl .top) = .stuck := by
  intro m
  induction m with
  | zero => rfl
  | succ j ih =>
    cases j with
    | zero => rfl
    | succ i =>
      simp [eval, rulesL, Prog.run, newL_x, ↓ih]

/-! ## `Prog.runT` -/

/-- Positive: the recorded trace lists the fetched keys in order with the
fingerprints of their values. -/
theorem runT_example_ordered_trace :
    (rulesD .top).runT (eval rulesD oldD 3) fpId = (.val 20, [(.inl .guard, 1), (.inl .risky, 20)]) := by
  decide

/-- Negative: in the new state, the trace of `top` omits the dead dependency
`risky`. -/
theorem runT_example_dead_dependency_not_recorded :
    (rulesD .top).runT (eval rulesD newD 3) fpId = (.val 0, [(.inl .guard, 0)]) := by decide

/-! ## `Terminates` -/

/-- Positive: in example C the code contains the cycle `top → risky → top`, but
every query terminates in both states, because the cycle is never live. -/
theorem terminates_example_dead_code_cycle :
    ∀ q, Terminates rulesC oldD (.inl q) ∧ Terminates rulesC newD (.inl q) := by
  intro q
  cases q <;> exact ⟨⟨6, by decide⟩, ⟨6, by decide⟩⟩

/-- Negative: a live self-dependency does not terminate. -/
theorem terminates_example_live_cycle : ¬ Terminates rulesL newL (.inl .top) :=
  fun ⟨n, hn⟩ => hn (eval_L_stuck n)

/-! ## `FpInjective` -/

theorem fpId_injective : FpInjective fpId := fun _ _ h => h

theorem fpParity_not_injective : ¬ FpInjective fpParity :=
  fun h => absurd (h 1 3 rfl) (by decide)

theorem fpSat_not_injective : ¬ FpInjective fpSat :=
  fun h => absurd (h 11 12 rfl) (by decide)

/-! ## `EntryConsistent`, `DBConsistent` -/

/-- Positive: a database recorded from scratch is consistent. -/
theorem dbConsistent_example : DBConsistent rulesD fpId oldD odbD :=
  recordAll_consistent rulesD fpId oldD 10

theorem entryConsistent_example :
    EntryConsistent rulesD fpId oldD .top ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ :=
  dbConsistent_example .top _ odbD_top

/-- Negative: the recorded dependencies in the wrong order. -/
theorem entryConsistent_rejects_reordered_trace :
    ¬ EntryConsistent rulesD fpId oldD .top ⟨[(.inl .risky, 20), (.inl .guard, 1)], 20⟩ :=
  fun h => absurd (entryConsistent_unique rulesD fpId oldD .top h entryConsistent_example)
    (by decide)

/-- Negative: a wrong recorded fingerprint. -/
theorem entryConsistent_rejects_wrong_fingerprint :
    ¬ EntryConsistent rulesD fpId oldD .top ⟨[(.inl .guard, 2), (.inl .risky, 20)], 20⟩ :=
  fun h => absurd (entryConsistent_unique rulesD fpId oldD .top h entryConsistent_example)
    (by decide)

/-- Negative: an entry consistent with the old state is not consistent with the
new state (in which `top` no longer fetches `risky`). -/
theorem entryConsistent_rejects_other_state :
    ¬ EntryConsistent rulesD fpId newD .top ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ := by
  intro h
  have hnew : EntryConsistent rulesD fpId newD .top ⟨[(.inl .guard, 0)], 0⟩ := ⟨3, by decide⟩
  exact absurd (entryConsistent_unique rulesD fpId newD .top h hnew) (by decide)

/-- Negative: database `odbB` records a wrong result for `top`, so it is
consistent with no input state at all (`top`'s code returns `0` whatever `x`
is). -/
theorem odbB_not_consistent : ∀ oldInp, ¬ DBConsistent rulesB fpId oldInp odbB := by
  intro oldInp h
  have hgood : EntryConsistent rulesB fpId oldInp .top ⟨[(.inl .a, 0)], 0⟩ := ⟨2, rfl⟩
  exact absurd (entryConsistent_unique rulesB fpId oldInp .top (h .top _ rfl) hgood) (by decide)

/-- Positive: a partial cache (an entry for `top` but none for its dependency
`a`) is consistent: `DBConsistent` constrains only the entries present. -/
theorem dbConsistent_partial_cache : DBConsistent rulesPC fpId (inpXY 5 0) odbPC := by
  intro q e h
  cases q with
  | top => cases h; exact ⟨2, by decide⟩
  | a => cases h
  | b => cases h

/-! ## `start`, `Inv` -/

theorem start_example : start odbD .top = .old ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ := by
  decide

/-- Positive: the start of a revision from a consistent database. -/
theorem inv_example : Inv rulesD fpId oldD newD (start odbD) :=
  inv_start rulesD fpId oldD newD odbD dbConsistent_example

/-- Negative: a `done` slot holding an entry that is only valid in the old state. -/
theorem inv_rejects_stale_done_slot :
    ¬ Inv rulesD fpId oldD newD
      (fun q => match q with
        | .top => .done ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ true
        | _ => .none) :=
  fun h => entryConsistent_rejects_other_state (h .top)

/-! ## `changedAt` (early cutoff) -/

/-- Positive: with early cutoff, a re-executed dependency that reproduces its
recorded fingerprint is unchanged. -/
theorem changedAt_cutoff_example :
    changedAt true fpId (fun _ => (.done ⟨[(.inr .x, 3)], 0⟩ true : Slot Q3 IK Nat Nat))
      (.inl .a) 0 0 = false := by decide

/-- Negative: without early cutoff, the same dependency counts as changed. -/
theorem changedAt_no_cutoff_example :
    changedAt false fpId (fun _ => (.done ⟨[(.inr .x, 3)], 0⟩ true : Slot Q3 IK Nat Nat))
      (.inl .a) 0 0 = true := by decide

/-- Negative: in either mode, a different fingerprint is a change. -/
theorem changedAt_fingerprint_example (c : Bool) :
    changedAt c fpId (fun _ => (.none : Slot Q3 IK Nat Nat)) (.inr .x) 3 1 = true := by
  cases c <;> decide

/-! ## `fetch`, `markGreen`, `Replay` -/

/-- Positive: in example D, ordered replay finds `guard` red, re-executes `top`
and returns the from-scratch value `0`; the dead dependency `risky` is never
touched. -/
theorem fetch_example_ordered (c : Bool) :
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .val 0 ∧
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).2 .risky =
      start odbD .risky := by
  cases c <;> decide

/-- Negative: the incremental fetch does not reuse the stale cached result
`20` of `top`. -/
theorem fetch_example_rejects_stale (c : Bool) :
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 ≠ .val 20 := by
  cases c <;> decide

/-- Contrast: exhaustive replay does touch the dead dependency `risky` (and
panics on it). -/
theorem fetch_example_exhaustive_touches_dead_dependency (c : Bool) :
    (fetch ⟨.exhaustive, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .panic := by
  cases c <;> decide

/-! ## `Reachable` -/

/-- Positive: the database after one fetch is reachable. -/
theorem reachable_example :
    Reachable ⟨.ordered, true⟩ rulesD fpId newD (start odbD)
      (fetch ⟨.ordered, true⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).2 :=
  .step 6 (.inl QK.top) .refl

/-- Negative: fetches never create `old` slots, so a database with an `old`
slot is not reachable from an empty one. -/
theorem reachable_rejects_new_old_slot (cfg : Config) :
    ¬ Reachable cfg rulesD fpId newD (fun _ => (.none : Slot QK IK Nat Nat))
      (fun _ => .old ⟨[], 0⟩) := by
  intro h
  have := reachable_noNewOld cfg rulesD fpId newD _ _ h QK.top ⟨[], 0⟩ rfl
  cases this

/-! ## `AgreesWithEval` -/

/-- Positive: the trivial program `rulesZ` (every query returns `0`) over an
empty database agrees with from-scratch evaluation at every fuel. -/
theorem agreesWithEval_example (cfg : Config) :
    AgreesWithEval cfg rulesZ fpId newD (fun _ => .none) (.inl .top) := by
  refine ⟨fun m hm => ⟨m, ?_⟩, fun n hn => ?_⟩
  · cases m with
    | zero => exact absurd rfl hm
    | succ m => rfl
  · cases n with
    | zero => exact absurd rfl hn
    | succ n => simp [fetch, exec, rulesZ, Prog.runSt]

/-- Negative: reversed replay in example D panics where from-scratch
evaluation returns `0`. -/
theorem agreesWithEval_rejects_example (c : Bool) :
    ¬ AgreesWithEval ⟨.reversed, c⟩ rulesD fpId newD (start odbD) (.inl .top) :=
  not_agrees_of_wrong_outcome 6 3 .panic (by cases c <;> decide) (by decide) (by decide) (by decide)

/-! ## `execLog` -/

/-- Positive: with early cutoff, fetching `top` in example K executes only
`a`; `top` is marked green. -/
theorem execLog_example_cutoff :
    execLog ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top) = [.a] := by decide

/-- Negative: without early cutoff, `top` is executed too. -/
theorem execLog_example_no_cutoff :
    execLog ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top) = [.a, .top] := by
  decide

/-- Negative (the log sees what slots cannot): in example P, fetching `top`
in the new state (`x = 0`) executes `top`, whose code panics; `fetch` leaves
`top`'s slot unchanged, so the slot alone does not show that `top` was
executed. -/
theorem execLog_example_aborted_execution :
    (fetch ⟨.ordered, true⟩ rulesP fpId newP 4 (start odbP) (.inl .top)).1 = .panic ∧
    (fetch ⟨.ordered, true⟩ rulesP fpId newP 4 (start odbP) (.inl .top)).2 .top =
      start odbP .top ∧
    start odbP .top = .old ⟨[(.inr .x, 5)], 5⟩ ∧
    execLog ⟨.ordered, true⟩ rulesP fpId newP 4 (start odbP) (.inl .top) = [.top] := by
  decide

/-- Model behaviour on a partial cache, with unchanged inputs (`x = 5` in both
states): the entry of `top` is cached, the entry of its dependency `a` is not.
With early cutoff `a` is executed, reproduces the recorded fingerprint `5`, and
`top` is marked green; without early cutoff `top` is re-executed although no
input changed. -/
theorem partial_cache_example (c : Bool) :
    execLog ⟨.ordered, c⟩ rulesPC fpId (inpXY 5 0) 4 (start odbPC) (.inl .top) =
      (if c then [.a] else [.a, .top]) ∧
    (fetch ⟨.ordered, c⟩ rulesPC fpId (inpXY 5 0) 4 (start odbPC) (.inl .top)).1 = .val 6 := by
  cases c <;> decide

end Toy.RedGreen
