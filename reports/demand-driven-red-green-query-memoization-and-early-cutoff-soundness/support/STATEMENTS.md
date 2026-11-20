# Statements of all declarations referenced by `results.json`

Quoted verbatim from `lean/Toy/RedGreen/*.lean` (docstring and signature, up to the proof), grouped by card. Section variables `{Q I V F : Type} [DecidableEq Q] [DecidableEq F]` are implicit where the signature does not bind them. Statement and closure hashes are in `../audit/statements.json`.

## `incremental-fetch-agrees`

### Results

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_agrees_with_eval_of_ordered_replay`:

```lean
/-- **Agreement of ordered red-green replay (first demand).**  With ordered
replay (early cutoff on or off), collision-free fingerprints, the same query
code as the one that produced the database, and a database consistent with
the old input state, the incremental fetch of any key at the start of a
revision agrees with from-scratch evaluation in the new state (partial
correctness, and adequacy at equal fuel). -/
theorem fetch_agrees_with_eval_of_ordered_replay (cfg : Config) (hord : cfg.replay = .ordered)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (k : Key Q I) :
    AgreesWithEval cfg rulesNew fp newInp (start odb) k
```

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_agrees_with_eval_during_revision_of_ordered_replay`:

```lean
/-- **Agreement during a whole revision.**  Under the same hypotheses, every
fetch made from a working database reachable from the start of the revision
by earlier fetches (of any keys, with any fuel) agrees with from-scratch
evaluation in the new state. -/
theorem fetch_agrees_with_eval_during_revision_of_ordered_replay (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I) :
    AgreesWithEval cfg rulesNew fp newInp db k
```

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_eventually_eq_eval_during_revision_of_ordered_replay`:

```lean
/-- **Eventual equality during a whole revision.**  Under the same hypotheses,
for every working database reachable from the start of the revision (in
particular the start database itself, `Reachable.refl`), for all sufficiently
large fuel the incremental fetch and from-scratch evaluation have the same
outcome — including the case where both are `stuck` at every fuel. -/
theorem fetch_eventually_eq_eval_during_revision_of_ordered_replay (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I) :
    ∃ N, ∀ m, N ≤ m → (fetch cfg rulesNew fp newInp m db k).1 = eval rulesNew newInp m k
```

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_eventually_finishes_during_revision_of_terminates`:

```lean
/-- **Termination transfer during a whole revision.**  Under the same
hypotheses, if `k` terminates from scratch in the new state, then for every
working database reachable from the start of the revision the incremental
fetch of `k` finishes for all sufficiently large fuel. -/
theorem fetch_eventually_finishes_during_revision_of_terminates (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I)
    (hterm : Terminates rulesNew newInp k) :
    ∃ N, ∀ m, N ≤ m → (fetch cfg rulesNew fp newInp m db k).1 ≠ .stuck
```

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_simulation_invariant`:

```lean
/-- **Main simulation invariant.**  For ordered replay (with or without early
cutoff) and collision-free fingerprints, one incremental fetch from a working
database satisfying `Inv` (old slots consistent with the old state, done
slots with the new state)

* returns a database that again satisfies `Inv`;
* if it finishes, returns the from-scratch outcome (value or panic) of the new
  state;
* finishes whenever from-scratch evaluation finishes with the same fuel. -/
theorem fetch_simulation_invariant (cfg : Config) (hord : cfg.replay = .ordered)
    (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) :
    ∀ (n : Nat) (db : DB Q I V F) (k : Key Q I), Inv rules fp oldInp newInp db →
      Inv rules fp oldInp newInp (fetch cfg rules fp newInp n db k).2 ∧
      ((fetch cfg rules fp newInp n db k).1 ≠ .stuck →
          ∃ m, eval rules newInp m k = (fetch cfg rules fp newInp n db k).1) ∧
      (eval rules newInp n k ≠ .stuck → (fetch cfg rules fp newInp n db k).1 ≠ .stuck)
```

### Non-vacuity witnesses

`Toy/RedGreen/Witnesses.lean` — `Toy.RedGreen.fetch_agrees_with_eval_nonvacuous`:

```lean
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
    eval rulesC newD 6 (.inl .top) = .val 0
```

`Toy/RedGreen/Witnesses.lean` — `Toy.RedGreen.fetch_during_revision_nonvacuous`:

```lean
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
    eval rulesC newD 6 (.inl .risky) = .val 0
```

`Toy/RedGreen/Witnesses.lean` — `Toy.RedGreen.fetch_simulation_invariant_nonvacuous`:

```lean
/-- **Non-vacuity of `fetch_simulation_invariant`.**  In example C, for either
cutoff mode, the working database left by fetching `top` (in which `top` has
been re-executed and holds a `done` slot) satisfies `Inv`, together with
ordered replay and collision-free fingerprints. -/
theorem fetch_simulation_invariant_nonvacuous (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ FpInjective fpId ∧
    Inv rulesC fpId oldD newD (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).2 ∧
    (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).2 .top =
      .done ⟨[(.inl .guard, 0)], 0⟩ true
```

### Hypothesis counterexamples

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.reversed_replay_executes_dead_dependency_and_panics`:

```lean
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
    ¬ AgreesWithEval ⟨.reversed, c⟩ rulesD fpId newD (start odbD) (.inl .top)
```

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.exhaustive_replay_executes_dead_dependency_and_panics`:

```lean
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
    ¬ AgreesWithEval ⟨.exhaustive, c⟩ rulesD fpId newD (start odbD) (.inl .top)
```

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.reversed_replay_diverges_on_dead_code_cycle`:

```lean
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
        (fetch ⟨.reversed, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 ≠ .stuck)
```

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.exhaustive_replay_diverges_on_dead_code_cycle`:

```lean
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
        (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 ≠ .stuck)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval`:

```lean
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
    ¬ AgreesWithEval ⟨.ordered, c⟩ (rulesN 1) fpId newN (start odbN) (.inl .top)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.untracked_code_change_diverges_although_new_state_terminates`:

```lean
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
        .stuck)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.fp_collision_reuses_stale_result`:

```lean
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
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesH fpParity newH (start odbH) (.inl .top)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.fp_collision_diverges_although_new_state_terminates`:

```lean
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
        .stuck)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.inconsistent_db_reuses_wrong_result`:

```lean
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
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesB fpId oldB (start odbB) (.inl .top)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.inconsistent_db_diverges_although_new_state_terminates`:

```lean
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
        (fetch ⟨.ordered, c⟩ rulesZ fpId newD m (start odbLoop) (.inl .top)).1 ≠ .stuck)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.stale_done_slot_returns_wrong_result`:

```lean
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
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesD fpId newD staleDbD (.inl .top)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.unreachable_db_diverges_although_new_state_terminates`:

```lean
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
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.ordered, c⟩ rulesZ fpId newD m loopDb (.inl .top)).1 ≠ .stuck)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.cyclic_new_state_both_diverge`:

```lean
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
      (fetch ⟨.ordered, c⟩ rulesL fpId newL m (start odbL) (.inl .top)).1 ≠ .stuck)
```

## `early-cutoff-agrees-with-reexecution`

### Results

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.early_cutoff_agrees_with_reexecution_of_ordered_replay`:

```lean
/-- **Early cutoff agrees with full re-execution (reference corollary of
`incremental-fetch-agrees`).**  With ordered replay, collision-free
fingerprints, the same query code as the one that produced the database, and
a database consistent with the old input state, the first incremental fetch of
a revision with early cutoff (a re-executed dependency that reproduces its
recorded fingerprint counts as unchanged) and without it (every dependent of a
re-executed query is re-executed) return the same outcome: whenever both
finish, at any fuels, their outcomes are equal; and for all sufficiently large
fuel their outcomes are equal.  Only outcomes are compared; the working
databases the two modes leave behind differ. -/
theorem early_cutoff_agrees_with_reexecution_of_ordered_replay (r : Replay) (hord : r = .ordered)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (k : Key Q I) :
    (∀ m₁ m₂,
      (fetch ⟨r, true⟩ rulesNew fp newInp m₁ (start odb) k).1 ≠ .stuck →
      (fetch ⟨r, false⟩ rulesNew fp newInp m₂ (start odb) k).1 ≠ .stuck →
      (fetch ⟨r, true⟩ rulesNew fp newInp m₁ (start odb) k).1 =
        (fetch ⟨r, false⟩ rulesNew fp newInp m₂ (start odb) k).1) ∧
    (∃ N, ∀ m, N ≤ m →
      (fetch ⟨r, true⟩ rulesNew fp newInp m (start odb) k).1 =
        (fetch ⟨r, false⟩ rulesNew fp newInp m (start odb) k).1)
```

### Non-vacuity witnesses

`Toy/RedGreen/Witnesses.lean` — `Toy.RedGreen.early_cutoff_agrees_nonvacuous`:

```lean
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
    (fetch ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .top = .done eK true
```

### Hypothesis counterexamples

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.reversed_replay_breaks_early_cutoff_agreement`:

```lean
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
        (fetch ⟨.reversed, false⟩ rulesR fpId newD m₂ (start odbR) (.inl .top)).1)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.ambient_dependent_code_breaks_early_cutoff`:

```lean
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
        (fetch ⟨.ordered, false⟩ (rulesM 1) fpId newM m₂ (start odbM) (.inl .top)).1)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.fp_collision_breaks_early_cutoff`:

```lean
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
        (fetch ⟨.ordered, false⟩ rulesS fpSat newS m₂ (start odbS) (.inl .top)).1)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.inconsistent_db_breaks_early_cutoff`:

```lean
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
        (fetch ⟨.ordered, false⟩ rulesB fpId newB m₂ (start odbB) (.inl .top)).1)
```

## `every-replay-order-is-value-sound`

### Results

`Toy/RedGreen/ValueSound.lean` — `Toy.RedGreen.fetch_value_sound_of_any_replay`:

```lean
/-- **Value soundness for every replay order (card
`every-replay-order-is-value-sound`).**  For any configuration — recorded,
reversed or all-edges replay, early cutoff on or off — collision-free
fingerprints, the same query code as the one that produced the database, and
a database consistent with the old input state: every incremental fetch made
during the revision (from the start database or from any database produced
from it by earlier fetches) that returns a value returns a from-scratch value
of the new state. -/
theorem fetch_value_sound_of_any_replay [DecidableEq Q] [DecidableEq F] (cfg : Config)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (m : Nat) (k : Key Q I) (v : V)
    (hv : (fetch cfg rulesNew fp newInp m db k).1 = .val v) :
    ∃ n, eval rulesNew newInp n k = .val v
```

### Non-vacuity witnesses

`Toy/RedGreen/Witnesses.lean` — `Toy.RedGreen.fetch_value_sound_nonvacuous`:

```lean
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
    eval rulesK newK 6 (.inl .top) = .val 2
```

### Hypothesis counterexamples

* `Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval` — quoted above.

* `Toy.RedGreen.fp_collision_reuses_stale_result` — quoted above.

* `Toy.RedGreen.inconsistent_db_reuses_wrong_result` — quoted above.

* `Toy.RedGreen.stale_done_slot_returns_wrong_result` — quoted above.

* `Toy.RedGreen.cyclic_new_state_both_diverge` — quoted above.

## `ordered-replay-necessary`

### Results

* `Toy.RedGreen.reversed_replay_executes_dead_dependency_and_panics` — quoted above.

* `Toy.RedGreen.exhaustive_replay_executes_dead_dependency_and_panics` — quoted above.

* `Toy.RedGreen.reversed_replay_diverges_on_dead_code_cycle` — quoted above.

* `Toy.RedGreen.exhaustive_replay_diverges_on_dead_code_cycle` — quoted above.

### Positive controls

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.ordered_replay_returns_from_scratch_value_on_dead_dependency`:

```lean
/-- **Positive control.**  On the same two instances, ordered replay (early
cutoff on or off) returns the from-scratch value `0`, and in example D leaves
the dead dependency `risky` untouched. -/
theorem ordered_replay_returns_from_scratch_value_on_dead_dependency (c : Bool) :
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .val 0 ∧
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).2 .risky =
      start odbD .risky ∧
    (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).1 = .val 0
```

## `fingerprint-collision-breaks-reuse`

### Results

* `Toy.RedGreen.fp_collision_reuses_stale_result` — quoted above.

* `Toy.RedGreen.fp_collision_breaks_early_cutoff` — quoted above.

* `Toy.RedGreen.fp_collision_diverges_although_new_state_terminates` — quoted above.

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.fp_collision_reexecutes_query_with_unchanged_recorded_dependencies`:

```lean
/-- **Collision-freedom is needed.**  Example F: `fpCollide13` collides on `1`
and `3`.  Every other hypothesis holds for `q = top` (its recorded dependency
`b ↦ 30` is unchanged in the new state), yet fetching `top` executes it: the
collision makes `a` look unchanged, so `a` is marked green with the stale `1`;
`b` is re-executed because `y` changed and computes `10` from the stale `a`;
`10` differs from the recorded `30`, so `top` is executed. -/
theorem fp_collision_reexecutes_query_with_unchanged_recorded_dependencies :
    ¬ FpInjective fpCollide13 ∧ Inv rulesF fpCollide13 oldF newF (start odbF) ∧
    start odbF .top = .old eF ∧
    (∀ d f, (d, f) ∈ eF.deps → ∃ n v, eval rulesF newF n d = .val v ∧ fpCollide13 v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesF fpCollide13 newF (start odbF) (start odbF) ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesF fpCollide13 newF 8 (start odbF) (.inl .top)
```

## `untracked-change-breaks-reuse`

### Results

* `Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval` — quoted above.

* `Toy.RedGreen.ambient_dependent_code_breaks_early_cutoff` — quoted above.

* `Toy.RedGreen.untracked_code_change_diverges_although_new_state_terminates` — quoted above.

## `inconsistent-database-breaks-reuse`

### Results

* `Toy.RedGreen.inconsistent_db_reuses_wrong_result` — quoted above.

* `Toy.RedGreen.inconsistent_db_breaks_early_cutoff` — quoted above.

* `Toy.RedGreen.inconsistent_db_diverges_although_new_state_terminates` — quoted above.

* `Toy.RedGreen.stale_done_slot_returns_wrong_result` — quoted above.

* `Toy.RedGreen.unreachable_db_diverges_although_new_state_terminates` — quoted above.

## `cyclic-new-state-both-diverge`

### Results

* `Toy.RedGreen.cyclic_new_state_both_diverge` — quoted above.

## `early-cutoff-skips-cached-query-with-unchanged-dependencies`

### Results

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps`:

```lean
/-- **Early cutoff never executes a cached query whose recorded dependencies
are unchanged.**  For any replay order with early cutoff, collision-free
fingerprints, and a working database `db₀` satisfying `Inv`: if query `q`
holds the cached entry `e` (`db₀ q = old e`) and every recorded dependency of
`e` has, in the new state, a from-scratch value whose fingerprint is the
recorded one, then for every working database `db` reachable from `db₀` by
incremental fetches, the slot of `q` in `db` is still `old e` or has been
marked green as `done e false`, and no fetch from `db` executes `q`. -/
theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps
    {Q I V F : Type} [DecidableEq Q] [DecidableEq F]
    (r : Replay) (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V)
    (db₀ : DB Q I V F) (hinv : Inv rules fp oldInp newInp db₀)
    (q : Q) (e : Entry Q I V F) (hq : db₀ q = .old e)
    (hunch : ∀ d f, (d, f) ∈ e.deps → ∃ n v, eval rules newInp n d = .val v ∧ fp v = f)
    (db : DB Q I V F) (hreach : Reachable ⟨r, true⟩ rules fp newInp db₀ db)
    (m : Nat) (k : Key Q I) :
    q ∉ execLog ⟨r, true⟩ rules fp newInp m db k ∧ (db q = .old e ∨ db q = .done e false)
```

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies`:

```lean
/-- **Early cutoff is needed.**  Example K with early cutoff off (ordered
replay): every other hypothesis holds for `q = top`, and fetching `top`
executes it (its slot becomes `done … true`), because its dependency `a` was
re-executed, although `a` reproduced its recorded fingerprint. -/
theorem no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, false⟩ rulesK fpId newK (start odbK) (start odbK) ∧
    .top ∈ execLog ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top) ∧
    (fetch ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .top = .done eK true
```

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.early_cutoff_reexecutes_query_whose_value_is_unchanged`:

```lean
/-- **Unchanged recorded dependencies are needed — and an unchanged value is
not enough.**  In example K, take `q = a` with its entry `eKa`: every other
hypothesis holds, `a`'s recorded dependency `x` changed (`1 → 3`), and fetching
`top` executes `a`, although `a`'s value (`0`) is the same in both states.
Early cutoff stops propagation at `a`'s dependents, not at `a`. -/
theorem early_cutoff_reexecutes_query_whose_value_is_unchanged :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .a = .old eKa ∧
    ¬ (∀ d f, (d, f) ∈ eKa.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesK fpId newK (start odbK) (start odbK) ∧
    eval rulesK newK 2 (.inl .a) = .val eKa.value ∧
    .a ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top) ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .a =
      .done ⟨[(.inr .x, 3)], 0⟩ true
```

### Non-vacuity witnesses

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.early_cutoff_skips_nonvacuous`:

```lean
/-- **Non-vacuity, and the property in action.**  Example K satisfies every
hypothesis of
`early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps` for
`q = top`, for every replay order: `x` changes, `a` is executed and reproduces
`0`, `y` is unchanged.  Fetching `top` executes only `a` and marks `top`
green. -/
theorem early_cutoff_skips_nonvacuous (r : Replay) :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨r, true⟩ rulesK fpId newK (start odbK)
      (fetch ⟨r, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 ∧
    execLog ⟨r, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top) = [.a] ∧
    (fetch ⟨r, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .top = .done eK false
```

### Hypothesis counterexamples

* `Toy.RedGreen.no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies` — quoted above.

* `Toy.RedGreen.early_cutoff_reexecutes_query_whose_value_is_unchanged` — quoted above.

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.stale_db_reexecutes_query_with_unchanged_recorded_dependencies`:

```lean
/-- **`Inv` is needed.**  Take `db₀ = db = staleDbK`: every other hypothesis
holds for `q = top` (its recorded dependencies `a ↦ 0`, `y ↦ 2` are unchanged
in the new state), yet fetching `top` executes it, because the stale slot makes
`a` look changed. -/
theorem stale_db_reexecutes_query_with_unchanged_recorded_dependencies :
    FpInjective fpId ∧ ¬ Inv rulesK fpId oldK newK staleDbK ∧ staleDbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesK fpId newK staleDbK staleDbK ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 staleDbK (.inl .top) ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 staleDbK (.inl .top)).2 .top ≠ .old eK ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 staleDbK (.inl .top)).2 .top ≠ .done eK false
```

* `Toy.RedGreen.fp_collision_reexecutes_query_with_unchanged_recorded_dependencies` — quoted above.

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.uncached_query_with_unchanged_recorded_dependencies_executes`:

```lean
/-- **A cached entry is needed (`db₀ q = old e`).**  In example K′ (example K
without a cached entry for `top`), `top`'s slot is `none`; with `e = eK` every
other hypothesis holds, and fetching `top` executes it (first execution in this
revision). -/
theorem uncached_query_with_unchanged_recorded_dependencies_executes :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbKnoTop) ∧
    start odbKnoTop .top = .none ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesK fpId newK (start odbKnoTop) (start odbKnoTop) ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbKnoTop) (.inl .top)
```

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.unreachable_db_reexecutes_query_with_unchanged_recorded_dependencies`:

```lean
/-- **Reachability is needed.**  Take `db₀ = start odbK` (which satisfies
`Inv`) and `db = staleDbK`, which is not reachable from it (every reachable
database satisfies `Inv`).  The slot of `top` in `staleDbK` is still `old eK`,
but fetching `top` from `staleDbK` executes it. -/
theorem unreachable_db_reexecutes_query_with_unchanged_recorded_dependencies :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    ¬ Reachable ⟨.ordered, true⟩ rulesK fpId newK (start odbK) staleDbK ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 staleDbK (.inl .top)
```
