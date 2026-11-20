# Toy.RedGreen — demand-driven red-green query memoization and early cutoff

Self-contained Lake project (Lean `v4.34.1`, no dependencies, no Mathlib).

* `Toy/RedGreen/Basic.lean` — programs with dynamic dependencies (`Prog`), outcomes, from-scratch evaluation
  (`eval`), traces (`Prog.runT`), databases and slots, the incremental algorithm (`fetch`, `markGreen`,
  `checkDeps`, `exec`, `Replay`, `Config`), consistency (`EntryConsistent`, `DBConsistent`), the simulation
  invariant `Inv`, `Reachable`, and the conclusion predicate `AgreesWithEval`.
* `Toy/RedGreen/ExecLog.lean` — an instrumented copy of the algorithm (`fetchX`) that logs every query
  execution, the log `execLog`, and the proof `fetchX_eq` that the instrumentation does not change `fetch`.
* `Toy/RedGreen/Examples.lean` — concrete instances (examples D, C, K, K′, L, H, S, N, M, B, P, F, R, PC and the
  divergence instances) and `recordAll`.
* `Toy/RedGreen/Lemmas.lean` — fuel monotonicity of `eval`, uniqueness of consistent entries, `inv_start`,
  refutation helpers.
* `Toy/RedGreen/Frame.lean` — fetches never create `old` slots.
* `Toy/RedGreen/ValueSound.lean` — card `every-replay-order-is-value-sound`: for every replay order, one fetch
  preserves `Inv` and returns only from-scratch values; `inv_of_reachable`.
* `Toy/RedGreen/DefExamples.lean` — positive and negative examples for every core definition.
* `Toy/RedGreen/Soundness.lean` — cards `incremental-fetch-agrees` and `early-cutoff-agrees-with-reexecution`;
  the main simulation invariant `fetch_simulation_invariant`.
* `Toy/RedGreen/Replay.lean` — card `ordered-replay-necessary`, its positive control, and the replay-order
  counterexample for `early-cutoff-agrees-with-reexecution`.
* `Toy/RedGreen/Necessity.lean` — cards `fingerprint-collision-breaks-reuse`, `untracked-change-breaks-reuse`,
  `inconsistent-database-breaks-reuse`, `cyclic-new-state-both-diverge`, and the divergence and reachability
  counterexamples.
* `Toy/RedGreen/Minimal.lean` — card `early-cutoff-skips-cached-query-with-unchanged-dependencies` and its
  counterexamples.
* `Toy/RedGreen/Witnesses.lean` — non-vacuity theorems.
* `Toy/RedGreen/Audit.lean` — build-time axiom audit.

Build with `lake build`. The audit prints `AUDIT OK` and fails the build if any declaration of the project depends
on an axiom other than `propext`, `Quot.sound`, `Classical.choice` (in particular, on `sorryAx`).
