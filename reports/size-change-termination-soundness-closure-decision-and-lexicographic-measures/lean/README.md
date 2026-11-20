# Toy.SCT — size-change termination: soundness, closure decision, and lexicographic measures

Self-contained Lake project (Lean `v4.34.1`, no dependencies, no Mathlib).

* `Toy/SCT/Graph.lean` — arc labels and their sequencing (`Label.seq`, plus the deliberately wrong
  `seqOverStrict`, `seqForgetLeft`, `seqForgetRight`), size-change graphs `SCG nf k`, composition
  `compWith` / `comp`, programs `Prog nf k`, the composition closure `InClosureWith`, the closure
  criterion `ClosureCriterion` and its variants (`WeakSelfArcCriterion`, `GeneratorCriterion`,
  `CriterionWith`, `NoLoopGuardCriterion`, `AllLoopsCriterion`).
* `Toy/SCT/Semantics.lean` — what a graph says about argument values (`RespectsIn`), consistent
  infinite and finite runs, semantic models (`StepRespects`, `Terminates`, `runStep`), call paths and
  threads (`SizeChangeTerminating`), lexicographic projection measures (`LexLt`, `LexProjDecreases`).
* `Toy/SCT/Check.lean` — the decision procedure `checkSCT` (fixpoint iteration with fuel).
* `Toy/SCT/Enum.lean` — an explicit list of all `nf * nf * 3 ^ (k * k)` size-change graphs.
* `Toy/SCT/Ramsey.lean` — infinite Ramsey theorem for pairs with finitely many colours.
* `Toy/SCT/Threads.lean` — thread semantics of composition; factor paths of closure graphs.
* `Toy/SCT/Soundness.lean` — closure criterion ⇒ size-change termination (via Ramsey);
  size-change termination ⇒ no consistent run over `Nat`.
* `Toy/SCT/Exactness.lean` — failing criterion ⇒ consistent run over `Nat`.
* `Toy/SCT/CheckCorrect.lean` — soundness and completeness of `checkSCT`.
* `Toy/SCT/Fixtures.lean` — concrete programs and models used throughout.
* `Toy/SCT/Examples.lean` — helper lemmas and the proved positive and negative examples of every
  definition.
* `Toy/SCT/Results.lean` — the main statements and their non-vacuity witnesses.
* `Toy/SCT/Counterexamples.lean` — counterexample results, tightness witnesses, positive controls.
* `Toy/SCT/Infinite.lean` — a generalized model with arbitrary function and parameter types,
  showing that finiteness of both is needed (graph-level and model-level counterexamples), and
  proving that on finite types it agrees with the package's model.
* `Toy/SCT/Audit.lean` — build-time axiom and `sorry` audit.

* `RevalidationAudit.lean` (outside the library target) — prints `#print axioms` and the statement
  and definition-closure text of every declaration named in a result card's structured Lean fields;
  run it with `lake env lean RevalidationAudit.lean` after `lake build`.

Build with `lake build`. The audit prints `AUDIT OK` and fails the build if any declaration
depends on `sorryAx`, or on an axiom other than `propext`, `Quot.sound`, `Classical.choice`.
