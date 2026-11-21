# Tricolor marking invariants and write-barrier soundness (toy model)

Lean `leanprover/lean4:v4.34.1`, no Mathlib, no dependencies. Namespace `Toy.Tricolor`.

Build: `lake build`.

Modules:

* `Toy/Tricolor/Basic.lean`: heap states, colors, reachability, the strong and weak
  tricolor invariants, root conditions, collector and mutator operations, barriers,
  configurations, the step relation (heap stores write pointers held in the roots; root loads
  take reachable objects; allocation takes isolated objects) and runs.
* `Toy/Tricolor/Examples.lean`: concrete states; positive and negative examples for the
  definitions of `Basic.lean`.
* `Toy/Tricolor/EndOfMarking.lean`: end-of-marking safety from the strong and weak
  invariants; grey protection of reachable white objects; strong implies weak and not
  conversely; tightness counterexamples.
* `Toy/Tricolor/Preservation.lean`: Dijkstra barrier preserves the strong invariant; Yuasa
  barrier with non-white allocation preserves the weak invariant with its root clause;
  allocation-color characterizations; shaded root loads with non-white allocation preserve the
  strong invariant with non-white roots under any heap barrier; state-level lemmas on
  allocating a non-isolated object grey, or black with non-white targets, or black with
  root-held targets in a state whose roots are non-white.
* `Toy/Tricolor/Marking.lean`: whole marking cycles (paused mutator; Yuasa without rescan;
  Dijkstra with a final root rescan; shaded loads without rescan).
* `Toy/Tricolor/Counterexamples.lean`: the lost-object interleaving without heap or load
  barrier, root-load and allocation-color interleavings, step-relation counterexamples,
  positive controls, floating garbage, non-vacuity witnesses, and whole-cycle examples in
  which one step violates exactly one enabling condition of `Run` (isolation of allocations,
  held pointers in stores).
* `Toy/Tricolor/Termination.lean`: the measure `2·#white + #grey`, paused-mutator
  termination, the active-mutator work bound (with and without re-coloring allocation),
  termination under collector fairness with eventually black-only allocation or with
  allocation of white cells only, the counterexamples showing that no assumption can be
  dropped (1- to 3-object heaps), and scope lemmas (falsity of the fairness antecedent in
  every model; finitely many non-white allocations under white-cell allocation).
* `Toy/Tricolor/Tightness.lean`: remaining canonical-form tightness counterexamples.
* `Toy/Tricolor/RunExamples.lean`: positive and negative examples for `Step`, `Run`,
  `ScansOnly` and the termination definitions.
* `Toy/Tricolor/Companions.lean`: proof-only corollaries of results in the other modules (the
  execution with non-enabled scans also refutes the infinitely-often termination corollary).
