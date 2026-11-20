# Toy.Scc — SCC condensation and mutual-recursion fixpoint summaries

Self-contained Lake project (Lean `v4.34.1`, no dependencies, no Mathlib).

* `Toy/Scc/Graph.lean` — call graphs, reachability (inductive and fuel-bounded), SCC decompositions, condensation,
  processing orders, the SCC checker, fixture graphs, and definition examples.
* `Toy/Scc/Lattice.lean` — summary vectors, monotonicity and call-locality laws, extremal fixpoints, Kleene iteration,
  the monotone transfer families used by the fixtures, and definition examples.
* `Toy/Scc/BottomUp.lean` — the single-pass bottom-up algorithm, hierarchical solutions (coordinatewise
  block-extremality), certification helpers, the correctness proof of the bottom-up pass, examples.
* `Toy/Scc/Decomp.lean` — cards `scc-check`, `scc-char`, `topo-order`.
* `Toy/Scc/Fixpoint.lean` — cards `kleene-bound`, `bottomup-one-sided`, `prefix-postfix-sound`, `checks-not-exact`,
  `ranked-cert`, `ranked-cert-complete`.
* `Toy/Scc/Transfer.lean` — cards `bottomup-lfp`, `bottomup-gfp`, `bottomup-mixed`, `mixed-neither`, `merge-convex`,
  `merge-nonconvex`, `split-scc`, `caller-first`.
* `Toy/Scc/Termination.lean` — cards `lex-iff`, `termination-intra`, `inner-alone`.
* `Toy/Scc/Checks.lean` — mechanical cross-checks: each tightness counterexample, combined with its main theorem,
  refutes exactly the dropped hypothesis; each main theorem is instantiated at its non-vacuity witness.
* `Toy/Scc/Audit.lean` — build-time axiom and `sorry` audit.

Build with `lake build`. Every result is fully proved. The audit prints `AUDIT OK` and fails the build if any
declaration depends on `sorryAx`, or if any declaration depends on an axiom other than `propext`, `Quot.sound`,
`Classical.choice`.
