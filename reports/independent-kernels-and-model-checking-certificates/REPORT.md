# Independent checking, model-checking witnesses, and a concrete kernel boundary

## Summary

Different implementations reduce some correlated failures, but shared conversion rules, exports, primitives and statement selection remain common boundaries. The exact Lean 4.31 and legacy 4.30rc2 sources inspected here contain an omitted nested-parameter validation path fixed by upstream PR 14577. A zero-axiom dependency list therefore does not establish adversarial checking assurance for those pins.

IC3 search can be removed from the trusted path by checking its final inductive invariant. Certifaiger generalizes the witness to a circuit related to the original model, with distinct safety and liveness obligations. Checking those obligations still needs a trustworthy circuit-to-formula translation and the selected SAT-proof checking mode.

## Applicability

This is a source and primary-theorem comparison, not a new checker deployment or an exploit run. Exact revisions are in REPORT.json and support/evidence.json. The inspected Nanoda, Lean4Lean, Comparator and Isabelle snapshots are separate subjects; compatible export versions and simultaneous acceptance were not executed. The model-checking claims concern finite Boolean transition systems with their original reset, constraint, transition and property definitions.

## Findings

### The exact kernel defect changes what our previous observations establish

Basis: **source**, upstream issue and fix, **derived** applicability.

[PR 14577](https://github.com/leanprover/lean4/pull/14577) identifies nested inductive applications whose parametric arguments disappear during auxiliary-type construction. The fix adds their local context and finally invokes `tc.check` on the restored nested applications in the new environment. [Issue 14576](https://github.com/leanprover/lean4/issues/14576) reports an ordinary checked `addDecl` repro on nightly `0bfc3acaef4ed0576307a77fbaa0c6e1a5dca402`; the report prints no axioms and does not rely on the documented checking bypasses.

Direct inspection of `environment::add_inductive` finds the omitted final check at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (4.30rc2) and `68218e876d2a38b1985b8590fff244a83c321783` (4.31). It finds the added check at `5045d0056413266e57c625dcd7c365b10e377c52` (4.34.1). Exact paths, line ranges, source fingerprints and Boolean inspection results are retained in support/kernel-boundary.json. This establishes source affectedness of those two old paths. It does not execute the full repro, identify the earliest introducing commit, or infer that every earlier version is affected.

The official [4.32.2 release account](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) also explains that Nanoda did not have that same bug, yet a combined proof could exploit a separate Nanoda bug. Checking twice is useful evidence about implementations, not a mathematical guarantee that their errors are independent. Conversely, presence of this particular fix in 4.34.1 does not prove universal soundness of that release.

Controlled prior proofs and native runs remain observations about exact artifacts. They must be interpreted under the implementation frontier. Their printed `propext`/`Quot.sound`/choice lists describe logical dependencies, not correctness of the executing checker, loader or runtime.

### The source implementations provide different kinds of diversity

Basis: **source**, **derived** classification.

Nanoda `src/tc.rs` checks theorem/definition bodies through type inference and definitional equality, keeps separate checked and inference-only caches, and implements projection checking against the inferred structure name. Its `src/inductive.rs` implements its own inductive-declaration pipeline over Rust arena/DAG structures. This is independent implementation work and a distinct runtime, but still shares Lean's intended theory, primitive specifications, and exported environment.

Lean4Lean uses Lean expressions, Lean execution and an algorithm closely corresponding to the reference kernel: `TypeChecker.lean` explicitly identifies the C++ projection counterpart, weak-head-normalization cache and conversion routines. It supplies a useful formalization/verification route and another implementation, while preserving more implementation structure and host machinery than an unrelated encoding. This comparison does not reclassify every current verification theorem or assume that prior reports about other Lean4Lean pins apply unchanged.

Comparator `Main.lean:152–206,288–303` distinguishes external process failure from successful exit, accumulates any external rejection/error, replays the builtin environment, and rejects if any selected checker fails. `compareAt` and `checkAxioms` precede replay. This is an all-selected-checkers admission policy, not majority voting. Missing output, crash, resource exhaustion and logical rejection should remain different diagnostics even where all deny acceptance. The shared exporter and trusted challenge definitions still require independent binding.

### IC3/PDR needs an invariant certificate, not a faithful search trace

Basis: primary algorithm paper, **source**, **derived** checking interface.

[Bradley's VMCAI 2011 paper](https://theory.stanford.edu/~arbrad/papers/IC3.pdf) describes clause frames refined by relative induction until a frame becomes an inductive strengthening or a concrete counterexample is produced. The original IC3ref `check()`/`propagate()` source preserves this relationship: pushing all border clauses forward establishes the fixed-frame success condition.

For a candidate invariant `J`, a consumer can instead check unsatisfiability of `I ∧ ¬J`, `J ∧ T ∧ ¬J'`, and `J ∧ ¬P` for the independently selected `I,T,P`. The final certificate need not reproduce clause generalization or frame scheduling. A counterexample needs initial-state, every transition, constraints and final bad-state replay. An invariant about a substituted transition relation proves a different problem.

Bounded UNSAT alone establishes only the tested prefix bound. The original [BMC work](https://cca.informatik.uni-freiburg.de/papers/BiereCimattiClarkeZhu-TACAS99.pdf) and [Biere's simple-path presentation](https://cca.informatik.uni-freiburg.de/biere/talks/Biere-SAT-SMT-Summer-School-2011.pdf) distinguish this from completeness. A checked recurrence-diameter/no-longer-simple-path bound can close finite-state exploration; k-induction uses separately checked base and inductive cases. Neither a producer-supplied bound nor a timeout supplies completeness.

### Witness circuits separate model simulation, induction and liveness

Basis: **source**, primary theorem.

Certifaiger's pinned `src/certifaiger.cpp:440–551` emits Reset, Transition, Safety, Liveness, Base, Inductive, Decrease, Closure and Consistent outputs. The format retains an original model and a witness circuit, shared-latch/input mappings and optional intervention mappings. An optional filename/hash comment is descriptive metadata; it cannot select the consumer's model.

The [CAV 2026 liveness paper](https://cca.informatik.uni-freiburg.de/papers/FroleyksYuBogaertsBiereHeljanko-CAV26.pdf), Definitions 1–8 and Theorem 1, proves a finite-circuit witness rule using simulation, inductiveness and propositional ranking conditions. Its liveness property is eventual permanent truth of an edge signal. Reset stratification and finite state are essential; this is not unrestricted Rust fairness or arbitrary LTL interpretation. The paper's eight-condition presentation and the source's additional multi-signal consistency condition should not be silently identified as the same proved generalization.

`scripts/check_unsat.in` negates/splits the circuit obligations and translates them with `aigtocnf`. Its ordinary mode trusts SAT solver status 20. Its configured proof mode also checks the proof-consumer status; LRAT modes select different expected exit codes and wait for both processes. Reusing a verified LRAT checker removes trust in that SAT answer, while leaving AIGER parsing, obligation generation, CNF meaning, wrapper execution and original-model binding to justify.

### Reconstruction and reflection remove different work from trust

Basis: **source**, narrow reuse of the original Isabelle study.

[Hammering Away](https://isabelle.in.tum.de/~blanchet/h4qed.pdf) separates external discovery from reconstruction. In the pinned Isabelle source, Metis reconstruction produces host theorems through proof rules. `smt_solver.ML:253–285` explicitly chooses replay when `smt_oracle` is disabled, errors if replay is unavailable, and has a separately registered oracle route when enabled. A solver success flag is not the reconstruction result.

Reflection instead proves a checker sound once, then checks a computation on a quoted object. Quotation must denote the original goal, the soundness theorem must entail the required property, and the chosen evaluation path must be accounted for. The sibling finite-heap prototype exercises this pattern over data; its conditional implementation frontier is the exact Lean boundary above.

For Anneal, retain the consumer statement, checker family/version, original transition/program encoding, permitted axioms, exported primitives, proof mode and complete result vector. Diversity is a reason to investigate disagreement, never a reason to accept an unexplained disagreement.

## Boundaries

**Not executed:** independent Nanoda/Lean4Lean replay, IC3, Certifaiger, Isabelle, or the kernel exploit. Algorithm family/source differences and the real upstream incident answer the bounded diversity question; no statistical failure-independence estimate is claimed.

**Not established:** complete current Lean metatheory verification, conversion correctness of an arbitrary export, soundness of all Certifaiger multi-signal extensions, completeness of a bounded run without its extra evidence, or a Rust liveness interpretation. Implementing an Anneal adapter remains future engineering after selecting those semantics and premises.

## Evidence

support/evidence.json identifies inspected immutable source units and their normalized-text hashes. support/kernel-boundary.json records the three exact source comparisons. Primary paper identities and narrow sections are linked beside their claims. No source repository mirror or exploit program is included in this package.

## Revalidation

Diff the final nested-application checks at the exact Lean pins; inspect projection/conversion/inductive pipelines and shared exporters before changing the diversity classification. Check Comparator's all-selected result logic. For another model checker, obtain its exact invariant/witness grammar and soundness relation, and test the selected model/property binding separately from the SAT-proof consumer.

*Authored by an AI agent acting on joshlf's behalf.*
