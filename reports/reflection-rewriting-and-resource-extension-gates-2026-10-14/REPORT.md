# Reflection, rewriting, spatial rules, and checked extension gates

## Summary

Automation can earn authority either through a proved transformation on quoted syntax or by reconstructing a proof from a proposed explanation. The examined Rocq rewriter has an interpretation-preservation theorem with well-formedness and rule-correctness premises; lean-egg reconstructs host equality proofs and retains side-condition subgoals. Aeneas' examined spatial draft proves heap-splitting and frame rules directly in Lean.

A small fresh Lean experiment checks the generic invariant interface: initiation, preservation, and consequence are sufficient to prove safety of every reachable state. This does not turn bounded traces into unbounded safety or supply liveness evidence.

## Applicability

The immutable source pins in REPORT.json are separate subjects. Aeneas claims apply to exact draft head 75fb1479040d32d43d31b74510167ee3b873d28a, previously audited in the reference corpus, not current Aeneas main or Anneal's selected release. The draft's typed-slot model is not established here as a semantics of arbitrary unsafe Rust. lean-egg was not built.

The fresh InvariantGate.lean experiment uses Lean 4.34.1/commit 5045d0056413266e57c625dcd7c365b10e377c52, Darwin 27 arm64, with binary identity under support/. It is a report-owned generic interface demonstration, not an imported analyzer certificate.

Research contributions concern T018–T020, T033, T089, T094–T095, P051, and P054. Complete IC3/PDR and liveness certificate systems, a certified spatial checker, and measured specialization costs remain open.

## Findings

### Proved rewriting must bind quoted syntax, rule interpretation, and the result

Basis: **source**.

The Rocq rewriter's InterpRewrite theorem states equality of interpretation between Rewrite(rewrite_head,fuel,e) and e. It requires expr.Wf e and a correctness premise for rewrite_head that is valid under a semantically sound recursive do_again operation. Its surrounding section also assumes the interpretation/inversion/transport interface conditions used in the proof. This is a precise semantic endpoint, not a theorem that every plugin can define an arbitrary rewrite_head.

Rewriter.v distinguishes rule specifications, compiled rule data, decision-tree/precomputed paths, and default_fuel. Rewrite is bounded by supplied fuel; an exhausted search need not find a normal form, but a semantically proved result remains valid. Fuel therefore addresses computation/search termination at that interface, not completeness of normalization.

Sources: [InterpProofs.v](https://github.com/mit-plv/rewriter/blob/902bd7bfd807f4511fa07b0b1f07ca640f9da4a8/src/Rewriter/Rewriter/InterpProofs.v), section premises (near1470), interp_repeat_rewrite (1529), InterpRewrite (1591–1609); [Rewriter.v](https://github.com/mit-plv/rewriter/blob/902bd7bfd807f4511fa07b0b1f07ca640f9da4a8/src/Rewriter/Rewriter/Rewriter.v), repeat_rewrite/Rewrite (1438–1453), rewriter_dataT and Rewrite interface (1543–1587).

The correct published identity is [Accelerating Verified-Compiler Development with a Verified Rewriting Engine](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.17), ITP 2022 article 17, DOI 10.4230/LIPIcs.ITP.2022.17. The source pin, not an invalid placeholder DOI or a broad performance headline, supports the theorem account here. No build of the large rewriting engine or fresh transitive axiom audit was performed.

For reflection, two bridges are needed: quotation of the consumer's host expression into well-formed syntax with preserved meaning, and correctness of the quoted transformation/checker. A theorem about the latter does not silently prove the former.

### Equality saturation can be untrusted search with checked reconstruction

Basis: **source**.

At the inspected lean-egg pin, Explanation.proof handles the proposed explanation through host congruence, rewrite proof application, and definitional-equality checks. Rewrite instances must match both actual lhs and rhs; proof/instance side conditions are checked or retained as obligations. A reified equality step also validates that the left side is an equivalence whose members are definitionally equal.

In the normal proof-producing path, the tactic's resultToProof reconstructs from the explanation and abstracts remaining metavariables. Its success branch reopens these as subgoals, assigns the reconstructed proof to the consumer goal by assignIfDefeq', and returns the subgoals. An e-graph equality or tactic success log is therefore insufficient if the final declaration retains obligations. Congruence/rewriting evidence and final host checking are the authority path.

Sources: [Explanation/Proof.lean](https://github.com/marcusrossel/lean-egg/blob/2605a63b6a78407114c692f5dc626531ff62df55/Lean/Egg/Core/Explanation/Proof.lean), rewrite matching/conditions (151–181), reified equality (190–201), prove' (262 onward); [Tactic/Basic.lean](https://github.com/marcusrossel/lean-egg/blob/2605a63b6a78407114c692f5dc626531ff62df55/Lean/Egg/Tactic/Basic.lean), resultToProof (21–38), proof assignment/subgoals (74–84).

There is an explicit admission mode: runEqSat returns none for exitPoint.beforeEqSat or beforeProof, and eval then calls goal.id.admit. Core/Config.lean defines these Debug.ExitPoint alternatives with default none. The reconstruction claim requires the normal none exit-point setting and a final declaration that meets the consumer's admission/dependency policy. Sources: the same Basic.lean (82, 88–91) and [Core/Config.lean](https://github.com/marcusrossel/lean-egg/blob/2605a63b6a78407114c692f5dc626531ff62df55/Lean/Egg/Core/Config.lean), Debug.ExitPoint/config (52–59). This is a source configuration finding; no frontend execution was run.

This normal path is proof reconstruction from an e-graph, not a verified equality-saturation engine or an audit of every unsafe foreign interface. A fully checked host proof can reduce the trust needed in explanation search; source lowering, semantics of registered rewrites, final axioms, and evaluator policy still require attention.

### Spatial proof rules can be direct semantic lemmas

Basis: **source**, with narrowly reused corpus findings.

Aeneas' draft IProp is an upward-closed Heap→Prop predicate. sep requires compatible heap fragments whose union is the owned heap. owns_union proves that owning a compatible union is equivalent to separating ownership of the fragments; Ref.pointsTo_exclusive proves duplicate ownership of a single typed slot entails False.

The draft iwp quantifies over every disjoint frame and runs rawIwp with that frame retained in the postcondition. ispec and dispec select total and partial correctness. ispec_frame then derives framed triples using associativity; the frame property is in the semantics, not an unchecked tactic convention. Sources: [Basic.lean](https://github.com/AeneasVerif/aeneas/blob/75fb1479040d32d43d31b74510167ee3b873d28a/backends/lean/Aeneas/SepLogic/Basic.lean), IProp (39–45), sep (106–117), owns_union/pointsTo_exclusive (369–389); [Std/WP.lean](https://github.com/AeneasVerif/aeneas/blob/75fb1479040d32d43d31b74510167ee3b873d28a/backends/lean/Aeneas/Std/WP.lean), iwp/ispec/dispec (58–76), ispec_frame (239–246), dispec_frame (376 onward).

A spatial certificate checker could quote predicates and validate splitting, framing, unfolding, and updates against these semantic lemmas. It would need a proved soundness endpoint for its quoted judgment and a connection to the consumer's actual heap predicates. This report has not acquired or built such a checker. Direct Lean proof application is available in the inspected draft; this is a comparison basis, not evidence that a certified small spatial checker exists there.

The existing reference reports aeneas-separation-logic-status-2026-09-26 and iris-concepts-for-rust-aeneas-separation-logic-2026-09-27 were read through Findings and Boundaries before reuse. Their narrow reused fact is that this exact draft models typed-slot heaps and separate Lean operations, while arbitrary Rust raw-pointer translation/adequacy is not established. This audit independently inspected the cited core rule definitions.

### The smaller invariant checker needs semantic obligations, not the analyzer's method

Basis: **derived** + **execution**.

InvariantGate.lean fixes the consumer's init relation, step relation, and safety predicate. InvariantEvidence contains proofs of initiation (Init⇒I), preservation (I(s)∧Step(s,t)⇒I(t)), and consequence (I⇒Safe). invariant_gate proves by induction on Reach that the supplied evidence makes every reachable state safe. The proposed even-number invariant for transitions n↦n+2 satisfies all three obligations. The generic gate has no axioms; the concrete demonstration depends only on propext. Final elaboration exits 0 without sorryAx.

An untrusted analyzer may propose I through abstract interpretation, IC3/PDR search, synthesis, or a human hint. The checker can validate the same three obligations independently of that search, provided the transition encoding and implication-checking endpoint are sound. This report does not claim that a particular PDR implementation emits this interface.

Bounded traces establish reachability/counterexamples at a given depth, or absence only within that depth. Extending absence to unbounded safety requires a justified completeness threshold or an inductive argument. Liveness requires additional progress/fairness/acceptance evidence; a safety invariant alone cannot supply it. These are derived semantic distinctions, not an audit of an IC3/PDR or liveness certificate grammar.

### Extension capabilities should carry checked semantic interfaces

Basis: **derived**, supported by the checked generic interface.

The report-owned CheckerAdequacy structure separates a check function from its sound field: for every consumer statement and witness, check=true implies the statement's meaning. Supplying a new search routine is not a substitute for supplying this field. For a new primitive model, also bind the encoded primitive to the intended operational semantics through adequacy evidence; for a new property domain, provide interpretation and rule/checker soundness.

A tactic/lemma extension may simply emit a host proof. A reflection extension should supply quotation and checker/transformation correctness. A staged specialization extension should prove that the specialized checker preserves the original checker predicate or theorem. An e-graph rule extension should carry the host equality theorem and explicit conditions used by reconstruction. These are design obligations for P054/T095; this is not an implemented Anneal registration API.

## Boundaries

**Answered:** concrete reflection/reconstruction authority paths, direct spatial rule endpoints, the generic checked invariant interface, and evidence requirements for extension design.

**Research still open:** certificate formats and implementation proofs for ownership splitting/predicate unfolding/resource updates; comparative spatial checking costs; exact IC3/PDR, completeness-bound, and liveness certificate mechanisms.

**Future implementation obligations:** Anneal-specific quotation, primitive adequacy, extension registration, specialization validation, and proof/dependency policy. Their absence does not make the source theorem comparisons incomplete.

**Not established:** semantic equivalence between Aeneas IProp and full Iris, unsafe-Rust adequacy, or a proved lean-egg engine. No performance claim follows from the number of theorems, finite fuel, or e-graph reuse.

## Evidence

support/evidence.json records immutable primary source coordinates and retrieved-content hashes. The official ITP 2022 page supplies publication identity only. support/InvariantGate.lean, its output, and observations.json preserve the fresh derivation and exact execution identity. The two read reference packages were reused only for their explicit model/adequacy boundaries at google/zerocopy reference commit a0ff759e7d2d9a953f0ac40b326dd23197bd9188: reports/aeneas-separation-logic-status-2026-09-26/REPORT.md and reports/iris-concepts-for-rust-aeneas-separation-logic-2026-09-27/REPORT.md. No later/main status was inferred.

## Revalidation

Check the full assumptions of InterpRewrite, quotation soundness, rewrite-rule interpretation, and any specialized checker theorem. Diff lean-egg matching, side-condition handling, and final goal/subgoal assignment. Re-run the generic invariant fixture with the recorded Lean binary; then test a proposed invariant that violates initiation or preservation through the actual deployment adapter. Diff Aeneas' spatial judgment definitions before reusing the frame/split rules at a new revision.


*Authored by an AI agent acting on joshlf's behalf.*
