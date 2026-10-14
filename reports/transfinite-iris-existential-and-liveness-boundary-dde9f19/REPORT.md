# Transfinite Iris: existential witnesses, termination and refinement

## Summary

Transfinite Iris addresses a precise obstacle to termination proofs: a witness that exists separately at every finite step index need not be one witness valid at every index. Its `LargeIndex` interface permits the latter extraction for downward-closed predicates. The refinement logic then proves preservation of strong normalization, while an ordinal-credit instance proves termination without an upfront finite execution bound.

The inspected theorem is conditional on logical source/state interpretations, a large step-index instance and, for strong normalization, classical reasoning. The concrete ordinal construction uses choice and extensionality axioms. This framework is not a fairness theorem for Rust threads, a Rust operational model, or a universal upgrade of finite Iris.

## Applicability

The primary paper is the PLDI 2021 final version, DOI `10.1145/3453483.3454031`, SHA-256 `9fa709124b9c058076809816475c26212776a3084ea6322267af562978523427`. Its technical documentation is dated May 14, 2021, SHA-256 `d9cbc16acd64e3a2deea0afcba45a117bf137dc002066a10a33bd5d197f191b8`. These are distinguished from source commit `dde9f193fb3d504be680480b2ca21052edae49df` of `iris/transfinite`, committed August 11, 2025. The source is a later repository observation, not claimed to be the untouched PLDI submission artifact.

The inspected README lists Coq 8.11.2 and stdpp 1.3.0 as a known build combination. No Rocq build, `Print Assumptions` execution or dependency installation was performed. Source theorem statements and proofs were inspected directly. The paper and source README use different theorem numbering, so mappings below name declarations and premises rather than identifying them by number alone.

## Findings

### F1. LargeIndex states the required existential property

Basis: source + documentation.

`theories/algebra/stepindex.v:LargeIndex` has a universe constraint `i < j`. For every small witness type `X : Type@{i}` and downward-closed predicate `P : X → SI → Prop`, it maps `(∀ a, ∃ x, P x a)` to `∃ x, ∀ a, P x a`. The downward-closure premise is explicit: if `a ≺ b`, then `P x b → P x a`. This is stronger than rearranging quantifiers inside the object logic.

`base_logic/satisfiable.v` defines `uPred_satisfiable P := ∀ n, ∃ x, ✓{n} x ∧ P n x`. The lemma `uPred_satisfiable_exists`, under `LargeIndex SI`, obtains a fixed logical existential witness while still allowing different resource witnesses at different indices. `base_logic/lib/fancy_updates.v:satisfiable_at_exists` lifts that property through world satisfaction and updates. The adequacy proof uses these declarations rather than an informal appeal to “infinite indices.”

The paper's motivating finite-index failure is an existential witness chosen increasingly late as the index grows. An object-logic existential can then hold at every index without yielding a witness usable externally for an infinite execution argument. Ordinal indices large enough relative to the witness type eliminate that escape. This explanation concerns the logic's model, not bounded symbolic execution.

### F2. The actual adequacy endpoint preserves strong normalization

Basis: source.

`program_logic/refinement/ref_adequacy.v` works with a target `language`, a logical `source Σ A`, and `ref_irisG` carrying source/state interpretations. Its `rwp_tp_pre` permits a target step either with a source advancement under a later or with a same-source continuation justified through a least-fixpoint argument. `rwp_tp` is a BI least fixpoint; not every recursive occurrence is guarded by a later.

`guarded_satisfiable` requires `sn source_rel a`, `LargeIndex SI`, and satisfiability of `guarded a P`; it yields satisfiability of `P`. `rwp_adequacy` combines a strongly normalizing source, an infinite target loop, and satisfiability of `source_interp a ∗ ref_state_interp σ n ∗ RWP e ...` to derive `False`. `rwp_sn_preservation` adds the `Classical` instance and concludes `sn erased_step ([e], σ)`. Classical reasoning is used to infer strong normalization from the absence of an infinite loop. The declarations separate that step from the logical contradiction argument.

The concrete `examples/refinements/refinement.v:heap_lang_ref_adequacy` requires, for all newly allocated `rheapG`, `seqG` and authoritative source ghost-state instances, a proof from `src s` to a sequential refinement WP of `t` with a relational result postcondition `φ`. Its conclusion has two components: every target termination has a corresponding source result related by `φ`; and source strong normalization implies target strong normalization. `heap_lang_ref_adequacy_fully_closed` fixes the ghost functors to `refΣ ordI` and supplies excluded middle using `Coq.Logic.Classical_Prop`. It still assumes the program's logical refinement proof.

This is the source counterpart of the final paper's Theorem 4.3. The README calls its refinement-adequacy theorem “Theorem 3.3,” reflecting a numbering mismatch rather than an additional theorem. The result relation and strong-normalization implication above are the stable semantic identification.

### F3. Ordinal credits and the concrete foundational assumptions

Basis: source.

`examples/termination/adequacy.v:heap_lang_ref_adequacy` assumes `Classical`, `LargeIndex`, heap ghost state, non-atomic invariant state and authoritative ordinal-credit resources. Its program premise is a logical existential `∃ α, $α -∗ SEQ e ⟨⟨ v, True ⟩⟩`, quantified over freshly chosen ghost-state instances. The conclusion is `sn erased_step ([e], σ)`. The existential property extracts one sufficient ordinal outside the logic. `heap_lang_ref_adequacy_closed` instantiates `ordI`, the required ghost functors and classical reasoning; the source ends with `Print Assumptions` as an upstream audit command, whose output was not replayed here.

`algebra/ordinals/ord_stepindex.v:set_model_large_index` proves `LargeIndex ordI` via `commute_exists` and an ordinal upper-bound argument. Its header identifies propositional extensionality, functional extensionality, Hilbert epsilon, excluded middle and proof irrelevance (the last implied by propositional extensionality). `set_model.v` explicitly imports epsilon and the two extensionality libraries, constructs intensional well-founded set trees, then uses a choice operator to obtain an extensional model. The closed program theorem therefore closes resource-instantiation parameters, not all foundational assumptions. The exact compiled dependency list remains unknown without the recorded `Print Assumptions` replay.

### F4. What transfinite indices change and what they do not

Basis: source + documentation + derived.

`examples/counterexamples.v:no_later_existential_commuting` demonstrates a compatibility cost: the transfinite existential property conflicts with the finite-Iris style rule commuting a later through an existential in the stated BI setting. The finite and transfinite logics therefore have different admissible laws. A proof using a convenient finite-index law cannot be transferred merely by changing the index type.

Ordinary partial correctness says that terminating executions satisfy a postcondition and, in a safety WP, that represented executions do not get stuck. It does not require termination. Finite credits can justify a fixed step budget; ordinal credits can justify well-founded decreases and existentially sufficient ordinal budgets. Obligations and scheduler fairness address a different question: whether a particular enabled thread or external action will eventually proceed. This inspected strong-normalization theorem does not add fair-scheduler premises or prove that theorem for a Rust scheduler.

The source includes `examples/termination/eventloop.v` and termination logical relations; these show the framework's application beyond first-order numerical ranking functions. Their complete proof bodies, operational scheduler choices and costs were not audited here. No hazard-pointer, RCU, Rust async, lock-freedom or cancellation claim follows from those filenames.

### F5. A reusable certificate interface for Anneal liveness

Basis: derived from F1–F4.

A liveness claim should identify its reduction relation and distinguish four endpoints: safety/conditional result, bounded cost, strong normalization, and fairness-dependent eventual behavior. For a transfinite termination certificate, preserve the index/witness universes, the `LargeIndex` instance, chosen ordinal algebra, source relation and its well-foundedness argument, logical source/state interpretations, the refinement or credit proof, and the foundational assumption closure. For fairness-based progress, additionally state which scheduling/environment assumptions are required and prove an adequacy theorem for that trace property.

This answers the named transfinite mechanism comparison in R028 with explicit constraints. A Lean port, Rust model instantiation, proof automation and runtime cost study are future engineering or new experiments. Comparing particular obligation/fairness libraries remains research outside this package; this report does not silently claim they were examined.

## Boundaries

- **Not examined:** full formalization replay, actual axiom output, every termination example, fairness/obligation frameworks, Rust source extraction or correspondence, or a Lean transfinite-Iris implementation.
- **Unknown:** modern Rocq compatibility and engineering effort of a Lean port. A successful public source retrieval does not settle either question.
- **Known not to apply:** a strong-normalization result cannot be read as progress under fair scheduling alone, and HeapLang adequacy is not Rust UB/provenance adequacy. Later/existential laws require compatibility checks before transferring a finite-Iris proof.
- **Operational failures:** an initial guessed project URL ending in `transfinite-iris` failed; the official project page resolved `iris/transfinite` successfully. An unavailable local PDF text-extraction executable was not installed; source and primary web PDF text were used. Neither failure is a negative tool-support result.

## Evidence

Primary documentation: [PLDI 2021 final paper](https://iris-project.org/pdfs/2021-pldi-transfinite-iris-final.pdf), §§2, 4 and 5, especially Theorem 4.3; [technical documentation](https://iris-project.org/pdfs/2021-pldi-transfinite-iris-final-appendix.pdf), §§2.2–2.3, 4.4, 9.3–9.4. Artifact hashes are recorded under Applicability.

Primary source: [transfinite-Iris commit](https://gitlab.mpi-sws.org/iris/transfinite/-/tree/dde9f193fb3d504be680480b2ca21052edae49df), `theories/algebra/stepindex.v:479–486`; `theories/algebra/ordinals/ord_stepindex.v:1–17, 300–321`; `theories/algebra/ordinals/set_model.v:364–385`; `theories/base_logic/satisfiable.v:uPred_satisfiable_exists`; `theories/base_logic/lib/fancy_updates.v:satisfiable_at_exists`; `theories/program_logic/refinement/ref_adequacy.v:guarded_satisfiable/rwp_adequacy/rwp_sn_preservation`; `theories/examples/refinements/refinement.v:heap_lang_ref_adequacy/heap_lang_ref_adequacy_fully_closed`; `theories/examples/termination/adequacy.v:heap_lang_ref_adequacy_closed`; `theories/examples/counterexamples.v:no_later_existential_commuting`. `source-identities.json` records the inspected files' hashes. Source remains authoritative; no upstream source mirror is included in this package.

## Revalidation

At the pinned source, check the full premises of the named adequacy declarations and the `LargeIndex` universe constraint. Build only in a separately authorized matching environment and run the source's `Print Assumptions` commands. Do not infer closure from the word “closed.” Reconcile theorem numbers by their statements when replacing the paper or source version.

Before applying a finite-Iris proof, inventory its later/existential commuting rules and establish replacements. Before making a Rust liveness claim, provide a Rust language/state interpretation and the actual liveness property; prove source correspondence and scheduler/environment premises appropriate to that property.

*Authored by an AI agent acting on joshlf's behalf.*
