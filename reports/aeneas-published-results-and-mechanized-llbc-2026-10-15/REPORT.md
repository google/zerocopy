# Aeneas published results and the current mechanized LLBC boundary

## Summary

Aeneas has a published ownership-oriented functional translation, a later mathematical account connecting symbolic borrow checking and ownership semantics to pointer execution, and substantial downstream Lean verification experience. These results concern different objects. None should be silently promoted to a mechanically established correspondence for the complete current rustc → Charon → Aeneas → Lean implementation.

The current Rocq development examined here is narrower than production LLBC. Its common grammar contains mutable borrowing, tuple construction, arithmetic, branches and loops, but no function-call, return, trait, destructor or pure-target syntax. Direct source inspection also finds nine explicit Admitted endings and eleven Abort endings in the acquired src files. These are source facts, not an executed assumption audit: an aborted proof does not introduce a theorem, while an admitted theorem can become an assumption of later results. The exact dependency closure of particular compiled theorems remains unmeasured.

The useful reusable result is a correspondence map: distinguish the source artifact, frontend transformations, ownership interpretation, symbolic analysis, functional synthesis, backend definition and external models. A specification-transfer claim needs justified relations across every boundary it traverses.

## Applicability

Evidence acquired on 2026-10-15:

- Aeneas source/documentation: AeneasVerif/aeneas at 21345f80fa212c596f6437378d7d57984fa2ea77.
- Rocq source: AeneasVerif/mechanized-llbc at 2762a26a3c0792017fa7a731aab1683d9a4cf23a.
- The publication editions and URLs listed below.
- Existing corpus reports are reused only for the subjects they identify; their older Aeneas/mechanization pins are not evidence for the current pins.

This report covers checklist A01–A04 in issue #3886. The bibliography search is bounded by the Aeneas README, the principal author's projects/publications pages, the papers' links, and targeted title searches. It identifies the relevant public foundational and experience publications found through those routes, not every unpublished collaboration, talk or future paper. Full industrial evaluation is treated separately.

No Rocq compilation, kernel replay, Print Assumptions, Rust execution or Aeneas extraction was performed for this report. Acquiring and checking source blob identities is source-acquisition validation, not proof execution.

## Findings

### Publication inventory and distinct result domains

| Publication | Established subject and role | Boundary to retain |
| --- | --- | --- |
| Ho and Protzenko, [Aeneas: Rust Verification by Functional Translation](https://arxiv.org/abs/2206.07185v2), ICFP 2022, DOI 10.1145/3547647, arXiv 2206.07185v2 | Gives value-based ownership semantics for LLBC and a functional translation using symbolic abstractions and backward functions; demonstrates verification of a resizing hash table. | The paper explicitly places semantic/translation soundness against memory-based Rust models in future work. Formal definitions and verified translated examples do not constitute verification of the production translator. |
| Ho, Fromherz and Protzenko, [Sound Borrow-Checking for Rust via Symbolic Semantics](https://arxiv.org/abs/2404.02680v2), ICFP 2024, DOI 10.1145/3674640, arXiv 2404.02680v2 | Relates ownership and pointer interpretations, establishes a symbolic borrow-checking argument and sound environment joining, and develops loop support. Theorem 4.1 assumes all functions in the environment borrow-check; Theorem 4.2 supplies the reverse correspondence to pointer executions under related initial states. | Theorems concern the paper's languages and hypotheses. They are not a rustc/Charon extraction theorem, implementation-refinement theorem for all current algorithms, or universal theorem for unsafe Rust. |
| Ho et al., [Charon: An Analysis Framework for Rust](https://arxiv.org/abs/2410.18042v2), arXiv 2410.18042; CAV 2025 tool paper | Explains the frontend's decorated MIR-like representations, compiler integration and usefulness to multiple clients. | A stable analysis AST is an engineering interface, not by itself a semantic-preservation certificate. |
| Ho, [Formal Verification of Rust Programs by Functional Translation](https://www.sonho.fr/papers/thesis-manuscript.pdf), PhD thesis, 2024 | Chapters 9–12 develop the ownership/symbolic account; Chapter 13 presents translation; Chapter 14 discusses implementation and backends. The introduction and evaluation explicitly describe the translation/implementation as trusted. | The updated synthesis rules are useful formal definitions, not an implementation-refinement theorem for later constructs. |
| Ho et al., [Scaling Verification of Cryptographic Software with Aeneas, Rust, and Lean](https://arxiv.org/abs/2609.15648v1), arXiv 2609.15648v1, September 2026 draft | Reports production-oriented Rust/Lean verification, including explicit trusted models and platform intrinsics. | Application correctness results retain the paper's trust assumptions. Extent of application proofs is not evidence that the extraction implementation itself has been verified. |
| Klaus, Tolmach and Conejero, [A Rust-to-Lean Verification Pipeline with AI Provers: An Experience Report](https://arxiv.org/abs/2605.30106v1), arXiv 2605.30106v1 | Documents a downstream pipeline using Aeneas/Charon or hax and AI-assisted proof development. | Experience with checked model proofs and toolchain limitations is not foundational source-semantics preservation. |

The hybrid-language methodology supplies a reusable proof pattern: local state relations can pass through representations outside either endpoint language. Preserve its behavior quantifiers, panic/divergence cases and function-environment hypotheses when comparing another semantic claim.

Basis: documentation (publication claims and theorem statements), source (README and formal definitions).

### Individual publication results and their exact premises

The [publication-result appendix](publication-results.md) inventories all 37 numbered semantic results (10 theorems and 27 lemmas) and three definitions in the 2024 long paper, plus all 38 semantic results (11 theorems and 27 lemmas) in the specified thesis soundness sections. [publication-results-inventory.json](publication-results-inventory.json) records each result's source locator, quantified domain, premises, conclusion, exclusions and mechanization qualification. [publication-application-inventory.json](publication-application-inventory.json) separately records named/displayed application contracts and unfinished goals from the other publications and cited source.

The scope is publication-level results, not every imported lemma or thousands of application-artifact theorems. Printed formula ambiguities remain explicit. In particular, thesis Theorem 5's display omits an initial related-state premise used by the surrounding composition argument; the inventory distinguishes the literal display from the intended restricted composition. This is not a claim that the intended mathematical proof is false. Source declarations, mathematical claims and compiled assumption audits remain separate.

### Current formal syntax is an intentionally smaller object

The common src/lang.v defines:

- types TInt, TRef and TTuple with an auxiliary type_list;
- constants as natural-number integers and booleans;
- operands Const, Move, Copy and Tuple;
- binary operations BAdd and BLe;
- rvalues Use, BinaryOp and BorrowMut;
- statements Nop, Assign, Seq, SwitchBool, Loop, Panic, Break and Continue;
- flow tokens for panic, ordinary completion, break and continue.

The mutable reference constructor here does not encode the full production distinction among shared/mutable references, complete lifetime binders and trait environments. There is no call or return statement in this common statement grammar. There is also no frontend decoder or functional-output AST in that grammar. Those absences are established for the inspected definition, not for every experimental file or another revision.

PL.v contains a separate pointer-language/HLPL development with memory representation machinery imported from Chamois. It should not be assumed to share every constructor or invariant with src/lang.v merely because both reside in the same repository. Its block mapping and byte/value correspondence add obligations distinct from symbolic LLBC evaluation.

The abstractness is useful for proving structural ownership facts. It prevents directly instantiating the development with arbitrary current serialized LLBC without an elaboration, restriction or representation theorem. In particular, natural-number arithmetic in the shared grammar does not establish Rust-width overflow behavior.

Basis: source; derived consequence from the compared syntactic domains.

### The source contains completed proof scripts, admissions and abandoned attempts

The acquired scope is every src/*.v and src/**/*.v blob in the complete pinned Git tree, plus build/project metadata. The acquisition inventory records each upstream Git blob ID; all 28 initially acquired files matched those identities byte-for-byte. The separately acquired _RocqProject lists the semantic, simulation and execution files, including PL.v.

| File | Explicit source markers examined | Interpretation |
| --- | --- | --- |
| src/simulations/Simulation_HLPL_plus.v | Seven Admitted endings, including operand_preserves_HLPL_plus_rel and operand_preserves_well_formedness | A Qed-ending theorem using these declarations may still rely on admitted assumptions. |
| src/PL.v | Two Admitted endings: offset_less_modulus and WellTypedState_equiv | These are open proof obligations represented as accepted declarations in source. |
| src/PL.v | Eleven Abort endings; four inner admit tactic occurrences in aborted attempts | An aborted lemma is absent as a completed declaration. Counting an inner admit as an additional admitted theorem would be wrong. |
| src/simulations/Simulation_LLBC_sharp_LLBC_plus.v | simulation_LLBC_sharp_LLBC_plus ends in Qed | This is a completed source proof script for a specific forward_simulation statement, not a checked dependency-closure claim from this investigation. |
| src/simulations/Simulation_LLBC_plus.v | stmt_preserves_LLBC_plus_rel ends in Qed | It relates the symbolic/hybrid semantics at its stated step index and relations. |
| src/simulations/Simulation_HLPL_plus.v | stmt_preserves_HLPL_plus_rel ends in Qed and invokes operand lemmas | Its source dependencies show why checking only its final keyword would overstate the evidence. |

The final simulation_LLBC_sharp_LLBC_plus proof is parameterized by a natural step index and statement, and relates LLBC_sharp.eval_stmt to LLBC_plus.eval_stmt using equality and leq_branching. That is a useful explicit proof boundary. It does not mention production OCaml state representations or an elaborated Lean output term.

Several Abort endings occur in test/example sections and may be intentional; their count is not a count of missing required theorems. Text search is not Print Assumptions. Section parameters, imported axioms, module interfaces and theorem dependencies also matter. The source includes an Axiom blockof_inj in PL.v and imports dependency material; the nine Admitted count must not be reported as the complete logical TCB or as a demonstrated inconsistency.

Basis: source, plus derived dependency observation.

### A reusable specification-transfer diagram

A later claim about an actual Rust artifact can be decomposed as follows:

| Boundary | Relation that needs a definition or evidence |
| --- | --- |
| Build subject → compiler intermediate artifact | Source/dependency/configuration identity and an explicit compiler assumption or theorem. |
| Imported artifact → normalized ULLBC/LLBC | Preservation of evaluation, observable errors and undefined behavior across frontend passes. |
| Concrete memory → ownership LLBC | Value/resource representation, validity, aliasing and permitted observations. |
| Ownership states → symbolic states | Concretization, path coverage, abstraction soundness and sufficient invariants. |
| Symbolic execution → pure program | Backward-continuation adequacy and preservation through pure transformations. |
| Pure program → elaborated Lean definition | Identity of the actual term, typing, partiality and backend/model interpretation. |
| Library/external operations → model calls | Separately justified contracts and correct selected implementations. |
| Model theorem → source specification | A transfer theorem with the correct behavior quantifiers and all premises exposed. |

This is a derived decomposition, not a claim that all arrows are already proved. Each arrow can be supported by a reusable theorem, per-program witness, independently checked relation, or an explicit assumption. These alternatives change proof organization; they do not remove the semantic obligation.

For partial correctness, it is insufficient to show that some favorable model run matches a source run when other admitted source behaviors can fail. For total correctness, a source may not gain termination merely because the target is a total function in Lean's logic. For contextual safety, the theorem must state the surrounding code's contract and resources rather than quantify only over closed executions.

### How to select and compare an external semantics

“External” has several independent dimensions: independently maintained definitions, a separate implementation, a different proof assistant, and a different abstraction level. None alone guarantees an adequate model of the source fragment.

A comparison must record at least:

1. the accepted program syntax and the build artifact to which it applies;
2. state representation, byte/value mapping and target parameters;
3. validity, provenance, borrowing and destruction;
4. observable behavior, nondeterminism, panic and divergence;
5. the contract for external calls and open program contexts;
6. existing mechanized adequacy and the assumptions needed to instantiate it.

MiniRust supplies a candidate memory-detail endpoint; RustBelt/RefinedRust-style developments supply semantic resource interpretations and safe/unsafe composition techniques. They answer different questions. A proof in another assistant also requires a justified cross-formalization relation; two definitions with similar names are not automatically interchangeable.

For current candidate details, reuse the corpus's external-semantics and safe/unsafe bridge reports together with the newer Charon/MiniRust investigation. Do not use the current Rocq common grammar as a drop-in semantic definition for full Rust.

## Boundaries

- Not examined: a complete dependency-level proof audit, compiled Rocq objects, historical artifact reproduction, private/unpublished results, or every paper citing Aeneas.
- Unknown: the exact compiled assumptions of each named theorem and whether the complete pinned project currently builds under its declared dependencies.
- Known not to apply: interpreting the inspected common grammar as full production LLBC, or interpreting a Qed ending as an axiom-free compiled theorem.
- No finding here says the published 2024 mathematical theorem is false. Repository admissions and narrower syntax characterize this examined implementation of formal definitions.
- No new end-to-end source soundness proof was constructed. Stronger proof goals require their own checked artifacts.
- The existing report aeneas-formal-results-literature-2026-09-27 concerns older exact pins; this package adds current evidence without silently changing that older subject.

## Evidence

Primary publications are linked in the inventory. Discovery was cross-checked against [Son Ho's publications](https://www.sonho.fr/2-papers.html), [projects](https://www.sonho.fr/1-projects.html), and the pinned [Aeneas README](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/README.md). The author's list identifies Charon as the CAV 2025 tool paper although its arXiv submission dates to 2024.

Immutable Rocq source anchors, all at 2762a26a3c0792017fa7a731aab1683d9a4cf23a:

- [lang.v](https://github.com/AeneasVerif/mechanized-llbc/blob/2762a26a3c0792017fa7a731aab1683d9a4cf23a/src/lang.v), type/operand/rvalue/statement/flow_token.
- [SimulationUtils.v](https://github.com/AeneasVerif/mechanized-llbc/blob/2762a26a3c0792017fa7a731aab1683d9a4cf23a/src/simulations/SimulationUtils.v), forward_simulation.
- [Simulation_HLPL_plus.v](https://github.com/AeneasVerif/mechanized-llbc/blob/2762a26a3c0792017fa7a731aab1683d9a4cf23a/src/simulations/Simulation_HLPL_plus.v), the seven named admissions and stmt_preserves_HLPL_plus_rel.
- [Simulation_LLBC_plus.v](https://github.com/AeneasVerif/mechanized-llbc/blob/2762a26a3c0792017fa7a731aab1683d9a4cf23a/src/simulations/Simulation_LLBC_plus.v), stmt_preserves_LLBC_plus_rel.
- [Simulation_LLBC_sharp_LLBC_plus.v](https://github.com/AeneasVerif/mechanized-llbc/blob/2762a26a3c0792017fa7a731aab1683d9a4cf23a/src/simulations/Simulation_LLBC_sharp_LLBC_plus.v), simulation_LLBC_sharp_LLBC_plus.
- [PL.v](https://github.com/AeneasVerif/mechanized-llbc/blob/2762a26a3c0792017fa7a731aab1683d9a4cf23a/src/PL.v), offset_less_modulus, WellTypedState_equiv, Assign_Preserves_PL_HLPL_Rel and aborted attempts.
- [_RocqProject](https://github.com/AeneasVerif/mechanized-llbc/blob/2762a26a3c0792017fa7a731aab1683d9a4cf23a/_RocqProject).

The support inventory contains identities and narrow audit observations, not a whole upstream source mirror. The inspected grammar and proof markers were read directly; the source inventory's byte verification only confirms acquisition identity.

## Revalidation

1. Resolve immutable upstream revisions and compare the common grammar and project manifest.
2. Inspect the named proof declarations and their endings; distinguish admission from abort.
3. On a separately prepared execution surface, compile the exact project and issue Print Assumptions for the named simulation results and all proposed transfer theorems. Record compiler/dependency identities and full outputs.
4. Compare every production construct actually admitted by the frontend against the formal syntax and hypotheses.
5. Recheck the author's publication list, README and newer papers for additional theorem or implementation-correspondence results.
6. Update the correspondence map only when a boundary has new direct evidence.

*Authored by an AI agent acting on joshlf's behalf.*
