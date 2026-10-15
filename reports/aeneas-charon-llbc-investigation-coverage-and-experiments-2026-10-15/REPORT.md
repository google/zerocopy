# Aeneas, Charon and LLBC: investigation coverage and experiment synthesis

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

The investigation groups the 36 topics and 144 questions in [issue #3886](https://github.com/google/zerocopy/issues/3886) into fourteen reports. The grouping follows semantic boundaries rather than one report per question: frontend capture, ownership interpretation, functional synthesis, target proof checking and concrete resource adequacy need different evidence. [coverage.json](coverage.json) records a concise answer and report locator for every question; [grouping.json](grouping.json) preserves the adjustable grouping.

The central result is an assurance decomposition. A proof of a generated function's specification, a proof of translation correctness, a proof that the selected Rust memory model is adequate, and proof/artifact identity are separate obligations. Existing Aeneas publications and implementations provide useful results at several of these boundaries. The examined evidence does not establish a whole-current-pipeline source-semantics theorem.

Five of the eleven experiment cases reuse actual executions already preserved in the reference corpus, at their original revisions. The others reconcile current source/history or propose discriminating fixtures. No new upstream build, extraction, Lean/Rocq replay, differential fuzzing or MiniRust execution was performed for this investigation. Research-report coverage is not completion of every proposed experiment or stronger proof goal.

## Applicability

The current source comparison concerns Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`, its declared Charon dependency `1aebab5f03a58067e5dc0ede2fec584117f54964`, and independent upstream Charon `9e95cf318e3a2964fcf5e03104cde5b718f98ea5`. The two Charon subjects must not be interchanged. No compatible combination of these heads was executed here.

The synthesis was acquired/reconciled on 2026-10-15 against the reference corpus at `fa65b241fd0cb2c791c841eace86d43d724359bc`. Each linked report supplies its own exact source, paper, toolchain, target and configuration identities. Legacy alpha24 experiments and June 2026 compatible-pair probes retain those identities; they do not establish current acceptance or unchanged behavior. The newer Lean comparison concerns the named release/master snapshots and distinguishes Aeneas's declared rc4 toolchain.

The issue is a research agenda: record findings, assumptions, open questions and reproducible follow-ups. An answer can be a supported boundary or an explicitly unresolved empirical quantity. Neither a completed report nor a checked checklist item asserts that an unsupported feature has become supported, a pending adequacy theorem has been proved, or a proposed experiment has run.

## Findings

### Candidate grouping and the reason for each boundary

Basis: **derived** synthesis of the linked primary-source reports.

| Group | Report | Why these questions share a report |
| --- | --- | --- |
| G01 / A01–A04 | [Published results and mechanized LLBC](../aeneas-published-results-and-mechanized-llbc-2026-10-15/REPORT.md) | Theorems can be compared only after identifying their syntax, assumptions and actual mechanization. |
| G02 / A06–A07 | [Charon extraction and normalization](../charon-extraction-normalization-9e95cf3/REPORT.md) | Effective compiler inputs and information-erasing passes jointly determine the semantic subject. |
| G03 / A08–A10 | [Production LLBC, CFG reconstruction and MiniRust](../charon-llbc-cfg-minirust-9e95cf3/REPORT.md) | Language distinctions, control-flow reconstruction and alternative exporters must be reconciled together. |
| G04 / A13,A14,A17 | [Ownership and continuations](../aeneas-symbolic-ownership-continuations-21345f80/REPORT.md) | Borrow ending changes the same resources and historical values later used for backward synthesis. |
| G05 / A15–A16 | [Joins, loops and recursion](../aeneas-joins-loops-fixed-points-21345f80/REPORT.md) | Generalization and post-fixed-point acceptance control loop coverage and synthesis. |
| G06 / A05,A18,A30 | [Pipeline, pure transformations and output identity](../aeneas-pipeline-pure-extraction-21345f80/REPORT.md) | Intermediate semantics, pass ordering and the actual elaborated target must form one traceable chain. |
| G07 / A19–A23 | [Types, traits, primitives and models](../aeneas-types-traits-primitives-and-models-2026-10-15/REPORT.md) | Generic/type interfaces and external models jointly define the mathematical operations available to generated code. |
| G08 / A11–A12 | [Decoding, binding and admission](../llbc-decoding-binding-admission-1aebab5f-9e95cf31/REPORT.md) | A decoded AST is not automatically closed, well-scoped, complete or in the supported semantic fragment. |
| G09 / A26,A27,A29 | [Lean WP, partiality and checking](../lean-wp-partiality-and-aeneas-integration-2026-10-15/REPORT.md) | Outcome semantics, VCG adequacy and proof-checking trust determine what target proofs mean. |
| G10 / A02,A24,A25,A35 | [Semantic domains and spatial composition](../rust-semantic-domains-spatial-composition-3886/REPORT.md) | Unsafe Rust, concurrency and assembly require concrete representation and authority beyond value equations. |
| G11 / A31–A32 | [History and regression oracles](../aeneas-charon-history-and-regression-oracles-2026-10-15/REPORT.md) | Historical failures reveal which independent oracles and invariant checks discriminate real errors. |
| G12 / A33 | [Scaling and maintenance](../aeneas-scaling-proof-engineering-and-maintenance-2026-10-15/REPORT.md) | Performance and reuse depend on stage/configuration identity and proof closure. |
| G13 / A28,A34 | [Certification and related techniques](../certifying-translations-related-techniques-3886/REPORT.md) | Verified algorithms, checked witnesses, hinted replay and specialization have different proof interfaces. |
| G14 / A36, crosswalk | This report | Reuse must retain original scope and expose what remains unperformed. |

These are candidate research units. A later concrete experiment may justify separating byte/resource adequacy from value-level synthesis, or combining a validator and its historical counterexamples. The crosswalk, rather than package count, preserves the questions when that happens.

### Reused execution answers narrow, valuable questions

Basis: **execution** retained by the original packages; **derived** reuse here. This investigation did not repeat those executions.

| Case and retained report | What was actually established | Important limit |
| --- | --- | --- |
| X01 / [pair-field update](../aeneas-pair-returned-update-alpha24/REPORT.md) | Actual emitted endpoints, an imported pair-field update/frame certificate, exhaustive native byte-update controls (16,777,216 updates). | The ordinary `choose` example returns bytes; it is not a returned-mutable-reference certificate. Import and exclusive authority remain assumptions. |
| X05 / [CFG/storage certificate](../charon-fork-storage-certificate-alpha24/REPORT.md) | Actual four-block ULLBC and structured endpoints related over modeled states/fuel ≥ 3; deliberate bad storage/move transformations rejected with counterexamples. | A call-free, loop-free legacy specimen; trusted import and modeled semantics, not certification of the current structurer. |
| X06 / [zerocopy validity specimen](../zerocopy-validity-real-pass-certificate-alpha24/REPORT.md) | Selected real bool-validity source through raw/final operations and actual emitted endpoints, covering all bytes under preserved local-state framing. | A wrapper and selected function, with imported scalar meanings; no physical byte-read or whole-crate theorem. |
| X07 / [safe API with unsafe body](../safe-unsafe-bool-domain-certificate-2026-10-14/REPORT.md) | 256 native inputs, a checked finite-prefix model and counterexamples for an overbroad guard and narrowed proof domain. | Manual import; no aliasing, allocation, concurrency, destructor or universal memory-safety argument. |
| X09 / [compatible-pair probes](../rust-llbc-lean-golden-and-aeneas-revision-probes-2026-09-28/REPORT.md) | Preserved Rust/LLBC/Lean specimens and cross-pair rejection; compatible pairs can emit equal baseline Lean bytes from different LLBC. | Older June releases, small input set and co-varying components; no current support or Aeneas-only causal attribution. |

The original packages preserve commands, exact revisions, artifacts and results. Their certificates justify the mathematical relations stated there. Their import/state-model assumptions remain visible rather than becoming stronger merely because the packages are reused.

### Focused unperformed probes and independent expectations

Basis: **derived** experimental design from source/history. [candidate-fixtures.rs](candidate-fixtures.rs) preserves small candidate inputs. They were not compiled, extracted or verified. Their inclusion supplies reproducible questions, not acceptance evidence.

| Probe | Independent expected observation | Distinguishing mutation or comparison |
| --- | --- | --- |
| `pick_mut` / `update_chosen` | Mutation through the returned borrow changes exactly the selected original byte. Test both selections, identical input values and distinct replacement values. | Swap backward owners or always update the second byte; a byte-only `choose` proof must not satisfy this test. |
| `enum_borrow` / `nested_update` | Empty has no update; Present preserves its first field; nested reborrows restore ownership and change only the intended component. | Drop a correlated projection or restore a stale historical value; compare direct and helper-extracted versions. |
| `loop_borrow` | The first field is unchanged and the second increases by the initial count modulo 256. | Lose the carried loan, alter the invariant or route a continue to the wrong state; distinguish rejection from a wrong accepted translation. |
| `borrowed_instantiation` | Instantiating generic identity with a mutable reference updates the original referent exactly once. | Replace the borrowed instance by a copied value or lose its final-update relationship. |
| `fnmut_unit` | Closure state is updated twice; the final byte is start+2 modulo 256. | Drop the updated closure state when the call result is unit; compare direct calls and a helper taking FnMut. |
| `drop_trace` | On ordinary return, explicit drop logs 2 then scope exit logs moved marker 1. Under unwind, the later-declared moved marker drops before marker 2; abort has a distinct process-level outcome. | Erase/move/reorder cleanup or identify unwind with abort; use Rust's configured panic runtime as one oracle and a separately stated drop trace as another. |

For each future run, freeze the source and full compatible toolchain pair, actual MIR/body choice, normalization flags, target widths, panic/overflow mode and external models. Capture request/output/error sets before evaluating generated proofs. Use at least one oracle that does not share the transform being tested. The current hax Lean route cannot supply that independence merely by using another command, because it delegates to Charon/Aeneas.

Returned references, nested-loop resources and destructor traces are not asserted to be supported by the current toolchain. An informative outcome may be an explicit supported-fragment rejection. An internal exception, partial extraction, ill-typed target and semantic disagreement need separate classifications. A correct rejection does not supply a positive source-correspondence theorem.

X08's historical model cases add another independent expectation: test distinguishable Ord ties, insertion versus replacement at middle/end boundaries, and signed versus unsigned byte interfaces against the operation's actual Rust contract. Pure target proofs cannot detect a consistently incorrect model unless the intended source relation is also checked.

### What remains to establish stronger assurance

Basis: **derived**, using the gaps documented in G01–G13. This priority order follows dependency and discriminating value, not a claim of implementation cost.

1. **Make the subject and admission boundary explicit.** Bind requested declarations, effective compiler bodies, configuration, dependencies and models; preserve partial-output metadata; state a pre-erasure supported-fragment predicate. A complete target theorem cannot repair a missing source declaration.
2. **Establish a checked semantic baseline.** Build the chosen formal development in a controlled environment, audit the complete assumptions of selected theorems, and relate its grammar/outcomes to the exact imported fragment. Source-level Qed and admission counts are not that audit.
3. **Certify one actual transition chain.** Extend the retained concrete CFG/storage and primitive examples with independently checked witnesses tied to actual input/output bytes. Then cover returned-borrow restoration and feasible-path completeness. Search and heuristic choices can remain untrusted only when every accepted choice satisfies the relation.
4. **Check joins and loops at acceptance.** State entry inclusion, one-step/body preservation and all-exit obligations. A bounded search may fail; it must not accept an uncovered branch or an unproved post-fixed point. Termination and stuttering need separate treatment.
5. **Justify effect-sensitive functionalization.** Define the pure IR denotation and prove or validate actual transformations, keeping fail/divergence and sequencing. Connect model calls and the elaborated target's full closure, including helpers, dictionaries and imports.
6. **Prove and measure the Lean interface in a compatible configuration.** Check exact DWP/DWLP-to-WP adapters, use an explicit axiom policy, and measure producer/proof/elaboration/checking/storage separately. Native-backed proof steps and source/compiler/runtime assumptions must remain visible.
7. **Extend through concrete resources.** Supply representation, initializedness, provenance, validity, frame and lifetime relations. Unsafe APIs, concurrency/async cancellation and Rust/assembly ABI linking add semantic obligations rather than being ordinary value-model extensions.

These steps are follow-up experiments and proof projects. The earlier execution agenda's unperformed items retain their own tracking and are not completed by this research synthesis. In particular there is no new universal Charon normalization proof, current-loop certificate checker, cross-assistant semantics correspondence, full library-model refinement or Rust/assembly ownership theorem here.

### Coverage and limits are separate data

Each of the 144 entries in [coverage.json](coverage.json) retains the original question, a research answer and report locator. The disposition `research-answer-with-explicit-boundaries` means exactly that. It must not be interpreted as `proved`, `executed`, `supported`, or a theorem that no other literature exists.

For examples: the theorem inventory identifies published statements and current source boundaries; it does not execute their proof closures. The scaling report records published/retained measurements and missing current empirical quantities; it does not invent current timings. The history report uses a recorded bounded sample rather than claim a complete issue census. Literature discovery cannot prove that no unpublished or unlocated result exists.

## Boundaries

Not performed: new toolchain builds, extraction/proof replay, current-version compatibility validation, cross-model execution, fuzzing, current-stage benchmarks, or the stronger proof projects above. Proposed fixtures may need refinement after real compiler/extractor feedback; such feedback should preserve whether the failure is in the candidate Rust input, the toolchain, support restrictions or the model relation.

Unknown quantities include current proof/certificate sizes and costs, exact compiled axiom closures, and adequacy/correspondence for combined full production semantics. They are stated as unknown rather than zero, unsupported or disproved.

The findings and coverage concern the identified public sources. They do not provide a decision that one particular assurance architecture is best. Current source restrictions are not claimed to be fundamental impossibility results.

## Evidence

The fourteen linked reports preserve the primary paper/source coordinates and their relevant support artifacts. [experiment-inventory.json](experiment-inventory.json) records eleven cases with their status, result and scope. Five cases are explicitly `reused-executed`; none is a fresh execution in this investigation. The other statuses distinguish source/history reconciliation and proposed-not-executed work.

[coverage.json](coverage.json) reconciles the 36-topic/144-question issue agenda against these packages; [grouping.json](grouping.json) records the provisional many-to-many grouping. Exact legacy configuration and command/output evidence must be read in the original retained experiment package before reuse. No local source cache or unpublished filesystem artifact is required to interpret the published synthesis.

## Revalidation

Start from a concrete desired theorem and list the source, frontend, ownership, target and resource boundaries it traverses. Rebind those exact subjects before reusing a finding. For source changes, diff the controlling symbol/pass rather than rerun broad literature discovery. For a new experiment, record its independent expectation before inspecting the generated model and retain negative controls.

When reports are regrouped, preserve all 144 question identities and repair the crosswalk links. When a proposed experiment is run, replace its status only with exact environment, input/output identity, observed outcome and limitations; historical results retain their original subjects. A newly checked theorem should record its statement and complete assumption closure, not just the proof tool's exit status.
