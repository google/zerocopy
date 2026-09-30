# Dafny/Boogie and Viper: verification conditions as an architectural boundary

## Summary

Dafny/Boogie and Viper both separate source-language reasoning from backend proof search, but they expose different useful units at different layers. Boogie is deliberately an intermediate verification language: frontends translate source semantics into Boogie, and Boogie generates verification conditions for an SMT solver. Viper makes the same architectural move with Silver, then supports two materially different backends: Carbon generates verification conditions, while Silicon symbolically executes Silver programs. Those designs make the intermediate language a durable semantic boundary without making a backend verification condition the universal public interface.

Dafny adds another layer above raw verification conditions. Its user-facing verification unit is an assertion batch: a set of source-level assertions plus the assumptions needed to prove them. Dafny can split a method into different batches, retry after a counterexample, record per-batch resource use, and map failures back to source assertions. Current Dafny source also carries origin wrappers, generated implementation identifiers, source ranges, and optional checksums into Boogie. This metadata is useful for provenance and reuse, but it does not make a raw Boogie procedure, verification condition, or SMT query a stable semantic identity across translator changes, option changes, or batch repartitioning.

Viper sharpens the distinction. Silver is shared by both a verification-condition backend and a symbolic-execution backend. A public obligation interface defined as "the generated VC" would therefore privilege one backend and expose encoding choices that the architecture otherwise keeps replaceable. Silver's common verification-result layer instead reports errors with source positions and short identifiers and can transform errors as programs pass through frontend or intermediate transformations. ViperServer then manages whole verification requests, caching, IDE integration, and backend selection outside either backend.

The architectural lesson for Anneal is conditional. If Anneal only needs coarse whole-stage execution, source/model snapshots plus stage generations are enough; a new obligation API would add another consistency surface without buying correctness. If Anneal needs to schedule, cache, cancel, prioritize, or report proof work below a whole translation/prover stage, it should introduce a first-class **semantic obligation descriptor**, not expose raw Lean goals, generated formulas, or solver queries as stable identifiers. The descriptor should identify the Rust/model promise that must be discharged, carry exact source/model/environment/tool generations and provenance, and allow one semantic obligation to produce multiple backend attempts or child obligations. Backend payloads may be recorded for diagnosis, but their identities should remain subordinate to the semantic obligation unless a backend explicitly promises stronger stability.

Basis: exact current project source/documentation, primary architecture papers, current Dafny verification documentation, and derived Anneal analysis. No Dafny, Boogie, Viper, or solver process was executed for this report.

## Applicability

This report addresses #3732 J022: the separation among source analysis, obligation generation, solver scheduling, IDE feedback, and counterexample presentation in Dafny/Boogie and Viper, including the costs of hiding intermediate languages and unstable obligation identity.

The current source observations bind to these exact revisions:

- Dafny `5f717bf447b19d38cad1b69b1bf9a9f102feccfb`, especially `Source/DafnyCore/Verifier/BoogieGenerator.cs`;
- Boogie `fcecf73a49d11ad3ab16729abd03169e5ecfd938`;
- Viper Silver `da1c8993b66feb39976e3609e2580a4661137a0f`;
- Silicon `6ceff8be6ba55d858b7d018fdfeb866b7e8aa0ed`;
- Carbon `6421cfda16d35f37cb9a7966f04fcd2d96abdda2`; and
- ViperServer `4cc5bbbe18d4a83e4b398da3904ba9696256611b`.

Historical intent and architecture come from Barnett et al., *Boogie: A Modular Reusable Verifier for Object-Oriented Programs* (FMCO 2005, DOI `10.1007/11804192_17`), Leino, *Dafny: An Automatic Program Verifier for Functional Correctness* (LPAR 2010, DOI `10.1007/978-3-642-17511-4_20`), and Müller, Schwerhoff, and Summers, *Viper: A Verification Infrastructure for Permission-Based Reasoning* (VMCAI 2016, DOI `10.1007/978-3-662-49122-5_2`). Current Dafny documentation supplies assertion-batch behavior and verification-optimization guidance.

The Anneal judgment is bounded by `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. The design contract requires precise verification identity and scope, Rust-oriented presentation of unsatisfied obligations, explicit trust, complete accounting for semantics relevant to the reported promise, and minimally sufficient mechanisms. It deliberately does not decide the atomic unit of verification or whether obligations are represented as arguments, sidecar theorems, weakest preconditions, or another proof encoding. This report therefore proposes a decision rule and interface shape, not adopted Anneal policy.

The current `reference` corpus already contains reports on batch/live architecture contracts, source/input identity, LSP proof-assistant state, and pipeline invalidation. J022 is narrower: it asks where proof obligations themselves should sit in the architecture and how their identity should relate to generated intermediate forms and backend attempts.

## Findings

### Intermediate languages separate semantic translation from proof search

Boogie's current README describes Boogie as a modeling language intended as a layer on which verifiers for other languages are built. The Boogie tool accepts that language, generates verification conditions, and sends them to an SMT solver. The 2005 architecture paper presents the same separation historically: a program verifier combines source-language semantics, invariant/property machinery, verification-condition generation, decision procedures, and user-facing diagnostics, and Boogie factors reusable verification machinery out of source-specific frontends.

Dafny uses that split directly. The source language and verifier present specifications and errors in Dafny terms, while the translation encodes those semantics into Boogie. The 2010 Dafny paper emphasizes automated SMT-backed verification with errors expressed against the program rather than requiring ordinary users to manipulate solver formulas.

Viper deliberately generalizes the intermediate-language boundary for permission-based reasoning. The 2016 paper argues that an intermediate language should express the reasoning concepts shared by many frontends so tool builders can reuse verification infrastructure. Current project structure preserves that architecture: Silver defines the Viper intermediate verification language; Silicon verifies Silver through symbolic execution; Carbon verifies Silver through verification-condition generation and Boogie; and ViperServer sits outside both backends to manage requests, IDE use, startup cost, caching, and programmatic access.

This history supports a specific distinction. An intermediate verification language can be a stable architectural boundary even when a raw backend verification condition cannot. Silver is meaningful to both Carbon and Silicon. A Carbon-generated formula is not the natural unit for Silicon. Likewise, Boogie is more reusable than the particular SMT query that one Boogie revision generates for one option set.

Basis: primary publications + exact current project documentation/source.

### Dafny's useful interactive unit sits above the raw VC

Current Dafny verification documentation calls the assertion batch the fundamental unit of verification. A batch contains one or more assertions and turns the remaining relevant assertions into assumptions. By default, Dafny groups the assertions for a definition, but it can split them into smaller batches. An isolated-assertion mode can make each assertion its own batch.

The batch is both a scheduling unit and a presentation unit. A batch can succeed, fail, or time out independently. Dafny reports duration and solver resource counts per batch. When a verifier produces a counterexample, Dafny uses it to identify a failing assertion and path; it may then ask again with already failed assertions turned into assumptions to expose additional failures. This means a single source definition and even a single semantic set of assertions can map to different backend query structures depending on splitting policy and prior outcomes.

Dafny also exposes verification instability as a first-class practical concern. Its documented random-seed controls make meaning-preserving changes such as declaration reordering and variable renaming, plus solver randomization, so users can measure how much verification outcome or resource cost depends on incidental encoding/search choices. The documentation recommends splitting or isolating assertions to localize difficult work and improve diagnosis. These facilities are strong evidence against using raw SMT query text, query order, or resource behavior as a durable semantic obligation identity.

The current translator source carries richer provenance into Boogie. `CanVerifyOrigin` records which Dafny `ICanVerify` node originated a Boogie implementation. `TranslatorFlags` controls source-range reporting and optional checksums. Generated implementations can receive an `id` attribute based on an input prefix and generated implementation name; checksum attributes derive from printed Dafny declarations or expressions, with `stable` markers used where no more specific checksum was inserted. These mechanisms support tracking, snapshot verification, and source association. They remain translation artifacts: their values can change when file naming, translation naming, printed syntax, splitting, or implementation strategy changes.

The resulting layer model is therefore:

| Layer | Example in Dafny/Boogie | Identity property |
| --- | --- | --- |
| Source promise | a Dafny assertion, precondition, postcondition, invariant, or implicit safety check | closest to what the user intends to establish |
| Verification unit | an assertion batch / generated Boogie implementation | useful for scheduling and resource accounting; partitioning is policy-dependent |
| Backend condition | one or more Boogie VCs | depends on translator, VC generation, options, and splitting |
| Solver attempt | an SMT query under a seed/options/resource budget | deliberately ephemeral; repeated attempts may differ while proving the same source promise |
| Diagnostic projection | Dafny source error, path, hover/resource information | must preserve provenance back to the source promise |

A system that collapses these layers gets one of two bad outcomes: either incidental backend changes invalidate user-visible identities, or a supposedly stable identifier hides a changed theorem or changed translation.

Basis: current Dafny documentation + exact Dafny source + derived identity analysis.

### Viper shows why raw verification conditions are too backend-specific

Viper's architecture supplies a useful counterexample to a "VC = obligation" design. Silicon is a symbolic-execution verifier for the Viper intermediate language. Carbon is a verification-condition-generation verifier for the same language. ViperServer can dispatch verification requests to either. The shared semantic input is Silver; the shared result abstraction is verification success or a sequence of Viper errors. Raw verification conditions are specific to Carbon's backend strategy.

Silver's current `VerificationResult.scala` makes the common result boundary explicit. `VerificationResult` is either success or failure; failures contain `AbstractError` values. An abstract error has a source `Position`, a short unique `fullId`, a readable message, a cached marker, and an optional member scope. Errors can be transformed through `transformedError()`. The file even records a design note that finer-grained timeouts could be represented per member or proof obligation. This is not a complete obligation protocol, but it shows the direction of the shared abstraction: source/provenance and semantic error classification survive across verifier strategies, while backend search machinery remains replaceable.

ViperServer reinforces the outer boundary. Its stated purposes include IDE integration, frontend integration, avoiding repeated JVM startup, caching encodings, and programmatic verification requests. These are orchestration concerns around a verification request; they do not require exposing Carbon's formulas or Silicon's symbolic states as the common external API.

The same split appears in debugging. Viper's Lizard prototype consumes verification errors and SMT models to present counterexamples next to failing Viper assertions, postconditions, or invariants and works with both Carbon and Silicon. Counterexample presentation therefore needs a provenance path from backend evidence to an intermediate/source obligation, not a promise that both backends expose the same internal proof-search object.

For Anneal, this argues against defining its first-class proof-work unit as a generated Lean goal string, SMT formula, tactic state, or another backend-specific payload. Such payloads are valuable support artifacts and may become stable interfaces if an upstream tool explicitly commits to them, but they should not acquire durable semantic identity merely because an orchestrator can serialize them.

Basis: Viper primary paper + exact current Silver/Silicon/Carbon/ViperServer source/documentation + derived comparison.

### Hiding the intermediate language buys usability but moves debugging pressure elsewhere

The Boogie and Viper designs intentionally let most source-language users avoid the intermediate language. That makes ordinary diagnostics source-oriented and lets frontend authors change encodings without teaching every user the backend language. It also gives backend implementers a reusable target shared by many frontends.

The cost appears when failures concern the translation or proof search rather than the source property itself. Performance regressions, missing provenance, unsupported source semantics, incorrectly encoded assumptions, solver instability, and backend bugs often require inspecting generated intermediate programs, verification conditions, traces, or solver models. Dafny therefore retains escape hatches such as printing Boogie and exposing batch/resource statistics. Viper frontends and debugging tools likewise preserve Viper source, error positions, verifier identities, and optional counterexample information.

Anneal has the same tension, amplified by source/model correspondence. Ordinary users should see Rust-oriented obligations, as the design contract requires. Specialists and agents still need access to generated LLBC, Lean, provenance maps, theorem statements, tactic/solver traces, and backend payloads when the failure lies below the Rust presentation layer. "Hide from the ordinary interface" should therefore mean "not required for ordinary use," not "discarded" or "unaddressable."

A useful obligation layer should carry links to these support artifacts without making any one representation the semantic identity of the obligation.

Basis: documented source/IDE behavior + Anneal design constraints + derived analysis.

### Stable semantic identity and attempt identity should be different fields

Dafny's batching and retry behavior shows why one semantic obligation can create multiple verification attempts. Viper's multiple backends shows why one semantic obligation may not even have one common backend formula. Anneal should reflect this explicitly if it introduces sub-stage proof work.

A semantic obligation descriptor should answer: **what promise about what exact program/model generation remains to be established?** An attempt descriptor should answer: **which backend computation tried to establish it, using which derived payload and controls?**

A minimal semantic descriptor would need at least:

- the exact Rust compilation/source generation and relevant model generation;
- the property or promise class, including whether it contributes to always-on UB freedom or a user-selected property;
- a semantic owner such as item/contract/operation plus source provenance sufficient to explain the obligation;
- the toolchain/translation semantics that determine what the obligation means;
- dependencies or parent/child relationships when satisfying one obligation relies on others; and
- a completeness relation telling Anneal which obligations must succeed before a larger verification result can be accepted.

An attempt can then add backend name/revision, generated artifact digest, solver or prover options, split strategy, timeout/resource budget, random seed, process/worker identity, start/end status, and diagnostic/counterexample artifacts.

The semantic identifier should not claim more stability than its inputs permit. A source span alone is insufficient because edits move spans and can change meaning. A generated function name alone is insufficient because translation naming can change. A content hash alone identifies bytes but not their role in the promised theorem. A robust key is therefore normally a structured identity over the exact verification generation plus semantic owner/kind. If Anneal wants identity to survive benign edits, it needs an explicit matching/reconciliation rule and must treat that match as a separate, fallible relation rather than pretending the raw backend identifier stayed unchanged.

This split also improves cache semantics. Reusing a backend result is justified only if Anneal can show that the semantic obligation and every meaning-bearing input required by the backend remain equivalent under the cache's contract. A matching string identifier is not enough.

Basis: Dafny batching/instability behavior + Viper backend diversity + Anneal precise-success contract + derived design.

### A first-class obligation interface is useful only when Anneal owns obligation-level policy

There are three plausible architectures.

**Stage-only orchestration.** Anneal captures exact source/model/environment inputs, invokes complete translation/proof stages, and accepts only complete stage results. The backend owns all internal obligation decomposition. This is the smallest design and remains attractive if interactive latency is acceptable at whole-stage granularity. It avoids a new public schema and lets Charon, Aeneas, Lean, or another prover change internal proof decomposition freely.

**Raw backend obligations as the interface.** Anneal schedules generated Lean goals, VCs, solver queries, or equivalent backend objects directly. This maximizes inspectability and can expose very fine parallelism, but it couples Anneal to encodings whose identity and granularity change with translation and proof-search strategy. Viper's two-backend design is direct evidence that this representation need not span equally valid verifier architectures. This option is justified only where the backend itself offers a documented stable obligation contract that Anneal deliberately adopts.

**Semantic obligation manifest with opaque backend payloads.** A translation stage emits a manifest of source/model-level obligations plus provenance and completeness metadata. The selected verifier may internally split, merge, retry, or transform them and may attach diagnostic payloads. Anneal schedules and reports using the semantic manifest while treating backend attempts as children. This costs schema design, completeness accounting, and identity/invalidation logic, but it creates exactly the abstraction needed for obligation-level cancellation, prioritization, caching, progress, and agent-facing repair without freezing one prover encoding.

The third design is the strongest fit **if** Anneal decides it needs obligation-level orchestration. It also creates a serious new proof obligation: Anneal must justify that the manifest is complete for the reported promise. A beautifully stable obligation ID is harmful if translation silently omits a Rust behavior. For that reason, the manifest cannot replace source/model correspondence or complete-coverage evidence; it must be downstream of those guarantees or explicitly trusted as part of them.

Basis: comparative architecture + current Anneal design contract + derived judgment.

### The lowest-risk Anneal step is to preserve the seam before standardizing it

Current Anneal design deliberately leaves the atomic verification unit and proof encoding undecided. The evidence does not justify standardizing a permanent obligation schema before real interactive workloads show a need for sub-stage control.

A low-regret implementation path is narrower:

1. Keep exact source/model/environment/tool generation identity at every existing stage boundary.
2. Require generated diagnostics and proof artifacts to retain Rust/model provenance where the upstream tools can provide it.
3. Distinguish semantic work identity from backend attempt identity in internal APIs and logs even if the first implementation has one obligation per whole stage.
4. Preserve generated intermediate artifacts behind opt-in diagnostic handles so source-oriented UX does not destroy debuggability.
5. Add a first-class obligation manifest only when Anneal needs to control independent sub-stage work; at that point, define completeness and invalidation before using obligation IDs for acceptance or cache hits.

This path keeps the stage-only baseline simple while avoiding an API shape that would later force raw Lean or solver identities to masquerade as durable verification subjects.

Basis: derived conditional judgment.

## Boundaries

No Dafny, Boogie, Viper, Carbon, Silicon, Z3, IDE, or ViperServer process was executed. The report therefore does not measure latency, throughput, cache-hit rate, batching heuristics, counterexample quality, or stability under actual edits.

The report does not claim that current Dafny assertion-batch names or generated Boogie `id` attributes are guaranteed public stable identifiers. They are evidence that current implementations carry provenance and grouping metadata, not a compatibility promise.

The report does not claim that Silver is semantically complete for every source language that targets Viper. Each frontend still has to justify its source-to-Silver encoding and preserve the provenance needed to interpret results.

The report does not claim that Carbon and Silicon prove exactly the same supported subset with identical soundness assumptions, performance, diagnostics, or counterexamples. Their coexistence is used only to show that a shared semantic/intermediate boundary can sit above different backend proof-search representations.

The report does not infer that a first-class obligation interface is required for Anneal V2. The recommendation is conditional on Anneal owning obligation-level scheduling, caching, cancellation, prioritization, progress reporting, or repair interaction. Whole-stage orchestration remains the serious simpler alternative.

The proposed semantic obligation descriptor is not an adopted schema. Fields such as property taxonomy, owner identity, dependency relation, and completeness witness depend on unresolved Anneal design questions and source/model correspondence work.

Backend identities may legitimately be more stable than assumed here if a specific backend documents such a contract. Revalidation should prefer that documented contract over this conservative default.

Primary papers explain project architecture and author intent but are not independent outcome evaluations. Project READMEs and source establish implemented/documented mechanisms at the named revisions; they do not establish broad user-experience or maintenance outcomes.

Anneal implications are derived analysis, not project policy.

## Evidence

**Boogie architecture — primary publication and current project documentation.** Barnett, Chang, DeLine, Jacobs, and Leino, *Boogie: A Modular Reusable Verifier for Object-Oriented Programs*, FMCO 2005, DOI `10.1007/11804192_17`, documents the reusable-verifier architecture. `boogie-org/boogie@fcecf73a49d11ad3ab16729abd03169e5ecfd938`, `README.md` blob `422b2f8869a30ae6c5fd8056a159c1000f2da4ff`, states that Boogie is a modeling/intermediate layer for program verifiers and that the tool generates verification conditions for SMT solvers.

**Dafny architecture — primary publication.** K. Rustan M. Leino, *Dafny: An Automatic Program Verifier for Functional Correctness*, LPAR 2010, DOI `10.1007/978-3-642-17511-4_20`, describes Dafny's automated source-oriented verification model and SMT encoding.

**Dafny batching and verification optimization — current first-party documentation observed 2026-09-30.** `https://dafny.org/dafny/VerificationOptimization/VerificationOptimization.html` documents assertion batches, independent success/failure/timeout, per-batch resource reporting, splitting/isolation, and source-level identification of difficult assertions. The Dafny reference/FAQ documents split/focus controls. Earlier reference documentation also explicitly describes Boogie's `randomSeed` facility as simulating meaning-preserving input changes that can change solver behavior; this is used here only as evidence about backend-search instability, not about current default options.

**Dafny provenance implementation — exact source.** `dafny-lang/dafny@5f717bf447b19d38cad1b69b1bf9a9f102feccfb`, `Source/DafnyCore/Verifier/BoogieGenerator.cs` blob `f097f9c6be4b349b913c9df6853687fb57047fdf`, defines `CanVerifyOrigin`, translator flags for checksums/ranges/unique-ID prefixes, generated implementation IDs, and checksum attributes.

**Viper architecture — primary publication.** Peter Müller, Malte Schwerhoff, and Alexander J. Summers, *Viper: A Verification Infrastructure for Permission-Based Reasoning*, VMCAI 2016, DOI `10.1007/978-3-662-49122-5_2`, motivates a permission-aware intermediate verification language and reports two backends: symbolic execution and verification-condition generation.

**Viper current backends — exact source/documentation.** `viperproject/silicon@6ceff8be6ba55d858b7d018fdfeb866b7e8aa0ed`, `README.md` blob `d4983b9cdbd67dcc0bce44d67c3fa55bf299540d`, describes Silicon as a symbolic-execution verifier for the Viper IVL. `viperproject/carbon@6421cfda16d35f37cb9a7966f04fcd2d96abdda2`, `README.md` blob `3146d1b9a61dfa66d547c18e08cecde8a7317dee`, describes Carbon as a VCG verifier for the same IVL and records its Boogie/Z3 dependency.

**Viper result/provenance interface — exact source.** `viperproject/silver@da1c8993b66feb39976e3609e2580a4661137a0f`, `src/main/scala/viper/silver/verifier/VerificationResult.scala` blob `95980f6c5d21d2bf264ec388ddd6a885f5b494f0`, defines success/failure results and errors carrying positions, identifiers, readable messages, cached state, scope, and transformation hooks. A source comment explicitly notes proof-obligation-level timeout reporting as a possible finer-grained design.

**Viper orchestration boundary — exact current documentation.** `viperproject/viperserver@4cc5bbbe18d4a83e4b398da3904ba9696256611b`, `README.md` blob `a35027560fcf3580590277758797a0c41bb43d2d`, describes an HTTP server managing requests to Carbon and Silicon for IDE/frontend integration, caching, reduced startup latency, and programmatic access.

**Counterexample projection — first-party project documentation.** The Viper Lizard repository documents an experimental debugger that consumes verifier errors and SMT models and presents counterexamples next to failed Viper assertions, postconditions, or invariants while supporting both Carbon and Silicon. This evidence is used only to establish the need for cross-layer provenance in diagnostic tooling.

**Anneal normative context — exact current source.** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb` and `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`, require precise success identity/scope, complete semantic accounting, Rust-oriented unsatisfied obligations, explicit replaceable trust, and minimally sufficient mechanisms while leaving verification atomicity and obligation representation undecided.

**Adjacent Anneal reference evidence — current `reference` at `97677918e2120591c57486a353ee1b75e2f0bd6f`.** `anneal-3730-architecture-contracts-2026-09-29` distinguishes semantic request identity, process policy, stage results, publication, and proof acceptance. `lsp-proof-assistant-architecture-2026-09-27` separates request IDs from durable semantic document identity. `anneal-interactive-pipeline-invalidation-graph-main-41f5b37` separates locator identity from content generations across Charon, Aeneas, Lake, and Lean. J022 extends those distinctions specifically to proof-obligation and backend-attempt identity.

## Revalidation

Before relying on this report for an Anneal obligation API decision:

1. Re-read current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, especially any later decision about the atomic verification subject, proof encoding, or source/model correspondence.
2. Re-check current Dafny batching/logging behavior and the Dafny-to-Boogie provenance/checksum implementation. Treat generated IDs as unstable unless current documentation explicitly promises compatibility.
3. Re-check Boogie's public API and VC-splitting model if Anneal would depend on a concrete Boogie-like obligation representation rather than the abstract lesson here.
4. Re-check Silver, Carbon, Silicon, and ViperServer if Viper adopts a shared proof-obligation service or stable obligation identifier that changes this report's negative-space analysis.
5. Test representative Anneal workloads before adding obligation-level scheduling. Measure whether whole-stage granularity is actually the latency or parallelism bottleneck.
6. If a semantic obligation manifest is proposed, validate three properties before using it for acceptance or caching: complete enumeration for the reported promise, exact binding to source/model/environment/tool generations, and deterministic fail-closed treatment of missing/unknown obligations.
7. Preserve diagnostic access to generated intermediate artifacts and backend attempts even if ordinary users see only Rust-oriented obligations.
8. Compare obligation identity across benign source edits, translator upgrades, changed splitting policies, and backend changes. Any promised cross-generation identity must come from an explicit reconciliation rule, not accidental name stability.