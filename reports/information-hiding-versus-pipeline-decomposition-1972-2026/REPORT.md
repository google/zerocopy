# Information hiding versus pipeline decomposition for Anneal

## Summary

David Parnas's 1972 modularity result applies directly to a temptation in verification-tool architecture: treating the visible execution sequence as the software's primary module decomposition. A pipeline such as Rust source → Cargo/rustc → Charon → LLBC → Aeneas → generated Lean → Lean/Lake → diagnostics is a useful **runtime/dataflow description**. It does not follow that the long-lived code boundaries should be `cargo_stage`, `charon_stage`, `aeneas_stage`, `lean_stage`, and `diagnostic_stage`. Parnas's distinction is that modules are responsibility and knowledge boundaries chosen to confine difficult or likely-to-change design decisions. Those decisions often cross execution time, so a good module need not correspond to one processing step.

The distinction matters especially for Anneal because its durable correctness contract is cross-cutting. A successful result must identify the Rust subject and source to which it applies, the promises proved, the trusted code and assumptions on which it depends, and enough evidence to reject stale, partial, or semantically incomplete work. Current Anneal design authority deliberately does not assign those responsibilities among Anneal, Rust, Charon, Aeneas, and Lean. Existing reference evidence also separates semantic request identity, process policy, stage-result validation, publication fencing, and proof acceptance. Those are already clues that the product's stable responsibilities do not line up one-for-one with tool invocations.

A Parnas-style decomposition for Anneal should therefore begin with the decisions most likely to change or whose accidental spread would make the system hard to reason about. The strongest current candidates are: **subject/source authority**, **tool integration**, **prepared-environment construction**, **execution and scheduling policy**, **provenance projection**, **artifact identity/storage**, and **acceptance/publication authority**. Tool-specific details should remain behind adapters when callers do not need them. But information hiding must not erase evidence that changes the meaning of verification. Exact tool/configuration identity when it contributes to the TCB, semantic subject identity, source generations, explicit partial/failure status, claim/obligation identity, imported proof environment, trusted assumptions, provenance, and freshness/publication fences must remain visible through stable interfaces when downstream acceptance depends on them.

This is not an argument against a pipeline. Pipes-and-filters is a legitimate architecture style with independent transformations and explicit connectors, and Anneal naturally has a transformation graph. The judgment is narrower: **use the pipeline to describe and schedule dataflow; do not assume that pipeline stages are therefore the right ownership and change boundaries**. A tool-named stage should become a module boundary only when its semantic contract is stable enough to hide the implementation decisions behind it. Otherwise, make the tool invocation an implementation of a responsibility-oriented module.

For current Anneal, this suggests a hybrid rather than either extreme. Keep explicit typed artifacts and a visible execution graph because transformation order, dependencies, and debugging matter. Place volatile mechanism behind responsibility-oriented interfaces, and make acceptance authority a first-class consumer of cross-stage evidence instead of merely “the final stage.” Treat this as a design lens, not adopted Anneal policy: current `anneal/DESIGN.md` intentionally leaves component boundaries open, and current V2 source has not yet wired a verification pipeline that could validate the decomposition in production.

## Applicability

The literature anchor is D. L. Parnas, “On the Criteria to Be Used in Decomposing Systems into Modules,” *Communications of the ACM* 15(12), 1972, DOI `10.1145/361598.361623`. The report also uses Parnas's 1979 treatment of extension/contraction, DOI `10.1109/TSE.1979.234169`, and Parnas, Clements, and Weiss's 1985 module-guide paper, DOI `10.1109/TSE.1985.232209`, to distinguish hidden design decisions from navigable documentation of a complex system. Garlan and Shaw's 1994 SEI report, `CMU/SEI-94-TR-021`, supplies the serious competing/complementary view of pipes-and-filters as an architectural style rather than a module-decomposition criterion.

The Anneal design authority examined here is `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md`, `anneal/DESIGN.md`, and current `anneal/src/{main,resolve,scanner,setup,util}.rs`. At this revision the current V2 command surface still exposes `setup`, while target-resolution, artifact-naming, toolchain, locking, scanner, and process helpers exist as partially wired source. There is no production verification command connecting Cargo/rustc, Charon, Aeneas, Lean, proof acceptance, and publication. The concrete module judgments below are therefore architecture analysis over current design constraints and adjacent evidence, not a source review of a completed V2 engine.

The historical pipeline comparison uses the current `reference` corpus at the evidence snapshot recorded below. `anneal-v1-end-to-end-pipeline-41f5b37` reconstructs the retained V1 path and explicitly marks it historical. `anneal-interactive-pipeline-invalidation-graph-main-41f5b37` records the conservative handoffs and invalidation boundaries of the selected toolchain. `anneal-3730-architecture-contracts-2026-09-29` separates semantic request, process policy, stage result, publication, and proof acceptance and gives counterexamples to weaker freshness/acceptance schemes. `anneal-v2-current-source-surface-main-bd0956b-2026-09-29` distinguishes current V2 helper code from a reachable verification architecture.

The analysis answers #3732 J026. It does not decide J027-J031, does not adopt a specific scheduler or cache, and does not claim that a Parnas-style decomposition is sufficient for semantic soundness. Information hiding is about controlling knowledge and change impact; Anneal still needs evidence that the semantics and acceptance conditions on either side of each boundary are correct.

## Findings

### Parnas's target was the criterion for responsibility boundaries, not the existence of a processing sequence

Parnas's KWIC example compares two ways to assign development responsibility over essentially the same computation. The conventional decomposition follows processing steps: input, circular shift, alphabetization, output, and control. The alternative assigns modules around knowledge that should be hidden: storage representation, circular-shift representation, alphabetization choices, and related decisions. In the paper's terms, a module is a **responsibility assignment**, not necessarily a subprogram.

That distinction carries the central mechanism. In the processing-step decomposition, shared table formats and representation choices leak into several modules. A change to one representation therefore requires coordinated knowledge across nominal stage boundaries. In the information-hiding decomposition, callers see narrower abstract operations while the representation decision is localized. Parnas then proposes beginning with difficult or likely-to-change design decisions and assigning modules so each hides such a decision. Because those decisions often matter across several moments in execution, modules generally need not correspond to execution phases.

Two qualifications matter for applying this to Anneal.

First, information hiding is not synonymous with making interfaces opaque or generic. Parnas criticizes an interface that exposes **more of a decision than clients need** because the extra detail unnecessarily constrains future implementations. A useful abstraction still exposes every property on which correct clients depend. The design task is to choose the smallest sufficient semantic interface, not to suppress observable facts.

Second, Parnas explicitly separates clean decomposition from hierarchy. A system may have a useful dependency hierarchy yet still put important design decisions in interfaces, or vice versa. The modern analogue is that Anneal may have a well-formed DAG of stages and still have poor module boundaries if source identity, environment assumptions, scheduling policy, or acceptance semantics are duplicated throughout the DAG.

Basis: **primary publication** and derived application. The 1972 paper's publication text was inspected, including the KWIC comparison, the criteria discussion, and the conclusion.

### A pipeline is a different architectural dimension and remains useful

Garlan and Shaw describe pipes-and-filters in terms of independent transformations connected by streams. Filters should not share state and should not depend on the identities of adjacent filters. The style supports reuse, replacement, composition, analysis, and in some cases concurrency. It also has costs: some systems do not fit batch transformation well; interactive coordination and multiple related streams can be awkward; and common interchange formats can impose conversion or lowest-common-denominator costs.

That model answers a different question from Parnas's: how does computation flow among runtime components? Parnas asks where knowledge and responsibility should live so that change and understanding remain local. The two structures can coincide, but neither entails the other.

For Anneal, the transformation sequence is real and should remain inspectable. Rust compilation precedes Charon extraction; LLBC is consumed by Aeneas; generated Lean is elaborated in a Lean environment; accepted proof results must correspond to the intended source and claims. Hiding that dependency order behind one undifferentiated API would make debugging, resource accounting, provenance, and incremental execution harder. The mistake would be the opposite one: assuming that because Charon and Aeneas are adjacent transformations, every decision relevant to Charon must live in a “Charon stage” and every decision relevant to Aeneas in an “Aeneas stage.”

The useful synthesis is: **dataflow edges define what must flow; module boundaries define which design decisions callers are allowed to know**. An Anneal component may implement one pipeline node, several nodes, or a cross-cutting check, depending on which responsibility it owns.

Basis: **primary architecture literature** plus **derived** Anneal judgment. No Garlan/Shaw implementation was executed.

### Anneal's own history gives a concrete pipeline-shaped baseline without proving it was the wrong decomposition

The retained V1 implementation was strongly organized around a visible toolchain path. Existing reference reconstruction records Cargo/target resolution and source scanning, Charon LLBC generation, Aeneas Lean generation, Anneal specification generation and source mapping, Lake preparation/build, direct Lean checking, and diagnostic projection. That is useful historical evidence about the pipeline shape.

Current V2 design authority does not carry that decomposition forward as a commitment. `anneal/DESIGN.md` explicitly stops short of choosing the division of responsibility among Rust, Charon, Aeneas, Lean, and Anneal. It instead states durable semantic constraints: verification success needs precise identity/scope; Rust-level claims need justified Rust semantics; abstractions may hide details only when relevant semantics survive the boundary; trust must remain explicit and shrinkable; and mechanisms should be no richer than needed.

Current V2 source also exposes some responsibility-oriented seams already. `resolve.rs` centralizes Cargo subject selection and gives each selected package target/kind an explicit `AnnealTargetName`; `scanner.rs` turns that identity into a stable Lean-compatible artifact slug; `setup.rs` centralizes installed-toolchain layout and sanitized command construction; `LockedRoots` and `DirLock` encode filesystem exclusion. These helpers are not yet a complete architecture, but they show that the code already has decisions that do not fit cleanly into a single upstream-tool stage.

This history should not be overread. There is no evidence here that Anneal V1 was replaced *because* pipeline-shaped decomposition caused maintenance failures. The source history establishes a before/after design context, not author motive. The Parnas analysis is a design inference applied to the redesign opportunity.

Basis: **source**, **source history**, existing **reference synthesis**, and **derived** judgment.

### The useful unit of decomposition is a change decision

The following matrix applies Parnas's criterion to concrete Anneal decisions. “Hide” means hide the volatile mechanism from callers that do not need it. “Export” identifies semantics or evidence that must cross the boundary because another component's correctness or interpretation depends on them.

| Decision family | Mechanism likely to change | Natural owner | What the interface should hide | What must remain visible when relevant |
| --- | --- | --- | --- | --- |
| Subject and source authority | Cargo selection rules, workspace traversal, path canonicalization, source capture | subject/source authority | `cargo_metadata` traversal details, locator construction, filesystem discovery policy | semantic compilation subject; build/config selectors that affect code; exact source/annotation generation or digest; unsupported coverage |
| Tool integration | CLI flags, library APIs, process lifecycle, output paths, diagnostics quirks | per-tool adapter behind semantic artifact interface | invocation syntax, temporary files, reset protocol, stderr parsing | exact tool/version/config when trusted; input identity; explicit success/failure; complete output manifest; semantically relevant tool limitations |
| Prepared proof environment | archive layout, Lake manifests, cache paths, env vars, package wiring | environment preparer | installation and cache layout, relocation mechanics, host path construction | imported environment/toolchain identity, configuration that affects elaboration, trust-bearing dependencies, preparation failure |
| Scheduling and execution | one-shot vs persistent workers, queues, parallelism, cancellation, resource limits | scheduler/executor | worker topology and cache placement where semantically irrelevant | request identity, attempt/generation, cancellation/failure semantics, completion witness, worker/incarnation where freshness depends on it |
| Artifact identity/storage | directory names, cache hierarchy, serialization layout | artifact store / artifact authority | mutable path conventions and storage backend | content/semantic identity, producer identity, completeness, provenance, immutability/currentness contract |
| Provenance projection | Charon/Aeneas spans, source maps, remapping data structures, diagnostic rendering | provenance mapper | internal mapping tables and format-specific mechanics | originating authored subject/range, ambiguity/unmappable state, transformation lineage needed to interpret diagnostics |
| Acceptance and publication | ordering of checks, CAS mechanism, publication store, retry protocol | acceptance/publication authority | internal check scheduling and storage mutation details | intended claim/obligations, result/evidence identity, allowed assumptions/TCB, fresh generation fence, explicit rejection reason |
| Incremental invalidation | dependency graph representation, cache algorithms, dirty propagation | invalidation/rebuilder subsystem | graph storage and scheduling heuristic | dependency/evidence closure sufficient to justify reuse; invalidation witness when reused artifacts contribute to acceptance |

The table is not a proposed Rust module list. Several rows may be implemented by one component initially, and a small system should not create layers merely to match a taxonomy. The value is diagnostic: if one decision changes, which parts of the system should need to know? If changing the Charon process API forces edits to proof acceptance, publication fencing, editor provenance, and Cargo subject logic, then the interface probably exposes the wrong information. If changing the Rust compilation subject changes the proof meaning, however, the downstream acceptance interface **should** change or receive a different subject identity; hiding that dependency would be unsound.

Basis: **derived** synthesis over current Anneal design and reference evidence.

### Subject/source authority should not be scattered across every stage

Current `resolve.rs` contains a good local example. It converts Cargo metadata into an explicit `AnnealTargetName` containing package name, target name, and target kind, and it forwards feature selection during metadata resolution because conditional compilation can change the dependency graph and source. It also canonicalizes the manifest path and assigns per-workspace run roots. These choices collectively answer a responsibility question: “what compilation artifact is Anneal talking about?” They are not intrinsically Charon concerns, even though Charon will eventually consume the result.

A pipeline-stage decomposition can accidentally make each stage rediscover the subject from filenames, current directories, Cargo defaults, or its own flags. Existing Anneal evidence already treats this as dangerous: stable names and paths can identify changed content, and source/model identity must be part of acceptance. A Parnas-style owner should instead establish the semantic subject once, preserve its relevant configuration, and let tool adapters consume that identity.

The abstraction cannot stop at today's `AnnealTargetName`. The current structure does not by itself prove the complete rustc compilation subject: target triples, profiles, cfg/build-script outputs, host/target roles, environment and other inputs may matter. The module boundary should therefore hide **how subject identity is discovered**, not freeze an incomplete identity tuple. A later expansion of the compilation-subject model should be localized behind the same responsibility boundary while changing the exported semantic identity as required.

Conditional judgment: this is a strong candidate for a durable Anneal boundary because source/subject identity is product semantics, not an incidental property of one external tool.

### Tool names are useful adapter names but weak top-level ownership boundaries

Charon, Aeneas, Lean, and Lake each have real semantics and operational constraints. Anneal cannot abstract them into an interchangeable `Transform<Input, Output>` if doing so hides trust-bearing or soundness-relevant behavior. Charon's relationship to rustc, Aeneas's translation, Lean's elaboration environment, and Lake's dependency/configuration behavior affect what evidence means.

But callers also should not know every current integration detail. Whether Charon is invoked by CLI, library, or future service; whether Aeneas is one-shot or persistent; where temporary output lands; which stderr line indicates progress; or how Lake manifests are materialized are changeable mechanism. These belong inside per-tool adapters or narrower facilities.

The stable interface should be phrased in Anneal terms: consume a captured subject plus explicit tool/config identity; produce a complete, immutable semantic artifact set or an explicit failure; report provenance and trust contributions; never make partial/stale path contents look like a successful output. The adapter can retain a tool-specific type if Anneal genuinely relies on tool-specific semantics. Information hiding does not demand a single universal artifact type.

This decomposition also makes upstream replacement less expensive. If Charon gains a structured library protocol, only the Charon adapter and any exported semantics that truly change should move. If replacing Charon changes the source/model correspondence that acceptance relies on, the exported evidence contract must change and downstream code must notice. That is desirable coupling because the proof meaning changed.

Conditional judgment: name modules after external tools at the **adapter layer**, not automatically at the architectural responsibility layer.

### Environment preparation is a hidden mechanism with a visible semantic fingerprint

Current `setup.rs` centralizes installed toolchain location and command environment construction. Existing reference work on Lake, toolchain archives, relocation, and prepared environments shows why this is more than a convenience wrapper: imported packages, tool revisions, environment variables, cache state, and filesystem layout can change elaboration or reuse behavior.

The Parnas criterion suggests hiding installation mechanics, archive layout, relocation, cache directories, and command-path construction behind an environment-preparation responsibility. Callers should ask for an environment satisfying an operation-specific contract instead of manipulating Lake paths and archive internals throughout the pipeline.

But an acceptance boundary must still know the environment **identity that affects proof meaning**. If a different Lean revision, imported `.olean`, package configuration, plugin, or trusted library can change the theorem checked, then its identity cannot disappear merely because preparation is encapsulated. The environment module should export an immutable prepared-environment witness or manifest, not merely a pathname or “ready” boolean.

This is a recurring information-hiding pattern for Anneal: hide the *construction decision*, export the *semantic consequences needed by dependents*.

### Scheduling policy should be replaceable without changing result meaning

Existing architecture-contract evidence compared one process per request, persistent per-project workers, and a shared broker in a toy workload. The accepted semantic results could be kept equal while process count, cache warmth, contention, and restart behavior changed. Adjacent evidence also shows that cancellation and completion order do not by themselves authorize publication of a current result.

That is close to an ideal Parnas boundary. Worker topology, queue strategy, process reuse, cache placement, parallelism, and resource limits are likely to evolve with performance data. They should not leak into source authority, tool semantics, or proof acceptance unless they change observable correctness behavior.

The scheduler therefore needs an interface richer than `run(stage)`. A request must carry immutable semantic identity; attempts/generations must distinguish retries; completion must not confer publication authority by itself; cancellation must have defined effects; and persistent workers need incarnation or environment identity when stale state is possible. Those exported facts let acceptance remain correct while scheduling policy changes underneath.

A one-shot implementation can satisfy the same boundary first. That is important: information hiding should permit a simple mechanism before a more optimized one, rather than forcing a broker or daemon architecture prematurely.

Conditional judgment: scheduler/executor is a strong responsibility boundary if publication authority remains outside it.

### Provenance is a semantic service, not just the output end of the pipeline

V1 produced source maps and remapped Lean diagnostics back to Rust. Current reference work finds cross-tool provenance and source mapping nontrivial: generated spans, lexical/source coordinates, projections, and stale source versions can disagree. If provenance code is owned only by the “diagnostics stage,” other consumers may invent their own mappings for cache keys, editor projections, result attribution, or proof repair.

A better information-hiding boundary owns the transformation lineage and the mapping rules. Its implementation may understand Charon spans, Aeneas generated positions, Anneal source maps, and Lean positions. Callers see an authored-source origin, an explicit ambiguity/unmappable state, and enough lineage to detect stale projections.

The boundary should not promise more than the underlying tools provide. If a macro-generated or transformed construct has no unique editable Rust range, the stable result is “ambiguous” or a set of origins, not a fabricated exact location. This preserves the distinction between hiding representation mechanics and inventing semantics.

Conditional judgment: provenance deserves an independent responsibility boundary because it crosses multiple stages and multiple user-facing operations.

### Acceptance and publication authority should not be modeled as merely the last filter

Anneal's strongest divergence from a simple compiler pipeline is its fail-closed promise. `anneal/DESIGN.md` requires successful results to identify subject/scope, promises, trusted code, and assumptions; missing evidence, omitted coverage, unsupported semantics, or failed tools cannot silently acquire the meaning of success. Existing architecture-contract work further separates stage completion, publication fencing, and proof acceptance.

Those requirements are cross-cutting. Acceptance needs evidence produced by subject capture, tool adapters, environment preparation, provenance, and proof checking. Publication additionally needs a current-generation decision so late or canceled work cannot replace newer state. Treating this as `final_stage.rs` risks making acceptance depend on incidental path state or whatever the immediately previous filter returned.

A responsibility-oriented design gives one component authority to convert evidence into a result with an explicit semantic status. It consumes immutable identities and manifests from the rest of the system. It should not itself know how Charon was spawned or where Lake cached files. Conversely, tool adapters and schedulers should not self-declare “verified” merely because their subprocess succeeded.

This module is not a generic policy engine. It encodes Anneal's product-level success semantics and therefore may intentionally be less replaceable than a tool adapter. The volatile decisions to hide are check ordering, retry mechanics, storage mutation, and perhaps publication backend; the stable visible contract is the accepted claim, subject, evidence/trust envelope, and freshness authority.

Conditional judgment: among the candidate boundaries in this report, acceptance/publication authority is the most directly demanded by current normative design.

### Artifact storage should hide paths but not identity or completeness

Both V1 and current V2 source use paths and slugs to connect intermediate artifacts. Paths are operationally necessary, but a pathname is a poor semantic identity: contents can change, stale files can survive failed producers, and different subjects can collide if identity is underspecified.

A Parnas-style artifact facility would own directory layout, cache hierarchy, serialization, temporary files, and atomic storage mechanics. Other components would exchange typed immutable artifact handles carrying content or semantic identity, producer/config identity where necessary, and completeness. The pipeline can still materialize files for external tools; the path becomes an implementation detail associated with an artifact handle rather than the meaning of the artifact.

This boundary has a cost. External tools often demand path-based files and directories, debugging is easier when artifacts have comprehensible locations, and content-addressing every object can add hashing and storage complexity. The minimally sufficient design may therefore begin with ordinary files plus sidecar identity/manifests and only later move to stronger artifact storage if races or reuse justify it. The information-hiding criterion says where that evolution should be localized; it does not prescribe a content-addressed store today.

### Some upstream details must remain deliberately visible

Information hiding can be misapplied to verification systems by treating every external-tool fact as an implementation detail. Anneal's trust model rules that out. The following categories must cross a boundary whenever downstream meaning depends on them:

1. **Semantic subject identity.** Package/target names are not enough if compilation configuration changes the Rust program being modeled.
2. **Captured source and annotation identity.** A proof about revision A cannot be silently presented for revision B.
3. **Tool and configuration identity when trusted.** If correctness relies on a particular translator or elaborator behavior, replacing it is a semantic change until stronger checked evidence removes the trust dependency.
4. **Explicit success, failure, and completeness.** Partial output after a producer error must not be indistinguishable from a complete artifact.
5. **Claim and obligation identity.** “Lean accepted something” is weaker than “the intended Anneal obligations for this Rust subject were accepted.”
6. **Imported proof environment and assumptions.** A theorem's interpretation depends on imports, available axioms, plugins, and other trusted context.
7. **Provenance.** Diagnostics and proof-edit operations need to know which authored source and generated artifacts they refer to.
8. **Freshness/publication authority.** Currentness requires an explicit generation/fence when work may finish out of order or workers retain state.

These are not necessarily raw upstream structures. A stable Anneal-defined manifest can summarize them. The criterion is semantic dependence: if changing a hidden fact can change whether a reported proof means what Anneal promises, the interface must expose that fact or a checked witness that subsumes it.

### Hiding too much and hiding too little have different failure modes

A tool-stage decomposition tends to hide too little of the wrong things. Filesystem layouts, CLI flags, process topology, output naming, and cache behavior can spread to orchestration, diagnostics, acceptance, and UI code. Changes then become multi-module edits even when result meaning is unchanged.

An aggressively generic “verification engine” can hide too much. If it reduces Charon, Aeneas, and Lean to opaque transforms with one `success` bit, it can erase the differences in translation trust, partial output, imported environment, assumptions, and provenance that Anneal needs for sound interpretation.

The design target is therefore not maximum encapsulation. It is **semantic information hiding**: conceal design choices that clients should not rely on; surface invariants and evidence they must rely on. A useful test is counterfactual:

- If the implementation choice changes but the Anneal result meaning does not, should this caller need to change? Prefer no.
- If the implementation choice changes the result meaning, should the caller be forced to notice? Prefer yes.

This test connects Parnas directly to Anneal's fail-closed principle.

### Module guides complement information hiding for a system with many cross-cutting contracts

Parnas, Clements, and Weiss later argued that information hiding in complex systems benefits from a hierarchical “module guide” that helps maintainers find the parts they must understand without reading irrelevant detail. This addresses a practical weakness in purely local abstraction: even well-hidden modules participate in system-level invariants and dependency relations that engineers must navigate.

Anneal is a strong candidate for such a guide because source authority, environment identity, provenance, acceptance, trust, and publication form a small set of cross-cutting contracts. A module guide could document responsibility ownership and the allowed dependency direction without duplicating implementation details. For example:

```text
result acceptance
  uses: subject witness, translation witness, proof-environment witness,
        claim/obligation witness, provenance, freshness fence
  does not own: Cargo discovery, Charon process lifecycle, Lake cache layout

Charon adapter
  owns: invocation/output contract for selected Charon identity
  exports: LLBC artifact + producer/config/source witness + diagnostics
  does not own: publication currentness or final verification success
```

That kind of documentation is distinct from the runtime pipeline diagram. Anneal likely needs both. The pipeline answers “what runs next?”; the module guide answers “where does this decision live, and what do I need to understand to change it?”

Conditional judgment: if V2 grows beyond a handful of files, a responsibility/module guide would likely pay for itself earlier than an elaborate framework enforcing every boundary in code.

### Serious alternatives remain viable

**Tool-stage modules.** This is the most straightforward organization and maps directly to external documentation and logs. It is appropriate when each tool's contract is stable and most changes are local to one tool. Its risk is cross-stage duplication of subject, environment, freshness, provenance, and acceptance logic. It should remain the baseline alternative, not a straw man.

**One orchestration module with small tool helpers.** A single coordinator can keep cross-cutting semantics explicit and avoid premature abstraction. For today's incomplete V2, this may be the cheapest implementation. Its risk is growth into a “god object” in which every new cache, interactive mode, and trust rule becomes coupled. This is a reasonable first implementation if responsibilities are documented and split only when change pressure appears.

**Pure pipes-and-filters.** Strong immutable artifacts between independent filters can simplify caching, replay, and parallelism. It works well for batch transforms and can coexist with responsibility modules. Its weak point is stateful interactive Lean, cancellation, shared environment preparation, and publication authority, which are not naturally just another stateless filter.

**Incremental build/database architecture.** A dependency graph and rebuilder can own invalidation, scheduling, and memoization. This may become attractive for interactive Anneal. It still needs separate semantic ownership for source capture, environment identity, provenance, and acceptance. The graph is execution machinery, not a replacement for those contracts.

**Process/service isolation.** Charon, Aeneas, or Lean could be wrapped as services with message schemas. Process boundaries can enforce failure/resource isolation, but they do not automatically create good information hiding: a badly chosen RPC schema can leak every implementation detail or erase soundness-relevant evidence. Deployment topology should follow measured need rather than define the conceptual modules.

The conditional choice is therefore evolutionary. Start with a small orchestrator and explicit typed evidence. Split durable responsibilities where the current source and expected changes already justify it—subject authority, toolchain preparation, and acceptance are strong candidates. Keep tool adapters thin. Add scheduler/invalidation/artifact-store sophistication when measured interactive or concurrency needs warrant it.

### A concrete dependency direction follows from the judgment

A responsibility-oriented design can remain simple if the dependency direction is explicit:

```text
CLI / editor / MCP shells
        |
        v
request + subject capture  ----->  provenance view
        |                              ^
        v                              |
execution planner/scheduler            |
        |                              |
        +----> tool adapters ----------+
        |          |
        |          v
        |       immutable artifacts
        |          |
        +----------+
                   v
        evidence/result assembly
                   |
                   v
        acceptance + publication fence
```

Environment preparation and artifact storage are services used by adapters/execution but export witnesses into evidence assembly. The diagram intentionally does not say that `CharonAdapter` owns LLBC semantic truth, that `LeanAdapter` owns verification success, or that the scheduler owns currentness. Those stronger responsibilities belong to Anneal-defined contracts.

The exact Rust module graph could be flatter. The important invariant is conceptual ownership: there should be one authoritative place for each decision family and stable evidence should flow toward acceptance without downstream code reaching back into mutable implementation state.

### Conditional judgment for Anneal

J026 asks whether Anneal should prefer information hiding over a pipeline-shaped decomposition. The defensible answer is **yes for module ownership, no for execution/dataflow visibility**.

Prefer information hiding when choosing code and responsibility boundaries because Anneal's most consequential changes are not aligned with one tool invocation: subject identity, process policy, environment construction, provenance, and acceptance cut across the runtime sequence. Preserve a visible typed pipeline because stage order, transformation products, failure locations, resource costs, and invalidation dependencies matter operationally and diagnostically.

The strongest architectural rules implied by this study are:

- Do not make external tool names the only top-level modularization criterion.
- Give cross-cutting semantic responsibilities explicit owners rather than duplicating them among stages.
- Hide replaceable mechanism, not evidence that affects the meaning of verification.
- Let acceptance depend on immutable witnesses, not mutable stage-local paths or “last success” state.
- Keep pipeline topology and module ownership as separate diagrams/documents so neither is mistaken for the other.
- Start with the minimum number of components that can preserve these responsibilities; split further only when independent change, testing, or isolation justifies it.

These are derived design recommendations. They do not amend `anneal/DESIGN.md`, do not select a V2 implementation, and do not establish that any proposed interface is complete. A design review should falsify them against concrete change scenarios before adoption.

## Boundaries

- **No fresh Anneal execution was performed.** The current V2 observations are source-level. Existing execution results are cited through current reference reports and retain their original scopes.
- **No author-intent claim about the V1→V2 redesign is made.** The repository history establishes a historical pipeline and a current redesign whose design document leaves component boundaries undecided. It does not establish that Parnas-style modularity motivated the redesign.
- **The literature is not a proof of Anneal correctness.** Parnas supplies a change/comprehension criterion, and Garlan/Shaw supply architecture-style tradeoffs. Neither validates Anneal's translation semantics, TCB, source correspondence, or proof acceptance.
- **The change matrix is judgment-driven.** The listed responsibility families are inferred from current Anneal constraints and evidence. They are not existing project policy and may need combining or splitting after implementation experience.
- **“Hide” does not mean omit from the TCB or result.** Trust-bearing identities and assumptions must remain visible when result meaning depends on them. Encapsulation cannot shrink the TCB by relabeling unchecked facts.
- **No performance conclusion is drawn.** Responsibility boundaries may add indirection, serialization, hashing, artifact copies, or conversion. A boundary that materially harms interactive latency should be measured and revised without sacrificing semantic evidence.
- **No requirement for process boundaries or microservices is implied.** A module is a responsibility/knowledge boundary. It may compile into the same binary and share a process with adjacent modules.
- **A pipeline stage can still be a good module.** If its semantic input/output contract is stable and its hidden decisions are genuinely local, there is no reason to split it merely to satisfy the taxonomy in this report.
- **Some coupling is correct.** Changes to trusted tool semantics, source/model correspondence, claim meaning, or imported environment should propagate to acceptance because the meaning of verification changed.

## Evidence

Evidence was acquired or revalidated on 2026-09-30 unless otherwise noted.

### Primary literature

- D. L. Parnas, “On the Criteria to Be Used in Decomposing Systems into Modules,” *Communications of the ACM* 15(12):1053–1058, 1972, DOI `10.1145/361598.361623`. Primary publication page: <https://dl.acm.org/doi/10.1145/361598.361623>. The inspected publication text supports the responsibility-assignment definition of module, KWIC comparison, information-hiding criterion, and conclusion that design decisions often transcend execution steps.
- D. L. Parnas, “Designing Software for Ease of Extension and Contraction,” *IEEE Transactions on Software Engineering* SE-5(2):128–138, 1979, DOI `10.1109/TSE.1979.234169`. Primary index: <https://ieeexplore.ieee.org/document/1702607/>. Used for the broader change/family-of-programs framing, not for a specific Anneal mechanism.
- D. L. Parnas, P. C. Clements, and D. M. Weiss, “The Modular Structure of Complex Systems,” *IEEE Transactions on Software Engineering* SE-11(3):259–266, 1985, DOI `10.1109/TSE.1985.232209`. Primary index: <https://ieeexplore.ieee.org/document/1702002/>. Used for the module-guide idea and navigation of hidden-information systems.
- D. Garlan and M. Shaw, *An Introduction to Software Architecture*, CMU/SEI-94-TR-021, 1994: <https://www.sei.cmu.edu/library/an-introduction-to-software-architecture/>. The pipes-and-filters section supplies the complementary runtime architecture style and its tradeoffs.

### Current Anneal design and source

At `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`:

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: fail-closed correctness promise, Rust-oriented usability, extensibility, and preference for general understanding.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: precise result identity/scope, justified Rust semantics, compositional abstraction, explicit/shrinkable trust, minimum sufficient mechanism, and deliberate non-decision about the Anneal/Rust/Charon/Aeneas/Lean responsibility boundary.
- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: current reachable V2 CLI and setup path.
- `anneal/src/resolve.rs`, blob `a87fa5cde060d5fbf59d47f68b5ed0823fe001c5`: Cargo subject selection, explicit target identity, workspace/run roots, and locked output-root access.
- `anneal/src/scanner.rs`, blob `7b4884c9ac16cf30146b851894bd7216b0d1edb8`: `AnnealArtifact`, artifact slug, LLBC filename, and locked LLBC path.
- `anneal/src/setup.rs`, blob `9e17911f4d1e7695cc63fe9f8b2b20b2f0322f00`: installed toolchain layout and command environment construction.
- `anneal/src/util.rs`, blob `602e1585d1c7b4cd61c736a420750b4c396ecdef`: directory-lock primitive and process-output helper.

### Current reference evidence

The native corpus was re-read from `google/zerocopy` `refs/heads/reference` during this run. The relevant package metadata currently includes:

- `reports/anneal-v1-end-to-end-pipeline-41f5b37`: historical V1 execution/dataflow reconstruction and V1/V2 reorganization boundary `dbb81cc7759bb6b21b82a1ca98bb32e9676f8655` / PR #3487.
- `reports/anneal-interactive-pipeline-invalidation-graph-main-41f5b37`: current-toolchain invalidation graph and conservative cross-tool handoffs.
- `reports/anneal-3730-architecture-contracts-2026-09-29`: separation of semantic request, process policy, stage result, publication, and proof acceptance plus topology/freshness counterexamples.
- `reports/anneal-v2-current-source-surface-main-bd0956b-2026-09-29`: source-reachability map showing current V2 helper surfaces without a complete verification pipeline.

These packages are evidence, not adopted Anneal design policy. Their source/execution distinctions and original boundaries continue to apply.

## Revalidation

Revalidate this report in three layers.

First, re-read `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. If current design authority has assigned component responsibilities, compare those decisions to the change matrix instead of treating this report as current architecture. Pay special attention to any new definition of verification result identity, TCB representation, publication authority, or source/model correspondence.

Second, trace the reachable current implementation rather than inferring architecture from filenames. Starting at the CLI/editor/MCP entry points, record where the following responsibilities actually live: subject capture, tool invocation, environment construction, scheduling, artifact identity, provenance, acceptance, and publication. For each material change since the pinned revision, ask which modules needed edits. A good information-hiding boundary should keep changes local when result meaning is unchanged and force visible interface changes when semantic meaning changes.

Third, run a change-scenario review before adopting any proposed split. At minimum simulate these changes on paper or in small patches:

1. Charon CLI becomes a library API without semantic output changes.
2. Aeneas gains a persistent server with reset/cancellation semantics.
3. Lean/Lake package preparation changes layout but preserves the same imported environment.
4. Cargo subject identity expands to include a newly discovered build/config input.
5. Source-map representation changes while authored-source provenance remains equivalent.
6. A stale worker returns a proof result after a newer request is published.
7. A trusted translator version changes in a way that changes the TCB but not artifact syntax.
8. Incremental reuse introduces a dependency graph that can omit a newly discovered input.

For each case, list the components that must change and the evidence acceptance must observe. If mechanism-only changes propagate broadly, the decomposition hides too little. If meaning-changing cases pass without an interface or witness change, it hides too much. Re-run the judgment after actual V2 implementation experience; the current source is too incomplete to establish the final split.