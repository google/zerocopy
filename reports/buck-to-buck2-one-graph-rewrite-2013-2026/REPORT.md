# Buck to Buck2: what the rewrite simplified, and what it did not

## Summary

Buck2 is strong evidence for replacing a build system's architectural core when the old core makes important invariants and performance properties difficult to express locally. It is weaker evidence for adopting a general incremental-computation engine whenever a workflow has dependencies.

Meta describes Buck2 as a from-scratch rewrite that retained a high degree of Buck1 target compatibility while changing three coupled architectural choices. First, it moved language rules out of the core into Starlark behind a smaller rule API. Second, it replaced Buck1's target-graph, action-graph, and execution phases plus some work outside those graphs with one dynamic incremental dependency graph. Third, it designed execution around remote execution from the start rather than adding it later. Meta reports large improvements after the rewrite, including roughly 2x faster builds overall in internal tests, near-zero no-op latency in a cited benchmark, faster CI, and many dependency bugs exposed during migration.

Those outcomes do not establish that the single graph alone caused the gains. Buck2 simultaneously changed implementation language, rule architecture, dependency discipline, caching, remote execution, file-system integration, and many details of the scheduler. The public evidence is first-party and does not publish a controlled decomposition of those effects. The strongest causal claim supported by the architecture is narrower: a single dependency model removed phase boundaries that had forced coarse invalidation or work outside dependency tracking, so it made precise invalidation and cross-stage parallelism expressible in one place.

The rewrite also did not make the core trivial. DICE is a sophisticated dynamic incremental-computation engine. Current Buck2 documentation describes its generic DICE layer as experimental and being rewritten, while a later "Modern DICE" account explains that the implementation itself was substantially redesigned from fine-grained shared locking to a single-threaded core-state model. That same account identifies hard correctness hazards around equality across transactions and data that flows outside tracked dependencies. Buck2 therefore simplified the *architectural contract* seen by rule authors and integrators while moving substantial complexity into a reusable incremental engine.

Migration was part of the cost and part of the benefit. Buck2 preserved the familiar target model and aimed for target compatibility, but rules moved from Java classes embedded in Buck1 to external Starlark, the rule API changed, and stricter dependency accounting exposed many missing dependencies. Meta's public material says the migration fixed a "huge number" of such defects and also says Buck1 had accumulated corner-case behavior over nearly a decade. Public sources do not quantify the total engineering labor, elapsed rewrite time, or migration cost well enough to compute a return on investment independently.

For Anneal, the useful lesson is not "build DICE." It is to unify state transitions that must share one correctness and freshness model, and to keep domain-specific policy outside that core. Anneal's present workload is much smaller than Meta's multi-language monorepo build problem. A small explicit DAG or state machine can likely provide the important properties—identity, dependency tracking, cancellation boundaries, validation, and atomic publication—without immediately paying for a general self-adjusting computation engine. Anneal should cross that complexity threshold only when concrete workloads require dynamic dependency discovery, cross-request memoization, early cutoff, or fine-grained invalidation strongly enough that a simpler orchestration model becomes the limiting constraint.

## Applicability

This report addresses issue #3732 J044: **Buck to Buck2: did replacing the core simplify the system?** It reconstructs the public rationale for the Buck2 rewrite, the boundary between rules, incremental evaluation, and execution, the benefits attributed to the single DICE graph, and the costs visible in migration and later DICE evolution. It then asks whether those reasons transfer to Anneal.

The Buck2 source observations are pinned to `facebook/buck2` revision `738e69a6c5f1efb6a015645228e7a19ee9b1d9c0`, observed on 2026-09-30. The historical launch account is Meta Engineering's 2023-04-06 article. Buck1's terminal public state is represented by archived `facebook/buck` revision `9c7c421e49f4d92d67321f18c6d1cd90974c77c4`, whose README directs users to Buck2. The build-system design vocabulary comes from Mokhov, Mitchell, and Peyton Jones's 2018 *Build Systems à la Carte* paper. Anneal implications are checked against `google/zerocopy` `main` revision `cc135f46155b72e4b51188525c2974a3b84acf92`, specifically the current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` blobs named in `REPORT.json`.

The report treats four kinds of statements separately:

- **Author intent:** what Meta says it was trying to fix or enable.
- **Implementation:** what the current public Buck2 source and documentation actually expose.
- **Reported outcomes:** Meta's internal benchmark and migration claims.
- **Derived judgment:** what those facts suggest for Anneal. These implications are analysis, not adopted Anneal policy.

The comparison is architectural, not a benchmark. No Buck or Buck2 workload was executed for this report, and the public sources do not expose Meta's internal monorepo, migration ledger, or benchmark datasets.

## Findings

### 1. Buck2 rewrote the places where Buck1's structure leaked into correctness and performance

Meta's launch account does not describe the rewrite as a cosmetic reimplementation. It identifies structural limitations in Buck1 and deliberately changes the boundaries around them.

Buck1 had multiple graph-shaped phases. Meta describes target-graph construction, action-graph construction, and action execution as distinct, and notes that some operations did not run on a tracked graph at all. Changes could therefore force an entire graph to be thrown away rather than invalidating the smallest affected computations. The OCaml example in the launch article is a concrete correctness failure of that architecture: Buck1 ran `ocamldep` after parsing a BUCK file in a place where dependency tracking did not properly cover what the tool discovered, so sufficiently large import changes could cause spurious build failures.

Rules were another structural boundary. Buck1 language rules were Java classes built into the executable. Over time those rules accumulated performance features and implicit invariants. Meta's current Buck2 comparison says Buck1 rule authors had to obey many subtle side conditions in a large API. Deploying a rule change also meant rebuilding and shipping Buck itself, sometimes while maintaining compatibility with both old and new versions.

Buck2 deliberately changes both boundaries. Its core is language agnostic, and language rules live in Starlark. Advanced facilities such as dep files, incremental actions, dynamic dependencies, anonymous targets, and transitive sets are exposed as general APIs rather than as privileged tricks available to selected built-in rules. The intended simplification is therefore not merely fewer source lines. It is a smaller set of privileged concepts and fewer ways for a rule to work around the dependency model.

That distinction matters for Anneal. Rewriting a core pays off when the existing decomposition makes the desired invariant non-local—for example, when freshness can be violated by work that happens between nominal phases and is invisible to the invalidation model. A rewrite is much harder to justify when the existing core already exposes the invariant directly and the complaint is only local code quality.

### 2. The single graph removes a semantic boundary, not just an implementation phase

Buck2's headline graph change is that loading, analysis, and later computations can participate in one DICE dependency graph rather than being organized as separately materialized target and action graphs. Meta's current documentation calls Buck2 "not phased": requests become a chain of dependencies in a single graph, which can let work from what would have been different phases overlap and can let invalidation stop at a recomputed value that is equal to its prior value.

DICE supplies the generic mechanism. A computation is identified by a key, computes a value, and records other DICE computations it requests as dependencies. Leaf or injected values can be changed or invalidated. DICE then rechecks only the affected path, can deduplicate identical concurrent requests, and can apply early cutoff when a recomputed value is equal to its previous value.

This is a real simplification in *authority over incrementality*. Instead of each phase deciding independently what is stale, one engine records dependency edges and owns reuse. The engine can see a dependency that crosses what would otherwise have been a phase boundary. Dynamic dependencies also fit naturally because the graph can be discovered as computations run rather than having to be known before a phase starts.

The same feature can also increase semantic reach. Buck2 uses the dynamic graph for cases such as OCaml dependency discovery and distributed ThinLTO, and anonymous targets can create sharing that is not explicit in the user-authored target graph. These are capabilities that an ordinary static DAG scheduler does not provide automatically.

But a single graph is not the same as a single *kind* of work. Rule evaluation, configuration, artifact execution, remote execution, materialization, and user-facing commands retain different semantics. The graph unifies dependency and invalidation bookkeeping while the APIs continue to distinguish those operations. This is an important part of why the design scales: Buck2 centralizes the mechanism that benefits from one model without flattening every domain concept into an undifferentiated node type.

### 3. Meta reports large outcomes, but the public evidence does not isolate the cause

Meta reports several substantial improvements after moving to Buck2:

- the 2023 launch account says internal tests observed builds completing about 2x as fast as Buck1;
- current Buck2 comparison documentation gives an example in which a no-op build fell from 23 seconds to 0.1 seconds;
- the same documentation reports examples ranging from a 5% / 10-second improvement for a header change to a 42% / 145-second improvement for a Thrift change;
- it says most CI projects were 2–4x faster at the time of that comparison;
- it reports faster and lower-memory queries for CI target determination; and
- it says migration uncovered and fixed a large number of missing dependencies.

These are first-party operational observations, not controlled experiments published with enough data for independent replication. More importantly, the rewrite changed many variables together. Rust removed Java GC behavior. Remote execution became a first-class design assumption. Rules moved out of the core. Dependency correctness tightened. File-system integration changed. Caching and shared-cache policy changed. DICE removed graph phases. Individual data structures and hot paths were tuned.

The evidence therefore supports "the Buck2 architecture plus implementation produced a large practical improvement at Meta" more strongly than "the single graph alone produced the improvement." Meta itself describes speed as the consequence of many factors plus detailed engineering work.

For Anneal, this argues against cargo-culting the most visible architectural feature. The decision should ask which specific failure mode a general incremental graph would remove and what evidence shows that failure mode matters to Anneal's workload.

### 4. Buck2 simplified the external model by concentrating complexity in DICE

A system can become conceptually simpler for its clients while its substrate becomes more sophisticated. Buck2 is a clear example.

For a rule author, the contract is smaller: write Starlark against a documented API, declare or dynamically discover dependencies through supported mechanisms, and let the core track them. The current Buck2 comparison explicitly describes this API as smaller and dependency-correct by construction compared with Buck1's larger API and subtle side conditions.

Inside DICE, however, incremental computation has difficult semantics. The current generic DICE index describes DICE as the engine behind Buck2's incremental transformations, with parallel execution, request deduplication, invalidation, cancellation, transient-error handling, and projections. It also still labels the DICE layer experimental and says it is being largely rewritten.

The later "Modern DICE" account makes the implementation cost more concrete. It says a previous design kept core state in the async evaluator behind fine-grained locks; complexity in that design motivated a move to a single-threaded core-state component. It also calls out two classes of correctness hazard:

1. **Equality across versions.** A key or value that is unique during one command may not denote the same semantic object across commands. Incremental reuse therefore depends on equality meanings that survive transactions, not just local identity assumptions.
2. **Untracked data flow.** Mutable state hidden behind locks, lazily initialized values, or per-transaction user data can bypass DICE's dependency tracking. If such data affects a computation without becoming a tracked input, the graph can reuse a result under the wrong assumptions.

These are not incidental implementation bugs. They are the characteristic costs of a self-adjusting system: the engine only gives sound reuse if semantic identity, equality, and all relevant inputs are modeled correctly.

The important judgment is therefore claim-relative. Buck2 made the *build architecture* simpler by giving dependency tracking one owner and rule authors a smaller capability surface. It did not make incremental-computation semantics simple. It made them reusable and concentrated.

### 5. The rewrite preserved user-facing continuity while deliberately breaking internal extension structure

Buck2 was not a clean-slate product in the sense of abandoning Buck's user model. Meta's current documentation says it aimed to retain Buck1's best parts with a high degree of target compatibility. The launch account similarly says the user model remained mostly the same and that Buck2 was mostly compatible with Buck1 BUCK files.

At the same time, the extension architecture was intentionally incompatible. Buck1's Java rule classes did not simply move into a Rust core. Buck2 forced rules through Starlark and a general API. That choice removed privileged language-specific hooks from the executable, but it required rule implementations and their hidden assumptions to be reconstructed on the new surface.

The migration exposed latent correctness debt. Meta says many missing dependencies were fixed during the transition, and it lists Buck1 cases such as missing headers, genrules without dependencies, and incomplete OCaml dependency tracking. In that sense migration cost was also diagnostic value: a stricter architecture forced previously implicit dependencies to become explicit or to use sanctioned dynamic mechanisms.

The public record does not give enough information to quantify the total cost. It does not provide person-years, a full migration timeline, the number of rules converted, the number of compatibility shims, or the aggregate productivity loss during dual operation. Current documentation also distinguishes the internal and open-source environments: Meta's internal remote-execution setup and toolchains are not identical to the public release. Claims about migration economics should therefore stay qualitative.

### 6. "One graph" remains an engineering choice within a wider build-system design space

*Build Systems à la Carte* is useful here because it separates concepts that production build systems often fuse. Its core result is that build scheduling and rebuilding strategy are distinct design choices, with further variation in static versus dynamic dependencies, persistent traces, cloud execution, and early cutoff. The paper's purpose is precisely to show that build-system capabilities can be recombined rather than inherited as one indivisible architecture.

Buck2 chooses a powerful point in that space: dynamic dependencies plus a persistent incremental computation engine, aggressive parallelism, early cutoff, and remote execution. That choice is justified by Meta's scale and by workloads where dependencies can emerge during computation.

Serious alternatives exist:

- **Repair a phased system.** A system can keep separate phases while improving their explicit inputs, caches, and invalidation contracts. This preserves simpler phase-local reasoning at the cost of less cross-phase reuse and more boundary bookkeeping.
- **Use a static DAG scheduler.** If dependencies are known after a cheap preparation step, an ordinary DAG can already provide parallelism, cancellation propagation, and minimal rebuilds without a general self-adjusting engine.
- **Compose component-local incrementality.** A host can treat a compiler or prover's own incremental engine as an opaque service and establish an explicit freshness contract at the boundary. This avoids duplicating the component's internal dependency model, but the host cannot infer state that the component does not expose.
- **Adopt a generic incremental framework only where needed.** Salsa-, Adapton-, Shake-, or DICE-like mechanisms can be introduced for the subset of computations whose dynamic dependencies and cross-request reuse justify them, while leaving execution and publication as explicit state transitions.

Buck2's own design supports this narrower reading. The single graph unifies computations whose dependency semantics DICE can represent, but it still has explicit APIs and distinct execution machinery around the graph. The architectural lesson is to centralize a cross-cutting invariant when many subsystems otherwise reimplement it—not to erase every subsystem boundary.

### 7. Anneal should borrow Buck2's boundary discipline before borrowing its engine

Anneal's design contract requires precise success semantics, justified source-to-model correspondence, compositional boundaries, explicit trust, and minimally sufficient mechanisms. Those constraints align with several Buck2 lessons.

First, Anneal should have one authoritative place where freshness and publication identity are decided. A proof result should not be accepted because one phase believes an input is current while another phase has a separate cache or hidden configuration. Whatever prepares a Charon/Aeneas/Lean environment should expose the identities and dependencies needed by the publication path to validate that the result still applies.

Second, component-specific policy should stay outside that small authority when possible. Which goal to attempt, which cache entry to prefer, how aggressively to parallelize proof search, or which backend to choose can be ordinary policy so long as the final acceptance boundary independently checks the properties that matter to Anneal's promise.

Third, Anneal should treat hidden input flow as a correctness problem, not merely a cache-performance problem. DICE's warnings about untracked mutable state have a direct analogue in environment variables, toolchain selection, generated files, native libraries, plugin state, or editor buffers that affect a proof without appearing in the identity of the prepared environment. A more sophisticated scheduler does not repair an incomplete input model.

Fourth, Anneal should not infer that one generic graph is required today. Its current architecture is orders of magnitude smaller than Meta's multi-language build graph, and its most important irreversible transition is canonical publication rather than maximizing build throughput. A small DAG or explicit generation/state model can satisfy the current contract if it records all semantically relevant inputs and validates before reuse or publication.

A reasonable threshold for introducing a DICE-like core would be evidence of several of the following at once:

- dependency discovery that genuinely occurs during computation and cannot be cheaply normalized into a preparation step;
- expensive recomputation across interactive requests where early cutoff materially improves latency;
- multiple clients requesting overlapping semantic computations concurrently;
- repeated correctness bugs caused by separate invalidation logic in different Anneal phases;
- enough stable key/value identity to make cross-generation equality precise; and
- profiling showing orchestration and recomputation, rather than Charon/Aeneas/Lean execution itself, on the critical path.

Without that evidence, the smaller design better matches Anneal's stated preference for minimally sufficient mechanisms. Buck2 shows that a rewrite can be worth it when complexity is already distributed throughout the old architecture. It does not show that paying the generic-engine cost early prevents such complexity from appearing.

## Boundaries

This report does not independently benchmark Buck1 or Buck2. Performance numbers are Meta's published internal measurements and are labeled as such.

The report does not attribute Buck2's performance gain to DICE alone. The rewrite changed multiple major variables simultaneously, and the public evidence does not provide an experimental decomposition of their effects.

The report does not quantify Buck2's rewrite or migration cost. Public sources establish substantial compatibility and migration work but do not expose enough labor or timeline data for a reliable cost estimate.

The report does not treat the current DICE documentation's "experimental" wording as evidence that Buck2 itself is experimental in production. Buck2 is heavily used at Meta; the wording applies to the generic DICE layer and its API/implementation evolution.

The report intentionally avoids the deeper Kotlin incremental-compilation composition case requested by J045. That is a separate question about composing two incremental systems and should be adjudicated independently rather than smuggled into J044.

The Anneal recommendation is conditional. It assumes the current design contract remains authoritative and that Anneal's orchestration workload remains substantially smaller than a general monorepo build. A future workload with widespread dynamic dependencies or expensive cross-request recomputation could change the tradeoff.

## Evidence

### E1 — Meta Engineering launch account, 2023-04-06

Role: **documentation / reported outcome / author intent**.

Source: https://engineering.fb.com/2023/04/06/open-source/buck2-open-source-large-scale-build-system/

Meta describes Buck2 as a from-scratch rewrite, explains the language-agnostic core and Starlark rules, contrasts Buck1's multiple graphs/phases with Buck2's single incremental graph, gives the OCaml dependency example, and reports roughly 2x faster internal builds. This is the strongest first-party historical account of the rewrite rationale. It is not an independent benchmark.

### E2 — Buck2 `docs/about/why.md` at revision `738e69a6c5f1efb6a015645228e7a19ee9b1d9c0`

Role: **documentation / current architecture**.

Source: https://github.com/facebook/buck2/blob/738e69a6c5f1efb6a015645228e7a19ee9b1d9c0/docs/about/why.md

Blob: `6799f38df279cc03f1806b1d0d447fb19570bcfa`.

This current project documentation records the rewrite's compatibility goal, Rust core, remote-execution-first design, Starlark-only rules, language-agnostic binary, dynamic graph, transitive sets, and absence of target/action phases.

### E3 — Buck2 `docs/about/benefits/compared_to_buck1.md` at the same revision

Role: **documentation / reported outcome / migration evidence**.

Source: https://github.com/facebook/buck2/blob/738e69a6c5f1efb6a015645228e7a19ee9b1d9c0/docs/about/benefits/compared_to_buck1.md

Blob: `296661b09239357fa870a55192dff6c5d54c25ca`.

This first-party comparison reports no-op, incremental-build, CI, query, and memory improvements; describes Buck2's smaller rule API; and says migration exposed many missing dependencies. It also lists stability and corner-case costs. The numbers are internal Meta observations.

### E4 — DICE `dice/dice/docs/index.md` at the same revision

Role: **source documentation / implementation boundary**.

Source: https://github.com/facebook/buck2/blob/738e69a6c5f1efb6a015645228e7a19ee9b1d9c0/dice/dice/docs/index.md

Blob: `46897b9bd66a7bd055bbad8db7f363558347d4f0`.

The DICE documentation identifies DICE as Buck2's generic dynamic incremental-computation engine, with parallel computation and deduplication, and currently describes the layer as experimental and being largely rewritten.

### E5 — Buck2 `docs/insights_and_knowledge/modern_dice.md` at the same revision

Role: **documentation / implementation history**.

Source: https://github.com/facebook/buck2/blob/738e69a6c5f1efb6a015645228e7a19ee9b1d9c0/docs/insights_and_knowledge/modern_dice.md

Blob: `04a9950e2b077cdfdf91ca3e6e6ede68df508580`.

This project-hosted knowledge-sharing transcript explains invalidation, early cutoff, the move from fine-grained locks to a single-threaded core-state design, dependency-checking changes, and practical hazards involving equality across transactions and data flow that DICE does not track.

### E6 — archived Buck1 repository at revision `9c7c421e49f4d92d67321f18c6d1cd90974c77c4`

Role: **source / historical state**.

Source: https://github.com/facebook/buck/blob/9c7c421e49f4d92d67321f18c6d1cd90974c77c4/README.md

README blob: `59e9fda6c885670ebb3e0ce1b799ea8f9e97cf9c`.

The terminal public README directs users to Buck2 and marks the old repository dead. It establishes the replacement outcome, not the causes of the rewrite.

### E7 — Mokhov, Mitchell, and Peyton Jones, *Build Systems à la Carte*, ICFP 2018

Role: **literature / design vocabulary**.

Source: https://doi.org/10.1145/3236774

The paper separates build-system scheduling from rebuilding strategy and surveys static/dynamic dependencies, traces, early cutoff, and cloud execution. It supports comparing Buck2's chosen point in the design space against smaller alternatives rather than treating production build systems as indivisible packages.

### E8 — Anneal `PRINCIPLES.md` and `DESIGN.md` at `google/zerocopy` revision `cc135f46155b72e4b51188525c2974a3b84acf92`

Role: **normative for Anneal constraints**.

Sources:

- https://github.com/google/zerocopy/blob/cc135f46155b72e4b51188525c2974a3b84acf92/anneal/PRINCIPLES.md
- https://github.com/google/zerocopy/blob/cc135f46155b72e4b51188525c2974a3b84acf92/anneal/DESIGN.md

Blobs: `d5339a95254eae14ac201139d07d9d36d48a19fb` and `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`.

These files require precise verification meaning, justified Rust correspondence, compositional abstraction, explicit/shrinkable trust, and minimally sufficient mechanisms. They constrain the derived Anneal judgment but do not themselves select an orchestration engine.

## Revalidation

Before treating this report as current coverage for J044:

1. Re-read live issue #3732 and confirm J044's wording and combine/split boundaries have not changed.
2. Re-read the current `reference` branch and search semantically for any Buck/Buck2 rewrite report published after this observation. Package-name absence is not enough.
3. Re-read current Buck2 documentation and source if the pinned revision is no longer representative, especially DICE documentation and any migration/architecture retrospectives that add controlled performance evidence or quantified rewrite cost.
4. Re-read Anneal's current `PRINCIPLES.md` and `DESIGN.md`; if the design has adopted a concrete scheduler, cache, or preparation service, reassess the alternative set against that decision rather than this report's pre-decision assumptions.
5. Keep J045 separate unless new evidence makes a combined Buck2 rewrite-plus-Kotlin composition report materially more coherent than two focused reports.