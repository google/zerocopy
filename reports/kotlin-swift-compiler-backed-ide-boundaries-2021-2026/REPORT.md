# Kotlin and Swift: what a compiler-backed IDE buys, and what it still leaves to orchestration

## Summary

Kotlin K2/Analysis API and Swift SourceKit make the same high-level trade in different forms: they put editor semantics on top of compiler-owned frontend machinery, then surround that machinery with explicit project, build, lifetime, and invalidation protocols. The compiler service buys capabilities that an external orchestrator cannot reproduce cheaply or reliably: lazy semantic resolution, reusable compiler-owned state, semantic objects whose validity tracks source revisions, and operations such as completion or cursor information that can reuse an existing frontend state rather than rebuild it from scratch.

That benefit does **not** make the compiler service authoritative for the whole development environment. Kotlin's Analysis API receives its project structure from a platform such as IntelliJ or Standalone, and JetBrains explicitly distinguishes the compiler frontend bundled into the IDE from the compiler version selected by the build. SourceKit-LSP likewise obtains targets, source membership, compiler options, index locations, and preparation from a build system or BSP server. Its own contributor documentation requires preparation options to match the options later used for semantic requests. In both systems, the build model remains a separate input whose freshness and identity must be managed.

Generated inputs expose the same boundary. Kotlin can integrate declarations that do not exist as ordinary source only because the Analysis API and FIR expose first-class mechanisms for compiler-plugin declarations and resolve extensions; a resolve extension participates in the analysis session, publishes invalidation, and can shadow stale generated source files. An orchestrator can run a generator and present materialized files, but it cannot manufacture the compiler's notion of synthetic or plugin-generated declarations unless the frontend exposes a faithful interface. Swift's build integration goes the other direction: SourceKit-LSP asks the build system to prepare targets and provide their sources/options, so build-tool output can enter through an explicit build boundary, while sourcekitd retains responsibility for compiler-internal semantic products such as AST state and macro/generated-interface views.

The conditional lesson for Anneal is therefore narrower than "use a compiler service." Keep environment preparation, build-context identity, generated-artifact identity, and publication under explicit orchestration. Add or depend on a persistent upstream service only where Anneal needs state that is *owned by that upstream semantic engine*—for example, a Lean tactic state at a particular proof position, or reusable compiler/frontend state that cannot be reconstructed from stable external artifacts without repeating substantial work. Treat such a service as a cache and semantic executor over an explicit immutable context, not as the source of truth for which context is current. Batch verification success must still bind the exact Rust/translation/proof inputs and accepted checker result required by Anneal's design contract.

## Applicability

This report addresses J016 of `google/zerocopy#3732`: selected Kotlin FIR/Analysis API and Swift SourceKit/SourceKit-LSP decisions about reusable frontend state, generated inputs, plugins, and build configuration, and the resulting boundary between upstream compiler-service capability and downstream orchestration.

The current implementation evidence is pinned to:

- `JetBrains/kotlin@bce49f3701fb8dc461fb98240fdc7c3c81c592f2`;
- `swiftlang/sourcekit-lsp@045c18e9e9ea35b896857b6cb982aa2373fb5816`;
- `swiftlang/swift@f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d`; and
- Anneal's current V2 design at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.

Historical rationale is taken from first-party JetBrains and Swift project material from 2019–2025 and is identified separately under **Evidence**. Those historical sources explain why particular mechanisms were introduced or changed; current source bounds claims about current mechanisms.

"Compiler-backed IDE" here means an editor analysis path that invokes or embeds compiler frontend semantics, not merely an IDE that shells out to a batch compiler. "Orchestration" means code outside the semantic engine that can select versions, derive or acquire build settings, run generators, start/stop processes, route requests, cache stable artifacts, and decide which outputs may become authoritative. The distinction is functional, not process-based: a compiler service can run out of process and still own semantic state; an orchestrator can run in the same process and still merely supply environment and lifecycle.

The Anneal conclusions are derived design analysis. They do not alter the current Anneal architecture or decide the design contract's explicit non-decisions about result subjects, generated artifacts, or the boundary among Rust, Charon, Aeneas, Lean, and Anneal.

## Findings

### Compiler reuse and build authority are separate decisions

Kotlin's current Analysis API makes the separation unusually explicit. `KaSession` is the entry point for frontend work, but every analysis session has a use-site `KaModule`. `KaModule` determines the session's resolution scope and the content and dependencies from which symbols resolve. Crucially, the Analysis API engine does not itself define the project structure: a platform implementation such as IntelliJ or Standalone supplies `KaModule` implementations and the module provider.

That makes the compiler frontend an evaluator of a supplied semantic world, not the sole authority that constructs the world. `KaModule` includes regular, `dependsOn`, and friend dependencies, target platform, language-version settings, content roots/scopes, and module identity. A wrong module graph can therefore produce coherent compiler-backed answers for the wrong project context.

JetBrains's K2 rollout provides a historical version of the same point. The 2023 K2 announcement states that the Kotlin IDE plugin contains a compiler frontend for semantic analysis, while the compiler actually used to build the project is selected by build-file settings. JetBrains therefore had to build a new IDE plugin on the K2 frontend rather than assume that using K2 for compilation automatically changed IDE analysis. This is a useful counterexample to the idea that "same compiler technology" automatically gives build-equivalent editor semantics.

SourceKit-LSP draws the same boundary through a protocol rather than an object model. Its BSP integration requires the build server to provide `workspace/buildTargets`, `buildTarget/sources`, `textDocument/sourceKitOptions`, build-change notifications, and a way to wait for build-system updates. For background indexing, the build server also prepares targets, and SourceKit-LSP's contributor documentation says the compiler options used for preparation should match the options sent for semantic requests to avoid module-loading mismatches.

**Basis: source + documentation + historical first-party documentation.**

**Derived Anneal judgment.** An Anneal interactive service should not discover or silently mutate its own notion of the verification subject when the surrounding build already has a stronger authority. The orchestrator should pass an explicit project/subject context—or a digest/handle that resolves to one—and that context should include the build and generated-input information needed to reproduce the semantic world. A long-lived Lean, Charon, Aeneas, or Rust semantic service can then cache work *within* that context. This preserves the design contract's requirement that successful verification have enough identity and scope to make its promise meaningful.

### Reusable frontend state is a real upstream capability, not a process-lifetime trick

Kotlin's FIR-backed Analysis API does more than keep a JVM process alive. The current implementation caches `KaFirSession`s by use-site module, ties them to underlying low-level FIR sessions, validates them on acquisition, invalidates them when the corresponding FIR sessions are invalidated, and allows garbage collection of unused sessions. `KaModule` is also documented as the unit of non-local modification invalidation.

The FIR checker documentation shows why this state model matters. CLI compilation runs checkers after whole-project body resolution, but IDE analysis uses lazy resolution: some files may already be resolved through `BODY_RESOLVE` while others may not be resolved at all. FIR accessors are responsible for resolving declarations to the minimum phase needed by a query. That is an interactive evaluation policy baked into the frontend architecture, not something an external daemon can obtain merely by memoizing completed batch invocations.

The Analysis API's lifetime rules expose the correctness cost of this reuse. `KaSession` and most semantic objects may not escape the analysis call that created them. Cross-session reuse goes through explicit pointers, because symbols and types are interpreted in a use-site context and can become invalid after source or project changes. JetBrains's K1-to-Analysis-API migration guide says that careless handling of the old `BindingContext` and its contents had been a source of exceptions, incorrect behavior, and leaks; the new API makes the lifetime constraint explicit rather than relying on clients to preserve a hidden invariant.

Swift SourceKit contains the same kind of compiler-owned reuse at a lower level. Current SourceKit tests assert that consecutive cursor-information requests can reuse an AST context. `SwiftASTManager` exposes a `canUseASTWithSnapshots` decision: a consumer may accept an AST built from a particular set of text snapshots, and the manager can route a compatible built AST to later work. The key condition is semantic compatibility with source snapshots, not simply that a sourcekitd process remains alive.

**Basis: source + current project documentation; the K1 migration consequence is documentation by the Kotlin project.**

**Derived Anneal judgment.** If an interactive Anneal feature needs a state that only Lean (or another upstream engine) knows how to construct and update safely—most notably tactic state at a proof position—then an upstream interactive protocol is qualitatively better than a wrapper around repeated batch processes. The upstream engine can preserve and invalidate internal elaboration state at its native granularity. If, by contrast, the desired result is already a stable serialized artifact or a deterministic whole-input transformation, a long-lived process by itself adds little architectural value; orchestration plus content-addressed caching may deliver most of the benefit with a smaller stateful surface.

### Kotlin makes generated semantic inputs part of the frontend contract

Generated inputs are where a file-only orchestration model most clearly stops being equivalent to a compiler-integrated one.

At the surface level, current `KaSymbol` documentation says symbols may originate in source, libraries, the compiler itself, or compiler plugins. `KaSymbolOrigin.PLUGIN` identifies a declaration generated by a compiler plugin. Such a declaration may have no ordinary source PSI at all. A tool that only watches files cannot infer the same semantic declaration merely from the absence or presence of generated source files.

Kotlin's current `KaResolveExtension` is an even more direct example. A resolve extension can provide generated Kotlin files that are included in resolution as if they were ordinary module source. The extension is created for an analysis session and disposed when that session is invalidated. If its generated contents become stale, it must publish an out-of-block module modification event. It may also provide a shadowed scope for files that an external build task would normally generate, specifically to prevent stale materialized generated files from colliding with the declarations supplied by the extension.

This mechanism deliberately combines three concerns that an external generator alone cannot safely combine:

1. **semantic participation** — the frontend knows that generated declarations belong in name/type resolution;
2. **lifetime and invalidation** — the generated view changes when its source inputs change; and
3. **collision policy** — the frontend can suppress stale on-disk counterparts rather than resolving both copies.

The design is also constrained for responsiveness: implementations are told to cache where useful, avoid eagerly constructing the whole file structure, and avoid invoking Kotlin resolution during analysis-session initialization.

**Basis: source.**

**Derived Anneal judgment.** Anneal should distinguish *materialized generated inputs* from *semantic extensions*. If Aeneas, Charon, Rust, or a proof elaborator emits ordinary files whose complete meaning is captured by those files, orchestration can generate, hash, version, and present them without requiring a resident service. If an upstream plugin changes resolution by synthesizing declarations or otherwise participating in semantic queries without a faithful standalone artifact, Anneal cannot reproduce that behavior with "run the generator first" unless the plugin also offers a semantics-preserving materialization. An interactive design must either invoke the plugin-aware frontend or explicitly reject/mark unsupported that semantic mode.

### SourceKit-LSP delegates build truth instead of absorbing it

SourceKit-LSP is a compiler-backed language server built on sourcekitd, but its current architecture intentionally leaves build-system knowledge outside the semantic service. A BSP server supplies target membership, sources, compiler options, index locations, and notifications when the build graph changes. The protocol permits the build server to respond quickly with an incomplete target set if expensive graph computation is still running, then issue `buildTarget/didChange` once the graph is available. This chooses responsiveness without pretending that provisional build state is final.

The split has several practical consequences.

First, compiler arguments are data with freshness semantics. Swift 5.7 release notes called out recomputation of compiler arguments after `Package.swift`, `compile_commands.json`, or `compile_flags.txt` changes so semantic operations would remain correct after configuration changes. The language service can persist across these changes; the configuration feeding it must still be refreshed.

Second, preparation is a build operation, not a pure semantic query. To support background indexing, a build server may have to prepare a target so generated products, dependency modules, or other build outputs exist. SourceKit-LSP requires preparation options to agree with the later semantic options. The current configuration surface still carries many build-context knobs—SwiftPM configuration, SDK/triple/toolsets, compiler flags, package-resolution policy, plugin sandboxing, and background preparation mode.

Third, SourceKit-LSP has explicit degradation and recovery behavior around the semantic backend. Current configuration includes a request timeout and a separate semantic-service restart timeout; if sourcekitd or clangd appears hung beyond the latter, SourceKit-LSP restarts it to restore semantic functionality. The 2019 sourcekitd stress-tester announcement gives historical context: the tester had already found 91 reproducible sourcekitd crashes, assertion failures, and hangs. Persistent compiler state improved latency and fidelity, but also introduced a stateful subsystem whose failures needed isolation and recovery.

**Basis: current source/documentation + historical first-party release/engineering reports.**

**Derived Anneal judgment.** Process isolation and restartability belong naturally to Anneal's orchestration layer even when semantic state belongs upstream. A service restart should discard performance state, not silently change semantic identity. Requests should carry enough context that the orchestrator can recreate a service and reconstruct the same semantic world. This mirrors SourceKit-LSP's architecture more closely than embedding mutable build discovery into the compiler service.

### Generated source and compiler-internal generated views deserve different treatment in Swift too

SourceKit-LSP's build interface represents source membership explicitly. For SwiftPM, build preparation can execute the build machinery that produces generated sources or modules before semantic indexing. Current SourceKit-LSP integration tests include SwiftPM build-tool plugin cases that generate Swift source, and the build-server protocol has an explicit `generated` property on source items.

At the same time, SourceKit-LSP has compiler-internal generated views such as generated interfaces and macro-expansion reference documents. Its configuration includes a `generatedFilesPath` for generated interfaces and macro expansions, but those views do not behave like ordinary project files; current language-service source notes that macro-expansion and generated-interface reference documents do not have ordinary document dependencies or build settings associated with their reference-document URI.

The distinction matters. A generated Swift file produced by a build-tool plugin is part of the build graph and can be named as a file input after preparation. A macro expansion is a compiler semantic product whose identity depends on the macro implementation, compiler invocation, source, and expansion context. Both may be persisted for inspection, but they enter authority through different boundaries.

**Basis: source + documentation.**

**Derived Anneal judgment.** Anneal's artifact model should record what generated output *is*: a build-generated source, a translation output, a proof elaboration product, an index/cache, or an explanatory view. Materialization alone does not make these categories interchangeable. For publication and verification acceptance, generated artifacts should be tied to the producer and input closure that gives them meaning; for live IDE views, ephemeral compiler-generated representations may remain advisory and recreatable.

### The historical migrations show that compiler sharing has a substantial integration price

JetBrains's K2 work was motivated by more than IDE latency. The 2021 project overview described goals of faster language-feature development, a unified architecture across Kotlin platforms, performance, and a compiler-extension API. By 2023 JetBrains described K2 as a from-scratch frontend architecture rather than a refactoring and said a new IDE plugin was being written on top of it. The subsequent K2 plugin migration required third-party IntelliJ plugins that depended on K1 internals such as descriptors, `BindingContext`, or `ResolutionFacade` to move to the Analysis API.

That cost is not incidental to the benefit. A compiler frontend designed to serve both compilation and interactive analysis needs stable semantic abstractions, lazy/incremental evaluation rules, lifetime discipline, and a public extension surface. Reusing an existing batch frontend before it has those properties can move complexity into every client instead of eliminating it.

Swift's history shows a similar split of responsibilities rather than a single monolithic compiler daemon. Sourcekitd was designed as a request/response service and acquired state-reuse mechanisms; SourceKit-LSP later became the editor-facing coordinator over sourcekitd plus build-system integration, indexing, and LSP. Swift 5.7 added the ability to manage multiple SwiftPM projects in one SourceKit-LSP instance and refresh compiler arguments after build-definition changes. The server process became longer-lived while its build contexts became more explicitly dynamic.

**Basis: historical first-party documentation + current architecture.**

A serious alternative for Anneal is therefore to avoid refactoring Charon/Aeneas into interactive services until measured workloads justify it. Batch tools with stable serialized boundaries are easier to pin, replay, parallelize, and validate. If a fresh translation can be generated quickly enough, content-addressed orchestration can avoid a large class of invalidation bugs. The Kotlin/Swift evidence supports upstream services when they unlock *frontend-native reuse or interaction*; it does not show that every transformation benefits from becoming a daemon.

### What orchestration can obtain without upstream changes

The Kotlin and Swift cases support a fairly strong positive account of orchestration. Without modifying a semantic engine, Anneal can own or improve all of the following when the underlying tools accept the resulting explicit inputs:

- toolchain/version selection and process lifecycle;
- build-subject discovery and configuration snapshots;
- environment variables, search paths, target triples, feature flags, and other invocation inputs;
- generated-file execution when the generator produces faithful ordinary artifacts;
- content-addressed caches of stable input/output artifacts;
- process isolation, timeouts, cancellation at process/request boundaries, and restart;
- scheduling and prioritization across independent subjects;
- mapping from editor requests to explicit semantic contexts;
- deduplication of identical contexts across clients;
- publication fences, validation, and exact accepted-result identity; and
- provenance that records which tool/configuration/input closure produced an artifact.

These are substantial. SourceKit-LSP's architecture is evidence that a compiler-backed interactive experience does not require the compiler service itself to own the build graph.

However, orchestration cannot in general create:

- a valid compiler-internal AST/FIR/elaboration state for a partially edited document;
- fine-grained dependency/invalidation knowledge that the upstream engine never exposes;
- a tactic state at an interior proof position;
- safe reuse of semantic objects across revisions when the upstream service gives no lifetime contract;
- synthetic/plugin declarations whose semantics are not faithfully materialized;
- editor-tolerant recovery semantics for incomplete code if the batch frontend rejects it before creating useful state; or
- query-specific lazy resolution that the batch interface always computes eagerly.

Trying to infer these from process outputs risks duplicating an upstream semantic engine in the orchestrator.

### Conditional architecture for Anneal

The strongest design suggested by the comparison is a layered one.

**1. Give every semantic request an explicit context identity.** The context should be sufficient to distinguish the Rust/Cargo subject, source snapshot, relevant generated inputs, selected toolchains/plugins, and translation/proof configuration. The exact fields remain an Anneal design question; the key property is that service-local mutable state does not decide which world a request means.

**2. Let upstream services own only state they are uniquely qualified to maintain.** Lean should own elaboration/tactic state if interactive proof queries require it. A future Charon/Aeneas service should own incremental translation state only if it can invalidate and reuse that state according to its semantics. Anneal should not mirror internal object graphs merely to keep them alive.

**3. Make service state disposable.** A service cache may improve latency, but a restart against the same explicit context should reconstruct equivalent semantics. If a service cannot do that, its hidden state has become part of the result's authority and must be modeled accordingly.

**4. Keep batch acceptance separate from advisory interaction unless equivalence is established.** Kotlin and SourceKit can give high-fidelity editor semantics while still depending on a separate build context; Kotlin's own IDE/compiler-version split shows why semantic sharing does not prove build equivalence. Anneal's ordinary success promise is stronger than an IDE hint. Interactive answers may be extremely useful without acquiring verification-success authority.

**5. Treat generated declarations according to their semantic mechanism.** Ordinary generated files can be orchestrated. Compiler/plugin semantic extensions require either the real extension-capable frontend or a proven faithful materialization. Ephemeral generated views should not silently become accepted source inputs.

**6. Make configuration changes first-class invalidations.** SourceKit-LSP's compiler-argument refresh and Kotlin's module-scoped invalidation both show that source text is not the only invalidation key. An Anneal service must invalidate or select a new context when build flags, dependencies, toolchain pins, plugins, or generated-input producers change.

This architecture leaves room for a direct Lean LSP/MCP path without committing every Anneal stage to daemonization. It also leaves room for later upstream work: if profiling shows that Charon or Aeneas dominates interactive latency and repeated invocations discard reusable internal state, the Kotlin/Swift pattern supplies a criterion for adding a service—expose stable semantic query boundaries, explicit context/lifetime rules, and deterministic invalidation, rather than merely putting the batch command behind a socket.

## Boundaries

**Not examined:** No Kotlin compiler, Analysis API, sourcekitd, or SourceKit-LSP binary was executed for this report. No latency, memory, cache-hit, or incremental-rebuild benchmark was reproduced.

**Not examined:** This report does not attempt a complete history of K2, FIR, SourceKit, SourceKit-LSP, SwiftPM, or either project's plugin ecosystem. It selects mechanisms directly relevant to J016.

**Unknown:** The public evidence reviewed here does not establish a universal latency threshold at which a persistent compiler service becomes preferable to batch orchestration. That decision depends on workload, invalidation frequency, startup cost, cacheability, concurrency, and failure isolation.

**Known not to follow:** A compiler-backed IDE does not imply that IDE analysis uses the exact compiler binary/version/configuration that a subsequent build uses. Kotlin explicitly documents a separate IDE frontend copy and build-selected compiler version.

**Known not to follow:** Keeping a semantic process alive does not by itself make reuse correct. Kotlin requires session/lifetime/invalidation contracts; SourceKit conditions AST reuse on compatible source snapshots.

**Known not to follow:** Materializing a generated file is not always semantically equivalent to running a compiler plugin. Kotlin exposes plugin-generated symbols and resolve extensions precisely because some generated semantic declarations participate inside resolution.

**Unsupported generalization:** `KaResolveExtension` is an Analysis API mechanism, not evidence that every Kotlin compiler plugin can be converted to a resolve extension or that every plugin semantic effect can be materialized as files.

**Unsupported generalization:** SourceKit-LSP's build-tool/plugin support does not establish that every arbitrary Swift/Xcode build-system plugin or generated input is discoverable through every SourceKit-LSP workspace mode. The report's claim is about the architectural boundary and the current SwiftPM/BSP mechanisms examined.

**Evidence limitation:** JetBrains and Swift project blogs are first-party historical accounts, but they remain author reports rather than controlled experiments. The source evidence is stronger for current mechanism; the blogs are used to recover motivation, transition cost, and reported outcomes.

**Anneal scope:** The recommended separation between context authority, service-local cache state, and batch acceptance is derived from these cases and Anneal's existing design contract. It is not an adopted project decision, and it does not settle the atomic verification subject, generated-artifact format, or exact process/API boundary.

## Evidence

### Kotlin current source

`JetBrains/kotlin@bce49f3701fb8dc461fb98240fdc7c3c81c592f2`

- `analysis/analysis-api/src/org/jetbrains/kotlin/analysis/api/KaSession.kt` — session lifetime, use-site context, non-leakage rules, and pointer-based transfer of symbols/types between analysis calls.
- `analysis/analysis-api/src/org/jetbrains/kotlin/analysis/api/projectStructure/KaModule.kt` — module-supplied project structure, resolution scope, dependency kinds, language settings, and module-level invalidation.
- `analysis/analysis-api-fir/src/org/jetbrains/kotlin/analysis/api/fir/KaFirSessionProvider.kt` — cached FIR-backed sessions, validity checks, low-memory cleanup, and invalidation coupling to underlying FIR sessions.
- `compiler/fir/checkers/module.md` — CLI whole-project resolution versus IDE lazy resolution, minimum-phase symbol access, and checker constraints required by partial resolution.
- `analysis/analysis-api/src/org/jetbrains/kotlin/analysis/api/resolve/extensions/KaResolveExtension.kt` — generated declarations/files, session lifetime, modification publication, lazy construction guidance, and shadowing of stale external generated sources.
- `analysis/analysis-api/src/org/jetbrains/kotlin/analysis/api/symbols/KaSymbol.kt` — semantic declarations from source, libraries, compiler synthesis, and compiler plugins.

Observed 2026-09-30.

### Kotlin historical and public design documentation

- JetBrains, "The Road to the K2 Compiler," 2021: https://blog.jetbrains.com/kotlin/2021/10/the-road-to-the-k2-compiler/ — stated goals of performance, cross-platform unification, faster language evolution, and compiler-extension APIs.
- Roman Elizarov / JetBrains, "The K2 Compiler Is Going Stable in Kotlin 2.0," 2023: https://blog.jetbrains.com/kotlin/2023/02/k2-kotlin-2-0/ — from-scratch frontend architecture, continuous IDE use of the frontend, and distinction between the IDE-bundled frontend and build-selected compiler.
- Kotlin Analysis API documentation, observed 2026-09-30: https://kotlin.github.io/analysis-api/index_md.html — Analysis API as compiler-backed semantic layer, lazy resolution/cache invalidation, IntelliJ use, and current Standalone-mode qualification.
- Kotlin Analysis API, "Migrating from K1," observed 2026-09-30: https://kotlin.github.io/analysis-api/migrating-from-k1.html — Analysis API lifetime discipline and historical `BindingContext` misuse as a source of exceptions, incorrect behavior, and leaks.
- Kotlin Analysis API `KaSymbol` documentation, observed 2026-09-30: https://kotlin.github.io/analysis-api/kasymbol.html — compiler/plugin symbol origins.

### Swift current source and documentation

`swiftlang/sourcekit-lsp@045c18e9e9ea35b896857b6cb982aa2373fb5816`

- `README.md` — SourceKit-LSP as an LSP layer over sourcekitd/clangd and the dependence of cross-module/global features on index/module preparation.
- `Contributor Documentation/Implementing a BSP server.md` — external build-server responsibilities for targets, sources, SourceKit options, change notifications, index locations, and target preparation; requirement that preparation and semantic options agree.
- `Documentation/Configuration File.md` — build-context options, generated-interface/macro path, background preparation, semantic request timeout, and semantic-service restart timeout.
- `Sources/BuildServerIntegration/SwiftPMBuildServer.swift` and `Tests/SourceKitLSPTests/SwiftPMIntegrationTests.swift` — current SwiftPM/build-tool plugin integration and generated-source test coverage.
- `Sources/SwiftLanguageService/SwiftLanguageService.swift` — generated-interface and macro-expansion reference documents as semantic reference documents rather than ordinary project documents.

`swiftlang/swift@f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d`

- `tools/SourceKit/lib/SwiftLang/SwiftASTManager.h` and `.cpp` — AST producers/consumers and snapshot-qualified reuse.
- `tools/SourceKit/lib/SwiftLang/SwiftSourceDocInfo.cpp` — request-specific acceptance of reusable AST state.
- `test/SourceKit/CursorInfo/cursor_reuses_astcontext.swift` — regression test that expects AST-context reuse on repeated cursor requests.

Observed 2026-09-30.

### Swift historical first-party evidence

- Nathan Hawes, Swift.org, "Introducing the sourcekitd Stress Tester," 2019-02-06: https://www.swift.org/blog/sourcekitd-stress-tester/ — sourcekitd's service/request-response role and 91 reproducible crashes, assertion failures, or hangs found by the then-new stress testing.
- Swift.org, "Swift 5.7 Released!", 2022: https://www.swift.org/blog/swift-5.7-released/ — SourceKit-LSP recomputation of compiler arguments after build-definition changes and support for multiple SwiftPM projects in one server instance.
- Swift compiler architecture documentation, observed 2026-09-30: https://www.swift.org/documentation/swift-compiler/ — compiler frontend as the semantic base for IDE functions.

### Anneal authority used for derived implications

`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`

- `anneal/PRINCIPLES.md` — verification success must not fail open; ordinary interface is Rust-oriented; trust is explicit.
- `anneal/DESIGN.md` — successful results require precise identity/scope, incomplete work must remain distinguishable from success, and the boundary among Anneal/Rust/Charon/Aeneas/Lean plus treatment of generated artifacts remain deliberate non-decisions.

Observed 2026-09-30.

## Revalidation

For a newer Kotlin revision, recheck five narrow regions before carrying the conclusions forward:

1. `KaSession` lifetime and cross-session pointer rules;
2. `KaModule` ownership of project structure and modification/invalidation semantics;
3. `KaFirSessionProvider` or its successor for session reuse/invalidation;
4. FIR IDE lazy-resolution rules; and
5. `KaResolveExtension` plus plugin-generated symbol support.

If those still establish platform-supplied project structure, frontend-owned lazy/reusable state, explicit invalidation, and semantic generated-declaration support, the central orchestration-versus-upstream distinction remains supported. If Standalone becomes a mutable long-lived platform with a different lifetime model, re-evaluate the claim that the current API's interactive advantages depend primarily on IntelliJ platform integration.

For a newer SourceKit-LSP/Swift revision, recheck:

1. the BSP/build-server contract for targets, sources, compiler options, and preparation;
2. sourcekitd AST/elaboration reuse keyed to text/source state;
3. how generated build-tool sources and macro/generated-interface documents enter the semantic model;
4. whether semantic-service restart remains a supported recovery mechanism; and
5. whether SourceKit-LSP has moved build-graph authority into sourcekitd or kept it outside.

A cheap discriminating probe, if execution is available, is to modify only build configuration (not source text) and verify that semantic compiler arguments/context change; then edit a single open source buffer and observe whether a second semantic query reuses frontend state only when the service considers the relevant snapshots compatible. Those two probes test the report's central separation between external context authority and internal reusable semantic state without requiring a full IDE benchmark.

For Anneal, re-read `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` before applying the derived architecture. In particular, if later design work chooses an atomic result subject, generated-artifact model, or interactive/batch equivalence rule, those decisions may narrow or supersede the conditional recommendations here even if the Kotlin and Swift evidence remains unchanged.