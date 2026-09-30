# HIE, ghcide, and Haskell Language Server: environment and incremental-state boundaries

## Summary

The Haskell IDE lineage is most useful as a decomposition-and-recombination case study, not as a story in which one implementation simply replaced another. The archived Haskell IDE Engine (HIE) combined a rich plugin surface with a mutable GHC/ghc-mod session, serialized plugin execution, cached last-good typechecked modules, and substantial installation and project-configuration machinery. `ghcide` separated several of those concerns: `hie-bios` supplied project/compiler context, a dependency graph governed incremental semantic work, LSP transport was a separate library, and feature integrations could remain plugins. Haskell Language Server (HLS) then combined the `ghcide` core with HIE's plugin, packaging, and editor-integration experience. The maintainers who announced the consolidation described complementary strengths and limited contributor capacity; the public record does not justify attributing the consolidation to one architectural cause.

The strongest durable boundary is the **project environment**, not the editor workspace. `hie-bios` states the governing rule directly: the build tool is responsible for describing the environment in which a package should be built. A file is analyzed with GHC flags, package databases, component membership, language extensions, and a compatible GHC version. HIE and `ghcide` both exposed costs when that context was guessed or duplicated: version-specific binaries, explicit `hie.yaml` mappings, multi-component edge cases, and direct GHC-argument configurations that the `hie-bios` documentation warns can drift from the build description. The lesson is not that an IDE must invoke a particular build tool. It is that editor analysis needs an explicit, versioned compiler context whose authority is traceable to the build configuration.

The incremental engine changed while the boundary survived. `ghcide` used Shake-style rules to model parsing, typechecking, dependencies, invalidation, diagnostics, and editor-triggered recomputation. Current HLS says its `hls-graph` is a purpose-built in-memory reimplementation that replaced Shake, dropped persistence, kept dynamic dependencies, and added reactive change tracking for minimal rebuilds. That history separates a reusable idea—explicit dependency/invalidation structure—from a particular general-purpose engine. It also gives a serious alternative to both extremes of "make every editor query a fresh compiler run" and "make the editor cache the authority."

For Anneal, the conditional judgment is therefore layered. Keep batch verification authoritative over an explicit source/toolchain/project identity. Let an interactive engine reuse and incrementally invalidate expensive intermediate results, but identify every answer with the environment and source generation that produced it and fail closed when that identity cannot be reconstructed. Ask upstream build/configuration layers for compiler context rather than maintaining a second hand-written model of it. Keep protocol and plugin conveniences outside the acceptance boundary. If a general incremental engine expresses the needed dependencies cleanly, use it until measured workload or semantic constraints justify specialization; the Shake-to-`hls-graph` transition is a precedent for preserving the dependency model while changing the engine, not evidence that Anneal should copy either implementation.

## Applicability

This report addresses J014 in `google/zerocopy#3732`: the HIE, `ghcide`, and Haskell Language Server lineage, with emphasis on GHC API use, incremental dependency tracking, project environments, plugin integration, abandoned approaches, and the cost of keeping editor analysis aligned with the build.

The implementation observations are pinned to four Git revisions listed in `REPORT.json`:

- HIE archive `d84b84322ccac81bf4963983d55cc4e6e98ad418`;
- `ghcide` archive `3ef4ef99c4b9cde867d29180c32586947df64b9e`;
- HLS `187fcd4a685c220caabb72999565604b3287aff2`;
- `hie-bios` `32dd07707423ffabb34e44af68fcbd027b60ded2`.

The first two repositories explicitly describe themselves as historical artifacts. Their archived heads are useful end-state records of the old designs, but they do not date every intermediate transition. Current HLS is used to establish the surviving component structure and `hls-graph` design as observed on 2026-09-30. `hie-bios` is examined independently because both the archived `ghcide` documentation and HIE project-configuration documentation delegate environment setup to it.

Two maintainer essays are used as historical accounts: Neil Mitchell's 2020 announcement that the HIE and `ghcide` teams planned to join forces, and his later recommendation to use HLS rather than `ghcide` directly. Those sources report participant intent and experience. They are not independent evaluations, controlled performance studies, or proof that one technical decision caused HLS to succeed.

The Anneal conclusions are **derived** from those mechanisms and boundaries. They do not assert that Anneal already implements an HLS-like graph, that Haskell's GHC-version coupling matches Rust/Charon/Aeneas/Lean coupling exactly, or that an editor result can stand in for Anneal's batch verification result.

## Findings

### The lineage changed where state lived, not the need for exact compiler context

HIE's archived architecture centers plugin work in a mutable `IdeState` layered on `ghc-mod`. LSP mode used separate input, message, dispatcher, and output threads, but GHC-session limitations restricted plugin requests in `IdeM` to one thread. On each open or edit HIE tried to obtain a GHC `TypecheckedModule`. A successful result became the file's `CachedModule`; if the current text failed to compile, HIE could keep the previous successful module and map positions between the current document and that last-good state. Unsaved buffers were represented through `ghc-mod` mapped temporary files. Plugin-specific cached data was tied to the cached module and invalidated when a new typechecked module arrived.

That design had an important user-facing benefit: queries could remain useful while the current buffer was temporarily ill-typed. It also created state questions that are easy to miss if "the compiler" is treated as a single oracle. A query could be based on a previous successful typecheck rather than the current text. A queued request could be rejected as stale or cancelled before it started, but the single-threaded dispatcher could not cancel an already-running request. Source positions for unsaved text needed explicit old/new mappings and temporary-file reverse mappings. These behaviors were deliberate mechanisms for an interactive workload, not batch compiler semantics.

**Basis: source + documentation.** HIE's archived `docs/Architecture.md` defines the four-thread layout, serialized `IdeM` execution, `CachedModule` behavior, position mappings, mapped-file handling, cache invalidation, and cancellation limitation. The archived README describes HIE as an LSP "universal interface" to multiple Haskell tools and documents installation/project setup across multiple GHC versions.

`ghcide` moved the center of gravity from a mutable per-module cache exposed to plugins toward an explicit incremental dependency graph. Its archived README describes a layered architecture: `hie-bios` determines files, dependencies, extensions, and compiler setup; `ghcide` decides how and when to typecheck and produces diagnostics; plugins provide optional features; and an LSP library transports results to editors. The source organized semantic computations as typed rules whose dependencies can be invalidated and recomputed. The public architecture account describes editor buffers as graph inputs and parsing/typechecking as rules that depend on those inputs and on other modules.

This did not remove compiler-context coupling. The archived README warns that `ghcide` must be compiled with the same GHC as the project. Multi-component projects could require an explicit `hie.yaml`; cross-component features depended on which components had been loaded; and a three-component dependency pattern could produce inconsistent interface behavior when an intermediate component was not loaded. The graph made dependencies explicit, but it did not make the surrounding build context optional.

**Basis: documentation + source.** The mechanism is supported by the archived `ghcide` README and the rule-oriented `Development.IDE.Core` source. The account of why Shake was attractive is also present in the contemporary maintainer article "Shaking up the IDE"; that article is treated as author rationale, not as an external benchmark.

### `hie-bios` made build configuration an interface rather than duplicated IDE policy

`hie-bios` states a narrow design principle: **the build tool is responsible for describing the environment in which a package should be built**. It then asks for the GHC flags needed to establish a GHC API session. Those flags can come from Cabal, Stack, an arbitrary "bios" program, or a direct list. A multi-cradle maps source paths to components when a workspace contains several components with different dependencies.

This is an architectural boundary, not merely a configuration-file feature. The IDE does not need to understand every build tool's internal model if it can obtain the compiler arguments that define the semantic environment. Conversely, a bare filesystem path does not identify a unique analysis subject: component choice affects dependencies and flags, and the same workspace may require several component-specific contexts.

The direct-cradle alternative makes the cost visible. `hie-bios` calls a literal GHC-argument list useful for debugging but a poor general approach because it quickly gets out of sync with the Cabal file. Automatic project discovery has the opposite tradeoff: it reduces manual duplication, but its correctness and latency depend on the build tool exposing enough information and successfully preparing dependencies. Explicit multi-cradles improve determinism when discovery is insufficient, at the cost of maintaining another mapping.

The archived `ghcide` README reports exactly this pressure: users got better multi-component results from a manually specified `hie.yaml` until Cabal and Stack exposed better interfaces. That is not evidence that manual configuration is intrinsically superior. It is evidence that **the quality of the build/editor boundary constrains the quality of editor semantics**.

**Basis: documentation.** `hie-bios` documents the design principle, compiler-flag contract, multi-cradle mapping, and direct-cradle drift warning; `ghcide` documents the corresponding multi-component limitations.

For Anneal, the analogous rule is derived: do not make an editor workspace, open file, or hand-maintained adapter configuration the sole identity of a verification subject. An interactive request should resolve to an explicit source revision/content generation plus the Cargo/Charon/Aeneas/Lean configuration needed to give that source meaning. If the build-derived environment cannot be resolved unambiguously, declining the semantic query is safer than silently analyzing a plausible but different subject.

### The incremental model survived replacement of the incremental engine

The current HLS repository contains `hls-graph`, whose README calls it a limited reimplementation of Shake for in-memory build graphs. It says `ghcide` was originally built on Shake and that HLS later replaced Shake with this special-purpose engine. The documented trade is unusually clear:

- retained: dynamic dependencies, user-defined rules, build reports, and reactive change tracking for minimal rebuilds;
- added relative to the old use of Shake: a reactive change mechanism specialized for the IDE workload;
- deliberately omitted: persistence, default filesystem-build rules, a general-purpose application model, and other Shake generality;
- motivation stated by the project: simplicity and performance.

The current HLS source still expresses compiler work as rules over keys and values and performs parsing, module-summary, dependency, and typechecking work through that graph. The mechanism therefore outlived its original engine: the stable architectural unit was the dependency/invalidation model, not Shake itself.

**Basis: documentation + source.** The replacement and its stated tradeoffs come from the pinned HLS `hls-graph/README.md`. The current `ghcide/src/Development/IDE/Core/Rules.hs` shows the surviving rule-based compiler-service structure.

There are two serious alternatives worth keeping explicit.

1. **Fresh compiler work for each query.** This minimizes hidden cache state and makes freshness easier to reason about, but repeats parsing/typechecking and makes low-latency editor feedback expensive. It can remain appropriate for authoritative batch acceptance.
2. **A general persistent incremental engine.** This can reuse mature dependency and persistence machinery, but carries behavior and abstractions that may not match an editor's invalidation model. HLS eventually chose a narrower in-memory engine.
3. **A purpose-built in-memory graph.** This can encode the actual editor workload and discard unneeded generality, but its invalidation, equality, cancellation, and graph-lifetime rules become project-specific correctness concerns.

The HLS history does not establish a universal ordering among these options. It does establish that an architecture can preserve explicit dependency structure while changing the engine after the workload is better understood.

For Anneal, this supports an incremental adoption strategy: define subject identity, dependency edges, and invalidation semantics first; keep authoritative acceptance independently reproducible; then choose or specialize the execution engine based on measured cost. A specialized live engine should not acquire stronger semantic authority merely because it is faster.

### HLS was a recombination of complementary assets, not a clean technical succession

The archived `ghcide` README records that the HIE and `ghcide` teams agreed to join under HLS. It says the likely model was `ghcide` as the core while plugins and integrations lived in HLS. It also credits HIE's ecosystem libraries—`hie-bios`, the LSP library, and LSP testing—and GHC changes that enabled editor buffers to be analyzed without ordinary on-disk files.

Neil Mitchell's January 2020 consolidation announcement is even more explicit about the rationale. It identifies HIE's strengths as its mature plugin set, build/install scripts across compiler configurations, accumulated LSP/editor liveness knowledge, and GHC API work. It identifies `ghcide`'s strengths as the Shake-backed state model, a simpler programming model, and a way to break apart GHC work sufficiently to reuse interface files and support several components in one session. It also names finite contributor capacity as a reason to stop splitting work across two servers.

That evidence rules out a simplistic conclusion such as "Shake won" or "HIE's plugin architecture failed." The merger plan was to combine the parts each project did better. By September 2020 the same maintainer recommended HLS rather than running `ghcide` directly, describing HLS as `ghcide`-based core plus plugins and installer work inherited from HIE. This is a reported outcome from a participant, not a controlled comparison.

**Basis: documentation + historical maintainer account.** Repository documentation establishes the resulting project relationship; the blog posts establish stated participant rationale and later experience. No independent causal attribution is made.

For Anneal, the derived lesson is organizational as well as technical: a successful integration boundary may deliberately combine an upstream semantic core with locally specialized packaging, projection, or user-facing layers. Reuse should be evaluated per responsibility. "Use upstream" does not require one upstream to own every layer, and "write a local adapter" does not justify duplicating upstream semantic logic.

### Plugin richness belongs outside the acceptance boundary

HIE's original goal was to expose many Haskell tools through one LSP server. Its architecture gave plugins direct access to cached GHC-derived state and allowed plugins to cache additional data alongside a `TypecheckedModule`. HLS preserves an end-user language-server layer above the compiler-service core and continues to ship feature plugins.

This decomposition is useful, but it creates a trust distinction. Hover, navigation, refactoring, formatting, linting, and code actions can improve the editing loop even when they are computed from cached, partial, last-good, or plugin-specific state. A verifier's acceptance result has a different contract: it must identify the exact source and environment whose claim was checked.

**Basis: source + documentation + derived.** HIE/HLS establish that rich plugin behavior can be layered around compiler-derived state. The requirement that Anneal not promote that state to authoritative acceptance follows from Anneal's own fail-closed and explicit-trust principles, not from an HLS claim.

A practical Anneal split is therefore:

| Responsibility | Suitable live behavior | Authority |
| --- | --- | --- |
| Project/subject resolution | Resolve source to explicit build/toolchain/proof context; reject ambiguity | Input identity for later work |
| Incremental analysis | Cache parsing, translation, imported facts, diagnostics, goals; invalidate by dependency | Advisory unless rechecked |
| Editor/protocol features | Project diagnostics, navigation, code actions, progress, cancellation | Convenience layer |
| Batch acceptance | Reconstruct declared environment and run the authoritative verification criterion | Decides success |
| Publication | Bind accepted result to source, toolchain, generated artifacts, and generation identity | Durable effect after validation |

The table is a **derived Anneal model**, not an HLS API map. Its purpose is to preserve the useful separation demonstrated by the Haskell lineage without importing Haskell-specific assumptions about GHC sessions or plugins.

### Configuration drift is a semantic risk, while cache staleness is only one instance of it

It is tempting to reduce IDE correctness to cache invalidation. The Haskell history shows a broader problem. A perfectly invalidated graph can still analyze the wrong thing if it was initialized with the wrong component, package database, flags, compiler version, or project environment. Conversely, a correctly identified environment can still return stale results if the graph does not invalidate the relevant dependency.

These are separate failure classes:

1. **Subject-resolution error:** the system maps a file/request to the wrong build component or compiler environment.
2. **Dependency-model error:** the right subject is selected, but a semantic input is missing from the graph.
3. **Invalidation error:** the dependency is modeled, but a change does not retire affected results.
4. **Scheduling/cancellation error:** obsolete work completes and is mistaken for a current answer.
5. **Authority error:** a valid live answer is treated as equivalent to the batch acceptance criterion when the two contracts differ.

HIE's last-good module and serialized-request behavior illustrate (3) and (4). `hie-bios` and `ghcide` multi-component limitations illustrate (1). Shake/`hls-graph` illustrate attempts to structure (2) and (3). The editor-versus-batch distinction is the report's **derived** response to (5).

For Anneal, these categories suggest separate identities rather than one opaque "workspace version": source generation, compilation/proof subject, prepared environment/toolchain, incremental graph generation, and authoritative acceptance result. Combining them into one hash is possible, but the components should remain recoverable so a future agent can tell which boundary changed.

### Conditional judgment for Anneal

The Haskell lineage supports the following design only under stated conditions.

**Use build-derived environment descriptions.** If Anneal can obtain the effective Cargo/Charon/Aeneas/Lean context from authoritative upstream configuration, prefer that over reconstructing an independent editor-only model. Any local normalization should be deterministic and recorded. This applies most strongly when one Rust file can participate in several build subjects or feature selections.

**Keep live state generation-fenced.** Every cached semantic result should be tied to the source and environment generation that created it. Cancellation is useful for latency but is not a correctness proof; a stale computation may still finish. The consumer must reject answers whose generation no longer matches the request.

**Keep batch acceptance reproducible and separately authoritative.** Incremental results may answer "what is likely true for the current editor state?" The acceptance path must answer "what exact subject was verified under what exact toolchain/environment?" If those paths share libraries or artifacts, record that sharing; do not infer equivalence from implementation reuse.

**Specialize the incremental engine only after the dependency contract is explicit.** HLS could replace Shake with `hls-graph` while preserving the rule/dependency model. Anneal should likewise avoid coupling its semantic identities to one cache framework. A general engine is a reasonable starting point when it faithfully represents the graph; a purpose-built engine is justified when measured latency, memory, cancellation, or invalidation behavior requires it.

**Put plugin/protocol features above stable semantic facts.** Editor features may evolve faster than the verifier. An adapter should project from versioned semantic results into LSP/MCP/editor actions rather than making protocol state the canonical proof state. Code actions that would mutate source should carry an explicit source-generation precondition and be rejected if their ownership or freshness is ambiguous.

**Do not infer a single cause from HLS consolidation.** The primary record attributes the merger to both complementary engineering assets and finite contributor capacity. The safe generalization is modular: preserve good boundaries and combine proven responsibilities where they fit. It is not "copy ghcide" or "replace all batch work with a graph."

These are **derived conditional recommendations**, not adopted Anneal policy.

## Boundaries

- **No execution study.** No HIE, `ghcide`, HLS, GHC, Cabal, Stack, or `hie-bios` binary was run for this report. Performance, memory use, latency, cancellation behavior, and multi-component failure rates were not benchmarked.
- **Historical heads are not timelines.** The HIE and `ghcide` repositories now identify themselves as historical artifacts. Their pinned archive heads reliably preserve documented mechanisms, but this report did not bisect Git history to assign every mechanism an introduction/removal date.
- **Maintainer accounts are participant evidence.** The 2019/2020 architecture and consolidation essays explain rationale and reported experience. They are not independent studies and do not prove that a specific design decision caused adoption or project success.
- **No universal claim about Shake or `hls-graph`.** HLS documents that `hls-graph` replaced Shake for simplicity/performance and dropped persistence. The report does not quantify that improvement, claim Shake was incorrect, or claim a purpose-built graph is always preferable.
- **No claim that HLS editor answers equal GHC batch acceptance.** The report deliberately separates interactive usefulness from authoritative acceptance; it did not construct a current HLS-versus-GHC semantic-differential test.
- **GHC-version coupling is not mechanically transferred to Anneal.** Haskell's requirement that server/compiler builds match is evidence that compiler-internal APIs can create version boundaries. The exact Rust/Charon/Aeneas/Lean compatibility relation must be established from those tools' own pins and interfaces.
- **Project consolidation has multiple plausible causes.** The public record explicitly mentions complementary project strengths and contributor economics. Any stronger claim that architecture alone drove consolidation is unsupported here.
- **Adjacent `reference` reports remain distinct.** The current corpus contains detailed Lean LSP, source-projection, project-routing, and upstream-API precedents, including `anneal-3730-upstream-api-projection-precedents-2026-09-29`. They support nearby editor-boundary questions but do not reconstruct the HIE/`ghcide`/HLS history or the build-environment boundary examined here.

## Evidence

The machine-readable source inventory and claim-role mapping is preserved in `source-map.json`. `lineage-matrix.json` preserves the report's cross-project mechanism comparison separately from prose.

Primary source observations acquired or revalidated on 2026-09-30:

- **HIE architecture.** `haskell/haskell-ide-engine` at `d84b84322ccac81bf4963983d55cc4e6e98ad418`, `docs/Architecture.md`, especially "Overall Architecture", "Plugins and the IdeM Monad", "Dispatcher and messaging", and "Deferred requests". Immutable URL: <https://github.com/haskell/haskell-ide-engine/blob/d84b84322ccac81bf4963983d55cc4e6e98ad418/docs/Architecture.md>. Basis: **source documentation**.
- **HIE project/configuration surface.** Same revision, `README.md`, especially the deprecation notice, Features, Installation, and Project Configuration. Immutable URL: <https://github.com/haskell/haskell-ide-engine/blob/d84b84322ccac81bf4963983d55cc4e6e98ad418/README.md>. Basis: **documentation**.
- **`ghcide` decomposition and history.** `haskell/ghcide` at `3ef4ef99c4b9cde867d29180c32586947df64b9e`, `README.md`, especially the opening component decomposition, "Limitations to Multi-Component support", "Using it", and "History and relationship to other Haskell IDE's". Immutable URL: <https://github.com/haskell/ghcide/blob/3ef4ef99c4b9cde867d29180c32586947df64b9e/README.md>. Basis: **documentation / maintainer history**.
- **`hie-bios` environment contract.** `haskell/hie-bios` at `32dd07707423ffabb34e44af68fcbd027b60ded2`, `README.md`, especially the opening design principle, Stack/Cabal component mappings, Bios, Direct, and Multi-Cradle sections. Immutable URL: <https://github.com/haskell/hie-bios/blob/32dd07707423ffabb34e44af68fcbd027b60ded2/README.md>. Basis: **documentation**.
- **Current HLS incremental engine.** `haskell/haskell-language-server` at `187fcd4a685c220caabb72999565604b3287aff2`, `hls-graph/README.md`. Immutable URL: <https://github.com/haskell/haskell-language-server/blob/187fcd4a685c220caabb72999565604b3287aff2/hls-graph/README.md>. Basis: **documentation**.
- **Current HLS rule implementation.** Same revision, `ghcide/src/Development/IDE/Core/Rules.hs`, inspected for the surviving key/rule-based compiler-service structure and dependency traversal. Immutable URL: <https://github.com/haskell/haskell-language-server/blob/187fcd4a685c220caabb72999565604b3287aff2/ghcide/src/Development/IDE/Core/Rules.hs>. Basis: **source**.
- **Current HLS project structure.** Same revision, repository `README.md` and `cabal.project`; the latter includes the root server, `hls-graph`, `ghcide`, plugin API, and test-support packages. Immutable URLs: <https://github.com/haskell/haskell-language-server/blob/187fcd4a685c220caabb72999565604b3287aff2/README.md> and <https://github.com/haskell/haskell-language-server/blob/187fcd4a685c220caabb72999565604b3287aff2/cabal.project>. Basis: **source/documentation**.

Historical rationale:

- Neil Mitchell, "Shaking up the IDE" (2019), <https://4ta.uk/p/shaking-up-the-ide>. The article describes the DAML/Haskell IDE Core motivation for using Shake rules to model editor inputs and compiler stages. Basis: **maintainer rationale**; no immutable source revision was available for the article.
- Neil Mitchell, "One Haskell IDE to rule them all" (2020-01-27), <https://neilmitchell.blogspot.com/2020/01/one-haskell-ide-to-rule-them-all.html>. The post describes the HIE/`ghcide` consolidation plan, complementary strengths, and contributor-capacity rationale. Basis: **maintainer historical account**.
- Neil Mitchell, "Don't use Ghcide anymore (directly)" (2020-09-22), in the September 2020 archive at <https://neilmitchell.blogspot.com/2020/09/>. The post recommends HLS as the end-user combination after the planned consolidation. Basis: **maintainer reported outcome**.

No source above is treated as a normative language or compiler specification. This report reconstructs software architecture and project rationale, so implementation source and maintainer documentation are the strongest available evidence for most claims.

## Revalidation

For a later HLS revision, the cheapest discriminating revalidation is:

1. Read `cabal.project` or the current package manifest and confirm whether `ghcide`, `hls-graph`, the plugin API, and server packages remain distinct components.
2. Read `hls-graph/README.md` and the graph implementation. Check whether it still omits persistence, supports dynamic dependencies/reactive invalidation, and remains the engine used by the compiler-service rules.
3. Read the current `ghcide`/core rule implementation around parsing, module summaries, dependency discovery, and typechecking. Confirm that the observable semantic pipeline is still graph-keyed rather than relying on the old HIE mutable `CachedModule` model.
4. Read the current `hie-bios` README and the HLS cradle-loading code. Confirm who owns build-context discovery, whether source-to-component mapping can still be ambiguous, and what compiler-version constraints remain.
5. If Anneal wants to depend on a stronger claim—such as "live HLS results are equivalent to a fresh GHC build for configuration X"—do not infer it from this report. Construct a differential execution test under exact build flags and compiler/package identities.
6. If the question is historical rather than current, inspect the commits/PRs that introduced `ghcide`, HLS consolidation, and `hls-graph` rather than relying on archive-head documentation to date transitions.

For Anneal itself, revalidate the derived judgment whenever the accepted batch contract, project-subject identity, or interactive engine changes. The narrow check is whether a live answer can still be traced to exact source and prepared-environment generations and whether the batch acceptance path can still reproduce the declared subject independently of editor cache state. If either answer is no, the Haskell precedent does not justify treating the live path as authoritative.