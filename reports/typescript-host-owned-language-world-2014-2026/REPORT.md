# TypeScript's host-owned world around shared language machinery

## Summary

TypeScript's language-service architecture is a useful precedent for Anneal because it does **not** make the compiler or language service the authority for the whole world around a query. The reusable semantic machinery owns parsing, binding, type analysis, and editor operations over the state it is given. A host supplies the project's files, versions, snapshots, compiler options, filesystem semantics, module-resolution inputs, cancellation, and related environment facts. `ProjectService` then adds another substantial layer that tracks open editor buffers, configured, inferred, and externally supplied projects, config-file discovery, watchers, and version history.

That split bought TypeScript two important properties. First, the same compiler machinery could serve a one-shot compiler, long-lived editor services, and incremental watch/build workflows without forcing those workflows to have one state lifecycle. Second, the editor could operate on client-owned text that is newer than disk while still reusing compiler semantics. The price is that consistency obligations move into the host and project-service layers. The host must say which files exist, which bytes are current, which project they belong to, and which configuration and dependency world those bytes should be interpreted against. A narrow semantic API therefore reduces duplication of language semantics; it does not eliminate the need for an authoritative world model.

The historical record reinforces that distinction. TypeScript 6.0.2 exposes the mature JavaScript implementation's programmatic language-service API. TypeScript 7.0, released on 2026-07-08 as a Go port intended to preserve TypeScript 6's checking behavior, deliberately shipped **without** a stable programmatic API; the TypeScript team told API-dependent tools to keep using the 6.0 API side-by-side and expected a new, different API in 7.1. Semantic compatibility and integration-surface compatibility are therefore separate properties even within one project.

For Anneal, the conditional judgment is to prefer a narrow reusable semantic core only when its host contract makes all meaning-bearing inputs explicit. Anneal should retain authority for source/model/environment identity, project selection, generated-artifact generations, lifecycle, and publication fences. A long-lived Charon, Aeneas, Lean, or future semantic service may cache and evaluate an explicit context, but it should not silently decide what "the current project" or "the current verified result" means. If a host cannot enumerate and invalidate the state that affects semantics, the abstraction has merely hidden the consistency problem behind an adapter.

## Applicability

The mature API/source observations in this report apply to `microsoft/TypeScript@607a22a90d1a5a1b507ce01bb8cd7ec020f954e7`, the `v6.0.2` release commit. This revision is useful because TypeScript 6 is the last release line based on the JavaScript implementation whose programmatic compiler and language-service APIs are the subject of the historical architecture.

The language-service rationale also uses `microsoft/TypeScript-wiki@966988bcca7c835fd22ab066bb6a9ff4d5ba511d`, especially `Using-the-Language-Service-API.md`. That document describes the language service as a long-lived compilation context, explains on-demand phase separation, assigns file monitoring and maintenance to the host, describes immutable script snapshots and incremental change ranges, and explains document-registry sharing across project services.

The TypeScript 7 transition evidence comes from first-party TypeScript team announcements dated 2025-03-11, 2026-03-23, and 2026-07-08. The 7.0 release announcement is especially useful because it records both intended semantic compatibility with TypeScript 6 and the absence of a stable programmatic API in 7.0. Performance numbers in those announcements are author-reported and are not used here to predict Anneal performance.

The Anneal judgment is derived against `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Current `reference` already contains `anneal-3730-architecture-contracts-2026-09-29`, which cites TypeScript as a broad precedent for host-managed files and versioned snapshots. This report is narrower and deeper: it reconstructs where authority actually sits, the cost of the host abstraction, and what the 6-to-7 transition says about relying on a shared compiler API. The conclusions are analysis for issue #3732 J011, not adopted Anneal policy.

## Findings

### The language service was designed as a semantic engine over host-supplied state

The TypeScript language-service design guide states two central goals: compute only the semantic phase needed for a query, and decouple compiler phases that a command-line compilation would normally run in sequence. A syntax-diagnostics request can stop after parsing one file; a completion request can resolve only what it needs; an emit request can target one file. This is not merely a caching optimization. It changes who drives the pipeline: the host can ask for selected semantic work in an order suited to an editor rather than replaying the command-line compiler's whole lifecycle.

The same guide is explicit about the boundary. `LanguageServiceHost` abstracts interactions between the service and the external world. The host, not the service, manages, monitors, and maintains input files. The host supplies the full file set for the context and may interpose on reference resolution. The language service asks synchronously for facts when it needs them rather than independently watching the world in the background.

This split is attractive for Anneal for the same reason: semantic machinery can be reused without giving it ownership of every source of mutable truth. But the useful abstraction is not "a compiler library." It is "a semantic evaluator over a host-defined world." The host contract is part of the semantics whenever file selection, configuration, or external state changes what a query means.

Basis: TypeScript language-service design guide + TypeScript 6.0.2 `LanguageServiceHost` source + derived Anneal comparison.

### `ScriptSnapshot` gives text a stable local identity, not a complete project identity

At TypeScript 6.0.2, `IScriptSnapshot` is documented as an immutable snapshot of a script at a specified time. Its observable text is stable, and it may describe the change range from an older snapshot so incremental parsing can reuse unaffected structure. `LanguageServiceHost` separately supplies `getScriptVersion(fileName)` and `getScriptSnapshot(fileName)`. `createLanguageServiceSourceFile` stores the supplied version and snapshot on the source file, and update logic uses a change range to decide whether incremental parsing is possible.

This is a clean division: a snapshot answers "what are the bytes for this script state?" and a version tells the host and service that a named script has advanced. Neither fact says that the file belongs to the right project, was interpreted with the right compiler options, saw the right dependencies, or corresponds to the bytes on disk.

For Anneal, a document or source snapshot should be treated the same way. Stable text is one coordinate of a verification request, not the whole request identity. Tool versions, translation/model configuration, dependency closure, generated proof environment, trusted assumptions, and requested property remain separate. A versioned editor buffer cannot by itself justify a batch verification result.

Basis: `src/services/types.ts` and `src/services/services.ts` at TypeScript 6.0.2 + Anneal design contract + derived comparison.

### The host interface is deliberately broad because semantics depend on more than text

TypeScript 6.0.2's `LanguageServiceHost` asks for substantially more than file contents. It includes compilation settings, project version, script file names and kinds, project references, current directory, default library location/name, case-sensitivity policy, filesystem existence and reads, directory enumeration and realpath when available, cancellation, and hooks for module/type resolution and other environment-sensitive operations.

That breadth is evidence against a tempting but weak interpretation of "narrow semantic core." The semantic implementation can be narrow in *responsibility* while its input contract remains wide enough to name the world that affects meaning. If the adapter omits a meaning-bearing input, the core cannot repair the omission.

There are two serious alternatives. One is to let the semantic service discover its own files, configuration, and environment. That reduces host plumbing but creates a second authority whose view can diverge from orchestration. The other is to require a completely materialized immutable input closure for every request. That makes authority clearer but may be expensive or awkward for low-latency editing. TypeScript chooses an intermediate host protocol: the service asks the host for authoritative facts as needed, while the host bears the consistency obligation.

For Anneal, this suggests a design test rather than a predetermined API shape: every fact that can change proof meaning must either be carried in an immutable request/environment identity or be supplied through an explicitly versioned host capability whose changes invalidate dependent semantic state.

Basis: TypeScript 6.0.2 `LanguageServiceHost` + derived alternative analysis.

### `ProjectService` shows that "the host" becomes a real subsystem, not a thin adapter

TypeScript's server layer makes the cost of that split concrete. At 6.0.2, `ProjectService` owns a document registry; maps file names to `ScriptInfo`; retains version information for deleted script infos so recreated files do not accidentally reuse a version for different contents; tracks open files; caches config-file relationships; and maintains external, inferred, and configured projects.

Those project kinds encode distinct authorities. External projects have roots and configuration controlled outside `tsserver`. Inferred projects are built from open-file roots. Configured projects are defined by `tsconfig.json`. Config-file existence and parsed configuration are cached and watched because a newly appearing or changing config file can move an open file between project worlds. The service also manages filesystem watchers and resolution invalidation.

The editor-buffer boundary is equally explicit. `openClientFile` accepts file content described as a known version that can be more up to date than the copy on disk. The semantic world for an open document therefore cannot be reconstructed from pathname plus filesystem state.

This is the central cost result for J011: a host-owned architecture does not remove state; it gives state a named owner. The architecture succeeds only if that owner is sufficiently complete and disciplined. For Anneal, an "adapter" that owns source generations, Cargo/model selection, generated Lean package identity, open-document text, watchers, and backend lifecycle is architectural infrastructure and should be designed and tested as such.

Basis: TypeScript 6.0.2 `src/server/editorServices.ts` + derived Anneal application.

### Watch/build is a separate state machine over the same compiler machinery

The TypeScript watch API demonstrates a second host-shaped lifecycle. `WatchHost` supplies file and directory watch operations and optional timer scheduling. `WatchCompilerHost` combines watch behavior with the program host. `createWatchProgram` tracks a builder program, update level, missing-file watchers, wildcard-directory watchers, stale watches, parsed configurations, and delayed recompilation state.

The watch path therefore shares parsing/checking/emission machinery with ordinary compilation, but it does not get freshness "for free" from that sharing. It has its own invalidation rules and event sources. Builder programs deliberately cache work and update only what they believe is affected.

This distinction matters for Anneal's batch/live relationship. Sharing a translator or proof engine can reduce duplicated semantics, but the live path still needs an explicit invalidation model. The authoritative batch path may use a closed captured input set while the live path consumes watcher events and editor generations. Reusing implementation does not make those two state machines equivalent.

A useful acceptance rule is therefore semantic rather than topological: for one explicit verification-input identity, live and batch paths should agree on accepted meaning. The mechanisms used to reach that state may differ.

Basis: TypeScript 6.0.2 `src/compiler/watchPublic.ts` + existing Anneal architecture-contract evidence + derived comparison.

### Generated output remains an artifact boundary rather than invisible semantic state

TypeScript's language-service API exposes `getEmitOutput`, including declaration-only emission, while compiler/watch hosts expose output-writing hooks. The language-service design guide likewise notes that one file may be emitted without running a full-program batch pipeline.

That capability is useful, but it introduces a boundary between an in-memory semantic snapshot and externally consumed generated artifacts. The source that a downstream project or tool consumes may be an emitted `.d.ts` rather than the source document currently open in an editor. `ProjectService` source-mapping and project-reference logic contains explicit cases where a location may remain in a declaration file rather than redirect to source, depending on project availability and configuration.

The safe inference is modest: generated declarations have their own production and consumption lifecycle. An editor service that can emit a declaration is not proof that every downstream consumer has advanced to that declaration generation. Anneal has an analogous boundary between generated model/proof files and the state of a long-lived proof worker. Publication and import identity must be explicit rather than inferred from "the service just generated it."

Basis: TypeScript 6.0.2 language-service emit API, watch-host output interface, and `ProjectService` project-reference/source-mapping paths + derived Anneal application.

### The 6-to-7 transition separates semantic compatibility from API compatibility

The TypeScript team's native-port history is unusually valuable because it changes the implementation and integration surface while explicitly trying to preserve language semantics.

On 2025-03-11, the team announced a Go port of the compiler and tools. The stated goal was to port the current codebase and preserve behavior while using native code and shared-memory parallelism; the team separately called out a future compiler API. TypeScript 6.0, released on 2026-03-23, was described as the last release based on the JavaScript codebase and a transition release for TypeScript 7.

TypeScript 7.0, released on 2026-07-08, is the native port. Its release announcement states that 7.0 aims to be compatible with TypeScript 6.0 checking and command-line behavior. Yet 7.0 does not ship a stable programmatic API. The team recommends running 7.0's compiler alongside the TypeScript 6.0 API for tools that need programmatic compiler access, and says 7.1 is expected to ship a new and different API. Embedded-language workflows are called out as a case that may need to remain on 6.0 until that surface exists.

This is a concrete negative result for architectural planning: "we share the compiler" is not a durable interface contract. Even when upstream preserves language behavior, its embeddability, object model, threading model, and lifecycle API can change independently.

For Anneal, upstream library integration should therefore be treated as a replaceable adapter, not as the identity of the verification architecture. A process protocol or host abstraction may survive an upstream rewrite more easily than an intimate in-process dependency; conversely, a stable upstream library API may offer performance and richer incremental state. The right boundary depends on measured benefit and explicit lifecycle contracts, not on an assumption that a compiler's internal API is permanent.

Basis: TypeScript team 2025 native-port announcement, TypeScript 6.0 release announcement, TypeScript 7.0 release announcement + derived Anneal implication.

### A host-owned world supports editor flexibility but creates three consistency joins

TypeScript's architecture exposes three joins that an Anneal host would also need to make explicit.

The first is **buffer-to-project**: which versioned source bytes belong to which configuration/project graph? An open editor buffer may be newer than disk, while config discovery can move it between inferred and configured projects.

The second is **project-to-environment**: which filesystem, module/dependency, options, generated outputs, plugins, and tool identities define the semantic world? The host and project service answer these questions through filesystem, resolution, configuration, and project APIs.

The third is **semantic-state-to-publication**: which result is still current when asynchronous or incremental work finishes? TypeScript's service APIs provide versioned inputs and project update machinery, but Anneal's stronger verification promise requires an explicit acceptance fence tying a successful result to the exact source/model/environment identity being published.

These joins are where a vague "thin adapter" would fail. The adapter can remain conceptually narrow only if it carries concrete identities and invalidation rules for each join.

Basis: synthesis of TypeScript 6.0.2 source and Anneal's current verification-result identity requirements.

### TypeScript supports a conditional host/core split for Anneal, not a blanket endorsement

The strongest transferable pattern is:

1. keep semantic algorithms behind a reusable service boundary;
2. let a host own changing external state;
3. represent per-document text as immutable/versioned snapshots;
4. make project/configuration discovery a first-class state machine;
5. keep watch/build invalidation separate from one-shot semantics; and
6. treat generated output and publication as explicit artifact boundaries.

For Anneal, that pattern is appropriate if the host can name every meaning-bearing input and can invalidate or reconstruct dependent backend state. It is especially attractive for live feedback, where open buffers and incremental work matter.

It is insufficient if a backend reads ambient process state, hidden global configuration, uncontrolled filesystem paths, mutable plugins, or generated artifacts outside the host's authority. In that case the host API gives a false appearance of completeness. The safer baseline remains a fresh, fully specified request whose successful result is fenced to an explicit identity; a persistent service is an optimization over that contract.

This leads to a practical architecture criterion: Anneal should be able to reconstruct an authoritative batch request from durable identities without consulting opaque daemon memory. A long-lived semantic service may accelerate that request or provide best-effort live queries, but cache contents and "current project" pointers should not be the sole evidence behind a published verification result.

Basis: TypeScript architecture + current Anneal principles/design + adjacent architecture-contract report + derived conditional judgment.

## Boundaries

- No TypeScript compiler, language server, editor, or watch build was executed for this report. Mechanism claims come from first-party documentation and pinned source; performance claims from TypeScript announcements are not independently reproduced.
- TypeScript 6.0.2 is used for the mature JavaScript API because TypeScript 7.0 intentionally does not ship that stable API. The report does not assume the future 7.1 API will reproduce 6.0's object model.
- TypeScript 7.0 performance and stability numbers are first-party reported outcomes. They support the motivation for the native port, not a quantitative prediction for Anneal.
- The report does not establish a complete causal commit history of `LanguageServiceHost`, `ProjectService`, or watch mode. It reconstructs durable design roles from the language-service guide, the mature 6.0.2 implementation, and first-party transition announcements.
- `ScriptSnapshot` immutability is local to text observed through that snapshot. It does not imply an immutable project, filesystem, compiler configuration, dependency graph, plugin set, or output world.
- The existence of host methods does not prove every external influence is captured correctly by every TypeScript embedding. Soundness of a particular host implementation remains separate.
- `ProjectService` is evidence about `tsserver`'s host/project model, not a requirement that Anneal implement equivalent project kinds or filesystem watchers.
- Generated-declaration analysis is limited to the public emit surface, host output boundary, and project-reference/source-mapping behavior. No end-to-end generated-`.d.ts` synchronization experiment was run.
- The report does not claim that process boundaries are always preferable to library integration. It treats them as a conservative reconstruction/reset boundary when upstream lifecycle or hidden-state contracts are insufficiently explicit.
- Anneal implications are derived analysis under current project authority, not adopted design policy.
- Candidate-only status outside the native reference branch means this report does not establish J011 coverage until a later fenced run acquires J011 and explicitly revalidates/adjudicates the salvage under normal coordination.

## Evidence

### TypeScript language-service design guide

**Repository:** `microsoft/TypeScript-wiki@966988bcca7c835fd22ab066bb6a9ff4d5ba511d`.

- `Using-the-Language-Service-API.md`, blob `c3584b2b433dd304216e0affe3302a56a2ace681`: describes the language service as a long-lived program/compilation context; states on-demand processing and decoupling of compiler phases as design goals; assigns file management/monitoring to `LanguageServiceHost`; defines `ScriptSnapshot` as point-in-time text plus change-range information; explains host-controlled reference resolution and `DocumentRegistry` sharing across project services.

Role: **first-party design documentation** for intended language-service responsibilities. It explains design intent and documented mechanism; it is not an execution result.

### TypeScript 6.0.2 source

**Repository:** `microsoft/TypeScript@607a22a90d1a5a1b507ce01bb8cd7ec020f954e7` (`v6.0.2`).

- `src/services/types.ts`, blob `5329fe901b2403fad070e2fdb3b61212102e7c57`: `IScriptSnapshot`, `LanguageServiceHost`, language-service emit API. Establishes observable snapshot immutability, version/snapshot host hooks, compilation/project/filesystem inputs, and declaration-capable emit surface.
- `src/services/services.ts`, blob `9885093ed618047cfebad26ac731032cd7071ab6`: language-service source-file creation/update from supplied snapshots, versions, and change ranges.
- `src/server/editorServices.ts`, blob `aa578c7ed0815f064b88eda052c7d8ac9029558f`: `ProjectService` ownership of script infos, retained versions, open files, inferred/configured/external projects, config discovery/cache/watch state, and `openClientFile` handling of client content newer than disk.
- `src/compiler/watchPublic.ts`, blob `4bcedabb7eb0f4d168a2f6b43a54cadd924a1eb5`: watch/program host contracts, filesystem watchers, timer hooks, output hook, project/config inputs, and `createWatchProgram`'s mutable incremental state.
- `src/compiler/builder.ts`, blob `34adf6e49b7daa33c0b9d65bb3675cfde7a8b85b`: builder-program implementation context for incremental build reuse.

Role: **immutable source evidence** for the mature pre-native architecture. No source execution was performed.

### TypeScript native-port transition

**First-party TypeScript team publications:**

- Anders Hejlsberg, *A 10x Faster TypeScript*, 2025-03-11: `https://devblogs.microsoft.com/typescript/typescript-native-port/`. Announces a Go port of the compiler/toolset, describes preservation of the current codebase's behavior as a goal, and separately identifies a future compiler API.
- Daniel Rosenwasser, *Announcing TypeScript 6.0*, 2026-03-23: `https://devblogs.microsoft.com/typescript/announcing-typescript-6-0/`. Describes 6.0 as the last release based on the JavaScript codebase and a transition to the native implementation.
- Daniel Rosenwasser, *Announcing TypeScript 7.0*, 2026-07-08: `https://devblogs.microsoft.com/typescript/announcing-typescript-7-0/`. States 7.0 compatibility goals relative to 6.0, records that 7.0 ships without a stable programmatic API, recommends side-by-side 6.0 API use for API-dependent tools, and expects a new/different API in 7.1.

Role: **first-party historical intent and reported outcome** for the implementation/API transition. Performance figures are author-reported, not independently validated here.

### Anneal authority

**Repository:** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: fail-closed verification promise and explicit trusted-assumption accounting.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: successful-result identity/scope, evidence-bounded claims, Rust/model correspondence, and deliberate non-selection of lower-level integration mechanisms.

Role: **project authority** constraining the derived Anneal judgment.

### Adjacent current reference evidence

Observed on current `reference` during this candidate-only run:

- `reports/anneal-3730-architecture-contracts-2026-09-29/REPORT.md`, blob `d532b9fe321f547efe355a9044b707a06727ed65`: broad language-tooling precedents, explicit batch/live semantic contract, and process-topology adoption gates.
- `reports/anneal-3730-rust-input-snapshot-2026-09-29/REPORT.md`, blob `8d1ca9ff320e216be72abbca267c4372fcb8d0e1`: concrete Rust/Cargo input-snapshot evidence relevant to what an Anneal host may need to identify.

Role: **existing Anneal corpus evidence**. The present report adds the J011 historical/host-cost judgment rather than replacing those execution-grounded reports.

## Revalidation

For TypeScript 6.x, first verify the exact source revision still matters to the question. If the concern is the mature pre-native API, reread `LanguageServiceHost`, `IScriptSnapshot`, `ProjectService`, and `WatchHost`/`createWatchProgram` at the selected 6.x tag. The discriminating questions are whether the host still owns text/version/project/filesystem/configuration facts, whether open-client text can diverge from disk, and whether watch/build still has a separate invalidation state machine.

For TypeScript 7+, do not project the 6.0 programmatic object model forward. Check the current stable TypeScript release and its programmatic API status. If 7.1 or later has shipped an API, compare its host/state boundaries directly against the 6.0 model and record which responsibilities moved, disappeared, or became protocol-level LSP concerns. Keep semantic compatibility claims separate from API/lifecycle compatibility.

For Anneal, revalidate the current authoritative source/model/environment identity contract and the actual lifecycle of each backend. A useful host-boundary experiment should inject independently changing inputs: editor bytes, on-disk bytes, Cargo/model configuration, generated proof artifacts, tool/plugin versions, and backend restarts. For each mutation, show which generation or host field changes, which caches invalidate, and whether batch and live acceptance converge on the same explicitly named input identity.

A proposed persistent backend should also pass A/B/A and cross-project tests: load context A, switch to B, return to A, and verify that results either match a fresh reconstruction or are rejected as stale. Kill/restart the backend and reconstruct from durable request identities. If any correctness-relevant state exists only inside the service and cannot be reconstructed or named by the host, treat that state as part of the trusted architecture rather than as an invisible cache.