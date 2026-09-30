# clangd authority and freshness: incomplete code, preambles, indexing, and scheduling

## Summary

clangd does not converge on one global notion of “ready.” Its mature architecture assigns different freshness and authority rules to different operations. The compile command determines which language and build model the parser is approximating; a fallback command is explicitly unreliable. A normal AST request is fenced to the document version tracked when the request was scheduled. Code completion deliberately uses a fresh parse of the current incomplete buffer with a potentially stale—or, in one mode, absent—preamble because latency dominates. Diagnostics are generated from Clang parsing, but the scheduler may satisfy the normal policy with either the requested snapshot or a subsequent one, while an explicit mode can require diagnostics for exactly the requested snapshot. Cross-file queries combine a dynamic index for open files with background, static, or remote indexes that trade freshness for coverage and resource use. The current source and design documents encode these differences directly.

That outcome was not accidental drift. From 2017 through 2023, clangd repeatedly made freshness, memory, CPU, and responsiveness tradeoffs explicit. Reviewers made in-memory preambles optional after observing roughly doubled memory in an early comparison. Background indexing moved to low-priority worker threads after discussion of foreground interference. Cancellation work allowed obsolete reads and intermediate diagnostic builds to disappear instead of forcing every version to complete. A later change invalidated editor-generated requests on subsequent edits to avoid building snapshots whose results had already become less useful. In 2023, maintainers accepted asynchronous preamble indexing with a documented temporary reduction in result freshness because much of the index-consuming feature set already tolerated stale information.

The defensible Anneal lesson is therefore narrower than “copy clangd.” Anneal should expose operation-specific authority rather than one global readiness bit. Completion-like suggestions, navigation, speculative indexing, cache warming, and other advisory views may use a declared older or incomplete generation when their consumers can tolerate that. Any result that authorizes generated artifacts, Charon/Aeneas translation, proof acceptance, refactoring edits, or publication should instead be tied to an exact source snapshot *and* an exact semantic model: Cargo subject/build configuration, tool revisions, generated inputs, and proof environment as applicable. A current buffer parsed under guessed configuration is fresh but not authoritative; an authoritative model paired with an old buffer is authoritative for the wrong snapshot. Freshness and model authority are independent axes.

clangd also warns against equating “compiler-backed” with “the command-line build accepted this program.” It reuses Clang, but editor diagnostics can be skipped for intermediate versions, use a guessed compile command, and intentionally omit some analysis for responsiveness. clangd does not perform the build’s code-generation step. For Anneal, the batch acceptance path should remain the oracle unless and until a live path carries an explicit equivalence contract and evidence. The useful precedent is the separation of service levels, not the claim that an interactive frontend is itself an acceptance oracle.

## Applicability

This report answers #3732 J012: reconstruct clangd’s compilation-database, preamble, background-index, and AST-scheduling decisions; distinguish approximate navigation from compiler-backed diagnostics and code generation; and judge which Anneal operations may be best-effort versus exact.

Current implementation claims refer to `llvm/llvm-project@ded546ad82656ce6605ee2f2aa60c78dec70d95f`, observed 2026-09-30. Current design-documentation claims refer to `llvm/clangd-www@ae5866d4552e30a173b8e9c3cec872a82e4c0120`. Historical changes are pinned individually in `REPORT.json`. The old LLVM Phabricator pages preserve author/reviewer rationale for those changes; those comments are evidence about stated intent and design judgment, not controlled measurements.

The report does not execute clangd. It reconstructs the architecture from current source, current project documentation, landed commit history, and selected review discussions. It therefore establishes control-flow and contract facts more strongly than performance facts. Where a review reports a local or production measurement, this report preserves it as a reported observation and does not generalize it to Anneal.

The existing `anneal-3730-architecture-contracts-2026-09-29` report cites clangd among several language-tooling precedents. That package establishes a broad batch/live contract and a small topology experiment. It does not reconstruct clangd’s historical consistency choices or adjudicate J012’s operation-specific freshness question. This report is complementary rather than a replacement.

## Findings

### clangd has several authority domains, not a single readiness state

The current design separates at least four states that a single “ready” flag would conflate:

1. **Document snapshot.** `TUScheduler::runWithAST` promises that the AST delivered to a request corresponds to the version tracked when the request was made, even if later edits arrive before the callback runs. Some requests may instead be invalidated by a later update.
2. **Preamble freshness.** `runWithPreamble` explicitly permits a preamble built from an older file version. Callers either validate that the preamble remains suitable or knowingly accept that it may be outdated.
3. **Project/build model.** `GlobalCompilationDatabase` supplies the compile command that determines language mode, target, include paths, macros, and other parser semantics. When it cannot supply a known-good command, its fallback command is explicitly documented as unreliable.
4. **Cross-file index coverage.** The merged index combines data with different lifetimes and update schedules. Open-file data can be refreshed quickly while the background or remote corpus remains older.

These states can disagree in useful, intentional ways. Code completion may prefer current buffer text plus an old preamble. A definition query may use a current open-file AST plus an older project index. Diagnostics may describe a newer buffer than an earlier intermediate edit because that intermediate build was elided. None of these situations means the entire server is simply “not ready.”

The important negative result is that the architecture does not support the implication

`latest source text observed -> all semantic dependencies and project-wide data are equally fresh`.

It instead makes enough provenance and scheduling distinctions for each caller to choose a useful service level.

**Evidence.** `clang-tools-extra/clangd/TUScheduler.h` at the current pinned LLVM revision, especially `runWithAST`, `PreambleConsistency`, `WantDiagnostics`, and `ASTActionInvalidation`; `llvm/clangd-www/design/threads.md` and `design/indexing.md` at the pinned documentation revision.

### The compilation database is part of semantic identity, not incidental setup

clangd cannot interpret a C or C++ source file from bytes alone. Its design documentation treats the virtual compile command as parser configuration: language dialect, target, include paths, defines, warnings, and related options can all change the meaning or parsability of the same bytes. `GlobalCompilationDatabase::getCompileCommand` returns a known-good command when available. If it cannot, `getFallbackCommand` synthesizes a command roughly equivalent to invoking Clang on the file, and the current source says clangd should treat the result as unreliable.

Headers make the boundary more obvious. The documented strategy may borrow a command from a translation unit that included the header or infer a likely command from filename similarity. That produces a useful editing experience without proving that the selected command is the one a particular build subject will use.

This yields a distinction that matters directly to Anneal:

- **snapshot freshness** asks whether the analysis consumed the intended source bytes;
- **model authority** asks whether it consumed the intended build/configuration subject.

A result can satisfy one without the other. A current Rust file analyzed under the wrong Cargo subject or feature set has the same category error as a current C++ header analyzed under the wrong compile command.

The closest Anneal analogue is not merely Cargo metadata availability. The semantic model can include target/features, build-script and generated inputs, selected Charon/Aeneas revisions and options, and the Lean import environment. Those identities should be part of the authority witness for operations that affect acceptance or publication.

**Evidence.** `clang-tools-extra/clangd/GlobalCompilationDatabase.h`, symbols `GlobalCompilationDatabase::getCompileCommand`, `getFallbackCommand`, and `DirectoryBasedGlobalCompilationDatabase`; `llvm/clangd-www/design/compile-commands.md`.

### Preambles are a latency cache with explicit staleness semantics

Clang can split the leading include-heavy region of a translation unit into a preamble. clangd exploits that because rebuilding the preamble can be much more expensive than rebuilding the main-file AST. Current `design/threads.md` describes the preamble as an immutable reusable object once built.

The critical point is that reuse is not hidden behind a fiction of perfect freshness. Current `TUScheduler::PreambleConsistency` has modes that explicitly permit an older preamble, and `ClangdServer::codeComplete` says it uses a potentially stale preamble because latency is critical. Code completion also does not reuse the ordinary AST: incomplete code is a special case, so clangd runs a fresh parse with Clang’s completion API and an injected completion token. The operation therefore combines a current ephemeral parse with a possibly old preamble.

Signature help makes a slightly different trade. It waits for a preamble to exist, but it also permits a stale preamble. This is an example of two superficially similar interactive features choosing different readiness requirements without requiring a server-wide state transition.

The historical path reinforces that this is a resource decision as well as a correctness decision. In D39843 (landed as `e9eb7f0cb815641827fa3d031c38190c10900c14` on 2017-11-16), an early proposal to make in-memory preambles the default was changed after the author reported that the implementation consumed almost twice the memory in a local comparison. Reviewers argued that RAM pressure could be more harmful than slower disk-backed reuse and asked for measurement before changing the default. The landed change made storage configurable and kept on-disk storage as the default at that point.

That episode does not establish a timeless optimal storage policy; current clangd has evolved substantially. It does establish a design habit: reusable compiler state was treated as a cache with explicit resource costs, not as sacred global state that had to be retained at any cost.

**Evidence.** Current `TUScheduler.h`, `ClangdServer.cpp::codeComplete`, and `llvm/clangd-www/design/threads.md`; historical D39843 and landed commit `e9eb7f0cb815641827fa3d031c38190c10900c14`.

### AST scheduling preserves exact request snapshots selectively, while obsolete work is disposable

`runWithAST` provides a strong local guarantee: the AST belongs to the file version tracked when the request was scheduled. This is stronger than “whatever is current when the worker happens to run.” It gives request handlers a stable snapshot even under concurrent edits.

clangd does not infer from that guarantee that every scheduled snapshot must be constructed. Two historical changes made this explicit.

D54746, landed as `a2b048bc4bdf9320249d0ff512fab6f16c2e6e47` in November 2018, taught `TUScheduler` to respect task cancellation. Cancelled reads do not run, and they stop keeping earlier updates alive. A cancelled update that had demanded diagnostics can be downgraded to the ordinary eventual diagnostic policy, permitting the scheduler to elide it when later writes make it unnecessary.

D75602, landed as `c627b120eb8b7add3f9cf893721335c367d9f037` in March 2020, added invalidation for operations whose value drops sharply after a new edit. The stated motivation was to avoid building many snapshots that nobody still needed, especially for requests automatically generated by editors rather than explicit user actions. The current `ASTActionInvalidation` interface retains this distinction.

These mechanisms separate two concepts that are easy to collapse:

- If a request **does run**, the snapshot passed to it is well-defined.
- The system may decide that an obsolete request **should not run at all**.

For Anneal, this is a useful model for cancellation. A proof-context lookup for version `v` should never silently execute against `v+1` and label the answer as `v`; but a lookup for `v` may be cancelled when `v+1` arrives if nobody still needs it. Exact identity does not imply mandatory completion.

**Evidence.** Current `TUScheduler.h`; D54746 / commit `a2b048bc4bdf9320249d0ff512fab6f16c2e6e47`; D75602 / commit `c627b120eb8b7add3f9cf893721335c367d9f037`.

### Diagnostics are compiler-derived but normally eventual, and are not build acceptance

`WantDiagnostics` exposes a three-way policy in current source:

- `Yes`: diagnostics must be generated for this snapshot;
- `No`: they must not be generated for this snapshot;
- `Auto`: diagnostics must be generated for this snapshot *or a subsequent one* within a bounded amount of time.

clangd’s protocol extension exposes the same idea to clients. This is a direct counterexample to a global rule that every visible edit requires a completed diagnostic pass before the server is ready. Intermediate diagnostics are intentionally droppable when they would soon be obsolete.

Yet even `Yes` is not equivalent to “the project’s command-line compiler accepted this build.” It requests the clangd diagnostic pass for an exact document snapshot. Authority still depends on the selected compile command and clangd’s analysis strategy. The clangd FAQ documents a responsiveness optimization that can skip bodies of functions defined in included headers, which can produce false or missing diagnostics compared with a more complete analysis. Wrong compile commands can also generate spurious diagnostics.

clangd is therefore “compiler-backed” in an important sense—it uses the Clang parser and semantic machinery—but its editor diagnostic contract is not identical to the build system’s compile-and-codegen contract. clangd itself is not the project code-generation oracle.

For Anneal, the analogous separation should be explicit:

- a live diagnostic may report that an annotation or generated proof fragment currently appears invalid under the live service’s model;
- an acceptance result should certify that the exact intended source/model/environment was processed by the authoritative pipeline and that all required stages succeeded;
- a live “no diagnostics” result should not by itself authorize publishing generated artifacts or declaring a Rust-level verification obligation discharged.

**Evidence.** Current `TUScheduler.h::WantDiagnostics`; clangd protocol extension documentation for `wantDiagnostics`; clangd FAQ sections on false/missing diagnostics and compile-command problems.

### The index is intentionally layered: active-file freshness can coexist with stale global coverage

clangd’s current index design combines multiple sources through `MergedIndex`.

The dynamic `FileIndex` is the highest-priority layer. It contains symbols from open files and their preambles. The design documentation gives two freshness-oriented reasons for this layer: cross-references for active files should be available before the background index finishes, and locations for actively edited definitions/references should not remain stale.

The `BackgroundIndex` has a different goal: whole-project coverage. When a compilation database is discovered, translation units are queued and indexed in the background; shards are cached on disk to avoid full re-indexing on restart. Static and remote indexes move more work out of the interactive process. Remote-index documentation explicitly describes the offline index as periodically produced and therefore slightly stale.

This is not a compromise hidden behind one abstract `Index` interface. The interface allows feature code to query a merged view while the implementation deliberately combines data with different update policies. The dynamic layer repairs the most user-visible staleness without requiring the entire project corpus to reach the same generation before navigation can proceed.

The history again shows resource pressure shaping the boundary. In D53651, landed as `6675be87477395658f6d3859b028ab8dee81ba19` in October 2018, maintainers debated how a background-index thread pool could hurt foreground latency. The chosen direction used LLVM’s thread pool and lowered priorities for background work rather than making indexing coequal with foreground AST tasks. That is a scheduling-policy judgment, not merely an implementation convenience.

The resulting lesson for Anneal is to avoid a project-global barrier for advisory indexes and caches. A source-to-proof symbol map, search index, or cached navigation aid can be useful while incomplete, provided the response carries enough generation/model identity for the caller to interpret it. The same latitude does not apply to a proof acceptance result that will be published as current.

**Evidence.** `llvm/clangd-www/design/indexing.md`; current `clang-tools-extra/clangd/index/FileIndex.cpp` and `index/Background.cpp`; remote-index design documentation; D53651 / commit `6675be87477395658f6d3859b028ab8dee81ba19`.

### Asynchronous preamble indexing made the freshness trade explicit

The 2023 D148088 discussion is especially useful because it exposed a choice that an interface abstraction could otherwise hide. The proposal moved preamble indexing out of document-open’s critical path. Reviewers initially warned that preamble indexing populated data needed by code completion, diagnostics, and rename, so asynchronous execution could change early results.

The maintainers then separated features by what they already tolerated. One review account observed that nearly all index-using features already assume a stale index. Code completion was the most exposed because it depends on the preamble index for declarations not deserialized into the main AST; until indexing completed, results could be partial or fall back to older global-index data. The same discussion explicitly characterized the change as trading some freshness for substantial latency savings. The landed commit is `a8ad413f0d18c07a4adaa0d547e0096874d809c5`.

The reported measurements in that review are not reproduced here and should not be treated as universal performance facts. What is robust is the design decision: maintainers considered temporary partial/stale results acceptable for some interactive features, while carefully preserving object lifetime and ordering constraints needed for safe asynchronous indexing.

This provides stronger support for J012 than a generic claim that “IDEs are eventually consistent.” It identifies *which kind* of state became eventual: auxiliary index information feeding features that already tolerated staleness. It did not make the source snapshot passed to a running AST request ambiguous.

**Evidence.** D148088 and landed commit `a8ad413f0d18c07a4adaa0d547e0096874d809c5`; current `UpdateIndexCallbacks` and `FileIndex` source.

### The historical direction is operation-specific consistency, not progressively weaker consistency

It would be easy to tell a one-direction story in which clangd began strict and relaxed consistency for performance. The evidence does not support that simplification.

Some mechanisms are intentionally weaker than a full rebuild: stale preambles, eventual diagnostics, asynchronous/background indexes, and cancellation of obsolete work. Other mechanisms are deliberately strong: reads are associated with the expected document version; publication callbacks guard against close/reopen races; dynamic index layers replace stale active-file locations; compile commands are treated as semantically consequential; races between index rebuilds discard older versions.

The architecture is better understood as placing strong invariants exactly where ambiguous identity would make results unusable, while allowing staleness where it can be surfaced or repaired cheaply.

The current `ParsingCallbacks::onMainAST` contract is illustrative. Results published from a built AST are wrapped so clients see them in the correct sequence across concurrent close/reopen actions. This is a publication-order fence around a system that otherwise aggressively overlaps and elides work.

Anneal should preserve that distinction. “Best effort” should mean a weaker *freshness or coverage guarantee that is named in the result contract*, not permission to mislabel a result’s source/model identity or to publish an old result as current.

### Serious alternatives and why the evidence disfavors them for Anneal

#### One global exact-ready barrier

A simple architecture could define one project generation and answer no request until source, generated artifacts, proof environment, indexes, and all upstream stages have caught up.

This gives a compact mental model, but clangd’s history shows why it is expensive for an interactive system. Preamble work can dominate latency; whole-project indexing is resource-intensive; intermediate edits often become obsolete before expensive work finishes; and code completion benefits from current incomplete text even when other state is older. A global barrier would force latency-sensitive advisory operations to wait for state they do not need.

For Anneal, this alternative remains reasonable for a small first implementation if interactive volume is low, because simplicity is valuable. But it should be understood as a conservative implementation policy, not a semantic requirement. The protocol should not bake “global ready” into its conceptual model if future operations will have different needs.

#### Everything is latest-best-effort

The opposite design can always answer from whichever state is most recent or convenient and rely on the client to retry.

That model is inadequate for operations whose result has authority beyond display. A transformation applied to the wrong source generation, a proof context from the wrong imported environment, or a generated artifact published from an obsolete translation is not merely lower quality. It can mutate or certify the wrong thing. clangd’s exact request-version AST contract and sequencing fences show that a latency-oriented service still needs hard identity boundaries.

#### Run the batch compiler or verifier after every edit

This gives a clear oracle and avoids semantic drift between interactive and batch modes. It also defeats much of the purpose of a language service: incomplete source is normal while typing, expensive setup is repeated, and obsolete snapshots consume resources. clangd’s dedicated completion parse, preamble reuse, debouncing, cancellation, and background indexing are all responses to that mismatch.

For Anneal, the batch oracle should remain available, but a live service can answer advisory questions from cheaper state and invoke the oracle only for acceptance-sensitive actions or explicit exact queries.

#### Duplicate a separate live semantics and compare later

This can maximize responsiveness, as rust-analyzer’s history illustrates in adjacent J009 work, but it creates semantic-divergence risk. clangd avoids much of that particular risk by reusing Clang’s parser, yet still demonstrates that shared frontend code does not eliminate model/freshness differences. Anneal should therefore not infer that using the same Charon/Aeneas/Lean libraries automatically makes a live result authoritative. The invocation model, configuration, generated inputs, and retained environment still matter.

### A useful Anneal model has at least three service levels

The clangd evidence supports an Anneal contract in which each operation declares the minimum authority it needs. One workable vocabulary is:

| Service level | Required witness | Suitable examples | Forbidden use |
| --- | --- | --- | --- |
| **Advisory** | result generation plus the source/model generations actually observed; staleness or incompleteness permitted | completion, navigation, search, hover-like summaries, speculative dependency discovery, cache warming | publication, proof acceptance, silently applying edits |
| **Snapshot-exact** | exact requested authored source/annotation snapshot; explicit model identity even if model is provisional | tactic-state query for a named open document generation; preview refactor; local semantic inspection | claiming authoritative project acceptance if build/tool/proof environment is not exact |
| **Model-exact / acceptance** | exact source snapshot *and* exact build subject, tool/config revisions, generated inputs, dependency/proof environment, plus a current publication fence | Charon extraction selected for downstream proof, Aeneas translation selected for checking, accepted proof result, generated-artifact publication, applied refactor mutation | returning a result produced from guessed/fallback project configuration or stale imports |

The names are not product-policy recommendations; the separation is the derived judgment. A later Anneal design can choose different terminology or add intermediate levels.

For a tactic-state MCP operation, “snapshot-exact” is usually the minimum useful contract: an agent asking for the goal at a particular proof point needs that exact document generation, not merely the newest available one. If the goal’s meaning depends on imported generated modules, then the request moves toward model-exact: the result must also identify the imported environment. A stale answer can still be useful if explicitly requested by immutable historical handle, but it must not be confused with the current document.

For a refactoring or source edit, a preview can be snapshot-exact. Applying the edit should include a compare-and-swap style source fence so that the edit is rejected or recomputed if the target source changed.

For proof acceptance and publication, there is no corresponding best-effort mode. These operations create durable authority and therefore need the full identity tuple plus a publication fence.

### “Freshness” should be a vector, not a boolean

A practical result envelope should make the independent axes explicit. For example:

- authored-source generation or digest;
- Rust/Cargo subject and build-configuration identity;
- projection/generated-source identity;
- Charon/Aeneas/Lean tool and configuration identities;
- imported proof-environment identity;
- index/cache generation, if relevant to the operation;
- worker/session incarnation when retained process state matters;
- operation-specific completeness/freshness status.

The service can then define predicates such as `snapshot_exact`, `model_exact`, or `publishable` from those facts instead of setting one mutable `ready` bit.

This matters because two common failure modes are orthogonal:

- **fresh but wrong model:** latest source parsed under guessed flags or the wrong Cargo feature set;
- **right model but stale source:** authoritative configuration applied to an old document generation.

clangd has concrete versions of both risks. Its compile-command documentation treats fallback/inferred commands as potentially wrong even for current text, while its preamble/index design permits older state under a known project model. Anneal should not collapse those cases.

### Best-effort results need explicit fallbacks, not silent promotion

The strongest reusable clangd pattern is not staleness itself; it is *bounded staleness plus a stronger path when needed*.

Examples in clangd include an exact-version AST path alongside stale-preamble reads, forced diagnostics alongside eventual diagnostics, and a dynamic open-file index layered above slower global indexes. The user experience can stay responsive because the common path is cheap, while a caller with stronger requirements can pay for a stronger result.

Anneal should follow the same shape where the upstreams permit it:

- return fast advisory navigation or proof-search hints with provenance;
- expose an exact query that waits/rebuilds against the requested source and environment;
- retain a fresh-process/batch fallback where a persistent upstream cannot attest reset or environment identity;
- never promote an advisory response to acceptance just because no better response is immediately available.

This also clarifies cancellation. Cancelling a superseded advisory computation is a throughput optimization. Cancelling an exact acceptance computation means “no result”; it does not authorize substituting a newer or older result under the original request identity.

## Boundaries

- **No execution.** This report did not run clangd, build LLVM, measure completion latency, compare diagnostic sets, or reproduce the historical performance reports. Current behavior is reconstructed from source/documentation; historical motivation is reconstructed from landed commits and review discussion.
- **Historical comments are intent evidence.** The D39843 memory comparison and D148088 latency figures are reports by participants, not measurements reproduced here. They show what tradeoffs informed the design, not universal quantitative effects.
- **clangd is not Anneal.** C/C++ preambles, compile commands, and symbol indexes are not structurally identical to Cargo subjects, Charon LLBC, Aeneas-generated Lean, or Lake environments. The applicability section derives a consistency model; it does not claim an implementation can be transplanted.
- **Shared compiler machinery does not prove equivalence.** clangd reuses Clang but still has editor-specific scheduling, incomplete-code behavior, stale indexes, and build-model inference. The report does not claim that every clangd diagnostic differs from a compiler build, only that the contracts are not equivalent.
- **Exact code-generation behavior was not studied inside clang.** The relevant J012 distinction is that clangd does not serve as the project’s code-generation/build acceptance path. This report does not reconstruct LLVM backend or linker semantics.
- **No full causal claim.** Individual changes have multiple motives and interact with later redesigns. The report claims a durable architectural pattern—operation-specific consistency—because it is visible in current contracts and repeated history, not because one historical change caused the modern design.
- **No adopted Anneal policy.** The service-level table and result-envelope fields are derived recommendations for design evaluation. They are not an approved V2 architecture or protocol.
- **Current-source volatility.** `llvm/llvm-project` advances rapidly. Implementation statements are pinned to `ded546ad82656ce6605ee2f2aa60c78dec70d95f`; revalidate the named symbols before relying on details after a material clangd change.

## Evidence

### Current implementation and documentation

- **Source:** `llvm/llvm-project@ded546ad82656ce6605ee2f2aa60c78dec70d95f`, `clang-tools-extra/clangd/TUScheduler.h`: `WantDiagnostics`, `ASTActionInvalidation`, `runWithAST`, `PreambleConsistency`, and `runWithPreamble`. These are the primary current contracts for per-request snapshot identity, cancellation, diagnostic policy, and stale preambles.
- **Source:** same revision, `clang-tools-extra/clangd/ClangdServer.cpp`: `addDocument`, `codeComplete`, `signatureHelp`, `locateSymbolAt`, and `findHover`. These call sites show the operation-specific choice between current ASTs and stale/absent preambles.
- **Source:** same revision, `clang-tools-extra/clangd/GlobalCompilationDatabase.h`: `getCompileCommand`, `getFallbackCommand`, and `DirectoryBasedGlobalCompilationDatabase`. The fallback is explicitly unreliable.
- **Source:** same revision, `clang-tools-extra/clangd/index/FileIndex.cpp` and `index/Background.cpp`: dynamic main/preamble indexes, versioned replacement, and background indexing.
- **Documentation:** `llvm/clangd-www@ae5866d4552e30a173b8e9c3cec872a82e4c0120`, `design/threads.md`: request queuing, debouncing, AST version ordering, and code completion’s fresh parse with immediately available preamble.
- **Documentation:** same revision, `design/indexing.md`: dynamic/background/static/remote index roles and layered index semantics.
- **Documentation:** same revision, `design/compile-commands.md`: parser dependence on virtual compile commands, database discovery, header-command inference, and fallback behavior.
- **Documentation:** same revision, protocol extensions `wantDiagnostics`: exact-versus-eventual diagnostic policy.
- **Documentation:** same revision, remote-index design: offline periodic index is inherently somewhat stale.
- **Documentation:** same revision, FAQ: wrong compile commands and responsiveness optimizations can produce false or missing diagnostics.

### Historical changes and rationale

- **Source/history:** `llvm/llvm-project@e9eb7f0cb815641827fa3d031c38190c10900c14`, 2017-11-16, “[clangd] Use in-memory preambles in clangd.” Review D39843 records the decision to make the behavior configurable and initially keep on-disk storage by default after memory concerns.
- **Source/history:** `llvm/llvm-project@6675be87477395658f6d3859b028ab8dee81ba19`, 2018-10-30, “[clangd] Use thread pool for background indexing.” D53651 records explicit discussion of foreground interference and the decision to lower background-task priority.
- **Source/history:** `llvm/llvm-project@a2b048bc4bdf9320249d0ff512fab6f16c2e6e47`, 2018-11-22, “[clangd] Respect task cancellation in TUScheduler.” Its commit message and D54746 summarize cancellation and diagnostic-update elision.
- **Source/history:** `llvm/llvm-project@c627b120eb8b7add3f9cf893721335c367d9f037`, 2020-03-04, “[clangd] Cancel certain operations if the file changes before we start.” D75602 states the goal of avoiding obsolete snapshots for editor-generated operations.
- **Source/history:** `llvm/llvm-project@a8ad413f0d18c07a4adaa0d547e0096874d809c5`, 2023-06-12, “[RFC][clangd] Move preamble index out of document open critical path.” D148088 records the explicit temporary-freshness versus latency trade and identifies which features already tolerate stale index data.

### Derived claims

The following are analysis in this report rather than statements adopted by clangd or Anneal:

- freshness and semantic-model authority should be independent axes in Anneal;
- Anneal should classify operations by required authority rather than use one global ready bit;
- advisory/snapshot-exact/model-exact is a useful candidate taxonomy;
- applying edits and publishing generated/proof artifacts need stronger fences than navigation or completion;
- a fresh batch/fresh-worker oracle should remain available until persistent/live upstream services can attest equivalent environment identity and reset behavior.

## Revalidation

For clangd, re-read the named symbols in current `TUScheduler.h`, `ClangdServer.cpp`, `GlobalCompilationDatabase.h`, `FileIndex.cpp`, and `Background.cpp`, then compare the current `clangd-www` design pages. If any of these contracts have changed—especially preamble consistency modes, diagnostic guarantees, compile-command fallback semantics, or index layering—update the derived matrix rather than extrapolating from this pin.

A high-value execution follow-up would run a pinned clangd on one controlled C++ project and capture, for a sequence of rapid edits:

1. document versions sent by the client;
2. the versions for which diagnostics arrive under ordinary and forced-diagnostic policy;
3. completion behavior before and after a preamble rebuild;
4. navigation before and after background indexing;
5. behavior after intentionally changing or removing the compilation database;
6. cancellation of transient requests after a subsequent edit.

The expected result is *not* byte-for-byte equality across these modes. The useful falsification target is the architectural claim: exact-source requests should never be mislabeled as another document version, while advisory operations are permitted to expose bounded stale/incomplete auxiliary state. A failure of the first property would weaken this report substantially; differences in timing or index quality would refine, rather than refute, the operation-specific model.

For Anneal, the corresponding integration test should take one immutable request identity and run it through both the batch oracle and any live backend, then mutate one axis at a time: authored Rust/Lean text, Cargo subject/features, generated source, Charon/Aeneas revision/configuration, imported Lean environment, and worker incarnation. Advisory queries may return explicitly tagged older state. Acceptance-sensitive queries should either match the exact requested identity or fail/rebuild; they should never silently substitute “latest available.” This test directly distinguishes a sound operation-specific freshness model from a global-ready implementation that merely happens to work on the happy path.