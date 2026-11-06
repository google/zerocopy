# Language Server Snapshots, Views, and Compiler-Backed IDE Architectures

## Summary

This report synthesizes fourteen primary-source architectural studies and current-source delta reviews across eight language-server and compiler-backed IDE lineages (`RLS` to `rust-analyzer`, `clangd`, `gopls`, the Haskell IDE lineage from `haskell-ide-engine` through `ghcide` and `hie-bios` to `haskell-language-server` and `hls-graph`, Kotlin K2 Analysis API and Swift `SourceKit-LSP`/`sourcekitd`, the .NET Compiler Platform `Roslyn`, and TypeScript's host-owned `LanguageService`/`ProjectService` through the TypeScript 7.0 native Go port):

1. **Why `RLS` Yielded to `rust-analyzer`, and Why Shared Semantic Libraries Do Not Imply One Runtime Engine**: Rust's 2015 IDE plan ([RFC 1317](https://github.com/rust-lang/rfcs/blob/4e4c756e6df95167dda553251cc37a75a294f002/text/1317-ide.md)) envisioned turning `rustc` into a long-running library server with in-memory incrementality, fine-grained invalidation, cancellation, and error resilience. In practice, archived `RLS` (`rust-lang/rls@04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc`) became a hybrid coordinator combining crate-level `rustc` runs (`rustc -> rustc_save_analysis -> rls_data -> rls_analysis -> rls`), JSON save-analysis dumps for dependencies, a VFS (`FileLoader`) for unsaved buffers, build squashing, and a second approximate engine (`Racer`) for completions and go-to-definition when compiler state was stale or unavailable. `rust-analyzer` ([RFC 2912](https://github.com/rust-lang/rfcs/blob/ba27c4c027704c716fcc1f54be601939fdc29c57/text/2912-rust-analyzer.md), `rust-lang/rust-analyzer@03fcb77246f2568adb0e9b2fa60d19c6cc1686f4`) inverted that design: it keeps an explicit mutable `AnalysisHost` and immutable snapshot `Analysis` boundary backed by Salsa queries, an error-tolerant rowan syntax tree, an explicit `CrateGraph` in a no-I/O `base-db`, function-body edit invariance across the HIR spine, out-of-process procedural-macro isolation, and background `cargo check` (`flycheck`) for authoritative compiler diagnostics. Today `rustc` and `rust-analyzer` share extracted domain libraries (`rustc_lexer`, `rustc_abi`, `rustc_ast_ir`, `rustc_type_ir`, `rustc_next_trait_solver`, `rustc_pattern_analysis`) parameterized over `trait Interner` (`TyCtxt` in `rustc` vs `DbInterner` in `rust-analyzer`) while deliberately keeping separate front-end state, incrementality, and scheduling engines.
2. **Multi-Domain Freshness, Preambles, and Index Authority in `clangd`**: `clangd` (`llvm/llvm-project@ded546ad82656ce6605ee2f2aa60c78dec70d95f` and `llvm/clangd-www@ae5866d4552e30a173b8e9c3cec872a82e4c0120`) demonstrates that a language server does not serve one uniform notion of truth. It mediates across four independently advancing authority domains: (a) per-file AST workers serialized in `TUScheduler` (`runWithAST`, with `ASTActionInvalidation` cancelling transient queries on subsequent edits), (b) asynchronous preamble threads (`runWithPreamble` with `Stale`, `StaleOrAbsent`, or `Consistent` `PreambleConsistency`), (c) compilation-database flag resolution (`GlobalCompilationDatabase::getCompileCommand` vs heuristic `getFallbackCommand`), and (d) layered symbol indexes (`MergedIndex` combining dynamic in-memory `FileIndex` slabs over open files and preambles with persisted `BackgroundIndex` or remote indexes). Diagnostics and semantic tokens remain gated by the `ParsingCallbacks::onMainAST` publication fence and `WantDiagnostics` (`Yes`, `No`, `Auto`).
3. **Folders, Views, Snapshots, and Shared Caches in `gopls`**: `gopls` (`golang/tools@98444708d405557b5ddd6179be1a6abc14150d5f`) separates four distinct state scopes across `session.go`, `view.go`, `snapshot.go`, and `workspace.go`: editor workspace **Folders** (`Folder`), resolved build-context **Views** (`View` / `viewDefinition` keyed by Go version, `GOOS`/`GOARCH`, build flags, environment, and workspace module roots), immutable **Snapshots** (`Snapshot` with a View-local monotonic `sequenceID`), and cross-View **shared caches** (process-wide file-content cache and persistent file-backed package analysis cache introduced in `gopls/v0.12.0` after abandoning the single-super-module model of `gopls/v0.11.0`, reducing memory usage and startup time by roughly 75% across multi-module repositories). A single file edit in `Session.DidModifyFiles` classification-checks whether the edit alters View definitions (`selectViewDefs`), clones each affected View's `Snapshot` simultaneously, and classifies changes into metadata-invalidating (`invalidateMetadata`), import-changing, or package-local narrow invalidations.
4. **Build-Environment Negotiation vs In-Memory Dependency Graphs in the Haskell IDE Lineage**: Across `haskell-ide-engine` (`d84b84322ccac81bf4963983d55cc4e6e98ad418`), `ghcide` (`3ef4ef99c4b9cde867d29180c37586947df64b9e`), `hie-bios` (`32dd07707423ffabb34e44af68fcbd027b60ded2`), and `haskell-language-server` (`187fcd4a685c220caabb72999565604b3287aff2`), Haskell IDE architecture split into two distinct boundaries: **cradle/environment discovery** (`hie-bios`, asking Cabal, Stack, Bazel/Obelisk bios scripts, or direct flag lists how a file is compiled and which targets exist) and **in-memory session evaluation** (`ghcide` and `hls-graph`). `hls-graph` evolved from Shake (`Development.Shake.Database`) by dropping on-disk build persistence and optimizing purely for in-memory reactive IDE invalidation, session keys, dirty-key sets, and last-good artifact caching with source-position mapping.
5. **Compiler-Backed Session Lifetimes, Synthesis Extensions, and Build-Server Protocols in Kotlin K2 and Swift `SourceKit-LSP`**: Kotlin's K2 Analysis API (`JetBrains/kotlin@bce49f3701fb8dc461fb98240fdc7c3c81c592f2`) replaces K1's leak-prone `BindingContext` maps with lifetime-managed `KaSession` tokens (`analyze(useSiteElement) { ... }`), explicit `KaModule` world units, lazy FIR phase resolution (`BODY_RESOLVE` only on demand), and session-scoped compiler-plugin symbol synthesis (`KaResolveExtension`, `KaSymbolOrigin.PLUGIN`, out-of-block modification trackers, and package/file shadowing over stale on-disk generated sources). Swift (`swiftlang/sourcekit-lsp@045c18e9e9ea35b896857b6cb982aa2373fb5816` and `swiftlang/swift@f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d`) splits build graph negotiation (Build Server Protocol `buildTarget/prepare` and `textDocument/sourceKitOptions`) from `sourcekitd`'s `SwiftASTManager`, which only reuses a prior `ASTContext` (`canUseASTWithSnapshots`) when edits are confined to function bodies without shifting global token offsets or structural declarations, and exposes macro expansions as read-only virtual reference documents.
6. **Immutable Solution Snapshots, Red-Green Trees, and Checksum-Identified Cross-Process Sync in `Roslyn`**: `Roslyn` (`dotnet/roslyn@7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b`) layers four distinct abstractions: bottom-up immutable green syntax nodes wrapped in top-down parented red façade nodes (`Red-Green Trees.md`), immutable single-project `Compilation` values, immutable workspace-wide `Solution`/`Project`/`Document` graphs (`SolutionCompilationState` hiding `AsyncLazy` and weak caches behind pure value semantics), and a mutable `Workspace` shell (`CurrentSolution`, serialized mutation locks, event queues). For out-of-process execution (`RemoteWorkspace`, `SolutionAssetCache`, `RemoteWorkspaceManager`), Roslyn never serializes live `Solution` object graphs; instead it transmits Hierarchical `SolutionChecksum` trees, pulls missing assets on demand, and pins committed on-disk build outputs via PDB document checksums (`CommittedSolution.cs`) to detect build-versus-buffer desynchronization.
7. **Host-Owned Language Worlds and the Native Go Port Boundary in TypeScript**: In TypeScript 6.0.2 (`microsoft/TypeScript@607a22a90d1a5a1b507ce01bb8cd7ec020f954e7`), `LanguageService` does not own files or projects; its caller supplies a `LanguageServiceHost` exposing versioned `IScriptSnapshot` buffers, project version strings, compilation settings, and resolution hooks, while `tsserver`'s `ProjectService` maintains mutable `ScriptInfo` caches and routes files across Configured (`tsconfig.json`), External, and Inferred projects. TypeScript 7.0.2 (`microsoft/TypeScript@1e4744d68260a7cb91b62b12edc3f6a2187faaf1`, mirrored from `microsoft/typescript-go@2bd066d87f5bafd315be9f40889d0a60b9e58e0b`) replaces the JS compiler and LSP server (`cmd/tsgo/lsp.go`, `internal/lsp/server.go`, `internal/project/project.go`) with a native Go implementation while explicitly deferring replacement of the programmatic JavaScript Language Service API (`LanguageServiceHost`/`ProjectService`), requiring tools that depend on the JS host API to bridge across or remain on 6.0 until later 7.x releases.
8. **Current-Source Delta Verification Across All Studied Lineages**: Re-audits against current upstream heads (`llvm/llvm-project@229b9b2f4e20840a8280174fa08385fd9e36844b`, `golang/tools@134264d72fba423ca1ad358683cd3c32699b010e`, `rust-lang/rust-analyzer@03fcb77246f2568adb0e9b2fa60d19c6cc1686f4`, `haskell/haskell-language-server@187fcd4a685c220caabb72999565604b3287aff2`, `haskell/hie-bios@32dd07707423ffabb34e44af68fcbd027b60ded2`, `JetBrains/kotlin@79b33f2836ef88425c100924bb8d29bcdf52bf48`, `swiftlang/swift@0fcad6fb60755587d39a758761b219bf433cf9dc`, `swiftlang/sourcekit-lsp@045c18e9e9ea35b896857b6cb982aa2373fb5816`, and `dotnet/roslyn@36d26c5466e4d25940657ccb8d5b9557ccaf7be1`) confirm zero blob drift across every claim-mapped source file in the `clangd`, `gopls`, `rust-analyzer`, Haskell, Kotlin, Swift, and Roslyn cohorts, while recording the explicit native Go target transition in TypeScript `v7.0.2`.

---

## Applicability

These findings govern the architecture of compiler-backed interactive tools, verification servers, and IDE/LSP/MCP surfaces in projects such as Anneal and `zerocopy`:

1. **Separate Semantic Libraries, Interactive Query Engines, and Batch Acceptance Gates**:
   - Follow the `rustc`/`rust-analyzer` split: share well-typed semantic domain crates (type representations, trait/constraint solvers, ABI and pattern analyzers, obligation constructors) parameterized over an abstract interner or context trait (`trait Interner`), while allowing the interactive server and the batch compiler/verifier to maintain distinct state-management, incrementality, and scheduling substrates.
   - Never assume that wrapping a batch compiler pass pipeline in a long-running process with serialized side tables (the `RLS` save-analysis pattern) yields sub-second interactive responsiveness under incomplete edits.
2. **Maintain Explicit Immutable Snapshot Values Behind a Narrow Mutable Host**:
   - Every successful language server studied converges on the same structural boundary: `AnalysisHost` vs `Analysis` in `rust-analyzer`, `Session`/`View` vs `Snapshot` in `gopls`, `Workspace` vs `Solution`/`Compilation` in `Roslyn`, and `KaSession` over a bounded `KaModule` world in Kotlin K2.
   - All read queries, verification checks, and code actions must execute against an immutable snapshot value with an explicit monotonic sequence ID or content checksum. Internal lazy caches (`AsyncLazy`, Salsa memo tables, weak compilation caches) may populate on demand inside a snapshot only if observable query results remain pure functions of the snapshot's inputs.
3. **Represent Compilation Subjects as `(File, View/Target/Context)` Pairs, Never Bare File Paths**:
   - The same source file can belong to multiple crate targets, feature sets, `GOOS`/`GOARCH` build tags (`gopls` `View`), Cabal/Stack components (`hie-bios` multi-cradle), Kotlin `KaModule`s, or C++ translation units (`clangd`). Keying semantic state by bare file URI causes cross-target cache poisoning and silent mis-diagnostics.
   - Separate per-View semantic graphs from content-addressed cross-View file and artifact caches (`gopls` `v0.12.0` file/compilation cache split; `Roslyn` `SolutionAssetCache`).
4. **Expose Multi-Domain Freshness Vectors and Service Levels Rather Than Pretending "Current State" Is Atomic**:
   - Like `clangd`, an interactive verification or analysis server combines inputs that advance on different clocks: unsaved buffer snapshots, imported-module preambles/interfaces, build-system target/flag resolution, and background cross-workspace indexes or proof caches.
   - Classify operations into explicit service levels (**Advisory** fast path on last-good/stale preambles, **Snapshot-exact** path pinned to the current document and target configuration, and **Model-exact / Acceptance** path requiring full workspace build/proof consistency) and attach freshness metadata (`document_rev`, `preamble_epoch`, `build_graph_epoch`, `index_coverage`) to published results.
5. **Enforce Publication-Order Fences and Function-Body Edit Firewalls**:
   - Gate asynchronous diagnostic and verification publication with a monotonic version fence (`clangd` `ParsingCallbacks::onMainAST`, `gopls` `Snapshot.sequenceID`, `Roslyn` `SolutionChecksum`) so slow analyses on older revisions never overwrite newer editor state.
   - Isolate function-body / proof-body edits from module-signature / item-spine invalidation (`rust-analyzer` HIR item-tree firewall, Kotlin K2 `BODY_RESOLVE` phase separation, Swift `canUseASTWithSnapshots`, `gopls` package-local body invalidation).

---

## Findings

### 1. Rust IDE Lineage: From RFC 1317 and `RLS` to `rust-analyzer` and Shared `rustc` Libraries

*(Coalescing `rls-rust-analyzer-architecture-evolution-2015-2026`, `rls-rust-analyzer-architecture-transition-2015-2026`, and `rls-to-rust-analyzer-editor-engine-history-2015-2026`)*

#### 1.1 The Original RFC 1317 Vision (`rustc` as a Direct Long-Running IDE Server)
In October–December 2015, [RFC 1317 (`text/1317-ide.md`)](https://github.com/rust-lang/rfcs/blob/4e4c756e6df95167dda553251cc37a75a294f002/text/1317-ide.md) (`rust-lang/rfcs@4e4c756e6df95167dda553251cc37a75a294f002`, later updated at `82d48b36568286b93fc2ce55f89594024f421a3b`) proposed evolving `rustc` itself into the core of Rust's IDE story. The RFC specified:
- Refactoring `rustc` so a long-running coordination server could invoke the compiler as an in-process library rather than only as a batch CLI executable.
- Maintaining a central database, a prioritized work queue, in-memory buffer edits, and lazy compilation so that keeping the compiler warm in memory would support interactive IDE queries.
- Even in RFC 1317, the authors noted that keeping `rustc` in memory across edits posed unresolved difficulties around fine-grained invalidation, task cancellation, and partial/malformed inputs.

#### 1.2 What Archived `RLS` Actually Built: Hybrid Coordinator + Save-Analysis + `Racer`
Inspection of the archived `rust-lang/rls` repository (`04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc`, `architecture.md` blob `a7bde5799d73cbaf7319dad2773fd58a89a978a8` and `README.md`) shows that `RLS` never became a single fine-grained on-demand query engine inside `rustc`:
1. **End-to-End Save-Analysis Pipeline**: `RLS` drove `rustc -> rustc_save_analysis -> rls_data -> rls_analysis -> rls`. During initialization, `RLS` ran a Cargo `check`-style build plan. For workspace primary/path crates, it ran `rustc` in-process via `rustc_driver` and passed the `save-analysis` data structure directly in memory; for non-path dependencies, `rustc` wrote JSON save-analysis files to disk that `rls_analysis` loaded and lowered.
2. **Coarse Invalidation and Build Squashing**: Edits arrived over LSP into an in-memory Virtual File System (`rls_vfs`, wired into `rustc`'s `FileLoader` trait). Because `rustc` still executed per-crate compilation passes to produce a fresh `SaveAnalysis` dump, `RLS` relied on build squashing and dirty-crate scheduling rather than sub-crate query invalidation. Multi-package workspaces suffered from over-broad rebuild scheduling (documented in [`rust-lang/rls#1714`](https://github.com/rust-lang/rls/issues/1714), where Cargo-level package rebuild filtering had to be patched to avoid rebuilding unaffected workspace members).
3. **Dual-Engine Split with `Racer`**: Because `rustc` could not reliably typecheck broken intermediate syntax at keystroke latency and save-analysis tables lagged behind active typing, `RLS` delegated autocompletion and fallback definition lookup to `Racer`, a separate text/AST heuristic tool using its own VFS bridge. Thus `RLS` already had two semantic engines (`rustc` + `Racer`) inside one product, with divergent semantics and failure modes.
4. **Late-2019 Hybrid Save-Analysis Proposal**: By the November 18, 2019 IDE team meeting ([2019-12-04 Inside Rust blog post](https://blog.rust-lang.org/inside-rust/2019/12/04/ide-team-meeting-2019-11-18/)), maintainers considered a hybrid model combining precomputed save-analysis indexes for dependencies with library-ified on-demand components for active crates, before concluding that `rust-analyzer`'s query-first architecture was the viable foundation.

#### 1.3 `rust-analyzer`'s Architectural Inversion (2018–2026)
Started in January 2018 (`rust-lang/rust-analyzer@5e21ae9418380b8c183c4663ca03bd63dd240aa9` and `6d14bb0cd0af55fe45711ac048236f9dd9d24a3f`), explained in Aleksey Kladov's posts (`First Release` on 2020-04-20, `Three Architectures for a Responsive IDE` on 2020-07-20, `IDEs and Macros` on 2021-11-21), adopted via [RFC 2912 (`text/2912-rust-analyzer.md`)](https://github.com/rust-lang/rfcs/blob/ba27c4c027704c716fcc1f54be601939fdc29c57/text/2912-rust-analyzer.md) (`ba27c4c027704c716fcc1f54be601939fdc29c57` / `b6fffdf18f8b867648de0d95657cc13a64cae4e2`, blob `9f5986eeacafbea1ad99c6cbc4c24d2eab278c99`), transferred to the `rust-lang` organization on 2022-02-21, and followed by the official [`RLS Deprecation` announcement on 2022-07-01](https://blog.rust-lang.org/2022/07/01/RLS-deprecation/), `rust-analyzer` (`03fcb77246f2568adb0e9b2fa60d19c6cc1686f4`, `docs/book/src/contributing/architecture.md` blob `8b6ea56c851650cac23c27cc1ffb0a7f1b2a854c`) enforces six architectural invariants:
1. **`AnalysisHost` vs `Analysis` Snapshot Split**: `ide::AnalysisHost` owns the single mutable Salsa database and applies input batches (`apply_change`). Calling `host.analysis()` produces an immutable `ide::Analysis` snapshot handle that can be shared across concurrent worker threads. If a new edit arrives on `AnalysisHost`, in-flight `Analysis` snapshots trigger deterministic unwind-based cancellation (`Cancelled`) when attempting to observe mutated Salsa revisions.
2. **Error-Tolerant Full-Fidelity Syntax (`parser` / `syntax` / `rowan`)**: Every parse produces a lossless concrete syntax tree plus a list of syntax errors (`Parse<T>`), never aborting on malformed tokens. As documented in [`rust-lang/rust-analyzer#10765` (2021-11-14)](https://github.com/rust-lang/rust-analyzer/issues/10765), even when maintainers explored sharing a parser with `rustc`, `rust-analyzer`'s grammar resilience, token/tree representation, and IDE recovery requirements prevented drop-in unification of the front-end parser.
3. **Pure Value Input Boundary (`base-db` Performs No Direct File I/O)**: The core analysis database never touches the filesystem or spawns Cargo. Project discovery (`project-model`) and file watching happen outside the database and feed explicit `FileId` texts and an explicit `CrateGraph` into `base-db` (upgraded to the newer Salsa framework in [`rust-analyzer` Changelog #277 on 2025-03-17](https://rust-analyzer.github.io/thisweek/2025/03/17/changelog-277.html)).
4. **Function-Body Edit Firewall Across the HIR Spine (`hir-def`, `hir-ty`, `hir`)**: Editing tokens inside a function body does not invalidate module-level `ItemTree` signatures, name resolution, or cross-crate import graphs.
5. **Out-of-Process Procedural Macro Isolation (`proc-macro-srv`)**: Because procedural macros execute arbitrary native code that can crash or hang, `rust-analyzer` expands them in a separate `proc-macro-srv` child process over an RPC boundary while keeping macro expansion results memoized as pure Salsa query values inside the database.
6. **Dual-Path Authority via `flycheck` (`cargo check --message-format=json`)**: Rather than forcing the interactive Salsa engine to replicate every late `rustc` borrow-check, MIR lint, or codegen diagnostic in real time, `rust-analyzer` runs background `cargo check` (`flycheck`) processes on saved workspace state and merges authoritative `rustc` diagnostics with low-latency in-memory IDE diagnostics.

#### 1.4 How `rustc` and `rust-analyzer` Actually Share Code Today
As documented in the `rustc` Developer Guide (`rust-lang/rustc-dev-guide@0fb89036f8e46a80ee815ed99ff7d9dae9d172ae`, `src/solve/sharing-crates-with-rust-analyzer.md`), code sharing between `rustc` and `rust-analyzer` operates at the **semantic domain library layer**, not by running one monolithic compiler database:
- Shared crates include `rustc_lexer`, `rustc_abi`, `rustc_ast_ir`, `rustc_type_ir`, `rustc_next_trait_solver`, and `rustc_pattern_analysis`.
- Both engines implement `rustc_type_ir::Interner`: `rustc` backs it with `TyCtxt<'tcx>` arena allocation and query tables, whereas `rust-analyzer` backs it with its Salsa-based `DbInterner`.
- This establishes a three-part taxonomy of sharing:

| Sharing Dimension | Definition | Verdict from the Rust IDE Lineage |
| :--- | :--- | :--- |
| **Semantic-Source Sharing** | Sharing pure domain algorithms and IR definitions (`rustc_lexer`, `rustc_type_ir`, `rustc_next_trait_solver`, `rustc_pattern_analysis`, `rustc_abi`) parameterized over a representation trait (`trait Interner`). | **Validated & Active**: Eliminates duplicate type/trait/pattern semantics without coupling scheduling or state lifetimes. |
| **Acceptance Sharing** | Using the authoritative batch toolchain (`cargo check` / `rustc` via `flycheck`) as the final acceptance gate for full-program diagnostics and soundness. | **Validated & Active**: Keeps the interactive engine responsive while preserving exact batch compiler authority. |
| **Runtime-State Sharing** | Running the interactive IDE and the batch compiler inside a single shared mutable database, representation, and pass pipeline. | **Falsified (`RLS`)**: Incompatible latency budgets, error-recovery needs, and invalidation granularities make a single runtime database brittle or unresponsive. |

| Engine Architecture Pattern | Representative System | Primary Strength | Structural Failure Mode |
| :--- | :--- | :--- | :--- |
| **Batch Compiler + Serialized Side Tables + Heuristic Fallback** | Archived `RLS` (`rustc_save_analysis` + `rls_analysis` + `Racer`) | Reuses existing compiler passes with minimal initial compiler refactoring | Crate-wide rebuild latency on edits; broken semantics on incomplete syntax; split-brain divergence between compiler dump and `Racer` heuristics |
| **Dedicated Query-First IDE Engine + Isolated Background Acceptance** | `rust-analyzer` (`AnalysisHost`/`Analysis` + Salsa + `rowan` + `proc-macro-srv` + `flycheck`) | Sub-100ms keystroke responsiveness, deterministic cancellation, total parser recovery, function-body firewall | Requires maintaining IDE-specific syntax/HIR lowering and bridging shared semantic crates (`trait Interner`) |
| **Shared Semantic Domain Libraries over Distinct State Substrates** | `rustc_type_ir` + `rustc_next_trait_solver` across `TyCtxt` and `rust-analyzer` | Single authoritative trait solver and type IR across batch and interactive engines | Requires explicit abstraction boundary (`trait Interner`) free of arena-lifetime or I/O assumptions |

---

### 2. `clangd`: Multi-Domain Authority, Preamble Consistency, and Index Freshness

*(From `clangd-authority-freshness-2017-2026`)*

#### 2.1 Four Independently Advancing Authority Domains in `clangd`
Inspection of `llvm/llvm-project@ded546ad82656ce6605ee2f2aa60c78dec70d95f` (`clang-tools-extra/clangd/{TUScheduler.h,ClangdServer.cpp,GlobalCompilationDatabase.h,index/FileIndex.cpp,index/Background.cpp}`) and `llvm/clangd-www@ae5866d4552e30a173b8e9c3cec872a82e4c0120` (`design/{threads.md,indexing.md,compile-commands.md}`) shows that `clangd` decomposes per-request state into four distinct authority domains:

1. **Domain 1 — Active Document AST Snapshot (`TUScheduler::runWithAST`)**:
   - Each open translation unit owns a dedicated AST worker thread in `TUScheduler` (`TUScheduler.h`).
   - Edits arrive via `TUScheduler::update` with a `WantDiagnostics` policy (`Yes`, `No`, or `Auto`).
   - Read actions queued via `runWithAST` execute in FIFO order relative to updates on that file's AST worker, observing the exact main-file buffer snapshot paired with whatever preamble was selected when the AST was built.
   - Commit `a2b048bc4bdf9320249d0ff512fab6f16c2e47` (`D54746`, 2018-11-22) added task cancellation and diagnostic elision inside `TUScheduler`, and commit `c627b120eb8b7add3f9cf893721335c367d9f037` (`D75602`, 2020-03-04) added `ASTActionInvalidation` so transient read requests (such as hover or code actions) queued before a newer edit are automatically cancelled rather than computing wasted AST rebuilds.
2. **Domain 2 — Asynchronous Preamble Snapshot (`TUScheduler::runWithPreamble` & `PreambleConsistency`)**:
   - Parsing the `#include` preamble of a C++ translation unit dominates compile time. `TUScheduler` offloads preamble rebuilds onto a separate asynchronous preamble thread so the AST worker is not blocked from serving latency-sensitive queries.
   - Commit `e9eb7f0cb815641827fa3d031c38190c10900c14` (`D39843`, 2017-11-16) introduced configurable in-memory versus on-disk preamble storage after measuring roughly 2x memory growth from keeping all serialized preambles resident in RAM.
   - Latency-critical requests (such as code completion and signature help) call `runWithPreamble` on the concurrent request pool with an explicit `PreambleConsistency` policy (`TUScheduler.h`):
     - `Consistent`: Wait for a preamble compatible with the latest update if the `#include` prefix changed.
     - `Stale`: Immediately use the most recent available preamble even if `#include` lines in the current buffer have been edited.
     - `StaleOrAbsent`: Proceed immediately even if no preamble has finished building yet (returning best-effort results from the current buffer and global index).
   - Commit `a8ad413f0d18c07a4adaa0d547e0096874d809c5` (`D148088`, 2023-06-12) moved preamble symbol indexing off the document-open critical path onto an asynchronous task so initial preamble readiness is not delayed by index slab construction.
3. **Domain 3 — Project Build Model (`GlobalCompilationDatabase`)**:
   - `GlobalCompilationDatabase::getCompileCommand` (`GlobalCompilationDatabase.h`) queries `compile_commands.json` (or an overlay/CDB plugin) for the authoritative compiler invocation of a file, including inferred header commands (`design/compile-commands.md`).
   - When no entry exists in the compilation database, `clangd` falls back to `GlobalCompilationDatabase::getFallbackCommand`, which synthesizes a heuristic `clang <file>` invocation. The header comment on `getFallbackCommand` explicitly warns that fallback commands are **unreliable** because they lack project include paths, `-D` defines, and language-standard flags.
4. **Domain 4 — Layered Symbol Index (`MergedIndex` over `FileIndex` and `BackgroundIndex`)**:
   - `clangd` merges multiple symbol index tiers (`design/indexing.md`, `index/FileIndex.cpp`, `index/Background.cpp`) via `MergedIndex`:
     - **Dynamic `FileIndex`**: Maintains two in-memory `FileSymbols` stores—one updated from parsed preambles of open files and one updated from main-file ASTs of open files.
     - **Static / Persisted `BackgroundIndex` (and optional Remote Index)**: Commit `6675be87477395658f6d3859b028ab8dee81ba19` (`D53651`, 2018-10-30) introduced a background indexing thread pool running at lowered OS thread priority that indexes translation units from `compile_commands.json` and persists symbol shards to disk.
   - Because `MergedIndex` queries dynamic open-file symbols alongside asynchronously updated background/remote shards, cross-file references and workspace symbol searches are inherently eventually consistent with respect to unopened files and in-flight background indexing.

#### 2.2 Publication Fence (`ParsingCallbacks::onMainAST`) and Service Levels
In `ClangdServer.cpp`, diagnostic and semantic-token callbacks are emitted through `ParsingCallbacks::onMainAST`, which is invoked synchronously on the file's serialized AST worker thread (`TUScheduler.h` guarantees that `onMainAST` callbacks for a given file are never delivered out of order for older document versions). This yields three distinct service levels for interactive verification and language servers:

| Service Level | `clangd` Realization | Allowed Freshness Vector | Appropriate Operations |
| :--- | :--- | :--- | :--- |
| **Advisory (Fast Interactive)** | `runWithPreamble(Stale / StaleOrAbsent)` + `MergedIndex` + optional `getFallbackCommand` | Current buffer text; preamble may lag `#include` edits; index shards may lag background indexing; build flags may be heuristic fallback | Code completion, signature help, workspace symbol search, speculative hints |
| **Snapshot-Exact (Per-File Semantic)** | `runWithAST` + `ParsingCallbacks::onMainAST` fence + `WantDiagnostics::Yes/Auto` | Exact main-file buffer revision; latest available or `Consistent` preamble; CDB flags recorded with snapshot | File diagnostics, semantic tokens, local hover, local AST refactoring (`ExtractFunction`) |
| **Model-Exact / Acceptance** | Authoritative CDB (`getCompileCommand` required; reject `getFallbackCommand`) + `Consistent` preamble + verified cross-TU index/build state | All four domains synchronized to the target workspace revision | Multi-file rename, soundness/proof acceptance, automated batch code transformation |

---

### 3. `gopls`: Folders, Views, Snapshots, and Cross-View Cache Separation

*(From `gopls-snapshots-views-workspace-evolution-2018-2026`)*

#### 3.1 Evolution from Multi-Module Pain (`v0.11.0`) to Separate Shared Caches (`v0.12.0`) and Zero-Config Views (`v0.15.0`)
Inspection of `golang/tools@98444708d405557b5ddd6179be1a6abc14150d5f` (`gopls/internal/cache/{session.go,view.go,snapshot.go,workspace.go}` and `gopls/doc/{workspace.md,design/implementation.md,design/design.md}`), alongside historical tags `gopls/v0.11.0` (`611cff71b9afeb81ae6eb16c5ce9376c051b1828`), `gopls/v0.12.0` (`236850463aea0b1949167349b44c37f97aefd9c5`), `gopls/v0.15.0` (`50e6ff28fb47219a23c4d0ed12da704b94087f76`), and the super-module design doc (`golang/proposal@0be13090fdb0cbae0d71641bb676d924bc1c94de`, `design/37720-gopls-workspaces.md` blob `5929e7e7894b8d51afbf2aa8ef38d1b34121ab4b`), traces three architectural generations:

1. **The Super-Module Experiment and Its Limits (`golang/go#32394`, Proposal 37720, `gopls/v0.11.0`)**:
   - Early `gopls` struggled when a workspace contained multiple `go.mod` files, nested sub-modules, or build-tagged variants (`golang/go#32394`). Proposal 37720 (`37720-gopls-workspaces.md`) synthesized an internal "super-module" (`gopls.mod` / `go.work` precursor) so one `View` could typecheck multiple modules together.
   - However, forcing an entire repository into one synthetic build context broke when sub-modules required incompatible Go versions, conflicting `replace` directives, or distinct `GOOS`/`GOARCH`/build-tag configurations, and `expandWorkspaceToModule` caused surprising workspace root expansion (`golang/go#57514`).
2. **Decoupling Views from File & Compilation Caches (`gopls/v0.12.0`, 2023-09-08 Scaling Blog)**:
   - In `gopls/v0.11.0` (`view.go` blob `500358c0e6006042167249ffb9d2b68bdea161a1`, `snapshot.go` blob `32967df48621634294964647c7d6490f56cf9660`), much of the workspace state was coupled to the `View` and in-memory package graph.
   - `gopls/v0.12.0` (`view.go` blob `1dc13aaee8c9587676f09c29bd8b24867ac46529`, `snapshot.go` blob `de9524bf0ae5b4660ba92be053c7ed81e8b892bb`) separated **file caches** and **content-addressed package analysis/export-data caches** (persisted to disk) from the in-memory `Snapshot` state of each `View`. As reported in the September 8, 2023 Go blog post (*Scaling gopls for the growing Go ecosystem*), this redesign reduced memory usage and startup latency by roughly 75% across a benchmark suite of 28 repositories while enabling fine-grained invalidation where editing a function body without changing imports or exported types avoids re-evaluating downstream dependent packages.
3. **Zero-Config Multi-View Workspaces (`golang/go#57979`, `gopls/v0.15.0` to Current `98444708d405`)**:
   - In `gopls/v0.15.0` (`50e6ff28fb47219a23c4d0ed12da704b94087f76`) and current `session.go` (`476d4baaa0baa58328e0478b343ee59e308a7754`) / `view.go` (`d1f264f4d23578fe735d1c95aeadfe7df0d3d433`), `selectViewDefs` automatically partitions open folders and active files into the minimal set of orthogonal `View`s (`GoWorkView`, `GoModView`, `GOPATHView`, `GoPackagesView`, `AdHocView`), dynamically re-evaluating View definitions whenever `go.mod`, `go.work`, or open files with distinct build tags change.

#### 3.2 Four State Scopes and Three Invalidation Layers in `gopls`
Current `gopls` (`98444708d405557b5ddd6179be1a6abc14150d5f`) maintains four distinct state abstractions:

| `gopls` Abstraction | Primary Source Location | Identity & Mutability | Architectural Role |
| :--- | :--- | :--- | :--- |
| **`Folder`** | `session.go` (`476d4baaa0ba`), `view.go` (`d1f264f4d235`) | Editor workspace root URI + user `Options` | Captures user/LSP workspace configuration without assuming a single build graph |
| **`View` (`viewDefinition`)** | `view.go` (`d1f264f4d235`), `workspace.go` (`6b2291e5bc94`) | Resolved build context (`GoEnv`, `GOOS`/`GOARCH`, build flags, `viewType`, root, `go.mod`/`go.work` set) | Owns the sequence of `Snapshot`s for one coherent Go build environment; analogous to Cargo's compilation `Unit` identity |
| **`Snapshot`** | `snapshot.go` (`4ec7ca7d764c`) | Immutable generation (`sequenceID` monotonic per `View`) | Pins an immutable map of overlaid/disk file handles, package metadata graph (`meta`), active package handles, and symbol/module tables |
| **Shared Caches** | `session.go` (`476d4baaa0ba`), `snapshot.go` (`4ec7ca7d764c`) | Process-wide `Cache` + file-system store | Content-addressed file reads, parsed AST caches, and persistent package typecheck/analysis summaries shared safely across concurrent `View`s and `Snapshot`s |

When files change in `Session.DidModifyFiles` (`session.go`), `gopls` executes a three-layer invalidation cascade:

| Invalidation Layer | Trigger in `session.go` / `snapshot.go` | Scope of Rebuilding |
| :--- | :--- | :--- |
| **Layer 1: Context / View-Definition Invalidation** | Added/removed `go.mod` or `go.work`, changed build flags/env, or opened a file requiring a new build-tag/ad-hoc `View` (`selectViewDefs`) | Recreates or replaces affected `View` instances while preserving unaffected `View`s and all content-addressed shared caches |
| **Layer 2: Snapshot / Metadata Graph Invalidation** | Edited `go.mod`/`go.work`, added/deleted `.go` file, or edited `package` / `import` declarations (`invalidateMetadata` in `snapshot.clone`) | Clones a new `Snapshot` (`sequenceID + 1`) and marks the package metadata graph dirty so `go list` re-runs lazily on next query |
| **Layer 3: Narrow Computation-Cache Invalidation** | Edited tokens inside a `.go` file without changing `package` or `import` headers | Clones `Snapshot` (`sequenceID + 1`), reuses the existing package metadata graph verbatim, invalidates only the edited package's direct handle, and relies on export-data content hashes in the shared compilation cache to short-circuit unchanged downstream packages |

---

### 4. The Haskell IDE Lineage: Environment Negotiation (`hie-bios`) vs Reactive In-Memory Graphs (`hls-graph`)

*(From `haskell-ide-lineage-environment-graph-boundaries-2017-2026`)*

#### 4.1 Four Historical Stages (`HIE` -> `ghcide` -> `hie-bios` -> `HLS` / `hls-graph`)
1. **`haskell-ide-engine` (`HIE`, `haskell/haskell-ide-engine@d84b84322ccac81bf4963983d55cc4e6e98ad418`)**:
   - As documented in `docs/Architecture.md` and `README.md`, `HIE` ran four main threads (LSP reader, request dispatcher, GHC dispatcher executing single-threaded `IdeM` over a mutable `IdeState` backed by `ghc-mod`, and response writer).
   - To serve queries when the current buffer failed to typecheck, `HIE` stored a `CachedModule` containing the last known good `TypecheckedModule` plus bidirectional source-position mapping functions (`newPosToOld` / `oldPosToNew`).
   - However, `HIE`'s reliance on `ghc-mod` and coarse mutable `IdeState` sessions broke down on complex multi-component Cabal/Stack/custom build setups and scaled poorly on large module graphs.
2. **`ghcide` (`haskell/ghcide@3ef4ef99c4b9cde867d29180c32586947df64b9e`) and Neil Mitchell's Shake Architecture (2019–2020)**:
   - Neil Mitchell's 2019 essay (*Shaking up the IDE*) and `ghcide` recast the IDE core as an in-memory dependency graph of fine-grained rules (`GetParsedModule`, `GetModSummary`, `TypeCheck`, `GetHieAst`) evaluated over a Shake database (`Development.Shake.Database`), while delegating compiler-flag discovery entirely to `hie-bios`.
   - Early `ghcide` explicitly documented its multi-component limitation: loading modules from multiple Cabal/Stack components with conflicting flags into a single GHC `HscEnv` session caused target collisions.
3. **`hie-bios` (`haskell/hie-bios@32dd07707423ffabb34e44af68fcbd027b60ded2`)**:
   - `hie-bios` (`README.md`) isolated the **cradle contract**: it is the build tool's responsibility (`cabal`, `stack`, `bios` script/program for Bazel/Obelisk/Nix, `direct` flags, or `multi` cradle routing subtrees) to report the exact GHC invocation flags, component dependencies, and working directory for any source file.
4. **`haskell-language-server` (`HLS`, `haskell/haskell-language-server@187fcd4a685c220caabb72999565604b3287aff2`) and `hls-graph`**:
   - Following the January 2020 unification (*One Haskell IDE to rule them all*) and September 2020 merge (*Don't use Ghcide anymore (directly)*), `HLS` absorbed `ghcide` and replaced raw Shake with `hls-graph` (`hls-graph/README.md`, `ghcide/src/Development/IDE/Core/Rules.hs`).
   - `hls-graph` deliberately removed Shake's on-disk build-system persistence and file-modification-time machinery, specializing the graph engine for **in-memory reactive IDE workloads** where only a small dirty-key set changes per edit and values are arbitrary in-memory Haskell heap objects (`HscEnv`, `TypecheckedModule`, HIE ASTs).

#### 4.2 Five Failure Classes Separated by the Haskell Lineage
The Haskell lineage demonstrates that IDE failures must be separated into five orthogonal architectural boundaries (`support/haskell-ide-lineage-environment-graph-boundaries-2017-2026/lineage-matrix.json`):
1. **Subject-Resolution Boundary (`hie-bios` Cradle)**: Mapping a file path to the right build target/component and compiler flags (`multi`-cradle routing).
2. **Session/Environment Isolation Boundary (`HscEnv` per Component)**: Preventing cross-component flag or package-database collisions by keying GHC sessions per resolved component rather than per workspace.
3. **Dependency-Model & Invalidation Boundary (`hls-graph`)**: Propagating dirty keys strictly in memory without disk-serialization overhead, while retaining last-good typed artifacts (`CachedModule` / stale rule values with position maps) when downstream modules fail to parse or typecheck.
4. **Scheduling & Cancellation Boundary**: Aborting obsolete rule evaluations when a newer edit arrives while keeping read queries non-blocking against cached rule values.
5. **Plugin Surface Boundary (`HLS` `IdeRule` plugins)**: Allowing formatting, linting, and code-action plugins to consume typed graph rules without mutating the underlying build-cradle or session graph.

---

### 5. Compiler-Backed IDE Boundaries in Kotlin K2 and Swift `SourceKit-LSP`

*(From `kotlin-swift-compiler-backed-ide-boundaries-2021-2026`)*

#### 5.1 Kotlin K2 Analysis API (`JetBrains/kotlin@bce49f3701fb8dc461fb98240fdc7c3c81c592f2`)
1. **From K1 `BindingContext` Maps to Lifetime-Scoped `KaSession` Tokens**:
   - In K1, IDE plugins queried a flat `BindingContext` map returned by the compiler frontend; holding `Descriptor` or `BindingContext` references across edits caused severe memory leaks and stale-state crashes (documented in the K2 migration guide).
   - In K2 (`analysis/analysis-api/src/org/jetbrains/kotlin/analysis/api/KaSession.kt`), all semantic queries must run inside a lexically scoped `analyze(useSiteElement) { ... }` block backed by a `KaSession` (`KaFirSessionProvider.kt`). `KaSymbol` and `KaType` instances are lifetime-bound (`KaLifetimeOwner` / `KaLifetimeToken`) and throw immediately if accessed outside their creating `KaSession` or after an edit invalidates the session.
2. **Explicit World Units (`KaModule`) and Lazy Phase Resolution (`BODY_RESOLVE`)**:
   - `KaModule.kt` defines the explicit compilation worlds (`KaSourceModule`, `KaLibraryModule`, `KaDanglingFileModule` for unsaved/scratch/injected fragments) and their dependency edges (`directRegularDependencies`, `directDependsOnDependencies`, `directFriendDependencies`).
   - As documented in `compiler/fir/checkers/module.md`, the K2 FIR frontend resolves declaration headers through progressive phases and runs full `BODY_RESOLVE` lazily on demand for the specific function or property being inspected, avoiding whole-module body typechecking on local edits.
3. **Session-Scoped Compiler Plugin Synthesis (`KaResolveExtension` & `KaSymbolOrigin.PLUGIN`)**:
   - When compiler plugins or code generators synthesize declarations, waiting for an external Gradle/Maven build leaves the IDE blind or watching stale on-disk generated files.
   - `KaResolveExtension.kt` and `KaSymbol.kt` (`KaSymbolOrigin.PLUGIN`) let IDE extensions synthesize package/classifier declarations lazily inside the active `KaSession`, declare explicit out-of-block modification trackers (`createModificationTracker`), and **shadow stale on-disk generated files** so in-memory source edits immediately reflect in synthesized symbols.

#### 5.2 Swift `SourceKit-LSP` and `sourcekitd` (`swiftlang/sourcekit-lsp@045c18e9e9ea35b896857b6cb982aa2373fb5816` & `swiftlang/swift@f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d`)
1. **Build Server Protocol (BSP) Target Preparation vs Compiler Invocation**:
   - `SourceKit-LSP` (`Contributor Documentation/Implementing a BSP server.md`, `SwiftPMBuildServer.swift`, `SwiftPMIntegrationTests.swift`) separates build-system orchestration from `sourcekitd`. The BSP server handles `buildTarget/prepare` (generating Swift module interfaces, C header maps, and build artifacts) and `textDocument/sourceKitOptions` (returning exact compiler arguments for a file within a target).
2. **Constrained In-Memory `ASTContext` Reuse (`SwiftASTManager::canUseASTWithSnapshots`)**:
   - In the Swift compiler's SourceKit layer (`tools/SourceKit/lib/SwiftLang/SwiftASTManager.h`, `SwiftASTManager.cpp`, `SwiftSourceDocInfo.cpp`, and test `cursor_reuses_astcontext.swift`), `SwiftASTManager::canUseASTWithSnapshots` checks whether a newly edited buffer snapshot can reuse a previously built `ASTContext`.
   - Reuse succeeds **only** when the edit is strictly confined inside a function/accessor body without altering top-level declarations or shifting source offsets of outer declarations. Any top-level signature edit triggers a full `ASTContext` rebuild for that translation unit.
3. **Macro Expansion Reference Documents (`SwiftLanguageService.swift`)**:
   - Rather than mutating user source files on disk, `SwiftLanguageService.swift` materializes Swift macro expansions and generated interfaces as read-only virtual reference documents keyed by deterministic URI schemes so go-to-definition and hover can inspect synthesized code pinned to the originating snapshot.

#### 5.3 What External Orchestration Can vs Cannot Obtain Without Frontend Support
| Capability | Obtainable by External LSP/Build Orchestration Alone? | Why / Required Frontend Contract |
| :--- | :--- | :--- |
| Target flag discovery, dependency preparation (`buildTarget/prepare`), and multi-target routing | **Yes** | Handled by `SourceKit-LSP` BSP / `hie-bios` / `gopls` `View` selection outside the compiler frontend |
| Virtual reference documents for macro/codegen output | **Yes (Once spans/text are emitted)** | Orchestrator can host virtual URIs (`SwiftLanguageService.swift`) if the compiler emits deterministic expansion trees |
| Sub-file function-body incrementality (`BODY_RESOLVE` / `canUseASTWithSnapshots` / `hir-def` firewall) | **No** | Requires the frontend's own symbol table and AST/FIR resolver to decouple declaration spines from body checking |
| Lifetime-safe fine-grained semantic handles (`KaSession` + `KaLifetimeToken`) | **No** | Requires internal compiler IR pointers to be guarded by session validity tokens rather than raw arena/map references |
| In-memory shadowing of stale on-disk generated files (`KaResolveExtension`) | **No** | Requires the frontend's name resolver to intercept package/file lookup before reading compiled jar/disk artifacts |

---

### 6. `Roslyn`: Red-Green Trees, Immutable `Solution` Snapshots, and Checksum-Driven Out-of-Process Synchronization

*(From `roslyn-immutable-snapshots-workspace-boundaries-2012-2026`)*

#### 6.1 Four Structural Layers in `dotnet/roslyn` (`7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b`)
Inspection of `dotnet/roslyn@7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b` (alongside initial open-source commit `4a74095f0e3598e514f3147479beee208c0ad7ed`, early out-of-process design commit `c141605a972871644cc43f2caec597c88e9662db`, and Eric Lippert's 2012-06-08 persistence post) establishes Roslyn's four-layer snapshot hierarchy:

1. **Layer 1 — Syntax (`docs/compilers/Design/Red-Green Trees.md`)**:
   - **Green nodes** are bottom-up, immutable, parentless, position-independent, and maximally shared across edits and across documents (storing only relative widths and syntax kinds).
   - **Red nodes** are top-down, immutable, parent-pointered, absolute-offset façade nodes constructed lazily on demand as callers traverse down from the syntax root, and discarded by GC when no longer referenced.
   - An edit reparses only the affected token spine, builds a new green spine sharing all unaffected green subtrees, and creates a fresh red root.
2. **Layer 2 — Single-Project Semantic Snapshot (`Compilation.cs`)**:
   - `Compilation` is an immutable value representing a single project's syntax trees, metadata references, and compilation options. `SemanticModel` instances obtained from a `Compilation` lazily bind method bodies and cache symbols internally while presenting a thread-safe immutable API.
3. **Layer 3 — Workspace-Wide Graph Snapshot (`Solution.cs` & `SolutionCompilationState.cs`)**:
   - `Solution`, `Project`, and `Document` form an immutable persistent graph representing the entire multi-project workspace at a point in time.
   - Inside `SolutionCompilationState.cs`, Roslyn uses `AsyncLazy<Compilation>`, weak references, and partial declaration-only skeleton compilations so creating a new `Solution` on a keystroke is $O(1)$—copying state descriptors without eagerly rebuilding `Compilation` objects for untouched projects.
4. **Layer 4 — Mutable Host Shell (`Workspace.cs`)**:
   - `Workspace` is the only mutable coordination point. It holds `_latestSolution` (`CurrentSolution`), serializes mutations through internal locks (`_serializationLock`), listens to host buffer/project events, and dispatches asynchronous workspace-change notifications.
   - Any IDE feature (completion, diagnostics, refactoring) captures `var solution = workspace.CurrentSolution;` at the start of its operation and executes against that self-consistent immutable snapshot without holding locks or blocking subsequent user edits.

#### 6.2 Checksum-Addressed Out-of-Process Synchronization and Build/Buffer Desynchronization Detection
1. **Hierarchical `SolutionChecksum` Pull Protocol (`docs/ide/api-designs/Out-of-Process Synchronization.md`, `RemoteWorkspace.cs`, `SolutionAssetCache.cs`, `RemoteWorkspaceManager.cs`)**:
   - When offloading heavy IDE analysis to the `ServiceHub` out-of-process worker (`RemoteWorkspace.RunWithSolutionAsync`), Roslyn never serializes an entire `Solution` over IPC.
   - Instead, the host computes a hierarchical Merkle-like `SolutionChecksum` tree (checksums for solution state, project states, document text/options, and metadata references) and sends only the root `SolutionChecksum` to `RemoteWorkspace`.
   - The remote process consults its local `SolutionAssetCache` (`RemoteWorkspaceManager.cs` sweeps the cache every **30 seconds** and purges assets unused for **1 minute**), identifies only the missing checksums, fetches those specific delta assets from the host, and reconstructs a structurally identical `Solution` snapshot in the remote address space.
2. **Detecting Build vs Workspace Desynchronization (`CommittedSolution.cs`)**:
   - Because in-memory `Workspace.CurrentSolution` buffers advance ahead of on-disk MSBuild outputs, features like Edit-and-Continue (`src/Features/Core/Portable/EditAndContinue/CommittedSolution.cs`) cannot assume `CurrentSolution` matches the running binary.
   - `CommittedSolution` reads the cryptographic document checksums embedded in the compiled `.pdb` debug symbols and matches or synthesizes the exact historical `Solution` snapshot corresponding to the last committed build on disk.
3. **Retiring Ad-Hoc Persistent DBs (`IPersistentStorageService.cs` & `AbstractPersistentStorageService.cs`)**:
   - Roslyn marked legacy `IPersistentStorageService` paths obsolete in favor of `IChecksummedPersistentStorageService` keyed by lightweight `SolutionKey`/`ProjectKey`/`DocumentKey` descriptors and content checksums.

---

### 7. TypeScript: Host-Owned Language World (`6.0.2`) and the Native Go Port Transition (`7.0.2`)

*(From `typescript-host-owned-language-world-2014-2026` and `typescript-602-to-702-source-review`)*

#### 7.1 The Host-Owned Language World in TypeScript 6.0.2 (`microsoft/TypeScript@607a22a90d1a5a1b507ce01bb8cd7ec020f954e7`)
Inspection of `microsoft/TypeScript@607a22a90d1a5a1b507ce01bb8cd7ec020f954e7` (`src/services/types.ts` blob `5329fe901b2403fad070e2fdb3b61212102e7c57`, `src/services/services.ts` blob `9885093ed618047cfebad26ac731032cd7071ab6`, `src/server/editorServices.ts` blob `aa578c7ed0815f064b88eda052c7d8ac9029558f`, `src/compiler/watchPublic.ts` blob `4bcedabb7eb0f4d168a2f6b43a54cadd924a1eb5`, `src/compiler/builder.ts` blob `34adf6e49b7daa33c0b9d65bb3675cfde7a8b85b`) and `microsoft/TypeScript-wiki@966988bcca7c835fd22ab066bb6a9ff4d5ba511d` (`Using-the-Language-Service-API.md` blob `c3584b2b433dd304216e0affe3302a56a2ace681`) reveals an inverted ownership boundary compared to standalone compiler daemons:

1. **`LanguageServiceHost` and `IScriptSnapshot` (`src/services/types.ts`, `src/services/services.ts`)**:
   - `ts.createLanguageService(host, documentRegistry)` does not read files or manage project state itself; it polls `LanguageServiceHost` (`getScriptFileNames`, `getScriptVersion`, `getScriptSnapshot`, `getProjectVersion`, `getCompilationSettings`) on demand when `synchronizeHostData()` runs.
   - `IScriptSnapshot` represents an immutable character snapshot of a script at a specific version (`getText`, `getLength`, `getChangeRange(oldSnapshot)`), enabling incremental AST reparsing via `createLanguageServiceSourceFile` and `updateLanguageServiceSourceFile` in `services.ts` while reusing unchanged AST nodes across a shared `DocumentRegistry`.
2. **`ProjectService`, `ScriptInfo`, and Three Project Kinds (`src/server/editorServices.ts`)**:
   - In `tsserver`, `ProjectService` owns the mutable `ScriptInfo` table (bridging disk files and open editor overlays via `openClientFile`) and assigns each `ScriptInfo` to one or more projects:
     - **Configured Project**: Governed by a discovered `tsconfig.json` or `jsconfig.json`.
     - **External Project**: Supplied explicitly by an IDE host (such as Visual Studio project files).
     - **Inferred Project**: Synthesized automatically for loose/standalone files that do not belong to any `tsconfig.json` so every open buffer still has a valid `LanguageService` world.
3. **Three Consistency Joins Across Language Service and Watch/Build APIs**:
   - **Join 1 (Buffer-to-Project Join)**: `ScriptInfo` edits update script versions; `Project.updateGraph()` and `synchronizeHostData()` reconcile `ScriptInfo` snapshots into each owning `Project`'s `Program` only when that project is queried.
   - **Join 2 (Project-to-Environment Join)**: Module resolution caches, `tsconfig.json` root file globs, and `package.json` auto-imports depend on host directory/file watchers (`WatchHost` / `WatchCompilerHost` in `watchPublic.ts`).
   - **Join 3 (Semantic-State-to-Publication Join)**: Incremental `BuilderProgram` state (`src/compiler/builder.ts`) tracks per-file semantic signature hashes (`affectedFilesPendingEmit`) to decide which downstream files require re-typechecking or `.d.ts` re-emit.

#### 7.2 The TypeScript 7.0 Native Go Port Boundary (`v7.0.2`)
As documented in the TypeScript team's announcements (2025-03-11 native port announcement, 2026-03-23 TypeScript 6.0 release notes positioning 6.0 as the last JS-codebase major release, and 2026-07-08 TypeScript 7.0 release notes) and verified in `support/typescript-602-to-702-source-review/matrix.json`:
- The latest stable release `7.0.2` has two official upstream Git identities:
  - `microsoft/TypeScript` tag `v7.0.2` at commit `1e4744d68260a7cb91b62b12edc3f6a2187faaf1` (mirroring the Go implementation into the main repository).
  - `microsoft/typescript-go` tag `typescript/v7.0.2` at commit `2bd066d87f5bafd315be9f40889d0a60b9e58e0b`.
- In `7.0.2`, the legacy JavaScript file paths (`src/services/types.ts`, `src/services/services.ts`, `src/server/editorServices.ts`, `src/compiler/watchPublic.ts`, `src/compiler/builder.ts`) are replaced by the native Go implementation (`internal/project/project.go`, `internal/lsp/server.go`, `cmd/tsgo/lsp.go`), which serves editors directly over LSP rather than the legacy `tsserver` JS `LanguageServiceHost` API.
- Furthermore, TypeScript 7.0 explicitly shipped **without** a replacement programmatic Language Service API, advising downstream tools that embed `ts.createLanguageService` / `LanguageServiceHost` to run TypeScript 6.0 side-by-side until the 7.1+ API surface stabilizes.

---

### 8. Current-Source Delta Reviews Across All Studied Lineages

*(Coalescing `editor-engines-current-source-review`, `haskell-hls-hie-bios-current-source-review`, `kotlin-swift-current-source-review`, `roslyn-current-source-review`, and `typescript-602-to-702-source-review`)*

The five current-source review packages audited every baseline commit and claim-mapped source file against the latest upstream branch heads and release tags as of the September 30, 2026 freeze (`version-inventory-ebcdcad-581.csv`):

| Review Cohort | Upstream Repository | Baseline Commit / Tag | Observed Target Head / Tag | Forward Commits | Claim-Mapped Path Overlap & Verdict |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Editor Engines (`clangd`)** | `llvm/llvm-project` | `ded546ad82656ce6605ee2f2aa60c78dec70d95f` | `main` `229b9b2f4e20840a8280174fa08385fd9e36844b` | +181 commits | **0 overlap** across all 5 mapped `clangd` files (`TUScheduler.h`, `ClangdServer.cpp`, `GlobalCompilationDatabase.h`, `FileIndex.cpp`, `Background.cpp`); only 3 unrelated test/tweak files (`ExtractFunction.cpp`, `FindTargetTests.cpp`, `ExtractFunctionTests.cpp`) changed. Verdict: `unchanged_in_substance` |
| **Editor Engines (`gopls`)** | `golang/tools` | `98444708d405557b5ddd6179be1a6abc14150d5f` | `master` `134264d72fba423ca1ad358683cd3c32699b010e` | +5 commits (17 files) | **0 overlap** across all 7 mapped `gopls` files (`session.go`, `view.go`, `snapshot.go`, `workspace.go`, `workspace.md`, `implementation.md`, `design.md`). Verdict: `unchanged_in_substance` |
| **Editor Engines (`rust-analyzer`)** | `rust-lang/rust-analyzer` | `03fcb77246f2568adb0e9b2fa60d19c6cc1686f4` | `master` `03fcb77246f2568adb0e9b2fa60d19c6cc1686f4` | 0 commits | Identical commit (`03fcb77246f2568adb0e9b2fa60d19c6cc1686f4`). Verdict: `unchanged_in_substance` |
| **Haskell (`HLS`)** | `haskell/haskell-language-server` | `187fcd4a685c220caabb72999565604b3287aff2` | `master` `187fcd4a685c220caabb72999565604b3287aff2` | 0 commits | Identical commit and tree across all 4 mapped paths (`README.md`, `cabal.project`, `ghcide/src/Development/IDE/Core/Rules.hs`, `hls-graph/README.md`). Verdict: `unchanged_in_substance` |
| **Haskell (`hie-bios`)** | `haskell/hie-bios` | `32dd07707423ffabb34e44af68fcbd027b60ded2` | `master` `32dd07707423ffabb34e44af68fcbd027b60ded2` | 0 commits | Identical commit (`32dd07707423ffabb34e44af68fcbd027b60ded2`). Verdict: `unchanged_in_substance` |
| **Kotlin & Swift (`kotlin`)** | `JetBrains/kotlin` | `bce49f3701fb8dc461fb98240fdc7c3c81c592f2` | `master` `79b33f2836ef88425c100924bb8d29bcdf52bf48` | +106 commits | **0 blob changes** across all 6 mapped K2 Analysis API / FIR files (`KaSession.kt`, `KaModule.kt`, `KaFirSessionProvider.kt`, `module.md`, `KaResolveExtension.kt`, `KaSymbol.kt`). Verdict: `unchanged_in_substance` |
| **Kotlin & Swift (`swift`)** | `swiftlang/swift` | `f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d` | `main` `0fcad6fb60755587d39a758761b219bf433cf9dc` | +36 commits (246 files) | **0 blob changes** across all 4 mapped SourceKit files (`SwiftASTManager.h`, `SwiftASTManager.cpp`, `SwiftSourceDocInfo.cpp`, `cursor_reuses_astcontext.swift`). Verdict: `unchanged_in_substance` |
| **Kotlin & Swift (`sourcekit-lsp`)** | `swiftlang/sourcekit-lsp` | `045c18e9e9ea35b896857b6cb982aa2373fb5816` | `main` `045c18e9e9ea35b896857b6cb982aa2373fb5816` | 0 commits | Identical commit across all 6 mapped `SourceKit-LSP` files. Verdict: `unchanged_in_substance` |
| **Roslyn (`main` & NuGet `5.9.0`)** | `dotnet/roslyn` | `7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b` | `main` `36d26c5466e4d25940657ccb8d5b9557ccaf7be1` (and stable NuGet `5.9.0` at `35d9211b841e7613c1d2f8f5af6d628ace696c4c`) | +7 commits on `main` (49 files) | **0 overlap** on `main` across all 13 mapped Roslyn paths (`Roslyn-Overview.md`, `Red-Green Trees.md`, `Compilation.cs`, `Solution.cs`, `SolutionCompilationState.cs`, `Workspace.cs`, `Out-of-Process Synchronization.md`, `RemoteWorkspace.cs`, `SolutionAssetCache.cs`, `RemoteWorkspaceManager.cs`, `CommittedSolution.cs`, `IPersistentStorageService.cs`, `AbstractPersistentStorageService.cs`). Verdict: `unchanged_in_substance` |
| **TypeScript (`6.0.2` -> `7.0.2`)** | `microsoft/TypeScript` & `microsoft/typescript-go` | `v6.0.2` (`607a22a90d1a5a1b507ce01bb8cd7ec020f954e7`) | `v7.0.2` (`1e4744d68260a7cb91b62b12edc3f6a2187faaf1`) / `typescript/v7.0.2` (`2bd066d87f5bafd315be9f40889d0a60b9e58e0b`) | Architectural language port (JS -> Go) | Legacy JS paths (`src/services/*`, `src/server/*`) replaced by Go packages (`internal/project/project.go`, `internal/lsp/server.go`, `cmd/tsgo/lsp.go`); recorded as `unresolved_at_target` (`unexecuted_in_this_review` / `unassessed`) pending full Go-port source mapping |

---

## Boundaries

1. **Historical Reconstruction vs Live Benchmarking**:
   - The architectural comparisons across `RLS`, `rust-analyzer`, `clangd`, `gopls`, `HIE`/`ghcide`/`HLS`, Kotlin K2, Swift `SourceKit-LSP`, `Roslyn`, and TypeScript are grounded in pinned repository commits, design RFCs, and maintainer engineering analyses rather than new cross-language latency benchmarks executed in this environment.
   - Reported quantitative ratios (such as `clangd`'s ~2x in-memory preamble footprint in `D39843`, `gopls/v0.12.0`'s ~75% memory and startup reduction across 28 repositories, and the 2019 `sourcekitd` stress-tester report of 91 crashes/hangs) are cited as maintainer-published empirical observations on their respective benchmark suites.
2. **Archived Upstream Lineages**:
   - `rust-lang/rls` (`04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc`), `haskell/haskell-ide-engine` (`d84b84322ccac81bf4963983d55cc4e6e98ad418`), and standalone `haskell/ghcide` (`3ef4ef99c4b9cde867d29180c32586947df64b9e`) are permanently archived upstream repositories. Their findings establish negative and transitional architectural boundaries, while live evolution occurs in `rust-lang/rust-analyzer` and `haskell/haskell-language-server`.
3. **Roslyn Stable Release Branch vs `main`**:
   - In `support/roslyn-current-source-review/official-stable-compare.json`, the official NuGet `Microsoft.CodeAnalysis.Workspaces.Common` `5.9.0` package is built from release-branch commit `35d9211b841e7613c1d2f8f5af6d628ace696c4c`, which diverged from `main` before the `7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b` baseline commit. Consequently, the forward delta check is verified against `dotnet/roslyn` `main` (`36d26c5466e4d25940657ccb8d5b9557ccaf7be1`), where all 13 mapped files are byte-for-byte unchanged.
4. **TypeScript `6.0.2` to `7.0.2` Native Port Discontinuity**:
   - Because TypeScript `7.0.2` (`microsoft/TypeScript@1e4744d68260a7cb91b62b12edc3f6a2187faaf1` / `microsoft/typescript-go@2bd066d87f5bafd315be9f40889d0a60b9e58e0b`) is a complete codebase replacement from TypeScript/JavaScript (`src/services/*`, `src/server/*`) to Go (`internal/project/project.go`, `internal/lsp/server.go`, `cmd/tsgo/lsp.go`) and intentionally omits a programmatic Language Service API in 7.0, a path-by-path diff against the 6.0.2 JavaScript files does not exist. In `support/typescript-602-to-702-source-review/matrix.json`, the 6.0.2-to-7.0.2 row is explicitly recorded as `unresolved_at_target` (`execution_status: "unexecuted_in_this_review"`, `product_result: "unassessed"`), and during local preflight the review environment measured 8 GiB RAM with 156,667 free/inactive/speculative 16 KiB pages (~29.88%, just below the 30% local heavy-checkout admission threshold) and 18,136,008 KiB available disk.

---

## Evidence

### Primary Source Repositories and Pinned Commits
1. **Rust (`RLS`, `rust-analyzer`, `rfcs`, `rustc-dev-guide`)**:
   - `rust-lang/rfcs`: `4e4c756e6df95167dda553251cc37a75a294f002` and `82d48b36568286b93fc2ce55f89594024f421a3b` (`text/1317-ide.md`); `ba27c4c027704c716fcc1f54be601939fdc29c57` and `b6fffdf18f8b867648de0d95657cc13a64cae4e2` (`text/2912-rust-analyzer.md`, blob `9f5986eeacafbea1ad99c6cbc4c24d2eab278c99`).
   - `rust-lang/rls`: `04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc` (`architecture.md` blob `a7bde5799d73cbaf7319dad2773fd58a89a978a8`, `README.md`, issue `rust-lang/rls#1714`).
   - `rust-lang/rust-analyzer`: `5e21ae9418380b8c183c4663ca03bd63dd240aa9`, `6d14bb0cd0af55fe45711ac048236f9dd9d24a3f`, issue `rust-lang/rust-analyzer#10765`, and current `03fcb77246f2568adb0e9b2fa60d19c6cc1686f4` (`docs/book/src/contributing/architecture.md` blob `8b6ea56c851650cac23c27cc1ffb0a7f1b2a854c`).
   - `rust-lang/rustc-dev-guide`: `0fb89036f8e46a80ee815ed99ff7d9dae9d172ae` (`src/solve/sharing-crates-with-rust-analyzer.md`).
2. **`clangd` (`llvm/llvm-project` & `llvm/clangd-www`)**:
   - `llvm/llvm-project`: baseline `ded546ad82656ce6605ee2f2aa60c78dec70d95f` and target head `229b9b2f4e20840a8280174fa08385fd9e36844b` (`clang-tools-extra/clangd/{TUScheduler.h,ClangdServer.cpp,GlobalCompilationDatabase.h,index/FileIndex.cpp,index/Background.cpp}`); historical commits `e9eb7f0cb815641827fa3d031c38190c10900c14` (`D39843`), `6675be87477395658f6d3859b028ab8dee81ba19` (`D53651`), `a2b048bc4bdf9320249d0ff512fab6f16c2e47` (`D54746`), `c627b120eb8b7add3f9cf893721335c367d9f037` (`D75602`), and `a8ad413f0d18c07a4adaa0d547e0096874d809c5` (`D148088`).
   - `llvm/clangd-www`: `ae5866d4552e30a173b8e9c3cec872a82e4c0120` (`design/threads.md`, `design/indexing.md`, `design/compile-commands.md`, `faq.md`, `remote-index.md`).
3. **`gopls` (`golang/tools` & `golang/proposal`)**:
   - `golang/tools`: baseline `98444708d405557b5ddd6179be1a6abc14150d5f` and target head `134264d72fba423ca1ad358683cd3c32699b010e` (`gopls/internal/cache/session.go` `476d4baaa0baa58328e0478b343ee59e308a7754`, `view.go` `d1f264f4d23578fe735d1c95aeadfe7df0d3d433`, `snapshot.go` `4ec7ca7d764c92d3cc2c27c42602dc959751992c`, `workspace.go` `6b2291e5bc9401f552c92eae3c8aefb213cf2c83`, `gopls/doc/workspace.md` `1e19fd3657b159a7eaeabc1bf3b56c59a5e5f024`, `gopls/doc/design/implementation.md` `887c02cd35c14edecdd1342d5664e3fb174f4bf8`, `gopls/doc/design/design.md` `8ef3c32023b23f72837112c479e46519d1f2d46b`); historical tags `gopls/v0.11.0` (`611cff71b9afeb81ae6eb16c5ce9376c051b1828`), `gopls/v0.12.0` (`236850463aea0b1949167349b44c37f97aefd9c5`), `gopls/v0.15.0` (`50e6ff28fb47219a23c4d0ed12da704b94087f76`).
   - `golang/proposal`: `0be13090fdb0cbae0d71641bb676d924bc1c94de` (`design/37720-gopls-workspaces.md` blob `5929e7e7894b8d51afbf2aa8ef38d1b34121ab4b`).
4. **Haskell IDE Lineage**:
   - `haskell/haskell-ide-engine`: `d84b84322ccac81bf4963983d55cc4e6e98ad418` (`docs/Architecture.md`, `README.md`).
   - `haskell/ghcide`: `3ef4ef99c4b9cde867d29180c32586947df64b9e` (`README.md`).
   - `haskell/hie-bios`: `32dd07707423ffabb34e44af68fcbd027b60ded2` (`README.md`).
   - `haskell/haskell-language-server`: `187fcd4a685c220caabb72999565604b3287aff2` (`README.md`, `cabal.project`, `ghcide/src/Development/IDE/Core/Rules.hs`, `hls-graph/README.md`).
5. **Kotlin & Swift**:
   - `JetBrains/kotlin`: baseline `bce49f3701fb8dc461fb98240fdc7c3c81c592f2` and target head `79b33f2836ef88425c100924bb8d29bcdf52bf48` (`KaSession.kt`, `KaModule.kt`, `KaFirSessionProvider.kt`, `compiler/fir/checkers/module.md`, `KaResolveExtension.kt`, `KaSymbol.kt`).
   - `swiftlang/sourcekit-lsp`: `045c18e9e9ea35b896857b6cb982aa2373fb5816` (`README.md`, `Contributor Documentation/Implementing a BSP server.md`, `Documentation/Configuration File.md`, `SwiftPMBuildServer.swift`, `SwiftPMIntegrationTests.swift`, `SwiftLanguageService.swift`).
   - `swiftlang/swift`: baseline `f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d` and target head `0fcad6fb60755587d39a758761b219bf433cf9dc` (`SwiftASTManager.h`, `SwiftASTManager.cpp`, `SwiftSourceDocInfo.cpp`, `cursor_reuses_astcontext.swift`).
6. **`Roslyn`**:
   - `dotnet/roslyn`: initial import `4a74095f0e3598e514f3147479beee208c0ad7ed`, early OOP commit `c141605a972871644cc43f2caec597c88e9662db`, baseline `7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b`, target `main` `36d26c5466e4d25940657ccb8d5b9557ccaf7be1`, and NuGet `5.9.0` commit `35d9211b841e7613c1d2f8f5af6d628ace696c4c`.
7. **TypeScript**:
   - `microsoft/TypeScript`: `v6.0.2` (`607a22a90d1a5a1b507ce01bb8cd7ec020f954e7`, `src/services/types.ts`, `src/services/services.ts`, `src/server/editorServices.ts`, `src/compiler/watchPublic.ts`, `src/compiler/builder.ts`) and `v7.0.2` (`1e4744d68260a7cb91b62b12edc3f6a2187faaf1`).
   - `microsoft/typescript-go`: `typescript/v7.0.2` (`2bd066d87f5bafd315be9f40889d0a60b9e58e0b`, `internal/project/project.go`, `internal/lsp/server.go`, `cmd/tsgo/lsp.go`).
   - `microsoft/TypeScript-wiki`: `966988bcca7c835fd22ab066bb6a9ff4d5ba511d` (`Using-the-Language-Service-API.md`).

### Staged `support/` Artifacts
- **Rust (`RLS` / `rust-analyzer`)**:
  - `support/rls-rust-analyzer-architecture-evolution-2015-2026/judgment-matrix.json`
  - `support/rls-rust-analyzer-architecture-evolution-2015-2026/source-map.json`
  - `support/rls-rust-analyzer-architecture-evolution-2015-2026/timeline.json`
  - `support/rls-rust-analyzer-architecture-transition-2015-2026/evidence-map.json`
  - `support/rls-to-rust-analyzer-editor-engine-history-2015-2026/evidence-ledger.json`
- **`clangd` & `gopls` & Editor Engines Review**:
  - `support/clangd-authority-freshness-2017-2026/evidence-map.json`
  - `support/gopls-snapshots-views-workspace-evolution-2018-2026/evidence-map.json`
  - `support/editor-engines-current-source-review/baseline-report-paths.txt`
  - `support/editor-engines-current-source-review/check_matrix.py`
  - `support/editor-engines-current-source-review/frozen-cohort.csv`
  - `support/editor-engines-current-source-review/matrix.json`
  - `support/editor-engines-current-source-review/official-source-observation.json`
  - `support/editor-engines-current-source-review/version-inventory-ebcdcad-581.csv`
- **Haskell (`HIE`, `ghcide`, `hie-bios`, `HLS`)**:
  - `support/haskell-ide-lineage-environment-graph-boundaries-2017-2026/lineage-matrix.json`
  - `support/haskell-ide-lineage-environment-graph-boundaries-2017-2026/source-map.json`
  - `support/haskell-hls-hie-bios-current-source-review/baseline-report-paths.txt`
  - `support/haskell-hls-hie-bios-current-source-review/check_matrix.py`
  - `support/haskell-hls-hie-bios-current-source-review/frozen-cohort.csv`
  - `support/haskell-hls-hie-bios-current-source-review/matrix.json`
  - `support/haskell-hls-hie-bios-current-source-review/official-source-observation.json`
  - `support/haskell-hls-hie-bios-current-source-review/version-inventory-ebcdcad-581.csv`
- **Kotlin & Swift**:
  - `support/kotlin-swift-compiler-backed-ide-boundaries-2021-2026/evidence-map.json`
  - `support/kotlin-swift-current-source-review/baseline-report-paths.txt`
  - `support/kotlin-swift-current-source-review/check_matrix.py`
  - `support/kotlin-swift-current-source-review/frozen-cohort.csv`
  - `support/kotlin-swift-current-source-review/matrix.json`
  - `support/kotlin-swift-current-source-review/official-source-observation.json`
  - `support/kotlin-swift-current-source-review/version-inventory-ebcdcad-581.csv`
- **`Roslyn`**:
  - `support/roslyn-immutable-snapshots-workspace-boundaries-2012-2026/evidence-map.json`
  - `support/roslyn-current-source-review/baseline-report-paths.txt`
  - `support/roslyn-current-source-review/check_matrix.py`
  - `support/roslyn-current-source-review/frozen-cohort.csv`
  - `support/roslyn-current-source-review/matrix.json`
  - `support/roslyn-current-source-review/official-main-compare.json`
  - `support/roslyn-current-source-review/official-stable-compare.json`
  - `support/roslyn-current-source-review/version-inventory-ebcdcad-581.csv`
- **TypeScript**:
  - `support/typescript-host-owned-language-world-2014-2026/evidence-map.json`
  - `support/typescript-602-to-702-source-review/baseline-report-paths.txt`
  - `support/typescript-602-to-702-source-review/check_matrix.py`
  - `support/typescript-602-to-702-source-review/frozen-cohort.csv`
  - `support/typescript-602-to-702-source-review/matrix.json`
  - `support/typescript-602-to-702-source-review/version-inventory-ebcdcad-581.csv`

---

## Revalidation

To revalidate or refresh this synthesized report when upstream language servers or compiler frontends evolve:

1. **Re-Run the Current-Source Matrix Validators**:
   - Execute the staged matrix verification scripts:
     - `python3 support/editor-engines-current-source-review/check_matrix.py`
     - `python3 support/haskell-hls-hie-bios-current-source-review/check_matrix.py`
     - `python3 support/kotlin-swift-current-source-review/check_matrix.py`
     - `python3 support/roslyn-current-source-review/check_matrix.py`
     - `python3 support/typescript-602-to-702-source-review/check_matrix.py`
2. **Trigger Conditions for Re-Auditing**:
   - **`rust-analyzer` / `rustc`**: Any change to `ide::AnalysisHost` / `ide::Analysis` snapshot cancellation, `base-db` Salsa inputs, or the `rustc_type_ir::Interner` sharing boundary between `rustc` and `rust-analyzer`.
   - **`clangd`**: Any modification to `TUScheduler::runWithAST`, `TUScheduler::runWithPreamble`, `PreambleConsistency`, `ParsingCallbacks::onMainAST`, `GlobalCompilationDatabase::getFallbackCommand`, or `MergedIndex`.
   - **`gopls`**: Any change to `Session.DidModifyFiles`, `selectViewDefs`, `Snapshot.clone` metadata-vs-narrow invalidation, or cross-View shared file/package caches in `gopls/internal/cache/`.
   - **Haskell (`HLS` / `hie-bios`)**: Any redesign of `hls-graph`'s dirty-key invalidation or `hie-bios`'s multi-cradle component discovery contract.
   - **Kotlin K2 & Swift `SourceKit-LSP`**: Any change to `KaSession` lifetime tokens, `KaResolveExtension` in-memory generated-file shadowing, `SwiftASTManager::canUseASTWithSnapshots`, or BSP `buildTarget/prepare` / `textDocument/sourceKitOptions`.
   - **`Roslyn`**: Any change to `Workspace.CurrentSolution` snapshot publication, `SolutionCompilationState` lazy compilation caching, `SolutionChecksum` / `RemoteWorkspace` asset synchronization, or `CommittedSolution` PDB checksum verification.
   - **TypeScript (`typescript-go` 7.x+)**: Inspect `microsoft/typescript-go` (`internal/project/project.go`, `internal/lsp/server.go`, `cmd/tsgo/lsp.go`) and future TypeScript 7.1+ releases once the native Go programmatic Language Service API is published, and replace the `unresolved_at_target` bridge status with a direct Go-source evidence map.
