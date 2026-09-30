# gopls snapshots, views, and why one open file can denote several builds

## Summary

gopls evolved away from treating an editor workspace folder as the unit of analysis. Its current architecture separates at least four concepts that an editor presents as one workspace: an LSP `Folder` carrying UI-scoped configuration, a `View` representing one logical Go build, a `Snapshot` representing one immutable-enough generation of that build's file and derived state, and shared caches that reuse computations across snapshots and even processes. An open file can participate in more than one build. Changes to open files can cause gopls to create or remove Views; changes to build-defining files can reconstruct Views; ordinary source edits advance and invalidate Snapshots within every relevant View.

That split is the result of two distinct redesigns. The v0.12 scalability redesign replaced the earlier whole-program in-memory model with separate compilation, persistent per-package summaries, and pruned invalidation. That reduced the cost of keeping several build contexts live. The v0.15 zero-configuration workspace redesign then decoupled Views from LSP workspace folders and made the set of Views depend on both folders and open files. The redesign deliberately permits several Views for one folder and, conversely, several folders to resolve to one `go.work` View.

The history matters because gopls previously explored the opposite answer: force multiple projects into one synthetic super-module so that cross-project queries had one dependency universe. That model simplified global identity, but only by requiring all projects to share dependency versions. The later design accepted multiple simultaneous build contexts instead, then made ambiguity explicit in routing. Current gopls still chooses a default build for some file-oriented operations because searching every build is too expensive. That is a latency tradeoff, not evidence that a file path has one intrinsic semantic context.

For Anneal, the defensible conditional lesson is narrower than “copy gopls.” A Rust source file should not itself be the authority for a proof result when that file participates in several Cargo compilation subjects. A verification request needs an explicit analysis context: a Cargo subject plus the proof/tool environment needed to interpret it, with a snapshot or generation identity for the state against which the request ran. Shared caches may aggressively reuse subcomputations across contexts when their inputs justify reuse, but verification success should remain attributable to one coherent context. Heuristic “best context” routing may be acceptable for advisory navigation; it is not a sufficient basis for a sound success result whose meaning depends on exact subject identity.

This is derived architectural analysis, not adopted Anneal policy. Anneal's current design contract explicitly leaves the atomic verification subject and build-matrix treatment undecided.

## Applicability

The current gopls implementation was inspected at `golang/tools@98444708d405557b5ddd6179be1a6abc14150d5f`, whose commit date is 2026-09-29. The principal source files are:

- `gopls/internal/cache/session.go` blob `476d4baaa0baa58328e0478b343ee59e308a7754`;
- `gopls/internal/cache/view.go` blob `d1f264f4d23578fe735d1c95aeadfe7df0d3d433`;
- `gopls/internal/cache/snapshot.go` blob `4ec7ca7d764c92d3cc2c27c42602dc959751992c`;
- `gopls/internal/cache/workspace.go` blob `6b2291e5bc9401f552c92eae3c8aefb213cf2c83`;
- `gopls/doc/workspace.md` blob `1e19fd3657b159a7eaeabc1bf3b56c59a5e5f024`;
- `gopls/doc/design/implementation.md` blob `887c02cd35c14edecdd1342d5664e3fb174f4bf8`; and
- `gopls/doc/design/design.md` blob `8ef3c32023b23f72837112c479e46519d1f2d46b`.

Historical source was inspected at the release commits for `gopls/v0.11.0` (`611cff71b9afeb81ae6eb16c5ce9376c051b1828`), `gopls/v0.12.0` (`236850463aea0b1949167349b44c37f97aefd9c5`), and `gopls/v0.15.0` (`50e6ff28fb47219a23c4d0ed12da704b94087f76`). At v0.11, `gopls/internal/lsp/cache/view.go` is blob `500358c0e6006042167249ffb9d2b68bdea161a1` and `snapshot.go` is `32967df48621634294964647c7d6490f56cf9660`. At v0.12, the corresponding blobs are `1dc13aaee8c9587676f09c29bd8b24867ac46529` and `de9524bf0ae5b4660ba92be053c7ed81e8b892bb`.

The architectural rationale is supplemented by public Go project records: `golang/go#32394` (multi-module workspace failure, opened 2019), the `golang/proposal` multi-project workspace design at `design/37720-gopls-workspaces.md` blob `5929e7e7894b8d51afbf2aa8ef38d1b34121ab4b`, `golang/go#57514` (deprecating `expandWorkspaceToModule`, opened 2022-12-29), `golang/go#57979` (zero-config workspaces, opened 2023-01-24), and the Go team's “Scaling gopls for the growing Go ecosystem” article published 2023-09-08.

The Anneal comparison uses `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` for `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, and reference branch `ebfeac694e945da0b52e09c6a185d857f982f4f3` for previously published subject-identity and invalidation evidence. Those Anneal reports are evidence about Anneal's Rust/Cargo/Charon/Aeneas/Lean pipeline; they are not gopls evidence.

## Findings

### The original gopls model already knew that editor files and analysis packages were different units

The original 2018–2019 design describes gopls as a long-running stateful process so several editor features can share parsed and type-checked state. It explicitly identifies a mismatch that remains central to the later redesigns: the editor operates on files, while Go type checking operates on packages. A file can move between packages as its contents or build tags change, can belong to more than one package, and can change outside the editor. The design therefore treats file-to-package mapping and invalidation as core architecture rather than UI plumbing.

That original design also made an assumption that later failed: low-memory environments were initially a non-goal, and the architecture expected to retain substantial state in memory for latency. Rob Findley's 2023 retrospective in the same design document says this was reconsidered as repositories grew and development moved into resource-constrained environments. The current document points to gopls's hybrid on-disk indexes and in-memory caches as the response.

This is useful historical evidence because the later `View`/`Snapshot` model did not originate from abstract purity. It was forced by two practical facts: the semantic unit differs from the UI unit, and eagerly retaining all semantic state does not scale.

Basis: **historical design documentation** at `golang/tools@98444708d...`, `gopls/doc/design/design.md`.

### The early multi-project proposal tried to restore one semantic universe

The 2020-era multi-project workspace proposal in `golang/proposal` starts from an ambiguity that occurs when several projects use different versions of the same dependency. At the type-checker level, different versions are unrelated packages even when humans think of them as “the same” library. The proposal gives a stronger example: after navigating into a shared utility package, the filesystem path of the source file does not encode which upstream application context led there, so the next definition request can be ambiguous.

Its proposed solution was a synthetic super-module. All projects in the editor workspace would resolve dependencies together, producing one version of each dependency in scope. This made cross-project references and rename operations have one coherent semantic universe. The authors argued that correlating independently loaded versions by name/signature would be error-prone and could silently miss results.

This was a serious alternative, not a straw man. It traded representational fidelity for a simpler global model: conflicting dependency requirements would become unsupported, while ordinary cross-project operations would have one answer. The proposal even observed that, if adopted fully, the super-module could remove the need for multiple Views in one session.

The cost is equally important. A synthetic unification changes the builds being analyzed. Two projects that genuinely compile against different dependency versions, flags, or environments no longer remain two independent subjects. That is acceptable only when the user intends a shared build universe. It is not a faithful default when multiple configurations are semantically real.

Basis: **historical design proposal** `golang/proposal@0be13090...`, `design/37720-gopls-workspaces.md`; issue lineage `golang/go#32394`.

### By late 2022, “workspace” had become too overloaded to be an architectural primitive

`golang/go#57514` records the rationale for removing the `expandWorkspaceToModule` setting. The issue asks what “workspace” actually means: the root at which to run the Go command, the boundary for diagnostics and analysis, or a memory optimization. Its proposed answer is to stop using one setting to stand for all three. The best Go-command root should be selected independently, open files should drive what must be analyzed, and memory policy should depend on active work rather than directory boundaries.

That diagnosis is broader than one setting. It separates three concerns that an editor folder had previously bundled:

1. **build interpretation** — which Go command, environment, modules, and flags define the program;
2. **user-visible scope** — which files and results the editor wants to present; and
3. **resource residency** — which semantic state is worth keeping live.

The later zero-config model makes that separation concrete.

Basis: **maintainer rationale** in `golang/go#57514`.

### v0.12 made multiple contexts economically plausible by changing the cache model

The Go team's v0.12 scalability account says v0.11 effectively held the typed representation of the whole program in memory. The authors report that typed syntax trees can be roughly 30 times source size, and that the old design made memory proportional to the entire analyzed program. The v0.12 redesign changed the unit of retained semantic work to packages.

The new architecture separately compiles packages and writes compact summaries and indexes to a persistent file cache. Cross-reference, method-set, export, and similar information can be loaded on demand. Memory becomes closer to the set of open packages plus their direct imports rather than the entire workspace. The Go team reports average memory and startup savings around 75 percent across 28 popular repositories in their benchmark, with larger relative savings for larger repositories.

The redesign also makes invalidation finer grained. A changed package must be reconsidered, but invalidation can stop propagating when the package's externally relevant summary is unchanged. The blog describes this as pruning work according to the scope of the change. Current source retains the same general division: snapshots keep package metadata and handles, while reusable indexes are stored in shared or persistent caches.

This was a prerequisite for the later multi-build workspace model. The blog explicitly says simpler workspace configuration and improved build-tag handling became feasible because each additional build configuration otherwise multiplied memory cost.

The benchmark numbers are a **reported outcome by the Go team**, not reproduced here. The separate-compilation and cache structures are also visible in the v0.12 and current source.

Basis: **reported outcome + implementation history**, Go blog 2023-09-08; `golang/tools@gopls/v0.11.0`, `gopls/v0.12.0`, and current source.

### v0.15 decoupled the editor folder from the build context

`golang/go#57979` describes the pre-redesign invariant directly: gopls determined one `View` for each workspace folder. That coupling made internal state depend on which directories a user happened to open, required users to understand nested module layout, caused eager scanning/loading, and failed when a user opened a file in a module outside the chosen View.

The proposed replacement was a dynamic set of Views derived from both workspace folders and open files. A folder contributes configuration, but it is no longer the build itself. An open file that does not fit an existing View can cause gopls to create another View, and several workspace folders can resolve to one shared `go.work` View. Changes to `go.mod`, `go.work`, configuration, open files, or workspace folders can cause the set of Views to be recomputed; equal Views can be reused.

The issue also makes immutability part of the correctness model. Its implementation plan first separates `Folder` state, makes build-defining View information immutable, moves mutable state into Snapshots, and reconstructs Views when build-defining inputs change. One checklist item says moving mutable View state into the Snapshot is “necessary for correctness anyway.”

The v0.15 source already exhibits this structure. Current source makes it more explicit: `View` is “a single build for a workspace,” and a `viewDefinition` is an immutable logical build consisting of a Folder, build root, module/workspace identity, and environment overlay. The `Snapshot` then holds one generation of file and derived state for that View.

Basis: **maintainer design rationale + implementation**, `golang/go#57979`, `golang/tools@gopls/v0.15.0`, and `golang/tools@98444708d...`.

### Current gopls has four different identities where the editor shows “the workspace”

At the current revision, the cache layer documentation and source divide state as follows.

| Concept | What it means | Mutation/lifetime |
|---|---|---|
| `Folder` | An LSP workspace folder plus per-folder options and Go environment | Treated as immutable; may be shared by multiple Views |
| `View` / `viewDefinition` | One logical Go build: root, module/workspace, build type, environment overlay, options | Build definition is immutable; rebuilt when defining inputs change |
| `Snapshot` | One consistent state generation for a View, including file handles, package metadata, derived handles, and invalidation bookkeeping | Replaced/advanced after edits; sequence IDs are comparable only within a View |
| shared caches | Reusable parse/package/index computations and persistent file-cache entries | May outlive a Snapshot and can be reused across snapshots/processes when cache keys match |

This separation answers a common but misleading question: “what is the workspace state?” There is no single object with that meaning. The editor folder is configuration and presentation scope; the View is build semantics; the Snapshot is temporal state; the cache is reusable computation.

One detail is especially important for identity. `Snapshot.sequenceID` is monotonic only within its View, and current source explicitly says sequence IDs from different Views cannot be compared. A generation counter without its View identity is therefore not a global state identity even inside gopls.

Basis: **current source + implementation documentation** at `golang/tools@98444708d...`.

### Open buffers are inputs to context selection, not merely unsaved bytes layered on one global build

Current `selectViewDefs` first creates a default View for each Folder, then checks open files and creates additional View definitions as needed. A build-constrained file can require a different `GOOS`/`GOARCH` context from the default. `gopls/doc/workspace.md` gives a concrete example: a repository containing three modules, with two in a `go.work`, plus an open Windows-constrained file, can cause gopls to track three builds.

Unsaved content is represented separately as overlays. The Session owns the overlay filesystem, and snapshots expose those buffer contents through file handles and through Go-command overlays. When a user opens or closes a file, gopls may need to recompute the set of Views because the set of open files is itself an input to which build contexts should exist. When the contents of an open Go or assembly file change its build constraints, gopls may also recompute View selection.

This yields two different effects from an edit:

- **content state changed within an existing build**: clone/invalidate the View's Snapshot and affected derived state;
- **the edit changed which build context the file belongs to**: recompute View definitions and possibly replace the build context itself.

Treating both as “the file changed” loses a boundary that the implementation relies on for correctness and resource control.

Basis: **current source** `session.go`, `view.go`, `snapshot.go`; **current documentation** `gopls/doc/workspace.md`.

### One file may have several valid semantic contexts

The zero-config issue explicitly says file-oriented requests can have metadata in more than one View. The old `bestViewForURI` approach was already known to produce path-dependent or incomplete results. The proposed ideal for cross-view operations such as references was to multiplex across all applicable Views and merge results, while operations such as hover or signature help could pick one context heuristically when any plausible result was more useful than none.

Current user documentation preserves the same compromise in a different form. For operations invoked from a file, gopls uses the default build for that file and does not search every possible build because doing so can be too expensive. A reference search from a Linux-constrained file can therefore have different scope from a reference search from the corresponding Windows-constrained file.

The important conclusion is not that gopls always multiplexes. It does not. The conclusion is that the implementation recognizes a many-to-many relation between user-visible files and build contexts, then chooses query semantics according to cost and UX. “Best View” is a routing policy, not a proof that the other Views are semantically irrelevant.

Basis: **maintainer design rationale** `golang/go#57979`; **current documentation** `gopls/doc/workspace.md`; **current implementation** `Session.viewOfLocked`, `RelevantViews`, `matchingView`, and `MetadataForFile`.

### Invalidation is context-sensitive even when bytes are shared

`Session.DidModifyFiles` updates the overlay set before allowing Views to observe the new bytes. It then decides whether the change can alter the set of Views. Opening or closing a file, changing build constraints in an open file, changing relevant configuration, or changing `go.mod`/`go.work` can trigger View recomputation.

After that routing step, the same modification is applied to every current View. This is necessary because a changed file can affect a shared package in several builds. Each View produces a new Snapshot and determines whether diagnostics should be recomputed. Shared caches can still preserve computations whose cache keys remain valid.

This is a useful decomposition:

1. **context invalidation** asks whether the logical build definition changed;
2. **snapshot invalidation** asks what state within a still-valid build changed; and
3. **computation-cache invalidation** asks which derived results can be reused despite the new snapshot.

The v0.12 pruning work operates mainly at the third layer. The zero-config View redesign operates mainly at the first. Conflating them creates either stale answers or unnecessary rebuilds.

Basis: **current implementation** plus **v0.12 reported architecture**.

### Anneal already has evidence that a Rust path is weaker than a Cargo subject

The current Anneal reference branch contains independent evidence that lines up with the gopls distinction without depending on it.

`cargo-compilation-subject-identity-2026-05-31` reconstructs Cargo's internal `Unit` identity at the Anneal-era toolchain. Cargo distinguishes units by dimensions including concrete package, target, effective profile, host/target compilation kind, compilation mode, features, compiler flags, dependency context, and artifact state. A package, target, source file, or filesystem path alone is therefore not an exact compilation subject.

`anneal-3730-rust-input-snapshot-2026-09-29` gives bounded execution evidence that identical primary Rust source bytes can produce different compiled behavior when included files, features, manifest defaults, or proc-macro inputs differ. `anneal-3730-saved-vs-private-rust-overlay-2026-09-29` gives a controlled materialized-overlay experiment and stale/wrong-unit rejection model. `anneal-3730-identity-state-mutation-model-2026-09-29` supplies a finite counterexample showing that a physical path alone can alias distinct Cargo subjects.

Those reports already establish the Rust-side premise needed for the comparison: a file path does not uniquely identify the program semantics Anneal is verifying. gopls contributes the architectural history of how a mature incremental tool handled the analogous file/build mismatch.

Basis: **existing Anneal reference evidence** at `google/zerocopy@reference:ebfeac694e...`.

### Conditional Anneal judgment: make the proof context explicit, and make snapshots local to it

The strongest transferable idea from gopls is not its exact type hierarchy. It is the separation between user-visible location, semantic context, temporal snapshot, and reusable computation.

For a Rust file that participates in several Cargo subjects, an Anneal request should carry or resolve an explicit proof context. Conceptually, that context should be strong enough to determine the compilation subject and proof environment relevant to the claim. The exact representation remains an Anneal design decision, but it may need to account for dimensions such as Cargo unit identity, active features/profile/target/configuration, toolchain versions, generated-input identity, and the Lean/Lake environment in which the generated proof is interpreted.

Within that context, the request should execute against a coherent snapshot or generation. Results should be attributable to that context and generation. A generation number by itself is insufficient if generations are only ordered within a context, just as gopls Snapshot sequence IDs are not comparable across Views.

Shared work should be factored separately. Parsing source text, reading manifests, translating an unchanged dependency, or indexing proof artifacts may be reusable across several proof contexts if their real inputs are identical. Reusing those computations does not require pretending the contexts are the same. This is the v0.12 lesson: separate semantic authority from the storage lifetime of reusable summaries.

A practical invalidation model would therefore distinguish at least these cases:

| Change | Conservative semantic response |
|---|---|
| Rust buffer/source content changes | Advance every proof-context snapshot that includes that input; invalidate only dependent derived work when sound dependency information permits pruning |
| Cargo manifest, features, target/profile/configuration, generated input, build-script or proc-macro input changes | Re-evaluate the proof-context definition; do not assume the previous compilation subject still exists under the same identity |
| Editor open/close or folder layout changes | Re-evaluate which contexts should be resident or suggested; do not make editor residency itself part of verification truth unless it changes actual source/build inputs |
| Rust/Charon/Aeneas/Lean/Lake/toolchain or prepared proof environment changes | Route to a new context/environment generation unless reuse has been explicitly revalidated across that change |

For an agent asking about one particular proof context, routing should be explicit enough that the agent can say which subject it meant. A UI may default that selection for convenience, but verification success should preserve the resolved identity in the result. For genuinely cross-context questions, Anneal can multiplex across contexts and tag each answer, rather than merge several proof universes into one unlabeled success.

This judgment is **derived** from gopls architecture plus existing Anneal subject-identity evidence. It is not a statement that Anneal must expose a public type named `View` or `Snapshot`.

### Four alternatives remain useful in narrower roles

#### One synthetic unified workspace

The historical gopls super-module proposal shows the attraction: a single dependency universe makes cross-project references and refactorings easier to interpret. Anneal can use an analogous model when the user has explicitly selected one canonical Cargo workspace/build configuration and the underlying toolchain actually builds one coherent subject graph.

It is not a safe universal default. If the same Rust file genuinely participates in two Cargo units with different features, profiles, targets, dependency resolutions, or build-script inputs, unifying them changes the program being reasoned about.

#### One proof context per editor folder

This is operationally simple and matches old gopls. Its failure mode is also well documented: editor layout is not build semantics. Nested modules, multiple configurations in one folder, and one build spanning several folders break the equivalence.

#### One default proof context per file

This can be useful for low-latency advisory features. Current gopls intentionally makes a similar compromise for some operations. It is inadequate as the sole verification model because a valid alternative context may impose different obligations or produce a different program.

#### Always evaluate every context

This maximizes completeness but can multiply cost and can make a simple local question return several semantically different answers. gopls's history shows why resource economics matter. Anneal should reserve all-context evaluation for queries whose semantics actually require it, while making a single-context verification request explicit.

### The current Anneal contract raises the standard above ordinary IDE routing

Anneal's `DESIGN.md` requires a successful verification result to have enough identity and scope to make its guarantee meaningful. It must identify the program or behavior to which the result applies and must not silently report a stronger claim than its evidence supports. The document deliberately leaves the atomic subject and build-matrix treatment undecided.

That means gopls's heuristic context selection is evidence about UX and resource tradeoffs, not a sufficient correctness rule for Anneal. A hover request can be useful even if gopls chose one plausible build among several. A verification-success result cannot silently acquire the meaning “all relevant Cargo subjects verified” merely because a default subject was selected.

The appropriate transfer is therefore asymmetric:

- adopt gopls's separation of presentation scope, build context, snapshot generation, and reusable cache;
- adopt its willingness to multiplex only where query semantics require it;
- do **not** inherit its willingness to return an unlabeled best-context answer for a claim whose sound meaning depends on the exact subject.

Basis: **derived comparison** against `anneal/DESIGN.md` and existing reference evidence.

## Boundaries

- This report reconstructs public architecture and maintainer rationale; it does not execute gopls or reproduce its performance benchmarks.
- The approximately 75 percent v0.12 memory/startup improvement is the Go team's reported benchmark across 28 repositories. It is not an independent measurement and should not be generalized to Anneal's workloads.
- The historical super-module proposal is evidence of a considered alternative, not a claim that every detail shipped. Later gopls design moved toward multiple dynamic Views instead.
- `golang/go#57979` is a design-and-implementation tracking issue. Its checked task list records author intent and implementation progress, while current source and current workspace documentation are the authority for behavior examined here.
- Current gopls still contains heuristic context selection and some non-multiplexed operations. This report does not claim that every LSP feature has context-complete semantics.
- gopls's View identity is not asserted to be minimal or complete for Anneal. Rust/Cargo compilation subjects and Lean proof environments have different identity dimensions.
- The existing Anneal reference reports cited here are separate evidence. This report does not re-run their experiments or strengthen their claims.
- Anneal's current design contract explicitly leaves the atomic verification subject and build-matrix policy undecided. The Anneal implications above are conditional architectural judgments, not adopted project policy.
- Candidate-only coordination status is external to this report package. Publication or campaign coverage must not be inferred from the existence of these bytes.

## Evidence

### Primary gopls source and documentation

- `golang/tools@98444708d405557b5ddd6179be1a6abc14150d5f`
  - `gopls/internal/cache/session.go` blob `476d4baaa0baa58328e0478b343ee59e308a7754`
  - `gopls/internal/cache/view.go` blob `d1f264f4d23578fe735d1c95aeadfe7df0d3d433`
  - `gopls/internal/cache/snapshot.go` blob `4ec7ca7d764c92d3cc2c27c42602dc959751992c`
  - `gopls/internal/cache/workspace.go` blob `6b2291e5bc9401f552c92eae3c8aefb213cf2c83`
  - `gopls/doc/workspace.md` blob `1e19fd3657b159a7eaeabc1bf3b56c59a5e5f024`
  - `gopls/doc/design/implementation.md` blob `887c02cd35c14edecdd1342d5664e3fb174f4bf8`
  - `gopls/doc/design/design.md` blob `8ef3c32023b23f72837112c479e46519d1f2d46b`
- `golang/tools@gopls/v0.11.0` / `611cff71b9afeb81ae6eb16c5ce9376c051b1828`
  - `gopls/internal/lsp/cache/view.go` blob `500358c0e6006042167249ffb9d2b68bdea161a1`
  - `gopls/internal/lsp/cache/snapshot.go` blob `32967df48621634294964647c7d6490f56cf9660`
- `golang/tools@gopls/v0.12.0` / `236850463aea0b1949167349b44c37f97aefd9c5`
  - `gopls/internal/lsp/cache/view.go` blob `1dc13aaee8c9587676f09c29bd8b24867ac46529`
  - `gopls/internal/lsp/cache/snapshot.go` blob `de9524bf0ae5b4660ba92be053c7ed81e8b892bb`
- `golang/tools@gopls/v0.15.0` / `50e6ff28fb47219a23c4d0ed12da704b94087f76`.

### Primary design/history records

- `golang/go#32394`, “x/tools/gopls: support multi-module workspaces,” opened 2019-06-02, closed 2022-03-18: https://github.com/golang/go/issues/32394
- `golang/proposal@0be13090fdb0cbae0d71641bb676d924bc1c94de`, `design/37720-gopls-workspaces.md` blob `5929e7e7894b8d51afbf2aa8ef38d1b34121ab4b`: https://github.com/golang/proposal/blob/0be13090fdb0cbae0d71641bb676d924bc1c94de/design/37720-gopls-workspaces.md
- `golang/go#57514`, “x/tools/gopls: deprecate the expandWorkspaceToModule setting,” opened 2022-12-29, closed 2023-10-13: https://github.com/golang/go/issues/57514
- `golang/go#57979`, “x/tools/gopls: zero-config gopls workspaces,” opened 2023-01-24, closed 2023-12-28: https://github.com/golang/go/issues/57979
- Robert Findley and Alan Donovan, “Scaling gopls for the growing Go ecosystem,” 2023-09-08: https://go.dev/blog/gopls-scalability

### Anneal design and comparison evidence

- `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`
  - `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb`
  - `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`
- `google/zerocopy@reference:ebfeac694e945da0b52e09c6a185d857f982f4f3`
  - `reports/cargo-compilation-subject-identity-2026-05-31/REPORT.md` blob `cb4ac7e31d1381aac2ba4842da3737cd23b76ca8`
  - `reports/anneal-3730-rust-input-snapshot-2026-09-29/`
  - `reports/anneal-3730-saved-vs-private-rust-overlay-2026-09-29/REPORT.md` blob `8efa8102e1f7604a914697955ab95921c0c3ad50`
  - `reports/anneal-3730-identity-state-mutation-model-2026-09-29/REPORT.md` blob `943084141353173b9a4af383920507f0c3cccdbf`
  - `reports/anneal-interactive-pipeline-invalidation-graph-main-41f5b37/`

The accompanying `evidence-map.json` classifies which source supports each major claim and separates maintainer rationale, implementation evidence, reported outcomes, existing Anneal evidence, and this report's derived analysis.

## Revalidation

To revalidate the gopls side after a significant upstream redesign:

1. Resolve the current `golang/tools` revision and inspect `gopls/doc/workspace.md`, `gopls/internal/cache/session.go`, `view.go`, and `snapshot.go`.
2. Confirm whether `Folder`, `View`, and `Snapshot` still represent distinct presentation/configuration, build-context, and temporal-state layers.
3. Construct a small repository with:
   - two modules, only one pair joined by `go.work`;
   - a file selected by the default host build;
   - an otherwise corresponding file constrained to a second `GOOS`/`GOARCH`;
   - one unsaved overlay in the editor.
4. Record gopls's active Views before and after opening the constrained file, editing its build constraint, changing `go.work`, and closing the file.
5. Run a file-local query and a workspace-wide reference query from files that participate in more than one build; record whether results are default-context, multiplexed, or tagged by build.
6. Measure memory/state growth with one versus several active Views, separating resident snapshot state from persistent cache entries.

To revalidate the Anneal comparison, pair that experiment with the current Cargo-subject and interactive-pipeline reports. Construct one Rust file that participates in at least two Cargo units with different feature/profile/target or dependency context, then verify that any proposed Anneal context handle distinguishes those units and that a response from one generation cannot be accepted as authoritative for the other. The acceptance criterion is not that Anneal reproduce gopls's object model; it is that user-visible file identity, semantic proof context, temporal generation, and reusable cached computation are not silently conflated.