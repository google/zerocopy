# Lean 4 `.ilean` schema and server/reference uses at v4.30.0-rc2

## Summary

At Lean `v4.30.0-rc2`, a `.ilean` is a compact JSON projection of elaboration metadata for editor and project-wide reference services. It is not a serialized `InfoTree`, not a proof-state snapshot, and not a substitute for `.olean`. The persisted top-level value has five fields: format `version` (default `5`), logical `module`, `directImports`, `references`, and declaration ranges `decls`.

Lean generates the file only after successful frontend processing. It collects all available `InfoTree`s, extracts and deduplicates references, drops local free-variable references for the persisted file, converts locations and parent-declaration ranges to a compact JSON-oriented representation, and writes the compressed JSON text. The result preserves enough information for cross-file definitions/references, rename, call hierarchy, workspace-symbol search, module hierarchy, and declaration-range correction, but it intentionally omits most elaborator state.

The language server has a second, transient use of the same reference representation. An open file worker extracts references from current `InfoTree`s with local-variable references enabled and sends incremental and final `$/lean/ileanInfo*` notifications to the watchdog. The watchdog overlays this live worker data on built `.ilean` data. Thus navigation can use unsaved and unbuilt positions from an open file while closed dependencies continue to use their persisted `.ilean` indexes.

This boundary matters for Anneal's future interactive architecture. `.ilean` is useful as a cheap persistent symbol/reference index and for project-wide navigation, but tactic state, goals, expected types, and other InfoView-style proof interactions require the live snapshot/`InfoTree` path. The pinned plain-goal and term-goal handlers query current `InfoTree` state directly; those values do not appear in the `.ilean` schema.

One compatibility subtlety is especially important: although the schema contains `version := 5`, the pinned `Ilean.load` and `References.addIlean` paths parse and install the value without explicitly comparing that field to an expected version. Structural JSON decoding can still reject incompatible shapes, but Anneal should not treat the numeric `version` field itself as an enforced compatibility gate at this revision.

Basis: exact pinned Lean implementation source. No fresh Lean executable or language server was run for this report.

## Applicability

The subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`, the Lean revision selected by the Anneal dependency state used by this reference program. Claims about `.ilean` fields, JSON representation, extraction, server precedence, and request routing are limited to that revision unless revalidated.

This report distinguishes three layers:

1. **Persisted `.ilean` artifact.** A JSON file written by the standalone frontend after successful elaboration. It excludes local free-variable references.
2. **Transient worker reference state.** Reference/declaration data recomputed from current open-file `InfoTree`s and sent to the watchdog with a document version. It uses nearly the same compact reference representation, but includes local variables.
3. **Live interactive elaboration state.** Snapshot and `InfoTree` data retained inside a file worker. Goal state, term expected types, hoverable elaborator information, and RPC-backed InfoView interactions live here rather than in `.ilean`.

The report uses “InfoView-style” narrowly for interactive proof/term information derived from live elaboration state. It does not claim to inventory every VS Code widget or RPC method. The important architectural boundary is that `.ilean` supplies a persistent project index, while rich interactive state remains worker-local and snapshot-backed.

The `.ilean` numeric `version` and LSP document `version` are unrelated. The former is a field in the persisted schema and defaults to `5`; the latter tracks revisions of an open document so the watchdog can order incremental worker reference updates.

## Findings

### Persisted `.ilean` is compressed JSON with five top-level fields

`Lean.Server.Ilean` contains:

- `version : Nat := 5` — the format-version field;
- `module : Name` — the logical module whose index this is;
- `directImports : Array Lsp.ImportInfo` — direct import statements and their flags;
- `references : Lsp.ModuleRefs` — definitions and uses grouped by reference identity; and
- `decls : Lsp.Decls` — declaration and selection ranges.

`Ilean.load` reads the entire file as text, parses JSON, and runs `FromJson`. The frontend writes `Json.compress (toJson ilean)`, so whitespace and formatting are not semantically significant. Standard `Name` JSON encoding at this revision is a string produced by `toString` and decoded through `String.toName`.

The persisted `.ilean` is therefore inspectable and structurally different from native `.olean` object images. It does not contain kernel declarations, proof terms, environment-extension payloads, tactic goals, metavariable contexts, or arbitrary `InfoTree` nodes.

Basis: source — `src/Lean/Server/References.lean`, `Ilean`; `src/Lean/Elab/Frontend.lean`, `.ilean` emission; `src/Lean/Data/Json/FromToJson/Basic.lean`, `Name` JSON encoding.

### The persisted file is generated from `InfoTree`s only after successful frontend processing

The standalone frontend reports diagnostics, waits for a final command state, and returns early when errors remain. If an `.ilean` output path was requested, it then gathers every snapshot's `infoTree?`, extracts module references with `findModuleRefs ... (localVars := false)`, converts those references to the compact LSP-oriented representation, records the logical module and direct imports, and writes the JSON file.

The `localVars := false` choice is a deliberate persistence boundary. `findModuleRefs` normally collects both global constants and local free-variable identifiers, but with `localVars` disabled it filters every `RefIdent.fvar`. A persisted `.ilean` can therefore support cross-file/global reference services without retaining ephemeral local-variable identities from one elaboration run.

The extraction itself is more semantic than a textual identifier scan. `identOf` maps term constants, free variables, field projections, option references, and documented declaration references to reference identities using elaboration context. The collector ignores canonicalized syntax heads, combines aliases and overlapping representations, deduplicates references, and records definition/use ranges.

Basis: source — `src/Lean/Elab/Frontend.lean` lines 193-211; `src/Lean/Server/References.lean`, `identOf`, `findReferences`, `combineIdents`, `dedupReferences`, and `findModuleRefs`.

### The compact reference schema is optimized for project indexing

Reference identities have two cases:

- `RefIdent.const(moduleName, identName)` for globally available named declarations; and
- `RefIdent.fvar(moduleName, id)` for local references.

Both names are stored as strings. Their JSON uses a shortened tagged representation; `ModuleRefs` then serializes a tree map as a JSON object whose keys are the compressed JSON encoding of those identities. This unusual “JSON encoded inside an object key” representation is an implementation detail of the compact index, not a stable human-authored format.

Each reference maps to a `RefInfo` containing an optional definition location and zero or more usage locations. A location is encoded as an array of four integers — start line, start UTF-16 character, end line, end UTF-16 character — with an optional fifth string naming the parent declaration. The missing parent is represented in memory by an empty string and omitted from the four-element JSON form.

`Decls` is a JSON object keyed by declaration-name string. Each `DeclInfo` is an array of exactly eight integers: start/end line and UTF-16 character for the full declaration range, then start/end line and character for the selection range. Direct imports use a four-element JSON array containing module string plus `isPrivate`, `isAll`, and `isMeta` booleans.

For an agent consuming `.ilean` directly, the safest rule is to use Lean's own `FromJson` types at the exact pin when possible rather than duplicating these compression conventions. The representation was designed to reduce file size and allocation, not to provide a separately versioned external protocol.

Basis: source — `src/Lean/Data/Lsp/Internal.lean`, `ImportInfo`, `RefIdent`, `DeclInfo`, `Decls`, `RefInfo`, and `ModuleRefs` JSON instances.

### The `version := 5` field is present but is not an explicit load-time compatibility check

The `Ilean` structure gives `version` a default value of `5`, and deriving supplies its JSON codec. At the pinned revision, however, `Ilean.load` performs only JSON parsing plus structural `FromJson`, and `References.addIlean` consumes `module`, `directImports`, `references`, and `decls` without reading or comparing `ilean.version`.

A repository-wide inspection of the pinned server path found no explicit equality test against `5` before installing loaded `.ilean` data. Consequently, the numeric field should not be interpreted as an enforced protocol negotiation mechanism at this revision. Structural changes can still fail decoding because fields or custom compact representations no longer parse, and semantic changes can still make old data wrong even when decoding succeeds.

For Anneal, exact toolchain identity remains the conservative cache boundary. A future revision could begin checking the field, change its meaning, or alter a nested representation without adding an independent compatibility contract for every nested type.

Basis: source + derived — `Ilean`/`Ilean.load` and `References.addIlean` in `src/Lean/Server/References.lean`; no explicit numeric gate on the pinned load/install path.

### The watchdog loads every `.ilean` in the Lean search path asynchronously

At server startup, `startLoadingReferences` enumerates all files with extension `ilean` on the current Lean search path and loads them in an asynchronous task. Startup therefore does not wait for the complete project-wide reference index. The source explicitly states that reference-dependent requests can return incomplete results while loading is still in progress.

Initial load failures are swallowed rather than made fatal, with a comment noting that build-system races are one possible cause. Once the client has registered file watchers, `.ilean` creations and changes are reloaded when the changed path belongs to the module search path, and deletions remove the corresponding index data. A changed file is removed before the replacement is added.

The internal `$/lean/waitForILeans` request exists mainly for synchronization in tests and external tooling. It waits for the initial loading task and, when a URI/document version is supplied, also waits until the watchdog has observed an `.ilean`-finalization notification for at least that worker version.

For deterministic agent orchestration, this means ordinary language-server readiness is weaker than “all project `.ilean` indexes loaded and this open file's current reference projection finalized.” A client that requires the latter needs an explicit synchronization point or equivalent state tracking.

Basis: source — `src/Lean/Server/Watchdog.lean`, `startLoadingReferences`, file-change handling, and `$/lean/waitForILeans`; `src/Lean/Data/Lsp/Extra.lean`, `WaitForILeansParams`.

### Open-file workers overlay built `.ilean` data with current unsaved state

The watchdog's `References` value has two maps: loaded `.ilean` data and transient worker data. The source documents workers as overriding corresponding `.ilean` files. `allRefs`, `allDirectImports`, `getModuleRefs?`, `getDirectImports?`, and `getDecls?` all prefer current worker data when it has usable references.

A file worker recomputes this transient projection from live `InfoTree`s with `localVars := true`, unlike persisted `.ilean`. As asynchronous elaboration snapshots finish, the worker accumulates new `InfoTree`s. After it has blocked long enough to report incremental progress, it sends `$/lean/ileanInfoUpdate` messages for newly completed trees. At the end it sends `$/lean/ileanInfoFinal` computed from all collected trees; the source says this final message overwrites existing info in case incremental updates went wrong.

Each worker message carries the LSP document version. The watchdog ignores older versions, replaces on newer versions, merges same-version incremental updates, and treats the final message as authoritative for that version. This allows reference positions from unsaved/unbuilt source to coexist with persisted indexes for closed dependencies.

This is the critical freshness model for interactive navigation: `.ilean` on disk is a baseline project index, while current workers provide a versioned overlay.

Basis: source — `src/Lean/Server/FileWorker.lean`, `mkIleanInfoNotification` and `reportSnapshots`; `src/Lean/Server/References.lean`, `References`, `updateWorkerRefs`, `finalizeWorkerRefs`, and aggregate lookup functions; `src/Lean/Server/Watchdog.lean`, worker notification handling.

### `.ilean` powers project-wide references, rename, symbols, call hierarchy, and module hierarchy

The watchdog answers `textDocument/references` from the aggregate `References` index. It identifies the symbol at the cursor in the current module and then collects definition/use locations across project modules. Rename reuses the same reference query with declarations included. Workspace-symbol search scans indexed definitions and fuzzy-matches declaration names.

Call hierarchy is also index-backed. Incoming calls use project-wide references and their parent-declaration metadata. Outgoing calls inspect usage locations within the selected module and group them by parent declaration. The persisted `decls` table supplies declaration ranges used to present parent call items.

Direct imports in `.ilean` support module-hierarchy queries. The server can report what a module imports and compute the inverse “imported by” relation from the aggregate reference/import index.

This is why `.ilean` is more than “find references cache”: it is the watchdog's durable cross-file symbol/import index. Its compact parent-declaration and declaration-range metadata are specifically useful for navigation and hierarchy features that do not need a full elaboration environment.

Basis: source — `src/Lean/Server/Watchdog.lean`, `handleReference`, call-hierarchy handlers, module-hierarchy handlers, `handleWorkspaceSymbol`, `handlePrepareRename`, and `handleRename`.

### Definition locations can be corrected from `.ilean`/worker data when `.olean` positions are stale

Go-to-definition/declaration/type-definition starts in the file worker, which inspects the current `InfoTree` at the cursor and emits `LeanLocationLink`s. The watchdog then post-processes those links. When a link carries a declaration identity, the watchdog looks up the corresponding definition in its aggregate reference index and replaces the target range with the indexed current range.

The source explains the motivation directly: location data coming from imported `.olean` information can be stale if the defining source file has been edited without being saved or rebuilt, while `.ilean` update notifications from an open worker contain current position information. If the file worker only produced fallback links, the watchdog also tries to obtain better definition locations from its reference index.

This gives `.ilean` a specific relationship to `.olean`: kernel/environment import information can tell the worker what declaration an identifier denotes, while the `.ilean`/worker reference index can supply fresher source positions for editor navigation.

Basis: source — `src/Lean/Server/FileWorker/RequestHandling.lean`, `handleDefinition`; `src/Lean/Server/Watchdog.lean`, `bendLocationLinks` and `findDefinitions`; `src/Lean/Data/Lsp/Internal.lean`, `LeanLocationLink` documentation.

### Proof-state and InfoView-style interaction stays on the live `InfoTree` path

The `.ilean` schema contains reference identities, source ranges, direct imports, and declaration ranges. It contains no metavariable goals, local contexts, expected types, expressions, tactic state, or arbitrary elaborator `Info` nodes.

The pinned plain-goal request illustrates the live path. `handlePlainGoal` obtains interactive goals from the current document's snapshots. The term-goal handler calls `findInfoTreeAtPos`, finds `TermInfo`, runs metaprogramming in the captured context, instantiates metavariables, and constructs an interactive goal. Document highlighting similarly rebuilds references from the current finished snapshot prefix rather than consulting the persisted project index.

The same architectural split explains why `.ilean` cannot by itself support an agent asking “what is the tactic state at this proof position?” That query requires the elaborated snapshot/`InfoTree` (or an RPC API backed by it). `.ilean` can help resolve declarations and references across modules, but it is a lossy derivative index.

For a future Anneal MCP/LSP mode, a robust design should therefore treat `.ilean` as optional persistent navigation acceleration and the live Lean server/RPC snapshot as the authority for proof interaction. Persisting `.ilean` cannot replace preserving or recreating the live elaboration context needed for goals and tactics.

Basis: source + derived — `.ilean` schema; `src/Lean/Server/FileWorker/RequestHandling.lean`, goal, term-goal, definition, and document-highlight handlers.

### Persisted `.ilean` and transient worker data intentionally differ on local-variable references

Persisted generation calls `findModuleRefs(..., localVars := false)`, while file-worker notifications call the same function with `localVars := true`. This difference is semantically useful rather than incidental.

Local free-variable identities are meaningful inside the current elaboration of one module, so the worker can use them for same-file interactions such as document highlighting. They are poor durable project identities: their names derive from elaborator-generated `FVarId`s and are not intended as globally addressable declarations. The persisted file therefore strips them, leaving global constant references plus source/declaration metadata.

An agent reading `.ilean` should not infer that the absence of a local variable means Lean lacks reference information for it in an open editor session. Conversely, an agent should not persist transient worker `fvar` identities and expect them to be stable across rebuilds.

Basis: source + derived — `findModuleRefs` and its two call sites in `Frontend.lean` and `FileWorker.lean`.

## Boundaries

- **No fresh execution.** This investigation did not generate a `.ilean`, run `lean --server`, inspect live LSP traffic, or mutate a project while observing navigation. File shape and behavior are established from exact pinned source.
- **No byte-for-byte sample fixture.** The report inventories the codec implementation rather than presenting a generated example file. Nested `FromJson`/`ToJson` derivation details not material to the architectural boundary should be rechecked from the pinned codec before writing an independent parser.
- **The numeric `version` field is not claimed useless.** It records an intended format generation and may be used by other code or future revisions. The narrower claim is that the pinned `Ilean.load` → `References.addIlean` server path does not explicitly compare it before installation.
- **No guarantee that arbitrary stale `.ilean` data is harmless.** The server tolerates load failures and overlays open-worker state, but a structurally valid stale index can still give incomplete or stale navigation results for closed files. Build orchestration remains responsible for keeping generated artifacts current.
- **InfoView scope is architectural, not exhaustive.** Goal/term-goal handlers establish that rich proof state comes from live snapshots. This report does not catalog every widget, hover payload, completion path, or custom RPC method.
- **No stable third-party protocol promise.** `.ilean` is checked-in Lean implementation machinery. The presence of JSON and a numeric version does not by itself constitute a public forward/backward compatibility guarantee.
- **No `.olean` duplication.** Kernel module contents and `.olean` compatibility are covered by the separate `.olean` report. This report only records the navigation boundary where imported declaration identities/positions interact with `.ilean` data.
- **No claim that all reference requests wait for initial loading.** The source explicitly permits incomplete results during asynchronous `.ilean` startup. `$/lean/waitForILeans` is the synchronization mechanism inspected here.

## Evidence

All source below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` and was inspected on 2026-09-27.

- `src/Lean/Server/References.lean`, blob `8171fcc2c120f952c7c77b270f235e2f0b0906f7`:
  - reference extraction and conversion at lines 23-399;
  - `Ilean` and `Ilean.load` at lines 205-228;
  - loaded/transient reference stores at lines 488-566;
  - worker precedence and aggregate lookup beginning around lines 600-749.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/References.lean#L205-L228>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/References.lean#L389-L399>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/References.lean#L488-L566>
- `src/Lean/Data/Lsp/Internal.lean`, blob `bd64732ada62ab8127091ef690fa13f85acb4071`:
  - compact `ImportInfo` at lines 29-53;
  - `RefIdent` and JSON codec at lines 55-101;
  - `DeclInfo`/`Decls` at lines 103-183;
  - compact `RefInfo`/`ModuleRefs` at lines 185-295;
  - worker `.ilean` notification payload types beginning around lines 297-322.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Internal.lean#L29-L101>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Internal.lean#L103-L295>
- `src/Lean/Elab/Frontend.lean`, blob `fd3760667db96a351b4f654720193c89bbee356e`, lines 193-211: successful frontend `.ilean` generation from all `InfoTree`s with `localVars := false` and compressed JSON output.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/Frontend.lean#L193-L211>
- `src/Lean/Server/FileWorker.lean`, blob `c803034ed8810f13a5ef38a603a21e610efca2bc`:
  - worker reference notifications at lines 154-173;
  - accumulated/new `InfoTree` state at lines 182-192;
  - final full replacement at lines 239-255;
  - incremental updates as snapshots finish at lines 308-335.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker.lean#L154-L192>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker.lean#L239-L335>
- `src/Lean/Server/Watchdog.lean`, blob `68ed22f9178c9ae917c595c364d23df902d9478f`:
  - worker `.ilean` setup/update/final handling at lines 501-529;
  - project module queries and definition correction beginning around lines 626-725;
  - project reference, call hierarchy, module hierarchy, workspace symbol, and rename handlers around lines 956-1221;
  - watched `.ilean` reload handling at lines 1278-1306;
  - `$/lean/waitForILeans` at lines 1395-1431;
  - asynchronous startup loading at lines 1670-1692.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L501-L529>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L626-L725>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L956-L1221>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L1670-L1692>
- `src/Lean/Server/FileWorker/RequestHandling.lean`, blob `a51b43e1894fc1d0949a60a4b789992c14d10fee`:
  - definition routing and `.ilean` position-correction boundary at lines 117-142;
  - live goal/term-goal handling around lines 143-249;
  - same-file document highlighting from current snapshots at lines 251-286.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker/RequestHandling.lean#L117-L286>
- `src/Lean/Data/Lsp/Extra.lean`, blob `073e8ce7273bb4bd90d43c59eb307aad76da5e3a`, `WaitForILeansParams` and synchronization documentation.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Extra.lean>
- `src/Lean/Data/Json/FromToJson/Basic.lean`, blob `5bde8a07adbc9def32fb9d87280b271dfa5f5988`, lines 112-125: `Name` JSON uses string form.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Json/FromToJson/Basic.lean#L112-L125>

The current `google/zerocopy` Anneal redesign was separately observed at main commit `41f5b37afe7060fd9fe08c00b200672cd76d77b9`; the exact Lean subject identity above comes from the already reconstructed Anneal dependency state used by this reference program. The technical claims here are about the pinned Lean source rather than moving Lean `master`.

## Revalidation

For another Lean revision, revalidate the `.ilean` contract in this order:

1. Inspect `Lean.Server.Ilean` and its loader. Record the top-level fields, default format version, and whether the reader now actively rejects mismatched versions.
2. Inspect `Lean.Data.Lsp.Internal` for custom `ImportInfo`, `RefIdent`, `DeclInfo`, `RefInfo`, `Decls`, and `ModuleRefs` codecs. These compact nested encodings can change independently of the top-level field list.
3. Inspect frontend generation to see whether `.ilean` is still produced from `InfoTree`s after successful elaboration, whether local references remain filtered, and whether output is still JSON.
4. Inspect `FileWorker` and `References` for the transient-overlay model. Confirm version ordering, incremental merge, final replacement, and worker-over-built precedence.
5. Inspect `Watchdog` startup/loading, watched-file replacement, reference handlers, definition correction, symbol/call/module hierarchy, and synchronization request.
6. Inspect proof/goal and RPC request paths to confirm which InfoView-style features still require live snapshots rather than `.ilean`.

When a runnable exact-pin toolchain is available, a focused probe can add useful behavioral confirmation:

- compile a tiny multi-file project with `-i`/normal Lake build and inspect the emitted JSON keys and compact nested values;
- change an open dependency without rebuilding and confirm definition ranges follow worker updates rather than the old on-disk `.ilean`;
- start the server on a project with many `.ilean`s and compare reference results before and after `$/lean/waitForILeans`;
- alter only the numeric `.ilean` `version` in an otherwise valid file to test whether the exact binary accepts it; and
- compare persisted data against the live worker projection to demonstrate the absence/presence of local `fvar` references.

Treat those probes as confirmation of the exact revision, not as a stable protocol guarantee. For Anneal, bind any durable parser/cache to the exact Lean revision unless a future Lean API explicitly documents broader `.ilean` compatibility.