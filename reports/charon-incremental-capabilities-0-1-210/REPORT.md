# Charon incremental capabilities at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), Charon has useful **within-run** demand-driven translation and caching, but the pinned extraction pipeline does not expose a **cross-run incremental Charon state** that can be updated after a source edit.

The distinction matters because several mechanisms that look incremental operate at different layers:

- `--start-from` and the translation queue reduce the Charon item graph translated during one extraction. They begin from selected Rust items and recursively discover referenced items.
- Hax and Charon maintain per-run caches and processed-item sets while a single rustc `TyCtxt` is alive. These avoid duplicate work inside that translation.
- `charon cargo` delegates compilation orchestration to an ordinary `cargo build`, so Cargo/rustc may provide their own build or query reuse. Charon 0.1.210 does not turn that lower-layer reuse into a persistent LLBC snapshot or an item-level invalidation API.
- Each selected-crate extraction constructs a fresh `TranslateCtx`, fresh `TranslatedCrate`, fresh item-ID maps, fresh queues, and a fresh Hax state. After translation, Charon returns a `TransformCtx`, serializes a complete result, and the driver process exits.

Thus the exact pin supports **translation-scope pruning** and **ephemeral in-process memoization**, not incremental LLBC maintenance. An interactive Anneal design can use `--start-from` to reduce work for a known root set, and it may benefit from Cargo/rustc reuse, but it cannot rely on Charon 0.1.210 to accept an edit plus a previous translation and return only a validated delta.

The pinned `charon cargo` wrapper also has no Charon-owned freshness protocol. It invokes `cargo build` with `RUSTC_WRAPPER=charon-driver`; it does not assign snapshot generations, content hashes, or prior-LLBC identities. A later Charon `main` snapshot adds a fresh `RUSTC_WORKSPACE_WRAPPER` fingerprint specifically to force Cargo to rerun Charon, so Cargo freshness behavior is an upgrade-sensitive boundary rather than something Anneal should infer from 0.1.210 source alone.

## Applicability

This report applies to Charon 0.1.210 at commit `a535e914f74db4fd9e6be7048f4233270d8945c0`, the revision pinned by Aeneas release `nightly-2026.06.03`. Its `rust-toolchain` selects `nightly-2026-05-31`.

“In-run caching” means state retained while one `charon-driver` rustc invocation is translating one selected crate. “Cross-run incremental translation” means retaining a previous Charon translation or extraction state across source changes and selectively invalidating/recomputing the affected portion. “Build reuse” means work Cargo or rustc may avoid through their own mechanisms; it does not imply Charon-level incremental LLBC semantics.

The findings are source-based. No fresh Charon/Cargo execution, timing measurement, incremental-directory inspection, or edited-workspace probe was performed in this report.

## Findings

### One selected-crate extraction owns one rustc session and one fresh translation state

`charon-driver::run_rustc_driver` invokes `rustc_driver::run_compiler` with `CharonCallbacks`. In `after_expansion`, the callback receives the current `TyCtxt` and calls `translate_crate::translate`. The resulting `TransformCtx` is stored only in the callback for that driver invocation. After rustc analysis, the callback returns `Compilation::Stop`, and the driver later runs post-processing and serializes the result.

`translate_crate::translate` constructs a new `TranslateCtx` for that call. The constructor initializes a new `TranslatedCrate`, `id_map`, `reverse_id_map`, `items_to_translate`, `processed` set, name/meta caches, method-status table, file map, and lifetime analysis state. It also constructs a new Hax `State` tied to the current `TyCtxt`.

The lifetime structure is significant. `TyCtxt<'tcx>` and Hax values parameterized by `'tcx` are compiler-session state; the translation function explicitly returns a `TransformCtx` after dropping the Hax state and rustc `tcx`. The exported result retains Charon's translated representation, not a live compiler context that can answer a later edit incrementally.

Basis: pinned **source** — `charon/src/bin/charon-driver/driver.rs`, `charon/src/bin/charon-driver/translate/translate_crate.rs`, and `charon/src/bin/charon-driver/translate/translate_ctx.rs`.

### Charon and Hax cache aggressively inside a run, but those caches are created afresh for the run

`TranslateCtx` contains multiple memoization structures: the rustc-item-to-Charon-ID map, reverse IDs, processed items, cached names, cached item metadata, and the pending item queue. `register_no_enqueue` reserves a Charon item slot on first encounter; `register_and_enqueue` adds work; the main translation loop suppresses repeat processing through the `processed` set.

Hax has another cache layer. `GlobalCache<'tcx>` stores per-item caches, rustc-to-Hax IDs, reverse generic arguments, and synthetic-item identities. Each `ItemCache<'tcx>` stores translated full definitions, translated types, item references, and trait proofs. `TranslateCtx::hax_def_for_item` explicitly notes that Hax caches these translations.

These are useful incremental mechanisms in the ordinary algorithmic sense: repeated references during one extraction do not force the same conversion work repeatedly. They are not durable incremental state. `translate_crate::translate` creates a new Hax `State::new(...)` and a new `TranslateCtx` every time it is called, so none of these maps or caches is loaded from a previous LLBC file or previous Charon invocation.

Basis: pinned **source** — `translate_ctx.rs`, `translate_crate.rs`, and `charon/src/bin/charon-driver/hax/state.rs`.

### `--start-from` prunes the translation graph; it does not update a prior translation

The pinned CLI exposes several ways to choose roots: `--start-from`, `--start-from-if-exists`, `--start-from-attribute`, and `--start-from-pub`. The option documentation says Charon translates the chosen starting items and the items they refer to according to opacity rules; with no explicit roots, translation starts from `crate`.

The implementation matches that contract. `translate_crate::translate` resolves each selected root and enqueues it into the fresh translation context. The queue then explores references recursively. Items may be kept opaque, included, or excluded, and method bodies are translated lazily when used.

This can substantially reduce the amount of Charon work for a known call graph or root set. It is nevertheless a **from-scratch traversal over the current compiler session**. The pinned source has no input parameter for a previous `TranslatedCrate`, no item-change set, and no merge procedure that replaces only invalidated definitions in an older LLBC snapshot.

Basis: pinned **source/documentation** — `charon/src/options.rs`, `translate_crate.rs`, and `translate_ctx.rs`.

### Charon item IDs are allocated during the fresh traversal, not presented as a cross-run incremental identity

When a `TransItemSource` is first registered, `register_no_enqueue` reserves the next slot in the relevant translated declaration collection and records the mapping in the current `id_map`. The reverse map and early item name are likewise populated in the current `TranslateCtx`.

This gives references a consistent identity within one resulting `TranslatedCrate`. The inspected path does not load an earlier ID map or reserve IDs according to a persistent snapshot identity. Therefore Anneal should not use a raw Charon `ItemId` from one run as the sole key for patching another run's LLBC. Cross-run correspondence must use a separately justified stable source/item identity and revalidate the affected graph.

This finding does not claim that IDs necessarily change on every run; deterministic traversal can reproduce the same numeric IDs. It establishes the weaker and operationally important fact that the pinned incremental contract does not guarantee preservation of those IDs across edits or runs.

Basis: pinned **source** — `translate_ctx.rs` and `translate_crate.rs`.

### The supported Cargo path delegates lower-layer reuse to Cargo rather than defining a Charon cache

`charon cargo` creates a normal Cargo command, sets `RUSTC_WRAPPER` to `charon-driver`, sets Charon-specific environment variables, invokes `cargo build`, and waits. Workspace dependencies and host-side build scripts/proc macros are compiled normally; selected target crates run Charon's translation callback.

The wrapper does not select a Charon-specific target directory, maintain a Charon dependency graph on disk, or read a previous serialized LLBC before extraction. Consequently, whatever compilation artifacts Cargo or rustc reuse remain lower-layer implementation behavior. Charon 0.1.210 does not expose those artifacts as a Charon snapshot with item-level invalidation semantics.

The pinned source also does not itself prove how Cargo will classify every repeated `charon cargo` invocation for freshness. This is a meaningful boundary because current Charon `main` has since added a fresh `RUSTC_WORKSPACE_WRAPPER` fingerprint with the explicit comment that it forces Cargo to rerun Charon each time. That later behavior must not be projected backward onto 0.1.210, but it demonstrates that Cargo freshness is a version-sensitive part of this integration.

Basis: pinned **source** — `charon/src/bin/charon/main.rs` and `driver.rs`; later non-authoritative **history snapshot** — Charon `main@67da6d3b8f31dfb0d003aee1596040f9efd7d27f`, `charon/src/bin/charon/main.rs`.

### rustc query reuse is session-local from Charon's point of view

Charon translates while rustc's `TyCtxt` is available and issues many rustc queries through it. rustc can memoize query results within its compiler execution. Charon also overrides selected query providers and configures MIR extraction for its needs.

However, the Charon integration shown here calls one `rustc_driver::run_compiler` for the selected crate and receives its `TyCtxt` only inside that compiler session. The public Charon result after extraction is a `TransformCtx`/`TranslatedCrate`, not a persisted rustc query database. No pinned Charon API reopens an old compiler session or maps an edit to a subset of rustc queries that Anneal can request directly.

Therefore any rustc incremental compilation or on-disk query reuse should be treated as an underlying compiler property that requires its own validation. It is not the same as a Charon incremental-translation protocol.

Basis: pinned **source** — `driver.rs`, `translate_ctx.rs`, and the Hax state/cache implementation.

### Serialization is whole-result publication, not an LLBC delta protocol

After the rustc-backed translation finishes, Charon runs transformation passes and constructs `CrateData` from the resulting `TransformCtx`. `CrateData::serialize_to_file` creates the destination file and serializes the complete crate as JSON or Postcard. The reader deserializes a complete `CrateData` and enforces Charon version equality.

There is no delta record in this interface: no base snapshot hash, changed-item list, tombstone list, generation number, or protocol operation that applies a patch to an existing LLBC file. A consumer can deserialize an LLBC value and manipulate it in-process with `charon_lib`, but the source-extraction path does not use an earlier file as incremental input.

Basis: pinned **source** — `charon/src/bin/charon-driver/main.rs` and `charon/src/export.rs`.

### Multi-target translation reinforces the per-run boundary

When multiple target architectures are requested, `charon` launches one translation per target in separate threads, writes each result to a temporary file, deserializes those complete results, and merges them afterward. The option documentation warns that this initial implementation is extremely slow.

This is another explicit example of Charon composing whole translation results rather than maintaining one persistent compiler/LLBC state across configurations. The multi-target merger is useful reuse at the representation level, but it is not incremental recompilation of a shared source snapshot.

Basis: pinned **source/documentation** — `charon/src/bin/charon/main.rs` and `charon/src/options.rs`.

### For interactive Anneal, the useful pinned primitive is bounded re-extraction, not Charon-owned invalidation

The pinned architecture supports a practical but limited interactive strategy: identify a root set, invoke Charon with `--start-from`/opacity controls, and treat the resulting translation as a fresh snapshot for that request. This can be combined with separate caching in Anneal, Cargo, rustc, or a future Charon service.

What the pin does not supply is the correctness contract needed to mutate a previous LLBC snapshot in place after an edit. Such a design would need, at minimum, stable source/item identities, an explicit invalidation graph, versioned source/config/toolchain inputs, deletion/tombstone handling, dependency invalidation across local and foreign items, cancellation semantics, and rules for when the compiler session itself must be reconstructed.

The absence of that contract does not make incremental Charon impossible. It identifies the engineering that is not already provided by Charon 0.1.210.

Basis: pinned **source** plus **derived** architecture requirements.

## Boundaries

- **No fresh execution was performed.** This report does not measure warm/cold latency, rustc incremental hits, Cargo rebuild decisions, disk use, or the speedup from `--start-from`.
- **Cargo freshness is intentionally not overclaimed.** The pin delegates to `cargo build`; source inspection here does not establish every condition under which Cargo invokes or skips the selected crate's wrapper. Later Charon source changed this area explicitly, so it must be revalidated behaviorally.
- **rustc's own incremental compiler is a separate layer.** Charon may benefit from rustc/Cargo caching without thereby having incremental LLBC semantics.
- **Deterministic output is separate.** Repeating a fresh traversal may reproduce the same IDs/bytes, but determinism does not itself create an incremental update contract.
- **`--start-from` is root selection, not edit invalidation.** It reduces reachable work but does not compute which roots changed.
- **No impossibility claim.** A future server or an Anneal-owned cache could reuse Charon results. This report only characterizes what the pinned Charon interface and state lifetime already provide.
- **No performance conclusion.** The source shows where reuse can occur and where state is recreated; it does not quantify whether Charon, rustc, or Cargo dominates an edited-workspace latency budget.

## Evidence

Primary subject:

```text
AeneasVerif/charon
a535e914f74db4fd9e6be7048f4233270d8945c0
version 0.1.210
rust-toolchain nightly-2026-05-31
```

Pinned source:

- `charon/src/bin/charon/main.rs`, blob `b4460ce4cd3baa32308718e79b6e194860b042a6`: Cargo/rustc subprocess topology, one translation per target, and whole-result multi-target merge.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: one `rustc_driver::run_compiler` invocation, `TyCtxt`-scoped callback translation, selected-crate behavior, and stopping after analysis.
- `charon/src/bin/charon-driver/main.rs`, blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`: post-extraction transforms and complete-result serialization.
- `charon/src/bin/charon-driver/translate/translate_ctx.rs`, blob `e7e10ceb5c6d8ee1834ad2d11d021c92b1f5f6ec`: per-run maps, queues, processed set, metadata/name caches, and Hax-definition lookup.
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: root-driven reachability traversal, fresh context construction, item-slot allocation, queue processing, and dropping rustc/Hax state before returning the translated result.
- `charon/src/bin/charon-driver/hax/state.rs`, blob `63fc236effb5b581582a8bf10f3c5934d857d6eb`: Hax global/per-item cache structures and fresh state construction tied to `TyCtxt`.
- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: `--start-from`/include/opaque/exclude semantics and the multi-target performance warning.
- `charon/src/export.rs`, blob `d5428958eb870f9f8531a8d193385c6be782338a`: whole-`CrateData` serialization/deserialization and exact-version check.
- `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`: selected Rust nightly.

Adjacent non-authoritative history used only for a boundary:

- `AeneasVerif/charon@67da6d3b8f31dfb0d003aee1596040f9efd7d27f`, `charon/src/bin/charon/main.rs`, blob `a5aa2c459ccde69502093dcf6988f2a5d314c7d3`: later code sets a fresh `RUSTC_WORKSPACE_WRAPPER` fingerprint with the explicit purpose of forcing Cargo to rerun Charon.

The evidence roles are **source** and **derived** architecture conclusions. There is no fresh **execution** evidence in this package.

## Revalidation

For another Charon revision, check the incremental question in layers rather than asking only whether a server exists:

1. **Extraction lifetime.** Follow the selected-crate path from `charon cargo`/`charon rustc` through `rustc_driver::run_compiler`. Record whether compiler state survives a request.
2. **Charon state lifetime.** Inspect construction of `TranslateCtx`, Hax state, ID maps, processed sets, and caches. Determine whether any are restored from a prior run.
3. **Root pruning.** Revalidate `--start-from`, include/opaque/exclude rules, and whether they remain a fresh graph traversal or accept a previous translation as input.
4. **Persistent identity.** Determine whether item/source IDs now have a documented cross-run stability contract suitable for patching snapshots.
5. **Serialization/protocol.** Look for base-snapshot IDs, deltas, tombstones, generations, server sessions, invalidation messages, or incremental result APIs.
6. **Cargo freshness.** Inspect wrapper/fingerprint handling. In particular, preserve the distinction between the 0.1.210 pin and later revisions that explicitly force a rerun through `RUSTC_WORKSPACE_WRAPPER`.
7. **rustc reuse.** Record whether Charon enables, disables, or isolates rustc incremental state and what cache directory/fingerprint identity is used.

On an execution-capable surface, add a bounded edited-workspace probe. Use a small workspace with one target crate and one dependency, then record for cold, unchanged-warm, leaf-edit, signature-edit, dependency-edit, and `--start-from` runs:

- whether Cargo invokes `charon-driver` for each crate;
- rustc invocation arguments and incremental-cache paths;
- Charon translated-item counts;
- output hashes and item-ID/name correspondence;
- wall time and peak memory; and
- which output declarations change.

That matrix can quantify lower-layer reuse while preserving the central semantic distinction: a faster fresh extraction is still not the same thing as a Charon-owned incremental LLBC update protocol.
