# Interactive pipeline invalidation graph for Anneal V2

## Summary

An interactive Anneal pipeline cannot safely treat “the file changed” as one invalidation event. The selected stack has several independently cached state machines, and the current pins do not expose one end-to-end incremental protocol that composes them.

The conservative graph is:

```text
Rust source + Cargo compilation identity
        |
        v
rustc/Cargo + Charon execution
        |
        v
complete LLBC snapshot
        |
        v
Aeneas whole-crate translation
        |
        v
generated Lean source tree
        |
        +------------------------------+
        |                              |
        v                              v
Lake module artifacts             open LSP document text
(.olean/.ilean/...)                    |
        |                              |
        +--------------+---------------+
                       v
              Lean server snapshots
                       |
                       v
            tactic state / diagnostics
```

The crucial rule is that each edge owns its own freshness contract. A stable path, item name, process, workspace, or server is not a freshness token for the value behind it.

At the current Charon pin, translation has useful within-run caching and root pruning but no supported cross-run LLBC update protocol. After a Rust change, the safe Charon boundary is therefore a newly produced complete LLBC snapshot for the affected compilation subject. At the current Aeneas pin, a translation call reconstructs crate-wide contexts and retranslates the selected declaration classes; process reuse is possible, but the safe semantic invalidation unit is again the complete normalized LLBC crate. Generated Lean can then be rebuilt through Lake's own trace/hash rules.

The Lean server introduces a second kind of state. An open LSP document is client-owned text. Replacing a generated `.lean` file on disk does not change the already-open document that Lean is elaborating. Imported generated modules are different: Lean consumes compiled module artifacts, and a changed dependency is handled through rebuild/reload and worker invalidation rather than by silently mutating an already-loaded environment. A correct interactive Anneal host must therefore synchronize both the filesystem/build graph and the live document/server graph.

Current Anneal V2 does **not** yet implement this full pipeline. At `google/zerocopy@41f5b37...`, the live CLI exposes `setup`; translation/scanning modules are still marked `dead_code`. The current scanner nevertheless records an important intended contract: LLBC is the source of truth for annotations that affect Aeneas generation, and each Cargo target gets a stable Lean-compatible artifact slug. That slug is an identity for locating an artifact, not a content generation. This report therefore specifies the invalidation constraints that a future interactive V2 implementation must preserve; it does not claim that V2 already realizes the graph.

## Applicability

This report applies to the exact stack selected by Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`, Rust `nightly-2026-05-31`);
- Aeneas `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`); and
- Lean/Lake `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

“Inval­idation” means deciding that a previously computed result must not be treated as the current semantic result for a newer input snapshot. It is broader than deleting a cache file. Recomputing a stage, restoring a different artifact-cache entry, restarting a Lean file worker, or sending a new LSP document version can all be correct invalidation responses.

The graph deliberately separates **semantic invalidation** from **performance reuse**. Cargo may avoid compiler work, Charon may reuse data during one extraction, Aeneas may keep a worker pool alive, Lake may restore cached artifacts, and Lean may reuse command snapshots. None of those mechanisms independently proves that a result from generation `g` is valid for generation `g+1`.

The report also distinguishes **directly open generated files** from **generated modules imported by another proof file**. The first are governed by the LSP document-synchronization contract in addition to Lean elaboration. The second are governed first by Lake/module-artifact freshness and then by the server's dependency-refresh lifecycle.

## Findings

### Current V2 supplies identities but not an implemented interactive pipeline

At the examined zerocopy revision, `anneal/src/main.rs` exposes only the `setup` subcommand. `resolve`, `scanner`, `setup`, and `util` are compiled with `dead_code` allowed. The V2 source therefore does not justify a claim that Rust edits already flow through Charon, Aeneas, Lake, and a Lean language server.

The dormant scanner does define the intended translation identity boundary. `AnnealArtifact` identifies a Cargo target by manifest path, target name, and target kind. `artifact_slug` hashes those identity fields into a stable Lean-compatible name; `llbc_file_name` derives `<slug>.llbc`; and the source comment states that later Aeneas/Lean stages can reuse the same slug when associating generated Lean with that artifact.

The same file states that Charon compiles the entire target and that generated LLBC is the source of truth for Anneal annotations that affect Aeneas code generation. These two facts imply an important negative rule: **the artifact slug cannot serve as the LLBC freshness token**. Editing the Rust body normally leaves manifest path, target name, and target kind unchanged, so the same slug can name different LLBC contents over time.

A future interactive implementation should therefore keep locator identity and generation/content identity separate from the beginning.

### Rust edits invalidate a compilation subject, not merely one source pathname

`charon cargo` delegates build-unit selection and rustc command construction to Cargo. Cargo's unit graph includes the selected target, dependencies, host-side build scripts and proc macros, feature/cfg choices, and target/profile distinctions. Build-script execution can additionally affect compiler flags and environment after the initial unit graph is constructed.

For Anneal, this means that “Rust edit” should be read as a change to the effective compilation subject. A body edit is the simple case. A feature change, target change, dependency change, build-script output change, cfg change, or relevant compiler/toolchain change can alter the Rust program seen by Charon even when the edited `.rs` bytes are unchanged.

The safe invalidation edge is therefore:

```text
relevant compilation-subject change
    -> previous LLBC for that subject is not current
```

Cargo/rustc freshness may allow Charon's underlying compiler work to be cheaper, but Anneal should not infer LLBC freshness merely because Cargo reports other artifacts as reusable.

### Charon 0.1.210 does not expose a cross-run LLBC delta protocol

The selected Charon has demand-driven extraction, `--start-from`, per-run processed-item sets, and caches tied to one rustc `TyCtxt`. Those mechanisms reduce duplicate work inside one extraction.

They do not form a cross-run update protocol. Each selected-crate extraction constructs fresh translation state, builds a translated crate, applies post-extraction transforms, serializes the complete result, and exits the driver process. The public interface does not accept an earlier LLBC snapshot plus an edit set and return a validated delta.

This makes the complete LLBC snapshot the conservative semantic handoff to the next stage. An interactive host may retain process-independent metadata or exploit Cargo/rustc reuse, but it should publish a new LLBC generation only after a Charon execution establishes the complete result for the new compilation subject.

`--start-from` is useful for reducing the reachable item graph when roots are known. It is not an edit-invalidation algorithm. Anneal must not treat “the edited function was not one of these roots” as proof that a previous LLBC snapshot remains valid.

### LLBC changes conservatively invalidate the whole Aeneas crate translation

Aeneas exposes a real in-memory library boundary, but the selected revision does not expose cross-request incremental translation either.

`Translate.translate_crate_to_pure` starts by computing fresh crate-wide contexts. Those contexts include a use graph, declaration-group membership, type analysis, and function analysis. The translation then rebuilds the selected type/global/function/trait/trait-implementation results. Individual functions and later pure micro-passes have useful per-function decomposition and parallelism, but they execute against shared maps and crate-wide context.

Extraction adds another global dependency. Aeneas registers globally unique target names and computes dependency/SCC structure before emitting declarations. A declaration whose own translated body is reusable can still need different emitted Lean because another declaration changed naming or recursion structure.

The safe first interactive rule is therefore:

```text
new normalized LLBC crate generation
    -> recompute Aeneas semantic translation for that crate
    -> replace the generated Lean result as one coherent generation
```

A persistent Aeneas process may still be valuable for latency. Keeping the process or worker pool alive is not permission to retain semantic results from the preceding LLBC snapshot.

Finer-grained reuse can be added later, but it needs explicit dependency keys, deletion/tombstone handling, and equivalence tests against clean whole-crate translation. Until such a protocol exists, whole-crate semantic recomputation is the defensible baseline.

### A generated Lean path is not a generated Lean generation

The same naming issue appears at the Aeneas-to-Lean edge. Aeneas writes generated Lean to ordinary target files, and Anneal intends to associate LLBC/Lean through stable artifact-derived names. Reusing the same pathname after a Rust edit is desirable for navigation, but it means consumers need another way to distinguish old and new bytes.

A robust host should treat the generated output as a snapshot with a generation or digest. It should not publish a partly rewritten generated tree as the “current” model. In particular, removing a Rust declaration must remove its stale generated declaration; appending or selectively overwriting files without deletion accounting can leave a model that contains both generations.

The simplest correct baseline is staged replacement: produce the complete Aeneas output for one LLBC generation, validate that translation completed under the intended policy, then make that generated tree visible as the next generation.

### Lake owns module-artifact freshness after generated Lean changes

Once generated Lean becomes an input to a Lake project, Lake has its own invalidation model. At the selected revision, ordinary module reuse is based on a saved dependency trace, not solely on source mtimes or on the `.lean` pathname.

For `leanArts`, the trace incorporates the module's normalized source text, effective Lean options, module/package identity, selected Lean toolchain identity, traced compiler arguments, and imported/setup dependency traces. A changed trace invalidates the old local module result. Lake may then compile Lean or satisfy the new trace from an artifact-cache entry; “invalidated” does not necessarily mean “compiler process ran.”

This layer is valuable because Anneal does not need to replicate Lake's detailed `.olean` dependency logic. The host instead needs to supply a coherent generated source/configuration generation and let the exact selected Lake decide which compiled artifacts correspond to that generation.

Anneal must still avoid one shortcut: it cannot infer that an existing `.olean` is valid simply because the generated `.lean` path is unchanged. The trace, not the pathname, owns that decision.

### An open LSP document is a second copy of generated source state

LSP changes the state graph because an open document is no longer just a file on disk. Under LSP 3.18, the client supplies the text at `didOpen` and subsequent versioned `didChange` notifications. Lean's watchdog retains each open document's URI, version, and text and reconstructs a worker from that retained text after restart.

Therefore:

```text
Aeneas overwrites generated/F.lean on disk
```

does **not** imply:

```text
an already-open Lean worker now elaborates the new generated/F.lean bytes
```

If Anneal or an MCP bridge directly opens generated files, regeneration must be followed by an explicit synchronization step: send the complete new text (or a correct incremental edit sequence) through `didChange`, or close and reopen the document from the regenerated bytes. A tactic-state query is valid only after that document version has been accepted and elaborated.

This is an independent invalidation edge from Lake's build graph. Updating `.olean` files does not update the text of a directly open document, and updating an open document does not by itself rebuild imported module artifacts for other files.

### Imported generated modules require dependency rebuild/reload, not document sync alone

A proof file often imports generated definitions rather than opening the generated file itself. In that topology, Lean consumes the compiled dependency environment. Regenerating the imported `.lean` source must first flow through Lake/module compilation so that the dependency artifact represents the new generated model.

Lean's server then has its own stale-dependency rule. The selected server does not compute a semantic hash of a loaded `Lean.Environment` and mutate imported state in place. When dependencies change, the watchdog treats dependents as stale and refresh/restart rebuilds their setup/import environment. This is deliberate: imported compacted regions have process-lifetime constraints that make arbitrary in-place replacement unsafe.

The interactive host therefore needs two downstream actions after a generated-module change:

1. establish the new dependency artifacts under Lake's freshness rules; and
2. ensure affected open dependents reload those artifacts through the server's dependency-refresh/restart lifecycle.

A proof file that has not changed text can still require complete re-elaboration because the declarations it imports changed.

### Proof-only edits have a shorter invalidation path

A proof edit that changes only an already-open proof document, without changing the generated model, project imports, toolchain, or effective configuration, need not rerun Rust, Charon, or Aeneas.

Lean's file worker can apply the versioned `didChange`, retain snapshots before the first affected region where valid, invalidate later processing, and cancel pending requests tied to stale document state. This is the main fast path an interactive proof workflow should preserve:

```text
proof text edit
    -> new LSP document version
    -> Lean incremental re-elaboration
    -> new tactic state / diagnostics
```

The fast path ends when the edit changes the import header or other setup inputs, or when an upstream generated dependency changes. At that point Lean may need new import processing or a restarted worker rather than suffix-only elaboration.

### Toolchain and workspace changes invalidate server identity even when source is unchanged

The selected Lean server does not provide independent Lake workspace configuration per open file. One watchdog/server process inherits one working directory and environment, and per-file workers inherit that project context. `lake serve` prepares one workspace; `lake setup-file` configures files against that loaded workspace rather than discovering an arbitrary second project selected by LSP `rootUri`.

An Anneal server pool should therefore key reusable Lean servers by a complete prepared-environment identity: at minimum the Lean executable/toolchain, Lake workspace root/configuration, resolved dependency graph, relevant environment/search paths, plugins/native libraries, and server arguments.

Changing that identity should route work to a newly prepared server generation. Keeping the same process merely because the proof URI is unchanged can mix incompatible environments.

### One explicit generation record prevents cross-layer time travel

The individual tools do not provide one common generation identifier, so Anneal should add one at the orchestration layer.

For each interactive snapshot, the host can record a tuple such as:

```text
G = {
  Rust/Cargo compilation-subject identity,
  exact Rust + Charon + Aeneas + Lean/Lake identities,
  LLBC digest or immutable snapshot identity,
  generated-Lean tree digest or snapshot identity,
  prepared Lake workspace identity,
  relevant compiled-artifact trace identities,
  LSP document URI + version for every directly open generated/proof file
}
```

The precise serialization can change. The invariant matters more: a tactic-state result or diagnostic should be attributable to one coherent generation. If a query starts while regeneration is in flight, the host must either finish against the old generation or wait for the new one; it must not combine new LLBC with old generated Lean, new generated Lean with old imported artifacts, or new disk bytes with an old open-document version.

This also gives cancellation a semantic role. Once generation `G+1` becomes current, outstanding queries for `G` can be canceled or explicitly labeled stale rather than allowed to race into the new user-visible state.

### The minimum safe invalidation matrix is conservative by design

The following matrix gives the first implementation a correctness-oriented baseline. “Rebuild Lean” means let Lake/Lean establish artifacts for the changed source/configuration; an artifact-cache hit can satisfy that step without recompilation.

| Change | Cargo/Charon | Aeneas | Lake/module artifacts | Lean server action |
| --- | --- | --- | --- | --- |
| Proof-body edit only | no | no | usually no | `didChange`; await new elaboration |
| Proof import/header edit | no | no | as required by changed module setup | reprocess imports; restart if setup/dependency lifecycle requires it |
| Generated file replaced after Aeneas | no additional upstream work | already done | rebuild/restore artifacts for new source | `didChange`/reopen if directly open; refresh/restart dependents if imported |
| Rust body edit affecting a verified target | rerun affected compilation subject and Charon | recompute affected LLBC crate conservatively as a whole | rebuild generated modules | synchronize direct documents; reload affected dependents |
| Cargo features/cfg/target/build inputs change | rerun affected compilation subjects and Charon | recompute resulting LLBC crates | rebuild generated modules | synchronize/reload downstream state |
| Charon version/options affecting translation | rerun Charon | recompute Aeneas for new LLBC | rebuild generated modules | synchronize/reload downstream state |
| Aeneas version/options affecting translation | LLBC may be reusable only after compatibility is established | rerun Aeneas | rebuild generated modules | synchronize/reload downstream state |
| Lean/Lake/Mathlib/toolchain identity changes | Rust/LLBC may remain reusable | generated Lean may remain textually reusable | rebuild/revalidate under new environment | use a server prepared for the new environment |
| Workspace/dependency/plugin/search-path identity changes | no upstream translation solely for this reason | no upstream translation solely for this reason | re-resolve/rebuild setup as required | do not reuse a server keyed to the old environment |

This matrix intentionally invalidates more than a future optimized system may need. Each relaxation should come from a proved or tested dependency relation, not from observing that two filenames or process IDs happen to remain the same.

### A later fine-grained implementation needs deletion and dependency tests, not only edit tests

Most incremental prototypes begin with “edit one function and see less work.” That is insufficient here. Charon and Aeneas both have global or whole-crate structures, and Lean/Lake both have imported-environment state. A useful invalidation test suite needs at least:

- function body change;
- function signature change;
- type/layout change used by another function;
- trait declaration/implementation change;
- global/static change;
- declaration addition and deletion;
- rename causing target-name collision/resolution changes;
- Cargo feature/cfg change;
- generated Lean import/header change;
- proof-only body edit;
- generated dependency change while a dependent proof is open;
- direct regeneration of an already-open generated file; and
- toolchain/workspace identity change while a server is retained.

For any proposed incremental shortcut, the oracle should be a clean recomputation of the relevant full stage. Equality can be byte-level where the contract promises deterministic bytes, or semantic/diagnostic equivalence under a separately specified relation where bytes may legitimately differ. The test must state which relation it uses.

## Boundaries

No fresh Cargo, rustc, Charon, Aeneas, Lean, Lake, LSP, or MCP process was executed for this report. The graph is a synthesis of the exact pinned source and already-preserved source investigations.

Current Anneal V2 is incomplete. The report specifies constraints on a future implementation; it does not describe a currently working V2 interactive command or server.

The report does not claim a minimal invalidation graph. It chooses conservative whole-compilation-subject, whole-LLBC-crate, and prepared-workspace boundaries where the selected tools do not expose a smaller validated cross-request boundary.

Cargo/rustc incremental compilation is not characterized as an Anneal semantic cache. It may make rerunning a stage cheaper, but this report does not prove when Cargo will invoke or skip Charon's wrapper for every edit. The Charon corpus specifically records this as an upgrade-sensitive boundary.

Aeneas process reuse is not treated as declaration-result reuse. The selected library has shared process-global configuration/error state and no public edit/update protocol. A production persistent host needs request isolation independently of semantic invalidation.

Lake artifact-cache hits are not treated as proof that old local artifacts are current. Lake chooses artifacts for a new trace identity; the cache can satisfy invalidated work without reusing the stale result.

The LSP rules here concern document synchronization and the selected Lean server. They do not specify an MCP protocol. An MCP layer must preserve the same generation/document-version distinctions rather than inventing a second hidden text state.

The report does not specify source-map correctness from Lean positions back to Rust. The current corpus shows that this is a separate correspondence problem. Invalidation can keep generations coherent while diagnostics still have only declaration-level or generated-file provenance.

The matrix does not decide when a changed proof should be persisted back into Rust annotations, generated files, or a sidecar. That storage/design choice is outside this invalidation subject.

## Evidence

**Current Anneal authority — `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.**

- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: current V2 CLI surface; only `setup` is live; translation modules remain allowed as dead code; the same file contains the read-only generated-workspace archive-reuse integration test.
- `anneal/src/scanner.rs`, blob `7b4884c9ac16cf30146b851894bd7216b0d1edb8`: `AnnealArtifact`, stable artifact slug, LLBC pathname derivation, and the explicit statement that generated LLBC is the source of truth for annotations affecting Aeneas code generation.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: current design authority and deliberate non-decisions around the exact division of responsibilities and interactive implementation.
- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: governing verification and user-facing principles.

**Charon — `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.**

- `charon/src/bin/charon/main.rs`, blob `b4460ce4cd3baa32308718e79b6e194860b042a6`: Cargo/rustc orchestration and whole-result translation flow.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: selected rustc invocation and one-driver extraction boundary.
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: fresh translation context, root-driven traversal, and complete translated-crate construction.
- `charon/src/export.rs`, blob `d5428958eb870f9f8531a8d193385c6be782338a`: complete `CrateData` serialization and exact-version compatibility boundary.

The current reference reports `charon-cli-invocation-modes-0-1-210` and `charon-incremental-capabilities-0-1-210` preserve the detailed source walk that supports the Charon statements above.

**Aeneas — `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.**

- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: fresh `translate_crate_to_pure` pipeline, whole selected declaration-class translation, extraction boundary, generated-file writing.
- `src/interp/Interp.ml`, blob `7b06ee4d1bdd302d9cbd85fc2e822c1f5324c1e5`: fresh whole-crate context construction and analysis.
- `src/pure/PureMicroPasses.ml`, blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`: per-function micro-pass decomposition against shared whole-program maps.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: generated-output destination controls.

The current reference reports `aeneas-incremental-translation-feasibility-nightly-2026-06-03` and `lean-generated-file-interactive-workflows-v4-30-0-rc2` preserve the detailed source analysis behind the whole-crate and generated-file conclusions.

**Lean/Lake — `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.**

- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: module dependency trace, source/configuration inputs, artifact-cache flow, and aggregate Lean module outputs.
- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: saved-trace freshness and ordinary/old-mode reuse boundaries.
- `src/Lean/Server/Watchdog.lean`, blob `68ed22f9178c9ae917c595c364d23df902d9478f`: retained open-document state, per-file workers, restart lifecycle, and stale-dependency handling.
- `src/Lean/Server/FileWorker.lean`, blob `c803034ed8810f13a5ef38a603a21e610efca2bc`: `didChange` incremental re-elaboration and edit cancellation.
- `src/Lean/Language/Lean.lean`, blob `124d4739bc910eb30ec35844348c785bf9f6c70a`: incremental syntax-prefix reuse and invalidation after changed input.
- `src/Lean/Server/FileWorker/SetupFile.lean`, blob `35a756819a8de5ebb05256bb39d83148f9f24145`: per-document `lake setup-file` integration.
- `src/Lean/Server/README.md`, blob `4bac3026e17b604888324821f5725e0338f802e3`: worker architecture and dependency refresh/restart rationale.

The current reference reports `lake-olean-invalidation-v4-30-0-rc2`, `lean-environment-hashing-invalidation-v4-30-0-rc2`, `lean-generated-file-interactive-workflows-v4-30-0-rc2`, and `lean-server-multi-workspace-isolation-v4-30-0-rc2` preserve the detailed exact-pin investigations summarized here.

**LSP 3.18 document synchronization.** `microsoft/language-server-protocol@de9a671ae6ba374cc748a29c1c620cbc536302ff`.

- `_specifications/lsp/3.18/textDocument/didOpen.md`, blob `f2bc2141ca7b4efdc1521493470cc631cf083d99`: client-managed content for open documents.
- `_specifications/lsp/3.18/textDocument/didChange.md`, blob `81e7475181818d44229c10dbcc25de7f3de83c69`: versioned ordered synchronization before requests.
- `_specifications/lsp/3.18/textDocument/didClose.md`, blob `e8c956a6402a8a7ff031839fa58fba5d39c11f6d`: filesystem/URI master state resumes after close.

Evidence roles are exact pinned **source**, normative **protocol**, preserved corpus **source analysis**, and explicit **derived** composition rules. There is no fresh execution evidence.

## Revalidation

For a future Anneal toolchain, revalidate this graph from the boundaries inward.

First inspect current Anneal. Confirm whether V2 still treats a Cargo target/LLBC file as the main translation unit and whether it has introduced its own content generations, persistent Charon/Aeneas hosts, or a server protocol. If it now implements incremental state, identify the exact keys and invalidation rules instead of carrying forward this report's conservative whole-stage boundaries.

Then revalidate Charon and Aeneas. For Charon, check whether a supported cross-run translation server, persistent snapshot, content identity, or edit/delta protocol exists; distinguish it from within-run caches and Cargo/rustc reuse. For Aeneas, check whether `translate_crate_to_pure` still rebuilds whole-crate contexts and whether extraction still depends on global names/SCCs. If either tool introduces fine-grained reuse, test deletion, signature/type/trait/global changes, not only function-body edits.

Revalidate Lake's module trace and Lean server behavior at the selected Lean revision. Verify which effective inputs enter module freshness, how changed imports become server state, whether open-document text remains client-owned, and whether server workers still require restart/refresh for changed dependencies. Recheck workspace isolation before sharing one server across independently configured projects.

On an execution-capable surface, build a small end-to-end probe with one Rust target, one generated Lean module, and one open proof document. Preserve every generation's Rust input, LLBC, generated Lean, Lake trace/module artifacts, LSP document versions, and tactic-state query result. Run at least these mutations separately: Rust body; Rust signature; deleted Rust item; Cargo feature; generated Lean import; proof body; proof import header; dependency artifact; and toolchain/workspace identity. For every mutation, compare the incremental result against a clean reconstruction under the same exact toolchain.

The probe should deliberately overwrite an already-open generated file without sending `didChange`. It should fail the freshness assertion until the document is synchronized. It should also change an imported generated module while keeping the dependent proof text unchanged and verify that the dependent worker is refreshed before accepting a new tactic-state result. Those two cases catch the most dangerous cross-layer stale-state mistakes described by this report.
