# Lean environment identity and invalidation at v4.30.0-rc2

## Summary

Lean 4.30.0-rc2 does not use a content hash of the full `Environment` to decide whether an old elaboration state is still reusable. The incremental language processor says explicitly that it has no cheap semantic test for an unchanged `Environment`. It therefore reuses old state through persistent snapshots and syntactic checks, and it stops forwarding old state from the first relevant syntax change.

This distinction matters for an interactive Anneal architecture. A `Lean.Environment` is persistent—updates produce new environment values rather than mutating one environment in place—but persistence does not give Anneal a stable cross-process environment digest. Within one document worker, the incremental processor can reuse an old import-processing result when the parsed header is unchanged. Changes in an imported file are handled outside that reuse test: the language-server watchdog tracks the document's import closure and marks dependent workers stale on dependency save or watched-file change. The worker then asks the user/client to restart the file. This is event-driven dependency invalidation, not environment-hash comparison.

The module-loading boundary has the same shape. `ModuleSetup.importArts` supplies paths for imported artifacts. Lean reads those `.olean*` files and reconstructs the imported environment; the `ImportArtifacts` structure itself contains paths, not content digests. Lake owns the build-freshness hashes and traces that decide which artifact paths are current. A separate reference report covers that Lake layer. Do not treat Lake's file/build hashes, Lean's Git revision string, an in-memory `Environment`, and a server document snapshot as interchangeable identities.

For Anneal, the useful rule is: **reuse a Lean environment only inside the lifetime and invalidation protocol that produced it, or attach your own complete semantic basis. Do not assume Lean exposes a canonical environment fingerprint that makes arbitrary environment reuse safe.**

Basis: **source + derived**. No fresh Lean or Lake execution was performed.

## Applicability

These findings apply to `leanprover/lean4` commit
[`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`](https://github.com/leanprover/lean4/tree/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc),
tagged `v4.30.0-rc2`, which current Anneal `main` at
[`41f5b37afe7060fd9fe08c00b200672cd76d77b9`](https://github.com/google/zerocopy/tree/41f5b37afe7060fd9fe08c00b200672cd76d77b9)
selects in `anneal/flake.nix`.

The report covers four connected layers:

1. the in-memory `Lean.Environment` and imported `ModuleData`;
2. Lean's incremental command/document processor;
3. the language-server mechanism that notices imported Lean source changes; and
4. the boundary at which Lake supplies pre-resolved imported artifacts.

The report deliberately does **not** re-specify Lake's own `BuildTrace`, `.trace`, `.hash`, file-content-hash, or `LEAN_GITHASH` machinery. Published `lake-state-model-v4-30-0-rc2` and durable ready work `lean-lake-trace-hash-artifacts-v4-30-0-rc2` own those mechanisms. Here they matter only because they sit below the environment-construction boundary.

"Environment identity" in this report means the facts needed to know whether an environment or a snapshot derived from it remains semantically applicable. It does not mean pointer identity, declaration identity, the Lean compiler's Git revision, or a cryptographic hash of `.olean` bytes.

No fresh execution was performed. Statements about runtime behavior are source-level consequences unless this report explicitly identifies preserved upstream test evidence.

## Findings

### 1. `Environment` is persistent, but persistence is not a fingerprint

Lean's kernel environment documentation says that environments are never destructively updated. The elaborator-level `Lean.Environment` similarly stores persistent kernel/environment state, asynchronous branches, extension state, and imported module metadata. A later declaration or extension update produces another environment value rather than mutating all prior snapshots in place.

That is what makes command snapshots useful: a completed snapshot can retain the exact environment state that existed after its command.

It does **not** imply that Lean can cheaply tell whether two independently obtained environment values mean the same thing. At this revision, the incremental processor states the opposite: semantic change detection is not available because there is no cheap way to determine that the `Environment` is unchanged.

Basis: **source + derived**.

Implication for Anneal: persistent values support safe reuse *through Lean's own snapshot chain*. They do not provide a portable cache key for an environment reconstructed in another process, VM, workspace, or build tree.

### 2. Incremental reuse is driven by syntax and retained snapshots, not a full-state hash

`Language.mkIncrementalProcessor` retains the previous top-level snapshot and passes it to the next call. Lean's language processor then decides how much prior state remains reusable.

The source documents the intended rule directly. Ideally Lean would use strong hashes over the full state and inputs for reuse inside elaboration, but this revision instead performs simpler syntactic checks. The processor records the first textual difference and stops forwarding old state from the first relevant syntactic mismatch.

At command granularity, this lets Lean restart from the environment stored in the last still-valid command snapshot. At finer granularity, participating elaborators compare the syntax they previously inspected and reuse snapshot tasks only while those checks continue to match.

Basis: **source**.

This means "same current source suffix" is not enough to recover a reusable environment. Reuse is justified by the incremental processor's retained predecessor snapshot plus its syntax-comparison protocol.

### 3. An unchanged import header reuses the previous import-processing result

The header path is especially important for dependency invalidation.

When the newly parsed header is syntactically unchanged, `Language.Lean.process` takes a fast path that reuses the old processed header/import snapshot. It does not reconstruct an imported environment and compare a semantic environment hash. The reused snapshot already contains the prior `Command.State` and imported `Environment`.

When the header syntax changes, the processor discards/cancels the old path and calls `setupImports` again. The resulting setup supplies direct imports, options, plugins, and pre-resolved import artifacts, and `processHeaderCore` builds a fresh header environment from that setup.

Basis: **source**.

A dependency can therefore change while the dependent file's own header text remains byte-for-byte unchanged. That case cannot be made correct merely by the document processor's syntax reuse rule. It needs a separate dependency invalidation channel.

### 4. The language server handles dependency changes by marking dependents stale

Each file worker computes its imported-module closure from the initialized environment and reports that closure to the watchdog. The watchdog uses this relationship to invalidate dependents.

When an open Lean file is saved, the watchdog looks up workers that depend on it and sends each a `$/lean/staleDependency` notification. Watched `.lean` filesystem changes follow the same pattern. The receiving worker does not splice a new imported `Environment` into its existing snapshot chain. It publishes a sticky diagnostic telling the client that imports are out of date and that the file should be restarted.

The watchdog source also explains the process boundary: it can restart a file worker when needed, and a restart frees/reconstructs that worker's imports.

Basis: **source**.

This is a coarse but explicit invalidation protocol:

`dependency source event -> watchdog dependency graph -> stale notification -> file restart -> import setup/environment reconstruction`

There is no environment digest comparison in that chain.

### 5. Document edits and dependency edits have different invalidation mechanisms

The two cases should not be conflated:

- **Edit inside the current file:** the same worker invokes the incremental processor with its prior snapshot. Text/syntax comparisons decide the reusable prefix; old state after the first relevant change is discarded.
- **Change to an imported file:** the dependent worker's own source may be unchanged, so syntax comparison cannot notice the semantic dependency change. The watchdog's import-closure tracking marks the dependent stale and requires restart/re-setup.

Basis: **source + derived**.

For an Anneal MCP/LSP service, this is the key architectural distinction. A per-file Lean session may safely exploit Lean's incremental reuse for edits to that file, but the service still needs an external dependency/version protocol for imported artifacts and toolchain/configuration changes.

### 6. `ModuleData` serializes environment contents, not an environment fingerprint

`ModuleData` is the Lean-side payload stored in `.olean` files. At this revision it contains:

- whether the file participates in the module system;
- its imports;
- constant names and constant information;
- extra constant names; and
- serialized persistent-environment-extension entries.

`EnvironmentHeader` separately records the main module, imports, imported module metadata, compacted regions, and module data.

Neither structure exposes a field documented as a content hash or semantic digest of the whole environment. `mkModuleData` constructs serialized module data from the environment; `writeModule` writes exported/server/private parts.

Basis: **source**.

This observation is narrower than claiming that no hash exists anywhere in Lean. Lean and Lake use many hashes for specific purposes. The point is that the serialized/imported environment representation inspected here does not itself provide the general semantic fingerprint that the incremental processor says it lacks.

### 7. `ModuleSetup` supplies artifact paths; Lean does not receive Lake's freshness proof as an environment hash

`Lean.Setup.ImportArtifacts` is an array-backed collection of file paths for the `.olean`, `.ir`, server, and private artifacts used for an import. `ModuleSetup.importArts` is a map from module names to those artifact path collections.

During import, `importModulesCore` either uses those pre-resolved paths or locates `.olean` files itself, then loads module data with `readModuleDataParts`. The import layer consumes the selected artifacts. The inspected setup structure does not carry Lake's `BuildTrace`, dependency hash, or file-content hash alongside each path.

Basis: **source + derived**.

The freshness decision therefore belongs outside this boundary. In normal Lake-managed use, Lake decides whether artifacts are reusable and supplies the resulting paths. Once Lean is given paths, its environment import path consumes them as the import inputs.

For Anneal, a path alone is not a durable semantic cache key. If Anneal persists or transfers a prepared Lean environment across machines or build trees, it must also preserve or reconstruct the source/toolchain/configuration/artifact identity that made those paths valid.

### 8. Lake artifact hashes and Lean environment applicability answer different questions

Lake's trace/hash state answers a build question: "May this output artifact be reused for these build inputs?" Lean's incremental snapshots answer a session question: "May this prior elaboration state be reused for this next document version?" The language-server stale-dependency path answers another session question: "Has an imported source changed so this worker must rebuild/restart its imported state?"

Those mechanisms intersect, but none is a substitute for the others.

Basis: **derived from source and the published Lake state-model report**.

A useful Anneal cache identity therefore needs to state what is being cached:

- generated Lean source;
- prepared Lake build artifacts;
- a particular `.olean`/`.ilean` set;
- a live Lean worker/session;
- an incremental document snapshot; or
- a higher-level proof result.

Using the word "environment" for all of them obscures different invalidation rules.

### 9. There is no supported source basis here for cross-process `Environment` equality

The inspected source supports these positive statements:

- environments are persistent;
- old command/document snapshots carry prior environments;
- incremental reuse is syntax/snapshot based;
- the processor explicitly lacks cheap semantic `Environment` equality;
- imports rebuild an environment from selected module artifacts; and
- server dependency changes cause explicit stale/restart handling.

It does **not** establish a supported API that serializes an arbitrary live `Environment` identity to a stable digest and later proves another environment equivalent by comparing that digest.

Basis: **source + derived**.

For a future Anneal service, treat any such digest as an Anneal-owned protocol unless a later Lean revision introduces and documents a suitable primitive.

## Boundaries

**No fresh execution.** This report did not run Lean, Lake, or the language server. It relies on the exact pinned source and on existing reference-corpus findings for adjacent Lake/server behavior.

**No claim that Lean contains no hashes.** Lean uses hashes for many local data structures, compiler/runtime objects, names, widgets, and other purposes. This report claims only that the inspected environment/incremental-import protocol does not provide the full-environment semantic fingerprint needed for arbitrary reuse, and the incremental processor explicitly says it has no cheap unchanged-environment test.

**No byte-level `.olean` identity claim.** A separate inventory item/report covers `.olean` format and identity. This report uses only the source-level fact that `ModuleData` is environment/module payload and that import consumes selected artifact paths.

**Lake freshness is not re-derived here.** The `lake-state-model-v4-30-0-rc2` report covers Lake's build traces and file hashes. The ready `lean-lake-trace-hash-artifacts-v4-30-0-rc2` result covers the detailed boundary between Lean-produced artifacts and Lake-owned trace/hash state.

**Dependency invalidation is scoped to the inspected server paths.** The save/watched-file handlers establish how the language server marks known source dependents stale. This report does not claim that every possible external mutation, generated artifact replacement, plugin change, environment variable change, or toolchain change is detected by those handlers.

**Restart behavior is not a proof of build freshness.** Restarting a file worker reconstructs its setup/import environment, but whether the imported artifacts are current is still governed by the setup/Lake build policy.

**No distributed-cache protocol is established.** The report gives constraints for designing one; it does not prove relocation, concurrency safety, shared-cache coherence, or cross-machine reproducibility.

## Evidence

### Anneal toolchain selection

**Source**

- `google/zerocopy` `41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
  [`anneal/flake.nix`](https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/flake.nix#L40-L45):
  current Anneal selects Lean `v4.30.0-rc2`.

### Persistent environment and serialized module state

**Source**

- `leanprover/lean4` `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`,
  [`src/Lean/Environment.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L122-L143):
  `ModuleData` payload.
- Same file,
  [lines 151-189](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L151-L189):
  `EnvironmentHeader` import/module state.
- Same file,
  [lines 207-220](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L207-L220):
  kernel environment model and non-destructive updates.
- Same file,
  [lines 560-622](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L560-L622):
  elaborator `Environment` structure.
- Same file,
  [lines 1825-1881](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L1825-L1881):
  `mkModuleData` and `writeModule`.

### Incremental environment reuse

**Source**

- `leanprover/lean4` `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`,
  [`src/Lean/Language/Lean.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Lean.lean#L81-L118):
  incremental reuse design; full-state hashes are an ideal, while the implementation uses syntax checks.
- Same file,
  [lines 365-384](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Lean.lean#L365-L384):
  processor entry point and explicit lack of cheap unchanged-`Environment` semantic detection.
- Same file,
  [lines 391-427](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Lean.lean#L391-L427):
  unchanged-header fast path reusing the prior processed snapshot.
- Same file,
  [lines 455-499](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Lean.lean#L455-L499):
  header comparison, old-state cancellation, and fresh `setupImports`/header processing.
- `src/Lean/Language/Basic.lean`
  [lines 397-406](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Basic.lean#L397-L406):
  `Language.mkIncrementalProcessor` retains and feeds back the previous snapshot.

### Artifact-path import boundary

**Source**

- `src/Lean/Setup.lean`
  [lines 65-100](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Setup.lean#L65-L100):
  `ImportArtifacts` is a path collection.
- Same file,
  [lines 135-160](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Setup.lean#L135-L160):
  `ModuleSetup.importArts`.
- `src/Lean/Environment.lean`
  [lines 2038-2130](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L2038-L2130):
  import graph traversal and artifact selection.
- Same file,
  [lines 2167-2180](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L2167-L2180):
  pre-resolved `.olean` paths are passed to `readModuleDataParts`.

### Server dependency invalidation

**Source**

- `src/Lean/Server/FileWorker.lean`
  [lines 475-496](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker.lean#L475-L496):
  a worker wraps `Language.Lean.process` in the incremental processor.
- Same file,
  [lines 543-549](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker.lean#L543-L549):
  import closure is obtained from the initialized environment.
- Same file,
  [lines 632-652](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker.lean#L632-L652):
  stale-dependency notification becomes a sticky "restart file" diagnostic.
- `src/Lean/Server/Watchdog.lean`
  [lines 939-949](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L939-L949):
  stale-dependency notification helper.
- Same file,
  [lines 1259-1274](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L1259-L1274):
  save event marks known dependents stale.
- Same file,
  [lines 1279-1290](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L1279-L1290):
  watched `.lean` changes also mark dependents stale.

### Adjacent corpus evidence

**Source + prior synthesis**

- `reports/lake-state-model-v4-30-0-rc2` at current `reference` head
  `741b0f90dfef1cd572249a88f8f1f8e79f5912cf`:
  Lake build traces, dependency hashes, modification-time fallback, and `.hash` sidecars.
- Durable ready result `e971875d-3410-4dae-8363-12e61acb5554`,
  `lean-lake-trace-hash-artifacts-v4-30-0-rc2`:
  detailed ownership of Lean Git-hash input versus Lake-owned artifact traces/hashes.
- `reports/lean-server-tactic-state-v4-30-0-rc2`:
  adjacent server architecture and dependency-staleness behavior.

No source above is treated as normative specification. These are implementation facts for the exact pinned subject.

## Revalidation

For another Lean revision, start with four cheap discriminators before repeating the full study.

1. **Incremental semantic-equality rule.** Diff `src/Lean/Language/Lean.lean` around the incremental-processing design note and `Language.Lean.process`. If the source still says semantic `Environment` equality is unavailable and still chooses reuse by syntax/snapshots, the central conclusion likely remains.
2. **Header reuse boundary.** Check whether an unchanged parsed import header still reuses the old processed import snapshot, and whether a changed header reruns `setupImports`.
3. **Artifact setup shape.** Check `ImportArtifacts`, `ModuleSetup`, and `importModulesCore`. If setup now carries content/semantic digests and Lean verifies them during import, update this report rather than assuming path-only behavior.
4. **Server dependency invalidation.** Check watchdog save/watched-file handling plus worker stale-dependency handling. If the server begins transparently rebuilding/rebinding imported environments instead of requiring restart, the session-level conclusion has changed.

A capable-surface execution probe should then distinguish syntax reuse from dependency invalidation:

1. create modules `A` and `B` with `B` importing `A`;
2. open `B` in a Lean server and obtain a tactic/diagnostic result;
3. edit only a command body in `B` and observe ordinary incremental reuse;
4. restore `B`, change and save `A` without changing `B`;
5. record whether `B` receives a stale-dependency diagnostic, whether its worker/session is automatically restarted, and what happens to existing RPC references;
6. restart `B` and verify that the reconstructed environment sees the new `A`;
7. repeat with dependency build mode set not to rebuild stale imports, recording Lake/setup-file status separately.

If testing a proposed Anneal cache, add one more experiment: copy or reconstruct the prepared artifacts in a fresh process/build root while preserving only the candidate cache identity. Verify that the identity changes for every source, import, toolchain, option, plugin, generated-file, and artifact mutation the cache claims to cover. Do not infer that Lean's in-process snapshot reuse proves that stronger cross-process property.