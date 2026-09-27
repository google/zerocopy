# Lean environment identity and invalidation at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lean's incremental language processor does **not** decide whether an elaboration environment can be reused by computing a semantic hash of `Lean.Environment`. The source states the opposite: there is no cheap way to determine whether an `Environment` is unchanged, so incremental reuse relies on syntax-preserving prefixes and stops carrying old state forward after the first relevant syntactic change.

This is not an accidental implementation detail around one cache. The processor's snapshot protocol is designed around that limitation. Its documentation says that strong hashes over the full state and inputs would be preferable, and that the current one-version snapshot history may someday be replaced by a cache indexed by strong hashes. At this revision, those strong environment/state hashes do not drive reuse.

The resulting invalidation model has three distinct layers:

- **Inside one file**, Lean carries immutable/persistent environment values through command snapshots. If the header and command prefix are syntactically unchanged, it reuses the previous snapshots and their command state. At the first syntactic change, it stops passing previous states to later processing because semantic environment equivalence is not cheaply testable.
- **At the import boundary**, an unchanged header can reuse the old import-processing task. If the header changes, Lean reruns setup/import processing and constructs a new imported environment.
- **Across changed dependency artifacts in the language server**, Lean does not silently rehash an already-open dependent's environment. The server treats the dependent as stale; refreshing dependencies restarts its worker and reruns Lake setup/import loading. This process boundary is deliberate because imported compacted regions cannot safely be freed and replaced in place.

`Lean.Environment` itself is persistent rather than destructively updated: adding declarations produces successor environments, and imported/local declaration storage is append-oriented. That persistence makes snapshot reuse possible, but it does not give the environment a stable content identity suitable for an Anneal cache key.

For Anneal, a cached proof or prepared Lean state must therefore not use "same `Lean.Environment` hash" as an upstream contract at this revision. Reuse must be grounded in stronger external identities that determine the environment—such as the exact resolved import artifacts, toolchain/configuration, and generated source—or it must stay within Lean's own snapshot lifecycle and invalidation rules.

No fresh Lean or server execution was performed. The report is based on pinned implementation source plus Lean's own server design documentation.

## Applicability

This report covers Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, selected by the Anneal toolchain examined here.

"Environment" means Lean's elaboration environment and its kernel environment substrate: imported and local constants, imported-module metadata, persistent environment-extension state, and the asynchronous elaboration state carried by `Lean.Environment`.

"Environment hash" means a stable semantic identity that could tell a caller that two complete Lean environments are interchangeable for elaboration or snapshot reuse. This report does not use "hash" to mean the hash tables inside `Environment`, hashes of individual names/expressions, or Lake's build/artifact hashes.

"Invalidation" below means when Lean stops reusing previously elaborated state or when the server requires an imported environment to be rebuilt/reloaded. It is distinct from Lake's decision to rebuild an `.olean`; Lake build invalidation is a separate inventory subject.

This report complements:

- `lake-state-model-v4-30-0-rc2`, which covers Lake's build traces and freshness machinery;
- the durable `lean-lake-trace-hash-artifacts-v4-30-0-rc2` result, which covers Lake-owned hashes around Lean-produced module artifacts;
- the durable `lean-module-import-semantics-v4-30-0-rc2` result, which covers how resolved compiled modules become a Lean environment; and
- the published Lean server report, which covers worker/document lifecycle and stale-dependency notifications.

The focus here is the missing identity/invalidation link: how Lean decides that an already-computed environment-bearing snapshot remains reusable.

## Findings

### `Lean.Environment` is persistent state, not a content-addressed value

The kernel environment stores the constant map, module ownership metadata, extension state, and an `EnvironmentHeader`. Its source documentation says environments are never destructively updated. Adding a constant returns a new environment whose constant map contains the new entry.

The declaration map uses `SMap`, which separates imported constants from local constants. Its implementation notes that declarations are never removed from the environment. Imported entries can be built efficiently, while local entries use persistent map storage.

The elaboration-level `Lean.Environment` wraps kernel environments with additional state: public/private visibility views, a task for the fully checked kernel environment, asynchronously elaborated constants, realization contexts, and server-specific imported extension state.

This representation is well suited to passing successor environments through an ordered elaboration. It is not a serialized semantic digest. The environment includes opaque extension state and task-backed asynchronous state in addition to declarations.

Basis: **source**.

### The incremental processor explicitly lacks semantic environment change detection

`Lean.Language.Lean.process` states the governing rule directly:

> there is no cheap way to check whether the `Environment` is unchanged

The consequence follows immediately in the same source comment: semantic change detection is not currently possible, so the processor must stop passing previous states from the first syntactic change onward.

The broader incrementality documentation says the preferred design would use strong hashes over the full state and inputs. Instead, this revision relies on syntactic checks: if all syntax inspected up to a point is unchanged, Lean assumes that the corresponding old state can be reused.

`SnapshotBundle` likewise describes a one-element previous-history mechanism and says a future implementation may replace it with a global cache indexed by strong hashes.

These statements are stronger than merely failing to find an `envHash` API. The subsystem that would consume such an identity explicitly documents that it does not have one and that strong-hash reuse remains future work.

Basis: **source**.

### Unchanged syntax preserves the environment by reusing the old snapshot chain

The language processor creates a chain/tree of snapshots that contains command state, and `Command.State` contains the current `Environment`.

When a command's syntax remains unchanged, `parseCmd` can reuse the previous command processing result and then continue from the old result's `cmdState`. Thus the environment before the following command is not recomputed and compared; it is the state produced by the reused earlier snapshot.

This reuse is safe only because the processor preserves the invariant that the state at the beginning of reused elaboration is identical. Command elaboration's snapshot documentation records exactly that invariant.

At this revision, the identity proof is therefore *structural history plus syntax equality*, not `hash(environment)` equality.

Basis: **source**.

### The first relevant syntactic change cuts off later state reuse

The same processor applies a conservative invalidation boundary. After the first relevant syntactic difference, it passes `none` for subsequent old snapshots and resumes normal processing from the newly produced command state.

This matters even when two different edits would happen to produce semantically equivalent declarations. Lean does not attempt to prove that equivalence in order to retain downstream snapshots. A syntactic change is sufficient to lose the fast-forwarding reuse chain.

Nested elaborators can apply finer-grained reuse rules, but they inherit the same requirement: an old snapshot may be used only when the context/state at its start is known to be unchanged. The source repeatedly records this as an invariant for command, definition, and tactic snapshots.

For Anneal, source transformations that are semantics-preserving are therefore not automatically cache-preserving under Lean's own incremental protocol.

Basis: **source**.

### Header equality is the import-environment reuse gate inside a worker

Header processing has its own snapshot.

If the newly parsed header syntax is equal to the old header syntax modulo trailing trivia, the processor reuses the old import-processing task and its resulting command state. It does not rerun module resolution or import loading merely to validate that the environment still has the same semantics.

If the header changes, the old import-processing snapshot is discarded. Lean calls `setupImports`, then `Elab.processHeaderCore`, and constructs a fresh `Command.State` around the newly imported `headerEnv`.

This boundary is critical: within a live worker, an unchanged import header is enough for the language processor to retain the previously loaded imported environment. External dependency changes are handled outside this syntactic reuse mechanism.

Basis: **source**.

### Changed imported files do not mutate an open dependent's environment in place

Lean's server design makes the external dependency boundary explicit.

The server documentation says that if `B.lean` imports `A.lean`, editing `A` does not change the environment already being used by an open `B`. `B` can continue interacting with the old compiled contents. After `A` is saved, dependency refresh restarts the relevant worker and runs `lake setup-file` again so the dependent can rebuild/locate and reload its imports.

The watchdog also sends `$/lean/staleDependency` notifications to open dependents when a relevant `.lean` dependency changes.

This is not merely a user-interface choice. The server design notes that imported modules use compacted memory regions outside ordinary reference-counting GC. When imports change, safely freeing and replacing those regions in a live worker is difficult; restarting the per-file worker is deliberately simpler because its state must be recomputed anyway.

Thus dependency invalidation is a lifecycle event, not a semantic rehash of `Lean.Environment`.

Basis: **documentation** + **source**.

### Batch processing normally constructs a fresh imported environment instead of reusing one across processes

The normal frontend parses the file header, obtains its module setup, calls the import machinery, and creates the first `Command.State` from the resulting imported environment. It then processes the file's ordered commands, each of which advances that state.

The incremental `old?` snapshot parameter exists for long-lived/incremental processing. A fresh batch invocation has no previous snapshot chain to reuse.

This separates two questions that are easy to conflate:

- Lake may decide that previously compiled dependency artifacts are reusable.
- Lean still constructs an in-process environment by loading those selected artifacts for the current frontend/worker lifecycle.

An externally reusable `.olean` tree is therefore not itself a reusable `Lean.Environment` object.

Basis: **source** + **derived**.

### Hash tables and expression hashes are not environment identities

Lean uses hashing heavily inside an environment: declaration lookup uses hash maps, persistent extensions may use hashed collections, and meta-level caches use hashes of expressions/configuration keys.

Those hashes serve local data-structure and cache-key purposes. They do not provide a digest of the complete declaration and extension state.

At the pinned revision, `Lean.Environment` and `Kernel.Environment` do not derive or define the ordinary `Hashable`/equality interfaces in `Environment.lean`, and the language processor contains no `envHash`/`environmentHash` mechanism. More importantly, the incremental processor's explicit "no cheap way" statement shows that it does not have a semantic identity usable for its reuse decision.

Do not infer environment equivalence from a hash table's internal hash, a declaration name hash, a module index, or an object pointer.

Basis: **source** + **derived**.

### The environment's semantic inputs extend beyond its constant table

A cache key based only on declaration names or constant bodies would still be incomplete.

The environment includes persistent environment-extension state. Imported extension entries can influence elaboration through syntax, attributes, instances, simp lemmas, tactic registries, and other metaprogramming state. The import layer installs both constants and persistent extension entries.

The elaboration-level environment also has visibility distinctions and async state. In server mode it carries additional imported extension state for the server view.

Therefore a hypothetical Anneal environment fingerprint would need a declared semantic model of which environment components matter. Lean does not supply that complete fingerprint as a stable public contract at this revision.

Basis: **source** + **derived**.

### Anneal should key durable reuse from inputs that determine the environment, not from an inferred Lean environment hash

For a durable cache that survives processes or machines, the useful invariant is not "Lean says these environments have the same hash." Lean does not provide that contract here.

A stronger Anneal cache identity would need to determine, directly or transitively:

- the exact Lean/toolchain identity and relevant options;
- generated Lean source and module/header mode;
- the exact resolved compiled import artifacts;
- the transitive import graph and visibility/phase semantics;
- imported persistent extension state as determined by those artifacts; and
- any plugins or other setup inputs that can affect elaboration.

Lake's build graph may be a practical source of much of this identity, but Lake's non-cryptographic build hashes are not automatically a semantic proof of environment equivalence. The final Anneal cache contract must state which upstream identities it trusts and under what revalidation rule.

For a single long-lived Lean worker, the simpler safe option is to stay inside Lean's own snapshot lifecycle and obey its syntax/dependency invalidation boundaries.

Basis: **derived** from the source-level rules above.

## Boundaries

**No fresh execution.** This report did not run Lean, mutate a live language-server document, or instrument environment objects.

**No claim that Lean never hashes any environment-related component.** Lean hashes names, expressions, options, artifacts, and many cache keys. The narrower established claim is that the pinned incremental language processor has no cheap semantic `Environment` equality/hash used for reuse and instead documents syntax-based snapshot reuse.

**No byte-level `.olean` identity claim.** How `.olean` contents are serialized or whether two `.olean`s are byte/semantically equivalent is a separate inventory item.

**No complete Lake invalidation rule.** Lake decides whether dependency artifacts need rebuilding before Lean imports them. This report covers what Lean does with an already loaded environment and how it invalidates its own snapshot reuse.

**No proof that every environment extension affects Anneal.** The environment can contain arbitrary user/plugin extension state. Determining a minimal Anneal-specific semantic fingerprint would require a separately defined workload and trust boundary.

**No process-memory identity guarantee.** Pointer identity or persistent-object sharing can be useful for implementation-local caches, but this report does not characterize every such cache and does not treat address identity as portable semantic identity.

**Server dependency behavior assumes the pinned worker/watchdog architecture.** A future server could replace worker restart with a safe import-region replacement protocol; revalidate before relying on this lifecycle boundary.

## Evidence

All implementation source below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), inspected on 2026-09-26.

- `src/Lean/Environment.lean`
  - `Kernel.Environment`
  - `Lean.Environment`
  - `EnvironmentHeader`
  - persistent environment-extension machinery
  - Establishes persistent/non-destructive environment updates, constants/import metadata/extension state, and the asynchronous elaboration wrapper.
  - Role: **source**.

- `src/Lean/Data/SMap.lean`
  - `SMap`
  - Establishes imported-versus-local declaration storage and states that declarations are never removed from an environment.
  - Role: **source**.

- `src/Lean/Language/Basic.lean`
  - `SnapshotBundle`
  - Documents the one-version snapshot history and explicitly notes that a future implementation may use a global cache indexed by strong hashes.
  - Role: **source**.

- `src/Lean/Language/Lean.lean`
  - incrementality design notes
  - `process`
  - `parseHeader`
  - `processHeader`
  - `parseCmd`
  - States that there is no cheap way to check whether `Environment` is unchanged, describes strong full-state hashes as the ideal rather than current implementation, and implements syntax-based prefix reuse plus invalidation after the first change.
  - Role: **source**.

- `src/Lean/Elab/Command.lean`
  - `Command.State`
  - command snapshot context
  - Shows that command state carries the current `Environment` and records the invariant that reused elaboration begins from identical state.
  - Role: **source**.

- `src/Lean/Elab/Frontend.lean`
  - `IO.processCommandsIncrementally`
  - `runFrontend`
  - Shows the snapshot-aware frontend and the ordinary path that receives the final environment after processing.
  - Role: **source**.

- `src/Lean/Server/Watchdog.lean`
  - `notifyAboutStaleDependency`
  - dependent notification on changed `.lean` files
  - Shows the watchdog marking open dependents stale rather than replacing their environment in place.
  - Role: **source**.

- `src/Lean/Server/README.md`
  - "Recompilation of opened files"
  - "Worker architecture"
  - Explains the deliberate stale-dependent/restart design and the compacted-region lifetime reason for replacing workers when imports change.
  - Role: **documentation**.

The statements about Anneal cache identity are **derived** from these source-level boundaries. No fresh runtime evidence was collected.

## Revalidation

For a new Lean revision, first diff these exact seams:

1. `Lean.Language.SnapshotBundle` and its strong-hash note;
2. the incrementality notes in `Lean.Language.Lean.process`;
3. `parseHeader` and `parseCmd`, especially when they retain or drop `old?`;
4. `Command.State` and any new environment identity/version field;
5. `Lean.Environment` and `Kernel.Environment` for a new stable digest/equality API;
6. server stale-dependency handling and worker restart behavior; and
7. Lake's setup/import boundary if worker initialization changed.

A source change that introduces a strong full-state hash, environment version, or semantic fingerprint is a direct revalidation trigger.

On a Lean-capable surface, run a small three-module probe:

- `A` exports one declaration;
- `B` imports `A` and uses it;
- `C` imports `B`.

For an open `B` worker, record snapshot reuse and environment-visible declarations under these mutations:

1. edit only a command after an unchanged prefix in `B`;
2. make a semantics-preserving but syntactically different edit to an early command in `B`;
3. change only `B`'s import header;
4. change `A` without saving it;
5. save/rebuild `A` while `B` remains open;
6. refresh `B`'s dependencies/restart its worker.

The expected source-level model is:

- unchanged prefixes can reuse old state;
- the first syntax change cuts off later reuse even if semantically equivalent;
- a header change reruns import setup;
- an external dependency change does not silently replace `B`'s loaded environment;
- refresh/restart constructs a new imported environment.

Instrument the probe with module names, representative constant lookups, and one persistent environment-extension entry. Do not rely only on object addresses.

If Anneal later adds a durable prepared-environment cache, separately test its proposed key by changing exactly one determinant at a time: Lean revision, option, plugin, import artifact, transitive import, generated source, and environment-extension-producing declaration. The cache should miss whenever the promised semantic environment can change.
