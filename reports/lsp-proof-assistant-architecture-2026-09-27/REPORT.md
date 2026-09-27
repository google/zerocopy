# LSP architecture for stateful proof-assistant integrations

## Summary

The Language Server Protocol is a client/server synchronization protocol, not a proof-session model. The client and server negotiate capabilities at `initialize`; open documents become client-owned text snapshots; edits advance a versioned document state through `textDocument/didChange`; ordinary requests are correlated by JSON-RPC request IDs; and cancellation is best effort. LSP does not prescribe a language server's process topology, persistent state layout, workspace implementation, or a universal "this document version is fully elaborated" barrier.

For a proof assistant, the durable semantic identity therefore has to be richer than an LSP request ID. A reliable interactive query needs at least the project environment, document URI, client-known document version, source position, and an implementation-specific indication that the relevant semantic state has caught up. If a server restarts, the client must be prepared to reconstruct protocol state rather than treating the old process as the proof session.

Lean `v4.30.0-rc2` makes these boundaries concrete. One watchdog process fronts one worker process per open file. The watchdog retains the current text of open documents so a crashed worker can be recreated; each worker receives one full `didOpen`, then subsequent changes. Inside a worker, Lean incrementally reuses parser/elaborator snapshots across edits. A new edit cancels pending requests tied to the old document state. The implementation also deliberately isolates imported-module state: editing an open dependency does not automatically re-elaborate open dependents against the unsaved text.

This architecture is suitable for an agent-facing proof service, but only if the wrapper preserves the underlying state boundaries instead of presenting LSP as a stateless "query goals at byte offset" API. In particular, generated files that are open in LSP are governed by the client's in-memory text, not by whatever bytes later appear at the same filesystem path.

Basis: normative LSP specification + pinned Lean source + derived proof-assistant implications.

## Applicability

The protocol findings apply to the LSP 3.18 specification source in `microsoft/language-server-protocol@de9a671ae6ba374cc748a29c1c620cbc536302ff`. Microsoft's LSP landing page identified 3.18 as the latest released specification when observed on 2026-09-27; the repository already also contained later-development material, so this report binds its claims specifically to the 3.18 files rather than to repository `main` in general.

The concrete implementation findings apply to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, release `v4.30.0-rc2`, which is the Lean release selected by the current Anneal/Aeneas toolchain at the time of observation.

The report is about the protocol and server-state architecture that matters to interactive proof tooling: initialization, workspace coordinates, open-document ownership, edits and versions, request/notification identity, cancellation, worker lifetime, incremental semantic state, and restart/reconstruction. It does not duplicate the corpus's detailed report on Lean tactic-state lookup, its separate report on Lean multi-workspace isolation, or the MCP architecture report.

No LSP or Lean process was executed. Established behavior comes from the exact specification and source revisions named above. Statements about how an agent-facing service should carry state are derived architectural consequences, not upstream requirements.

## Findings

### LSP standardizes messages and synchronization, not server internals

LSP messages use JSON-RPC. A request has an `id` and requires a response; a notification has no response. These identifiers correlate one in-flight operation. They are not persistent document, workspace, proof, or process identities.

The initialization handshake carries client capabilities and workspace coordinates. `InitializeParams` includes a client `processId`, deprecated `rootUri`, and optional `workspaceFolders`. The workspace-folder protocol can describe multiple roots when both sides support it. None of these fields requires a particular server process topology or state-store architecture.

Basis: normative LSP source.

For proof-assistant integration, this means a language server can be one process, a process tree, a remote service, or something else without changing the LSP surface. Process identity is therefore not a portable semantic key. A wrapper should name its logical project/document state explicitly rather than assuming that "same LSP connection" means "same proof session."

Basis: derived.

### An open document is an in-memory client-owned snapshot

`textDocument/didOpen` transfers content management to the client for that URI. While the document is open, the LSP specification says the server must not obtain the document's content by rereading the URI. Opening is therefore a synchronization concept, not merely an editor-visibility event.

`textDocument/didChange` is permitted only after the client has claimed the content with `didOpen`. Its `VersionedTextDocumentIdentifier` names the version *after* all changes in that notification are applied, and multiple changes in one notification are applied in order. The specification explicitly requires a client to synchronize document state before requesting information if it wants reliable results.

`textDocument/didClose` ends client content ownership. After close, the master content is again where the URI points, such as the filesystem for a file URI.

Basis: normative LSP source.

This boundary is especially important for generated proof files. Replacing `Foo.lean` on disk does not by itself replace the semantic input of an already-open `Foo.lean`. The client must reflect the new generated bytes through the document synchronization protocol, or close/reopen as appropriate. A service that regenerates a file behind an LSP client's back can otherwise query a semantic state for bytes different from the current filesystem bytes.

Basis: derived directly from open/close ownership semantics.

### Document version and request ID solve different problems

An LSP request ID correlates one request with one response. A document version orders client-managed text snapshots. The two identifiers have different lifetimes and must not be conflated.

Most language-feature requests address a document and position rather than carrying the client's expected document version as a universal optimistic-concurrency token. The protocol instead places the burden on the client to synchronize changes before sending a query. Consequently, LSP by itself does not give a generic proof service a response-level assertion that "this answer was computed from document version N."

Basis: normative document-synchronization rules + derived distinction.

A proof-assistant wrapper that requires reproducible tactic-state queries should maintain its own expected document generation and use whatever server-specific completion/barrier mechanism exists before accepting an answer. This is an application protocol concern layered over LSP.

Basis: derived.

### Cancellation is advisory at the protocol layer

LSP cancellation is sent as the `$/cancelRequest` notification carrying the request ID. The specification classifies `$/` messages as implementation-dependent and explicitly permits a receiver to ignore such notifications where it cannot meaningfully react. Cancellation therefore cannot be treated as a transaction rollback or as proof that the underlying computation stopped before observing or producing state.

Basis: normative LSP source.

For proof tooling, cancellation should be used to reduce obsolete work, not to establish semantic isolation. Correctness after an edit still needs version/state validation even if the client canceled an earlier request.

Basis: derived.

### Lean uses a watchdog plus one worker process per open file

At the pinned Lean revision, the main language-server process is a watchdog. `textDocument/didOpen` causes it to launch a file worker, record watchdog state, and start asynchronous worker communication. `didChange` first updates the watchdog's retained document state and then forwards the change. `didClose` shuts down the file worker and removes the state.

The watchdog-to-worker protocol is LSP-shaped but intentionally narrower than an ordinary client/server session. A new worker receives `initialize` and then a single full `didOpen` containing the current URI, version, and text. Workers do not receive another `didOpen`; subsequent edits arrive as `didChange`. When a worker crashes, the watchdog restarts it only when a later `didChange` arrives, using the retained current document to reconstruct the worker.

Basis: pinned Lean source.

The design gives Lean strong per-file failure isolation. A metaprogram or evaluation in one file can crash that worker without necessarily taking down the whole server. It also means that a worker process is disposable implementation state: the watchdog's retained document snapshot is the recovery source of truth for that worker.

Basis: pinned Lean documentation + source.

### Lean's semantic state is an incremental snapshot tree

The pinned server documentation describes snapshots as the mechanism for saving and reusing processing state between versions of an open file. Lean's language processor reuses parsing and elaboration state where possible and reprocesses from the affected region downward. The implementation records command-level and nested snapshots so semantic requests can wait for and inspect the relevant elaborated state.

On `didChange`, the file worker constructs the new document/version and cancels all pending requests through a distinct "cancelled by edit" path. The worker also supports explicit `$/cancelRequest`, tracked separately. The implementation documentation explains why: a request waiting on an elaboration task invalidated by an earlier edit must not quietly return an answer from the obsolete computation.

Basis: pinned Lean source.

This is stronger than generic LSP cancellation. In this Lean version, edits are part of the semantic invalidation mechanism. An agent-facing bridge should preserve that property rather than caching a goal response independently of the document generation that produced it.

Basis: derived from pinned Lean behavior.

### Incremental reuse is local to what Lean can prove reusable

Lean's incremental parser/elaborator does not simply reuse "everything before the byte offset." The source notes that grammar effects can invalidate syntax earlier than a naive edit boundary and that elaboration reuse depends on snapshot/syntax comparisons. The implementation can also wait on still-running prior snapshot tasks when reuse is valid and cancel subtrees ruled out for reuse.

Basis: pinned Lean source.

For an external service, the safe abstraction is therefore "Lean owns incremental reuse" rather than exposing its cache as if document offsets were independent proof-state checkpoints. A bridge can request semantic state at a position, but it should not invent a stronger reuse contract than the server provides.

Basis: derived.

### Open-file edits and imported-module state are different invalidation domains

Lean's server documentation distinguishes edits to the currently open file from changes to its imported modules. Each open file is elaborated incrementally from its in-memory content. By contrast, imports are backed by compiled artifacts. Editing an open dependency does not immediately cause another open dependent to re-elaborate against the unsaved dependency text. Saving an imported file marks dependents stale, and refreshing/restarting their workers is the mechanism that moves them to rebuilt dependency state.

Basis: pinned Lean server documentation.

This matters for a proof service that manages generated modules. A "document version" is not sufficient to identify the complete semantic environment if imported artifacts can change. The project/dependency generation must also be part of the service's notion of a valid proof snapshot, or the service must restart/reprepare when that environment changes.

Basis: derived.

### A protocol wrapper needs an explicit reconstruction story

LSP defines initialization, document synchronization, requests, and shutdown behavior, but not durable recovery of a logical proof session after server-process loss. Lean's watchdog reconstructs individual workers because it retains each open document's current state. A loss of the outer server requires a client to establish a new protocol session and replay the state it needs.

Basis: normative LSP lifecycle model + pinned Lean worker-restart design + derived synthesis.

For an agent-facing proof service, a robust model is therefore:

1. identify a prepared project environment;
2. identify each open document by URI and monotonic client generation;
3. synchronize the exact text through LSP;
4. wait for an implementation-specific semantic barrier when a stable answer is required;
5. issue semantic queries against that synchronized state;
6. invalidate or reject answers when document or dependency generation changes; and
7. be able to reconstruct the state after a process restart from durable project/document inputs.

This model follows the protocol boundaries without making process lifetime part of the logical proof identity.

## Boundaries

- **Not examined:** fresh wire behavior, latency, throughput, memory growth, cancellation timing, and crash behavior under execution. The report is source/specification based.
- **Not examined:** exact Lean tactic-state response structures and lookup rules. `reports/lean-server-tactic-state-v4-30-0-rc2` covers that subject.
- **Not examined:** whether multiple independent Lake workspaces can share one Lean server process. `reports/lean-server-multi-workspace-isolation-v4-30-0-rc2` covers that boundary for this Lean revision.
- **Not examined:** MCP hosting/session semantics. `reports/mcp-proof-assistant-architecture-2026-07-28` covers the current MCP protocol separately.
- **Unknown from LSP alone:** a universal "fully processed document version" barrier. LSP document synchronization orders text state, but proof-assistant readiness is implementation-specific.
- **Known not to apply:** filesystem replacement is not an implicit content update for an open LSP document; open document content is client-managed until close.
- **Known not to apply:** request cancellation is not a rollback or exactly-once mechanism.
- **Known not to apply:** an LSP request ID is not a persistent proof-session or document-version identity.

## Evidence

### LSP 3.18 specification

Repository: `microsoft/language-server-protocol`
Revision: `de9a671ae6ba374cc748a29c1c620cbc536302ff`

- `_specifications/lsp/3.18/specification.md`, blob `2c33357fc28b47a7090655cc93b227968c459b4a`: JSON-RPC request/notification distinction and `$/cancelRequest` semantics.
- `_specifications/lsp/3.18/general/initialize.md`, blob `177eb366b7e7769527007cbd652b6372a03aa789`: `processId`, client capabilities, `rootUri`, and `workspaceFolders` initialization state.
- `_specifications/lsp/3.18/textDocument/didOpen.md`, blob `f2bc2141ca7b4efdc1521493470cc631cf083d99`: client ownership of open-document text and prohibition on rereading the URI for its content.
- `_specifications/lsp/3.18/textDocument/didChange.md`, blob `81e7475181818d44229c10dbcc25de7f3de83c69`: open-before-change rule, synchronization-before-query rule, post-change document version, and ordered content changes.
- `_specifications/lsp/3.18/textDocument/didClose.md`, blob `e8c956a6402a8a7ff031839fa58fba5d39c11f6d`: return of content mastery to the URI after close.
- `_specifications/lsp/3.18/workspace/workspaceFolders.md`, blob `005d024417ed5bed246f9ee4a0fe5fdf67f7d414`: multi-root workspace coordinates and capability-dependent workspace-folder support.

Evidence role: **normative** specification source. Microsoft's public LSP landing page was also checked on 2026-09-27 and identified 3.18 as the latest released specification; that observation is descriptive **documentation**, not an immutable protocol identity.

### Lean v4.30.0-rc2

Repository: `leanprover/lean4`
Revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`

- `src/Lean/Server/Watchdog.lean`, blob `68ed22f9178c9ae917c595c364d23df902d9478f`: watchdog/file-worker topology, `didOpen`/`didChange`/`didClose` routing, retained file state, worker restart, and cancellation forwarding.
- `src/Lean/Server/FileWorker.lean`, blob `c803034ed8810f13a5ef38a603a21e610efca2bc`: worker initialization, edit handling, edit-driven cancellation, explicit cancellation, and incremental request invalidation.
- `src/Lean/Server/ProtocolOverview.lean`, blob `4f493fc900319113e00a0a9c0f5eac4c3e5bb8e5`: pinned server protocol inventory and Lean's requirement that target documents be opened first.
- `src/Lean/Server/RequestCancellation.lean`, blob `7d310d0cd941641334a799828d4746c08e6a89d1`: distinct cancellation tokens for explicit request cancellation and edit invalidation.
- `src/Lean/Language/Lean.lean`, blob `124d4739bc910eb30ec35844348c785bf9f6c70a`: incremental parsing/elaboration design, snapshot reuse, and invalidation boundaries.
- `src/Lean/Server/README.md`: server topology, worker isolation, imported-module refresh model, and snapshot-tree architecture. The exact blob is recorded in `source-map.json`.

Evidence role: pinned **source** and upstream **documentation** embedded in the source tree. No fresh **execution** evidence was gathered.

### Existing corpus overlap

The current `google/zerocopy` `reference` corpus was checked before drafting. `reports/lean-server-tactic-state-v4-30-0-rc2` already covers goal-at-position RPC semantics and version-sensitive tactic-state queries. `reports/lean-server-multi-workspace-isolation-v4-30-0-rc2` covers Lean-specific project/workspace isolation. `reports/mcp-proof-assistant-architecture-2026-07-28` covers MCP state and lifecycle. This report keeps the generic LSP synchronization model and its concrete Lean process/invalidation realization separate from those subjects.

Evidence role: corpus-navigation **derived** overlap assessment, not upstream authority.

## Revalidation

For a future LSP revision, the cheapest protocol revalidation is to diff the exact sections governing `initialize`, `didOpen`, `didChange`, `didClose`, workspace folders, request/notification identity, and `$/cancelRequest`. The key discriminators are: who owns open-document text, whether change versions remain post-change identifiers, whether synchronization-before-query is still required, whether cancellation remains advisory, and whether a standard semantic-ready/version barrier has been added.

For a future Lean revision, first diff `Watchdog.lean`, `FileWorker.lean`, `RequestCancellation.lean`, `Server/README.md`, and the incremental-language processor. Recheck whether the server still uses one watchdog plus per-file workers, whether the watchdog retains complete open-document text for restart, whether edits cancel old-version requests, and whether incremental snapshots remain the semantic reuse unit.

A narrow execution probe can then validate the architecture without a broad benchmark: open a file, issue a semantic request, edit before completion, confirm the obsolete request's disposition, wait for the new version, query again, kill/restart one file worker if the harness permits, and verify that the reconstructed worker sees the latest synchronized text. A separate generated-file probe should overwrite the filesystem path of an already-open document and confirm that the server continues to use the client-managed in-memory text until the client synchronizes or reopens it.