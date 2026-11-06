# Findings

## The server is a watchdog plus one worker process per open file

Lean's server README describes a two-level process architecture. One watchdog process owns client communication and minimal persistent state. Each open Lean file gets its own worker process, and almost all elaboration, evaluation, completion, and proof-state work happens inside that worker.

The process boundary isolates file-local crashes and provides a simple way to discard imported-module compacted regions when a dependency environment changes. The watchdog retains the current text of open files because LSP clients normally send edits as diffs, so it can recreate a worker with the complete current document after a restart.

Basis: upstream **documentation** + **source**.

## Interactive requests target open documents, not arbitrary paths

The protocol overview states that Lean requires a file to receive `textDocument/didOpen` before the server will process requests or notifications for it. Requests for closed files are rejected. The watchdog returns a `contentModified` error when a request resolves to a file without a live worker.

For an agent service, a file URI is therefore not sufficient state. The service must manage the document lifecycle and keep the server's in-memory document contents synchronized with the version it intends to query.

Basis: **source**.

## Lean exposes both a plain goal request and the richer InfoView RPC path

The Lean-specific request `$/lean/plainGoal` takes `PlainGoalParams`, which extends the ordinary LSP document-and-position parameters. Its response is either null or a `PlainGoal` containing pretty-printed goal strings and rendered Markdown.

The InfoView path is richer. Lean registers `Lean.Widget.getInteractiveGoals` as a built-in RPC procedure taking the same `PlainGoalParams` and returning `Option InteractiveGoals`. The structured result contains an array of tactic goals. Each goal includes hypothesis bundles, the target as tagged interactive code, a reference to the elaboration context, the goal metavariable identity, and optional inserted/removed markers used for goal diffs.

Both interfaces call the same `FileWorker.getInteractiveGoals` implementation. Their difference is presentation and transport, not a separate proof-state semantics.

Basis: **source**.

## The structured query has an explicit two-step session protocol

The RPC transport is tunneled through Lean-specific JSON-RPC methods. A client first sends `$/lean/rpc/connect` with the open document URI. The worker creates an RPC session and returns a random `sessionId`.

The client then sends `$/lean/rpc/call` with the same document URI, an LSP position, the session ID, the fully qualified procedure name `Lean.Widget.getInteractiveGoals`, and JSON parameters encoding `PlainGoalParams`.

Lean's checked-in server test runner implements exactly this handshake. It lazily connects on the first RPC request, stores the session ID, constructs `RpcCallParams`, and calls `Lean.Widget.getInteractiveGoals` with the current URI and position.

This source client removes an important ambiguity: `getInteractiveGoals` is not itself a top-level LSP method. The top-level request is `$/lean/rpc/call`; the procedure name travels inside `RpcCallParams.method`.

Basis: **source** + checked-in client implementation.

## RPC sessions own server-side references and are deliberately disposable

InfoView responses can contain values that would be expensive or impossible to serialize directly, such as elaboration contexts. `WithRpcRef` turns such values into opaque client references backed by an `RpcObjectStore` in the worker. The store reference-counts live objects and can reuse a reference for the same server-side object so clients can preserve UI identity across requests.

A session is local to one worker. `RpcConnectParams` documents that sessions may be destroyed at any time, including after a crash, and that clients must discard old references and reconnect when they receive `RpcNeedsReconnect`. The worker generates random session IDs to avoid accidentally accepting stale references after restart.

At this revision a session expires 30 seconds after its last keep-alive. The protocol asks clients to send keep-alive notifications every 10 seconds. Release notifications decrement the reference counts for remote objects.

An agent integration should therefore treat session IDs and `RpcRef` values as ephemeral capabilities bound to a live worker, not durable identifiers that survive process replacement.

Basis: **source**.

## Goal lookup is driven by elaboration snapshots and InfoTrees

The worker incrementally processes the document into a tree of snapshots. Lean's server README explains that snapshots preserve processing data across edited versions and may contain nested snapshots for finer-grained incrementality. The `InfoTree` attached during elaboration contains data that cannot simply be reconstructed from final kernel declarations, including local/metavariable contexts and goal/subterm information.

`findGoalsAt?` starts from the parsed command snapshot covering the requested UTF-8 position, traverses nested elaboration snapshots whose syntax ranges cover that position, and asks the associated `InfoTree` for `goalsAt?`. It prefers a goal set whose syntax body directly covers the position, while accounting for trailing whitespace and indented tactic records.

This is why position queries can return an interactive proof state even though the final theorem environment contains no record of the user's intermediate tactic goals.

Basis: **source** + upstream **documentation**.

## The returned state can be the context before or after the tactic at the cursor

Each goal-selection result records whether the relevant state should be read before or after a tactic. `getInteractiveGoals` constructs the `ContextInfo` and metavariable context accordingly, then converts the selected metavariables into `InteractiveGoal` values. It also computes an optional goal diff against the after-state when possible.

The practical consequence is that "position" is interpreted through Lean's elaborated tactic ranges, not as a raw snapshot index chosen by the client. This is the behavior an InfoView user sees and the behavior an agent receives.

A consumer that needs a repeatable location should preserve the document version and LSP line/character position it queried. It should not infer that moving one character without changing the text must return a distinct state.

Basis: **source**.

## Edits invalidate old requests and reprocess the document incrementally

On `textDocument/didChange`, the watchdog updates its copy of the full document and forwards the change to the current file worker. The worker folds the changes into its text, creates a new document version, invokes its language processor for the new input, replaces the active snapshot/reporting state, and cancels pending requests from the older version.

The worker source explains the intended race behavior: a request may be traversing asynchronous elaboration tasks when an edit invalidates one of them. In that case the request gets a content-changed error rather than an answer silently assembled from stale processing state.

This is a useful fail-closed property for an agent loop. The client should retry against the new version instead of treating an invalidated proof-state response as current.

Basis: **source**.

## Lean provides an explicit synchronization barrier for automation clients

Elaboration and diagnostics are asynchronous and incremental. `textDocument/waitForDiagnostics` exists specifically for synchronization in tests and external tools. Its parameter includes a URI and document version; the response is delayed until diagnostics for at least that version have been emitted.

Lean's server test runner uses synchronization before later edit/query operations. The goal request itself can wait on relevant snapshot tasks, but an external client that wants a deterministic "edit, finish processing, then inspect" loop has a first-party barrier rather than needing to infer quiescence from sleeps.

There is a second test-oriented barrier, `$/lean/waitForILeans`, for waiting until project `.ilean` information and the current file's `.ilean` state are loaded. That is useful for reference/index tests but is not required merely to read a tactic goal in the current open file.

Basis: **source**.

## Saving a dependency marks open dependents stale instead of silently changing their environment

The watchdog tracks import relationships. When an open file is saved, `handleDidSave` finds open workers that depend on it and sends them `$/lean/staleDependency`. The dependent worker publishes a sticky diagnostic saying that its imports are out of date and should be rebuilt with the editor's "Restart File" action.

The server README describes the same model: an open dependent can continue using the previously compiled version of an imported module until its worker is explicitly refreshed; refresh uses `lake setup-file` to rebuild and locate dependencies.

Updating a generated Anneal Lean dependency does not, by itself, establish that every already-open proof worker is now elaborating against the new dependency. An integration must decide when to restart or otherwise refresh affected workers.

Basis: **source** + upstream **documentation**.

## Worker restart invalidates interactive state but preserves enough watchdog state to reconstruct it

A file worker can be terminated because of a crash, dependency refresh, or close. The watchdog retains the current document text and can start a replacement worker. The replacement receives initialization followed by a fresh `didOpen` carrying the complete current document.

The old RPC session does not survive that transition. Release notifications for an old session are explicitly ignored, while calls with an unknown session produce `RpcNeedsReconnect`.

For an agent-oriented service, recovery can therefore be deterministic at the protocol level: reconstruct the worker from the authoritative document, wait for processing, reconnect RPC, and query the desired position again. Whether the reconstructed proof state is byte-for-byte identical across all environmental changes is a stronger determinism question not established here.

Basis: **source**.

## The language server is directly usable as an external process

Lean's Lake configuration source identifies the language-server executable form as `lean --server`, and `lake serve` launches that server with package/server options. The server protocol is ordinary JSON-RPC/LSP plus documented Lean-specific methods.

This gives an external service two separable integration layers: Lake/toolchain preparation determines which `lean --server` process and dependency environment to launch, while the server protocol manages open documents, incremental edits, diagnostics, RPC sessions, and tactic-state queries.

This report establishes the second layer. It does not establish which Lake preparation is sufficient for an Anneal-generated project.

Basis: **source**.

## Existing server APIs are enough for an MCP bridge to expose tactic-state lookup without embedding Lean

The existing protocol already has the required request boundaries: document identity, document version updates, source position, synchronization, structured goal lookup, cancellation, reconnect, and server-side opaque references.

A thin MCP service could therefore own a Lean server process and translate an agent request such as "show goals at this generated Lean position" into the existing LSP/RPC sequence. The MCP layer would still need its own resource identity, concurrency policy, workspace/process ownership, and error schema, but it would not need to reimplement Lean elaboration or tactic-state extraction.

This is a **derived** architectural capability, not fresh evidence that any particular MCP implementation works. The exact process lifecycle, workspace isolation, and cross-layer Rust-to-Lean source mapping remain separate design and validation problems.

Basis: **derived** from the pinned server protocol and source.
