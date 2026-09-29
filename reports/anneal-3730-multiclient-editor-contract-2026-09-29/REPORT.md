# Two logical clients over one Lean document authority

## Summary

A direct Lean 4.30.0-rc2 server answered two separately correlated local-client goal requests for the same unsaved projected document, while a small broker model kept one Rust-host source buffer authoritative. Its editor and agent roles alternated version-checked edits and queries; stale edits conflicted, an identical retry did not repeat a mutation, a reused request ID with changed payload conflicted, and polling repaired a deliberately dropped local notification. An unchanged disk mirror still contained an invalid proof while the open Lean document initially reported `no goals`. After edits, the direct Lean goal changed `no goals → ⊢ False → no goals → ⊢ False` as the authoritative buffer changed.

The server was genuine Lean; the Rust `//%` projection, editor/agent roles, subscriptions, access control, and retry store were local Python prototype code. There was **one** LSP stdio client connection and **no actual MCP server, MCP transport, editor extension, rust-analyzer, or Anneal integration**. A separate tactic-gated direct Lean cancellation returned JSON-RPC `-32800` in both retained runs. The report gives the exact integration work left for #3731 I057–I072, I152, and I155–I157.

## Applicability

The binary was `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, run as direct `lean --server` with `LEAN_NUM_THREADS=1` on macOS arm64. A fresh Lean batch `--json` invocation used the fixture's disk mirror. No Lake project, generated Aeneas model, plugin, Rust compiler, or server setup operation participated. CPython 3.14.7 and its standard library implemented the local broker and LSP framing; all disposable files were under the conversation-owned Meta/Data scratch root.

The invented `//% ` line prefix copies a Rust-host comment payload into an unsaved hidden `Hidden.lean` document. It is **not** Anneal's chosen annotation grammar. `Host.rs` and `Hidden.lean` begin on disk with `theorem demo : False := by exact ?_`; the broker opens the hidden URI with unsaved `theorem demo : True := by trivial`. The text has no imports, so this probes document ownership and protocol correlation, not environment freshness. Logical `editor` and `agent` clients are Python identities sharing one broker object; they are not two independent OS processes or MCP connections.

The normative comparison uses [LSP 3.18 `didOpen`/`didChange`](https://github.com/microsoft/language-server-protocol/blob/de9a671ae6ba374cc748a29c1c620cbc536302ff/_specifications/lsp/3.18/textDocument/didChange.md) and MCP [2026-07-28 subscriptions](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/patterns/subscriptions.mdx) and [cancellation](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/patterns/cancellation.mdx). Those protocol sources were inspected at their pinned commits. The fixture's `subscribe` and `negotiate` functions are intentionally **MCP-shaped only**; they do not send conforming `subscriptions/listen` or `tools/call` messages. The earlier `anneal-3730-editor-mcp-shadow-authority-v4-30-0-rc2` report found no local Anneal MCP/LSP bridge in the selected `anneal/src` source tree and delimits that availability claim.

## Findings

### One authoritative unsaved source can serve both logical clients

The disk `Hidden.lean` compiled with fresh `lean --json` exited 1. The direct Lean server opened the same file URI with projection of the unsaved good Rust-host buffer at LSP version 1 and returned `no goals`. The disk hidden-file and host-file SHA-256 values stayed at their bad-source values until the broker later saved the host. Two goal requests with distinct LSP wire IDs 80 and 81, representing editor and agent local request ID 1, returned equal goal results. This is **Lean execution** for one open document plus **prototype execution** for the broker's two-client correlation; it does not prove two real clients can independently attach to Lean's one stdio session.

The editor changed the host to the bad text at application version 2; the broker derived the hidden text and sent one `didChange` to Lean. After `waitForDiagnostics`, the agent query returned `⊢ False`. The agent later applied a fresh, authorized version-3 edit restoring good text, and the editor query returned `no goals`. The editor then restored bad text at version 4 and the goal returned `⊢ False` again. Both retained runs made these classifications. The model records full source and projection hashes, application version, host document epoch, Lean document version, and server incarnation separately. A false theorem goal is a Lean local tactic state, not a Rust-level verification status.

### Stale edits, lost responses, and version reset have different guards

After the editor's version-2 change, the agent's edit based on version 1 and its old source hash returned `conflict` without a Lean `didChange`. The fixture then modeled a lost response to the editor's successful mutation: retrying the same `(client, request ID, request payload)` returned the original applied result at version 2 and did not increment the version. Reusing that ID with a different payload returned `id-reuse-conflict`. A new agent request under current preconditions applied version 3. These are **local adapter** behaviors, not MCP protocol guarantees or Anneal behavior. The dedup table is in memory and has no expiry/restart persistence policy.

After a forced Lean server kill, the broker preserved the application source at version 4, launched a new Lean server, reopened the hidden file at **LSP version 1**, and again observed `⊢ False`. The response envelope kept application version 4 and changed server incarnation from 1 to 2. The broker subsequently saved and renamed the host to `Renamed.rs`, closed old hidden URI, opened `RenamedHidden.lean` with the same unsaved projected text, and obtained `⊢ False`. That new hidden file had no physical disk file. Closing the host made the broker reject further queries as `closed`; reopening from saved disk gave the bad goal. Finally, closing and reopening the same bad text again reset the application document version to 1; a precondition from the previous open incarnation (same source hash and version) was rejected because `document_epoch` changed. The new epoch guard is a **prototype design rule**; the Lean server itself did not validate it.

### Notifications are hints; the local current-state read repairs one missed event

The local editor role advertised a subscription capability and accepted a prototype `generation-changed` stream. The local agent role declined subscriptions and used polling. The harness deliberately dropped the editor's version-2 event after delivering version 1. Its last received event still reported version 1, while a broker current-state read reported version 2 and the bad-source hash. A client that only retained the stream would have stale state in this fixture. Reconciliation by polling repaired it. This is **local model execution**, not a delivered MCP stream, network loss, or Lean diagnostic subscription.

The raw direct Lean transcript also contains versioned `textDocument/publishDiagnostics` messages for the hidden document as proof text changes. The broker does not yet multiplex those messages with rustc/Charon/Aeneas diagnostics or implement pull diagnostics; the local subscription stream carries its own generation events. The MCP `2026-07-28` specification permits a client to request and receive an acknowledged subset of subscription classes; reconnection requires a new subscription, and a resource update notification alone is not a durable current proof state. The application therefore needs a current-state read with its own source/model/version envelope if it uses subscriptions. Basis: **normative** MCP text plus **derived** contract and the local dropped-event control.

### Direct Lean cancellation and capability response stay separate from broker promises

A second direct `lean --server` instance elaborated a tactic paused on a file gate. The client sent `$/lean/plainGoal` request ID 201, immediately sent `$/cancelRequest` for 201, and released the tactic gate. The request returned JSON-RPC error code `-32800` in both runs. This is a direct Lean/LSP cancellation observation in this schedule. It does not establish that a prior result was rolled back, that Lean descendants were killed, or that an MCP cancellation request propagates to the correct Lean request. The broker model does not connect its local logical cancellation to this LSP test.

The first direct server was initialized with offered `utf-16`, and a separate server was initialized with only `utf-8`. Both responses omitted an explicit `positionEncoding` field, and a simple ASCII proof returned `no goals` under the latter. ASCII positions cannot distinguish UTF-8 from UTF-16; no negotiated-encoding correctness conclusion follows. The fixture used full-document `didChange` only. It did not test Unicode positions, incremental ranges, unsupported feature negotiation, or representative real editors.

### Exact #3731 residuals

| ID | New evidence | Remaining requested experiment |
| --- | --- | --- |
| I057 | One local broker routes two roles to direct Lean. | Actual editor extension/LSP proxy/separate Rust and Lean servers; completion, hover, diagnostics, and cancellation inside/outside annotations. |
| I058 | Lean's versioned diagnostic messages are retained; one local generation event is dropped and repaired. | Origin-scoped rustc/Charon/Aeneas/Lean push/pull merge, clears, rename, and supersession. |
| I059 | No new navigation/token execution. | Map definitions/references/semantic tokens and approximate imported-model origins to Rust/read-only views. |
| I060 | Hidden URI rename only; no LSP rename/workspace edit. | Cross-file helper rename, resource operations, atomic preconditions, and generated/ambiguous edit rejection. |
| I061 | Plain goals survive broker restart/rename. | InfoView RPC objects, widgets, hyperlinks, projected Rust positions, reconnect and rich-UI comparison. |
| I062 | UTF-16 and UTF-8-only initialize offers, full-document changes, version reset recorded. | Non-ASCII position semantics, actual negotiated encodings, incremental sync, and feature fallback across clients. |
| I063 | One local save/rename/close path. | Autosave/formatter/watcher/background-build loops and dirty-buffer/duplicate-work controls in a real editor. |
| I064 | Lean server killed and unsaved broker source replayed. | Actual editor disconnect while service remains live, divergent buffer/disk handoff, ownership transfer. |
| I065 | Version-labeled local capability descriptors and fallback. | Real MCP revision/client handshake, long-running handles, progress, cancellation, retrieval, and compatibility. |
| I066 | Local goal, poll, CAS edit calls use source/version/epoch. | Actual typed tool surface over subject/obligation IDs, diagnostics, context, verification, and minimality measurement. |
| I067 | Lost-response identical retry and changed-payload ID conflict; stale CAS rejection. | MCP transport loss/retry, worker-create/check-start idempotency, persistent bounded dedup expiry. |
| I068 | Editor and agent alternate reads/edits against one unsaved buffer. | Independent MCP/editor clients sharing real Rust-hosted authority and generated model across reconnect. |
| I069 | Only local editor/agent edit policy. | Separate query/edit/import/build permissions and cross-workspace/path containment controls. |
| I070 | No scratch fork in this package. | Multiple tactic attempts in isolated real context and candidate application with statement/assumption/obligation controls. |
| I071 | Direct Lean cancellation only; local missed event/retry model. | Actual MCP long jobs, slow clients, stream backpressure, cancellation, reconnect/result expiry and worker cleanup. |
| I072 | No installed Lean MCP adapter executed. | Representative adapters under unsaved projection, replaced import, scratch, and simultaneous editor access. |
| I152 | Local subscription-vs-poll and drop control. | Actual MCP `subscriptions/listen`, capability acknowledgment, delayed/dropped delivery, reconnect and result retrieval. |
| I155 | Invented Rust-host projection; hidden file stays stale; open/change/save/rename/close/restart. | Real Anneal parser and editor host, Lake `setup-file`, generated imports, custom URI/model regeneration, hidden-worker cleanup. |
| I156 | Local descriptor for subscription/poll/edit and unsupported subscription fallback. | Versioned Charon/Aeneas/Lean capability descriptors tested against actual backend behavior and unsupported operations. |
| I157 | Local repeated live driver and one disk batch control. | One structured Anneal engine behind real batch/live shells, current CLI comparison, model changes, cancel/reconstruction and fresh exact-input oracle. |

Each row remains partial or unexecuted at its full issue scope. The user's requested integrated editor/MCP behavior cannot be inferred from the success of one direct Lean stdio connection and a Python broker.

## Boundaries

- The invented `//% ` annotation parser and one-core-theorem projection are not Anneal. The direct Lean server imports no generated model; source-to-obligation attachment, proof adequacy, and Rust-level coverage are untested.
- The two logical clients are method calls in one Python process. There is no actual MCP transport, resource subscription, JSON-RPC MCP request, browser/editor client, two-process race, or cross-repository access test.
- The broker keeps deduplication and source ownership only in memory. Restarting Lean preserves the broker; restarting the broker or reconnecting a real editor/MCP client was not tested.
- The `-32800` result is one gated request schedule repeated twice. It does not generalize to cancellation of every elaboration phase, process cleanup, or MCP cancellation propagation.
- The missing explicit `positionEncoding` field under a UTF-8-only offer is a recorded response, not a proof of incorrect coordinates. The specimen is ASCII and cannot discriminate encodings.
- The local subscription event is application-defined. It does not satisfy MCP `subscriptions/listen` filters/acknowledgment/stream correlation or LSP diagnostics lifecycle.
- The broker's source hash, version, and document epoch checks prevent the seeded stale and same-text reopen edits in this fixture. They do not establish a minimal sufficient identity tuple, durable replay, multi-document atomicity, or malicious-client isolation.

## Evidence

- `support/probe.py`, SHA-256 `f222d8e7397bc9ffadeeaab10924aeadc3da55546ac770d2b78321dc67e17e75`, preserves the complete fake Rust projection/broker and direct LSP framing, gate control, and assertions. `support/transcript-run1.json` and `support/transcript-run2.json`, SHA-256 `0dfa65ce0ca0d1a6782e1606a772303230d191492bf1bad7c4bd6d3a505b33ad` and `a1577e95c386df68730026e80a7b106322fac279c079d7c960e8660cfb2b85a4`, retain full normalized LSP messages, local broker events, hashes, diagnostics, cancellations, capability responses, and process incarnations. Absolute temporary/tool paths were replaced with `$WORK`/`$LEAN_BIN`. Both runs agreed on all classifications above. Basis: **execution** for Lean messages and **prototype execution** for local broker behavior.
- The pinned [MCP subscriptions](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/patterns/subscriptions.mdx), [MCP cancellation](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/patterns/cancellation.mdx), and [LSP change](https://github.com/microsoft/language-server-protocol/blob/de9a671ae6ba374cc748a29c1c620cbc536302ff/_specifications/lsp/3.18/textDocument/didChange.md) sources define protocol behavior independent of this model. Basis: **normative** specification where stated.
- `anneal-3730-editor-mcp-shadow-authority-v4-30-0-rc2/REPORT.md` records earlier direct two-document Lean shadow/replay and pinned protocol research; `anneal-3730-lean-protocol-races-v4-30-0-rc2/REPORT.md` records a different direct version/cancellation race. Their boundaries remain in force.
- [Issue #3731](https://github.com/google/zerocopy/issues/3731) supplies the exact requested agenda. This report does not edit its status or claim those investigations complete.

## Revalidation

Set `LEAN_BIN` to the selected pinned Lean executable and `ANNEAL_PROBE_SCRATCH` to an existing owned scratch directory, then run `python3 support/probe.py` from this package. It writes `support/results.json`; compare the source/projection hashes, good/bad/good/bad goal sequence, two wire request IDs, stale/idempotent/ID-reuse/same-text-reopen edit outcomes, dropped-event repair, restart/rename/reopen lifecycle, and cancellation code with the retained transcripts. PIDs and notification timing can change. For an actual Anneal integration, replace the local broker with its real editor and MCP adapters, preserve captured source/model/import identities, and rerun with independent clients, Unicode coordinates, generated imports, real diagnostics origins, and fresh batch verification.
