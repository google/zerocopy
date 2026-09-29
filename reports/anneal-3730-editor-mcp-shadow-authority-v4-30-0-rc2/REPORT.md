# Editor-owned Lean documents and MCP reconciliation boundary

## Summary

A direct Lean 4.30.0-rc2 LSP server elaborated unsaved `didOpen`/`didChange` text while the same file URI's disk bytes remained stale. Closing and reopening from disk changed the goal back to the disk version; replaying the unsaved text after a forced server restart restored the prior goal. Two open documents kept separate diagnostics and versions. The bare direct server also accepted an open `file:` URI with no physical file and an `untitled:` URI for a small core proof.

The examined Anneal source checkout has no local editor proxy or MCP bridge to execute. MCP `2026-07-28` subscriptions are resource-URI notifications with no durable replay across reconnect; they do not define a Lean document version or proof authority. A small deterministic contract model over the observed Lean notification stream shows why a missed clearing event leaves a stale diagnostic until the client reads current authoritative state. These are separate **Lean execution**, **MCP/LSP specification**, and **local model** findings, not a tested end-to-end Anneal editor or MCP integration.

## Applicability

The execution used `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` on arm64 macOS, direct `lean --server`, `LEAN_NUM_THREADS=1`, no Lake project, imports, plugins, Rust host, editor extension, or MCP server. The binary SHA-256 is recorded in each transcript's `subject` event. Three repetitions were acquired on 2026-09-29.

The normative comparison is pinned to LSP 3.18 at `microsoft/language-server-protocol@de9a671ae6ba374cc748a29c1c620cbc536302ff` and MCP `2026-07-28` at `modelcontextprotocol/modelcontextprotocol@5f5440bb26a62e2cf3440b92da5a667efa03b267`. These are compared as protocol contracts; their combination is not implemented in this fixture. Prior corpus reports already survey [LSP proof-assistant architecture](../lsp-proof-assistant-architecture-2026-09-27/REPORT.md), [MCP proof-assistant architecture](../mcp-proof-assistant-architecture-2026-07-28/REPORT.md), and [Lean MCP implementations](../lean-mcp-implementations-2026-09-27/REPORT.md). This package adds a direct two-document shadow/replay transcript and a deliberately bounded reconciliation model.

The local implementation search used `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` at the project checkout. It found CLI/scanner/resolve/setup modules in `anneal/src` and no MCP/LSP handler there. This absence is scoped to that source tree and does not characterize external integrations.

## Findings

### Open document text, disk mirror, and replay have different authority

`Shadow.lean` on disk contains `theorem demo : False := by exact ?_`. Batch `lean --json` against those disk bytes exits 1. The direct server opens the same file URI with unsaved text `theorem demo : True := by trivial` at document version 1, waits for diagnostics, and reports `no goals`. The disk hash remains the bad-source hash. Version 2 changes only the open document to the bad source and reports `⊢ False` plus placeholder/unsolved diagnostics. Version 3 restores the good source in memory and reports `no goals`; the disk remains bad.

After `didClose`, reopening the URI with its disk bytes at version 4 reports the bad `⊢ False` goal and errors. Closing and reopening with the retained good text at version 5 reports `no goals` again. After deliberately killing the watchdog, a new server opened the retained good text at version 1 and reported `no goals` while the disk still contained the bad text. The new server's version 1 is a new process/document incarnation, not continuation of the old version sequence. All three runs agreed. Basis: **execution** in `support/transcript-run{1,2,3}.json`.

LSP 3.18 [`didOpen`](https://github.com/microsoft/language-server-protocol/blob/de9a671ae6ba374cc748a29c1c620cbc536302ff/_specifications/lsp/3.18/textDocument/didOpen.md) assigns open-document content management to the client, [`didChange`](https://github.com/microsoft/language-server-protocol/blob/de9a671ae6ba374cc748a29c1c620cbc536302ff/_specifications/lsp/3.18/textDocument/didChange.md) advances the synchronized version, and [`didClose`](https://github.com/microsoft/language-server-protocol/blob/de9a671ae6ba374cc748a29c1c620cbc536302ff/_specifications/lsp/3.18/textDocument/didClose.md) ends that ownership. The direct Lean observations match this division for the fixture. A hypothetical Anneal hidden document must be reconstructed from an explicit authoritative source snapshot after restart; a stale shadow file is only a locator/mirror until chosen as authoritative by the application. This final sentence is **derived design guidance**, not existing Anneal behavior.

### Physical path is not required for every bare Lean document

The fresh direct server opened `Missing.lean` via a `file:` URI with good unsaved text while no such file existed on disk, completed `waitForDiagnostics`, and returned `no goals`. A separate direct server accepted `untitled:AnnealProof.lean` with the same text, wait, and goal response. These results repeated three times. Basis: **execution**.

This only establishes that the bare direct server can elaborate these tiny core documents. It does not show that `lake setup-file`, project imports, plugins, generated modules, source maps, or editor URI routing work without a physical path. No general claim that Anneal can dispense with shadow files follows.

### Diagnostic routing is per origin, URI, and version

A second simultaneously open document, `Other.lean`, contained `#check nonexistentName` and received a version-1 unknown-identifier error. While `Shadow.lean` moved through versions 1, 2, and 3, the transcript contains no clearing notification for `Other.lean`; its error remained associated with its own URI and version. `Shadow.lean` emitted two version-2 errors and then a version-3 empty diagnostic update. When both documents were replayed in the new server, `Other.lean` again received its own error while `Shadow.lean` was clean. Basis: **execution**.

`support/contract_probe.py` consumes the raw LSP stream as a **local adapter model**. It simulates a client disconnect after transcript sequence 36, dropping the later version-3 clearing event at sequence 43. Its retained cache says `Shadow.lean` version 2 has two errors and `Other.lean` version 1 has one. A read of the authoritative state at sequence 47 instead says `Shadow.lean` version 3 has zero and `Other.lean` version 1 still has one. A single flattened “last diagnostic notification” would show zero errors and lose the independent `Other.lean` error. This is a deterministic counterexample to those two proposed client-cache strategies on this event stream; it is **not** an MCP transport experiment or proof of an implemented adapter.

An Anneal diagnostic envelope should therefore carry at least producer origin, document/obligation identity, producer generation, document version, and a clear operation scoped to that origin and URI. That is **derived** from the multi-document observation and model. The fixture has only Lean diagnostics; rustc/Charon/Aeneas multiplexing was not executed.

### LSP and MCP state boundaries cannot be inferred from one another

MCP `2026-07-28` [`subscriptions/listen`](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/patterns/subscriptions.mdx) filters notification classes and resource URIs, requires an acknowledged subset, and labels notifications with the subscription request ID. Reconnecting stdio requires a new subscription; the server does not retain subscription state for replay. [`resources/read`](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/server/resources.mdx) is a separate current-state read. Resource update notifications identify a URI but do not themselves specify Lean document versions, model generations, or an authoritative proof result. Basis: **normative** MCP specification + **derived** comparison.

The MCP [`base protocol`](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/index.mdx) correlates one request/response by JSON-RPC ID and requires protocol metadata; it does not turn a transport connection into a Lean document owner. MCP [cancellation](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/patterns/cancellation.mdx) is request-scoped and advisory. The application contract must name the source snapshot and workspace/generation on every proof operation, decide which client may edit, and define an authoritative state read after reconnect. These are **derived requirements**; no local MCP implementation was run to validate them.

### Backlog coverage and residual deltas

| Issue #3731 item | Evidence here | Remaining work |
| --- | --- | --- |
| I057 editor/LSP coexistence | Two Lean documents route separately in one server | Rust Analyzer/Lean editor routing, hover/completion, and cancellation across languages. |
| I058 diagnostics | Distinct URI/version updates and a lost-clear model | Real rustc/Charon/Aeneas multiplexing, rename, pull clients, and producer-scoped clears. |
| I061–I062 InfoView/encoding | Plain-goal and LSP version lifecycle only | Structured RPC, widgets, capability/encoding negotiation, projected Rust positions. |
| I064 disconnect | Forced Lean watchdog loss and explicit unsaved-text replay | Real editor disconnect while Anneal and Lean stay live; ownership transfer. |
| I065–I068 MCP state/authority | Pinned MCP contract versus LSP authority, executable reconciliation model | Built typed MCP tools, retries/CAS, simultaneous editor/MCP clients, shared unsaved Rust source. |
| I069–I072 access/scratch/cancellation/adapters | Existing corpus inventory and protocol boundary only | Authorization, scratch attempts, MCP cancellation/backpressure, representative adapter execution. |
| I152 subscriptions versus polling | Pinned subscription/read rules plus dropped-event model | Actual MCP server/client with negotiated capabilities, disconnect, and reconciliation. |
| I155 hidden/shadow lifecycle | File-backed stale mirror, missing file URI, custom URI, close/reopen/restart | Rust-host lifecycle, Lake setup, rename/save, generation replacement, and model imports. |

I059–I060 hover/navigation/tokens/rename and I063 save/build/format interactions were not exercised. The local tree search found no Anneal LSP proxy, editor extension, or MCP bridge executable/source under `anneal/src`; the checked-in V1 design labels interactive IDE support future work. An externally surveyed Lean MCP adapter was not installed for this investigation, so there is no claim about its runtime behavior.

## Boundaries

- **Not examined:** Rust-hosted annotations, true projected positions, generated Aeneas imports, Lake setup, editor clients, MCP transports, MCP tool calls, resource subscription delivery, or any production Anneal state engine.
- **Not established:** direct Lean acceptance of `untitled:` under a Lake project. The custom URI result is limited to core Lean and one simple proof.
- **Not established:** durable diagnostics from a push stream. The model deliberately drops a notification; it assumes an application-owned current-state read for reconciliation and does not implement one over MCP.
- **Not established:** permission or write authority. The fixture only queries and changes disposable Lean documents through one synthetic LSP client.
- **Known not to apply:** a closed document's prior unsaved text is not automatically recovered by reopening from stale disk; the direct Lean probe returned to disk semantics at close/reopen.

## Evidence

- [`support/lsp_probe.py`](support/lsp_probe.py) and three raw wire/event transcripts: [`run 1`](support/transcript-run1.json), [`run 2`](support/transcript-run2.json), [`run 3`](support/transcript-run3.json). Local absolute fixture and Lean toolchain paths are replaced with `$WORK`, `$LEAN_BIN`, and `$LEAN_HOME`; event order, message payloads, hashes, and process transitions remain.
- [`support/contract_probe.py`](support/contract_probe.py) and [`support/contract-observations.json`](support/contract-observations.json) replay a notification-cache counterexample over the raw Lean events. This script is application-model evidence only.
- Primary LSP specification source at the pinned revision: [`didOpen`](https://github.com/microsoft/language-server-protocol/blob/de9a671ae6ba374cc748a29c1c620cbc536302ff/_specifications/lsp/3.18/textDocument/didOpen.md), [`didChange`](https://github.com/microsoft/language-server-protocol/blob/de9a671ae6ba374cc748a29c1c620cbc536302ff/_specifications/lsp/3.18/textDocument/didChange.md), [`didClose`](https://github.com/microsoft/language-server-protocol/blob/de9a671ae6ba374cc748a29c1c620cbc536302ff/_specifications/lsp/3.18/textDocument/didClose.md).
- Primary MCP specification source at the pinned revision: [`subscriptions`](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/patterns/subscriptions.mdx), [`resources`](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/server/resources.mdx), [`base protocol`](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/index.mdx), and [`cancellation`](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/5f5440bb26a62e2cf3440b92da5a667efa03b267/docs/specification/2026-07-28/basic/patterns/cancellation.mdx).
- Local availability check at `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`: `rg -n 'MCP|mcp|textDocument/didOpen|lake serve|lean --server' anneal/src anneal/Cargo.toml` returned no matches. A search of `.anneal-local-tools` found reference reports and Aeneas instructions but no installed Lean MCP adapter implementation. No dependency was installed for the probe.

## Revalidation

Run `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/lsp_probe.py`, then `python3 support/contract_probe.py`. Confirm disk bad-source hash stays fixed while the open Shadow goal toggles good/bad/good; Other's error remains separately versioned; close/reopen from disk gives bad; explicit replay after watchdog loss gives good; missing-file and custom URIs give goals only under the stated bare setup. If an MCP bridge becomes available, replace the local contract model with actual negotiated `subscriptions/listen`, resource/tool state reads, dropped notifications, reconnect, and cancellation traces. Keep the LSP document owner and MCP workspace authority explicit in every request/result.
