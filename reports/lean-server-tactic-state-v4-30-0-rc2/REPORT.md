# Lean language server and tactic-state queries at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), the Lean language server already exposes the proof-state primitive an interactive Anneal client would need: given an open Lean document and an LSP source position, a client can ask for the tactic goals at that position.

The structured InfoView path is a Lean-specific RPC layered over LSP. A client opens the document, creates a per-file RPC session with `$/lean/rpc/connect`, and sends `$/lean/rpc/call` with method `Lean.Widget.getInteractiveGoals`, the document URI, the source position, and `PlainGoalParams`. Lean returns structured goals containing hypotheses, target text with embedded interactive information, metavariable identity, and a server-side context reference. A simpler `$/lean/plainGoal` request uses the same goal-selection machinery and returns pretty-printed goal strings.

The query is not a stateless parser operation. Lean runs one worker process per open file under a watchdog process. Each worker incrementally elaborates the document into an asynchronous snapshot tree whose nested `InfoTree` data records tactic contexts. `getInteractiveGoals` locates the snapshot and tactic information covering the requested position and selects the before- or after-tactic metavariable context according to the stored goal record.

Document versions and worker lifetime are part of the interface. A `didChange` updates the worker's document, starts processing the new snapshot tree, and cancels pending requests from the old version. A worker restart destroys its RPC sessions; stale session IDs produce `RpcNeedsReconnect`. Saving an imported file does not silently update already-open dependents: the watchdog marks those dependents stale and asks the user/client to restart them. Explicit synchronization through `textDocument/waitForDiagnostics` is available when a client needs a versioned processing barrier before querying.

These source-level facts establish that a long-lived agent-facing service can delegate tactic-state-at-position queries to Lean's existing server protocol rather than inventing a second proof-state engine. They do not establish the behavior, latency, resource use, or robustness of a particular MCP bridge or Anneal integration.

No fresh Lean server, Lake, LSP, or MCP execution was performed. The report is based on exact pinned Lean source, the pinned server protocol overview, and Lean's checked-in server test client.

## Applicability

- Lean repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- version: `v4.30.0-rc2`
- Anneal context: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, whose selected Aeneas toolchain uses this Lean release.

"Goal at a position" means Lean's own server selection semantics, not a promise that every byte offset has exactly one distinct proof state. The implementation searches nested elaboration snapshots and `InfoTree` tactic records whose ranges cover the requested position, then chooses a goal set using Lean's syntax-range and before/after-tactic rules.

This package concerns one Lean language-server process and its per-open-file workers. It does not characterize multiple independent Lake workspaces inside one process, server memory scaling, or the complete Lake setup graph.

## Findings

See [`FINDINGS.md`](FINDINGS.md). The high-value conclusions are that the server is a watchdog plus per-open-file workers; target files must be open; `getInteractiveGoals` is a structured RPC reached through `$/lean/rpc/call`; `$/lean/plainGoal` is a simpler control using the same goal lookup; tactic states come from snapshot/InfoTree elaboration data; edits invalidate pending old-version work; worker replacement invalidates RPC sessions; and saved dependencies mark open dependents stale instead of silently changing their environment.

## Boundaries

See [`BOUNDARIES.md`](BOUNDARIES.md). In particular, this package contains no fresh server execution or wire transcript and does not establish performance, batch/server equivalence, Lake preparation behavior, MCP concurrency, or Rust-to-generated-Lean source correspondence.

## Evidence

See [`EVIDENCE.md`](EVIDENCE.md) for exact source files and blob identities. Evidence roles are upstream **documentation**, pinned **source**, a checked-in source client, and **derived** architectural conclusions; there is no fresh **execution** evidence.

## Revalidation

See [`REVALIDATION.md`](REVALIDATION.md) for a minimal future protocol probe covering open/synchronize/query, structured RPC versus plain goal output, edit invalidation, and reconnect after worker restart.
