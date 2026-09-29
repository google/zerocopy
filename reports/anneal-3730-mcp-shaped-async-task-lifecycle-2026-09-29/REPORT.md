# G03: toy async task lifecycle over a real Lean goal query

Observed 2026-09-29 on AArch64 macOS. This is new **component/contract evidence** for #3730 G03 and #3731 I065/I071 beyond the earlier [I072 adapter-availability/two-client probe](../anneal-3730-lean-mcp-adapter-availability-probe-2026-09-29/REPORT.md). It is **not** an existing MCP adapter, an MCP SDK/conformance test, an Anneal bridge, or a product implementation. Accordingly G03's requested actual MCP long-running-task integration remains **not run**.

## Availability and subject

The [scoped inventory](support/results.json) found no `mcp`, `fastmcp`, or `modelcontextprotocol` module in the active Python 3.14 environment; the global npm list had only `corepack`, `homebridge`, `homebridge-config-ui-x`, and `npm`; and six likely Lean MCP executable names did not resolve in the current PATH. This adds an SDK/package check to the prior checkout/PATH adapter inventory. It does not search every Python environment, npm project, browser extension, or machine path. Nothing was installed or downloaded.

The only language server under test is the already cached Lean **4.30.0-rc2** executable, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The fixture is one `Proof.lean` with `skip` at a `Nat.add_zero` proof site, SHA-256 `7f26c6edb74cf1cab89a66ddcc47530d92bdd989863ebe305c6f30c9d29bd0a3`. The [bridge](support/bridge.py) speaks deliberately **toy** line-delimited JSON-RPC over stdio. It starts separate worker processes for task handles, and each working task launches an actual `lean --server`, waits for diagnostics, and calls `$/lean/plainGoal`. Its task states are private JSON files in [support/work/tasks](support/work/tasks), with atomic file replacement. The bridge's task store, expiry policy, watcher notifications, revision names, and tools are experimental design choices; they are not MCP protocol guarantees.

## Executed sequence

The [driver](support/probe.py) requested toy `toy-async-v2` and received a `toyTasks` capability and `start_goal`/`get_task`/`result_task`/`cancel_task`/`release_task` tools. A separate client requested an unknown revision, was offered toy `toy-sync-v1`, received only `goal_sync`, had an async call rejected, and completed a direct synchronous Lean goal call. This is a capability/fallback *fixture*, not negotiation against an MCP SDK or published MCP revision.

Four distinct async task handles then exercised the following cases:

| Case | Retained observation | Exact boundary |
| --- | --- | --- |
| Stdio disconnect and retrieval | Client A observed `queued`/`waiting`, released the worker, and closed its stdio bridge. A new client/process polled that handle to `complete` and retrieved Lean's goal `n : Nat ⊢ n + 0 = n` and one `unsolved goals` diagnostic. The result was later `expired` under the fixture's 2-second post-completion TTL. | The worker survives **bridge/client disconnect**, not a machine crash; the new client has filesystem access to the toy state store. Expiry denies the result API but does not garbage-collect the file. |
| Cancellation | A task was cancelled while waiting at the probe's release gate. Its terminal state and retrieval were `cancelled`. | This checks pre-execution cancellation, not processing an in-flight Lean request or proving descendant cleanup under a kill race. |
| Partial failure | The worker obtained a real Lean goal and then deliberately raised an error before publishing a final result. Retrieval returned `failed`, the injected error, and only partial metadata (`goal_observed: true`, LSP PID). | The failure is injected at one controlled publication point, not an organic Lean or transport crash. |
| Recovery | A new task after that failure returned `complete` with the same Lean goal and diagnostic. | Shows a fresh isolated worker can recover this fixture, not a shared long-lived Anneal server. |

The first client received a `queued` progress notification before disconnect. The reconnected client received **no old progress notification for that handle**, yet retrieved the completed result. Other handles emitted `checking`, `failed`, and `complete` progress notifications. Thus progress loss did not itself lose the result in this toy store. [Full client/server transcripts](support/results.json), all four [task state files](support/work/tasks), worker logs, and [summary.json](support/summary.json) preserve the evidence. The [offline checker](support/check.py) verifies the fixture/source hashes, negotiated tool sets, all four terminal states, a real Lean goal and diagnostic, reconnect retrieval, expiry, failed partial publication, progress, and fallback.

## Decision relevance and residual

The probe makes one possible contract explicit: a durable task handle can outlive a stdio session, progress notifications can be lossy while result retrieval remains authoritative, cancellation has a terminal state distinct from proof failure, expiration can remove API access to an old result, and a partial observation must not be advertised as final success. A toy legacy capability fallback can reject async tools rather than silently pretending they exist. These are **candidate behaviors**, not observed behavior of MCP or Anneal.

I065 remains partial: test actual supported MCP protocol revisions/capabilities and an existing client/adapter pair, including handle identity across connection reuse and restart. I071 remains partial: test actual adapter transport and task API; an in-flight Lean cancellation, slow clients/backpressure, dropped responses, reconnect to a selected persistent service, worker loss, timeouts, and expiry/GC under failures. G03 remains not run as an actual MCP long-running-task integration. A real Anneal workspace/model generation, source freshness fence, permissions, and multi-client mutation are also absent. The prior I072 experiment covers a different two-client cancellation/freshness toy and does not fill these gaps.

## Reproduce

From the repository root, with the pinned Lean installation and current local npm/Python still available:

```sh
python3 reports/anneal-3730-mcp-shaped-async-task-lifecycle-2026-09-29/support/probe.py
python3 reports/anneal-3730-mcp-shaped-async-task-lifecycle-2026-09-29/support/check.py
```

The probe replaces only this package's `support/work` and `support/results.json`; run a copy to preserve this observation. It uses one small Lean file and four sequential task workers and finished in about eight seconds. The offline checker passed on the retained run. A later environment with an installed MCP SDK or adapter may legitimately change the availability inventory and should trigger a real adapter test instead of this fallback.
