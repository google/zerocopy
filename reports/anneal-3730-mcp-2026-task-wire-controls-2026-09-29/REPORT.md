# MCP 2026 task wire controls in a local stdio test bridge

## Summary

The earlier [MCP-shaped async lifecycle report](../anneal-3730-mcp-shaped-async-task-lifecycle-2026-09-29/REPORT.md) deliberately used invented revision names and tools. The current MCP 2026-07-28 core and Tasks extension use materially different wire shapes: modern requests carry version and capabilities per request, `server/discover` replaces `initialize`, a task-capable `tools/call` may return `resultType: "task"`, and `tasks/get` carries the final result. A new standard-library-only stdio test bridge exercised these shapes and negative controls. It is a protocol **model**, not an MCP SDK/conformance result, an existing adapter, or Anneal interoperability.

## Applicability

The normative source for version and fallback behavior is the official [2026-07-28 versioning specification](https://modelcontextprotocol.io/specification/2026-07-28/basic/versioning), together with [discovery](https://modelcontextprotocol.io/specification/2026-07-28/server/discover), the [base message rules](https://modelcontextprotocol.io/specification/2026-07-28/basic), and the [stdio binding](https://modelcontextprotocol.io/specification/2026-07-28/basic/transports/stdio). The official [Tasks extension draft](https://tasks.extensions.modelcontextprotocol.io/specification/draft/tasks), read on 2026-09-29, defines the task result shape, polling, cancellation and optional task status notifications. This extension page is labeled **draft**, so recheck it before implementation.

`support/bridge.py` and `support/probe.py` use only Python 3's standard library and line-delimited JSON-RPC over local subprocess stdio. The bridge has a modern mode and a separate legacy test mode. A test-only `test/release` RPC controls worker completion; it is not an MCP method. The worker returns fixture text, not a Lean goal. There was no SDK, installed MCP adapter, HTTP transport, real Lean server, Anneal process, credential, network call, package installation or download. The prior report owns the separately executed toy task lifecycle over real Lean LSP.

## Findings

### Modern discovery and legacy fallback have different branches

The local modern bridge returned `-32022` with `supported: ["2026-07-28"]` for an unsupported version, then answered a retry with `server/discover` advertising tools and `io.modelcontextprotocol/tasks`. A request missing the per-request version was rejected by this bridge; `initialize` was rejected in modern mode. The same bridge returned an ordinary `resultType: "complete"` tool result when the client omitted the Tasks extension opt-in and a `resultType: "task"` handle when it included the extension in `_meta.io.modelcontextprotocol/clientCapabilities.extensions`. **Basis: local execution.** The required version error, modern metadata, discovery and extension negotiation are specified by the [official core](https://modelcontextprotocol.io/specification/2026-07-28/basic/versioning) and [Tasks extension](https://tasks.extensions.modelcontextprotocol.io/specification/draft/tasks); this bridge's exact missing-metadata error code and sync fallback content are its own choices.

In a separate legacy bridge process, `server/discover` returned a non-modern method-not-found error, after which the client sent `initialize` for `2025-11-25`, `notifications/initialized`, and a synchronous `tools/call`. Its legacy tool result omitted `resultType`; the [2026 core message rule](https://modelcontextprotocol.io/specification/2026-07-28/basic) treats an absent `resultType` from an earlier server as complete. The client did **not** fall back to `initialize` after the modern bridge's recognized `-32022` error. This is the distinct decision prescribed by the [stdio backward-compatibility rules](https://modelcontextprotocol.io/specification/2026-07-28/basic/transports/stdio). **Basis: normative specification plus local execution.** The driver follows that branch deliberately; it is not an SDK's negotiation algorithm.

### Task polling, final result, cancellation and errors

The task handle was visible to `tasks/get` immediately after `tools/call` returned it, which is the durability ordering required by the [Tasks extension](https://tasks.extensions.modelcontextprotocol.io/specification/draft/tasks). Polling first returned `working`; after the test release gate it returned `resultType: "complete"`, `status: "completed"` and a nested final tool result. The old toy `tasks/result` shape was rejected as an unknown method. This bridge chose a 350 ms TTL and returned an expired-task error after that time; the extension allows expiry/purge but does not require this exact retention period or error timing. An unknown task ID also produced an error. **Basis: local execution; normative limits from the extension.**

The local domain-error task ended `completed` with nested `result.isError: true`; an injected JSON-RPC error ended `failed` with an `error` object. That separation follows the Tasks extension's status definition. `tasks/cancel` returned an empty `resultType: "complete"` acknowledgement while the task still read `working`; the worker moved to `cancelled` only after the test gate was released. Sending a `notifications/cancelled` notification using the original call ID did not cancel the task, and cancelling an unknown task returned an error. The extension specifies `tasks/cancel` for task cancellation, forbids using ordinary `notifications/cancelled` for that purpose, and makes cancellation cooperative rather than guaranteeing a `cancelled` terminal state. This bridge's eventual cancellation is a fixture outcome. **Basis: normative specification plus local execution.**

The server emitted no `notifications/progress`. The client observed status by polling `tasks/get`. The Tasks extension permits optional `notifications/tasks` on a `subscriptions/listen` stream but says ordinary `notifications/progress` and `notifications/message` are not supported for tasks there. This run did not implement or test subscriptions, backpressure or pushed task status. The earlier toy report's progress notifications were explicitly invented and do not establish the current extension behavior.

| Negative control | Retained local response |
| --- | --- |
| Unsupported modern revision | `-32022` and supported version list; retry remained modern. |
| Missing modern version metadata | Rejected by test bridge. |
| Modern `initialize` | Rejected. |
| No Tasks opt-in | Synchronous complete tool result. |
| Old `tasks/result` method | `-32601` method not found. |
| Expired or unknown task ID | `-32602` in this bridge. |
| `notifications/cancelled` for a task | Task remained `working`; `tasks/cancel` acknowledged intent. |
| Tool-domain error versus JSON-RPC failure | `completed` + `isError: true` versus `failed` + error. |
| Legacy discovery | Non-modern error, then 2025-11-25 initialization and sync fallback. |

## Boundaries

This is a wire-shaped local model, **not a conformance test**. The bridge implements only the methods and error cases needed for this bounded experiment. It has no authentication or task ownership policy; the task store is in-memory and is lost when the bridge exits. It does not exercise a real SDK's schema validation, HTTP routing headers, `subscriptions/listen`, `tasks/update`/input-required flows, reconnect retrieval, true long work, in-flight Lean cancellation, dropped frames, persistence or cross-client permissions. The existing toy Lean report covers a different reconnect/result fixture; neither report establishes an actual MCP/Lean adapter or Anneal bridge.

G03/I065/I071 therefore gain a concrete **current-spec protocol-shape** test and an important correction to any temptation to map toy method names directly into MCP. The requested existing client/adapter negotiation and real asynchronous Lean/Anneal task lifecycle remain untested. A durable service would need to bind task IDs to authorization and generation identities, respect the selected revision/extension, and verify result publication and cancellation against its actual workers. Those are design requirements, not observations of this bridge.

## Evidence

- `support/bridge.py` SHA-256 `2fe6aa257a42f02deade18f1a9ecb9862eb3b8c1bf3c809211f906853c56165e` defines the two local modes, test gate, task state transitions and JSON-RPC responses.
- `support/probe.py` SHA-256 `154579a8f76b421cca54fe25fb2304aa1fb9d01e11c9f727f01af5b96b14df8b` sends raw line-delimited client messages and asserts the negative controls.
- `support/results.json` SHA-256 `a6fca5636e69da22c5b9a527875c190f83abfa7116d6f950c5d4065f625a6c20` preserves 53 modern and 9 legacy client/server transcript entries, process exits, cases and status polls. `support/check.py` validates the retained protocol-shape outcomes without launching a bridge.
- Normative reading was performed on 2026-09-29 at the official versioning, discovery, stdio, base and Tasks extension URLs above. The extension is draft and its URL can later serve revised text; the protocol revision/date here are part of the report's applicability.

## Revalidation

Run `python3 support/check.py` to check the retained transcript. To replay the local bridge, run `python3 support/probe.py`; it overwrites only this package's `support/results.json`. Compare modern versus legacy fallback, per-request metadata, task result shapes and negative-control responses. Before implementing against an SDK or Anneal, recheck the current official protocol and extension revisions, then run SDK/client interoperability tests against a selected real bridge. Do not promote this model's chosen TTL, error messages or cooperative worker timing into protocol guarantees.
