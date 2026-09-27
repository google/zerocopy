# MCP state, lifecycle, and concurrency boundaries for proof-assistant integrations at 2026-07-28

## Summary

Model Context Protocol (MCP) `2026-07-28` deliberately separates a server's process lifetime from the logical state of work performed through it. Every modern MCP request is self-contained: it carries its protocol version and client capabilities, and a server must not infer session or conversation context from an existing connection or process. State that spans requests must instead have an explicit identifier that the client supplies on each relevant request.

That rule is the central constraint for a proof-assistant MCP server. A server may keep a Lean process, workspace, elaboration environment, or other expensive state alive between calls, but MCP does not make that process or connection a proof session. If later calls depend on earlier state, the application protocol needs an explicit workspace, document, prover, task, or similar handle, or enough request data to reconstruct the state. The core protocol does not define such proof-assistant handles.

The two standard transports reinforce that distinction in different ways. With stdio, the client launches one server subprocess and all responses and notifications share one bidirectional stream. The protocol explicitly permits unrelated requests to be interleaved on that process. With Streamable HTTP, every request is a separate POST to an independently running server; there is no MCP session ID, and a request may be served without connection affinity. In neither transport does connection identity supply semantic continuity.

MCP supplies several narrower correlation mechanisms instead of a session: JSON-RPC request IDs correlate responses; progress tokens correlate optional progress notifications; the request ID of `subscriptions/listen` becomes its subscription ID; resource URIs identify resources; and multi-round-trip requests carry explicit `requestState` when a server needs continuation data across retries. The specification's non-normative guidance for stateful tools similarly recommends server-minted opaque handles passed as ordinary tool arguments.

These mechanisms do not provide transactionality or exactly-once execution. Cancellation is best effort and races with completion. An HTTP response-stream failure loses the in-flight request rather than resuming it. A retry is a new request with a new request ID. For a proof server whose calls can mutate workspace or prover state, duplicate handling, serialization, optimistic version checks, rollback, and idempotency remain application-level responsibilities.

Basis: normative specification + non-normative protocol guidance + derived proof-assistant implications.

## Applicability

The protocol findings apply to the released MCP specification at `modelcontextprotocol/modelcontextprotocol@5f5440bb26a62e2cf3440b92da5a667efa03b267`, version `2026-07-28`.

This report examines the core protocol architecture, request/response correlation, explicit cross-request state, subscriptions, progress, cancellation, and the stdio and Streamable HTTP transports. It derives what those interfaces permit or require when a server fronts a stateful proof assistant.

The report does **not** examine any concrete Lean MCP implementation, Lean's own language-server protocol, tactic-state semantics, document-version rules, or a particular Lean process manager. Those subjects require separate evidence. It also does not inspect the optional MCP Tasks extension; the core specification names Tasks as an extension for durable asynchronous work, but its semantics are outside this report.

The report uses the `2026-07-28` release exactly. That release is the first "modern" stateless protocol era in the versioning document and materially differs from `2025-11-25` and earlier session-oriented revisions. No continuity to an adjacent MCP version is assumed.

No MCP implementation was executed. All established protocol behavior comes from the pinned specification and schema; proof-assistant consequences are labeled as derived where they go beyond what the specification states directly.

## Findings

### A connection or process is not an MCP session

The core protocol is stateless. Each request contains the information needed to interpret it, including the protocol version and client capabilities. A server must not use previous requests on the same connection to establish protocol context. The specification also says that related operations should not require the same connection or process, and that a stdio process should not use one task, thread, or conversation as its lifetime boundary.

Basis: normative specification.

This is stronger than "the transport can reconnect." It rules out using connection identity itself as the semantic key for cross-call application state. A long-lived server process can cache state, but a later request that depends on that state needs an explicit identifier or explicit state carried by the request.

The architecture document assigns lifecycle and orchestration to the host: a host manages client instances, and each MCP client communicates with exactly one server. Servers may be local processes or remote services. That host/client/server topology does not introduce a protocol-level conversation identity.

Basis: normative architecture description + derived synthesis.

For a proof assistant, the direct consequence is that a long-lived Lean process can be an implementation detail without being a logical proof session. A server that exposes operations such as "open workspace," "check document," or "query goal" needs an application-visible identity for whatever persistent state later calls address. MCP does not choose whether that identity names a Lean process, workspace, document snapshot, elaboration generation, or a more abstract object.

Basis: derived from statelessness.

### Standard transports define hosting and message flow, not semantic continuity

Under the stdio transport, the client launches the MCP server as a subprocess. Requests, responses, request-scoped notifications, and subscription notifications share one reliable bidirectional byte stream. Responses are correlated by JSON-RPC ID; subscription notifications carry a separate subscription ID because several subscriptions can share the same stream. The server must not send independent JSON-RPC requests to the client.

Basis: normative specification.

The stdio process therefore gives an implementation a convenient place to keep a Lean worker alive, but the process is not a conversation key. Unrelated requests may be interleaved on it. If two requests address different proof workspaces, the server has to distinguish those workspaces from request data rather than from which stdio process received them.

Basis: derived from normative statelessness and stdio semantics.

Under Streamable HTTP, the server is an independent process that may handle multiple client connections. Each client message is a separate POST to one MCP endpoint. A request can receive either one JSON response or its own SSE response stream for request-scoped notifications followed by the result. There is no MCP session ID in this revision.

Basis: normative specification.

The HTTP transport also removed SSE resumption. If a response stream breaks, the in-flight request is lost; the changelog requires a retry to use a new request ID. The protocol therefore does not provide transport-level exactly-once execution or replay recovery for a mutating tool call.

Basis: normative changelog + transport specification.

For stateful proof operations, an HTTP deployment can route related requests to different server instances unless the application adds its own state store or routing mechanism. Any such mechanism remains outside MCP. A sticky load balancer can be an optimization, but using stickiness as the only state identity would conflict with the protocol's requirement that a server not infer continuity from a connection.

Basis: derived.

### MCP uses several narrow correlation identifiers instead of one ambient session

The identifiers in the core protocol have deliberately different scopes:

| Mechanism | Protocol role | Scope relevant to proof-assistant integrations |
| --- | --- | --- |
| JSON-RPC request `id` | Correlates a response with an outstanding request | Unique among the sender's still-active requests; not a persistent workspace/session identity |
| `progressToken` | Correlates optional progress notifications | Unique across active requests; ends with the operation |
| `io.modelcontextprotocol/subscriptionId` | Correlates notifications to a `subscriptions/listen` request | Equals that request's JSON-RPC ID; identifies one live subscription stream |
| Resource `uri` | Identifies an MCP resource | Persistent identity is application-defined through the URI; MCP does not add document-generation semantics |
| MRTR `requestState` | Carries opaque continuation data across a retry | Tied to retrying one logical operation; not a general session |
| Stateful-tool handle | Non-normative cross-call state pattern | Ordinary tool result/argument value; MCP gives it no special wire semantics |

Basis: normative specification except the stateful-tool row, which is non-normative protocol guidance.

The narrow scopes matter because a proof server usually has more identities than one request: repository, workspace, document, document version, theorem, source position, elaboration generation, and possibly a long-lived prover process. MCP does not collapse those concepts into a session. If correctness depends on distinguishing them, the server's own schemas must carry the distinction.

Basis: derived.

### Cross-request state must be explicit

The core statelessness rule says that state spanning multiple requests must be referenced by an explicit identifier supplied with each request. The tools specification gives a matching non-normative pattern: a creation tool can return a server-minted opaque handle, and later calls can take that handle as an ordinary argument. The guidance treats authorization, opacity, lifetime, and expiry as properties the server must define rather than properties MCP supplies.

Basis: normative statelessness + non-normative tool-design guidance.

This pattern maps directly to a stateful proof server without prescribing one architecture. A server could, for example, return a `workspace_id` after preparing a Lean environment, then require that ID on document and tactic-state tools. It could instead make each tool self-contained by passing source, dependency identity, and position on every call. MCP permits either approach.

Basis: derived.

An explicit handle does not itself make state durable or portable. A process-local handle becomes invalid when that process dies unless the server can reconstruct or locate the named state elsewhere. If a handle is meaningful across processes, the server has to supply the backing storage or routing. If authorization applies, the tool guidance recommends validating the caller's authorization against the handle on every call rather than treating possession of an authenticated handle name as sufficient.

Basis: non-normative guidance + derived.

### Concurrent requests require application-level state discipline

MCP request IDs allow multiple requests to be outstanding at once, and the statelessness section explicitly anticipates requests for multiple tasks, threads, or conversations. The stdio transport multiplexes them on one stream; Streamable HTTP naturally handles them as independent requests.

Basis: normative specification.

MCP does not define a lock, transaction, document version, compare-and-swap token, or ordering rule for application state touched by two tool calls. A proof server that permits concurrent mutation of one workspace therefore has to define its own discipline: serialize mutations, address immutable snapshots, carry expected generations, reject stale operations, or use another scheme appropriate to the underlying prover.

Basis: derived.

This also affects dynamically exposed capabilities. `tools/list` and `resources/list` may change over time and may vary with per-request authorization, but they must not vary merely by connection or as a side effect of requests on that connection. Per-proof dynamic behavior should therefore be expressed through explicit tool arguments, resource identities, authorization, or another request-visible input rather than hidden connection state.

Basis: normative tools/resources specification + derived.

### Multi-round-trip input is a retry protocol, not a suspended server call

In `2026-07-28`, a server no longer sends an independent JSON-RPC request to a client for sampling, elicitation, or roots. Instead, selected client requests can return `InputRequiredResult`. The client obtains the requested input and then retries the original operation. The retry must use a different JSON-RPC request ID.

Basis: normative specification.

The server can include opaque `requestState`, which the client must echo without interpreting. The protocol is designed so that the retry can be processed without relying on the server instance that handled the first request. When `requestState` influences authorization, resource access, or business logic, the server must integrity-protect it; the specification also recommends binding it to a principal, short lifetime, and originating request identity to reduce replay risk.

Basis: normative specification.

For a proof interaction that pauses for user or model input, this means the wire-level continuation is explicit. A server may keep an internal continuation alive, but it cannot require that the retry reach the same process unless it has exposed enough explicit state to recover that continuation correctly. Conversely, a server can encode or reference continuation state and remain horizontally routable.

Basis: derived.

### Subscriptions are long-lived requests, not durable sessions

`subscriptions/listen` opens a long-lived notification stream. Clients opt in to specific event classes such as tool-list changes, resource-list changes, or updates to selected resource URIs. Each subscription is identified by the JSON-RPC ID of the request that opened it, and every delivered notification carries that value in `io.modelcontextprotocol/subscriptionId`.

Basis: normative specification.

Several subscriptions can be active concurrently. On stdio they share the same byte stream, so the subscription ID is required for demultiplexing. If a stdio connection is lost and recreated, the client must issue `subscriptions/listen` again; the server holds no subscription state across the reconnection. Streamable HTTP likewise has no resumable SSE event log in this revision.

Basis: normative specification.

A proof server can use subscriptions to signal that a resource or capability changed, but the stream is not a durable proof-state journal. After a disconnect, a client should reacquire current state from an authoritative read/query surface rather than assume it can replay missed notifications from MCP itself.

Basis: derived.

### Progress reports activity; it does not create a task identity

A client opts into progress by placing a `progressToken` in request metadata. The token must be a string or integer and must be unique across active requests. A server may then emit monotonically increasing progress notifications, but it is allowed to emit none.

Basis: normative specification.

Progress is therefore useful for a long-running proof check or elaboration request, but it does not make that work durable after the request or transport ends. The core protocol's optional Tasks extension is the separately named mechanism for durable asynchronous operations; it is outside this report.

Basis: normative core specification + boundary note.

### Cancellation is best effort and transport-specific

For stdio, a client cancels an in-flight request by sending `notifications/cancelled` with the request ID. For Streamable HTTP, closing that request's SSE response stream is the cancellation signal. Servers should stop work and free resources, but the specification permits them to ignore cancellation when work is unknown, complete, or not cancellable. The protocol explicitly requires both sides to tolerate cancellation racing with completion.

Basis: normative specification.

The resulting guarantee is weaker than rollback. A client cannot infer from "cancellation requested" that a proof process reverted every application-level change, that no generated files were written, or that an underlying Lean operation ceased before producing side effects. If a proof tool mutates durable state, the tool contract must specify what cancellation means for that state.

Basis: derived.

Timeouts are similarly advisory at the protocol level. Implementations should establish request timeouts and may reset them on progress, but should keep a maximum timeout. This controls resource use; it does not create transaction boundaries.

Basis: normative specification + derived.

### Discovery and capability negotiation no longer create a session

Servers must implement `server/discover`, and clients may use it to learn supported versions, server capabilities, and self-reported identity. Calling it is optional for a modern client because every ordinary request carries its own protocol version and capabilities. There is no modern initialization handshake.

Basis: normative specification.

A version mismatch produces an explicit unsupported-version error and the client may retry with a mutually supported version. The release's versioning document defines `2026-07-28` and later as the modern per-request era and `2025-11-25` and earlier as the legacy initialization-based era.

Basis: normative specification.

This boundary is unusually important for architecture comparisons. Designs based on `Mcp-Session-Id`, an `initialize` lifecycle, server-initiated requests, or resumable SSE describe earlier revisions rather than the protocol pinned here. Revalidation must therefore start with the exact MCP protocol version before carrying forward assumptions from an older implementation or design document.

Basis: normative changelog + versioning specification.

### Resources provide generic identity, not a proof-document protocol

MCP resources are identified by URI. A server can list resources, read them, expose URI templates, and deliver update notifications for subscribed resource URIs. The resource abstraction is deliberately generic and application-driven.

Basis: normative specification.

That is enough to represent proof-related artifacts such as source files, generated Lean, diagnostics snapshots, or serialized goal views if an implementation chooses to expose them that way. The core resource protocol does not define proof-assistant document versions, source positions, incremental edit sequencing, elaboration generations, or tactic-state semantics. Those identities and transitions must come from the application's resource URI scheme, tool arguments, or another layer such as the prover's own language-server protocol.

Basis: derived from the generic resource schema and the absence of proof-specific state in the examined core protocol.

Tools similarly provide generic named operations with JSON-Schema inputs and outputs. That makes them suitable for actions such as "query tactic state at position" or "check proof" without assigning semantics to the workspace/document identifiers those calls need.

Basis: normative tool interface + derived.

## Boundaries

**Not examined:** concrete Lean MCP servers, their tool names, or whether any existing implementation already exposes stable workspace/document handles.

**Not examined:** Lean LSP document-open/change/save semantics, exact tactic-state querying, elaboration cancellation, server cache invalidation, or process-restart behavior. MCP cancellation and resource subscriptions do not establish those Lean behaviors.

**Not examined:** the MCP Tasks extension. Core progress and cancellation describe an in-flight request only; they do not establish durable asynchronous task semantics.

**Not examined:** detailed HTTP authorization flows. This report uses only authorization facts needed to interpret connection-independent lists and stateful handles.

**Unknown at the proof-assistant layer:** the best granularity for a persistent handle. MCP permits a handle to represent a prover process, workspace, document snapshot, or other object; choosing among them is an application-design question.

**Known not to apply across versions:** the no-session/no-initialize conclusions describe `2026-07-28`. The changelog records that the release removed protocol-level sessions, initialization, server-initiated JSON-RPC requests, and SSE resumption from the preceding era. Older MCP implementations can therefore have materially different lifecycle assumptions.

**No execution evidence:** the report did not run an SDK, server, client, or proof assistant. It establishes protocol obligations and architecture consequences, not implementation conformance.

## Evidence

Primary subject: `modelcontextprotocol/modelcontextprotocol@5f5440bb26a62e2cf3440b92da5a667efa03b267` (`2026-07-28`).

Pinned specification files inspected:

- `docs/specification/2026-07-28/index.mdx` — blob `2ae92c1169bd608da95ea6f3844dad66d42fd6e2`; protocol overview, core primitives, JSON-RPC basis, and security framing.
- `docs/specification/2026-07-28/changelog.mdx` — blob `dc5c9a9cf3e6895504534cf3f300514394d8c6ae`; removal of sessions/initialization/resumable SSE, MRTR introduction, and subscription changes.
- `docs/specification/2026-07-28/architecture/index.mdx` — blob `ec180b8b443c423fecfe35ad6666d3a4e959cdd6`; host/client/server responsibilities and one-client-to-one-server topology.
- `docs/specification/2026-07-28/basic/index.mdx` — blob `dfe11ecc1443b7dec051b1b1b9a93982b735c647`; request IDs, per-request metadata, statelessness, and base message rules.
- `docs/specification/2026-07-28/basic/versioning.mdx` — blob `fcfea9f0a150923ffd6637ff53fadc8240eefedf`; modern-versus-legacy eras, version negotiation, and no-handshake lifecycle.
- `docs/specification/2026-07-28/basic/patterns/mrtr.mdx` — blob `a66d667094e73a65a202ed512bd4d398676c9287`; multi-round-trip input, `requestState`, retry IDs, and replay/security constraints.
- `docs/specification/2026-07-28/basic/patterns/subscriptions.mdx` — blob `866898e18ca45bab5912f184962fc655bf2d8107`; subscription IDs, concurrent subscriptions, and reconnection behavior.
- `docs/specification/2026-07-28/basic/patterns/progress.mdx` — blob `f6dc5c041b0bd9fea07888253fed184e7e9028df`; progress-token scope and notification rules.
- `docs/specification/2026-07-28/basic/patterns/cancellation.mdx` — blob `b8db4c83d989bfe662eb47d74539c1cc19e4bf97`; transport-specific cancellation, races, and timeout guidance.
- `docs/specification/2026-07-28/basic/transports/stdio.mdx` — blob `b03ac10081d7a7a92516b5b074e4c843bc75d473`; subprocess ownership, shared stream, shutdown, restart, and stdio cancellation.
- `docs/specification/2026-07-28/basic/transports/streamable-http.mdx` — blob `7b9813d67a9d8b90a496a6c251193a70ce79c657`; independent server process, per-request POST/SSE, lack of sessions/resumption, and HTTP cancellation.
- `docs/specification/2026-07-28/server/discover.mdx` — blob `f6fc1acf974819d99338d2be25ad953fcb9e57a6`; server discovery and self-reported capabilities.
- `docs/specification/2026-07-28/server/tools.mdx` — blob `449020f54a6582122607b4869129bec5f1035f37`; tool identity, connection-independent listing semantics, and non-normative explicit-handle guidance for stateful tools.
- `docs/specification/2026-07-28/server/resources.mdx` — blob `f49dd8e6be3fd8f13911788ae5f5d4c87d2c53cd`; URI resource identity, subscriptions, and connection-independent listing semantics.
- `schema/2026-07-28/schema.ts` — blob `9b55feeb412bc3ae877f2eac10b5c01ba29a2eed`; authoritative message/type schema referenced by the specification.

All protocol requirements above use the specification as **normative** evidence. The stateful-tool handle section labels itself non-normative; this report treats it as **documentation/guidance**, not a wire requirement. Statements about how these constraints apply to a stateful proof assistant are **derived** and are identified as such.

## Revalidation

For another MCP revision, first establish whether it belongs to the same lifecycle era. Do not begin with an SDK's process model.

The cheapest discriminating source diff is:

1. compare `basic/index.mdx` for the statelessness rule, required per-request metadata, request-ID semantics, and any new application-state primitive;
2. compare `basic/versioning.mdx` and `changelog.mdx` for restoration or further changes to initialization, sessions, or negotiation;
3. compare both transport specifications for process ownership, session/connection affinity, SSE resumption, cancellation, and restart rules;
4. compare `patterns/mrtr.mdx`, `subscriptions.mdx`, `progress.mdx`, and `cancellation.mdx` for continuation and correlation semantics;
5. compare `server/tools.mdx` and `server/resources.mdx` for list scoping, explicit state handles, and resource identity; and
6. diff `schema/<version>/schema.ts` for changed message fields and correlation IDs.

A narrow implementation probe can then test only conformance details the specification cannot prove: run one server over stdio and one over Streamable HTTP; issue two interleaved requests with distinct explicit state handles; cancel one; restart or reconnect; and verify that no hidden connection state is required to address the surviving logical state. If the server supports subscriptions, re-establish them after reconnect and confirm that missed events are recovered through an authoritative state read rather than transport replay.

For a proof-assistant integration, revalidate the MCP protocol separately from the prover layer. The MCP probe above establishes transport and correlation behavior; a distinct Lean/prover probe must establish workspace identity, document generations, tactic-state positions, cancellation, invalidation, and restart reconstruction.
