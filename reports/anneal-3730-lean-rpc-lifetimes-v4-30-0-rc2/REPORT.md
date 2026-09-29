# Direct Lean RPC session lifetimes, delayed replies, and historical snapshots

## Summary

For direct Lean 4.30.0-rc2 servers, an RPC session remained usable across an in-place document edit and returned the *new* goal. It became invalid after close/reopen or a new server, returning `-32900`. A cancelled, gated RPC request returned `-32800`, while the session remained usable. A killed worker's outstanding request did not complete within 15 seconds; close/reopen then delivered `-32801` and started a usable worker. Separate old and replacement servers returned opposite goals for the same URI, document version, and request number, with the old reply arriving last. Thus the transport/process incarnation and current source identity must accompany a result; numerical request IDs and RPC reference payloads are insufficient identities. This is a **derived client design implication**, not a demonstrated Anneal adapter behavior.

A separate URI containing retained 64-byte V1 source yielded its old goal while the original URI yielded V3's new goal. This is one executable historical-snapshot construction, not a native exact-version query in one Lean document.

## Applicability

The execution used the pinned arm64 macOS Lean release binary `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, with direct `lean --server`, `LEAN_NUM_THREADS=1`, no Lake project, no user imports or plugins, and tiny generated files. The probe's own SHA-256 is in `REPORT.json`. All worker and server scenarios ran sequentially except the deliberately overlapping old and replacement servers; the latter each held one small file worker. The test host had 8 GiB of RAM. Recorded process RSS is sampled macOS `ps` RSS, whose sum may count shared pages more than once.

The exact issue scope was [#3731 I041–I047](https://github.com/google/zerocopy/issues/3731), as retained in the corpus investigation matrix. This report adds direct execution to the earlier [goal/edit race](../anneal-3730-lean-protocol-races-v4-30-0-rc2/REPORT.md) and [topology](../anneal-3730-server-topology-v4-30-0-rc2/REPORT.md) reports. It makes no claim about Anneal, its MCP server, or generated projects.

## Findings

### RPC sessions and references

V1, V2, and V3 have the same declaration and cursor position, but goals `n + 1 = 8`, `= 9`, and `= 10`. The probe opened V1, connected RPC session A, and received `Lean.Widget.getInteractiveGoals` with context reference `{"p":"9"}`. It then edited the same URI to V2. Calling RPC through **the same session A** returned the V2 `= 9` goal. The probe sent `$/lean/rpc/release` for the retained context reference. It did not dereference that object after the edit; successful session reuse does not prove an old context reference remains semantically current.

After close/reopen of the same URI at document version 1 with V3, a call through session A returned `-32900 Outdated RPC session`. A new connection returned V3's `= 10` goal. A separate fresh watchdog likewise rejected the prior session with `-32900`, then accepted a new session. The new session's response again contained a `{"p":"9"}` context reference. The repeated wire value is a negative control against treating a reference number as globally unique. **Basis: execution**, `support/transcript.json` events `retained`, `after_edit`, `after_reopen`, and `fresh_session`; [Lean's RPC schema](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Extra.lean#L197-L254) describes reconnect and reference release; [RPC encoding](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Rpc/Basic.lean#L65-L80) makes context objects opaque to clients.

The distinct gated RPC cancellation sent request 60 while `run_tac` was blocked, sent `$/cancelRequest`, and released the gate. Request 60 returned `-32800`; a subsequent call under the same session returned `⊢ True`. The transcript preserves client/server wire order and gate events. This shows cancellation of this pending request, not cancellation of the session or every RPC method. **Basis: execution**.

### Worker and server incarnation

The probe sent RPC request 12 and killed the single identified file-worker PID. Within its 15-second read bound, it saw progress but no final reply and no replacement child. It then sent `didClose` and `didOpen` for the same URI/version: the old request returned `-32801 The file worker ... has been terminated`, a new diagnostics wait completed, a new worker PID appeared, and a fresh RPC connection returned the V3 goal. The observed recovery depended on close/reopen in this run; automatic recovery without it remains unresolved. **Basis: execution**, events `worker_crash_unresolved`, the request-12 wire reply, and `worker_crash_recovery`.

A tactic gate held a V1 `⊢ True` request in old server O. Before releasing the gate, the probe opened V2 `⊢ False` on replacement server N, reused the same URI, document version 1, and JSON-RPC request ID 50, and received N's `⊢ False`. It then released O's gate and received O's delayed `⊢ True`. Both are valid within their separate transports, but a caller that merges them solely by `(URI, version, request ID)` can misattribute the late reply. This is a **separate-server replacement simulation**, not an internal replacement of one worker in a live watchdog. **Basis: execution**, event `late_reply` and surrounding wire events.

Clean LSP shutdown/exit returned watchdog code 0 and the two prior file-worker PIDs were absent at the subsequent `ps` check. The forced case killed a watchdog while a tactic was gated, then released the gate; watchdog code was `-9`, and the prior worker PID was absent at the later check. Because release and pipe closure followed the kill, the result cannot isolate which event ended that worker, nor establish general orphan reclamation. **Basis: execution**, `clean_after` and `forced_after`.

### Latest and historical goal construction

The main URI was reopened with V3 at version 1. A `plainGoal` request containing an extra `textDocument.version: 1` returned `= 10`, the current V3 goal. A distinct `Historical.lean` URI opened with retained V1 source returned `= 8`. Opening that second document and waiting for diagnostics took 238.8 ms in the recorded warm run; it added one file-worker process, with sampled RSS 383,959,040 bytes beside the existing worker's 384,614,400 bytes. The source itself was 64 bytes. This demonstrates one isolation route and its local cost, not full revision retention, exact environment reconstruction, or a robust latency distribution. **Basis: execution**, event `historical` and `support/summary.json`.

For this fixture, a client can implement *latest at completion* by accepting a goal only after checking its own current source digest and transport/worker incarnation after the reply. It can implement an *explicit historical* query by retaining the exact source and an isolated prepared environment, then querying a separate file/worker and labelling that result with the retained identity. These are **derived protocol designs**, not implemented end-to-end in the probe; Lean's returned `plainGoal` payload itself contains neither the client's source hash nor worker incarnation.

## Boundaries

- **Not examined:** dereferencing the retained `ctx` object through a procedure after an edit; reference expiration after the documented keep-alive timeout; `rpc/release` memory reclamation; multiple simultaneous sessions within one worker; server restart using an identical RPC session ID by chance.
- **Not examined:** same-transport request-ID reuse while an old request is pending (which would make response matching ambiguous); internal watchdog worker replacement with a deliberately late *successful* old response. The successful late-old-reply case used two independent transports. The worker-kill case returned `-32801` only after close/reopen.
- **Unknown:** whether a crashed worker would eventually restart without close/reopen after a wait longer than 15 seconds, and whether the watchdog observed the kill before that wait ended.
- **Not examined:** native snapshot-specific Lean operations, complete imported environment retention, rapid edit trains, actual historical revision storage policy, process-wide USS, proof acceptance, or partial-file error recovery. These remain substantial I041/I042/I043/I046/I047 dimensions.
- **Not established:** that a goal is proof acceptance. V1/V2/V3 deliberately contain `exact ?_` and therefore have diagnostics; their goals are state probes only. The `True`/`False` gated fixtures also have placeholders.
- **Not examined:** actual Anneal worker ownership, MCP envelopes, or source/artifact generation fences. Every successful/incomplete observation here concerns direct Lean protocol behavior only.

## Evidence

- Replayable Python standard-library probe: [`support/probe.py`](support/probe.py), SHA-256 `b17723466f7ff64e8566cd1df1b861fa81b3c3b8893d365cd99a31703f6b859b`.
- Full JSON-RPC client/server message transcript and process events: [`support/transcript.json`](support/transcript.json), SHA-256 `fd1bb5e7875d6ee01ae0f9509ff15e370cfe4f024fb6d5c708b6ad62d20acf51`. Paths to the local fixture and binary are tokenized as `$WORK_URI`, `$WORK`, and `$LEAN_BIN`; ordering, elapsed times, payloads, PIDs, process statuses, and stderr remain.
- [`support/summarize.py`](support/summarize.py) asserts only the bounded observations above and writes [`support/summary.json`](support/summary.json), including binary/source/probe/transcript hashes. It passed on the retained 242-event transcript.
- Lean primary source at the pinned commit: [`Extra.lean` RPC schemas](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Extra.lean#L197-L254); [`RequestHandling.lean` outdated-session handling](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Rpc/RequestHandling.lean#L74-L95); [`Basic.lean` RPC reference store](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Rpc/Basic.lean#L65-L80).

## Revalidation

Run `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/probe.py`, then `python3 support/summarize.py`. The probe writes only inside its `support/work` and output files. Compare the binary SHA-256 before interpreting the result; a changed Lean build requires a new subject identity. The assertions check the old/new goals, stale-session errors, cancellation behavior, worker termination reply, late response collision, clean/forced process statuses, and the historical separate-URI control. Inspect the complete wire trace if an assertion changes; the checker does not establish unmeasured properties of Lean or an adapter.
