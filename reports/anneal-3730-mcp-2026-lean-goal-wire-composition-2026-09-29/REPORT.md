# Current-wire task model backed by a real Lean goal query

## Question and exact subject

The [2026 MCP task wire-control report](../anneal-3730-mcp-2026-task-wire-controls-2026-09-29/REPORT.md) checked the contemporary discovery/version/Tasks shapes with fixture text, while the earlier [Lean-backed toy lifecycle](../anneal-3730-mcp-shaped-async-task-lifecycle-2026-09-29/REPORT.md) queried real Lean under invented task methods. This report composes those two **local test ideas**: a standard-library stdio bridge shaped around 2026-07-28 `server/discover`, per-request version/capability metadata, `tools/call`, `tasks/get`, and `tasks/cancel` invokes an actual pinned Lean 4.30.0-rc2 LSP goal query. The core version and Tasks extension are described in the cited prior report; the extension was draft on this observation date. This bridge remains a model, not an MCP SDK, existing Lean adapter, conformant server, or Anneal service.

The inputs are `Proof.lean`, which proves `True` by `trivial`, and `Slow.lean`, whose elaboration pauses for 1.5 seconds before the same proof. Both carry `trace_state` and `#print axioms target`. The bridge checks the exact source SHA-256 before accepting a call, creates a task handle when the test client opts into `io.modelcontextprotocol/tasks`, then starts Lean only after a test-only release gate. Without opt-in, it runs the same Lean goal synchronously and returns `resultType: "complete"`. Separate fresh `lean --json` commands check both proofs. All programs were already cached; no install or network dependency download occurred.

## Observations

| Control | Retained result |
| --- | --- |
| Version and source identity | Unsupported version returned `-32022`; discovery advertised the Tasks extension. A wrong expected source SHA-256 returned `-32602` before Lean ran. |
| Synchronous fallback | A no-Tasks `tools/call` returned `resultType: "complete"`, text `⊢ True` from real Lean LSP, and the pinned source digest. |
| Task path | A task-capable call returned `resultType: "task"`; immediate `tasks/get` was `working`. After test release, polling returned `completed` with nested `resultType: "complete"` and text `⊢ True`. The obsolete `tasks/result` method returned `-32601`. |
| Cooperative cancellation before start | `tasks/cancel` acknowledged intent; after release, the task became `cancelled`. The bridge's query count remained two: synchronous and completed-task calls. No third Lean query was started for that cancelled task. |
| Cancellation during slow Lean work | The client saw `Lean waitForDiagnostics in flight`, then sent `tasks/cancel`. The bridge forwarded `$/cancelRequest` to Lean; Lean answered that request with `-32800`, later returned `⊢ True` to a goal query, and the bridge suppressed the task result as `cancelled`. The run shows processed request cancellation, not early interruption of elaboration. |
| Fresh checkers | `lean --json` exited 0 for both Proof and Slow files, traced `⊢ True`, and reported that `target` does not depend on any axioms. |

The retained run has 132 raw client/server transcript entries; the count varies with status polling. Three actual Lean queries returned one `⊢ True` goal: synchronous, completed task and slow in-flight cancellation. The bridge published only the first two results. Each query had a Lean watchdog and file worker in its pre-shutdown process snapshot; all three tracked process sets were absent after orderly shutdown. The snapshots are process-lifetime checks, not peak memory measurements. Preflight found 46% free system memory and 53,170,761,728 free disk bytes. The bridge used one Lean query at a time, with no large imported project.

## Decision relevance and limits

This confirms that the **model's** current-shaped task envelope can carry a real Lean goal result and source digest, that cancel-before-start can avoid an unneeded Lean query, and that a task cancellation acknowledged during a running Lean wait can be forwarded as a real Lean `$/cancelRequest`, receive `-32800`, and suppress the eventual task result while a subsequent Lean goal query still succeeds. It does not establish interoperability with any existing MCP client or SDK, protocol conformance, a persistent task store, task ownership across clients, reconnection, subscription/backpressure behavior, early interruption or resource savings during Lean elaboration, or Anneal workspace generation and verification. The bridge's `test/release` and `test/stats` are test-only methods, and its TTL/error policy is local. The fresh batch checks prove only these tiny Lean theorems, not Rust→Lean correspondence.

For #3731 I065/I071 and #3730 G03, this is additional **partial component evidence**. G03 still lacks a real existing adapter/client and long-running Anneal task lifecycle. L09/I072 also remain not run because no existing Lean MCP adapter was exercised. The separate wire-control report already tested legacy fallback and expiry; this report does not repeat those cells.

## Evidence and replay

`support/Proof.lean` and `support/Slow.lean` are the exact inputs. `support/bridge.py` implements the local test bridge and direct Lean LSP worker; `support/probe.py` drives the raw stdio sequence and fresh batch oracle. `support/results.json` records source/tool/script hashes, preflight, full transcript, task responses, three Lean goal/cleanup records and both fresh batch outputs. `support/check.py` validates all retained identities and outcomes offline; it passed. `reference._load_report` validated this package.

Run `python3 support/check.py` for retained evidence. To repeat with the same cached pin, run `python3 support/probe.py` in a copy of this package; it rewrites only `support/results.json`. Compare version/error branches, task result shape, goal text, source identity and process cleanup. The reported memory preflight, process IDs, timing and raw diagnostics may vary.
