# Goal queries around partial and failed Lean elaboration

## Summary

In four direct Lean 4.30.0-rc2 fixtures, a failed middle declaration did not prevent the server from exposing tactic goals in valid declarations both before and after it. Batch compilation still exited 1 in every case. The failure-position goal depended on the error: unfinished proof and unknown tactic yielded `⊢ True`; deterministic heartbeat timeout and recoverable syntax error yielded JSON `null`. `#print axioms after` reported that the later `after` theorem used no axioms in all four files. These local observations make reachable goal state useful for repair, while the diagnostics and batch exit code retain the whole-file failure.

At the same valid `trivial` tactic, column 2 returned the input goal while column 4 and the end of the line returned no goals in this fixture. An edit from a failing `True` theorem to a failing `False` theorem produced `⊢ False` on an immediate query and on later queries carrying either document version. Neither the goal payload nor the version field establishes whole-module acceptance or an exact historical snapshot.

## Applicability

This is execution against the pinned arm64 macOS release binary for `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The probe invokes direct `lean --json` and direct `lean --server`, with `LEAN_NUM_THREADS=1`, one watchdog and one open file at a time, no Lake project, no imports beyond `Lean`, no plugins, and generated tiny files. The server was shut down cleanly with exit code 0. Binary and fixture hashes are preserved in `support/summary.json` and the raw transcript.

This report addresses the narrow execution gap in [#3731 I046](https://github.com/google/zerocopy/issues/3731): valid proofs before and after unfinished, unknown-tactic, timeout, and syntax-error declarations. It also supplies bounded position/readiness observations for I041–I043. It does not test Anneal, its MCP server, or generated Aeneas modules.

## Findings

### Four failure classes with later valid declarations

Each file has `theorem before : True := by trivial`, `#print axioms before`, one failing `broken` theorem, then `theorem after : True := by trivial` and `#print axioms after`. The exact generated source and SHA-256 values are in `support/work/` and `support/summary.json`.

| Middle declaration | Batch result | Goal at failing tactic/token | Goal at start of `before` and `after` |
| --- | --- | --- | --- |
| `exact ?_` | Placeholder and unsolved-goal errors | `⊢ True` | `⊢ True` each |
| `tactic_that_does_not_exist` | Unknown tactic and unsolved-goal errors | `⊢ True` | `⊢ True` each |
| `set_option maxHeartbeats 1` with `omega` | Deterministic timeout at elaborator | JSON `null` | `⊢ True` each |
| Unexpected `)` in tactic block | Parse error and unsolved-goal errors | JSON `null` | `⊢ True` each |

Batch returned code 1 in all four cases. The final nonempty LSP diagnostics for each file contained the same respective error class and both axiom reports. The two `#print axioms` information messages said `before` and `after` do not depend on any axioms; the latter appeared after the middle error in source order. This directly verifies that these two simple declarations remained available to the command elaborator in this fixture. It does **not** make the erroneous module a successful artifact or establish acceptance of an external obligation. **Basis: execution**, raw `batch`, `case`, and diagnostic notification events in [`support/transcript.json`](support/transcript.json); checked by [`support/summarize.py`](support/summarize.py).

The timeout was generated deterministically by Lean's `maxHeartbeats 1`, not by killing a process or waiting for wall-clock time. The syntax case used one recoverable unexpected token in a tactic block; a different delimiter error can have a larger parse recovery span. At the failed position, `null` was a successful JSON-RPC result with no available goal, not a server transport error. **Basis: execution**.

### Position and edit/readiness behavior

For both valid `trivial` lines in all four files, zero-based column 2 produced `⊢ True`, while column 4 and end-of-line produced an empty `goals` array. For the middle failure, the recorded position was column 4 on the failing tactic/token. These exact coordinates matter: a query returning no goals at column 4 in a valid proof should not be read as proof that no input goal existed. The test covers only these points, not a complete tactic-position grid. **Basis: execution**, `case.positions` and `case.samples`.

An additional same-URI edit opened the unfinished `broken : True` source as version 1, queried its `⊢ True` goal, then sent version 2 with `broken : False` and an unknown tactic. The goal request sent after `didChange` but **before** `waitForDiagnostics(version=2)` replied `⊢ False` in this run. The version-2 wait succeeded, and a later wait requesting version 1 also succeeded. Later `plainGoal` requests with extra `textDocument.version` values 1 and 2 both returned `⊢ False`. The version-2 diagnostic notification included `unknown tactic` and `⊢ False`. This is a concrete example of latest-current state being accessible, not an exact-version query: the protocol does not bind `plainGoal` to that supplied extra version key. **Basis: execution**, `edit_case` and the surrounding wire order; the related version-field limitation was also observed in the earlier [goal/edit race report](../anneal-3730-lean-protocol-races-v4-30-0-rc2/REPORT.md).

The four batch measurements were 1848.5, 584.7, 584.5, and 582.7 ms in that order; the first includes cold startup effects. These timings are retained for replay comparison only and are not a performance comparison among error classes. **Basis: execution**.

## Boundaries

- **Not examined:** multiple simultaneous errors that alter parser recovery; nested tactics, combinators, macros, EOF, whitespace grid, and rich interactive RPC goals. I043 remains open beyond the three valid-tactic columns sampled here.
- **Not examined:** wall-clock cancellation/timeouts, asynchronous tasks, slow imports, permanently broken imports, worker crashes, and resource exhaustion. The heartbeat timeout is only one Lean elaborator failure mode.
- **Not established:** that the full file is valid because `after` exists or its local proof is axiom-free. Every batch run exited 1, and diagnostics reported errors. A future adapter must keep local goal availability separate from whole-module proof verification.
- **Not established:** a universal order between edit processing and a goal requested immediately afterward. The immediate request returned V2's `⊢ False` in this one execution; no gated interleaving or repetition was added here. The prior race report has the complementary delayed-old-response fixture.
- **Not examined:** actual Anneal source generation, accepted proposition identity, imported artifacts, or MCP envelopes. These results are direct Lean behavior only.

## Evidence

- [`support/probe.py`](support/probe.py), SHA-256 `1a52598fa127dbdc06ca021a8b954e03c320419c3c8575a98f66116913a5f6a9`, generates all five sources, runs batch controls, and records every direct-server JSON-RPC message.
- [`support/transcript.json`](support/transcript.json), SHA-256 `af3249d8ddf9da06628b00fba72d13eb0b08827766c98606c9f65b69f899ba10`, contains 344 ordered events, raw batch stdout/stderr/exit codes, all server diagnostics and goal replies, source hashes, elapsed times, and clean shutdown. Absolute local paths are tokenized as `$WORK_URI`, `$WORK`, and `$LEAN_BIN`.
- [`support/summarize.py`](support/summarize.py) asserts the four failure classes, before/after axiom reports, LSP diagnostics, position-specific goals, edit response, and exit status; its passing digest is [`support/summary.json`](support/summary.json).
- Fixture files are preserved under [`support/work`](support/work). Their five source SHA-256 values are in the summary. The direct source of the issue requirement is [#3731 I046](https://github.com/google/zerocopy/issues/3731), as transcribed in the corpus investigation matrix.

## Revalidation

Run `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/probe.py`, then `python3 support/summarize.py`. Both scripts use only Python's standard library; the probe writes its fixtures and output inside this package. Compare binary and source hashes before interpreting a replay. A changed error message, goal-position mapping, or edit ordering should be reviewed in the full transcript, then recorded as a new subject-specific observation rather than generalized from this one run.
