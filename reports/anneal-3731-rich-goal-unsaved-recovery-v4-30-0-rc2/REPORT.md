# Plain and rich Lean goals across unsaved nested proof errors

## Summary

In one direct Lean 4.30.0-rc2 server, `$/lean/plainGoal` and `Lean.Widget.getInteractiveGoals` agreed at 24 matched cursor positions across valid, syntax-error, unknown-tactic, and recovered versions of an unsaved nested proof. They returned a goal at 17 pairs, an empty goal list at two, and JSON `null` at five. At every nonempty pair, the rendered rich goal target matched the plain target after stripping RPC presentation tags. The syntax error and unknown tactic had different local availability patterns, even though both failed fresh batch compilation. This supplies bounded evidence for #3731 I043/I046 and #3730 C02, plus one live-session observation relevant to I044; it does not implement Anneal's exact-version query protocol.

## Applicability

The probe ran the pinned arm64 macOS release binary `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (binary SHA-256 in `REPORT.json`) through direct `lean --server` and `lean --json`, with `LEAN_NUM_THREADS=1`, no Lake project, no plugins, and `import Lean` only. One server and one URI held the four successive LSP document versions. Its disk file remained the original valid source; versions 2 and 3 existed only in `didChange` text. The same RPC session was used for every rich query after one initial `rpc/connect`.

This extends the [nested unsaved recovery grid](../anneal-3730-nested-unsaved-recovery-grid-v4-30-0-rc2/REPORT.md), which used `plainGoal` only. It tests the rich goal procedure's local selection behavior, not the lifecycle or dereference semantics of its opaque references. The cursor coordinates below are zero-based UTF-16 LSP coordinates; all fixture text is ASCII.

## Findings

The six fixed positions were outer `have` `(3,2)`, inner tactic start `(4,4)`, inner tactic body `(4,8)`, inner tactic end `(4,24)`, next outer tactic `(5,2)`, and a later theorem's tactic `(8,2)`. The valid source uses `simpa using h`; version 2 replaces it with `)`; version 3 replaces it with `this_is_not_a_tactic`; version 4 restores the original source. Column 24 lies beyond the shorter syntax-error line; its result is a sampled coordinate, not a token position in that version.

| Version | Fresh batch | Outer `have` | Inner start/body/end | Next outer tactic | Later theorem |
| --- | --- | --- | --- | --- | --- |
| 1 valid | exit 0 | goal | goal / goal / no goals | goal | goal |
| 2 syntax error | exit 1 | goal | null / null / null | null | goal |
| 3 unknown tactic | exit 1 | goal | goal / goal / goal | null | goal |
| 4 recovered | same source as valid | goal | goal / goal / no goals | goal | goal |

Both query methods gave the same category at every cell. At all 17 goal cells, both returned one goal and the rich target's tagged display text equaled the target after `⊢` in the plain goal. The valid inner body target was `n = 0`, while the inner start target was `n + 0 = 0`; the same distinction returned after recovery. The later theorem continued to expose `⊢ True` under both errors. **Basis: execution**, `support/results.json` cases and all 48 request/reply pairs in `support/transcript.json`; `support/check.py` checks the categories and target text.

The server's last diagnostics notification for versions 1–4 contained 0, 3, 3, and 0 diagnostics respectively. Version 2 reported the unexpected `)` token and unsolved goals; version 3 reported an unknown tactic and unsolved goals. Fresh `lean --json` controls exited 0 for valid source and 1 for each erroneous source. `textDocument/waitForDiagnostics` returned `{}` for every version, including those with errors; readiness of this request is not whole-file success. The server shut down with exit 0. **Basis: execution**, batch output and ordered diagnostics notifications in the retained files.

One `rpc/connect` session served all 24 rich calls through three `didChange` notifications without a protocol error. That is an observed session lifetime for this fixture. It does not make any retained `ctx`, `info`, or `mvarId` reference safe to reuse after an edit. The captured `ctx.p` handles changed across versions, while some `mvarId` strings repeated; neither pattern establishes cross-edit reference validity or semantic identity. **Basis: execution** for the request count and recorded values; **derived** for the client implication that semantic goal comparison must ignore presentation-reference numbers.

## Boundaries

- **Not examined:** rich RPC object dereference, release, expiration, worker restart, cancellation, late replies, simultaneous requests, or exact historical versions. The sequential `waitForDiagnostics` and query order does not challenge an exact-version fence.
- **Not examined:** multiple files, imports from generated modules, tactic macros, Unicode positions, broad whitespace/comment positions, projected Rust source, MCP transport, or an Anneal adapter.
- **Not established:** that plain and rich APIs agree on hypothesis formatting, widget actions, diff annotations, reference identity, or every possible goal count. The checker compares availability, number of goals, and target display text in these 24 cells.
- **Not established:** that a locally available goal proves the whole file. Both erroneous variants failed batch compilation; their later theorem goal remained queryable.

## Evidence

- `support/probe.py` (SHA-256 `f5fcc6eadabe08bf54463bf3b98d15840dc2f77dc5688e0dcf00f76235839671`) creates the tiny fixture and batch controls, sends every JSON-RPC message, and writes tokenized raw evidence.
- `support/transcript.json` (SHA-256 `608458932c47f5a054b4a6157def570b2f238e1364580596f5ea5445ae468e97`) retains ordered sends, replies, diagnostics, batch output, and server exit. Local absolute paths are replaced with `$HERE`, `$HERE_URI`, and `$LEAN_BIN`.
- `support/results.json` (SHA-256 `561c2246041961e086e66f67f5776d83659a4a4a96579be032e147a5153383d9`) indexes the same 24 query pairs by version and cursor name. The generated `support/Nested.lean` and `support/Batch-*.lean` preserve exact source bytes.
- `support/check.py` (SHA-256 `5b80334f937edf8013eb9c7505800b08ecce0b1feb04dd58d0e21675005e3174`) validates the retained evidence offline. Its observed output was `{"diagnostics": {"1": 0, "2": 3, "3": 3, "4": 0}, "outcomes": {"empty": 2, "null": 5, "target": 17}, "pairs": 24, "server_exit": 0}`.

## Revalidation

Run `python3 support/check.py` for an offline check. To repeat the experiment, set `LEAN_BIN` to the absolute path of the identified binary, run `python3 support/probe.py`, then rerun the checker. Compare the binary SHA-256 and source hashes before treating a replay as the same subject. Changed query categories, target text, or diagnostics should be investigated in the ordered transcript; this fixture alone cannot establish behavior for a different Lean revision or an Anneal-produced document.
