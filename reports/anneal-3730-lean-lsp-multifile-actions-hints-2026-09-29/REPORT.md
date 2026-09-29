# Lean LSP two-file rename, nonempty action, signature and inlay edits

## Direct protocol fixture

Pinned Lean 4.30.0-rc2 compiled `Helper.lean` to `.olean` and `.ilean`, then a single `lean --server` session opened four small Unicode files. `LEAN_PATH` and `LEAN_SRC_PATH` both pointed to the scratch source root. The source-path setting mattered: in a discarded preliminary run without it, Lean represented the open `Helper.lean` as an `external:file:` module and rename returned only `Main.lean` edits. With it, the retained result uses module `Helper` and includes the declaration file. The complete initialization capabilities, requests, responses, diagnostics, and versions are in `support/transcript.json`.

| Request | Retained Lean response |
| --- | --- |
| Rename `αhelper` to `βhelper` from `Main.lean` | `WorkspaceEdit.changes` for **two files**: one declaration edit in `Helper.lean` (line 0, characters 4–11) and three use edits in `Main.lean` (lines 1, 2, and 5). References included the same cross-file symbol set. |
| Quick fix on `Action.lean` unknown `αhelper` | Nonempty response, including `Import αhelper from Helper` with versioned `documentChanges` for `Action.lean` version 1. Its edits insert `import Helper\n` at file start and replace the identifier range at line 0, characters 7–14. A separate `Import all unambiguous unknown identifiers` source action was also offered. |
| Signature help in `add_three 1 2` | At two adjacent cursor columns, returned a signature labelled `(x y : Nat) → Nat`; other sampled columns returned `null`. |
| Inlay hint on `theorem auto_hint (x : α)` | Returned ` {α}` at line 6, character 17, with an insertion `textEdits` entry and tooltip explaining the auto-bound implicit parameter. |
| Completion on diagnostic `#check αhel` | One `αhelper` item; resolving it returned `Nat → Nat` detail and label but no `textEdit`, `insertText`, or `additionalTextEdits`. |

`support/apply_returns.py` applied returned edits in isolated branches. The two-file rename branch recompiled the renamed helper and batch-checked `Main.lean`; the quick-fix branch batch-checked `Action.lean`; the inlay branch applied the returned insertion and batch-checked `Main.lean`. All returned-edit branches exited 0. A fourth branch made an explicitly **client-selected word replacement** `αhel` → `αhelper` from the completion label and batch-checked `Completion.lean`; Lean did not return that edit range. The resulting sources and batch results are retained under `support/applied/` and `support/applied-results.json`.

The action's `TextDocumentEdit` carried version 1. The replay rejected a simulated version-2 application before changing text. Rename used `WorkspaceEdit.changes`, which carried no document version; the replay checked both source preimage hashes before applying either file and rejected a simulated intervening edit as one transaction. Those guards are harness policy, not behavior demonstrated by a real editor. They do not prove that Lean or an editor will make multi-file saves atomic.

## Issue coverage and residuals

This package adds direct Lean component evidence for [#3731](https://github.com/google/zerocopy/issues/3731) I030 and I059–I063, with bounded relevance to [#3730](https://github.com/google/zerocopy/issues/3730) editor/projection crosswalk rows.

| Rows | Added evidence | Still required |
| --- | --- | --- |
| I030 | Nonempty versioned quick-fix edits; source action; resolved completion with no edit fields; isolated batch checks. | Real projection of action/completion snippets, auxiliary imports, ambiguous generated regions, and editor application policy. |
| I059 | Cross-file reference/rename symbol set plus signature and inlay responses. | Rust-hosted mapped hover/navigation/semantic tokens and unavailable imported-source behavior. |
| I060 | Two-file Lean rename `WorkspaceEdit` applied and batch checked; source-hash guard illustrates stale rejection. | Cross-file projected Lean-to-Rust routing, editor transaction semantics, protected Rust symbol names and partial client capabilities. |
| I061 | No InfoView or RPC flow. | Real widget/RPC/hyperlink path from a Rust-hosted proof position through reconnect. |
| I062 | UTF-16 ranges, advertised client capabilities and versioned code action. | Multiple real client encodings, sync modes, and feature fallback; server omitted an explicit `positionEncoding` choice. |
| I063 | Fresh batch check after four isolated edits. | Autosave/format/watch/build loops with dirty-buffer and duplicate-work controls in a real editor. |

No Anneal editor adapter, source map, UI, scheduler, or product acceptance path was exercised.

## Replay and verification

With the pinned Lean binary already present, run from the package directory:

```sh
python3 support/probe.py --work /Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r18-protocol-replay-new
python3 support/apply_returns.py --work /Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r18-apply-replay-new
python3 support/verify.py
```

Both `--work` directories must be absent and owned. The first command replaces the transcript; the second replaces batch-checked source snapshots and results. The verifier checks retained protocol responses, exact edit ranges, source hashes, and recorded batch exits without launching a server. Notification order may vary between runs.
