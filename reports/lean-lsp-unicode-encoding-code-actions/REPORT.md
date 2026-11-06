# Lean LSP Unicode Position Encoding Negotiation, Navigation, Multi-File Rename, and Code Actions

## Summary

Across Lean `v4.29.0` and `v4.30.0-rc2`, direct `lean --server` sessions omit `positionEncoding` in their `initialize` response regardless of whether the client offers `["utf-16", "utf-8"]`, `["utf-8", "utf-16"]`, `["utf-8"]` alone, `["utf-16"]` alone, or `["utf-32"]` alone. In every case, Lean uses the LSP 3.17 default **UTF-16** code-unit representation for emitted diagnostic ranges and incoming incremental `textDocument/didChange` ranges. On the Unicode line `#check ("😀é", unknownName)` (where `unknownName` starts at Unicode scalar column 15, UTF-16 column 16, and UTF-8 byte 19), both `v4.29.0` and `v4.30.0-rc2` emit the initial error at UTF-16 characters `16–27`. Sending an incremental `didChange` using UTF-16 characters `16–27` cleanly substitutes `Nat.zero`, whereas sending UTF-8 byte range `19–30` produces `unexpected end of input` and sending UTF-32 scalar range `15–26` leaves a corrupted `Unknown constant Nat.zeroe` diagnostic. The only `initialize` capability difference observed between `v4.29.0` and `v4.30.0-rc2` is that `v4.30.0-rc2` adds `experimental.rpcProvider.rpcWireFormat: "v1"`.

For navigation, completion, code actions, inlay hints, signature help, and rename across single-file and two-file Unicode fixtures on `v4.30.0-rc2`:
1. **Two-file rename and `LEAN_SRC_PATH`**: When both `LEAN_PATH` and `LEAN_SRC_PATH` point to the workspace root, renaming `αhelper` to `βhelper` from `Main.lean` returns `WorkspaceEdit.changes` spanning both `Helper.lean` (declaration at line 0, UTF-16 chars 4–11) and `Main.lean` (three uses at lines 1, 2, and 5); omitting `LEAN_SRC_PATH` causes Lean to treat `Helper.lean` as an `external:file:` module and return edits only for `Main.lean`.
2. **Code actions (`quickfix` vs. empty responses)**: An unknown-tactic or single-file unknown-identifier diagnostic with no matching importable module returns `[]` from `textDocument/codeAction`. When a compiled `Helper` module exports `αhelper`, querying `textDocument/codeAction` on unknown `αhelper` in `Action.lean` returns a nonempty `Import αhelper from Helper` quick fix carrying versioned `documentChanges` (inserting `import Helper\n` at `(0,0)` and replacing `(0,7)–(0,14)`), alongside an `Import all unambiguous unknown identifiers` source action.
3. **Completion, inlay hints, and signature help**: `textDocument/completion` and `completionItem/resolve` return item labels, types (`Nat → Nat`), and documentation without server-authored `textEdit`, `insertText`, or `additionalTextEdits`, requiring client-side word replacement if applied. `textDocument/inlayHint` returns an auto-bound implicit parameter insertion (` {α}` at line 6, character 17 with `textEdits`), and `textDocument/signatureHelp` returns `(x y : Nat) → Nat` at argument columns.

## Applicability

### Evaluated Toolchain Subjects and Shared versus Version-Specific Behavior

- **Lean 4 and Lake `v4.29.0`**: `leanprover/lean4` revision `98dc76e3c0a9b856c9b98726b713fb04fab16740`, `lean` executable SHA-256 `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`, `lake` executable SHA-256 `0e56506385ec20d56bffd7c031c4d48573ab5fdb74e5246ec8c45a220bebc68b`.
- **Lean 4 and Lake `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` executable SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`.
- **Shared Cross-Version Behavior**: In the cross-version Unicode encoding probe (`support/lean429-version-diff/`), both `v4.29.0` and `v4.30.0-rc2` omit `positionEncoding` from `initialize` responses under both `["utf-8"]` and `["utf-16"]` offers, emit identical UTF-16 `16–27` diagnostic ranges, fail with `unexpected end of input` on UTF-8 byte range `19–30` incremental edits, succeed with `Nat.zero` information diagnostics on UTF-16 range `16–27` incremental edits, and produce identical batch JSON messages and exit codes (`1` on original, `0` on patched).
- **Version Deltas**: In the `initialize` response capability object, `v4.30.0-rc2` advertises `experimental.rpcProvider.rpcWireFormat: "v1"`, whereas `v4.29.0` omits `rpcWireFormat` (`support/lean429-version-diff/comparison.json`). All other decoded `initialize` capability fields are identical across both versions.

### Subprobe Scope

1. **UTF-8-only vs. UTF-16-only offers on `v4.30.0-rc2`** (`support/utf8-only-unicode-lsp/`): Sequential `lean --server` sessions on `#check ("😀é", unknownName)` with coordinate oracle SHA-256 `7f7aac75610935a82f2382381ca0fbab519eaee9abb26767dcd90ab8cabe4cc7`.
2. **Lean `v4.29.0` vs. `v4.30.0-rc2` encoding-offer comparison** (`support/lean429-version-diff/`): Exact replay of the UTF-8-only and UTF-16-only sessions on `v4.29.0` compared byte-for-byte against retained `v4.30.0-rc2` baselines.
3. **UTF-32-only offer on `v4.30.0-rc2`** (`support/utf32-only-unicode-lsp/`): `general.positionEncodings: ["utf-32"]` with scalar-range `15–26` incremental `didChange` and oracle SHA-256 `c7bf9661e8ebef39410aa24e898949fc16614770cc2477ce601f2c14a68cc894`.
4. **Dual-encoding offer orders and 500-edit piecewise projection model** (`support/lean-lsp-projection-code-actions/`): Offering `['utf-16','utf-8']` vs. `['utf-8','utf-16']` on `Unicode.lean`, plus a 64-line, 500-edit piecewise source-map model with compare-and-swap (CAS), synthetic-segment rejection, and surrogate-pair guards.
5. **Single-file Unicode navigation, rename, semantic tokens, completion, and projection replay** (`support/lean-lsp-navigation-edit-operations/`): Testing `UnicodeOps.lean` (`α`, `hα`, `β`, `hβ`, `exa hβ`) and replaying returned edits through the piecewise projection model.
6. **Two-file Unicode rename, quick-fix import action, signature help, and inlay hints** (`support/lean-lsp-multifile-actions-hints/`): Testing `Helper.lean`, `Main.lean`, `Action.lean`, and `Completion.lean` with isolated branch application and fresh batch verification.

## Findings

### 1. Unicode Position Encoding Negotiation and Incremental `didChange` Boundaries (`v4.29.0` and `v4.30.0-rc2`)

Across `support/utf8-only-unicode-lsp/results.json`, `support/lean429-version-diff/results.json`, `support/lean429-version-diff/comparison.json`, and `support/utf32-only-unicode-lsp/results.json` (SHA-256 `15bbeb7d5ae7f7c0d7e5f9016363214d3ef02558fd280069134333a850ab05ac`), the fixture line `#check ("😀é", unknownName)` places `unknownName` after a 4-byte astral emoji (`U+1F600`, 2 UTF-16 code units) and `e` + combining acute accent (`U+0301`, 2 scalar code points, 2 UTF-16 code units, 3 UTF-8 bytes), yielding three distinct coordinate intervals for `unknownName`:
- **Unicode scalars (UTF-32)**: characters `15–26`
- **UTF-16 code units**: characters `16–27`
- **UTF-8 bytes**: bytes `19–30`

| Cell / Toolchain Pin | Client `positionEncodings` Offer | Server `positionEncoding` Reply | Initial `unknownName` Diagnostic Range | Incremental `didChange` Range Sent (`-> "Nat.zero"`) | Post-Edit Server Diagnostic | Server / Batch Exit |
| --- | --- | --- | --- | --- | --- | --- |
| `v4.30.0-rc2` UTF-8-only | `["utf-8"]` | absent (`null`) | line 0, chars 16–27 | line 0, chars 19–30 (UTF-8) | `unexpected end of input` | Server 0 |
| `v4.30.0-rc2` UTF-16-only | `["utf-16"]` | absent (`null`) | line 0, chars 16–27 | line 0, chars 16–27 (UTF-16) | none; `Nat.zero` info message | Server 0 |
| `v4.29.0` UTF-8-only | `["utf-8"]` | absent (`null`) | line 0, chars 16–27 | line 0, chars 19–30 (UTF-8) | `unexpected end of input` | Server 0 |
| `v4.29.0` UTF-16-only | `["utf-16"]` | absent (`null`) | line 0, chars 16–27 | line 0, chars 16–27 (UTF-16) | none; `Nat.zero` info message | Server 0 |
| `v4.30.0-rc2` UTF-32-only | `["utf-32"]` | absent (`null`) | line 0, chars 16–27 | line 0, chars 15–26 (UTF-32) | `Unknown constant Nat.zeroe` (chars 15–24) | Server 0 |
| Fresh batch original (`v4.29.0` & `v4.30.0-rc2`) | n/a | n/a | line 1, scalar cols 15–26 | n/a | `Unknown identifier unknownName` | Batch 1 |
| Fresh batch patched (`v4.29.0` & `v4.30.0-rc2`) | n/a | n/a | n/a | n/a | none; `Nat.zero` info message | Batch 0 |

Resource telemetry across the encoding runs confirmed bounded execution:
- **`v4.30.0-rc2` UTF-8/UTF-16 run** (`support/utf8-only-unicode-lsp/results.json`): Preflight 34.9060% reclaimable RAM, 18,846,994,432 B free disk; peak process-group RSS 196,880 KiB (UTF-8-only) and 115,824 KiB (UTF-16-only); batch peak RSS 98,016 KiB; maximum scratch 8,814 B and 15,934 B.
- **`v4.29.0` UTF-8/UTF-16 run** (`support/lean429-version-diff/results.json`): Preflight 36.5541% reclaimable RAM, 18,709,319,680 B free disk; peak process-group RSS 197,744 KiB (UTF-8-only) and 120,720 KiB (UTF-16-only); batch peak RSS 105,920 KiB; maximum scratch 9,332 B and 16,426 B; `$/lean/fileProgress` emitted 8 notifications on `v4.29.0` vs. 7 on `v4.30.0-rc2` for UTF-8-only.
- **`v4.30.0-rc2` UTF-32-only run** (`support/utf32-only-unicode-lsp/results.json`): Preflight 31.7915% reclaimable RAM, 18,597,441,536 B free disk; peak server group RSS 188,192 KiB; batch peak RSS 97,248 KiB; maximum scratch 8,272 B.

In `support/lean-lsp-projection-code-actions/lsp-transcript.json`, offering `['utf-16','utf-8']` and `['utf-8','utf-16']` on `support/lean-lsp-projection-code-actions/Unicode.lean` likewise omitted `positionEncoding` in both sessions and reported `unknownName` after `😀` at line 3, UTF-16 character 14 (scalar index 13, UTF-8 byte 16) (**Basis: execution**).

### 2. Single-File and Multi-File Navigation, Rename, Code Actions, Inlay Hints, and Signature Help

- **Single-file Unicode navigation and edit operations** (`support/lean-lsp-navigation-edit-operations/transcript.json`, `support/lean-lsp-navigation-edit-operations/UnicodeOps.lean`, `support/lean-lsp-navigation-edit-operations/Applied.lean`):

| Request | Observed response |
| --- | --- |
| Definition on `unicode_demo` in `#check` | One target at line 0, characters 8–20; origin selection line 3, characters 7–19. |
| References with declaration included | Two locations: declaration line 0, characters 8–20, and use line 3, characters 7–19. |
| Prepare rename | Use range line 3, characters 7–19. |
| Rename to `renamed_demo` | `WorkspaceEdit.changes` with those two same-file ranges and `newText="renamed_demo"`. |
| Semantic tokens full | 75 integers, decoding to 15 tokens under the advertised legend (marking keywords and variables, not the theorem name). |
| Completion at line 6, character 5 (`exa`) | 223 items, including `exact`. Resolving `exact` returned documentation and the label, without `textEdit`, `insertText`, or `additionalTextEdits`. |
| Code action over the observed unknown-tactic diagnostic | Empty list `[]`, despite advertised `quickfix`, `refactor`, and `source.organizeImports` kinds. |

- **Two-file Unicode rename, quick-fix import action, signature help, and inlay hints** (`support/lean-lsp-multifile-actions-hints/transcript.json`, `support/lean-lsp-multifile-actions-hints/applied-results.json`):

| Request | Retained Lean response |
| --- | --- |
| Rename `αhelper` to `βhelper` from `Main.lean` (`LEAN_PATH` and `LEAN_SRC_PATH` set) | `WorkspaceEdit.changes` for **two files**: one declaration edit in `Helper.lean` (line 0, characters 4–11) and three use edits in `Main.lean` (lines 1, 2, and 5). References included the same cross-file symbol set. |
| Quick fix on `Action.lean` unknown `αhelper` | Nonempty response, including `Import αhelper from Helper` with versioned `documentChanges` for `Action.lean` version 1. Its edits insert `import Helper\n` at file start `(0,0)` and replace the identifier range at line 0, characters 7–14. Also offered `Import all unambiguous unknown identifiers`. |
| Signature help in `add_three 1 2` | At two adjacent cursor columns, returned a signature labelled `(x y : Nat) → Nat`; other sampled columns returned `null`. |
| Inlay hint on `theorem auto_hint (x : α)` | Returned ` {α}` at line 6, character 17, with an insertion `textEdits` entry and tooltip explaining the auto-bound implicit parameter. |
| Completion on diagnostic `#check αhel` | One `αhelper` item; resolving it returned `Nat → Nat` detail and label but no `textEdit`, `insertText`, or `additionalTextEdits`. |

  Applying the two-file rename (and recompiling `Helper`), the versioned quick-fix edit on `Action.lean`, the inlay hint insertion on `Main.lean`, and a client-side word replacement `αhel -> αhelper` on `Completion.lean` in isolated branches (`support/lean-lsp-multifile-actions-hints/applied/`) all passed fresh batch `lean` verification with exit `0` (**Basis: execution**).

### 3. Piecewise Source-Map Stream and Projection Guards

In `support/lean-lsp-projection-code-actions/projection-stream.json` (`support/lean-lsp-projection-code-actions/projection_model.py`) and `support/lean-lsp-navigation-edit-operations/projection-replay.json` (`support/lean-lsp-navigation-edit-operations/projection_replay.py`):
- Interleaving 64 authored comment lines containing `α` and `😀` with synthetic header/obligation text and applying 500 seeded edits took ~12.7 ms total to rebuild piecewise maps and ~1.9 ms total to project 500 edits.
- At 20 checkpoints, the model rejected stale document versions, edits targeting synthetic ranges, edits crossing generated segment boundaries, and UTF-16 column offsets landing inside a surrogate pair.
- Replaying the two `WorkspaceEdit.changes` rename ranges from `UnicodeOps.lean` and the client completion fallback through the piecewise model produced exact byte agreement with `support/lean-lsp-navigation-edit-operations/Applied.lean` while rejecting prior-version edits (**Basis: execution of illustrative model**).

## Boundaries

- **Not examined**: Real editor client extensions (VS Code, Neovim) or Anneal's production Rust-to-Lean source projection and multi-file transaction manager.
- **Not examined**: Server-authored snippet placeholders (`$1`) or completion items returning `additionalTextEdits` (the tested Lean `completionItem/resolve` responses returned labels and documentation only).
- **Unknown**: Whether Lean's LSP server can be configured to negotiate `utf-8` or `utf-32` position encodings via any non-default launch flag or environment variable; in all tested `v4.29.0` and `v4.30.0-rc2` sessions, `positionEncoding` was omitted and defaulted to UTF-16.
- **Known not to apply**: Offering `["utf-8"]` or `["utf-32"]` in `initialize` `general.positionEncodings` does not switch `lean --server` out of UTF-16 coordinate units; sending UTF-8 byte offsets or UTF-32 scalar offsets in `textDocument/didChange` corrupts lines containing astral or combining Unicode characters.

## Evidence

- **Two-file rename, quick-fix code actions, signature help, and inlay hints**: [`support/lean-lsp-multifile-actions-hints/probe.py`](support/lean-lsp-multifile-actions-hints/probe.py), [`support/lean-lsp-multifile-actions-hints/apply_returns.py`](support/lean-lsp-multifile-actions-hints/apply_returns.py), [`support/lean-lsp-multifile-actions-hints/verify.py`](support/lean-lsp-multifile-actions-hints/verify.py), [`support/lean-lsp-multifile-actions-hints/transcript.json`](support/lean-lsp-multifile-actions-hints/transcript.json), [`support/lean-lsp-multifile-actions-hints/applied-results.json`](support/lean-lsp-multifile-actions-hints/applied-results.json), [`support/lean-lsp-multifile-actions-hints/fixture`](support/lean-lsp-multifile-actions-hints/fixture), and [`support/lean-lsp-multifile-actions-hints/applied`](support/lean-lsp-multifile-actions-hints/applied).
- **Single-file Unicode navigation and rename**: [`support/lean-lsp-navigation-edit-operations/UnicodeOps.lean`](support/lean-lsp-navigation-edit-operations/UnicodeOps.lean), [`support/lean-lsp-navigation-edit-operations/Applied.lean`](support/lean-lsp-navigation-edit-operations/Applied.lean), [`support/lean-lsp-navigation-edit-operations/probe.py`](support/lean-lsp-navigation-edit-operations/probe.py), [`support/lean-lsp-navigation-edit-operations/projection_replay.py`](support/lean-lsp-navigation-edit-operations/projection_replay.py), [`support/lean-lsp-navigation-edit-operations/verify.py`](support/lean-lsp-navigation-edit-operations/verify.py), [`support/lean-lsp-navigation-edit-operations/transcript.json`](support/lean-lsp-navigation-edit-operations/transcript.json), and [`support/lean-lsp-navigation-edit-operations/projection-replay.json`](support/lean-lsp-navigation-edit-operations/projection-replay.json).
- **Dual-encoding offers and 500-edit piecewise projection model**: [`support/lean-lsp-projection-code-actions/Unicode.lean`](support/lean-lsp-projection-code-actions/Unicode.lean), [`support/lean-lsp-projection-code-actions/lsp_probe.py`](support/lean-lsp-projection-code-actions/lsp_probe.py), [`support/lean-lsp-projection-code-actions/lsp-transcript.json`](support/lean-lsp-projection-code-actions/lsp-transcript.json), [`support/lean-lsp-projection-code-actions/projection_model.py`](support/lean-lsp-projection-code-actions/projection_model.py), [`support/lean-lsp-projection-code-actions/projection-stream.json`](support/lean-lsp-projection-code-actions/projection-stream.json), and [`support/lean-lsp-projection-code-actions/verify.py`](support/lean-lsp-projection-code-actions/verify.py).
- **UTF-8-only vs. UTF-16-only (`v4.30.0-rc2`)**: [`support/utf8-only-unicode-lsp/probe.py`](support/utf8-only-unicode-lsp/probe.py), [`support/utf8-only-unicode-lsp/oracle.py`](support/utf8-only-unicode-lsp/oracle.py), [`support/utf8-only-unicode-lsp/oracle.json`](support/utf8-only-unicode-lsp/oracle.json), [`support/utf8-only-unicode-lsp/results.json`](support/utf8-only-unicode-lsp/results.json), [`support/utf8-only-unicode-lsp/comparison.json`](support/utf8-only-unicode-lsp/comparison.json), [`support/utf8-only-unicode-lsp/check.py`](support/utf8-only-unicode-lsp/check.py), [`support/utf8-only-unicode-lsp/fixture`](support/utf8-only-unicode-lsp/fixture), and [`support/utf8-only-unicode-lsp/raw`](support/utf8-only-unicode-lsp/raw).
- **Lean `v4.29.0` vs. `v4.30.0-rc2` version diff**: [`support/lean429-version-diff/probe.py`](support/lean429-version-diff/probe.py), [`support/lean429-version-diff/oracle.py`](support/lean429-version-diff/oracle.py), [`support/lean429-version-diff/oracle.json`](support/lean429-version-diff/oracle.json), [`support/lean429-version-diff/results.json`](support/lean429-version-diff/results.json), [`support/lean429-version-diff/baseline-v430-results.json`](support/lean429-version-diff/baseline-v430-results.json), [`support/lean429-version-diff/baseline-v430-batch-original.stdout`](support/lean429-version-diff/baseline-v430-batch-original.stdout), [`support/lean429-version-diff/baseline-v430-batch-patched.stdout`](support/lean429-version-diff/baseline-v430-batch-patched.stdout), [`support/lean429-version-diff/comparison.json`](support/lean429-version-diff/comparison.json), [`support/lean429-version-diff/check.py`](support/lean429-version-diff/check.py), [`support/lean429-version-diff/fixture`](support/lean429-version-diff/fixture), and [`support/lean429-version-diff/raw`](support/lean429-version-diff/raw).
- **UTF-32-only (`v4.30.0-rc2`)**: [`support/utf32-only-unicode-lsp/probe.py`](support/utf32-only-unicode-lsp/probe.py), [`support/utf32-only-unicode-lsp/oracle.py`](support/utf32-only-unicode-lsp/oracle.py), [`support/utf32-only-unicode-lsp/oracle.json`](support/utf32-only-unicode-lsp/oracle.json), [`support/utf32-only-unicode-lsp/results.json`](support/utf32-only-unicode-lsp/results.json), [`support/utf32-only-unicode-lsp/comparison.json`](support/utf32-only-unicode-lsp/comparison.json), [`support/utf32-only-unicode-lsp/check.py`](support/utf32-only-unicode-lsp/check.py), [`support/utf32-only-unicode-lsp/fixture`](support/utf32-only-unicode-lsp/fixture), and [`support/utf32-only-unicode-lsp/raw`](support/utf32-only-unicode-lsp/raw).

## Revalidation

Run all six offline verification scripts to validate wire frames, coordinate ranges, applied edits, cross-version comparisons, and piecewise source-map streams without starting Lean:

```sh
python3 support/lean-lsp-multifile-actions-hints/verify.py
python3 support/lean-lsp-navigation-edit-operations/verify.py
python3 support/lean-lsp-projection-code-actions/verify.py
python3 -B support/utf8-only-unicode-lsp/check.py
python3 -B support/lean429-version-diff/check.py
python3 -B support/utf32-only-unicode-lsp/check.py
```

To reacquire live server transcripts, run the corresponding `probe.py` / `lsp_probe.py` in a clean copy of the subprobe directory with the pinned `v4.29.0` and `v4.30.0-rc2` `lean` binaries.
