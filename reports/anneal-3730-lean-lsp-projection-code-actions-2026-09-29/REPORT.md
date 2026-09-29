# Lean LSP position, completion, code-action, and illustrative projection controls

## Direct Lean LSP observation

This component probe runs pinned Lean 4.30.0-rc2 `lean --server` twice against the same Unicode proof file. The two `initialize` requests offered `['utf-16','utf-8']` and `['utf-8','utf-16']` respectively. In both sessions, the server omitted `positionEncoding` in its returned capabilities. The retained direct diagnostic for `unknownName` after `😀` begins at line 3, character 14: the Python scalar index is 13 and UTF-8 byte offset is 16, while UTF-16 column 14 matches the LSP range. The observed default is thus consistent with UTF-16; the server did not advertise a negotiated alternative in either session. The protocol transcript records the full capability objects and messages.

The server advertised completion with resolution and code actions with `quickfix`, `refactor`, and `source.organizeImports` kinds. Completion at `exa` returned 223 items in each run, including `exact`, `exact?`, and `exact_mod_cast`. A `quickfix` code-action request using the observed unknown-identifier diagnostic returned `[]` in each run. An `hα` hover returned its local type and range line 1, characters 8–10. The empty code-action result is a result for this one diagnostic and request context, not a claim that Lean never produces code actions. Neither completion item was resolved nor applied. There was no editor adapter, Rust buffer, or Anneal UI in the experiment.

`support/Unicode.lean` is the exact source; `support/lsp_probe.py` records complete JSON-RPC requests and responses in `support/lsp-transcript.json`. The transcript includes diagnostic publications, which can arrive incrementally before the `waitForDiagnostics` response. A retained response of `{}` from that wait method does not itself carry diagnostics; the harness reads `textDocument/publishDiagnostics` notifications. Both server processes exited 0.

## Illustrative source-map stream

`support/projection_model.py` is an explicit **model**, not an Anneal parser or map. It interleaves 64 authored comment lines containing `α` and `😀` with synthetic header/obligation text. It applies 500 seeded edits within one authored segment, rebuilding the piecewise map each time. At 20 checkpoints it rejects a stale version, a synthetic-range edit, and an edit crossing generated segments. The retained stream stores per-step source/generated hashes, generated ranges, replacements, and rejection reasons. A small UTF-16 conversion corpus rejects a column inside a surrogate pair. On this run, the model spent about 12.7 ms total rebuilding maps and 1.9 ms total projecting 500 edits; those timings are for the tiny Python model and do not estimate Anneal latency or an incremental map implementation.

## Issue coverage and exact residuals

| [#3731](https://github.com/google/zerocopy/issues/3731) rows | Added evidence | Still required |
| --- | --- | --- |
| I025/I062 | Direct Lean diagnostic with astral Unicode and two offered encoding orders; exact UTF-16 column distinction. | Negotiated round trips through a real Rust-to-Lean projection host and representative editor clients. |
| I026/I029/I032 | 64-line, 500-edit illustrative piecewise map with CAS, synthetic/cross-segment rejection and measured rebuild/projection time. | Actual Anneal annotation grammar, source map, shifting multi-range patches, and realistic latency/fuzz corpus. |
| I027/I028 | No new direct evidence. | One-to-many/many-to-one provenance and identical batch/live generator output. |
| I030 | Direct Lean completion and empty quick-fix response on a Unicode proof. | Real mapped completion insertion/snippet/additional edits, resolved code actions, imports, and synthetic crossing behavior. |
| I031 | Direct diagnostic range and hover; generated model segments carry explicit ownership. | End-to-end diagnostic responsibility/ownership across generated scaffolding, models, imports and ambiguous spans. |
| I059/I060 | Direct hover range only. | Mapped navigation, semantic tokens, rename and cross-file workspace edits with Rust symbols protected. |
| I061/I063 | No new direct evidence. | InfoView/RPC through a Rust-hosted position and real editor save/build/format/watch loops. |

The related [#3730](https://github.com/google/zerocopy/issues/3730) projection and editor crosswalk rows gain bounded component evidence only. No issue row is claimed complete from this package.

## Reproduce and verify

With the identified Lean binary already installed, run from this package directory:

```sh
python3 support/lsp_probe.py
python3 support/projection_model.py
python3 support/verify.py
```

The LSP probe creates two narrow scratch directories under this conversation's Meta/Data directory. `support/verify.py` validates retained observations without starting a server. Rerunning the model preserves seeded semantic results; wall-clock timings may differ. Rerunning Lean may change notification count/order while preserving the asserted response and range facts at this pin.
