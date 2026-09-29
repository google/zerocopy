# Lean LSP navigation and edit operations on a Unicode proof

## Direct component observation

Pinned Lean 4.30.0-rc2 `lean --server` opened `support/UnicodeOps.lean` in one scratch workspace. The source has Greek identifiers (`α`, `hα`, `β`, `hβ`), a theorem reference, and the incomplete tactic `exa hβ`. The client advertised UTF-16 then UTF-8. The server did not return an explicit `positionEncoding`, and this package uses UTF-16 columns for every decoded range. The complete JSON-RPC exchange and initialization capabilities are retained in `support/transcript.json`.

| Request | Observed response |
| --- | --- |
| Definition on `unicode_demo` in `#check` | One target at line 0, characters 8–20; origin selection line 3, characters 7–19. |
| References with declaration included | Two locations: declaration line 0, characters 8–20, and use line 3, characters 7–19. |
| Prepare rename | Use range line 3, characters 7–19. |
| Rename to `renamed_demo` | `WorkspaceEdit.changes` with those two same-file ranges and `newText="renamed_demo"`. |
| Semantic tokens full | 75 integers, decoding to 15 tokens under the advertised legend. This response marked keywords and variables; it did not mark the theorem name as a function token in this tiny file. |
| Completion at line 6, character 5 (`exa`) | 223 items, including `exact`. Resolving `exact` returned documentation and the label, without `textEdit`, `insertText`, or `additionalTextEdits`. |
| Code action over the observed unknown-tactic diagnostic | Empty list `[]`, despite advertised `quickfix`, `refactor`, and `source.organizeImports` kinds. |

The two rename edits were applied exactly as returned by Lean. Since resolved completion gave only a label, the harness separately used an **illustrative client word replacement** for `exa` → `exact` at line 6, characters 2–5. That range was not returned by Lean and must not be reported as a server-authored edit. The resulting `support/Applied.lean` contains `renamed_demo` at the declaration and use and `exact hβ`; a fresh `lean --json` exited 0. The batch output contains the expected informational `#check` line. No action or formatting edit was applied from the empty code-action response.

## Projection replay boundary

`support/projection_replay.py` imports the **illustrative** piecewise model from `anneal-3730-lean-lsp-projection-code-actions-2026-09-29`, not an Anneal source map. It maps both server rename ranges and the labelled client completion fallback into model generated offsets, applies three authored-segment edits, and checks that each prior-version request is rejected. The result exactly matches `Applied.lean` and is retained in `support/projection-replay.json`. This establishes that the example edit shapes can pass that model's single-owner and version guards; it does not establish mapping of real generated Lean back into Rust annotations or cross-file edits.

## Coverage and residuals

This report adds bounded evidence for [#3731](https://github.com/google/zerocopy/issues/3731) I030 and I059–I063, plus the related [#3730](https://github.com/google/zerocopy/issues/3730) editor/projection crosswalk rows.

| Rows | Added evidence | Still required |
| --- | --- | --- |
| I030 | Resolved actual Lean completion and actual empty code-action response; client fallback distinguished from server edits. | Server-provided snippets, `additionalTextEdits`, nonempty code actions, imports, and synthetic/cross-segment edit handling in a real projection host. |
| I059 | Direct definition, references, and semantic-token response with exact ranges. | Mapped Rust-hosted hover/navigation/tokens and unavailable imported-source behavior. |
| I060 | Direct same-file Lean `WorkspaceEdit` for rename, applied and batch checked. | Cross-file rename, Rust symbol protection, partial client capability and real projected edit acceptance. |
| I061 | No InfoView/RPC experiment in this package. | Widget/RPC/hyperlink flow through a Rust-hosted proof position and reconnect. |
| I062 | Client advertised encoding order and actual Unicode source/ranges. | Representative client negotiation and fallback across encodings, sync modes, versions and features; this server omitted an explicit encoding choice. |
| I063 | Fresh batch check after applying edits. | Real editor save/build/format/watch loops with dirty-buffer and duplicate-work controls. |

No editor adapter, Anneal UI, or product acceptance behavior was tested.

## Reproduce and verify

The exact Lean binary hash is in `REPORT.json` and `support/transcript.json`. With that binary already installed:

```sh
python3 support/probe.py
python3 support/projection_replay.py
python3 support/verify.py
```

The first script uses the conversation's Meta/Data scratch directory and overwrites this package's transcript and applied source. The second requires the earlier illustrative model report to be present as a sibling package. The verifier checks retained responses, edit ranges, applied source hash, model replay, and recorded batch exit without launching Lean. Notification order and timing can differ on replay.
