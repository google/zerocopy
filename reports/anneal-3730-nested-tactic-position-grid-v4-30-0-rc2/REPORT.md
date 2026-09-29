# Nested tactic and term position grid in Lean 4.30.0-rc2

Observed 2026-09-29 with local `lean` at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. This is direct component evidence for [#3731 I043](https://github.com/google/zerocopy/issues/3731). The prior [plain-goal protocol transcript](../lean-tactic-state-protocol-transcript-v4-30-0-rc2/REPORT.md) tested a flat tactic and versioned edit; the [partial-elaboration report](../anneal-3730-partial-elaboration-queries-v4-30-0-rc2/REPORT.md) tested a few positions on valid flat tactics and explicitly left nested tactics, combinators, and a fuller position grid open. The [InfoTree report](../lean-infotree-elaboration-info-v4-30-0-rc2/REPORT.md) explains the source selection machinery but did not execute this nested grid.

## Fixture and method

The retained [`Nested.lean`](support/Nested.lean) has a nested `have ... := by simpa`, a `first` combinator whose first branch executes `trace "🧪"; exact hz`, a second unselected branch, a `constructor` proof with two bullets, and a separate `exact Eq.refl n` term. It imports only `Lean`. The exact file passed `lean --json` with exit 0 and one expected informational `🧪` trace. A fresh direct `lean --server` process opened the identical file as document version 1, completed `textDocument/waitForDiagnostics`, and answered twenty `$/lean/plainGoal` and three `$/lean/plainTermGoal` requests. The full request/response stream, readiness, diagnostics and process cleanup are retained in `support/transcript.json`.

The hypothesis was that a position query in nested syntax can expose different local contexts and goal sets depending on its precise zero-based LSP position, while a term query can expose a term goal where `plainGoal` reports no tactic goal. Identical states at every nested position, a missing term goal, or disagreement with the successful batch check on a server error would have challenged that hypothesis. The experiment observes only this pinned server's selection policy; it is not a proof that every cursor position has a unique semantic state.

## Results

| Position in the fixture | `plainGoal` result |
| --- | --- |
| Outer `by`, start of `have`, start of inner `simpa` | One goal with `n : Nat`, `h : n = 0`, target `n + 0 = 0` |
| Five UTF-16 units after the start of `simpa` | One goal with target `n = 0` and the same `n`, `h` context |
| `first`, `trace`, emoji string, before outer `exact` | One goal with added `hz : n + 0 = 0` |
| End of outer `exact hz` and start of unselected branch | No goals |
| Before `constructor` | One `True ∧ n = n` goal |
| First bullet marker | Two goals, `case left ⊢ True` and `case right ⊢ n = n` |
| Start/end of `trivial` | Left goal / no goals |
| Second bullet marker and start of `rfl` | Right goal |
| Before `exact Eq.refl n` / within `Eq.refl n` | One tactic goal / no tactic goals |

The `plainTermGoal` request at `Eq.refl` returned `n : Nat ⊢ n = n` with the exact term range line 15, columns 8–17. The same method returned JSON `null` at the earlier `exact` tactic position and in the emoji string. Thus “no tactic goals at this cursor” and “no term goal at this cursor” differ even in a successful proof. At the start of the inner `simpa`, the selected goal was the outer target; a later column on that same tactic selected `⊢ n = 0`. An editor must retain Lean's exact position and selection result rather than infer a universally valid “before nested tactic” state from visual indentation.

The emoji is before `exact` on the same line. The start of `exact` is Python/code-point column 15 but LSP UTF-16 column 16; the query grid records emoji start at column 11 and after its surrogate pair at column 13. This verifies that the client sent UTF-16 offsets across a non-BMP character. The trace diagnostic appeared with severity 3, and no error diagnostic was observed. The initialize response did not explicitly advertise a position encoding, so the UTF-16 interpretation follows the LSP default and the client's coordinate calculation, not an explicit server negotiation in this session.

## Replay and limits

Run `python3 support/check.py` from this report directory to validate retained source and binary identities, batch output, the twenty exact goal observations, three term-goal results, UTF-16 coordinates, diagnostics and clean shutdown without starting Lean. Run `python3 support/probe.py` to repeat the direct batch/LSP calls with the already installed pinned Lean binary; `LEAN_BIN` can override its path. The probe writes only `support/transcript.json` in this package and uses a single server process. A later binary should be treated as a new subject even if the script runs.

This fixture tests one successful file and selected positions, not all whitespace, macro-expanded syntax, parser recovery, unsaved edits, source projection, interactive RPC goal objects, or an Anneal LSP/MCP adapter. Batch success is a whole-file elaboration observation for this small file, while each cursor result is a local server query; neither establishes Rust-level claim equivalence. I043 remains partly open for position grids across failures, macros, edits and generated proofs.
