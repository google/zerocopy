# Offline client envelope replay for late Lean goal replies

## Summary

A small client state machine bound each `plainGoal` request to its submission-time `(process incarnation, URI, document version, source SHA-256, position)`. On each of three retained Lean 4.30.0-rc2 wire traces, it admitted the version-2 `⊢ False` reply as current and rejected the later version-1 `⊢ True` reply for a latest-state caller. An explicit historical caller could receive that older result with its version-1 envelope. Synthetic reorder, single-field mutation, and restart/request-ID-reuse cases expose the decision points. This is **execution** of a proposed client policy over recorded messages, not an Anneal implementation or a new Lean server run.

## Applicability

The wire records are byte-for-byte copies of three direct `lean --server` runs from [the cross-version goal report](../lean-lsp-cross-version-goal-completion-v4-30-0-rc2/REPORT.md). Its Lean binary, source revision, single URI, one transport, V1 gate and V2 marker, and batch controls apply to the *recorded* case. The replay itself used only Python's standard library and the copied source and JSON files in this package. Its `A` and `B` incarnation names are client-assigned model tokens, not fields sent by Lean or observed process IDs. Each run's recorded `A` represents that run's one server transport; runs are independent.

The state machine models reply **attribution**, not whether Lean computed the right goal. A live result requires an exact envelope match against current client state. A request marked historical at submission may be returned as `historical_only` under its original envelope; it never becomes a latest-state result. The explicit-history flag and all scenario reorderings or mutations are client-side model inputs. Only `recorded_arrival` uses the retained receive order.

## Findings

The replay extracts actual V1/V2 source text, request positions, request IDs 20 and 21, and `⊢ True`/`⊢ False` replies from each complete transcript. Before modeling a decision it checks source hashes, open/edit payloads, the V2 wait and goal reply before V1 release and old reply, and the extra `textDocument.version: 1` on request 21. That extra field did not pin Lean's query to V1. The model attaches version and source hash at **request submission**, independently of the unversioned Lean `plainGoal` schema. **Basis: recorded execution plus derived client policy.**

| Scenario | Reply decisions | Final latest result | Evidence role |
| --- | --- | --- | --- |
| Recorded V2 reply, then late V1 reply | `current_live`, `stale_snapshot` | `⊢ False` | Retained receive order; modeled fence |
| V1 request explicitly historical | `current_live`, `historical_only` | `⊢ False` | Synthetic client intent on retained payloads |
| Old reply first, after edit | `stale_snapshot`, `current_live` | `⊢ False` | Counterfactual receive order |
| Old reply before edit | `current_live`, `current_live` | `⊢ False` | Counterfactual timing; earlier acceptance loses current authority on edit |
| Restart to B, same URI/version/source/ID 20 | `expired_incarnation` | none | Synthetic incarnation collision |
| Source changes while version remains 1 | `stale_snapshot` | none | Synthetic source-hash control |
| Goal target position changes with same source/version | `stale_snapshot` | none | Synthetic position control |
| URI changes with same source/version/position | `stale_snapshot` | none | Synthetic URI control |

These eight decisions are identical for all three retained runs. In the restart case, the model has a new B request also numbered 20; the delayed A reply is identified by its A transport and cannot satisfy B's pending request. The old-before-edit case shows that a result admitted when current must still be checked against current state when later reused. The same-version control shows why URI/version alone is insufficient when client-observed source bytes change without a version bump. The position and URI controls change the client's intended goal target without claiming a corresponding Lean response. **Basis: deterministic model execution.**

This adds narrow component evidence for #3731 **I041** and #3730 **C01**: a concrete request envelope and receive-time fence driven by actual late goal payloads. For **C09**, the retained trace has two overlapping goal requests at the *same* position in one document, and the replay correlates their distinct IDs despite reverse-version completion. It does not exercise C09's requested many-position concurrency, cancellation, or broader ordering. No row is completed: an Anneal V2 source/import envelope and actual adapter behavior remain the product gate.

## Boundaries

- **Not examined:** Anneal code, Rust projection, imports or environment generation, Lake state, RPC `getInteractiveGoals`, multiple URIs or positions, cancellation, actual worker replacement, or true concurrent replay scheduling. The model tuple lacks the import generation required by a full Anneal result contract.
- **Unknown:** when Lean internally computed the old goal. The retained transcript proves client-visible order and the newer V2 barrier, not server-side computation order.
- **Not established:** a real response can authenticate its own process incarnation. Here the client transport supplies the token; a production adapter must preserve that routing through restarts and callbacks.
- **Not established:** a goal is a valid proof or a complete verification result. The V2 source has batch errors, as the originating report records.
- The reordered and restart scenarios are adversarial **model controls**, not additional Lean observations. A positive model verdict is no proof that Anneal implements this policy or that it covers all interleavings.

## Evidence

- [`support/replay.py`](support/replay.py) implements exact-envelope request capture, edit/restart transition, `(incarnation, request ID)` correlation, receive classification, and current-result recheck. SHA-256 `c170f5444284cfcbd81177812d530e598e5dcd47c3da278d17f2b5bd20a91d41`.
- [`support/scenarios.json`](support/scenarios.json) specifies eight action sequences, including the factual receive order and seven labeled counterfactual controls. [`support/expected.json`](support/expected.json) retains canonical output for all three runs. Their SHA-256 values are `5367ddd76c8183421c34dae497a645ac0fd90c8abaf0b58ce94fed371be23ea6` and `92ef8557ac393a9089f786dfd98e0cf66a07fe76c6c1adbb5e6cba4f436f1d46`.
- Complete copied wire records: [`run 1`](support/transcripts/transcript-run1.json), [`run 2`](support/transcripts/transcript-run2.json), [`run 3`](support/transcripts/transcript-run3.json), SHA-256 `12514acc62e577ad18cc446a32a28c23ba3fe1be070f279a22649c31f27c27c0`, `568711ed5a7d758660dccb72a63ef3d6f0d242e286cd44fa8aaab72c8abff25e`, `00561c961a49f9544ae4b5af181ce84335968582332df88bba68732b5c6ac8f8`. Exact copied sources are [`V1.lean`](support/sources/V1.lean) and [`V2.lean`](support/sources/V2.lean), SHA-256 `17f79c983f479120cd5324330ee4cbf299922b90f55ad11957a2b9d7af3d0ad3` and `acf6662f56cbeff6ce95f35affefc9bb03e262079274a814e0d45f4bd8ce70e5`.
- [`support/check.py`](support/check.py) is a read-only checker. It invokes the replay with `-B`, compares exact output bytes, and asserts all case decisions. The originating report's [offline checker](../lean-lsp-cross-version-goal-completion-v4-30-0-rc2/support/check.py) additionally validates the full gate, diagnostic, batch, and exit evidence. This package intentionally does not claim that broader validation as a new experiment.

## Revalidation

Run `python3 -B support/check.py` from this package. It reads only package files and starts no Lean process. For a different Lean revision or transport, collect new direct wire evidence and recheck the event/schema assumptions before applying the policy. For an Anneal product gate, implement the envelope with source and imported-environment identity in its adapter, then exercise real edits, worker replacement, historical requests, and simultaneous positions against its response routing.
