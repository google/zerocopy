# #3730/#3731 evidence audit v8: provisional models and scratch tactics

## Scope and status

At the public GitHub API snapshot of **2026-09-29T11:16:36Z**, [#3730](https://github.com/google/zerocopy/issues/3730) was closed and [#3731](https://github.com/google/zerocopy/issues/3731) open. Their bodies and single comments remained byte-identical to v7: #3730 body SHA-256 `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0`, comment `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 body `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88`, extension comment `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`. The builder verifies exactly **159 unique I001–I159 investigation rows**, **174 #3730 suggestions**, and each suggestion's mapped destinations.

Both R23–R24 suites planned in v7 are complete. This snapshot contains **72 completed substantive #3730 report packages**: 70 from v7 and the two reviewed here. The builder validates all 72 with `reference._load_report`; it inspected and hashed all 38 files (109,458 bytes) in the new packages. Both offline evidence checkers passed.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations (159) | 2 | 149 | 5 | 3 |
| #3730 suggestions (174) | 4 | 144 | 22 | 4 |

I023 and I070 move from **not run to partial**. #3730 G07 moves from **not run to partial** because R24 executed a private scratch-candidate prototype; it did not clone a real Rust-projected virtual document or measure warm-prefix reuse. G06 was already partial. All other statuses remain as in v7. I046/I049 and C03/C04/C13/N11 remain the only complete rows at their narrow previous scopes. `support/investigation-final-v8.csv` and `support/3730-crosswalk-final-v8.csv` give exact per-row evidence and residuals; no partial row is promoted to complete by a batch-success surrogate.

## Distinguishing new evidence

| Suite and report | Executed finding | Binding boundary |
| --- | --- | --- |
| R23 [`anneal-3730-last-good-model-after-rust-failure-2026-09-29`](../anneal-3730-last-good-model-after-rust-failure-2026-09-29/REPORT.md) | A tiny Rust `inc` model A passed Charon, one-shot Aeneas and Lean proof. Later source B was malformed: Charon exited 2 while `current.llbc` still held model-A bytes. Source C was syntactically valid with an unsupported raw pointer: Charon succeeded, Aeneas exited 1 after partial Lean with `sorry` and the changed body. Distinct proof v2/v3 batch checks still exited 0 **against explicitly labeled old model A**. Experiment policy marked both provisional/stale, recorded requested/current versus model-A hashes, and set `current_verified=false`; a stop policy suppressed each query. | Saved tiny fixture and Lean batch as interaction surrogate. Provenance/freshness policy is in the experiment harness, not emitted by Anneal or its tools. No changed signature, valid recovery, live goal RPC, UI or human-comprehension observation. |
| R24 [`anneal-3730-scratch-tactic-cas-experiment-2026-09-29`](../anneal-3730-scratch-tactic-cas-experiment-2026-09-29/REPORT.md) | Eleven private batch-checked candidate decisions covered accept/retry, stale proof/import, partial/failing/admitted tactics, weaker target, post-check mutation, cancellation and scratch reuse. An experiment-side file lock and source/import OLean/binary preimage CAS guarded immutable-generation pointer publication. Final fresh Lean batch matched the accepted candidate. | One direct import and theorem with fixture-specific text/admission guards. No Anneal subject mapping, projected document, long-lived server, full proposition/axiom oracle, concurrent writers or crash-safe pointer/journal transaction. |

`support/new-package-review-v8.csv` records their exact row mapping, procedures, primary files and limits; `support/new-file-inventory-v8.csv` hashes every file; `support/r23-r24-disposition-v8.csv` connects the v7 plan to the completed packages. The R23 `support/results.json` and retained source/partial Lean specimens substantiate the old-model distinction. R24 `support/results.json`, final sources and verifier substantiate its exact acceptance/rejection matrix. These are component and contract experiments, not observations of a running Anneal V2 service.

## Remaining not-run rows, local work, and gates

Five #3731 investigations remain not run:

| ID | Unexecuted requested operation | Primary gate |
| --- | --- | --- |
| I028 | Compare independently materialized and streamed outputs of one real batch/live generator under incomplete proof/import edits. | Anneal batch/live generator implementation. |
| I061 | Follow InfoView widget/RPC/hyperlink behavior from a Rust-hosted proof position through reconnect. | Rust-hosted Lean integration. |
| I063 | Exercise actual editor autosave/format/watch/build loops with dirty-buffer and duplicate-work controls. | Selected editor and Anneal transaction loop. |
| I072 | Run two independent Lean MCP adapter clients concurrently against a consistent Anneal workspace, including cancellation. | Selected adapter and workspace integration. |
| I086 | Compare in-memory or structured-stream handoff with serialized LLBC/Lean outputs. | Compatible same-process OCaml Aeneas API or approved dependency scope. |

`support/not-run-investigations-v8.csv` retains the exact delta for all five. Twenty-two #3730 suggestions also remain not run: **C11, D01, E10, E11, F03, F04, G03, G15, H06, H08, H09, J02, J05, J06, J09, J10, J14, L09, M03, M04, M06, N08**. `support/not-run-suggestions-v8.csv` lists their complete text, crosswalk destinations and residuals. A not-run suggestion can have partially investigated mapped IDs; suggestion status follows its own requested experiment.

Two further bounded local suites were **dispatched after this snapshot and are in progress, with no inferred results**. R25 tests I023 under changed function signatures and subsequent Rust/Aeneas recovery; R26 tests I070 with competing scratch publishers and crash points around its journal and pointer. Their planned scope and limits are in `support/remaining-local-experiments-v8.csv`. Seven gate groups in `support/gated-work-v8.csv` retain the user/dependency, real-human, platform, editor/MCP, Anneal-integration and design-decision boundaries. Additional small local probes can refine partial rows, but cannot by themselves validate the unavailable production bridge or human understanding.

## Rebuild and validation

Run `python3 reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v8/support/build_audit.py` from the checkout. It rechecks frozen issue hashes/counts, validates the 72 snapshot packages, checks R23/R24 against the v7 planned suites, and regenerates only this package's CSV/JSON ledgers. It does not refetch GitHub or rerun original toolchains. Two offline rebuilds produced byte-identical output files. `reference._load_report` validates this `REPORT.md` and `REPORT.json`. This package remains unstaged and unpublished here.
