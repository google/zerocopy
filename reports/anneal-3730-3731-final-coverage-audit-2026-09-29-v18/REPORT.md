# #3730/#3731 coverage audit v18: the two disposable vertical slices

## Scope and current disposition

This audit fetched public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) at **2026-09-29 17:36:55 UTC** and inspected `reference` at `b1787210c0143a705f6bbbf2da3b2fba30cc5718`, plus the completed but not yet published [embedded-proof/model-change prototype](../anneal-3731-embedded-proof-generated-model-vertical-v4-30-0-rc2/REPORT.md). Both issue bodies and their scope comments have the same SHA-256 values as v17. The [investigation ledger](support/investigation-final-v18.csv), [suggestion crosswalk](support/3730-crosswalk-final-v18.csv), and [333-item challenge](support/row-challenge-v18.json) cover all 159 I001–I159 investigations and 174 #3730 suggestions. Each row retains its historical evidence, exact v18 residual, new file links where applicable, and next prerequisite.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 4 | 161 | 5 | 4 |

**I137 and I138 advance from partial to complete at their literal disposable-prototype scope.** I046/I049 remain complete at their earlier narrow scopes. No #3730 suggestion becomes complete: A03, B15, G06, I03, and I05 now link the prototype, but each has other mapped investigations or product-level acceptance work still open. The corpus remains far from 100% complete.

## Why I137 and I138 are complete narrowly

| Item | Executed evidence | Limit outside the requested prototype |
| --- | --- | --- |
| I137, minimal embedded-proof vertical slice | A fixture-owned parser read an unsaved Rust-comment Lean annotation, projected it over a retained real Charon/Aeneas model, opened v1 in Lean's actual server, queried a goal, applied a host/projection/version/model-checked edit, queried v2 `no goals`, and checked the exact captured Lean bytes in fresh batch. The manifest retains source, LLBC, model files and imported artifact hashes. | The marker and projector are Python, not Anneal V2 syntax or source ownership. No actual editor/MCP transaction or single production batch/live engine was tested. |
| I138, full model-change vertical slice | Real Charon/Aeneas stage calls changed the Rust model; an invalid intermediate failed Charon. Actual Lean queries were recorded before, during the failed/provisional state, during gated B preparation, and after B selection. Fresh old/new cross-model proof checks reject both mismatches. A causally gated old Lean check exited 0 after B selected, but fixture-local publication fencing rejected it. Old, provisional, new and stale identities are explicit. | The owner, status labels, gate and fence are a disposable Python driver. This does not establish Anneal scheduler, atomic publication, crash recovery, parallel writer, or cancellation behavior. |

The new package's offline checker passed with 66 I137 events, 223 I138 events, and eight retained mutation commands. It verifies raw source/model hashes, live request/version pairs, fresh batch and fixed-proposition checks, Charon's intermediate failure, cross-model negative controls, and the late-result causal order. The [35-file inventory](support/new-file-inventory-v18.csv) and [package review](support/new-package-review-v18.csv) retain exact hashes. We did not edit the new package.

The prototype also narrows selected partial rows about unsaved authority, revision-checked patches, provisional/late generations, exact fresh checking, comparator sensitivity and file-level model manifests. Their [row assessments](support/row-challenge-v18.json) state exactly what the fixture exercised and what still needs Anneal, a real editor/adapter, broader matrix or trusted declaration mapping. A changed `Current/Funs.olean` with byte-identical `Current.olean` gives a useful I147 negative identity control; it does not authenticate all imported state.

## Remaining inputs and newly feasible work

The [unrun/conditional gate table](support/unrun-conditional-inputs-v18.csv) lists all 13 such rows and their exact blocker/input. In particular, a real Lean MCP adapter and clients are absent; same-process Aeneas needs OCaml/Dune/opam or a supplied callable runtime; a later compatible Lean/Lake tuple and an actual Anneal archive are absent; remote durability is conditional on measured need; and human evaluation needs a frozen interface and consenting participants. The [resource recheck](support/resource-recheck.json) confirms that the 14 cached binary/source pins from v17 are unchanged, `ocaml`/`dune`/`opam` remain absent from `PATH`, and the host still has 8 GiB physical RAM. No dependency was installed or downloaded.

Every remaining row was challenged against the new prototype's actual methods. The host-shift CAS, synthetic shared-generator, direct Lean concurrency and small resource controls already in the corpus cover the obvious extensions at their component level. Repeating those inside this fixture would still not supply the remaining product editor/owner or representative capacity. The audit identifies no *newly available distinct cached-only* experiment from this package that would materially close another row. An independently running I051 publication experiment is outside this snapshot and must be assessed in a later audit. This is a snapshot judgment, not a claim that future implementation or platform access cannot unlock more work.

## Replay and validation

Run `python3 support/check.py` from this package. It rebuilds the LF ledgers and validation manifest twice with byte-identical hashes; verifies all 333 row decisions, four current issue text hashes, 159/174 unique IDs, the two specific status transitions, the 13 unrun/conditional prerequisites, the new package's reference metadata, and its offline checker. `support/validation-v18.json` pins source commit, issue hashes, row counts, package-file hashes and generated-file hashes. The audit builder is offline and does not stage, commit, push, install dependencies, or touch `.local/`.
