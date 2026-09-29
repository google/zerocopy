# #3731 I001–I053 post-publication residual review

## Disposition

The [53-row decision table](support/row-review.csv) records each investigation's exact requested scope, present evidence, status, remaining gate, and next prerequisite. **I046 and I049 remain complete at their narrow direct-Lean scope; the other 51 remain partial.** No present Anneal V2 batch/live, editor, LSP, MCP, archive, or worker integration is inferred. This is a supplement to the [published v23 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v23/REPORT.md), not a revision of its dated classification.

The one changed cached-only assessment is **I005**. Its earlier review correctly said that the cited finite controls did not compare a minimal snapshot engine and versioned scheduler under *identical* edits and cancellations. That comparison was possible locally, so the blanket `False` availability judgment was too strong. The [retained finite probe](support/i005_models.py) and [result](support/i005-results.json) now compare both models with the same fake translation/proof backends, four source/proof/model/import changes, all 12 permitted completion/cancellation orders for each change, and two cancellation/finish orders with two readers. Both models fence publication against the latest requested identity and preserve the surviving reader in every enumerated case. An unfenced negative control selects stale A in 12 of 48 edit schedules; a cancel-all negative control loses the surviving reader in both cancellation orders. The versioned scheduler avoids one translation invocation on a proof-only or import-only change in this tiny fixture, while each model invokes proof twice. These are symbolic stage-call counts, not time or memory measurements.

This result fills only I005's **matched fake-backend comparison cell**. Both safe models use the same final publication fence, so the probe does not establish that either architecture is uniquely necessary or sufficient in Anneal. Actual dependency discovery, cancellation ownership, real Charon/Aeneas/Lean costs, and acceptance under an implemented product pipeline remain untested. I005 remains partial. The other 52 rows retain their v23 status and gate; no further distinct bounded cached-only cell was identified from their retained controls and currently pinned resources. The row table keeps exact per-ID residuals, including I003's independent embedded client, I004/I047's representative resource workloads, I023's consenting-human observation, I048's environment attestation, and I052's prepared archive/consumer boundary.

## Source and scope check

The public [#3731 issue](https://github.com/google/zerocopy/issues/3731) was reread without authentication at `2026-09-29T20:02:49Z`. It was open and its issue-body and single-comment hashes matched the original [frozen source snapshot](../anneal-3730-3731-coverage-audit-2026-09-29/support/source-snapshot/manifest.json). The [live summary](support/live-issue-summary.json) retains the update time and hashes, without copying the issue text. The checkout was at published reference HEAD `9d2426519c7eaaf58b13b109a2f4c16d84c51616` when this review began.

The [cited-package inventory](support/package-inventory.csv) hashes current `REPORT.md`, `REPORT.json` where present, and `support/check.py` where present for **70** packages named by the v23 I001–I053 ledger. All **147** cited evidence paths resolved locally. The [resource summary](support/resource-summary.json) records 14 pre-existing source/tool pins present, all file pins hash-matching v21; no OCaml/Dune/opam, Lean/Lake, Charon, or Aeneas executable was on `PATH`, though pinned Lean, Charon, and Aeneas executables were available by absolute path. Cargo, rustc, Node, and npm were on `PATH`. No dependency was fetched or installed. No credentials were read. No existing report package was changed.

The row assessment was made against each issue question and the [earlier I001–I053 review](../anneal-3731-i001-i053-residual-reaudit-2026-09-29/REPORT.md), including its retained I010 ABA experiment. The source review's per-row evidence text is carried forward except for a corrected relative link and the new I005 finding; the current v23 exact request, residual, and prerequisite are carried alongside it. This supplemental check verifies citation existence and package/report hashes, not the truth of every upstream experimental claim. It does not promote a finite model result to a product workflow.

## Reproduction

From the checkout, run:

```sh
python3 reports/anneal-3731-i001-i053-postpublication-residual-review-2026-09-29/support/check.py
```

The checker is read-only and offline. It verifies the 53 statuses and per-row source fields, 70 package hashes, 147 cited paths, live-scope hashes against the frozen snapshot, recorded pin hashes against v21, and a fresh deterministic replay of the I005 matrix. Its expected result is `PASS: 53 rows (2 complete, 51 partial), 70 package hashes, 147 cited files, live scope, pins, and I005 48/12 + cancellation replay`. [build_review.py](support/build_review.py) documents how this package's row table and inventory were generated; do not run that builder merely to check the package because it writes this package's derived files.
