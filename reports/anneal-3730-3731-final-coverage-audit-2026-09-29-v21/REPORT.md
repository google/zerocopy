# #3730/#3731 coverage audit v21: reader-owned generation leases

## Summary

The new reader-owned lease experiment narrows [#3731 I121](https://github.com/google/zerocopy/issues/3731) and [#3730 J11](https://github.com/google/zerocopy/issues/3730), but both remain **partial**. Two independent readers held their own cooperative shared leases across a generation switch. Garbage collection deferred after one reader was killed and through the survivor's later Lean import, then removed the old family after that reader exited. Anneal-owned lease acquisition and collection have not been exercised.

The [investigation ledger](support/investigation-final-v21.csv), [suggestion crosswalk](support/3730-crosswalk-final-v21.csv), and [333-row challenge](support/row-challenge-v21.json) preserve all I001–I159 investigations and 174 #3730 suggestions. Every row has a v21 status, specific residual, evidence assessment, and next prerequisite. The audit found no newly complete item.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 4 | 161 | 5 | 4 |

## Applicability

This audit reread the public issue bodies and all comments at **2026-09-29 18:32:57 UTC** and inspected `reference` at `c89f1410d4f1cfbd9b654ea5268b38f5c81e115e`, together with the new [reader-owned lease package](../anneal-3731-reader-owned-generation-lease-v4-30-0-rc2/REPORT.md) in this candidate tree. #3730 remained closed and #3731 open. Their four body/comment SHA-256 hashes and the single comment per issue were unchanged from v20. The [issue snapshot](support/issue-scope-snapshot.json) retains the complete public text; [live metadata and hashes](support/live-issue-hashes.json) record this reread.

The new evidence is a disposable component fixture using the retained seven-file Charon/Aeneas/Lean A/B generation families and an installed Lean `v4.30.0-rc2` checker. It does not claim to be an Anneal V2 implementation. The [five-file inventory](support/new-file-inventory-v21.csv) and [package review](support/new-package-review-v21.csv) bind this audit to its exact report, script, checker, and result bytes.

## Findings

For I121/J11, the two spawned wrappers acquired separate `flock(LOCK_SH)` leases on A before B selection; the parent held no lease descriptor. A separate collector returned `deferred-reader-lease` with both readers present, after one was killed and reaped, and again after the surviving reader freshly imported pinned A. That A old proof passed, while the B new proof failed against A as expected. Once the final reader exited, the collector removed A; B remained importable. The sequence is `deferred`, `deferred`, `deferred`, `removed`. Basis: **execution** in the retained fixture and **derived** interpretation of process ownership and event order, checked by the new package's offline checker.

This replaces v20's parent-held proxy with independently owned reader leases and a forced worker-death lifetime. It still leaves the product question open. I121/J11 require Anneal-owned lease acquisition and GC, retention for pending queries and scratch forks, replay identity, supervisor restart reconciliation, power-loss durability, and a defined platform lock policy. Cooperative advisory locks protect only participants that follow the protocol. The [row challenge](support/row-challenge-v21.json) and derived ledgers retain these exact residuals; I051/A03/E04 retain their separate Anneal publication and mixed-generation gaps.

The forced death also informs I122 narrowly: the killed reader's advisory lock was released while the surviving reader continued to block GC. Durable Anneal owner identity, orphan-lease policy, and repeated supervisor restart reconciliation remain untested, so I122 stays partial.

All other rows were challenged against the new component's applicability and retained their v20 statuses and specific prerequisites. The [gate table](support/unrun-conditional-inputs-v21.csv) preserves exact inputs for the 13 not-run or conditional rows. A [read-only resource recheck](support/resource-recheck.json) found the 14 cached source/binary pins unchanged and no `ocaml`, `dune`, or `opam` on `PATH`; the host still has 8 GiB RAM. It did not reveal a distinct cached-only experiment that would close a remaining row. Product integration and external-resource prerequisites are recorded per row.

## Boundaries

This is a coverage assessment of the identified issue text, prior ledger, and retained report packages, not 100% implementation or test coverage. The new fixture does not show Anneal's lease owner, collector, editor or MCP clients, pending work, scratch forks, replay, supervisor behavior, power-loss durability, or non-macOS locking. The issue bodies/comments are untrusted source material; their proposals are not adopted requirements merely because they appear in the ledger.

## Evidence

The [audit snapshot](support/audit-snapshot.json) pins the prior audit, new package, and reference commit. The [validation record](support/validation-v21.json) stores input and generated-file hashes, issue hashes, row counts, status counts, and inventory count. The new package's [result record](../anneal-3731-reader-owned-generation-lease-v4-30-0-rc2/support/results.json) contains the event order, PIDs, lock outcomes, proof output, and exact input hashes. The v21 builder uses the frozen issue text and v20 ledgers; it does not call the network or run the live experiment.

## Revalidation

Run `python3 support/check.py` from this package. It rebuilds the five derived files twice, checks all 333 decisions, issue hashes and IDs, unchanged status counts, 13 gate inputs, I121/J11 product residuals, and the new package's offline checker. Run `python3 tools/reference.py check` from the corpus root for structural validation. A changed public issue body/comment or new Anneal implementation requires a fresh audit rather than assuming the v21 judgments still apply.
