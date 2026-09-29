# #3730/#3731 coverage audit v28: live imports, goal replies and fresh Lake consumers

## Summary

Five pinned Lean/Lake component reports sharpen **12 partial rows** in the published [v27 coverage ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v27/REPORT.md): investigations **I012, I038, I041, I089, I092, I099** and suggestions **C09, C11, F07, F08, F19, I04**. All 333 IDs, 345 #3730→#3731 destination links, original issue request text, gate categories and statuses remain unchanged. The [investigation matrix](support/investigation-final-v28.csv), [suggestion crosswalk](support/3730-crosswalk-final-v28.csv) and [333-row challenge](support/row-challenge-v28.json) append v28 evidence, residuals, prerequisites and an explicit scope assessment to every inherited row.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

The new direct-server and Lake-server [unsaved import](../lean-unsaved-cross-module-import-v4-30-0-rc2/REPORT.md) [reports](../lean-lake-unsaved-cross-module-import-v4-30-0-rc2/REPORT.md) show that an open producer buffer was not a live import of another open document in their tiny fixtures. The [goal reply report](../lean-lsp-cross-version-goal-completion-v4-30-0-rc2/REPORT.md) records newer-version completion before older-version replies arrive. The [fresh Lake consumer matrix](../anneal-3731-lake-fresh-cache-consumer-matrix-2026-09-29/REPORT.md) separates selected cache equivalence, source requirements, metadata replay and batch versus live readiness. The [path-disappearance report](../lean-lsp-open-buffer-path-disappearance-v4-30-0-rc2/REPORT.md) shows an open Lean buffer retaining its goal after its disk path is renamed or deleted. These observations do not implement an Anneal V2 service or editor host, or consume its actual prepared archive.

## Applicability

The baseline is published `reference@1b67b6b87b3266f1f798cd825de9988e297b5822` and its v27 ledger. The five new reports execute `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) on arm64 macOS. Their exact fixture, launch, artifact, server and resource conditions remain in their own reports and retained support records. The Lake cache matrix uses a tiny two-package project, a seeded cache and fresh consumer roots; the direct and Lake import probes use one producer plus a few consumers. The goal race uses one direct server URI. None covers actual Anneal generated obligations, full import graphs, a read-only omnibus archive or a production client envelope.

The live public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again on 2026-09-29 and preserved verbatim in the [v28 snapshot](support/live-issue-snapshot-v28.json). #3730 was closed with one comment; #3731 was open with one comment. Both bodies and both comment bodies matched v27 and the frozen v22 request snapshot byte-for-byte. The #3730 body/comment SHA-256 values are `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values are `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Source report | Direct investigation rows | Direct #3730 suggestions | What changed |
| --- | --- | --- | --- |
| Open-buffer path disappearance | I012 | None | Three direct Lean runs retain B's open goal after the URI's disk path is renamed or deleted, then switch to recreated C after close/reopen. |
| Direct and Lake unsaved imports | I038 | C11 | Resident and new consumers import an old compiled producer despite its open unsaved `4` buffer; rebuild changes fresh/reopened consumers. The direct-server probe also rejects an open-buffer-only module. |
| Cross-version goal completion | I041 | C09 | Three transcripts place a current version-2 wait and goal before older version-1 replies; a later old-version wait succeeds. |
| Fresh Lake cache consumer | I089, I092, I099 | F07, F08, F19, I04 | A fresh cache fetch agrees with selected clean artifacts and goals; source removal yields no-build failure and a null server goal even while direct batch accepts retained OLean; trace/hash/config ablations take distinct paths. |

Every mapped row remains **partial**. I012 still needs a real editor/Anneal buffer-disk authority and save-conflict policy: the probe harness physically wrote B before `didSave`, injected watched-file notifications, and supplied C on reopen. I038/C11 still need Anneal's live-proof materialization and dependency policy. I041/C09 still need an implemented request envelope, version fence and worker identity. I089/I092/I099 and their mapped suggestions still require an actual content-identified prepared archive or production generated consumer, read-only and write tracing where requested, and broader equivalence or readiness oracles. The per-row residual and next prerequisite are in the ledgers.

### Deliberate exclusions

Fourteen related rows receive explicit context-only assessments while their v27 residual, prerequisite and evidence fields remain unchanged: **B15, C01, I042, I045, I039, I091, I131, I132, I134, F02, F04, F13, F20 and I02**. B15 remains unchanged because the path-disappearance harness did not run an editor or Anneal host that decides proof authority and save conflicts. The race does not implement C01's version-bound wrapper or I045's worker-incarnation control; the fresh-cache fixture does not execute F02's real read-only Anneal archive, F04's real-archive manifest removal, F13's many concurrent consumers, F20's generated-module rebuild accounting, or I02's worker-reported loaded-import attestation. I042 asks for a causal readiness protocol, beyond the observed null-goal failure control. These distinctions are recorded individually in [row-challenge-v28.json](support/row-challenge-v28.json).

For each of the other **307 unchanged rows**, its v28 scope assessment names the row and inherited gate, states that none of these five reports directly exercises it, and keeps its v27 residual and prerequisite. Thus 12 direct + 14 context-only + 307 other unchanged = 333. No row is reclassified as complete because a bounded Lean or Lake component behaved as expected.

## Boundaries

- The direct-server and `lake serve` unsaved-import probes agree on their selected old-artifact contrast, but they are distinct launch/preparation paths. They do not establish an editor-wide or Anneal-wide import policy, worker refresh latency, fanout, cycle behavior or InfoView reference lifecycle.
- The path-disappearance probe used harness-controlled physical writes, explicit notifications and supplied reopen text. It did not run editor conflict arbitration, filesystem watcher delivery or an Anneal authority host. Its A/B/C goals all occurred in batch-failing files.
- The goal race records client-visible wire order and a version-2 tactic marker, wait and goal barrier. It does not timestamp Lean's internal computation of the late old reply, prove cancellation behavior or supply a production latest-version classifier.
- The fresh Lake matrix samples one theorem, one dependency and selected OLean/ILEAN/C hashes. Its producer and cache inventories capture net file-byte differences, not syscall-level writes or attempted reads. Producers were writable, and replay command traces refer to a shared seed path that was not resnapshotted after the cells. It cannot establish whole-archive read-only or complete clean/prepared equivalence.
- The live public issue snapshot attests request scope at its fetch time. It does not change the issue state or assert that component experiments satisfy the original full requests.

## Evidence

- The [source inventory](support/source-package-inventory-v28.csv) records SHA-256 for every retained file in v27 and the five new source packages. [validation-v28.json](support/validation-v28.json) records generated and input hashes, row counts, unchanged statuses and gate categories, direct/context IDs and source package list.
- Independent review of the path-disappearance package found its retained transcripts and checker sound without a needed correction. The review retained the I012 product gate because the harness writes B before `didSave`, injects watched events, and supplies C at reopen; no conflict handler or editor authority was exercised. The Lake-server I038 package also received independent review and its final corrected checker passed before this inventory was built.
- The [offline builder](support/build_audit.py) derives all v28 rows from v27 and the preserved live issue text. The [self-checker](support/check.py) verifies every inherited field and original request mapping across 159 investigations, 174 suggestions and 345 destinations; checks all row deltas and unchanged explanations; validates all source hashes; and runs the v27 and five new report checkers. Source reports retain their own raw transcripts/results and exact toolchain conditions.
- The v27 row-challenge SHA-256 is `9ec8bb96dbf66f45397362c439379ea4bf6bbabcabd7cffa509e9456014142ce`. The source Anneal revision represented by the inherited ledger remains `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`; none of the five probes executes that source as an end-to-end service.

## Revalidation

Run `python3 -B support/check.py` from this package or an unchanged copy of the reference tree. It reads the retained ledgers and source reports, checks hashes and scope mappings, and runs all six source checkers without starting Lean, Lake, Charon or Anneal. If public issue text later changes, fetch a new immutable snapshot and create a later ledger revision; preserve v28's fetched bytes and historical mapping.
