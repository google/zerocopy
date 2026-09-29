# #3730/#3731 coverage audit v23: reconciled local review wave

## Summary

The [333-row challenge](support/row-challenge-v23.json), [159-investigation ledger](support/investigation-final-v23.csv), and [174-suggestion crosswalk](support/3730-crosswalk-final-v23.csv) reconcile the separate I001–I053, I054–I106, I107–I159, and all-suggestion reviews with the C03, F15, I080, I010 and I147 local controls. The frozen #3730/#3731 issue text still maps 174 suggestions to 159 investigations through 345 exact destination links. Only **C03** changes status: its full refresh-strategy question is now **partial**. The narrow I049 direct Lean launch-mode investigation remains **complete** at its pinned fixture scope. No product implementation or other complete item is inferred from these component probes.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability and method

This is a new local coverage point based on the dated [v22 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v22/REPORT.md) at reference base `75fa78c1b623ab8db9d9acb4f31ec7958bfb9110`, plus the same-checkout report packages named in the [package inventory](support/review-package-inventory-v23.csv). V22 remains unchanged. The frozen issue snapshot in v22 was last reread there at 2026-09-29 18:49:42 UTC; this package does not claim a later live issue read. Issue proposals remain research scope, not adopted requirements.

The offline [builder](support/build_audit.py) copies each v22 row and its historical fields, then applies explicit review overlays. Every row gets a v23 status, gate category, remaining delta, review package, assessment, evidence-file references where a distinct cell was added, and next prerequisite. `status` in the two v23 CSVs denotes the v23 classification. Older `v22_status` and earlier fields remain available to reconstruct the chronology. The [validation record](support/validation-v23.json) hashes source rows, the three investigation review inputs, the crosswalk review, the independent v22 review, generated files, and current report-package metadata. Source report inventories are checked against their current files; a later edit requires deliberate regeneration.

## Status and evidence decisions

- **C03 → partial.** The original suggestion asks for watched notifications, proof resend, dependency refresh, close/reopen, file-worker and server restarts, and a new workspace/server generation against fresh batch. The earlier three-launch matrix omitted proof resend. The [new direct Lean probe](../anneal-3730-c03-proof-resend-refresh-2026-09-29/REPORT.md) shows both identical-text and newline `didChange` resends leave the old worker stale, while reopening, fresh server and batch see the changed import. Explicit supervisor file-worker reset, new workspace generation, and matched launch-mode coverage remain. C03's destination I049 remains complete for its narrower pinned launch comparison, so the destination and suggestion statuses intentionally differ.
- **I010/I011.** The [ABA double-collection control](../anneal-3731-i001-i053-residual-reaudit-2026-09-29/REPORT.md) shows two equal full scans can accept an impossible mixed pair without a fenced selection. Both remain partial pending coherent Anneal ownership/identity.
- **I052/F15.** The [paired tiny Lake path experiment](../anneal-3730-f15-final-versus-moved-lake-2026-09-29/REPORT.md) finds equal setup, server, batch, and no-build outcomes at one final pathname, while `Dep.trace` retains staging paths after a move. Both remain partial for a prepared Anneal archive, generated consumer, native paths and retained workers.
- **I080.** Two cached Charon jobs shared one writable Cargo target; overlap, a Cargo build-lock wait, companion completion after peer cancellation, and bounded samples were retained in the [two-process report](../anneal-3731-i080-shared-cargo-target-two-process-2026-09-29/REPORT.md). Representative sustained workload, incremental-on behavior and many-worker cleanup remain partial.
- **I126/I129/I147/I148/I151.** The I107–I159 review narrows trust execution, adds a human interpretation gate to proof acceptance, corrects the two already-run I147 artifact/model controls and I151 conflicting Lake writers, and narrows I148's intended flag/cost residual. The I147 report also adds same-nanosecond-mtime valid OLean replacement and byte-identical rebuilt OLean controls. All five remain partial.

The seven misleading generic OCaml/Dune/opam next prerequisites are corrected for **I065, I071, I077, I089, I094, I101, and I103**. Their actual next inputs are respectively real MCP client/adapter negotiation, MCP task lifecycle, a Charon reuse boundary, a real prepared archive, a later compatible Lean/Lake tuple, producer-removed archive relocation, and actual installation/archive replacement. OCaml remains a legitimate gate for the Aeneas same-process library rows; those rows were not changed.

The [174-row crosswalk re-audit](../anneal-3730-174-row-crosswalk-reaudit-2026-09-29/REPORT.md) challenged 23 suggestions. V23 resolves them as follows:

| IDs | Reconciliation |
| --- | --- |
| C03 | Downgraded to partial with exact remaining refresh controls. |
| D01, F02, F14, I04 | Replaced unrelated OCaml prerequisite with the needed Anneal overlay or prepared archive/consumer input. |
| F12 | V22 already states the two-writer reverse-kill result and remaining artifact/trace interruption; retained that accurate residual explicitly. |
| F15 | Added the paired tiny Lake path result; kept real prepared-consumer gate. |
| F19, I01, I03, I08 | Corrected human-only or missing product/interface gates; I01 now explicitly cites the previously existing generated-model vertical slice. |
| J01–J10, J12, J14 | Added the actual prepared Anneal workload and scheduler/consumer to resource or platform prerequisites. |

The four complete investigations (I046, I049, I137, I138) and three remaining complete suggestions (C04, C13, N11) retain their narrow direct Lean or disposable-prototype scopes. The 13 not-run or conditional inputs remain open, including the real MCP adapter, prepared archive, later compatible Lake release, human study, and optional OCaml library route. No current Anneal V2 verification command, proof acceptance, LSP or MCP path has been executed by this wave.

The earlier I001–I053 and crosswalk reviews recorded a re-review checker failure at their review points. The later [third-pass package](../anneal-3730-five-original-packages-third-pass-review-2026-09-29/REPORT.md) separates historical first/second-pass hashes from current-file hashes. Its current-file manifest was refreshed after the later source-package edits and its checker passes; the older checker-run logs remain valid history of when their mismatch was observed.

## Revalidation

Run `python3 support/check.py` from this package. It rebuilds derived files twice, compares every inherited v22 field, checks all 333 titles and 345 links against frozen issue text, validates the one status change, 23 challenged suggestions and seven OCaml gate corrections, verifies package/file hashes and citations, and reruns ten selected offline checkers. It does not fetch, install, alter issue state or validate a product workflow. Run `python3 tools/reference.py check` only after a future catalog update includes this package; this task does not edit CATALOG.
