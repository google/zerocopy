# #3730/#3731 coverage audit v12: nine published and two local follow-ups

## Snapshot and row method

This audit snapshots the current public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and sole extension comments at 2026-09-29T14:15:13Z. The four SHA-256 values in `support/validation-v12.json` match v11; #3730 is closed and #3731 is open. The source branch is `upstream/reference` at `d3e0e39ab26ddd79d03bea58cfe87813a33ef633`. The builder compares the issue headings and extension crosswalk to all 159 I001–I159 and 174 #3730 suggestion rows, including destination sets. It validates every one of 102 substantive #3730 report packages with `reference._load_report`, including nine newly published packages and two fresh local follow-ups. The retained offline checker passed in each of those eleven packages.

The row-level results are `support/investigation-final-v12.csv` and `support/3730-crosswalk-final-v12.csv`. Each row carries its requested scope, prior evidence, new package and primary evidence paths, actual method, evidence boundary, status, and specific remaining delta. `support/new-file-inventory-v12.csv` hashes all 778 files in the eleven newly accounted packages (15,869,168 bytes). These are **coverage of experiments**, not evidence that current Anneal V2 implements the measured component behavior.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations, 159 | 2 | 153 | 1 | 3 |
| #3730 suggestions, 174 | 4 | 161 | 5 | 4 |

I046/I049 and C03/C04/C13/N11 retain their narrowly complete classifications. Six suggestions move from not run to partial: E11, H08, H09, M03, M04 and M06. No investigation becomes complete. I072 is still not run; F03, F04, G03, G15 and L09 remain not run as suggestions. No 100% claim follows from these counts.

## What the eleven additions establish

| Package | Executed observation | Exact boundary |
| --- | --- | --- |
| [Restricted Aeneas reuse](../anneal-3730-aeneas-restricted-reuse-2026-09-29/REPORT.md) | Trait body/signature variants, parsed generated imports, guarded `Types.olean` reuse, fresh proof and unsafe controls. | Aeneas itself regenerated whole-crate; no same-process item invalidation or measured speedup. |
| [Combined tiny pipeline](../anneal-3730-combined-pipeline-concurrency-2026-09-29/REPORT.md) | Two private Charon→Aeneas→batch Lean workflows serial, concurrent and one-Lean-slot; selected proofs and sampled resource guards. | Four workers skipped; no Lake/server/Anneal scheduler or hard transient peak. |
| [Compatible bundle upgrade](../anneal-3730-compatible-bundle-upgrade-golden-2026-09-29/REPORT.md) | Two cached paired Charon/Aeneas revisions, base/changed Rust, four fresh Lean checks and cross-pair rejection. | Small manually assembled obligations; same Lean pin, no Anneal generated workspace or workaround deletion. |
| [H08 project router](../anneal-3730-h08-project-switch-router-v4-30-0-rc2/REPORT.md) | A→B→A two-server route preserved A's unsaved buffer; cold A reconstruction read disk; same-named imports remained isolated. | Synthetic client router, no editor workspace-folder event or Anneal pool. |
| [H09 cancellation](../anneal-3730-h09-lsp-to-upstream-cancellation-boundaries-2026-09-29/REPORT.md) | Direct Lean processed `-32800`; one private Cargo group/descendants stopped while independent peer survived and retry passed. | No shared in-flight job or editor-to-Anneal scheduler identity. |
| [M06 Lake source-order trace](../anneal-3730-m06-generated-lake-source-order-trace-2026-09-29/REPORT.md) | Nine Lake builds on real Aeneas-generated tiny modules: no-write/mtime replay and byte-change rebuild/restore. | Source path and span comments changed together; no general key proof or workaround deletion. |
| [MCP-shaped task lifecycle](../anneal-3730-mcp-shaped-async-task-lifecycle-2026-09-29/REPORT.md) | Toy stdio bridge over real Lean LSP showed handle retrieval, reconnect, expiry, cancellation, partial failure and recovery. | No installed SDK/adapter interoperability or Anneal task service. |
| [Pinned cross-layer navigation](../anneal-3730-pinned-cross-layer-navigation-boundary-2026-09-29/REPORT.md) | Fifteen item links, six genuine loop-helper fanout links, reorder/ambiguous-name controls and seven stale rejections; fresh selected Lean/Rust checks. | Cross-tool joins and proof obligations remain manual; helper `rfl` attempts failed; no authenticated producer IDs or agent trial. |
| [Real-archive availability gate](../anneal-3730-real-archive-manifest-gate-2026-09-29/REPORT.md) | Scoped local inventory found no built archive; one-module read-only Lake complete/missing-manifest and producer-removal controls ran. | No actual Anneal archive, real graph or first-goal server write trace. |
| [R47 shared Cargo ownership](../anneal-3730-shared-cargo-consumer-ownership-2026-09-29/REPORT.md) | One actual offline Cargo job shared by two toy consumers; one/last-owner cancellation and failure fan-out/retry controls passed. | Owner logic was a Python harness, without Anneal request identities or independent MCP/editor clients. |
| [R48 full Lake/server chain](../anneal-3730-full-lake-server-chain-2026-09-29/REPORT.md) | One tiny full Charon→Aeneas→direct Lean→Lake→live goal→fresh batch chain passed with 2,590,336-KiB sampled RSS peak. | Two-worker cell skipped by admission; no Anneal scheduler or hard memory peak. |

`support/new-package-review-v12.csv` gives each package's method, evidence files and residual. The 91 inherited reports remain accounted for in `support/all-package-accounting-v12.csv`; a package title alone was never used to mark a row complete. In particular, the two toy MCP reports do not turn G03/L09/I072 into an existing-adapter experiment, and the hash-gated navigation report does not establish a producer-authenticated cross-language obligation key.

## Outstanding work

The five not-run suggestions are enumerated in `support/not-run-suggestions-v12.csv`; I072 is in `support/not-run-investigations-v12.csv`. The actual Anneal archive, a later Lean/Lake pin, and an existing Lean MCP adapter are unavailable in the checked local installation. The product-level Anneal editor, scheduler, workspace and source-map experiments await an implementation; a human study requires participants, and independent-host/platform claims require those environments. `support/gated-work-v12.csv` retains the seven broader gate groups from v11. Partial rows each state their smaller specific residual in the two full ledgers.

The two bounded cached-only component experiments identified during this audit were executed as R47 and R48, and are included in the row ledger. `support/remaining-local-experiments-v12.json` records their outcomes and exact limits. R48’s two-worker Lake/server cell remains unexecuted because the admission rule rejected it at 40% free memory and a projected 5,180,672-KiB sampled RSS. No further distinct cached-only suite was exposed that can be run safely on this host now; product, dependency, human and platform gates remain. The skipped two-worker cell is a resource-gated local opportunity, not completed evidence.

## Rebuild

Run `python3 reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v12/support/build_audit.py` from this checkout. It is offline and deterministic against the frozen issue snapshot and the current 102 accounted report packages; it rejects changed issue hashes, headings, crosswalk destinations, missing package files or invalid report metadata. This audit does not rerun toolchains, edit prior packages or update `CATALOG.json`. Each of the eleven newly accounted packages' `support/check.py` passed independently during this audit. Publication requires the parent to regenerate the repository catalog after this package is accepted.
