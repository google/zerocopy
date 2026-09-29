# #3730/#3731 coverage audit v13: current Tasks wire and Lean goal composition

## Snapshot and method

This audit uses a fresh public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) body/comment snapshot at **2026-09-29T14:43:11Z** and upstream `reference` at `dee4c4d22bae91da4b68019db8898952ea0fbd12`. The four SHA-256 values in `support/validation-v13.json` are unchanged from v12; #3730 remains closed and #3731 open. The offline builder checks 159 distinct I001–I159 headings, 174 distinct #3730 suggestions, and each extension-crosswalk destination against the issue text. It validates all 104 substantive #3730 report packages with `reference._load_report` and hashes every file in the two newly accounted packages.

[`support/investigation-final-v13.csv`](support/investigation-final-v13.csv) and [`support/3730-crosswalk-final-v13.csv`](support/3730-crosswalk-final-v13.csv) retain the requested method, prior and new evidence, status, actual procedure, boundary and specific remaining delta **for every row**. The new 14-file/189,210-byte inventory is in `support/new-file-inventory-v13.csv`; package-level methods and limits are in `support/new-package-review-v13.csv`. These classifications concern research evidence, not a claim that Anneal V2 implements the tested behavior.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations, 159 | 2 | 153 | 1 | 3 |
| #3730 suggestions, 174 | 4 | 161 | 5 | 4 |

The same narrowly complete rows remain I046/I049 and C03/C04/C13/N11. I072 remains the sole not-run investigation; F03, F04, G03, G15 and L09 remain not-run suggestions. No row moved status from v12. In particular, the new wire-model and Lean-backed composition are **partial component evidence** for I065/I071, while G03/L09/I072 still require an existing adapter/client under Anneal conditions. The corpus is not 100% complete.

## New evidence and exact limits

The [MCP 2026 task wire controls](../anneal-3730-mcp-2026-task-wire-controls-2026-09-29/REPORT.md) use a standard-library stdio model to test 2026-07-28 per-request metadata, `server/discover`, unsupported-version retry, Tasks opt-in, task polling, cancellation, error-class separation and the distinct 2025-11-25 fallback branch. Its 62-entry retained transcript and checker passed. It used fixture text, no Lean worker or SDK, and the Tasks extension it modeled was draft when read. This corrects a protocol-shape gap in the earlier invented-method toy bridge without turning it into an adapter test.

The [real-Lean current-wire composition](../anneal-3730-mcp-2026-lean-goal-wire-composition-2026-09-29/REPORT.md) uses a separate raw stdio test client and local bridge under that current-shaped envelope. Synchronous fallback and an opted-in task both returned the pinned Lean LSP goal `⊢ True`; fresh `lean --json` accepted the same tiny theorem without axioms. A wrong source hash was rejected. Cancel-before-start avoided another Lean query. During a slow in-flight `waitForDiagnostics`, `tasks/cancel` forwarded Lean `$/cancelRequest`, the real server returned `-32800`, and the bridge suppressed the task result while a subsequent goal query still succeeded. This demonstrates processed request cancellation and result suppression, **not** early interruption or compute savings. The bridge has no SDK interoperability, persistent task store, independent clients, authorization, Anneal workspace or product scheduler. Its retained checker passed.

The two reports add 14 inspected files and 189,210 bytes. `support/new-package-review-v13.csv` identifies the exact primary files and source/experiment boundaries. Neither report exercises an existing Lean MCP adapter. A real adapter and two client trial remain the decisive G03/L09/I072 residual; the other partial rows retain their specific product, dependency, human or platform gates in the ledgers and inherited `support/gated-work-v13.csv`.

## Remaining local work and rebuild

The newly exposed cached-only composition was executed as R49 and included in this audit. `support/remaining-local-experiments-v13.json` records its disposition and no further distinct suite that is safe with cached tools on the present host. R48's two-worker Lake/server cell remains **unexecuted** because its earlier memory admission rule rejected it. Later Lean/Lake, a built Anneal archive, an existing MCP adapter, same-process Aeneas dependencies, product implementation, human participants and independent environments remain gates; the audit does not substitute toy bridges for them.

Run `python3 reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v13/support/build_audit.py` from this checkout. It regenerates LF-only CSVs deterministically from the frozen issue snapshot, v12 ledger and current package evidence, verifies package metadata and counts, and does not fetch dependencies, edit prior reports or update `CATALOG.json`. Both new package checkers, the v13 loader and a second byte-identical builder run passed before publication. The parent publication step must regenerate the repository catalog and stage this package separately.
