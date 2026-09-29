# #3730/#3731 coverage audit v24: post-publication residual controls

## Summary

The [v24 333-row challenge](support/row-challenge-v24.json), [159-investigation ledger](support/investigation-final-v24.csv), and [174-suggestion crosswalk](support/3730-crosswalk-final-v24.csv) incorporate three post-publication audits into the [published v23 snapshot](../anneal-3730-3731-final-coverage-audit-2026-09-29-v23/REPORT.md). V23 remains a dated record. The new evidence changes **17 specific residuals**, refines **seven prerequisites**, and changes **no status**. The 345 exact #3730→#3731 destination links are unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

This is a source and evidence reconciliation at published `reference@9d2426519c7eaaf58b13b109a2f4c16d84c51616`. The [live issue read](support/live-issue-hashes.json) fetched both public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and their comments on 2026-09-29. Their full hashes and update times match the frozen v22 source snapshot: #3730 remained closed and #3731 open at this read. The [offline builder](support/build_audit.py) starts from every v23 row and verifies the preserved frozen text before adding v24 fields; it never changes v23 or the source audits. The issue proposals are research questions, not implemented Anneal requirements.

The three source packages are the [I001–I053 audit](../anneal-3731-i001-i053-postpublication-residual-review-2026-09-29/REPORT.md), [I054–I106 audit](../anneal-3731-i054-i106-postpublication-residual-audit-2026-09-29/REPORT.md), and [I107–I159 audit](../anneal-3731-i107-i159-postpublication-residual-audit-2026-09-29/REPORT.md). They reviewed all 159 investigation scopes. The [source package inventory](support/source-package-inventory-v24.csv) hashes **41 substantive files** across them, including their retained inputs, results, checkers and row decisions. Python bytecode caches are excluded. Each v24 investigation row names its post-publication review and the corresponding decision table; changed rows cite the pertinent probe/result files. All 174 suggestions retain v23 evidence and exact destination links, with new citations added to the twelve directly linked suggestions affected by the controls.

## Findings

| Investigation | New bounded evidence | Exact remaining boundary |
| --- | --- | --- |
| **I005** | A matched fake-backend snapshot/scheduler replay covers four edit/dependency variants, 48 valid completion/cancellation schedules, and two shared-reader cancellation orders. Both fenced models select current B; an unfenced control selects stale A in 12/48 schedules. | Actual Anneal dependency discovery, cancellation ownership, stage costs and product generation policy remain; **partial**. |
| **I076** | Two offline sibling Cargo libraries serialize the same Charon crate/function names but distinct bodies, `11` versus `29`, into distinct LLBC files. | A sufficient compilation-unit key, host/target/feature and concurrent-output matrix, and collision-rejecting Anneal publisher remain; **partial**. |
| **I126** | Lake configuration `run_cmd` wrote an owned outside-workspace marker when permitted; a targeted macOS sandbox denial blocked the write while the static Lake control built. | Native extensions, broad containment and resource limits, inspection-before-execution, and Anneal trust-entry authorization remain; **partial**. |
| **I127** | The I126 denial diagnostic carried an absolute owned marker path; the retained transcript normalizes that scratch root. | Private-source, credential, environment and product-log leakage controls remain; **partial**. This is a cross-slice observation, not a distinct I127 experiment. |
| **I145** | The I076 sibling-name collision adds a name-only identity counterexample to the prior seven-file manifest and OLean ablation. | Full Cargo→Charon→Aeneas→Lake→Lean→MCP tuple ablation, causality/content distinction and response-envelope routing remain; **partial**. This is a cross-slice observation, not a distinct I145 experiment. |

**Crosswalk impact.** D07 (destination I076) and G09 (destination I126) receive the direct LLBC and Lake trust controls. The I145 destination links in **A01, A02, A08, C01, F05, G01, G02, G12, L01, O03** receive the I076 name-only counterexample as bounded evidence; their broader identity, freshness, or interface work remains. No #3730 suggestion directly targets I005 or I127, so v24 does not add an invented destination. Those twelve suggestion statuses remain partial. The v24 fields on each row state the precise residual and next prerequisite; all other v23 fields and statuses are preserved byte-for-value in the derived rows.

The **four narrowly complete investigations** remain I046, I049, I137 and I138. The three complete suggestions remain C04, C13 and N11. All other conditional/not-run gates remain as in v23. The new fake backend, sibling Cargo, and Lake sandbox controls cannot establish an integrated current Anneal V2 batch/live verification, LSP or MCP workflow, prepared archive, or claim acceptance.

## Boundaries

- I005's two safe models share a publication fence, so the 48 schedules do not prove one architecture necessary or compare measured resource cost.
- I076's LLBCs retain distinct source paths and were written to separate destinations. The result refutes *name-only* selection, not all Charon provenance or an implemented collision policy.
- I126's sandbox denies writes to one owned outside directory and network operations. It is a targeted denial control, not complete containment of arbitrary untrusted projects. I127's path is an owned scratch path, not leaked private data.
- Source report hashes are a local audit point. Later source corrections require a deliberate v24 inventory update; they do not retroactively change the three retained observations.

## Evidence

The [validation manifest](support/validation-v24.json) pins v23 input files, the live issue hash summary, four derived files, changed row IDs, status counts and the 41-file source inventory. The I005 [result](../anneal-3731-i001-i053-postpublication-residual-review-2026-09-29/support/i005-results.json) and [probe](../anneal-3731-i001-i053-postpublication-residual-review-2026-09-29/support/i005_models.py), I076 [LLBC result](../anneal-3731-i054-i106-postpublication-residual-audit-2026-09-29/support/results.json), and I126 [Lake result](../anneal-3731-i107-i159-postpublication-residual-audit-2026-09-29/support/results.json) are retained by their own packages with their exact tool/input/fixture controls. Their checkers and metadata loaders passed while v24 was built. No dependency was fetched or installed, no credentials were read, and no issue status or product data was changed.

## Revalidation

Run `python3 -B support/check.py` from this package. It checks 333 inherited rows, 159 titles and 174 suggestion titles/destinations against frozen issue text, all 345 links, all cited v24 evidence files, the 41 source-file hashes, and the three supplemental package loaders/checkers. It is offline and read-only. The builder can regenerate this package's derived files deterministically; running it is a write to this new package, so use the checker for routine validation. `tools/reference.py check` also requires CATALOG to include this new package when publication is prepared; this report does not edit CATALOG.
