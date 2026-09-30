# Six prior Lean 4.29/4.30 comparisons against 4.34.1: bounded source review

## Summary

The frozen [six-row matrix](support/matrix.json) preserves the exact prior report paths, claim excerpts and section/line locators, report and metadata SHA-256 values, and original subject identities. Five reports compare locally observed Lean/Lake `v4.29.0` with `v4.30.0-rc2`; their comparisons remain **historical evidence at those pins**. The sixth, R462, was placed in this inventory category but directly observed only `v4.30.0-rc2`. One narrow R462 source clause about document-version waiting and unversioned goal parameters is rechecked in official `v4.34.1` source. **All six full report claims remain unresolved at 4.34.1**, every newer runtime result is unexecuted, and Anneal product behavior is unassessed.

## Applicability

The [official Lean `v4.34.1` release](https://github.com/leanprover/lean4/releases/tag/v4.34.1) resolves to [`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`](https://github.com/leanprover/lean4/commit/5045d0056413266e57c625dcd7c365b10e377c52). Lake is part of that Lean source tree. A read-only official `git ls-remote` query returned direct tag refs with no separate peeled `^{}` objects: [`v4.29.0` → `98dc76e3c0a9b856c9b98726b713fb04fab16740`](https://github.com/leanprover/lean4/commit/98dc76e3c0a9b856c9b98726b713fb04fab16740), [`v4.30.0-rc2` → `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`](https://github.com/leanprover/lean4/commit/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc), and `v4.34.1` → `5045d0056413266e57c625dcd7c365b10e377c52`. These were lightweight refs in that observation. The matrix preserves exact old binary hashes and toolchain strings where direct old metadata has them; it does not fill in missing direct source commits by assumption.

The six packages are selected from the 581-report `version-inventory-ebcdcad-581.csv` at reference `ebcdcadb63fefd1e6c0f46cb2030270ae3232837` under its exact category `Lean/Lake v4.29.0 versus v4.30.0-rc2 (prior comparison)`. At frozen reference `6c0988948cb2098a7c2d11ff89bd20322d562eaa`, there are 588 packages; seven post-inventory additions are listed and hashed separately. These six are a distinct inventory cohort from the previously reviewed 161 `Lean/Lake v4.30.0-rc2` rows. Topical overlap does not merge the selectors or make an earlier 4.29→4.30 observation a 4.30→4.34.1 test.

## Findings

| Frozen row | Prior observation retained at its original pins | 4.34.1 classification |
| --- | --- | --- |
| R182 | Clean/prepared and batch/live agreement in a small two-file fixture at both versions. | Historical evidence; current behavior unresolved. |
| R196 | Transitive import, option, macro, plugin and RPC lifecycle comparison in a small project at both versions. | Historical evidence; current behavior unresolved. |
| R255 | Unicode LSP coordinate/encoding-offer replay was qualitatively alike at the two pins, while one advertised RPC capability field differed. | Historical evidence; current encoding and capability behavior unresolved. |
| R447 | Repeated clean/cache artifact comparison and a version-specific advertised RPC capability field. | Historical evidence; current determinism, cache and capability behavior unresolved. |
| R456 | Direct-server imported-generation refresh contrast at both versions. | Historical evidence; current refresh behavior unresolved. |
| R462 | Three direct `v4.30.0-rc2` runs with a newer goal reply arriving before an older request's reply. No direct 4.29 run belongs to this report. | One exact source clause rechecked; current reply ordering and full claim unresolved. |

### R462: a narrow source clause still exists

R462's selected exact passage says that `waitForDiagnostics` allows a document version greater than or equal to the requested one, and the handler accepts `p.version ≤ doc.meta.version`. The original report cites the [4.30-rc2 `WaitForDiagnosticsParams`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Extra.lean#L37-L48) and [handler](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker/RequestHandling.lean#L466-L481). In [4.34.1 `Extra.lean`](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Data/Lsp/Extra.lean), the request documentation still specifies greater-or-equal completion, and `PlainGoalParams` still extends `TextDocumentPositionParams`. The [4.34.1 handler](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Server/FileWorker/RequestHandling.lean) still tests `p.version ≤ doc.meta.version`, then awaits its reporter and command snapshots. The [4.34.1 basic LSP types](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Data/Lsp/Basic.lean) define `TextDocumentPositionParams.textDocument` as `TextDocumentIdentifier`, whose only field is `uri`, rather than `VersionedTextDocumentIdentifier`. **Basis: source.**

This rechecks only the selected type/guard clause and supports treating a requested wait version as a lower bound in the inspected source. It does not reproduce R462's late reply ordering at 4.34.1, prove how extra JSON fields are decoded in all circumstances, or establish an Anneal response fence. The full R462 claim stays unresolved at the target; `rechecked_source_claim` labels the narrow clause, not a runtime result.

## Boundaries

No 4.34.1 Lean, Lake, or language-server binary was downloaded, installed, built or run. The five old comparisons do not determine 4.34.1 artifact bytes, Unicode positions, imported-generation refresh, RPC capability advertisement, or live goal behavior. R462's source continuity does not establish scheduling or response order. None of these rows tests an Anneal integration at the newer version, changes an issue gate, or supplies a product guarantee.

No raw remote source snapshot was acquired. The matrix records `null` for old/new raw-file snapshot SHA-256 instead of treating a Git commit or rendered web page as a byte hash of an inspected file. Official tag/source pages must be independently inspected for semantic review.

## Evidence

The package retains the [six-row selector](support/frozen-cohort.csv), [baseline inventory](support/version-inventory-ebcdcad-581.csv), [baseline path set](support/baseline-report-paths.txt), [matrix](support/matrix.json), and [offline checker](support/check_matrix.py). The checker verifies exact baseline/current Git commit IDs, all six selector paths, report and metadata hashes, original subjects, old commit mentions, exact excerpts and locators, separate source/runtime/product labels, and seven later packages. It does not authenticate public GitHub source pages.

Official source was read on 2026-09-30 at the full commits linked above. The tag query was `git ls-remote https://github.com/leanprover/lean4.git refs/tags/v4.34.1 'refs/tags/v4.34.1^{}' refs/tags/v4.29.0 'refs/tags/v4.29.0^{}' refs/tags/v4.30.0-rc2 'refs/tags/v4.30.0-rc2^{}'`. It returned the three commit IDs listed under Applicability and no peeled lines. Fresh local preflight saw 8 GiB physical RAM and 158,743 free/inactive/speculative pages of 16 KiB, about 30.28% by the established admission estimate; disk had 18,163,828 KiB available. No compiler process was launched regardless of that marginal admission.

## Revalidation

Run `python3 reports/lean-429-430-comparison-to-4341-source-review/support/check_matrix.py` in a reference checkout containing the two frozen corpus commits. For R462, re-open the three 4.34.1 source files linked above and inspect `WaitForDiagnosticsParams`, `PlainGoalParams`, `TextDocumentIdentifier`, `TextDocumentPositionParams`, and `handleWaitForDiagnostics`. To advance any full row, compare its claim-specific 4.34.1 source and run its retained fixture under a newly admitted toolchain, separately recording runtime and Anneal integration results. Setup/prompt refinement: keep an explicit old-version pair and exact executable hashes, flag inventory-category outliers such as R462, and ask for a claim-specific newer-source or runtime result rather than a generic version bump.
