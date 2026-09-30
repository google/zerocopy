# #3730/#3731 coverage audit v45: rich term goals, Unicode spans, and identity ablation

## Summary

Three reviewed source packages add bounded evidence to the published [v44 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v44/REPORT.md): a [nested Lake rich term-goal probe](../anneal-3731-lake-rich-term-goal-nested-2026-09-30/REPORT.md), a [Charon Unicode local-span probe](../anneal-3731-i079-unicode-charon-spans-2026-09-30/REPORT.md), and a [symbolic identity-ablation model](../anneal-3731-i145-cross-layer-identity-ablation-model-2026-09-30/REPORT.md). Residuals change only for **I043, C02, I079, and I145**. The Unicode source-coordinate observation is bounded context for **D05, A02, and A08**; those three residuals are unchanged. These observations do not implement an Anneal V2 service or close any product gate.

All **333 row IDs**, **159 investigation IDs**, **174 #3730 suggestions**, **345 suggestion destinations**, original issue fields and row order are preserved. Every status, gate and next prerequisite is carried forward unchanged. I043, C02, I079 and I145 remain **partial** at the **product** gate.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability and current issue state

The parent is published `upstream/reference@d8a86362f68d2f84c6f1165e4fe3bffa35529ee2`. A fresh public REST fetch on 2026-09-30 found #3730 closed and #3731 open, with one comment each. Their bodies and comments are byte-identical to the [retained v44 snapshot](../anneal-3730-3731-final-coverage-audit-2026-09-29-v44/support/live-issue-snapshot-v44.json); [v45's refreshed snapshot](support/live-issue-snapshot-v45.json) preserves the exact texts and fetch time. The four body/comment SHA-256 values remain in `REPORT.json`. Thus the issue agenda, 159 titles, 174 suggestion rows and 345 destination relationships did not change during this update.

## Direct row mapping

| Row | New bounded observation | Remaining decision |
| --- | --- | --- |
| I043 | The pinned Lake server queried one imported nested `Eq.trans` proof at 11 positions with four goal APIs. Eight inner positions had matching plain/rich term targets and ranges while both tactic APIs returned empty lists; three positions had null term replies. A fresh same-text batch accepted the proof and reported no theorem axioms. | General term selection, unsaved/error and lifecycle controls, exact import/version fences, generated/projected Anneal proof, Rust source coordinates and complete-obligation batch comparison remain open. |
| C02 | `Lean.Widget.getInteractiveTermGoal` is now directly paired with `plainTermGoal` at all 11 positions, filling v44's named rich-term endpoint gap for this fixture. Rich tagged target text matches the plain text at eight non-null positions; `ctx` and `term` are opaque RPC references. Plain/rich tactic counts also match. | Reference dereference/expiry, other proof shapes and server lifecycle, Anneal projection and proof verification remain open. |
| I079 | A retained three-line Rust source and error-free Charon LLBC give seven exact local `source_text`/span matches. In this fixture, UTF-8 byte, Unicode scalar and UTF-16 hypotheses have 7, 6 and 4 mismatches; a fixture-specific display-cell calculation has zero. | General Unicode width behavior, generated-file spans, source-to-Lean declaration mapping, annotation attachment and Anneal provenance/cache policy remain open. |
| I145 | A standard-library finite model enumerates 65,536 independent binary cross-stage states. For its declared oracles, content, strict lineage and current-request admission need 3, 12 and 16 modeled fields respectively. Its 31 present-field omissions have explicit collisions; 17 absent-field controls leave keys unchanged. | These counts follow the model's chosen policies. Actual Cargo→Charon→Aeneas→Lake→Lean→MCP causality, identity envelope, correctness and product routing remain untested. |

D05, A02 and A08 receive only the Unicode span package as bounded source-coordinate context. It says nothing new about concurrent Charon determinism, locator policy or hash/revision routing in a product. Their v44 residuals and all prerequisites are preserved.

## Evidence and boundaries

The Lake run is one disk-identical proof version and RPC session. Its eight non-null rich term objects agree with plain target text and ranges; the three null positions have no target or range to compare. The proof uses `Eq.trans` over reflexive subterms. The batch file has equal text and a different filename, so its success is a same-text oracle for this import, not a module-identity comparison.

The Charon run covers one tiny local source under one installed binary. Its display-cell calculation is deliberately a fixture oracle for the observed emoji and combining mark, not a general rule for Charon or editor coordinates. The identity model's minima are conditional on independent axes and explicit oracle projections; they are not an empirical end-to-end pipeline result or a globally minimum cache schema.

[source-package-inventory-v45.csv](support/source-package-inventory-v45.csv) hashes every retained file in the v44 parent audit and the three exact source package copies. [validation-v45.json](support/validation-v45.json) records input and generated hashes, counts, changed IDs and source packages. The [builder](support/build_audit.py) derives every v45 row from v44, checks current issue headings and destination mappings, and writes the ledgers. The [checker](support/check.py) verifies inheritance, changed-row limits, source hashes and checkers, inventory and metadata. It does not rerun Charon, Lake or Lean.

Run `python3 -B support/check.py` from this package. The next product work is the inherited version-fenced Anneal generated/projected proof and source-map integration, plus actual full-chain identity routing and complete-obligation batch comparison. This report records evidence for agenda rows; it does not select an architecture.
