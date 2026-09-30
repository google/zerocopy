# #3730/#3731 coverage audit v42: local LLBC source spans

## Summary

The [retained ASCII-local source-span report](../anneal-3731-i079-local-span-source-text-2026-09-29/REPORT.md) adds bounded direct evidence to **#3731 I079** in published [v41](../anneal-3730-3731-final-coverage-audit-2026-09-29-v41/REPORT.md). It checks all 16 retained I080 edit/revert LLBCs against the baseline Rust fixture and its hash-verified one-expression edited state. All **64** testable local `app/src/lib.rs` file-ID-0 item spans select exactly their serialized `item_meta.source_text` in the corresponding source state. This is a fixture-specific ASCII source-provenance observation, not an authenticated cross-layer map or a general source-span convention.

All **333 row IDs**, **345 suggestion destinations**, inherited request fields and row order are preserved. Only **I079** has a changed residual. It remains **partial**, and every status, gate and next prerequisite is carried forward unchanged. **I149 is context only**: no compiler-authenticated Rust→Charon→Aeneas→Lean declaration mapping was obtained. I149 and the other 331 rows retain their v41 residuals.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@974c035a2a32b8b873ad560b572eeda7a69679bb` and its v41 ledger. The source report reanalyzes exact LLBC bytes retained from pinned Charon 0.1.210's sequential shared-target source edit/revert experiment, with incremental compilation off and on and cold baseline/edited oracles. The new comparison used guarded offline Python only; it did not run Charon, Cargo, rustc, Aeneas, Lean, Lake, Anneal, a server or a network request.

The [v42 issue snapshot](support/live-issue-snapshot-v42.json) is byte-identical to v41's retained public issue text, originally fetched at `2026-09-30T01:30:04.750897+00:00`; it was not fetched again. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct I079 mapping

Each of the 16 LLBCs embeds an `app/src/lib.rs` file-ID-0 content field equal byte for byte to the expected baseline or edited source state. Four local single-line function items per LLBC have `item_meta.source_text` equal to the corresponding ASCII source slice at their recorded span: **64/64 exact matches**. The two edited-A shared-target outputs and two edited cold oracles contain `wrapping_add(2)` in `step`; unchanged B and reverted A contain baseline `wrapping_add(1)`. A shifted-start slice and inclusive-end slice fail against the retained source text. For these ASCII intervals, the matches support **one-based lines, zero-based columns and exclusive ends**. **Basis: execution** of the source package's retained-data comparator.

Another **32 local item records** point to generated Rust file ID 1, including duplicate function/global representations of `SNAPSHOT_VALUE`. No independent generated `.rs` state was retained outside those LLBCs, so these records are **excluded** from the source-state check. All tested source bytes are ASCII: byte, Unicode-scalar and UTF-16 column units coincide here, and the general column unit remains **undetermined**. Non-ASCII, multiline, moved-source and generated-file conventions remain open. The serialized spans and text come from the same LLBC producer; the independent baseline and reconstructed edited hashes constrain the source-state choice but do not authenticate a compiler cross-layer mapping. This is distinct from the earlier I079 selected-binary cold/warm full-field byte-identity analysis. I079's product gate and next prerequisite remain unchanged.

### I149 context and unchanged rows

The source report records local source-text and span agreement in one Charon fixture. It supplies no Rust→Charon→Aeneas→Lean→obligation identity graph, navigation consumer, or authenticated generated-declaration range. I149's residual, status, gate, prerequisite and evidence fields remain unchanged. The other **331 rows** also retain their v41 residuals and prerequisites. All 159 investigation titles, 174 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- The 64 matched intervals are single-line local functions in one ASCII `app/src/lib.rs`; the 32 generated-file local item records lack an independent source state and were excluded.
- Exact text matching does not prove Unicode column units, Charon source-map completeness, arbitrary annotation association or a safe source-identity/cache-key rule.
- The comparison adds no producer invocation, generated-source oracle, Aeneas/Lean correspondence, Anneal publication behavior or general LLBC normalization.

## Evidence and revalidation

- [source-package-inventory-v42.csv](support/source-package-inventory-v42.csv) hashes every retained file in published v41 and the new local source-span package. [validation-v42.json](support/validation-v42.json) records the published baseline, input and generated hashes, one direct ID, and row/link counts.
- The [builder](support/build_audit.py) derives every v42 row from v41 and checks issue titles and suggestion destinations against the retained snapshot. The [checker](support/check.py) verifies inheritance, unchanged residuals, inventory hashes, both source checkers and metadata loading.
- The source report's [comparison record](../anneal-3731-i079-local-span-source-text-2026-09-29/support/comparison.json), copied 16 raw LLBCs, two Rust source states, original source results and checker bind all 64 matches, 32 exclusions and offset controls. Its guarded Python run sampled minimum 25.8722% reclaimable memory, peak measured self RSS 22,396,928 bytes and elapsed 0.1321 seconds.
- Published v41's row-challenge SHA-256 is recorded in this report's metadata and verified by the checker.

Run `python3 -B support/check.py` for offline revalidation. Reacquiring the source analysis requires exact retained hashes and a fresh >20% reclaimable-memory preflight under its 64 MiB RSS and five-second caps. Unicode and generated-source conventions require separate independently retained source oracles.
