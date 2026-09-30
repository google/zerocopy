# #3730/#3731 coverage audit v39: selected-binary LLBC byte identity

## Summary

The [cold/warm selected-binary full-field report](../anneal-3731-i075-warm-bin-full-field-2026-09-29/REPORT.md) adds direct, bounded evidence to **#3731 I079** in published [v38](../anneal-3730-3731-final-coverage-audit-2026-09-29-v38/REPORT.md). Its two retained `subject_matrix_cli` LLBC files have different raw hashes. Exhaustive decoded comparison finds exactly one requested destination-path difference and 29 positional `short_names` leaf differences; the 15 typed-key/name entries agree. Both original compact JSON files round-trip byte for byte, so those differences explain their raw-byte inequality **in this pair**. The second source request was a retained-target **forced-dirty rebuild**, not a cache-fresh hit. The comparison establishes neither semantic equivalence nor a general LLBC canonicalizer.

All 333 row IDs, 345 suggestion destinations, inherited request fields and row order are preserved. Only I079 has a changed residual. Its status remains **partial**, and every gate and prerequisite is carried forward unchanged. D03, I075/I076, both prior I080 full-field comparisons, and every other suggestion retain their v38 residuals.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@f15ee4d3a9896c17b13c3167e364cb98f11a259f` and its v38 ledger. The source report reanalyzes two exact LLBCs preserved by a pinned Charon 0.1.210 `--bin subject_matrix_cli` cold request and same-source retained-target repeat with distinct initially absent destinations. Cargo marked its cached library Dirty after failing to read `.rlib` metadata, then recompiled the library and binary. The analysis itself used guarded Python only; it did not run Charon, Cargo, rustc, Aeneas, Lean, Lake, Anneal, a server or a network request.

The [v39 issue snapshot](support/live-issue-snapshot-v39.json) is byte-identical to v38's retained public issue text, originally fetched at `2026-09-30T01:30:04.750897+00:00`; it was not fetched again. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct I079 mapping

The baseline and repeat LLBCs are 54,276 and 54,279 bytes. Exactly **30 decoded leaves** differ: `/translated/options/dest_file` and 29 leaves under `/translated/short_names/`. Eleven of 15 short-name array positions contain different entries, while the typed-key/name maps match. Seven nested object-key-sequence differences occur only within those reordered array slots. Both files equal their own compact JSON reserialization byte for byte. No function declaration, embedded source contents, file-table entry, crate identity, error status or other decoded field differs. This gives one additional I079 observation about raw artifact identity versus keyed contents. **Basis: execution** of the source package's retained-data comparison.

The source report's forced-dirty producer observation remains separate from the current byte analysis. The new component does not test a cache-fresh warm request, producer skipping, Anneal output ownership, path-insensitive cache safety, arbitrary LLBC normalization or downstream semantic equivalence. I079 stays partial at its product gate. **D03 is context only**: its #3730 destination mapping is I075;I080, and this reanalysis adds no materialized-snapshot reuse, resource or product policy observation.

### Unchanged rows

The other **332 rows** preserve their v38 residual, prerequisite, status, gate and evidence fields. Their new v39 assessment says this selected-binary byte comparison does not directly exercise their remaining request. All 159 investigation titles, 174 #3730 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- Two completed outputs from one tiny `--bin` fixture and one pinned Charon tool were compared. The repeat was forced dirty because Cargo could not read cached library metadata. Cache-fresh behavior remains open.
- Different destination bytes and `short_names` order are genuine artifact differences. Equal keyed names and unchanged decoded model fields in these files do not prove Rust semantic equivalence or that every LLBC consumer ignores array order.
- This analysis adds no Charon invocation, changed-source negative control, producer attestation, output-collision protocol or Anneal cache-key implementation. It does not alter I075/I076, D03, D05 or E07 residuals.

## Evidence

- [source-package-inventory-v39.csv](support/source-package-inventory-v39.csv) hashes every retained file in published v38 and the new full-field source package. [validation-v39.json](support/validation-v39.json) records the published baseline, input and generated hashes, one direct ID, and row/link counts.
- The [builder](support/build_audit.py) derives every v39 row from v38 and checks all issue titles and suggestion destinations against the retained snapshot. The [checker](support/check.py) verifies inheritance, unchanged residuals, inventory hashes, both source checkers and metadata loading.
- The source report's [complete comparison record](../anneal-3731-i075-warm-bin-full-field-2026-09-29/support/comparison.json), two raw LLBCs, copied source results and checker bind every field difference and byte-exact JSON round trip. Its Python acquisition measured minimum 24.4379% reclaimable memory, peak self RSS 22,429,696 bytes and elapsed 0.02585 seconds. These are sampled short-run observations.
- Published v38's row-challenge SHA-256 is recorded in this report's metadata and verified by the checker.

## Revalidation

Run `python3 -B support/check.py` from this package. It validates retained evidence without starting compilers or servers. Reacquiring the source analysis requires the two exact LLBC hashes and a fresh ≥20% reclaimable-memory check under its 64 MiB RSS and five-second caps. The open cache-fresh producer and Anneal ownership questions require separate guarded production-path experiments.
