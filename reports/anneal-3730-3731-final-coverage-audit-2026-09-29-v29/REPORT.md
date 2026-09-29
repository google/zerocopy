# #3730/#3731 coverage audit v29: dirty Cargo reuse, imported goals and translation repeats

## Summary

Three finalized component reports sharpen **eight partial rows** in the published [v28 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v28/REPORT.md): investigations **I043, I080 and I148**, plus #3730 suggestions **C02, D03, D05, E06 and E07**. All 333 IDs, 345 #3730→#3731 destination links, inherited request text, statuses and gate categories are unchanged. The [investigation matrix](support/investigation-final-v29.csv), [suggestion crosswalk](support/3730-crosswalk-final-v29.csv) and [333-row challenge](support/row-challenge-v29.json) append an exact v29 residual, prerequisite and scope assessment to each inherited row.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

The [I080 source edit/revert probe](../anneal-3731-i080-source-edit-revert-incremental-cache-2026-09-29/REPORT.md) adds a sequential dirty shared-target transition under incremental compilation on and off. The [Lake-launched position probe](../anneal-3731-lake-launched-position-context-v4-30-0-rc2/REPORT.md) compares plain and rich goals at seven positions through a prepared local import and a fresh batch control. The [I148 multi-function repeat](../anneal-3731-i148-multifunction-translation-repeat-2026-09-29/REPORT.md) adds successful sequential and overlapping Charon extractions, five matching Aeneas split-file inventories and one direct Lean compilation. These are bounded components; no Anneal V2 service or representative product archive was executed.

## Applicability

The baseline is published `reference@baa5c11b71289c5bf124a3f0fdc4194cf758c527` and its v28 ledger. The Charon probes use pinned local Charon 0.1.210 and nightly-2026-05-31 Cargo/rustc on macOS arm64. The position probe uses `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) with a tiny two-package Lake project. I148 also uses the pinned Aeneas bundle and cached Lean. Exact tools, source bytes, options, commands, resource guards and support records are in the three source reports. Their fixture outputs do not generalize to arbitrary generated obligations, path-sensitive Cargo inputs, full Lean import graphs or an Anneal scheduler.

The public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again on 2026-09-29 and retained verbatim in the [v29 snapshot](support/live-issue-snapshot-v29.json). #3730 was closed and #3731 open, each with one comment. All four bodies matched v28 and the frozen v22 request snapshot byte-for-byte. #3730 body/comment SHA-256 values are `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values are `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Source report | Investigation | Direct #3730 suggestions | Measured slice |
| --- | --- | --- | --- |
| Source edit/revert shared Cargo target | I080 | D03 | Six sequential shared-target requests per incremental mode, plus cold oracles, distinguish edited A, reverted A and unchanged B selected LLBC function bodies; incremental-on target files and allocation grew in this short sequence. |
| Lake-launched position context | I043 | C02 | Seven paired plain/rich cursor positions through one compiled import: four goal contexts, two empty lists and one null, with clean build, setup-file and batch controls. |
| Multi-function Charon/Aeneas repeat | I148 | D05, E06, E07 | Three same-target serial and two overlapping private-target Charon runs give error-free LLBC equal after destination and typed `short_names` ordering normalization; five Aeneas split-file inventories match byte-for-byte, and one set compiles with five checked names. |

Every mapped row remains **partial**. I080/D03 still need dirty-target concurrency, cancellation, path-sensitive inputs, full output and representative resource/ownership policy. I043/C02 still need an Anneal projected/generated proof, exact-version fence and rich-reference lifecycle. I148/D05/E06/E07 still need the intended Anneal generation flags, provenance-safe identity, representative workload, downstream Lake invalidation and obligation-level comparison. The I148 Lean compilation and stated axiom inventory establish the selected generated definitions, not Rust refinement or arbitrary LLBC semantic equivalence. Per-row residuals and prerequisites in the ledgers retain those boundaries.

### Deliberate exclusions and unchanged rows

Nine adjacent rows receive specific context-only explanations while their v28 residual, prerequisite and evidence fields remain unchanged: **D06, F20, I079, I084, I132, I044, I046, I075 and I105**. D06 and I105 require cancellation/interruption; every new Charon request finished. F20 requires full-chain generated-module rebuild isolation and byte accounting, not these selected target inventories. I079 asks for source relocation/provenance association, which output-destination and `short_names` variation does not test. I084/I132 require broader semantic or diagnostic comparator controls. I044 needs opaque rich-reference lifecycle, I046 retains its already complete narrow failed-elaboration status, and I075 requires authenticated Cargo subject selection. The [row challenge](support/row-challenge-v29.json) states each exclusion separately.

Each of the other **316 unchanged rows** names its own inherited gate and says why none of these three reports directly exercises it. Thus eight direct + nine context-only + 316 other unchanged = 333. No finite component result changes a status or gate.

## Boundaries

- The I080 edit/revert sequence ran Charon processes sequentially, with equal-length source roots and one tiny path-only workspace. It does not erase the prior longer-root build-script counterexample, measure dirty concurrent lock contention, or capture transient peak memory with its 0.1-second headroom samples.
- The Lake position fixture used one successful disk-identical document and a local compiled import. It does not combine unsaved edits, errors, macros, cancellation or projected Rust positions with those imported seven points. Rich display text equality does not attest opaque object identity or lifetime.
- I148 normalizes only destination and six typed `short_names` entries. It does not prove arbitrary order changes safe for every consumer, complete Rust-to-Lean equivalence, or Lake cache reuse. Its concurrent intervals bracket subprocess calls rather than independently timestamping OS starts/exits.
- The public issue snapshot establishes request scope at its fetch time. It does not alter the issues or reclassify the requests as satisfied.

## Evidence

- [source-package-inventory-v29.csv](support/source-package-inventory-v29.csv) records SHA-256 for every retained file in published v28 and the three finalized reports. [validation-v29.json](support/validation-v29.json) records the input and generated hashes, full row/link counts, direct/context IDs, unchanged status/gate counts and source package list.
- The [offline builder](support/build_audit.py) derives the full v29 ledger from v28 and the preserved live issue text. The [self-checker](support/check.py) compares every inherited field across all 333 rows and both matrices, verifies the 159 investigation titles and 174 suggestion/destination mappings against the live text, checks all evidence paths and source hashes, and runs v28 plus the three new report checkers. Each source report retains its own raw outputs and checker.
- Published v28's row-challenge SHA-256 is `60802186d258eda42c5b4cf5316463032a151e04d2522050f0f5038bbd491b7e`. The inherited Anneal source revision is `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`; none of these probes runs it as an end-to-end verification service.

## Revalidation

Run `python3 -B support/check.py` from this package or an unchanged copy of the reference tree. It checks retained evidence without starting Cargo, Charon, Aeneas, Lake, Lean or Anneal. If issue text or source packages change later, preserve v29's exact snapshot and hashes and add a later audit revision.
