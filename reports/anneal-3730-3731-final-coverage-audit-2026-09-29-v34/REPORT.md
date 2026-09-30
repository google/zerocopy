# #3730/#3731 coverage audit v34: warm multi-unit Charon output ownership

## Summary

The finalized [warm multi-unit Charon report](../anneal-3731-i075-warm-multiunit-test-target-2026-09-29/REPORT.md) adds direct, bounded evidence to **#3731 I075 and I076** in published [v33](../anneal-3730-3731-final-coverage-audit-2026-09-29-v33/REPORT.md). Both remain **partial**. The source report's two unchanged-source, same-target `--test check` calls re-invoked all three Charon-producing units, but the warm call's one destination contained the binary LLBC despite requesting the test. This is a component producer/output attestation finding, not an Anneal V2 publisher result.

All 333 row IDs, 345 suggestion destinations, inherited request fields and row order are preserved. No status, gate or prerequisite changes. The [investigation matrix](support/investigation-final-v34.csv), [suggestion crosswalk](support/3730-crosswalk-final-v34.csv) and [333-row challenge](support/row-challenge-v34.json) append v34 fields to every row; only I075 and I076 have changed residuals. No #3730 suggestion row has a direct new mapping.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@71fc3a50aadd50902bbbd22743ce884218af391e` and its v33 ledger. The new source component used pinned Charon 0.1.210 and nightly Rust/Cargo 2026-05-31 on macOS arm64. One dependency-free fixture had a library, a binary and an integration test. Two sequential `charon cargo --preset aeneas --dest-file <distinct destination> -- --manifest-path <same manifest> --test check --offline --locked -j 1 -v` calls used the same source path and one retained private Cargo target, with `CARGO_INCREMENTAL=0`. The second was warm. The source package records exact binary, fixture and output hashes, commands and resource guards; it did not run the Anneal V2 extraction publisher.

Public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again at `2026-09-30T01:16:45.093927+00:00` and retained verbatim in the [v34 snapshot](support/live-issue-snapshot-v34.json). #3730 was closed and #3731 open, each with one comment. Body and comment bytes match v33. #3730 body/comment SHA-256 values are `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values are `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Row | Direct observation | Remaining scope |
| --- | --- | --- |
| I075 | On an unchanged-source, same-target warm `--test check` repeat, full verbose logs show library, test and binary Charon drivers all ran; the call exited 0 and created a new parseable error-free LLBC at a fresh destination. Thus this selected warm request **did not skip** the producing units. | Other target kinds/wrappers, and an Anneal policy that rejects success when the requested unit does not run or is not the selected output. |
| I076 | The cold call's destination identified test `check`; the warm call's destination identified binary `subject_matrix_cli` although `check` was compiled and the command succeeded. A distinct destination excludes reuse of the old output file. | Complete Cargo unit key, output ownership and attestation, concurrent arbitration, invalidation and actual Anneal publication. |

The cold driver order was library, binary, test; the warm order was library, test, binary. That order matches the final destination in each observed cell, but does not establish write syscall interleaving or a general last-writer rule. The two outputs are error-free Charon LLBC with distinct retained hashes. The source report's parser correction read the saved LLBCs after execution; the runner was not replayed for that correction. **Basis: execution and retained-output parsing** in the source report.

### Unchanged rows

The other **331 rows**, including I020, D03, D06, D07 and every #3730 suggestion, preserve their v33 residual, prerequisite, status, gate and evidence fields. Their new v34 assessments state that this warm multi-unit Charon cell does not directly exercise their remaining request. The v33 profile/cfg slug and D03 clarification remain inherited evidence; v34 does not reinterpret them.

## Boundaries

- This is one tiny, sequential, warm `--test check` fixture with one target directory and distinct destinations. It does not measure other target kinds, true concurrency, cancellation, cache sharing or representative Anneal workloads.
- A successful Charon process and parseable LLBC do not attest that the single destination belongs to the requested Cargo unit. The run did not test a V2 output rejection or collision policy.
- Resource values are sampled guards, not physical peaks or scaling measurements. Across both calls, the maximum sampled process-group RSS was 137,392 KiB; the warm call's maximum was 78,464 KiB. The minimum estimated reclaimable memory was 23.333%.
- The public issue snapshot preserves request scope at fetch time. No issue or product state was changed.

## Evidence

- [source-package-inventory-v34.csv](support/source-package-inventory-v34.csv) hashes every retained file in published v33 and the I075 source package. [validation-v34.json](support/validation-v34.json) records input/generated hashes, exact direct IDs and row/link counts.
- The [builder](support/build_audit.py) derives every v34 row directly from v33 and checks 159 investigation titles, 174 suggestion destinations and 345 links against refreshed public text. The [checker](support/check.py) checks every inherited field and unchanged residual, inventory hash, issue snapshot and both source checkers; it calls `reference._load_report` on v33, the source report and v34.
- The source report's [results](../anneal-3731-i075-warm-multiunit-test-target-2026-09-29/support/results.json), complete verbose logs, two retained LLBCs and checker bind the two observed cells. Source checker and metadata acceptance passed in place and from a relocated copy during this audit validation.
- Published v33's row-challenge SHA-256 is `b5b5a1ed3d6baa86b541e06032475bce21cbe3ca0732561f46132cfa90126f5e`.

## Revalidation

Run `python3 -B support/check.py` from this package. It verifies retained evidence without starting Charon, Cargo, Rustc, Lean, Lake or Anneal. Reacquiring the source cell is a separate observation subject to its pinned tools and resource guards.
