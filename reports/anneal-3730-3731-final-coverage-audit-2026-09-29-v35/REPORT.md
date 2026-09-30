# #3730/#3731 coverage audit v35: warm selected-binary Charon control

## Summary

The [selected-binary Charon report](../anneal-3731-i075-warm-bin-target-2026-09-29/REPORT.md) adds direct, bounded evidence to **#3731 I075 and I076** in published [v34](../anneal-3730-3731-final-coverage-audit-2026-09-29-v34/REPORT.md). Both stay **partial**. Under a pinned `--bin subject_matrix_cli` request, the second unchanged-source call retained the first call's target directory, but Cargo marked the library **Dirty** because it could not read cached `.rlib` metadata. It then invoked library and binary Charon drivers and created an error-free LLBC whose decoded crate matched the requested binary. This is a positive selected-output control under a dirty rebuild, contrasted with v34's retained-target `--test check` mismatch; it is **not a cache-fresh warm producer test**.

All 333 row IDs, 345 suggestion destinations, inherited request fields and row order are preserved. No status, gate or prerequisite changes. The [investigation matrix](support/investigation-final-v35.csv), [suggestion crosswalk](support/3730-crosswalk-final-v35.csv) and [333-row challenge](support/row-challenge-v35.json) append v35 fields to every row. Only I075 and I076 have changed residuals; **no #3730 suggestion receives new direct evidence**.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@641f55cfd54fcd3c6ba0de67643a62a29df4f3a1` and its v34 ledger. The source component used pinned Charon 0.1.210 and nightly Rust/Cargo 2026-05-31 on macOS arm64. One dependency-free fixture had a library, binary and integration test. Two sequential `charon cargo --preset aeneas --dest-file <distinct destination> -- --manifest-path <same manifest> --bin subject_matrix_cli --offline --locked -j 1 -v` calls used unchanged source, the same path and one retained private Cargo target with `CARGO_INCREMENTAL=0`. Retaining that target did not make the second call cache-fresh: verbose stderr recorded `Dirty subject_matrix ... couldn't read metadata for ... libsubject_matrix-....rlib`. The report preserves exact tool/input/output identities, logs and resource guards. It did not run the Anneal V2 extraction publisher.

Public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again at `2026-09-30T01:30:04.750897+00:00` and retained verbatim in the [v35 snapshot](support/live-issue-snapshot-v35.json). #3730 was closed and #3731 open, each with one comment. Body and comment bytes match v34. #3730 body/comment SHA-256 values are `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values are `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Row | Direct observation | Remaining scope |
| --- | --- | --- |
| I075 | Cold and retained-target selected-binary calls logged library and binary `charon-driver rustc` invocations, exited 0 and created parseable LLBC at distinct initially absent destinations. The second invocation followed Cargo's **Dirty** decision for missing cached `.rlib` metadata, so it attests a rebuild path, not a cache-fresh skip path. | Fresh-cache producer behavior, other targets/wrappers, tool revisions and an Anneal policy that rejects a missing or wrong requested output. |
| I076 | Both outputs decoded as `subject_matrix_cli`, matching the selected binary under the observed rebuild. This positive control bounds, but does not erase, the v34 retained-target selected-test mismatch. | Cache-fresh output behavior, complete Cargo compilation-unit identity, producer ownership, general output-writer order, collision rejection and actual Anneal publication. |

The two raw LLBC hashes differ, but the source report does not establish a semantic difference or its cause. The cold and dirty-rebuild driver order was library then binary. Both observations are sequential and share one target, with fresh destinations; they do not prove cache-fresh behavior, general last-writer behavior or concurrent safety. The v34 warm selected-test stderr likewise logged a missing `.rlib` metadata Dirty decision, so the contrast here is selected target/output under retained-target rebuilds. **Basis: execution** in the source reports.

### Unchanged rows

The other **331 rows**, including I020, D03, D07 and every #3730 suggestion, preserve their v34 residual, prerequisite, status, gate and evidence fields. Their new v35 assessment states that this selected-binary cell does not directly exercise their remaining request. Earlier slug collisions, the warm test mismatch and the D03 clarification remain inherited evidence.

## Boundaries

- This is one tiny, sequential, retained-target `--bin` fixture under one exact Charon/Cargo pin. Its second call was Dirty, not cache-fresh. It does not test other target kinds, concurrent writers, cancellation, cache sharing or representative Anneal workloads.
- A matching decoded crate is a positive selected-output control, not proof of a complete unit key, authenticated producer or universal Charon output ownership.
- The source report's sampled guards are not physical peaks or scaling measures: its minimum estimated reclaimable memory was 23.012%, and maximum sampled process-group RSS was 124,704 KiB.
- The public issue snapshot preserves request scope at fetch time. No issue or product state was changed.

## Evidence

- [source-package-inventory-v35.csv](support/source-package-inventory-v35.csv) hashes every retained file in published v34 and the selected-binary source package. [validation-v35.json](support/validation-v35.json) records input/generated hashes, exact direct IDs and row/link counts.
- The [builder](support/build_audit.py) derives every v35 row directly from v34 and checks 159 investigation titles, 174 suggestion destinations and 345 links against refreshed public text. The [checker](support/check.py) checks every inherited field and unchanged residual, inventory hash, issue snapshot and both source checkers; it calls `reference._load_report` on v34, the source report and v35.
- The source report's [results](../anneal-3731-i075-warm-bin-target-2026-09-29/support/results.json), complete verbose logs, two retained LLBCs and checker bind the observations. Source checker and metadata acceptance are revalidated in place and from a relocated copy before handoff.
- Published v34's row-challenge SHA-256 is `f9879b9386c6fbf7e5a622acad319fb36f4ff770d4dd298b89a41555754db948`.

## Revalidation

Run `python3 -B support/check.py` from this package. It verifies retained evidence without starting Charon, Cargo, Rustc, Lean, Lake or Anneal. Reacquiring the source cell is a separate observation subject to its pinned tools and resource guards.
