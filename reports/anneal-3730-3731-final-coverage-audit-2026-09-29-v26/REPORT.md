# #3730/#3731 coverage audit v26: Cargo subjects, incremental targets and Charon repeat order

## Summary

This revision extends the [v25 333-row challenge](../anneal-3730-3731-final-coverage-audit-2026-09-29-v25/REPORT.md) with six completed, bounded reports. It preserves all v25 row fields, 159 investigation IDs, 174 suggestion IDs, 345 exact crosswalk destinations, original request text, and every status. Exactly **12** rows receive new residual and prerequisite wording: **I020, I076, I080, I113, I125, I148, D03, D07, E07, J01, J02 and L02**. The [investigation ledger](support/investigation-final-v26.csv), [suggestion crosswalk](support/3730-crosswalk-final-v26.csv) and [333-row challenge](support/row-challenge-v26.json) record the per-row evidence paths and limits.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

The checked-in Anneal V2 source subject is `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`. The experiments use exact copied resolver/scanner source or pinned Charon/Cargo binaries as their own reports specify. They do not execute a current V2 extraction-to-verification service. A row marked partial describes research coverage, not product acceptance.

## Applicability and issue scope

Public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again on 2026-09-29. The complete returned text and metadata are retained in [`support/live-issue-snapshot-v26.json`](support/live-issue-snapshot-v26.json). Their four body/comment SHA-256 values exactly match v25 and the frozen source snapshot: #3730 body `81bdc705...`, comment `7544fde7...`; #3731 body `0375e6dc...`, comment `4cc53278...`. #3730 remains closed and #3731 open. The checker compares the **full bytes**, IDs, title text and crosswalk destinations, not just these displayed prefixes.

The [offline builder](support/build_audit.py) derives v26 solely from v25, the retained live snapshot and the six report packages below. It does not fetch, install, or edit any previous report. The v26 checker verifies that every field inherited from v25 remains equal in both CSV matrices and in the row challenge. The additional v26 columns identify only the new evidence relation, residual, next prerequisite and evidence paths.

## Twelve exact row updates

| Row | New bounded finding | Remaining claim |
| --- | --- | --- |
| **I020** | The [V2 Cargo root-selection probe](../anneal-v2-cargo-root-selection-multipackage-2026-09-29/REPORT.md) found that the copied resolver included a non-default workspace member and a binary with disabled `required-features`, unlike matched Cargo checks. The separate [feature-slug probe](../anneal-v2-feature-subject-slug-collision-2026-09-29/REPORT.md) found one V2 LLBC filename for default/selected feature compilations whose Charon bodies were `7`/`11`. | Neither harness called the full V2 CLI. A selected Charon invocation, complete subject key, proof-context selection, visible mismatch and cross-stage rejection remain. |
| **I076** | The feature-slug probe adds a checked-in V2 locator collision to the prior sibling-library same-name Charon witness. | No overwrite was observed. Complete unit identity, broader host/target/profile/cfg/tool matrix, output ownership, invalidation and concurrent collision rejection remain. |
| **I080** | The [incremental target-layout matrix](../anneal-3731-i080-incremental-target-layout-matrix-2026-09-29/REPORT.md) ran private/shared targets with incremental compilation off/on, cold and warm: all 16 Charon requests yielded parseable LLBC with the same selected local body projection. Shared cells logged Cargo lock waits; incremental-on targets retained more files and bytes. | One tiny path-controlled fixture, no source edits or cancellation. Representative sustained load, path-sensitive changes, incremental-on cancel/restart, many-worker cleanup and physical resource economics remain. |
| **I113** | The [full-chain transient accounting probe](../anneal-3731-full-chain-transient-workspace-accounting-2026-09-29/REPORT.md) observed 24 stage boundaries and 331 interval samples in one successful tiny chain. Its largest sampled disposable run-directory regular-file allocation was 4,825,088 bytes. Twelve Cargo-target files and 28,672 allocated bytes were captured before deletion. Four selected external roots had zero net `du` change at 1 KiB resolution. | These are sampled lower bounds and selected net-root checks. Cumulative/outside writes, short-lived temporary peaks, physical extents, dependencies and multiworker scaling remain. |
| **I125** | The [pinned plugin path-alias probe](../anneal-3731-i125-plugin-cwd-path-alias-v4-30-0-rc2/REPORT.md) shows that `--plugin=file` resolves a bare name relative to cwd through `realPath`; `LEAN_PATH` did not supply it. A symlink target switch yielded v1 then v2 initializer markers in newly opened file workers, while the old file still answered. | Initializer markers are execution witnesses, not loaded-binary attestation. ABI compatibility, multiple native dependencies, process mapping, worker ownership and Anneal routing remain. |
| **I148** | The [real zerocopy library repeat probe](../charon-zerocopy-library-repeat-order-nightly-2026-05-31/REPORT.md) found that, after normalizing one destination path and omitting an identically keyed but differently ordered `short_names` array, all other LLBC bytes matched across three Charon runs. The pinned Aeneas importer clears that field. | All three LLBCs had `has_errors: true` and 13 warnings despite exit 0. Aeneas and Lean were not run; successful larger-corpus translation, downstream cost/comparator and V2 workload determinism remain. |
| **D03** | The I080 matrix adds direct cold/warm, private/shared and incremental-on Cargo reuse evidence for this suggestion. | The run did not mutate materialized snapshots, attest the Charon-producing unit, or evaluate representative parallel economics. It adds **no** D06 cancellation claim. |
| **D07** | The I020/I076 feature-slug witness gives two feature-selected Charon bodies one current V2 LLBC locator. | This is one feature slice, not an invalidation matrix or a witnessed Anneal overwrite. Collision-safe publication and full compilation-unit dimensions remain. |
| **E07** | The I148 zerocopy run adds a real-library short-name ordering case: complete keyed entries are equal across runs, and pinned Aeneas source clears that cache before translation. | The LLBCs have `has_errors: true`; there is no successful generated-source or Lean semantic-sameness oracle. Broader changes and an authenticated obligation comparator remain. |
| **J01** | The I113 replay supplies stage-attributed allocation and one observed transient baseline for a tiny full chain. | It is one worker, not real generated-project disk scaling. Representative prepared projects, multiple workers, archive/shared inputs and true peak/write economics remain. |
| **J02** | The I113 replay includes the Cargo target files deleted after compilation and sampled stage-by-stage file/allocated-block counts. | It does not classify every copied or written byte; short-lived files, cumulative/outside writes, dependencies and worker scaling remain. |
| **L02** | The I113 replay records stage-local file effects and zero net `du` change in four selected external roots. | Net equality at 1 KiB resolution cannot exclude writes or create/delete cycles. A complete adapter-wide filesystem-effects trace remains. |

The remaining 321 rows retain their v25 residuals and prerequisites exactly. **F20** remains unchanged because I113 did not exercise an Anneal prepared archive or fresh consumer. **D05 and E06** remain unchanged because I148's error-bearing Charon output did not establish concurrent determinism or successful generated-source equality. **D06** remains unchanged because I080's new matrix had no cancellation. I125 has no direct #3730 suggestion destination. The six new reports each state their executed command/tool subject, retained raw or summarized evidence, and limits; [the v26 source inventory](support/source-package-inventory-v26.csv) hashes 133 non-bytecode files across those packages, including the reviewer-corrected I148 report text.

## Evidence and revalidation

[`support/validation-v26.json`](support/validation-v26.json) pins all five base inputs, four generated ledgers/inventories, counts, source package names and the 12 changed IDs. Each affected row links to the relevant report, retained result or raw specimen, and its source checker. No status or gate category changes.

Run `python3 -B support/check.py` from this package. The checker is read-only and offline: it verifies the v25 field-preserving extension, complete live issue text against the frozen snapshot, 159/174 title and ID sets, 345 links, 12 exact evidence mappings, 133 source-file hashes, and the six source package checkers. The builder can regenerate the derived v26 files in this package with `python3 -B support/build_audit.py`; it does not modify v25, CATALOG, or another source package.

## Boundaries

- Resolver and slug harnesses compile exact V2 source modules with small surrounding stubs; they do not establish extraction, model/proof selection, or verification behavior of the full CLI.
- The I080 target-layout run did not test cancellation or source mutation. The earlier incremental-off cancellation report remains separate evidence and is not attributed to this matrix or D03.
- The I148 zerocopy LLBC is error-bearing. The matching non-cache serialization cannot be used as a success claim for Aeneas, Lean or Anneal.
- I113's sampled maximum and external-root `du` comparisons do not measure true temporary peak or exclude outside writes. I125's initializer marker does not attest every loaded mapping or ABI interaction.
- This package does not alter existing reports or CATALOG. Later work on other rows requires a subsequent revision.
