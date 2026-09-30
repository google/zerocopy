# R494 Ninja source and release disposition

## Summary

The [R494 matrix](support/matrix.json) freezes the original report's five exact `## Summary` paragraphs, section locator, subjects and evidence map at reference `48b8693b47bb3e33ada4fe6fbb437adad40bbb7e`. On 2026-09-30, official Ninja `master` still resolved to R494's pinned [`4e4df1e567eb3c1475a51af261cba2bfff60b4be`](https://github.com/ninja-build/ninja/commit/4e4df1e567eb3c1475a51af261cba2bfff60b4be). The forward source range on that branch is empty, so no changed file or claim drift from a newer `master` revision can be reported.

The [latest official GitHub release](https://github.com/ninja-build/ninja/releases/tag/v1.13.2) is `v1.13.2` at [`3441b633c2fe2c494e958780ba0f4227b1327634`](https://github.com/ninja-build/ninja/commit/3441b633c2fe2c494e958780ba0f4227b1327634), published 2025-11-20. Its Git ref points directly to a commit. The official compare metadata reports **diverged** histories relative to R494's `master` pin: from the release tag to the pin, 196 commits ahead and 60 behind. Its manual blob differs from R494's pinned manual blob. This release is recorded as a separate source identity, not treated as a forward recheck of R494's 2026 development-line claims.

## Applicability

R494 compares historical Make, GNU Make 4.4.1, and Ninja's generator/executor boundary, then derives a conditional Anneal architecture judgment. This supplement reviews Ninja's exact pinned source. It does not revise the 1979 Make publication, GNU Make manual/release, Chromium-era Ninja history, or Anneal design pin. The selector is R494 in the 581-row inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The current frozen corpus contains 596 report packages; all 15 additions are reconciled and hashed in the matrix.

## Claim mapping and source finding

R494's first two Summary paragraphs set the combined Make/Ninja question and Make background. Its third paragraph states Ninja's policy-removing design and later executor mechanisms, including command tracking, dependency discovery, `restat`, pools, dynamic dependencies, validations, and GNU jobserver participation. Its fourth and fifth paragraphs are conditional Anneal interpretation and limitation. The exact paragraphs and their evidence-map IDs are preserved in the matrix.

R494 maps its present-tense Ninja claims to `doc/manual.asciidoc` at the pinned commit, blob `81ecf7d388f899a1481df9f25ec1065710de679d`. Official contents metadata at the observed `master` ref returns the **same blob ID**. The branch's commit ID is also identical, making the mapped source unchanged by identity. The release branch's manual blob is `a9b97ee92b67d5d3a246d2e06e94bf44ff70b0c5`; because its commit history diverged, that difference is not characterized as a newer behavioral change or as proof that a specific R494 clause changed. No later default-branch source commit was available for a forward changed-path map.

The original evidence map also distinguishes Feldman's publication, GNU Make documentation, Ninja project-author history, an early Ninja manual, and Anneal authority. Those historical and derived components are carried forward as their original evidentiary roles. The same-commit Ninja observation supports a bounded source-identity result only.

## Boundaries

No Ninja binary, generator, Make process, or Anneal product was installed or executed. All five Summary rows record `runtime_result: unexecuted_in_this_review`; the Anneal product result is `unassessed`. No source archive was acquired and raw source snapshot SHA-256 is null. The offline checker verifies recorded ref, commit, compare, and manual-blob relationships against the exact frozen corpus; it cannot refresh GitHub or establish runtime equivalence. The release/manual difference is a branch comparison, not a longitudinal result for R494's pinned development line.

## Evidence and revalidation

The package includes the [matrix](support/matrix.json), [official-source observation](support/official-source-observation.json), [single-row selector](support/frozen-cohort.csv), [baseline inventory](support/version-inventory-ebcdcad-581.csv), [baseline path list](support/baseline-report-paths.txt), and [offline checker](support/check_matrix.py). Run `python3 reports/ninja-current-source-review/support/check_matrix.py` from a checkout containing the frozen commits. When `master` advances, compare ancestry and claim-mapped blobs against the exact R494 pin before considering behavior. Prompt/setup refinement: resolve a development ref and stable release separately, peel the release tag, and require a forward source relation before labeling a release difference as later behavior.
