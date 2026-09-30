# R405 HLS and hie-bios current-source disposition

## Summary

The [R405 matrix](support/matrix.json) freezes the report's exact four `## Summary` paragraphs, section locator, original subjects and source-map bytes at reference `3d730ab522554cd534b2ddf582b96e1e233f1fff`. On 2026-09-30, the official Haskell Language Server `master` ref still resolved to R405's pinned [`187fcd4a685c220caabb72999565604b3287aff2`](https://github.com/haskell/haskell-language-server/commit/187fcd4a685c220caabb72999565604b3287aff2), while the independent official hie-bios `master` ref still resolved to its pinned [`32dd07707423ffabb34e44af68fcbd027b60ded2`](https://github.com/haskell/hie-bios/commit/32dd07707423ffabb34e44af68fcbd027b60ded2). There is **no forward source revision** in either repository to compare for this bounded review. Current-version runtime behavior and Anneal product implications were not tested.

## Applicability

R405 combines historical HIE and ghcide archives, HLS's incremental graph and compiler-service structure, and hie-bios's project/compiler environment contract. The first two remain historical sources; the current-source question here concerns the two separately pinned repositories. The original selector is R405 in the 581-row inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The current frozen reference contains 594 report packages, including 13 additions accounted for and hashed in the matrix.

The [recorded official observation](support/official-source-observation.json) preserves each repository's `git ls-remote` output, official default branch, commit parent/tree identity, and GitHub content blob IDs for R405's five HLS/hie-bios mapped files. Both repositories use `master` as their official default branch. Each default ref equals its original report pin exactly. Therefore the forward commit count and changed-path set are zero for each **same-commit comparison**. This is equality of source identities, not independent runtime validation.

## Claim mapping and source result

| Exact frozen Summary paragraph | Mapped source | Disposition |
| --- | --- | --- |
| 1. HIE/ghcide/HLS lineage and recombination | Historical HIE architecture and ghcide README; HLS README; hie-bios README | Historical components remain original evidence. HLS and hie-bios have no newer default-branch commit to recheck. |
| 2. Project environment as semantic boundary | hie-bios README; historical ghcide README | The mapped hie-bios README has the same Git blob ID at the pinned and observed default-branch commit. No newer source result. |
| 3. Shake to `hls-graph`, in-memory dependency engine | HLS `hls-graph/README.md` and `ghcide/src/Development/IDE/Core/Rules.hs` | Both mapped HLS blobs have the same IDs because the branch remains at the pinned commit. No later engine behavior is inferred. |
| 4. Conditional Anneal judgment | HLS graph and hie-bios documentation as upstream inputs | This remains derived analysis, not an observed Anneal implementation or acceptance result. |

R405's source map also names HLS `cabal.project`; its blob ID is unchanged at the same commit. The exact file-to-claim supports, old/current blob IDs and commit-pinned URLs are in the observation and matrix. The source map's HIE/ghcide archive pins and external maintainer essays were not updated or reinterpreted as new current-version evidence.

## Boundaries

No HLS, hie-bios, GHC, editor host, or Anneal process was installed or run. All four summary rows record `runtime_result: unexecuted_in_this_review`; the product result is `unassessed`. No source archive was acquired. The checker validates the recorded ref and blob observations against the frozen reference corpus and their internal identity relationship; it cannot refresh GitHub, prove that a branch will remain fixed, or establish semantic equivalence beyond the same source commit. This report makes no new release-version or compatibility claim.

## Evidence and revalidation

The package includes the [matrix](support/matrix.json), [official-source observation](support/official-source-observation.json), [single-row selector](support/frozen-cohort.csv), [baseline inventory](support/version-inventory-ebcdcad-581.csv), [baseline path list](support/baseline-report-paths.txt), and [offline checker](support/check_matrix.py). Run `python3 reports/haskell-hls-hie-bios-current-source-review/support/check_matrix.py` from a checkout containing the frozen commits. Revisit the two repositories separately once either default branch advances, then compare commit ancestry and changed blobs for each exact claim before proposing a behavior difference. Prompt/setup refinement: ask for independent component refs and claim-specific mapped paths, and allow a same-commit no-newer-source result rather than implying a version recheck occurred.
