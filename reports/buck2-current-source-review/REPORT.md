# R346 Buck2 one-graph architecture against current source

## Summary

The [R346 matrix](support/matrix.json) freezes the exact six `## Summary` paragraphs, source-pin metadata, report bytes and section locator at reference `ef8e39197bf8d1f6bb8753e7155c3a494fa8e2f4`. Official Buck2 `main` at [`b2b7ba58b5188aa35adc784d8ec6425dd93b98df`](https://github.com/facebook/buck2/commit/b2b7ba58b5188aa35adc784d8ec6425dd93b98df) is 29 commits forward of R346's [`738e69a6c5f1efb6a015645228e7a19ee9b1d9c0`](https://github.com/facebook/buck2/commit/738e69a6c5f1efb6a015645228e7a19ee9b1d9c0). The four Buck2 documentation blobs named in R346's source subject are unchanged. Three adjacent DICE implementation files changed to add a `compute_with_key` API and a source test. This is a narrow source-level delta, not evidence that the one-graph architecture, performance, incremental correctness, or Anneal design judgments changed.

## Source and tag identities

The [official-source observation](support/official-source-observation.json) records raw Git refs, the 29-commit forward comparison, its complete 114-file changed-path list, and commit-pinned source-file Git blob SHA-1/content SHA-256 values. None of R346's four cited documentation paths is in the changed-file list. The compare is below GitHub's 300-file cap. Buck1's archived source, Meta's 2023 launch account, *Build Systems à la Carte*, and Anneal's design pin remain historical or derived evidence under their original identities.

GitHub's `releases/latest` endpoint returned 404 for `facebook/buck2`; this review does not identify a GitHub Release object. The [official tag-ref snapshot](support/official-tag-refs.txt) contains 77 date-named tags, latest by name `2026-09-15` at commit `6507dd157a6f81a810c48583edf1758dd0c337c5`. That date-named tag is 514 commits behind R346's old pin and 543 behind selected `main`. The same captured snapshot recorded the floating `latest` tag at `0161ff601e2f82af9b8cd431e04e7d9acf9f305c`. A [live ref recheck](support/official-ref-recheck.txt) completed at 2026-09-30 21:55:50 UTC found that `latest` had moved to `b2b7ba58b5188aa35adc784d8ec6425dd93b98df`, equal to selected `main`. The floating ref is time-dependent and is not substituted for the date-named tag or treated as a GitHub Release object. The date-named tag predates R346's pin; the development-line source comparison uses the exact old and new commits, independently of either tag.

The original selector is R346 in the 581-row inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The frozen reference contains 605 report packages; all 24 additions are reconciled and hashed in the matrix.

## Claim-mapped source findings

R346 identifies four exact Buck2 source documents: [`docs/about/why.md`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/docs/about/why.md), [`docs/about/benefits/compared_to_buck1.md`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/docs/about/benefits/compared_to_buck1.md), [`dice/dice/docs/index.md`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/dice/dice/docs/index.md), and [`docs/insights_and_knowledge/modern_dice.md`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/docs/insights_and_knowledge/modern_dice.md). All four old/current Git blob IDs match the IDs in R346's `REPORT.json`; each old/current content SHA-256 matches as well. The matrix maps those files to the exact Summary paragraphs about Buck2's rewrite and DICE contract. This establishes continuity **for those documents**, not a fresh runtime or whole-source validation.

The complete changed-path comparison also includes three DICE files adjacent to the report's incremental-engine discussion:

| Changed source path | Direct source observation |
| --- | --- |
| [`dice/dice/src/api/computations.rs`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/dice/dice/src/api/computations.rs) | Adds a public `compute_with_key` method that returns the key allocation DICE retains alongside the computed value. |
| [`dice/dice/src/epoch/ctx.rs`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/dice/dice/src/epoch/ctx.rs) | Adds the tracked-computation implementation and `canonical_key` lookup from the key index. |
| [`dice/dice/src/epoch/tests/general.rs`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/dice/dice/src/epoch/tests/general.rs) | Adds a source test asserting that equal keys requested through different paths share the retained allocation. The test was not run. |

These changes add an API for canonical key allocation reuse. They do not demonstrate changed scheduling, invalidation, early-cutoff, or build performance behavior, and do not isolate any cause of Meta's historical reported gains. Other Buck2 source paths changed in the 114-file range; this review did not trace every dependency of R346's architectural claims.

## Boundaries and revalidation

No Buck2 binary, DICE test, build graph, or Anneal product was installed or executed. `runtime_result` is `unexecuted_in_this_review`; `anneal_product_result` is `unassessed`. Commit-pinned individual files were read for hashes, but no full source archive was acquired. The [offline checker](support/check_matrix.py) validates exact frozen R346 claims and subjects, corpus reconciliation, recorded ref/tag/ancestry metadata, changed-path overlap, mapped doc blobs and adjacent source patches. It cannot refresh upstream or establish behavior equivalence.

Run `python3 reports/buck2-current-source-review/support/check_matrix.py` from a checkout containing the frozen corpus commits. A stronger review would trace DICE's new key-return path and other changed source against precise incremental invariants, then run a version-pinned fixture. Prompt/setup refinement: distinguish stable architecture documentation, adjacent source API changes, date-named tags, and a floating `latest` ref before assigning version or behavior meaning.
