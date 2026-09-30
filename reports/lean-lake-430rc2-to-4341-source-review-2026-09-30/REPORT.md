# Lean/Lake 4.30.0-rc2 cohort against 4.34.1: bounded source review

## Summary

At frozen reference commit `3c82f8819d4f4ce0ad1f043e7771e2f0ebce0d73`, 161 report packages belonged to the Lean/Lake `v4.30.0-rc2` newer-version recheck cohort. The [row matrix](support/matrix.json) retains all 161 report paths, section and line locators, exact frozen claim excerpts, report and metadata hashes, exact frozen subject metadata, and the old/new full version identities. The [offline checker](support/check_matrix.py) re-reads every selected report from that frozen Git commit and checks every row. The frozen [cohort selector](support/frozen-cohort.csv) is included so the row set is auditable.

This is a **bounded source review, not a 161-report revalidation**. Three selected Lake claims have evidence-backed source deltas at Lean/Lake `v4.34.1`: one artifact-cache mapping-read claim and two compiled-configuration-cache location claims. The other 158 rows are explicitly **unresolved** at the newer source version. All 161 newer-version runtime outcomes are **unexecuted**. In particular, old LSP, elaboration, Lake process, concurrency, resource, and Mathlib observations are not carried forward as 4.34.1 behavior.

The original reports retain their pinned 4.30.0-rc2 scope. This matrix does not revise their findings, issue states, or Anneal product gates.

## Applicability and exact version pair

The old Lean/Lake source is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). The primary newer target is the [official Lean `v4.34.1` release](https://github.com/leanprover/lean4/releases/tag/v4.34.1), whose [release commit](https://github.com/leanprover/lean4/commit/5045d0056413266e57c625dcd7c365b10e377c52) is `5045d0056413266e57c625dcd7c365b10e377c52`. Lake is read as part of that Lean source tree, not as an independently versioned package.

Three of the 161 frozen report metadata files directly name `leanprover-community/mathlib4`: R416, R420, and R459. Their old pin is [Mathlib `v4.30.0-rc2` commit](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6) `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The paired newer target is [Mathlib `v4.34.1` commit](https://github.com/leanprover-community/mathlib4/commit/d13f23b723b8a846827a245b89c10fc7d3f11612) `d13f23b723b8a846827a245b89c10fc7d3f11612`; its [toolchain file](https://github.com/leanprover-community/mathlib4/blob/v4.34.1/lean-toolchain) selects `leanprover/lean4:v4.34.1`. These three rows retain both version pairs. Their Mathlib-dependent behavior remains unresolved because no matching newer source or runtime claim was established here. Other subjects in the frozen reports retain their exact original identities in the matrix; they are not silently upgraded into this Lean/Mathlib pair.

The cohort selector came from the prior 581-report version inventory's `Lean/Lake v4.30.0-rc2` category. Every selected path and excerpt was then read from the frozen `3c82f881` Git objects rather than from mutable working-tree files. For an item without a chosen narrow source delta, the excerpt is the first substantive paragraph under `## Summary`, or after the title when there is no Summary section. Such an excerpt is an **index into the claim to revisit**, not a finding that the whole paragraph was checked against 4.34.1. The three reviewed rows select a narrower exact passage and retain their line locator.

## Findings

### R414: malformed output mappings take a different local error path

The frozen R414 excerpt says that `readOutputs?` warns about malformed JSON and returns `none`. The [old `Cache.readOutputs?` source](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Cache.lean#L454-L467) has precisely that local branch. In [4.34.1 `Cache.readOutputs?`](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Config/Cache.lean), malformed JSON instead calls `error`. In the inspected [4.34.1 cache-aware build helper](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Common.lean), `getArtifactsUsingCache?` catches that error, logs it at verbose level, and returns `none`. The local diagnostic route changed; the higher helper still has a source path to a miss. Whether a particular Lake invocation emits a visible warning, takes another recovery path, or succeeds after malformed state is **runtime-unexecuted** here.

The newer [mapping writer](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Config/Cache.lean) adds an `overwrite` parameter; the default is `true` and that branch still calls `IO.FS.writeFile`. The `false` branch calls `writeFileIfNew`. That is source context for the same report, not proof of crash atomicity or an end-to-end recovery guarantee.

### R421 and R422: compiled configuration-cache placement changed

At the old pin, [Lean configuration loading](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L175-L188) derives `configDir` from `cfg.lakeDir / "config" / pkgName`, while [old `LoadConfig.lakeDir`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Config.lean#L69-L70) is `cfg.pkgDir / defaultLakeDir`. That supports the frozen package-local claim.

At 4.34.1, [`LoadConfig.configDir`](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Load/Config.lean) is `cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx`, and [the Lean configuration importer](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Load/Lean/Elab.lean) uses `cfg.configDir` for the `.olean`, `.trace`, and `.lock` files. `LoadConfig.lakeDir` still exists and remains package-relative; the changed importer path is the decisive source fact. Therefore the old R421/R422 package-local **compiled configuration cache** placement must not be projected onto 4.34.1. This is a source-level path comparison only. The handling of read-only dependencies, concurrent workspace loads, and actual on-disk migration was not executed at the newer version.

### Remaining 158 rows

The matrix marks every other row `unresolved`. Some original reports are source inspections, some are executed direct-tool probes, and some combine both. This review did not inspect enough claim-specific 4.34.1 source to confirm or refute their selected passages. A newer release tag, a retained symbol name, or a related delta above is insufficient to transfer their pinned findings. The three Mathlib-paired rows are among these unresolved entries. No 4.34.1 Lean/Lake compiler, server, Lake command, Mathlib build, or Anneal integration was run.

## Evidence and revalidation

The package contains `support/matrix.json` and `support/frozen-cohort.csv`. Run `python3 reports/lean-lake-430rc2-to-4341-source-review-2026-09-30/support/check_matrix.py` from a checkout that has frozen commit `3c82f8819d4f4ce0ad1f043e7771e2f0ebce0d73`. The checker verifies all 161 selector entries and rows, exact report and metadata hashes, exact excerpts and line/heading locators, original subject identities, full old/new Lean and paired Mathlib IDs, comparison labels, and runtime-unexecuted labels. It does **not** fetch or independently validate the remote newer source pages; those specific source comparisons require the linked official GitHub pages or an independently obtained source tree at the stated full commit.

The local environment had less than 30% reclaimable memory at review time. No dependency archive was downloaded or installed, and no Lean/Lake compiler or build process ran. Source pages were read through public official GitHub. A later reviewer should inspect the three linked newer source areas and the matrix classification before publication. To establish behavior for an unresolved row, compare its full original report and claim-specific newer source, then run only the needed newer-version probe under a fresh resource admission. Keep source findings, runtime observations, and Anneal product guarantees separately attributed.
