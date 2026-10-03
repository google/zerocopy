# Lean/Lake 4.35.0-rc3 output-reference routing: source follow-up

## Summary

At the tagged Lean/Lake 4.35.0-rc3 prerelease, the mapped output-reference insertion condition changes from `pkg.isRoot` to `pkg.wsIdx = ctx.outputsIdx`. The direct package-scoped `Cache.writeOutputs` call remains. The v91 coverage audit indexes this source-only R414 supplement; its runtime and issue status remain unchanged.

## Applicability

The persisted v90 matrix at reference `ba4556c30835b56d108b0a6854a760bccf8438c5` targets Lean/Lake stable `v4.34.1` for its Lean cohort and mentions `v4.35.0-rc3` only as an optional later target. The official Lean release and tag identify [4.34.1](https://github.com/leanprover/lean4/releases/tag/v4.34.1) as `5045d0056413266e57c625dcd7c365b10e377c52` (24 September 2026) and [4.35.0-rc3](https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc3) as `470d5ce1400764999581fd26d5d72b00d990b0f4` (24 September 2026). A read-only official `git ls-remote` on 3 October returned current `leanprover/lean4` HEAD `193c3589a4fc16c4059261ab38cfa365eb24f323`. The exact stdout is retained in `upstream_refs.json`.

Lake is in the Lean repository. The source finding below was already present at the **tagged rc3**, and remains byte-identical in the relevant block at the later HEAD. It is not a new stable-release behavior finding.

## Findings

At [4.34.1 `src/lake/Lake/Build/Common.lean`](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Build/Common.lean#L724-L731), after a cache-aware artifact build, Lake inserts the artifact description into the build context's optional `outputsRef?` only when `pkg.isRoot`. At [4.35.0-rc3 `Common.lean`](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/lake/Lake/Build/Common.lean#L667-L672), a new `Internal.getOutputsRef?` returns that reference when `pkg.wsIdx = ctx.outputsIdx` (Lean equality syntax); the [call site](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/lake/Lake/Build/Common.lean#L724-L735) then inserts through the returned reference. This is a real condition change in a source file mapped to R414's cache-aware build path. It plausibly changes which package contributes to a context output reference in workspaces with differing package indices. The source alone does not establish a user-visible difference, identify a fixture where the two predicates disagree, or prove full archive/mapping behavior.

Crucially, the direct `Cache.writeOutputs pkg.cacheScope inputHash art.descr` call in the same helper remains at [rc3 lines 719–720](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/lake/Lake/Build/Common.lean#L711-L721). This supplement therefore does **not** revise R414's narrower claim that cacheable artifact publication writes the package-scoped input/output mapping after artifact creation. It identifies a neighboring output-reference route that deserves a targeted later review. The 4.34.1 and rc3 `Cache.lean` difference in the inspected file is only a deprecation-message spelling correction; the mapped cache mapping read/write code did not change in this file.

The [4.35.0-rc3 `RequestHandling.lean`](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Server/FileWorker/RequestHandling.lean) also refactors completion/goal lookup through `Language.Lean` helpers, but the mapped R462 `waitForDiagnostics` comparison `p.version ≤ doc.meta.version` is unchanged. This does not establish goal-reply ordering at rc3.

Mathlib's [4.35.0-rc3 tag](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0-rc3) resolves to `c55e6e786f49471c72fbddbec5415808896aec1e` (25 September 2026); its `lean-toolchain` selects `leanprover/lean4:v4.35.0-rc3`. Current Mathlib HEAD `302343bb9a029d4edab4f736703f0736896c1b64` has the same toolchain text. This is version alignment only, not a Mathlib behavior check.

## Boundaries

No Lean/Lake server, build, Mathlib test, or archive probe was run. RAM admission was below the retained 30% gate (approximately 24.3% at the parent task's latest check). This report should be cataloged as **source-only, rc3 evidence**, with R414's v90 outcome and runtime status unchanged. It does not upgrade 161 Lean/Lake rows, the 4.29/4.30 comparison rows, the Mathlib rows, or R462. A later runtime study should first construct a workspace where `pkg.isRoot` and `pkg.wsIdx = ctx.outputsIdx` differ, then compare the actual context output reference and resulting cache/archive artifacts at exact pinned versions.

## Evidence

From this directory, the read-only ref command was `git ls-remote https://github.com/leanprover/lean4.git HEAD refs/tags/v4.34.1 refs/tags/v4.35.0-rc3`; the analogous Mathlib command used `leanprover-community/mathlib4.git`. Source was fetched only from `https://raw.githubusercontent.com/<repo>/<full-commit>/<mapped-path>` with `curl --fail --silent --show-error --location`. `raw/leanprover/lean4/<commit>/src/lake/Lake/Build/Common.lean` contains all three exact source versions. SHA-256: 4.34.1 `03c6017c49303720287e76e7c31decea54f1fddec5d0d7fd358e036e3b48575c`; rc3 `ac4245ce6f64078d0204503c0340d27572e331c2a3df452b29432b463fe2fccd`; later HEAD `653f29fa0b07ef75ee9f097f76d7183d2f508dfca1343c40cb648df7b11896e6`.

For exact comparison: `diff -u raw/leanprover/lean4/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Build/Common.lean raw/leanprover/lean4/470d5ce1400764999581fd26d5d72b00d990b0f4/src/lake/Lake/Build/Common.lean`. The 52-path selection and byte results are in `mapped_source_results.json`, built from claim maps in the persisted reference reports; it includes 48 equal and four changed mapped paths (three Lean files and Mathlib's toolchain). The separate [cohort note](COHORT-NOTE.md) records other upstream tips and the TypeScript native-source exception. `REPORT.json` contains only reference-format retrieval metadata; [verification-manifest.json](support/verification-manifest.json) stores evidence hashes and source provenance separately.

## Revalidation

Run `python3 -B check.py --reference-root /path/to/zerocopy-checkout` from this package, using a checkout that contains `ba4556c30835b56d108b0a6854a760bccf8438c5`. The offline checker verifies the retained hashes, release refs, mapped source predicates, and frozen R414/R462 matrix identities. The networked `check_mapped_sources.py` is an optional read-only refresh and is not part of this offline result.
