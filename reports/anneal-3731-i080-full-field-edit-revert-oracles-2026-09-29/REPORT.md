# Full-field cold-oracle comparison of retained I080 source edit and revert LLBCs

## Summary

All **12 completed shared-target LLBCs** in the retained I080 source edit → rebuild → revert corpus were compared with the cold oracle for their exact source state, using the original decoded JSON values and no normalization. Across both `CARGO_INCREMENTAL=0` and `1`, every differing leaf in those 12 comparisons is a requested destination path, a generated-file local path, or a positional `translated.short_names` entry. The typed-key/name maps in `short_names` agree for each pair. Two edited-versus-baseline cold-oracle negative controls detect the embedded Rust source change and serialized `step` call literal **"2" versus "1"**. This extends the [source report](../anneal-3731-i080-source-edit-revert-incremental-cache-2026-09-29/REPORT.md)'s five selected local body hashes per output for #3731 **I080** and #3730 **D03**, and informs #3731 **I079**. It does not establish byte identity, semantic equivalence, or an Anneal target policy.

## Applicability

This is offline reanalysis of the exact 16 LLBC byte artifacts and source execution record published in the source edit/revert report, not a new Charon schedule. The source run used pinned Charon 0.1.210 and nightly-2026-05-31 Cargo/rustc on macOS arm64. In each incremental mode, equal-length A/B source roots sequentially reused one writable Cargo target. A changed only `wrapping_add(1)` to `wrapping_add(2)` and reverted; B stayed baseline. Independent cold A oracles supplied baseline and edited outputs. This package copied all 16 LLBCs and `results.json` byte for byte into `support/`; the source package checker passed before comparison. No compiler, server, network or download was used in this reanalysis.

Each of the six shared outputs per incremental mode was paired with its same source-state oracle: edited A with edited A oracle, and baseline/reverted A plus every B with baseline A oracle. Source root paths and Cargo targets differ between a shared output and its oracle. Those path values remain explicit in the difference record and must not be silently normalized away.

## Findings

| Incremental | Baseline A/B | Edited A/B | Reverted A/B |
| --- | --- | --- | --- |
| Off | 22 / 22 differing leaves | 22 / 17 | 22 / 22 |
| On | 20 / 18 differing leaves | 20 / 22 | 22 / 19 |

The 12 pairs contain **248 differing decoded leaves** in total. For every pair, exactly one difference is `/translated/options/dest_file` and exactly one is `/translated/files/1/name/Local`; all others are array-position differences under `/translated/short_names/`. Every decoded object key, array position, type and scalar was compared recursively. Keying `short_names` by its serialized typed key yields the same key/value map in each pair. No function declaration, embedded source contents, crate name, error status, or other decoded field differs between a shared output and its same-state oracle. **Basis: execution** of the retained-data Python comparison, with every path and both exact values in `support/comparison.json`.

The two negative controls compare cold edited A with cold baseline A at each incremental setting. They have 24 and 20 differing leaves and include changed `/translated/files/0/contents` plus the serialized `step` call argument at `/translated/fun_decls/0/body/Structured/body/statements/2/kind/Call/args/1/Const/kind/Literal/Scalar/Unsigned/1` (`"2"` versus `"1"`). The source text contains `wrapping_add(2)` versus `wrapping_add(1)`. Thus the comparator detects a substantive model change in this retained corpus. **Basis: execution**.

The source report already established the sequential edit/revert schedule, selected five-body equality and bounded Cargo-target resource observations. This package adds an exhaustive decoded-field inventory for those outputs. It does not add concurrency, cancellation, build-script provenance or downstream Aeneas/Lean execution.

## Boundaries

- The field result applies to these 12 paired outputs and four reused cold oracle files. It does not prove Rust semantic equivalence, Charon soundness, byte-identical LLBCs, safe path-insensitive cache keys, or that arbitrary `short_names` permutations are irrelevant to every consumer.
- The generated-file local path and requested destination differ in all pairs. Both are part of the original artifact identity even when this fixture's remaining decoded fields agree.
- A and B source roots had equal absolute pathname lengths; the prior path-sensitive build-script counterexample is not erased. The source edit/revert run was sequential and tiny. Dirty concurrent workloads, cancellation, representative resources, and Anneal-owned output/target publication remain open.
- The cold edited-versus-baseline result is a discriminating negative control for this one Rust edit, not proof that every source change reaches the model.
- The Python process stayed below its acquisition gates: 31 memory/RSS samples, minimum estimated reclaimable memory **22.5082%**, maximum measured self RSS **24,739,840 bytes**, and elapsed **0.13825 seconds**. Sampling cannot exclude a briefer RSS or host-memory excursion.

## Evidence

- `support/artifacts/` preserves all 16 raw LLBCs. Their exact SHA-256 values are in `support/comparison.json` and cross-checked against the unchanged `support/source-results.json` copy (SHA-256 `e1f8ac94a2bda6f93ca21d11c8fae4c6030bd2f9a9ac5491d2e4b36f981e1d4a`). The source report's checker validates original run commands, source A/B/A hashes, selected bodies, guards and cleanup.
- `support/compare.py` (SHA-256 `e70c139e1c4b9769b789ca67023bf1a523f89f118f5a68a199ff6565648bd804`) is the exact guarded Python comparator. It checked ≥20% reclaimable memory before input and after each decode and comparison; it capped measured self RSS at 64 MiB and wall time at five seconds. `support/comparison.json` (SHA-256 `7fb668a000adbf5bd8d2a8534e40b1c0164aac1e7e9c9d71d797bd17a3977be7`) retains all differences, hashes, negative controls and guard samples.
- `support/check.py` independently recomputes every difference and keyed-name map, checks both negative controls and validates all artifact and resource records without invoking compilers or servers.

## Revalidation

Run `python3 -B support/check.py` from this package to verify the retained analysis. A fresh comparison acquisition needs a separate copy with the same 16 source hashes and an immediate ≥20% reclaimable-memory preflight; run `python3 -B support/compare.py` only under the documented RSS/time caps. A new Charon/Cargo revision, different path lengths, source states or target schedule requires new cold oracles and a new report.
