# Full-field comparison of retained I080 target-layout LLBC matrix

## Summary

The [published target-layout matrix](../anneal-3731-i080-incremental-target-layout-matrix-2026-09-29/REPORT.md) retained 16 successful Charon LLBC outputs from four private/shared Cargo-target × incremental-off/on cells, each with cold and warm A/B requests. It checked five selected local function bodies per output. This offline reanalysis compares **every decoded JSON field** along all 24 matched one-axis pairs: eight warm versus cold, eight shared versus private, and eight incremental-on versus off. Every observed difference is a requested destination path, a positional `translated.short_names` leaf, or—for layout and incremental contrasts—the generated-file local path. The `short_names` typed-key/name maps agree in every pair. This adds bounded #3731 **I080** and #3730 **D03** output-identity evidence; it does not establish semantic equivalence, safe target sharing or an Anneal ownership policy.

## Applicability

This package is offline Python reanalysis of the exact 16 LLBC byte files and `results.json` from the published source report at `upstream/reference@bc6753abb676164cf355af600d7abfecd6c3f59f`. The source report's checker passed before these files were copied byte for byte into `support/`. Its original execution used pinned Charon 0.1.210 and nightly-2026-05-31 Cargo/rustc on macOS arm64, with two tiny source roots and a path dependency/build script. Root paths had equal length across cells; no source bytes changed. Within each cold or warm phase, A and B ran concurrently; the four cells ran sequentially. The shared cells logged Cargo build-directory lock waits. The current analysis did not run a compiler, translator, server, network request or installation.

The matched comparisons change one fixture axis at a time while holding the other recorded labels fixed. Warm/cold pairs use the same source root, layout and incremental mode within a cell. Shared/private pairs match incremental mode, phase and A/B root label. Incremental-on/off pairs match layout, phase and root label. The latter two are **matched peer contrasts**, not independent clean-build semantic oracles. Original absolute target and destination paths remain part of the retained differences.

## Findings

| Matched axis | Pairs | Decoded leaf differences across pairs | Per-pair range | Non-`short_names` paths |
| --- | ---: | ---: | ---: | --- |
| Warm versus cold | 8 | 154 | 16–21 | `/translated/options/dest_file` |
| Shared versus private | 8 | 167 | 14–22 | destination path; `/translated/files/1/name/Local` |
| Incremental-on versus off | 8 | 158 | 16–22 | destination path; `/translated/files/1/name/Local` |

All **24** pairs have one requested destination-path difference and positional `short_names` differences. Each of the 16 shared/private and incremental-mode pairs also differs at the generated-file local path, which points into its Cargo target. The complete record contains 479 per-pair differing leaves in aggregate; outputs recur across axes, so this is not a count of unique file fields. Every object key, array position, type and scalar was recursively compared without normalization, and every path and exact pair of values is retained in `support/comparison.json`. In each pair, the serialized typed-key/name map in `short_names` is equal. No function declaration, embedded source contents, crate name, error status or other decoded field differs in these matched comparisons. **Basis: execution** of the retained-data comparison.

Three **synthetic in-memory negative controls** changed a copied decoded crate name, one copied function body and the order of two copied `short_names` entries. The comparator reported the expected path families for all three. The 16 original LLBCs were not modified. These controls demonstrate sensitivity of this comparator to those changes; they are not evidence of a real changed-source Charon result.

This corpus is distinct from the published I080 edit/revert full-field comparison, which checked 12 sequential dirty shared-target outputs against cold source-state oracles, and from the incremental-on cancellation/retry full-field comparison, which checked four completed outputs after one canceled peer. The current matrix holds source bytes fixed and varies target layout, incremental flag and cold/warm phase. It adds no source edit, cancellation, restart, descendant trace, build-script provenance or downstream Aeneas/Lean result.

## Boundaries

- Equal decoded fields outside the listed differences describe only this small fixed-source corpus. They do not prove byte-identical LLBC, Rust semantic equivalence, Charon soundness, general path-insensitive cache keys, or that every LLBC consumer ignores `short_names` order.
- Requested destination and generated-file local paths are genuine artifact/provenance values. The comparator recorded them rather than normalizing them away.
- Equal-length roots deliberately avoid the source fixture's known path-sensitive build-script counterexample. The target-layout matrix does not resolve dirty concurrent source changes, cancellation, representative sustained resources or an Anneal target/publication policy.
- The three negative controls are synthetic decoded-value mutations, not independent producer executions or a changed Rust model oracle.
- The guarded Python run sampled 44 points: preflight reclaimable memory **26.3670%**, minimum **26.2953%**, peak measured self RSS **25,968,640 bytes**, elapsed **0.20167 seconds**. Samples do not establish a sustained host peak.

## Evidence

- `support/artifacts/` preserves all 16 raw LLBCs and their original cell/phase/root paths. `support/source-results.json`, SHA-256 `040f6e477a358b602af87298fbc8517cd5269e8803d4ede7e70762ae31d58828`, is an unchanged copy of the source execution record. The published source `REPORT.md` SHA-256 is `07ebaa3cb0d2177d4c088caf9cbcff6973bc4cb7ca932cc91e07a97d25e59d44`.
- `support/compare.py`, SHA-256 `867d5f0f2d568d6f7b1a69057df48c90757ea482ceb34852eba668508cd5eae7`, is the executed guarded procedure. It required **greater than 20%** reclaimable memory before input and after each decode, pair and control; it enforced 64 MiB self RSS and five seconds. `support/comparison.json`, SHA-256 `4d4396890b7a05eaad9684ccaf76067cf6f0ba1e74bd8d48caf109dd75dd4c02`, contains all hashes, 24 exhaustive diffs, three control diffs and resource samples.
- `support/check.py` independently reconstructs the exact 24 pair topology, recomputes every diff and keyed map, checks all 16 source hashes and replays the synthetic controls in memory without invoking compilers or servers.

## Revalidation

Run `python3 -B support/check.py` from this package to validate the retained analysis. A fresh acquisition needs the same 16 raw hashes and a fresh >20% reclaimable-memory preflight under the stated RSS/time caps. A different tool pin, path-length distribution, source state, concurrency schedule or Anneal target policy requires new producer controls and a new report.
