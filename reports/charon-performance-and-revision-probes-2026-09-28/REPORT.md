# Charon scaling and revision-diff execution probes

## Summary

On one macOS arm64 host, Charon 0.1.210 extracted generated Rust crates containing 10, 100, and 1,000 independent small functions, and selected 1, 10, 100, and 1,000 roots from the same 1,000-function crate. All commands completed with `has_errors: false`; output size grew with selected declaration count. A matched three-function fixture run under Charon 0.1.208 and 0.1.210 produced equal schema-aware LLBC projections after excluding the destination path and canonicalizing only the keyed name maps. These are bounded probes, not large-workspace or dependency-chasing benchmarks.

## Applicability

The current executable was the macOS arm64 Charon release paired with Rust nightly 2026-05-31. Current Charon source is `charon-lang/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`. The comparison executable was the official macOS arm64 release for Charon 2026.06.02, corresponding source tag commit `6101d742777bf9f9b48979ac1ad4d2c07dfe10db`. The identical compiler, host, preset (`aeneas`), fixture bytes, crate name, and options were held constant for the June 2/3 comparison. Binaries are identified by the hashes below; source revisions do not prove binary build provenance.

## Findings

### Generated whole-crate and many-root matrix

A deterministic 51,915-byte crate with 1,000 independent simple functions (SHA-256 `a7242d3ed0681bcaae7121eb11665febcbdfd0b7ae2be325c4d7c7b2d86f64b1`) was invoked with explicit `--start-from` root counts of 1, 10, 100, and 1,000. Each invocation exited 0 and had `has_errors: false`. The emitted local function counts were exactly 1, 10, 100, and 1,000; ordered declaration counts were 2, 11, 101, and 1,001. LLBC output sizes were 59,592; 86,112; 353,715; and about 3.06 MB. Captured wall times were 0.390s (the first cold run), 0.075s, 0.082s, and 0.18s respectively. The outputs and extracted declarations matched the expected selected root counts.

Earlier same-host whole-crate runs on 10/100/1,000 generated functions also succeeded; their three-run medians were 0.051s, 0.062s, and 0.145s, with 33,433; 303,310; and 3,044,692 LLBC bytes. These runs indicate that this simple fixture is inexpensive at these sizes, but do not justify a linear cost model.

Basis: execution. The generated Rust inputs, whole-crate LLBC outputs, root-count LLBC outputs, and compact run records are preserved under `generated-crates/` and `many-roots/`; `root_matrix.py` shows the harness. The normalized revision projections, comparison script, and hashes are in `revision-diff/`.

### Charon revision comparison and golden normalization

The matched baseline LLBC from Charon 0.1.208 and 0.1.210 normalized to the same JSON value (both normalized SHA-256 `c6df813c98fbc86c32a89e8895add960d2def6d14bb9d63a3ba96001483b4914`). Normalization replaced only `translated.options.dest_file` with `<OUTPUT>` and sorted the associative arrays `item_names`, `short_names`, and `assoc_item_names`; it did not reorder declaration lists or erase source/type information. The raw files differed because path-bearing metadata and ordering were not canonicalized by the producer. Preserve raw LLBC when diagnosing a diff; use this normalization only for the listed fields.

Basis: execution + derived comparison procedure. Exact hashes, binary identities, and projection are in `revision-comparison.json`.

### Source-level scaling factors

Charon translates through a work queue and a processed set. Work can depend on crate HIR size, selected roots, reachable bodies, referenced foreign signatures, translation passes, and serialization. `--start-from-pub`/attribute selection scans crate definitions even when the selected root set is small. `charon cargo` also includes Cargo/rustc dependency and build-script work. These are source-backed costs, not measured by the simple rustc fixtures.

Basis: source (`charon-lang/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, `charon/src/bin/charon-driver/translate/translate_crate.rs`, and CLI/Cargo driver paths) + derived.

## Boundaries

No dependency graph was varied in this probe. It did not measure a large multi-package Cargo workspace, build scripts, proc macros, crate dependencies, foreign body inclusion, or target selection. The generated functions are uniform and independent, so the root matrix does not measure dependency chasing. Peak RSS is process maximum resident size on an individual Charon invocation, not an aggregate process tree or a production capacity result. No conclusion about zerocopy-scale extraction or Anneal job concurrency follows.

The June 2/3 equality is limited to one matched fixture and a narrowly defined normalization. It is not a compatibility guarantee for all LLBC, nor an Aeneas comparison. Earlier May 31/June 3 probes changed both Charon and rustc toolchain and are not used to attribute revision effects.

## Evidence

- Charon June 3 source: `charon-lang/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`; binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`.
- Charon June 2 source tag: `charon-lang/charon@6101d742777bf9f9b48979ac1ad4d2c07dfe10db`; binary SHA-256 `094ba2dc1d23f82be5ad2bb378e94ce8c66ca9d13c551edfeb8597b392558272`.
- Rust nightly: `rust-lang/rust` toolchain `nightly-2026-05-31`, `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, `aarch64-apple-darwin`.
- Charon source coordinates: `charon/src/bin/charon-driver/translate/translate_crate.rs` (`enqueue_module_item`, queue/processed-set loop); `charon/src/bin/charon/main.rs` and `charon/src/bin/charon-driver/driver.rs` (Cargo/rustc integration), all at `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`.
- Execution scripts, fixture sources, emitted LLBC, normalization projections, and outcome hashes are preserved in this package. The root-matrix raw argv is omitted from the compact record because it contains machine-specific absolute paths; the fixed `--start-from` flags and root counts are recorded by the harness and output declarations.

## Revalidation

Regenerate the fixture with the recorded source hash, pin Rust and Charon binaries, rerun whole-crate extraction and root counts with distinct output paths, and assert `has_errors`, expected function identities, declaration counts, and output hashes. Add a separate explicit local-dependency graph and multi-member Cargo workspace before making claims about dependency chasing or workspace scaling. Compare Charon revisions with the same Rust toolchain and fixture, preserving raw JSON and applying the exact field-only normalization above.
