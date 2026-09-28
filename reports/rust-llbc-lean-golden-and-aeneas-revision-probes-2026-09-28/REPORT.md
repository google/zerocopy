# Executed Rust-to-LLBC-to-Lean specimens and Aeneas revision comparison

## Summary

A compact execution suite linked Rust fixture classes through Charon LLBC and Aeneas-generated Lean, and a paired-release comparison found the same baseline `Baseline.lean` bytes when each Aeneas release was used with its pinned Charon. The important constraint is that Aeneas June 1 accepts its Charon 0.1.208 pair and June 3 accepts Charon 0.1.210; cross-pairing fails the explicit version compatibility check. This is paired-bundle evidence, not an Aeneas-only comparison on identical LLBC input.

## Applicability

The newer pair is Aeneas `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` and Charon `charon-lang/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`; the older pair is Aeneas `AeneasVerif/aeneas@f95a80abaf554d4612cb60ef9ec8e849139bec44` and its June 1 pinned Charon release. Runs used macOS arm64 and the locally installed Lean 4.30.0-rc2 for checking emitted source. The test suite is intentionally small and treats generated source as translation output, not a correctness proof.

## Findings

### Translation pattern specimens

The preserved specimen runner exercises baseline arithmetic/branching/mutable update plus closure, trait dispatch, loop, type-alias namespace selection, raw pointer, function-pointer, and duplicate-name cases. Charon produced LLBC for supported fixtures; Aeneas emitted Lean for the supported subset. The ordinary source-to-output examples expose these distinctions:

- branch control flow becomes a Lean conditional;
- checked arithmetic can remain an opaque external call in LLBC and Lean;
- mutation through `&mut` becomes an explicit returned updated state;
- closure, trait, and loop cases exercise additional item/control-flow shapes;
- a type alias can alter the generated namespace unless the configured namespace override is used;
- raw-pointer and function-pointer fixtures reach explicit Aeneas unsupported-operation diagnostics with source locations rather than successful Lean semantics.

The report-owned `translation-specimens/cases/` contains each tested Rust source, Charon LLBC, and generated Lean output where Aeneas succeeded; `translation-specimens/RESULTS.md` and `coverage.json` record all stage outcomes. The examples show where behavior is preserved or the pipeline rejects it; they do not assert semantic correctness for unsupported cases.

Basis: execution. See `translation-specimens/RESULTS.md`, `coverage.json`, and `canonical-order-check.json`.

### Aeneas revision comparison is constrained by pair compatibility

The June 1 Aeneas archive accepts its bundled/pinned Charon 0.1.208, while the June 3 Aeneas archive accepts Charon 0.1.210. The two cross-version cells failed with a compatibility error. The matching June 1 pair generated LLBC SHA-256 `455145d...`; the matching June 3 pair generated a different LLBC SHA-256 `3e081d...`. Despite those LLBC bundle differences, the baseline fixture's generated `Baseline.lean` was 1,120 bytes and had identical SHA-256 `3d854188c5820b9d08f9d767a7af2efb520140017243afa9cdcc3eb0b1cd503f` in both matching cells.

This isolates a useful paired-release observation: for one baseline fixture, generated Lean bytes match across the two supported toolchain bundles. It does not isolate Aeneas changes because each release consumed a different Charon/LLBC result.

Basis: execution + derived attribution boundary. Exact compatibility matrix is in `aeneas-revision-matrix.json`; the two matching-pair generated files and the cross-pair error output are preserved under `aeneas-revision/`.

### Relation to deterministic-output probes

Existing corpus reports cover Aeneas same-input repeat-run determinism and Charon LLBC revision diffs separately. The present evidence complements those reports with executable pattern coverage and a compatible paired Aeneas-release baseline; it does not replace their broader run repetitions or claim identical behavior for every output file.

## Boundaries

No common LLBC specimen was accepted by both Aeneas releases, so there is no isolated Aeneas-only revision diff. The baseline generated Lean equality does not imply all generated files, diagnostics, proofs, or source mappings match. The fixture suite is not exhaustive of every Rust-to-LLBC-to-Lean translation pattern. Lean acceptance of generated files is not a theorem that translation preserves Rust behavior.

## Evidence

- Aeneas June 3: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- Aeneas June 1: `AeneasVerif/aeneas@f95a80abaf554d4612cb60ef9ec8e849139bec44`.
- Charon June 3: `charon-lang/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`; Charon June 2 release: `charon-lang/charon@6101d742777bf9f9b48979ac1ad4d2c07dfe10db`.
- Lean: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).
- Current runner records and source→LLBC→Lean specimens in `translation-specimens/`; compatibility and generated-file hashes in `aeneas-revision-matrix.json` and `aeneas-revision/`.
- Aeneas pipeline/error source: `src/Main.ml` (`-backend` dispatch and final error exit), `src/Translate.ml` (LLBC-to-pure translation), and `src/Errors.ml` (registered error/source-span records) at `ac9f1bc5262a5e4ff1e24ca78617121382202727`. Matching LLBC producer sources are covered by the Charon source coordinates in the companion Charon report.

## Revalidation

Run the same source fixtures with each Aeneas release's pinned Charon and Rust compiler, record tool binary hashes and raw LLBC/Lean outputs, and first check the compatibility matrix. To isolate Aeneas, supply a single serialized LLBC version that both binaries explicitly accept; if none is accepted, report only the paired-bundle comparison. Compile the supported generated Lean outputs, and retain unsupported/error specimens as expected outcomes.
