# ASCII-local Charon span and source-text check across retained edit/revert LLBCs

## Summary

The [published I080 edit/revert report](../anneal-3731-i080-source-edit-revert-incremental-cache-2026-09-29/REPORT.md) retained 16 LLBC byte files from independent cold oracles and sequential shared-target requests at incremental-off/on settings. This offline analysis checks their **local `app/src/lib.rs` item spans and `item_meta.source_text`** against the exact baseline Rust fixture and its hash-verified, one-expression edited state. All **64 locally testable ASCII function intervals** match their recorded source text in the corresponding source state. This is bounded direct provenance evidence for #3731 **I079**; **I149** is context only. It does not establish an authenticated Rust→Charon→Aeneas→Lean mapping.

The local span convention supported by these exact ASCII bytes is **one-based line numbers, zero-based columns, and an exclusive end position**. The retained source is ASCII, so byte, Unicode-scalar and UTF-16 column units all give the same offsets here. Their general distinction remains **undetermined**. No Unicode or multiline span oracle is claimed.

## Inputs and method

The source package is published at `reference@974c035a2a32b8b873ad560b572eeda7a69679bb`. Its report, probe and results hashes were verified. All 16 LLBC hashes and sizes match `support/results.json`; the original baseline `app/src/lib.rs` hashes to `bbe231375dfe3d5ae46a420067496a466ee223e8e2acb2aa54d0c931691d041e`. The original probe edits exactly one occurrence of `x.wrapping_add(1)` to `x.wrapping_add(2)` without changing length. Reconstructing that state from the retained fixture produces the recorded edited SHA-256 `d264e3214d6b82cc98a3dc13d3fb4d839d1ed54ccdf705225c17210195e61bae`. Both exact source states and all 16 LLBCs are copied into this package.

For each LLBC, the source hash recorded for its request selects one of those two states. The comparison verifies that LLBC file ID 0 is `app/src/lib.rs` and its embedded `contents` equals that independent retained/reconstructed state byte for byte. For each local item with a single-line span in file ID 0, it interprets line and column coordinates on the ASCII source bytes and compares the exact end-exclusive slice with `item_meta.source_text`. The four eligible functions per LLBC are `step`, `use_step`, `payload_len`, and `generated_value`. No source file or LLBC input was changed.

## Findings

Every one of the **16 × 4 = 64** file-ID-0 intervals matches its recorded source text. The two edited-A outputs and two edited cold oracles contain `wrapping_add(2)` in `step`; all baseline, unchanged-B and reverted-A outputs contain `wrapping_add(1)`. The source-state hashes and embedded source bytes also follow that split. A deliberately shifted start and an inclusive-end slice fail against the retained `step` source text, providing local offset controls. **Basis: execution** of the guarded offline comparator.

Another **32 local item records** point to generated Rust file ID 1, including duplicate function/global representations of `SNAPSHOT_VALUE`. The original generated `.rs` file is not independently retained outside the LLBC; those records are explicitly **excluded** from the source-state comparison. Nonlocal standard-library/dependency items and intervals lacking a locally testable source state are outside scope. The checker preserves every exclusion and its file ID.

The observed exact matches support only the fixture-specific coordinate interpretation. With all tested source bytes ASCII, this corpus cannot distinguish column units for Unicode. It does not prove how Charon encodes a non-ASCII column, multiline span, generated file, macro-expanded item or moved source, nor that source text and spans are sufficient as cache keys. The serialized `source_text` and file contents come from the same LLBC producer; the independent baseline and reconstructed edited hashes constrain the source-state choice but do not constitute a separate compiler-authenticated mapping. I149's cross-layer declaration/generation handoff remains unresolved.

## Resource and scope limits

The one Python-only run sampled fresh preflight reclaimable memory above 25% and minimum **25.8722%** during the comparison, peak measured self RSS **22,396,928 bytes**, and elapsed **0.1321 seconds**. It enforced >20% reclaimable memory, ≤64 MiB RSS and ≤5 seconds; no compiler, translator, server, network access or installation ran. Samples do not establish a sustained host peak.

I079 remains open for Unicode/line-column conventions, arbitrary source movement, generated-file provenance, general LLBC normalization, annotation association, path-sensitive builds, tool/flag changes and Anneal cache-key policy. This result does not update I149 directly.

## Evidence and revalidation

- `support/source-report.md`, `source-report.json`, `source-probe.py`, and `source-results.json` preserve the published witnesses. `support/source-states/` contains the baseline and deterministically reconstructed edited Rust files; `support/artifacts/` contains all 16 raw LLBCs.
- `support/compare.py` is the executed guarded procedure. `support/comparison.json` records every matched item, exact span, source-text hash, source-state/LLBC hash, generated-file exclusion and resource sample.
- `support/check.py` independently validates all copied hashes, reconstructs the 64 slices and 32 exclusions, and checks the edit/revert and offset controls without producer tools.

Run `python3 -B support/check.py` to verify the retained comparison offline. A Unicode or generated-source convention requires a separate independently retained source oracle and fresh guarded experiment.
