# Full-field comparison of retained Charon cancellation and cold-oracle LLBCs

## Summary

Four retained successful LLBCs from the warmed shared-target cancellation/retry fixture were compared field by field with their independent cold-target oracles. In each same source-state pair, **every decoded JSON leaf difference** is confined to the requested destination path, one generated-file path under the Cargo target, or the positional order of `translated.short_names`. The typed-key-to-name mappings in `short_names` are equal. No function declaration, embedded source contents, error status, crate name, or other decoded field differs in those pairs. An edited-versus-baseline oracle control detects the expected `step` literal and source-text change. This extends the source report's five selected function-body-hash checks for #3731 **I080** and #3730 **D03/D06**; it does not establish an Anneal output-ownership policy or general semantic equivalence.

## Applicability

This is **offline reanalysis** of the exact six LLBC bytes published in [the I080 cancellation report](../anneal-3731-i080-incremental-on-shared-target-cancel-recovery-2026-09-29/REPORT.md), whose source `results.json` SHA-256 is `42822b05…c89ea`. That source run used pinned Charon 0.1.210, nightly-2026-05-31 Cargo/rustc, `CARGO_INCREMENTAL=1`, one warmed shared writable Cargo target for A/B, and separate cold targets for the two oracles. The current analysis did not rerun Charon, Cargo, rustc, Aeneas, Lean or Lake. The six byte-for-byte copied LLBCs and source results are retained under [`support/`](support/).

The comparison parses each LLBC as JSON and recursively compares **all** object keys, array positions, types and scalar values. It performs no normalization before recording differences. [`comparison.json`](support/comparison.json) contains every differing leaf path and both exact values. A separate interpretation checks whether each `short_names` array, when indexed by its serialized typed key, contains the same key/value entries; it does not erase the original order differences.

## Findings

| Pair against cold oracle | Different decoded leaves | Exact difference families |
| --- | ---: | --- |
| prewarm A → baseline B | 14 | 12 positional `short_names`; destination path; generated-file local path |
| prewarm B → baseline B | 12 | 10 positional `short_names`; same two path fields |
| companion B → baseline B | 17 | 15 positional `short_names`; same two path fields |
| recovered A → edited A | 19 | 17 positional `short_names`; same two path fields |

The generated-file path is `/translated/files/1/name/Local`; it points into the shared or oracle Cargo target. The output locator is `/translated/options/dest_file`. Those path identities remain part of the evidence and cannot be dropped from an authenticated artifact key merely because this fixture's other decoded fields agree. `translated.short_names` entries occupy different array slots, but each same source-state pair has the same typed key/value map. **Basis: execution of the retained-data comparison**, with exact values in the machine record.

The negative control compares cold edited A with cold baseline B and finds 23 different leaves. Besides destination, generated-file path, and positional short-name differences, it finds a changed embedded Rust source body (`wrapping_add(2)` versus `wrapping_add(1)`), changed `step` source text, and the serialized call argument literal **2 versus 1** at `/translated/fun_decls/0/body/Structured/body/statements/2/kind/Call/args/1/Const/kind/Literal/Scalar/Unsigned/1`. The comparison therefore detects a substantive model change in the same corpus. **Basis: execution**.

The source report's cancellation/companion scheduling and process cleanup remain its own observations. This package checks the completed outputs, not the canceled A request, which produced no LLBC. It does not show when Cargo acquired or released a lock, whether the retried build script ran, or whether all Rust dependency effects were faithfully included.

## Boundaries

- Field equality after excluding the three observed difference families is a statement about these six decoded JSON values only. It is not a proof of Rust semantic equivalence, model soundness, path-insensitive caching, or byte-identical LLBCs.
- The source report's selected five local bodies were already equal for the same source-state pairs. This reanalysis adds an exhaustive decoded-field inventory and the generated-file-path distinction; it does not add a new Charon schedule.
- Array-position differences in `short_names` may matter to a byte-keyed cache even when typed-key maps agree. This package does not prove all LLBC consumers ignore that order.
- The old/edited oracle difference is a negative control, not evidence that every relevant Rust edit is reflected in LLBC.
- No actual Anneal owner, publication transaction, target policy, or representative resource workload was exercised. I080 and D03/D06 remain partial.
- Resource gates sampled this short Python process, not a sustained host peak. The comparison itself ran for 0.05482 seconds, with maximum measured self RSS 22,216,704 bytes and minimum sampled reclaimable memory 22.6244%. It stayed below the 64 MiB, five-second, and 20% gates.

## Evidence

- [`support/artifacts/`](support/artifacts/) preserves all six raw LLBCs (145,317 bytes total) with exact SHA-256 values in [`comparison.json`](support/comparison.json). [`support/source-results.json`](support/source-results.json) is an unchanged copy of the source report's execution record. The source package's checker passed before these copies were made.
- [`support/compare.py`](support/compare.py), SHA-256 `cbe0ac43e1a4d81458c9256a066b8cea224de504a889b5d47f2363895d8f22fc`, is the exact guarded Python comparison. It rechecks `vm_stat` at preflight, after each decode and after each pair, and checks self peak RSS and elapsed wall time at those points. [`support/comparison.json`](support/comparison.json), SHA-256 `be26b95d7a7e290624598f1916382ab79db89832271a1ad0ae742785db942029`, is the acquired complete difference record.
- [`support/check.py`](support/check.py) revalidates source/artifact hashes, every recorded difference, typed-key map equality, negative-control fields and sampled guards without launching any compiler or server.

## Revalidation

Run `python3 -B support/check.py` from this package to validate the retained analysis. A fresh acquisition requires a separate copy without `support/comparison.json`, the same six content hashes, and a new ≥20% reclaimable-memory preflight; run `python3 -B support/compare.py` there. A different Charon tool, Cargo target policy, source root or artifact set is a new subject and needs new controls.
