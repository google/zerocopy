# Full-field explanation of the retained cold/warm selected-binary LLBC hash change

## Summary

The two raw Charon LLBC files in the [warm selected-binary report](../anneal-3731-i075-warm-bin-target-2026-09-29/REPORT.md) have different SHA-256 values. An exhaustive decoded JSON comparison finds **exactly 30 differing leaves**: one requested destination path and 29 positional leaves under `translated.short_names`. The 15 typed-key/name entries are the same map in both files; 11 array slots changed position. Every other decoded field, including all function declarations, embedded source contents, crate name and error status, agrees. Both original compact JSON files round-trip byte for byte through the decoded representation, so these observed path and ordering differences fully account for their raw-byte inequality in this pair. This advances #3731 **I079** with #3730 **D03** context; it does not establish semantic equivalence or cache-fresh behavior.

## Applicability

This is offline reanalysis of the exact `baseline.llbc` and `warm_repeat.llbc` preserved by the source report. The original pinned Charon 0.1.210 `--bin subject_matrix_cli` commands selected one unchanged source fixture and reused one Cargo target sequentially, but used distinct initially absent output paths. The second call was warm **only by retained-target reuse**: Cargo logged `Dirty subject_matrix ... couldn't read metadata for file ...libsubject_matrix-21be0fdd0836da51.rlib` and recompiled the library and binary. The source report's checker passed before copying the two LLBCs and results byte for byte. This analysis ran no Charon, Cargo, rustc, server, network request or installation.

The comparison recursively checked every JSON object key, array position, type and scalar without normalization. It separately compared the serialized typed-key/name map in `short_names` and checked whether compact JSON serialization reproduced each original raw file exactly. The source report's producer-invocation and cleanup evidence is inherited; the current package does not replay it.

## Findings

| Raw file | Bytes | SHA-256 |
| --- | ---: | --- |
| Cold baseline | 54,276 | `5d1ae9cb6d26d618985cd092fd0218faf1a3c6e2c188f77eebd8615fccf20580` |
| Retained-target forced-dirty repeat | 54,279 | `6021a295099927891f14c18bfbb0ec2b1e6b851f72b800f1c203443e9d5cbe0d` |

The first changed decoded leaf is `/translated/options/dest_file`: the preserved original destinations end in `baseline.llbc` and `warm_repeat.llbc`. The latter path is three bytes longer, matching the raw file-size difference. The other **29 changed leaves** are under `/translated/short_names/`. That array has 15 entries in both outputs; positions 3, 4, 5, 6, 8, 9, 10, 11, 12, 13 and 14 contain different entries. Indexing by serialized typed key yields the same 15 key/value entries in both. Seven nested object-key-sequence differences occur where two reordered entries of different typed-key variants occupy the same array slot; they are part of that positional permutation, not another independent change.

Both files equal the compact JSON reserialization of their own decoded values byte for byte. Their differing raw hashes are therefore explained by the one path string and the `short_names` permutation in this exact pair. No function declaration, source contents, file-table entry, option other than the destination, crate identity, error status or other decoded field differs. **Basis: execution** of the retained-data comparison, with every differing path and exact value in `support/comparison.json`.

The source report already established that Cargo re-invoked the requested binary Charon producer in a **forced-dirty** retained target. The present observation only isolates output-byte variability. It does not imply that a genuinely cache-fresh warm request would invoke Charon or yield this output. Matching decoded model fields outside the two difference families does not prove Rust semantic equivalence or that every LLBC consumer ignores `short_names` order.

## Boundaries

- Two outputs from one small selected-binary fixture and one pinned tool combination were compared. No independent changed-source negative control, second Charon pin, Aeneas/Lean consumer, or general LLBC canonicalizer was run.
- The requested destination path is real artifact identity. Array order is observable in the serialized LLBC even though this fixture's typed-key/name map agrees. A raw-byte cache will distinguish the files; dropping either field requires an explicit provenance and consumer policy.
- The original warm repeat was a forced-dirty rebuild after a missing cached `.rlib` metadata read. The open I075 cache-fresh producer case, I076 output ownership policy, and Anneal materialized-snapshot target behavior remain untested.
- The Python run had four resource samples: preflight reclaimable memory **24.4442%**, minimum **24.4379%**, peak measured self RSS **22,429,696 bytes**, and elapsed **0.02585 seconds**. Sampling does not establish an unsampled host peak.

## Evidence

- `support/artifacts/` preserves the two byte-for-byte copied raw LLBCs. `support/source-results.json`, SHA-256 `ecc7934451a6da4bc94ee7e0e7006f5fdfa162736afa344e32f31d4491b7dac5`, is an unchanged copy of the original source execution record. The published source `REPORT.md` SHA-256 is `866d4712bc9991cb95c6ecfad3c395a0b34f58799ec0a9e145144dde71267914`.
- `support/compare.py`, SHA-256 `8e511e81aa48dde2695348314bf1145eb6496919e2055a8fdfd67682a24f9332`, is the executed guarded Python procedure. It checked ≥20% reclaimable memory before input and after each decode/comparison, and enforced 64 MiB self RSS and five seconds. `support/comparison.json`, SHA-256 `463abe75a867c3a14dc1d827bd08430b606ee07aaaadf0270fdc89eddeab4360`, retains both raw hashes, all 30 differences, array-order observations, byte-exact JSON round trips and resource samples.
- `support/check.py` independently recomputes every decoded difference, array/keyed-map relation and exact JSON round trip, and validates source hashes and resource gates without invoking compilers or servers.

## Revalidation

Run `python3 -B support/check.py` from this package. It validates the retained comparison only. A fresh analysis requires the same two raw hashes and a fresh ≥20% reclaimable-memory preflight under the documented RSS/time caps. To answer cache-fresh producer behavior or Anneal output ownership, a separate guarded producer experiment and product integration are required.
