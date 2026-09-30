# Lexical declaration-block comparison of retained Aeneas mutation outputs

## Summary

The [published Aeneas identity-manifest report](../anneal-3730-aeneas-identity-manifest-2026-09-29/REPORT.md) preserved seven successful source/LLBC inputs and their complete generated Lean output trees. It compared whole-file bytes and inventoried declaration heads, but did not compare the text of individual generated declaration blocks. This offline reanalysis compares the **lexically delimited head-through-body text** for every retained declaration in the six mutation outputs against the base output. It adds bounded textual evidence for #3731 **I083** and **I084**; #3730 **E11** is context for a possible finer-grained prototype, not a direct product result.

Each result is a name-matched textual comparison within this one fixture. The names and nearest source comments are not authenticated Rust→Charon→Aeneas→Lean mappings. Identical text does not prove semantic equivalence, safe reuse, stable proof context, or a working per-declaration cache.

## Input and method

The source is published `reference@1332bf21478d8418403d306a7884b653cd735eea`, report `anneal-3730-aeneas-identity-manifest-2026-09-29`. Its `results.json` and `handoff-manifest.json` hashes, all seven Rust and LLBC hashes, and all 21 generated Lean file hashes matched before the comparison. This package copies those exact bytes into `support/` and checks them again. The original producer used pinned Charon 0.1.210 and Aeneas nightly-2026.06.03; this reanalysis ran Python only, with no compiler, translator, server, network access or installation.

For each generated file, the parser checks each declaration head and line number against the published manifest. A block starts at its `def`, `structure`, or other supported head and ends before the next Aeneas source comment, declaration head, or lexical `end` line; trailing blank separator lines are excluded. It hashes the exact UTF-8 bytes in that interval and records start/end lines and byte offsets. This **fixture-scoped lexical delimiter** omits preceding attributes, source comments, imports, namespace/mutual wrappers and module options. It is not a Lean parser and does not assign semantic declaration ownership. No duplicate name/file keys or conflicting boundaries occurred in these retained files.

## Results

| Mutation versus base | Added blocks | Removed blocks | Changed common blocks | Unchanged common blocks | Common blocks with moved starting line |
| --- | ---: | ---: | ---: | ---: | ---: |
| Function body | 0 | 0 | 1 | 11 | 0 |
| Type shape | 0 | 0 | 2 | 10 | 8 |
| Trait implementation body | 0 | 0 | 1 | 11 | 0 |
| Recursive-group member | 0 | 0 | 1 | 11 | 0 |
| Helper insertion | 1 | 0 | 0 | 12 | 5 |
| Delete `step` and `use_step` | 0 | 2 | 0 | 10 | 3 |

The function-body edit changes only the `identity_probe.step` lexical block; `use_step` remains textually unchanged despite referring to `step`. The type-shape edit changes `identity_probe.Wrap` and `Wrap.Insts.Identity_probeBump.bump`; `use_bump` remains textually unchanged despite using that method and type. The trait-implementation edit changes only the method block. The recursive-group edit changes `even`; the retained `odd` block remains textually unchanged despite calling `even`. These unchanged callers are **textual observations**, not independent soundness or dependency-closure oracles.

The helper insertion adds `helper`, keeps all 12 prior blocks byte-identical under this delimiter, and moves five head lines. Deletion removes exactly `step` and `use_step`, keeps the other ten blocks textually identical, and moves three head lines. The complete machine-readable record names every block, file, line/byte interval and SHA-256, with per-case added/removed/changed/unchanged/moved sets. The four requested mutation controls were checked explicitly against expected changed blocks. **Basis: execution** of the guarded retained-data comparison.

## Limits for I083, I084 and E11

I083 gains one small whole-translation oracle decomposition: some generated blocks remain textually identical while their containing `Funs.lean` file changes. It does not establish a dependency graph, safe item-level invalidation, producer support, or a semantic oracle. I084 gains same-name block and line-movement observations for this fixed fixture, including helper insertion. It does not test module moves, arbitrary name/signature stability, annotation migration or Lean elaboration. E11 remains context: no restricted cache prototype or same-process Aeneas API was exercised here.

The delimiter excludes comments, attributes and surrounding commands; changes in those regions can affect elaboration without changing a recorded block. Source comments contain path and line hints only. Aeneas output text may move while a block hash stays equal. The result must not be used as a publication or reuse decision by itself.

## Evidence and revalidation

- `support/source-report.md`, `source-report.json`, `source-probe.py`, `source-results.json` and `source-handoff-manifest.json` preserve the published report and result witnesses. `support/inputs/` preserves seven Rust and seven LLBC files; `support/outputs/` preserves 21 raw Lean files. All hashes are checked by `support/check.py`.
- `support/compare.py` is the guarded acquisition procedure. `support/comparison.json` records all 83 block observations, six comparisons, input/output hashes, resource samples and exact lexical intervals. Its run sampled minimum **25.1751%** reclaimable memory, peak self RSS **22,708,224 bytes**, and elapsed **0.0730 seconds** under 64 MiB/5-second caps.
- `support/check.py` independently reconstructs the lexical intervals and six comparison sets from the copied raw bytes, verifies the four mutation controls and metadata, and uses no producer tools.

Run `python3 -B support/check.py` for offline verification. A fresh acquisition requires exact source hashes and a fresh >20% reclaimable-memory preflight; it must remain under 64 MiB RSS and five seconds. A different Aeneas output grammar needs a newly reviewed delimiter or a real parser.
