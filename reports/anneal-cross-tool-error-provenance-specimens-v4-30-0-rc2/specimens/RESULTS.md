# Charon → Aeneas → Lean bounded local experiments

Run on 2026-09-27 in this directory only. The published `reference` subjects inspected first were Charon closure/trait/dependency coverage, Aeneas loops/type aliases/raw pointers/Rust support/naming, plus `anneal/research/aeneas-determinism.md` and `translation-goldens.md`. This is a fresh small fixture probe of the pinned local binaries, not a revision comparison or a correctness proof.

## Reproduce and evidence

From the zerocopy checkout, in order:

```sh
source .anneal-local-tools/env.sh
python3 .anneal-local-tools/scratch/20260927-reference-experiments/aeneas_charon/run.py
python3 .anneal-local-tools/scratch/20260927-reference-experiments/aeneas_charon/followup.py
python3 .anneal-local-tools/scratch/20260927-reference-experiments/aeneas_charon/coverage.py
```

`run.py`, `followup.py`, and `coverage.py` contain every invocation, flags, input, and timeout. `manifest.json`, `followup.json`, and `coverage.json` record exact argument vectors, working directories, status, duration, output paths, hashes, and log paths. `cases/`, `followup/`, and `coverage/` preserve Rust, LLBC, and generated Lean. `logs/` preserves stdout and stderr. No repository source, published report, or reference package was modified.

The scripts ran one process at a time, with 30-second Charon/Aeneas and 60-second Lean timeouts; the maximum observed child wall time was 13.709 seconds, and no subprocess timed out. The script checked scratch size, free disk, and `memory_pressure` before each case. Scratch stayed well below 1 GiB; final size was under 1 MiB. These are direct-process timeout bounds, not a full process-tree resource measurement.

## Cross-layer matrix actually run

All Charon runs below used `charon rustc --preset aeneas` with the local nightly rustc, `--crate-type lib --edition 2021`, one source file, and an explicit LLBC destination. `has_errors` was false in every emitted LLBC. Aeneas used Lean backend, `-abort-on-error -warnings-as-errors -sequential -no-progress-bar`. Lean checks used `lake env lean FILE` from the prebuilt Aeneas Lean project. A successful Lean check establishes acceptance of the generated file against that local library, not semantic correspondence with Rust.

| Fixture | Charon | Aeneas | Lean | Direct observation |
| --- | --- | --- | --- | --- |
| Baseline `choose`, mutable `bump` | 3/3 exit 0, 3 ordered declarations | 3/3 exit 0 | 3/3 exit 0 | Same generated Lean hash on three repeats despite raw LLBC hash drift. |
| Capturing closure | exit 0, 19 ordered declarations | exit 0 | exit 0 | Generated closure state, `Fn`/`FnMut`/`FnOnce` methods and impls. |
| Local trait and impl | exit 0, 6 ordered declarations | exit 0 | exit 0 | Generated `Step` structure, impl dictionary, method call. |
| `while` loop | exit 0, 2 ordered declarations | exit 0 | exit 0 | Generated `sum_to_loop.body`, `sum_to_loop`, and `loop` combinator call. |
| Ordinary `Count = u32` alias | exit 0, alias appears in `type_decls` | exit 0, only `inc` emitted | **exit 1** | Default crate namespace `alias` is a Lean keyword; parser rejects `namespace alias`. `Count` is absent in Lean, and `inc` uses `Std.U32`. |
| Raw pointer dereference | exit 0, function body present | **exit 2** | not run | Explicit error: `Aeneas does not yet support dereferencing raw pointers`, with Rust source span. |
| Function pointer parameter/call | exit 0, function body present | **exit 2** | not run | Explicit error: `Arrow types are not supported yet`, with Rust source span. |
| Same `tick` spelling in two modules | 3/3 exit 0, 4 ordered declarations | 3/3 exit 0 | 3/3 exit 0 | Generated `alpha.tick` and `beta.tick` as distinct declarations, identical Lean bytes across repeats. |

The alias namespace issue was isolated by rerunning the same LLBC with `-namespace alias_probe`: Aeneas exit 0, and the resulting generated Lean checked with exit 0. This identifies an output naming/escaping edge case under the default namespace, not a failure to translate the alias's underlying `u32` type. The exact default and overridden outputs and Lean diagnostics are in `cases/alias/` and `followup/alias_namespace/`.

## Repeatability and coverage probes actually run

- Four Charon extractions of the baseline into the **same** destination all exited 0. Raw LLBC SHA-256 values were `a31a1bdb…`, `d0333837…`, `4740a442…`, `4740a442…`. JSON values differed in keyed `translated.item_names` and `translated.short_names` ordering. Sorting only these and `assoc_item_names` by serialized key, while preserving all other arrays, made all four complete JSON values equal; the canonical hashes are in `canonical-order-check.json`. This demonstrates an observed serialization-order difference on one fixture, not general deterministic semantics.
- Against one fixed baseline LLBC, two `-sequential` Aeneas runs generated identical `Baseline-0.lean` hashes; two `-split-files` runs generated the same `Types.lean` and `Funs.lean` inventory and per-file hashes. The split files were **not** separately Lean checked, because that requires assembling their generated import/module layout. The ordinary single-file and namespace-override outputs were Lean checked as noted above.
- `--start-from crate::choose` on the baseline emitted one ordered declaration rather than the whole-crate three. Charon exit 0 and `has_errors: false`, Aeneas exit 0, and Lean exit 0; the generated file contains `choose` but not `bump`. This is a concrete coverage boundary: successful stage statuses do not establish coverage of unselected source items. Evidence: `coverage.json`, `coverage/choose.llbc`, and `coverage/lean/Choose.lean`.

## Exact tool identity and limits

- Local release `charon` SHA-256: `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`; release `charon-driver`: `09a530746044c0ef169f7d0cfa099700c06934163a70b138cafc6d125d08037e`. This Charon binary rejects top-level `--version` and `-V`, so its source report's `0.1.210` is not claimed as an executable version response here.
- Local release `aeneas` SHA-256: `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`; `aeneas -version` reported `unknown`.
- `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`; executed binary SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`.
- `lake env lean --version` from the bundled Aeneas project reported Lean `4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. Executed Lean binary SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. Invoking the elan `lean` shim outside a project reported no default toolchain; all actual Lean checks used the bundled project's `lake env`.

Scope is eight tiny dependency-free Rust libraries on one macOS aarch64 target. No Cargo workspace, build script, cfg matrix, large-scale extraction, V1 scanner execution, binary revision change, unsupported feature universe, proof obligations, or Rust↔Lean semantic adequacy was established. The `--start-from` comparison is a direct Charon/Aeneas coverage probe, not an Anneal scanner test. The successful Lean checks only establish parser/elaborator acceptance of the generated examples.
