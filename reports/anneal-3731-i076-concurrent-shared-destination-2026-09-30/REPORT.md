# Concurrent Charon release/cfg writers at one LLBC destination

## Summary

One guarded pair of pinned Charon 0.1.210 `cargo` requests compiled distinct release and debug `--cfg probe_alt` subjects concurrently into one initially absent `.llbc` destination. Both commands exited 0, and repeated RSS samples show both process groups alive simultaneously. After both settled, the single retained output was parseable, error-free LLBC whose selected function literals matched the **release** control (`11/23`), not the cfg control (`7/29`). This is a concrete concurrent shared-path outcome for #3731 **I020/I076**. It does not establish write order, atomicity, an Anneal publisher decision, or a wrong-subject proof result.

## Applicability

The subjects were one unchanged dependency-free Rust library source (`src/lib.rs` SHA-256 `990beab58abb9a04f48c119fdcea2918865232730e278de3def35e15831b123d`) and the locally installed Charon/Cargo/rustc binaries identified by full SHA-256 values in [REPORT.json](REPORT.json). The Rust toolchain was `nightly-2026-05-31-aarch64-apple-darwin`. These hashes identify the observed binaries; the package does not independently establish their source-build provenance.

The experiment reused byte-exact [v47 separate-destination controls](../anneal-3731-i076-sequential-shared-destination-2026-09-30/REPORT.md). Their release LLBC had selected `profile_value`/`config_value` U32 literals `11/23`, while the cfg LLBC had `7/29`; their raw SHA-256 values are pinned and copies are retained under [`support/controls/`](support/controls/). The fixture, tool hashes and source hash matched v47 exactly, so no new controls were compiled. Prior source-level copied Anneal V2 slug evidence links both compilation variants to one artifact filename, but this new pair invoked Charon directly, not the V2 CLI or Anneal publisher.

Both requests used `--preset aeneas`, `--lib --offline --locked -v -j 1`, `CARGO_NET_OFFLINE=true`, `CARGO_INCREMENTAL=0`, and one Rayon thread. Release added `--release` with release debug assertions disabled; cfg used debug mode with `RUSTFLAGS=--cfg probe_alt`. Each had a private `CARGO_TARGET_DIR`; both used the exact same initially absent `--dest-file` path. The pair ran once with no package fetch or installation.

## Findings

| Observation | Release process | Cfg process |
| --- | ---: | ---: |
| PID | 97577 | 97578 |
| Exit | 0 | 0 |
| Driver invocations in verbose stderr | 1 | 1 |
| Pinned separate control literals | `11 / 23` | `7 / 29` |
| Simultaneous RSS sample at 0.2262 seconds | 33,264 KiB | 33,312 KiB |

Five of six periodic samples recorded nonzero RSS for **both** process groups, including the shown sample. That is direct evidence of simultaneous live Charon process groups, independent of the recorded command collection intervals. Both `charon-driver rustc` lines are retained in full; the release line contains `-C opt-level=3` and the cfg line contains `--cfg probe_alt`. Both commands exited 0 with no guard reason. **Basis: execution.**

The output path was absent before launch. After both process groups had settled, the retained [`shared-final.llbc`](support/artifacts/shared-final.llbc) was 5,592 bytes, SHA-256 `14940da1e9aa6b79b8c03abd3981bb85a6cee4b99a6fac97093a51c3d163fe49`. It parsed as `unit_key_probe` LLBC with `has_errors: false`, included the unchanged fixture source hash, and serialized the shared destination path. Its selected `profile_value`/`config_value` literals were **`11/23`**, matching the release control. The two subjects' local function bodies are distinguishable by the selected literals; raw whole-file equality to a separate-destination control is not expected because the serialized path differs. **Basis: execution.**

The runner required >33% estimated reclaimable memory to admit this run, giving more than the requested >30% launch threshold. Its retained preflight was **34.3779%** with **18,911,215,616 bytes** free disk. During the pair, the minimum sampled reclaimable estimate was **34.2907%**, minimum free disk **18,911,092,736 bytes**, peak summed process-group RSS **66,576 KiB**, and peak private scratch **64 KiB**. The pair completed in **0.2843 seconds**, inside 15 seconds; no 20%-memory, 10-GiB-disk, 512-MiB-RSS or 100-MiB-scratch stop fired. A post-run check found zero non-zombie RSS in both process groups, and the private work tree was removed. These sampled measures can miss short peaks and do not attribute host memory changes to Charon. **Basis: execution.**

## Boundaries

Only one concurrent pair was admitted and run. The final release model shows which complete selected model was present **after** both commands settled, not which writer reached or closed the file last. The runner did not make an in-flight file snapshot: copying while two producers wrote could have produced an unstable observation. Its recorded `end_monotonic_ns` values are collection timestamps after polling, not exact exit or file-write timestamps. Therefore the package does not establish write interleaving, first/last writer order, atomic replacement, partial-reader behavior, repeatability across schedules, or cross-platform behavior.

I020 and I076 remain **partial** at their existing **product** gates. The pair did not use the V2 CLI, Anneal artifact publication, a consumer workspace or an interactive proof query. Complete compilation-unit identity, output ownership, collision rejection and concurrent producer/consumer policy remain product prerequisites. #3730 D07 gains bounded component context, but its residual, gate and prerequisite remain unchanged.

## Evidence

- [`support/probe.py`](support/probe.py) is the exact executed guarded runner. [`support/results.json`](support/results.json) retains both argv/environment records, PIDs, monotonic/UTC intervals, every host/RSS/scratch sample, stdout/stderr hashes, driver lines, final output projection and cleanup. [`support/raw/`](support/raw/) retains complete stderr/stdout for both commands.
- [`support/fixture/`](support/fixture/) and [`support/controls/`](support/controls/) retain the exact source and byte copies of v47's separate controls. [`support/artifacts/shared-final.llbc`](support/artifacts/shared-final.llbc) is the sole after-settlement destination snapshot. All are pinned by the recorded hashes. No in-flight bytes were captured.

## Revalidation

Run `python3 -B support/check.py` from this package. It validates the retained controls, simultaneous RSS evidence, command/environment distinctions, resource limits, final LLBC bytes and decoded release literals, and cleanup without rerunning Charon. A new execution requires a fresh package copy and a new resource admission; any different winner or parse failure would be a separate observation, not a reason to relabel this one.
