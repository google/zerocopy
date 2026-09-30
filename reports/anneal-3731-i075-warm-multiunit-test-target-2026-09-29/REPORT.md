# Warm multi-unit Cargo test target: Charon producer and destination ownership

Observed 2026-09-29 on macOS arm64 with pinned Charon 0.1.210 and nightly Rust/Cargo 2026-05-31. This is a bounded component follow-up for [#3731 I075/I076](https://github.com/google/zerocopy/issues/3731). It does not exercise the Anneal V2 extraction publisher.

## Prior evidence and distinct question

The [subject/output-phase matrix](../anneal-3730-charon-subject-output-phase-matrix-2026-09-29/REPORT.md) ran four `--test check` requests in separate **cold** Cargo targets. Each invoked library, binary and test Charon drivers, and the one destination ended as either the requested test or the binary. The [warm-target controls](../anneal-3730-charon-warm-target-controls-2026-09-29/REPORT.md) repeatedly extracted one explicit `--lib` unit, including after ordinary Cargo reported `Fresh`. The [scaling/closure report](../anneal-3730-charon-scaling-subject-closure-2026-09-29/REPORT.md) used fresh targets. None retained an unchanged-source, same-target warm repeat of a **multi-unit** `--test check` Charon request. Published [v33](../anneal-3730-3731-final-coverage-audit-2026-09-29-v33/REPORT.md) leaves I075's warm alternate-target extraction attestation and I076's produced-output ownership open at the product gate.

## Executed cell

The package copies the earlier tiny dependency-free `subject_matrix` fixture without modification: library, `subject_matrix_cli` binary and `check` integration test. The copied source, manifest and lockfile hashes are retained in `support/results.json`. Two sequential invocations used the **same fixture path**, unchanged bytes and one private `CARGO_TARGET_DIR`. Both used `charon cargo --preset aeneas --dest-file <distinct private destination> -- --manifest-path <same Cargo.toml> --test check --offline --locked -j 1 -v`, `CARGO_INCREMENTAL=0`, one Cargo job and `RAYON_NUM_THREADS=1`. No install, fetch, network or concurrent process was requested. The second invocation began after the first exited and retained its target directory, so it was a warm-target repeat. It used a new destination pathname to attest creation rather than accept an old file.

| Cell | Charon driver crate order in full verbose stderr | Exit | Retained destination LLBC crate | LLBC SHA-256 |
| --- | --- | ---: | --- | --- |
| Cold baseline | `subject_matrix`, `subject_matrix_cli`, `check` | 0 | `check` | `218a41353a6755bcfc6b1ebb2b8c4f21e2f5a7430e1f18b7c4e2b56bf297a623` |
| Warm repeat | `subject_matrix`, `check`, `subject_matrix_cli` | 0 | `subject_matrix_cli` | `007fe60b44f660294b1253c76758f77841b0f85fbfb904c3aa28556adb5ae370` |

Both outputs parse as Charon 0.1.210 LLBC with `has_errors: false`. Both verbose logs say `Compiling subject_matrix`, contain three full `Running ... charon-driver rustc --crate-name ...` lines, and finish the dev profile. Therefore this warm request did **not** skip the Charon-producing invocations in the observed cell. Yet the requested test's driver ran and the warm repeat's single destination contained the binary. The process success, existence and parseability of that destination did not attest the requested `check` unit. The observed driver-line order matches the final crate in each cell; this does not prove low-level writer interleaving or a general last-writer rule.

The guarded runner sampled `vm_stat` reclaimable memory (`free + inactive + speculative` / physical memory), filesystem free bytes, process-group RSS and owned scratch throughout both calls. Lowest observed estimate was **23.333%** and free disk **43,310,911,488 bytes**; maximum sampled process-group RSS was **137,392 KiB**, maximum owned scratch **419,083 bytes**, and each call was below one second. No guard fired. The runner removed the private target/fixture/destinations after copying raw outputs. These are sampled host measurements, not peak unique memory or a sustained scalability estimate.

## Scope for I075 and I076

- **I075, direct bounded component evidence:** under this exact warm `--test check` command and tool pin, Cargo re-invoked all three Charon-producing units and produced a new LLBC. This closes neither other target kinds/wrappers nor the V2 requirement to reject success when its requested producer did not run.
- **I076, direct bounded component evidence:** the warm repeat's destination identified the binary, although the requested test compiled and the command succeeded. A consumer must bind and attest the chosen output to the complete requested Cargo compilation unit before publication. The Anneal V2 helper, CLI path, full unit key, collision rejection, concurrent arbitration and invalidation were not exercised.

## Retained evidence and verification

`support/probe.py` is the executed guarded runner, with the post-run parser correction from top-level `crate_name` to `translated.crate_name`; it was **not replayed** after that correction. `support/results.json` retains exact command arrays, selected environment, tool/input hashes, per-sample resource readings, destination paths/hashes and decoded crate names. `support/raw/` retains complete stdout/stderr; `support/artifacts/` retains both exact LLBCs. The parser correction to the retained result read the saved LLBCs only. The original private destination paths remain in the record, while `support/check.py` verifies corresponding candidate-local artifact bytes, so it works after package relocation. Run `python3 -B support/check.py` from the package. This is read-only and does not invoke Charon.
