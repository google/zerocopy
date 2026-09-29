# Pinned Charon/Cargo build-input closure and wrong-unit control

## Scope and result

This is a component experiment for [#3731](https://github.com/google/zerocopy/issues/3731) I073–I080/I105 and the related Rust-subject rows of [#3730](https://github.com/google/zerocopy/issues/3730). It does not exercise an Anneal implementation. The fixture is a three-package offline Cargo workspace: a primary library and independent binary, a path dependency, and a local proc macro. The primary library uses a `build.rs`-generated `include!`, `include_str!`, `env!`, the path dependency, and proc-macro-generated code.

Ten requests used pinned Charon 0.1.210/Cargo nightly 2026-05-31 on macOS arm64, with one Cargo job, disabled incremental compilation, `--offline --locked -v`, a private source copy, private Cargo target, and private destination for each request. The baseline verbose Cargo log records `build_script_build`, `proc_local`, `dep_path`, and `app_closure` rustc driver units. The build script and proc macro compiled as host artifacts under `target/debug`; the path dependency and primary library compiled for `aarch64-apple-darwin` under `target/aarch64-apple-darwin/debug`. The LLBC parsed with `has_errors=false`.

## Controlled changes

Ordinary source roots have equal-length names so `CARGO_MANIFEST_DIR` length stays fixed. The separate `source-path` case deliberately extends that path. `support/probe.py` records the complete source-file SHA-256 manifest, explicit environment values, command, normalized verbose output, driver-unit sequence, generated Rust text, LLBC hash, crate name, file table, and declaration-body hashes for each request. `support/artifacts/*.llbc` retains the exact outputs.

| One changed input | Observed primary-crate LLBC evidence |
| --- | --- |
| `BUILD_VALUE=7` → `8` | Generated `BUILD_SUBJECT` source and its declaration body changed; `root` body did not need to change because it references the declaration. |
| `PROC_VALUE=3` → `4` | `macro_generated` body changed, including its literal. |
| `PROBE_ENV=A` → `AA` | `root` body changed. |
| `include_str!` payload | `root` body changed. |
| Path dependency `wrapping_add(11)` → `wrapping_add(12)` | Source hash changed and path-dependency unit was compiled, but `dep_path::dep` is opaque in the primary LLBC; its body hash and the primary `root` body stayed the same. |
| Proc-macro source `wrapping_add` → `wrapping_mul` | The primary LLBC function table changed from `core::num::wrapping_add` to include `core::num::wrapping_mul`; the generated function's serialized body uses a function ID, so its body hash alone stayed the same. |
| `build.rs` expression | Generated `BUILD_SUBJECT` text and body changed. |
| Source path length | Generated text and `BUILD_SUBJECT` body changed through `CARGO_MANIFEST_DIR`. |

The path-dependency case is a concrete reason to key a full extraction subject on a resolved Cargo input closure rather than only the resulting primary LLBC bytes. Conversely, a raw whole-LLBC byte diff can be sensitive to destination and source paths; the declaration projections above isolate the observed mechanism. This fixture does not establish the complete closure for arbitrary `build.rs` I/O, network access, environment reads in dependencies, or every proc-macro behavior.

## Compilation-unit rejection

An independent `--bin app_closure_cli` request exited successfully and produced parseable LLBC with `translated.crate_name=app_closure_cli`. The harness then deliberately presented that record to `require_unit(..., "app_closure")`; it rejected it with `wrong compilation unit: expected app_closure, got app_closure_cli`. This negative control checks that a success exit and parseable output are insufficient when the requested unit identity differs. The check covers this fixture's crate-name distinction; a production unit key also needs package, target kind, target triple, profile/features, and appropriate host-versus-target roles.

## Coverage and residuals

| Issue rows | Evidence here | Remaining boundary |
| --- | --- | --- |
| I073–I074 | Materialized private source roots; full source hashes; build script, proc macro, path dependency, generated include, string include, environment and source-path variations. | Unsaved editor overlays, arbitrary build-script/proc-macro side effects, complete Cargo graph and sandbox identity. |
| I075–I076 | Verbose unit sequence, parsed LLBC identity, and deterministic wrong-unit rejection. | Warm-target omission and multi-unit destination collisions are covered in other reports; no full production unit-key implementation here. |
| I077 | Fresh process and private target for each of ten requests. | Same-process Charon reuse/reset remains untested. |
| I078 | Private destination and retained artifact hash per request. | No interruption, atomic publication, or last-good policy tested here; see the separate output-phase report. |
| I079 | One-input-at-a-time LLBC and declaration projections, including opaque path dependency. | Cross-revision semantic diff and an Anneal normalization policy remain open. |
| I080/I105 | Single-process, one-job bounded execution; no shared-writable target. | Multi-process work sharing, cancellation, descendants, resource peaks, and Anneal request lifecycle remain untested in this package. |

## Reproduction and validation

From this report directory, with the pinned tools already present:

```sh
python3 support/probe.py --work /Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r08-replay-new
python3 support/verify.py
```

`--work` must be an absent owned path, and the script requires at least 15 GiB free before starting. The first command overwrites this package's retained LLBC and raw results; the second checks the retained hashes and projections without running Charon. Pinned binary hashes are in `support/raw-results.json` and `REPORT.json`. The LLBC contains absolute paths from the observed run; replay is expected to preserve the qualitative assertions, not the original whole-file hashes.
