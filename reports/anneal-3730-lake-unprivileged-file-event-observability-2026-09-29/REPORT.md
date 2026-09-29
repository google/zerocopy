# Unprivileged file-event witness for Lake replay and rebuild

## Result and scope

This report adds a bounded **I095 / #3730 F10** observation absent from the prior Lake action-and-net-delta report: an unprivileged `DYLD_INSERT_LIBRARIES` observer recorded selected libc file calls by the actual Lake process and its Lean child. On one tiny private Lake module, a warm `Replayed Dep` still opened `Dep.lean`, `Dep.trace`, hash sidecars, and compiled configuration files; it positively recorded an 88-byte `read` of `lakefile.olean`, although the before/after file inventory showed no net change. Cold and changed builds recorded a Lean child whose logged parent was the Lake PID, and a successful rename from a temporary `Dep.olean.tmp.<Lean PID>` to the final OLean. That temporary file was absent from the final inventory. This is a positive observation of selected library calls, not a complete syscall, file-read, or no-write proof.

The fixture used cached Lean/Lake `v4.30.0-rc2` on arm64 macOS 26.6.2. `lean-toolchain`, `lakefile.lean`, `Dep.lean`, and `Check.lean` were generated inside a private report worktree. `Dep.lean` initially defined `value : Nat := 7`; a mutation changed it to `9` while restoring its previous mtime. Each Lake call used `--keep-toolchain --no-cache --no-ansi -v`, `LAKE_ARTIFACT_CACHE=false`, `LAKE_NO_CACHE=1`, and `LEAN_NUM_THREADS=1`. The source mutation's no-build call also used `--rehash --no-build`. The single Lake process per phase had a 35-second timeout and a 2-GB free-disk preflight. No dependency was downloaded, installed, or accessed outside the existing cached toolchain and private fixture.

| Phase | Exit | Selected libc events / distinct PIDs | Net fixture changes | Main observation |
| --- | ---: | ---: | ---: | --- |
| Cold build | 0 | 41 / 2 | 11 | Lake `Built Dep`; child `process-lean` names Lake as parent; temporary OLean rename |
| Unchanged replay | 0 | 11 / 1 | 0 | Lake `Replayed Dep`; opens source/trace/hash files; one positive configuration-OLean read |
| Same-mtime mutation, `--rehash --no-build` | 3 | 9 / 1 | 1 | Builder needed; `.trace.nobuild` added |
| Changed build | 0 | 40 / 2 | 9 | Lean child and temporary-to-final OLean rename; `Built Dep` |
| Subsequent replay | 0 | 11 / 1 | 0 | `Replayed Dep` with selected file calls |
| Unhooked subsequent replay | 0 | no hook | 0 | Same Lake replay classification without the observer |
| Fresh batch `#eval value` | 0 | no hook | 0 | Lean reported `9` |

Each event records PID, operation, return value, numeric flags or byte count, and a path under `$WORK`. The process-start event also records PPID and the observed executable basename; in cold and changed builds the Lean PPID equals the Lake PID. The retained output includes every selected event, not just the table counts. The `-v` replay output also prints a saved `lean ... Dep.lean` command, as earlier reports warned; the one-process replay event record provides an independent positive contrast to the two-process build record. It does not prove no short-lived child existed through another launch path.

## What the observer sees

[`support/observe.c`](support/observe.c) interposes `open`, selected `openat`, `read`, `write`, `rename`, and `unlink` in an inheritable user-space dylib. It logs only paths under the private fixture root, uses direct system calls for its own append-only event log to avoid recursion, and records a process-start marker when loaded. Relative `openat` with a directory FD other than `AT_FDCWD` is deliberately excluded because this small observer cannot attribute its path correctly. The reproducible compile invocation and observer binary SHA-256 are in [`support/results.json`](support/results.json); the host-specific dylib is not retained. The raw per-phase TSV files were normalized into `results.json` and removed, as were generated build artifacts. Only source, checker, and compact captured results are part of the package.

The observer does **not** see direct syscalls that bypass these interposed symbols, other libc entry points such as `fopen`/`pread`/`mmap`, all reads or writes performed inside library implementations, access outside `$WORK`, or short calls that happen before the dylib loads. Its `open` records intent and return FD, not proof that bytes were consumed; its `read` record is a positive byte-count witness for that one compiled configuration file. No ordinary OLean `write` event was captured even though OLean bytes changed, illustrating this observer's incompleteness. The interposition itself can affect behavior; the unhooked final replay and fresh unhooked batch are narrow semantic controls, not equivalence of every build event. No privileged `fs_usage`, DTrace, or kernel tracing was used.

## Reproduction and residual

Run `python3 support/check.py` for the retained offline assertions. It verifies the source hash, pinned binary hashes, all phase exits, Lake labels, normalized selected paths, parent-child relationship, positive read, no-build sidecar, temporary artifact rename, unhooked replay, and fresh value `9`. Run `python3 support/probe.py` to recreate the private fixture and event record using existing `/usr/bin/clang` and cached Lean/Lake. The probe writes only inside this package's `support/` directory, then removes generated work, raw TSV files, and the local dylib after serializing `results.json`. Its exact compile command and Apple clang version are retained. No shell profile, global cache, published report, or toolchain file is modified.

This narrows **I095/F10** from action labels and net deltas to a positive selected read and transient artifact rename in a real process tree. Complete read/write provenance, true no-process/no-network assertions, prepared-scale parallelism, and the actual Anneal archive still require an authorized tracing or instrumented product surface and representative prepared consumer. The prior [Lake consumer identity/observability report](../anneal-3730-lake-consumer-identity-observability-2026-09-29/REPORT.md) owns the index/alias and action-label controls; this package adds only the private library-call witness.
