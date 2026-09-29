# A frozen Lake producer rejects a changed consumer dependency index

## Summary

At Lake `v4.30.0-rc2`, a producer prepared under one consumer dependency index could be reused by another consumer with the same index while the producer tree was frozen. A consumer that assigned the **same physical producer** a different index failed with permission denied on the producer's compiled-configuration lock file. Restoring producer write permission let that same consumer succeed and changed the producer configuration trace from `idx=1` to `idx=2`. A prepared producer with fixed file permissions therefore did not support these two consumer graph shapes interchangeably in this fixture.

This is a direct frozen-tree control for the writable index rewrite observed in [Lake consumer identity and observability](../anneal-3730-lake-consumer-identity-observability-2026-09-29/REPORT.md). It supplies additional component evidence for #3731 **I090** and #3730 **F01/F05**, while leaving the full preparation key and real Anneal archive contract open. The run does not add a distinct syscall/process observability result for I095/F10.

## Applicability

The tested binaries are Lean/Lake `v4.30.0-rc2`, `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, on macOS arm64. The Lake and Lean binary SHA-256 values in the retained result are `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The fixture has a tiny path dependency `probe_dep` defining `depValue := 7`, an optional `dummy` dependency, and three writable consumer workspaces. Their manifests are complete and local. Lake calls use `--keep-toolchain --no-cache --no-ansi -v build Generated`, `LAKE_ARTIFACT_CACHE=false`, `LAKE_NO_CACHE=1`, isolated home/cache directories, and a 30-second process limit. No install or download occurs.

The primer and matching consumers list only `probe_dep`; Lake assigns it index 1. The shifted consumer lists `probe_dep` and `dummy` in the order that assigns the producer index 2 in this Lake revision. The producer is a single physical directory throughout; only the consumer graph and the producer's write permissions change.

## Findings

| Step | Exit | Producer config trace | Producer inventory |
| --- | ---: | ---: | --- |
| Prime writable producer for index 1 | 0; `Built Dep` | `idx=1` | Baseline after freezing |
| Matching consumer, producer frozen | 0; `Replayed Dep`, evaluates 7 | `idx=1` | Byte/size/mode identical |
| Shifted consumer, producer frozen | 1; permission denied on `.lake/config/probe_dep/lakefile.olean.lock` | Still `idx=1` | Byte/size/mode identical |
| Same shifted consumer, producer writable | 0; `Replayed Dep`, evaluates 7 | `idx=2` | Configuration OLean and trace bytes changed |

The paired frozen and writable shifted calls isolate a producer-side write requirement caused by this graph identity change. The producer module still reported `Replayed Dep` in the successful writable call: module reuse and compiled-configuration mutation are separate observations. The permission failure is an explicit failure rather than a silently stale successful consumer. **Basis: execution**, `support/results.json` command records, trace snapshots, and SHA-256/size/mode inventories.

The lock pathname is the first write-denied object reported by Lake. It does not by itself identify every subsequent write Lake would attempt. The writable control shows actual configuration OLean and trace byte changes after that gate was removed. **Basis: execution**.

## Boundaries

- This test freezes the producer after a single index-1 preparation. It does not determine whether a producer prepared separately for each identity, or a different state layout, could support read-only consumers. It does not derive the complete preparation key.
- The fixture has one tiny Lean module and no real Anneal omnibus archive, Mathlib/Aeneas graph, editor/server operation, native plugin, or dynamic library. F02/F04 still need the actual archive; F03 still needs a later compatible Lake binary.
- Calls are sequential. This result does not characterize simultaneous consumers, shared writers, cache restoration, platform changes, assigned-name changes, root relocation, or all graph orders.
- The inventory records net file SHA-256, size, and mode under the producer. It cannot establish file reads, transient writes that leave equal final bytes, or writes outside that tree. No privileged syscall tracing was used. I095/F10 retain those provenance gaps.

## Evidence

- `support/probe.py` creates the source, manifests, workspaces, isolated environment, frozen permissions, and four bounded Lake invocations. Its retained command output replaces the temporary fixture root and toolchain directory with `$WORK` and `$TOOLCHAIN_BIN`.
- `support/results.json` preserves exact exit codes, stdout/stderr, binary hashes, producer configuration traces, and file inventories before and after each frozen call and after the writable control. The first frozen run and matching control preserve identical inventories; the failed shifted call also leaves the producer inventory unchanged.
- `support/check.py` verifies the distinguishing retained observations and binary hashes without invoking Lake.
- The preceding [consumer identity report](../anneal-3730-lake-consumer-identity-observability-2026-09-29/REPORT.md) contains the related writable name/index matrix and pinned Lake source coordinates. The earlier [concurrency preparation report](../anneal-3730-lake-concurrency-preparation-v4-30-0-rc2/REPORT.md) exercised frozen producers only with matching consumer identities. This package adds the mismatched frozen control.

## Revalidation

Run `python3 support/check.py` for retained-result consistency. To recreate the exact local experiment, run `python3 support/probe.py /new/absent/work/path /absolute/pinned/bin/lake /new/result.json`. Confirm the binary hashes, then compare the four exits, the lock-file failure, producer `idx` sequence `1 → 1 → 2`, and the producer inventory classes. A later Lake revision requires a separately identified toolchain and fresh execution; this report makes no upgrade claim.
