# Lake behavior probes

## Summary

A fresh consumer could use a relocated read-only prebuilt producer when its relative Lake manifest existed before Lake first loaded the workspace. Without that manifest, Lake attempted a config-lock write in the producer. The small clean/cache variants produced identical `.olean` bytes.

## Applicability

Lean 4.30.0-rc2/Lake 5.0.0-source on macOS arm64, using a two-module local synthetic dependency and a generated consumer. No Mathlib tree was copied. Related corpus reports: [lake-readonly-relocation-offline-concurrency-v4-30-0-rc2](../lake-readonly-relocation-offline-concurrency-v4-30-0-rc2/REPORT.md), [lake-server-preparation-v4-30-0-rc2](../lake-server-preparation-v4-30-0-rc2/REPORT.md).

## Findings


**Scope.** This is a Nix-independent, synthetic Lake experiment for Anneal's current redesign, not a claim about the full Aeneas/Mathlib archive or verification correctness. I used [the current principles](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/PRINCIPLES.md) and [design contract](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/DESIGN.md), with `v1/` treated as historical. The checked-in archive test in `src/main.rs` motivates the relative manifest and `--old` commands; its archive behavior was not executed here. Lake success alone cannot satisfy Anneal's coverage, Rust-semantics, or TCB promises.

### Environment and limits

- Host: macOS arm64. Before writing scratch: `df -h .` showed **78 GiB available**. Scratch: `support/lake-probes` only; final measured file payload **2,277,167 bytes**, well below the 1 GiB cap. No Mathlib tree was copied. No Nix command or credential access was used.
- Tool discovery used `# Set PATH to the pinned local binaries identified above.` and pinned `ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0-rc2`; probe wrappers then invoked the resolved local binary by absolute path with the same toolchain environment. `lake --version`: `Lake version 5.0.0-src+3dc1a08 (Lean version 4.30.0-rc2)`. `lean --version`: `Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)`.
- Executed binaries: `$ELAN_HOME/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake` (SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`) and `lean` (SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`). These are the binaries behind the sourced `elan` shims.
- Every Lake invocation was sequential and wrapped by Python `subprocess.run(..., timeout=30)`; the largest observed wall time was 3.306 seconds. `LEAN_NUM_THREADS=1` and `LAKE_JOBS=1` were set. The latter has no matching Lake source reference in this checkout, so it is **not evidence of a global Lake concurrency control**. The fixture has one dependency module and one consumer module, with a serial import relation; Lake's printed “jobs” is total job count, not measured simultaneous workers. A stricter one-worker guarantee for a larger DAG needs a process-concurrency limiter or observation.

Exact per-run executable, arguments, working directory, selected environment, exit code, elapsed time, stdout, and stderr are in [`runs.json`](support/lake-probes/runs.json), produced by [`probe.py`](support/lake-probes/probe.py), [`probe2.py`](support/lake-probes/probe2.py), [`probe3.py`](support/lake-probes/probe3.py), and [`probe4.py`](support/lake-probes/probe4.py). In the command examples below, `lake` means that pinned binary. The initial consumer manifest SHA-256 is `4b5492c7d64718a5d310b0e588428b5de28293ebed2875792ec65b25b32f3897`; it has a relative `"dir": "../producer"` path entry.

### Fixture and observed matrix

The producer is a package `probe_dep` with `Dep.lean` defining `depValue : Nat := 7`. The generated consumer is `probe_consumer`, whose `Generated.lean` imports `Dep` and evaluates `depValue`. Its `lakefile.lean` says `require probe_dep from "../producer"`. `layout-a` builds producer and consumer, creating both Lake state trees and a relative consumer manifest. Relocation cells copy only this **small** producer. Read-only cells remove all write bits from copied producer files and directories; a tree hash before and after confirms no content mutation.

| Cell / exact Lake arguments | Observation |
|---|---|
| Producer: `--keep-toolchain --no-cache --old build Dep`; then consumer: `--keep-toolchain --no-cache --old build Generated` | Both exit 0; consumer prints `7`. Producer `Dep.olean` SHA-256 `cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b`. |
| Relocate built producer to `layout-b`, make it read-only, create consumer **without** manifest; `--keep-toolchain --no-cache --old build Generated` | Exit 1: permission denied creating `producer/.lake/config/probe_dep/lakefile.olean.lock`. `--no-build`, `setup-file Generated.lean`, and `lake env lean --json Generated.lean` fail at the same config load. Producer tree hash stays `feff44a7359080f18d0a64ebe9190a1311de0d587d8754171ba2540916df4e65`. |
| Prime that relocated producer alone while writable, then make it read-only; fresh consumer without manifest | Still fails on the same config lock. Priming only the producer does not resolve this consumer configuration path. |
| Prime a consumer while producer is writable, then freeze producer | That same consumer's `--no-build build Generated`, `setup-file Generated.lean`, and `env lean --json Generated.lean` exit 0. `setup-file` JSON points `importArts.Dep` at the relocated producer `Dep.olean`; Lean JSON reports value `7`. Producer tree hash is unchanged across those read-only calls (`46b046ceaf6a9423ec9d57e4e97ebd3234d0deb3a5964d4443222bd9b7894a4f`). A **second** fresh consumer without a manifest still fails on the lock. |
| Copy the relative consumer manifest before first use in a fresh relocated, read-only `layout-g`; `--keep-toolchain --no-cache --old --no-build build Dep`; then `--keep-toolchain --no-cache --old build Generated`; then `--keep-toolchain --no-cache setup-file Generated.lean` | All exit 0. `Dep` is up to date without rebuilding; consumer prints `7`; server setup resolves relocated `Dep.olean`. Producer tree hash is unchanged (`feff44a7359080f18d0a64ebe9190a1311de0d587d8754171ba2540916df4e65`). A second fresh consumer also succeeded after receiving this manifest. |
| On that preseeded consumer: `--keep-toolchain --offline --no-cache --old build Generated` | Exit 0. It replays generated work with no external package. This shows the local path fixture can run with `--offline` and `--no-cache`; it is **not proof of zero network attempts** or a fully disconnected Aeneas/Mathlib build. In this Lake source, the `offline` option is visibly passed to `init`/`new`, so its effect on `build` should not be assumed. |
| Fresh writable consumers with `LAKE_ARTIFACT_CACHE=true`, `LAKE_CACHE_DIR=<scratch>/cache-true`; and with `LAKE_ARTIFACT_CACHE=false`, `LAKE_CACHE_DIR=''` | Both build and print `7`. The true case created eight files under the specified cache (`artifacts/` and `outputs/`); the empty-dir case did not use that custom cache. Lake source defines an empty `LAKE_CACHE_DIR` as disabling the system cache, and the artifact-cache flag as controlling package artifact cache read/write defaults. These cells do not measure cache reuse after relocation. |
| Source-only producer copy (no `.lake`), `--no-build build Dep`; then normal `build Generated` | `--no-build` exits 3 because `Dep` is out of date; normal build exits 0 and rebuilds it. This distinguishes producer artifact state from consumer workspace state. |

**Initial clean/cache equivalence check.** The small consumer `Generated.olean` is byte-identical across the baseline, primed relocation, artifact-cache-true, empty-cache-dir, source-only rebuild, and preseeded relocation cells: SHA-256 `260bd52b339001cbd7fa23ad2a656976e007ddecc2f4c5596cb56ba031b4d0ec`. This is only a two-module pilot. It does not establish trace stability, full output equivalence, cache correctness for transitive packages, server data completeness, or proof equivalence for Aeneas/Mathlib. Do not copy the 6 GB Mathlib build tree to extend this matrix.

### Interpretation and next probe

**Observed:** A prebuilt, read-only producer can be consumed after relocation by a fresh generated workspace **when its relative path manifest is present before Lake loads the workspace**. Missing manifest takes a path that attempts to configure the producer and create a lock in its read-only `.lake/config` directory. `setup-file` shares that workspace-load dependency. A source-only producer cannot satisfy `--no-build`.

**Inferred:** The relative manifest prevents the lock-triggering reconfiguration in this fixture, while the existing producer OLean and traces remain usable. The successful second consumer with a copied manifest supports the manifest's role; it does not prove that all real archive metadata or trace paths are relocatable.

**Proposed compact follow-up:** Use the actual packaged Aeneas archive in place, without copying its Mathlib build tree. Create one tiny generated workspace under scratch; generate a relative manifest for all path dependencies; compare `--no-build` dependency checks, `--old build` of one generated module, `setup-file`, and `env lean --json` under read-only permissions. Record producer file hashes/mtimes and any writes. For a true disconnected claim, run under a network-denying harness. Keep one active process, 30 seconds per command, and stop if scratch growth approaches 1 GiB. A later, separately budgeted experiment can test a larger dependency DAG and enforce/measure simultaneous Lake workers.

**Setup/prompt tweak:** Make “preseed a relative `lake-manifest.json` before the first Lake invocation in each generated workspace” an explicit setup requirement, and ask future Lake probes to distinguish no-download-cache (`--no-cache`) from network-offline execution while checking editor `setup-file` alongside `build`.

## Boundaries

The fixture does not establish behavior of the full Aeneas/Mathlib archive or network isolation. `--no-cache` is not a network firewall, and the probe does not bound Lake worker concurrency for arbitrary DAGs.

## Evidence

This report's subject identities are recorded in `REPORT.json`. Source links in the Findings are pinned to immutable upstream or zerocopy revisions where available. Executed-probe support material is included under `support/lake-probes/`; local home/checkout prefixes are redacted in text artifacts.

## Revalidation

Use the retained tiny producer/consumer scripts. Seed relative `lake-manifest.json` before the first Lake command, compare read-only producer hashes before/after `build`, `setup-file`, and `env lean`, and test network-offline behavior under an explicit firewall separately.
