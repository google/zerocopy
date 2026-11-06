# Prepared Lake Consumer Contracts, Manifest Readiness, and Interactive Server Behavior

## Summary

At Lean and Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), ten component experiments characterize what a prepared Lake dependency tree and local artifact cache must provide for read-only consumption, batch verification (`lake env lean --json`), per-file module setup (`lake setup-file`), and interactive LSP goal queries (`lake serve` `$/lean/plainGoal`):

1. **Manifest-before-first-load requirement for read-only dependencies**: Consuming a prebuilt, write-denied (`sandbox-exec`) path dependency succeeded under `lake setup-file` and `lake env lean --json` only when the dependency already held compiled configuration state from a primer consumer and the fresh consumer workspace had a complete relative-path `lake-manifest.json` installed before its first Lake invocation. Omitting the consumer manifest caused both commands to fail (`exit 1`) with `operation not permitted` when Lake attempted to create `producer/.lake/config/probe_dep/lakefile.olean.lock`.
2. **Malformed or incomplete consumer manifests and `lake serve` fallback**: Replacing a consumer's `lake-manifest.json` with malformed JSON (`{\n`, hex `7b 0a`) caused `lake --no-build --no-cache setup-file` and `lake --no-build --no-cache env lean --json` to fail closed (`exit 1`, `invalid JSON: offset 2: unexpected end of input`). However, `lake --no-build --no-cache serve` logged `warning: package configuration has errors, falling back to plain 'lean --server'`, completed the LSP `initialize`/`shutdown` handshake, and exited 0. When a document was opened (`textDocument/didOpen`) under either malformed JSON or a parseable JSON manifest omitting the declared dependency (`packages: []`), `lake serve` never reached an empty processing-quiescent state and returned `null` for `$/lean/plainGoal`, whereas a valid pre-seeded manifest reached quiescence (`processing: []`) in ~6.08 seconds and returned `⊢ depValue = 7`.
3. **Source retention vs. metadata/artifact ablations in cache-seeded consumers**: One or two concurrent source-only consumers fetching from a seeded eight-file artifact cache under `--no-build` matched a clean build on `.olean`, `.ilean`, and `.c` SHA-256 digests, batch theorem/axiom output, and live `$/lean/plainGoal` (`⊢ depValue + 1 = 8`). Deleting `Dep.lean` from a prepared producer while keeping `Dep.olean` split the oracles: `lake --no-build` failed (`exit 1`, missing source), direct `lake env lean --json` still succeeded (`exit 0`) using the retained `.olean`, and `lake serve` published setup diagnostics and returned `null` for `$/lean/plainGoal`. Removing saved `.trace` files, `.hash` sidecars, or `.lake/config` allowed `--no-build` to succeed by recreating those files in the writable producer copy, whereas `Dep.setup.json` remained absent without error.
4. **Operation-specific artifact families, selective pruning, and staging renames**: Selective deletion of `Extra.olean`, `Macro.olean`, and a native plugin `.dylib` (saving 102,240 of 174,866 build bytes) left base batch proofs passing, caused batch imports of `Extra`/`Macro` and `--no-build` checks to fail, and allowed an ordinary writable `lake serve` session to rebuild `Extra.olean` on demand from retained source for an unsaved scratch document. Building at a staging pathname and renaming to a final pathname left seven staging-path strings in `Dep.trace` while all nine non-trace `.lake` files matched a direct final-path build and passed `setup-file`, `lake serve`, batch Lean, and `--no-build`. Finally, substituting a valid wrong-generation `.olean` (`depValue = 9`) under the cache filename for `depValue = 7` passed `lake --no-build build` and `setup-file` (`exit 0`) but failed downstream theorem verification (`exit 1`).

## Applicability

All experiments executed Lean and Lake `v4.30.0-rc2` (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, reporting `Lake version 5.0.0-src+3dc1a08`) on macOS arm64 (`macOS 26.6.2`, APFS, 8 GiB physical RAM) with pinned binary digests:

- `lean` SHA-256: `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`
- `lake` SHA-256: `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`

Fixtures consist of local two-package workspaces (`probe_dep` defining `depValue : Nat := 7` in `Dep.lean` and `probe_consumer` importing `Dep` in `Generated.lean` or `Proof.lean`) with no remote Git or registry dependencies, executed under `LEAN_NUM_THREADS=1`, isolated `HOME`/`XDG_CACHE_HOME`, bounded timeouts (25–35 seconds per command), and macOS `/usr/bin/sandbox-exec` network/write-denial profiles where noted. These probes characterize Lake `v4.30.0-rc2` component contracts; an availability inventory (`support/real-archive-manifest-gate/availability.json`) confirmed that only unbuilt Nix derivations (`anneal-toolchain-omnibus*.drv`) and a separate 61 MB Aeneas release archive (`aeneas-macos-aarch64.tar.gz`) were present locally, so full Mathlib/Aeneas omnibus archives were not executed.

## Findings

### Final-Path Build vs. Staging-Path Build and Atomic Rename

Building a four-source project (`Dep.lean` defining `selected : Nat := 7`, `Proof.lean` proving `selected = 7` by `rfl`) directly at `final` versus building at `stage` and renaming to `final` under `sandbox-exec -p '(version 1)(allow default)(deny network*)'` with `--keep-toolchain --no-cache` produced identical operational verdicts despite stale path strings in `Dep.trace`:

| Observation | Built at Final Path | Built at Stage, Renamed to Final |
| --- | --- | --- |
| `lake build Dep` | Exit 0; 3 jobs (despite `LAKE_JOBS=1`) | Exit 0; 3 jobs (despite `LAKE_JOBS=1`) |
| `lake setup-file Proof.lean` | Exit 0; import artifact at `final/.lake/build/lib/lean/Dep.olean` | Exit 0; import artifact at `final/.lake/build/lib/lean/Dep.olean` |
| Fresh `lake serve` goal at `rfl` | `no goals` | `no goals` |
| LSP diagnostics | `7`; `checked` has no axioms | `7`; `checked` has no axioms |
| Fresh `lake env lean --json Proof.lean` | Exit 0; `7`, no axioms | Exit 0; `7`, no axioms |
| `lake --no-build build Dep` | Exit 0; all targets up to date | Exit 0; all targets up to date |
| Location-bearing `.lake` file | `Dep.trace`: 7 `final`-path occurrences | `Dep.trace`: 7 `stage`-path occurrences retained at `final` |
| `.lake` inventory (10 files) | 9 non-trace files byte-identical to moved build | `Dep.trace` alone differed; no rewrite during setup/server/no-build |

Basis: **execution** (`support/final-versus-moved-lake/probe.py`, `support/final-versus-moved-lake/results.json`).

### Configuration Formats, Native Facets, and Wrong-Generation Cache Substitution

Across 26 sequential commands in `support/lake-prepared-contract/probe.py` (with `sandbox-exec` network denial verified by a Python loopback-connect control failing with `Operation not permitted`):

1. **Lean vs. TOML configuration**: Clean `lakefile.lean` and `lakefile.toml` producers built byte-identical `Dep.olean` (`cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b`), `.ilean`, and `.c` outputs and passed consumer batch verification (`8`, no axioms for `generatedEq`). Only the Lean configuration compiled `.lake/config/probe_dep/lakefile.olean` and its trace, and `Dep.trace` hashes differed between the two formats.
2. **Relocated read-only producer vs. non-writable consumer**: Relocating the prepared tree to `different/depth/prepared`, removing the old path, and freezing the producer allowed `--no-build build Dep`, `--no-build setup-file Generated.lean`, and `lake env lean --json` to exit 0 with zero inventory changes. Removing `consumer/.lake` and making the consumer directory non-writable caused `lake build Generated` to exit 1 (`permission denied` on `consumer/.lake`).
3. **Native shared-library facet (`+Dep:dynlib`)**: Building `+Dep:dynlib` produced `probe__dep_Dep.dylib` (50,464 bytes, SHA-256 `f33e23d9227a6fc0205ca052a6a35e038d6596b79aa609d14b87b2b703b259b4`). Explicit `lake env lean --load-dynlib` exited 0 (and exited 1 with a `dlopen` error when given invalid dylib bytes). Deleting the `.dylib` made `--no-build build +Dep:dynlib` exit 3 (out of date), while ordinary batch checking of `Generated.lean` still exited 0.
4. **Valid wrong-generation `.olean` substitution**: Replacing the cached `.olean` named by the `depValue = 7` output map (`4ab07c203eb6f06e.olean`) with the valid `.olean` from a `depValue = 9` build (SHA-256 `fe893ce3c24d2c295ade06017eb859638f0e75aa29df7e9444f3026bfd7a7745`) left `lake --no-build build Dep` (`Fetched Dep`) and `--no-build setup-file Generated.lean` successful (`exit 0`). Direct Lean checking of the value-7 proof against that object exited 1 (`decide` reported `depValue + 1 = 8` false and `#eval` printed `10`), whereas truncating the output-map JSON to `{"data":` caused both `--no-build` commands to exit 3 (`invalid JSON`).

Basis: **execution + derived** (`support/lake-prepared-contract/probe.py`, `support/lake-prepared-contract/results.json`).

### Selective Artifact Pruning vs. Interactive `lake serve` Extension

In `support/pruned-lake-interactive-extension-v4-30-0-rc2/probe.py`, a producer built `Base` (`selected : Nat := 7`), `Extra` (`extra := selected + 1`), `Macro` (`new_tac` expanding to `decide`), and `Plugin` (`+Plugin:dynlib`, native initializer writing `plugin-loaded`), totaling 39 build files (174,866 bytes). Deleting `Extra.olean` (5,776 bytes), `Macro.olean` (45,344 bytes), and the plugin `.dylib` (51,120 bytes) removed 102,240 bytes (leaving 36 files / 72,626 bytes) while retaining source, `.ilean`, `.c`, traces, and `Base.olean`:

| Operation | Fully Prepared | After Selective Pruning | Observation |
| --- | --- | --- | --- |
| Fresh batch proof importing `Base` | Exit 0 | Exit 0 | Retained base `.olean` remained importable. |
| Fresh batch proof using built-in `decide` | Exit 0 | Exit 0 | Built-in tactic used retained core and `Base.olean`. |
| Fresh batch proof importing `Extra` | Exit 0 | Exit 1 (`unknown module prefix 'Extra'`) | Retained source alone did not satisfy batch import without building. |
| Fresh batch proof importing `Macro` and using `new_tac` | Exit 0 | Exit 1 (`unknown module prefix 'Macro'`) | Macro module was unavailable without `Macro.olean`. |
| Explicit `--plugin=<dylib>` load | Exit 0 (marker `plugin-loaded`) | Exit 1 (missing file; no marker) | Native plugin dylib is required when explicitly loaded. |
| `lake --no-build build Extra` / `Macro` | Not needed | Exit 3 (target out of date) | Read-only `--no-build` consumer cannot rebuild pruned modules. |
| Unsaved `lake serve` scratch document importing `Base` | Not separately run | Goal `⊢ selected = 7` | Retained base module remained queryable interactively. |
| Unsaved `lake serve` scratch document importing `Extra` | Not separately run | `Extra.olean` rebuilt (`Built Extra`); goal `⊢ extra = 8` | Writable `lake serve` crossed the pruning boundary by compiling `Extra` from retained source. |

Basis: **execution** (`support/pruned-lake-interactive-extension-v4-30-0-rc2/results.json`).

### Read-Only Producer Manifest Gate, Malformed Manifests, and `lake serve` Quiescence

When a producer (16 regular files, `Dep.olean` SHA-256 `cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b`) was primed with a writable consumer to materialize `.lake/config` and then protected by `sandbox-exec` denying `file-write*` below the producer and `network*` (`support/real-archive-manifest-gate/results.json`):

| Consumer Operation | Exit | Observation |
| --- | ---: | --- |
| Prepare producer and primer consumer | 0, 0 | `Dep.olean` and producer configuration state materialized before read-only consumption. |
| Fresh consumer, complete relative-path manifest, sandboxed `setup-file` | 0 | `importArts.Dep` resolved to the prepared producer `.olean`. |
| Same consumer, sandboxed `lake env lean --json` | 0 | Batch proof `firstGoal` reported no axioms; producer inventory unchanged. |
| Fresh consumer, **no** manifest, sandboxed `setup-file` and batch | 1, 1 | Both attempted to create `producer/.lake/config/probe_dep/lakefile.olean.lock` and failed with `operation not permitted`. |
| Rename producer out of required path; complete-manifest `setup-file` | 1 | Failed explicitly with `probe_dep: package directory not found`. |

After an initial preflight refusal at 25.09% free memory (`support/lake-malformed-manifest-preflight-refusal/preflight.json`, 131,533 reclaimable 16,384-byte pages = 2,155,036,672 of 8,589,934,592 bytes, below the 30% gate), the executed malformed-manifest preflight suite (`support/malformed-manifest-preflight/results.json`, admitted at 30.322% reclaimable RAM, peak summed RSS 1,037,536 KiB) tested replacing the valid consumer `lake-manifest.json` (SHA-256 `4cf0c1b12e990e08af5075710832c08e1df761220ab141edb2da7211cb2fd230`) with the two bytes `{` + LF (hex `7b 0a`, SHA-256 `a6fb08fda1acb957b6116bd37811a1fe41a01611c0631edbf786d6889a27a55c`) under `--no-build --no-cache`:

| Consumer Manifest | `lake setup-file` | `lake env lean --json` | `lake serve` Initialize / Shutdown |
| --- | --- | --- | --- |
| Valid | exit 0; `Dep.olean` in `importArts` | exit 0; `#eval` reports `7` | responses to initialize and shutdown; exit 0; empty stderr |
| Malformed (`7b 0a`) | exit 1; `invalid JSON: offset 2: unexpected end of input` | exit 1; same error | responses to initialize and shutdown; exit 0; stderr reports manifest error and fallback to plain `lean --server` |
| Exact valid bytes restored | exit 0; `Dep.olean` in `importArts` | exit 0; `#eval` reports `7` | responses to initialize and shutdown; exit 0; empty stderr |

A separate direct `lean --json Generated.lean` invocation with explicit `LEAN_PATH` pointing to the producer `.olean` directory exited 0 and evaluated `7` while the consumer manifest remained malformed.

Opening `Generated.lean` (71 bytes, version 1) and requesting `$/lean/plainGoal` at line 1 character 40 over the 36-file pre-seeded worktree (`support/preseeded-valid-server-goal/results.json`, where the valid run exited 0 in 9.5118 s with 41 server frames and max 949,024 KiB RSS before the second cell was refused at 29.8279% RAM, and `support/preseeded-manifest-server-readiness/results.json`, where all three cells completed) established that `lake serve` initialize/exit 0 does not imply document readiness:

| Manifest State | Fresh RAM Admission | Opened-Document Behavior (`lake --no-build --no-cache serve`) | Goal Response After Wait | Server Exit |
| --- | ---: | --- | --- | ---: |
| Valid dependency | 31.16% | Information diagnostic `7`; final `processing: []`; quiescence recorded after 6.0899 s (38 frames) | `⊢ depValue = 7` | 0 |
| Malformed JSON (`7b 0a`) | 31.04% | Invalid JSON at offset 2, workspace configuration failure, `lake setup-file` diagnostic, fallback to plain `lean --server`; no final empty processing state (`readiness_quiescent: false`, 25 frames) | `null` after 8.0261 s diagnostic wait | 0 |
| Parseable manifest without dependency (`packages: []`) | 31.38% | `missing manifest; use lake update`, workspace configuration failure, `lake setup-file` diagnostic, fallback to plain `lean --server`; `readiness_quiescent: false` (25 frames) | `null` after 8.0315 s diagnostic wait | 0 |

Basis: **execution** (`support/real-archive-manifest-gate/results.json`, `support/malformed-manifest-preflight/results.json`, `support/preseeded-valid-server-goal/results.json`, `support/preseeded-manifest-server-readiness/results.json`).

### Fresh Cache-Seeded Consumers, Producer State Ablations, and Concurrent Goal Queries

In `support/lake-fresh-cache-consumer-matrix/results.json`, a clean build (`lake -v build Generated`) and a fresh consumer fetching from an eight-file artifact cache (`lake -v --no-build build Generated`, logging `Fetched Dep` and `Fetched Generated` and materializing seven producer build files) produced identical SHA-256 digests for `Dep.olean` (`cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b`), `Dep.ilean` (`ee34578f6077d4f2019dca615b30d0de14340a9d0d36cdb2870f3285adeb00e5`), and `Dep.c` (`36383e740367044dc594c872922b0c37356a7c73a35f72ff5cdc252e829e052e`), identical batch evaluation (`8`, no axioms for `generatedEq`), and identical live `$/lean/plainGoal` (`⊢ depValue + 1 = 8`). Ablating individual producer files in separate writable producer copies before running a fresh consumer yielded:

| Producer Removal Before Fresh Consumer | `--no-build` Lake Action | Direct Batch / Live `$/lean/plainGoal` | Producer Net-Byte Result |
| --- | --- | --- | --- |
| `Dep.lean` (`no_source`) | Exit 1 (`no such file or directory` at `producer/Dep.lean`, bad `Dep` import) | Batch exit 0 (`8`, no axioms); live goal `null` (missing-source setup diagnostics) | No remaining file changed |
| Both saved `.trace` files (including config trace) | Exit 0 (`Fetched Dep`, `Fetched Generated`) | Batch exit 0; goal `⊢ depValue + 1 = 8` | Two `.trace` files recreated |
| Three `.hash` sidecars | Exit 0 (`Replayed Dep`, `Fetched Generated`) | Batch exit 0; goal `⊢ depValue + 1 = 8` | Three `.hash` sidecars recreated |
| `Dep.setup.json` (`no_setup`) | Exit 0 (`Replayed Dep`, `Fetched Generated`) | Batch exit 0; goal `⊢ depValue + 1 = 8` | `Dep.setup.json` remained absent |
| Compiled producer `.lake/config` | Exit 0 (`Replayed Dep`, `Fetched Generated`) | Batch exit 0; goal `⊢ depValue + 1 = 8` | Config `.olean` and `.trace` recreated |

When two independent source-only consumer roots (7 initial files each) concurrently ran `lake -v --no-build build Generated` against a read-only (`0444` files, `0555` directories) seeded artifact cache under a `sandbox-exec` profile denying network and cache writes (`support/two-concurrent-fresh-cache-goal-consumers/results.json`, admitted at 24.57% free memory, runtime low 19.92%, peak summed descendant RSS 2,789,392 KiB across at most 8 processes):

| Control | Consumer A | Consumer B |
| --- | --- | --- |
| Fresh `--no-build` Lake action | Exit 0; `Fetched Dep`, `Fetched Generated` | Exit 0; `Fetched Dep`, `Fetched Generated` |
| Fetched `.olean` digests | `Dep.olean` `cebebbbc...`; `Generated.olean` `e807370f82380c588dad12a60d8e2475ac82fc5232cffbbf68a8b1a7dbef9401` | Identical SHA-256 digests |
| Direct `lake --no-cache env lean --json Generated.lean` | Exit 0; goal trace, no-axioms result, value `8` | Exit 0; byte-identical batch JSON output |
| Concurrent `lake --no-cache serve` `$/lean/plainGoal` | Exit 0; `⊢ depValue + 1 = 8` | Exit 0; `⊢ depValue + 1 = 8` |
| Shared cache and original seed tree | Unchanged file/hash/mtime inventories across both consumers | Unchanged file/hash/mtime inventories |

Basis: **execution** (`support/lake-fresh-cache-consumer-matrix/results.json`, `support/two-concurrent-fresh-cache-goal-consumers/results.json`).

## Boundaries

- **Real Mathlib/Aeneas omnibus archive consumption (`not examined`)**: Because no prebuilt immutable omnibus archive existed in the inspected local workspace or `/nix/store` (`support/real-archive-manifest-gate/availability.json`), all ten subprobes executed against synthetic two-package local fixtures. Behavior across full Mathlib/Aeneas dependency closures, external Git/registry packages, and multi-package native plugin chains was **not examined**.
- **`lake serve` initialize handshake and batch import as interactive readiness oracles (`known not to apply`)**: Neither an LSP `initialize`/`shutdown` exit 0 nor a direct `lake env lean --json` exit 0 establishes that `lake serve` has a valid package configuration or can serve interactive goals (`$/lean/plainGoal` returned `null` under malformed/missing manifests and under missing `Dep.lean` source despite direct batch import succeeding).
- **Seeded artifact cache as a complete read-only dependency archive (`known not to apply`)**: Removing producer `.trace`, `.hash`, or `.lake/config` files caused `--no-build` consumers to recreate those files inside the producer tree; a read-only dependency tree therefore requires pre-materialized producer configuration, traces, and retained `.lean` sources in addition to compiled artifacts.
- **Unbounded server wait after fallback (`unknown`)**: In the malformed and missing-dependency manifest server runs (`support/preseeded-manifest-server-readiness/results.json`), `$/lean/plainGoal` returned `null` after an 8-second wait while `processing` remained non-empty (`kind: 2`). Whether a plain `lean --server` fallback could ever resolve imports under an alternative environment or unbounded wait is **unknown**, though it failed the quiescent readiness contract.

## Evidence

### Final-Path vs. Staging Rename (`support/final-versus-moved-lake/`)
- Scripts and transcript: [`support/final-versus-moved-lake/probe.py`](support/final-versus-moved-lake/probe.py) (SHA-256 `9db4cc17e93ea169d893c20cd04fec63b8e3e45cee471fead2a49fb7cb553d78`), [`support/final-versus-moved-lake/results.json`](support/final-versus-moved-lake/results.json) (SHA-256 `a51334657934e866f35d635a0076d18f2a760127a045c49fb9dbe6d8b02b41f8`), and [`support/final-versus-moved-lake/check.py`](support/final-versus-moved-lake/check.py).

### Prepared Contract and Selective Pruning (`support/lake-prepared-contract/` and `support/pruned-lake-interactive-extension-v4-30-0-rc2/`)
- Prepared contract driver, results, and specimens: [`support/lake-prepared-contract/probe.py`](support/lake-prepared-contract/probe.py) (SHA-256 `49164a0ff66b0feb871c774242b1d5d89c517512a847340992ab806495b81f19`), [`support/lake-prepared-contract/results.json`](support/lake-prepared-contract/results.json) (SHA-256 `0c35667195c8c77f4ae27e6383e24b3a9ada68e0b545224f1eabe581b2cecacd`), and [`support/lake-prepared-contract/artifacts/`](support/lake-prepared-contract/artifacts/).
- Pruned interactive extension driver, checker, and worktree: [`support/pruned-lake-interactive-extension-v4-30-0-rc2/probe.py`](support/pruned-lake-interactive-extension-v4-30-0-rc2/probe.py) (SHA-256 `f7773f0e56164bfa2029aae5f78146b6537bd24fd266669a510ecc854902f036`), [`support/pruned-lake-interactive-extension-v4-30-0-rc2/results.json`](support/pruned-lake-interactive-extension-v4-30-0-rc2/results.json) (SHA-256 `4b106162cb62afcbb4d9385a1f9db70ecb4fbd5f29c74abb2acb68ec969205a1`), [`support/pruned-lake-interactive-extension-v4-30-0-rc2/check.py`](support/pruned-lake-interactive-extension-v4-30-0-rc2/check.py), and [`support/pruned-lake-interactive-extension-v4-30-0-rc2/work/`](support/pruned-lake-interactive-extension-v4-30-0-rc2/work/).

### Manifest Gate, Malformed Manifests, and Server Readiness (`support/real-archive-manifest-gate/`, `support/lake-malformed-manifest-preflight-refusal/`, `support/malformed-manifest-preflight/`, `support/preseeded-valid-server-goal/`, `support/preseeded-manifest-server-readiness/`)
- Archive availability and sandboxed manifest gate: [`support/real-archive-manifest-gate/availability.json`](support/real-archive-manifest-gate/availability.json), [`support/real-archive-manifest-gate/probe.py`](support/real-archive-manifest-gate/probe.py) (SHA-256 `d1fc309aeeb98bf146cc5e2d078b2ae193c6fb4159f0b58c9dfe14c1c75414dd`), [`support/real-archive-manifest-gate/results.json`](support/real-archive-manifest-gate/results.json) (SHA-256 `c52a4491a6a5c588a7aaa55342f586573132bc453c920e01cd0c85ad7baa2fee`), and [`support/real-archive-manifest-gate/check.py`](support/real-archive-manifest-gate/check.py).
- Malformed manifest preflight refusal and executed batch/initialize suite: [`support/lake-malformed-manifest-preflight-refusal/preflight.json`](support/lake-malformed-manifest-preflight-refusal/preflight.json), [`support/lake-malformed-manifest-preflight-refusal/check.py`](support/lake-malformed-manifest-preflight-refusal/check.py), [`support/malformed-manifest-preflight/probe.py`](support/malformed-manifest-preflight/probe.py), [`support/malformed-manifest-preflight/results.json`](support/malformed-manifest-preflight/results.json), [`support/malformed-manifest-preflight/fixtures/malformed-lake-manifest.json`](support/malformed-manifest-preflight/fixtures/malformed-lake-manifest.json), [`support/malformed-manifest-preflight/raw/`](support/malformed-manifest-preflight/raw/), [`support/malformed-manifest-preflight/preliminary/`](support/malformed-manifest-preflight/preliminary/), [`support/malformed-manifest-preflight/work/`](support/malformed-manifest-preflight/work/), and [`support/malformed-manifest-preflight/check.py`](support/malformed-manifest-preflight/check.py).
- Pre-seeded live server goal and readiness suites: [`support/preseeded-valid-server-goal/probe.py`](support/preseeded-valid-server-goal/probe.py), [`support/preseeded-valid-server-goal/results.json`](support/preseeded-valid-server-goal/results.json), [`support/preseeded-valid-server-goal/preseed.json`](support/preseeded-valid-server-goal/preseed.json), [`support/preseeded-valid-server-goal/raw/`](support/preseeded-valid-server-goal/raw/), [`support/preseeded-valid-server-goal/fixtures/`](support/preseeded-valid-server-goal/fixtures/), [`support/preseeded-valid-server-goal/work/`](support/preseeded-valid-server-goal/work/), [`support/preseeded-valid-server-goal/check.py`](support/preseeded-valid-server-goal/check.py), [`support/preseeded-manifest-server-readiness/probe.py`](support/preseeded-manifest-server-readiness/probe.py), [`support/preseeded-manifest-server-readiness/results.json`](support/preseeded-manifest-server-readiness/results.json), [`support/preseeded-manifest-server-readiness/preseed.json`](support/preseeded-manifest-server-readiness/preseed.json), [`support/preseeded-manifest-server-readiness/raw/`](support/preseeded-manifest-server-readiness/raw/), [`support/preseeded-manifest-server-readiness/fixtures/`](support/preseeded-manifest-server-readiness/fixtures/), [`support/preseeded-manifest-server-readiness/work/`](support/preseeded-manifest-server-readiness/work/), and [`support/preseeded-manifest-server-readiness/check.py`](support/preseeded-manifest-server-readiness/check.py).

### Fresh Cache Consumer Matrix and Concurrent Goal Consumers (`support/lake-fresh-cache-consumer-matrix/` and `support/two-concurrent-fresh-cache-goal-consumers/`)
- Sequential ablation matrix: [`support/lake-fresh-cache-consumer-matrix/probe.py`](support/lake-fresh-cache-consumer-matrix/probe.py) (SHA-256 `0b5dc8abace2ac483cf64f7cf783ce3bc878eabcf7b142c8d2c8b4e6b9e5d491`), [`support/lake-fresh-cache-consumer-matrix/results.json`](support/lake-fresh-cache-consumer-matrix/results.json) (SHA-256 `2b566c7e04e1cf94a270e64b35a3ddc17f3b49ca1c768a87beaf63d97dfda23e`), and [`support/lake-fresh-cache-consumer-matrix/check.py`](support/lake-fresh-cache-consumer-matrix/check.py).
- Concurrent cache-fetch and goal consumers: [`support/two-concurrent-fresh-cache-goal-consumers/probe.py`](support/two-concurrent-fresh-cache-goal-consumers/probe.py), [`support/two-concurrent-fresh-cache-goal-consumers/results.json`](support/two-concurrent-fresh-cache-goal-consumers/results.json), [`support/two-concurrent-fresh-cache-goal-consumers/rejected-wrapper-results.json`](support/two-concurrent-fresh-cache-goal-consumers/rejected-wrapper-results.json), and [`support/two-concurrent-fresh-cache-goal-consumers/check.py`](support/two-concurrent-fresh-cache-goal-consumers/check.py).

## Revalidation

All nine offline verification scripts validate the preserved results, JSON-RPC transcripts, SHA-256 inventories, and resource-gate records without launching Lake or Lean:

```console
python3 support/final-versus-moved-lake/check.py
python3 support/pruned-lake-interactive-extension-v4-30-0-rc2/check.py
python3 support/real-archive-manifest-gate/check.py
python3 support/lake-malformed-manifest-preflight-refusal/check.py
python3 -B support/malformed-manifest-preflight/check.py
python3 -B support/preseeded-valid-server-goal/check.py
python3 -B support/preseeded-manifest-server-readiness/check.py
python3 support/lake-fresh-cache-consumer-matrix/check.py
python3 -B support/two-concurrent-fresh-cache-goal-consumers/check.py
```

To re-run the active probes on a host with the pinned `v4.30.0-rc2` toolchain (or to test a newer Lean/Lake candidate for manifest-ownership and server-fallback differences), execute the `probe.py` scripts in fresh private scratch directories and compare `setup-file` lock behavior, `lake serve` `processing` quiescence, and `$/lean/plainGoal` outputs.
