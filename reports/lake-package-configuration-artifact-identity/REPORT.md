# Lake Package Configuration Identity, Artifact Families, and Build-Action Observability

## Summary

Across nine component execution suites at Lean and Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, with `v4.29.0` at `98dc76e3c0a9b856c9b98726b713fb04fab16740` sharing the same pre-4.31 dependency-owned configuration directory layout), Lake separates workspace-relative package configuration state (`producer/.lake/config/<assigned-name>/lakefile.olean` and `.trace`) from compiled module artifacts (`Dep.olean`, `Dep.ilean`, `Dep.c`, `Dep.setup.json`, and `Dep.trace`):

1. **Dependency-owned configuration collisions by assigned name, index, and package version**: Two consumers pointing to the same physical dependency tree rewrote `producer/.lake/config/probe_dep/lakefile.olean` and its trace whenever the producer's resolved workspace index shifted (`idx = 1 -> 2 -> 1`), even while module builds logged `Replayed Dep`. When the producer was frozen read-only after an `idx = 1` prime, a matching (`idx = 1`) consumer succeeded without writes, whereas a shifted (`idx = 2`) consumer failed (`exit 1`, permission denied on `.lake/config/probe_dep/lakefile.olean.lock`). Assigning a different dependency alias (`dep_alias`) created a separate configuration slot (`.lake/config/dep_alias/`) with the same `configHash` (`ba08543c33d179c7`). Editing only `version := v!"1.0.0"` to `v!"2.0.0"` in `lakefile.lean` recompiled `lakefile.olean` and changed `configHash` (`a5b4b476a0591aca -> b74db869a8cb920f`) while replaying `Dep.olean` unchanged.
2. **Executable `lakefile.lean` (`run_cmd`) side effects, hidden environment inputs, and sandboxing**: During configuration elaboration (`LoadConfig`), a `lakefile.lean` containing `run_cmd` executes arbitrary IO before target building begins, writing outside-workspace files unless blocked by an OS sandbox (`sandbox-exec` denying outside writes caused `lake build` to fail with `exit 1`, `operation not permitted`, whereas static declarative `lakefile.lean`/`lakefile.toml` configurations succeeded). Furthermore, Lake does not track arbitrary `IO.getEnv` reads inside `run_cmd`: changing an environment variable (`PROBE_CONFIG_VALUE` from `A` to `B`) on an already built dynamic root did not re-run `run_cmd`, leaving `--no-build`, `setup-file`, batch Lean, and direct servers observing the stale `depValue = 7` artifact.
3. **Cache keys, cross-generation local artifact mixing, and operation-specific requirements**: `LAKE_CACHE_DIR` selects cache location (empty string resolves to `.lake/cache`) independently of `LAKE_ARTIFACT_CACHE` (`true` vs. `false`). Changing producer source bytes or `leanOptions` (`pp.unicode.fun`) generated new producer output-map keys in the cache, whereas changing the root directory path or consumer package name did not. Deleting `.olean`, `.ilean`, `.trace`, or `.c` caused `--no-build build` and `--no-build setup-file` to exit 3, while `lake env lean --json` required only `Dep.olean` (and neither needed `Dep.setup.json`). Overwriting a local baseline file with a valid wrong-generation `.olean`, `.ilean`, `.c`, or `Dep.setup.json` left `--no-build build` and `--no-build setup-file` exiting 0 (returning the cached baseline `.olean`), while local-path batch and server imports failed only on the wrong-generation `.olean`.
4. **Build-action observability, unprivileged libc event tracing, and generated provenance sensitivity**: Verbose (`-v`) `Replayed Dep` output reprints historical compiler command lines from the saved trace without spawning a new `lean` child process, while `--rehash --no-build` after a same-mtime source edit exits 3 and writes `Dep.trace.nobuild`. An unprivileged `DYLD_INSERT_LIBRARIES` libc interposition observer confirmed 2 PIDs and a temporary-to-final `Dep.olean.tmp.<PID> -> Dep.olean` rename on cold/changed builds (40–41 events) versus 1 PID and an 88-byte `read` of `lakefile.olean` on unchanged replays (11 events). On a 1,686-job Aeneas-generated Lake graph, no-write and mtime-only touches replayed all four local modules in 3.67–5.63 s with zero build-file hash changes, whereas a provenance doc-comment change in `Source/Funs.lean` rebuilt `Source.Funs`, `Source`, and `Consumer` (28.15 s), changing `Source/Funs.olean` and downstream `.trace` files while leaving `.ilean` and `.c` bytes unchanged.

## Applicability

The `REPORT.json` subjects identify two cached upstream Lean 4 and Lake releases on macOS arm64 (`Darwin 24.6.0` / `25.6.0` / macOS `26.6.2`, APFS, 8 GiB physical RAM):

- **Lean 4 and Lake `v4.29.0`** (`leanprover/lean4` revision `98dc76e3c0a9b856c9b98726b713fb04fab16740`): `lean` SHA-256 `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`, `lake` SHA-256 `0e56506385ec20d56bffd7c031c4d48573ab5fdb74e5246ec8c45a220bebc68b`.
- **Lean 4 and Lake `v4.30.0-rc2`** (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, reporting `Lake version 5.0.0-src+3dc1a08`): `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`.

**Shared behavior vs. version scope**: Both `v4.29.0` and `v4.30.0-rc2` were present in the local toolchain inventory and share the pre-`v4.31.0` Lake package-configuration placement model (`src/lake/Lake/Load/Config.lean`, `src/lake/Lake/Load/Lean/Elab.lean`, `src/lake/Lake/Config/Package.lean`), in which compiled dependency configuration state (`lakefile.olean`, `lakefile.olean.trace`, and `lakefile.olean.lock`) is written under the dependency's own `.lake/config/<assigned-name>/` directory and keyed by workspace package index (`idx`). All nine active execution suites in this package ran against the `v4.30.0-rc2` binary pair under `LEAN_NUM_THREADS=1`, offline environment controls (`LAKE_NO_NET=1`, `--keep-toolchain`), and isolated scratch workspaces. Behavior on `v4.31.0` and later releases (where Lake relocated package configuration ownership) is outside the execution scope of this package and is covered in the cross-version shared-tree writer report.

## Findings

### Consumer Graph Identity, Frozen Index Collisions, and Duplicate Package Resolution

In `support/lake-consumer-identity-observability/results.json`, varying how consumers reference the same physical `producer` directory (`probe_dep`, `Dep.lean` defining `depValue := 7`) mutated dependency-owned files under `producer/.lake/config/` even when `Dep` itself was replayed:

| Consumer Graph Change | Producer Configuration Observation (`producer/.lake/config/`) | `Dep` Module Action |
| --- | --- | --- |
| Initial `probe_dep` dependency | `.lake/config/probe_dep/lakefile.olean.trace` has `name=probe_dep`, `idx=1`, `configHash=ba08543c33d179c7` | `Built Dep` |
| Same physical tree assigned alias `dep_alias` | New `.lake/config/dep_alias/lakefile.olean` and trace created with `name=dep_alias`, `idx=1`, `configHash=ba08543c33d179c7` | `Replayed Dep` |
| `probe_dep` follows `dummy` in resolved graph | Existing `probe_dep` `lakefile.olean` and trace rewritten; trace records `idx=2` (`configHash` unchanged) | `Replayed Dep` |
| Root moved one directory deeper (two-level parent relative path to `producer`), `probe_dep` first again | Existing `probe_dep` `lakefile.olean` and trace rewritten; trace returns to `idx=1` | `Replayed Dep` |

Freezing the producer directory after priming it at `idx = 1` (`support/lake-frozen-index-collision/results.json`) proved that an index shift requires write access to the dependency's configuration directory at `v4.30.0-rc2`:

| Step | Exit | Producer Config Trace | Producer Inventory |
| --- | ---: | --- | --- |
| Prime writable producer for index 1 | `0` (`Built Dep`) | `idx=1` | Baseline after freezing |
| Matching consumer (`idx=1`), producer frozen | `0` (`Replayed Dep`, `#eval` `7`) | `idx=1` | Byte, size, and mode identical |
| Shifted consumer (`idx=2`), producer frozen | `1` (permission denied on `.lake/config/probe_dep/lakefile.olean.lock`) | Still `idx=1` | Byte, size, and mode identical |
| Same shifted consumer (`idx=2`), producer writable | `0` (`Replayed Dep`, `#eval` `7`) | `idx=2` | Configuration `.olean` and `.trace` bytes changed |

When two physical producers declared the same package name `probe_dep` (Producer A: version `1.0.0`, `depValue := 7`; Producer B: version `2.0.0`, `depValue := 9`):

| Duplicate-Source Graph Shape | Outcome | Artifact and Config Observation |
| --- | --- | --- |
| Root directly requires A then B as `probe_dep` | Exit 1 (`` `probe_dep` has already been declared ``) | Neither producer acquires a config or module artifact |
| Root directly requires B then A as `probe_dep` | Exit 1 (same error) | Neither producer acquires a config or module artifact |
| Root requires `wrapper_a` then `wrapper_b`; root manifest maps `probe_dep` to A | Exit 0 (`#eval depValue` prints `7`) | Producer A acquires config and `Dep.olean`; B remains untouched |
| Root requires `wrapper_b` then `wrapper_a`; root manifest still maps `probe_dep` to A | Exit 0 (`#eval depValue` prints `7`) | B remains untouched; wrapper config slots rewritten for new root |
| Root requires `wrapper_a` then `wrapper_b`; root manifest maps `probe_dep` to B | Exit 0 (`#eval depValue` prints `9`) | Producer B acquires config and `Dep.olean` |

Isolating the `version` field in `producer/lakefile.lean` (`v!"1.0.0" -> v!"2.0.0" -> v!"1.0.0"`) while holding `Dep.lean` content (`7`) and `mtime`, manifests, assigned name, and index constant (`support/lake-version-only-identity/results.json`, admitted at 31.56% reclaimable RAM, peak group RSS 1,015,360 KiB) showed that `version` changes only the configuration hash and configuration `.olean`, not module `.olean` bytes:

| Cell | Producer Version | `Dep.lean` Value | Producer Config OLean SHA-256 Prefix | Config Trace `configHash` | `Dep.olean` SHA-256 Prefix | `Generated.olean` SHA-256 Prefix | Fresh `#eval` |
| --- | ---: | ---: | --- | --- | --- | --- | ---: |
| `main A` | `1.0.0` | `7` | `b6b95601a569` | `a5b4b476a0591aca` | `cebebbbc8923` | `eedfc1593799` | `7` |
| `main B` | `2.0.0` | `7` | `ca501585c360` | `b74db869a8cb920f` | `cebebbbc8923` (`Replayed Dep`) | `eedfc1593799` | `7` |
| `main A return` | `1.0.0` | `7` | `b6b95601a569` | `a5b4b476a0591aca` | `cebebbbc8923` (`Replayed Dep`) | `eedfc1593799` | `7` |
| `source control A` | `1.0.0` | `7` | `b6b95601a569` | `a5b4b476a0591aca` | `cebebbbc8923` | `eedfc1593799` | `7` |
| `source control B` | `1.0.0` | `9` | `b6b95601a569` | `a5b4b476a0591aca` | `fe893ce3c24d` (`Built Dep`) | `eedfc1593799` | `9` |

Basis: **source + execution** (`support/lake-consumer-identity-observability/results.json`, `support/lake-frozen-index-collision/results.json`, `support/lake-version-only-identity/results.json`).

### Executable `lakefile.lean` (`run_cmd`) Sandbox Boundary and Hidden Environment Inputs

Because `lakefile.lean` is elaborated as Lean code during workspace loading (`LoadConfig`), a `run_cmd` block executes arbitrary IO before any target build starts (`support/lakefile-run-cmd-sandbox-boundary/results.json`):

| Case Label | Configuration File (SHA-256) | OS Sandbox Profile | Exit Code | Outside-Workspace Marker (`$WORK/<case>/outside/marker.txt`) |
| --- | --- | --- | ---: | --- |
| `dynamic-allow` | `dynamic-lakefile.lean` (`aee462168252...`) | None | `0` (1.4668 s) | Created (`marker_exists: true`, SHA-256 `26105cafeae6...`) |
| `dynamic-deny` | `dynamic-lakefile.lean` (`aee462168252...`) | `(deny file-write* (subpath "$WORK/dynamic-deny/outside")) (deny network*)` | `1` (0.3345 s) | Blocked (`marker_exists: false`; `operation not permitted`) |
| `static-deny` | `static-lakefile.lean` (`759dd5105701...`) | `(deny file-write* (subpath "$WORK/static-deny/outside")) (deny network*)` | `0` (0.5517 s) | None (`marker_exists: false`; `Built Dep`) |

In `support/lake-dynamic-config-identity/results.json` (57 command/server records), an adversarial `lakefile.lean` used `run_cmd` to read `PROBE_CONFIG_VALUE` (`A` -> `depValue := 7`, `B` -> `depValue := 9`) and write `Dep.lean`. Comparing clean dynamic Lean, static `lakefile.toml`, static Lean option variants, timestamp shifts, and metadata replacements showed:

| Cell / Control | `--no-build build Dep` | `setup-file` Returned OLean | Direct Local Batch (`LEAN_PATH`) | Fresh Direct Server |
| --- | ---: | --- | --- | --- |
| Clean dynamic Lean `A` (`7`) | Initial build | Value `7` (`cebebbbc8923...`) | Exit `0`, value `8` | Value `8`, no theorem error |
| Clean dynamic Lean `B` (`9`) | Initial build | Value `9` (`fe893ce3c24d...`) | Exit `1`, expected `8` false | Failed theorem, value `10` |
| Clean static TOML value `7` | Initial build | Value `7` (`cebebbbc8923...`) | Exit `0`, value `8` | Value `8`, no theorem error |
| Clean static TOML value `9` | Initial build | Value `9` (`fe893ce3c24d...`) | Exit `1`, expected `8` false | Not queried |
| Clean static Lean option value `7` | Initial build | Value `7` (`cebebbbc8923...`, changed `Dep.setup.json`) | Exit `0`, value `8` | Not queried |
| Already built dynamic `A`, environment changed to `B` | `0` (config cached; `run_cmd` not re-run) | Still value `7` | Exit `0`, value `8` | Still value `8` |
| Source `mtime` $\pm 1$ day; trace `mtime` $+1$ day, bytes unchanged | `0` in all three | Still value `7` | Exit `0` in all three | Not queried |
| Valid value-9 `Dep.trace` replacing value-7 trace | `0` (fetched value-7 cache object) | Value `7` (cache path) | Exit `1` (local `Dep.olean` absent) | Not queried |
| Valid option-generation `Dep.setup.json` replacing value-7 setup | `0` | Value `7` | Exit `0`, value `8` | Not queried |
| Value-9 source bytes with original value-7 nanosecond `mtime` | `0` (fetched value-9 cache object) | Value `9` (cache path; proof fails) | Exit `1` (local `Dep.olean` absent) | Not queried |

Basis: **execution** (`support/lakefile-run-cmd-sandbox-boundary/results.json`, `support/lake-dynamic-config-identity/results.json`).

### Cache Policy, Key Ablations, Artifact-Family Omissions, and Cross-Generation Mixing

In `support/lake-identity-matrix-v4-30-0-rc2/results.json` (36 commands, replayed identically in `replay-results.json`), `LAKE_CACHE_DIR` and `LAKE_ARTIFACT_CACHE` acted independently:

| Incoming `LAKE_CACHE_DIR` | `LAKE_ARTIFACT_CACHE` | Resolved Child Cache Path (`lake env printenv LAKE_CACHE_DIR`) | Files Populated After Build |
| --- | --- | --- | ---: |
| `""` (empty string) | `false` | Consumer `.lake/cache` | `0` |
| `""` (empty string) | `true` | Consumer `.lake/cache` | `8` (6 artifacts + 2 maps) |
| Explicit absolute directory | `false` | Explicit directory | `0` |
| Explicit absolute directory | `true` | Explicit directory | `8` (6 artifacts + 2 maps) |

Renaming the consumer package from `probe_consumer` to `probe_consumer_alt` in `lakefile.lean` and `lake-manifest.json` at the same directory changed `setup-file`'s `package` field and recompiled the consumer configuration `.olean` (`b14e1bbac7ece9818f6f3dac1f25a49d8f825bb402b406b729faa007fecb6f67 -> 6647e5c18fa405cc29091f736e3e2d9361391453eedb450d7c70265e0e526b5b`) and `.trace` (`7d5612c273bf2488d76aa2a1f7f6d17dbeaff617b35f024f1475b0df9b91d1de -> e191429fd6ae3ba82d7e7881f00e4ede843a6505d1fb031655d1cfa887a909f1`) while keeping `importArts.Dep` unchanged. Creating a directory symlink `producer-alias -> producer` (same inode) resolved `importArts.Dep` to the same physical `producer/.lake/build/lib/lean/Dep.olean` path. Removing individual producer build files from an intact non-cached build showed:

| Removed Producer File | `--no-build build Dep` | `--no-build setup-file` | `lake env lean --json Generated.lean` |
| --- | ---: | ---: | --- |
| `.lake/build/lib/lean/Dep.olean` | `3` | `3` | `1` (missing import error) |
| `.lake/build/lib/lean/Dep.ilean` | `3` | `3` | `0` (evaluates `7`) |
| `.lake/build/lib/lean/Dep.trace` | `3` | `3` | `0` (evaluates `7`) |
| `.lake/build/ir/Dep.c` | `3` | `3` | `0` (evaluates `7`) |
| `.lake/build/ir/Dep.setup.json` | `0` | `0` | `0` (evaluates `7`; file remains absent) |

In `support/lake-key-artifact-family-matrix/results.json` (39 command records), six input variations against one cumulative artifact cache generated four distinct producer output-map keys:

| Input Case | New Producer Output-Map Key | Local `Dep.olean` After Lake | Direct Local Batch Outcome |
| --- | --- | --- | --- |
| Baseline `depValue = 7` | `bc2ee9095550ff31.json` | Present | Exit `0`, value `8` |
| Same bytes, different root path | None (reused `bc2ee9095550ff31.json`) | Absent after cache fetch | Exit `1` (`unknown module prefix 'Dep'`) |
| Source body `depValue = 9` | `9f80558e806f84cd.json` | Present | Exit `1` (expected `8` false; value `10`) |
| Added declaration with `depValue = 7` | `56754994d46eab8e.json` | Present | Exit `0` |
| Producer `pp.unicode.fun` option | `ae8ebb304e3ca915.json` | Present (baseline `.olean`/`.ilean`/`.c` hashes; changed `Dep.setup.json`) | Exit `0` |
| Consumer manifest/package name only | None beyond prior four | Absent after cache fetch | Exit `1` (`unknown module prefix 'Dep'`) |

Overwriting one baseline local file at a time with valid bytes from another generation while the artifact cache remained enabled showed that `--no-build` and `setup-file` resolved the cached baseline `.olean` (`cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b`) without repairing the overwritten local file:

| Valid Replacement at Baseline Local Path | Lake `--no-build build Dep` | Lake `--no-build setup-file` | Fresh Batch via Setup-Returned OLean | Fresh Batch via Local Path | Fresh Isolated Lean Server via Local Path |
| --- | ---: | ---: | ---: | --- | --- |
| Wrong-generation `.olean` (`depValue = 9`) | `0` | `0` | `0` (value `8`) | `1` (false proposition, value `10`) | Failed `decide`, value `10` |
| Added-declaration `.ilean` | `0` | `0` | `0` | `0` | No proof error, value `8` |
| Wrong-generation `.c` (`depValue = 9`) | `0` | `0` | `0` | `0` | No proof error, value `8` |
| Option-generation `Dep.setup.json` | `0` | `0` | `0` | `0` | Not queried |

Loading two valid native plugin `.dylib` generations under `plugin__probe_Plugin.dylib` compiled the same theorem while emitting distinct initializer markers (`plugin-v1` vs. `plugin-v2`), showing that theorem success alone does not identify loaded native code. Basis: **execution** (`support/lake-identity-matrix-v4-30-0-rc2/results.json`, `support/lake-key-artifact-family-matrix/results.json`).

### Build-Action Observability, Unprivileged File-Event Witness, and Generated Provenance Trace Response

In `support/lake-consumer-identity-observability/results.json`, verbose (`-v`) `Replayed Dep` output reprinted the saved `lean ... Dep.lean` command line from `Dep.trace` even though `ps` descendant polling caught `$TOOLCHAIN_BIN/lean` only during `Built Dep` runs, and `--rehash --no-build build Dep` after a same-mtime edit (`7 -> 8`) exited 3 while writing `Dep.trace.nobuild`.

To observe process-level file activity without root privileges, `support/lake-unprivileged-file-event-observability/observe.c` interposed `open`, `openat` (`AT_FDCWD`), `read`, `write`, `rename`, and `unlink` via `DYLD_INSERT_LIBRARIES`:

| Phase | Exit | Selected Libc Events / Distinct PIDs | Net Fixture File Deltas | Main Observation |
| --- | ---: | --- | ---: | --- |
| Cold build (`value := 7`) | `0` | `41` / `2` | `11` | `Built Dep`; child `process-lean` has `PPID == Lake PID`; renames `Dep.olean.tmp.<PID> -> Dep.olean` |
| Unchanged replay | `0` | `11` / `1` | `0` | `Replayed Dep`; opens source/trace/hash files; records 88-byte `read` of `lakefile.olean` |
| Same-mtime mutation (`7 -> 9`), `--rehash --no-build` | `3` | `9` / `1` | `1` | Builder needed; `.trace.nobuild` added |
| Changed build (`value := 9`) | `0` | `40` / `2` | `9` | `Built Dep`; Lean child and temporary-to-final `.olean` rename |
| Subsequent replay | `0` | `11` / `1` | `0` | `Replayed Dep` with selected file calls |
| Unhooked subsequent replay | `0` | No hook | `0` | Same Lake replay classification without observer |
| Fresh batch `#eval value` | `0` | No hook | `0` | Lean reported `9` |

Finally, `support/generated-lake-source-order-trace/results.json` tested a 1,686-job Aeneas-generated Lake graph containing four local modules (`Source.Types`, `Source.Funs`, `Source`, and `Consumer.lean` checking `inc`, `twice`, and `choose` by `rfl`; 32 local build files: 12 `.hash` and 4 each of `.json` setup, `.c`, `.trace`, `.olean`, and `.ilean`). Between `base` and `reorder`, `Source/Types.lean` and `Source.lean` were byte-identical, while `Source/Funs.lean` differed only in three `Source:` doc-comment provenance lines (`base/source.rs` vs. `reorder/source.rs` and line ranges, with identical executable `def` text and order):

| Run | Wall Time | Local Module Result | Local `.lake/build` Inventory Observation (32 Files) |
| --- | ---: | --- | --- |
| Fresh `base` | 73.60 s | All four `Built` | Initial 32 local build files created |
| Fresh `reorder` | 25.21 s | All four `Built` | Equal `.olean`, `.ilean`, and `.c` bytes to same-path `reorder`; 4 `.trace` and 3 `.json` setup files differed across paths |
| Same-path `base` | 61.41 s | All four `Built` | Baseline 32 local build file hashes |
| Same-path no-write | 5.63 s | All four `Replayed` | Zero hash or `mtime` changes |
| Same-path `mtime`-only touch (`Source/Funs.lean`) | 4.30 s | All four `Replayed` | Zero build-file hash or `mtime` changes |
| Same-path `reorder` | 28.15 s | `Source.Types` `Replayed`; `Source.Funs`, `Source`, `Consumer` `Built` | `Source/Funs.olean`, its `.hash`, and `Source.Funs`/`Source`/`Consumer` `.trace` bytes changed; `.ilean` and `.c` bytes stayed identical |
| Same-path `reorder` no-write | 4.14 s | All four `Replayed` | Zero hash or `mtime` changes |
| Same-path restore `base` | 21.17 s | `Source.Types` `Replayed`; other three `Built` | All 32 local build-file hashes returned to original `base` values (27 `mtime` values advanced) |
| Same-path restore no-write | 3.67 s | All four `Replayed` | Zero hash or `mtime` changes |

Basis: **execution** (`support/lake-unprivileged-file-event-observability/results.json`, `support/generated-lake-source-order-trace/results.json`).

## Boundaries

- **Upgraded `v4.31.0+` configuration ownership (`not examined` in this package)**: Only `v4.29.0` and `v4.30.0-rc2` were present in the local toolchain cache when these nine suites ran; execution of the read-only consumer and server matrix on `v4.34.1` is covered separately in the cross-version shared-tree writer report.
- **Unprivileged libc interposition completeness (`known not to apply`)**: `DYLD_INSERT_LIBRARIES` interposition (`support/lake-unprivileged-file-event-observability/observe.c`) does not capture direct syscalls, `mmap`/`fopen`/`pread`, `openat` calls relative to non-`AT_FDCWD` descriptors, or accesses outside `$WORK` (for example, no `write` call was captured for `Dep.olean` even though its temporary file was written and renamed).
- **Verbose `-v` compiler lines and `--no-build` as no-process / no-write guarantees (`known not to apply`)**: `Replayed` targets reprint historical compiler command lines from saved traces without launching `lean`, and failing `--rehash --no-build` runs write `.trace.nobuild` files into the build directory.
- **Provenance comment vs. declaration-order isolation (`unknown`)**: In `support/generated-lake-source-order-trace/`, `Source/Funs.lean` changed both Rust source pathnames (`base/source.rs` vs. `reorder/source.rs`) and line-range comments simultaneously; which component specifically altered `Source/Funs.olean` bytes was **not examined** in isolation.

## Evidence

### Consumer Identity, Frozen Index Collision, and Version-Only Identity (`support/lake-consumer-identity-observability/`, `support/lake-frozen-index-collision/`, `support/lake-version-only-identity/`)
- Consumer identity and observability: [`support/lake-consumer-identity-observability/probe.py`](support/lake-consumer-identity-observability/probe.py), [`support/lake-consumer-identity-observability/results.json`](support/lake-consumer-identity-observability/results.json), and [`support/lake-consumer-identity-observability/check.py`](support/lake-consumer-identity-observability/check.py).
- Frozen index collision: [`support/lake-frozen-index-collision/probe.py`](support/lake-frozen-index-collision/probe.py), [`support/lake-frozen-index-collision/results.json`](support/lake-frozen-index-collision/results.json), and [`support/lake-frozen-index-collision/check.py`](support/lake-frozen-index-collision/check.py).
- Package-version-only ablation: [`support/lake-version-only-identity/oracle.json`](support/lake-version-only-identity/oracle.json), [`support/lake-version-only-identity/probe.py`](support/lake-version-only-identity/probe.py), [`support/lake-version-only-identity/results.json`](support/lake-version-only-identity/results.json), [`support/lake-version-only-identity/raw/`](support/lake-version-only-identity/raw/), [`support/lake-version-only-identity/snapshots/`](support/lake-version-only-identity/snapshots/), [`support/lake-version-only-identity/preliminary/`](support/lake-version-only-identity/preliminary/), [`support/lake-version-only-identity/work/`](support/lake-version-only-identity/work/), and [`support/lake-version-only-identity/check.py`](support/lake-version-only-identity/check.py).

### Dynamic Configuration and `run_cmd` Sandbox Boundary (`support/lakefile-run-cmd-sandbox-boundary/` and `support/lake-dynamic-config-identity/`)
- `run_cmd` sandbox boundary: [`support/lakefile-run-cmd-sandbox-boundary/probe.py`](support/lakefile-run-cmd-sandbox-boundary/probe.py), [`support/lakefile-run-cmd-sandbox-boundary/inputs/dynamic-lakefile.lean`](support/lakefile-run-cmd-sandbox-boundary/inputs/dynamic-lakefile.lean), [`support/lakefile-run-cmd-sandbox-boundary/inputs/static-lakefile.lean`](support/lakefile-run-cmd-sandbox-boundary/inputs/static-lakefile.lean), and [`support/lakefile-run-cmd-sandbox-boundary/results.json`](support/lakefile-run-cmd-sandbox-boundary/results.json).
- Dynamic configuration and timestamp/metadata matrix: [`support/lake-dynamic-config-identity/probe.py`](support/lake-dynamic-config-identity/probe.py), [`support/lake-dynamic-config-identity/results.json`](support/lake-dynamic-config-identity/results.json), [`support/lake-dynamic-config-identity/artifacts/`](support/lake-dynamic-config-identity/artifacts/), and [`support/lake-dynamic-config-identity/check.py`](support/lake-dynamic-config-identity/check.py).

### Cache Ownership, Input Keys, and Artifact Families (`support/lake-identity-matrix-v4-30-0-rc2/` and `support/lake-key-artifact-family-matrix/`)
- Cache ownership and single-artifact omission matrix: [`support/lake-identity-matrix-v4-30-0-rc2/probe.py`](support/lake-identity-matrix-v4-30-0-rc2/probe.py) (SHA-256 `d1ac13b75671a9454259bc2e1377d7fb426683bfbc111b7b7ff3823436bed50e`), [`support/lake-identity-matrix-v4-30-0-rc2/results.json`](support/lake-identity-matrix-v4-30-0-rc2/results.json), and [`support/lake-identity-matrix-v4-30-0-rc2/replay-results.json`](support/lake-identity-matrix-v4-30-0-rc2/replay-results.json).
- Input-key and cross-generation artifact family matrix: [`support/lake-key-artifact-family-matrix/probe.py`](support/lake-key-artifact-family-matrix/probe.py), [`support/lake-key-artifact-family-matrix/results.json`](support/lake-key-artifact-family-matrix/results.json), [`support/lake-key-artifact-family-matrix/artifacts/`](support/lake-key-artifact-family-matrix/artifacts/), and [`support/lake-key-artifact-family-matrix/check.py`](support/lake-key-artifact-family-matrix/check.py).

### Unprivileged File-Event Witness and Generated Provenance Trace (`support/lake-unprivileged-file-event-observability/` and `support/generated-lake-source-order-trace/`)
- Unprivileged libc file-event observer: [`support/lake-unprivileged-file-event-observability/observe.c`](support/lake-unprivileged-file-event-observability/observe.c), [`support/lake-unprivileged-file-event-observability/probe.py`](support/lake-unprivileged-file-event-observability/probe.py), [`support/lake-unprivileged-file-event-observability/results.json`](support/lake-unprivileged-file-event-observability/results.json), and [`support/lake-unprivileged-file-event-observability/check.py`](support/lake-unprivileged-file-event-observability/check.py).
- Aeneas-generated multi-module provenance trace response: [`support/generated-lake-source-order-trace/fixture/`](support/generated-lake-source-order-trace/fixture/), [`support/generated-lake-source-order-trace/probe.py`](support/generated-lake-source-order-trace/probe.py), [`support/generated-lake-source-order-trace/results.json`](support/generated-lake-source-order-trace/results.json), [`support/generated-lake-source-order-trace/logs/`](support/generated-lake-source-order-trace/logs/), [`support/generated-lake-source-order-trace/work.tar.gz`](support/generated-lake-source-order-trace/work.tar.gz), and [`support/generated-lake-source-order-trace/check.py`](support/generated-lake-source-order-trace/check.py).

## Revalidation

Run the seven offline verification scripts to check all retained results, SHA-256 digests, configuration trace snapshots, and file-event records without invoking Lake or Lean:

```console
python3 support/lake-consumer-identity-observability/check.py
python3 support/lake-frozen-index-collision/check.py
python3 -B support/lake-version-only-identity/check.py
python3 support/lake-dynamic-config-identity/check.py
python3 support/lake-key-artifact-family-matrix/check.py
python3 support/lake-unprivileged-file-event-observability/check.py
python3 support/generated-lake-source-order-trace/check.py
```

To revalidate against a newer Lean/Lake toolchain, run `support/lake-frozen-index-collision/probe.py`, `support/lake-identity-matrix-v4-30-0-rc2/probe.py`, and `support/lakefile-run-cmd-sandbox-boundary/probe.py` in fresh empty scratch directories and compare whether shifted consumer dependency indices still attempt to lock or rewrite `.lake/config` inside a read-only dependency tree.
