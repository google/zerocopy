# Lean LSP Native Plugin Loading, Artifact Family Sufficiency, Worker Mapping Isolation, and OS Sandboxing

## Summary

In Lean and Lake `v4.30.0-rc2`, native plugins (`--plugin=...dylib` and Lake `@pkg/+Plugin:dynlib` facets) and prepared module artifact families (`.olean`, `.ilean`, `.c`, `.dylib`) exhibit distinct per-operation sufficiency, per-worker process-mapping lifecycles, path-resolution rules, and OS sandboxing requirements:
1. **Operation-specific artifact sufficiency**: Removing `Dep.olean` breaks direct batch compilation (`exit 1`) until `lake setup-file` rebuilds it. Removing `Dep.ilean` or `Dep.c` causes `lake --no-build build Dep +Plugin:dynlib` to exit `3` (out of date), yet direct batch proof checking still passes (`exit 0`). Removing `Plugin.dylib` breaks `lake --no-build` (`exit 3`) and explicit `lean --plugin=...` (`exit 1`, and `lake setup-file` does not rebuild the separate plugin target), whereas batch checking without `--plugin` passes (`exit 0`).
2. **Cross-generation family mixing**: A Lake workspace mixing `v1` `Dep.lean`/`Dep.olean`/`Dep.ilean` (`selected = 7`) with `v2` `Plugin.dylib`, `v2` `Dep.c`, and `v2` Lake option `pp.universes = true` succeeds in `lake setup-file`, `lake serve`, and `lake env lean`, evaluating `selected` to `7` while executing the `plugin-v2` native initializer without triggering a rebuild.
3. **Worker-scoped plugin loading, reversal (`v1 -> v2 -> v1`), and `lsof`/`vmmap` process mappings**: Replacing a valid `--plugin` dylib on disk (or atomically retargeting a symlink) leaves already-open file workers and the server watchdog mapped to `v1`, while each newly opened file spawns a worker process that loads the current on-disk target (`v1 -> v2 -> v1` across successive file opens in one watchdog). `lsof` and `vmmap` confirm that the watchdog retains `v1` mapped even after the first worker closes (`didClose`) and the second worker maps `v2`. Replacing the dylib with a valid Mach-O binary whose initializer symbol does not match (`initialize_plugin__probe_Plugin` missing) crashes newly opened file workers with `waitForDiagnostics` error `-32901` while already-open workers continue answering normally.
4. **Plugin path resolution (`IO.FS.realPath`)**: Lean's `loadPlugin` (`src/Lean/LoadDynlib.lean`) resolves `--plugin=file` relative to the process working directory via `IO.FS.realPath` before calling `Dynlib.load` and explicitly does **not** search `LEAN_PATH` or system library paths.
5. **Lack of internal plugin sandboxing vs. OS kernel enforcement**: A native plugin's `@[init]` initializer executes arbitrary native code in both `lean` batch and `lean --server` workers and writes outside the workspace root (`outside-marker.txt`) unless confined by an OS-level sandbox such as macOS `sandbox-exec` (`deny file-write*` outside workspace, which blocks the write with `Operation not permitted`).

## Applicability

- **Evaluated Toolchain Subject**: Lean 4 and Lake `v4.30.0-rc2` (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` executable SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`) on arm64 macOS with `LEAN_NUM_THREADS=1` and offline execution.
- **Subprobe Coverage**:
  1. **Prepared artifact family matrix and plugin replacement stages** (`support/lake-plugin-artifact-identity-v4-30-0-rc2/`): Per-family removal matrix (`Dep.olean`, `Dep.ilean`, `Dep.c`, `Plugin.dylib`) and live server replacement with valid `v2`, wrong-initializer `Alien` dylib, truncated Mach-O, and deleted dylib.
  2. **Lake-discovered plugin, setup option, and `.olean` family mix** (`support/lake-plugin-combined-family-mix/`): Two-package `@plugin_probe/+Plugin:dynlib` consumer mixing `v1` `.olean`/`.ilean` with `v2` `.dylib`/`.c` and `pp.universes = true`.
  3. **Plugin reversal across file workers and server restart** (`support/plugin-reversal-worker-order/`): `v1 -> v2 -> v1` atomic `os.replace` sequence across three file workers in one watchdog followed by a fourth file in a fresh server.
  4. **Process-mapped plugin paths (`lsof` and `vmmap`) and resource-guarded restart** (`support/native-plugin-mapped-workers/`): Direct inspection of mapped `.dylib` paths in the watchdog and file-worker PIDs across open, `didClose`, symlink switch, a 1,536 MiB (`1,572,864` KiB) summed-RSS guard stop, and a forced server restart.
  5. **Plugin basename `cwd` resolution and symlink alias switching** (`support/plugin-cwd-path-alias-v4-30-0-rc2/`): Pinned source verification (`Lean/LoadDynlib.lean` SHA-256 `88941bc513806a35f7a86ee4056e1cecab8af9a8feb596ad01000914d3f570f1`, `Lean/Shell.lean` SHA-256 `0de8cdbadedf418ccfb051ec8cb2c7bcd3bb6fef524c16962c72e4acfbf64d54`) and CLI/server execution across empty `cwd` with `LEAN_PATH=A`, `cwd=A`, `cwd=B`, and symlink target switching.
  6. **Native plugin initializer OS sandbox boundary trial** (`support/native-plugin-sandbox-trial/`): Harvested meta-audit security probe testing `@[init]` out-of-workspace file writes under permissive vs. restrictive `sandbox-exec` profiles.

## Findings

### 1. Prepared Artifact Family Sufficiency and Invalid/Mismatched Plugin Failure Stages

In `support/lake-plugin-artifact-identity-v4-30-0-rc2/transcript.json` (224 events, SHA-256 `9d26d845e404706a93e9ee5ff8a95261cb8fb54a553966b4d2a0299464c4b581`) and `support/lake-plugin-artifact-identity-v4-30-0-rc2/summary.json` (initial `v1` dylib SHA-256 `3f4a1cb3a67a0027f0c90e819afc20d009ddb921cb7f4c0e0095db074e085aa4`, `v2` dylib SHA-256 `f7b4c875cb1c91a35259462b5034f48ad96f819e519d9414edc68975045f92a9`, wrong-initializer `Alien` dylib SHA-256 `36444a43c5c5a9b0a4cb3d7f13d1e1922b13428afb30b858f746fccf142ea77b`):

| Removed family | `--no-build` target (`build Dep +Plugin:dynlib`) | Batch before setup, with `--plugin` | `setup-file Proof.lean` | Batch after setup | Observation |
| --- | ---: | ---: | ---: | ---: | --- |
| `Dep.olean` | 3 | 1 | 0 | 0 | Setup rebuilt the missing imported OLean. |
| `Dep.ilean` | 3 | 0 | 0 | 0 | Batch import did not need this info artifact; setup rebuilt it. |
| `Dep.c` | 3 | 0 | 0 | 0 | Batch import did not need generated C; setup rebuilt it. |
| `Plugin.dylib` | 3 | 1 | 0 | 1 | File setup did not rebuild this separate plugin target. Batch **without** `--plugin` passed before setup (exit 0). |

When replacing `Plugin.dylib` while a `lean --server` instance had `Proof.lean` open:
- **Valid `v2` replacement**: The already-open `Proof.lean` worker continued returning `no goals` with marker `plugin-v1`; opening `New.lean` in the same server initialized a new worker that wrote `plugin-v2`, and a fresh server/batch also wrote `plugin-v2`.
- **Wrong-initializer (`Alien`) dylib replacement**: The already-open `Proof.lean` worker remained usable (`no goals`), while opening `New.lean` failed `waitForDiagnostics` with JSON-RPC error `-32901` and stderr `error: while loading '...': initializer not found 'initialize_plugin__probe_Plugin'` (the watchdog itself remained alive and exited `0` on shutdown).
- **Truncated Mach-O and deleted dylib**: Both failed in fresh processes at explicit plugin load (`dlopen` invalid-Mach-O or missing file error) before proof elaboration (**Basis: execution**).

### 2. Cross-Generation Artifact Family Mixing Under Lake Discovery

In `support/lake-plugin-combined-family-mix/transcript.json` and `support/lake-plugin-combined-family-mix/artifacts/`:

| Cell | Imported `Dep.olean` SHA-256 | Plugin dylib SHA-256 | Setup option | Fresh `lake serve` observation |
| --- | --- | --- | --- | --- |
| `v1` | `078123f009c35edce8716cda15d83568dfbcb60c8840a0b74c26d47213ae02f2` | `5418363ec3b0d09e2cf5d8d058d088d9642da848531fb399cce6f863f2b63d3a` | none | No goals; info `7`; marker `plugin-v1` |
| `v2` | `82056aa6634611238637e5c3d5dc166a1d0abc359ee14f61f2a12d5a541e8fd8` | `7e7f461e977f5f4cd22c6151ebeb3096fe40f08116e954527dce923ea6e01968` | `pp.universes=true` | No goals; info `9`; marker `plugin-v2` |
| `mixed` | `v1` hash (`078123f0…`) | `v2` hash (`7e7f461e…`) | `pp.universes=true` | No goals; info `7`; marker `plugin-v2` |

In the `mixed` workspace (which also included `v2` `Dep.c` SHA-256 `cddb20d2857b7998332e77a26aebac9123bbbec3f59814704fd4a6ed1a36ce18`), `lake setup-file Proof.lean`, `lake serve`, and `lake env lean Proof.lean` all succeeded without rebuilding or modifying any artifact hash (**Basis: execution**).

### 3. Worker-Order Reversal (`v1 -> v2 -> v1`) and Process Memory-Map Inspection (`lsof` / `vmmap`)

- **Three-worker `v1 -> v2 -> v1` reversal in one watchdog** (`support/plugin-reversal-worker-order/transcript.json`):

| Event | Plugin path SHA-256 | New file marker | Goal |
| --- | --- | --- | --- |
| First file in retained server | `v1` (`3f4a1cb3…`) | `plugin-v1` | no goals |
| New file after `v1 -> v2` | `v2` (`f7b4c875…`) | `plugin-v2` | no goals |
| New file after `v2 -> v1` | `v1` (`3f4a1cb3…`) | `plugin-v1` | no goals |
| New server, fourth file | `v1` (`3f4a1cb3…`) | `plugin-v1` | no goals |

- **Direct `lsof` and `vmmap` process-mapping snapshots and RSS guard** (`support/native-plugin-mapped-workers/mapping-logs/`, `support/native-plugin-mapped-workers/guard-abort.json`, `support/native-plugin-mapped-workers/restart-transcript.json`):

| Snapshot | Watchdog mapping | File-worker mapping | Lifecycle observation |
| --- | --- | --- | --- |
| `v1-first` | PID 93511 → `v1/plugin__probe_Plugin.dylib` | PID 93518 → `v1/plugin__probe_Plugin.dylib` | First document open; both `lsof` and `vmmap` include the `v1` real path. |
| `v1-after-close` | PID 93511 → `v1/plugin__probe_Plugin.dylib` | No file worker in the watchdog's process tree | `didClose` sent and 0.5 s elapsed; worker exited while watchdog retained `v1` mapped. |
| `v2-open` | PID 93511 → `v1/plugin__probe_Plugin.dylib` | PID 93706 (`P1.lean`) → `v2/plugin__probe_Plugin.dylib` | Stable symlink pointed to `v2`; watchdog stayed mapped to `v1` while new worker mapped `v2`. |
| `forced-restart-v1` | PID 93910 → `v1/plugin__probe_Plugin.dylib` | PID 93911 → `v1/plugin__probe_Plugin.dylib` | After the retained server hit a unique-PID summed RSS of `1,576,608 KiB` (exceeding the `1,572,864 KiB` cap by `3,744 KiB`) and was killed, a fresh server peaked at `1,572,736 KiB` (128 KiB below cap), wrote `plugin-v1`, returned `goals: []`, and exited 0. |

### 4. `--plugin` Basename Resolution (`IO.FS.realPath`) vs. `LEAN_PATH`

In `support/plugin-cwd-path-alias-v4-30-0-rc2/transcript.json`, source analysis of `src/Lean/LoadDynlib.lean` (lines 93–98, SHA-256 `88941bc513806a35f7a86ee4056e1cecab8af9a8feb596ad01000914d3f570f1`) and `src/Lean/Shell.lean` (lines 409–413, SHA-256 `0de8cdbadedf418ccfb051ec8cb2c7bcd3bb6fef524c16962c72e4acfbf64d54`) was paired with six CLI/server execution cases:

| Case | `--plugin` argument and `cwd` | Resolved binary | Observation |
| --- | --- | --- | --- |
| CLI negative | `--plugin=plugin__probe_Plugin.dylib`, empty `cwd`; `LEAN_PATH=A` | none | exit 1, no marker, `no such file or directory` (`LEAN_PATH` is not searched) |
| CLI A | `--plugin=plugin__probe_Plugin.dylib`, `cwd` A | `v1` (`3f4a1cb3…`) | exit 0, `plugin-v1` |
| CLI B | `--plugin=plugin__probe_Plugin.dylib`, `cwd` B; `LEAN_PATH=A` | `v2` (`f7b4c875…`) | exit 0, `plugin-v2` |
| Retained server, first file | `--plugin=plugin__probe_Plugin.dylib`, `cwd` alias→A | `v1` | `plugin-v1`, diagnostics and goal succeeded |
| Same server, new file after alias→B | `--plugin=plugin__probe_Plugin.dylib`, same `cwd` | `v2` | `plugin-v2`, diagnostics and goal succeeded; old file goal still succeeded |
| Fresh server, alias→B | `--plugin=plugin__probe_Plugin.dylib`, same `cwd` | `v2` | `plugin-v2`, diagnostics and goal succeeded |

### 5. Native Plugin Initializer OS Sandbox Boundary Trial

In `support/native-plugin-sandbox-trial/probe.py`, `support/native-plugin-sandbox-trial/inputs`, `support/native-plugin-sandbox-trial/results.json`, `support/native-plugin-sandbox-trial/raw-streams`, and `support/native-plugin-sandbox-trial/excluded-basename-attempt.json`:
- A Lean `v4.30.0-rc2` native plugin (`plugin__probe_Plugin.dylib`, SHA-256 `a6fa72cb...`) was compiled with an `@[init]` initializer that writes `outside-marker.txt` outside the workspace directory.
- Under macOS `sandbox-exec` with outside-workspace writes permitted (`allow-write*`), both batch `lean --plugin=...` and `lean --server` executed the `@[init]` symbol on load and created `outside-marker.txt`.
- Under `sandbox-exec` denying writes outside the workspace root (`deny file-write*` outside workspace), the OS kernel blocked the native initializer's write (`Operation not permitted`), leaving `outside-marker.txt` absent (`exists: false`). This confirms that Lean's language server has no internal sandbox against `--plugin` / `--load-dynlib` native code execution; process-level OS sandboxing is required to enforce filesystem write boundaries when loading native plugins (**Basis: execution**).

## Boundaries

- **Not examined**: Cross-version or cross-compiler C++ ABI subtle incompatibilities where a plugin loads (`dlopen` and `initialize_*` succeed) but later corrupts Lean heap objects during tactic execution.
- **Not examined**: Linux `seccomp`/`landlock`/`bubblewrap` or Windows job-object sandboxing equivalents (only macOS `sandbox-exec` was executed).
- **Unknown**: Whether any mechanism can unload a native shared library from a running Lean watchdog process without terminating the process (`LoadDynlib.lean` explicitly keeps `Dynlib` handles persistent for the lifetime of the process).
- **Known not to apply**: `LEAN_PATH` does not govern `--plugin` lookup, and `lake setup-file` on a proof module does not rebuild an out-of-date or missing standalone `:dynlib` plugin target unless the package configuration or build target explicitly triggers it.

## Evidence

- **Plugin artifact identity and failure stages**: [`support/lake-plugin-artifact-identity-v4-30-0-rc2/probe.py`](support/lake-plugin-artifact-identity-v4-30-0-rc2/probe.py) (SHA-256 `fb824c4a0549cd72ace1bc872152c5042438dff22df0afa532ab38e42abf48cc`), [`support/lake-plugin-artifact-identity-v4-30-0-rc2/transcript.json`](support/lake-plugin-artifact-identity-v4-30-0-rc2/transcript.json) (SHA-256 `9d26d845e404706a93e9ee5ff8a95261cb8fb54a553966b4d2a0299464c4b581`), [`support/lake-plugin-artifact-identity-v4-30-0-rc2/summarize.py`](support/lake-plugin-artifact-identity-v4-30-0-rc2/summarize.py), [`support/lake-plugin-artifact-identity-v4-30-0-rc2/summary.json`](support/lake-plugin-artifact-identity-v4-30-0-rc2/summary.json), and [`support/lake-plugin-artifact-identity-v4-30-0-rc2/work`](support/lake-plugin-artifact-identity-v4-30-0-rc2/work).
- **Combined artifact family mix**: [`support/lake-plugin-combined-family-mix/probe.py`](support/lake-plugin-combined-family-mix/probe.py), [`support/lake-plugin-combined-family-mix/check.py`](support/lake-plugin-combined-family-mix/check.py), [`support/lake-plugin-combined-family-mix/transcript.json`](support/lake-plugin-combined-family-mix/transcript.json), and [`support/lake-plugin-combined-family-mix/artifacts`](support/lake-plugin-combined-family-mix/artifacts).
- **Plugin reversal across workers**: [`support/plugin-reversal-worker-order/probe.py`](support/plugin-reversal-worker-order/probe.py), [`support/plugin-reversal-worker-order/check.py`](support/plugin-reversal-worker-order/check.py), [`support/plugin-reversal-worker-order/transcript.json`](support/plugin-reversal-worker-order/transcript.json), [`support/plugin-reversal-worker-order/artifacts`](support/plugin-reversal-worker-order/artifacts), and [`support/plugin-reversal-worker-order/work`](support/plugin-reversal-worker-order/work).
- **Process-mapped plugin inspection (`lsof`/`vmmap`)**: [`support/native-plugin-mapped-workers/probe.py`](support/native-plugin-mapped-workers/probe.py), [`support/native-plugin-mapped-workers/restart.py`](support/native-plugin-mapped-workers/restart.py), [`support/native-plugin-mapped-workers/check.py`](support/native-plugin-mapped-workers/check.py), [`support/native-plugin-mapped-workers/guard-abort.json`](support/native-plugin-mapped-workers/guard-abort.json), [`support/native-plugin-mapped-workers/restart-transcript.json`](support/native-plugin-mapped-workers/restart-transcript.json), [`support/native-plugin-mapped-workers/mapping-logs`](support/native-plugin-mapped-workers/mapping-logs), [`support/native-plugin-mapped-workers/artifacts`](support/native-plugin-mapped-workers/artifacts), [`support/native-plugin-mapped-workers/run`](support/native-plugin-mapped-workers/run), and [`support/native-plugin-mapped-workers/seed`](support/native-plugin-mapped-workers/seed).
- **Plugin `cwd` resolution and path alias**: [`support/plugin-cwd-path-alias-v4-30-0-rc2/probe.py`](support/plugin-cwd-path-alias-v4-30-0-rc2/probe.py), [`support/plugin-cwd-path-alias-v4-30-0-rc2/check.py`](support/plugin-cwd-path-alias-v4-30-0-rc2/check.py), and [`support/plugin-cwd-path-alias-v4-30-0-rc2/transcript.json`](support/plugin-cwd-path-alias-v4-30-0-rc2/transcript.json).
- **Native plugin OS sandbox boundary trial**: [`support/native-plugin-sandbox-trial/probe.py`](support/native-plugin-sandbox-trial/probe.py), [`support/native-plugin-sandbox-trial/inputs`](support/native-plugin-sandbox-trial/inputs), [`support/native-plugin-sandbox-trial/results.json`](support/native-plugin-sandbox-trial/results.json), [`support/native-plugin-sandbox-trial/raw-streams`](support/native-plugin-sandbox-trial/raw-streams), and [`support/native-plugin-sandbox-trial/excluded-basename-attempt.json`](support/native-plugin-sandbox-trial/excluded-basename-attempt.json).

## Revalidation

Run all offline verification scripts to check retained transcripts, artifact hashes, process-mapping logs, and marker orders without launching Lean or Lake:

```sh
python3 support/lake-plugin-artifact-identity-v4-30-0-rc2/summarize.py
python3 support/lake-plugin-combined-family-mix/check.py
python3 support/plugin-reversal-worker-order/check.py
python3 -B support/native-plugin-mapped-workers/check.py
python3 support/plugin-cwd-path-alias-v4-30-0-rc2/check.py
```

To re-run live acquisition on a pinned `v4.30.0-rc2` macOS installation, execute each subprobe's `probe.py` in a fresh scratch directory under `LEAN_NUM_THREADS=1` and the corresponding `sandbox-exec` profile.
