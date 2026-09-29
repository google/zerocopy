# Native plugin and prepared-artifact identity: bounded Lean/Lake probe

## Summary

On pinned Lean/Lake `v4.30.0-rc2`, a tiny Lake project imported a module containing a `probe_tac` macro and checked `selected = 7`; a separate Lean-built native plugin wrote `plugin-v1` or `plugin-v2` when loaded. A missing imported `.olean` made direct batch checking fail until `lake setup-file` rebuilt it. Missing `.ilean` or generated `.c` made the requested Lake `--no-build` target out of date, but direct batch import and the proof still passed. Removing the plugin dylib likewise made its native Lake facet out of date and explicit plugin loading fail; the same proof passed without `--plugin`. The artifact requirement therefore depended on the requested operation in this fixture.

Replacing the valid plugin dylib on disk while a server was live left an already open file's goal query usable. Opening a new file worker loaded the replacement `plugin-v2` initializer, and a fresh batch and fresh server also succeeded with v2. Replacing the path instead with a valid dylib whose module/initializer name did not match produced a new-file worker crash (`waitForDiagnostics` error `-32901`) while the already open file still answered. Fresh batch failed at plugin loading with `initializer not found`. This is a specific initializer-symbol mismatch, not a complete ABI-compatibility matrix. **Basis: execution**, with ordered wire and command transcript in [`support/transcript.json`](support/transcript.json).

## Subject and fixture

- Exact Lean/Lake release `leanprover/lean4:v4.30.0-rc2`, arm64 macOS 26.6.2. Lean SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; Lake SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`.
- Local `Dep.lean` imports Lean, declares the `probe_tac` macro expanding to `decide`, and defines `selected : Nat := 7`. `Proof.lean` imports `Dep`, proves `selected = 7` with `probe_tac`, then runs `#eval selected`. `Plugin.lean` imports Lean and has an initializer writing a marker selected at compile time. The plugin is loaded explicitly via `--plugin=...dylib`; `Proof.lean` does not import `Plugin`.
- All project copies, generated native artifacts, markers, and cache state are under [`support/work`](support/work). The script uses `--keep-toolchain --no-cache`, `LAKE_ARTIFACT_CACHE=false`, `LAKE_CACHE_DIR=''`, `LEAN_NUM_THREADS=1`, one batch/Lake command at a time and at most one Lean server session at a time. The pre-run free-memory check aborts under 20%; it is not a sampled peak-RSS bound. No package download, global installation, Anneal source, MCP server, or Mathlib participated.

## Prepared artifact matrix

Each row began from an independent copy of the v1 built project. The requested Lake target was `build Dep +Plugin:dynlib`; `setup-file Proof.lean` and batch loading were then tried. Exit codes and complete output are preserved under each command label in the transcript.

| Removed family | `--no-build` target | Batch before setup, with plugin | `setup-file` | Batch after setup | Observation |
|---|---:|---:|---:|---:|---|
| `Dep.olean` | 3 | 1 | 0 | 0 | Setup rebuilt the missing imported OLean. |
| `Dep.ilean` | 3 | 0 | 0 | 0 | Batch import did not need this info artifact; setup rebuilt it. |
| `Dep.c` | 3 | 0 | 0 | 0 | Batch import did not need generated C; setup rebuilt it. |
| `Plugin.dylib` | 3 | 1 | 0 | 1 | File setup did not rebuild this separate plugin target. Batch **without** `--plugin` passed before setup (exit 0). |

The valid initial v1 dylib SHA-256 was `3f4a1cb3a67a0027f0c90e819afc20d009ddb921cb7f4c0e0095db074e085aa4`. V2 was `f7b4c875cb1c91a35259462b5034f48ad96f819e519d9414edc68975045f92a9`. The wrong-initializer replacement was `36444a43c5c5a9b0a4cb3d7f13d1e1922b13428afb30b858f746fccf142ea77b`. Source and generated artifact copies remain in the work directory; the baseline OLean/ILean/C hashes are in [`support/summary.json`](support/summary.json). The `--no-build` exit 3 reports a requested Lake target's incompleteness, not that all batch proof checks require all four families.

## Live process boundary and failure stage

1. An old server loaded plugin v1, opened `Proof.lean`, completed diagnostics, and returned `no goals` after the tactic. A separate fresh query to the same old open file still returned `no goals` after the dylib path was atomically replaced by valid v2; the marker at that point remained `plugin-v1`.
2. Opening `New.lean` in the same server completed and wrote marker `plugin-v2`. This is evidence that its new worker loaded v2; it does not report a Lean internal plugin identity from the old worker. A fresh batch evaluated 7 and a fresh server opened `Proof.lean` with marker v2. Both servers shut down with exit 0.
3. In a separate copy, the old server loaded v1 and retained an answering `Proof.lean` worker after replacement by the valid `Alien` dylib under the original `Plugin` filename. A newly opened `New.lean` worker failed with `-32901` and the server stderr said `initializer not found 'initialize_plugin__probe_Plugin'`. Fresh batch failed with the same loader-stage error. The watchdog itself shut down with exit 0; the file worker failed.
4. Two fresh-process negative controls used an invalid short Mach-O replacement and a deleted dylib. Both failed before proof evaluation at explicit plugin load. The invalid file produced a `dlopen` invalid-Mach-O error.

No proposition change was attempted during plugin replacement; these cases distinguish a retained proof worker from a newly initialized worker, not proof semantic drift. The marker records the most recent initializer write and is not a complete per-process load log.

## Issue coverage and residuals

- **I120:** Directly exercises an imported tactic/macro in a prepared module, plus per-family pruning. It does not exercise additions to an actual generated Anneal proof workspace, multiple imports, or a plugin-defined tactic that changes a theorem's meaning.
- **I125:** Directly exercises a real Lean-built native plugin load, valid binary replacement, wrong initializer symbol, malformed binary, and missing file. The actual Lean plugin API may accept other ABI-incompatible binaries with different failure modes; no cross-toolchain or system-library ABI change was tested.
- **I150:** Shows that artifact sufficiency differs for `lake --no-build build`, `lake setup-file`, direct batch with explicit plugin, batch without it, and old/new server file workers. It does not define a minimum complete prepared archive or a safe cleanup policy. The `.olean/.ilean/.c` setup calls were allowed to rebuild inside the disposable copy.

The valid v2 case used the same module name and initializer symbol, so it demonstrates binary-generation transition without deliberately breaking the interface. The wrong-name `Alien` case is the bounded ABI-negative control. Dynamic libraries are never unloaded in this Lean implementation, but this run did not inspect memory mappings or test safe deletion after worker exit. No real Anneal MCP behavior follows from these direct Lean/Lake outcomes.

## Evidence and replay

[`support/probe.py`](support/probe.py) creates only its own `support/work`, builds tiny fixtures, runs the sequential matrix and server protocol, and writes [`support/transcript.json`](support/transcript.json). Acquired transcript: 224 ordered events, SHA-256 `9d26d845e404706a93e9ee5ff8a95261cb8fb54a553966b4d2a0299464c4b581`. Probe SHA-256 `fb824c4a0549cd72ace1bc872152c5042438dff22df0afa532ab38e42abf48cc`. [`support/summarize.py`](support/summarize.py) asserts the exits, stage signals, plugin markers, worker result, and artifact restoration; it passed and wrote [`support/summary.json`](support/summary.json). Full raw paths, argv, stdout/stderr, RPC messages, source and binary identities, and sequence timing are in the transcript. A replay may produce different dylib byte hashes due to native build identity and should compare semantic outcomes and control stages.

From this directory, with the pinned toolchain already installed, run `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/probe.py` and then `python3 support/summarize.py`. The probe replaces only `support/work`, `support/transcript.json`, and on subsequent summary the `support/summary.json` file. It requires the native macOS compiler toolchain that Lake uses for the dylib facet. No catalog, matrix, index, staged change, commit, or publication is part of this package.
