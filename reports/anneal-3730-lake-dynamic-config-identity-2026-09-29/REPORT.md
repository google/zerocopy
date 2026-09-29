# Pinned Lake dynamic configuration, timestamp, trace, and setup identity

## Result and boundary

On pinned Lean/Lake 4.30.0-rc2, five tiny clean producer/consumer cells compared an executable Lean `lakefile.lean` with static `lakefile.toml` and a static Lean option variant. The deliberately adversarial Lean configuration used `run_cmd` to read `PROBE_CONFIG_VALUE` and write its private `Dep.lean` as `depValue := 7` for `A` or `9` for `B`. Clean `A` and TOML value-7 builds produced the same `Dep.olean` SHA-256 `cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b`; clean `B` and TOML value-9 produced `fe893ce3c24d2c295ade06017eb859638f0e75aa29df7e9444f3026bfd7a7745`. Their respective `Dep.trace` bytes differed by configuration form. The static Lean option variant produced the value-7 OLean again, but its `Dep.setup.json` differed from baseline.

Changing **only** `PROBE_CONFIG_VALUE` from `A` to `B` in the already built Lean-configured root did not cause the cached configuration to execute its source-writing `run_cmd` again. `lake --no-build build Dep`, `setup-file`, direct local batch, setup-artifact batch and a fresh direct server all continued to observe value 7 and the value-7 OLean. A separately clean `B` root wrote value 9; its fresh batch/server correctly rejected a theorem expecting value 8 and evaluated 10. This is a selected **hidden configuration input** control, not a claim that Lake promises to track arbitrary `IO.getEnv` calls in executable configuration. A preparation contract that treats the current environment value as part of source identity must materialize or attest it explicitly.

Three byte-preserving timestamp changes shifted producer-source mtime one day older and newer and trace mtime one day newer. In each, no-build, setup-artifact batch and direct local batch exited zero and used the same value-7 OLean. In contrast, rewriting source bytes from value 7 to 9 while restoring exactly the old source nanosecond mtime made the no-build call fetch the value-9 cache entry. `setup-file` returned the value-9 OLean and its fresh import rejected the expected-8 theorem; the conventional local `Dep.olean` was absent after the fetch, so direct local batch failed with an unknown module prefix. The byte/mtime result is specific to this selected Lake path and cache state; it is not a universal mtime-insensitivity guarantee.

Two valid metadata replacements started from a restored value-7 local tree. Copying a value-9 `Dep.trace` over the value-7 trace caused no-build to fetch the value-7 cache object and return success. Setup returned the baseline OLean while the conventional local OLean was then absent; direct local batch failed to import. Copying the static-option generation's valid `Dep.setup.json` instead left no-build, setup, and local batch successful, with the baseline OLean consumed. These cases show that a no-build success and a direct local import do not necessarily name the same bytes; they do not establish a complete validator for every trace or setup family.

This is **component execution** in tiny private local packages, not an Anneal prepared archive, a general cache-key proof, or a recommendation to use config-time file writes. The four direct Lean watchdogs returned diagnostic results and were then forcibly torn down (`-9`), so they do not demonstrate graceful server lifecycle.

## Procedure and exact evidence

The host was macOS arm64 with 8 GiB RAM; the preflight system-wide free-memory reading was at least 35% and free disk exceeded 15 GiB. The local `lake` SHA-256 is `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; `lean` is `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The harness used one isolated `LAKE_CACHE_DIR`, private roots, `LEAN_NUM_THREADS=1`, an isolated home, at most one command at a time and a 25-second limit per CLI call. It disabled the artifact cache for each initial local compile, then enabled it for cache publication and subsequent operations. No dependency was installed or downloaded.

`support/results.json` retains 57 labelled command/server records with arguments, chosen dynamic environment value, artifact-cache setting, exit status, normalized stdout/stderr, and snapshots of source/config/manifest/trace/setup/OLean/ILean/C bytes and nanosecond mtimes. `support/artifacts/` holds the five clean cells' exact source/config/trace/setup/OLean/consumer specimens and the original value-7 files used to restore between perturbations. `support/probe.py` regenerates the fixture under an absent owned scratch root. `support/check.py` verifies archived file bytes and outcomes without launching Lake.

| Cell/control | No-build `Dep` | Setup-returned OLean | Direct local batch | Fresh direct server |
| --- | ---: | --- | ---: | --- |
| Clean dynamic Lean `A` | Initial build | Value 7 | 0, value 8 | Value 8, no theorem error |
| Clean dynamic Lean `B` | Initial build | Value 9 | 1, expected 8 false | Failed theorem, value 10 |
| Clean static TOML value 7 | Initial build | Value 7 | 0, value 8 | Value 8, no theorem error |
| Clean static TOML value 9 | Initial build | Value 9 | 1, expected 8 false | Not queried |
| Clean static Lean option value 7 | Initial build | Value 7 | 0, value 8 | Not queried |
| Already built dynamic `A`, environment changed to `B` | 0 | Still value 7 | 0, value 8 | Still value 8 |
| Source mtime ±1 day; trace mtime +1 day, bytes unchanged | 0 in all three | Still value 7 | 0 in all three | Not queried |
| Valid value-9 trace replacing value-7 trace | 0, fetched value-7 cache object | Value 7 | 1, local OLean absent | Not queried |
| Valid option-generation setup JSON replacing value-7 setup | 0 | Value 7 | 0, value 8 | Not queried |
| Value-9 source bytes with original value-7 mtime | 0, fetched value-9 cache object | Value 9 | 1, local OLean absent | Not queried |

The server cells used explicit local `LEAN_PATH` in isolated source directories without a Lake project; the setup-artifact batch checks separately imported the exact OLean path returned by `lake setup-file`. The table's server entries are diagnostic publications observed before bounded forced teardown. The public source snippets in `support/artifacts/` are selected byte evidence; no private workspace source is included.

## Investigation coverage and exact residuals

| Row | Bounded contribution | Remaining delta |
| --- | --- | --- |
| I089 | Private clean/config/cache consumers and fresh setup/batch/server controls. | Real Anneal archive from empty home/cache, read-only dependency universe, first-goal writes and producer removal. |
| I090 | One relative two-package graph in Lean and TOML forms. | Duplicate name/version/order/rename graph collisions and exact package identity. |
| I091 | File-specific setup-returned object contrasted with local search-path import. | Attested setup and loaded import choice for a current or unsaved live document. |
| I092 | No-build accepted selected mtime/trace/setup/source-key states, sometimes returning a cache object without a local OLean. | Full no-build/no-cache contract across generated archive/config/native/server operations. |
| I093 | Executable Lean configuration read environment and wrote source; TOML static cells and a Lean option variant were compared. | Representative dynamic configuration and graph inputs, explicit input declaration policy, and wider Lean/TOML equivalence. |
| I094 | One pinned Lake/Lean revision. | A selected compatible later revision, migration and prior workaround deletion. |
| I095 | Cache fetch appeared in no-build logs and setup returned its object. | Process read/write tracing, effective parallelism, larger graph and physical reuse accounting. |
| I096 | Exact Lake/Lean binaries, home/cache selector, cwd and dynamic environment captured. | CLI/editor/MCP/CI discovery and actual worker environment attestation. |
| I097 | Selected source/config/env/path and valid metadata perturbations with exact OLean identity. | Sufficient cache-key policy for all model/tool/flag inputs and integrity checks at every consumer. |
| I098 | Setup, trace and OLean family interaction tested in one tiny graph. | Coherent native/plugin/ILean/C/setup/server families across generations and actual generated project. |
| I099 | Fresh clean Lean/TOML value-7 cases agree on selected OLean/proof; setup/local placement divergence exposed. | Complete clean-versus-prepared declarations, assumptions, goals, diagnostics and loaded-byte equivalence. |
| I100 | Byte-preserving source/trace mtime shifts and a same-mtime source-byte change with cache fetch. | More source-order/trace-normalization, clock-skew, directory and revision perturbations on real graphs. |
| I101 | Private copied paths and setup-returned object identity. | Producer-removed relocated Anneal environment, native paths and retained workers. |
| I102 | Valid trace/setup replacements but no interrupted writer in this run. | Concurrent publication and all interruption/restart/durability phases; R10 has narrower partial-object controls. |
| I103 | Changed metadata generation under one local package label. | Archive install replacement and attested consumed identity across same-label versions. |
| I104 | Local fixture without downloads. | Enforced network denial and producer/consumer filesystem-attempt tracing. |
| I108 | One operation at a time. | Cross-component lock order, shared-writer restart and GC schedules. |
| I109 | Per-command timeout and preflight guards. | Memory/disk/fd/process exhaustion with Anneal last-good recovery. |

No result validates Rust-to-Lean proof correspondence or a theorem's complete obligation set. The clean `B` and TOML value-9 theorem failures are intentional negative controls, not tool failures.

## Reproduction and validation

From this package run `python3 support/check.py`; it checks retained bytes, all twelve cases, the four server diagnostic observations and 57 command records offline. To reacquire on the pinned host, run `python3 support/probe.py --work /absolute/absent/owned/scratch-directory`. The script replaces only this report's `support/results.json` and `support/artifacts/`; it requires the already cached binaries and writes all scratch work under the supplied private root. Compare selected values, exits, consumed OLean hashes and exact metadata/mtime relations on replay; path-bearing trace bytes and timings can differ. The direct server watchdogs are forcibly stopped after responses, and that teardown is not a test of graceful cancellation.
