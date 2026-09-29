# Lake consumer identity collisions and observable build actions at Lean 4.30.0-rc2

## Summary

In a small offline Lake graph, two consumers of the **same physical dependency tree** collided in dependency-owned compiled-configuration state when they assigned different workspace indices. The first consumer left `producer/.lake/config/probe_dep/lakefile.olean.trace` with `idx = 1`; adding another dependency before `probe_dep` changed that same trace to `idx = 2`; a third consumer changed it back to `idx = 1`. All three builds reported `Replayed Dep`. Lake's module replay therefore did not imply that loading the prepared dependency was free of shared configuration writes. Assigning a different dependency name created a second producer configuration slot instead. A two-producer control found that direct duplicate `require` declarations with the same assigned name fail before loading either producer; transitive wrappers loaded one physical producer chosen by the complete root manifest.

For reuse observability, a clean build reported `Built Dep`, a repeat reported `Replayed Dep`, and a same-mtime source mutation made `--rehash --no-build` exit 3 before a subsequent rebuild changed the OLean and trace bytes. A bounded `ps` poll directly observed a Lean child during the clean build and rebuild. The `-v` output on a **replay** still printed the earlier `lean ... Dep.lean` command from the saved build log, though no child was captured in replay polls. That historical line is not proof of a new Lean process. Before/after file inventories show net changes, not reads or every transient write.

This is additional executed component evidence for #3730 F01/F05/F10 and #3731 I090/I095. It is not a complete prepared-environment schema or a real-archive consumer run.

## Applicability

The subject is Lake and Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, on macOS arm64 (`arm64-apple-darwin24.6.0`). The local `lake` and `lean` binaries had SHA-256 values `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997` respectively. The fixtures were local one-module packages with complete path manifests, no remote dependency, `LAKE_ARTIFACT_CACHE=false`, `LAKE_NO_CACHE=1`, `--no-cache`, `LEAN_NUM_THREADS=1`, and separate empty home/cache directories. Each of 21 sequential Lake calls had a 30-second limit; there was no installation or download.

`producer` declares `probe_dep` and defines `depValue := 7`; the consumers import `Dep`. `dummy` is a second path dependency used to change `probe_dep`'s workspace position. All variants point at the same physical `producer` directory. The script's fixture source, exact command/output records, producer configuration-trace snapshots, and file deltas are retained in `support/`.

The duplicate-name extension instead has two physical producers: A declares `probe_dep` version `1.0.0` and value 7; B declares `probe_dep` version `2.0.0` and value 9. Direct duplicate declarations and two wrapper-mediated graph orders probe different resolution stages. In the wrapper cases the root manifest contains one explicit `probe_dep` path entry, selected independently of wrapper declaration order.

## Findings

### Assigned name and workspace index affect dependency-owned configuration state

| Consumer change | Producer configuration observation | `Dep` module action |
| --- | --- | --- |
| Initial `probe_dep` dependency | `.lake/config/probe_dep/lakefile.olean.trace` has `name=probe_dep`, `idx=1` | Built |
| Same tree assigned `dep_alias` | New `.lake/config/dep_alias/lakefile.olean` and trace, with `name=dep_alias`, `idx=1` | Replayed |
| `probe_dep` follows `dummy` in resolved graph | Existing `probe_dep` configuration OLean and trace bytes change; trace has `idx=2` | Replayed |
| Root moved one directory deeper, `probe_dep` first again | Same `probe_dep` configuration OLean and trace bytes change; trace returns to `idx=1` | Replayed |

The alias's configuration trace has the same `configHash` as the original (`ba08543c33d179c7`), while its `name` differs. The index shift changes the trace's `idx` without changing that configuration hash. This directly distinguishes physical package location and source configuration bytes from Lake's workspace-relative loaded-package identity. It also shows that one shared prepared tree can receive configuration writes during another consumer's ordinary build even when its compiled module is replayed. **Basis: execution**, `support/results.json` `snapshots.*_config_traces` and per-call `delta`/monitor output; interpretation of the fields is supported by pinned Lake `LoadConfig` and `ConfigTrace` source.

The nested consumer used a different relative dependency path (`../../producer` instead of `../producer`). Its own build products were new. Its action was `Replayed Dep`, but the producer configuration was rewritten from index 2 back to 1. The isolated contribution of path depth to a cache key is not established by that call because the preceding call deliberately changed the index. **Basis: execution**.

### One assigned name selects one physical producer in this fixture

| Duplicate-source shape | Outcome | Artifact/config observation |
| --- | --- | --- |
| One root directly requires A then B as `probe_dep` | Exit 1, `` `probe_dep` has already been declared `` | Neither producer acquires a config or module artifact |
| One root directly requires B then A as `probe_dep` | Same exit/error | Neither producer acquires a config or module artifact |
| Root requires wrapper A then wrapper B; root manifest maps `probe_dep` to A | Exit 0; `#eval depValue` prints 7 | Producer A acquires config and `Dep.olean`; B remains untouched |
| Root requires wrapper B then wrapper A; root manifest still maps `probe_dep` to A | Exit 0; prints 7 | B remains untouched; wrapper configuration slots are rewritten for the new root identity |
| Root requires wrapper A then wrapper B; root manifest maps `probe_dep` to B | Exit 0; prints 9 | Producer B acquires config and `Dep.olean` |

The direct form is rejected while elaborating the consumer's package configuration. The wrapper form requires a complete **root** manifest entry for the transitive `probe_dep`: an exploratory incomplete-manifest run failed with “dependency `probe_dep` of `wrapper_b` not in manifest,” and the retained control supplies that entry. Reversing wrapper order while holding the manifest entry at A did not change the chosen value; changing the manifest entry to B while holding order fixed did. In this fixture the root manifest selected which physical tree satisfied the one assigned name. It does not establish general version-conflict resolution or prove Lake validates that wrapper B's declared source matches the root's selected source. The source value and version changed together, so the effect of version alone was not isolated. **Basis: execution**, final retained `support/results.json` duplicate/transitive calls, output values, per-producer deltas and config snapshots.

For a 4.30 prepared-environment contract, the directly observed state at least includes the dependency tree's compiled configuration OLean/trace and module output/trace files, the consumer's own compiled configuration and outputs, complete path manifest, the resolved assigned names and indices, and the exact toolchain/platform recorded in the configuration trace. `setup-file` returned the producer OLean in `importArts.Dep`. The broader server/RPC/native-plugin schema remains in the existing [Lake server preparation report](../lake-server-preparation-v4-30-0-rc2/REPORT.md) and needs real-consumer execution. **Basis: execution + source/derived**; this is a lower bound, not a complete schema.

### Lake's action text and filesystem deltas answer different questions

| Control | Lake result | Net filesystem observation |
| --- | --- | --- |
| Clean `build Generated` | Exit 0; `Built Dep`, `Built Generated` | Producer and consumer build/config files added |
| Repeat `build Generated` | Exit 0; `Replayed Dep`, `Replayed Generated` | No added, removed, byte-changed, or mtime-only files in the scoped fixture |
| Repeat `--no-build build Generated` | Exit 0; replay actions | No net file changes in the scoped fixture |
| Change `Dep.lean` from 7 to 8 while restoring its mtime; `--rehash --no-build build Dep` | Exit 3; `Building Dep` followed by out-of-date error | `Dep.trace.nobuild` added; no new `Dep.olean` |
| `--rehash build Dep` after the mutation | Exit 0; `Built Dep` | `Dep.olean`, `Dep.trace`, generated C and hash-sidecar bytes changed |
| Repeat `build Dep` | Exit 0; `Replayed Dep` | No net file changes |

The `--no-build` failure demonstrates a required builder action was reached under the selected rehash mode; its `.trace.nobuild` write is a concrete counterexample to interpreting no-build as no-write. The first replay's verbose output included the exact older Lean command even though Lake classified the action as `Replayed Dep`. A `ps` poll of Lake descendants captured `$TOOLCHAIN_BIN/lean` during the clean build and rebuild, and none during either selected replay. The poll supplies positive process evidence for those two builds; its missed-process possibility means the empty replay samples are not an exhaustive absence proof. The trace log is historical command text; counting those lines as process launches would falsely count a replay as a build. **Basis: execution**, exact stdout, sampled descendants, and deltas in `support/results.json`; source details of `JobAction`, monitor logging, and no-build are in [Lake reuse/rebuild observability](../lake-reuse-rebuild-observability-v4-30-0-rc2/REPORT.md).

Two deliberately narrow controls did not validate stronger F05 dimensions. Changing an **unused** `-Kprobe` option from `one` to `two` made no net file change and returned the same setup JSON. That says nothing about an option actually read by a package configuration. Editing `moreServerOptions` recompiled the consumer configuration OLean and trace, but this fixture's `setup-file` result still had `options={}` and `isModule=false`; it cannot establish server-option reuse. **Basis: execution**.

## Boundaries

- **F03 later-version gate:** only Lean 4.29.0 and 4.30.0-rc2 were cached locally. No Lean 4.31+ binary was installed or downloaded for this investigation. The same consumer matrix has not been executed on the 4.31 ownership change, so this report does not validate removal of any 4.30 workaround. The [4.31 source report](../lake-configuration-ownership-v4-31-0/REPORT.md) remains source-level evidence of a different placement rule.
- **F04 real-archive gate:** no actual built Anneal omnibus archive was available in the local inventory. This package uses synthetic path dependencies. The separate [archive availability and manifest-gate report](../anneal-3730-real-archive-manifest-gate-2026-09-29/REPORT.md) records that bounded availability check; F04 remains unexecuted on Aeneas/Mathlib.
- The fixture did not exercise two simultaneous consumers, a physically read-only producer, a remote or local artifact-cache hit, dependency resolution from Git, `lake serve`, an LSP/RPC goal, native plugins/dynlibs, or a real Anneal generated workspace. It did not isolate source changes from package-version changes in the duplicate-name control.
- No system-call read/write trace was obtained. `fs_usage` on this host required root; no elevated tracing was attempted. A sampled descendant-process poll can establish a process it catches, but cannot prove an absent short-lived process. Hash/size/mtime inventories are scoped to the synthetic work tree and cannot detect reads, transient writes that leave the same final state, network attempts, or writes elsewhere. `-v` action labels are Lake's summaries, not a complete event stream.
- Platform and Lean-hash collision dimensions were observed only as fields in the persisted configuration trace, not varied by execution. The `-K` control used an unconsumed option. The server-option control did not return an effective changed option. No safe sharing rule for those dimensions follows from this matrix.
- The same-mtime source mutation was detected under explicit `--rehash`; this does not show default hash-sidecar behavior for that mutation or semantic correctness of all outputs.

## Evidence

- `support/probe.py`: deterministic local source/control fixture and 21 bounded, offline Lake calls. It records command, exit, stdout/stderr, timing, fixture file deltas, selected configuration traces, and a `ps` descendant sample during four selected calls. Local work paths and toolchain-bin prefix are replaced by `$WORK` and `$TOOLCHAIN_BIN` in retained output.
- `support/results.json`: raw selected run transcript and hashes. Its `snapshots` show `probe_dep` index `1 → 2 → 1`; the `runs` list gives file deltas and action output for each step.
- `support/check.py`: checks the distinguishing retained observations, including the alias slot, index rewrite, direct duplicate-name error, root-manifest-selected values 7/9, action transitions, no-build exit 3 and `.trace.nobuild`, and changed OLean after rebuild.
- Pinned implementation coordinates: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `src/lake/Lake/Load/Config.lean` (`LoadConfig`), `src/lake/Lake/Load/Lean/Elab.lean` (`ConfigTrace`/configuration cache), `src/lake/Lake/Config/Package.lean` (`Package.keyName`), `src/lake/Lake/Build/Job/Basic.lean` (`JobAction`), `src/lake/Lake/Build/Common.lean` (`buildAction` and no-build path). Source interpretation is also documented in the linked corpus reports; the new collision and command-log observations here are execution evidence.

## Revalidation

Run `python3 support/check.py` for retained-result consistency. To repeat the component experiment with the exact cached toolchain, run `python3 support/probe.py --lake /absolute/toolchain/bin/lake --lean /absolute/toolchain/bin/lean --work /new/absent/scratch/path --output /new/result.json`; the work path must not exist. Compare action classes, configuration trace name/index, duplicate-name errors, selected values 7/9, and file-delta classes, rather than absolute paths or timings. The generated work tree was omitted from the report; the script recreates every fixture file.

For F03, obtain an independently identified 4.31+ toolchain and rerun the same assigned-name/index/root cases with producer and consumer write inventories. For F04, obtain the actual content-identified prepared Anneal archive and matching generated consumer, then repeat complete-manifest and missing-manifest cases before any Lake load. For F10 process/read provenance, use a permitted syscall/process tracing facility around the Lake process and descendants, correlate that trace with action labels and snapshots, and retain positive controls for compiler execution and file reads.
