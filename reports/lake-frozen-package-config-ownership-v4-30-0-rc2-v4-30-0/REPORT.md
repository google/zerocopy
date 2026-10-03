# Frozen Lake path-package replay: 4.30.0-rc2 versus 4.30.0 final

## Summary

In a 24-run, two-package synthetic matrix on macOS arm64, both exact Lean/Lake
tuples replayed a prepared, read-only dependency across changes to the
**consumer** path/depth and root package name. Final Lean/Lake 4.30.0 also
loaded that dependency after dependency ordering changed or the consumer
manifest was absent, keeping compiled configuration state under the consumer.
4.30.0-rc2 instead attempted a lock-file write under the frozen dependency
and failed in those two cases. Neither tuple made `--no-build` an immutable
dependency policy: after one required dependency OLean was removed from a
separate frozen scratch copy, both attempted a dependency-local
`Shared.trace.nobuild` write and exited 3.

This demonstrates that the compiled-configuration ownership change was
present in **final 4.30.0**, not only in later 4.31 or 4.34 releases. It is a
small-fixture result, not proof that an arbitrary prepared archive remains
fully immutable under every Lake path.

## Applicability

The compared subjects are `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
(`v4.30.0-rc2`) and `@d024af099ca4bf2c86f649261ebf59565dc8c622`
(`v4.30.0` final), each with its **own** producer OLean, configuration cache,
and source tree. The source files were identical in meaning, but artifacts
were never reused across compiler hashes. Their `Shared.trace` hashes were
`8569e9315b04983e` and `b885d924048f9691`, respectively. The runtime
identity is present in each trace's `Lean 4.30.0, commit ...` input. The two
small launcher binaries happened to have matching bytes across extracted
tuples; the linked runtime libraries differed. The compiler commit, not just
launcher SHA-256, identifies the executable behavior here.
The measured launcher and runtime hashes are retained in
[runtime-identity.json](runtime-identity.json).

The fixture has `probe_shared` (`Shared.lean` defines `sharedValue : Nat := 7`),
`probe_pad` (a second package to vary workspace index), and a local consumer
`Client.lean`. Both dependencies use Lean DSL configurations and local path
`require`s. A primer workspace compiled each tuple's producer once; the two
producer source directories were then made read-only. All later consumer
commands were serial, used `lake --keep-toolchain --no-cache --verbose`, and
had a private workspace. Manifests, when present, used relative path entries.
The path/depth cases moved the **consumer** only; the producer itself was not
relocated. The `--old` case used a separate fresh consumer so prior commands
could not repair it.

## Findings

### Prepared hash replay survives consumer path and root-name changes

For each tuple, fresh same-context consumer `a`, deeper `nested/deeper/b`, and
renamed-root consumer `name` exited 0. Each logged `Replayed Shared`, and the
producer's `Shared.trace` `depHash` remained byte-identical to its primer
value: `8569e9315b04983e` at RC2, `b885d924048f9691` at final. The complete
read-only producer inventories before and after each command were identical.
The consumer built its own `Client` output. This is direct hash replay with
normal Lake mode, not the separate `--old` timestamp fallback. Basis:
**execution**, corroborated by both tuples' `Module.recFetchInput` and
`Module.recBuildLean` source regions in [source-map.json](source-map.json).

### Final 4.30 owns compiled configuration under the consumer

Changing both `require` and manifest ordering, or starting a fresh consumer
without a manifest, caused RC2 to attempt writes to a frozen dependency's
`.lake/config/<assigned-name>/lakefile.olean.lock`; both commands exited 1
with permission denied. The read-only dependency inventories stayed identical
because the attempted writes were blocked. In the same two cases at final
4.30, the commands exited 0, logged `Replayed Shared`, made no observed
dependency mutation attempt, and recorded compiled configuration traces under
the consumer's `.lake/config/<workspace-index>/` directory. For example, the
final reordered consumer held traces at `work/index/.lake/config/{0,1,2}`;
RC2's existing dependency traces remained at
`source/probe_shared/.lake/config/probe_shared` and
`source/probe_pad/.lake/config/probe_pad`.

The implementation explains this split. RC2's `importConfigFile` derives
`configDir` from package-local `cfg.lakeDir`; final derives it from
`cfg.configDir`, defined as `cfg.wsDir / .lake / config / cfg.pkgIdx`. Both
versions' cache validity includes workspace-assigned package index and name,
so changed assignment makes RC2's dependency-local cache stale. Final keeps
that mutable cache at the root workspace. Basis: **source + execution**;
[`LoadConfig` and `importConfigFile`](source-map.json) give the exact paths and
line anchors. The final code still has a missing-trace branch that calls
`createDirAll cfg.lakeDir`; the observed success concerns these prepared
producer trees, whose `.lake` already existed, not a pristine tree without it.

### Local edit/no-op and `--old` controls

After `a` succeeded, changing only `work/a/Client.lean` from `sharedValue + 1`
to `sharedValue + 2` rebuilt `Client` and replayed `Shared` on both tuples.
A second build logged `Replayed Client` and `Replayed Shared`. Producer
inventories stayed identical. A separate fresh `--old build Client` succeeded
at each tuple, but that success alone is not evidence of normal hash replay.
Basis: **execution** in [observations.json](observations.json) and
[state-snapshots.json](state-snapshots.json).

### Missing required OLean still reaches a shared write under `--no-build`

A dedicated source-package copy was primed and shown healthy for each tuple.
Only its `Shared.olean` was then removed; the damaged copy was frozen, and a
new consumer ran `--no-build build Client`. Both versions exited 3 and
attempted to write
`probe_shared/.lake/build/lib/lean/Shared.trace.nobuild`, receiving permission
denied. Their producer before/after inventories were again identical. Thus
`--no-build` signals a build demand but still uses a producer-local diagnostic
trace path; it does not promise read-only operation when an expected artifact
is absent. The `noBuildTraceFile` branch in `Lake/Build/Common.lean` corroborates
the observed path. Basis: **source + execution**.

## Boundaries

This report covers one tiny Lean-DSL path-dependency graph, a compatible
prebuilt producer per compiler, local `build Client`, macOS arm64, and serial
commands. It does not cover the full Aeneas/Mathlib archive, native plugins,
server workers, concurrency, network-backed packages, TOML configuration,
other platforms, or all Lake artifact families. A prepared `.lake` directory
was present; the final source's package-local `createDirAll` call means the
result cannot be generalized to a wholly pristine frozen checkout. The
`--no-build` negative used a separate scratch producer copy and deliberately
removed its OLean; no real archive artifact was deleted.

The tracer interposed selected mutation and network operations and was not
exhaustive syscall tracing. The full before/after inventories provide a
stronger unchanged-state check for each of 20 consumer cells, including
relative paths, file types, modes, sizes, nanosecond mtimes, SHA-256 hashes,
and symlink targets. A passing comparison still cannot exclude an unobserved
transient write that was later perfectly restored. Resource samples are
periodic, not instantaneous peaks.

The earlier [I094 installed-tuple report](../i094-lake-readonly-consumer-server-430rc2-to-4341-2026-10-01/REPORT.md)
compared RC2 with **4.34.1** and included `setup-file` and a live server. This
report narrows the version boundary to **final 4.30.0** for this configuration
ownership case. It does not infer behavior for 4.31, 4.34, or their server
protocol from adjacent version numbers.

## Evidence

The primary retained [observations](observations.json) contain all 24 cells
(two preparation runs plus ten consumer cells per tuple), command arguments,
exit/abort status, concise stdout/stderr, source/config trace fields and
original hash values, observed mutation/network attempts, and resource
summaries. [State snapshots](state-snapshots.json) retain complete producer
inventories before and after every consumer cell; these are small JSON data,
not binary artifacts. Absolute paths under the original validation directory
and the two toolchain directories were replaced by `${RUN_ROOT}`,
`${RC2_SYSROOT}`, and `${FINAL_SYSROOT}` in string fields. The substitution is
documented in `observations.json`; trace hashes and snapshot hashes, modes,
sizes, and mtimes were not transformed. The actual source texts and manifest
shape are regenerated by [repro.py](repro.py).

The [source map](source-map.json) names both immutable Lean commits, pinned raw
source URLs, SHA-256 of each retrieved source file, and exact anchors in
`Load/Config.lean`, `Load/Lean/Elab.lean`, `Build/Module.lean`,
`Build/Common.lean`, and related build/dependency files. RC2 lacks the
`LoadConfig.configDir` definition that appears at final. Source was read at
these exact commits on 2026-10-03; the execution matrix was also observed
2026-10-03.

All 24 guarded commands completed without an abort. The largest sampled
process-group RSS was 1,003.359 MiB; minimum sampled host free memory was
30%, minimum free disk 26.884 GiB. The controller had a 1.5 GiB group RSS
limit and memory/disk floors; no observed network attempt occurred. Its
24 command durations summed to 15.791 seconds, which is fixture accounting,
not a performance comparison.

## Revalidation

Run `python3 -B check.py` from this package. The offline checker asserts the
24-case outcome matrix, exact compiler identities, hash replay across the
named consumers, RC2 versus final configuration paths, local edit/no-op logs,
both `--no-build` missing-artifact failures, resource bounds, and exact
equality of all 20 producer before/after inventory pairs. It does not invoke
Lean or Lake.

For a new exact tuple, use [repro.py](repro.py) to generate a fresh tiny graph,
prime its producer with that tuple, freeze it, and rerun the few discriminating
cases: normal, path-depth, root-name, reordered dependencies, no manifest,
local edit/no-op, and damaged-copy `--no-build`. Record a new immutable
compiler identity and state snapshots; do not reuse these OLeans across
versions or infer changed behavior from this report without rerunning.
