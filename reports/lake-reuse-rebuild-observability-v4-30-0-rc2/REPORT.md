# Machine-observable Lake reuse versus rebuild evidence at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake exposes several useful but differently scoped signals for distinguishing reuse, cache fetching, and rebuilding. No single inspected signal proves every property Anneal might mean by “this build reused prior work.”

The strongest direct signal for **whether Lake needed to enter an ordinary build action** is `--no-build`. The generic build path sets `wantsRebuild` and refuses to execute the builder when an out-of-date target reaches `buildAction`; the CLI uses exit code 3 for that condition. `Workspace.checkNoBuild` exposes the corresponding question programmatically. This is valuable evidence that a required build action would or would not be needed, but it is not a dry-run guarantee. Artifact-cache lookup, download, restoration, `.hash` writes, synthetic trace writes, and some other work can occur before the builder would have been invoked. An exit code of 0 therefore does not prove that all outputs already existed locally, that nothing was written, or that no network access occurred.

Lake also tracks a per-job `JobAction`: `unknown`, `replay`, `fetch`, or `build`. The build monitor renders these as `Ran`, `Replayed`, `Fetched`, and `Built`. With non-ANSI verbose output, those action lines provide a useful execution transcript for ordinary debugging and probes. They are not a complete structured audit log: job-state merges retain only the maximum action, the monitor filters successful jobs according to verbosity and ANSI mode, and custom or composite jobs can collapse multiple lower-level events into one reported action.

Persisted `*.trace` files give a third signal. A normal successful builder writes `BuildMetadata` with `synthetic = false`, the dependency hash/input tree, output description, and build log. A cache fetch can write metadata with `synthetic = true`, the same input hash and output description, but an empty input tree and log. This records how that trace was created, not what every later invocation did. A later replay can leave the trace unchanged, and a later build can overwrite a synthetic trace.

For Anneal, a high-confidence reuse/rebuild probe should therefore collect several observations together: stable non-ANSI verbose action output, the `--no-build` result when testing “would a builder run?”, before/after ordinary trace metadata, cache/restoration evidence, and independent output-byte hashes when content identity matters. The probe must also fix the freshness mode and cache/network policy it is trying to test. Otherwise “reused” can silently conflate local trace replay, local artifact-cache substitution, remote artifact fetch, old-mode mtime acceptance, and an actual rebuild.

Basis: exact pinned Lake source and same-revision Lake CLI documentation. No fresh Lake process was executed for this report.

## Applicability

This report applies to Lake shipped in Lean `v4.30.0-rc2`:

- repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- component: Lake incremental build runner, trace/cache machinery, and CLI

The subject is deliberately narrower than build correctness or clean/cache-seeded equivalence. It asks what an automated Anneal test can observe to decide whether Lake replayed prior build state, obtained an artifact from a cache, or executed a build action.

The report uses three terms:

- **replay**: Lake accepts existing traced output as current and records the job action as `replay`;
- **fetch**: Lake satisfies work through a cache/download path and records `fetch`;
- **build**: Lake enters a builder action and records `build`.

Those are Lake's internal action categories, not a claim that every physical filesystem or network operation maps one-to-one to exactly one category. In particular, artifact restoration and trace/hash writes can accompany a fetch path.

The exact source contains both a package-build-cache control (`LAKE_NO_CACHE` / `--no-cache`) and a distinct local artifact-cache facility (`LAKE_ARTIFACT_CACHE` and package/workspace artifact-cache settings). A probe must state which mechanism it is enabling or excluding rather than treating “cache” as one switch.

## Findings

### `--no-build` answers whether a required builder action is reached

`BuildConfig.noBuild` is documented as an early exit when a target has to be rebuilt. The decisive generic check is in `buildAction`.

When an out-of-date target reaches `buildAction`, Lake first records the requested `JobAction` and then checks `noBuild`. If `noBuild` is enabled, Lake:

1. sets `wantsRebuild := true`;
2. if the ordinary trace file already exists, writes a sibling `.trace.nobuild` containing the current expected dependency trace; and
3. raises `target is out-of-date and needs to be rebuilt` instead of executing the builder.

The top-level runner reserves exit code 3 for the no-build/rebuild-needed condition. `Workspace.checkNoBuild` describes itself as equivalent to asking whether `lake build --no-build` exits with code 0.

For an ordinary required target, this is the cleanest exact-pin test of the proposition **“would Lake need to enter a builder action under this build configuration?”**

It is not a stronger proposition such as “the process made no changes.” Work can happen before `buildAction`, and optional-job failures are not treated as required build failures by the monitor. A test should therefore record the exact target set and whether optional jobs matter to its acceptance criterion.

Basis: **source** in `Lake/Build/Context.lean`, `Lake/Build/Common.lean`, and `Lake/Build/Run.lean`.

### A no-build success does not distinguish replay from cache satisfaction

Artifact-aware build paths attempt reuse before falling through to `buildAction`.

`buildArtifactUnlessUpToDate` computes the current input hash and reads the saved trace. Depending on package/cache configuration, it can resolve a matching cached output, restore that artifact to a local build path, write or refresh hash state, and write a synthetic fetch trace. Only when those routes fail and the existing output is not current does it call the builder.

Consequently, a successful `--no-build` invocation can mean materially different things:

- an existing local output and ordinary trace were replayed;
- a matching artifact already existed in Lake's local artifact cache;
- a cache artifact was resolved and restored into the build tree;
- a configured cache service supplied a missing artifact; or
- a combination of those operations satisfied dependencies without reaching a builder.

This is why `--no-build` is a good **build-action gate** but a poor standalone **reuse provenance** signal.

A test that specifically wants “preexisting local output was accepted without cache substitution” must constrain or independently observe the cache path. A test that merely wants “no compiler/build action was necessary” can use the no-build result directly.

Basis: **source** in `Lake/Build/Common.lean`.

### Lake records an action class per job

`JobAction` has four ordered values:

1. `unknown`
2. `replay`
3. `fetch`
4. `build`

Their monitor verbs are `Ran`, `Replayed`, `Fetched`, and `Built` on success.

The common paths update those values in the expected places:

- accepting a saved current trace calls `updateAction .replay`;
- artifact/cache retrieval can call `updateAction .fetch`;
- `buildAction` defaults to `updateAction .build`.

This is useful machine-adjacent evidence because it expresses Lake's own classification rather than inferring from output mtimes.

The limitation is that `JobState.merge` merges actions with `max`. A composite state that observed both replay and build is represented by `build`, not by a sequence `{replay, build}`. Likewise, a build dominates a fetch. The field is therefore a **strongest-action summary**, not an event log.

Basis: **source** in `Lake/Build/Job/Basic.lean` and `Lake/Build/Common.lean`.

### `-v --no-ansi` makes the monitor useful as a probe transcript

The build monitor formats completed jobs using the job action's verb. Its filtering rules matter.

In normal verbosity, the monitor's minimum interesting action is `fetch`; in verbose mode it is `unknown`. Successful action-only lines are printed when progress display is enabled and ANSI output is disabled. Verbose mode also shows optional jobs and trace-level logs. With ANSI enabled, the progress UI is transient and successful action-only job lines are not emitted through the same stable completed-job path unless they also have reportable log output.

The same-revision CLI help describes `--verbose` as showing trace logs, command invocations, and built targets, and `--no-ansi` as disabling ANSI formatting.

For an execution probe that needs a parseable text transcript, prefer a fixed non-ANSI verbose configuration. Then retain:

- process exit status;
- complete stdout/stderr;
- target names/captions;
- every `Replayed`, `Fetched`, and `Built` line.

Even then, treat the transcript as monitor output rather than a versioned telemetry schema. The action merge and monitor filtering rules remain part of its interpretation.

Basis: **source** in `Lake/Build/Run.lean` and **documentation** in `Lake/CLI/Help.lean`.

### Ordinary traces distinguish builder-written state from fetch-written state

The current `BuildMetadata` schema contains:

- `depHash`;
- serialized dependency `inputs`;
- `outputs`;
- `log`; and
- `synthetic`.

A successful ordinary builder writes metadata through `BuildMetadata.ofBuild`, which records the current dependency trace, outputs, the build log, and `synthetic = false`.

A cache-fetch trace is created through `BuildMetadata.ofFetch`, which records the input hash and fetched output description but deliberately stores an empty input list, empty log, and `synthetic = true`.

When `SavedTrace.replayOrFetchIfUpToDate` sees a matching synthetic trace with an empty log, it classifies the job as a fetch; a matching non-synthetic trace is classified as replay and its saved log is replayed.

This gives Anneal a durable provenance signal: **a synthetic trace says the persisted trace was produced by cache fetching rather than by an ordinary builder**.

It does not answer “what happened on this invocation?” by itself. Replaying a trace does not need to rewrite it. A synthetic trace can therefore persist across later invocations, while a subsequent ordinary build can replace it with non-synthetic metadata.

Basis: **source** in `Lake/Build/Common.lean`.

### `.trace.nobuild` is diagnostic evidence, not the primary decision record

When generic `buildAction` refuses a rebuild under no-build mode and an ordinary trace exists, it writes `<trace>.nobuild` with the currently expected dependency trace.

That sidecar is useful for diagnosing **why** Lake considered a target stale. It should not be used as the primary boolean signal for reuse versus rebuild:

- some no-build failures can occur without a preexisting ordinary trace;
- specialized paths can set `wantsRebuild` outside the generic sidecar-writing branch;
- the sidecar is not consulted by the ordinary freshness decision; and
- a later successful build removes it, while an up-to-date check need not.

The dedicated `.trace.nobuild` reference report owns its complete lifecycle. For observability, the important point is that the no-build exit/result is authoritative for the current attempted action; the sidecar is optional diagnostic context.

Basis: **source** in `Lake/Build/Common.lean` and `Lake/Build/Module.lean`; broader lifecycle intentionally delegated to the dedicated corpus subject.

### Cache restoration has observable side effects even when no builder runs

Cache retrieval is not only an abstract action label.

`resolveArtifact` can download a missing content-addressed artifact from a configured cache service and records `fetch`. `restoreArtifact` can hard-link or copy a cached artifact into the requested build-tree path, mark copied files read-only where possible, and write a neighboring `.hash` file. It logs the discovered cache path and restored path at verbose log level.

A no-build probe can therefore succeed while changing the local filesystem. If Anneal's test question is “can this prepared tree be consumed without mutating it?”, the no-build result is insufficient; the test needs filesystem placement/read-only isolation or direct mutation observation as a separate dimension.

Likewise, if the question is “did the compiler run?”, cache restoration is not a false positive: the builder still did not run. The two questions should not share one acceptance bit.

Basis: **source** in `Lake/Build/Common.lean`.

### Package build-cache controls and artifact-cache controls are separate

The pinned `Lake.Env` gives `noCache` the specific meaning “disable downloading build caches for packages,” controlled by `LAKE_NO_CACHE` and command-line override.

The same environment separately carries `enableArtifactCache?`, populated from `LAKE_ARTIFACT_CACHE`, plus the Lake cache location. Package/workspace helpers separately decide whether the artifact cache is readable or writable; artifact-cache reading defaults to enabled when not explicitly configured, while writing defaults to disabled.

Thus `--no-cache` should not be treated as a generic switch that proves no local artifact-cache substitution occurred. An observability test should configure the exact cache mechanism it is testing and, where the distinction matters, inspect the artifact-cache path rather than infer from one package-cache flag.

Basis: **source** in `Lake/Config/Env.lean` and `Lake/Config/Monad.lean`, plus same-revision CLI documentation.

### `--rehash` is useful when byte identity matters, but it does not identify the action

`fetchFileHash` normally trusts a neighboring `.hash` file when hash trust is enabled. `--rehash` disables that shortcut, forcing file contents to be hashed again for trace purposes.

That makes `--rehash` useful when a probe needs confidence that Lake has observed current bytes rather than accepted stale hash sidecars. It does **not** tell whether those bytes were built, fetched, or replayed. Action provenance still comes from the job action and trace/cache evidence.

For a strong Anneal experiment, use independent cryptographic hashes of semantically relevant outputs in addition to Lake's own state when comparing bytes across executions. Byte equality and action identity answer different questions: a deterministic rebuild can emit identical bytes, while a cache hit can reuse identical bytes without invoking the builder.

Basis: **source** in `Lake/Build/Common.lean`; cryptographic comparison is a **derived testing recommendation**.

### Old mode is a different freshness experiment

`--old` changes the freshness decision by permitting modification-time fallback when dependency hashes differ or saved trace state is unavailable in the relevant path.

An old-mode acceptance can therefore say “Lake considered the output fresh enough under mtime rules” even though normal hash-mode reuse would not accept the same state. It must not be mixed into a probe whose goal is to characterize ordinary trace/hash reuse.

Anneal should label old-mode experiments separately and avoid interpreting their action results as evidence of normal hash-mode cache equivalence.

Basis: **source** in `Lake/Build/Common.lean` and **documentation** in `Lake/CLI/Help.lean`.

### A practical probe should record evidence at four layers

For one target under a fixed toolchain, source tree, cache policy, and normal hash mode, the following matrix separates the main questions:

| Question | Primary observation | Supporting observation | What it does not prove |
| --- | --- | --- | --- |
| Would a required builder run? | `--no-build` result / exit code | `wantsRebuild`, `.trace.nobuild` when present | No filesystem writes, no fetch, no network |
| What action class did Lake report? | non-ANSI verbose `Replayed` / `Fetched` / `Built` line | in-process `JobState.action` when using Lake as a library | Complete lower-level event history |
| Was the persisted trace produced by a build or cache fetch? | `BuildMetadata.synthetic` | `inputs`, `log`, output descriptor | What happened on every later invocation |
| Are consumer-relevant output bytes unchanged? | independent cryptographic digest / byte comparison | `--rehash`, Lake descriptors and `.hash` state | Whether bytes were rebuilt or reused |

For a compact regression fixture:

1. build a target from scratch and preserve stdout/stderr, output digest, ordinary trace, and cache state;
2. run the unchanged target in hash mode with `-v --no-ansi --no-build` and preserve its exit code/transcript;
3. remove or isolate the local build output while retaining the intended cache state, then repeat to distinguish cache fetch/restoration from ordinary replay;
4. perturb one traced input and require no-build to report rebuild-needed;
5. run the normal build, require a `Built` classification, and preserve the new trace/output;
6. repeat unchanged and require the expected replay/fetch classification for the chosen cache policy;
7. repeat with `--rehash` when the experiment's claim depends on current file bytes rather than trusted `.hash` sidecars.

The exact cache isolation mechanism should be part of the fixture definition. “Cache enabled” is otherwise ambiguous across package release caches, local artifact mappings, remote artifact services, and existing build-tree outputs.

This procedure is a **derived test design** from the pinned control flow. It was not executed in this investigation.

## Boundaries

**No fresh execution.** No Lake command was run. The report specifies observability semantics from pinned implementation source and documents a probe that still needs exact-pin execution.

**Monitor text is not a structured event protocol.** The action words are directly produced from `JobAction`, but formatting/filtering depends on monitor configuration. A parser should pin the Lake revision and invocation flags or, where practical, expose `JobState.action` through a dedicated test harness.

**Action is a summary.** `JobState.merge` keeps the maximum action, so a composite `build` result can hide subordinate fetch/replay activity.

**No-build is not dry-run.** Cache resolution/restoration, sidecar writes, and other pre-builder operations remain possible. A successful no-build result answers a narrower builder-necessity question.

**Optional jobs are a policy boundary.** The monitor does not count an optional job's logged failure as a required failure. Tests that care about optional targets must name and observe them explicitly.

**Synthetic traces are provenance, not history.** They identify fetch-created metadata at the point of trace creation. They do not record every subsequent replay or fetch and can be replaced by later build metadata.

**No global syscall/network audit.** This report does not enumerate every process, filesystem mutation, or network path reachable from arbitrary custom Lake facets/scripts. It describes the pinned common build/cache machinery needed for Anneal's normal module/package build probes.

**Hash mode only unless stated otherwise.** Old-mode results have distinct mtime semantics.

**Byte identity is separate.** Lake action telemetry cannot prove deterministic rebuild bytes, and equal bytes cannot prove reuse. Clean/cache equivalence remains an execution subject.

## Evidence

Primary subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

Pinned source and documentation inspected:

- `src/lake/Lake/Build/Job/Basic.lean`, blob `1f0066910478137341388422d8d593ddffbaca18` — `JobAction`, verbs, job-state merge semantics.
- `src/lake/Lake/Build/Run.lean`, blob `afae31b7d20a37e6a505d4dc7a9ce875467faf7e` — monitor filtering/rendering, no-build exit code, `Workspace.checkNoBuild`.
- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014` — ordinary/synthetic build metadata, replay/fetch classification, builder gate, artifact-cache lookup/restoration, `.hash` behavior.
- `src/lake/Lake/Build/Context.lean`, blob `8f2eda8d462334f933f112d7ebc4acd3e9553568` — build configuration and no-build/hash/verbosity controls.
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84` — specialized module paths, including rebuild-needed state outside the generic sidecar case.
- `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969` — package build-cache versus artifact-cache environment controls.
- `src/lake/Lake/Config/Monad.lean`, blob `59e032d7c516298a494c070abb948eafe2474184` — artifact-cache readable/writable policy.
- `src/lake/Lake/CLI/Help.lean`, blob `aa96ac1b5fa65178418d4292b49d8086f0d6a9bb` — `--no-build`, `--rehash`, `--old`, `--no-cache`, verbosity, and ANSI option contracts.

Relevant neighboring corpus work was used to maintain scope boundaries rather than to substitute for pinned source:

- the dedicated `.trace.nobuild` candidate owns complete sidecar lifecycle semantics;
- the clean-build/cache-seeded equivalence candidate defines semantic equivalence and explicitly leaves the paired execution open;
- artifact-cache reports own cache architecture, keys, restoration/publication, concurrency, and noncoverage in detail.

## Revalidation

After a Lake version change, revalidate in this order:

1. **Job action model.** Check `Lake/Build/Job/Basic.lean` for action categories, ordering, merge behavior, and rendered verbs.
2. **Monitor contract.** Check `Lake/Build/Run.lean` for filtering, ANSI/non-ANSI behavior, no-build exit handling, and `Workspace.checkNoBuild`.
3. **Freshness/build gate.** Check `Lake/Build/Common.lean` for replay classification, `buildAction`, `wantsRebuild`, and old-mode fallback.
4. **Trace provenance.** Recheck `BuildMetadata` schema and the ordinary/fetch constructors.
5. **Cache-before-build behavior.** Recheck artifact lookup, remote resolution, restoration, and synthetic trace writing before assuming `--no-build` is mutation-free.
6. **Cache controls.** Recheck `Lake/Config/Env.lean`, `Lake/Config/Monad.lean`, and CLI parsing/help so package build caches and the local artifact cache are not conflated.
7. **Specialized facets.** Search all assignments to `wantsRebuild`, `updateAction`, and direct trace-writing functions; generic `buildAction` is not guaranteed to be the only relevant path.

Then execute the compact probe above on the exact selected Anneal toolchain. Preserve:

- full command lines and environment variables that affect cache/freshness;
- stdout/stderr and exit codes;
- ordinary traces and any `.trace.nobuild` sidecars before and after each step;
- cache input/output mappings and whether any artifact was downloaded/restored;
- output file identities and independent cryptographic digests; and
- an explicit classification of each run as local replay, local-cache fetch/restoration, remote fetch, or build.

A future Anneal harness should prefer a structured in-process observation of `JobState.action` if it can do so without changing the build semantics. Until then, pinned `-v --no-ansi` monitor output plus trace/cache state is the most practical source-grounded evidence bundle.
