# Lake `.trace.nobuild` semantics at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), a `*.trace.nobuild` file is **diagnostic output from a failed `--no-build` check**, not an input to Lake's rebuild algorithm.

When `buildAction` is reached for an out-of-date target while `noBuild` is enabled, Lake marks the job as wanting a rebuild and aborts instead of running the build. If the target's ordinary `*.trace` path already exists, Lake first writes a sibling `*.trace.nobuild` containing the **current expected dependency trace**. Its JSON uses the normal `BuildMetadata` format, with the current dependency hash and serialized inputs, `outputs: null`, an empty log, and `synthetic: false`. The original `*.trace` remains the prior saved build trace. Comparing the two can therefore show which traced inputs changed.

Lake does not read the `.nobuild` file when deciding whether a target is current. At this revision the only source references to the derived `.nobuild` path create it in the `--no-build` failure branch and remove it after a later successful `buildAction`. As a result, the file's presence is not an authoritative "this target currently needs rebuilding" marker. It can remain stale after inputs revert, after a later build attempt fails, or when a later check becomes up-to-date without entering `buildAction`. Conversely, some `--no-build` failures do not create one at all, including a missing primary trace and rebuild requirements handled outside `buildAction`.

The behavior is intentionally diagnostic. The feature's introducing commit says the new expected trace is emitted beside the old trace so their inputs can be compared, and a later fix restricted emission to cases where the ordinary trace already exists because creating the build directory during a no-build probe could itself interfere with later cloud-release fetching.

Basis: pinned implementation source + pinned test/source history + derived synthesis.

## Applicability

These findings apply to Lake as shipped in `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`.

The report concerns the `.nobuild` sidecar created by the generic `Lake.Build.Common.buildAction` path and the surrounding `--no-build` result protocol. It distinguishes that sidecar from the ordinary `.trace` file, from the process exit status, and from rebuild requests that bypass `buildAction`.

The report does not restate Lake's complete trace schema or dependency-hash algorithm. The neighboring `lean-lake-trace-hash-artifacts-v4-30-0-rc2` and `lake-olean-invalidation-v4-30-0-rc2` reports own those subjects. Here the trace format matters only because `.trace.nobuild` reuses it to preserve a diagnostic snapshot.

No fresh Lake process was executed. The exact file-creation/removal and exit-code behavior comes from pinned source plus pinned upstream history. The runtime tests shipped at the same revision establish `--no-build`'s exit-before-build behavior, but they do not directly assert every stale-sidecar case derived below.

## Findings

### `--no-build` asks Lake to stop at the first action that would actually rebuild

`BuildConfig.noBuild` is an early-exit mode for targets that are not current. Normal up-to-date checks still run. If a saved trace and current dependency trace establish that a target is current, Lake replays the saved result/log as usual and does not enter `buildAction`.

If the target is out of date, `buildUnlessUpToDate?` calls `buildAction`. In normal mode, `buildAction` executes the build, writes the ordinary trace, and returns the new output. In no-build mode it instead records that the job wanted a rebuild and fails with `target is out-of-date and needs to be rebuilt`.

At the top level, a failed build result whose configuration has `noBuild = true` and whose job state has `wantsRebuild = true` exits with dedicated code `3`. A successful no-build run reports that all targets are up to date. `Workspace.checkNoBuild` exposes the same basic question programmatically by running with `noBuild := true` and returning whether the build graph completed without failures.

Evidence:
- [`BuildConfig.noBuild`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Context.lean#L15-L39)
- [`buildUnlessUpToDate?` and `buildAction`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L295-L369)
- [`noBuildCode`, finalization, and `Workspace.checkNoBuild`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Run.lean#L259-L260)
- [`Workspace.checkNoBuild`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Run.lean#L382-L396)
- [same-revision CLI help](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/CLI/Help.lean#L45-L61)

### The `.nobuild` file is the *new expected trace* written beside an existing old trace

`buildAction` derives the diagnostic path with:

```text
noBuildTraceFile := traceFile.addExtension "nobuild"
```

For an ordinary module trace such as `Foo.trace`, that produces `Foo.trace.nobuild`.

In the no-build branch Lake first sets `wantsRebuild := true`. It then checks whether the ordinary `traceFile` path exists. Only when that path exists does Lake call:

```text
writeBuildTrace noBuildTraceFile depTrace Json.null {}
```

The `depTrace` argument is the current trace Lake just computed for the would-be build. The ordinary `traceFile`, by contrast, is the previous saved trace that failed the current up-to-date check. The intended diagnostic operation is therefore to compare the old saved inputs in `*.trace` with the new expected inputs in `*.trace.nobuild`.

The feature's introducing commit `3e16f5332faba0844efb1524222df026095bff14` states exactly that purpose: on a no-build rebuild requirement, emit the new expected trace beside the old trace so their recorded inputs can be compared.

Evidence:
- [`buildAction`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L295-L327)
- [introducing commit `3e16f5332faba0844efb1524222df026095bff14`](https://github.com/leanprover/lean4/commit/3e16f5332faba0844efb1524222df026095bff14)

### Its bytes use normal build-trace metadata with deliberately empty output/log fields

`writeBuildTrace` constructs `BuildMetadata.ofBuild depTrace outputs log`. `BuildMetadata.ofBuildCore` records:

- serialized `depTrace.inputs`;
- `depTrace.hash` as `depHash`;
- the supplied output JSON;
- the supplied log; and
- `synthetic := false`.

For `.trace.nobuild`, the supplied output is `Json.null` and the log is empty. Thus a current-format sidecar contains the normal trace `schemaVersion`, current `depHash`, current serialized inputs, `outputs: null`, an empty log, and `synthetic: false`.

The sidecar does **not** describe artifacts produced by a failed no-build run—none were produced through this action. Its useful payload is the expected input/dependency trace. Treating its `outputs` field as an artifact inventory would be a category error.

Evidence:
- [`BuildMetadata` JSON encoding and `ofBuildCore`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L65-L150)
- [`writeBuildTrace`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L176-L188)
- [`.nobuild` write call](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L303-L323)

### Lake writes no sidecar when the primary trace path does not exist

The pinned implementation's `traceFile.pathExists` guard was added by commit `9c852d2f8cc6819a546146aa48d49cc10d32a32a`.

That change fixed a concrete side effect: writing a `.nobuild` trace for a never-built target created the build directory, and the directory's existence could prevent a later cloud release fetch. Lake therefore emits diagnostic sidecars only when there is already an ordinary trace path to compare against.

This creates an important negative rule: **absence of `*.trace.nobuild` does not mean a no-build check found the target current.** A target with no ordinary trace can require rebuilding and exit through the no-build failure path without leaving the sidecar.

The same-revision `tests/lake/tests/noBuild/test.sh` checks the broader invariant after the fix: a first `--no-build` probe for an unbuilt setup/module target exits with code `3` without creating `.lake/build` or the target artifact. That test is consistent with, and was modified by, the guard-fix commit.

Evidence:
- [guard-fix commit `9c852d2f8cc6819a546146aa48d49cc10d32a32a`](https://github.com/leanprover/lean4/commit/9c852d2f8cc6819a546146aa48d49cc10d32a32a)
- [pinned no-build test](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/tests/lake/tests/noBuild/test.sh)

### A later successful `buildAction` removes the sidecar; other paths need not

In normal build mode, `buildAction` runs the build body. If that body returns successfully, Lake captures the new log, writes the ordinary `traceFile`, then calls `removeFileIfExists noBuildTraceFile` before returning.

This gives `.trace.nobuild` a cleanup path, but not a strong lifecycle invariant. Cleanup occurs only after a successful action reaches that line.

Several consequences follow directly:

- If a subsequent normal build enters `buildAction` but fails fatally before writing its ordinary trace, an existing `.nobuild` file is not removed by this function.
- If inputs later revert so the old ordinary trace becomes up to date again, the up-to-date path returns before `buildAction`; an old `.nobuild` file can therefore remain even though the target is now current.
- If the ordinary trace is later removed, a subsequent no-build failure does not create a replacement sidecar, but this branch also does not remove a previously existing sidecar.

Therefore the sidecar is a potentially stale diagnostic snapshot. Its existence and mtime are not sufficient evidence that the current target still wants rebuilding.

Basis: source + derived control-flow analysis.

Evidence:
- [`SavedTrace.replayIfUpToDate'`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L237-L267)
- [`buildAction` successful-build cleanup](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L303-L327)
- [`buildUnlessUpToDate?`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L330-L355)

### The sidecar is not read by Lake's up-to-date logic

At the pinned source revision, the derived `traceFile.addExtension "nobuild"` path appears in `buildAction`: Lake may write it in no-build mode and remove it after a successful normal build. The ordinary up-to-date path reads `traceFile`, not the `.nobuild` sibling.

Consequently `.trace.nobuild` does not participate in:

- the saved `depHash` comparison;
- output existence checks;
- trace log replay;
- the ordinary decision to rebuild;
- artifact-cache input lookup; or
- the process's no-build exit status except indirectly as output produced by the same failure branch.

Deleting a `.trace.nobuild` file therefore discards diagnostic evidence but, under this pinned implementation, does not alter the target's rebuild decision. Conversely, preserving it does not make a stale ordinary trace valid.

Basis: pinned source search + control-flow inspection.

Evidence:
- [`readTraceFile` and up-to-date checks read the ordinary trace path](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L152-L267)
- [`buildAction` is the `.nobuild` path constructor/writer/remover](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L295-L327)

### Not every no-build rebuild requirement produces a `.trace.nobuild`

The generic `buildAction` path is common, but it is not the only code that can detect work forbidden by `noBuild`.

For example, `Module.recBuildLtar` needs an archive artifact. If the archive is absent and `getNoBuild` is true, it sets `wantsRebuild := true` and errors with `archive does not exist and needs to be built`. This path does not call `buildAction` and does not write a `.trace.nobuild` sidecar.

Together with the missing-primary-trace guard, this means sidecar presence is neither necessary nor sufficient for the global statement "`lake build --no-build` would fail now." The authoritative observation for that global question is the actual no-build result (or `Workspace.checkNoBuild`) under the configuration and target set of interest.

Evidence:
- [`Module.recBuildLtar` no-build branch](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L832-L843)
- [`Workspace.checkNoBuild`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Run.lean#L382-L396)

### Practical interpretation for prepared Anneal state

For a prepared build tree, use `.trace.nobuild` only as a debugging aid:

1. The ordinary `.trace` is the saved prior build metadata.
2. A `.trace.nobuild`, when freshly produced for that same ordinary trace, is the current expected input snapshot that made Lake want to rebuild.
3. Diffing their `inputs` and `depHash` can identify the traced mismatch.
4. The sidecar is not itself an invalidation token and need not be preserved for Lake to make correct future rebuild decisions.
5. Before treating an old sidecar as evidence about current state, rerun the relevant no-build check or otherwise re-establish that its current-input snapshot is still applicable.

A path-sanitizing archive process should also distinguish **rewriting diagnostic metadata** from **changing build validity**. The separate path-embedding report establishes that trace captions can carry absolute producer paths without necessarily contributing those strings to the trace hash. This report adds that a `.trace.nobuild` file is not read by Lake's rebuild logic at all. Rewriting or deleting it can still destroy useful diagnostics, but its presence is not part of the pinned target-validity protocol.

## Boundaries

No fresh run compared an actual `*.trace`/`*.trace.nobuild` pair from Lean v4.30.0-rc2. The sidecar schema and lifecycle are established directly by pinned source and history; concrete example bytes remain useful execution evidence for later revalidation.

The claim that the sidecar is not read is scoped to the inspected Lake source at the pinned revision. External scripts, editor integrations, build wrappers, or Anneal-specific tooling may choose to consume these files. Such consumers would create their own protocol; they are not part of Lake's rebuild decision established here.

The sidecar's `depHash` has the same meaning and hash strength as an ordinary build trace's dependency hash. This report does not independently re-establish that algorithm or claim cryptographic integrity.

A stale sidecar is possible by source control flow, but this investigation did not execute each stale-file scenario. The report therefore distinguishes the proven cleanup trigger from the derived absence of cleanup on other paths rather than assigning frequencies or claiming that stale files are common.

This report does not establish trace relocation or trace-rewriting safety in general. Those remain separate inventory subjects because ordinary `.trace` files can contain operationally or diagnostically relevant path-bearing information even though the `.nobuild` sibling is not an input to Lake's own up-to-date check.

## Evidence

The primary subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

Pinned source/test blobs inspected:

- `src/lake/Lake/Build/Common.lean` — `c283fda65ba4d6e3138a0b4ab8252885bf78a014`
- `src/lake/Lake/Build/Context.lean` — `8f2eda8d462334f933f112d7ebc4acd3e9553568`
- `src/lake/Lake/Build/Run.lean` — `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`
- `src/lake/Lake/Build/Module.lean` — `21c5f343112a1690390188642a05d6092432ab84`
- `src/lake/Lake/CLI/Main.lean` — `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`
- `src/lake/Lake/CLI/Help.lean` — `aa96ac1b5fa65178418d4292b49d8086f0d6a9bb`
- `tests/lake/tests/noBuild/test.sh` — `a538bb91d5429c8f60a8336aa572d65126bc6824`

Pinned history inspected:

- `3e16f5332faba0844efb1524222df026095bff14` — introduced `.nobuild` traces for comparing the new expected trace against the old saved trace.
- `9c852d2f8cc6819a546146aa48d49cc10d32a32a` — restricted sidecar emission to cases where the ordinary trace already exists, to avoid no-build probes creating the build directory and interfering with later cloud-release fetching.

Neighboring reference reports consulted for boundaries rather than as primary evidence:

- `lean-lake-trace-hash-artifacts-v4-30-0-rc2`
- `lake-olean-invalidation-v4-30-0-rc2`
- `lake-path-embedding-v4-30-0-rc2`

No fresh execution evidence was acquired.

## Revalidation

For another Lake revision, first search for every reference to `nobuild`, `noBuildTraceFile`, and `getNoBuild`. Then check these exact questions:

1. Does the current equivalent of `buildAction` still derive a sibling `.nobuild` path?
2. Is it written only when an ordinary trace exists?
3. Does it still use `writeBuildTrace` with the current dependency trace, null/empty outputs, and empty log?
4. Is the sidecar read anywhere in up-to-date, cache, or scheduling logic?
5. What event removes it, and can an up-to-date replay bypass that cleanup?
6. Which no-build failure paths set `wantsRebuild` without going through `buildAction`?
7. Does the top-level no-build exit code or `Workspace.checkNoBuild` contract change?

The cheapest exact-pin execution probe uses one tiny module package:

- build once and preserve its ordinary `.trace`;
- change one traced input and run `lake build --no-build`, preserving the resulting `.trace.nobuild` and exit code;
- decode both JSON files and diff `depHash` and `inputs`;
- revert the input without a successful rebuild, rerun `--no-build`, and observe whether the old sidecar remains while the target is now accepted;
- make the target out of date again, run a normal build that fails before completion, and observe sidecar persistence;
- then run a successful normal build and confirm sidecar removal;
- finally delete the ordinary trace and run `--no-build` from a clean build-directory state to confirm that the probe fails without creating a `.nobuild` sidecar or build directory.

Preserve commands, exit statuses, directory listings, and both trace files. That fixture would make the lifecycle and diagnostic meaning concrete without requiring a large Lake workspace.
