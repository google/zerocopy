# Revalidation

For a future Lean/Lake revision, first resolve the exact Lean commit and compare the following source boundaries before running experiments:

1. `Workspace`, `Package`, and default paths;
2. package/TOML loading and dependency materialization;
3. `Manifest.version`, `Manifest`, and package-entry source identity;
4. `BuildKey`, target, facet, and build-index dispatch;
5. `JobState` and `BuildTrace`;
6. persisted `BuildMetadata` and its schema version;
7. `buildUnlessUpToDate?`, old-mode fallback, and file-hash trust;
8. representative module trace inputs.

On a capable surface, create one minimal two-package Lake workspace at the exact revision. Preserve the root lakefile, dependency lakefile, `lake-manifest.json`, source files, complete `.lake` trees, commands, stdout/stderr, and hashes.

Run these discriminators:

1. **Initial build.** Build one root module that imports the dependency. Record target output paths, trace files, hash sidecars, mtimes, and verbose job actions.
2. **No-change rebuild.** Build again with verbose logging. Confirm which jobs replay/reuse instead of rebuild.
3. **Manifest-only dependency identity.** Change only the manifest's dependency revision/path in a controlled way and observe materialization/configuration consequences separately from target trace consequences.
4. **Source change.** Change one dependency source file without otherwise editing configuration. Record which traces/hashes/artifacts change.
5. **Deleted trace control.** Restore outputs but delete one saved target trace. Rebuild and record whether the mtime fallback is used.
6. **Old-mode control.** Create a saved-trace hash mismatch with output mtimes that would satisfy the old comparison, then compare ordinary and `--old` behavior.
7. **Hash-sidecar control.** Change an input while preserving an intentionally stale `.hash` sidecar, compare trusted-hash behavior with the exact rehash option at this revision, and do not generalize beyond what the command demonstrates.
8. **No-build control.** Make a target stale and run the exact no-build mode. Preserve the exit code, `.trace.nobuild`, and normal trace state.

These probes establish concrete state transitions and reuse observations at the tested revision. They do not establish relocation, read-only safety, concurrency, offline behavior, or semantic equivalence between independently produced artifact sets.
