# Revalidation

For a future Lean/Lake pin, source-diff these boundaries first:

1. `Lake.serve`: workspace loading, environment, global server arguments, and fallback behavior;
2. worker-side `runLakeSetupFile` and `FileSetupResult`;
3. `Lake.setupFile` exit codes and workspace loading;
4. `setupServerModule`, `setupEditedModule`, and `setupExternalModule`;
5. `ModuleSetup` fields and JSON shape;
6. import-artifact construction, especially server/private olean components;
7. server-option composition;
8. the worker's handling of out-of-date imports and import reload/restart.

On a capable surface, create a two-module project:

```lean
-- A.lean
def a : Nat := 1
```

```lean
-- B.lean
import A
#check a
```

Preserve exact toolchain revision, lakefile, manifest, full build tree, commands, JSON, stdout/stderr, and hashes. Then:

1. Run the ordinary build selected for the project and snapshot all artifacts.
2. Run `lake setup-file B.lean` with B's parsed header on stdin. Preserve the exact `ModuleSetup` JSON and verify which returned artifact paths already existed from the ordinary build.
3. Remove or stale one imported artifact and repeat normally. Record exactly what `setup-file` rebuilds or fetches.
4. Repeat with `--no-build --no-cache`. Require exit code 3 and verify the server maps it to `importsOutOfDate`.
5. Without saving B, change its in-memory header to import a second module and send that header to `setup-file`. Verify that the setup follows the supplied header rather than the saved file header.
6. Compare a workspace module with a Lean file outside the workspace module map and preserve the different module/package identity and server-option output.
7. Launch `lake serve`, open B through LSP, and record the child `setup-file` invocation plus progress/error behavior.
8. If relocation/read-only behavior is under study, repeat from a copied read-only dependency tree as a separate experiment rather than inferring it from successful setup here.

These observations establish the actual producer/consumer behavior for the tested revision. They do not prove concurrency safety, offline guarantees, relocatability, or cache/build semantic equivalence.
