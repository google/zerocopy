# Findings

## `lake serve` launches the server; per-file setup happens later

`Lake.serve` first tries to load the Lake workspace. If that succeeds, it takes the workspace's augmented environment variables and the root package's `moreGlobalServerArgs`. It then spawns the selected Lean executable as:

```
lean --server <moreGlobalServerArgs> <serve-cli-args>
```

If workspace loading fails, `serve` warns and falls back to plain `lean --server`, passing an environment marker containing the configuration error so a later `setup-file` call can surface it.

The process launch therefore establishes the server executable, global arguments, and process environment. It does not produce the `ModuleSetup` for each document.

Basis: **source**.

## The worker asks Lake for setup only after it has parsed the document's current imports

Lean's language processor calls the worker's `setupImports` callback after parsing the header and before processing the first command. The callback converts the parsed syntax to a `ModuleHeader` and invokes the worker-side `setupFile`.

The worker then starts Lake as:

```
lake setup-file <file-path> -
```

and writes the parsed `ModuleHeader` as JSON to Lake's stdin. Passing `-` tells the Lake command to read the header supplied by the caller instead of relying only on the file's saved header.

This means server preparation can reflect the current edited import block held by the language server, including unsaved changes. A preparation scheme that only precomputes setup from files on disk cannot replace this file-version-sensitive step without reproducing its semantics.

Basis: **source**.

## `setup-file` loads the workspace and runs a dedicated top-level setup build

Lake's `setupFile` command resolves the requested file and finds the relevant Lake configuration. If no configuration exists it exits with the dedicated no-config code 2. Otherwise it loads the workspace and executes `setupServerModule` in a build context.

For a file that corresponds to a workspace module, `setupServerModule` calls `setupEditedModule`. For a Lean file outside the workspace's module map, it uses `setupExternalModule` with workspace/root server options.

Both paths build/fetch the imports and supporting dependencies needed to elaborate the current file, then return a `ModuleSetup`.

Basis: **source**.

## The setup-file top-level job intentionally has no normal persistent trace state

The source documentation on both `setupEditedModule` and `setupExternalModule` says that, because each is used only as a top-level build, it "does not construct a proper trace state."

This does not mean the operation ignores ordinary Lake freshness machinery. Its import, extra-dependency, dynamic-library, plugin, and precompile jobs are fetched through the normal build graph and can themselves build or reuse persistent artifacts.

The distinction is narrower: the synthetic top-level operation "prepare this edited document" is not itself a persistent module build product with the ordinary trace identity of compiling that module.

Basis: **source**.

## `setup-file` prepares dependencies, not the edited module's compiled artifacts

For a workspace module, `setupEditedModule` fetches:

- the library's extra dependency target;
- import information computed from the current header;
- transitive/precompiled import dependencies as required;
- import dynamic libraries;
- package external libraries when precompilation requires them;
- configured dynamic libraries;
- configured plugins.

It then follows the current direct imports to collect transitive import artifacts and returns a `ModuleSetup`.

It does not invoke the ordinary `recBuildLean` path for the currently edited module. The current document is elaborated by the file worker from its in-memory text.

An ordinary `lake build` can therefore produce artifacts that `setup-file` later consumes, but "the project was built" and "this edited document has been prepared for the server" are different claims.

Basis: **source**.

## ModuleSetup is an explicit file-specific interface between Lake and Lean

`Lean.ModuleSetup` is JSON-serializable and contains:

- module name;
- optional package identifier;
- module-system participation flag;
- optional direct imports override;
- a map of pre-resolved artifacts for transitively imported modules;
- dynamic libraries;
- plugins;
- additional Lean options.

`setup-file` prints this object as JSON. The file worker parses it, loads the returned dynamic libraries, merges the setup options with command-line options, and passes the resulting package/import/artifact/plugin information into Lean's header-processing state.

This is the concrete data contract between Lake's project/build knowledge and Lean's per-document elaborator at this revision.

Basis: **source**.

## Import artifacts can include server-specific olean components

For module-system imports, Lake's `computeExportInfo` requires and records multiple artifacts. The ordinary import-artifact array can contain the main `.olean`, IR, and `.olean.server`; an `import all` path can additionally include `.olean.private`.

`ImportArtifacts.oleanParts` makes the server distinction explicit: when Lean is in server mode, it can load the `.olean.server` component in addition to the main `.olean`.

Thus "all imports have .olean files" is not a complete description of the server preparation contract for module-system builds. Which artifact components must exist depends on the module/import mode at this revision.

Basis: **source**.

## The returned options differ intentionally from ordinary compilation options

The server setup path uses server options, not merely the exact option vector used for batch module compilation.

For an internal workspace module, the setup returned by the server path uses the module/library's server options. Lake's configuration layer defines those as an accumulation including build-type Lean options, package/server options, and library overrides. For an external file, `setupExternalModule` uses the workspace's server options.

Separately, `lake serve` passes the root package's global server arguments on the process command line.

The result has two scopes:

- process-wide server arguments/environment from `lake serve`;
- file/package-sensitive `ModuleSetup.options` from `setup-file`.

A prepared environment that reproduces only compilation flags can therefore miss server-only option state.

Basis: **source**.

## The server needs full paths for some dynamic-library setup

`computeModuleDeps` contains a source comment explaining that building from the Lean server requires full paths for dynamic libraries even where other modes can rely on the augmented library path. It also notes Linux's need for the augmented path to resolve nested dynamic-library dependencies and a macOS Lake-plugin special case for precompiled modules.

The returned `ModuleSetup` consequently carries explicit dynamic-library/plugin paths, not just logical target names.

This is directly relevant to later relocation research: the source contract contains concrete paths. This report does not infer whether those paths can be rewritten or regenerated after relocation.

Basis: **source**.

## Dependency build policy is explicit and can force a fail-closed setup error

The worker's `DocumentMeta.dependencyBuildMode` controls whether it permits setup to build dependencies. If the mode is `never`, the worker invokes:

```
lake setup-file <path> - --no-build --no-cache
```

Lake uses exit code 3 when no-build mode discovers that rebuilding is required. The worker maps code 3 to `FileSetupResult.importsOutOfDate`.

Header processing then stops with a diagnostic saying that imports are out of date and must be rebuilt, rather than continuing with absent or stale dependency setup.

This is a useful fail-closed boundary for interactive verification: a no-build consumer can detect that its prepared dependency state is insufficient.

Basis: **source**.

## No Lake project and Lake setup failure are different states

The worker distinguishes:

- exit code 0 with a valid `ModuleSetup`: success;
- exit code 2: no Lake project/configuration found;
- exit code 3: imports out of date under no-build policy;
- other nonzero exits or malformed JSON: setup error.

For no-Lakefile input the worker falls back to a minimal setup based on the document module name and parsed module flag. For out-of-date imports or a true setup error, header processing returns an error snapshot.

A service wrapping the server should preserve these states instead of collapsing them into one generic "setup failed" condition.

Basis: **source**.

## One worker process loads its imports only once

The worker tracks whether imports have already been loaded. If incremental processing reaches a point that would require loading imports a second time in the same worker, the worker requests process restart instead. The source explains that imports cannot be unloaded from the process.

This complements the saved-dependency behavior from the server report: changes that alter dependency setup are handled through worker replacement, not by mutating an already-loaded import environment in place.

For an Anneal interactive service, keeping a worker alive is therefore not equivalent to keeping arbitrary project dependency state hot forever. Some changes require restart and setup-file re-execution.

Basis: **source**.

## Ordinary module building and server preparation share dependency machinery but have different top-level outputs

The ordinary module build path `recBuildLean` fetches the module's setup, source, options, toolchain trace, package identity, arguments, and import artifacts, then produces persistent module artifacts through `buildLean` and its trace/cache machinery.

The server setup path stops earlier. It assembles the `ModuleSetup` that lets the language worker elaborate the current text.

The shared dependency graph is why a previously built workspace can make setup cheap. The different top-level product is why a normal build does not eliminate the need for setup-file.

Basis: **source**.

## `lake lean` is a useful comparison point because it also consumes ModuleSetup

For an external file, the same `setupExternalModule` helper is used by both `lake setup-file` and `lake lean`. `lake lean` serializes the resulting `ModuleSetup` into a temporary file and invokes Lean with `--setup <file>`.

This shows that `ModuleSetup` is not an editor-only ad hoc record. It is the general interface by which Lake can pre-resolve package/import/plugin state for a Lean frontend invocation.

The server differs because it obtains the setup dynamically after parsing each document header and supplies it directly to the long-lived file worker.

Basis: **source**.

## A prepared language-server environment must satisfy both process and file setup layers

At this revision, the source implies two distinct preparation obligations for a consumer:

1. **server launch preparation**: select the correct Lean/Lake executables, workspace environment, library/search paths, and global server arguments;
2. **document preparation**: for each open file/version, resolve the current header to import artifacts, plugins/dynlibs, package identity, and server options, building missing dependencies unless policy forbids it.

This is **derived** from the pinned code. It does not prescribe Anneal's architecture. In particular, Anneal could invoke Lake normally, precompute and validate equivalent setup data, or use another faithful mechanism. What cannot be inferred from "lake build succeeded" alone is that the second obligation has been discharged for an arbitrary edited document.
