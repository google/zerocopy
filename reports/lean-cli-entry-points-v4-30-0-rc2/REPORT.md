# Lean CLI entry points and environment at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), the `lean` command is one executable with several entry paths rather than separate batch, JSON, and server programs. `Lean.Shell` parses the command-line state and dispatches either to ordinary file processing, the language-server watchdog (`--server`), or the server worker (`--worker`). Ordinary file processing reads one source file or stdin and calls `Lean.Elab.runFrontend`; `--json` and `-E` change reporting policy on that same frontend path instead of selecting a different checker.

The batch command is also an artifact-producing entry point. After successful elaboration, the same frontend can write `.olean` and `.ilean` outputs, and the shell can emit C or LLVM output. With `--run`, it instead evaluates the module's `main` definition after successful elaboration. Dependency-only modes bypass full elaboration and print imports or source dependencies.

The environment is part of the command's semantics. Lean initializes its compiled-module search path from the running installation and `LEAN_PATH`; source lookup uses `LEAN_SRC_PATH`. The input file's module name normally comes from its path relative to `--root` or the current directory. A `--setup` JSON file can instead supply the module name, imports, import artifacts, plugins, dynamic libraries, package identity, and options. A caller therefore cannot treat `lean file.lean` as depending only on the bytes of `file.lean` and the executable version.

Toolchain selection has an important boundary. The pinned `Lean.Shell` does not parse a `lean-toolchain` file and does not implement Elan's proxy-selection algorithm. It runs after some executable has already been selected. Lean's own path helper explicitly warns that a `lean` found in `PATH` may be an Elan proxy. Lake then builds a workspace execution environment around the detected Lean installation: it prefers `ELAN_TOOLCHAIN` or its compiled Lean toolchain identity, sets `LEAN_SYSROOT`, augments `LEAN_PATH` and `LEAN_SRC_PATH`, and exposes `lake env lean`, `lake lean`, and `lake serve` as workspace-aware launch surfaces. Exact Elan proxy precedence is outside this pinned Lean/Lake source report.

For Anneal, the durable integration boundary is therefore two-layered: select the intended toolchain/workspace outside `Lean.Shell`, then choose the Lean entry path inside the selected executable. A reproducible agent should not infer toolchain identity from the `lean` command name alone, and it should not treat `--json` or `--server` as independent environments from batch checking.

No fresh Lean, Lake, or Elan process was executed for this report. The findings come from exact pinned Lean/Lake implementation source. Detailed JSON framing and server lifecycle behavior are covered by their dedicated corpus reports; this report establishes how those modes are selected and which environment feeds them.

## Applicability

- Lean/Lake repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- version: `v4.30.0-rc2`
- Anneal context: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`

This report covers the `lean` shell, its direct frontend invocation, the search-path/system-root helpers used by the process, and the Lake environment/launcher boundary in the same pinned Lean repository. It does not claim the command-line behavior of a different Lean revision.

"Toolchain selection" is split deliberately. This report establishes what the selected Lean binary and the pinned Lake code do with installation and toolchain environment state. It does not establish the independent Elan project's complete proxy-selection precedence, installation/download behavior, or directory-override semantics. Those require a separately pinned Elan subject.

The detailed wire contracts for `lean --json` and `lean --server` are separate concerns. Here they matter because the shell selects them from the same executable and environment. A client that needs JSON field semantics, LSP/RPC lifecycle, tactic-state querying, or worker restart behavior should use the dedicated reports rather than infer those details from this entry-point report.

## Findings

### The `lean` executable has one shell dispatcher

`src/Lean/Shell.lean` defines the user-visible help, the parsed `ShellOptions`, the per-option updates, and `shellMain`. Its state includes the frontend/server component, input mode, root directory, setup file, output artifact paths, JSON mode, warning-to-error kinds, resource limits, and `--run` state.

The component branch happens before normal file handling:

- ordinary invocation keeps `.frontend` and proceeds to input processing;
- `--server` changes the component to `.watchdog`, and `shellMain` returns from `Server.Watchdog.watchdogMain`;
- `--worker` changes it to `.worker`, and `shellMain` returns from `Server.FileWorker.workerMain`.

Server mode is therefore not a second executable or a wrapper around batch invocation. It is an early dispatch branch of the same selected Lean process. Some command-line state is explicitly forwarded to the watchdog so that workers can be started consistently.

The help text exposes `--server` and `--worker` only when Lean was built with multithreading support. That is a build-capability boundary, not merely a runtime option.

### Direct checking and artifact production share `runFrontend`

For ordinary file checking, `shellMain` expects exactly one file name unless `--run` is active, or uses `<stdin>` with `--stdin`. It decodes the source as lossy UTF-8, handles the dependency-only modes, computes a main module name, and calls:

`Elab.runFrontend contents opts.leanOpts fileName mainModuleName ...`

The frontend enables command-line snapshots and defaults asynchronous elaboration on. It parses and processes the module, reports diagnostics, waits for the final command state, and returns `none` if processing did not produce a final state or if reportable errors remain. The shell maps successful versus failed frontend completion to process success versus failure.

Successful frontend processing can write an `.olean` through `writeModule` and an `.ilean` derived from the final snapshot tree. The shell can then emit C or LLVM output from the returned environment. `--run` evaluates the module's `main` with the remaining command arguments after the frontend has succeeded.

This means "check this file," "compile this file," and "run this file" share a substantial frontend state machine. An Anneal integration that wants only checking should avoid requesting output artifacts or `--run`; it does not need a distinct checker executable.

### Dependency-only modes are separate fast paths

`--deps`, `--src-deps`, and the internal dependency-JSON path return before ordinary frontend elaboration. The shell reads the input and asks the import parser to print import/module dependencies or source dependencies.

These modes are useful for dependency discovery, but their success is not evidence that the module fully elaborates. They intentionally answer a narrower question than `runFrontend`.

### `--json` is a reporting mode of the batch frontend

`--json` sets `ShellOptions.jsonOutput`. `shellMain` passes that Boolean to the same `Elab.runFrontend` call used for ordinary checking. `-E kind` likewise accumulates message kinds and passes them as severity overrides.

Inside `runFrontend`, `jsonOutput` and the severity overrides affect snapshot reporting. They do not select a different parser, elaborator, environment, or source-loading path. Frontend errors still cause `runFrontend` to return `none`, and the shell still derives the process result from frontend success.

For an agent, this is the key composition rule: machine-readable diagnostics are an output representation layered on the normal frontend. They should be invoked in the same prepared environment as non-JSON checking. The dedicated `lean --json` report owns the exact line framing, serialized message fields, position conventions, stdout/stderr caveats, and revision-stability boundary.

### Module identity depends on the file path and root

Absent setup metadata, `shellMain` asks `moduleNameOfFileName` for the source module name. `moduleNameOfFileName` resolves the source path and root to real paths, defaults the root to the current directory, requires the input to lie beneath that root, removes the root prefix and source extension, and converts path components to the Lean module name.

`--root=dir` therefore changes module identity for a direct file invocation. Running the same bytes at a different path or under a different root can change the module name even before imports are considered.

For a plain check that is not producing certain compiled outputs, `shellMain` has a fallback `_stdin` module name when normal path-derived identity cannot be established. Callers that care about durable module identity should not rely on that fallback; they should supply a coherent root or setup metadata.

### `--setup` can replace header-derived execution context

`--setup=file` loads `ModuleSetup` JSON before frontend execution. When setup data is present, it can supply the main module name, package identity, module/public status, imports, imported artifacts, dynamic libraries, plugins, and options. Setup options are merged so that setup-provided values override command-line options for the frontend configuration covered by that merge.

This is a stronger input than a convenience flag. It can supersede parts of the source header and normal path-derived context. A prepared Lake/Anneal environment that uses setup files must therefore treat the setup artifact itself as an input to checking and cache validity.

### Compiled-module lookup uses the selected installation plus `LEAN_PATH`

`src/Lean/Util/Path.lean` derives the running Lean installation root from the selected executable's application directory. The built-in compiled-module search path is the installation's `lib/lean`. Initialization then adds `LEAN_PATH`; with the ordinary empty initial path, entries from `LEAN_PATH` precede the built-in library path.

`findOLean` searches that initialized path for compiled modules. Import resolution is consequently sensitive to `LEAN_PATH`, not just to the source file and Lean version.

Source-location utilities use a separate `LEAN_SRC_PATH`, augmented with source directories adjacent to the selected Lean installation. This source path matters to editor/reference/source-location features even when compiled imports resolve through `.olean` files.

### `LEAN_SYSROOT` identifies an installation but does not itself select the running shell

Lean's external `findSysroot` helper first accepts `LEAN_SYSROOT`; otherwise it invokes a `lean` command with `--print-prefix`. Its documentation calls out the important case where that command is an Elan proxy rather than the final executable under the returned system root.

Inside the already-running shell, `--print-prefix` prints the root derived from the running executable. The shell does not parse `ELAN_TOOLCHAIN` or `lean-toolchain` to replace itself with another binary.

The distinction matters operationally: `LEAN_SYSROOT` and `--print-prefix` describe or discover an installation, while the process launcher determines which executable started in the first place.

### Lake constructs the workspace-aware environment around Lean

Pinned Lake source makes the outer layer explicit. `Lake.findLeanInstall?` uses `LEAN_SYSROOT` first, then `LEAN`, then a `lean` found through `PATH`. Lake's environment records a preferred toolchain string from `ELAN_TOOLCHAIN` or, if absent, `Lean.toolchain`.

`lake env` documents the variables it supplies to child processes. Relevant ones include:

- `LEAN_SYSROOT`, pointing at the detected Lean installation;
- `LEAN_PATH`, augmented with Lake/workspace Lean library directories;
- `LEAN_SRC_PATH`, augmented with Lake/workspace source directories;
- `PATH`, augmented with Lean/Lake/workspace binary directories;
- platform shared-library search paths;
- `LEAN` and related compiler/tool paths in Lake's computed base environment.

`lake lean <file>` builds the file's imports and then runs `lean` in this environment with workspace Lean arguments. `lake serve` similarly runs the installation's `lean --server` with workspace server arguments.

For Anneal, these Lake entry points are materially different from invoking an arbitrary ambient `lean`: they construct the workspace search paths and installation variables that the selected Lean process consumes.

### Toolchain selection is an outer-launcher responsibility

At this pin, the examined `Lean.Shell` source contains no `lean-toolchain` parser and no Elan proxy algorithm. Lake knows about an optional Elan installation and an `ELAN_TOOLCHAIN` identity, but that is not evidence for every rule by which Elan selects or downloads a toolchain when a user types `lean`.

The stable architectural conclusion is narrower and more useful: by the time `Lean.Shell` handles `--json`, `--server`, `--root`, or a source filename, an executable has already been selected. Reproducibility therefore requires controlling the launcher/toolchain layer as well as the shell arguments.

A robust Anneal invocation can satisfy that requirement by running inside a prepared Lake environment or by using an explicitly selected Lean executable plus explicit environment state. Merely recording the string `lean` is insufficient provenance.

## Boundaries

No fresh Lean, Lake, Elan, compiler, server, or filesystem experiment was run. This is pinned source inspection.

This report does not reproduce the full command-line grammar implemented by the native shell launcher around `Lean.Shell`. It establishes the Lean-side option semantics that matter to Anneal and the resulting dispatch paths.

The report does not specify the JSON wire schema. The separate JSON-protocol report should remain authoritative for serialized diagnostic fields, line framing, source coordinates, stderr leakage, and exit-status subtleties.

The report does not specify the language-server wire protocol or worker lifecycle beyond the shell entry branch. The dedicated server reports remain authoritative for JSON-RPC/LSP methods, per-file workers, cancellation, tactic-state queries, dependency staleness, and reconnect behavior.

The report does not establish Elan's complete proxy precedence. In particular, it does not claim an order among command-line toolchain overrides, `ELAN_TOOLCHAIN`, directory overrides, and `lean-toolchain` files. Those behaviors belong to a separately pinned Elan subject if Anneal needs to rely on them directly.

The report also does not claim that arbitrary ambient environment state is irrelevant. The opposite is established for the paths discussed here: search paths and installation variables materially affect resolution. Other environment variables, dynamic-loader state, plugins, and platform behavior may add further inputs.

Finally, the CLI is revision-coupled. The presence of a flag at `v4.30.0-rc2` is not a compatibility guarantee for later Lean versions. Revalidation must inspect the selected revision rather than extrapolate from adjacent releases.

## Evidence

Primary evidence is exact source at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`:

- `src/Lean/Shell.lean`, blob `2ff5c4b0c82f876ddd4384c9c20dcaefebc1b90e`: user-visible CLI, `ShellOptions`, option processing, frontend/watchdog/worker dispatch, direct file input, module-name/setup handling, `runFrontend`, `--run`, and code-generation branches.
- `src/Lean/Elab/Frontend.lean`, blob `fd3760667db96a351b4f654720193c89bbee356e`: `runFrontend`, snapshot processing/reporting, JSON/severity parameters, error return boundary, `.olean`/`.ilean` writing, and returned environment.
- `src/Lean/Util/Path.lean`, blob `b2af1878ec01bcf790f31401c0d46efd6b94c840`: installation root/library path, `LEAN_PATH`, `LEAN_SRC_PATH`, module-name derivation, `findSysroot`, and the Elan-proxy warning.
- `src/Lean/Server/Watchdog.lean`, blob `68ed22f9178c9ae917c595c364d23df902d9478f`: server watchdog process and selected-worker path behavior, including `LEAN_SYSROOT`/`LEAN_WORKER_PATH` inputs. This report uses it only to confirm the shell's server branch, not to replace the dedicated server report.
- `src/lake/Lake/Config/InstallPath.lean`, blob `e309253fe8c39aa90ce48de295305d160286a9b1`: Lean/Lake/Elan installation detection; `LEAN_SYSROOT`, `LEAN`, `PATH`, and co-located toolchain assumptions.
- `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`: Lake environment state, preferred toolchain identity, and child-process environment variables.
- `src/lake/Lake/CLI/Help.lean`, blob `aa96ac1b5fa65178418d4292b49d8086f0d6a9bb`: source-level user contract for `lake serve`, `lake env`, and `lake lean`.

Evidence roles are **pinned source** and **derived architecture**. There is no fresh **execution** evidence in this package.

## Revalidation

For a new Lean/Lake revision, recheck at least the following source surfaces before carrying these conclusions forward:

1. `Lean.Shell.ShellOptions.process` and `shellMain`: flag names, component dispatch, direct-file cardinality, setup/module-name behavior, JSON/error policy, artifact outputs, and `--run`.
2. `Lean.Elab.runFrontend`: setup precedence, reporting mode, error return semantics, artifact writing, and asynchronous/snapshot defaults.
3. `Lean.Util.Path`: running-installation derivation, `LEAN_PATH` ordering, `LEAN_SRC_PATH`, `moduleNameOfFileName`, and `findSysroot`.
4. `Lean.Server.Watchdog`: whether server startup still uses the same selected executable/environment model and which arguments/environment values select workers.
5. Lake installation/environment construction: `findLeanInstall?`, preferred toolchain identity, variables produced by `lake env`, and the implementations behind `lake lean` and `lake serve`.

On a surface that can execute the exact pin, a compact validation probe should use a temporary Lake workspace and record the exact executable identity (`--version`, `--githash`, `--print-prefix`), `lake env` values for `LEAN_SYSROOT`/`LEAN_PATH`/`LEAN_SRC_PATH`, and the process status for the same small file under plain checking and `--json`. A second probe should start `lake serve` only long enough to verify that the server process comes from the same selected toolchain environment. These probes would validate the source-derived integration contract; they are not required to understand the dispatch architecture itself.

If Anneal ever plans to rely directly on Elan selection rather than entering through a preselected Lake/toolchain environment, add a separate report pinned to the exact Elan revision in use. That report should establish the proxy's toolchain-selection precedence and its behavior when a requested toolchain is absent, rather than importing those facts by assumption into this Lean report.