# Lean server multi-workspace and project isolation at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), one Lean language-server process can manage many open files, but it does not implement independent LSP workspaces inside that process. The server has one launch working directory and one inherited environment. Its own protocol description states that `InitializeParams.rootUri?` is ignored in favor of the server process's current working directory. Although Lean's generic LSP data type parses `workspaceFolders`, the server does not advertise workspace-folder capabilities, has no `workspace/didChangeWorkspaceFolders` implementation, and does not use the parsed folder list to select per-file project state.

The per-file worker architecture does not change that boundary. The watchdog starts a separate `lean --worker` process for each open document URI, which is useful isolation for elaboration crashes and imported-module memory. Those workers inherit the watchdog's process environment and current directory. The watchdog forwards the same initialization parameters and server command-line arguments to every worker. A worker then invokes `lake setup-file <file> -` without a per-file current-directory or environment override.

When the server was launched by `lake serve`, that inherited context comes from one Lake `Workspace`. `lake serve` loads one workspace, derives that workspace's augmented environment and root server arguments, and spawns one `lean --server`. Later `lake setup-file` invocations load configuration from that same invocation context. An opened source file that belongs to the loaded workspace is configured as that workspace module. A source file outside the loaded workspace can be treated as an *external module*, but its imports, options, libraries, and plugins are still resolved against the already-loaded workspace. This is not discovery or isolation of a second project's Lake configuration.

The practical model for Anneal is therefore one prepared project/workspace environment per Lean server process. Files that are part of one Lake workspace can share that server, including files from packages already represented by the workspace dependency graph. Distinct projects that require different Lake roots, dependency graphs, `LEAN_PATH` values, plugins, dynamic libraries, or toolchains should use distinct Lean server processes. Opening their files through one LSP connection does not give each file its own project environment.

No fresh server or Lake process was executed for this report. The result is based on exact pinned Lean/Lake source and Lean's pinned protocol overview.

## Applicability

- Lean/Lake repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- version: `v4.30.0-rc2`
- Anneal context: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`

"Multiple workspaces" here means multiple independently configured projects whose correct Lean environment can differ: different Lake configuration roots, manifests, dependency graphs, toolchains, search paths, plugins, dynamic libraries, or global server arguments. A Lake workspace may itself contain or depend on multiple packages. Sharing one server across files that are all correctly represented by that single loaded workspace is not the unsupported case described here.

The report distinguishes two forms of isolation. Lean provides strong *per-file process isolation*: each open file gets its own worker process. It does not provide corresponding *per-workspace configuration isolation* inside one watchdog process.

This report does not claim that an arbitrary file outside the current Lake workspace always fails. Lake has an explicit external-module path, and plain-Lean fallback can also make some files elaborate. The claim is narrower: such a file is not automatically assigned an independent project environment based on its own `rootUri`, `workspaceFolders`, or neighboring Lake configuration.

## Findings

### LSP workspace roots do not select Lean's project environment

Lean's checked-in protocol overview explicitly documents a standard violation for `initialize`: `InitializeParams.rootUri?` is not used by the language server. The server uses the current working directory of the server process instead.

This is the most direct statement of the workspace boundary. An LSP client cannot launch Lean in one directory and then select a different project root merely by changing the `rootUri` in `initialize`.

The generic `InitializeParams` structure does include `workspaceFolders?`, so Lean can parse a client's folder list. Parsing is not the same as implementing multi-workspace semantics. At this revision:

- `Lean.Data.Lsp.Workspace` leaves `WorkspaceFoldersServerCapabilities`, `DidChangeWorkspaceFoldersParams`, and `WorkspaceFoldersChangeEvent` as TODOs.
- `ServerCapabilities` has no workspace-folders capability field.
- `mkLeanServerCapabilities` therefore cannot advertise workspace-folder support.
- The server implementation has no `workspace/didChangeWorkspaceFolders` handler.
- Searches of the pinned server source show no use of `InitializeParams.workspaceFolders?` to choose a root, search path, Lake configuration, worker environment, or dependency graph.

The server stores the whole `InitializeParams` because it forwards initialization to file workers. That forwarding does not give the workers independent workspace configuration: each worker receives the same parameters, and the workspace-folder values are likewise not used to establish a project environment.

### One watchdog can still manage files at many URIs

The absence of multi-workspace configuration support does not mean the watchdog accepts only one directory's URIs. Its file-worker map is keyed by `DocumentUri`. A `textDocument/didOpen` creates a worker for the opened URI, and the watchdog can hold many such workers simultaneously.

This distinction matters. The server's data model is multi-*document*, and document paths need not be identical or adjacent. But path diversity is not project isolation. All of those documents live under one server-level process context unless later setup code explicitly constructs something more specific.

### Per-file worker processes isolate computation, not workspace state

`startFileWorker` launches one copy of the selected Lean executable with `--worker` for each open file. This architecture is intentionally robust: a worker crash or imported-module compacted-region lifetime problem can be handled by restarting that file's process without taking down the watchdog or other workers.

The process launch does not set a worker-specific current directory or environment. It supplies the selected worker executable, the watchdog's server arguments, and the document URI. The operating-system child therefore inherits the watchdog's current directory and environment.

The watchdog then forwards the same stored `InitializeParams` to every worker. It also sends one `didOpen` containing the document URI and text. There is no per-file workspace-root negotiation between these steps.

For Anneal, worker process isolation is valuable but should not be mistaken for configuration isolation. Two workers in the same server can have separate heaps and elaboration state while still resolving their project setup through the same inherited Lake/Lean environment.

### File setup runs Lake in the inherited process context

A Lean file worker calls `Lean.determineLakePath` and then runs:

`lake setup-file <absolute-file-path> -`

The subprocess launch specifies command, arguments, and piped stdio. It does not specify a different current directory or environment. The `lake` subprocess therefore inherits those from the worker, which inherited them from the watchdog.

`determineLakePath` is likewise process-global. It selects Lake from `LAKE` if present, otherwise from `LEAN_SYSROOT/bin/lake`, otherwise next to the running Lean executable. There is no path-dependent selection of a different Lake executable for each opened document.

The absolute file path still matters. `setup-file` uses it to parse the target source and to ask the loaded workspace whether that path corresponds to a known module. But the configuration context in which that question is asked comes from the Lake invocation, not from a search beginning at the target file's directory.

### `lake serve` prepares exactly one loaded workspace

Pinned Lake describes `serve` as starting the Lean LSP for the `Workspace` loaded from its `LoadConfig`. The implementation loads that workspace once. If successful, it takes:

- the workspace's augmented environment variables; and
- the root package's additional global server arguments.

It then spawns the selected Lean executable with `--server`.

`LoadConfig` makes the root explicit. It contains an absolute `wsDir`, a package directory derived from that workspace directory, and a configuration file path derived from that package directory. Its `configFile` is therefore already tied to the loaded workspace.

This is the outer preparation layer for the server. The LSP initialization request arrives after the process has been spawned with that workspace environment. As noted above, `rootUri` and `workspaceFolders` do not replace it.

### `lake setup-file` does not discover a second project for an external file

The server's setup path makes the cross-project boundary concrete. `lake setup-file` loads the workspace identified by its existing `LoadConfig`, then calls `setupServerModule` on the requested source path.

`setupServerModule` has two cases:

1. If `findModuleBySrc? path` identifies the file as a module in the loaded workspace, Lake uses the module's package, options, plugins, libraries, and dependency information.
2. Otherwise Lake calls `setupExternalModule`.

The second case is deliberately named and documented as "Lean code external to the workspace." It does not load a new workspace rooted at the external file. Instead, it uses the current workspace's root package, server options, module lookup, imports, external libraries, dynamic libraries, and plugins to build a `ModuleSetup` for that file.

An external file can therefore be usable, but it remains an external file *relative to the one loaded workspace*. If the file actually belongs to a different Lake project with a different manifest or dependency graph, this code path does not switch to that project's configuration.

### Dynamic workspace-folder changes are not a configuration mechanism

The LSP standard defines workspace-folder capability negotiation and `workspace/didChangeWorkspaceFolders`. The pinned Lean LSP types explicitly leave those pieces unimplemented. The watchdog's protocol overview includes `workspace/didChangeWatchedFiles`, but that is a different feature: it reports filesystem changes for registered `*.lean` and `*.ilean` watchers.

Changing watched files can invalidate or restart file workers. It does not add or remove Lake workspaces. A client cannot use the presence of the word "workspace" in `workspace/didChangeWatchedFiles` as evidence for multi-root workspace support.

### A single Lake workspace can legitimately span multiple packages

The correct process boundary is a prepared workspace, not necessarily a single package or source directory. Lake's `Workspace` already represents a root package plus resolved dependencies and package-level module information. `setupServerModule` can identify source paths against that loaded workspace and use the corresponding module/package configuration.

Accordingly, an Anneal service need not create one Lean server per file or necessarily one per package. It needs one per independently prepared environment whose files can be represented correctly by the same loaded workspace, toolchain, process environment, and server arguments.

This distinction avoids unnecessary process proliferation while preserving semantic isolation.

### Separate servers are the conservative model for independent projects

For independent projects, one process cannot safely express conflicting process-global inputs. Examples include:

- different Lean executables or `LEAN_SYSROOT` values;
- different Lake roots or manifests;
- different `LEAN_PATH`/`LEAN_SRC_PATH` values;
- different dependency versions;
- different dynamic libraries or plugins; and
- different root-package global server arguments.

The pinned implementation offers no per-document namespace around these values. A future Anneal LSP/MCP service should therefore key reusable Lean server instances by a complete prepared-environment identity and route a document only to a server whose environment matches that document's project.

An implementation can still multiplex many logical agent clients over a server for the same environment. The unsupported operation is merging semantically different prepared workspaces into one Lean server merely because LSP supports multiple document URIs.

## Boundaries

No fresh Lean server, Lake process, editor, or filesystem experiment was run. The findings are source-derived at the exact selected Lean/Lake revision.

This report does not establish editor-side behavior. VS Code, Neovim, Emacs, or an MCP bridge may independently decide to launch one Lean server per workspace. That client policy can provide isolation even though the Lean server itself does not implement LSP workspace folders.

This report also does not claim that every path outside the loaded workspace fails. The pinned Lake code intentionally supports `setupExternalModule`; a file can elaborate using imports and options available from the current workspace. The unsupported case is automatic independent configuration of a second project.

The report does not quantify the cost of separate server processes, the memory cost of many workers, or the point at which a long-lived server should be recycled. Those questions belong to the separate server-memory-growth inventory item and require runtime measurement for strong conclusions.

It also does not establish behavior when two project configurations happen to be semantically identical. Sharing could be safe if an outer orchestrator proves that the complete effective environment is the same. The pinned Lean server provides no built-in workspace identity or equivalence mechanism that performs that proof.

Finally, all conclusions are revision-coupled. Future Lean versions could implement `workspaceFolders`, dynamic workspace changes, per-file project discovery, or per-worker environment selection. Revalidate before carrying this isolation model forward.

## Evidence

Primary evidence is exact source at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`:

- `src/Lean/Server/ProtocolOverview.lean`, blob `4f493fc900319113e00a0a9c0f5eac4c3e5bb8e5`: explicitly states that `InitializeParams.rootUri?` is ignored and server cwd is used.
- `src/Lean/Data/Lsp/InitShutdown.lean`, blob `e964ff53076c2e5bb6eed1ac776bf721c7a1ff90`: parses `rootUri?` and `workspaceFolders?` into generic initialize parameters.
- `src/Lean/Data/Lsp/Workspace.lean`, blob `bbe312565dd8958d38f333642d839fb5874faa0f`: marks workspace-folder server capabilities and workspace-folder change parameters/events as TODO.
- `src/Lean/Data/Lsp/Capabilities.lean`, blob `886e54140b4571bfc1e6b28fcb75ad196df0199e`: `ServerCapabilities` lacks a workspace-folders capability.
- `src/Lean/Server/Watchdog.lean`, blob `68ed22f9178c9ae917c595c364d23df902d9478f`: one watchdog, per-document workers, shared initialization parameters, worker process spawning without per-worker cwd/environment, and advertised capabilities.
- `src/Lean/Server/FileWorker/SetupFile.lean`, blob `35a756819a8de5ebb05256bb39d83148f9f24145`: worker-side `lake setup-file` invocation with the document path and no cwd/environment override.
- `src/Lean/Util/LakePath.lean`, blob `ad9adf149c25c15df499e7baf4e5574cfd23ffe9`: process-global Lake executable selection from `LAKE`, `LEAN_SYSROOT`, or the Lean installation.
- `src/lake/Lake/CLI/Serve.lean`, blob `27d3e89530105b7ea9fe9f951b9459c1ee1f9cc9`: `lake serve` loads one workspace and spawns `lean --server` with that workspace's augmented environment; `setup-file` loads the invocation's workspace before configuring a target file.
- `src/lake/Lake/Load/Config.lean`, blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`: `LoadConfig` contains one absolute workspace directory and configuration-file path.
- `src/lake/Lake/Load/Package.lean`, blob `e9e858a54048ffa96972d264dbd51ca35b4ba403`: resolves and loads the configuration file from the `LoadConfig` package/workspace context.
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: `setupServerModule` distinguishes a module found in the loaded workspace from an external module, and configures the latter using the current workspace rather than loading a second project.

Lean's checked-in server README, blob `4bac3026e17b604888324821f5725e0338f802e3`, corroborates the worker architecture: one watchdog coordinates per-file workers, and workers use `lake setup-file` to rebuild and locate dependencies.

Evidence roles are **pinned source**, **pinned protocol documentation**, and **derived architecture**. There is no fresh **execution** evidence.

## Revalidation

For a future Lean revision, first inspect the protocol and capability surface:

1. Check whether `ProtocolOverview` still says `rootUri` is ignored.
2. Check `InitializeParams`, `ServerCapabilities`, and workspace LSP types for implemented workspace-folder negotiation.
3. Search the server for `workspaceFolders`, `rootUri`, and `workspace/didChangeWorkspaceFolders` uses, not merely type declarations.
4. Inspect watchdog worker spawning for per-worker current-directory or environment overrides.
5. Inspect file-worker setup for changes to Lake executable/configuration discovery.
6. Inspect `lake serve`, `LoadConfig`, and `setupServerModule` to determine whether setup remains bound to one loaded workspace or discovers a project per target file.

On a surface that can execute the exact revision, a compact behavioral probe should create two minimal Lake projects with deliberately conflicting dependency or option identities. Launch one `lake serve` from project A, send `initialize` with both A and B as `workspaceFolders`, open a file from each project, and record the `$/lean/ileanHeaderSetupInfo`/diagnostics plus the actual `lake setup-file` subprocess context. Repeat with `rootUri` pointing only at B. The source-derived prediction is that both files remain under project A's launch/setup context rather than receiving independent project configurations.

A second control should launch one server separately from each project and verify that each file receives the expected project-specific setup. If a future revision begins honoring multiple workspace folders, extend the probe with `workspace/didChangeWorkspaceFolders` and verify both configuration isolation and dependency invalidation before treating one process as a supported multi-project container.