# Lake command and environment reproducibility inputs at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), a Lake command is not determined by a workspace tree plus the `lake` executable alone. Lake constructs an explicit `Lake.Env` from installation discovery and process environment, then combines it with command-line options to build a `LoadConfig` and, for build-like commands, a `BuildConfig`. Those inputs select the workspace and configuration file, package overrides, package-configuration options, dependency-update policy, Lean identity, source and binary search paths, package URL remapping, registry endpoints, cache location/policy, and the incremental-build validation mode.

The most important reproducibility distinction is between **inputs that choose semantic state** and **inputs that only change presentation**. `--dir`, `--file`, `--packages`, `-K`, `--update`, `--keep-toolchain`, `--reconfigure`, `ELAN_TOOLCHAIN`, `LEAN`/`LEAN_SYSROOT`, `LAKE_OVERRIDE_LEAN`, `LEAN_GITHASH`, `LAKE_PKG_URL_MAP`, the Reservoir endpoint variables, and inherited/search-path variables can change which configuration, dependencies, compiler identity, imports, or tools Lake uses. `--old` and `--rehash` change how Lake validates reuse. Cache controls can change whether Lake reconstructs state from local or remote artifacts. By contrast, verbosity, output formatting, ANSI, and failure-reporting thresholds generally change reporting rather than the selected program state.

Several precedence rules are source-defined and should be made explicit by a reproducible caller. `--no-cache` / `--try-cache` override `LAKE_NO_CACHE` for that invocation. `LAKE_CACHE_DIR`, when set, selects the cache path directly; an empty value disables the system cache. `ELAN_TOOLCHAIN` supplies Lake's preferred toolchain string when present. `LEAN_GITHASH` can deliberately replace the detected Lean Git hash used in Lake build traces. `LEAN_SYSROOT` takes precedence over `LEAN` during Lean installation discovery, and `LAKE_OVERRIDE_LEAN=true` forces separate Lean discovery even when Lake and Lean appear collocated.

The command line also contains a revision-specific trap: `--offline` is parsed into `LakeOptions.offline`, but ordinary `lake build` creates its `LoadConfig` without that field. In this revision the option is passed explicitly by `lake new` and `lake init`; it is not a general build-time network-denial switch. The dedicated read-only/offline report owns the complete network boundary, but a reproducibility profile must not record `lake build --offline` as though it closed that boundary.

`lake env` exposes the normalized environment Lake intends children to see. Without a workspace, it exports the detected Lake/Lean installation, selected toolchain, cache and package-URL settings, Lean search paths, Lean identity, and executable path. With a workspace, it additionally prepends package build/source paths and fixes the selected workspace cache. This makes `lake env` a useful *observable projection* of important execution inputs, but not a complete semantic fingerprint: package configuration, manifests, source files, CLI build flags, platform, arbitrary child-process environment dependencies, and external tool contents remain outside that printed mapping.

For Anneal, the robust rule is to treat the **effective Lake invocation** as part of prepared-environment identity. Record the exact Lean/Lake pin and workspace tree, but also normalize or record the command options and environment values that can select dependencies, package configuration, toolchain/compiler identity, search paths, cache/materialization sources, or freshness behavior. Do not assume that two invocations against identical files are equivalent merely because both say `lake build`.

Basis: exact pinned Lake source plus derived control-flow consequences. No fresh Lake, Lean, Elan, Git, Reservoir, cache, or compiler execution was performed.

## Applicability

This report applies to Lake shipped in:

- repository `leanprover/lean4`;
- revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`;
- release label `v4.30.0-rc2`.

The subject is the command/environment input surface relevant to reproducibility: installation discovery, `Lake.Env`, top-level Lake options, `LoadConfig`, `BuildConfig`, workspace environment augmentation, and the system Lake configuration file. The report identifies inputs whose values can alter selected state or reuse behavior; it does not claim that every listed input changes bytes for every package.

This report deliberately delegates detailed mechanisms to narrower corpus reports:

- dependency resolution and manifest locking govern how selected dependency declarations become a locked graph;
- Git-versus-path and prepared-environment reports govern materialization and network behavior;
- `.lake/config` reports govern compiled package-configuration caching;
- artifact-cache reports govern cache keys, restoration, publication, and concurrency;
- Lake state/reuse reports govern trace, mtime, hash, and `--old` algorithms;
- Lean CLI/server reports govern the selected Lean process after Lake has prepared its environment.

The report also does not attempt to enumerate every environment variable that arbitrary user scripts, C/C++ toolchains, Git, curl, shell commands, or other subprocesses might inspect. Those processes inherit an execution environment and can introduce additional package-specific inputs. The inventory here is the Lake-defined surface plus directly selected Lean/tool inputs visible in the pinned implementation.

## Findings

### Lake computes one explicit option state before loading a workspace

`LakeOptions` is the top-level parsed command state. At this revision its state includes:

- workspace root and configuration file;
- `-K` configuration options and package overrides;
- dependency-update, toolchain-update, and reconfiguration policy;
- old-mode, hash-trust, and no-build flags;
- cache download policy;
- the parsed `offline` flag;
- output/reporting controls; and
- cache-command-specific service/scope/platform/toolchain/revision options.

`LakeOptions.mkLoadConfig` resolves the selected workspace root, computes `Lake.Env`, and transfers only the load-relevant fields into `LoadConfig`: the original Lake arguments, workspace root, selected config file, package overrides, `-K` options, reconfiguration flag, dependency-update flag, and toolchain-update flag. `mkBuildConfig` separately transfers `oldMode`, `trustHash`, `noBuild`, logging, and build-output mapping state.

This split matters for reproducibility. A flag being parsed by the CLI does not imply that it participates in workspace loading or building. The caller must trace it to the action that consumes it.

Basis: Lake **source**.

### `--dir` and `--file` select the workspace/configuration identity

`-d` / `--dir` changes `LakeOptions.rootDir`; `-f` / `--file` changes the package configuration filename. `mkLoadConfig` resolves the root to an absolute `wsDir` and carries the configuration path as `relConfigFile`. `LoadConfig.configFile` is then `pkgDir / relConfigFile`.

The same command text run with a different current directory, `--dir`, or config filename can therefore load a different root package and manifest graph. A reproducible invocation should make the intended root/config path explicit instead of depending on ambient current-working-directory discovery.

Basis: Lake **source**.

### `--packages` can replace dependency-package source selection

`--packages <file>` parses package entries from the supplied manifest-format file and appends them to `LakeOptions.packageOverrides`. Those entries become `LoadConfig.packageOverrides` and participate in workspace loading.

Package overrides are not a presentation option. They can select different package materializations than the workspace manifest/dependency declarations would otherwise use. A record of a reproducible invocation that permits `--packages` must preserve the override file bytes and their position in the effective option state.

Basis: Lake **source**.

### `-K` is an input to Lean-authored package configuration

Each `-Kkey=value` inserts into `LakeOptions.configOpts`; `mkLoadConfig` passes the map as `LoadConfig.lakeOpts`. Package configuration elaboration can consume that map.

At this exact revision, the compiled `.lake/config` cache has unusual option persistence semantics: a cache hit does not compare the current `-K` map, and some automatic re-elaboration paths reuse options stored in the old trace. That behavior is documented by the dedicated `.lake/config` report. The reproducibility consequence here is simpler: the effective `-K` map is a declared configuration input and should be recorded, while a caller must not infer from current CLI text alone which option map a reused cached package configuration embodies.

Basis: Lake **source** + cross-report boundary.

### `--update`, `--keep-toolchain`, and `--reconfigure` change load semantics

`--update` sets `LoadConfig.updateDeps`; ordinary `loadWorkspace` can then update/materialize dependencies instead of only consuming locked state. `--keep-toolchain` clears the default `updateToolchain` behavior used during dependency updates. `--reconfigure` tells package loading to re-elaborate Lean-authored configuration instead of reusing the compiled configuration cache.

These flags can change persistent workspace/package state and the state from which a build proceeds. They therefore belong in any invocation identity that is intended to distinguish a pure consumer from a workspace-updating or configuration-regenerating run.

Basis: Lake **source**.

### `--old`, `--rehash`, and `--no-build` change validation behavior, not source identity

`BuildConfig` records three important validation controls:

- `--old` sets `oldMode`, enabling modification-time fallback behavior documented by the separate `--old`/reuse reports;
- `-H` / `--rehash` sets `trustHash := false`, causing Lake not to trust persisted `.hash` sidecars where the build machinery consults that policy;
- `--no-build` sets `noBuild`, causing an early failure when a build action is required, while still permitting some pre-build/cache-side effects documented in the `.trace.nobuild` report.

These options do not choose a different source graph directly, but they can change whether existing prepared state is accepted, rehashed, or rejected. Reproducibility claims about “reused without rebuild” therefore need the build-validation mode as part of their evidence.

Basis: Lake **source**.

### `--no-cache` and `--try-cache` override `LAKE_NO_CACHE`

`Lake.Env.compute` receives `LakeOptions.noCache : Option Bool`. If the command-line option is present, it wins; otherwise Lake parses `LAKE_NO_CACHE`; otherwise the value defaults to false. The CLI maps `--no-cache` to `some true` and `--try-cache` to `some false`.

This is an explicit precedence rule. A hermetic command wrapper cannot understand cache-download behavior from the environment alone if it permits either CLI override.

`LAKE_ARTIFACT_CACHE` is separate. Lake parses it into `enableArtifactCache?`, which controls the local artifact-cache default when package/workspace configuration does not override it. `LAKE_CACHE_DIR` selects where Lake's cache state lives. The dedicated artifact-cache report owns the detailed read/write and key semantics.

Basis: Lake **source**.

### `LAKE_CACHE_DIR` has a three-way meaning

When `LAKE_CACHE_DIR` is absent, Lake chooses a cache using the detected Elan toolchain when possible and otherwise the user/system cache directory. When it is present and nonempty, that exact path becomes both `lakeCache?` and `lakeSystemCache?`. When it is present but empty, Lake sets `noSystemCache := true` and does not select a system cache through the normal fallback path.

Thus an empty value is not equivalent to an unset value. It explicitly disables the ordinary system-cache selection. This distinction survives into the environment Lake constructs for subprocesses.

Basis: Lake **source**.

### `ELAN_TOOLCHAIN` is a Lake-visible toolchain identity input

`Lake.Env.computeToolchain` uses `ELAN_TOOLCHAIN` when present and otherwise falls back to Lake's compiled `Lean.toolchain` string. The result is stored as `Lake.Env.toolchain` and contributes to the cache toolchain identity.

Actual executable selection by an Elan proxy can involve Elan behavior outside this repository. The pinned source establishes only Lake's use of the environment value after the Lake process is running. A reproducibility record should therefore distinguish “which executable was actually launched” from the `ELAN_TOOLCHAIN` string Lake records and propagates.

Basis: Lake **source** + explicit boundary.

### Lean installation discovery is environment-sensitive

At startup, Lake calls `findInstall?` and places the detected Elan, Lean, and Lake installations into `LakeOptions`. The pinned detection logic has several environment-controlled branches.

For Lean:

1. if `LEAN_SYSROOT` is set, Lake uses that sysroot;
2. otherwise it considers `LEAN`; an explicitly empty `LEAN` disables that discovery path;
3. otherwise it tries `lean` from `PATH` and asks it for `--print-prefix`.

For Lake, the running executable is inspected first; `LAKE_HOME` is a fallback installation root. For Elan, `ELAN_HOME` enables detection and `ELAN` selects the executable; an empty `ELAN` disables the detected Elan installation.

If Lake and Lean appear collocated, Lake normally treats them as one toolchain. `LAKE_OVERRIDE_LEAN=true` forces separate Lean discovery instead. Two invocations with the same repository files but different values for these variables can therefore select different compiler/install trees.

Basis: Lake **source**.

### Native compiler/archive selection is also environment-sensitive

After a Lean sysroot is selected, `LeanInstall.get` chooses the native archive/compiler tools used by Lake's Lean-native build paths.

For `ar`, the precedence is:

1. `LEAN_AR`;
2. the Lean installation's bundled `llvm-ar`, when present;
3. `AR`;
4. `ar` from `PATH`.

For the C compiler, the precedence is:

1. `LEAN_CC`;
2. the Lean installation's bundled `clang`, when present;
3. `CC`;
4. `cc` from `PATH`.

The internal bundled compiler path also changes the flags Lake associates with the compiler. Native outputs can therefore depend on more than Lean source, `.olean` identity, and target platform. A byte-reproducibility claim involving C/object/shared/executable artifacts needs the selected native tools and relevant environment/tool contents in its basis.

Basis: Lake **source**.

### `LEAN_GITHASH` can deliberately override Lake's Lean build identity

Lake detects a Lean Git hash from the selected installation, but `Lake.Env` also records `LEAN_GITHASH`. `Lake.Env.leanGithash` returns the override when nonempty; otherwise it returns the detected installation hash.

The source explicitly describes this override as a way to replace the Lean version used by a library without completely rebuilding it while testing custom Lean builds. Lake's build context hashes that selected string into its Lean trace, as documented by the dedicated Lean/Lake trace-hash report.

This is therefore a deliberate escape hatch around the normal compiler-version invalidation token. A reproducibility protocol must either fix/record `LEAN_GITHASH` or reject overrides. “Same Lake trace” is not proof that the physical Lean binary was the same when the override is available.

Basis: Lake **source** + cross-report boundary.

### `LAKE_PKG_URL_MAP` changes where named Git packages are obtained

`LAKE_PKG_URL_MAP` is parsed as JSON into a name-to-URL map in `Lake.Env`. During Git dependency materialization, Lake consults that map by dependency/package name and substitutes the mapped URL for the declared/manifest URL when present.

This variable can therefore redirect dependency acquisition without changing the checked-in `lakefile` or manifest text. If the locked exact revision is available from the replacement source, the resulting commit may still be the same; if not, materialization can fail or interact with a different repository. Either way, the environment value is part of dependency-resolution provenance.

Basis: Lake **source**.

### Reservoir endpoint variables change the registry service Lake talks to

`Lake.Env.compute` derives the registry endpoint from `RESERVOIR_API_BASE_URL` and `RESERVOIR_API_URL`. A directly supplied `RESERVOIR_API_URL` wins; otherwise Lake derives `/v1` from the base URL, whose default is `https://reservoir.lean-lang.org/api`.

Registry-backed dependency resolution uses `Lake.Env.reservoirApiUrl`. Consequently, a dependency declaration that relies on Reservoir is not fully described by package config and version constraint if these endpoint variables are unconstrained.

A locked complete manifest plus already-materialized exact dependency state can reduce or remove that live-registry dependence for a consumer path, but that is a property of the selected load/materialization path, not evidence that the environment variable is semantically irrelevant in general.

Basis: Lake **source** + dependency-resolution boundary.

### `LAKE_CONFIG` selects a system configuration file

Lake sets `Lake.Env.lakeConfig?` from `LAKE_CONFIG`; if it is absent, Lake uses the user's `~/.lake/config.toml` when a home directory is available. `loadLakeConfig` reads that file when it exists and otherwise constructs defaults.

At this revision, the system configuration primarily defines cache services and their default download/upload selections. Those settings can change where cache mappings/artifacts are obtained or published. A supposedly reproducible cache-enabled build that leaves `LAKE_CONFIG` and the user's home configuration unconstrained therefore has an ambient input even when the project tree is fixed.

Basis: Lake **source**.

### Cache endpoint/key environment variables are execution provenance even when outputs are content-addressed

Lake reads `LAKE_CACHE_KEY`, `LAKE_CACHE_ARTIFACT_ENDPOINT`, `LAKE_CACHE_REVISION_ENDPOINT`, and `LAKE_CACHE_SERVICE`. The pinned cache CLI can use them to choose download/upload endpoints and authentication, although source comments already mark environment-based service configuration as deprecated in favor of configured services for some commands.

These values do not by themselves establish a semantic difference in a successfully validated content-addressed artifact. They do change which external service is consulted and which side effects are possible. A provenance record should preserve them when remote cache use is in scope, while semantic equivalence must still be established by the artifact/cache rules rather than by endpoint identity.

Basis: Lake **source** + boundary.

### `LEAN_PATH`, `LEAN_SRC_PATH`, `PATH`, and the shared-library path feed Lake's execution environment

`Lake.Env` captures the initial `LEAN_PATH`, `LEAN_SRC_PATH`, platform shared-library search path, and `PATH`. It then builds normalized paths around the detected Lake/Lean installations.

A loaded `Workspace` augments those values further:

- package binary directories are prepended to `PATH`;
- package Lean library directories are prepended to `LEAN_PATH`;
- package source directories are prepended to `LEAN_SRC_PATH`;
- workspace shared-library directories participate in the platform's dynamic-library search path.

`lake env` either exports `Lake.Env.vars` when no workspace config exists or `Workspace.augmentedEnvVars` after loading a workspace. This behavior makes dependency/package outputs available to spawned tools, but it also means ambient search paths can resolve names/tools differently unless the caller controls them.

Basis: Lake **source**.

### `lake env` is an observable projection, not a complete invocation digest

The base environment exported by Lake includes values such as `ELAN`, `ELAN_HOME`, `ELAN_TOOLCHAIN`, `LAKE`, `LAKE_HOME`, `LAKE_CONFIG`, `LAKE_PKG_URL_MAP`, `LAKE_NO_CACHE`, cache service variables, `LEAN`, `LEAN_SYSROOT`, `LEAN_AR`, and optionally `LEAN_CC`. `Lake.Env.vars` adds cache path/policy, Lean search paths, selected Lean Git hash, and `PATH`; workspace augmentation substitutes workspace-aware search paths and cache state.

This is useful for diagnostics and for spawning a child in the same prepared environment. It is not a complete reproducibility fingerprint. Notably, it does not encode the bytes of the workspace, manifest, package/configuration files, package overrides, `-K` map, `BuildConfig` flags such as `--old`/`--rehash`, platform executable contents, arbitrary subprocess environment reads, or the contents of remote/cache services.

For Anneal, preserving `lake env` output is useful evidence, but it should be paired with the normalized Lake command, immutable source/configuration identities, and prepared artifact identities.

Basis: Lake **source** + derived consequence.

### `--offline` is not part of ordinary build loading at this pin

The CLI parses `--offline` into `LakeOptions.offline`. `lake new` and `lake init` explicitly pass that field into their actions. `LakeOptions.mkLoadConfig` does not contain an offline field, and `lake build` simply calls `mkLoadConfig`, `loadWorkspace`, and `mkBuildConfig`—none of which receives `LakeOptions.offline` from this path.

Thus the parsed flag is not a general build-time network prohibition in v4.30.0-rc2. A wrapper that wants a network-free build must establish that property through prepared local state and an external network-denial mechanism or a separately verified command path.

The dedicated read-only/offline report contains the wider list of dependency/cache paths that can attempt network access. This finding records only the command/environment reproducibility implication.

Basis: Lake **source** + derived control-flow consequence.

### Reporting flags should not be confused with semantic-state inputs

Lake also parses verbosity, text/JSON output format, log/fail levels, ANSI policy, and similar user-interface options. These can change stdout/stderr, diagnostic thresholds, progress rendering, or process failure policy without changing the selected dependency/configuration graph.

They still matter to a protocol that treats exact diagnostics or exit status as an output. They should not, however, be mixed into the same category as source/toolchain/cache selection when defining semantic build identity. A useful reproducibility record separates **semantic/build-state inputs** from **observation/reporting inputs**.

Basis: Lake **source** + classification.

### A practical reproducibility basis is layered rather than one environment hash

The pinned implementation suggests four layers for a reproducible Lake run:

1. **Immutable subject identity:** exact Lean/Lake revision, platform/toolchain binaries, project/package sources, manifest and configuration bytes.
2. **Load selection:** workspace root/config file, package overrides, `-K`, update/reconfigure policy, URL/registry remapping, selected Lean/Lake installations.
3. **Build/reuse policy:** `--old`, hash trust/rehash, no-build behavior, artifact-cache policy/location and any remote-cache provenance.
4. **Execution environment:** normalized Lean/source/binary/shared-library search paths plus native compiler/archive tools and package-specific subprocess inputs.

No single variable in the inspected Lake source combines these into a canonical content identity. Anneal should therefore make the relevant layer inputs explicit rather than inventing a claim that `lake env`, `lean-toolchain`, the manifest, or the Lake trace alone identifies the whole build.

Basis: **derived** synthesis from pinned source.

## Boundaries

- No fresh Lake, Lean, Elan, Git, Reservoir, cache-service, C compiler, linker, or filesystem execution was performed.
- This is a Lake-defined input inventory, not a complete audit of every environment variable visible to arbitrary package scripts or subprocesses.
- The report does not establish the external Elan proxy's complete toolchain-selection precedence. It records how the running Lake process detects and propagates Elan/Lean state.
- The report does not re-establish artifact-cache correctness, collision properties, remote-service trust, or cache concurrency. Those belong to the artifact-cache reports.
- The report does not claim that changing a listed variable necessarily changes output bytes. Some inputs affect only acquisition path, cache availability, validation policy, or child-process lookup for a given workload.
- Conversely, absence from the Lake-defined list does not make an arbitrary environment variable irrelevant. User scripts, Git, curl, compilers, linkers, dynamic loaders, and other tools may consume additional state.
- `lake env` output is not a cryptographic or semantic digest of a workspace/build state.
- The command-line option inventory is scoped to the general/load/build path needed by this subject. Cache subcommand switches such as service/scope/platform/revision controls are noted only where they illustrate external-state selection, not exhaustively specified.
- The report does not generalize the `--offline` control-flow observation to adjacent Lake revisions.
- Exact diagnostics and exit-code reproducibility may require reporting options even when they do not change semantic program state.

## Evidence

Primary subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/lake/Lake/CLI/Main.lean`, blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`: `LakeOptions`; `mkLoadConfig`; `mkBuildConfig`; `-d`, `-f`, `-K`, `--packages`, update/reconfigure/build/cache/offline option parsing; `lake build`; `lake env`; explicit `offline` forwarding by `new`/`init`.
- `src/lake/Lake/Load/Config.lean`, blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`: `LoadConfig` fields and workspace/package/configuration path derivation.
- `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`: environment ingestion, toolchain string, package URL map, Reservoir endpoints, cache settings, system configuration path, Lean Git-hash override, search paths, and environment export.
- `src/lake/Lake/Config/InstallPath.lean`, blob `e309253fe8c39aa90ce48de295305d160286a9b1`: Elan/Lean/Lake installation detection; `LEAN_SYSROOT`/`LEAN`/`LAKE_HOME`/`LAKE_OVERRIDE_LEAN`; Lean Git-hash detection; `LEAN_AR`/`AR` and `LEAN_CC`/`CC` precedence.
- `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`: workspace-augmented `PATH`, `LEAN_PATH`, `LEAN_SRC_PATH`, shared-library path, cache directory, and Lean identity exported to child processes.
- `src/lake/Lake/Load/Toml.lean`, blob `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`: loading `LAKE_CONFIG`/default system TOML and cache-service defaults.
- `src/lake/Lake/Build/Context.lean`, blob `8f2eda8d462334f933f112d7ebc4acd3e9553568`: `BuildConfig.oldMode`, `trustHash`, and `noBuild` semantics.
- `src/lake/Lake/Load/Materialize.lean`, blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`: use of `lakeEnv.pkgUrlMap` during configured and locked Git materialization.
- `src/lake/Lake/Load/Resolve.lean`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`: update/materialization behavior reached through `LoadConfig.updateDeps` and toolchain-update policy.
- `src/lake/Lake/Load/Workspace.lean`, blob `9f25dd62bc752ede695a25fc20371157eb65d64b`: ordinary load selection between manifest materialization and update/materialization.
- `src/lake/Lake/Load/Lean/Elab.lean`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`: use of package configuration options and selected `lakeEnv.leanGithash` in compiled configuration state.

No fresh **execution** evidence was produced in this report.

## Revalidation

For a future Lake revision, first diff the exact source areas above, especially `LakeOptions`, `mkLoadConfig`, `mkBuildConfig`, `Env.compute`, installation detection, and environment export. Search for newly added/removed environment variables and for command-line fields whose propagation changed.

On a capable execution surface, use one minimal pinned workspace and record a matrix that changes one input at a time while preserving all others. At minimum cover:

1. `--dir` / `--file` and current working directory;
2. one `--packages` override;
3. one `-K` option with and without explicit `--reconfigure`;
4. ordinary locked load versus `--update` and `--keep-toolchain`;
5. default build validation versus `--old` and `--rehash`;
6. `LAKE_NO_CACHE` with CLI `--try-cache`/`--no-cache` precedence;
7. unset, empty, and explicit `LAKE_CACHE_DIR`;
8. `ELAN_TOOLCHAIN`, `LEAN_SYSROOT`, `LEAN`, and `LAKE_OVERRIDE_LEAN` installation selection;
9. detected Lean Git hash versus a deliberately distinct `LEAN_GITHASH` override;
10. `LEAN_AR`/`AR` and `LEAN_CC`/`CC` selection where native outputs are built;
11. `LAKE_PKG_URL_MAP` and Reservoir endpoint substitution against a controlled local/fake service;
12. `LAKE_CONFIG` absent, missing-path, and explicit controlled TOML;
13. `LEAN_PATH`, `LEAN_SRC_PATH`, `PATH`, and shared-library-path changes with deliberately ambiguous candidate files/tools;
14. `lake env` output with and without a loaded workspace;
15. `lake build --offline` under hard network denial, to preserve the revision-specific distinction between parsed CLI state and actual build-time network behavior.

For each case preserve the exact argv, current directory, relevant environment mapping, `lake env` projection, selected install/tool paths, manifest/config/package bytes, trace/hash changes, filesystem mutations, network attempts, stdout/stderr, and exit code. Where native outputs are involved, also hash the selected compiler/archive binaries and resulting artifacts.

That probe can establish concrete behavior for the tested environment. It still does not prove hermeticity for arbitrary package scripts or tools; those require either sandbox-enforced input closure or workload-specific dependency tracing.