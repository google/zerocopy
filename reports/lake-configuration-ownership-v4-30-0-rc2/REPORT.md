# Lake configuration ownership at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake has a split configuration-ownership model that matters for prepared and read-only dependency trees.

The durable source configuration belongs to each package: a package is loaded from its own `lakefile.lean`, `lakefile.toml`, or explicitly selected configuration file, and the resulting in-memory `Package` records its own directory, configuration file, `PackageConfig`, dependency declarations, and targets. The workspace then aggregates the root package plus its resolved dependency `Package` values and separately owns workspace-wide environment, system-Lake configuration, and facet state.

For **Lean-authored** package configurations, however, loading is not read-only with respect to the package source tree. Lake v4.30.0-rc2 stores the compiled configuration cache under that package's own `.lake/config/<assigned-package-name>/`: an `.olean`, a JSON `.olean.trace`, and a `.olean.lock`. This is true for dependencies as well as the root because `LoadConfig.lakeDir` is `pkgDir / ".lake"`, and dependency loading supplies the dependency's resolved directory as `pkgDir`. A missing or stale cache causes Lake to create directories, rewrite the trace, remove an obsolete `.olean`, elaborate the configuration, and write a new `.olean` in the dependency package itself.

That package-local cache nevertheless contains **workspace-relative identity**. Its trace records the package's workspace index and assigned name, in addition to the configuration-file hash, platform, Lean Git hash, and Lake `-K` options. The cache-validity test compares index and name. Consequently, the same physical dependency checkout used in workspaces that assign it different indices or names can invalidate and rewrite the same package-local cache. Lake locks the trace and a companion lock file to prevent torn `.olean`/trace pairs, but the implementation deliberately does not wait through competing reconfigurations; if it cannot acquire the exclusive configuration lock, it errors. The source comments explicitly say simultaneous reconfigures are likely to produce unexpected results.

**TOML-authored** package configuration follows a different path. Lake reads and decodes the TOML file directly into a `Package`; this path does not use the compiled Lean-configuration `.olean`/trace/lock cache. That does not make a TOML package wholly immutable during a build—build products and other Lake state are separate subjects—but it removes this particular configuration-cache write.

This report is intentionally pinned to v4.30.0-rc2. The issue inventory separately calls out the post-4.30 configuration-ownership change; behavior from Lean 4.31 or current `main` must not be projected backward into this report.

No fresh Lake executable was run. The conclusions below are source-level facts at the exact pin. Revalidation includes a small execution probe for the filesystem effects and cross-workspace cache interaction.

## Applicability

- repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- release: `v4.30.0-rc2`
- component: Lake package/workspace/configuration loading
- configuration languages: Lean DSL and TOML
- Anneal context: this is the Lean/Lake revision selected by the current Anneal toolchain research basis.

"Ownership" here means both (1) which object or package a configuration value describes and (2) where Lake places mutable persisted state used to load that configuration. Those are distinct. A dependency's compiled configuration cache is physically package-local even though part of its validity identity is assigned by the surrounding workspace.

## Findings

### Package configuration is package-local data in memory

`Lake.Config.Package.Package` is defined as "a Lake package — its location plus its configuration." At this revision it stores:

- `wsIdx`, the package's index in the current workspace;
- `baseName`, `keyName`, and the package's declared `origName`;
- `dir` and `relDir`;
- `config : PackageConfig`;
- absolute and relative configuration-file paths;
- dependency configurations, target declarations, scripts, hooks, and other package-defined state.

The package's conventional Lake directory is also package-relative. `Package.relLakeDir` is the default Lake directory (`.lake`), and `Package.lakeDir` is `self.dir / self.relLakeDir`. The package build directory is likewise `self.dir / self.config.buildDir`. Thus the package object itself treats these paths as rooted in the package, not in a global workspace cache.

Evidence: `src/lake/Lake/Config/Package.lean` blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`.

### The workspace aggregates packages but derives much of its visible configuration from the root

`Workspace` stores the root `Package`, the detected Lake environment, loaded system Lake configuration, package array/map, and facet configurations. Its directory and conventional `.lake` directory are accessors on the root package. `Workspace.config` is the root package's `PackageConfig` projected to `WorkspaceConfig`; workspace manifest and package-overrides paths are likewise rooted in the root package's directory.

This is an important distinction from dependency package state. The root's `.lake` is the workspace `.lake`, but a dependency's `Package.lakeDir` is that dependency's own `<dependency>/.lake`.

`loadWorkspaceRoot` loads the root as package index zero, then constructs the `Workspace`. Full `loadWorkspace` resolves/materializes dependencies afterward and adds their independently loaded `Package` values.

Evidence: `src/lake/Lake/Config/Workspace.lean` blob `b9c01f130240ae7c65ee298778351ddbe312374e`; `src/lake/Lake/Load/Workspace.lean` blob `9f25dd62bc752ede695a25fc20371157eb65d64b`.

### Dependency loading preserves the workspace root separately from the dependency package directory

The distinction is explicit in `loadDepPackage`. For each materialized dependency it constructs a `LoadConfig` with:

- `wsDir := ws.dir`, the root workspace directory;
- `pkgDir := <resolved dependency directory>`;
- `relPkgDir := <dependency path relative to the workspace>`;
- `pkgIdx := wsIdx`, the package's current workspace index;
- `pkgName := dep.name`, the assigned dependency name;
- the dependency's configuration file, Lake options, Lean options, scope, and remote URL.

Therefore both the surrounding-workspace identity and the dependency's physical package location are available during configuration loading. Which one is used for persisted configuration state is a substantive choice rather than an unavoidable consequence of the data model.

Evidence: `src/lake/Lake/Load/Resolve.lean` blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`.

### At v4.30.0-rc2, `LoadConfig.lakeDir` selects the package directory, not the workspace directory

`LoadConfig` contains both `wsDir` and `pkgDir`. At this pin:

```text
LoadConfig.lakeDir = cfg.pkgDir / defaultLakeDir
```

This one definition determines the placement used by the Lean-configuration compilation path described below. Since dependency loading supplies the dependency checkout as `pkgDir`, the dependency's configuration cache is physically under the dependency checkout.

Evidence: `src/lake/Lake/Load/Config.lean` blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`.

### Lean configuration files are compiled into package-local mutable cache files

`importConfigFile` derives:

```text
configDir = cfg.lakeDir / "config" / <assigned package name>
olean      = configDir / <config filename with .olean extension>
trace      = configDir / <config filename with .olean.trace extension>
lock       = configDir / <config filename with .olean.lock extension>
```

Because `cfg.lakeDir` is package-local at this revision, a dependency named `foo` with a conventional `lakefile.lean` uses a path of the form:

```text
<dependency checkout>/.lake/config/foo/lakefile.olean
<dependency checkout>/.lake/config/foo/lakefile.olean.trace
<dependency checkout>/.lake/config/foo/lakefile.olean.lock
```

The function calls `IO.FS.createDirAll configDir` before deciding whether an existing compiled configuration can be reused. If no trace exists, it creates one. When re-elaborating it removes an old `.olean`, writes/truncates the trace, elaborates the package configuration, and calls `Lean.writeModule` for the new `.olean`.

For this part of Lake alone, a dependency source directory is therefore not generally consumable as a pristine read-only tree. A pre-existing matching cache may avoid re-elaboration, but a missing or invalid cache needs package-local writes. Whole-package read-only behavior also depends on build artifacts, manifests, release caches, and other state and is outside this report.

Evidence: `src/lake/Lake/Load/Lean/Elab.lean` blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`; `src/lake/Lake/Load/Config.lean` blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`.

### The package-local compiled cache contains workspace-assigned identity

The `.olean.trace` is a JSON serialization of `ConfigTrace` with:

- `idx : Nat` — the package's index in this workspace;
- `name : Name` — the assigned package name;
- `platform : String`;
- `leanHash : String` — the selected Lean Git hash;
- `configHash : Hash` — content hash of the configuration file;
- `options : NameMap String` — Lake configuration options supplied through `-K`/dependency options.

A cached `.olean` is considered up to date only if it exists and the trace's `idx`, `name`, configuration hash, platform, and Lean hash match the current load. The validation test does **not** treat the physical cache location as purely a content-addressed package artifact: workspace index and assigned package name are part of its validity identity.

This creates an ownership mismatch at this pin. The cache bytes live under the package, while two identity fields come from the containing workspace. If two workspaces assign the same shared checkout different package indices or assigned names, each can make the other's trace stale and force a rewrite of the same package-local configuration cache.

Evidence: `src/lake/Lake/Load/Lean/Elab.lean` blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`; dependency assignment in `src/lake/Lake/Load/Resolve.lean` blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`.

### Configuration-cache locking protects consistency but does not make competing reconfiguration transparent

Lake's source documents the race it is protecting against: one process writing a new configuration while another reads an old `.olean`/trace pair. Readers take a shared lock on the trace. A stale reader that needs to reconfigure first tries to acquire the companion `.olean.lock`, then releases/reopens the trace and takes an exclusive trace lock.

The lock acquisition is deliberately non-blocking at a key transition. The implementation explains that waiting can deadlock when multiple processes hold shared trace locks, and it also says simultaneous reconfigures are likely to produce unexpected results. If the exclusive configuration lock cannot be acquired, Lake reports:

```text
could not acquire an exclusive configuration lock; another process may already be reconfiguring the package
```

Therefore the exact-pin source supports a narrower concurrency claim than "safe shared immutable dependency cache": it has synchronization intended to avoid inconsistent `.olean`/trace pairs, but simultaneous consumers that both require reconfiguration may fail rather than serialize transparently. A consumer whose cache is already valid takes only the shared trace lock on this path.

Evidence: `src/lake/Lake/Load/Lean/Elab.lean` blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`.

### `-K` options are persisted in the configuration trace and are not part of the ordinary up-to-date predicate

When Lake first elaborates a configuration, it writes `cfg.lakeOpts` into `ConfigTrace.options`. When an existing trace is valid, the up-to-date predicate compares the package index/name, file hash, platform, and Lean Git hash—but not `cfg.lakeOpts`. If another part of the trace is stale and Lake re-elaborates without explicit `reconfigure`, it reuses `trace.options`. With `reconfigure` set, it instead elaborates using current `cfg.lakeOpts`.

Thus the compiled configuration cache owns a persisted copy of the option map. At this pin, changing current `-K` input alone is not shown by this source path to invalidate an otherwise valid cached configuration. `--reconfigure` (`-R`) is the explicit mechanism that bypasses reuse and applies current options.

This report records the source behavior rather than inferring a user-level compatibility promise. A fresh exact-pin probe is the cheapest way to preserve the observable CLI consequence.

Evidence: `src/lake/Lake/Load/Lean/Elab.lean` blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`; `LoadConfig.lakeOpts` and `reconfigure` in `src/lake/Lake/Load/Config.lean` blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`.

### TOML package configuration has no analogous compiled-configuration cache in this load path

`loadTomlConfig` reads `cfg.configFile`, parses TOML, decodes `PackageConfig`, dependencies, targets, and defaults, and returns the resulting `Package` directly. Unlike `loadLeanConfig`, this path does not call `importConfigFile` and does not create the Lean configuration `.olean`, trace, or lock files.

This distinction is specific to configuration loading. A TOML-configured package can still have mutable package-local build outputs and other Lake files.

Evidence: `src/lake/Lake/Load/Toml.lean` blob `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`; dispatch in `src/lake/Lake/Load/Package.lean` blob `e9e858a54048ffa96972d264dbd51ca35b4ba403`.

### The loaded `Package` normalizes both configuration languages into the same package/workspace model

`loadLeanConfig` elaborates/imports the Lean configuration, extracts the package declaration and persistent Lake extension data, and constructs a `Package` with `wsIdx`, assigned and original names, package/config paths, scope, remote URL, dependencies, targets, scripts, and hooks. `loadTomlConfig` decodes the same broad package model directly from TOML. `loadPackageCore` selects the language from the resolved configuration-file extension.

After this point the `Workspace` contains `Package` values, not a separate long-lived ownership model for Lean-versus-TOML configuration. The important persistent difference is how Lean configuration is cached before that package value is reconstructed.

Evidence: `src/lake/Lake/Load/Lean.lean` blob `b38ee619b42d8293fc9e4ffb4b8e2f4b1508c1e7`; `src/lake/Lake/Load/Toml.lean` blob `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`; `src/lake/Lake/Load/Package.lean` blob `e9e858a54048ffa96972d264dbd51ca35b4ba403`.

## Boundaries

This report does **not** generalize to Lake after v4.30.0-rc2. The Anneal reference inventory deliberately tracks "Lake configuration ownership after the Lean 4.31 change" as a separate subject. Revalidate the relevant definitions rather than assuming continuity in either direction.

It also does not claim that all package-local mutation comes from configuration compilation. Build outputs, artifact caches, source materialization, package manifests, downloaded release artifacts, and server preparation have separate ownership and write behavior.

The source-level analysis establishes the paths Lake computes and the I/O operations it invokes. It does not establish filesystem-specific lock semantics on NFS or other unusual filesystems, nor does it measure contention behavior.

The report does not claim that changing `-K` options is *intended* never to invalidate a cached configuration. It records that the ordinary exact-pin `ConfigTrace` up-to-date predicate does not compare current `cfg.lakeOpts`, while forced reconfiguration uses current options and stale-trace re-elaboration otherwise uses persisted trace options.

No fresh exact-pin execution was performed. In particular, the predicted cross-workspace rewrite/error behavior follows directly from the package-local cache path plus the trace identity and locking algorithm, but the revalidation probe below should preserve an executable specimen when a Lean-capable surface is available.

## Evidence

Primary pinned source:

- `src/lake/Lake/Load/Config.lean`, blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`: `LoadConfig`; separate `wsDir`/`pkgDir`; package-local `LoadConfig.lakeDir`; `lakeOpts`; `reconfigure`.
- `src/lake/Lake/Load/Lean/Elab.lean`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`: Lean configuration `.olean`/trace/lock path, trace schema and validity, locking, re-elaboration, option persistence, and module write.
- `src/lake/Lake/Load/Lean.lean`, blob `b38ee619b42d8293fc9e4ffb4b8e2f4b1508c1e7`: construction of `Package` from a Lean-authored configuration.
- `src/lake/Lake/Load/Toml.lean`, blob `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`: direct TOML configuration decoding and construction of `Package`.
- `src/lake/Lake/Load/Package.lean`, blob `e9e858a54048ffa96972d264dbd51ca35b4ba403`: package-configuration file resolution and Lean/TOML dispatch.
- `src/lake/Lake/Load/Resolve.lean`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`: dependency `LoadConfig`, including root `wsDir` plus dependency `pkgDir`, workspace index, and assigned name.
- `src/lake/Lake/Load/Workspace.lean`, blob `9f25dd62bc752ede695a25fc20371157eb65d64b`: root loading and construction of the complete workspace.
- `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: package data model, package-local `.lake`, manifest, and build-directory accessors.
- `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`: workspace data model and root-derived workspace paths/configuration.

Evidence class: immutable source inspection at the exact revision. There is no fresh execution evidence in this report.

## Revalidation

For source-only revalidation of this exact claim on another Lake revision, inspect these decision points in order:

1. `LoadConfig`: determine whether the configuration cache root is derived from `pkgDir`, `wsDir`, or another explicit directory.
2. `loadDepPackage` or its successor: record the values supplied for workspace root, dependency package directory, package index, and assigned package name.
3. Lean configuration loading: record the `.olean`, trace, and lock locations; the trace fields; the up-to-date predicate; the values used on re-elaboration; and locking behavior.
4. TOML loading: verify whether it still parses directly or has acquired an analogous persistent cache.
5. `Package` and `Workspace`: distinguish package-local paths/configuration from root/workspace-owned state.

A minimal exact-pin execution specimen should create one Lean-configured dependency and two root workspaces that refer to the same physical dependency checkout but place it at different dependency indices. Then:

1. Delete the dependency's `.lake` directory.
2. Load workspace A and record the files created under the dependency checkout plus the JSON trace contents.
3. Load workspace B and confirm whether the trace's `idx` changes and the configuration `.olean` is rewritten.
4. Load A again and observe whether it rewrites back.
5. Repeat with concurrent loads after deliberately making the shared trace stale; record whether one receives the documented exclusive-lock error.
6. Make the dependency tree read-only with no compiled configuration cache and confirm the first Lean-configuration load fails on the package-local write. Then seed an exactly matching cache, make it read-only, and test the narrower cached-read path separately.
7. Repeat the same dependency as `lakefile.toml` and confirm that this configuration-cache directory is not created by configuration loading alone.
8. For option ownership, load a Lean package with `-K x=one`, then invoke without `-R` using `-K x=two`; inspect the trace and observable package configuration. Repeat with `-R` to distinguish ordinary reuse from forced reconfiguration.

Preserve the two-workspace fixture, trace snapshots, directory listings, command output, and exact toolchain identity as support files if this probe is promoted into the reference corpus. Do not use a successful v4.30.0-rc2 probe as evidence for the separately tracked post-4.31 ownership model.