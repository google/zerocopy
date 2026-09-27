# Lake configuration ownership after the Lean 4.31 hoisting change

## Summary

Lean `v4.31.0` contains Lake change `41ecccec6d1244c5f89be2fc76638f22ba37cbc6` (`#13683`, “hoist compiled configurations”). The change fixes the main ownership mismatch documented for `v4.30.0-rc2`: compiled Lean package configurations no longer live under the dependency package's own `.lake/config/<assigned-name>`. At `leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783`, `LoadConfig.configDir` is instead

```text
<workspace>/.lake/config/<workspace-package-index>
```

and `importConfigFile` stores the configuration `.olean`, `.olean.trace`, and `.olean.lock` there. The upstream commit message states the purpose directly: remove a potential source of contention between workspaces that share a dependency.

This changes the concurrency and immutability boundary materially. Two different workspace roots that load the same physical dependency no longer read and rewrite the same compiled-configuration files merely because the dependency checkout is shared. Each workspace owns its own configuration-cache slots. The trace still records the package's workspace index and assigned name, so workspace-relative identity now lives in workspace-owned persisted state instead of package-owned persisted state.

The change is narrower than “Lake no longer writes dependency trees.” `LoadConfig.lakeDir` remains package-local, package build products remain package-local, and the `v4.31.0` missing-trace branch of `importConfigFile` still calls `IO.FS.createDirAll cfg.lakeDir` even though the compiled files themselves are written through `cfg.configDir`. A pristine read-only dependency checkout with no `.lake` directory can therefore still encounter a package-local directory-creation attempt during Lean-configuration loading. Other package-local mutation sources are separate subjects.

TOML-authored package configuration remains direct parse/decode and does not produce a compiled-configuration `.olean` in this path. The checked-in Lake dependency example explicitly tests the new placement: Lean-configured workspaces acquire numeric `.lake/config/0`, `.lake/config/1`, … directories under each workspace root, while a TOML-configured root does not get its own compiled configuration slot.

No fresh Lake process was run for this report. The core placement result is established by the exact `v4.31.0` source, the introducing commit and its regression test. The residual package-local `createDirAll` observation is source-level and should be execution-probed before using the change as a general read-only-dependency guarantee.

## Applicability

This report applies to:

- repository `leanprover/lean4`;
- release `v4.31.0`;
- revision `68218e876d2a38b1985b8590fff244a83c321783`;
- Lake's package/workspace loading and Lean-authored configuration compilation.

It is intentionally separate from `reports/lake-configuration-ownership-v4-30-0-rc2`. Current Anneal research is pinned to Lean `v4.30.0-rc2`; this report records the adjacent-version change so that a future upgrade does not accidentally project either ownership model across the boundary.

“Configuration ownership” has two meanings here. The source configuration still describes one package and is loaded from that package's `lakefile.lean` or `lakefile.toml`. The changed ownership is the **persisted compiled Lean configuration state** used while reconstructing that package inside a workspace.

## Findings

### Lean 4.31 deliberately hoists compiled package configurations into the workspace

Commit `41ecccec6d1244c5f89be2fc76638f22ba37cbc6`, merged as `#13683`, changes only the key placement decision and its regression test. It adds:

```lean
LoadConfig.configDir =
  cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx
```

and changes `importConfigFile` from deriving its directory from `cfg.lakeDir / "config" / <assigned-package-name>` to using `cfg.configDir`.

The commit message describes the intent as moving compiled Lake configurations from a package's `.lake/config` to the workspace's `.lake/config` to remove contention between workspaces sharing a dependency. The commit is an ancestor of `v4.31.0`; the release is 115 commits ahead of it with no divergence.

Basis: **repository history** plus exact-release **source**.

### The persisted files are workspace-owned and indexed by workspace package position

At `v4.31.0`, `importConfigFile` computes `configDir := cfg.configDir`, creates that directory, and places three files beneath it using the configuration filename:

```text
<workspace>/.lake/config/<idx>/lakefile.olean
<workspace>/.lake/config/<idx>/lakefile.olean.trace
<workspace>/.lake/config/<idx>/lakefile.olean.lock
```

The directory key is the decimal workspace package index, not the assigned package name. The root package has index zero; dependencies are assigned indices as they are added to the workspace.

The checked-in `tests/lake/examples/deps/test.sh` makes this layout an explicit regression property. After building its Lean-configured examples it requires `foo/.lake/config/0` through `/3` and `bar/.lake/config/0` through `/4`. After rebuilding with a TOML root, it requires no root slot at `foo/.lake/config/0` or `bar/.lake/config/0`, while Lean-configured dependencies still occupy later numeric slots.

Basis: exact-release **source** and checked-in **test artifact**.

### Workspace-relative trace identity now matches the physical ownership domain

The `ConfigTrace` schema still contains:

- `idx`, the package's workspace index;
- `name`, the assigned package name;
- `platform`;
- `leanHash`;
- `configHash`; and
- persisted Lake configuration `options`.

The normal up-to-date test still requires the `.olean` to exist and compares `idx`, `name`, configuration hash, platform, and Lean Git hash.

In `v4.30.0-rc2`, these workspace-derived `idx` and `name` fields lived in a cache stored in the dependency package itself. Two independent workspaces could therefore invalidate and rewrite the same package-local cache when they assigned different identities. In `v4.31.0`, the same identity is stored under the owning workspace. Different workspace roots naturally have different `.lake/config` trees, so their index/name choices no longer fight over one dependency-local trace.

The trace's `name` check remains meaningful even though the directory is keyed by index. Renaming the package at the same index makes the slot stale and causes re-elaboration. Moving a package to a different index selects a different slot.

Basis: exact-release **source**; cross-version interpretation is **derived** by comparing the two pinned implementations.

### Shared dependency source no longer implies shared compiled-configuration state

`mkDepLoadConfig` still passes both identities separately:

- `wsDir := ws.dir`, the root workspace directory;
- `pkgDir := dep.pkgDir`, the physical dependency directory;
- `pkgIdx := ws.packages.size`; and
- `pkgName := dep.name`.

The hoisting change chooses `wsDir` for compiled configuration state while leaving the dependency's source/configuration path rooted in `pkgDir`.

Therefore two workspaces can point at the same physical path dependency yet maintain independent compiled configuration `.olean`/trace/lock files. This directly removes the cross-workspace configuration-cache contention described in the `v4.30.0-rc2` report.

This does not imply that all other state is workspace-owned. The loaded `Package` still records the dependency's own directory and configuration, and its build directory remains derived from the package directory and package configuration.

Basis: exact-release **source**.

### Concurrency protection still matters inside one workspace cache

The locking algorithm in `importConfigFile` remains materially the same. A reader uses a shared lock on the trace. Reconfiguration attempts to acquire the companion lock file without waiting, then upgrades to exclusive trace access. The source still explains that waiting could deadlock and that simultaneous reconfiguration is likely to have unexpected results; failure to acquire the exclusive configuration lock produces an error.

Hoisting therefore changes **who shares the files**, not the single-cache synchronization model. Separate workspace roots no longer contend through a shared dependency checkout for this state. Two processes loading the same workspace can still address the same numeric configuration slot and can still encounter the documented reconfiguration-lock behavior.

Basis: exact-release **source**.

### The package-local `.lake` accessor and package-local build state remain

`LoadConfig.lakeDir` is unchanged in `v4.31.0`:

```lean
cfg.pkgDir / defaultLakeDir
```

`Package.lakeDir` likewise remains `<package>/.lake`, and `Package.buildDir` remains `<package>/<configured-build-dir>` (normally `.lake/build`). The hoisting commit introduces a separate `configDir`; it does not redefine the general Lake directory of a package.

This distinction is central for Anneal. A dependency tree can stop owning its **compiled configuration cache** while still owning build artifacts and other package-local Lake state.

Basis: exact-release **source**.

### A residual package-local directory-creation attempt remains on a missing trace

The exact `v4.31.0` `importConfigFile` first creates the workspace-owned `configDir`. Later, when the workspace-owned trace does not exist, the function still executes:

```lean
IO.FS.createDirAll cfg.lakeDir
```

before creating the trace file in `configDir`.

Because `cfg.lakeDir` is package-local, this is a residual package-tree operation even though the compiled files themselves are no longer stored there. If `<dependency>/.lake` already exists, the call is normally just ensuring an existing directory. If a pristine dependency tree has no `.lake` and is mounted read-only, the source path attempts to create that package-local directory and may fail before the workspace-owned trace is created.

This is not evidence that the hoisting change failed to move the compiled configuration cache; the cache paths are unambiguously workspace-owned. It is a narrower implementation caveat that prevents source inspection alone from upgrading the result into “Lean configuration loading never writes or creates anything in dependency trees.”

Basis: exact-release **source**; the read-only consequence is **derived** and requires execution revalidation.

### TOML configuration remains outside the compiled-configuration cache path

`loadConfigFile` dispatches Lean files to `loadLeanConfig` and TOML files to `loadTomlConfig`. The TOML loader reads and decodes the package configuration directly rather than invoking `importConfigFile`.

The dependency regression test confirms the practical placement distinction at this release: when the root configuration is TOML, there is no numeric compiled-configuration slot for root index zero, while Lean-configured dependencies still create their workspace-owned slots.

This is only a statement about package configuration compilation. TOML packages can still have mutable manifests, build outputs, artifact-cache interactions, and other state.

Basis: exact-release **source** and checked-in **test artifact**.

### The change does not migrate or reuse the old package-local cache layout

The introducing patch changes the lookup location from package-local `cfg.lakeDir / "config" / <name>` to workspace-local `cfg.configDir`. It contains no migration or fallback read of the old path.

Accordingly, a package-local `v4.30.0-rc2` compiled configuration is not the location `v4.31.0` consults for this path. On first use in a `v4.31.0` workspace, Lake uses the numeric workspace slot and may elaborate a new compiled configuration even if an old package-local cache is present. The old files can remain as stale package-local data until removed by some external cleanup; ordinary `Package.clean` removes the package build directory, not this historical configuration-cache path.

This is an upgrade hygiene point, not a compatibility problem: the compiled configuration is a cache and the new release intentionally changes its ownership domain.

Basis: introducing **patch** plus exact-release **source**; absence of fallback is a source-level observation.

## Boundaries

**No fresh execution.** No `lake` process was run. The core ownership result is unusually strong source evidence because the introducing commit also adds a checked-in shell regression test for the new numeric workspace layout.

**The report is not a general read-only-package guarantee.** Build products and other package-local state remain separate. In addition, the exact `v4.31.0` missing-trace branch still calls `createDirAll cfg.lakeDir`; a pristine read-only dependency should be tested directly before relying on read-only consumption.

**The report does not generalize beyond `v4.31.0`.** Later Lake revisions may alter configuration paths, trace schema, package indexing, locking, or the residual `cfg.lakeDir` call.

**The report does not claim package indices are stable across workspace graph changes.** They are workspace-relative positions. A changed dependency graph can assign a package a different index and therefore a different configuration slot.

**No stale-slot garbage-collection policy is established.** The source inspected here shows selection and creation of numeric slots. It does not establish a dedicated reclamation mechanism for configuration directories left behind after dependency reordering/removal.

**TOML nonparticipation is narrow.** It means TOML package loading does not compile a Lean `lakefile.olean`; it does not imply a TOML package is otherwise immutable.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary subject: `leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783` (`v4.31.0`).

- `src/lake/Lake/Load/Config.lean`, blob `afdb0a19d9f5443f3cd6081014601744e538c523`: separate package-local `LoadConfig.lakeDir` and workspace-owned `LoadConfig.configDir = wsDir/.lake/config/<pkgIdx>`.
- `src/lake/Lake/Load/Lean/Elab.lean`, blob `b3908d0cebb44cac15e48baa41cb439f6f94eaa5`: compiled configuration path, trace schema/validation, locking, re-elaboration, and residual `createDirAll cfg.lakeDir` in the missing-trace branch.
- `src/lake/Lake/Load/Resolve.lean`, blob `a316c67740973fd737e25eb351bea8249ffd64a6`: dependency load configuration supplies workspace root separately from dependency package directory and assigns workspace index/name.
- `src/lake/Lake/Load/Toml.lean`, blob `271d8c427a3beb1f6d4dcd90123e85e5fb3e8326`: direct TOML configuration parsing/decoding rather than compiled Lean configuration import.
- `src/lake/Lake/Config/Package.lean`, blob `b9f5c489126703625009077caaeda05d3688e06f`: package-local `.lake` and build-directory ownership remain.
- `src/lake/Lake/Config/Workspace.lean`, blob `5879e80f28e4679d164becc331db462b0995c635`: workspace directory/Lake directory derive from the root package and aggregate package state.
- `tests/lake/examples/deps/test.sh`, blob `d526c2852d68a6df92cdd00acba30772983a8de8`: checked-in assertions for numeric workspace-owned compiled-configuration slots and the TOML-root exception.

Introducing history:

- commit `41ecccec6d1244c5f89be2fc76638f22ba37cbc6`, `feat: lake: hoist compiled configurations (#13683)`, 2026-05-08. The commit adds `LoadConfig.configDir`, switches `importConfigFile` to it, and adds the dependency-example regression assertions. Its commit message states the cross-workspace contention motivation.
- `v4.31.0` revision `68218e876d2a38b1985b8590fff244a83c321783` is 115 commits ahead of that commit with the change in its ancestry.

Cross-version comparison basis:

- `v4.30.0-rc2` `src/lake/Lake/Load/Config.lean`, blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`.
- `v4.30.0-rc2` `src/lake/Lake/Load/Lean/Elab.lean`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`.
- Existing native reference package `reports/lake-configuration-ownership-v4-30-0-rc2`.

Evidence roles are **source**, **checked-in test artifact**, **repository history**, and **derived cross-version interpretation**. There is no fresh execution evidence.

## Revalidation

For a later Lean/Lake revision, revalidate this subject at the following decision points:

1. Inspect `LoadConfig.lakeDir` and `LoadConfig.configDir` separately. Do not infer compiled-configuration ownership from the general package Lake directory.
2. Inspect `importConfigFile` for `.olean`, trace, and lock paths; all directory-creation calls; trace fields; validity checks; and locking behavior.
3. Inspect dependency loading for the values supplied as `wsDir`, `pkgDir`, `pkgIdx`, and `pkgName`.
4. Inspect package/workspace state accessors to keep compiled-configuration ownership separate from build/state ownership generally.
5. Inspect TOML dispatch so absence of a Lean-compiled configuration is not assumed from older behavior.
6. Search for migration/fallback reads of prior configuration-cache locations before making upgrade claims.

A minimal exact-release execution probe should use two root workspaces sharing one Lean-configured path dependency:

1. delete both workspaces' `.lake/config` directories and the dependency's `.lake` directory;
2. load workspace A and record all created files plus trace JSON;
3. load workspace B and confirm its compiled configuration is created under B's own `.lake/config/<idx>` without altering A's slot;
4. re-load A and confirm B's different package index/name does not invalidate A's trace;
5. make both workspaces stale and run concurrent reconfiguration within one workspace to preserve the remaining same-workspace lock/error behavior;
6. mount or permission-protect the shared dependency so its `.lake` directory cannot be created, then test a first Lean-configuration load to determine the practical effect of the residual `createDirAll cfg.lakeDir` call;
7. pre-create only the dependency's empty `.lake` directory, keep the dependency otherwise read-only, and repeat to separate directory-creation failure from compiled-cache ownership;
8. repeat with a TOML-configured root and confirm no root compiled-configuration slot appears.

Preserve command lines, tool revision, filesystem listings, trace contents, permissions/mount setup, and hashes of generated `.olean`/trace files. That probe would establish the operational read-only and concurrency consequences that source inspection deliberately leaves bounded.
