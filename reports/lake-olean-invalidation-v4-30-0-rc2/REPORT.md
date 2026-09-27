# What invalidates a module `.olean` in Lake v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake does not decide whether a module `.olean` is current by comparing the `.lean` source alone. It computes a dependency trace for the module's whole Lean compilation, saves that trace's hash beside the outputs, and in ordinary mode reuses the outputs only when the newly computed hash matches the saved hash and the required module outputs still exist.

For a module's `leanArts` build, the hash includes the setup/dependency trace, the selected Lean toolchain identity, the module's own normalized source contents, the effective Lean options, whether the source is a module, the logical module name, the package identifier passed to Lean, and the non-weak Lean arguments. The setup trace in turn carries imported-module artifact/transitive traces and extra dependency targets, and normally carries dynamic-library/plugin traces; an explicit `platformIndependent` setting changes which of those traces and the host-platform trace participate.

This gives a sharper rule than "a source or lakefile change rebuilds the `.olean`." A source-file byte change that only changes line endings does not change Lake's normalized source hash. Moving the same source while preserving its logical module/package identity does not directly change the hash. Changing `moreLeanArgs` does; changing `weakLeanArgs` does not, even though both argument arrays are passed to `lean`. Changing package version, descriptive package metadata, server-only options, C compiler arguments, or linker arguments does not directly enter this module trace. Imported packages affect the module through the artifact and transitive-import traces Lake selects for the import relation, not because their raw source paths or every configuration field are hashed wholesale.

A changed dependency hash makes the existing local module outputs stale, but it does not guarantee a fresh compiler invocation. If an artifact cache contains outputs for the new input hash, Lake can restore those outputs instead. Conversely, unchanged source/configuration is not sufficient for local reuse when the saved trace or required outputs are missing. `--old` is also a deliberate exception: it can fall back from a hash mismatch or missing saved trace to modification-time freshness.

Basis: pinned Lake source + the already-published same-revision Lake state-model report + derived synthesis. No fresh Lake execution was performed.

## Applicability

These findings apply to the Lake implementation shipped in Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

The subject is the ordinary Lake build of a workspace `Module` through `Module.recBuildLean` / the `leanArts` facet and the resulting module outputs, especially `.olean`. The same Lean invocation also produces `.ilean`, generated C, and, depending on module/toolchain mode, other module artifacts; Lake uses one saved module trace for that aggregate build. Therefore a trace invalidation discussed here invalidates the aggregate `leanArts` result, not only one byte stream in isolation.

This report deliberately excludes the compiled package-configuration cache under `.lake/config`: that cache has its own validity predicate. It also excludes `.olean` binary format/identity, general dependency resolution, artifact-cache architecture, and the generic saved-trace algorithm except where those mechanisms determine the module-specific invalidation rule.

Unless stated otherwise, "invalidates" below means that ordinary hash-based checking cannot reuse the existing module result under its saved module trace. It does not mean that Lake must invoke `lean`; an artifact-cache hit can satisfy the new input hash. It also does not describe `--old`, which has an explicit mtime fallback.

## Findings

### The module's saved dependency hash is the ordinary reuse boundary

`Module.recBuildLean` constructs the module dependency trace, reads `mod.traceFile`, and checks the saved trace against the current trace. `SavedTrace.replayIfUpToDate'` considers the result hash-current when the current dependency hash equals the saved `depHash` and the required output set exists. Without `--old`, a hash mismatch is out of date. If the saved trace is missing or invalid, ordinary mode also reports it out of date.

This means the most precise source-level question is not "did this file or configuration object change?" but "did the module's recomputed dependency trace hash change?" Lake hashes selected *effective values and dependency traces*, not the lakefile text as a whole.

The module path then has an artifact-cache branch. Lake uses the current dependency hash as the cache input key. A stale local result can therefore be replaced by cached outputs for the new hash without recompiling. The existing local `.olean` is still not being reused under the old identity.

Evidence:
- [`Module.recBuildLean`, including saved-trace and cache decisions](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L874-L970)
- [`SavedTrace.replayIfUpToDate'`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L190-L267)
- [published Lake state model](../lake-state-model-v4-30-0-rc2/REPORT.md)

### The top-level `leanArts` trace names the direct invalidators

Before `recBuildLean` reaches its reuse decision, it mixes these components into the current job trace, in this order:

| Trace component | What a change means for ordinary module reuse |
| --- | --- |
| `mod.setup` job trace | Any traced dependency/setup change invalidates; unpacked below. |
| Lean trace | Changing the selected Lean toolchain identity invalidates. |
| module source trace | Changing normalized source text invalidates. |
| `setup.options` | Changing effective Lean options invalidates. |
| `setup.isModule` | Changing module/non-module mode invalidates. |
| `mod.name` | Changing logical module name invalidates. |
| `mod.pkg.id?` | Changing the Lean package identifier invalidates. |
| `mod.leanArgs` | Changing traced Lean arguments invalidates. |

Lake then captures this combined trace as `depTrace` and passes it to the build/reuse logic.

This list is more useful than a field-by-field lakefile inventory because it is the implementation's actual dependency identity. A configuration edit matters to `.olean` reuse exactly when it changes one of these effective values or one of the traces feeding `mod.setup`—subject to the old-mode and stale-hash boundaries below.

Evidence:
- [`Module.recBuildLean` trace construction](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L874-L897)
- [`BuildTrace.mix` hashes child traces independently of captions](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Trace.lean#L366-L380)

### Own-source invalidation is content-based and line-ending-normalized

`Module.recFetchInput` reads the `.lean` file and constructs its trace with `Hash.ofText contents`. `Hash.ofText` normalizes CRLF to LF before hashing. The trace caption is the source path, but `BuildTrace.mix` mixes the trace hash, not the caption string, into the parent hash.

For the same logical module and package, this yields three useful distinctions:

- changing source text in a way that changes its normalized text hash invalidates the module;
- changing only CRLF versus LF does not invalidate it through the source hash; and
- relocating the same source file does not invalidate it merely because its absolute path/caption changed.

Relocation can still change another traced component—for example package identity, imported artifacts, or setup dependencies—so path neutrality of this one source hash is not a whole-workspace relocation guarantee.

Unlike generic input-file hashing, this own-source trace is computed directly from the file contents read for header parsing; it is not obtained from a neighboring `.hash` sidecar.

Evidence:
- [`Module.recFetchInput`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L29-L42)
- [`Hash.ofText`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Trace.lean#L168-L182)
- [`BuildTrace.mix`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Trace.lean#L366-L380)

### The Lean toolchain identity is traced separately from source and package configuration

The build context creates its Lean trace from `ws.lakeEnv.leanGithash` and labels it with the Lean version/commit. `recBuildLean` calls `addLeanTrace` before the source/configuration components.

Thus selecting a Lean toolchain with a different Git hash invalidates the module trace even if the package sources and lakefile-derived options are unchanged. The source-level identity is the toolchain Git hash exposed by Lake's environment, not merely the human-readable version string.

Evidence:
- [build-context Lean trace](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Run.lean#L25-L34)
- [`addLeanTrace`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L37-L51)
- [`recBuildLean` call site](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L880-L893)

### Effective Lean options and non-weak Lean arguments invalidate; weak Lean arguments deliberately do not

A module's effective `leanOptions` combine build-type options, package `leanOptions`, and library `leanOptions`. `recFetchSetup` stores those options in `ModuleSetup`, and `recBuildLean` hashes every effective option through `traceOptions`.

A module's `leanArgs` combine the build type's Lean arguments, package `moreLeanArgs`, and library `moreLeanArgs`; `recBuildLean` hashes the resulting array directly. At this revision the built-in `BuildType.leanArgs` contribution is empty, but it is still part of the effective construction.

`weakLeanArgs` are intentionally different. The package and library weak arrays are prepended to the actual `lean` invocation in `Module.buildLean`, but `recBuildLean` does not add them to the dependency trace. The configuration documentation explicitly says they can change without triggering a rebuild.

Consequently:

- changing an effective `leanOptions` value invalidates;
- changing package/library `moreLeanArgs` invalidates;
- changing package/library `weakLeanArgs` alone does **not** invalidate, despite changing the compiler invocation.

That last behavior is deliberate Lake policy, not an inference that weak arguments are semantically irrelevant. An Anneal environment that changes weak arguments while reusing artifacts is relying on Lake's declared weak-input contract.

Evidence:
- [`LeanLib.leanOptions`, `leanArgs`, and `weakLeanArgs`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/LeanLib.lean#L123-L197)
- [`LeanConfig.moreLeanArgs` and `weakLeanArgs`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/LeanConfig.lean#L154-L180)
- [`Module.buildLean` invocation versus `recBuildLean` trace](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L849-L897)

### Logical module and package identity are traced; package version is not the package ID

`recBuildLean` hashes both `mod.name` and `mod.pkg.id?`.

`Module.name` is the logical Lean module name. Moving a file so that Lake resolves it as another module therefore changes a traced value even if the file bytes are identical.

`Package.id?` is the identifier passed to Lean for native-symbol disambiguation. At this revision it is `none` for bootstrap packages and otherwise the package's original configured name as a `PkgId`. The package `version` field is separate and does not participate in `Package.id?`.

Therefore changing the original package name or crossing the bootstrap/non-bootstrap boundary changes a directly traced value. Changing package version alone does not directly change this component. A version edit can still have indirect effects—for example if it changes dependency resolution or another traced setting—but the version field is not independently hashed by `recBuildLean`.

Evidence:
- [`Module.name` and package-derived accessors](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Module.lean#L14-L25)
- [`Package.id?` and `Package.version`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Package.lean#L152-L165)
- [module identity in the dependency trace](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L884-L893)

### Imports invalidate through exported artifact and transitive-import traces, not by wholesale upstream configuration hashing

The setup path computes `ModuleImportInfo` from the parsed imports. For each resolved imported module, Lake fetches that module's `exportInfo` and mixes selected transitive-import traces plus selected exported-artifact traces into the importing module's `info.trace`.

For an ordinary import, the relevant exported artifact trace includes the imported module's `.olean`; the transitive trace carries the exported dependency chain. `import all`, `meta`, and non-module cases deliberately select broader/different combinations of public, meta, all, IR, server/private OLean, and legacy traces.

This has an important consequence. A dependency's raw source or lakefile is not directly copied into the downstream module's hash. The change propagates when it changes the exported artifact/transitive trace selected by the import relation. If an upstream source/configuration change produces byte-identical relevant exported artifacts and leaves the selected transitive trace unchanged, the downstream import component can remain unchanged even though the upstream build itself had a different source-level input trace.

Conversely, a transitive imported dependency can invalidate a module even when the module's own source and direct import declaration are unchanged, because the selected transitive trace is part of `info.trace`.

Evidence:
- [`ModuleImportInfo.addImport`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L257-L352)
- [`fetchImportInfo`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L360-L423)
- [`Module.computeExportInfo`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L434-L479)

### Extra dependency targets always enter setup trace; dynamic-library/plugin traces depend on `platformIndependent`

`Module.recFetchSetup` builds more than Lean imports. It fetches the library's extra dependency target, imported precompiled libraries, package external libraries when precompilation requires them, module/package dynamic libraries, and plugins.

It then separates two trace groups:

- `depTrace`: the `extraDep` job trace plus the import trace; and
- `libTrace`: the traces accumulated from import libraries, external libraries, dynamic libraries, and plugins.

`platformIndependent` controls which groups participate:

| Effective `platformIndependent` | Setup trace mixed into module dependency hash |
| --- | --- |
| `none` | `depTrace` + `libTrace` |
| `some false` | `depTrace` + `libTrace` + host `platformTrace` |
| `some true` | `depTrace` only |

Thus an extra dependency target can invalidate through `depTrace` in all three cases. Changes in library/plugin/precompiled-library artifact traces invalidate when their `libTrace` is included, but are deliberately omitted when the module is explicitly platform-independent. An explicit `false` also adds the host target identity; a host-platform change can therefore invalidate that module class.

Configuration such as `precompileModules`, `dynlibs`, `plugins`, and related target declarations is not hashed as raw syntax. It matters insofar as it changes the jobs/artifact traces that this setup construction includes. `platformIndependent` is special because its effective value changes the trace composition itself.

Evidence:
- [`Module.recFetchSetup`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L493-L552)
- [precompiled import-library selection](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L110-L163)
- [`addPlatformTrace`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L33-L46)

### Several common configuration changes do not directly invalidate the module `.olean`

The direct trace construction also identifies important negative space. At this exact revision, the module `leanArts` trace does not directly mix arbitrary `PackageConfig`/`LeanLibConfig` records. In particular, a change does not directly invalidate this module result merely because it changes one of these categories:

- `weakLeanArgs`, as documented above;
- server-only options such as `moreServerOptions`;
- `moreLeancArgs` / `weakLeancArgs` used by downstream C/native compilation;
- `moreLinkArgs` / `weakLinkArgs`, link objects, or link libraries used by downstream linking;
- descriptive package metadata such as description or keywords;
- package version by itself;
- output/build-directory paths by themselves; or
- source/configuration path strings that change only trace captions or runtime locations while leaving the traced values/hashes unchanged.

Some fields in that list can still change *other* targets, can change which target Lake asks for, or can indirectly alter a traced setup input. For example, changing a target declaration may change an `extraDepTarget`, dynamic library, or plugin and therefore change its trace. The claim is only that the configuration record is not wholesale-hashed into `leanArts`.

This distinction is especially important for generated Anneal workspaces: rewriting a lakefile comment, package description, build output path, or weak argument should not be assumed to invalidate existing `.olean` state merely because the configuration file bytes changed. The effective build trace is the authority.

Evidence:
- [`recBuildLean`'s complete top-level trace additions](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L874-L897)
- [`LeanConfig` field contracts](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/LeanConfig.lean#L154-L220)
- [`LeanLib` effective Lean settings](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/LeanLib.lean#L123-L240)

### Missing trace/output state can make an unchanged module non-reusable

Source/configuration changes are not the only invalidation cause. Ordinary hash-based reuse requires a readable saved module trace with the matching `depHash` and an existing required output set. `Module.checkExists` accepts either the module archive (`.ltar`) or the expected module artifacts; if the saved hash matches but individual artifacts are absent, `recBuildLean` may unpack an available archive. With cache access, it may instead restore artifacts by the current input hash.

If neither a usable saved trace/output state nor a matching cache result is available, Lake builds even when all semantic inputs are unchanged. Thus "nothing changed" is not equivalent to "the local `.olean` will be reused."

Evidence:
- [`Module.checkArtifactsExsist` / `Module.checkExists`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L708-L743)
- [`recBuildLean` saved-trace/cache flow](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L931-L970)

### `--old` changes the invalidation rule from hash authority to an mtime fallback

`SavedTrace.replayIfUpToDate'` has an explicit compatibility path. If the dependency hash does not equal the saved hash and old mode is enabled, Lake checks output modification time against the supplied old trace time. If no valid saved trace exists, old mode can also use the mtime check.

For `recBuildLean`, the supplied old trace is the module source trace's mtime. This is materially weaker than the ordinary hash rule: it can call a module current despite a dependency-hash mismatch if the mtime relation passes.

Accordingly, the direct-invalidators above describe ordinary mode. An Anneal validation that needs hash-defined freshness should not treat a successful `--old` reuse as evidence that the current hash identity matches the saved build.

Evidence:
- [`checkHashUpToDate'` and `SavedTrace.replayIfUpToDate'`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L190-L267)
- [`recBuildLean` passes `srcTrace.mtime` as `oldTrace`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L931-L970)

### Imported artifact hashes can inherit Lake's separate hash-sidecar trust boundary

The current module's own `.lean` source is read and hashed directly. Imported-module participation is different: downstream import traces use artifact traces. Lake's generic artifact/file tracing can rely on adjacent `.hash` sidecars when the build context is configured to trust them, as documented in the published state-model report.

Therefore the logical invalidator is still "the imported artifact/transitive trace changed," but observing a changed artifact file on disk is not sufficient to prove that the trace Lake recomputed will change if a stale trusted hash sidecar masks that byte change. That is a freshness-state boundary, not a different dependency graph.

For a high-assurance prepared environment, record the hash-trust mode together with any claim that a byte mutation necessarily invalidated downstream `.olean`s.

Evidence:
- [published Lake state model: file-hash sidecars](../lake-state-model-v4-30-0-rc2/FINDINGS.md)
- [generic input/hash behavior](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L740-L830)

## Boundaries

**No fresh execution.** This report follows the exact source graph and saved-trace code. It does not supply an empirical matrix showing each configuration mutation and the observed Lake job action.

**Aggregate module result.** `leanArts` covers the outputs produced by one Lean module compilation. A changed trace invalidates that aggregate result. Separate downstream facets can have narrower traces—for example, `fetchOLeanCore` re-exports an already-produced `.olean` artifact trace—and native compilation/link targets have their own invalidation inputs.

**Configuration-file bytes are not a dependency by themselves.** Lake first loads configuration into package/library/module structures. This report describes the effective values and jobs then hashed by `recBuildLean`; it does not claim that editing an arbitrary lakefile expression is inert. The edit can change any of those effective values or even change the build graph.

**Imported artifact equality can suppress downstream invalidation.** Because importers trace selected exported artifacts/transitive traces rather than an upstream module's raw source trace, an upstream rebuild can occur without forcing a downstream rebuild when its relevant exported identity is unchanged.

**Weak inputs are intentionally outside the hash.** `weakLeanArgs` are a concrete counterexample to "any compiler-command change invalidates." Their exclusion is explicit source behavior, not a guarantee that every possible weak-argument change is semantically safe.

**Artifact-cache restoration is not local reuse.** A changed module input hash can select already-produced artifacts from a cache. This report distinguishes invalidating the old local trace identity from necessarily recompiling.

**`--old` is a separate policy.** Mtime-based success under old mode does not demonstrate ordinary hash equivalence.

**Platform and external-target behavior is trace-mediated.** This report establishes which setup trace groups are included. It does not claim that every edit to an external target declaration necessarily changes the target's resulting trace; that depends on the target job and output identity.

## Evidence

The primary implementation subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). Evidence was acquired on 2026-09-27.

Pinned source blobs inspected:

- `src/lake/Lake/Build/Module.lean` — `21c5f343112a1690390188642a05d6092432ab84`: own-source trace, import/export trace propagation, setup dependencies, module trace composition, artifact-cache flow, existence checks, and output artifact computation.
- `src/lake/Lake/Build/Common.lean` — `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: platform/Lean trace helpers, saved build metadata, ordinary hash checking, old-mode fallback, and generic input/build tracing.
- `src/lake/Lake/Build/Trace.lean` — `656c991fab8a6475802373224514ec7e73f9b18b`: `Hash.ofText`, `BuildTrace`, hash mixing, and hash/mtime freshness primitives.
- `src/lake/Lake/Build/Run.lean` — `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`: build-context Lean identity derived from `lakeEnv.leanGithash`.
- `src/lake/Lake/Config/LeanConfig.lean` — `9fdd5a656c4316ee6beb45bdc9a1be4dd8d5d42a`: effective module-build configuration fields and the documented weak-argument contract.
- `src/lake/Lake/Config/LeanLib.lean` — `077efb6c244fd53bab5dead6c850d40161c96e7f`: composition of package/library build type, Lean options, traced arguments, weak arguments, precompilation, dynamic libraries, and plugins.
- `src/lake/Lake/Config/Module.lean` — `f8b938e16fe53ada616364033b8d8353baa733ee`: logical module identity, source/output paths, and effective configuration accessors.
- `src/lake/Lake/Config/Package.lean` — `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: package identity fields, `Package.id?`, and the separate package version.

The neighboring published corpus report `reports/lake-state-model-v4-30-0-rc2` was used to preserve the already-established generic saved-trace/hash-sidecar model rather than restating it as new evidence. The module-specific dependency-trace conclusions above were re-read from the pinned Lean source.

No fresh **execution** evidence was acquired. Claims above labeled by mechanism are **source** claims; conclusions about what a configuration edit means for reuse are **derived** by following the exact trace construction into the exact ordinary reuse check.

## Revalidation

For a future Lake revision, first compare these source boundaries before running a broad experiment:

1. `Module.recFetchInput`: does own-source hashing still use normalized text, and is the path still caption-only?
2. `Module.recFetchSetup`: which dependency/library/plugin/platform traces feed setup?
3. `Module.recBuildLean`: enumerate every `addTrace`, `addPureTrace`, and direct trace helper before `depTrace` is captured.
4. `LeanLib.leanOptions`, `leanArgs`, and `weakLeanArgs`: map user-facing configuration to the effective values in step 3.
5. import/export tracing: identify which imported artifacts and transitive traces feed each import form.
6. `SavedTrace.replayIfUpToDate'` and the module cache branch: confirm the current hash/output/cache decision.

On a capable surface, the cheapest exact-pin execution matrix is one tiny two-module Lake package plus one dependency package. Build once, preserve the module `.trace`, then mutate one dimension at a time and run verbose/no-build checking so the job action and saved `depHash` can be recorded. Include at least these controls:

- own source semantic text change;
- CRLF/LF-only change;
- source relocation with unchanged logical module/package identity;
- `leanOptions` change;
- `moreLeanArgs` change;
- `weakLeanArgs` change;
- original package-name change versus package-version-only change;
- direct imported module change that changes its `.olean` bytes;
- upstream change deliberately chosen to leave the relevant exported artifact byte-identical, if reproducible;
- `extraDepTarget` output change;
- dynamic-library/plugin change under `platformIndependent := none`, `false`, and `true`;
- same inputs with the saved trace removed;
- same hash with a required output removed;
- ordinary mode versus `--old`; and
- artifact cache disabled versus a seeded cache for both the old and new input hashes.

For each case preserve: effective generated Lake configuration, command line, `.trace` before/after, verbose job action, current/saved dependency hashes, relevant artifact hashes, mtimes, and whether `lean` actually ran. That separates four different observations that are otherwise easy to conflate: the dependency identity changed, the old local output was rejected, a cached replacement was restored, and a fresh compilation occurred.