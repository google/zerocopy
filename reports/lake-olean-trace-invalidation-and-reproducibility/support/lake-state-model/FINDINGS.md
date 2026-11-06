# Findings

## A workspace is rooted in one package and adds resolved package-wide state

`Workspace` contains the root `Package`, detected `Lake.Env`, loaded system `LakeConfig`, a Lake cache handle, the CLI arguments, an ordered package array, a package map, and the registered facet configurations.

The package array is documented as following `require` declaration order with the root first. Package names used internally are not just user-facing strings: each package has a workspace index and a unique `keyName`, allowing Lake to distinguish packages that share a base name.

The workspace directory and manifest path are inherited from the root package. This makes the root package the filesystem anchor for ordinary workspace state while still letting each dependency retain its own package directory, configuration file, build directory, and manifest path.

Basis: **source**.

## A package combines loaded configuration with concrete filesystem identity

`Package` stores both declarative configuration and resolved paths. Its fields include:

- workspace index, assigned/base/original/key names;
- absolute package directory and workspace-relative directory;
- the loaded `PackageConfig`;
- absolute and relative configuration-file paths;
- relative manifest path;
- dependency configurations;
- target declarations and lookup maps;
- default targets, scripts, and hooks;
- repository/scope metadata.

At this revision the default package Lake directory is `.lake`, the default dependency directory is `.lake/packages`, and the default build directory is `.lake/build`. `Package.manifestFile` is the package directory joined with the relative manifest path; `Package.buildDir` is the package directory joined with the configured build directory.

These paths are package-relative state. A statement such as "the workspace has a .lake directory" is therefore incomplete when reasoning about dependency packages: each loaded package has its own package directory and its own derived Lake/build paths.

Basis: **source**.

## The root package configuration is loaded before dependencies are resolved

`loadWorkspaceRoot` loads the system Lake configuration, loads the root package configuration, and constructs a `Workspace` whose resolved dependency set is not yet populated.

The package loader accepts either a Lean or TOML configuration. If no extension is specified, it looks for `lakefile.lean` and `lakefile.toml`; if both exist, the Lean file wins. It resolves the concrete configuration-file path before producing the package value.

Only after the root workspace exists does `loadWorkspace` resolve/materialize dependencies. This separates "what the root package declares" from "which concrete dependency packages are now in the workspace."

Basis: **source**.

## The manifest records dependency materialization, not build freshness

The default manifest is `lake-manifest.json`. At this revision its schema version is `1.2.0`.

`Manifest` records the workspace/package name, Lake directory, fixed-toolchain flag, optional packages directory, and dependency package entries. A package entry includes its package name/scope, whether it is inherited, the dependency's configuration file, optional dependency manifest file, and a source description.

The source description is either:

- a local path, relative to the containing package directory; or
- a Git source with URL, resolved revision, optional input revision, and optional subdirectory.

The manifest documentation says this source describes exactly how Lake should materialize the package. `loadWorkspace` uses an existing manifest to materialize dependencies unless the caller requests a dependency update; if no manifest exists, Lake updates/resolves and materializes instead.

No build artifact hashes, target traces, build logs, or module freshness records live in this `Manifest` type. Those are separate build-layer state.

Basis: **source**.

## Build identity is represented by BuildKey, not by output paths alone

`BuildKey` has source-level variants for:

- module;
- package;
- package module;
- package target;
- facet of another build key.

The same key model underlies partial CLI target syntax used by `lake build` and `lake query`. Package qualification and facets are part of the key, so a path to an output file is not the full logical identity of the build request.

This matters for reusable prepared environments. The artifact path answers where a result resides; the build key answers which logical target/facet Lake is asking the build graph to produce.

Basis: **source**.

## Facets are typed projections over targets

A `FacetConfig` names the kind of input target it accepts, a fetch function, an output data kind, whether the facet is CLI-buildable, how its result is formatted, and whether the fetch should be memoized.

The build index handles a facet by finding its configuration, checking that the target kind matches, and running its fetch function. If the facet is marked memoizable, Lake caches the fetch in the build store under a facet build key.

Facets therefore are not merely filename suffixes. They are typed build operations layered over an existing target. A source-model report that treats "target" and "artifact" as synonyms misses this intermediate identity.

Basis: **source**.

## Fetching a target constructs a job through the build index

The build index maps complete build keys to recursive build functions. For package targets it looks up the package target declaration and runs its configured fetch function. For facets it runs the facet's fetch function. The recursive fetch path uses a topological/suspending scheduler and memoizes eligible build functions by build key.

A `Target α` itself is small: it carries a partial build key and an expected output type. The work happens when the target is fetched and resolved through the build index.

This split is useful when reading Lake code: target/facet declarations define logical graph nodes; fetch functions construct the jobs that compute them.

Basis: **source**.

## Jobs are asynchronous computations with explicit build state

A `Job α` wraps a Lean task that returns either an error or an output plus `JobState`. The job also carries a caption and an optional/failure policy.

`JobState` records:

- accumulated build log;
- `JobAction` (`unknown`, `replay`, `fetch`, or `build`);
- whether a no-build request discovered that rebuilding is required;
- the current `BuildTrace`;
- time spent building.

The monitor reports jobs as they finish and uses these actions to distinguish reuse/replay, cache fetch, and actual building. That distinction is operational state of a build run, not part of the dependency manifest.

Basis: **source**.

## BuildTrace deliberately combines hashes and modification times

`BuildTrace` contains a caption, an array of child input traces, a `Hash`, and an `MTime`. Mixing two traces:

- mixes their hashes;
- takes the maximum modification time;
- records the second trace as an input.

The same trace can therefore support either hash-based or time-based freshness decisions, and it retains enough input structure to serialize an explanatory dependency tree into saved build metadata.

Lake's `Hash` at this revision is a `UInt64` built with Lean's hash machinery. The source has an explicit TODO to use a secure hash instead of the builtin Lean hash. These hashes are engineering freshness/cache identifiers, not cryptographic integrity proofs.

Basis: **source**.

## Saved trace files record dependency identity, output description, and replayable log

`BuildMetadata` is the persisted trace-file payload. At this revision its schema string is `2025-09-10`. It contains:

- `depHash`: the combined dependency hash used for freshness;
- a serialized tree of named input hashes;
- an optional JSON description of outputs;
- the build log;
- a `synthetic` bit indicating metadata produced by fetching an artifact from cache.

A successful `buildAction` writes this metadata to the target-specific `traceFile`. If the build throws a fatal error, the normal successful trace write does not occur.

The source also supports historical trace stubs and older serialized forms. A trace file is therefore versioned build metadata, not simply a raw digest.

Basis: **source**.

## The ordinary up-to-date check prefers the saved dependency hash

`buildUnlessUpToDate?` states the reuse decision directly.

If a saved trace file exists, Lake first asks whether the current dependency trace hash matches the saved `depHash` and whether the output exists. If that succeeds, Lake replays the saved build log and treats the target as current.

If the hash check fails and old mode is enabled, the saved trace helper can fall back to a modification-time check against the supplied old trace time.

If no saved trace exists, Lake checks whether the output's modification time is newer than the dependency trace or supplied old trace. Thus the presence of a valid saved trace changes the primary freshness discriminator from an mtime relation to a hash equality plus output existence.

Basis: **source**.

## A no-build run records that a rebuild would have been needed

When `buildAction` is entered while the build context has no-build enabled, Lake marks `wantsRebuild`, writes a sibling trace with extension `.nobuild` when the normal trace file exists, and returns an error saying the target is out of date and needs rebuilding.

The top-level build runner gives the no-build-required-rebuild condition its own exit code, `3`.

This state is useful for diagnostics and validation, but it is not evidence that the requested target was rebuilt. A consumer should distinguish "fresh", "would rebuild", and "rebuilt successfully."

Basis: **source**.

## File hashes have their own mutable sidecar cache

For file inputs, Lake can cache a computed hash in an adjacent `.hash` file. `fetchFileHash` reads and trusts an existing sidecar when the build context says hashes are trusted. Otherwise it recomputes the file hash and writes the sidecar.

This adds another state layer beneath saved target traces. A target trace may depend on a file hash whose computation was itself reused from mutable sidecar state.

A prepared-environment design should therefore distinguish "the artifact exists", "the target trace matches", and "the input hash was freshly recomputed." They are not equivalent observations in this implementation.

Basis: **source**.

## Module builds mix semantic configuration into their dependency trace

The module build path does not trace only source bytes. Before fetching/building Lean artifacts it mixes in:

- the selected Lean/toolchain trace;
- source trace;
- Lean options;
- whether module mode is enabled;
- module name;
- package identity;
- Lean arguments;
- imported-module artifact traces.

The final module build therefore depends on configuration and dependency artifacts as well as the module source. That is the intended reason a matching source file alone is insufficient to establish that an existing `.olean` or related artifact is current.

Basis: **source**.

## The state model has separate producer and consumer questions

The source model supports a useful decomposition for Anneal research:

1. **configuration state**: lakefile/TOML plus environment/system configuration, loaded into Package/Workspace values;
2. **dependency state**: manifest plus materialized dependency package trees;
3. **logical build identity**: build keys, targets, and facets;
4. **execution state**: jobs and their actions/logs;
5. **artifact state**: build outputs under package build paths or restored from an artifact store/cache;
6. **freshness state**: build traces, trace files, and cached file hashes.

A producer that creates a prepared environment may populate all six layers. A consumer that wants read-only or relocatable reuse may need only some of them, but this report does not infer which subset is sufficient. That stronger question depends on concrete reads/writes and path assumptions in the relevant commands.

Basis: **derived** from pinned **source**.
