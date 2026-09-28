# Lake artifact-cache environment variables at v4.30.0-rc2

## Summary

At Lean/Lake `v4.30.0-rc2`, `LAKE_CACHE_DIR` and `LAKE_ARTIFACT_CACHE` control different parts of the local artifact-cache contract.

`LAKE_CACHE_DIR` selects **where** the workspace cache lives. A nonempty value selects that directory directly. An empty value does not mean “no cache”: it disables the toolchain/system cache choice, after which an ordinary workspace falls back to its root package’s `.lake/cache`. If the variable is unset, Lake prefers the Elan toolchain cache when one is available, then the system cache, then the workspace-local `.lake/cache`. `lake env` exports the **resolved workspace cache directory**, so a process that started with `LAKE_CACHE_DIR=` can observe a nonempty workspace-local path inside the augmented environment.

`LAKE_ARTIFACT_CACHE` controls the workspace-level default for whether packages may use Lake’s local artifact cache. Its value is parsed as a Boolean; recognized true spellings are `y`, `yes`, `t`, `true`, `on`, and `1`, while recognized false spellings are `n`, `no`, `f`, `false`, `off`, and `0`, case-insensitively. An empty or otherwise unrecognized value becomes “unset,” not false.

The effective per-package policy is asymmetric. A package’s explicit `enableArtifactCache` setting has first priority. Otherwise Lake falls back to the workspace setting, whose environment-derived value takes priority over the root package’s workspace default. If nothing is configured, Lake defaults to **readable but not writable**: a package may consume a matching artifact already present in the cache, but it does not populate the cache. An effective `true` makes the package both readable and writable; an effective `false` makes it neither readable nor writable.

The two variables therefore must not be collapsed into one switch. `LAKE_CACHE_DIR=` is a location-isolation choice, not an artifact-cache disable switch. Conversely, `LAKE_ARTIFACT_CACHE=true` does not choose the cache directory. Anneal can use an empty `LAKE_CACHE_DIR` to keep cache state workspace-local while separately deciding whether packages may read or write that cache.

Basis: exact pinned Lake source plus same-revision checked-in tests. No fresh execution was performed.

## Applicability

These findings apply to Lake in `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`.

The report concerns the process-environment interpretation performed by `Lake.Env.compute`, the workspace cache chosen by `computeLakeCache`, the workspace environment emitted by `lake env`, and the generic per-package read/write predicates used by cache-aware build paths.

“System cache” below follows Lake’s own state split. With Elan and a nonempty toolchain identifier, normal non-bootstrap work can use an Elan toolchain-specific Lake cache while bootstrap work uses the separate system-cache coordinate. When an explicit nonempty `LAKE_CACHE_DIR` is supplied, Lake assigns that path to both cache coordinates. When an empty value disables the shared/system choice, `computeLakeCache` falls back to the root package’s `.lake/cache`.

This report does not restate artifact layout, cache-key construction, publication/restoration, or target coverage. Neighboring reference reports own those subjects. Here they matter only enough to distinguish cache **location** from cache **read/write policy**.

## Findings

### `LAKE_CACHE_DIR` chooses the shared-cache location, and an empty value selects workspace-local fallback

During `Lake.Env.compute`, Lake handles `LAKE_CACHE_DIR` before its toolchain/system fallbacks.

If the variable is set to a nonempty string, Lake records that exact path as both `lakeCache?` and `lakeSystemCache?`.

If the variable is set to the empty string, Lake sets `noSystemCache := true` and does not populate either shared-cache coordinate. The later workspace constructor calls `computeLakeCache`; for an ordinary non-bootstrap root it uses `lakeEnv.lakeCache?` when present and otherwise falls back to:

```text
<root-package>/.lake/cache
```

The bootstrap path analogously uses `lakeSystemCache?` and the same package-local fallback.

If `LAKE_CACHE_DIR` is unset, Lake first prefers an Elan toolchain cache when Elan and a nonempty toolchain identifier are available. Otherwise it tries the system cache. If neither exists, the workspace again falls back to `<root-package>/.lake/cache`.

This gives the useful exact distinction:

| Incoming `LAKE_CACHE_DIR` | Workspace cache location |
| --- | --- |
| nonempty `P` | `P` |
| empty string | root-package `.lake/cache` |
| unset, Elan toolchain cache available | toolchain-specific Lake cache |
| unset, no toolchain cache but system cache available | system Lake cache |
| unset, no shared cache available | root-package `.lake/cache` |

Basis: **source** in `Lake/Config/Env.lean` and `Lake/Config/Workspace.lean`.

### An empty `LAKE_CACHE_DIR` disables the shared/system choice, not artifact caching itself

The empty-string branch changes only cache-location state: it sets `noSystemCache` and lets the workspace use its local fallback. It does not set `enableArtifactCache?`, and it does not change the per-package readable/writable predicates.

A package can therefore use a workspace-local `.lake/cache` while artifact caching is enabled. The same-revision Lake tests intentionally use this pattern for local/hermetic cache behavior.

The inverse also holds. A nonempty shared `LAKE_CACHE_DIR` does not make packages writable. Without an effective artifact-cache enablement, the default package policy remains read-only.

Basis: **source** + same-revision **checked-in tests**.

### `lake env` exports the resolved workspace cache path, not the original input string

`Workspace.augmentedEnvVars` emits:

```text
LAKE_CACHE_DIR=<workspace.lakeCache.dir>
```

unconditionally.

Consequently, `lake env` normalizes the cache-location choice into the concrete path Lake selected. A parent environment containing `LAKE_CACHE_DIR=` can therefore yield a child augmented environment in which `LAKE_CACHE_DIR` is a nonempty workspace-local `.lake/cache` path.

The same-revision environment test explicitly checks that a workspace always sets `LAKE_CACHE_DIR`, including when the incoming variable is empty.

Basis: **source** + same-revision **checked-in test**.

### `LAKE_ARTIFACT_CACHE` is tri-state after parsing

`Lake.Env.compute` reads `LAKE_ARTIFACT_CACHE` and applies `envToBool?`.

The accepted values are case-insensitive:

- true: `y`, `yes`, `t`, `true`, `on`, `1`;
- false: `n`, `no`, `f`, `false`, `off`, `0`;
- anything else, including the empty string: no value (`none`).

Thus `LAKE_ARTIFACT_CACHE=` is semantically “unset” for the workspace default. It is not equivalent to `LAKE_ARTIFACT_CACHE=false`.

The same-revision environment test preserves this distinction: with an empty incoming variable, `lake env` can emit the root package’s configured true or false value instead.

Basis: **source** in `Lake/Config/InstallPath.lean` and `Lake/Config/Env.lean`, plus same-revision **checked-in tests**.

### Effective package policy uses package configuration first, then the workspace default

The generic cache predicates are:

```text
readable := package.enableArtifactCache?
            <|> workspace.enableArtifactCache?
            |>.getD true

writable := package.enableArtifactCache?
            <|> workspace.enableArtifactCache?
            |>.getD false
```

The workspace default is:

```text
workspace.enableArtifactCache?
  := environment.enableArtifactCache?
     <|> root-package.enableArtifactCache?
```

This produces a two-level precedence rule.

1. A package’s explicit `enableArtifactCache` value wins for that package.
2. If the package is unset, it inherits the workspace default.
3. Within the workspace default, a recognized `LAKE_ARTIFACT_CACHE` value wins over the root package’s default.
4. If everything is unset, reads default to true and writes default to false.

A same-revision cache test exercises the first rule directly: a package configured with `enableArtifactCache = false` still declines the cache when the process sets `LAKE_ARTIFACT_CACHE=true`.

Basis: **source** in `Lake/Config/PackageConfig.lean`, `Lake/Config/Workspace.lean`, and `Lake/Config/Monad.lean`, plus same-revision **checked-in tests**.

### The default is intentionally read-only, not disabled

When neither the package nor workspace has an effective Boolean, the read and write predicates choose different defaults:

```text
isArtifactCacheReadable  -> true
isArtifactCacheWritable  -> false
```

This means “unset” is not equivalent to false. An unconfigured package may reuse artifacts that are already present, but a successful ordinary build does not by default publish new artifacts into the local artifact cache.

An effective false value disables both generic reads and writes. An effective true value enables both.

This asymmetry explains why the package-configuration documentation says Lake’s default is that a package “can use artifacts from the cache, but cannot write to it.”

Basis: **source** + **documentation embedded in source**.

### Location and permission form independent dimensions

For the normal cache-aware path, the useful state model has two independent axes:

| Cache location | Effective package policy | Consequence |
| --- | --- | --- |
| workspace-local `.lake/cache` | read-only default | may consume a seeded local cache; does not populate it |
| workspace-local `.lake/cache` | true | may consume and populate the local cache |
| explicit/shared cache directory | read-only default | may consume a seeded shared cache; does not populate it |
| explicit/shared cache directory | true | may consume and populate the shared cache |
| any location | false | generic artifact-cache read/write paths are disabled for that package |

Target coverage remains a third axis: only build paths that participate in Lake’s artifact-cache machinery can exhibit these behaviors.

Basis: **derived** from the configuration and package predicates above.

## Boundaries

No fresh Lake process was executed. The report uses exact pinned source and same-revision checked-in tests. It does not add new filesystem or performance observations.

This report does not claim that every build target uses the artifact cache. Target coverage is separately documented by the artifact-cache architecture/noncoverage reports.

This report does not characterize remote cache-service configuration, package build archives, `LAKE_NO_CACHE`, or Mathlib’s separate `lake exe cache` protocol.

`LAKE_CACHE_DIR=` disables Lake’s shared/system-cache selection; it does not promise that every process in a larger build graph uses only that workspace-local path. A parent build system can launch other tools or Lake invocations with different environments.

The package precedence described here is the generic `Package.isArtifactCacheReadable` / `Package.isArtifactCacheWritable` path. A specialized caller that bypasses those predicates is outside this report.

The workspace export behavior is an augmented-environment contract. It should not be mistaken for a claim that Lake preserves the parent process’s original environment bytes.

Adjacent Lean/Lake revisions can change cache discovery, precedence, or defaults. In particular, no continuity is inferred from later Lake source.

## Evidence

All implementation evidence is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- **Boolean parsing — source.** `src/lake/Lake/Config/InstallPath.lean`, blob `e309253fe8c39aa90ce48de295305d160286a9b1`, `envToBool?` at lines 20–24.
- **Environment parsing and cache discovery — source.** `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`, especially `Env.compute` and `addCacheDirs` around lines 128–201, plus exported variables around lines 304–312.
- **Package configuration contract — source/documentation.** `src/lake/Lake/Config/PackageConfig.lean`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`, `enableArtifactCache?` documentation around lines 273–289.
- **Workspace cache and workspace defaults — source.** `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`, `computeLakeCache` around lines 26–30, `enableArtifactCache?` around lines 95–106, and `augmentedEnvVars` around lines 351–359.
- **Effective per-package read/write policy — source.** `src/lake/Lake/Config/Monad.lean`, blob `59e032d7c516298a494c070abb948eafe2474184`, `Package.isArtifactCacheReadable` and `Package.isArtifactCacheWritable` around lines 186–207.
- **Environment behavior tests — checked-in execution specification.** `tests/lake/tests/env/test.sh`, blob `4cdee6b9ed39234ab584fa0f47697351b2f98f10`, especially lines 32–53.
- **Artifact-cache enablement tests — checked-in execution specification.** `tests/lake/tests/cache/test.sh`, blob `4c0134409f65b9e563cb3d7f26a1e550c013c140`, especially lines 26–39.

Related corpus reports:

- `reports/lake-artifact-cache-architecture-v4-30-0-rc2`
- `reports/lake-artifact-cache-key-semantics-v4-30-0-rc2`
- `reports/lake-artifact-cache-publication-restoration-v4-30-0-rc2`
- `reports/lake-artifact-cache-noncoverage-v4-30-0-rc2`

Those reports establish what the cache contains and how cache-aware builds use it. This report supplies the missing exact semantics of the two environment variables that choose cache location and default package policy.

## Revalidation

For a later Lake revision, revalidate the configuration chain before running broader cache experiments.

1. Inspect `envToBool?` and `Env.compute` for accepted Boolean spellings and `LAKE_ARTIFACT_CACHE` parsing.
2. Inspect `Env.compute`/cache-discovery helpers for the three `LAKE_CACHE_DIR` cases: nonempty, empty, and unset.
3. Inspect `computeLakeCache` for package-local fallback and any bootstrap distinction.
4. Inspect `Workspace.enableArtifactCache?` plus `Package.isArtifactCacheReadable` / `Package.isArtifactCacheWritable` for precedence and asymmetric defaults.
5. Inspect `Workspace.augmentedEnvVars` for what `lake env` exports to child processes.
6. Run the same-revision-style `env` and `cache` tests with an isolated root, checking at least:
   - `LAKE_CACHE_DIR=<explicit path>`;
   - `LAKE_CACHE_DIR=`;
   - `LAKE_CACHE_DIR` unset with and without Elan/toolchain cache discovery;
   - `LAKE_ARTIFACT_CACHE=true`, `false`, empty, and one invalid nonempty value;
   - package-explicit true/false against conflicting environment values; and
   - the default readable-but-not-writable case with a preseeded artifact.

Record both the resolved cache path and whether the target replayed/fetched/built. Location evidence alone does not establish the effective read/write policy, and cache-policy evidence alone does not establish which directory supplied the artifact.
