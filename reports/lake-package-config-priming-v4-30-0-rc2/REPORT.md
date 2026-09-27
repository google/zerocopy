# Lake package-config priming at v4.30.0-rc2

## Summary

At Lake `v4.30.0-rc2`, priming a Lean-authored dependency's package
configuration means creating a cache entry that Lake will accept **in the later
consumer's dependency identity**, before that dependency tree becomes read-only.
The relevant persistent state is the dependency package's
`.lake/config/<assigned-name>/<config>.olean` together with its
`.olean.trace`. A later cache hit opens the trace read-only under a shared lock and
imports the compiled configuration; a miss or stale entry enters a write path
that can delete the old `.olean`, rewrite the trace, and elaborate a replacement.

The cache identity is context-sensitive. At this revision the trace validates the
workspace-assigned package index and name, the configuration-file content hash,
the target platform, and the Lean Git hash. The cache directory is also selected
by the assigned package name. A producer that primes the same source checkout
under the wrong dependency index or alias can therefore leave a cache that a
read-only consumer immediately rejects and tries to rewrite.

Current Anneal V1 contains a concrete implementation of this rule. While building
its managed Aeneas archive, it creates a throwaway workspace whose only direct
dependency is that Aeneas package, runs `lake --old build Generated` after
importing `Aeneas`, and asserts that
`.lake/config/aeneas/lakefile.olean` now exists in the Aeneas package. Anneal V1
later generates workspaces that also require the managed archive directly as
`aeneas`; their locked manifest preserves that direct dependency and its inherited
dependency closure. In Lake's pinned resolver, the first direct dependency is
loaded at workspace package index `0`, so the primer deliberately reproduces the
later consumer's `idx = 0`, `name = aeneas` configuration-cache identity.

This is a cache-priming technique, not a general proof that any compiled Lake
configuration is relocatable or safe to share read-only. The cache-validity
predicate does not include package or workspace paths, and the package-directory,
name, and `-K` option context used while elaborating are stored in ordinary
non-persistent environment extensions rather than directly in the serialized
module-extension set that Lake reloads. However, a Lake configuration can define
constants, scripts, targets, or other persistent declarations whose values depend
on elaboration-time context. A source-specific or execution-level check is still
needed before treating arbitrary package configurations as relocation-independent.

Two additional details matter for reproducing the technique. First, a valid cache
hit still calls `createDirAll` on the already-existing config directory but does
not rewrite the trace or `.olean`; the later read-only filesystem must therefore
already contain the directory and permit normal traversal/open/locking of the
read-only files. Second, `--old` is part of Anneal's surrounding build-cache
strategy, but it is not an input to the package-config cache's freshness predicate.
The priming effect comes from loading the package configuration under the right
dependency identity, not from old-mode trace semantics.

No fresh Lake or Anneal execution was performed for this report. The Lake
mechanism is established from exact pinned source, and the Anneal recipe is
established from current `google/zerocopy` source.

## Applicability

The Lake findings apply to
`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
(`v4.30.0-rc2`). They concern Lean-authored package configuration loaded through
`Lake.Load.Lean.importConfigFile`.

The Anneal-specific findings apply to
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, where
`anneal/flake.nix` contains an explicit V1-only Aeneas configuration primer and
`anneal/v1/src/aeneas.rs` generates the corresponding locked consumer workspace.

This report explains **priming**, not the entire `.lake/config` format. The
neighboring corpus report
`lake-config-cache-contents-invalidation-v4-30-0-rc2` owns the full trace schema,
freshness algorithm, lock transition, malformed-trace behavior, and option-cache
quirks. Those facts are reused here only where they determine whether precomputed
state survives into a read-only consumer.

Likewise, this report does not generalize to the Lake configuration-ownership
model introduced after v4.30.0-rc2. Current upstream Lake source has changed this
area; the issue inventory deliberately tracks the later ownership model as a
separate subject.

## Findings

### A useful prime must populate the dependency package's own config cache

At this revision, `LoadConfig.lakeDir` is `cfg.pkgDir / ".lake"`.
`importConfigFile` then forms:

```text
<cfg.pkgDir>/.lake/config/<cfg.pkgName>/<config-name>.olean
<cfg.pkgDir>/.lake/config/<cfg.pkgName>/<config-name>.olean.trace
<cfg.pkgDir>/.lake/config/<cfg.pkgName>/<config-name>.olean.lock
```

The compiled configuration is therefore package-local. Priming a root workspace's
own configuration cache is not enough to make a dependency's configuration
read-only later: the later load looks in the dependency package's directory and
under the dependency's assigned name.

On a cache hit, Lake opens the existing trace in read mode, takes a shared lock,
checks the trace, imports the `.olean`, unlocks, and returns the reconstructed
configuration environment. It does not rewrite the trace or `.olean` on that
path.

Basis: **source**.

### Cache identity includes the workspace-assigned package index and name

`ConfigTrace` records:

```text
idx        : Nat
name       : Name
platform   : String
leanHash   : String
configHash : Hash
options    : NameMap String
```

The ordinary `upToDate` predicate requires the `.olean` to exist and compares
`idx`, `name`, `configHash`, `platform`, and `leanHash`. `options` is persisted
but is not compared by this predicate.

For priming, `idx` and `name` are the surprising fields. They are not intrinsic
properties of a source checkout. They come from the workspace resolver:

- `pkgName` is the dependency name used by the requiring workspace;
- `pkgIdx` is the workspace package index assigned when that dependency is
  loaded.

A cache created for one dependency context can therefore be stale in another even
when the package bytes, toolchain, and platform are identical.

Basis: **source**.

### The assigned name affects both lookup location and validation

`importConfigFile` converts `cfg.pkgName` to text and includes it in the
configuration-cache directory path. The same name also appears in `ConfigTrace`
and is checked on reuse.

Aliasing one physical package under a different dependency name therefore has two
effects: Lake looks in a different `.lake/config/<name>/` subtree, and any trace
copied into that subtree would still have to carry the new assigned name.

A robust primer should reproduce the later consumer's dependency alias rather
than merely compile the package once under whatever name its own root
configuration uses.

Basis: **source**.

### The package index makes priming sensitive to dependency-load context

In the pinned resolver, a missing direct dependency is loaded with
`ws.packages.size` as its workspace index and is then added to the workspace
package list. Recursive dependencies are loaded afterward. The root package itself
is loaded separately with index `0`; dependency indices are maintained in the
workspace package list used by resolution.

The practical consequence is that a dependency's trace can be invalidated by a
different surrounding dependency graph or load order. A primer that happens to
load package `P` at index `3` does not create a trace that will validate when the
final consumer assigns `P` index `0`.

This is why "build the package somewhere, then copy its `.lake` directory" is not
a complete priming specification. The producer must either reproduce the final
dependency identity or deliberately arrange and validate the cache under that
identity.

Basis: **source**; the priming consequence is **derived**.

### A cache miss or stale trace is incompatible with a truly read-only package tree

When the trace is missing, Lake opens a new trace file for writing, locks it,
writes configuration metadata, elaborates the package configuration, and writes
the `.olean`.

When an existing trace is stale, Lake transitions from a shared trace lock toward
a write path. It opens the companion `.olean.lock` for writing, obtains an
exclusive transition lock, reopens the trace read/write, removes the old
`.olean`, rewrites/truncates the trace, elaborates the configuration, and writes a
new `.olean`.

Therefore read-only use depends on **hitting** the primed cache. Priming is not a
performance optimization layered on top of an otherwise read-only fallback.
Missing or stale state changes the filesystem contract from read to write.

Basis: **source**.

### An up-to-date hit is materially narrower than reconfiguration

Even on the hit path, `importConfigFile` first calls `createDirAll` for the cache
directory. It then opens the trace read-only and takes a shared lock before
importing the `.olean`.

The pinned source does not write the config trace or compiled configuration when
the entry is valid. That is the source-level property a read-only archive relies
on. It does not establish that every filesystem, mount option, or operating
system permits the exact directory and file-lock calls Lake makes against a
read-only tree.

A capable-surface validation should therefore test the final permission mode
rather than assuming "no explicit write in this branch" proves complete
filesystem compatibility.

Basis: **source** plus a **derived** operational boundary.

### Current Anneal V1 primes Aeneas in a throwaway consumer-shaped workspace

`anneal/flake.nix` labels the step a "v1-only package config primer." After the
vendored package tree and build artifacts have been prepared, it creates a
temporary workspace containing:

```lean
import Lake
open Lake DSL

require aeneas from "@AENEAS_ROOT@"

package anneal_verification

@[default_target]
lean_lib «Generated» where
  srcDir := "generated"
  roots := #[`Generated]
```

The generated module contains `import Aeneas`. Anneal substitutes the actual
managed Aeneas root, runs:

```text
lake --old build Generated
```

from that temporary workspace, and then asserts:

```text
.lake/config/aeneas/lakefile.olean
```

inside the Aeneas package before the archive is frozen and copied to its final
output.

The key property is not that this is a throwaway workspace. It is that loading
`Generated` forces Lake to load Aeneas as a **dependency named `aeneas`**, causing
Lake to compile/import Aeneas's package configuration in the same dependency role
the later V1 generated workspaces use.

Basis: current Anneal **source**.

### The Anneal V1 consumer reproduces the same direct-dependency identity

`anneal/v1/src/aeneas.rs` generates a workspace whose Lake file contains one
direct requirement:

```text
require aeneas from "<managed Aeneas Lean directory>"
```

It also writes a complete `lake-manifest.json`. The manifest's first package
entry is a path dependency named `aeneas` pointing at that managed directory;
the package entries imported from Aeneas's own manifest follow as inherited path
dependencies.

At the pinned Lake revision, root dependency resolution begins with an empty
workspace package list. Because the root has one direct dependency, Aeneas is
loaded with `ws.packages.size == 0`, assigned name `aeneas`, and package index
`0`. Its transitive dependencies are resolved afterward.

The throwaway primer has the same one direct dependency. It therefore primes
Aeneas under the same `idx = 0`, `name = aeneas` identity that V1 generated
workspaces later present to the cache.

This relationship is the strongest explanation in current source for why Anneal
constructs a consumer-shaped primer instead of relying on the archive's ordinary
self-build.

Basis: pinned Lake **source** + current Anneal **source** + **derived**
cross-source synthesis.

### The complete generated manifest prevents dependency materialization from defeating the prime

The V1 generator does not rely on Lake to rediscover or rewrite the Aeneas
dependency graph. It reads Aeneas's installed manifest, emits Aeneas itself as a
path dependency, converts its dependency entries to path dependencies relative to
the generated workspace, marks those transitive entries inherited, and writes
the complete manifest before the generated workspace is activated.

The source comment states the purpose directly: keep Lake on the locked dependency
loading path so package config/build caches can stay read-only.

This matters because package-config priming alone cannot make an archive
read-only if workspace loading decides the dependency graph needs update,
materialization, or fetch work before it ever reaches the cached configuration.

Basis: current Anneal **source**; dependency-loading consequence consistent with
the pinned Lake resolver.

### `--old` is not the package-config cache key

Anneal's primer invokes `lake --old build Generated`. In the surrounding
`flake.nix`, old mode is used after vendoring rewrites changed Lake dependency
hashes while preserved build artifacts retained useful mtimes. The source comment
describes that as an archive-verification/build-cache measure.

The package-config cache described here does not key freshness on Lake's old-mode
setting. `ConfigTrace` contains no old-mode field, and `importConfigFile` bases
ordinary reuse on the package identity, config content hash, platform, Lean hash,
and `.olean` existence.

Thus the reusable priming rule is not "run Lake with `--old`." It is "cause Lake
to load and compile the package configuration under the final consumer identity
while the package tree is still writable." Anneal's exact build command also
needs old mode for adjacent build-artifact reasons.

Basis: pinned Lake **source** + current Anneal **source** + **derived**
separation of concerns.

### Priming should use the intended configuration options, even though the cache fails to key all of them

`ConfigTrace.options` records Lake `-K` options, but ordinary freshness does not
compare current `cfg.lakeOpts` with the persisted option map. Current
`cfg.leanOpts` is likewise not represented in the trace identity.

That makes priming more—not less—sensitive to producer discipline. If a producer
primes with one `-K` option set and the consumer later supplies another, the
otherwise-valid cache can be imported rather than re-elaborated. A producer that
wants a predictable read-only artifact should therefore prime using the exact
configuration semantics intended for consumers and treat relevant option changes
as requiring an explicit re-prime/revalidation, rather than expecting Lake's
freshness predicate to catch them.

If an explicit reconfigure is requested, Lake intentionally takes the write path,
which is incompatible with an immutable package cache.

Basis: **source**; producer guidance is **derived**.

### The trace identity is path-blind, but arbitrary configuration relocation is not thereby proven

The config trace does not contain the workspace path or package path. In
addition, the package index/name, package directory, and Lake option context used
to initialize configuration elaboration are stored in ordinary `EnvExtension`s
(`nameExt`, `dirExt`, and `optsExt`), not persistent environment extensions.

`importConfigFileCore` reconstructs a cached environment by loading the module's
constants and a selected set of persistent Lake, docstring, and IR extension
entries. It does not restore arbitrary ordinary `EnvExtension` state from the
serialized module.

These facts explain why the cache-validity mechanism itself does not reject a
relocated package merely because its absolute directory changed. They do **not**
prove that every lakefile is semantically relocation-independent. Configuration
commands can elaborate declarations, scripts, targets, or values that reflect
the environment available during elaboration; persistent output can therefore
capture source-specific information even when the generic trace schema does not.

Current Anneal is concrete evidence that the project intentionally relies on a
primed Aeneas configuration surviving its archive-production flow. A fresh
read-only/relocation execution probe remains the right way to validate that
assumption at the exact packaged artifact boundary.

Basis: **source** + **derived** boundary.

### Priming the dependency cache and preserving the generated workspace cache solve different problems

Anneal V1 also preserves the generated workspace's own `.lake` directory when it
atomically regenerates the generated Lean source tree. That preserves
workspace-local build/configuration state across regeneration.

This is separate from the archive primer. The Aeneas package's compiled
configuration lives in the managed Aeneas package tree; the generated workspace's
own `.lake` tree lives beside generated/user/Anneal source. A design can need both:
one to keep shared dependency state immutable, and one to avoid unnecessarily
discarding mutable consumer-local cache state.

Basis: current Anneal **source**.

## Boundaries

No Lake, Lean, Nix, or Anneal executable was run for this report. Current Anneal
source establishes that the primer exists and how it is constructed, but this run
did not independently demonstrate that a newly built archive survives the final
copy/permission/relocation boundary without reconfiguration.

The report does not claim that `.olean.lock` must exist after a first-time prime.
The companion lock path is defined for stale-cache lock upgrades; an ordinary
up-to-date hit opens only the trace read-only and imports the `.olean`.

The report does not claim that a valid package-config cache makes the whole
dependency tree read-only. Lake build outputs, ordinary module traces/hashes,
manifests, artifact-cache state, server setup, and other package/workspace state
have separate write contracts.

The report does not claim that path relocation is harmless for arbitrary
lakefiles. The generic cache identity omits package/workspace paths, but
configuration-specific persistent declarations may still encode
elaboration-time assumptions.

The report does not treat the omission of `options`/`leanOpts` from the freshness
identity as a stability guarantee. It is a cache-key limitation and a reason to
prime with deliberate option discipline.

The report does not project these v4.30.0-rc2 ownership paths onto v4.31 or current
Lean `main`. The issue inventory tracks the later configuration-ownership change
separately.

The current Anneal source labels the primer V1-only and contains a FIXME to remove
it once generated workspaces migrate to V2. This report therefore does not infer
that future Anneal V2 must preserve this exact mechanism.

## Evidence

The Lake subject is
`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
(`v4.30.0-rc2`).

Pinned primary **source**:

- `src/lake/Lake/Load/Lean/Elab.lean`, blob
  `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`: `ConfigTrace`,
  `importConfigFile`, `importConfigFileCore`, the cache-hit predicate,
  read/shared locking, stale write transition, trace/olean write order, and
  selected persistent extension restoration.
- `src/lake/Lake/Load/Config.lean`, blob
  `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`: the package-local
  `LoadConfig.lakeDir` at this revision.
- `src/lake/Lake/Load/Resolve.lean`, blob
  `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`: dependency loading with
  workspace-assigned package index and dependency name.
- `src/lake/Lake/Load/Workspace.lean`, blob
  `9f25dd62bc752ede695a25fc20371157eb65d64b`: root workspace loading and
  root-package setup.
- `src/lake/Lake/DSL/Extensions.lean`, blob
  `2f9a53c0883887889a7c9dc104482b8612c9a73f`: ordinary environment
  extensions carrying package index/name, package directory, and Lake options.
- `src/lake/Lake/Load/Lean.lean`, blob
  `b38ee619b42d8293fc9e4ffb4b8e2f4b1508c1e7`: package-configuration
  loading through `importConfigFile`.

The Anneal subject is
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

Current primary **source**:

- `anneal/flake.nix`, blob
  `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: archive build,
  V1-only `aeneas-config-primer`, `lake --old build Generated`, explicit
  `.lake/config/aeneas/lakefile.olean` assertion, later trace rewriting/pruning,
  and final archive copy.
- `anneal/v1/src/aeneas.rs`, blob
  `9b4618a20938315afc290744bbdfa498848620f4`: generated V1 Lakefile,
  direct `require aeneas`, complete path-based manifest, inherited Aeneas
  dependency entries, and preservation of generated workspace `.lake` state.

Neighboring current corpus evidence reused to avoid redoing already durable
research:

- `reports/lake-config-cache-contents-invalidation-v4-30-0-rc2/REPORT.md`,
  blob `e8cae1b63d2c429aec41f27b1b5b94e9ed40ddd7`: full `.lake/config`
  schema, freshness, option, failure, and locking model.
- `reports/lake-readonly-relocation-offline-concurrency-v4-30-0-rc2/REPORT.md`,
  blob `8939500f86c03c4da7d9339f8a02c12346267cf6`: broader prepared-state
  read-only/relocation/concurrency boundaries.
- `reports/lake-server-preparation-v4-30-0-rc2/REPORT.md`, blob
  `589374b2335773dffdcd4702100f9edfd0479c2f`: file-specific language-server
  preparation, kept separate from package-config priming.

There is no fresh **execution** evidence in this package.

## Revalidation

The cheapest source revalidation for another Lake revision is to inspect these
boundaries in order:

1. where `LoadConfig` places the compiled configuration cache;
2. how `importConfigFile` derives its directory and trace/olean paths;
3. the exact `ConfigTrace` fields and `upToDate` predicate;
4. the cache-hit file operations versus the stale/missing write path;
5. how the resolver assigns dependency package index and name;
6. whether package directory/name/options remain ordinary environment extensions
   or move into persistent serialized state; and
7. which extension entries `importConfigFileCore` restores from the cached
   module.

For Anneal, diff the V1 generated Lakefile/manifest and the Nix primer together.
The two sides must continue to agree on the Aeneas dependency identity. A primer
change without the consumer manifest, or vice versa, can make the cache
self-invalidating.

A minimal capable-surface probe should use the actual packaged artifact, not only
a writable source checkout:

1. build/obtain the managed Aeneas archive and record the exact Lean/Lake/Aeneas
   revisions;
2. inspect the Aeneas package's `.lake/config/aeneas/` directory and decode the
   `lakefile.olean.trace`;
3. record its `idx`, `name`, `platform`, `leanHash`, `configHash`, and `options`;
4. make the managed Aeneas tree read-only in the same way the production archive
   is read-only;
5. create a fresh V1-shaped generated workspace with the production complete
   manifest and run the smallest Lake command that must load Aeneas's package
   configuration;
6. verify the command succeeds without changing any file under the managed Aeneas
   tree, and compare the full pre/post tree metadata or hashes;
7. repeat after moving the archive root while preserving relative manifest
   topology;
8. deliberately change only the assigned dependency name and then only the
   dependency load index, verifying that Lake rejects the primed trace and enters
   the expected write/reconfigure path;
9. repeat with a materially changed `-K` option and with explicit `-R`, recording
   the distinction between silent cache reuse and forced reconfiguration; and
10. finally run the production `lake --old build Generated` / `lake env lean`
    consumer flow to distinguish package-config success from unrelated build or
    server-preparation failures.

Preserve commands, exact file permissions, decoded trace JSON, package-manifest
bytes, directory locations, and pre/post hashes. A passing probe establishes the
specific archive/configuration combination tested; it is not a universal
relocation theorem for arbitrary Lake configurations.
