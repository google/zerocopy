# Native artifacts inside Lean/Lake package trees at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), a Lake package can contain several distinct layers of compiled output. Lean's core module build emits `.olean`, `.ilean`, `.ir`, generated C, and optionally LLVM bitcode. Separate Lake facets compile C or bitcode into host object files, combine object files into static libraries, link shared libraries, and link executables. The defaults matter: a bare Lean-library target builds its `leanArts` facet, not its static or shared-library facet, while `precompileModules` is opt-in and causes per-module shared libraries to be loaded on import.

Those native outputs are not uniformly “files under `.lake/build`.” Lake's local artifact cache can make an artifact's preferred path live in the toolchain cache instead of the package build directory. Callers that require conventional package-local paths must request restoration. Conversely, static libraries, shared libraries/plugins, and executables use build paths that Lake explicitly restores on cache hits when their build helpers require stable names or locations.

Native machine-code products are platform-sensitive. Lake mixes the host platform into object, shared-library, and executable traces; static libraries are built from the platform-traced object jobs. A prepared package tree therefore must not treat retained `.o`, `.a`, `.so`, `.dylib`, `.dll`, or executable bytes as cross-platform substitutes merely because source-level Lean artifacts or package metadata are reusable.

Current Anneal pruning is narrower than the full native-artifact surface. For each pruned Mathlib module it removes matching module-prefix files only from `.lake/build/lib/lean` and `.lake/build/ir`, and it deletes `.ltar` archives globally. It does not inventory package-level static/shared libraries or prove that any retained per-module precompiled shared library still corresponds to the retained source/module set. This is conservative for deletion but incomplete as a native-artifact consistency argument.

No fresh Lean/Lake build was executed. The findings are exact-pin source facts plus derived consequences for the current Anneal package-pruning implementation.

## Applicability

The Lake findings apply to Lean/Lake `v4.30.0-rc2` at commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. They describe the built-in Lean module, Lean library, artifact-cache, and environment machinery at that revision. Custom facets and external build systems can add other native outputs.

The Aeneas-specific observation applies to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the release selected by current Anneal. Its `backends/lean/lakefile.lean` has two default Lean-library targets. `Aeneas` uses the ordinary defaults; `AeneasMeta` sets `precompileModules := notCI`, so per-module native shared libraries are potentially part of a non-CI build but are intentionally disabled when `CI` is present.

The pruning observations apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, specifically `anneal/prune-lake-cache.py` and the prepared-tree construction in `anneal/flake.nix`. They describe what the current script removes, not a proof that every retained or removed file is semantically necessary.

This report complements, rather than replaces, the existing reports on Lake artifact hashes/cache identity and read-only/relocation behavior. It focuses on the *classes, locations, build dependencies, and runtime role* of native artifacts inside or associated with a package tree.

## Findings

### Lean module outputs and native machine code are separate layers

`Lake.Build.Facets` defines the module `leanArts` facet as the Lean invocation that produces the module's Lean artifacts. At this pin, those outputs include `.olean`, `.ilean`, `.ir`, generated C, and optional LLVM bitcode. `ModuleOutputArtifacts` records exactly those classes, plus module-system `.olean.server` / `.olean.private` outputs and an optional `.ltar` archive.

The native object layer is separate. Module facets expose `c.o`, `c.o.export`, `c.o.noexport`, `bc.o`, and the generic `o` facet. `buildLeanO` compiles the generated source to an object file with Lean's C compiler and explicitly mixes the host platform into the build trace. The generic `o` facet selects the relevant C- or LLVM-based object path for the module configuration.

The library layer is separate again. A Lean library has built-in `static`, `static.export`, and `shared` facets. Static construction collects the modules' configured native facets and archives their object files. Shared construction collects those native objects plus dependency dynamic libraries and links the result with the Lean toolchain. Lake likewise builds executables from native objects and dynamic-library dependencies.

The distinction is operationally important for prepared trees: preserving `.olean` / `.ilean` or even generated C is not equivalent to preserving a ready-to-link native library. Conversely, a retained `.a` or `.so` is downstream compiled state whose validity depends on the object/compiler/link inputs that produced it.

Basis: **source** — `Lake/Build/Facets.lean`, `Lake/Build/ModuleArtifacts.lean`, `Lake/Build/Module.lean`, `Lake/Build/Library.lean`, and `Lake/Build/Common.lean` at the pinned Lean revision.

### Default package layout gives native outputs distinct locations

Lake's default package build directory is `.lake/build`. Within that directory, `leanLibDir` defaults to `lib/lean`, `nativeLibDir` defaults to `lib`, `binDir` defaults to `bin`, and `irDir` defaults to `ir`.

The resulting path split is deliberate:

- Lean module/library interface artifacts live under the package's Lean library directory;
- generated C, bitcode, object files, and other intermediary results use the IR directory;
- package-level static and shared libraries use the native library directory;
- executables use the binary directory.

A single-module precompiled dynamic library is an exception worth tracking explicitly: `Module.dynlibFile` places it in the package's Lean library directory and names it using the module initialization stem plus the platform shared-library extension. The file is therefore not simply the module path plus `.so`/`.dylib`/`.dll`.

Basis: **source** — `Lake/Config/Defaults.lean`, `Lake/Config/PackageConfig.lean`, `Lake/Config/Package.lean`, and `Lake/Config/Module.lean`.

### Bare Lean-library builds do not imply static/shared native libraries

`LeanLibConfig.defaultFacets` defaults to `#[LeanLib.leanArtsFacet]`. Thus an ordinary bare library build requests Lean module artifacts, not the library's `static` or `shared` facet. Static and shared libraries appear when a target/facet or another dependency requests them.

`precompileModules` is also false by default. When enabled, Lake compiles modules into native shared libraries that are loaded when those modules are imported; the configuration documentation specifically describes the purpose as accelerating metaprogram evaluation and supporting interpreted functions marked `@[extern]`.

The Aeneas pin makes this distinction concrete. Its `Aeneas` target leaves `precompileModules` at the default. `AeneasMeta` enables it only when the `CI` environment variable is absent. A prepared Anneal tree should therefore determine the actual build mode before inferring whether per-module dynamic libraries ought to exist.

Basis: **source** — `Lake/Config/LeanLibConfig.lean`, `Lake/Config/PackageConfig.lean`, and Aeneas `backends/lean/lakefile.lean`.

### Native artifacts can live in Lake's artifact cache rather than only in the package tree

Package configuration explicitly warns that artifact-cache-enabled targets may not be stored at their usual build-directory locations. Lake's build helpers represent outputs as content-addressed `Artifact` values; a cache hit can leave the preferred path in the cache unless the caller requests restoration or package/workspace policy enables `restoreAllArtifacts`.

The module build makes the distinction visible. Cache restoration always restores `.ilean` when only required outputs are needed, while `restoreAllArtifacts` also restores `.olean`, server/private oleans, IR, generated C, optional bitcode, and the `.ltar`. Native object construction uses the same artifact-cache-aware `buildArtifactUnlessUpToDate` machinery. Static libraries, shared libraries, and executables request `restore := true`, so their helpers restore cache hits to the conventional output path before returning them.

Prepared-tree logic must therefore distinguish two questions:

1. Is an artifact semantically available to Lake through the cache?
2. Is a package-local file present at the path an external consumer expects?

The two conditions are not equivalent. `restoreAllArtifacts` exists specifically to bridge that gap for consumers that inspect the build tree directly.

Basis: **source** — `Lake/Config/PackageConfig.lean`, `Lake/Build/Common.lean`, and `Lake/Build/Module.lean`.

### Host-native outputs are platform-dependent build state

`buildLeanO` and the generic object builder call `addPlatformTrace`; so do the shared-library and executable builders. Lake documents that a platform trace makes an artifact platform-dependent and causes it to rebuild on a different host platform. The trace uses `System.Platform.target`.

Static-library construction does not add a second platform token directly, but it consumes the object jobs that already carry platform-sensitive traces. The static archive is therefore derived from platform-specific object inputs. This is a dependency argument, not a claim that every archive format byte is unique to one platform.

The package's runtime environment also treats shared libraries as host-specific loadable state. The workspace shared-library search path includes each package's shared-library directory; on non-Windows hosts `lake env` augments the platform shared-library environment variable, while Windows adds shared-library directories to `PATH`.

The practical boundary is narrow: these source facts establish that Lake *intends* the native outputs to be host-platform-sensitive. They do not by themselves establish the detailed cross-OS/architecture portability of every file format; that remains the separate portability inventory subject.

Basis: **source** + **derived** — `Lake/Build/Common.lean` and `Lake/Config/Workspace.lean`.

### Current Anneal pruning covers module-path artifacts but not the full native library surface

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `prune-lake-cache.py` removes an unused Mathlib source module and then scans exactly two build subdirectories: `lib/lean` and `ir`. Within the corresponding module directory, it deletes files whose basename starts with `<module-name>.`. This catches the ordinary module-path family in those two directories, including generated C/bitcode/object-style files that follow that naming convention.

The script does not scan the package native-library directory as a separate semantic inventory. It therefore does not delete or validate package-level `lib<name>.a`, `.so`, `.dylib`, or `.dll` outputs merely because a source module was pruned. It also does not derive the mangled `Module.dynlibName` used by precompiled per-module shared libraries, so its `<module-name>.` deletion rule is not a proof that those dynamic libraries are removed when their source modules are removed.

This behavior is conservative in one dimension: the script is less likely to delete an unknown package-level native artifact merely because a module disappeared. But it leaves a separate consistency question. A retained native library can remain present—and shared-library directories remain runtime search inputs—even when the script has changed the package's source/module set. Current pruning therefore needs an explicit native-artifact inventory if Anneal wants either to delete those files safely for size or to assert that every retained native artifact corresponds to the retained sources.

The script does delete every `.ltar` archive under each package after pruning. That avoids preserving module-archive bundles whose member set may no longer match the pruned tree, but `.ltar` removal does not address package-level native libraries.

Basis: **source** — current Anneal `anneal/prune-lake-cache.py`; **derived** comparison with the pinned Lake path and naming rules.

### A durable prepared-tree policy can classify native artifacts by consumer

The source suggests a practical classification for Anneal without assuming that every file deserves the same treatment:

1. **Lean import artifacts** (`.olean`, `.ilean`, module-system variants, `.ir` where required) serve elaboration/import consumers and are covered by Lake's module-artifact machinery.
2. **Generated native inputs** (`.c`, optional `.bc`) are reproducible compiler inputs rather than linked native binaries.
3. **Module object files** (`.c.o`, `.bc.o`, generic `o`) are host-native intermediate state and should be retained only when later native linking or cache reuse needs them.
4. **Per-module precompile libraries** are runtime-loadable artifacts tied to `precompileModules`; their presence requirement depends on the selected package configuration/build mode.
5. **Package static/shared libraries and executables** are target/facet outputs with consumers distinct from Lean import resolution. Keep or remove them based on whether the prepared environment exposes those facets/targets or expects external/runtime use.

This classification is **derived**, not a Lake-declared lifecycle policy. Its value is that it ties pruning decisions to actual consumers rather than file extensions alone.

## Boundaries

**No fresh build or prune execution.** This run did not execute Lean, Lake, Aeneas, Nix, a C compiler/linker, or `prune-lake-cache.py`. Source establishes the build graph, configured locations, cache/restoration behavior, and current pruning algorithm, but not the exact native files present in a produced Anneal archive.

**No complete archive inventory.** The report does not claim that current Anneal archives contain a particular `.o`, `.a`, `.so`, `.dylib`, `.dll`, or precompiled-module library. Presence depends on the actual target/facet graph and environment, including AeneasMeta's `CI`-sensitive `precompileModules` setting. Inspecting a produced archive is the cheap discriminator.

**No cross-platform compatibility conclusion beyond Lake's trace policy.** Source establishes explicit platform traces on object/shared/executable construction and platform-sensitive downstream inputs. Detailed portability of artifact formats, ABI, toolchain versions, or same-platform-but-different-system configurations remains the separate cross-platform portability subject.

**No claim that retained native artifacts are currently unsafe.** Current Anneal pruning may leave package-level or mangled native files that are no longer needed. Source inspection alone does not show that current consumers load stale bytes. It shows that the pruning algorithm does not establish the stronger correspondence invariant.

**No universal pruning rule for custom packages.** Custom Lake facets, external libraries, plugins, scripts, and package-specific consumers can add native outputs or path assumptions outside these built-ins.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Lean/Lake subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/lake/Lake/Build/Facets.lean`, blob `0fcff78fdc4274994dc64229097ae4425f1361dd`: built-in module/library facet taxonomy, including `leanArts`, C/bitcode/object facets, and static/shared library facets.
- `src/lake/Lake/Build/ModuleArtifacts.lean`, blob `9863290328250c33d9933b1569387d96ec244da8`: exact `ModuleOutputDescrs` / `ModuleOutputArtifacts` classes.
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: module output cleanup/caching/restoration, `.ltar` packing, Lean build outputs, object/dynamic-library facets, and precompiled-module dependency behavior.
- `src/lake/Lake/Build/Library.lean`, blob `6cb600d16b99f31d29e13dccc6cdfccef6a8b23a`: static/shared Lean-library construction from native module facets.
- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: platform traces, content-addressed artifact restoration, object/static/shared/executable build helpers.
- `src/lake/Lake/Config/Defaults.lean`, blob `03033b5a032e450540ad99cc7c3be73544ad7416`: default package build subdirectories.
- `src/lake/Lake/Config/PackageConfig.lean`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`: package output-directory semantics, `precompileModules`, artifact-cache caveat, and `restoreAllArtifacts`.
- `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: resolved package paths for static/shared libraries and IR.
- `src/lake/Lake/Config/LeanLibConfig.lean`, blob `3cb6ba173b7e213bda5fedd7c390822d3f8fc8b3`: default `leanArts` facet and default native module facets.
- `src/lake/Lake/Config/LeanLib.lean`, blob `077efb6c244fd53bab5dead6c850d40161c96e7f`: static/shared library filenames and paths; inherited precompile/native-facet configuration.
- `src/lake/Lake/Config/Module.lean`, blob `f8b938e16fe53ada616364033b8d8353baa733ee`: IR/object paths and mangled per-module dynamic-library path.
- `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`: workspace shared-library search path and `lake env` augmentation.

Aeneas subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

- `backends/lean/lakefile.lean`, blob `c32062866e2f88d2eb768b904745e7104edddb0d`: default `Aeneas` / `AeneasMeta` libraries and `CI`-sensitive `precompileModules` configuration.

Anneal subject: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/prune-lake-cache.py`, blob `b0eb8eaa5ecefad9766a155994968712826ed996`: module reachability pruning, exact build directories scanned, prefix deletion rule, `.ltar` deletion, and metadata removal.
- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: current prepared-cache construction, pre-prune `lake --old build`, pruning stage, and archive checks.

Related current reference reports used to preserve boundaries:

- `reports/lean-lake-trace-hash-artifacts-v4-30-0-rc2`: Lake content hashes and module-output invalidation.
- `reports/lake-readonly-relocation-offline-concurrency-v4-30-0-rc2`: read-only and artifact-cache location constraints.
- `reports/aeneas-lean-project-package-anatomy-nightly-2026-06-03`: Aeneas Lean package structure and precompile configuration context.

Evidence roles are **source** and **derived**. There is no fresh **execution** evidence.

## Revalidation

For another Lean/Lake revision, first inspect `Lake/Build/Facets.lean` and `Lake/Build/ModuleArtifacts.lean` to recover the artifact taxonomy. Then inspect `Lake/Config/PackageConfig.lean`, `Package.lean`, `Module.lean`, and `LeanLibConfig.lean` for default locations, native-facet selection, precompile semantics, and cache restoration. Finally inspect the object/library/executable helpers in `Lake/Build/Common.lean` and `Lake/Build/Library.lean` for platform traces and restoration behavior.

For Anneal, the cheapest discriminating execution is an archive inventory on each supported platform/build mode:

1. build the exact prepared tree with the current Nix path;
2. before and after pruning, enumerate `.lake/build/ir`, `.lake/build/lib/lean`, `.lake/build/lib`, and `.lake/build/bin` by relative path, file type, size, and SHA-256;
3. classify every `.o`, `.a`, shared library, executable, and mangled per-module dynamic library by the Lake target/facet that produced it;
4. run the prepared environment's intended offline consumer operations after pruning;
5. repeat with `CI` set and unset to discriminate `AeneasMeta.precompileModules` behavior;
6. treat a native artifact as removable only after its consumer/facet is shown unnecessary, rather than because its extension looks auxiliary.

If Anneal changes `prune-lake-cache.py`, compare its deletion mapping against the pinned `Module` and `LeanLib` path/naming functions. A source-only check can establish that the mapping covers a file class; only an execution inventory can establish which such files the actual prepared build produced.
