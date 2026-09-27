# Cross-platform portability of Lean/Lake artifacts at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake does not provide one cross-platform portability guarantee for a prepared package tree. It has two materially different artifact classes.

Native machine-code products are explicitly platform-dependent in Lake's build model. Object builders mix `System.Platform.target` into their traces; shared-library builders do the same; static libraries are built from those platform-traced object jobs; and executables consume the same native object/library graph. Native filenames, linker flags, and runtime shared-library lookup also vary by operating system. These products should be rebuilt or supplied for the matching platform rather than copied across host/target triples.

Lean module outputs are subtler. Lake's `platformIndependent : Option Bool` controls how module setup participates in invalidation. With the default `none`, Lake propagates platform-sensitive library/plugin dependencies when they actually occur. `false` additionally forces the current platform into the module trace. `true` suppresses those platform-sensitive dependencies from the module trace. Lake explicitly warns that this is an unchecked assertion: configuration can lie, and Lake will not detect it.

That trace policy is not a proof that `.olean` or every member of a module `.ltar` is binary-portable across architectures or operating systems. The pinned Lean `.olean` implementation uses a native `size_t` in its header and a compacted Lean runtime object image; the existing exact-pin format report therefore deliberately makes no cross-architecture portability claim. A platform-neutral Lake key says that Lake has been told, or has inferred from its dependency graph, that a module need not be rebuilt for a platform change. It does not establish an external ABI theorem for the serialized bytes.

Lake also separates cache policy by platform. Normal remote-cache lookup/publication uses `System.Platform.target`; it drops the platform component only when the whole package is explicitly configured `platformIndependent = true`. Module output mappings likewise mark a module archive platform-independent only for explicit `true`, not for the default `none`. These safeguards reduce accidental cross-platform reuse, but they remain policy boundaries rather than proof that every retained artifact is portable.

The Anneal-selected Aeneas and Mathlib packages do not set `platformIndependent`; they therefore use Lake's default `none`. AeneasMeta can additionally enable `precompileModules` outside CI, producing native per-module shared libraries that are platform-dependent. Current Anneal packaging independently reinforces this boundary: it selects distinct Aeneas release assets, Rust toolchains, Lean archives, `leantar` binaries, and Mathlib-cache material for `x86_64-linux`, `aarch64-linux`, `x86_64-darwin`, and `aarch64-darwin`.

For Anneal, the safe default is therefore **platform-specific prepared state unless a narrower artifact class has explicit evidence for reuse**. Native `.o`/`.a`/`.so`/`.dylib`/`.dll`/executables are not cross-platform cache material. Pure Lean module artifacts may admit broader reuse, but the exact cross-platform boundary needs an execution probe before Anneal treats one platform's module archive as another platform's input.

## Applicability

The Lake and Lean findings apply to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, the source corresponding to Lean `v4.30.0-rc2` selected by current Anneal.

The package-configuration observations apply to:

- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`), whose Lean backend selects Mathlib `v4.30.0-rc2` and leaves `platformIndependent` unset; and
- `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`, whose root package likewise leaves `platformIndependent` unset.

The Anneal packaging observations apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

This report uses “platform” in Lake's concrete sense where possible: `System.Platform.target`, which the pinned Lean source documents as the LLVM target triple of the current Lean build. That identity is stronger than an OS name alone. It can distinguish architecture and ABI variants that share an operating system.

The report distinguishes three different propositions that should not be collapsed:

1. **Lake invalidation identity:** whether a platform change contributes to a target's build trace or remote-cache scope.
2. **Artifact-format compatibility:** whether bytes produced on one platform can be read or consumed on another.
3. **Anneal packaging support:** whether current Anneal deliberately supplies the matching toolchain and prepared assets for a host.

Evidence for one proposition does not establish the others.

## Findings

### Lake uses the Lean build's LLVM target triple as platform identity

`System.Platform.target` returns the LLVM target triple embedded when Lean itself was built. Lake's `platformTrace` hashes that string and documents the consequence directly: an artifact whose trace includes it is platform-dependent and will be rebuilt on another host platform.

This gives Lake a concrete architecture/OS/ABI discriminator rather than a generic “Linux versus macOS” bit. At the selected toolchain, examples include distinct x86-64 and AArch64 host triples.

Basis: **source** — `src/Init/System/Platform.lean`; `src/lake/Lake/Build/Common.lean`.

### Native objects, shared libraries, and executables are deliberately platform-dependent

Lake's native builders encode the boundary in the build graph rather than leaving it implicit.

`buildO` adds `platformTrace` before building an object file. `buildLeanO` adds both the exact Lean toolchain trace and `platformTrace` before invoking Lean's C compiler. Module C-to-object and bitcode-to-object facets use `buildLeanO`, so their native object outputs inherit the same platform dependency.

Shared-library builders also add `platformTrace`. Their command lines differ by platform: the external-library path uses macOS `-force_load` semantics but GNU-style `--whole-archive` elsewhere. Shared-library names use `.dll` on Windows, `.dylib` on macOS, and `.so` elsewhere; runtime lookup uses `PATH`, `DYLD_LIBRARY_PATH`, or `LD_LIBRARY_PATH` respectively.

Static-library construction does not need a second standalone platform token to be platform-sensitive: it consumes object jobs that already carry the platform trace. An executable similarly links platform-traced native object/library inputs through the current toolchain.

The module source contains an additional useful limit: the C-to-object and LLVM-bitcode-to-object paths still carry a `TODO` to add a target triplet for cross compilation. At this revision, these helpers are host-toolchain builds, not a general cross-compilation interface.

The operational rule is therefore straightforward: native objects, static/shared libraries, plugins, and executables are matched-platform state. A content hash can deduplicate identical bytes; it does not make a native binary portable to a different target triple.

Basis: **source** + **derived** — `Lake/Build/Common.lean`, `Lake/Build/Module.lean`, `Lake/Build/ExternLib.lean`, `Lake/Util/NativeLib.lean`.

### Module elaboration artifacts have a tri-state platform policy

Lean-module builds do not unconditionally add `platformTrace`. Instead, `Module.recFetchSetup` first computes two classes of dependency trace:

- a source/import/configuration trace; and
- a library trace derived from imported native libraries, package external libraries, configured dynamic libraries, and plugins.

It then applies the effective `platformIndependent` setting:

- `none`: include both dependency classes, so platform dependence propagates naturally if a consumed library/plugin job is platform-dependent;
- `some false`: include both dependency classes and explicitly add `platformTrace`, forcing re-elaboration after any platform change; and
- `some true`: include the ordinary dependency trace but omit the native-library/plugin trace and do not add an explicit platform trace.

The returned `ModuleSetup` still contains the concrete dynamic-library and plugin paths. `true` therefore does not remove those runtime inputs; it tells the trace model not to let those platform-sensitive inputs invalidate the module.

The upstream option documentation states the trust boundary plainly: there is no correctness check, so a configuration can lie and Lake will not catch it. `platformIndependent = true` is consequently an assertion by package configuration, not a discovered theorem about the produced artifacts.

Basis: **source** — `Lake/Build/Module.lean`; `Lake/Config/LeanConfig.lean`; `Lake/Config/LeanLib.lean`.

### The default `none` is “natural” dependence, not an assertion of portability

It is tempting to read an unset `platformIndependent` as “portable.” That is not what the source says.

With `none`, Lake does not force a platform token into every Lean module. If a module's effective dependencies are platform-neutral, its module trace can therefore remain unchanged across platforms. But if the setup depends on a platform-traced dynamic library or plugin, that platform dependence flows into the module trace.

This default is useful because pure Lean modules need not be invalidated merely because the host changes, while metaprogramming/native dependencies can still make a module platform-sensitive. It does **not** establish that every module artifact with a platform-neutral trace has been empirically demonstrated portable across every target triple.

This distinction matters for Anneal because both Aeneas and Mathlib use the default. Their source does not opt into the stronger `platformIndependent = true` assertion, nor does it force `false` globally.

Basis: **source** + **derived** — pinned Lake trace logic plus the Aeneas and Mathlib package configurations.

### A module `.ltar` contains module products, not the later native object/library layer

`Module.packLtar` packages the module trace and the Lean module-output family: `.olean`, optional server/private olean parts, `.ilean`, optional IR, generated C, and optional LLVM bitcode. It does not include the later native object, static-library, shared-library, or executable facets.

This split explains why Lake can sensibly discuss platform-independent module archives separately from native binaries. Generated C or LLVM bitcode is not itself the linked native binary that Lake later builds through platform-traced object helpers.

However, the archive's composition does not prove universal portability. Its `.olean` member still follows Lean's serialization compatibility rules, and generated IR/C/bitcode can have their own toolchain/target assumptions. Lake marks a root module archive's output mapping `platformIndependent` only when the effective module setting is explicitly `true`; `none` is classified as dependent at this output-map layer by `getD false`.

Basis: **source** — `Lake/Build/Module.lean`.

### Lake's `.olean` implementation does not justify a blanket cross-architecture claim

The existing exact-pin `.olean` format report establishes two details relevant here. The binary header includes native `size_t`, and the serialized payload is a compacted Lean runtime object image. The reader checks format markers and compatibility state, but core import does not carry a general cross-architecture portability contract.

Those facts are enough to reject an inference from “Lake did not add a platform token” to “these bytes are proven portable across architectures.” They are **not** enough to prove the opposite for every pair of 64-bit platforms. This investigation did not take an x86-64-produced `.olean` and import it on AArch64, or vice versa.

The durable conclusion is narrower: Lake's trace decision and Lean's binary-format compatibility are separate questions. Cross-architecture reuse of `.olean` must be supported by a specific format argument or execution evidence; it should not be inferred from `platformIndependent` alone.

Basis: **source** + **derived** — pinned Lean module serialization (`src/library/module.cpp`, `src/runtime/compact.cpp`) and the current `lean-olean-format-identity-v4-30-0-rc2` reference report.

### Lake's cache layers add additional platform fences

Lake's remote artifact-cache CLI has a package-level platform selector. By default it uses `CachePlatform.system`, which is `System.Platform.target`. `cachePlatform` replaces that platform with `none` only when the package is explicitly configured `platformIndependent = true`.

That means ordinary remote revision mappings for the default Aeneas/Mathlib configuration are selected per platform even when some individual pure-Lean module traces might happen to be platform-neutral. An explicit package-wide independence declaration removes this remote fence.

The root output-map path has a second distinction. `CacheMap` entries remember whether an output mapping is platform-independent, and writing a platform-independent map omits entries marked dependent. Module `.ltar` tracking marks an output independent only for explicit `platformIndependent = true`.

These are useful defense layers, but they should not be overread. The local cache's content-addressed artifact bytes and input-to-output mapping machinery are not, by themselves, an external portability proof. In particular, this report did not test one physical local cache directory shared between different operating systems or architectures.

Basis: **source** — `Lake/CLI/Main.lean`, `Lake/Config/Cache.lean`, `Lake/Build/Run.lean`, `Lake/Build/Module.lean`.

### The Anneal-selected Aeneas and Mathlib packages do not opt into platform independence

At `AeneasVerif/aeneas@ac9f1bc…`, the root Lean package is declared as `package «aeneas» {}`. Its ordinary `Aeneas` library uses defaults. `AeneasMeta` conditionally enables `precompileModules` when `CI` is absent, but neither the package nor those libraries sets `platformIndependent`.

The pinned Mathlib package at `5450b53e…` likewise declares `package mathlib where ...` without setting `platformIndependent`.

Both therefore inherit Lake's default `none`. Pure module traces can remain naturally platform-neutral when they have no native dependency, while native/plugin dependencies can propagate platform sensitivity. AeneasMeta's optional precompilation adds a separate native surface: per-module shared libraries are native machine code and follow Lake's platform-dependent native builders.

For a prepared Anneal tree, the distinction is important. “The Lean sources are the same” is insufficient to justify copying every `.lake` output across hosts. The actual retained set must distinguish module products from native precompile/library products.

Basis: **source** — Aeneas `backends/lean/lakefile.lean`; Mathlib `lakefile.lean`; pinned Lake defaults.

### Current Anneal packaging already treats toolchain/prepared assets as per-system inputs

Current `anneal/flake.nix` evaluates separately for the four supported Nix systems and maps each system to distinct upstream identities for Rust, Lean, Aeneas, and `leantar`. It also carries separate fixed-output hashes for those assets and for Mathlib-cache material.

The selected systems are:

- `x86_64-linux`;
- `aarch64-linux`;
- `x86_64-darwin`; and
- `aarch64-darwin`.

The Lean archive name itself distinguishes Linux x86-64, Linux AArch64, Darwin x86-64, and Darwin AArch64. Aeneas release assets likewise distinguish OS and architecture. This is independent evidence that Anneal's current packaging model does not expect one native toolchain/prepared artifact bundle to be universal.

This source fact does not prove that every Mathlib `.olean` differs by platform or could never be shared. It establishes the safer packaging invariant: current Anneal acquires and validates prepared inputs in a platform-specific derivation, leaving any cross-platform reuse to be justified at a narrower artifact layer.

Basis: **source** — current Anneal `anneal/flake.nix`; **derived** relation to the pinned Lake artifact classes.

### A useful Anneal portability policy is artifact-specific, not tree-wide

The source supports the following durable policy for prepared environments:

| Artifact class | Cross-platform default | Reason |
| --- | --- | --- |
| Lean source/config/manifest | re-evaluate separately from compiled outputs | path/topology and package identity rules govern these files, not native ABI |
| `.olean` / `.ilean` / module IR | do not assume; qualify by exact Lean/toolchain and evidence | Lake may use platform-neutral traces, but Lean binary compatibility is a separate question |
| generated C / bitcode | do not equate with native binary portability | these are inputs to a later platform-traced native compilation step |
| module `.ltar` | inherits member/configuration limits | archive can be labeled independent only under explicit policy; label is not a proof |
| `.o` | platform-specific | builder adds `platformTrace` |
| `.a` | platform-specific by dependency | built from platform-traced objects |
| `.so` / `.dylib` / `.dll` / plugins | platform-specific | platform trace, naming, linker, and loader semantics vary |
| executable | platform-specific | native object/library graph and current linker/toolchain |

This classification is **derived** from the pinned sources. It is intended to prevent a whole-tree cache or archive policy from granting the weakest artifact the portability of the strongest one.

## Boundaries

**No fresh cross-platform execution.** This investigation did not build the same module on x86-64 and AArch64, transfer `.olean`/`.ltar` files between hosts, share a cache between hosts, or execute a native artifact on a different platform. Claims about Lake's trace and cache policy are source facts; actual cross-host module-byte compatibility remains an execution gap.

**No blanket claim that `.olean` is non-portable.** The pinned implementation gives no basis for a universal cross-architecture guarantee, but this run did not prove that all relevant platform pairs are incompatible. In particular, two 64-bit hosts may share representation properties that a 32/64-bit comparison does not.

**`platformIndependent = true` is not validation.** Lake's own documentation says the option can be wrong without detection. A package setting it incorrectly can suppress dependency/platform invalidation that would otherwise occur.

**The default `none` is not equivalent to `false`.** `false` forces platform invalidation even when the module has no platform-dependent library/plugin inputs. `none` lets actual dependencies decide. Treating both as “platform-dependent” loses a meaningful Lake behavior.

**Remote cache partitioning and local cache reuse are different.** Normal remote revision lookup is platform-scoped for packages not explicitly independent. This report did not establish that one local cache directory is safe for simultaneous or sequential use by different host triples.

**Generated C and bitcode are not classified as universally portable.** They are not native object files, but their portability can depend on generated code, compiler options, LLVM/toolchain assumptions, and target-specific primitives. This report only establishes that Lake's later object compilation is explicitly platform-traced.

**Custom facets can add other rules.** The report covers Lake's built-in module/native/artifact-cache paths. A package can introduce custom targets, external builders, plugins, or files with different portability constraints.

**Anneal's per-system Nix graph is packaging evidence, not a minimality theorem.** The fact that Anneal currently downloads separate platform assets does not prove every byte in those assets must be distinct. It establishes the current supported construction and a conservative boundary for reuse.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27. `source-map.json` preserves the exact source/blob index; `portability-matrix.json` preserves the artifact-class synthesis.

### Lean and Lake

All paths below are from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/Init/System/Platform.lean`, blob `cbb97369634eeb1faff3621e4dbae7e6af1ccb25`: `System.Platform.target` and its LLVM-target-triple contract.
- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: `platformTrace`, object/shared/executable build helpers, and artifact-cache wrapper.
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: tri-state module setup traces, `.ltar` contents, module output tracking, and native object facets.
- `src/lake/Lake/Config/LeanConfig.lean`, blob `9fdd5a656c4316ee6beb45bdc9a1be4dd8d5d42a`: normative source documentation for `platformIndependent`, including the explicit “configuration can lie” limit.
- `src/lake/Lake/Config/LeanLib.lean`, blob `077efb6c244fd53bab5dead6c850d40161c96e7f`: package/library inheritance of `platformIndependent` and `precompileModules`.
- `src/lake/Lake/Config/Module.lean`, blob `f8b938e16fe53ada616364033b8d8353baa733ee`: module dynamic-library naming and effective configuration.
- `src/lake/Lake/Util/NativeLib.lean`, blob `5ed2cdaafed37f8b28524b09a55835f1f4ce69d6`: OS-specific library extensions/names and runtime search environment variables.
- `src/lake/Lake/Build/ExternLib.lean`, blob `9ed94d229d3ca5d41173941e157d31f9b9f6b814`: platform-traced shared external libraries and platform-specific linker behavior.
- `src/lake/Lake/Config/PackageConfig.lean`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`: platform-named default build archives and package native/precompile configuration.
- `src/lake/Lake/CLI/Main.lean`, blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`: remote cache platform selection and the package-wide independence override.
- `src/lake/Lake/Config/Cache.lean`, blob `607e6b92108f30e0a57d0de682f7faa283d7d470`: cache entry platform-independence flags and `CachePlatform.system`.
- `src/lake/Lake/Build/Run.lean`, blob `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`: build-context Lean identity and output-map filtering.
- `src/library/module.cpp`, blob `97a53f87b06595049cdfe6016ec2c66fd40748b6`: `.olean` native header fields and module reader/writer.
- `src/runtime/compact.cpp`, blob `c8bf24aa8206bc99cddde2fda2e4e2212b8a75b0`: compacted Lean runtime object representation used by module serialization.

The current reference reports `lean-package-native-artifacts-v4-30-0-rc2`, `lean-olean-format-identity-v4-30-0-rc2`, `lake-artifact-cache-key-semantics-v4-30-0-rc2`, and `lake-readonly-relocation-offline-concurrency-v4-30-0-rc2` were used as durable context. This report narrows their separate artifact, format, cache-key, and relocation facts into the cross-platform portability boundary; it does not replace them.

### Aeneas and Mathlib

- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `backends/lean/lakefile.lean`, blob `c32062866e2f88d2eb768b904745e7104edddb0d`: root package/default libraries; no `platformIndependent` override; `AeneasMeta.precompileModules := notCI`.
- Same revision, `backends/lean/lake-manifest.json`, blob `1a5af703163d8b39f4311aafe22ae171788179ee`: selected Mathlib revision `5450b53e…` and locked dependency graph.
- `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`, `lakefile.lean`, blob `2615d72c0aa5e414234eac5f7ade10f4f3890916`: root `package mathlib` and libraries; no `platformIndependent` override.
- Same Mathlib revision, `lake-manifest.json`, blob `86b358344ea45a46d99dc19ac861011583e6d6e5`: locked dependency graph.

### Anneal

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: four supported systems; distinct Aeneas/Rust/Lean/`leantar` names and fixed-output hashes; per-system Mathlib-cache download hashes.
- Current reference report `anneal-host-platform-matrix-main-41f5b37`: host-level packaging matrix and the distinction between host support and other Rust compilation targets.

All primary claims in this report use **source** evidence; classifications and Anneal policy implications are labeled or framed as **derived**. No fresh **execution** evidence was acquired.

## Revalidation

For a new Lean/Lake revision, the cheapest reliable source check is narrow:

1. Inspect `System.Platform.target` and `Lake.Build.Common.platformTrace`. Confirm what platform identity is hashed.
2. Inspect `buildO`, `buildLeanO`, shared-library, static-library, and executable helpers. Record which native outputs still carry platform traces and whether cross-compilation target arguments have been added.
3. Inspect `Module.recFetchSetup` and `LeanConfig.platformIndependent`. Preserve the distinction among `none`, `false`, and `true`; do not infer semantics from the option name alone.
4. Inspect `.ltar` construction and root output tracking. Record exactly which artifacts are packed and how platform independence is attached to cache mappings.
5. Inspect `CachePlatform`, cache CLI selection, and output-map filtering. Distinguish package-level remote scoping from individual target input hashes.
6. Inspect Lean's `.olean` header/reader and compact-object representation if any claim depends on cross-architecture module reuse.
7. Re-read the selected Aeneas and Mathlib package configurations for explicit `platformIndependent`, native plugins, external libraries, or `precompileModules` changes.
8. Re-read current Anneal packaging before assuming the same host/toolchain matrix.

A capable execution surface can settle the unresolved module-artifact boundary with a small matrix rather than a whole Anneal rebuild. Use one pure module and one module with a native/plugin dependency. For each of x86-64 Linux, AArch64 Linux, x86-64 macOS, and AArch64 macOS where runners are available:

1. build with the exact Lean/Lake revision and record `System.Platform.target`;
2. preserve `.olean`, `.ilean`, `.ltar`, generated C/bitcode, trace files, input/output mapping, and SHA-256 values;
3. attempt to consume each source platform's module artifacts on every other platform without rebuilding, recording whether Lean imports them and whether Lake considers them up to date;
4. repeat under `platformIndependent = none`, `false`, and `true`;
5. separately confirm that native objects/libraries/executables are rebuilt or rejected rather than silently reused;
6. test normal remote-cache lookup to verify the platform component in service keys and compare that with any deliberately platform-independent package; and
7. preserve the exact toolchain/archive identities so a success is not generalized beyond the tested pair.

The most important discriminator is not byte equality. It is whether the producer artifact is accepted by the consumer toolchain and whether doing so preserves the semantics Lake's cache identity claims. One successful same-OS transfer does not establish portability across architectures, ABIs, or operating systems.