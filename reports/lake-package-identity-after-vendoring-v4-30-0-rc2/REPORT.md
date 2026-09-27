# Lake package identity after vendoring

## Summary

At Lean/Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), changing a dependency from a Git source to a vendored path does **not by itself define a new Lake package identity**. Lake separates the dependency's source from the names it uses to identify the loaded package. A source-preserving vendoring transformation can therefore keep the same dependency-facing identity while replacing Git materialization with a path to copied files.

That statement has important limits. Lake does not attach a content digest or repository revision to a path dependency, and its internal package key includes the package's workspace index. Vendoring is identity-preserving only if the transformation preserves the dependency name, package configuration semantics, and effective workspace position. It does not establish that the bytes are the same, that old build products remain valid, or that the vendored tree is immutable.

This distinction matters directly to Anneal. At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Anneal's archive test constructs a generated Lake workspace with `require aeneas from "<path>"`, writes a path manifest entry named `aeneas`, and rebases Aeneas's transitive path entries into that workspace while retaining their other manifest fields. That is the right *shape* for preserving Lake's logical dependency names while changing where their files live. It still relies on Anneal's archive construction to preserve the actual package contents and dependency graph.

## Applicability

This report is pinned to:

- Lean/Lake `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`;
- Anneal V2 at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

"Vendoring" here means copying or unpacking dependency source trees into an Anneal-controlled tree and referring to those trees through Lake path dependencies or path manifest entries. It does not mean any particular package-manager feature named `vendor`, because Lake's relevant pinned mechanisms are ordinary dependency sources, manifest entries, package loading, and workspace construction.

The report distinguishes four identities that are easy to conflate:

1. **dependency source identity** — Git URL/revision versus filesystem path;
2. **assigned package name** — the dependency name by which the workspace resolves the package;
3. **internal workspace key** — the assigned name plus workspace index, used by Lake build/configuration machinery;
4. **author-declared package name** — the name written in the package's own configuration, retained separately and used by some compilation/linkage machinery.

Those identities overlap in common cases, but the pinned implementation keeps them distinct.

## Findings

### 1. Dependency source and package name are separate fields

Lake represents a dependency source independently from the dependency's package name. `DependencySrc` is either a path or Git source, while `Dependency.name` is a separate field. The source comment says `name` is the package name and must be unique across the dependency graph; `src?` says where Lake should materialize it.

- [`Lake/Config/Dependency.lean` lines 26-64](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Dependency.lean#L26-L64)

This separation is the basic reason a Git-to-path vendoring transformation can preserve package identity: changing `src?` does not mechanically require changing `name`.

It is also the first limit. A path source has no revision or content identity. A vendored path is "the package named N found at this path", not "the package whose source digest is H".

### 2. Loaded packages carry both assigned and author-declared names

A loaded `Package` records several distinct fields:

- `wsIdx`, the package's index in the workspace;
- `baseName`, the assigned package name;
- `keyName`, the package identifier used in target keys and configuration types;
- `origName`, the package name specified by the package itself;
- `dir` and `relDir`, its physical location;
- `scope` and `remoteUrl`, source/provenance metadata.

The structure defines `keyName` from `baseName.num wsIdx`, hashes packages by `keyName`, and compares package equality by `wsIdx`.

- [`Lake/Config/Package.lean` lines 24-93](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Package.lean#L24-L93)

The physical directory is therefore not the package's equality or build-key identity. Moving the same logical package into a vendored tree changes `dir`/`relDir`, but need not change `baseName`, `origName`, or `keyName`.

The converse is also important: a filesystem copy alone is not enough to preserve Lake identity. If the dependency is loaded under a different assigned name or at a different workspace index, the internal key changes even if the copied bytes are identical.

### 3. The dependency declaration supplies the assigned name when Lake loads a dependency

`LoadConfig` carries both `pkgIdx` and `pkgName`. The latter is explicitly "the assigned name of the package"; if it is anonymous, Lake falls back to the package's own name.

- [`Lake/Load/Config.lean` lines 20-45](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Config.lean#L20-L45)

For a Lean configuration, Lake elaborates the file with that assigned `pkgName` and `pkgIdx` installed in `nameExt`. The `package` DSL expands its type-level package name as `Name.num <assigned-or-original-name> <index>`, while separately retaining the author's original name.

- [`Lake/Load/Lean/Elab.lean` lines 57-89](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L57-L89)
- [`Lake/DSL/Package.lean` lines 21-46](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/DSL/Package.lean#L21-L46)

`loadLeanConfig` then reconstructs the runtime `Package`: `baseName` is the assigned name when one was supplied, while `origName` comes from the package declaration and `keyName` comes from the elaborated declaration.

- [`Lake/Load/Lean.lean` lines 24-42](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean.lean#L24-L42)

The TOML loader implements the same distinction directly: it reads `origName` from the TOML `name`, chooses `baseName` from the assigned name when present, and computes `keyName := baseName.num wsIdx`.

- [`Lake/Load/Toml.lean` lines 470-499](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Toml.lean#L470-L499)

So, for both configuration formats, a dependency can be relocated without making its physical path part of the package key. Preserving the dependency's assigned name and workspace position preserves the key even though the source path changes.

### 4. Lake's internal package identity is load-order-sensitive

The package key is not just a stable textual name. It includes `wsIdx`. Workspace construction stores packages in an array and indexes `packageMap` by `pkg.keyName`; lookup by assigned `baseName` is a separate first-match operation.

- [`Lake/Config/Workspace.lean` lines 170-205](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Workspace.lean#L170-L205)

This means a vendoring transformation that merely substitutes sources in an otherwise identical resolved graph can preserve internal keys. A transformation that changes dependency traversal, adds/removes packages, or otherwise changes a package's workspace index can change `keyName` even when `baseName` is unchanged.

That is not only a type-system implementation detail. Lake build keys use `keyName` for packages, package targets, modules, and configuration targets.

- [`Lake/Build/Info.lean` lines 31-40](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Info.lean#L31-L40)
- [`Lake/Build/Infos.lean` lines 24-33](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Infos.lean#L24-L33)

Therefore "same package name" is weaker than "same internal build identity". A robust vendoring transformation should preserve not only names but the effective resolved package order whenever reuse of keyed build state matters.

### 5. Resolution deduplicates by package name, not by source URL or path

The dependency resolver checks whether a package with the same `baseName` is already in the workspace before adding another dependency. It also rejects self-dependencies by name. Manifest entries are collected by package name, and the written root manifest locates entries by each loaded package's `baseName`.

- [`Lake/Load/Resolve.lean` lines 160-230](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L160-L230)
- [`Lake/Load/Resolve.lean` lines 430-470](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L430-L470)

Thus Git URL/revision and path are not namespace dimensions. Two sources for the same dependency name do not automatically become two independently addressable packages. Source replacement is interpreted inside the same name-based dependency graph.

For vendoring, this is useful: replacing the source of package `aeneas` with a path entry named `aeneas` fits Lake's graph model. It is also a constraint: renaming vendored packages to encode provenance changes the graph identity and can alter precedence/resolution.

### 6. Git and path materialization produce the same package-facing handoff, but different provenance guarantees

The materializer turns both dependency source kinds into a `MaterializedDep` that the loader consumes. A path dependency records a path entry; a Git dependency records Git provenance and an exact resolved revision. Both continue under the dependency's package `name`.

- [`Lake/Load/Materialize.lean` lines 145-185](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L145-L185)
- [`Lake/Load/Materialize.lean` lines 220-260](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L220-L260)

Changing Git to path can therefore preserve the package-facing name while discarding Git-specific identity. After vendoring, the manifest no longer proves which commit produced the files unless the vendoring layer records that fact separately.

This distinction is central for Anneal: Lake can keep treating a dependency as the same logical package, but the surrounding toolchain/archive machinery must carry the provenance and content-integrity guarantee that the path dependency itself lacks.

### 7. `origName` matters independently of the assigned workspace name

`Package.id?` is not based on `baseName` or `keyName`. For non-bootstrap packages it returns `origName` as the package identifier passed to Lean to disambiguate native symbols.

- [`Lake/Config/Package.lean` lines 149-160](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Package.lean#L149-L160)

That identifier feeds module/library initialization names and is included in module build traces.

- [`Lake/Config/LeanLib.lean` lines 58-69](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/LeanLib.lean#L58-L69)
- [`Lake/Config/Module.lean` lines 151-163](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Module.lean#L151-L163)
- [`Lake/Build/Module.lean` lines 884-896](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L884-L896)

A vendoring transformation should therefore preserve the package's own configuration, including its original declared name. Keeping only the dependency alias/assigned name is insufficient to claim equivalent native-symbol identity.

For ordinary vendoring that copies the package configuration unchanged, this follows naturally. Rewriting the package declaration itself is materially different from changing only the source location.

### 8. Configuration caches also bind to the assigned name and workspace index

Lean-format Lake configurations are cached under a directory containing the assigned package name. Their trace records `idx` and `name`, and Lake accepts the cached configuration only when both match the current load configuration (along with source hash, platform, and Lean hash).

- [`Lake/Load/Lean/Elab.lean` lines 165-187](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L165-L187)
- [`Lake/Load/Lean/Elab.lean` lines 245-279](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L245-L279)

So a move from Git checkout to vendored path is not itself what changes this configuration identity. Changing the assigned package name or workspace index does.

The physical package path can still affect configuration behavior in other ways, including path-dependent configuration code and where caches live. This finding only identifies the explicit name/index identity check in the pinned configuration-cache path.

### 9. Anneal's current archive workspace preserves names while rebasing paths

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Anneal's archive-reuse test generates a Lake workspace whose configuration says:

`require aeneas from "<archive path>"`

and names the root package `anneal_verification`.

- [`anneal/src/main.rs` lines 143-175](https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/src/main.rs#L143-L175)

It then constructs a root `lake-manifest.json` with a path entry whose name remains `aeneas`. For Aeneas's transitive manifest entries, it requires that each source is already a path dependency, canonicalizes the source path, rewrites only the `dir` to be relative to the generated workspace, sets `inherited := true`, and retains the rest of each entry.

- [`anneal/src/main.rs` lines 220-287](https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/src/main.rs#L220-L287)

This is an identity-preserving pattern in Lake's model: keep the package names and package contents/configuration, change the filesystem relation used to reach them, and preserve the transitive entry metadata apart from the fields that necessarily describe their new embedding.

It also explains why Anneal should treat the archive construction—not Lake path dependency semantics—as the provenance boundary. The archive code is responsible for choosing the actual Aeneas tree and its transitive trees. Lake subsequently sees ordinary named path packages.

### 10. A practical identity-preserving vendoring invariant is stronger than "the build still works"

For an Anneal toolchain that converts a pinned Git dependency graph into a vendored/path graph, the useful invariant is:

> For every package intended to remain the same logical dependency, preserve the dependency `name`, the package's author-declared configuration/name, and the resolved graph position; replace only the source/materialization path, while independently preserving source provenance and bytes.

The parts have different purposes:

- **same dependency `name`** preserves name-based resolution and assigned `baseName`;
- **same resolved graph position** preserves `wsIdx` and therefore `keyName`;
- **same package configuration/original name** preserves configuration typing and `Package.id?`;
- **same bytes/provenance**, established outside Lake's path source, preserves the semantic artifact being depended on;
- **updated path metadata** tells Lake where the vendored copy now lives.

If only the first condition holds, the workspace can still resolve successfully while internal build keys, native-symbol identity, configuration behavior, or package semantics differ.

## Boundaries

This report does **not** claim that a Git dependency and a vendored path dependency are semantically equivalent merely because Lake loads both under the same name. Lake path dependencies do not carry the Git revision/content identity that Git manifest entries carry.

It does **not** claim that package `keyName` is globally stable. The pinned implementation includes `wsIdx`, so changes in effective workspace order can change internal keys.

It does **not** claim that relocating a package leaves all build artifacts reusable. Package directories, generated configuration paths, traces, compiler arguments, and other path-sensitive state are separate subjects in this reference corpus.

It does **not** claim that all package code is insensitive to `scope` or `remoteUrl`. Those fields are retained on `Package` and can be consumed by higher-level behaviors. Vendoring should preserve metadata unless the transformation intentionally changes its semantics.

It does **not** claim that copying the package configuration unchanged is sufficient to preserve the source bytes. Archive/Nix hashes, exact release inputs, or another external provenance mechanism are still required.

Finally, the Anneal evidence is a checked-in test/construction path at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. It establishes the intended and mechanically encoded manifest transformation, not a fresh execution of that test in this report.

## Evidence

Primary pinned Lake sources:

- `src/lake/Lake/Config/Dependency.lean`, blob `a06fad9cd1da3df2ab1b2c6aaaba38535e64a0f1`
- `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`
- `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`
- `src/lake/Lake/DSL/Package.lean`, blob `91169e3d688711a5caf24491daa4f3f6d53d740d`
- `src/lake/Lake/Load/Config.lean`, blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`
- `src/lake/Lake/Load/Lean.lean`, blob `b38ee619b42d8293fc9e4ffb4b8e2f4b1508c1e7`
- `src/lake/Lake/Load/Lean/Elab.lean`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`
- `src/lake/Lake/Load/Toml.lean`, blob `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`
- `src/lake/Lake/Load/Manifest.lean`, blob `760eb81419762fb0ab11393e93082930645e2b6d`
- `src/lake/Lake/Load/Materialize.lean`, blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`
- `src/lake/Lake/Load/Resolve.lean`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`
- `src/lake/Lake/Build/Info.lean`, blob `6c723e06c58ce54b0aff43217847b45ed364434f`
- `src/lake/Lake/Build/Infos.lean`, blob `e7761bb5b29ef84a187e64c6c76b4274b5111261`
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`
- `src/lake/Lake/Config/LeanLib.lean`, blob `077efb6c244fd53bab5dead6c850d40161c96e7f`
- `src/lake/Lake/Config/Module.lean`, blob `f8b938e16fe53ada616364033b8d8353baa733ee`

Anneal source:

- `anneal/src/main.rs` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, blob `b947700606677ea89c7a205f3ffcc75493508f63`

No conclusions here depend on adjacent Lean versions. Search results from another branch were used only to locate files/symbols; every substantive Lake conclusion above was checked against the pinned `v4.30.0-rc2` revision.

## Revalidation

When Anneal changes its vendoring/archive strategy or Lean/Lake pin, revalidate in this order:

1. Inspect `Dependency`, `Package`, and `LoadConfig`. Confirm that dependency source, assigned package name, original package name, workspace index, and physical directories remain distinct.
2. Inspect both Lean and TOML package loaders. Confirm how `baseName`, `origName`, and `keyName` are derived.
3. Inspect dependency resolution. Confirm the graph's deduplication key and the order in which package indices are assigned.
4. Inspect `BuildKey` definitions and any package identifier passed to Lean/native compilation. Confirm whether `keyName` and `origName` still affect build and native-symbol identity.
5. Inspect manifest materialization. Confirm what provenance a Git entry records and what a path entry loses.
6. Inspect Anneal's archive/workspace construction. Verify that name fields and package configurations are preserved while only path/source fields are rewritten.
7. If equivalence of already-built artifacts matters, run a separate exact-pin relocation/cache experiment. This source report does not establish artifact-byte or trace equivalence across a Git-to-path transformation.

A future automated vendoring verifier should compare the pre- and post-vendoring resolved graphs at minimum by assigned package name, original package name, workspace index/key, and a separately authenticated content identity. Comparing only paths, or only package names, is too weak.