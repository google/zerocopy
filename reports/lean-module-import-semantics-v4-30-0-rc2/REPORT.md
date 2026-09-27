# Lean module and import semantics at v4.30.0-rc2

## Summary

At Lean `v4.30.0-rc2`, an `import` names a Lean **module**, not a source file. Lean resolves that module name through the active search path to compiled module data, then reconstructs the transitive import closure from the import records stored inside those compiled modules.

That distinction is central for generated Lean projects. The source header determines the **direct** imports of the file being elaborated, but the rest of the dependency graph comes from the imported artifacts themselves. A stale or differently resolved `.olean` can therefore change the environment even when the current source file's `import` lines are unchanged.

Lean also has two different import regimes at this revision:

- an ordinary file without the `module` header uses the legacy/full-import behavior; and
- a file with the `module` header participates in the newer module system, where `public`, `meta`, and `all` import modifiers control which public/private data and which IR phases flow through the dependency graph.

For module-system files, the loader computes a least fixed point over the import DAG. A module can be reached along several paths with different modifiers, and the loader upgrades its effective import level as stronger paths are discovered. The final environment records every direct and transitive imported module at most once, together with its effective import properties.

For Anneal, "the Lean environment" is therefore not determined by source text alone. It depends on the direct header, module-system mode, module-name-to-artifact resolution, the exact imported artifacts and their serialized imports, import modifiers, and imported environment-extension state. Lake decides which artifacts are built or supplied; Lean's import machinery consumes them and constructs the semantic environment.

No fresh Lean or Lake execution was performed. This report establishes the pinned source-level import contract and uses checked-in module-system tests as preserved evidence of intended behavior.

Basis: source + checked-in tests + derived.

## Applicability

This report covers `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, identified by the Anneal toolchain as Lean `v4.30.0-rc2`.

It focuses on:

- parsing a file header into `Lean.Import` records;
- resolving module names to compiled artifacts;
- reconstructing direct and transitive module dependencies;
- the legacy/non-`module` import regime;
- the `module` system's `public`, `meta`, and `all` modifiers;
- the imported constants and persistent environment-extension state that form the elaboration environment.

This report deliberately stops before the byte-level `.olean` representation, `.ilean` contents, Lake trace/hash invalidation, and the exact set of source/configuration changes that force `.olean` rebuilding. Those are separate inventory items. It also does not replace the existing Lake reports: Lake's build graph and `setup-file` contract determine which dependency artifacts are available, while the machinery here determines how Lean consumes those artifacts once supplied.

The `module` system is materially different from ordinary historical Lean import behavior. Claims below say explicitly which regime they apply to.

## Findings

### A source header becomes an array of structured imports

`Lean.Elab.HeaderSyntax.imports` converts the parsed module header into `Lean.Import` values. Each import carries four pieces of information:

- `module : Name`;
- `importAll : Bool`;
- `isExported : Bool`; and
- `isMeta : Bool`.

`Lean.Setup` documents those flags directly:

- `importAll` means `import all`, exposing all data saved by the imported module;
- `isExported` controls whether the import itself is active when the current module is later imported; and
- `isMeta` requests IR for definitions reachable at elaboration time.

A normal source file also gets implicit `Init` dependencies. Unless the header contains `prelude`, `HeaderSyntax.imports` prepends two `Init` imports: one ordinary import and one `meta` import.

The parser rejects `public import`, `meta import`, and `import all` outside a `module` file. For a non-`module` file, explicit imports are represented as exported imports regardless of a nonexistent `public` modifier.

This makes the parsed header a compact direct-dependency description. It is not yet the transitive dependency graph.

Basis: source.

### Module names resolve through the search path to compiled artifacts

Lean's import identity begins with a `Name`. `Lean.Util.Path` documents the mapping explicitly: importing `A.B.C` searches `LEAN_PATH` and resolves to `A/B/C.olean` under the first matching package root; importing `A` resolves to `A.olean`.

`findOLean` reads Lean's initialized search path and returns the matching `.olean` path. The source-file path is not stored in the `Import` record and is not consulted by `importModules` when loading dependencies unless a caller separately supplies artifact paths.

Two consequences follow.

First, the same module name can resolve to different compiled artifacts under different search paths. Module name alone is not a globally sufficient content identity.

Second, normal semantic imports consume `.olean` data rather than reparsing the dependency's current `.lean` source. Source changes become visible downstream only after the module artifact selected by the import environment changes accordingly.

Lake can pass explicit `ImportArtifacts` instead of relying on the global search path. That changes the artifact-selection mechanism, not the import's semantic module name.

Basis: source + derived.

### Imported artifacts carry the next edges of the dependency graph

`ModuleData`, the core data loaded from `.olean` files, contains the imported module's own `imports : Array Import`.

`importModulesCore` begins from the current file's direct imports. When it loads a module, it reads that module's `ModuleData` and recursively follows `mod.imports`. The transitive graph is therefore reconstructed from the serialized headers of the compiled dependencies, not from their source files.

This is an important cache and reproducibility boundary. If a dependency's source header changes but its selected `.olean` has not changed, downstream import reconstruction still sees the imports serialized in the old artifact. Conversely, replacing an `.olean` can alter the downstream environment even if the importing source file is byte-identical.

Basis: source + derived.

### The final environment records direct imports separately from the effective closure

`EnvironmentHeader` keeps both views:

- `imports` is the array of direct imports of the current file; and
- `modules` is the direct-and-transitive imported module closure using `EffectiveImport`.

The source states that each module appears in `modules` at most once. Its array index is the module's `ModuleIdx`, and `EnvironmentHeader.moduleNames` exposes the corresponding ordered names.

The loader maintains a `moduleNameMap` while traversing the graph. If a module is encountered again, it does not append a duplicate logical module. Instead, it combines the newly required flags with the previous requirements and, if the requirement became stronger, revisits that module's transitive closure.

The resulting environment therefore has a canonical per-load module entry for each reached module, even when the source graph contains diamonds or the same module is imported with different modifiers along different paths.

Basis: source.

### Ordinary files import the full reachable environment

When the file does **not** begin with `module`, `processHeaderCore` calls `importModules` at the `.private` level.

`importModulesCore` documents the consequence: when the root does not participate in the module system, it imports all transitively referenced modules and ignores module-system visibility annotations along the way.

This is the behavior most existing Lean code historically relies on. A plain `import Foo` makes the reachable compiled environment available without the public/private export filtering introduced by the new module system.

The parser correspondingly rejects `public`, `meta`, and `all` qualifiers in a non-`module` file because those qualifiers have meaning only inside the module system.

Basis: source.

### `module` files compute import visibility as a fixed point over the DAG

When the header contains `module`, `processHeaderCore` chooses `.exported` import level for normal batch elaboration and `.server` when elaborating in server mode.

For this regime, `importModulesCore` gives an unusually explicit specification in its source comment. Each reached module can have one of five effective data-import levels:

- **all** — public data in public scope and private data in private scope;
- **public** — public data in public scope;
- **privateAll** — public and private data in private scope;
- **private** — public data in private scope; or
- **none** — no `.olean` data imported.

The loader computes the least fixed point required by the graph. In particular:

- the root starts at `all`;
- `import all` propagates the need for private data when the importing module has private-all access;
- `public import` propagates public visibility through the public side of the graph;
- an ordinary import reached privately remains private; and
- repeated paths can strengthen the effective level, causing the loader to revisit the dependency's own imports.

This is not a simple "walk each direct import once" model. The meaning of an imported module can be strengthened by another path through the DAG.

Basis: source.

### `public import` and private import control whether dependency declarations can escape

The checked-in module tests illustrate the source rules.

`Module.PrivateImported` uses an ordinary `import Module.Basic`. It can use imported declarations in its private implementation, but attempts to place those declarations into public definitions fail with diagnostics recommending `public import Module.Basic`.

`Module.Imported` uses `public import Module.Basic`. Public declarations from `Basic` are available in its exported context, but ordinary definitions are imported without their bodies unless the producing module explicitly exposes them.

This distinction matters for generated Anneal modules. A dependency that is sufficient to elaborate a private proof helper may still be insufficient for a declaration that Anneal intends to export from the generated module. The correct import qualifier depends on whether imported names must remain available to downstream consumers of that module.

Basis: checked-in tests + source.

### `import all` brings private implementation data into the current private scope

The `all` modifier is stronger than an ordinary import, but its private data does not automatically become publicly exportable.

`Module.ImportedAll` combines `public import Module.Basic` with `import all Module.Basic`. The checked-in assertions show that implementation details such as theorem bodies and private equational theorems become accessible inside the current module. The same test also shows that those private details cannot simply be smuggled into public declarations.

The parser prohibits combining `public` and `all` on one import directive and recommends two separate imports when both public API visibility and private implementation access are needed. The fixed-point loader then merges the requirements for the repeated module.

That is a concrete example of why repeated module names are not semantically redundant: separate paths/directives can contribute different parts of the final effective import level.

Basis: source + checked-in tests.

### `meta import` changes phase availability, not ordinary declaration visibility by itself

The `isMeta` flag controls IR availability for compile-time/elaboration execution.

`importModulesCore` tracks whether IR is needed transitively. Its rules deliberately distinguish:

- `A meta import B; B import C`, where compile-time IR need propagates through `C`; from
- `A import B; B meta import C`, where the meta requirement inside `B` does not automatically become a compile-time requirement of `A`.

The resulting `EffectiveImport` records `IRPhases` as runtime, comptime, or both.

The checked-in `Module.MetaImported` test shows the other half of the boundary: a declaration reached through `meta import` is not thereby available to an ordinary non-meta definition, and a public meta definition still needs the appropriate public import visibility.

For Anneal, "the theorem/declaration is present" and "its implementation IR is available for elaboration-time execution" are separate properties.

Basis: source + checked-in tests.

### Importing merges constants and persistent environment extensions

Loading module data is not only a constant-table operation.

`ModuleData` contains constants plus serialized entries for persistent environment extensions. `finalizeImport` builds the private/public constant maps, installs imported extension entries, and—when `loadExts` is enabled—initializes the persistent extensions from imported data.

`processHeaderCore`, the ordinary elaboration path, calls `importModules` with `loadExts := true`.

This matters because syntax, attributes, tactics, instances, simp sets, and other elaboration behavior can depend on environment extensions even when the relevant constants themselves are present. `importModules` explicitly warns that an environment whose extensions were not loaded can expose the constant map while still being unsuitable for many `CoreM` operations.

A reproducible generated environment therefore needs the imported extension state as well as the declarations.

Basis: source + derived.

### Conflicting declaration identities are detected during environment construction

`finalizeImport` merges constants from imported modules by name. If two modules contribute incompatible information for the same declaration name, the import fails rather than silently selecting one.

There is a narrow subsumption rule for theorem/axiom representations, motivated by proof irrelevance and module-system theorem export. Outside that allowed relationship, `throwAlreadyImported` reports which imported modules provided the conflicting declaration.

The checked-in `Module.ConflictingImported` test exists specifically to ensure conflicting definitions cannot be imported merely because weakened axiom representations look superficially compatible.

Thus the module closure is not a "last import wins" namespace. It must form a coherent environment.

Basis: source + checked-in tests.

### Lean import semantics and Lake dependency semantics are adjacent layers

The existing Lake reports cover workspace/build state and `setup-file`: Lake determines module ownership, dependency artifacts, freshness, and the file-specific artifact set supplied to the server.

The Lean machinery in this report starts at the next boundary. Given direct `Import` records and either search-path lookup or explicit `ImportArtifacts`, Lean:

1. loads the corresponding compiled module data;
2. follows the imports serialized in those modules;
3. computes effective visibility/phase requirements;
4. merges constants and environment-extension entries; and
5. returns the environment in which the current file elaborates.

Keeping these layers separate avoids a common category error. A Lake build graph edge tells you what artifact should be built; a Lean import edge tells you what compiled module environment is semantically incorporated. They normally agree through Lake's integration, but they are not the same data structure or protocol.

Basis: source + existing corpus context + derived.

### Anneal should identify generated-project dependencies by more than import text

For an Anneal-generated Lean file, the direct `import` header is necessary but insufficient as a durable dependency identity.

The semantic environment also depends on:

- whether the file uses `module`;
- `public`, `meta`, and `all` qualifiers;
- implicit `Init` imports unless `prelude` is present;
- the module search path or explicit artifact map;
- the exact `.olean` parts selected for each module;
- each imported artifact's own serialized imports;
- effective fixed-point visibility/phase requirements; and
- imported persistent environment-extension state.

If Anneal caches proof results or generated environments, it should not infer semantic equivalence merely because two files have identical direct import text. At minimum, the dependency identity must be tied to the actual resolved artifact graph or to a stronger reproducible build identity that determines that graph.

This report does not prescribe the final cache key. It establishes why source header equality alone is too weak.

Basis: source + derived.

## Boundaries

**No fresh execution.** The report did not run Lean, compile module fixtures, or mutate an Anneal workspace. Checked-in tests are preserved source evidence, not fresh runtime evidence.

**No `.olean` byte-format claim.** This report uses the source-level `ModuleData` contract and loader. It does not describe the compacted-region serialization layout, compatibility rules, or file identity. Those belong to the separate `.olean` inventory item.

**No complete invalidation rule.** The fact that imports consume compiled artifacts does not by itself establish exactly which source/configuration changes cause Lake to rebuild those artifacts. That remains a separate #3720 question.

**No `.ilean` semantics.** Server/reference information stored in `.ilean` files is outside this report.

**Module-system behavior is revision-sensitive.** The `module`/`public`/`meta`/`all` machinery is an actively evolving part of Lean. Do not project these exact lattice rules onto adjacent releases without revalidation.

**Search-path resolution is contextual.** The source documents first-matching package-root behavior. This report did not execute competing-path fixtures or establish filesystem/case-sensitivity behavior across platforms.

**Cycle behavior is not characterized.** `importModulesCore` describes imports as a DAG. This report does not establish the failure mode for a manually constructed cyclic artifact graph.

**No claim that every environment extension is semantically relevant to Anneal.** The loader imports extension state because Lean elaboration generally depends on it. Which extensions matter to a specific generated proof requires workload-specific analysis.

## Evidence

All Lean source and test evidence below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), inspected on 2026-09-26.

- `src/Lean/Setup.lean`
  - `Import`
  - `ModuleHeader`
  - `ImportArtifacts`
  - Defines the structured import fields, their documented meaning, and the artifact bundle callers may supply.
  - Role: **source**.

- `src/Lean/Parser/Module.lean`
  - `parseHeader`
  - Validates which import qualifiers are legal in module versus non-module files, including the separate-directive requirement for `public import` plus `import all`.
  - Role: **source**.

- `src/Lean/Elab/Import.lean`
  - `HeaderSyntax.imports`
  - `processHeaderCore`
  - `parseImports`
  - Establishes implicit `Init` imports, direct header-to-`Import` conversion, module/server import levels, and the ordinary elaboration call into `importModules`.
  - Role: **source**.

- `src/Lean/Util/Path.lean`
  - module-level search-path documentation
  - `modToFilePath`
  - `SearchPath.findWithExt`
  - `findOLean`
  - Establishes module-name-to-path mapping and search-path resolution.
  - Role: **source**.

- `src/Lean/Environment.lean`
  - `ModuleData`
  - `EffectiveImport`
  - `EnvironmentHeader`
  - `importModulesCore`
  - `finalizeImport`
  - `importModules`
  - Establishes serialized transitive imports, fixed-point import levels, module de-duplication/upgrades, public/private constant maps, imported extension state, conflict handling, and final environment construction.
  - Role: **source**.

- `tests/pkg/module/Module/Basic.lean`
  - Exercises exported/private definitions, exposed versus hidden bodies, meta declarations, and public/private scope constraints in the module system.
  - Role: **source** as checked-in test input/expected diagnostics; no fresh execution.

- `tests/pkg/module/Module/Imported.lean`
  - Exercises `public import`, body hiding, cross-module phase restrictions, and exported use of imported declarations.
  - Role: **source** as checked-in test material; no fresh execution.

- `tests/pkg/module/Module/PrivateImported.lean`
  - Exercises private import visibility and diagnostics requiring `public import` when an imported declaration would escape through a public declaration.
  - Role: **source** as checked-in test material; no fresh execution.

- `tests/pkg/module/Module/ImportedAll.lean`
  - Exercises `import all`, including access to private implementation data in the importing module without making that data publicly exportable.
  - Role: **source** as checked-in test material; no fresh execution.

- `tests/pkg/module/Module/MetaImported.lean`
  - Exercises phase restrictions for `meta import`.
  - Role: **source** as checked-in test material; no fresh execution.

- `tests/pkg/module/Module/ConflictingImported.lean`
  - Exercises rejection of incompatible declarations imported from multiple modules.
  - Role: **source** as checked-in test material; no fresh execution.

The conclusions about cache identity and Anneal generated-project dependency identity are **derived** from the source-level resolution and environment-construction rules above.

## Revalidation

For a new Lean revision, begin with a source diff of:

1. `Lean.Setup.Import` and `ModuleHeader`;
2. `Lean.Elab.HeaderSyntax.imports` and `processHeaderCore`;
3. `Lean.Environment.importModulesCore`, especially the fixed-point comment and flag-combination logic;
4. `Lean.Environment.finalizeImport`;
5. `Lean.Util.Path.findOLean` and search-path initialization; and
6. the `tests/pkg/module/Module` fixtures.

On a Lean-capable surface, add a focused fixture DAG:

- one ordinary non-`module` root;
- one `module` root using private import;
- one using `public import`;
- one using `import all`;
- one using `meta import`;
- a diamond where the same dependency is reached with different modifiers; and
- two search-path roots that can provide the same module name.

For each case, record:

- direct parsed `Import` values;
- `Environment.header.imports`;
- `Environment.header.modules` and effective flags;
- the actual resolved artifact paths;
- visibility of representative public/private declarations;
- availability of representative compile-time code; and
- imported environment-extension behavior needed by elaboration.

For Anneal specifically, repeat the probe through the generated project's real Lake setup rather than only a hand-built Lean invocation. That is the cheapest way to verify that Lake's chosen artifact graph and Lean's consumed import graph agree for the exact generated workspace.

If Anneal introduces a cache key for prepared Lean environments or proof results, validate that changing only the resolved dependency artifact—or changing a transitive serialized import while keeping the root header constant—invalidates or separates that cache as intended.