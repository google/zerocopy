# Aeneas Lean project and generated-package anatomy at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the Lean side has two distinct layers that a consumer must keep separate: the checked-in Aeneas Lean package under `backends/lean`, and the crate-specific Lean files emitted by the Aeneas translator. Generated crate files depend on the checked-in package by importing the umbrella module `Aeneas`; they are not standalone translations.

The checked-in package pins Lean `v4.30.0-rc2` and Mathlib input revision `v4.30.0-rc2` (resolved by its manifest to Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`). Its Lake package exposes two default Lean libraries, `Aeneas` and `AeneasMeta`, plus an `extract` executable used to regenerate the OCaml table that maps modeled Rust items to Lean definitions. The `Aeneas` umbrella itself imports command support, data structures, do-notation support, extraction support, standard-library models, and tactics. Consequently, a generated file's plain `import Aeneas` names a broad proof/runtime support module graph, not a small semantics-only runtime module.

Aeneas can emit either one Lean file per translated crate or a small split package. In split mode it emits `Types.lean` and `Funs.lean`; optional external-model templates and termination-clause files join that graph when needed. `Funs.lean` imports `Types.lean`, external function models, and termination clauses as applicable. An optional crate entry module imports `Funs`. Checked-in generated fixtures follow this structure and show the common file prologue: `import Aeneas`, selected generated imports, opened Aeneas namespaces, linter settings, and resource limits.

The source contains a path that can write a default `lakefile.lean`, but at this revision the visible CLI wiring does not provide a working way to enable it: `lean_gen_lakefile` initializes to `false`, and `-lean-default-lakefile` uses `Arg.Clear`, which also sets it to `false`. Upstream setup documentation instead tells users to create a Lean project, copy the backend `lean-toolchain`, and add `backends/lean` as a Lake dependency. Treat the documented manual project setup as the supported evidence here; do not assume that Aeneas can generate a usable Lake project from the CLI without revalidation.

No fresh Lean, Lake, Aeneas, or Charon execution was performed. The report is based on pinned source, pinned Lake metadata, upstream setup documentation, and checked-in generated Lean files.

## Applicability

Primary subject:

- repository: `AeneasVerif/aeneas`
- revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`
- release: `nightly-2026.06.03`
- checked-in Lean toolchain: `leanprover/lean4:v4.30.0-rc2`
- checked-in Mathlib requirement: `v4.30.0-rc2`
- checked-in Mathlib resolved revision: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`

Current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects this Aeneas release. Current Anneal design deliberately does not freeze the Aeneas/Lean boundary or project layout. This report records the upstream package and generated-file structure available at the selected pin; it does not prescribe how Anneal V2 should package or cache Lean work.

“Checked-in package” below means `backends/lean` in the pinned Aeneas repository. “Generated crate package” means the Lean source emitted from one `.llbc` input by the Aeneas translator. The latter is not necessarily a complete Lake package: the translation source emits Lean modules, while upstream setup documentation supplies the surrounding project steps.

The prior `aeneas-rust-to-lean-translation-nightly-2026-06-03` report owns value/type/borrow semantics. The prior `aeneas-external-models-nightly-2026-06-03` report owns the semantic trust boundary around builtin and user-supplied external models. The prior `aeneas-wp-proof-tools-nightly-2026-06-03` report owns proof-facing `WP.spec` and tactic behavior. This report uses those mechanisms only where they determine package shape or imports.

## Findings

### The Lean backend is a Lake package with two libraries and one extraction executable

`backends/lean/lakefile.lean` declares package `aeneas` and three main targets:

- default library `Aeneas`;
- default library `AeneasMeta`, whose `precompileModules` setting is disabled when the `CI` environment variable is present;
- executable `extract`, rooted at `AeneasExtract`, with interpreter support disabled.

The package directly requires Mathlib from Git at input revision `v4.30.0-rc2`. Its comment explicitly says not to add a separate `std4` requirement because Mathlib already imports `std4` and `quote4` at this pin.

The adjacent `lean-toolchain` fixes Lean to `leanprover/lean4:v4.30.0-rc2`. The checked-in `lake-manifest.json` resolves Mathlib to commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and records inherited dependencies including Plausible, LeanSearchClient, import-graph, ProofWidgets, Aesop, Qq, Batteries, and Cli at exact commits. Those manifest entries describe this package's resolved dependency graph; they do not imply that every generated proof uses every dependency directly.

Basis: **source** + checked-in build metadata.

### `Aeneas` is a broad umbrella import

The root `backends/lean/Aeneas.lean` imports six umbrella modules:

- `Aeneas.Command`;
- `Aeneas.Data`;
- `Aeneas.Do`;
- `Aeneas.Extract`;
- `Aeneas.Std`;
- `Aeneas.Tactic`.

Those umbrellas expand further. For example, `Aeneas.Std` imports allocation, arrays, core models, primitives and lemmas, raw pointers, scalar operations, slices, strings, vectors, and related iterators. `Aeneas.Tactic` imports conversion, elaboration, miscellaneous helpers, Rust attributes, setup, simplifiers/simprocs, solvers, and the `step` family. `Aeneas.Data` imports arrays, bit vectors, bytes, discriminants, integer/list/range/tuple/vector support. `Aeneas.Command`, `Aeneas.Do`, and `Aeneas.Extract` add command, syntax/elaboration, and extraction support.

Every generated Lean file written by `Translate.ml` starts with `import Aeneas`. The generated crate therefore depends, at module-import level, on this umbrella rather than on a narrow hand-selected runtime subset. For build/caching design, “generated Rust model” and “Aeneas support package” are separate inputs whose changes can invalidate different layers, even though the generated file names only one root module.

This source graph establishes an import dependency, not measured compile cost. No statement about how much of the graph Lake recompiles, loads, or caches is made here.

Basis: **source** + **derived** implication about dependency boundaries.

### `AeneasMeta` is a separate library from the umbrella imported by generated code

The Lake file declares `AeneasMeta` independently from `Aeneas`. Its root module imports `AeneasMeta.Async`, `Extensions`, `OptionConfig`, `Saturate`, `Simp`, and `Utils`. The root `Aeneas.lean` does not itself import `AeneasMeta`.

This gives a useful package-level distinction: ordinary generated files explicitly import `Aeneas`, whereas Aeneas also ships a separate metaprogramming library. A future integration should not infer that `AeneasMeta` is part of a generated crate's direct import surface merely because both libraries belong to the same Lake package. Conversely, transitive imports from specific modules were not exhaustively reduced here, so this is not a proof that no `Aeneas` submodule ever reaches an `AeneasMeta` module.

Basis: **source**.

### The `extract` executable generates OCaml model-registry source from the Lean environment

`AeneasExtract.lean` imports `Aeneas`, initializes Lean's search path, loads the `Aeneas` environment, and invokes `writeToFile` to write `../../src/extract/ExtractBuiltinLean.ml`. This is the build-time bridge by which Lean definitions carrying Rust-model registrations become data consumed by the OCaml translator.

The external-model report describes the semantics and trust consequences of that registry. For package anatomy, the important point is directional: the checked-in Lean package is not only a dependency of generated proofs; its environment also feeds generated OCaml source used by the translation binary. Changes to model registrations can therefore cross the Lean/OCaml build boundary before any user crate is translated.

Basis: **source** + **derived** dependency relationship.

### Upstream documentation expects the consumer to create a Lean project around generated files

Pinned `documentation/aeneas-overview.md` describes the Lean setup in separate steps:

1. create a Lean package with Lake;
2. copy or symlink `backends/lean/lean-toolchain` into the project root;
3. add Aeneas as a path dependency on `backends/lean` in `lakefile.toml` or `lakefile.lean`;
4. produce LLBC with Charon;
5. run `aeneas -backend lean ...` to generate Lean files;
6. import those files and write proofs.

The repository's own Lean tests use the same shape: `tests/lean/lakefile.lean` says `require aeneas from "../../backends/lean"`, and its `lean-toolchain` matches the backend toolchain. This is preserved source/configuration evidence for the expected consumer relationship.

A generated crate is therefore not self-contained merely because Aeneas emitted `.lean` files. It needs a compatible Lean toolchain and a Lake project that can resolve the `Aeneas` module.

Basis: upstream **documentation** + checked-in build metadata.

### Non-split extraction emits one crate module

When `-split-files` is not active, `Translate.ml` creates one `<Crate>.lean` file. Its generation configuration includes types, globals, functions, trait declarations, trait implementations, transparent declarations, and opaque declarations in that one module.

For Lean, the file prologue imports `Aeneas`, opens `Aeneas`, `Aeneas.Std`, `Result`, `ControlFlow`, and `Error`, disables three noisy linters, emits `maxHeartbeats` and `maxRecDepth` settings, and enters the generated namespace. If unresolved opaque material requires it and `-all-computable` is not used, the generated file is also placed in a `noncomputable section`.

This single-file mode is a source organization choice. It does not collapse the underlying Aeneas package dependency or the distinction between translated definitions and opaque/model assumptions.

Basis: **source**.

### Split extraction has a small dependency-ordered module graph

With `-split-files`, Aeneas organizes one translated crate into a few roles rather than one file per Rust declaration.

The stable core is:

```text
Aeneas
  ↑
<Crate>.Types
  ↑
<Crate>.Funs
```

For Lean, `Types.lean` contains translated type declarations and trait declarations. `Funs.lean` contains translated function declarations, trait implementations, and globals. `Funs.lean` imports the Types module.

Additional nodes appear when required:

```text
TypesExternal      Clauses.Clauses      FunsExternal
      ↖                 ↑                   ↗
       Types    [template/support]          |
          ↖             |                  |
                    Funs ------------------+
```

More precisely:

- unresolved opaque types cause Aeneas to generate `TypesExternal_Template.lean`; the regular Types module imports the user-provided `TypesExternal` module;
- unresolved opaque functions cause generation of `FunsExternal_Template.lean`; the regular Funs module imports the user-provided `FunsExternal` module;
- requested termination/decreases support can add clause modules and a `Clauses/Template.lean` file;
- `Funs.lean` imports Types, any required external-function module, and the appropriate clauses module.

The templates and user-maintained external modules are intentionally distinct. The generated template path is not the module that the regular generated file expects to import after the user supplies the model.

Basis: **source**. The semantic meaning of external models is covered separately by `aeneas-external-models-nightly-2026-06-03`.

### An optional entry module flattens the split crate to one import

If both split mode and `-gen-lib-entry` are active, Aeneas writes `<Crate>.lean` containing an import of `<Crate>.Funs`. Because Funs already imports its dependencies, the entry file is a convenience root for the translated crate.

`Main.ml` enforces that `-gen-lib-entry` requires split mode and rejects combining it with `-subdir`. That constraint is part of the emitted module-layout contract at this revision.

Basis: **source**.

### Checked-in generated fixtures confirm the split file shape

The pinned repository preserves generated Lean output under `tests/lean`. For the AVL fixture:

- `Avl/Types.lean` starts with the automatic-generation banner, imports `Aeneas`, opens the standard Aeneas namespaces, sets the linter/resource options, enters namespace `avl`, and defines translated types and traits;
- `Avl/Funs.lean` has the same common prologue, additionally imports `Avl.Types`, enters the same namespace, and defines translated functions and trait implementations.

These files are preserved upstream execution artifacts from the project's own generation workflow. They confirm that the source-level module plan has been realized for representative generated code. They are not fresh output from this run and do not establish byte-for-byte determinism for regeneration today.

Basis: preserved upstream **execution** artifacts + **source**.

### Generated files carry build policy as well as translated declarations

The Lean prologue is not semantically empty boilerplate. `Translate.ml` emits:

- `import Aeneas` plus dependency imports;
- opened namespaces used by the generated syntax;
- linter suppressions for duplicate namespaces, hash commands, and unused variables;
- `set_option maxHeartbeats ...` and `set_option maxRecDepth ...` using configurable numeric values;
- `noncomputable section` when opaque content requires it unless `-all-computable` is requested.

Therefore the exact generated artifact depends on extraction configuration beyond Rust/LLBC semantics. A cache or source-correspondence key that wants exact generated Lean bytes must account for output-affecting Aeneas options, not only the Rust source and Aeneas revision.

Basis: **source** + **derived** cache-key consequence.

### The checked-in Aeneas package pins a matching Lean/Mathlib pair

At this revision the backend `lean-toolchain` selects Lean `v4.30.0-rc2`. The Lake file requests Mathlib at `v4.30.0-rc2`, and the manifest resolves that input to immutable Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` plus exact inherited dependency revisions.

The upstream setup documentation explicitly tells consumers to use the backend's `lean-toolchain` “to ensure version compatibility.” A future Anneal environment that reuses generated Lean while changing the Lean or Aeneas package must therefore treat toolchain/package compatibility as a revalidation boundary, rather than assuming generated source is independent of the backend environment.

This report does not claim that every adjacent Lean or Mathlib revision is incompatible. It records the exact supported combination encoded by this Aeneas checkout.

Basis: upstream **documentation** + checked-in build metadata.

### The source contains default-Lakefile generation code, but the visible CLI switch cannot enable it at this pin

`Translate.ml` has a Lean-only branch that, when `Config.lean_gen_lakefile` is true, writes a `lakefile.lean` requiring Mathlib from Git and declaring a package and Lean library for the translated crate.

At the same pinned revision, however, `Config.ml` initializes `lean_gen_lakefile` to `false`, while `Main.ml` registers `-lean-default-lakefile` with `Arg.Clear lean_gen_lakefile`. `Arg.Clear` sets a boolean reference to false. Searches of the current upstream repository for this symbol likewise show only the configuration declaration, the CLI check, and the translation use; no separate setter is visible there.

The safest conclusion is narrow: the code path exists, but the inspected CLI wiring does not establish a usable way to turn it on from its false default. Upstream documentation's explicit project-creation instructions are therefore the stronger evidence for how a consumer should obtain a Lake project at this revision.

Do not generalize this into a claim that no build or embedding path can ever set the reference. No fresh invocation was performed, and a future revision can fix or redesign this option trivially.

Basis: **source** + **derived** control-flow observation.

## Boundaries

- **No fresh build or generation:** this run did not execute Lake, Lean, Charon, or Aeneas. Checked-in generated files are preserved upstream execution evidence only.
- **No cache-performance claim:** the import graph shows dependency structure, but this report does not measure `.olean` reuse, disk footprint, incremental rebuild scope, parallel build behavior, or cache relocation. Those are separate Lake experiments in the research inventory.
- **No exhaustive transitive Lean import closure:** root and major umbrella imports were inspected, but every transitive file-to-file edge inside `Aeneas` was not reduced into a graph. The package-level conclusion only needs the observed umbrella dependency.
- **No semantic re-audit of support libraries:** this report identifies package/module roles. The Rust-to-Lean semantics, external-model trust boundary, and WP/tactic behavior are covered by dedicated reports.
- **Generated Lakefile path unresolved empirically:** source inspection finds an apparently non-enabling CLI flag. No execution was performed to determine whether another invocation path mutates `lean_gen_lakefile` before extraction.
- **No claim that broad imports imply proportional compilation cost:** Lean/Lake caching and elaboration can make the performance consequences much smaller than the source import graph suggests.
- **No claim about adjacent releases:** package layout, toolchain pins, module roots, split-file naming, and imports may change independently in another Aeneas revision.

## Evidence

Observed 2026-09-26 unless otherwise stated.

### Pinned Aeneas source and build metadata

Repository: `AeneasVerif/aeneas`
Revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`

- `backends/lean/lakefile.lean`, blob `c32062866e2f88d2eb768b904745e7104edddb0d`: Lake package, `Aeneas`/`AeneasMeta` libraries, extraction executable, Mathlib requirement.
- `backends/lean/lean-toolchain`, blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`: Lean `v4.30.0-rc2` pin.
- `backends/lean/lake-manifest.json`, blob `1a5af703163d8b39f4311aafe22ae171788179ee`: resolved Mathlib commit and inherited dependency revisions.
- `backends/lean/Aeneas.lean`, blob `6fc8d91f1d1fcead6971b6e0aad88eb889a6f370`: top-level `Aeneas` import surface.
- `backends/lean/AeneasMeta.lean`, blob `c12cdc64f9b6f8b4457759e703a76c048f9fb106`: top-level `AeneasMeta` import surface.
- `backends/lean/AeneasExtract.lean`, blob `8982440660888eeb671bda0e726adf5b31c4ec2d`: Lean-environment-to-OCaml model-registry generator.
- `backends/lean/Aeneas/Std.lean`, blob `565950fb36d3da1618a12866e0e5e3db2cc3be33`: standard-model umbrella imports.
- `backends/lean/Aeneas/Data.lean`, blob `825cb5c009818b011433120a935c0b6beb0df8ef`: data umbrella imports.
- `backends/lean/Aeneas/Tactic.lean`, blob `fc7a52a9fa77b762628de83a685f31cd0e98a273`: tactic umbrella imports.
- `backends/lean/Aeneas/Command.lean`, blob `dc50083d6aad72e0ccd9e2bc840b7fa296cae6c7`: command umbrella imports.
- `backends/lean/Aeneas/Do.lean`, blob `8cd4a8403eaf6e0cf70e944bbcbb74d34953d638`: do-notation umbrella imports.
- `backends/lean/Aeneas/Extract.lean`, blob `b8b88568546d9050c91158cec337cb2567e9b731`: extraction umbrella import.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: Lean file prologue, split/non-split output graph, external templates, entry module, and Lakefile-generation branch.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: CLI switches and consistency checks.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: generation configuration defaults, including `split_files`, `generate_lib_entry_point`, and `lean_gen_lakefile`.

### Upstream documentation

- `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`, section “Project Setup for Lean Backend”: create a Lake project, copy/symlink the backend toolchain, require the local Aeneas backend, run Charon, run Aeneas, then import generated files.

### Preserved generated/build artifacts

- `tests/lean/lakefile.lean`, blob `936ca23067e20c2f05bee88f77bbc00cc2b3b04e`: repository test package depends on `../../backends/lean` and declares many generated/test libraries.
- `tests/lean/lean-toolchain`, blob `635bb9534e5a211d17a7d660a07dd31d1d64c450`: test project uses the same Lean version.
- `tests/lean/Avl/Types.lean`, blob `3e5ad7260c9193434f73bd4d0b858794855e12f2`: checked-in generated split Types module.
- `tests/lean/Avl/Funs.lean`, blob `34be2c16a95a5ab7c59ebccc9cb54bb0bb84d38c`: checked-in generated split Funs module importing `Avl.Types`.

No fresh execution evidence was produced.

## Revalidation

For a newer Aeneas revision, the cheapest package-level revalidation is:

1. inspect `backends/lean/lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` for toolchain, direct requirements, target names, and resolved dependency changes;
2. inspect `Aeneas.lean`, `AeneasMeta.lean`, and the major umbrella modules to detect import-surface changes;
3. inspect `src/Translate.ml`, `src/Main.ml`, and `src/Config.ml` for changes to generated prologues, split/non-split file roles, external templates, entry modules, and output-affecting options;
4. diff one checked-in split fixture such as `tests/lean/Avl/{Types,Funs}.lean` against this report's shape;
5. specifically re-check the `lean_gen_lakefile` default and CLI action before relying on generated Lake project support.

If the question is build-cache behavior rather than package shape, do not infer it from this report. Run the separate clean/warm/relocated/concurrent Lake experiments with an exact Aeneas/Lean/Mathlib environment and record filesystem/cache identities and disk use.