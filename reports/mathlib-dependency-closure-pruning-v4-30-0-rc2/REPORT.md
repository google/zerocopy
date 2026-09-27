# Mathlib dependency-closure pruning in Anneal

## Summary

Current Anneal prunes the vendored Mathlib package by constructing a source-level module dependency graph and retaining the transitive closure reachable from every observed non-Mathlib consumer. It scans Mathlib `.lean` files to map each module to its Mathlib imports, scans non-Mathlib `.lean` files for direct Mathlib imports, adds additional seeds from non-Mathlib Lake trace JSON, computes ordinary graph reachability, and deletes Mathlib source modules outside that closure together with matching build artifacts. It deliberately keeps every Lean module in non-Mathlib packages.

The core idea is sound as a conservative packaging optimization only under explicit completeness assumptions. At Lean `v4.30.0-rc2`, imports are module-header declarations; following Mathlib-to-Mathlib import edges therefore captures the ordinary compile-time module dependency closure. Anneal also scans all current non-Mathlib source files, so direct consumers across Aeneas and its vendored dependencies can seed that closure.

The implementation is nevertheless a lightweight textual approximation rather than Lean's parser. Its source-import regular expression recognizes the ordinary forms Anneal expects, and its trace scanner intentionally searches arbitrary serialized JSON text for `Mathlib.*`-looking tokens. The latter can safely over-retain modules, but both mechanisms have under-approximation boundaries: unusual valid import formatting, trace-only names outside the ASCII component regex, consumers generated after pruning, or a nonstandard Mathlib source layout can escape the inferred graph. The pruning result should therefore be treated as a derived closure with validation obligations, not as a canonical property of Lake or Mathlib.

## Applicability

This report describes `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, where `anneal/flake.nix` invokes `anneal/prune-lake-cache.py` after the prepared Aeneas/Lean dependency tree has been built, vendored-path rewrites have run, the offline `lake --old build` has succeeded, package configuration has been primed, and trace relocation checks have completed. The output is then copied into the final Anneal toolchain bundle.

The Mathlib sources in that dependency tree are selected transitively by Aeneas's Mathlib `v4.30.0-rc2` dependency. The relevant Lean module-header syntax is pinned here to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, also `v4.30.0-rc2`.

The result is specifically useful for deciding which Mathlib modules and corresponding compiled artifacts may be omitted from Anneal's distributed dependency universe. It does not establish that arbitrary metadata, native artifacts, configuration files, or non-module package content can be pruned; those are separate package-tree and native-artifact questions.

## Findings

### The closure is seeded from every current non-Mathlib source consumer

`collect_mathlib_closure` scans both `project_root` and `packages_root`. For every `.lean` file outside the Mathlib package, it extracts imports beginning with `Mathlib` and adds them to the seed set. The scan excludes `.git` directories but otherwise traverses the available tree, including vendored packages.

For Mathlib's own `.lean` files, the same pass derives the module name from the file's path relative to the Mathlib package and records its direct Mathlib imports. A depth-first worklist then follows those edges from the seed set until no new Mathlib module is discovered.

This gives the algorithm the right graph shape for ordinary Lean module dependencies: roots are consumers outside Mathlib, edges are Mathlib module imports, and the kept set is the transitive Mathlib closure. Importantly, the root is not hard-coded to `Mathlib.lean`; a generated verifier that imports one narrow Mathlib module can keep that module and its dependencies without necessarily retaining the entire umbrella module.

### Lean's pinned header grammar makes imports an appropriate source-level edge

At Lean `3dc1a088...`, `Lean.Parser.Module.Syntax` parses a module header as an optional `module` declaration, optional `prelude`, then zero or more import directives. Each import directive contains optional `public`, optional `meta`, the `import` keyword, optional `all`, and one module identifier. `Lean.Parser.Module` elaborates those header imports before ordinary commands.

This means an ordinary compiled Lean module's module-level dependency edges are exposed in the header rather than being arbitrary command-time dynamic imports. A complete parser for the pinned import syntax could therefore recover the direct source dependency graph Anneal needs.

Anneal does not use that parser. `IMPORT_RE` is a line-oriented regular expression, and `imported_mathlib_modules` splits the captured suffix on whitespace. It handles the simple `import Mathlib.X`, `public import Mathlib.X`, and `meta import Mathlib.X` shapes found in the expected source corpus, and it still finds `Mathlib.X` in an `import all Mathlib.X` suffix. But its language is not identical to Lean's grammar. Comments or whitespace arrangements that Lean accepts between header tokens can make a valid import invisible to the regex.

### Trace-derived seeds are a conservative supplement, not a dependency parser

For non-Mathlib `.trace` files, Anneal parses the JSON and then applies `MATHLIB_TRACE_RE` to a re-serialized JSON string. It does not restrict the search to a semantic “dependency” field. Any serialized caption, log, path, option, or other string containing a token shaped like `Mathlib.Foo.Bar` can become a seed.

That broad search is useful in the safe direction: false positives retain extra modules instead of deleting required ones. It also helps retain Mathlib modules that are visible in already-produced Lake state even if a relevant source root is indirect or no longer present in the obvious project source set.

It is not complete by construction. The regex limits module components to ASCII letters, digits, underscore, and apostrophe. A module name represented only in trace state with another valid Lean identifier character would not be recognized. More generally, because the scan is textual rather than schema-aware, there is no theorem that every future Lake representation of a module dependency will contain a matching string.

### Pruning maps source modules to build products by module-path prefix

After computing the closure, `prune_package` enumerates `.lean` files outside `.lake`. For Mathlib, it converts each retained module name from dotted form to the platform path separator and deletes source files whose module paths are not in the closure.

For every deleted source module, `remove_build_artifacts` examines the corresponding directory under `.lake/build/lib/lean` and `.lake/build/ir` and deletes files whose base names start with `<module-name>.`. This removes the ordinary family of compiled files associated with that module without deleting a sibling such as `FooBar` when pruning `Foo`.

The mapping is intentionally narrower than “delete every artifact transitively related to an unused source.” It assumes Mathlib's conventional module-to-path layout and two build-product roots. A custom `srcDir`, target-specific output path, or artifact family stored elsewhere would require separate handling. Anneal's script acknowledges related layout assumptions in the surrounding toolchain work; this report does not generalize the prefix deletion beyond the exact code.

### Non-Mathlib packages are not dependency-pruned

`prune_package` takes a special path only when `pkg_dir.name == "mathlib"`. For every other package it marks every discovered `.lean` file as used and prints that all Lean modules are being kept. Thus a mistake in the Mathlib closure algorithm cannot silently prune Aesop, Batteries, Qq, or Aeneas module sources through the same reachability mechanism.

The script still removes selected package metadata and `.ltar` files from those package trees. That cleanup is independent of module closure and belongs to the separate “Safe pruning of Lean package trees” question.

### Root-project Mathlib build products are deleted to avoid a second untracked copy

After pruning vendored packages, `prune_root_mathlib_cache` removes `project_root/.lake/build/lib/lean/Mathlib` and root-level files whose names start with `Mathlib.`. The prepared archive is intended to use the Mathlib package's retained `.lake/build` products rather than preserving an additional root-project Mathlib build-cache copy.

This is relevant to validation because “the retained module exists somewhere” is not sufficient. A post-prune verifier must exercise the same package layout the final generated workspace will use and must not accidentally succeed by reading a duplicate root cache that the pruning script removes.

### The existing unit test covers the principal graph shape but not parser completeness

`test_prunes_mathlib_to_reachable_closure` constructs two independent seeds: one direct source import and one Mathlib-looking module name in a non-Mathlib trace. Both reach a shared transitive dependency. It verifies that the three reachable source modules and a reachable compiled artifact survive while an unrelated Mathlib module and its build products are deleted. It also verifies deletion of the root Mathlib build-cache copy.

A second test verifies that non-Mathlib source/build modules are retained. These tests protect the intended closure mechanics and package asymmetry. They do not test comments between import tokens, Unicode module components, generated-after-prune consumers, custom source layout, or equivalence of a complete post-prune offline build.

## Boundaries

No fresh Lean build or pruning execution was performed for this report. The algorithm and its tests are read from current `google/zerocopy` source; the import-language comparison is read from the exact Lean `v4.30.0-rc2` parser source.

The closure result is only as complete as the consumer universe present when `collect_mathlib_closure` runs. A later-generated Lean source file, a later-enabled package, or another execution mode with different roots can require a module that was legitimately unreachable during pruning. Consumers must therefore either be frozen before the prune step or participate in revalidation.

The source scanner is not a Lean parser. Its current regex appears sufficient for Anneal's ordinary import style, but exact syntax coverage has not been proven. A robust future implementation could use Lean's header parser or another authoritative import extractor and reserve trace scanning for conservative supplementary roots.

This report does not decide whether package metadata, tests, documentation, `.ltar` files, configuration artifacts, native libraries, executables, or other non-module files are safe to remove. It also does not establish cross-platform portability of retained `.olean`/native products. Those belong to adjacent inventory items.

## Evidence

- **Pruning implementation — source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/prune-lake-cache.py`, blob `b0eb8eaa5ecefad9766a155994968712826ed996`. `collect_mathlib_closure` builds the source graph and roots, `prune_package` applies the Mathlib-only closure, `remove_build_artifacts` deletes module-matched build products, and `prune_root_mathlib_cache` removes the duplicate root Mathlib cache.
  - https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/prune-lake-cache.py

- **Pruning tests — source.** Same revision, `anneal/tests/test_prune_lake_cache.py`, blob `596603415cf21be8b1e7b585e67bd37631b9a522`. The first test covers source and trace seeds, a shared transitive dependency, unused-module deletion, build-artifact deletion, package-metadata cleanup, and root-cache deletion. The second keeps all non-Mathlib modules.
  - https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/tests/test_prune_lake_cache.py

- **Placement in Anneal's build pipeline — source.** Same revision, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`. The Aeneas compiled derivation primes/unpacks dependencies, rewrites vendored Lake state, performs an offline `lake --old build`, primes package configuration, rewrites/scans traces, then invokes `prune-lake-cache.py` immediately before copying the final Aeneas package tree.
  - https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/flake.nix

- **Pinned Lean import grammar — source.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `src/Lean/Parser/Module/Syntax.lean`, blob `1fd6c0af6d7e204bbfd1c0e97fa80c818bf6f97c`, lines 17–29. The import parser accepts optional `public`, optional `meta`, `import`, optional `all`, and one module identifier; module headers contain repeated import directives.
  - https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Parser/Module/Syntax.lean#L17-L29

- **Pinned import-header handling — source.** Same Lean revision, `src/Lean/Parser/Module.lean`, blob `024a5c10df494caccca4bb908e7bcc32df2530ca`, lines 84–112. Header parsing iterates import syntax and extracts each module identifier before ordinary commands.
  - https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Parser/Module.lean#L84-L112

## Revalidation

A source-level revalidation should first compare the current pruning script and tests with the pinned blobs above. If Lean changes, compare the new authoritative module-header grammar with `IMPORT_RE`; any syntax accepted by Lean but not by the scanner is a potential under-approximation unless a separate conservative seed covers it.

An execution probe should start from the exact prepared dependency tree Anneal intends to distribute. Before pruning, enumerate every non-Mathlib source root that the supported generated-workspace modes can load. Use Lean's own header parser to compute a reference Mathlib import closure, then compare it with `collect_mathlib_closure`. The Anneal set may be larger because trace scanning intentionally over-approximates; it must not be smaller.

After pruning, delete or quarantine any duplicate root-project Mathlib cache, deny network access, and run every supported generated-workspace entry point against the pruned package tree. Record all module-load paths. A missing-module failure is evidence that the seed universe or graph extraction was incomplete, not merely a transient cache miss.

Add focused regression fixtures for valid import syntax that differs from the current textual assumptions, including comments/whitespace between import modifiers and the keyword. Add a trace fixture with a valid non-ASCII Lean module component if such a Mathlib module can exist at the selected revision; either widen the trace matcher or document why trace-only seeding cannot be relied on for such names.
