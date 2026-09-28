# Anneal V1 source scanner versus rustc at `41f5b37`

## Summary

Retained Anneal V1 does not discover verification subjects from rustc's configured, macro-expanded program. It first parses Rust source text with `syn`, finds a restricted set of source-level items carrying Anneal documentation blocks, constructs textual Charon `--start-from` roots, and separately asks Charon/Cargo/rustc to compile the selected target.

Those two views are not equivalent.

The scanner is explicitly configuration-agnostic. It does not evaluate `#[cfg]`, does not expand `cfg_attr`, does not expand declarative or procedural macros, does not run `include!`, and does not use rustc name resolution or compiler definition identities. Its hand-written module traversal covers common direct `mod foo;`, `foo.rs`, `foo/mod.rs`, and literal `#[path = "..."]` cases, but it is not rustc's module loader. In particular, it only warns about `cfg_attr(..., path = "...")`, and its unloaded-module record loses the enclosing inline-module path, so `mod outer { mod child; }` can be resolved and named differently from rustc.

The scanner also exposes a narrower item model than rustc. It supports module-level functions, structs, enums, unions, traits, impls, associated functions, trait functions, and foreign functions. It does not make imports/reexports, type aliases, constants/statics, macro-produced items, closures, anonymous constants, or other compiler-created definitions first-class Anneal annotation subjects. It traverses block-local items but deliberately rejects an Anneal annotation on an item defined inside a block.

Charon, by contrast, runs behind Cargo/rustc after configuration and macro expansion. It sees the compiler's selected program and then follows semantic definitions from Anneal's textual start roots. This semantic traversal can pull in dependencies that the scanner did not annotate, but it does not retroactively make the scanner's source inventory complete or create Anneal specifications for definitions that the scanner never recognized.

The correct historical interpretation is therefore narrow: V1 proves obligations for scanner-recognized annotations that successfully correspond to definitions in the rustc/Charon compilation selected by that invocation. A successful run is not evidence that the scanner and rustc had identical item inventories, module identities, or configuration views.

## Applicability

This report applies to the retained Anneal V1 implementation under:

- repository: `google/zerocopy`;
- revision: `41f5b37afe7060fd9fe08c00b200672cd76d77b9`;
- path: `anneal/v1`.

It addresses the #3720 inventory item:

> **V1 source scanner versus rustc** — `cfg`, aliases, macros, modules, imports, local items.

The compiler-side comparison uses current native reference reports for the Rust/Charon revisions selected by Anneal's pinned toolchain. The central V1 findings come directly from the retained V1 source.

This report is historical. Current Anneal V2 design on `main` is authoritative for new implementation work.

## Findings

### V1 joins two independently constructed program views

`resolve_roots` uses Cargo metadata to choose packages and targets and obtains each target's top-level `src_path`. `scan_workspace` then recursively reads those source files itself. Each file is parsed with `syn::parse_file`, and an `AnnealVisitor` walks the resulting source AST.

For each recognized Anneal item, the scanner constructs:

- a parsed Anneal specification/proof payload;
- a source file and syntactic module path;
- a textual Charon `--start-from` string.

Later, `run_charon` invokes `charon cargo --preset=aeneas` and passes those textual start roots to the compiler-backed translation.

There is no rustc `DefId`, `DefPathHash`, HIR identity, or Charon item identity joining the two views at discovery time. The correspondence is reconstructed from source-level names and module paths.

That architecture is sufficient only when the scanner's source interpretation and rustc's configured/expanded program agree on the relevant definition.

Basis: **retained V1 source** — `resolve.rs`, `scanner.rs`, `parse/mod.rs`, `charon.rs`.

### Feature flags are forwarded, but the scanner remains configuration-agnostic

`resolve_roots` forwards Anneal's Cargo feature flags to `cargo metadata`, and `run_charon` forwards `--all-features`, `--no-default-features`, and explicit `--features` arguments to the underlying Cargo invocation.

That synchronization is useful, but it does not configure the source scanner.

`scanner.rs` states the limitation directly: the scanner is currently CFG-agnostic and does not evaluate `#[cfg(...)]`. It can therefore visit an item that rustc removes for the active compilation, provided the item's source file exists.

The compiler-side problem is broader than Cargo features. At the pinned Rust revision, the active cfg set can also depend on target properties, test/proc-macro mode, panic/codegen settings, build-script-emitted cfg values, and explicit rustc cfg arguments. rustc strips cfg-false syntax before HIR and MIR.

Thus forwarding Cargo feature flags to both metadata and Charon does not make scanner discovery configuration-equivalent to rustc.

Basis: **retained V1 source** + native report `rust-conditional-compilation-nightly-2026-05-31`.

### A cfg-false annotated item can exist for the scanner but not for Charon

Because the scanner visits raw source syntax, an Anneal block on a cfg-false function or type can still produce a parsed item and a textual start root.

rustc removes that item before HIR/MIR for the selected compilation. Charon cannot translate a compiler definition that does not exist in that configured crate.

The exact downstream symptom depends on the root and surrounding module coverage; the source does not justify one universal failure mode. The stable conclusion is the mismatch itself: scanner discovery does not prove compiler presence.

Conversely, source that rustc includes only after configuration or expansion can be absent from scanner discovery, as discussed below.

Basis: **retained V1 source** + native conditional-compilation report.

### `cfg_attr(..., path = ...)` is explicitly unsupported, not approximated soundly

The scanner recognizes a syntactic `cfg_attr` containing `path = "..."` only to emit a warning:

> Anneal does not currently evaluate conditional paths; Anneal annotations in this file may be ignored.

Its actual module resolver consumes only a direct literal `#[path = "..."]` or the default `foo.rs` / `foo/mod.rs` search.

rustc's configured module loader behaves differently. A true `cfg_attr` can synthesize the active `path` attribute before module loading, so the selected source file can depend on the compiler cfg set.

This creates a direct false-negative boundary: rustc can compile an alternate module file containing verification-relevant code while V1 scans a different default file or no file for that logical module.

Basis: **retained V1 source** + native reports `rust-conditional-compilation-nightly-2026-05-31` and `rust-module-file-resolution-nightly-2026-05-31`.

### The manual module loader loses inline-module context for an out-of-line child

V1 has a second, source-defined module discrepancy independent of cfg.

Inside `parse/mod.rs`, the visitor tracks an inline module path in `current_path`. But when it encounters an unloaded declaration such as `mod child;`, the callback emits only:

- `name`;
- direct `path_attr`;
- whether the declaration was inside a block.

It does **not** include the visitor's enclosing `current_path`.

Back in `scanner.rs`, the recursive file loader resolves every returned unloaded module relative to a base directory computed from the current physical file and then appends only `module.name` to the scanner context.

For a shape such as:

```rust
mod outer {
    mod child;
}
```

in `src/lib.rs`, the callback for `child` does not preserve `outer`. V1 can therefore search for and name the child as though it were a direct child of the current file's scanner context rather than `crate::outer::child`. If a coincidentally matching file exists, it can scan the wrong source; if only rustc's actual nested module file exists, it can miss it.

Simple out-of-line nesting across separate files can still work because each recursive scanner invocation carries the prefix established when that file was entered. The defect is specifically that an unloaded module discovered while walking an **inline** module does not carry that inline path back to the outer file loader.

Basis: **retained V1 source** — `parse/mod.rs` and `scanner.rs`; native Rust module-resolution report for the compiler-side semantics.

### Literal `#[path]` support is narrower than rustc module identity

V1 does support a direct literal `#[path = "..."]` on an unloaded module. It also deliberately avoids global file deduplication because the same physical file may be mounted at different module positions.

That is useful, but it is still not equivalent to rustc's module system:

- cfg can select a path before rustc loads the module;
- relative module lookup depends on the containing module/file style;
- the same file path does not by itself determine logical module identity;
- inline nesting contributes to logical identity even when no separate file exists.

The scanner's physical recursion and rustc's logical module construction therefore need explicit correspondence; filesystem reachability alone is insufficient.

Basis: **retained V1 source** + native Rust module-resolution report.

### Macro expansion is a one-way visibility gap

The scanner calls `syn::parse_file` on the pre-expansion source and uses `syn::Visit`. It does not invoke rustc's macro expander.

As a result, it does not discover Anneal subjects that exist only after:

- `macro_rules!` expansion;
- function-like, derive, or attribute procedural macros;
- `include!` of generated Rust;
- another macro that emits functions, impls, types, or modules.

The compiler side is the opposite. rustc expands configured syntax before Charon's compiler callback, so target-crate definitions generated by macros can be visible to Charon like handwritten definitions, subject to normal Charon support and reachability.

Attribute macros create an additional correspondence hazard: V1 can scan and name the pre-expansion item while the macro removes, renames, duplicates, or otherwise replaces the compiler-visible definition. The raw source name is not a proof of post-expansion semantic identity.

Basis: **retained V1 source** + native report `generated-rust-visibility-nightly-2026-05-31`.

### Build-generated Rust can reach Charon without ever becoming scanner input

A Cargo build script can write Rust into `OUT_DIR`, and target source can consume it with `include!` or another compile-time mechanism. That generated Rust is part of rustc's selected target after expansion.

V1's scanner starts from Cargo metadata source paths and recursively follows only its own module-file rules. It does not execute macro expansion or discover arbitrary files included by `include!`.

Therefore an item generated into `OUT_DIR` can be compiler/Charon-visible while remaining absent from the scanner's annotation inventory and source-map model.

This is a correspondence limitation, not a claim that every generated Rust item should be separately user-annotated.

Basis: native generated-Rust-visibility report + retained V1 scanner architecture.

### Imports and aliases are not semantic identities in the scanner

V1's parsed item model has explicit variants for functions, concrete nominal types, traits, and impls. It has no Anneal item variant for:

- `use` imports or reexports;
- type aliases;
- constants or statics;
- macro definitions or invocations.

This needs two distinctions.

First, ignoring an ordinary `use foo::f as g` is not automatically incorrect for a specification attached to the original `foo::f`: the import introduces another source-level binding, not another implementation of the function. V1 can still target the defining item by its defining module path.

Second, V1 cannot use rustc name resolution to treat alternate public paths as identities, and it cannot make a documentation block attached to a `use`/reexport or type alias into a first-class Anneal verification subject. Those constructs are outside its parsed annotation model even though rustc understands them semantically.

The safe conclusion is therefore not "aliases break V1." It is that alias/import resolution belongs to rustc's semantic view and is not represented in V1's source-level subject identity.

Basis: **retained V1 source** — `ParsedItem` and `AnnealVisitor`; compiler-side identity model in the current reference corpus.

### Local items are found syntactically and then rejected as annotation subjects

The visitor recursively enters Rust blocks. Once inside a block, it sets `inside_block = true`.

If it finds an Anneal block attached to an otherwise supported item there, `process_item` returns an explicit error:

> Anneal cannot verify items defined inside function bodies or other blocks. Move this item to the module level if you wish to verify it.

This is an intentional V1 limitation, not an accidental omission.

rustc's program model is broader. Block-local functions, types, impls, closures, anonymous constants, and compiler-synthesized definitions can have compiler identities or bodies even though many have no ordinary canonical Rust source path.

V1 therefore cannot attach Anneal source annotations directly to the full set of compiler definitions. Charon may still encounter local or anonymous definitions through semantic traversal from a supported module-level root, but that does not make them independent Anneal annotation subjects.

Basis: **retained V1 source** + native report `rust-local-nested-items-nightly-2026-05-31`.

### Impl and method fallbacks reduce naming risk but do not reconcile the two worlds

V1 recognizes that several source items are hard to name reliably from syntax alone. For:

- impl blocks;
- impl methods;
- trait methods;
- foreign functions,

the scanner marks the item as "unreliable" and uses the containing module, rather than the exact syntactic item name, as the Charon start root.

This deliberately broadens extraction and avoids depending on an exact fully qualified name for those cases.

It does not solve cfg, macro, module-file, alias, or local-definition correspondence. A broader compiler root can include more semantic dependencies, but Anneal's own specification generation still operates on the source items the scanner recognized.

Basis: **retained V1 source** — `scanner.rs`.

### Charon semantic reachability can exceed Anneal annotation discovery

The current Charon corpus establishes that translation recursively follows semantic dependencies from its configured roots. Consequently, an unannotated or scanner-unaddressable definition can still appear in LLBC when it is required by a selected root.

This is useful, but it is not a completeness proof for the source scanner.

There are separate questions:

1. **Was a compiler definition translated?**
2. **Did V1 discover a source annotation for it?**
3. **Did V1 generate the intended specification/proof obligation for it?**

Semantic reachability can answer the first without answering the second or third.

Basis: native Charon dependency/source-coverage report + retained V1 scanner/generator boundary.

### A V1 success result is scoped to correspondence that actually held

The scanner/compiler split yields four materially different cases:

| Case | Scanner | rustc/Charon | Consequence |
| --- | --- | --- | --- |
| Source item exists and survives with matching identity | sees it | sees it | intended V1 path can work |
| cfg-false or macro-transformed-away source item | can see pre-expansion text | does not have matching definition | root/spec correspondence can fail |
| macro/include/generated compiler item | does not see generated item | can see it | compiler coverage can exceed annotation coverage |
| local/unsupported source construct | rejects or does not model it | compiler can represent it | not a first-class V1 annotation subject |

A successful historical V1 run should therefore be read as a theorem about the recognized items that made it through this correspondence boundary under the selected Cargo/rustc invocation.

It should not be promoted into either of these stronger claims:

- the raw source scanner enumerated the same program as rustc;
- every compiler-visible definition that matters to the proof had an independently scanner-addressable Anneal annotation.

Basis: **derived** from the source-defined architecture and compiler-side reports.

## Boundaries

- No fresh Anneal V1, Cargo, rustc, Charon, Aeneas, or Lean execution was performed.
- The report establishes source-defined mismatch classes. It does not claim that every mismatch leads to silent acceptance; some produce explicit scanner, Charon, compiler, or later verification failures.
- The report does not duplicate the separate V1 coverage/annotation-totality item. That subject asks whether every intended unsafe obligation was annotated; this report asks whether source-level discovery corresponds to the compiler program.
- It does not claim that imports/reexports create new executable definitions. The limitation is absence of rustc name-resolution identity in the scanner and lack of first-class annotation support for those source constructs.
- It does not claim that every compiler-created local or anonymous definition should become a user-visible Anneal subject.
- It does not fully enumerate Charon support for every macro-generated, local, anonymous, or foreign definition.
- It does not prescribe the V2 architecture. A compiler-backed discovery design, an explicit source-to-semantic correspondence layer, or another fail-closed scheme could address these problems in different ways.
- Current V2 on `main` remains authoritative; this is retained-V1 reference material.

## Evidence

**Retained V1 source — `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.**

- `anneal/v1/src/resolve.rs` — Cargo metadata roots, feature forwarding, target selection, and the explicit note that the scanner is cfg-agnostic.
- `anneal/v1/src/scanner.rs` — source-file recursion, cfg-agnostic warning/comments, `start_from` construction, manual module resolution, and broad-module fallback for hard-to-name items.
- `anneal/v1/src/parse/mod.rs` — `syn::parse_file`, supported annotation item taxonomy, inline-module path tracking, unloaded-module record shape, `cfg_attr(path)` warning, direct `path` extraction, and block-local annotation rejection.
- `anneal/v1/src/charon.rs` — compiler-backed Charon invocation, textual `--start-from` roots, target selection, and feature forwarding.
- `anneal/v1/src/main.rs` — ordering between resolution, scan, validation, Charon, and later stages.
- `anneal/v1/docs/design/design.md` and `docs/agent/01_philosophy_and_pipeline.md` — historical intended scanner/Charon division and V1 limitation context.

**Current native reference corpus.**

- `reports/rust-conditional-compilation-nightly-2026-05-31` — cfg/cfg_attr timing and compiler-input identity.
- `reports/rust-module-file-resolution-nightly-2026-05-31` — rustc module/file identity and path-selection rules.
- `reports/generated-rust-visibility-nightly-2026-05-31` — build-script/proc-macro generated target Rust before Charon.
- `reports/rust-local-nested-items-nightly-2026-05-31` — local/anonymous compiler definitions and absence of canonical source paths.
- `reports/charon-dependency-and-source-coverage-nightly-2026-06-03` — semantic root/reachability behavior after rustc preprocessing.

The source and native reports agree on the central boundary: V1 source discovery is a syntactic pre-rustc view, while Charon consumes the configured and expanded compiler program.

## Revalidation

For an execution-capable reproduction of retained V1, use one small workspace containing discriminating fixtures rather than a large application.

Include:

1. two annotated functions under mutually exclusive `#[cfg]` predicates;
2. `#[cfg_attr(..., path = "...")] mod selected;` with distinct annotated module files;
3. `mod outer { mod child; }` with `child.rs` only at rustc's nested location;
4. an annotated item emitted by `macro_rules!` or a procedural macro;
5. build-script-generated Rust consumed with `include!`;
6. an attribute macro that changes or removes a scanner-visible item;
7. a `pub use ... as ...` and a type alias carrying documentation;
8. an annotated local function inside a body.

Preserve, for each configuration:

- the scanner's discovered items, source files, module paths, and `start_from` strings;
- the exact Charon/Cargo argv and active cfg inputs;
- rustc post-expansion/HIR definition identities when available;
- the LLBC item inventory and source spans;
- Aeneas/Anneal generated Lean artifacts;
- process exit status and diagnostics.

The decisive comparison is not whether all files were read. It is whether every intended Anneal subject has an explicit, reproducible relation between:

1. the source item carrying the annotation;
2. the configured/expanded rustc definition;
3. the Charon start root/item;
4. the generated verification declaration.

Any case without that relation should remain outside a strong end-to-end coverage claim.
