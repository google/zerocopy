# Rust conditional compilation before HIR and MIR at nightly-2026-05-31

## Summary

At the Rust compiler revision used by Anneal's pinned Charon toolchain, false `#[cfg(...)]` branches disappear during AST configuration and macro expansion, before name resolution finishes and before the surviving AST is lowered to HIR. They therefore never become HIR or MIR for that compilation. A downstream MIR consumer cannot recover code excluded by the active configuration from the compiler representation it receives.

The active configuration is a property of one rustc invocation. rustc combines compiler-derived options such as target architecture, operating system, target features, panic strategy, test/proc-macro mode, and debug assertions with arbitrary `--cfg` options. Cargo turns each active Cargo feature on a compilation unit into `--cfg feature="name"`; it can also pass `--cfg test` and build-script-emitted custom cfg values. Two Cargo units for the same package can therefore expose different Rust source to later compiler phases.

`cfg_attr` is part of that same early transformation. A true `cfg_attr` expands to its listed attributes; a false one contributes no attributes. Because one of those attributes can be `path`, the active configuration can choose which external file supplies a `mod foo;`. rustc processes configuration attributes while collecting expansion work, and its module loader uses the resulting attributes when selecting and parsing an out-of-line module.

The built-in `cfg!` macro is different from `#[cfg]`: it evaluates a predicate to a Boolean literal but does not remove the surrounding source. Code in both branches of an ordinary `if cfg!(...)` is still syntactically present after cfg stripping and may survive until later compiler simplification.

No fresh rustc or Cargo execution was performed. The report uses the pinned Rust Reference, rustc source, and Cargo source. It establishes where configuration changes the compiler input and which inputs determine that configuration; it does not empirically enumerate every cfg value for every target.

## Applicability

Rust compiler subject:

- repository: `rust-lang/rust`
- revision: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
- relationship: rust source revision containing the Cargo submodule selected by the pinned nightly-2026-05-31 toolchain used by Anneal's Aeneas/Charon chain.

Normative-language subject:

- repository: `rust-lang/reference`
- revision: `ad35aca481751a06afeb23820a672b0f3b11a476`
- relationship: the `src/doc/reference` submodule recorded by the Rust compiler revision above.

Cargo subject:

- repository: `rust-lang/cargo`
- revision: `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`
- relationship: Cargo revision embedded by the Rust compiler revision above.

The report covers ordinary `cfg`, `cfg_attr`, `cfg!`, Cargo feature cfgs, Cargo test cfg, build-script custom cfg, target-derived cfg values, and cfg-dependent module-file selection. It does not attempt to catalogue every unstable cfg key or every compiler frontend transformation.

## Findings

### Configuration options are fixed from the compilation environment, not by source declarations

The Rust Reference states that configuration options are determined statically during compilation. Some are compiler-set from the compilation target and mode; others are arbitrary options supplied outside the crate. A crate cannot set a configuration option from its own Rust source.

For rustc, arbitrary options enter through `--cfg`. Compiler-derived options include target architecture, target OS/family/environment/vendor/endian/pointer width, target features, panic strategy, test mode, proc-macro mode, and debug assertions, among others.

The same source text can therefore denote different surviving Rust programs under different rustc invocations.

Basis: **normative** + **source**.

### `#[cfg]` removes the attached form when its predicate is false

The Reference defines `#[cfg(predicate)]` as conditional inclusion. Multiple `cfg` attributes compose conjunctively: if any predicate is false, the form is not included.

More strongly, the Reference says that when the predicate is false, the form is removed from the source code. When the predicate is true, the form remains with its `cfg` attribute removed.

The crate-level case has a narrow ordering rule: a false crate-level cfg keeps earlier crate attributes but removes later crate attributes and the following crate contents. That does not make the excluded items part of the compiled crate.

Basis: **normative**.

### rustc performs cfg stripping in the AST expansion machinery

At the pinned compiler revision, `rustc_expand::config::StripUnconfigured` is documented in source as the folder that strips items not belonging to the current configuration.

Its `configure` method first expands `cfg_attr`, evaluates the remaining `cfg` attributes with `in_cfg`, and returns `None` for a node that is not in the configuration. The token-specific path used for derive input likewise removes an attributes target when its cfg is false.

The invocation collector also handles `cfg` and `cfg_attr` as the first attributes on an AST node. A false cfg returns the node's default/empty output rather than collecting it for further expansion.

This is structural deletion of AST nodes, not merely a later code-generation decision.

Basis: **source**.

### cfg stripping precedes HIR lowering and MIR construction

`rustc_interface::passes::configure_and_expand` describes itself as running the compiler's early phases: initial cfg processing, syntax expansion, secondary cfg expansion, test-harness synthesis, standard-library/prelude injection, and name resolution.

After macro expansion, `configure_and_expand` calls `resolver.resolve_crate(&krate)` on the configured AST. The resulting AST is stored for lowering. The query provider later lowers that AST with `rustc_ast_lowering::lower_to_hir`; MIR construction comes after HIR in the compiler query graph.

A node removed by cfg stripping therefore cannot have an ordinary HIR or MIR body in that compilation. Any verification pipeline attached at MIR or later must treat the active cfg set as part of the subject identity if it wants its coverage claim to be precise.

Basis: **source** + **derived** phase ordering.

### cfg processing and macro expansion are interleaved enough that generated nodes are configured too

Conditional compilation is not only one preprocessing sweep over the original text. The expansion collector recognizes `cfg` and `cfg_attr` while it recursively processes AST nodes and macro output.

For derive proc-macro input, rustc also configures attached token streams eagerly so the proc macro receives cfg-expanded input. For ordinary AST expansion, `StripUnconfigured` operates on parsed AST nodes.

Thus source generated by macro expansion can itself be subject to cfg processing, while cfg can also determine which syntax is available to a macro.

Basis: **source**.

### `cfg_attr` can change semantics without deleting the annotated item

The Reference defines `cfg_attr(predicate, attrs...)` as conditional attribute insertion. If the predicate is true, each listed attribute is expanded onto the target; if false, those attributes are absent. Nested `cfg_attr` is allowed.

This can affect much more than diagnostics. A cfg-selected attribute can change representation, linkage, lint behavior, macro behavior, or module-file selection.

For source-coverage purposes, it is not sufficient to record only which items survived. The post-`cfg_attr` attribute set can also be semantically relevant.

Basis: **normative**.

### Conditional `path` selects which file backs an out-of-line module

The Reference gives the canonical pattern:

`#[cfg_attr(target_os = "linux", path = "linux.rs")]`
`#[cfg_attr(windows, path = "windows.rs")]`
`mod os;`

The `path` attribute controls where an external module is loaded from. Its relative-path rules depend on whether the containing file is a mod-rs-style file and whether the module declaration occurs inside an inline module.

At the pinned rustc revision, the expansion/module-loading path consumes the module's processed attributes when computing or recovering the external module path. An unloaded `mod foo;` is then parsed from the selected file. If parsing an external module introduces inner attributes, rustc reconfigures/recollects it.

The same logical module name can therefore denote different source files under different cfg sets. File identity is not recoverable from the module name alone.

Basis: **normative** + **source**.

### A false cfg on an external module declaration can prevent the module file from becoming part of the crate

Because the expansion collector drops a cfg-false item before ordinary processing continues, a cfg-false out-of-line module declaration does not become an ordinary loaded module for the configured crate.

This matters for source inventories. A filesystem crawl that finds both `unix.rs` and `windows.rs` does not show that both files were compiler inputs to one target. Conversely, an inventory based only on the configured HIR/MIR does not show source that was deliberately excluded.

Basis: **source** + **derived**.

### Cargo feature resolution becomes rustc `cfg(feature = "...")`

Cargo's unit contains its resolved feature vector. In the pinned Cargo source, `features_args(unit)` adds one pair of rustc arguments per active feature:

`--cfg`
`feature="feature-name"`

The Rust Reference explicitly treats the `feature` cfg key as a Cargo convention.

Because resolver 2/3 can give the same package different feature vectors in different compilation contexts, the same package's cfg-selected Rust items can differ between its host/proc-macro/build-dependency and target instances.

Basis: **documentation** + **source**.

### Cargo and build scripts can add non-feature cfg values

Cargo's rustc command construction adds `--cfg test` when compiling a test unit in the relevant mode.

Build scripts can emit custom rustc cfg directives. The pinned Cargo compiler collects the resulting build-script cfg strings and appends each to the target rustc command as `--cfg <value>`.

Therefore the active cfg set is not reconstructible from Cargo's package feature names alone. Build-script output and compilation mode can change which Rust forms survive.

This relationship is also preserved in the existing generated-Rust-visibility report; the point here is narrower: those outputs feed the same rustc cfg evaluator that removes AST forms.

Basis: **source**.

### Target cfgs are derived from the actual rustc target and compiler options

The pinned rustc configuration builder inserts well-known cfg values from the session target and codegen settings. Examples include target architecture, OS, families, environment, vendor, pointer width, object format, target features, atomic capabilities, panic strategy, proc-macro crate type, and debug-assertion state.

The compiler also rejects user attempts to set several well-known cfg keys directly through arbitrary `--cfg`, directing users to the corresponding target or codegen options instead. That separation prevents a user cfg from simply impersonating compiler-owned target facts.

A source audit that wants to cover target-conditioned code must therefore identify the supported target/configuration set, not invent cfg values independently from the compiler invocation.

Basis: **source**.

### `cfg!` does not remove the surrounding syntax

The built-in `cfg!` macro evaluates a configuration predicate to a Boolean literal. It is not the same mechanism as the `#[cfg]` attribute.

For example, an ordinary expression `if cfg!(unix) { A } else { B }` becomes a conditional with a constant Boolean value, but both branches are still Rust syntax presented to later frontend work. A later MIR optimization may remove an unreachable branch, as documented separately in the corpus's MIR report.

By contrast, `#[cfg(unix)] fn f() { ... }` removes the entire item during AST configuration when false.

This distinction matters when interpreting "not present in MIR": absence can arise either from early cfg deletion or from later compiler transformation, and those have different provenance.

Basis: **normative** + **derived** compiler-phase distinction.

### The configured crate is one member of a configuration family

A package with feature, target, test, build-script, or other cfg-dependent source does not have one configuration-independent set of compiler-visible items.

For a precise downstream coverage claim, the compilation subject must identify enough state to reproduce the relevant cfg set. At minimum that can include:

- Cargo unit/package and target;
- enabled Cargo features for that unit;
- host versus target compile kind;
- target triple and target-feature/codegen settings;
- test/proc-macro mode when relevant;
- build-script-emitted cfg values;
- explicit rustc `--cfg` values.

This is a statement about the source-to-compiler boundary. It does not choose how Anneal should encode that identity.

Basis: **derived** from the sources above.

## Boundaries

- No fresh rustc, Cargo, proc-macro, or build-script execution was performed.
- The report is pinned to exact Rust, Rust Reference, and Cargo revisions. It does not infer adjacent-version continuity.
- It does not enumerate every compiler-set cfg key. The exact set is revision- and target-sensitive.
- It does not enumerate every custom cfg emitted by every possible build script; those are build outputs and require the actual build context.
- It does not claim that a cfg-false source file is unreadable by every tool. The claim is that its cfg-false Rust forms are absent from the configured crate's later compiler representations.
- It does not claim that `cfg!` branches survive all the way to final code. Later constant propagation and MIR simplification can remove unreachable code.
- It does not fully specify macro expansion ordering for every macro form. It establishes the cfg/macro relationships needed to understand when AST forms are removed.
- It does not cover rustdoc-specific cfgs, doctest cfgs, Clippy/Miri-specific cfgs, or every frontend wrapper.
- It does not define the complete Rust module/file-identity model; this report covers only the cfg-dependent `path` and module-selection relationship.
- It does not choose an Anneal architecture or coverage schema.

## Evidence

**Normative — Rust Reference.** Repository `rust-lang/reference`, revision `ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/conditional-compilation.md`, blob `c0351610d6d0c495233eb382e97cdb6c5ff3864d`:
  configuration predicates; compiler-set and arbitrary configuration; target cfgs; `cfg`; `cfg_attr`; `cfg!`; crate-level cfg behavior.
- `src/items/modules.md`, blob `3cc015025bab29ec026d2a56538d97051eb6a660`:
  out-of-line module loading and `path` resolution.

The Rust compiler revision records this Reference revision as its `src/doc/reference` submodule.

**Source — rustc.** Repository `rust-lang/rust`, revision `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_expand/src/config.rs`, blob `2b914a2664fe5f398b3597db5f7c4aa8c64dc91e`:
  `StripUnconfigured`, `configure`, `process_cfg_attrs`, `in_cfg`, and configured derive token streams.
- `compiler/rustc_expand/src/expand.rs`, blob `741c34e0304af71c8fbbad394d18809f9126b0df`:
  invocation collection for `cfg`/`cfg_attr`, stripped-item recording, and external-module loading with processed attributes.
- `compiler/rustc_interface/src/passes.rs`, blob `623fb4e2c6dd2ff6731bcfa331827ad0d90563b0`:
  `configure_and_expand`, name resolution after expansion, configured AST storage, and later HIR lowering.
- `compiler/rustc_session/src/config/cfg.rs`, blob `d16ab59a02d9e2691d5eee2dea8ae237a301c466`:
  compiler-owned configuration population and validation of well-known cfg names.

**Source — Cargo.** Repository `rust-lang/cargo`, revision `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`.

- `src/cargo/core/compiler/mod.rs`, blob `746e01d01e256f254481160467b025afc220d2fe`:
  `features_args`; test cfg injection; build-script cfg forwarding to rustc.
- The companion corpus report `cargo-metadata-feature-resolution-2026-05-31` records how unit-level feature sets are resolved before they become these cfg arguments.
- The existing corpus report `generated-rust-visibility-nightly-2026-05-31` records build-script and proc-macro visibility boundaries.
- The existing corpus report `rustc-mir-before-charon-nightly-2026-05-31` records later MIR-phase removal and explains why cfg deletion and MIR unreachable-code elimination must not be conflated.

No evidence in this report is fresh **execution**.

## Revalidation

For another Rust/Cargo pin, the cheapest source check is:

1. Resolve the Rust commit and its exact `src/doc/reference` and Cargo revisions.
2. Re-read the Reference's `cfg`, `cfg_attr`, and module `path` rules.
3. Inspect rustc's cfg-stripping implementation and confirm that cfg-false AST nodes are still removed during expansion before HIR lowering.
4. Inspect module expansion/loading and confirm whether processed `cfg_attr(path = ...)` attributes still select external files.
5. Inspect Cargo rustc command construction and confirm how unit features, test mode, and build-script custom cfg values become rustc arguments.
6. Diff the compiler's well-known cfg population for target/mode changes relevant to the supported configuration matrix.

On an execution-capable surface, preserve one minimal fixture containing:

- mutually exclusive `#[cfg(target_os = ...)]` items;
- `#[cfg(feature = "a")]` and a Cargo feature;
- `#[cfg_attr(..., path = "...")] mod selected;` with two files;
- a build script that emits one custom cfg;
- an `if cfg!(...)` control case;
- one macro that emits a cfg-decorated item.

Compile it for two targets and two feature sets with the exact toolchain. Preserve rustc argv, build-script output, expanded AST/HIR when available, MIR, and Charon output. The decisive observations are which item/module-file identities survive into HIR/MIR and whether the `cfg!` control remains long enough to distinguish early cfg deletion from later MIR simplification.

That experiment establishes the concrete pipeline for the tested configurations. It does not establish coverage of cfg combinations or targets that were not exercised.
