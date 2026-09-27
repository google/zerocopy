# Charon entry-point selection and opacity at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (Charon 0.1.210, the revision pinned by Aeneas `nightly-2026.06.03`), `--start-from` does not mean "translate only these named functions." It seeds a dependency-driven work queue. Each selected item can enqueue types, traits, functions, constants, impls, nested items, and other declarations that its translated representation refers to. Transparent modules additionally enqueue their contents. Opaque bodies and opaque modules stop some of those exploration edges. The resulting closure is therefore determined jointly by entry points, item opacity, and Charon's translation rules, including its demand-driven treatment of trait methods.

`--start-from` accepts Charon name patterns, including globs and a constrained form of trait-implementation pattern. The resolver is stricter than the general name matcher: inherent impl patterns are unsupported; trait impl patterns must be the first path element, cannot specify trait generics, and can select only named self types. Multiple roots can be supplied by repeating the option or by comma-delimiting one option. All roots feed one queue and a `processed` set deduplicates work. However, the exact 0.1.210 source labels path resolution "expensive and should be used sparingly," resolves each root pattern separately, and has no file/response-file input for large root sets. No fresh scaling experiment was available on this surface, so this report does not establish throughput or asymptotic wall-clock behavior for hundreds or thousands of roots.

`--opaque` uses the same general name-pattern machinery as `--include` and `--exclude`. Charon orders matching patterns by specificity; for equally precise patterns, the more opaque setting wins. An opaque function or global retains its name and signature but has no translated body; an opaque type retains its identity/signature but not fields or variants; an opaque module is not traversed, although one of its children can still be reached from elsewhere. Trait declarations and trait impls remain structural declarations, while their method bodies are demand-driven and opacity prevents otherwise eager traversal of provided or implemented methods.

Opacity is not modeling. Charon's `--opaque` records that a body or representation was not translated; it does not attach an Aeneas/Lean model. Aeneas model selection is a later, separate Rust-name-matching mechanism. An Anneal pipeline that treats an opaque Charon declaration as modeled would therefore be conflating two distinct trust boundaries.

The checked-in Charon tests at this exact revision preserve execution evidence for repeated and comma-delimited entry points, glob and trait-impl roots, strict and non-strict root resolution, public-item roots, opaque attributes, opaque enum rejection, and an explicit `--opaque` trait-impl-method case. No fresh Charon, rustc, Aeneas, or Lean execution was performed for this report.

## Applicability

Primary subject:

- repository: `AeneasVerif/charon`
- revision: `a535e914f74db4fd9e6be7048f4233270d8945c0`
- version: `0.1.210`
- selected by: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`)

Current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects that Aeneas release. This report is revision-specific: later Charon releases have continued changing entry-point resolution and filtering behavior.

This report separates three related mechanisms:

1. **entry-point selection** (`--start-from`, `--start-from-if-exists`, `--start-from-attribute`, `--start-from-pub`), which seeds translation;
2. **reachability**, the dependency-driven queue that discovers additional items while translating the selected roots;
3. **opacity** (`--include`, `--opaque`, `--exclude`, source annotations, and the default `Foreign` treatment of dependencies), which controls how much of a reached item is explored.

A name being syntactically selectable does not imply its body will be available, and an item being opaque does not imply it is absent from LLBC.

## Findings

### `--start-from` seeds a work queue; it is not an output whitelist

`CliOpts.start_from` is a `Vec<String>` with comma value delimiters. `TranslateOptions::new` parses each supplied string as a `NamePattern`. If no explicit start mechanism is present, Charon inserts the pattern `crate`, making the current crate module the default root.

At translation time, every start pattern is resolved to one or more rustc `DefId`s. Each resolution is enqueued through `enqueue_module_item`. Charon then repeatedly pops `items_to_translate`; translating one item registers and enqueues the declarations that translation encounters. A `processed` set prevents a declaration source from being translated twice.

The source itself describes this as recursive registration: start from the crate root and "end up exploring the whole crate." The main loop says that an item referring to non-translated items adds those items to the queue.

This is a dependency closure over Charon's translated representation, not merely a function call graph. Types in signatures, trait evidence, constants, impls, vtables, nested declarations, drop machinery, and other translation-time dependencies can join the queue.

Basis: **source**.

### Transparent modules create containment edges; opaque modules cut those edges

Modules and inherent impl blocks are represented as module-like translation sources. `register_module` enqueues their contained items only when the module item's opacity is `Transparent`.

The default current-crate root is transparent, so recursively visiting transparent modules makes the default behavior cover the crate's ordinary top-level item tree. If a module is opaque, its contents are not traversed merely because the module was reached. A child can still be translated if another reached item refers to it directly.

The same principle applies to local items nested in a function body: Charon walks and enqueues nested HIR items only when the containing item is not opaque.

This distinction matters for Anneal. An entry-point set does not define a closed proof boundary unless the corresponding opacity choices and dependency edges are also recorded.

Basis: **source** + **derived** consequence for proof scoping.

### Start patterns use Charon syntax but a specialized rustc resolver

The parser accepts path elements separated by `::`, `_` or `*` globs, generic-pattern syntax, and structured trait-impl syntax. `crate` is a special local-crate name.

For `--start-from`, the parsed pattern then goes through `def_path_def_ids`, which resolves against rustc's crate/item hierarchy. The exact 0.1.210 resolver has important constraints:

- a first path element can name an external crate, `crate`, a primitive type with inherent impls, or a glob;
- a glob path element expands all nameable children at that position;
- a path can resolve to more than one item, including when multiple versions of one crate are present;
- a trait-impl pattern is supported only when it is the first pattern element;
- the impl self type must resolve to a named ADT, or `_` for all implementations;
- trait generics in a start-from impl pattern are rejected;
- inherent impl patterns are rejected;
- later `::{impl ...}` path elements are rejected.

The preserved `start_from_errors` fixture exercises these exact failures, including inherent impls, non-named self types, trait generics, misplaced impl patterns, malformed paths, and missing methods.

Basis: **source** + preserved upstream **execution** artifact.

### Strict and non-strict roots differ only in missing-match handling

Ordinary `--start-from` creates `StartFrom::Pattern { strict: true }`. `--start-from-if-exists` uses the same parser and resolver with `strict: false`.

In strict mode, an empty resolution at a path prefix is an error. In non-strict mode, an absent pattern simply contributes no roots. The checked-in `start-from-if-exists` fixture supplies one nonexistent root and one real root; its expected LLBC contains the real function without an error for the missing one.

This makes `--start-from-if-exists` useful for generated root lists, but it also creates a fail-open risk if Anneal were to use it for a promise-relevant verification scope without separately checking what actually matched.

Basis: **source** + preserved upstream **execution** artifact + **derived** Anneal risk.

### Other root selectors are unions, not replacements with separate closures

`--start-from-attribute` and `--start-from-pub` append additional start selectors to the same `start_from` vector. Attribute and public selectors scan local HIR items, exclude modules themselves, and enqueue matching items into the same queue.

`--start-from-pub` uses Charon's recorded `public` bit, not full Rust API reachability. The source explicitly notes that a `pub` item nested inside a private module still counts as public for this purpose.

A later upstream issue, #1270, reports an execution explicitly performed with Charon 0.1.210 where `--start-from-pub` produced a larger LLBC than default whole-crate extraction for one small example. That report is useful negative evidence against assuming that fewer syntactic roots monotonically imply a smaller serialized result. It is not a general performance result and was not rerun here.

Basis: **source** + preserved upstream issue **execution** report.

### Multiple entry points share one queue, but high-cardinality scaling is not established here

The checked-in tests demonstrate both repeated `--start-from` options and one comma-delimited option containing multiple roots. Internally all resolved `DefId`s enter the same queue, and `processed` deduplicates translation of the same `TransItemSource`.

That establishes functional aggregation and deduplication. It does not establish good performance for large root sets. The resolver's source comment says `def_path_def_ids` is expensive and should be used sparingly, and the translation setup calls it independently for each `StartFrom::Pattern`.

The exact 0.1.210 CLI has no `--start-from-file` or response-file path in `CliOpts`. A later upstream feature request, issue #1020, specifically identifies operating-system command-line length as a concern for very large root lists and requests file-based input. The issue is evidence of an upstream-recognized interface limitation, not an empirical benchmark at this revision.

Basis: **source**, preserved upstream **execution** fixtures, later upstream **documentation/issue**.

### Name patterns are prefix matches; specificity chooses the opacity rule

For opacity filtering, `NamePattern::matches_with_generics` treats a shorter matching pattern as a prefix match. Thus `crate::module` also matches descendants such as `crate::module::f`. Appending `::_` can target descendants without matching the parent itself.

`Pattern::compare` orders longer patterns as more precise; for equal lengths a non-glob final element outranks a glob. `TranslateOptions::opacity_for_name` chooses the maximum matching `(pattern, opacity)` pair. Because `ItemOpacity` is ordered `Transparent < Foreign < Opaque < Invisible`, equally precise conflicting rules resolve toward more opacity.

The baseline rule is `_ -> Foreign` unless `--extract-opaque-bodies` is active, in which case it is `_ -> Transparent`. Charon then adds `crate -> Transparent`, followed by user `--include`, `--opaque`, and `--exclude` rules.

Basis: **source**.

### `--opaque` preserves identity and signature while removing contents

At this revision the opacity lattice is:

- `Transparent`: translate fully;
- `Foreign`: dependency default; functions are effectively opaque, while some type representations can still be translated according to visibility;
- `Opaque`: translate name/signature but not contents;
- `Invisible`: translate nothing for the item.

For functions and global initializers, an opaque item becomes a declaration whose body is `Body::Opaque`. For types, an opaque item becomes `TypeDeclKind::Opaque`, so fields or variants are not available. For modules, opacity prevents traversal of contained items. `Invisible` is stronger: translation returns before retrieving the Hax definition.

Opacity can therefore change whether downstream dependencies are even discovered. A callee reachable only through an opaque function body is not found by traversing that body; a function named elsewhere may still be reached independently.

Basis: **source**.

### Free functions are directly filterable

A free function's translated name can be matched directly by `--opaque crate::path::function`. Once matched as opaque, Charon still translates its generic/signature information but chooses `Body::Opaque` instead of MIR-body translation.

This is a semantic abstraction boundary, not an exclusion boundary. Code that calls the function can still contain a reference to that function declaration.

Basis: **source**.

### Inherent impl blocks are not directly matchable, but inherent methods can be filtered by path shape

The general name matcher has no implementation for `PatElem::Impl` matching an inherent `ImplElem::Ty`; that branch returns false. The checked-in usage documentation therefore recommends patterns such as `crate::module::_::method` when filtering inherent methods.

The start-from resolver is even more explicit: `{impl Type}` patterns are rejected with ``--start-from` does not support inherent impls`.

For opacity, the practical unit is the method item, not the inherent impl block. A sufficiently broad prefix or wildcard method pattern can make those function items opaque even though the impl block itself cannot be named by impl-pattern syntax.

Basis: **source** + upstream **documentation** + preserved upstream **execution** error fixture.

### Trait impl filtering targets associated items rather than making the impl disappear

The CLI help at this revision warns that it is not possible to filter a trait impl itself; pattern filtering applies to its methods. The name matcher does understand trait-impl path elements and treats a pattern beginning with an impl as matching the rightmost trait impl in a translated name. This lets a pattern such as `{impl Trait for Type}` act as a prefix for associated items under that impl.

The preserved `issue-114-opaque-bodies` fixture passes `--opaque={impl core::marker::Destruct for alloc::vec::Vec}`. Its expected LLBC still contains the trait/impl structure, while the selected `drop_in_place` function is emitted with an opaque body.

Trait translation is also demand-driven. Charon normally avoids translating unused provided methods; a transparent trait or impl can cause methods to be marked used eagerly, whereas an opaque one does not. Required or otherwise used methods can still appear.

Basis: **source** + preserved upstream **execution** artifact.

### Source annotations can only strengthen opacity relative to CLI matching

`#[charon::opaque]`, `#[aeneas::opaque]`, and `#[verify::opaque]` are parsed as opaque source annotations. `translate_item_meta` takes the maximum of annotation-imposed opacity and name-pattern opacity. `exclude` similarly forces at least `Invisible`.

Consequently, a more specific `--include` cannot make a source-annotated opaque item transparent. The upstream documentation states this explicitly.

A module annotation differs from a CLI prefix pattern: `#[charon::opaque]` applies to the module item itself, not automatically to each child. A child reached from elsewhere retains its own opacity. In contrast, `--opaque crate::module` prefix-matches both the module and descendants unless a more precise pattern overrides them.

The checked-in `opaque_attribute` fixture preserves this distinction: an opaque module is not traversed to find an otherwise-unused child, but a called child function is still translated because its own item is transparent.

Basis: **source**, upstream **documentation**, preserved upstream **execution** artifact.

### External functions and external types react differently to `--opaque`

Without `--extract-opaque-bodies`, Charon's fallback opacity is `Foreign`. For functions, `Foreign` is effectively the same as `Opaque`: only the declaration/signature is retained. Applying `--opaque` to such a function may therefore make no additional body disappear.

For types the distinction matters. `Foreign` can still expose an enum or a struct with public fields, whereas `Opaque` hides fields and variants. The preserved `match_on_opaque_enum` fixture shows the consequence for a current-crate enum: after `--opaque crate::Enum`, matching on its discriminant fails translation because the enum representation is unavailable. The same representation distinction is relevant when deliberately making a foreign type opaque.

`--extract-opaque-bodies` changes the fallback `_` rule to `Transparent`; explicit more-precise `--opaque` patterns can still carve selected abstractions back out.

Basis: **source** + preserved upstream **execution** artifact.

### Charon opacity and Aeneas models are separate mechanisms

Nothing in Charon's `--opaque` handling binds an item to a Lean model. The Charon result records an opaque body or opaque type representation under the item's Rust-derived identity.

At the next stage, Aeneas may separately recognize that identity in its external-model registry and redirect it to a backend definition. If no model matches, an opaque declaration remains an external/assumption obligation rather than acquiring semantics merely because it was marked opaque.

For the pinned Aeneas mechanism and its trust boundary, see `reports/aeneas-external-models-nightly-2026-06-03/` in this corpus. For Anneal, the important invariant is that "opaque in Charon" and "semantically modeled downstream" must remain distinguishable in any promise-relevant scope or trust report.

Basis: Charon **source** + **derived** pipeline distinction; downstream model mechanics are covered separately.

## Boundaries

- No fresh Charon, rustc, Cargo, Aeneas, or Lean execution was performed.
- Checked-in `.out` fixtures are preserved upstream execution artifacts from the exact Charon revision. They demonstrate the cases encoded by those fixtures but are not fresh environment-independent reruns.
- No empirical benchmark measured translation time, memory, output size, or command-line limits as the number of `--start-from` roots grows. The source-level architecture and upstream issue #1020 establish a scaling concern and missing file-based input, not a performance curve. This missing experiment is material to the "many-entry-point scaling" part of the #3720 `--start-from` inventory item.
- Upstream issue #1270 is a reporter's preserved 0.1.210 execution result. This report does not independently reproduce it or generalize its larger-output observation to arbitrary crates.
- The report does not claim that Charon's dependency closure is a semantic program slice. It is the set induced by Charon's translation and registration behavior, which includes compiler/translation artifacts and lazy trait-method rules.
- The report does not prove that every Rust item kind is selectable by `--start-from`; the resolver explicitly rejects or skips several kinds, and unsupported-language coverage is inventoried separately.
- The report does not evaluate the semantic correctness of an Aeneas model for an opaque declaration. Charon opacity alone provides no such correctness argument.
- The report does not establish current behavior of later Charon versions. In particular, later fixes or regressions around inherent methods, trait impls, attributes, or response-file support must be rechecked at their own revisions.
- No Anneal architecture choice is inferred. The durable constraint is only that verification scope and trust accounting cannot collapse entry-point selection, reached closure, Charon opacity, and downstream modeling into one undifferentiated notion.

## Evidence

**Source — Charon 0.1.210.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: CLI fields; default `crate` root; strict/non-strict roots; opacity rule construction; pattern precedence.
- `charon/src/name_matcher/mod.rs`, blob `17d2683ee660595a75a56104c61d3ab162f54a6c`: prefix matching, impl matching, specificity ordering, inherent-impl limitation.
- `charon/src/name_matcher/parser.rs`, blob `fc5f292ba4f7038190c168070f5a3bf40d1f9014`: pattern grammar.
- `charon/src/bin/charon-driver/translate/resolve_path.rs`, blob `b091bf23f897cee6b84e0136b41426a7de9d91f2`: `--start-from` rustc resolution, multi-resolution behavior, strict failures, trait-impl constraints, "expensive and should be used sparingly" comment.
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: root enqueueing, queue/processed-set fixed point.
- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: item opacity application, module traversal, nested-item discovery, function/type opaque bodies, lazy trait methods.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`: source attributes and opacity combination.
- `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`: `ItemOpacity` semantics and ordering.

**Documentation — same revision.** `docs/what_charon_translates.md`, blob `780949ef1304a89e34c87b04958d65dbc3bf0810`: item-selection model, opacity/reachability distinction, pattern examples, source-annotation scope.

**Preserved execution fixtures — same revision.** The following checked-in source/output pairs were inspected; none were rerun:

- repeated/glob/trait-impl roots: `start_from.rs` blob `7b1d8b98c4918c6b091c448caac660cf7ccfb6ca`, output `d643755caf24befb41d0357ee1001b3f683505dd`;
- resolver failures: `start_from_errors.rs` blob `aecac45c05b58c3b521a19e0eaa2938a848c9779`, output `86ed12614ddb23d6eaba12266dd71154b1d1cb31`;
- optional roots: `start-from-if-exists.rs` blob `d55041495823aa2b11f028cdd65cbb9059ecb295`, output `a2b4de68cea3772348b2fb7e0758d1dd80aa8449`;
- public roots: `start_from_pub.rs` blob `7e22da0375df43d7a5871fb52223321320e3f4a2`, output `85327d35d3bf512af881574ba52369148aa11bb8`;
- comma-delimited roots: `comma-delimited-start-from.rs` blob `ae96633334ef5c48ada639ede7b548022964c4cb`, output `899c645976adc5176126d402bd7b37372959df18`;
- opaque source annotations/module reachability: `opaque_attribute.rs` blob `d69ad26b35289697732534343604e4712abdacf4`, output `9d25497b70aad9abb11206a8f1fa850a9497a430`;
- opaque-enum rejection: `match_on_opaque_enum.rs` blob `2f38d8122c95c09bedfe8ca35f968212988456ec`, output `33aef9c93a2462abc44966534a9dc36d97b57a7b`;
- CLI trait-impl opacity: `issue-114-opaque-bodies.rs` blob `6c6c094220e37b17a5a60d13307816757e6441a1`, output `89ea5450be1172432a167391c5cdf7a03a99f6e0`.

**Upstream issues.** These are contextual evidence, not normative behavior:

- AeneasVerif/charon#1020, "Allow passing `--start-from` arguments via file": later request documenting the high-cardinality CLI-input concern.
- AeneasVerif/charon#1270, "Unexpected behaviour concerning traits when using -start-from-pub": reporter states the shown result was tested on Charon 0.1.210.
- AeneasVerif/charon#956, "Support trait implementations in `--start-from`": historical request whose broad limitation is superseded at this revision by the constrained impl support visible in source/tests; it is useful history, not current-state authority.

## Revalidation

For a future Charon revision, first diff the smallest source surface that defines this behavior:

1. `CliOpts` and `TranslateOptions::new` in `charon/src/options.rs`;
2. `name_matcher::{parser, Pattern::matches, Pattern::compare}`;
3. `translate/resolve_path.rs`;
4. root setup and the work-queue loop in `translate_crate.rs`;
5. `translate_item_aux`, `register_module`, and trait-method enqueue rules in `translate_items.rs`;
6. `ItemOpacity` and source-annotation handling.

Then rerun the upstream filtering fixtures and compare their `.out` files.

On a surface with the exact Charon toolchain, add one bounded scaling experiment before considering the #3720 `--start-from` inventory item fully empirical. Generate a crate with at least 2,000 independently nameable leaf functions plus shared dependencies. Run the same pinned Charon configuration with 1, 10, 100, 500, 1,000, and 2,000 roots, using both repeated options and comma-delimited batches. Record command-line byte length, root-resolution time if trace spans expose it, total translation wall time, peak memory, and final LLBC item count. Repeat with highly overlapping roots to separate resolver cost from translation deduplication. Also test the platform's failure point for argument length and whether any response-file/file-list syntax exists at that future revision.

For opacity, use a small crate containing: a free function, an inherent method, a trait with a provided method, a trait impl, an enum, an opaque module with a child called from outside, and one external dependency type/function. Run a matrix of `--include`, `--opaque`, `--exclude`, source `#[charon::opaque]`, and `--extract-opaque-bodies`. Record which declarations exist, which bodies/fields are present, and which downstream dependencies enter the queue. Include one Aeneas model for an opaque external function and one unmodeled opaque function; confirm downstream that model selection is separate from Charon opacity.

Those experiments would establish current runtime behavior and scaling. They still would not prove that an Aeneas model is semantically faithful to Rust; that remains a separate trust argument.
