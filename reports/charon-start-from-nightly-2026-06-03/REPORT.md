# Charon `--start-from` selection and reachability at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (Charon 0.1.210), `--start-from` changes the **entry points** of Charon's translation, not the opacity policy of the selected items and not merely the set of names printed at the end. Charon resolves each configured start pattern to compiler definitions, enqueues those definitions, and then performs the same dependency-driven translation used by the default whole-crate entry point. While translating a transparent item, references to new items enqueue those dependencies. Opaque/foreign items expose less structure, so dependencies reachable only through an unexamined body do not enter the queue.

When no explicit start mode is configured, Charon inserts the pattern `crate` as a strict entry point. Because the current crate is a transparent module by default, module traversal reaches all of its direct items and recursively explores transparent submodules. A custom `--start-from` therefore changes the coverage model materially: it can select one function, module, method, foreign definition, or pattern family and translate only the dependency closure induced by that selection under the active opacity rules.

The option has several distinct variants. `--start-from` uses a strict pattern: a parse or resolution failure is an error. `--start-from-if-exists` uses the same pattern machinery but suppresses the missing-match error, making a stale generated selector non-fatal. `--start-from-attribute[=<ATTR>]` enumerates local HIR definitions with a matching attribute, excluding modules. `--start-from-pub` enumerates local non-module definitions whose rustc visibility is public; the internal `StartFrom::Pub` contract explicitly notes that this is based on the item's own `pub` visibility and does not require effective external accessibility or re-export.

Start patterns use Charon's name matcher rather than Rust source-path syntax. Checked-in tests at this exact revision preserve successful examples for crate modules, glob path elements, standard-library functions/methods, primitive-type methods, and trait-impl method patterns. They also preserve rejection boundaries: some Rust-like spellings are not accepted; inherent impl patterns are unsupported; impl matching is restricted to named self types; trait-generics in impl patterns are unsupported; impl patterns must occur at the beginning of the pattern; and a pattern that resolves to an associated type can still fail because that item kind is not registerable as a translation root.

Charon applies a second reachability computation late in the transformation pipeline. `reorder_decls` seeds a dependency graph from translated items that still match the configured `StartFrom` predicates, then traverses dependencies in the transformed AST. Its source comment states why: most inaccessible items were already avoided during translation, but later passes can render items inaccessible again. Final ordered declarations are built from this graph. Thus the selected result is shaped by both the rustc-facing work queue and a post-transformation dependency closure.

No fresh Charon/rustc execution was performed. The report uses the exact pinned source, checked-in upstream documentation, help output, and checked-in golden UI outputs. Those golden outputs are preserved historical execution evidence from the Charon repository; they are not fresh execution on this surface.

## Applicability

This report applies to:

- repository: `AeneasVerif/charon`;
- revision: `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon version: `0.1.210`;
- embedded Rust toolchain: `nightly-2026-05-31`.

It covers the entry-point options:

- `--start-from`;
- `--start-from-if-exists`;
- `--start-from-attribute`;
- `--start-from-pub`;

and their interaction with item opacity, dependency-driven translation, pattern resolution, and final declaration reachability.

It does not characterize the performance of thousands of start patterns, the scaling behavior of large workspaces, or the exact observed output of new fixtures run on this surface. Those are empirical questions. It also does not fully specify `--opaque`, `--include`, and `--exclude`; this report records only the opacity facts needed to explain what a start-point closure means. A dedicated opacity report remains useful.

The default whole-crate case is a special case of the same model: if no start selector is supplied, `TranslateOptions::new` inserts a strict `crate` pattern.

## Findings

### Start selection is a distinct concept from opacity

`CliOpts` documents `--start-from` as a list of item paths used as starting points: Charon translates those items and the items they refer to according to the opacity rules. `TranslateOptions` stores this as a vector of `StartFrom` predicates. Opacity is stored separately as name-pattern-to-`ItemOpacity` rules.

This separation is semantically important. Choosing an item as an entry point does not make it transparent. An entry point that is opaque or foreign is translated only to the extent its own opacity allows; dependencies visible only inside an unexamined body are not discovered through that path.

Conversely, making an item transparent does not make it reachable if no selected entry point or translated dependency leads to it.

Basis: Charon **source** + upstream **documentation**.

### The default is an explicit strict `crate` start pattern

`TranslateOptions::new` collects explicit `start_from`, `start_from_if_exists`, attribute, and public-item selectors. Only when the resulting vector is empty does it insert:

`StartFrom::Pattern { pattern: "crate", strict: true }`.

The default whole-current-crate translation is therefore implemented through the same start-point abstraction as custom selection rather than through an independent traversal mode.

Because the item-opacity table always makes `crate` transparent, processing the current-crate module explores its contents under the normal module rule.

Basis: Charon **source**.

### `--start-from` and `--start-from-if-exists` differ only in strictness after parsing

Both CLI lists are parsed with `NamePattern::parse` and converted to `StartFrom::Pattern`. Explicit `--start-from` uses `strict: true`; `--start-from-if-exists` uses `strict: false`.

The help text gives the intended use for the non-strict form: selectors generated by build scripts can become out of sync with the source, and a missing match should not by itself make translation fail.

This distinction concerns failure on an unmatched selector. It does not create a different dependency-closure algorithm for matched roots.

Basis: Charon **source** + checked-in help **documentation**.

### Parse failures are still option errors

`TranslateOptions::new` parses each supplied pattern before it becomes a `StartFrom`. If `NamePattern::parse` fails, Charon registers an error. The checked-in `start_from_errors.out` preserves a concrete malformed-pattern error for `std::iter:once`.

`--start-from-if-exists` is therefore not a general “ignore malformed selectors” mode. Its non-strictness concerns resolution/matching, not arbitrary parser failures.

Basis: Charon **source** + preserved upstream **execution** artifact.

### Explicit pattern roots are resolved before translation begins

For each `StartFrom::Pattern`, `translate_crate::translate` calls `ctx.resolve_path(..., &pattern, strict)`. Each resolved definition is converted to Charon's hax `DefId` form and passed to `enqueue_module_item`.

Errors discovered while resolving/parsing start selectors cause translation to stop before the main item work queue runs: after seeding start roots, the function tests the shared error context and returns an error if start processing produced errors.

A successful selector therefore creates concrete compiler-definition roots; it is not merely a string filter applied to already-translated output.

Basis: Charon **source**.

### Translation expands from roots through a work queue

The translation context starts with an empty `items_to_translate` queue and `processed` set. After start roots are enqueued, `translate_crate::translate` repeatedly pops one item. If that `TransItemSource` has not already been processed, it translates the item. Translation of an item can discover referenced definitions and add them to the same queue.

The source explicitly states that translation order does not matter for semantic lookup because Charon allocates translated IDs without requiring the referred-to definition to have already been translated.

The resulting set is therefore dependency-driven and deduplicated by translated item source.

Basis: Charon **source**.

### Module roots produce structural traversal

Pinned documentation defines a transparent module as an item whose direct contents are enqueued. A non-transparent module does not explore its contents. This is why the default transparent `crate` root reaches the current crate independently of call-graph reachability.

A custom module root behaves the same way: selecting a module does not mean “translate only functions dynamically callable from this module”; it means start with that module, then use normal transparent-module traversal plus dependency discovery.

Basis: upstream **documentation** + Charon **source** architecture.

### Non-module roots follow semantic references rather than source adjacency

For a transparent function/type/global/trait/impl selected as a root, Charon translates the item's represented contents and queues new referenced items encountered during translation.

Source-neighboring declarations that are not referenced and are not under a selected transparent module need not enter the translation. The checked-in `start_from.rs` fixture demonstrates this boundary: `dont_translate` and unrelated definitions are absent, while explicitly selected modules/methods/glob matches appear.

Basis: **source** + preserved upstream **execution** artifact.

### Opacity truncates the reachable closure

Pinned `what_charon_translates.md` states the rule directly:

- transparent non-module items are fully translated;
- foreign/opaque non-module items expose signatures rather than bodies;
- invisible items are not translated;
- opaque/non-transparent modules are not explored.

Therefore an item reachable only by reading the body of an opaque function is not queued through that function. An item referenced from an opaque function's signature can still be required by signature translation.

This is why `--start-from` cannot be interpreted independently from the active opacity configuration.

Basis: upstream **documentation** + **source**.

### Current-crate transparency does not imply whole-crate reachability under custom roots

The opacity table gives `crate` and current-crate descendants transparent treatment by default, but reachability remains separate. A transparent local function that is not selected and not referenced from any reached item can remain absent when a custom non-module root is used.

The default `crate` root makes the ordinary whole-crate case broad because it structurally explores modules. Replacing that default with a custom root removes that structural entry unless `crate` is also supplied.

The FAQ/docs wording preserved in this revision's source describes the same operational idea: to retain the whole current crate while adding a foreign or narrow root, include `--start-from=crate` as another start selector.

Basis: **source** + upstream **documentation**.

### Multiple roots form a union before dependency exploration

`TranslateOptions.start_from` is a vector. `translate_crate::translate` iterates every selector and enqueues every resulting root before running the main queue.

The selected translation is therefore the union of each root's reachable dependency closure under one shared opacity configuration. There is no per-root isolated result or per-root opacity environment.

Basis: Charon **source**.

### Start patterns can match more than one item

The option is parsed as a `NamePattern`, and `resolve_path` returns a collection of definitions. Checked-in tests use patterns such as `crate::*::do_translate_glob` and trait-impl patterns that resolve multiple relevant items.

A start selector is therefore not necessarily a unique-item identifier. Any consumer that wants one exact root must use a sufficiently discriminating pattern and account for the name matcher's supported syntax.

Basis: Charon **source** + preserved upstream **execution** artifact.

### Pinned tests preserve several successful pattern forms

`charon/tests/ui/filtering/start_from.rs` records start arguments for:

- `crate::module1`;
- `test_crate::module2`;
- `std::iter::once`;
- `std::clone::Clone::clone_from`;
- `std::slice::Iter::as_slice`;
- `u32::wrapping_add`;
- `crate::*::do_translate_glob`;
- a specific trait-impl method;
- a trait-impl pattern with a wildcard self type.

The matching `.out` file records the current-crate/module/glob/impl declarations retained in final LLBC. These files are useful golden evidence of selector forms accepted by the repository's own test suite at the pinned commit.

They do not prove adjacent revisions accept the same grammar.

Basis: preserved upstream **execution** artifacts.

### Pinned tests also preserve important resolver limitations

`start_from_errors.rs` / `.out` records the following boundaries at the examined revision:

- a malformed path such as `std::iter:once` fails parsing;
- unrooted local spellings such as `module2` fail resolution and suggest `crate::module2`;
- an associated type root can resolve far enough to fail later because `AssocTy` is not a registerable root kind;
- inherent impl roots are unsupported;
- impl roots require named self types;
- trait generics in an impl selector are unsupported;
- a missing method below an impl fails resolution;
- impl-pattern syntax is only supported as the first path element.

These are not merely display quirks. They restrict which Rust semantic objects can be expressed directly as `--start-from` roots.

Basis: preserved upstream **execution** artifact + resolver **source**.

### Inner items are addressable through Charon's structural name matcher

The checked-in `inner-items.rs` fixture supplies selectors including `crate::_::bar` and module roots around nested functions, trait definitions, impls, anonymous const-contained functions, and functions nested inside other function bodies.

Combined with the separate local/nested-item report, this shows the intended selector namespace is Charon/compiler structural identity rather than only canonical Rust source paths.

This report does not claim that every anonymous compiler definition has a stable or ergonomic selector across edits; anonymous path components can be implementation-sensitive.

Basis: preserved upstream test **source** + existing corpus **derived** context.

### Attribute-based roots scan all local HIR definitions but skip modules

For `StartFrom::Attribute`, Charon splits the configured attribute path, enumerates `tcx.hir_crate_items(()).definitions()`, converts each local definition to the hax ID representation, and enqueues it if:

1. the definition is not a module; and
2. one rustc attribute path matches the requested path.

The CLI default attribute name is `verify::start_from`.

The pinned `start_from_attribute.rs` test specifically annotates a module with `#[verify::start_from]` and comments that it “does nothing”; the code also explicitly rejects module roots in this attribute selection path.

Basis: Charon **source** + preserved upstream test **source**.

### Public-item roots use definition visibility, not effective exported reachability

`StartFrom::Pub` enumerates the same local HIR definition set, skips modules, and enqueues definitions whose hax/rustc visibility query returns `Some(true)`.

The `StartFrom::Pub` enum documentation adds a subtle but important qualification: it does not take accessibility into account; a non-reexported `pub` item is included.

Therefore `--start-from-pub` means “local definitions declared public according to this compiler-facing visibility test,” not “the externally nameable public API surface of the crate.”

Basis: Charon **source**.

### `StartFrom::matches` is reused after translation

A `StartFrom` also implements matching against translated `ItemMeta`:

- pattern roots use the same name pattern;
- attribute roots search translated unknown attributes for the exact configured path string;
- public roots test `item_meta.attr_info.public`.

That predicate is used by the late declaration-reordering pass to seed a new dependency graph.

Basis: Charon **source**.

### Final declaration reachability is recomputed after transformations

`compute_declarations_graph` in `reorder_decls.rs` does not simply retain every item that happened to be translated earlier. It starts from translated items matching any configured `StartFrom`, then traverses dependencies represented in the transformed Charon AST.

The source comment explains the need: Charon has “mostly only translated items accessible” from the roots, but some transformation passes can make items inaccessible again, so this pass filters them out.

Final ordered declaration groups are computed from strongly connected components of this dependency graph.

The published result is consequently a post-transformation reachable closure, not a raw dump of every definition touched by the rustc-facing translation work queue.

Basis: Charon **source**.

### Trait declarations have special dependency treatment during final reachability

The final dependency visitor deliberately treats trait declarations differently. It visits generics, parent clauses, associated types/vtable information, and method/const signatures, but it does not automatically traverse default method/const bodies merely because they are members of the trait declaration. It records their item IDs as reachable while treating actual body inclusion under separate rules.

This aligns with Charon's broader provided-method policy and prevents “selected trait declaration” from being equated mechanically with “all default implementation bodies are necessarily retained.”

Basis: Charon **source**.

### Start selection is not a source-coverage proof

A successful `--start-from` selection proves that Charon resolved the supplied selectors and produced a dependency closure according to its representation and opacity rules. It does not prove:

- that rustc lowered every source fragment the user considers semantically relevant;
- that Charon supports every Rust construct encountered;
- that generated/build-time/native behavior outside the selected compiler representation is covered;
- that a pattern names exactly one semantic item unless its match set is separately established;
- that an opaque boundary hides no behavior relevant to a stronger Rust-level promise.

For Anneal, `--start-from` can be useful machinery for a bounded subject only when the verification subject and the closure semantics are accounted for explicitly.

Basis: **derived** from the source model and Anneal's current design constraints.

## Boundaries

- No fresh Charon or rustc execution was performed.
- The checked-in `.out` files are upstream preserved execution evidence; this report did not regenerate them.
- The report does not benchmark many-root scaling or large dependency closures.
- It does not establish output determinism across repeated runs.
- It does not fully specify the Charon name-matcher grammar; it records the parts needed for `--start-from` and the pinned tests' accepted/rejected forms.
- It does not establish source-level refactoring stability of anonymous/local item selectors.
- It does not characterize `--opaque` comprehensively; opacity is included only to define the reachable-closure semantics.
- It does not claim `--start-from-pub` equals Rust's externally reachable API.
- It does not claim a successful root resolution implies successful semantic translation of every reached item; unsupported/failure behavior is covered by the existing Charon support/failure report.
- It does not establish that selecting a function captures behaviors already removed by rustc MIR construction or excluded from Charon's model.
- The exact behavior of pattern syntax may change across Charon revisions; adjacent-version continuity is not assumed.

## Evidence

**Documentation and source:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `docs/what_charon_translates.md`, blob `780949ef1304a89e34c87b04958d65dbc3bf0810`: item/opacity model, dependency-driven selection process, reachability versus opacity, entry-point options, pattern syntax and precedence.
- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: CLI fields, `StartFrom`, strict/non-strict patterns, default `crate` insertion, public/attribute selectors, opacity table.
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: root resolution/enqueueing, attribute/public HIR scans, error gate, work queue, processed-set deduplication.
- `charon/src/bin/charon-driver/translate/resolve_path.rs`, blob `b091bf23f897cee6b84e0136b41426a7de9d91f2`: compiler-path and impl-pattern resolution, including restrictions preserved by the UI failures.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`: attribute translation and module restriction for the `start_from` attribute family.
- `charon/src/transform/add_missing_info/reorder_decls.rs`, blob `256a7143194c31b22fb2809637d3991253f5d3ae`: late root reseeding, dependency graph, transformed-AST reachability filtering, SCC declaration ordering.
- `charon/tests/help-output.txt`, blob `dd724b5aa48efaee9a36fb29159a9956d31e4a9b`: generated CLI contract at the pinned source.
- `charon/tests/ui/filtering/start_from.rs`, blob `7b1d8b98c4918c6b091c448caac660cf7ccfb6ca`, and `start_from.out`, blob `d643755caf24befb41d0357ee1001b3f683505dd`: successful selector forms and retained declarations.
- `charon/tests/ui/filtering/start_from_errors.rs`, blob `aecac45c05b58c3b521a19e0eaa2938a848c9779`, and `start_from_errors.out`, blob `86ed12614ddb23d6eaba12266dd71154b1d1cb31`: parser/resolver/item-kind limitations.
- `charon/tests/ui/filtering/start-from-if-exists.rs`, blob `d55041495823aa2b11f028cdd65cbb9059ecb295`: non-strict missing-root fixture.
- `charon/tests/ui/filtering/start_from_pub.rs`, blob `7e22da0375df43d7a5871fb52223321320e3f4a2`: public-root fixture.
- `charon/tests/ui/filtering/start_from_attribute.rs`, blob `41000f22198cbd4086d4eb2614f354fa5197d81e`: attribute-root fixture and module exclusion.
- `charon/tests/ui/filtering/inner-items.rs`, blob `bc5779ce4a02f3b53c381178e869e2a7584e4d12`: local/nested structural selector fixture.

No evidence above is fresh **execution**.

## Revalidation

For another Charon revision, first diff:

1. `CliOpts` and `TranslateOptions::new` in `charon/src/options.rs`;
2. `StartFrom` and `StartFrom::matches`;
3. root seeding and the translation work queue in `translate_crate.rs`;
4. `resolve_path.rs` and the name-matcher implementation;
5. item-opacity construction;
6. `reorder_decls.rs` final root/dependency computation;
7. filtering/start-from UI tests and generated help output.

On a capable surface, run a compact golden matrix at the exact revision:

- no explicit selector, confirming default `crate`;
- one function root with an unrelated local function;
- one module root with reachable and unreachable calls;
- one opaque callee whose body alone references another function;
- two explicit roots whose closures overlap;
- a strict missing pattern and the same pattern through `--start-from-if-exists`;
- one `verify::start_from` attribute on a function and on a module;
- `--start-from-pub` with a `pub` item in a private module that is not re-exported;
- one glob pattern matching several roots;
- one inner/local item selector;
- accepted and rejected impl patterns from the pinned UI tests.

Preserve the exact CLI, Charon/rustc revisions, resulting ULLBC/LLBC, stderr, and output hashes. Compare the emitted declaration set against the expected dependency closure.

That experiment confirms concrete behavior for the revision and detects name-matcher or transformation regressions. It does not by itself prove that the resulting closure is sufficient for an Anneal verification promise; that requires the higher-level subject/coverage argument.
