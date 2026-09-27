# Rust item names and namespaces in Aeneas-generated Lean

## Summary

At Aeneas `nightly-2026.06.03`, generated Lean names are derived from Charon item identity rather than from source spelling alone. For an ordinary local item, Aeneas removes the leading local-crate component, simplifies the remaining Charon name, and joins its components with `.` for Lean. The generated file normally opens one outer namespace equal to the raw Rust crate name; `-namespace` can replace that outer namespace. Thus a local Rust item such as `crate::m::f` normally appears as `m.f` inside `namespace crate`, while an external name retains its crate component, as in `core.option.Option`.

Nested Rust modules therefore become components of Lean declaration names, not necessarily nested `namespace` commands. Output-file/module naming is a separate layer: Lean split-file paths use a CamelCase file basename and optional `-subdir`, while the semantic outer namespace still comes from the Rust crate name unless overridden.

Several item classes deliberately depart from the ordinary path rule. Trait implementations synthesize names from the self type, `Insts`, and the implemented trait plus relevant concrete generic arguments. Trait-implementation methods live below that synthesized impl name. Default trait methods add `.default`; extracted loop helpers add `_loop` and Lean loop bodies add `.body`. Renames can replace item names, and inherent methods that would collide with record-field projectors can gain an `impl` path component. These transformations are part of Aeneas's generated API and should not be reconstructed from Rust source with a single string substitution.

Basis: source + checked-in generated fixtures.

## Applicability

This report applies to the Lean backend at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the Aeneas release selected by Anneal, interpreting item names supplied by its paired Charon revision `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

The findings describe non-builtin declarations that survive Aeneas translation plus the special trait/impl/helper cases called out below. Builtin and modeled external definitions can have table-driven Lean names instead of a mechanical source-path spelling. Aeneas also transforms the program before extraction, so not every Rust source item necessarily corresponds to a standalone Lean declaration.

The checked-in Lean fixtures are source evidence preserved in the same Aeneas revision, not fresh execution performed for this report. Where the implementation source and a checked-in fixture expose different layers of the behavior, the report states both rather than treating the fixture as a normative naming specification.

## Findings

### The outer Lean namespace is the Rust crate name by default

`Translate.ml` chooses the extraction namespace from `Config.namespace` when the user supplied one; otherwise the Lean backend uses `crate.name` directly. `extract_file` then emits `namespace <namespace>` when the generated file is configured to be inside that namespace. `Config.ml` documents `-namespace` as the override.

This namespace is distinct from the generated Lean module/file name. `Translate.ml` derives a CamelCase `crate_name` from the `.llbc` filename for output-file and import naming. With `-split-files`, Lean output is divided into files such as `Types.lean` and `Funs.lean` under the selected destination/subdirectory; `-subdir` contributes to import paths. Those choices do not replace the default semantic namespace, which remains the raw Rust crate name unless `-namespace` is set.

The checked-in `tests/lean/Names.lean` illustrates the distinction: the Rust test crate `names` is emitted inside `namespace names`, while the generated file itself is `Names.lean`.

Basis: source + checked-in generated fixture.

### Ordinary local item paths become dot-qualified names relative to that namespace

`ExtractBase.ctx_prepare_name` recognizes the leading `PeIdent` that names the local crate and removes it when it equals `ctx.crate.name`. External names do not take this local-crate stripping path. `ctx_compute_simple_name` then feeds the remaining Charon name through `ExtractName.name_to_simple_name`, and Lean's `flatten_name` joins the resulting components with `.`.

For ordinary identifier path components, the practical mapping is therefore:

```text
Rust/Charon local item:    crate :: module :: item
Aeneas declaration name:          module . item
Generated outer namespace: crate
Fully qualified Lean name: crate.module.item
```

A checked-in nested-module fixture makes this concrete. Rust definitions under `mod ExpandSimpliy` become `ExpandSimpliy.Wrapper` and `ExpandSimpliy.check_expand_simplify_symb1` inside `namespace no_nested_borrows`. By contrast, references to external definitions retain the external crate path; the trait fixture contains names such as `core.option.Option.Insts.TraitsBoolTrait`.

The transformation operates on Charon's structured item name, not a textual `::` replacement. `ExtractName.ml` simplifies implementation/type-expression name elements and generic arguments before flattening. In particular, generic arguments that are only variables are omitted from some synthesized name components, while concrete type/literal arguments can contribute to synthesized impl names.

Basis: source + checked-in generated fixtures.

### Types, variants, fields, and constructors use Lean-specific naming rules

For ordinary local types, `ctx_compute_type_name_no_suffix` applies any item rename and then uses the same simplified dot-qualified name. Unlike some other backends, Lean adds no `_t` suffix.

The Lean backend sets `record_fields_short_names := true`. Named record fields therefore keep their short field name rather than being prefixed with the record type. Unnamed fields, when Aeneas needs field names rather than a tuple representation, use an underscore plus their field index. The checked-in trait fixture shows structures such as `Wrapper` with field `x` and `Foo` with fields `x` and `y`.

For enum variants, Lean returns the variant name directly rather than concatenating the type name into the spelling. Lean's own inductive namespace supplies qualification when a constructor is referenced. Explicit variant renames replace the variant spelling; `RenameAttribute.lean`, for example, emits `VariantsTest.Variant1` conceptually from an enum renamed `VariantsTest` and its first variant renamed `Variant1`.

Structure constructors are derived as `<generated-type-name>.mk`.

Basis: source + checked-in generated fixtures.

### Function names preserve path structure but add helper suffixes where translation needs them

For an ordinary non-trait-impl function, `ctx_compute_fun_global_name_no_suffix` applies an item rename, otherwise retains the simplified Charon path. `ctx_compute_fun_name` then adds translation-generated suffixes when the function represents a loop/helper declaration.

For loops, a function containing one extracted loop uses `_loop`; multiple loops use `_loop<index>` components derived from the loop position. A Lean loop-body declaration adds `.body`. `RenameAttribute.lean` demonstrates the exact family for a renamed Rust function `No_borrows_sum`: `No_borrows_sum`, `No_borrows_sum_loop`, and `No_borrows_sum_loop.body`.

A provided/default trait method is another special case. Aeneas appends `default` to the declaration path for the generated implementation of the default body. `Traits.lean` contains `BoolTrait.ret_true.default`. Renames act locally rather than as a global textual rewrite of all enclosing name components: the checked-in rename fixture renames the trait itself to `BoolTest` and the provided method to `retTest`, while its default body is emitted as `BoolTrait.retTest.default`.

Current checked-in Lean examples also show that mutable-borrow "backward" behavior is often merged into a returned local closure rather than materialized as a separate top-level `_back` declaration. For example, `choose` and `list_nth_mut` return updater functions. A caller should therefore not infer a universal top-level backward-function naming suffix from the Rust function name.

Basis: source + checked-in generated fixtures.

### Trait implementation names are synthesized, not copied from the Rust impl location

`ctx_compute_trait_impl_name_raw` derives an unrenamed implementation name from the implemented self type and trait. For a non-blanket implementation it combines:

1. a simplified name for the self type,
2. the literal path component `Insts`, and
3. a separator-free trait name extended with relevant concrete generic arguments.

The generated trait fixture supplies representative results:

- `impl BoolTrait for bool` → `Bool.Insts.TraitsBoolTrait`;
- `impl ToType<bool> for u64` → `U64.Insts.TraitsToTypeBool`;
- `impl<T: ToU64> ToU64 for Wrapper<T>` → `Wrapper.Insts.TraitsToU64`;
- implementations for external `Option<T>` retain the external path, for example `core.option.Option.Insts.TraitsBoolTrait`.

Methods and associated constants of a trait implementation are placed below that synthesized implementation name. A method-level rename on the implementation wins; otherwise Aeneas consults the corresponding trait declaration so a rename on the declared method can carry into implementations. An explicit rename on the impl itself replaces the synthesized impl name entirely: the rename fixture's renamed bool implementation becomes `BoolImpl`, with methods such as `BoolImpl.getTest`.

Blanket impls receive additional `Blanket` differentiation in the naming code. The exact spelling depends on the simplified self/trait pattern and should be obtained from Aeneas rather than reimplemented by consumers.

Basis: source + checked-in generated fixtures.

### Inherent method/field collisions can insert an `impl` namespace component

Lean uses short record-field names, so an inherent method can collide with the Lean field projector generated for a field of the same type. Aeneas records qualified ADT projector names and checks generated method names against them. With the default configuration, it inserts an `impl` path element only when needed to avoid such a collision; the source gives `Struct.impl.len` for a `len` method colliding with field `len`.

The `-impl-namespace` option changes this policy from conditional to uniform: Aeneas inserts `impl` into all relevant method names. The default for `method_names_in_impl_namespace` is false.

This conditional behavior means a generated method's name can depend on another declaration in the same translated crate. Consumers that need stable handles should query or preserve Aeneas's generated name rather than predict it from the method alone.

Basis: source.

### Renames replace item-level spellings, with trait/impl-specific propagation

Aeneas consumes rename metadata carried in Charon item metadata. For ordinary types, functions, globals, fields, and variants, the relevant extraction routine substitutes the requested name at the item level. `tests/src/rename_attribute.rs` and `tests/lean/RenameAttribute.lean` demonstrate trait, trait-method, trait-impl, free-function, enum, variant, struct, field, constant, and recursive-function renames.

Trait implementations need extra propagation because the generated method name is rooted at the synthesized or renamed impl name. If the implementation method itself lacks a rename, Aeneas looks up the corresponding trait declaration and can use the declaration's method rename. This is why the renamed trait method `getTest` appears under the renamed implementation as `BoolImpl.getTest`.

Renaming one declaration does not imply a global rewrite of every generated name whose source provenance mentions that declaration. The default-method example above is the important concrete warning.

Basis: source + checked-in generated fixture.

### Collision handling is intentionally asymmetric

Aeneas keeps global name maps for declarations whose collisions are forbidden, an "unsafe" map for categories where Lean can disambiguate some duplicate short names, and a strict map for names such as types and reserved identifiers. Function-name collisions are not generally repaired by silently appending an index; Aeneas reports a naming collision and recommends a `#[aeneas::rename("...")]` or `#[charon::rename("...")]` when an explicit declaration rename is appropriate.

By contrast, local variables, generic parameters, and trait-clause variables use `basename_to_unique`, which appends numeric indices until the name is unused. That local-variable uniquification rule should not be confused with top-level declaration naming.

`ctx_add` also makes one Lean-specific syntactic repair explicit at this revision: each dot-separated component containing `-` is wrapped in Lean's quoted-identifier syntax `«...».` Checked-in generated material additionally demonstrates quoted output for a reserved field spelling (`«name»` in `Names.lean`), but this report does not infer a broader source-level quoting algorithm beyond behavior established by the pinned implementation and fixture.

Basis: source + checked-in generated fixture.

## Boundaries

This report does not define a stable public naming ABI promised by Aeneas. It records the behavior of the exact Anneal-selected revision. Name generation is implementation policy and includes collision-sensitive and configuration-sensitive cases.

It does not exhaustively enumerate builtin mappings. `ExtractBuiltinCore.ml` constructs builtin type/function/trait tables with explicit extracted names, so builtin and modeled-external names may deliberately diverge from the ordinary local-item mapping.

It does not claim that every Rust item becomes a Lean declaration. Aeneas can erase, merge, synthesize, or restructure items as part of pure translation. In particular, current mutable-borrow examples often encode backward behavior as local returned closures.

It does not claim that every generated support file is inside the same namespace block. The ordinary generated Lean fixtures examined here are, and `extract_file` exposes `in_namespace`/`open_namespace` controls internally, but support/template files can choose those flags differently.

It does not establish a general theorem that all Rust identifiers needing Lean escaping are repaired. The pinned source explicitly establishes hyphen-component quoting and collision checks; checked-in output separately establishes quoted rendering of at least the reserved field spelling `name`.

No fresh Aeneas/Charon execution was performed in this environment. The checked-in source/generated pairs provide concrete same-revision specimens, but they do not substitute for a probe when validating a newly upgraded Aeneas revision or a configuration combination not represented by the fixtures.

## Evidence

All Aeneas source and fixtures below are from `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

- `src/extract/ExtractName.ml`, blob `294499309f9492bf74f9a5fc95261556fcdb76a6`: `pattern_to_extract_name`, `name_to_simple_name`, and generic/type-expression simplification used before names are flattened.
- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: name maps and collision policy; `ctx_prepare_name`; type, field, variant, function, loop, trait, and trait-impl name construction; inherent-method/projector collision handling; local-name uniquification; Lean hyphen quoting in `ctx_add`.
- `src/extract/ExtractBuiltinCore.ml`, blob `60961bddc9aa65a40b58caf5d1c3c777f7990ab9`: Lean `flatten_name` uses `.`; structure constructors use `.mk`; builtin tables accept explicit extracted names.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: namespace override, split-file configuration, short-field/variant defaults, and default `method_names_in_impl_namespace = false`.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: Lean backend activates short record-field names and unprefixed variant names; CLI includes `-namespace` and `-impl-namespace`.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: default namespace selection from raw `crate.name`, CamelCase output-module naming, split-file/subdirectory import handling, and emitted Lean namespace header.
- `tests/src/names.rs`, blob `7d6ed18643b37393a76881e5719c420a7451b265`, paired with `tests/lean/Names.lean`, blob `ff03c177c059ef63cb890038957b1b1626e89c6a`: outer crate namespace and quoted field-name specimen.
- `tests/src/rename_attribute.rs`, blob `0c9dd7f32725c1051437f5873856dea53db61308`, paired with `tests/lean/RenameAttribute.lean`, blob `76b08a33172229d237825cc6171832d319f76d5f`: rename propagation, default-method naming, and loop helper/body suffixes.
- `tests/src/traits.rs`, blob `a20f6ee91960cbacf99e8899a32e789f7b855671`, paired with `tests/lean/Traits.lean`, blob `d234936b72231024fbccf0030a08023836e5eb6e`: synthesized trait-impl names, external crate paths, nested local-item paths, fields, associated constants, and trait-method names.
- `tests/lean/NoNestedBorrows.lean`, blob `e2a706b744e2e9a105e305cf8a2b353354209dae`: nested Rust module path components (`ExpandSimpliy.*`) and merged backward/update closures in current Lean output.

The paired Charon subject is `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`). This report relies on Charon for the structured item identity consumed by Aeneas but does not duplicate the corpus's broader Charon item-shape reports.

## Revalidation

For another Aeneas revision, first diff the naming-critical regions rather than rerunning the whole translation corpus:

1. `src/extract/ExtractName.ml`: `pattern_to_extract_name*` and `name_to_simple_name`;
2. `src/extract/ExtractBase.ml`: `ctx_prepare_name`, `ctx_compute_*_name`, trait-impl naming, `default_fun_suffix`, name-map collision logic, `ctx_add`, and ADT-projector handling;
3. `src/Config.ml` and `src/Main.ml`: Lean backend defaults and `-namespace`/`-impl-namespace` options;
4. `src/Translate.ml`: namespace selection and output-file/module construction;
5. `src/extract/ExtractBuiltinCore.ml`: Lean name flattening and builtin extracted-name tables.

Then regenerate a small probe crate containing: a top-level function; a nested module; a struct with a field and same-named inherent method; an enum; a normal trait impl; a blanket impl; a trait method with a default body; one renamed declaration of each relevant kind; one one-loop function; and one identifier that requires Lean escaping. Run once with default options, once with `-namespace Probe`, and once with `-impl-namespace`. Preserve the Rust input and generated Lean output and compare the declaration names against this report.

For a cheap same-revision sanity check, regenerate the checked-in `names`, `rename_attribute`, `traits`, and `no_nested_borrows` Lean fixtures and diff them byte-for-byte in the naming regions cited above. A changed spelling in those specimens is sufficient reason to revisit this report even if the high-level translation remains semantically equivalent.