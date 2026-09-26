# Charon opacity and opaque-definition semantics at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), `--opaque` is an **extraction-boundary control**, not a semantic model. For functions and globals, an opaque item retains its name/signature but Charon does not translate its body. For structs/enums/unions, opacity hides fields or variants. For modules, opacity stops module-content traversal, though a nested item referenced from elsewhere can still be reached and translated according to that nested item's own opacity. Charon's `ItemOpacity` lattice is `Transparent < Foreign < Opaque < Invisible`.

CLI opacity and source annotations have different scope. CLI patterns are Charon name-matcher prefix patterns. `--opaque crate::module` therefore matches the module and its descendants unless a more precise CLI pattern wins. By contrast, `#[charon::opaque]` applies only to the annotated item. Charon computes a name-based opacity first, then combines source attributes and extern-item status by taking the more opaque result. A source `#[charon::opaque]` cannot be undone with `--include`, and an `extern { ... }` item is forced at least Opaque.

The per-item rule is especially important for modules, inherent impls, traits, and trait impls. An opaque module does not inherit opacity into a function called from outside that module; the called function can remain Transparent and have its body translated. An opacity annotation on an impl block likewise does not make every method body opaque. At this revision the CLI matcher cannot directly filter an inherent impl block, so the documented workaround is to match methods through a wildcard path such as `crate::module::_::method`. Trait and trait-impl opacity has specialized behavior: Charon's representation-level `ItemOpacity` documentation says Opaque does not by itself remove trait/impl structure, while provided/default methods are retained according to whether they are used/overridden and according to the opacity of the method items themselves.

Foreign items are a separate boundary. Ordinary definitions from another crate default to `Foreign`, which differs from Opaque for types: a foreign enum or a foreign struct whose fields are all public can still be translated structurally. Explicit Opaque hides those contents. Functions from foreign crates are already body-opaque under Foreign. Functions declared in Rust `extern` blocks are forced Opaque by `translate_item_meta` even if a CLI pattern would otherwise request transparency, and their downstream representation is an external declaration rather than a Rust body.

For Anneal's pinned Aeneas pipeline, an opaque Charon declaration still has no semantics merely because it is opaque. Aeneas has a separate external-model registry. If an opaque/external Rust identity matches a registered Aeneas builtin/model, extraction redirects it to that backend definition. If it does not match, Aeneas can leave it as an unresolved external/template/assumption boundary. Thus "`--opaque foo`" and "use model X for foo" are separate operations with separate trust obligations.

No fresh Charon, rustc, or Aeneas execution was performed. The report is based on exact pinned source, upstream documentation, and checked-in Charon golden outputs. Those `.out` files are preserved upstream execution evidence, not fresh execution on this surface.

## Applicability

This report applies to:

- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon 0.1.210;
- the embedded Charon Rust toolchain `nightly-2026-05-31`;
- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`, only for the downstream distinction between Charon opacity and Aeneas model replacement.

This report covers:

- `--opaque`, `--include`, `--exclude`, and `--extract-opaque-bodies` only as needed to explain opacity selection and precedence;
- `#[charon::opaque]`/compatible opaque annotations;
- functions/globals, ADTs, modules, inherent methods/impl blocks, traits/trait impls, foreign-crate items, and Rust `extern` declarations;
- the semantic consequence of handing an opaque declaration to Aeneas.

It does not prescribe which operations Anneal should trust or model. It also does not claim that an Aeneas model faithfully implements the Rust item merely because its registration matches.

## Findings

### Charon has four ordered opacity levels

`ItemOpacity` defines:

1. `Transparent`: translate the item fully.
2. `Foreign`: normal default for items outside the current crate. For types, Charon may translate a foreign enum or a struct with all-public fields; for other item classes this behaves like Opaque.
3. `Opaque`: retain name/signature but not contents. Function/global bodies and ADT fields/variants are absent; module contents are not traversed.
4. `Invisible`: translate nothing for the item and create no corresponding item-map entry.

The ordering is encoded by the enum's derived ordering and is used when source annotations or extern status make an item more opaque than its name-based CLI setting.

Basis: Charon **source**.

### Name-based opacity starts from Foreign outside the crate and Transparent inside it

`TranslateOptions::new` constructs an opacity pattern table. Without `--extract-opaque-bodies` it starts with:

- `_ -> Foreign`;
- `crate -> Transparent`.

It then adds explicit `--include` patterns as Transparent, `--opaque` as Opaque, and `--exclude` as Invisible. Marker-trait/allocator hiding can add further Invisible patterns.

Thus a normal local item is Transparent while a normal dependency item is Foreign, unless a more precise option pattern changes that result.

Basis: Charon **source**.

### `--extract-opaque-bodies` changes the CLI base policy, not forced source/extern opacity

With `--extract-opaque-bodies`, the catch-all `_` pattern is Transparent rather than Foreign, so even foreign items are requested as transparent at the name-policy layer.

That does not override a stronger source attribute or the forced extern-item rule. `translate_item_meta` later combines those facts using `Opaque.max(name_opacity)` or `Invisible.max(name_opacity)`.

`--extract-opaque-bodies` therefore means "request transparent extraction wherever the later item-level rules permit it," not "ignore all opacity constraints."

Basis: Charon **source**.

### CLI pattern conflicts choose the most precise match and then err toward opacity

`opacity_for_name` finds all matching name patterns and takes the maximum according to the matcher's ordering and opacity. Pinned documentation explains the effective precedence:

- longer/more precise patterns beat shorter ones;
- among equal-length patterns a non-glob final element beats a glob;
- when equally precise settings conflict, Charon errs toward the more opaque setting.

The checked-in `opacity.rs` fixture supplies both `--include ...dont_translate_body` and `--opaque ...dont_translate_body`; the golden output retains the function signature with `= <opaque>`.

Basis: Charon **source** + upstream **documentation** + preserved **execution** artifact.

### `--opaque` patterns are prefix patterns

The name matcher treats a pattern such as `crate::module` as matching that item and subitems. Therefore:

`--opaque crate::module`

can make both the module and names below it opaque.

A more precise pattern such as:

`--include crate::module::_`

can restore transparency to matching descendants while keeping the module itself opaque. This is a CLI pattern property, not inheritance from a module opacity state.

Basis: upstream **documentation** + pinned test source.

### A source opacity annotation applies only to the annotated item

`translate_item_meta` computes `attr_info` for the specific item and then upgrades that item's opacity if it contains an opaque attribute.

Pinned documentation explicitly contrasts this with CLI prefix matching: `#[charon::opaque]` on a module affects only the module. A nested function retains its independently computed opacity. If another translated item refers directly to that nested function, Charon can still enqueue and fully translate the function body.

The `opaque_attribute.rs` fixture preserves exactly this case: module `opaque` is annotated opaque; its unreferenced `other_fn_in_opaque_module` is skipped because module traversal stops, while `fn_in_opaque_module`, called from outside, appears in the golden output with a normal body.

Basis: Charon **source** + upstream **documentation** + preserved **execution** artifact.

### `--include` cannot override a source `#[charon::opaque]`

For an item with an opaque source attribute, `translate_item_meta` computes:

`ItemOpacity::Opaque.max(name_opacity)`.

If a CLI `--include` pattern makes `name_opacity` Transparent, the result is still Opaque. If a CLI `--exclude` makes the item Invisible, Invisible remains stronger.

Source annotations can therefore make an item more opaque than its CLI name policy but cannot make it less opaque.

Basis: Charon **source**.

### Free functions retain signatures but lose bodies when opaque

For a free function, Opaque means the function declaration/signature remains representable but Charon does not translate the MIR body.

`opacity.out` preserves `test_crate::module::dont_translate_body` as:

`fn dont_translate_body() = <opaque>`.

`opaque_attribute.out` similarly preserves `test_bool_trait_option` as an opaque generic function with its trait clauses/signature but no implementation body.

Basis: Charon **source** + preserved **execution** artifacts.

### Opaque globals/constants retain declaration/type boundaries but not implementation contents

The representation-level rule treats function and global bodies alike. The `opaque_attribute` fixture marks a const opaque; its output retains the const identity/type and an opaque initializer function boundary rather than translating the source computation `600 + 60 + 6`.

This preserves enough shape for references to the constant while removing the implementation semantics that would justify its value.

Basis: Charon **source** + preserved **execution** artifact.

### Opaque ADTs hide their fields or variants

For type declarations, Opaque means fields/variants are not translated. The `opaque_attribute` fixture's opaque type alias/type cases and other pinned tests preserve `opaque type` forms.

Foreign is intentionally different: Charon may expose a foreign enum or an all-public-field foreign struct. Explicitly setting such a type Opaque removes that structural information.

Basis: Charon **source** + upstream **documentation**.

### Inherent impl opacity is not an inherited method-body switch

An impl block and its methods are separate Charon items. A source `#[charon::opaque]` on an inherent impl does not automatically set each method's item opacity.

The option documentation records an additional CLI limitation: matching inherent impl blocks directly is currently unsupported. The standard workaround is a path such as:

`crate::module::_::method`

to target the method item.

Therefore "make this inherent impl opaque" must be interpreted carefully:

- an attribute on the impl changes the impl item's own opacity;
- a CLI prefix can affect descendants only when the name matcher can express the relevant pattern;
- suppressing a method body requires the method item itself to resolve Opaque.

Basis: Charon **source** + upstream **documentation**.

### Trait declarations and trait impls have specialized opacity semantics

`ItemOpacity::Opaque` documentation says that for traits and trait impls, opacity does not simply erase the trait/impl structure as it does for function bodies or ADT contents.

Pinned documentation further explains that provided/default methods are translated only when mentioned (used or overridden) in the final crate unless options request broader translation. Methods themselves remain separate items with their own opacity.

The `opaque-trait` fixture demonstrates the specialized behavior. An opaque trait and opaque impl still produce trait/impl structures and the subset of method declarations/bodies Charon's method-use rules require. A blanket interpretation "opaque trait impl means every implementing method body is hidden" is therefore wrong at this revision.

Basis: Charon **source** + preserved upstream **execution** artifact.

### Method-level source annotations can independently make a trait method opaque

The `opaque_attribute.rs` fixture annotates the required trait method `get_bool` itself. The golden output keeps its signature and emits `<opaque>` for that method declaration.

Other implementation methods in opaque impl blocks can still have bodies in the output because their own item opacity and method-use rules differ.

This is another direct example of per-item rather than inherited opacity.

Basis: preserved upstream **execution** artifact.

### Opaque modules stop discovery through module traversal but not independent references

For a module, Opaque means Charon does not enumerate its contents through that module.

This changes **reachability**, not the opacity of every nested item. A nested definition referenced from already-translated code can be discovered through that independent reference and then translated according to its own opacity.

This distinction is essential when combining `--opaque` with `--start-from`: the start-root dependency closure is truncated wherever exploration would need an opaque body/module, but independently reachable child items can still appear.

Basis: Charon **source** + upstream **documentation** + preserved **execution** artifact.

### `--exclude` is stronger than opacity

Invisible is stronger than Opaque. An excluded item is not represented at all rather than represented by signature only.

The `opacity.rs` fixture uses both opacity and exclusion patterns. Its purpose includes cases where an excluded trait identity still has to be kept indirectly so an included impl can be named, illustrating why filtering is not equivalent to deleting arbitrary textual declarations before semantic translation.

Basis: Charon **source** + pinned test **source**.

### Foreign functions are already body-opaque under the `Foreign` default

For non-type items, Foreign is representation-equivalent to Opaque according to the `ItemOpacity` documentation. Thus an ordinary dependency function's signature can be present without its body even when the user did not pass `--opaque`.

Applying `--opaque` to a foreign function often does not further reduce the function body because it was already omitted under Foreign. It can still matter to pattern policy and to types, for which Foreign can preserve more representation.

Basis: Charon **source**.

### Rust `extern` declarations are forced Opaque independently of CLI policy

`translate_item_meta` checks `is_extern_item(def)` and combines `ItemOpacity::Opaque` with the name-based opacity.

A declaration inside an `extern { ... }` block therefore cannot become a normal Rust body merely because a CLI `--include` or `--extract-opaque-bodies` requests transparency. The `opacity.rs` fixture notes that foreign modules themselves cannot be named/attributed normally; its golden output represents `extern_fn` as an external function boundary.

This is a semantic absence, not merely a filtering choice: the Rust declaration has no Rust function body for Charon to extract.

Basis: Charon **source** + preserved **execution** artifact.

### Opacity does not provide replacement semantics

An opaque Charon function tells downstream consumers its signature and that the body is unavailable in the Charon model. It does not assert a postcondition, a pure mathematical function, an FFI contract, or any other behavior.

Any verification system that uses the opaque call must separately decide how its behavior is represented, assumed, rejected, or modeled.

Basis: Charon **source** + **derived** semantic consequence.

### Aeneas model replacement is separate from Charon opacity

At the Aeneas revision selected by Anneal, external/model definitions are recognized through a distinct Rust-name-pattern-to-backend-definition registry. The companion corpus report `aeneas-external-models-nightly-2026-06-03` establishes that registered builtins/models are filtered separately from unresolved opaque non-builtin declarations.

Thus:

- Charon opacity determines that a Rust implementation body is absent from LLBC;
- Aeneas model matching can redirect the corresponding Rust identity to a Lean/backend model;
- an unmatched opaque declaration can remain an external/template/assumption boundary.

A model registration is not proved correct merely because it matches an opaque Rust item.

Basis: existing corpus **source** synthesis from pinned Aeneas.

### For Anneal, opacity creates an explicit semantic/trust boundary

If Anneal makes a Rust-level promise about behavior that passes through an opaque item, the missing body cannot silently disappear from the proof obligation.

A sound result must do one of the things current Anneal design permits in principle: reject unsupported opacity, account for the operation through a faithful model/specification, or expose the required assumption in the trust boundary. Which mechanism Anneal chooses remains a design question.

`--opaque` is therefore useful for controlling extraction and for substituting trusted/modeled boundaries, but it is not by itself evidence of correctness.

Basis: **derived** from Charon's representation and Anneal's current design contract.

## Boundaries

- No fresh Charon, rustc, Aeneas, or Lean execution was performed.
- Checked-in Charon `.out` files are preserved upstream execution evidence, not fresh execution.
- This report does not prove that any particular Aeneas model faithfully implements the Rust definition it replaces.
- It does not exhaustively specify Charon's name-matcher grammar; the dedicated start-from report and Charon docs cover selector syntax more broadly.
- It does not characterize every interaction with monomorphization, precise drops, multi-target merging, or unsupported constructs.
- It does not claim source annotations and CLI prefix patterns have identical scope; they explicitly do not.
- It does not claim opacity on an impl block automatically hides method bodies.
- It does not claim Foreign and Opaque are identical for types; Foreign can preserve public type structure that Opaque hides.
- It does not claim an extern declaration has a hidden Rust body that could be recovered by a stronger include option.
- It does not choose Anneal's model/assumption syntax or TCB representation.

## Evidence

**Charon:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `docs/what_charon_translates.md`, blob `780949ef1304a89e34c87b04958d65dbc3bf0810`: opacity lattice behavior, reachability interaction, source-vs-CLI scope, pattern semantics and precedence.
- `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`: `ItemOpacity` and `ItemMeta` semantics.
- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: CLI opacity options, default pattern table, `--extract-opaque-bodies`, most-precise-match selection.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`: source attribute parsing, `translate_item_meta`, source/external forced opacity.
- `charon/tests/ui/filtering/opacity.rs`, blob `2088ea043c3750201a3146aca9ed13e932a989b8`, and `opacity.out`, blob `5429afa54236e0fc0d82e7aaaf348b5d6442b4f0`: CLI pattern precedence, foreign inclusion, opaque free function, excluded items, extern declaration, impl annotation fixture.
- `charon/tests/ui/filtering/opaque_attribute.rs`, blob `d69ad26b35289697732534343604e4712abdacf4`, and `opaque_attribute.out`, blob `9d25497b70aad9abb11206a8f1fa850a9497a430`: per-item attributes on trait/method/impl/function/type/const/module and called child of opaque module.
- `charon/tests/ui/filtering/opaque-trait.rs`, blob `f2ed077aee2ec1ba55654728c5f205773de723b2`, and `opaque-trait.out`, blob `d6649d54d89eb6f59c2f81008e3f8627763d84fd`: opaque trait/impl method-use behavior.
- `charon/tests/ui/filtering/inner-items.out`, blob `1f17ef7a5a962eaccbdf7b5f4acc28cc5ea15dfb`: opaque local function body rendered as `<opaque>`.

**Aeneas downstream model boundary:** existing corpus report `aeneas-external-models-nightly-2026-06-03`, pinned to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

No evidence above is fresh **execution**.

## Revalidation

For another Charon revision, diff:

1. `ItemOpacity` and `ItemMeta`;
2. opacity-table construction and `opacity_for_name` in `options.rs`;
3. attribute and extern handling in `translate_item_meta`;
4. module/item enqueue behavior in the translation work queue;
5. trait/default-method filtering;
6. `opacity`, `opaque_attribute`, and `opaque-trait` UI fixtures.

Then run a minimal capable-surface matrix with exact revisions:

- a free function under `--opaque`;
- a type with visible fields under Foreign versus Opaque;
- a module annotated `#[charon::opaque]` with one child called from outside and one unreferenced child;
- the same module under CLI `--opaque crate::module`;
- `--opaque crate::module --include crate::module::_`;
- an inherent impl with an impl-level opaque attribute and separately opaque method patterns;
- a trait and impl with used/unused default methods;
- an `extern "C"` declaration under `--include`, `--opaque`, and `--extract-opaque-bodies`;
- a downstream Aeneas run for one registered model and one unmatched opaque declaration.

Preserve the exact CLI, generated LLBC, diagnostics, Aeneas output, and hashes. Confirm which item structures/bodies survive and which downstream calls are redirected to models.

This revalidates extraction/model handoff for that exact combination. It does not prove that a backend model is semantically faithful to the Rust implementation or foreign function.
