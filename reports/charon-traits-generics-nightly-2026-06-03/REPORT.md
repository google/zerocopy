# Charon traits, generics, and where-clauses at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), traits and generic constraints are represented as explicit semantic data rather than being left as source syntax or delegated to a downstream trait solver. A declaration's `GenericParams` separately records region, type, and const parameters; trait clauses; region-outlives and type-outlives predicates; and associated-type equality constraints. Generic arguments mirror those parameter classes and additionally carry concrete `TraitRef` values for required trait clauses.

Charon's distinctive trait feature is that a `TraitRef` records not only **which trait predicate holds** but also **how Charon/rustc established it**. `TraitRefKind` distinguishes a concrete trait impl, a local where-clause, a parent/supertrait clause derived from another proof, a clause on an associated type, the implicit `Self: Trait` assumption inside a trait declaration, compiler-provided builtin/auto implementations, `dyn Trait`, and an explicit unknown/error case. Charon's companion `rustc_trait_elaboration` crate describes its purpose exactly this way: given a trait reference, track which impl and/or local clauses caused it to be true.

A `TraitDecl` stores its generic parameters, implied/supertrait clauses, associated constants, associated types, methods, and optional vtable type. Associated types and methods have nested `Binder`s so GAT/method-level generic parameters remain distinct from the trait's outer generics. Each method also points to a function item: required methods have a dedicated `TraitMethodWithoutDefault` body marker, while provided methods can retain translated default bodies when selected.

A `TraitImpl` stores the instantiated trait being implemented, its own generics/where-clauses, explicit proof references satisfying the trait declaration's implied clauses, associated constant/type values, method references, and optional vtable instance. Missing method implementations can be represented by Charon-generated references/copies of the trait default. Method implementations and trait methods are indexed against the trait's associated-item IDs rather than being matched downstream by source spelling.

Rust source spellings such as `T: Foo`, `where T: Foo`, and supertrait syntax are therefore normalized into the same underlying clause structures. Trait associated-type equalities such as `T: Foo<Item = U>` become explicit `TraitTypeConstraint` values. Higher-ranked lifetime binders survive in Charon's binder representation, while Charon deliberately hides rustc's early-versus-late-bound lifetime distinction by translating both into its own region variables at the appropriate binding level.

Not every rustc predicate is retained. At this revision Charon ignores `ConstArgHasType`, `HostEffect` (`const Trait`), `WellFormed`, `ConstEvaluatable`, and an internal unstable-feature predicate in this translation path; other unrecognized clauses are errors, and negative trait predicates are not handled by the positive-trait translation routine. These omissions are material semantic boundaries, especially for unstable generic-const and const-trait features.

Checked-in golden outputs at this exact revision demonstrate the model across required/provided methods, concrete and generic impls, supertraits, associated types and equality constraints, const generics, late-bound regions, default methods, trait aliases, and compiler-provided trait evidence. No fresh Charon/rustc execution was performed on this surface; those checked-in `.out` files are preserved upstream execution evidence.

## Applicability

This report applies to:

- repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon version `0.1.210`;
- embedded Rust toolchain `nightly-2026-05-31`.

It jointly covers the #3720 subjects **Charon trait representation** and **Charon generics and where-clauses** because they share one representation and translation boundary. Trait declarations and implementations embed `GenericParams`; trait calls and associated-type projections consume `TraitRef` evidence whose local-clause IDs refer back to those generic predicates.

The report focuses on the ordinary polymorphic translation. Charon also has monomorphization modes and post-processing options that can rewrite associated types or clauses; those transformations are not the baseline representation described here unless explicitly noted.

The separate opacity report governs whether an item's body or associated structure is explored. The separate Aeneas translation report governs how this Charon representation is subsequently mapped into Lean/Aeneas dictionaries and generated functions.

## Findings

### Generic parameters are explicit typed collections, not one undifferentiated argument list

`GenericParams` contains separate vectors for:

- region parameters;
- type parameters;
- const-generic parameters;
- trait clauses;
- region-outlives predicates;
- type-outlives predicates;
- associated-type constraints.

`GenericArgs` mirrors regions, types, const values, and trait references. A reference to a generic item therefore carries both ordinary type-level substitutions and the concrete trait evidence corresponding to its required trait clauses.

Basis: Charon **source**.

### Bounds written in parameter syntax and `where` syntax converge into the same predicate representation

`translate_generics.rs` consumes rustc/hax `ParamEnv` information rather than preserving the textual placement of a bound. It pushes parameters and then registers predicates with a `PredicateOrigin` describing where the predicate came from: function/global, type, impl, trait, implicit trait `Self`, associated trait item, or `dyn` binder.

Thus `fn f<T: Foo>()` and an equivalent `fn f<T>() where T: Foo` are represented as trait clauses in the same generic environment. The origin records semantic context, not the exact syntactic spelling.

Basis: Charon **source** + **derived** normalization consequence.

### Parent generics are accumulated recursively

`push_generics_for_def` first visits the item's typing parent recursively and then adds the item's own environment. This is important for nested items such as methods, closures, and associated items, whose valid type environment can depend on enclosing generic parameters.

The translator uses binding levels to distinguish outer item parameters from inner method/GAT/higher-ranked binders instead of flattening all variables into one namespace.

Basis: Charon **source**.

### Charon hides rustc's early-versus-late-bound lifetime distinction

The generic translator explicitly says it does not preserve rustc's early/late region distinction. Early and late-bound regions are both mapped into Charon region IDs, with binding levels and De Bruijn indices retaining scope.

Function signatures can add late-bound regions after ordinary generic parameters; method/GAT/higher-ranked predicates introduce nested binders. This preserves quantification structure while discarding rustc's particular early/late implementation taxonomy.

The existing lifetime report covers the broader rustc→Charon→Aeneas region pipeline; this finding locates the generic binder representation within Charon.

Basis: Charon **source**.

### Trait predicates become explicit clause parameters

For each positive trait predicate, `translate_predicates` reserves a `TraitClauseId` and emits a `TraitParam` containing the predicate origin, source span, and quantified trait declaration reference.

The mapping from rustc/hax predicate identity to Charon clause ID is installed before translating the clauses themselves, because predicates can refer recursively to other predicates, including themselves.

A polymorphic function body can therefore refer directly to `TraitClauseN` as the evidence used for a trait method call or associated item.

Basis: Charon **source** + checked-in **execution** output.

### Outlives constraints have dedicated representation

Region-outlives predicates become `RegionOutlives`; type-outlives predicates become `TypeOutlives`. Both can be wrapped in region binders.

They are not encoded as ordinary trait clauses. This distinction lets a consumer distinguish Rust lifetime relationships from trait evidence even though both originate in generic predicate environments.

Basis: Charon **source**.

### Associated-type equality constraints are first-class generic predicates

A projection predicate such as `T: Foo<Item = U>` becomes `TraitTypeConstraint` containing:

- the trait proof/reference that gives meaning to the associated type;
- the associated type ID within that trait;
- the type to which the projection is constrained.

The checked-in `traits.out` and `predicates-on-late-bound-vars.out` files show these as `TypeConstraintN` entries referring through trait clauses and associated-type IDs.

Basis: Charon **source** + preserved **execution** evidence.

### Charon intentionally drops several rustc predicate classes

At this revision, `translate_predicate` does not preserve every rustc clause:

- `ConstArgHasType` is treated as trait-resolution bookkeeping and ignored;
- `HostEffect` for unstable `const Trait` is ignored;
- `WellFormed` and `ConstEvaluatable` are ignored in this path;
- an internal `UnstableFeature` clause is ignored;
- unknown remaining clause kinds are translation errors.

The source comment for `ConstEvaluatable` notes that predicates such as `[(); N + 1]:` can encode the requirement that a fallible generic-const expression succeeds. Dropping the predicate therefore means a downstream consumer cannot infer that Charon's generic predicate list is a lossless serialization of every rustc well-formedness obligation.

Basis: Charon **source**.

### Negative trait predicates are not represented by the positive trait-predicate path

`translate_trait_predicate` asserts that the incoming trait predicate is positive. The ordinary clause representation documented here therefore does not establish support for a negative trait predicate as an equivalent `TraitParam`.

This is a boundary rather than evidence that all Rust negative reasoning is absent from every rustc-derived fact; it states what this pinned Charon translation path represents.

Basis: Charon **source**.

### Trait declarations have their own item identity and explicit associated-item tables

`TraitDecl` stores:

- its Charon `TraitDeclId` and item metadata;
- `GenericParams`;
- implied clauses, including supertrait requirements;
- associated constants;
- associated types, each under a binder for GAT parameters;
- methods, each under a method-level binder;
- an optional vtable type when the trait is dyn-compatible.

Associated constants, types, and methods use IDs indexed within the trait declaration. Charon also stores their names separately for presentation/lookup. Consumers need not reconstruct trait membership from Rust path strings.

Basis: Charon **source**.

### Supertraits become explicit implied clauses

The `TraitDecl` representation calls supertrait requirements `implied_clauses`. The source notes that, at this revision, Charon treats all trait clauses on a trait declaration as parent/implied clauses.

A reference derived through a supertrait becomes `TraitRefKind::ParentClause(base, clause_id)`. The golden `traits.out` demonstrates chains such as a `ChildTrait` proof giving access to a `ParentTrait` method/associated type through the recorded implied-clause path.

Basis: Charon **source** + preserved **execution** evidence.

### The implicit `Self: Trait` assumption is represented explicitly

Inside a trait declaration, Charon constructs a `TraitRefKind::SelfId` proof for the trait's own `Self: Trait` predicate. Associated method translation initially receives an explicit clause from hax/rustc, then Charon rewrites that clause to refer to the ambient `SelfId` proof and removes the redundant method-local clause.

This normalization makes trait methods refer to the declaration's self evidence rather than carrying a duplicate local `Self: Trait` parameter.

Basis: Charon **source**.

### Trait methods are both associated entries and function items

Each `TraitMethod` stores its method name, attributes, translated signature, and a `FunDeclRef`. A required method's function item has `Body::TraitMethodWithoutDefault`; a provided method can retain a translated function body.

This gives Charon one function-level representation that ordinary calls and trait-associated method references can share, while the trait declaration retains the stable association between method ID and signature.

Basis: Charon **source** + preserved **execution** evidence.

### Charon prunes unused trait methods rather than blindly serializing every provided method

The translator tracks a `MethodStatus` per trait method. Registering an impl records the method implementation; marking a method used enqueues its known implementations. A final `remove_unused_methods` pass removes unmarked methods from trait declarations and impl tables.

Required methods, methods selected by transparent trait/impl traversal, direct trait-method uses, and certain options can mark methods used. The pinned opaque-trait fixture states this intended contract and shows unused methods disappearing while used/defaulted ones remain.

Basis: Charon **source** + checked-in **execution** evidence.

### Trait implementations record both the implemented trait and proofs of its parent requirements

`TraitImpl` stores:

- the instantiated `TraitDeclRef` being implemented;
- the impl's generic parameters/where-clauses;
- `implied_trait_refs`, which are explicit proofs satisfying the implemented trait's parent/implied clauses;
- associated const/type implementations;
- method references;
- an optional vtable instance.

A downstream consumer can therefore see not only that `impl Trait for T` exists but also the evidence Charon selected for the trait's required parent clauses.

Basis: Charon **source**.

### Concrete method dispatch and generic method dispatch preserve different evidence

When rustc resolves a call to a concrete implementation, Charon can represent the proof as `TraitRefKind::TraitImpl` pointing to the translated impl with generic arguments. In generic code, a call can instead use `TraitRefKind::Clause`, referencing the function's local where-clause.

The pinned `traits.out` demonstrates both: calls on concrete `bool`/`Option<T>` use concrete impl method references, while `test_bool_trait<T: BoolTrait>` calls through `TraitClause1::get_bool`.

Basis: Charon **source** + preserved **execution** evidence.

### Trait proof provenance is a structured tree

Charon's rustc trait elaborator tracks the reason a predicate holds. The source distinguishes:

- concrete impl item;
- local bound/where-clause;
- implicit self proof;
- `dyn` proof;
- compiler-provided builtin/auto proof;
- proof derived from another proof through an associated-item or parent clause;
- error.

Translation maps these into `TraitRefKind` variants such as `TraitImpl`, `Clause`, `SelfId`, `ParentClause`, `ItemClause`, `BuiltinOrAuto`, `Dyn`, and `Unknown`.

This is stronger information than a normalized proposition `T: Trait` alone: the translated program can retain the selected dictionary/evidence path used for method or associated-item access.

Basis: Charon **source**.

### Builtin and auto traits use explicit compiler-evidence variants

Compiler-computed implementations, including auto traits, are represented through `BuiltinOrAuto` rather than fabricated ordinary source impl IDs. `BuiltinImplData` has an `Auto` case and specialized cases for language/builtin traits.

The representation can carry parent trait references and associated type values for such compiler-provided evidence. This keeps the fact that the implementation was compiler-derived visible to a downstream consumer.

Basis: Charon **source**.

### `dyn Trait` has distinct proof/vtable representation

`TraitRefKind::Dyn` represents the automatically generated implementation supplied by a trait object. Trait declarations and impls also carry optional vtable type/instance references when dyn-compatible, and Charon has dedicated translation machinery for vtable structures and instances.

This report does not claim that every object-safety/dyn-dispatch semantic detail is fully captured; it establishes that dyn evidence is not collapsed into an ordinary source impl.

Basis: Charon **source**.

### Default trait methods are normalized into impl-facing method references

When an impl omits a method with a default body, Charon can create a `DefaultedMethod` function item tied to the impl, using the trait declaration's method generic parameters substituted through the impl's self proof. The generated impl then has a method entry as though it had an implementation.

Upstream documentation explicitly lists “Make non-overriden default methods in impl blocks appear as normal methods” as one of Charon's normalization responsibilities. Checked-in outputs show inherited default methods on concrete impls.

Basis: Charon **source**, upstream **documentation**, and preserved **execution** evidence.

### Trait aliases are represented as traits whose content is their implied clauses

For a `TraitAlias`, `translate_trait_decl` emits a `TraitDecl` with generic parameters and implied clauses but no ordinary associated items. Trait-proof translation can synthesize a blanket `TraitImplRef` for the alias. The pinned `trait-alias.out` shows `Alias` as a trait with implied proofs and an automatically represented generic implementation.

This is a normalization choice: downstream consumers can reason about aliases using the same trait-reference machinery rather than retaining Rust alias syntax.

Basis: Charon **source** + preserved **execution** evidence.

### Associated types can have their own bounds and GAT binders

A `TraitAssocTy` stores optional default value and its own implied clauses. It sits under a `Binder` whose generic parameters represent GAT parameters when present. Implemented associated types likewise carry a binder and proof references satisfying the declaration's associated-type clauses.

A later `lift_associated_item_clauses` transformation can move associated-item clauses into parent-clause structure, so consumers must bind claims to the configured transformation stage when exact clause location matters.

Basis: Charon **source**.

### Known binder/trait limitations remain material at this pin

The source contains explicit limitations rather than a claim of perfect rustc trait reconstruction. Notably:

- method/impl translation contains a FIXME for trait method signatures whose late-bound regions do not match the declaration (#513);
- the limitations document flags precise lifetimes for higher-ranked trait predicates as an area with known limitations;
- trait-proof translation can preserve an `Unknown` result after an elaboration error rather than pretending to have valid evidence;
- unsupported/ignored predicate kinds described above leave semantic information out of the generic predicate representation.

These are relevant to any downstream claim that treats Charon's trait/generic representation as a complete proof of Rust trait semantics.

Basis: Charon **source** + upstream **documentation**.

## Boundaries

- No fresh rustc, Charon, trait-solver, or LLBC execution was performed.
- Checked-in `.out` files are preserved upstream execution/test evidence, not fresh observations from this run.
- This report does not establish completeness or soundness of rustc trait solving itself; it records the evidence Charon receives and serializes.
- Negative trait predicates are not established as supported by the ordinary `TraitParam` path.
- `HostEffect`/const-trait predicates, `ConstEvaluatable`, `WellFormed`, `ConstArgHasType`, and internal unstable-feature predicates are not retained as ordinary generic constraints by the inspected translator.
- The semantics and proof obligations of generic const expressions are not reconstructed here.
- GATs and higher-ranked predicates have known revision-specific binder limitations; nearby Charon revisions must not be assumed equivalent.
- The report does not characterize every normalization option such as associated-type lifting/removal, marker-trait hiding, ADT-clause removal, monomorphization, or eager vtable generation.
- `dyn Trait` object semantics and vtable layout deserve a separate focused report if Anneal needs to reason about dynamic dispatch operationally.
- An explicit `TraitRef` evidence path is a representation of rustc/Charon's selected proof, not an independently machine-checked proof that a downstream semantic model faithfully implements Rust behavior.

## Evidence

**Primary subject:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/ast/types.rs`, blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`: `TraitRefKind`, `TraitRef`, `TraitDeclRef`, `TraitImplRef`, `GenericArgs`, `GenericParams`, binders, predicate origins, outlives predicates, associated-type constraints, builtin/auto evidence.
- `charon/src/ast/gast.rs`, blob `23044319a8f763d241912c5d693ed94cf597682f`: `TraitDecl`, `TraitImpl`, associated constants/types/methods, default references, vtable fields.
- `charon/src/bin/charon-driver/translate/translate_generics.rs`, blob `7475da93f6e6b54cddce6df15a9af467d05afad1`: binding levels; recursive parent generics; early/late regions; type/const parameters; predicate origins.
- `charon/src/bin/charon-driver/translate/translate_predicates.rs`, blob `97ca285fb2573c0abb02d7ac0e8e6c2014e24379`: trait clauses, outlives clauses, projection/equality constraints, ignored predicate classes, and trait-proof translation.
- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: trait declaration/impl translation, associated-item IDs, method-use tracking, default methods, self-clause normalization.
- `charon/src/bin/charon-driver/hax/traits.rs`: hax-side trait proof representation and translation from rustc trait elaboration.
- `charon/rustc_trait_elaboration/src/lib.rs`, blob `e251b1b540e3abb17445694a3425be5b1d195d95`: concrete/local/self/dyn/builtin/derived/error trait-proof taxonomy.
- `docs/what_charon_does_for_you.md`, blob `b0e9b32a11b78f106c7edf953bb0f60967de8cb2`: upstream statement that Charon tracks how trait bounds were proved, hides early/late lifetime distinctions, and normalizes default methods.
- `docs/limitations.md`, blob `34b20af95cdbe733f9094ded613ed23f42691de6`: alpha-status and revision-specific representation limitations.

**Preserved execution fixtures:**

- `charon/tests/ui/traits.rs`, blob `92a7f2783bf31dab3b9f438fc33a8bdbabe7f804`; `traits.out`, blob `e9a173d85a5925d935b10cb085a7bdc869efdd19`: required/default methods, concrete/generic impls, supertraits, associated types/constants, const generics, equality constraints, trait calls and proofs.
- `charon/tests/ui/predicates-on-late-bound-vars.rs`, blob `2c32b10c3d227f98f1963947b8f9a1e31a9c1e67`; `.out`, blob `3f268d5124209d8ce85f01d4a9a89a492ac3050f`: early/late region predicate normalization and associated-type equality.
- `charon/tests/ui/filtering/opaque-trait.rs`, blob `f2ed077aee2ec1ba55654728c5f205773de723b2`; `.out`, blob `d6649d54d89eb6f59c2f81008e3f8627763d84fd`: method-use filtering, default methods, trait/impl tables, implied proof references.
- `charon/tests/ui/simple/trait-alias.rs`, blob `16e04f29786352c1e572905f94b67fd091d9c61a`; `.out`, blob `8754643021d310fe45232bf99a8bf9e2c53a4518`: trait alias normalization and implied clauses.

No fresh **execution** evidence was produced in this run.

## Revalidation

For a future Charon revision, first diff:

1. `ast/types.rs` generic/predicate/trait-reference data structures;
2. `ast/gast.rs` trait declaration/impl and associated-item structures;
3. `translate_generics.rs` and `translate_predicates.rs`;
4. trait declaration/impl translation in `translate_items.rs`;
5. `hax/traits.rs` and `rustc_trait_elaboration` proof taxonomy;
6. transformations that move/remove associated-type or marker/ADT clauses.

On a capable execution surface, run a compact pinned fixture covering:

- equivalent parameter-bound and `where` syntax;
- type, const, early-region, and higher-ranked late-region parameters;
- region/type outlives clauses;
- supertraits and diamond supertraits;
- required and provided methods;
- an impl inheriting a default method and one overriding it;
- associated constants, associated types, a GAT, and associated-type equality;
- concrete dispatch and generic clause-based dispatch;
- an auto trait/builtin trait proof;
- a dyn-compatible trait and trait-object call;
- a trait alias;
- negative/const-trait/generic-const predicates where the compiler accepts suitable unstable fixtures.

Preserve Rust input, exact Charon flags, ULLBC/LLBC, diagnostics, and hashes. Compare the emitted generic-parameter order, clause IDs/origins, proof kinds, associated-item IDs, default-method references, vtable references, and ignored/rejected predicate behavior.

That probe establishes concrete behavior for the tested revision and features. It does not prove trait solver correctness, cross-version stability, or semantic adequacy of a downstream verifier.
