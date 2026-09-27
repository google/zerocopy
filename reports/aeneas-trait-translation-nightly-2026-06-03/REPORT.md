# Aeneas trait translation at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, Rust traits are translated to explicit dictionary records. For the Lean backend, an ordinary Rust trait becomes a Lean `structure`; a Rust trait bound becomes an explicit value parameter of that structure type; an implementation becomes a reducible `def` whose value fills the record fields; and generic method calls project through the explicit dictionary. Concrete dispatch can instead name the selected implementation directly. The generated Lean at this revision therefore does **not** use Lean's `class`/`instance` synthesis mechanism for ordinary translated traits, despite upstream overview documentation describing traits as Lean “type classes.”

The dictionaries carry more than methods. Supertrait obligations become dictionary fields containing parent dictionaries. Associated constants become fields whose values live in Aeneas's result model. Most associated types are normalized by Charon before Aeneas sees them: `--remove-associated-types` lifts them into ordinary trait parameters, so generated Lean structures such as `WithConstTy` and `ChildTrait` receive extra type parameters rather than dependent associated-type projections. This normalization also lets equality constraints become ordinary type instantiations in many cases.

That path has a sharp boundary. If associated types survive Charon's removal pass—for example with mutually recursive traits or GAT-like cases—the pinned Aeneas source warns that it cannot handle them correctly. Generic associated types are rejected; dynamic-trait evidence is rejected; unknown trait evidence is rejected. Aeneas also translates trait declarations and implementations independently and can drop a declaration or impl after a translation failure. A consumer cannot infer complete trait coverage merely because the crate produced Lean output.

No fresh Charon, Aeneas, Lean, or rustc execution was performed. The report uses exact pinned implementation source plus checked-in Rust/Lean fixtures and checked-in known-failure output. Those generated files are preserved upstream execution evidence, not observations produced on this surface.

## Applicability

- Aeneas: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`.
- Paired Charon: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`.
- Anneal context: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects this Aeneas release.
- This report describes the functional/pure Aeneas translation and Lean extraction for traits represented by the pinned Charon/Aeneas path. It does not choose an Anneal proof architecture.

“Dictionary” in this report means an explicit translated value that contains the operations and parent evidence required by a Rust trait. It is descriptive terminology for the generated structure value; it does not mean that Rust itself has dictionary-passing semantics or that Lean's typeclass resolver produced the value.

The companion Charon report `charon-traits-generics-nightly-2026-06-03` records the richer LLBC trait representation before Aeneas translation, including `TraitRefKind`, where-clause evidence, concrete impl evidence, associated items, supertraits, defaults, auto/builtin proofs, and `dyn` evidence. This report starts at the Aeneas boundary and records what survives into Aeneas's pure representation and generated Lean.

## Findings

### Trait declarations become explicit record types, not Lean classes

Aeneas's pure AST has a dedicated `trait_decl` record containing generic parameters, predicates, parent clauses, associated constants, residual associated types, and method references. `SymbolicToPure.translate_trait_decl` constructs that record from Charon's trait declaration. The Lean extractor then emits the translated trait through the same structural qualifier used for a non-recursive `Struct`.

The checked-in `tests/lean/Traits.lean` makes the result concrete. Rust

```rust
pub trait BoolTrait {
    fn get_bool(&self) -> bool;
    fn ret_true(&self) -> bool { true }
}
```

is preserved as generated Lean with the shape

```lean
structure BoolTrait (Self : Type) where
  get_bool : Self → Result Bool
  ret_true : Self → Result Bool
```

Likewise, `ToU64`, `ToType`, `OfType`, `ParentTrait0`, and the other fixture traits are ordinary `structure` declarations. The golden file contains explicit fields and parameters rather than `class` declarations.

This matters for proof-facing APIs. A generated function does not rely on Lean instance search to recover a Rust trait obligation. The needed dictionary is visible in the function's parameters or is named directly when dispatch has already resolved to a concrete impl.

Basis: **source** + preserved **execution** artifact.

### Generic Rust trait bounds become explicit dictionary parameters

Aeneas preserves trait clauses in `Pure.generic_params.trait_clauses`. Generic arguments likewise contain `trait_refs`. Extraction adds those clauses to the generated parameter list.

The Rust fixture

```rust
pub fn test_bool_trait<T: BoolTrait>(x: T) -> bool {
    x.get_bool()
}
```

becomes generated Lean with an explicit dictionary:

```lean
def test_bool_trait
  {T : Type} (BoolTraitInst : BoolTrait T) (x : T) : Result Bool := do
  BoolTraitInst.get_bool x
```

The distinction between syntactic forms also survives where it affects selected evidence. In the fixture, `f<T: ToU64>(x: (T,T))` uses the generated dictionary for the generic `T` to construct/select the pair implementation, while `g<T>(x: (T,T)) where (T,T): ToU64` accepts a dictionary directly for `ToU64 (T × T)`. Both express valid Rust obligations, but the generated Lean parameters reflect the evidence shape Charon supplied.

Basis: **source** + preserved **execution** artifact.

### Concrete and generic dispatch remain observably different

Aeneas's pure `trait_instance_id` distinguishes at least:

- `TraitImpl` for a concrete translated implementation;
- `Clause` for a local generic trait clause;
- `ParentClause` for evidence obtained through a supertrait/parent clause;
- `BuiltinOrAuto` for selected builtin cases such as `Copy`, `Clone`, and the `Fn*` family;
- `Self` while translating the trait's own items;
- `UnknownTrait`, which is an error path during extraction rather than usable evidence.

`SymbolicToPureTypes.translate_trait_ref_kind` translates Charon concrete impl, clause, parent-clause, and supported builtin/auto evidence into these pure cases. `ExtractTypes.extract_trait_instance_id` then prints the corresponding implementation value, local dictionary parameter, parent-dictionary projection, or builtin name.

The generated fixture demonstrates both main dispatch modes. `h0(u64)` calls `U64.Insts.TraitsToU64.to_u64` directly; `test_bool_trait<T: BoolTrait>` calls `BoolTraitInst.get_bool`. Aeneas therefore does not erase the difference between “rustc/Charon selected this concrete impl” and “this function is polymorphic over evidence supplied by its caller.”

Basis: **source** + preserved **execution** artifact.

### Implementations become reducible dictionary values

The pure AST has a separate `trait_impl` record containing the implemented trait reference, generic parameters and trait clauses, parent-trait references, associated constants, residual associated types, and method references. The Lean backend emits a definition whose type is the translated trait structure and whose value fills its fields.

For example, the checked-in `ToU64 for u64` implementation becomes a method definition plus:

```lean
@[reducible]
def U64.Insts.TraitsToU64 : ToU64 Std.U64 := {
  to_u64 := U64.Insts.TraitsToU64.to_u64
}
```

A generic implementation such as `impl<A: ToU64> ToU64 for (A,A)` becomes a reducible function from the prerequisite `ToU64 A` dictionary to a `ToU64 (A × A)` dictionary. This makes Rust impl dependencies explicit in Lean term structure.

The extraction source separately prints implementation constants, types, parent clauses, and methods into the record literal. The dictionary is therefore the point where an implementation's prerequisite evidence and selected members are assembled.

Basis: **source** + preserved **execution** artifact.

### Supertraits become parent-dictionary fields

Charon supplies implied/supertrait clauses on a trait declaration and corresponding evidence on an impl. Aeneas translates those into `trait_decl.parent_clauses` and `trait_impl.parent_trait_refs`. The Lean extractor emits parent clauses as fields of the trait structure and fills those fields in implementation dictionaries.

The checked-in fixture turns

```rust
pub trait ChildTrait: ParentTrait0 + ParentTrait1 {}
```

into a structure with explicit parent dictionaries. A generic call through `ChildTrait` projects `ParentTrait0Inst` before invoking a parent method. Likewise, a concrete `ChildTrait1 for usize` dictionary contains the selected `ParentTrait1` dictionary.

This is significant for source correspondence: a Rust supertrait method call can become a chain of dictionary projections in Lean even though no such field access exists in Rust source.

Basis: **source** + preserved **execution** artifact.

### Method-level generics and bounds become explicit method arguments

Trait methods remain references to separately translated functions, but the trait record contains their translated signatures. The extractor computes the method-specific generics after the trait-level prefix and, for Lean, uses `forall` for method-level generic parameters.

The fixture's

```rust
trait OfType {
    fn of_type<T: ToType<Self>>(x: T) -> Self;
}
```

becomes a field whose shape includes both the method type parameter and an explicit `ToType T Self` dictionary. A caller with `T1: OfType` and `T2: ToType<T1>` receives both dictionaries and passes the `ToType` evidence into the method projection.

Trait declaration translation is therefore not a flat list of monomorphic callbacks. Trait-level and method-level binders remain distinct enough to generate higher-rank method fields for supported inputs.

Basis: **source** + preserved **execution** artifact.

### Default methods survive as callable defaults, while concrete impl dictionaries expose normalized methods

The fixture's provided `BoolTrait::ret_true` produces a standalone generated helper named `BoolTrait.ret_true.default`. The concrete impl dictionary for `bool`, however, points at an implementation-specific translated `ret_true` function. This follows the input normalization recorded by the Charon trait report: Charon can materialize inherited default methods as ordinary impl-facing method references before Aeneas extraction.

A downstream consumer should therefore distinguish three related objects:

1. the Rust trait's source-level default body;
2. the generated default helper retained for the trait method;
3. the implementation-facing method reference that fills a concrete dictionary.

Source omission of an override does not imply that the generated impl dictionary lacks that method field.

Basis: **source** + preserved **execution** artifact + companion Charon report.

### Associated constants become dictionary fields in Aeneas's effect model

Trait associated constants are preserved explicitly. `translate_trait_decl` translates their types; the Lean extractor emits each trait constant as a field after applying `mk_result_ty`. An implementation refers to the translated global declaration for the constant and fills the record field, wrapping a non-failing constant with `ok` where needed.

The `WithConstTy` fixture demonstrates both an explicit associated constant and a defaulted one. Its generated trait structure contains `LEN1 : Result Std.Usize` and `LEN2 : Result Std.Usize`; the concrete dictionary fills `LEN1` from the impl's generated constant and `LEN2` from the generated default helper. The generic `use_with_const_ty1` function reads `WithConstTyInst.LEN1` from its dictionary.

The `Trait::LEN` examples additionally show impl constants depending on const generics or prerequisite trait dictionaries. The dictionary model therefore preserves the dependency needed to compute the selected associated constant, not just its Rust name.

Basis: **source** + preserved **execution** artifact.

### Most associated types are lifted into ordinary trait parameters before Aeneas extraction

The exact pinned Aeneas source states that most associated types are removed by Charon's `--remove-associated-types` transformation. The resulting Lean output reflects that normalization.

Rust `WithConstTy` declares associated types `V` and `W`, but generated Lean uses:

```lean
structure WithConstTy (Self : Type) (Self_V : Type) (Self_W : Type)
  (LEN : Std.Usize) where
  ...
```

Similarly, the supertrait fixture carries `W` as a type parameter on `ParentTrait0`, while `ChildTrait` receives an additional parameter representing the parent-associated type. `IntoIterator` receives `Self_Item` and `Self_IntoIter` as parameters and stores the `Iterator Self_IntoIter Self_Item` dictionary as evidence.

This means a common Rust projection such as `T::W` is represented in generated Lean by an ordinary type parameter tied to the relevant dictionary. An equality constraint such as `WithConstTy<32, V = u32>` can therefore appear as a concrete type argument (`Std.U32`) in the dictionary type rather than as an equality proof over a Lean projection.

This is a Charon/Aeneas normalization contract, not a general theorem that Rust associated types are definitionally equal to extra parameters.

Basis: Aeneas **source** + preserved **execution** artifact + companion Charon **source** report.

### Residual associated types, GATs, and associated-item evidence are a known unsupported boundary

`SymbolicToPure.translate_trait_decl` checks whether associated types survived Charon preprocessing. For a non-builtin trait it emits a warning that the generated code will likely be incorrect. The source says this can happen with mutually recursive traits and GATs. It also asserts that a retained associated type has no binder parameters and no implied trait clauses.

`SymbolicToPureTypes.translate_trait_ref_kind` is stricter for retained `ItemClause` evidence: it states that Charon's associated-type removal normally removes item clauses except for GATs, then raises `Generic Associated Types are not supported yet`.

The checked-in `mutually-recursive-traits` fixture is marked as a Lean known failure. Its preserved `.lean.out` reports the exact associated-type warning for `Trait1` and says Aeneas cannot handle such types today.

For the pinned release, “Aeneas supports associated types” is therefore too broad. The supported common path is primarily **associated-type elimination/lifting before Aeneas**, followed by ordinary type parameters and dictionaries. Cases that escape that normalization are not established as semantically correct.

Basis: **source** + preserved known-failure **execution** artifact.

### Dynamic trait evidence is rejected in the functional translation

Charon's trait representation has a distinct `Dyn` proof/evidence case. At this Aeneas revision, `translate_trait_ref_kind` raises `Dynamic trait types are not supported yet` when it encounters that evidence. A separate type-translation path likewise rejects dynamic trait types.

A report or verifier built on this functional translation cannot infer support for Rust `dyn Trait` semantics merely because Charon can represent trait-object evidence. Charon's representational coverage and Aeneas's accepted semantic subset differ here.

Basis: **source**.

### Supported builtin/auto evidence is narrower than Charon's full trait-proof taxonomy

Aeneas's pure `builtin_impl_data` has explicit cases for `Copy`, `Clone`, `DiscriminantKind`, and `Fn`/`FnMut`/`FnOnce`. `translate_trait_ref_kind` maps supported Charon builtin/auto evidence into those cases, and Lean extraction prints dedicated builtin dictionary names, with special argument reshaping for the `Fn*` family.

This is not a claim that all auto/builtin traits are modeled by the functional backend. The pure representation is a selected subset. The standard-library/external-model report should remain the authority for which external traits and implementations have models at this pin.

Basis: **source**.

### Unknown trait evidence fails rather than becoming an unconstrained dictionary

Charon can preserve an unknown/error trait-proof case. Aeneas maps Charon `UnknownTrait` to a translation error in `translate_trait_ref_kind`; `ExtractTypes` likewise treats its pure `UnknownTrait` case as an admission/error path rather than valid evidence.

This is a useful fail-closed boundary for interpreting a successful translated function: an unresolved trait proof is not silently accepted as an arbitrary Lean dictionary by this path. It does not establish whole-crate fail-closed behavior, because declaration-level translation failures can still cause individual declarations to be omitted as described below.

Basis: **source**.

### Trait declarations and implementations can fail independently and be omitted

`Translate.translate_crate_to_pure` maps trait declarations and trait implementations separately. For each declaration or impl, it catches an Aeneas translation failure, reports a warning, and returns `None`; successful entries continue into the translated crate.

The same pattern exists for functions elsewhere in the pipeline. Consequently a generated Lean module can coexist with a failed trait or impl translation. Coverage-sensitive consumers must account for the source/LLBC declarations expected and the translated declarations actually emitted. Presence of one trait dictionary or one successful output module is not a completeness certificate for all traits in the crate.

Basis: **source**.

### Upstream overview documentation is conceptually useful but imprecise about the exact Lean encoding

The pinned `documentation/aeneas-overview.md` says that traits are translated to Lean type classes. The checked-in generated `Traits.lean` and extraction source are more precise for the exact release: ordinary translated traits are Lean `structure`s, trait bounds are explicit dictionary parameters, and impls are reducible `def`s. The golden contains neither the ordinary `class`/`instance` pattern nor implicit instance synthesis for these examples.

A future agent should therefore use the overview for the broad functional-translation model but use pinned source and generated artifacts when the distinction between explicit dictionaries and Lean typeclass search matters to proof architecture or source correspondence.

Basis: upstream **documentation** compared with **source** and preserved **execution** artifact.

## Boundaries

- No fresh Charon, Aeneas, Lean, Lake, or rustc execution was performed.
- Checked-in `.lean` and `.lean.out` files are preserved upstream artifacts, not new execution observations.
- The report covers the functional/pure backend at the exact pin. It does not establish trait semantics for a future separation-logic or unsafe-Rust backend.
- It does not prove semantic soundness of Rust trait dispatch or of Charon's selected trait evidence. It records how the pinned Aeneas consumes and emits that evidence.
- It does not inventory every standard-library trait model. The existing Aeneas library-model report owns that question.
- It does not establish arbitrary support for associated types. The common successful fixtures use Charon's associated-type removal/lifting; residual associated types and GAT-related evidence have explicit failure/warning paths.
- It does not establish `dyn Trait` support. Dynamic trait evidence is explicitly rejected by the inspected translation path.
- It does not claim that all Charon builtin/auto evidence is supported. Aeneas's pure builtin cases are enumerated and narrower.
- It does not establish support for negative trait bounds or every unstable trait-system feature. The companion Charon trait report records upstream representation limits before the Aeneas boundary.
- It does not fully characterize recursive trait implementations. The extractor has a Lean-specific recursive-impl path, but this report did not establish its acceptance or semantic envelope with fresh examples.
- It does not establish that a successful crate-level translation emitted every trait declaration, impl, or function; per-declaration failure can omit items.
- The generated naming scheme is illustrated only where needed to explain dictionary flow. The separate item-to-Lean-name report should own complete naming rules.
- The scalar/data type mapping is illustrated only where needed to explain trait parameters. The separate Rust-types-to-Lean-types report should own complete type mapping.

## Evidence

**Primary Aeneas source:** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/symbolic/SymbolicToPure.ml`, blob `95ba91f539e48009efa420dfa956c4c55581cb3a`: `translate_trait_decl` and `translate_trait_impl`; associated-type warning and residual-associated-type assertions; parent-clause, constant, and method translation.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: `translate_trait_ref_kind`, `translate_trait_clause`, generic-parameter translation, associated-type projection translation, GAT/dyn/unknown rejection, and supported builtin/auto evidence.
- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: `trait_instance_id`, `trait_decl`, `trait_impl`, generic parameters/arguments, and builtin trait metadata.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: trait declaration and implementation extraction; trait structures, parent/constant/type/method fields, reducible implementation definitions, and method/default extraction.
- `src/extract/ExtractTypes.ml`, blob `371717638f4298cc9c488b31a597608f9bf5089c`: trait declaration/reference extraction and concrete/clause/parent/builtin dictionary printing.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: independent translation/filtering of trait declarations and trait implementations.

**Pinned documentation:** `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`; useful for the intended functional model, but its “Lean type classes” wording is less precise than the exact generated representation described above.

**Preserved Rust/Lean execution fixture:**

- `tests/src/traits.rs`, blob `a20f6ee91960cbacf99e8899a32e789f7b855671`.
- `tests/lean/Traits.lean`, blob `d234936b72231024fbccf0030a08023836e5eb6e`.

Together these preserve required and provided methods, generic bounds, `where` clauses, generic impls, trait methods with their own bounds, associated constants and defaults, associated types after lifting, associated-type equality, supertraits, selected concrete/generic dispatch, and const-generic trait implementations.

**Preserved known-failure fixture:**

- `tests/src/mutually-recursive-traits.rs`, blob `074ff639d23a8eca640a8f0ea1b639da269cf894`.
- `tests/src/mutually-recursive-traits.lean.out`, blob `d7d6c54d81761d6020aa8627592340ef43cc78f4`.

The output records the pinned Aeneas warning that associated types surviving preprocessing can arise with mutually recursive traits/GATs and are not handled correctly.

No evidence in this report is fresh **execution**.

## Revalidation

For a future Aeneas/Charon pin, first resolve both exact commits. Then diff these narrow implementation points:

1. `SymbolicToPureTypes.translate_trait_ref_kind` and `trait_instance_id` to see which Charon proof/evidence forms remain accepted;
2. `SymbolicToPure.translate_trait_decl` and `translate_trait_impl`, especially the associated-type warning/assertions and parent/constant/method handling;
3. `Pure.trait_decl` and `Pure.trait_impl` for dictionary contents;
4. Lean trait declaration/implementation extraction in `src/extract/Extract.ml` and trait-reference extraction in `ExtractTypes.ml`;
5. the checked-in `traits.rs` → `Traits.lean` golden;
6. the `mutually-recursive-traits` known-failure output.

On a capable execution surface, regenerate one compact fixture that contains: a required method, a provided/default method, a generic bound, a `where`-clause bound on a compound type, a method-level generic bound, a generic impl, a supertrait, an associated constant with a default, an associated type with a bound, an associated-type equality constraint, a concrete call, and a generic call. Preserve Rust, LLBC, generated Lean, diagnostics, exact commands/revisions, and hashes.

Run separate negative probes for (a) a GAT, (b) mutually recursive traits whose associated type survives Charon's removal pass, and (c) a `dyn Trait` call. The positive golden should establish dictionary shape and dispatch for the supported sample; the negative probes should establish only the tested rejection/warning boundary. Do not generalize either result to untested trait-system features.