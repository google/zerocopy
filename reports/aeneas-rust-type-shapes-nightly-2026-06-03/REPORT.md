# Rust type shapes in Aeneas Lean output at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, Rust types do not cross into Lean by a layout-preserving encoding. Aeneas first maps Charon types into its pure type language and then prints those pure types as Lean. That pipeline deliberately erases some Rust structure and rejects some source types.

For ordinary forward function inputs and outputs, the pinned implementation maps scalar primitives to Aeneas scalar types, tuples to products, arrays to `Array T N`, slices to `Slice T`, generic type parameters to Lean type parameters, `()` to `Unit`, and `!` to `Never`. It removes `Box` and ordinary reference constructors. Mutable-reference effects reappear through generated backward functions rather than through the target type itself. Structs and enums become logical Lean data declarations rather than Rust layout models. Raw pointers retain pointee type and mutability as `ConstRawPtr` or `MutRawPtr`, but representability does not imply usable pointer semantics: raw-pointer dereference is explicitly unsupported at this revision.

Function-like types require a sharper distinction. A Rust function-pointer type (`fn(...) -> ...`, Charon `TFnPtr`) is unsupported by the type translators examined here. A regular function *item* (`TFnDef`) can become an Aeneas pure arrow in the forward-function translator when its effect assumptions are satisfied. Aeneas also creates pure arrow types for its own generated functions, including backward functions. Therefore the presence of `→` in generated Lean does not establish support for Rust function pointers.

Generic associated types are unsupported in the examined translation path. Non-GAT associated types can remain pure trait projections, but the paired Charon preprocessing normally lifts associated types into explicit type parameters before Aeneas sees them; the checked-in Lean fixtures show those parameters carried by trait dictionaries. The mapping is therefore context-sensitive: function signatures, ADT fields, generated helper types, trait projections, and dynamic-trait values do not all use the same source-to-target rule.

No fresh Charon, Aeneas, Lean, Lake, or rustc execution was performed. The report uses exact pinned implementation source and checked-in generated Lean artifacts.

## Applicability

This report applies to Aeneas `nightly-2026.06.03` at `ac9f1bc5262a5e4ff1e24ca78617121382202727`, with the Aeneas-paired Charon input producer `a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`). It records the Lean backend selected by current Anneal research; it does not claim that later Aeneas revisions preserve these encodings.

The report covers the type-shape question in `google/zerocopy#3720`: scalars, tuples, structs, enums, arrays, slices, references, raw pointers, function pointers, unit/never, generics, and associated types. It also records nearby `Box`, dynamic-trait, and function-item behavior where those distinctions prevent a misleading type map.

The mapping is not a Rust ABI model. In particular, removing references or `Box`, simplifying tuple structure, or representing a struct as a Lean structure says nothing by itself about Rust object layout, padding, provenance, aliasing, drop behavior, or allocation identity. Those properties require separate semantic evidence.

Aeneas has more than one type-translation context. `translate_fwd_ty` handles types seen in ordinary forward function signatures and supports cases that `translate_sty`, used when translating type declarations and related signature material, rejects. The table below states the relevant context where that distinction matters.

## Findings

### The mapping is a semantic translation through Aeneas pure types

The pinned pure AST has these type forms: ADTs/builtins, type variables, literals, arrows, trait-associated-type projections, never, dynamic-trait predicates, and an error form. Its builtin type set adds Aeneas-specific `Result`, control-flow, error, fuel, arrays, slices, strings, and raw-pointer markers while deliberately omitting `Box`.

`translate_fwd_ty` is the principal source-to-pure mapping for forward function inputs and outputs. `ExtractTypes.extract_ty` then prints the pure type for the selected backend. The resulting Lean type is therefore downstream of Aeneas's semantic abstraction, not a direct spelling conversion from Rust.

Basis: **source** (`src/pure/Pure.ml`; `src/symbolic/SymbolicToPureTypes.ml`; `src/extract/ExtractTypes.ml`).

### The core Rust-to-Lean type map at this pin

| Rust/Charon shape | Aeneas pure / Lean shape | Important qualification |
| --- | --- | --- |
| `bool`, `char` | literal type / `Bool`, `Char` | Direct scalar target types. |
| signed and unsigned integers | literal integer type / Lean `Std.I*` or `Std.U*` names | Generated fixtures show, for example, `u32 -> Std.U32` and `usize -> Std.Usize`. |
| floating-point scalars | literal float type / backend float name | The type printer has a direct float-type branch; this report did not exercise float operations. |
| `()` | empty tuple / `Unit` | The Lean extractor prints an empty tuple type as `Unit`. |
| `!` | `TNever` / `Never` | Direct pure and Lean forms exist. |
| `(T1, T2, ...)` | pure tuple / Lean product `T1 × T2 × ...` | `mk_simpl_tuple_ty` simplifies a one-component tuple representation to the component type. |
| `struct` | pure structure / Lean `structure` in the ordinary record case | Logical data, not Rust layout. |
| `enum` | pure enum / Lean `inductive` | Logical variants, not Rust discriminant/niche layout. |
| tuple struct | configurable pure type-declaration simplification; Lean commonly emits a product | `Config.use_tuple_structs` is `true` at this pin; checked-in `Adt.lean` shows a multi-field tuple struct as a product and an empty tuple struct as `Unit`. |
| `[T; N]` | builtin array / `Array T N` | `N` is preserved as a translated const generic/value. |
| `[T]` | builtin slice / `Slice T` | Checked-in output uses `Slice T`. |
| `Box<T>` | `T` | `Box` is deliberately eliminated. |
| `&T` | forward type of `T` | Ordinary reference constructor and mutability do not survive in the forward type. |
| `&mut T` | forward type of `T` | Mutation/ownership flow is reconstructed by generated backward functions. |
| `*const T` | builtin const raw pointer / `ConstRawPtr T` | Type is representable, but raw-pointer operations remain restricted. |
| `*mut T` | builtin mutable raw pointer / `MutRawPtr T` | Raw-pointer dereference is explicitly unsupported. |
| type parameter `T` | pure type variable / Lean `T : Type` | Type generics are retained. |
| const generic | pure const generic / Lean value parameter | Arrays show `N` flowing into `Array T N`; const-generic parameters keep their scalar type. |
| `fn(...) -> ...` function pointer (`TFnPtr`) | unsupported | Both signature/type-declaration and forward translation paths reject `TFnPtr` with “Arrow types are not supported yet”. |
| regular function item (`TFnDef`) used as a forward value | may become a pure arrow | The forward translator resolves the referenced function, translates its signature, checks effect assumptions, substitutes generics, then constructs arrows. This is not function-pointer support. |
| associated type projection | `TTraitType` or, normally after Charon preprocessing, an explicit associated-type parameter in generated Lean | Charon's `--remove-associated-types` usually lifts ordinary associated types; GAT item clauses are unsupported. |
| `dyn Trait` in a forward value | pure `TDynTrait`; Lean `Dyn (fun _dyn => Trait _dyn ...)` for the supported shape | Type-declaration/signature translation is stricter and rejects dynamic trait types in `translate_sty`. |

Basis: **source** + checked-in generated **execution** artifacts preserved upstream. The artifacts were generated before this observation; they were not regenerated here.

### Scalars, unit, never, and tuples are direct target-level shapes after simplification

`ExtractTypes.extract_literal_type` prints booleans and characters with the backend names, prefixes signed and unsigned Lean integer names with `Std.`, and has a direct float-type branch. The pure language also carries mathematical natural and integer types, printed as `ℕ` and `ℤ`; those are Aeneas pure types rather than an assertion that ordinary Rust integers become unbounded integers.

`ExtractTypes.extract_ty` prints `TNever` as Lean `Never`. Its tuple branch prints an empty tuple as `Unit` and a nonempty pure tuple as a product using `×`. Earlier, `translate_fwd_ty` calls `mk_simpl_tuple_ty`; the source comment explicitly notes that a one-type tuple representation is simplified to the type itself.

The checked-in `Arrays.lean` artifact confirms several ordinary cases together: `u32` appears as `Std.U32`, `usize` as `Std.Usize`, generic `T` as `{T : Type}`, and Rust functions returning `()` produce `Result Unit`.

Basis: **source** (`src/extract/ExtractTypes.ml`, `src/symbolic/SymbolicToPureTypes.ml`) + preserved generated artifact (`tests/lean/Arrays.lean`).

### Structs and enums are logical declarations, with tuple structs simplified separately

The type-declaration translator maps supported Charon structures and enums into Aeneas pure structures/enums. The Lean extractor prints ordinary structures and inductives from those pure declarations. This mapping does not preserve Rust layout metadata.

Tuple structs are intentionally eligible for another simplification. `Config.use_tuple_structs` is `true` at the pinned revision. In the checked-in `Adt.lean`, a six-field tuple struct becomes a six-component Lean product, while an empty tuple struct becomes a reducible alias for `Unit`. Ordinary record `Struct { len: usize }` becomes a Lean `structure` whose field has type `Std.Usize`.

This distinction matters for source correspondence: “Rust struct -> Lean structure” is not universal even within the supported struct subset.

Basis: **source** (`src/Config.ml`, `src/extract/ExtractTypes.ml`) + preserved generated artifact (`tests/lean/Adt.lean`).

### Arrays preserve length; slices do not carry a length index

`translate_fwd_ty` maps a Rust array to builtin `TArray` with two pieces of generic state: the translated element type and translated constant length. A slice becomes builtin `TSlice` with only its translated element type.

The checked-in `Arrays.lean` artifact makes the resulting Lean shapes concrete. Rust `[T; 32]` becomes `Array T 32#usize`; Rust `[T]` becomes `Slice T`. Generic functions such as `array_len<T>` therefore have Lean inputs of the form `Array T 32#usize`, while `shared_slice_len<T>` takes `Slice T`.

The same artifact also shows how reference erasure composes with arrays and slices: `&[T; 32]` has forward input `Array T 32#usize`, and `&[T]` has forward input `Slice T`.

Basis: **source** (`src/symbolic/SymbolicToPureTypes.ml`) + preserved generated **execution** artifact (`tests/src/arrays.rs` with `tests/lean/Arrays.lean`).

### Ordinary references disappear from forward types; mutable effects become arrows elsewhere

Both shared and mutable Charon references match the same `translate_fwd_ty` branch: Aeneas recursively translates the referent and drops the reference constructor. The type alone therefore cannot tell `&T` from `&mut T`.

Mutable-reference semantics are represented elsewhere. The translation computes backward signatures from region groups and constructs pure arrow types that propagate final borrowed values back to their owners. The existing `aeneas-rust-to-lean-translation-nightly-2026-06-03` report documents that mechanism in depth; this report records its consequence for the type map.

`Arrays.lean` gives compact examples. A shared array reference used by `array_to_shared_slice_` appears as `Array T 32#usize -> Result (Slice T)`. Its mutable counterpart returns a slice paired with a backward function, `Slice T → Array T 32#usize`.

Basis: **source** + preserved generated artifact. The claim about ownership/update semantics is not inferred from the erased Lean type alone; it uses the separate backward-signature machinery.

### Raw pointers retain a marker type but do not gain general pointer semantics

Aeneas maps Charon raw pointers to a dedicated pure builtin with the translated pointee and const/mut distinction. The Lean builtin-name table prints those types as `ConstRawPtr` and `MutRawPtr`.

`Pure.ml` explains why this marker exists: raw pointers do not naturally fit the pure world, but some signatures contain them, so the pure language keeps a dedicated type and expects such functions not to be used blindly. The interpreter separately rejects dereference with the explicit error that Aeneas does not yet support dereferencing raw pointers. The checked-in `raw_pointers.lean.out` preserves that failure.

A future agent must therefore separate **type representability** from **operation support**. Seeing `ConstRawPtr T` or `MutRawPtr T` in generated Lean is not evidence that Rust raw-pointer behavior has been modeled.

Basis: **source** (`src/pure/Pure.ml`, `src/symbolic/SymbolicToPureTypes.ml`, `src/extract/ExtractBase.ml`, `src/interp/InterpPaths.ml`) + preserved known-failure artifact (`tests/src/raw_pointers.lean.out`).

### Rust function pointers are unsupported even though Aeneas emits Lean arrows

`translate_fwd_ty` handles `TFnPtr` by raising “Arrow types are not supported yet”. `translate_sty`, used for type declarations and related signature translation, rejects both `TFnDef` and `TFnPtr` with the same limitation. A Rust field or signature position routed through that stricter translator therefore cannot be justified merely because Lean supports arrows.

Regular function items are different. In the forward translator, `TFnDef` for a regular function can be resolved to the referenced Aeneas function declaration. Aeneas translates that declaration's signature, checks effect assumptions, substitutes the item's generics, and builds a pure arrow type with `mk_arrows`. Builtin and trait-method function items take unimplemented branches there.

Aeneas also uses `TArrow` internally for generated functions. `ExtractTypes.extract_ty` prints `TArrow` as Lean `→`; backward functions for mutable borrows are common examples. Thus these are three separate facts:

1. Lean arrows exist in generated code.
2. some regular Rust function *items* can become pure arrows in a forward-value context;
3. Rust `fn` pointer types are unsupported in the examined translators.

Collapsing those facts into “function types are supported” would be wrong for this pin.

Basis: **source** (`src/symbolic/SymbolicToPureTypes.ml`, `src/pure/Pure.ml`, `src/extract/ExtractTypes.ml`).

### Generic type, const, and trait parameters survive, while regions do not become Lean type parameters

`translate_generic_params` explicitly discards the Charon region-parameter list and translates type parameters, const generics, trait clauses, and associated-type constraints into Aeneas generic/predicate structures. This is consistent with the broader functionalization model: Rust regions guide borrow translation but do not appear as ordinary Lean type parameters.

Generated fixtures show the surviving forms. `Arrays.lean` uses `{T : Type}` and length values such as `32#usize`; `Traits.lean` passes trait obligations as explicit structure-valued dictionary arguments. Const-generic trait examples preserve lengths as `Std.Usize` parameters.

The absence of a lifetime parameter in generated Lean is therefore not evidence that lifetime information was irrelevant to translation. It says the resulting proof-facing generic signature no longer represents regions as target-language type parameters.

Basis: **source** (`src/symbolic/SymbolicToPureTypes.ml`) + preserved generated artifacts (`tests/lean/Arrays.lean`, `tests/lean/Traits.lean`).

### Associated types are supported in bounded forms, but GATs are not

The pure type language has `TTraitType`, a trait-reference plus associated-type identifier. The type translators preserve ordinary associated-type projections after translating the trait reference, but require the extra associated-type generic-argument list to be empty.

The stricter trait-reference translation rejects Charon `ItemClause` with an explicit “Generic Associated Types are not supported yet” error. That gives a clear boundary: ordinary associated types and constraints have machinery at this pin; GAT item clauses do not.

The paired Charon preprocessing explains the dominant generated shape. Aeneas source says that Charon's `--remove-associated-types` usually lifts associated types into parameters of the trait definition; the residual associated-type machinery mainly handles cases that preprocessing could not remove. The generated `Traits.lean` artifact matches that account. Rust `ParentTrait0::W` becomes an extra Lean type parameter such as `Self_W` or `Clause0_Clause0_W`, and the trait dictionary is parameterized by it. `IntoIterator::Item` and `IntoIterator::IntoIter` similarly become explicit type parameters with an `Iterator` dictionary linking the two. A nested projection such as `<Self::U as WithTarget>::Target` becomes another explicit type parameter in the `ChildTrait2` structure.

`ExtractTypes.extract_ty` can also print a surviving pure `TTraitType` projection. `Config.parameterize_trait_types` defaults to `false` at this pin, so that extractor path is not simply hidden by a global “parameterize associated types” setting. The ordinary fixture shapes instead agree with Charon's earlier associated-type removal/lifting pass. Aeneas warns that associated types left in a non-builtin trait declaration are unusual and may arise with mutually recursive traits or GATs; it says it cannot handle such residual types reliably.

Basis: **source** (`src/pure/Pure.ml`, `src/symbolic/SymbolicToPureTypes.ml`, `src/symbolic/SymbolicToPure.ml`, `src/extract/ExtractTypes.ml`, `src/Config.ml`) + preserved generated artifact (`tests/src/traits.rs` with `tests/lean/Traits.lean`).

### Dynamic-trait values are supported in a narrow forward-type shape

`translate_fwd_ty` maps a Charon dynamic-trait binder to pure `TDynTrait`, while `translate_sty` rejects dynamic trait types. The Lean extractor accepts a narrow dynamic predicate shape and prints a `Dyn` package parameterized by a predicate over the hidden concrete type.

The checked-in `Dyn.lean` artifact shows `Box<dyn Trait>` translated to `Dyn (fun _dyn => Trait _dyn)`. It also shows a generic dynamic `Into<V>` package. Because `Box` is erased, the target shape is the dynamic package itself rather than a boxed pointer.

This is another example of context sensitivity: a dynamic trait can be representable as a forward value while remaining unsupported in the type-declaration translation path.

Basis: **source** + preserved generated artifact (`tests/src/dyn.rs` with `tests/lean/Dyn.lean`).

## Boundaries

- **No fresh execution.** The source and checked-in generated artifacts were inspected at exact revisions, but this run did not invoke Charon, Aeneas, Lean, Lake, rustc, or the corpus validator against a materialized candidate tree.
- **This is not a semantic-soundness proof.** The report records implemented type shapes and explicit support boundaries. It does not prove that every accepted translation faithfully models Rust semantics.
- **This is not a layout/ABI map.** Logical structures, inductives, products, erased boxes, and erased references do not preserve Rust layout merely by sharing source-level data.
- **Function pointers are unsupported at the examined translators.** Support for arrows in the pure AST, generated backward functions, closures, or some function items does not change that result.
- **Function items are only partially characterized here.** The `TFnDef` forward branch has explicit unimplemented cases and effect assertions. This report does not claim every regular function item is accepted.
- **Raw-pointer operations are not generally supported.** The type marker exists, but dereference is explicitly rejected, and other raw-pointer operations have their own narrower constraints.
- **GATs are unsupported in the examined trait-type path.** Ordinary associated types and constraints are not evidence for generic associated type support.
- **Nested mutable borrows in ADTs remain restricted.** Type declaration translation asserts that ADTs containing nested mutable borrows are unsupported; the separate backward-signature machinery does not remove that boundary.
- **Type aliases are intentionally out of scope.** Issue #3720 tracks Aeneas type-alias handling as a separate research item.
- **The full supported/unsupported Rust matrix is intentionally out of scope.** That inventory is broader and, at the desired granularity, benefits from fresh executable matrix probing on a capable surface.
- **Backend-specific details outside Lean are out of scope.** The pure type language supports several extraction backends, but this report records Lean behavior for Anneal research.

## Evidence

**Source — Aeneas type translation.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: `translate_sty`, `translate_generic_params`, `translate_fwd_ty`, generic-argument translation, backward-type traversal. This is the primary source for source-type acceptance, erasure, and context-sensitive unsupported cases.
- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: pure `builtin_ty`, `ty`, generic arguments/parameters, associated-type projections, arrows, never, and dynamic predicates.
- `src/symbolic/SymbolicToPure.ml`, blob `95ba91f539e48009efa420dfa956c4c55581cb3a`: trait-declaration translation and the explicit account of Charon `--remove-associated-types` preprocessing.
- `src/extract/ExtractTypes.ml`, blob `371717638f4298cc9c488b31a597608f9bf5089c`: Lean printing for literals, tuples, arrows, surviving associated-type projections, never, dynamic traits, and data declarations.
- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: Lean builtin type names, including `Array`, `Slice`, `Str`, `MutRawPtr`, and `ConstRawPtr`.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: pinned defaults relevant to type presentation, including tuple-struct simplification and trait-type parameterization.
- `src/interp/InterpPaths.ml`, blob `ec23375a5ca0680500daea0248d2372c9901156e`: the pinned interpreter's explicit raw-pointer-dereference rejection. The exact statement is also preserved in the checked-in raw-pointer failure artifact.

**Preserved generated artifacts — same Aeneas revision.**

- `tests/src/arrays.rs`, blob `478af7171452826436f56f12c88493debac8e0d0`, with `tests/lean/Arrays.lean`, blob `00b7716b63b41c4747889b42f2dee3796d3ab12d`: arrays, slices, scalar names, generic `T`, reference erasure, backward functions, and `Unit`.
- `tests/src/slices.rs`, blob `13bfe864372318725d41e33a4179a74fcfdf1feb`, with `tests/lean/Slices.lean`, blob `f294e70359a20cf3db5022529204fc1102e7aa51`: slice generics and mutable-slice backward shapes.
- `tests/src/adt.rs`, blob `cc31a7085737e5efd8910316d99adbd74d9df32c`, with `tests/lean/Adt.lean`, blob `f99cbd9c162d060dc55ea2614d7d0b8bfa32ca9e`: ordinary structures, tuple-struct product simplification, empty tuple struct as `Unit`.
- `tests/src/traits.rs`, blob `a20f6ee91960cbacf99e8899a32e789f7b855671`, with `tests/lean/Traits.lean`, blob `d234936b72231024fbccf0030a08023836e5eb6e`: generic type parameters, explicit trait dictionaries, associated types represented as extra type parameters, nested associated-type constraints, and const generics.
- `tests/src/dyn.rs`, blob `fa2b29298fcc157e4b05a61098553525fe867f5d`, with `tests/lean/Dyn.lean`, blob `1ca9dd626eea93ec47dee2094febb8541d41c2c3`: dynamic-trait packages and closure-related generated arrow-bearing declarations.
- `tests/src/raw_pointers.rs`, blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`, with `tests/src/raw_pointers.lean.out`, blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`: preserved raw-pointer failure evidence.

**Related corpus evidence.** `reports/aeneas-rust-to-lean-translation-nightly-2026-06-03` on the observed `google/zerocopy` `reference` tree already records the forward/backward borrow translation, logical ADT translation, raw-pointer representability boundary, and trait-dictionary shape. This report narrows and completes the type inventory rather than replacing that semantic report.

No evidence in this report is fresh **execution**. The generated Lean and failure outputs are upstream checked-in artifacts at the pinned source revision.

## Revalidation

For a later Aeneas pin, the cheapest source-level check is a targeted diff rather than a broad repository crawl:

1. Resolve the exact Aeneas and paired Charon revisions.
2. Diff `SymbolicToPureTypes.ml` around `translate_sty`, `translate_generic_params`, `translate_fwd_ty`, and the backward-type traversal. Those branches determine source-type acceptance and most erasures.
3. Diff `Pure.ml` around `builtin_ty` and `ty`. New or removed pure type forms change what the extractor can represent.
4. Diff `ExtractTypes.ml` around `extract_literal_type`, `extract_ty`, and type-declaration extraction, plus `ExtractBase.ml` for Lean builtin type names.
5. Recheck `Config.ml` defaults that affect tuple-struct and trait-associated-type presentation.
6. Compare the pinned `Arrays.lean`, `Adt.lean`, `Traits.lean`, and `Dyn.lean` goldens with their Rust sources; recheck the raw-pointer failure artifact.

On a surface that can execute the toolchain, use a small generated-type fixture rather than the full test suite. Include one value of each relevant class: all scalar families, `()`, `!`, zero/one/multi-element tuples, record/tuple structs, an enum, `[T; N]`, `[T]`, `Box<T>`, `&T`, `&mut T`, both raw-pointer mutabilities, a generic type and const generic, an ordinary associated type plus a GAT control, a regular function item, an `fn` pointer, and a `dyn Trait` value. Preserve the LLBC, generated Lean, exact commands/revisions, and tool output.

That probe establishes accepted forms and generated shapes for the tested revision. It does not by itself prove semantic correctness or general support for every operation over those types.