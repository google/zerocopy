# Aeneas Type Shapes, Type-Alias Erasure, Trait and Closure Dictionaries, Scalar and Collection Primitives, and External Model Registration

## Summary

Aeneas translates a structured subset of safe, generic, and trait-bearing Rust into pure functional Lean specifications by combining Charon LLBC normalization, an intermediate pure type and expression language (`Pure.ml`), semantic pre-passes (`PrePasses.ml`), and an explicit Rust-name-pattern-to-Lean-definition model registry (`Extract.lean` and `ExtractBuiltin*.ml`). Across both the Anneal-pinned Aeneas release (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `nightly-2026.06.03`, paired with `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `0.1.210`) and newer upstream Aeneas source (`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`), this translation is a selective semantic abstraction rather than a layout-preserving ABI encoding or an admission of arbitrary safe or unsafe Rust:

1. **Type shapes and context-sensitive translation (`SymbolicToPureTypes.ml`, `ExtractTypes.ml`)**: Forward function signatures (`translate_fwd_ty`) map Rust scalars to fixed-width or platform-width Lean scalar types (`Std.I*`, `Std.U*`, `Bool`, `Char`), `()` to `Unit`, `!` to `Never`, multi-element tuples to products (`×`) with one-element tuples simplified to their component type (`mk_simpl_tuple_ty`), `[T; N]` to `Array T N`, and `[T]` to `Slice T`. `Box<T>` and ordinary references (`&T`, `&mut T`) are erased in forward types to `T`, while mutable-borrow updates are reconstructed through generated backward function arrows. Structs and enums become logical Lean `structure` and `inductive` declarations (with tuple structs simplified to products or `Unit` when `Config.use_tuple_structs = true`), and unions/opaque/erroneous type declarations become `Opaque`. Raw pointers retain marker types (`ConstRawPtr T`, `MutRawPtr T` or `RawPtr` with a mutability tag), but raw-pointer dereference is rejected in symbolic execution. Function pointers (`TFnPtr`) are rejected (`"Arrow types are not supported yet"`), whereas eligible regular function items (`TFnDef`) in forward value positions and internal backward functions emit Lean arrows (`→`). Dynamic trait values (`TDynTrait`) have a narrow forward representation (`Dyn (fun _dyn => Trait _dyn ...)`) while signature/type-declaration translation (`translate_sty`) rejects `dyn Trait`.
2. **Ordinary type-alias removal (`PrePasses.filter_type_aliases`)**: Although Charon preserves free Rust type aliases as top-level `TypeDeclKind::Alias(Ty)` declarations (and repairs missing projection bounds via `add_missing_alias_clauses` and lifts associated types via `expand_associated_types`), `rustc` has already inlined alias uses at ordinary type positions. Aeneas's `PrePasses.filter_type_aliases` deletes all `Alias` entries from `crate.type_decls` and `TypeGroup (NonRecGroup id)` from `crate.declarations` before concrete interpretation, borrow checking, or pure translation; downstream stages (`TypesAnalysis.ml` and `SymbolicToPureTypes.ml`) treat any surviving `Alias` as an internal invariant violation (`"type aliases should have been removed earlier"`). Consequently, source alias names (`OptNode`, `Key`, `Hash`) disappear completely from generated Lean.
3. **Explicit trait and closure dictionaries (`SymbolicToPure.ml`, `Extract.ml`, `Core/Cmp.lean`, `Core/Ops.lean`)**: Ordinary Rust traits translate to explicit Lean `structure` records rather than Lean `class`/`instance` typeclasses. Generic trait bounds become explicit dictionary value parameters; concrete implementations become `@[reducible] def` record values; supertraits become parent-dictionary fields (`parent_clauses`); associated constants become `Result`-wrapped fields; and most associated types are lifted by Charon's `--remove-associated-types` pass into explicit type parameters on the trait structure (while generic associated types (`ItemClause`), residual unlifted associated types on mutually recursive traits, `Dyn` trait evidence, and `UnknownTrait` proofs are rejected or warn). Operational trait models (`PartialEq`, `Eq`, `PartialOrd`, `Ord`) carry effectful methods without embedded mathematical law fields; proof rules such as `PartialEq.ne.default.spec` take logical law premises explicitly. Closures implement `FnOnce`, `FnMut` (returning `Result (Output × Self)`), and `Fn` dictionaries, supported by Charon-workaround pre-passes (`fix_closure_lifetimes` and single-region `fix_closure_signature_regions`).
4. **Effect interface, scalar arithmetic families, Drop, and collection models (`Primitives.lean`, `Scalar/Core.lean`, `Array.lean`, `SliceDef.lean`, `Vec.lean`)**: At `21345f80fa212c596f6437378d7d57984fa2ea77`, `Result α` is defined as an interaction tree `ITree RustEffect α` with failure constructors `assertionFailure`, `integerOverflow`, `divisionByZero`, `arrayOutOfBounds`, `maximumSizeExceeded`, `panic`, and `undef` (distinct from the auxiliary `MatchResult` view). Machine scalars wrap bitvectors (`8`, `16`, `32`, `64`, `128` bits, and `System.Platform.numBits` for `Usize`/`Isize`), and ordinary, `checked_*`, `wrapping_*`, `overflowing_*`, `saturating_*`, and division operations have distinct failure and return contracts. By default (`Config.drop_as_no_op = true`, overridden by `-eval-drops`), statement-level `Drop` is a no-op while `StorageDead` performs loan/borrow `drop_value` bookkeeping; `UnwindResume` is rejected. `Array`, `Slice`, and `Vec` wrap length-bounded lists (`ListN`) without heap capacity or allocator state, returning `(x, fun x => ...)` pairs for mutable indexing; notably, `Vec.insert` at `21345f80fa212c596f6437378d7d57984fa2ea77` enforces `i < length`, excluding end insertion (`i == length`).
5. **External and standard-library model registration (`Extract.lean`, `ExtractBuiltinLean.ml`, `ExtractBuiltin.ml`)**: Lean definitions register Rust name patterns via `rust_type`, `rust_fun`, `rust_const`, `rust_trait`, and `rust_trait_impl` attributes with semantic projection metadata (`keepParams`, `keepTraitClauses`, `canFail`, `lift`, `hasDefault`). Running `make extract-lean-std` (`lake exe extract`) inspects the Lean environment and regenerates `src/extract/ExtractBuiltinLean.ml`, which at `ac9f1bc5262a5e4ff1e24ca78617121382202727` contains 357 literal registrations (35 types, 212 functions, 45 trait declarations, 65 trait implementations: 319 `core::`, 37 `alloc::`, 1 `std::`) augmented by generic families in `ExtractBuiltin.ml` and distinct from LLBC internal builtins in `src/llbc/Builtin.ml`. Matched builtins are filtered out of unresolved opaque declarations (`Translate.ml`), while unmatched external items use the `-split-files` template workflow (`TypesExternal_Template.lean`, `FunsExternal_Template.lean`) or become opaque assumption boundaries (`ExtractBase.ml`). Model registration is an unverified semantic interface contract, not a proof of equivalence to Rust's implementation.

## Applicability

This report synthesizes evidence across the three primary subjects recorded in `REPORT.json` and their associated toolchains:

| Subject | Repository & Immutable Revision | Version / Release / Toolchain | Role in this Report |
|---|---|---|---|
| Aeneas Lean external and standard-library model registry selected by Anneal | `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` | `nightly-2026.06.03` (Lean toolchain `leanprover/lean4:v4.30.0-rc2`) | Pinned Aeneas baseline consumed by Anneal (e.g., at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`). Establishes the 357-entry generated `ExtractBuiltinLean.ml` fingerprint, the Rust-to-Lean type-shape map, `PrePasses.filter_type_aliases`, trait dictionary extraction, and checked-in `tests/lean/*.lean` fixtures. |
| Aeneas-paired Charon input producer | `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` | `0.1.210` | Paired Charon revision pinned by Aeneas `nightly-2026.06.03`. Establishes `TypeDeclKind::Alias(Ty)` representation, `add_missing_alias_clauses`, `expand_associated_types`, and `--remove-associated-types` preprocessing before Aeneas translation. |
| Aeneas current interfaces and models | `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` | Declares `charon-pin` `1aebab5f03a58067e5dc0ede2fec584117f54964` and Lean toolchain `leanprover/lean4:v4.35.0-rc4` (inspected alongside coordinating Charon source `9e95cf318e3a2964fcf5e03104cde5b718f98ea5`) | Newer upstream Aeneas source establishing exact line-level invariants for `SymbolicToPureTypes.ml`, universe keyword emission (`Type _` vs. `Type`), closure lifetime repair pre-passes, `Core/Cmp.lean` and `Core/Ops.lean` dictionaries, `ITree RustEffect` `Result`, bitvector scalar arithmetic families, `Drop`/unwind statement handling, and `Array`/`Slice`/`Vec` collection models. |

### Shared vs. Revision-Specific Behaviors

- **Shared across `ac9f1bc5262a5e4ff1e24ca78617121382202727` and `21345f80fa212c596f6437378d7d57984fa2ea77`**:
  - Two-stage type translation through `Pure.ml` (`SymbolicToPureTypes.ml` followed by `ExtractTypes.ml`), erasing `Box<T>` and `&T`/`&mut T` in forward types while reconstructing mutable borrows via backward arrows.
  - Pre-pass deletion of `TypeDeclKind::Alias` (`PrePasses.filter_type_aliases`) and downstream invariant rejection of surviving aliases in `TypesAnalysis.ml` and `SymbolicToPureTypes.ml`.
  - Translation of Rust traits into explicit Lean `structure` dictionaries, trait bounds into explicit value arguments, trait implementations into `@[reducible] def` records, supertraits into parent-dictionary fields, and reliance on Charon's associated-type lifting (`--remove-associated-types`) with rejection of GAT `ItemClause` and `UnknownTrait`.
  - Attribute-driven model registration in `backends/lean/Aeneas/Extract/Extract.lean` (`rust_type`, `rust_fun`, `rust_const`, `rust_trait`, `rust_trait_impl`) with `FunInfo` metadata (`keepParams`, `keepTraitClauses`, `canFail`, `lift`, `hasDefault`), regeneration of `src/extract/ExtractBuiltinLean.ml` via `make extract-lean-std` (`lake exe extract`), composition with generic mappings in `src/extract/ExtractBuiltin.ml`, and `-split-files` template generation for missing external models.
- **Revision-specific distinctions**:
  - **Lean toolchain and `Result` representation**: `ac9f1bc5262a5e4ff1e24ca78617121382202727` targets `leanprover/lean4:v4.30.0-rc2`, whereas `21345f80fa212c596f6437378d7d57984fa2ea77` targets `leanprover/lean4:v4.35.0-rc4` and defines `Result α` in `backends/lean/Aeneas/Std/Primitives.lean` as an interaction tree (`ITree RustEffect α`) with `PEmpty`-response failure events rather than a three-constructor inductive `Result` datatype (`MatchResult` is retained only as an auxiliary matching/printing view).
  - **Registry cardinality**: The exact count of 357 literal registrations in `src/extract/ExtractBuiltinLean.ml` (35 types, 212 functions, 45 trait declarations, 65 trait implementations) is a pinned fingerprint of `ac9f1bc5262a5e4ff1e24ca78617121382202727`.
  - **Raw-pointer Pure AST representation**: At `ac9f1bc5262a5e4ff1e24ca78617121382202727`, raw pointers print as `ConstRawPtr T` and `MutRawPtr T`; at `21345f80fa212c596f6437378d7d57984fa2ea77`, the Lean standard library also exposes `RawPtr` wrapping a value and `Mut`/`Const` mutability tag whose selected scalar cast fails with `Error.undef`.
- **Two meanings of "builtin" in Aeneas**:
  1. LLBC/pure semantic builtins implemented directly inside Aeneas's interpreter and translator (such as special `Box`/array/slice operations in `src/llbc/Builtin.ml`).
  2. External Rust declarations recognized by Rust name pattern and redirected to backend standard-library definitions by `src/extract/ExtractBuiltin*.ml`.
  This report covers the second mechanism in detail and distinguishes it from the first wherever they interact.

## Findings

### 1. Rust-to-Lean Type Shapes and Context-Sensitive Translation

#### 1.1 Semantic Translation Through Aeneas Pure Types

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` and `21345f80fa212c596f6437378d7d57984fa2ea77`, Rust types do not cross into Lean by a layout-preserving encoding. Aeneas first maps Charon LLBC types into its pure type AST (`src/pure/Pure.ml`) and then prints those pure types as Lean (`src/extract/ExtractTypes.ml`). The pure AST (`Pure.ml`) provides type forms for ADTs/builtins (`TAdt`), type variables (`TVar`), literals (`TLiteral`), arrows (`TArrow`), trait-associated-type projections (`TTraitType`), never (`TNever`), dynamic-trait predicates (`TDynTrait`), and an error form (`TError`). Its `builtin_ty` set adds Aeneas-specific `Result`, control-flow, error, fuel, arrays (`TArray`), slices (`TSlice`), strings (`TStr`), and raw-pointer markers (`TRawPtr`) while deliberately omitting `Box`.

Aeneas maintains distinct type-translation contexts in `src/symbolic/SymbolicToPureTypes.ml`:
- `translate_sty` (lines 137–198 at `21345f80fa212c596f6437378d7d57984fa2ea77`) translates types appearing in type declarations and signature material.
- `translate_fwd_ty` translates types seen in ordinary forward function inputs and outputs, supporting cases (such as eligible `TFnDef` function items and narrow `TDynTrait` values) that `translate_sty` rejects.
- Backward/projected type traversal computes region-group signatures for mutable borrows.

Basis: **source** (`src/pure/Pure.ml`, `src/symbolic/SymbolicToPureTypes.ml`, `src/extract/ExtractTypes.ml`).

#### 1.2 Core Rust/Charon-to-Lean Type Map and Feature Matrix

| Rust / Charon Shape | Aeneas Pure / Lean Shape | Context & Material Qualification |
|---|---|---|
| `bool`, `char` | `TLiteral` / `Bool`, `Char` | Direct scalar target types printed by `ExtractTypes.extract_literal_type`. |
| Signed and unsigned integers (`i8`..`i128`, `isize`, `u8`..`u128`, `usize`) | `TLiteral` integer / Lean `Std.I8`..`Std.I128`, `Std.Isize`, `Std.U8`..`Std.U128`, `Std.Usize` | Fixed widths are `8`, `16`, `32`, `64`, `128`; `Usize`/`Isize` use `System.Platform.numBits` (`32` or `64`). Pure AST also has mathematical `ℕ` and `ℤ`, which are internal pure types rather than translations of Rust machine integers. |
| Floating-point scalars (`f16`, `f32`, `f64`, `f128`) | `TLiteral` float / backend float name (`F16`, `F32`, `F64`, `F128`) | `ExtractTypes.extract_literal_type` has a direct float-type printer branch; complete IEEE floating-point operation models were not validated here. |
| `()` | Empty pure tuple / `Unit` | `ExtractTypes.extract_ty` prints an empty tuple type as `Unit`; Rust functions returning `()` produce `Result Unit`. |
| `!` | `TNever` / `Never` | Direct pure and Lean forms exist. |
| `(T1, T2, ...)` | Pure tuple / Lean product `T1 × T2 × ...` | `mk_simpl_tuple_ty` simplifies a 1-component tuple representation to the component type itself. |
| `struct` (record) | Pure structure / Lean `structure` | Logical fields (`tests/lean/Adt.lean`), not a Rust memory-layout, padding, or alignment model. Positivity and recursive grouping are backend concerns. |
| `enum` | Pure enum / Lean `inductive` | Logical variants, not a Rust discriminant or niche-layout model. |
| Tuple struct | Configurable pure type-declaration simplification; Lean commonly emits a product or `Unit` | `Config.use_tuple_structs` is `true` at `ac9f1bc5262a5e4ff1e24ca78617121382202727`; checked-in `tests/lean/Adt.lean` emits a 6-field tuple struct as a 6-component product (`×`) and an empty tuple struct as a reducible alias for `Unit`. |
| `union`, opaque, or error type declarations | `Opaque` | `SymbolicToPureTypes.ml` (lines 274–284 at `21345f80fa212c596f6437378d7d57984fa2ea77`) maps `Union`, `Opaque`, and `Error` declaration kinds to `Opaque` rather than a field-level memory model. |
| `[T; N]` | Builtin `TArray` / `Array T N` | Preserves translated element type `T` and const-generic length `N` (e.g., `Array T 32#usize` in `tests/lean/Arrays.lean`). |
| `[T]` | Builtin `TSlice` / `Slice T` | Carries translated element type `T` without a type-level length index (`tests/lean/Arrays.lean`, `tests/lean/Slices.lean`). |
| `Box<T>` | `T` | `Box` is deliberately eliminated in type translation; `Alloc` models `Box::deref` / `deref_mut` as value and value-plus-replacement-function without heap address, capacity, or OOM semantics. |
| `&T` | Forward type of `T` | Reference constructor and lifetime are erased in forward types (`&[T; 32]` becomes `Array T 32#usize`; `&[T]` becomes `Slice T`). |
| `&mut T` | Forward type of `T` (plus generated backward function arrows) | Forward input is `T`; mutation/ownership updates are returned explicitly or propagated via backward arrows (e.g., returning `Slice T` paired with `Slice T → Array T 32#usize`). Aeneas's `README.md` excludes instantiating generic type parameters with mutable references (including `Self` in trait implementations). |
| `*const T`, `*mut T` | Builtin `TRawPtr` / `ConstRawPtr T`, `MutRawPtr T` (and `RawPtr` wrapper) | Representable in signatures so declarations containing raw pointers can be extracted, but `src/interp/InterpPaths.ml` explicitly rejects raw-pointer dereference (`tests/src/raw_pointers.lean.out`), and selected scalar casts return `Error.undef`. |
| Type parameter `T` | Pure `TVar` / Lean `{T : Type}` or `Type _` | Retained across generic declarations; see Section 1.4 for universe-polymorphism restrictions on generic trait methods and opaque types. |
| Const generic `N` | Pure const generic / Lean scalar value parameter (e.g., `Std.Usize`) | Supported parameter types must be scalar types; selected literal, global, and variable constant-expression kinds translate, while arbitrary const evaluation fails with an unsupported-constant diagnostic. |
| `fn(...) -> ...` function pointer (`TFnPtr`) | **Unsupported** | Both `translate_sty` and `translate_fwd_ty` reject `TFnPtr` with `"Arrow types are not supported yet"`. |
| Regular function item (`TFnDef`) / closure | May become pure `TArrow` in `translate_fwd_ty`; `FnOnce`/`FnMut`/`Fn` trait dictionaries | Rejected in `translate_sty`. In `translate_fwd_ty` (lines 397–425 at `21345f80fa212c596f6437378d7d57984fa2ea77`), an eligible regular function item with no binder regions, an ordinary function ID, and compatible failure effects resolves its declaration signature, substitutes generics, and builds pure arrows via `mk_arrows` (printed as Lean `→`). Builtin and trait-method function items hit unimplemented branches. |
| Associated type projection (`<T as Trait>::Assoc`) | Pure `TTraitType` or, after Charon `--remove-associated-types`, an explicit type parameter on the trait dictionary | Requires empty associated-type generic arguments; Charon `ItemClause` is rejected with `"Generic Associated Types are not supported yet"`. |
| `dyn Trait` | Forward `TDynTrait` / Lean `Dyn (fun _dyn => Trait _dyn ...)` | Accepted in a narrow forward-value shape (`tests/lean/Dyn.lean` maps `Box<dyn Trait>` to `Dyn (fun _dyn => Trait _dyn)` after `Box` erasure), but rejected in `translate_sty`, borrow-projection paths, and `translate_trait_ref_kind` (`"Dynamic trait types are not supported yet"`). |

Basis: **source** (`src/pure/Pure.ml`, `src/symbolic/SymbolicToPureTypes.ml`, `src/symbolic/SymbolicToPure.ml`, `src/extract/ExtractTypes.ml`, `src/extract/ExtractBase.ml`, `src/Config.ml`, `src/interp/InterpPaths.ml`) + preserved generated **execution** artifacts (`tests/lean/Arrays.lean`, `tests/lean/Slices.lean`, `tests/lean/Adt.lean`, `tests/lean/Traits.lean`, `tests/lean/Dyn.lean`, `tests/src/raw_pointers.lean.out`).

#### 1.3 Region Erasure, Region Binders, and Nested Mutable Borrows

In `src/symbolic/SymbolicToPureTypes.ml`:
- `translate_generic_params` and `translate_generic_args` (lines 58–72 at `21345f80fa212c596f6437378d7d57984fa2ea77`) explicitly discard Charon region parameters and arguments while translating type parameters, const generics, trait clauses/references, and associated-type constraints. The source comment notes that region erasure in pure types is sound only because the preceding symbolic execution and region-group decomposition have already accounted for borrows and loans.
- `translate_region_binder` (lines 11–17 at `21345f80fa212c596f6437378d7d57984fa2ea77`) simply extracts `binder_value`. Its source comment explicitly states that de Bruijn index shifting would be required in complex higher-rank/nested region-binding situations and that such cases are not yet handled.
- Type-declaration translation asserts that ADTs containing nested mutable borrows are unsupported, and Aeneas's `README.md` excludes instantiating generic type parameters with mutable references (including `Self` in a trait implementation, which is broader than merely forbidding a direct `id(&mut x)` call).

Basis: **source** (`src/symbolic/SymbolicToPureTypes.ml`, `README.md`).

#### 1.4 Universe Polymorphism Boundaries in Lean Extraction

In `src/extract/ExtractBase.ml` (lines 1460–1477 at `21345f80fa212c596f6437378d7d57984fa2ea77`), `type_keyword` emits `Type _` for universe-polymorphic Lean binders and `Type` (`Type 0`) where Lean cannot infer universe levels. `src/extract/ExtractTypes.ml` (lines 1368–1379) explicitly selects the non-polymorphic `Type` keyword for generic type parameters of trait methods inside trait `structure` fields, as well as for opaque type result sorts. Consequently, universe polymorphism on ordinary top-level generic items does not extend to generic trait methods or associated/opaque types instantiated at higher universes.

Basis: **source** (`src/extract/ExtractBase.ml#L1460-L1477`, `src/extract/ExtractTypes.ml#L1368-L1379`).

---

### 2. Ordinary Type-Alias Handling Across the Charon-to-Aeneas Boundary

#### 2.1 Charon Top-Level `TypeDeclKind::Alias(Ty)` vs. Transparent Use Sites

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/ast/types.rs` (blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`) defines `TypeDeclKind::Alias(Ty)` and documents that an alias declaration appears only in the top-level item list because `rustc` inlines uses of ordinary free type aliases everywhere else. In `charon/src/bin/charon-driver/translate/translate_items.rs` (blob `7964644be017856c6d165545a67bd6ef06e0c85c`), `FullDefKind::TyAlias` translates visible aliases via `translate_ty` into top-level `TypeDeclKind::Alias` declarations carrying `ItemMeta`, source spans, and translated generics. Checked-in `charon/tests/ui/issue-395-failed-to-normalize.rs` (blob `08ec48928d42366324f2337fdf04aaaf893d951e`) and its `.out` fixture (blob `0fd678541b9c51aa81a123793d951e` / `0fd678541b9c51aa81a123793d56cda629c32665`) confirm that both `Alias<T> = Option<<T as Trait>::AssocType>` and `S2<I, F> = S<I, F>` are serialized as top-level `pub type` declarations in final LLBC.

Before serialization (`charon/src/transform/mod.rs`, blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`), Charon runs two alias-mutating passes:
1. `charon/src/transform/add_missing_info/add_missing_alias_clauses.rs` (blob `ce8ad412edd7a95c612020c97c37bbd2796a8f49`): Because Rust permits free type aliases to mention associated types such as `<T as Trait>::Assoc` without writing `T: Trait` on the alias, this pass visits every `TypeDeclKind::Alias`, extracts trait projections from the right-hand side, adds the missing trait clauses to the alias's generic parameters, and rewrites the references to clause-based proofs.
2. `charon/src/transform/normalize/expand_associated_types.rs` (blob `04c0d0c3ec2d883be87845ae30f198ff0372dd33`): Tracks whether the current item is a type alias (reporting a diagnostic if an unproved bound prevents computing an associated type) and lifts associated types into extra generic parameters on the alias. In `charon/tests/ui/associated_types/lift-assoc-ty-in-alias.rs` (blob `ed86667309d0d01370cb5b284407db1127494d7c`) and its `.out` fixture (blob `37885333c8011fcab23fb647a7b2668ca6740db6`), `type Alias<B> = <B as HasAssoc>::Assoc` is rewritten in LLBC to a top-level alias parameterized by the lifted type parameter and trait clause, with its body reduced to that parameter.

Basis: **source** (`charon/src/ast/types.rs`, `translate_items.rs`, `add_missing_alias_clauses.rs`, `expand_associated_types.rs`, `transform/mod.rs`) + preserved Charon **execution** artifacts (`issue-395-failed-to-normalize.out`, `lift-assoc-ty-in-alias.out`).

#### 2.2 Aeneas Pre-Pass Removal (`PrePasses.filter_type_aliases`) and Downstream Invariants

In `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `src/Main.ml` loads the LLBC crate and invokes `Aeneas.PrePasses.apply_passes` before running concrete interpreter tests, borrow checking, or calling `Aeneas.Translate.translate_crate`. Inside `src/PrePasses.ml` (blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`), `filter_type_aliases`:
1. Filters every `type_decl` whose kind is `Alias` (both non-generic and generic) out of `crate.type_decls`.
2. Removes the corresponding `TypeGroup (NonRecGroup id)` entries from `crate.declarations` (raising an internal error if an alias appears inside a `RecGroup`).

Because `rustc` and Charon have already inlined underlying types at all use sites, `filter_type_aliases` performs no use-site substitution. Downstream stages enforce alias absence as a hard invariant:
- `src/llbc/TypesAnalysis.ml` (blob `4b80030bddd0fc7d044894a85fe332c8d3bdb5d9`) raises `"type aliases should have been removed earlier"` if it encounters `Alias _` on a non-opaque type declaration.
- `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`, and lines 274–284 at `21345f80fa212c596f6437378d7d57984fa2ea77`) raises the same error if pure type-declaration translation receives `Alias _`.

Preserved Aeneas fixtures demonstrate the end-to-end result:
- `tests/src/mini_tree.rs` (blob `fbed6893fb840c0f0bc21bbf3b4e58b69db5ab6c`) declares `type OptNode = Option<Box<Node>>` and uses `OptNode` for `Node.child` and `Tree.root`. The generated `tests/lean/MiniTree.lean` (blob `ae54d4543872edac62862c999a2f91a227489b2f`) has no `OptNode` declaration and types both fields as `Option Node` (combining alias removal with `Box` erasure).
- `tests/src/hashmap.rs` (blob `fc18963eba56b3228132126c8ea985a04b2ea46f`) declares `pub type Key = usize` and `pub type Hash = usize`. The generated `tests/lean/Hashmap/Types.lean` (blob `57fd95233a6b5e6fef75ab00e04e9673ef7a085a`) contains neither `Key` nor `Hash` and types `AList.Cons` and public functions directly with `Std.Usize`.

Consequently, after `filter_type_aliases`, the alias's `TypeDeclId`, name, span, and generic/bound spelling are lost at the Aeneas-to-Lean boundary; any tool requiring source-alias correlation must anchor to `rustc` or Charon metadata before `PrePasses.filter_type_aliases`. Trait associated types do not pass through `TypeDeclKind::Alias` and are unaffected by this filter.

Basis: **source** (`src/PrePasses.ml`, `src/Main.ml`, `src/llbc/TypesAnalysis.ml`, `src/symbolic/SymbolicToPureTypes.ml`) + preserved **execution** artifacts (`tests/lean/MiniTree.lean`, `tests/lean/Hashmap/Types.lean`) + **derived** source-correspondence boundary.

---

### 3. Trait Translation, Operational Dictionaries, and Closure Interfaces

#### 3.1 Trait Declarations as Explicit Lean `structure` Records and Dictionary Passing

Despite `documentation/aeneas-overview.md` (blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`) informally referring to translated traits as Lean "type classes", the pinned implementation in `src/symbolic/SymbolicToPure.ml` (`translate_trait_decl`), `src/pure/Pure.ml` (`trait_decl`), and `src/extract/Extract.ml` (blob `52754e4fdb25b50fce63abe2d2184751d69632e8`) translates each ordinary Rust trait into a Lean `structure` record—not a `class`—and does not use Lean `instance` synthesis.

In `tests/src/traits.rs` (blob `a20f6ee91960cbacf99e8899a32e789f7b855671`) and `tests/lean/Traits.lean` (blob `d234936b72231024fbccf0030a08023836e5eb6e`), the Rust trait and generic caller:

```rust
pub trait BoolTrait {
    fn get_bool(&self) -> bool;
    fn ret_true(&self) -> bool { true }
}

pub fn test_bool_trait<T: BoolTrait>(x: T) -> bool {
    x.get_bool()
}
```

extract to explicit Lean dictionary types and parameters:

```lean
structure BoolTrait (Self : Type) where
  get_bool : Self → Result Bool
  ret_true : Self → Result Bool

def test_bool_trait
  {T : Type} (BoolTraitInst : BoolTrait T) (x : T) : Result Bool := do
  BoolTraitInst.get_bool x
```

Similarly, where-clause shape differences in Charon evidence remain visible in generated Lean signatures: `f<T: ToU64>(x: (T, T))` takes a `ToU64 T` dictionary and constructs the pair dictionary at the call site, whereas `g<T>(x: (T, T)) where (T, T): ToU64` takes a `ToU64 (T × T)` dictionary parameter directly.

Basis: **source** (`src/symbolic/SymbolicToPure.ml`, `src/pure/Pure.ml`, `src/extract/Extract.ml`) + preserved **execution** artifact (`tests/lean/Traits.lean`) compared with upstream **documentation** (`documentation/aeneas-overview.md`).

#### 3.2 Dispatch Taxonomy (`trait_instance_id`), Reducible Implementation Dictionaries, Supertraits, and Method Generics

Aeneas's pure `trait_instance_id` (`src/pure/Pure.ml`, populated by `SymbolicToPureTypes.translate_trait_ref_kind` and printed by `ExtractTypes.extract_trait_instance_id`) distinguishes:
- `TraitImpl`: concrete translated implementation (`h0(u64)` calls `U64.Insts.TraitsToU64.to_u64` directly, while concrete dictionary values are emitted as `@[reducible] def`, e.g., `@[reducible] def U64.Insts.TraitsToU64 : ToU64 Std.U64 := { to_u64 := U64.Insts.TraitsToU64.to_u64 }`, and generic implementations such as `impl<A: ToU64> ToU64 for (A, A)` become `@[reducible] def` functions from prerequisite dictionaries to target dictionaries).
- `Clause`: local generic trait clause parameter (e.g., `BoolTraitInst.get_bool x`).
- `ParentClause`: supertrait evidence stored as an explicit field inside a child trait's dictionary (`trait_decl.parent_clauses` and `trait_impl.parent_trait_refs`; e.g., `pub trait ChildTrait: ParentTrait0 + ParentTrait1 {}` emits a structure with `ParentTrait0Inst` and `ParentTrait1Inst` fields).
- `BuiltinOrAuto`: enumerated builtin/auto trait evidence restricted in `Pure.ml` to `Copy`, `Clone`, `DiscriminantKind`, and `Fn`/`FnMut`/`FnOnce`.
- `Self`: self-reference while translating a trait's own items.
- `UnknownTrait`: unresolved trait evidence from Charon, which `translate_trait_ref_kind` and `ExtractTypes.ml` reject as a translation/extraction error rather than admitting as an unconstrained dictionary.

Trait structure fields also preserve:
- **Method-level generics and bounds**: `Extract.ml` strips the trait-level generic prefix and emits `forall` binders inside the structure field for method-specific generics and dictionary arguments (e.g., `trait OfType { fn of_type<T: ToType<Self>>(x: T) -> Self; }` becomes a polymorphic field accepting `{T : Type}` and a `ToType T Self` dictionary).
- **Default methods**: A provided method such as `BoolTrait::ret_true` emits a standalone default helper (`BoolTrait.ret_true.default`), while concrete implementation dictionaries point to the implementation-specific normalized method reference materialized by Charon.
- **Associated constants**: Emitted as `Result`-typed dictionary fields (`mk_result_ty`, e.g., `LEN1 : Result Std.Usize` and defaulted `LEN2 : Result Std.Usize` on `WithConstTy`), populated from translated global constants or default helpers wrapped in `ok`.

Basis: **source** (`src/pure/Pure.ml`, `src/symbolic/SymbolicToPure.ml`, `src/symbolic/SymbolicToPureTypes.ml`, `src/extract/Extract.ml`, `src/extract/ExtractTypes.ml`) + preserved **execution** artifact (`tests/lean/Traits.lean`).

#### 3.3 Associated-Type Lifting vs. Residual Associated Types, GATs, and Per-Item Omission

Charon's `--remove-associated-types` pass normally lifts associated types into explicit type parameters on the trait declaration before Aeneas translation. In `tests/lean/Traits.lean`, Rust `WithConstTy` (with associated types `V` and `W` and const generic `LEN`) becomes:

```lean
structure WithConstTy (Self : Type) (Self_V : Type) (Self_W : Type)
  (LEN : Std.Usize) where
  ...
```

Similarly, `IntoIterator` receives `Self_Item` and `Self_IntoIter` type parameters plus an `Iterator Self_IntoIter Self_Item` dictionary field, and equality constraints such as `WithConstTy<32, V = u32>` instantiate `Self_V` directly with `Std.U32`. (`Config.parameterize_trait_types` defaults to `false` at `ac9f1bc5262a5e4ff1e24ca78617121382202727`; the parameter-lifted output comes from Charon's preprocessing pass.)

When associated types escape Charon normalization:
- `SymbolicToPure.translate_trait_decl` warns on any non-builtin trait with surviving associated types that generated code will likely be incorrect (noting this arises with mutually recursive traits and GATs) and asserts that any surviving associated type has no binder parameters and no implied trait clauses. The checked-in known-failure fixture `tests/src/mutually-recursive-traits.rs` (blob `074ff639d23a8eca640a8f0ea1b639da269cf894`) and `tests/src/mutually-recursive-traits.lean.out` (blob `d7d6c54d81761d6020aa8627592340ef43cc78f4`) record this exact warning for `Trait1`.
- `SymbolicToPureTypes.translate_trait_ref_kind` rejects retained Charon `ItemClause` evidence with `"Generic Associated Types are not supported yet"`, and rejects Charon `Dyn` trait-proof evidence with `"Dynamic trait types are not supported yet"`.
- In `src/Translate.ml` (`translate_crate_to_pure`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`), Aeneas translates each trait declaration, trait implementation, and function independently, catching translation errors, logging a warning, and returning `None` for the failed item while continuing to extract the rest of the crate. Consequently, a generated `.lean` module is not a completeness certificate for every trait or impl in the input crate.

Basis: **source** (`src/symbolic/SymbolicToPure.ml`, `src/symbolic/SymbolicToPureTypes.ml`, `src/Translate.ml`, `src/Config.ml`) + preserved **execution** artifacts (`tests/lean/Traits.lean`, `tests/src/mutually-recursive-traits.lean.out`).

#### 3.4 Operational Trait Models vs. Mathematical Laws (`Core/Cmp.lean`)

At `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, `backends/lean/Aeneas/Std/Core/Cmp.lean` demonstrates that standard-library trait models are operational function dictionaries rather than mathematical law bundles:
- `PartialEq` is a record containing effectful `eq` and `ne` functions.
- `Eq` contains a `PartialEq` parent dictionary plus `assert_fields_are_eq` (whose default returns `Unit`).
- `PartialOrd` contains its `PartialEq` parent dictionary plus `partial_cmp` and default comparison methods.
- `Ord` contains `Eq` and `PartialOrd` parent dictionaries plus `cmp`, `max`, `min`, and `clamp`.

None of these records carry reflexivity, symmetry, transitivity, antisymmetry, or `cmp`/`partial_cmp` agreement proof fields. Instead, theorems such as `PartialEq.ne.default.spec` (`backends/lean/Aeneas/Std/Core/Cmp.lean`, lines 42–51) require an explicit hypothesis that the supplied `eq` dictionary computes logical equality.

Basis: **source** (`backends/lean/Aeneas/Std/Core/Cmp.lean#L42-L51`).

#### 3.5 Closure Interfaces (`Core/Ops.lean`) and Lifetime Repair Pre-Passes (`PrePasses.ml`)

At `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, `backends/lean/Aeneas/Std/Core/Ops.lean` (lines 67–100) defines the callable trait models and builtin function wrappers:

| Trait / Wrapper Model | Method Signature Shape | Semantic Meaning in Generated Lean |
|---|---|---|
| `FnOnce Self Args Output` | `Self → Args → Result Output` | Consumes the closure state `Self` and arguments `Args` to produce `Result Output`. |
| `FnMut Self Args Output` | `Self → Args → Result (Output × Self)` | Returns both the call output and the updated closure state `Self` (even when `Output` is `Unit`). |
| `Fn Self Args Output` | `Self → Args → Result Output` | Shared callable interface carrying explicit `FnMut` and `FnOnce` parent dictionaries. |
| `BuiltinFn` / `BuiltinFnMut` / `BuiltinFnOnce` | `Inputs → Result Outputs` | Wraps a pure Lean function; `BuiltinFnMut` returns the original function unchanged as the updated callable state after application. |

Closure translation depends on two Charon-workaround pre-passes in `src/PrePasses.ml` (`21345f80fa212c596f6437378d7d57984fa2ea77`, checked-in regression source `tests/src/closures.rs`):
1. `fix_closure_lifetimes` (lines 1954–2014): Repairs missing region relationships between closure inputs and outputs in generated closure methods.
2. `fix_closure_signature_regions` (lines 2016–2080): Repairs erased lifetime arguments of closure types in function signatures, but **only** when the enclosing function binds exactly one region; signatures with multiple candidate regions are left unchanged because the pass cannot determine which region was captured.

Basis: **source** (`backends/lean/Aeneas/Std/Core/Ops.lean#L67-L100`, `src/PrePasses.ml#L1954-L2080`, `tests/src/closures.rs`).

---

### 4. Effect Monad, Scalar Arithmetic Families, Drop/Unwind, and Collection Models

#### 4.1 Interaction-Tree `Result` and `Error` Taxonomy (`Std/Primitives.lean`)

At `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, `backends/lean/Aeneas/Std/Primitives.lean` (lines 41–100) defines `Result α` as an interaction tree `ITree RustEffect α` rather than a three-constructor inductive type:
- `RustEffect` has `fail` inputs indexed by `Error`, with `PEmpty` response type.
- `Result.ok` returns a pure value; `Result.fail` emits an unresumable failure event; `Result.div` denotes divergence; and monadic bind delegates to `ITree.bind`.
- `Error` comprises seven constructors: `assertionFailure`, `integerOverflow`, `divisionByZero`, `arrayOutOfBounds`, `maximumSizeExceeded`, `panic`, and `undef`.
- The auxiliary `MatchResult` inductive type used for pattern-matching/printing views must not be conflated with `Result` itself.

Basis: **source** (`backends/lean/Aeneas/Std/Primitives.lean#L41-L100`).

#### 4.2 Scalar Widths and Arithmetic / Overflow Families (`Std/Scalar/*`)

In `backends/lean/Aeneas/Std/Scalar/Core.lean` (lines 31–80 and 602–616 at `21345f80fa212c596f6437378d7d57984fa2ea77`), signed (`IScalar`) and unsigned (`UScalar`) machine scalars are represented by bitvectors indexed by the scalar kind:
- Fixed integer widths are `8`, `16`, `32`, `64`, and `128` bits.
- `Usize` and `Isize` widths are parameterized by `System.Platform.numBits` (which Lean proves is either `32` or `64`); unsigned bounds are `[0, 2^w - 1]` and signed bounds are `[-2^(w-1), 2^(w-1) - 1]`. Any theorem sensitive to `usize`/`isize` bounds must therefore track the Lean platform width alongside the Rust target triple.
- `Scalar.tryMk` (lines 602–616) checks mathematical range bounds and returns `Result.fail Error.integerOverflow` when out of range.

The modeled arithmetic families in `backends/lean/Aeneas/Std/Scalar/` have distinct failure contracts:

| Operation Family | Pinned Lean Source File (`21345f80fa212c596f6437378d7d57984fa2ea77`) | Definition & Observable Failure / Result Contract |
|---|---|---|
| Ordinary modeled addition (`+`) | `backends/lean/Aeneas/Std/Scalar/Ops/Add.lean` | `UScalar.add` / `IScalar.add` delegates to `tryMk` on the mathematical sum; returns `Result.ok` in range and `Result.fail Error.integerOverflow` on overflow. |
| `checked_add` | `backends/lean/Aeneas/Std/Scalar/CheckedOps/Add.lean` | Defined as `Option.ofResult` of ordinary `add`; returns pure `Some v` or `None` without emitting a `Result.fail` overflow event. |
| `wrapping_add` | `backends/lean/Aeneas/Std/Scalar/WrappingOps/Add.lean` | Performs bitvector addition directly modulo $2^w$; returns a pure wrapped scalar with no overflow failure. |
| `overflowing_add` | `backends/lean/Aeneas/Std/Scalar/OverflowingOps/Add.lean` | Computes the bitvector sum paired with `uaddOverflow` / `saddOverflow`; returns a pure `(wrapped, Bool)` pair. |
| `saturating_add` / `saturating_sub` | `backends/lean/Aeneas/Std/Scalar/SaturatingOps.lean` | Clamps the mathematical sum/difference to the scalar kind's `[min, max]` bounds before constructing the bitvector; pure result with no overflow failure. |
| Unsigned division (`/`) | `backends/lean/Aeneas/Std/Scalar/Ops/Div.lean` | Tests for zero divisor and delegates to bitvector `udiv`; returns `Result.fail Error.divisionByZero` when divisor is `0`. |
| Signed division (`/`) | `backends/lean/Aeneas/Std/Scalar/Ops/Div.lean` | Checks for divisor `0` (`Error.divisionByZero`) and `MIN / -1` (`Error.integerOverflow`) before truncating signed bitvector `sdiv`. |

Basis: **source** (`backends/lean/Aeneas/Std/Scalar/Core.lean#L31-L80`, `Core.lean#L602-L616`, `Ops/Add.lean`, `CheckedOps/Add.lean`, `WrappingOps/Add.lean`, `OverflowingOps/Add.lean`, `SaturatingOps.lean`, `Ops/Div.lean`).

#### 4.3 `Drop`, Panic, and Unwinding Statement Semantics (`Config.ml`, `InterpStatements.ml`, `SymbolicToPure.ml`)

At `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`:
- `src/Config.ml` (lines 625–627) sets `drop_as_no_op = ref true` by default; `src/Main.ml` (lines 255–258) provides the `-eval-drops` CLI flag to set `drop_as_no_op := false`.
- In `src/interp/InterpStatements.ml` (lines 760–781), the LLBC `Drop` statement ignores its extra trait/destructor fields and either returns the unchanged evaluation context (when `drop_as_no_op` is `true`) or invokes `drop_value` (when `-eval-drops` is active). `StorageDead` always invokes `drop_value`, which prepares a write access and writes `Bottom` at the location for loan/borrow bookkeeping rather than invoking a user `Drop::drop` destructor body. (Explicit destructor calls that Charon has already lowered to ordinary function `Call` statements follow the `Call` path separately.)
- `Panic`, `UnwindTerminate`, and `UndefinedBehavior` terminators synthesize a symbolic `Panic` node (or concrete `Panic` result), which `src/symbolic/SymbolicToPure.ml` (`translate_fun_decl_body`, lines 33–48) translates into a `Result` failure rather than modeling stack unwinding or destructor cleanup during unwinding.
- `Assert` evaluates its boolean condition and ignores its unwind target continuation; `UnwindResume` fails immediately with an unwinding-unsupported diagnostic.

Basis: **source** (`src/Config.ml#L625-L627`, `src/Main.ml#L255-L258`, `src/interp/InterpStatements.ml#L760-L781`, `src/symbolic/SymbolicToPure.ml#L33-L48`).

#### 4.4 Collection Models: `Array`, `Slice`, and `Vec` (`Std/Array/Array.lean`, `Std/SliceDef.lean`, `Std/Vec.lean`)

At `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, Aeneas's container models abstract contiguous memory into length-indexed lists without heap capacity or allocator state:
- `backends/lean/Aeneas/Std/Array/Array.lean` (lines 21–45): Represents `Array α n` via a length-indexed `ListN` and proves its underlying list has length `n.val`. `Array.from` and `Array.make` require an explicit length-equality proof argument (with a `simp` tactic default on `Array.make`).
- `backends/lean/Aeneas/Std/SliceDef.lean` (lines 10–35): Represents `Slice α` with an existential `Nat` length, a `ListN` of that length, and a proof that the length is bounded by `Usize.max`.
- `backends/lean/Aeneas/Std/Vec.lean` (lines 25–55): Wraps `Slice α` directly (`ListN` and the wrapper avoid Lean positivity failures when `Array`, `Slice`, or `Vec` appear inside recursive inductive types). Neither capacity nor an allocator parameter is stored.
- **Indexing and mutation**: Checked shared indexing returns `Result.fail Error.arrayOutOfBounds` when out of bounds. Mutable indexing returns a pair `(element, update_fn)`—for `Vec` indexed by `Usize`, `(x, fun x => v.set i x)`—and slice-range specifications express the subslice and reconstruction function under explicit range hypotheses.
- **Growth and insertion boundaries on `Vec`**:
  - `Vec.push` appends the element if the new length is `≤ Usize.max` and otherwise fails with `Error.maximumSizeExceeded`.
  - `Vec.insert` delegates to `insertIdx` and checks capacity, but the inspected implementation at `21345f80fa212c596f6437378d7d57984fa2ea77` requires `i < length` rather than `i ≤ length`, **excluding insertion at the end of a vector (`i == v.len()`)** from its success branch (whereas Rust's `std::vec::Vec::insert` permits `index == len`).
  - `Vec.extend_from_slice` checks the combined length against `Usize.max` and sequences effectful element `clone` calls in `Result`.

Basis: **source** (`backends/lean/Aeneas/Std/Array/Array.lean#L21-L45`, `backends/lean/Aeneas/Std/SliceDef.lean#L10-L35`, `backends/lean/Aeneas/Std/Vec.lean#L25-L55`).

---

### 5. External and Standard-Library Model Registration and Trust Boundaries

#### 5.1 Lean Attribute Registration and `FunInfo` / Type Projection Metadata (`Extract.lean`)

In `backends/lean/Aeneas/Extract/Extract.lean` (blob `377130a8db02017dd17af1096b025c3a17e63088` at `ac9f1bc5262a5e4ff1e24ca78617121382202727`; lines 90–109 and 612–620 at `21345f80fa212c596f6437378d7d57984fa2ea77`), Aeneas defines five scoped Lean environment attributes that bind Lean declarations to Rust name patterns (using the exact pattern syntax Aeneas prints when a definition is missing):
- `rust_type`
- `rust_fun`
- `rust_const`
- `rust_trait`
- `rust_trait_impl`

These attributes control semantic signature projection as well as target naming:
- **`rust_fun` (`FunInfo`)**: Records an optional extracted name, `keepParams` (filtering out Rust type parameters absent from the Lean model, such as `Allocator` parameters), `keepTraitClauses` (filtering trait evidence), `canFail` (default `true`), `lift` (default `true`), and `hasDefault` (for trait-method defaults). When `canFail` is `false` and `lift` is `true`, Aeneas automatically coerces/lifts the pure Lean return value into `Result` so callers participate uniformly in monadic/`step` proofs.
- **`rust_type`**: Can filter type parameters, identify mutable-region positions, rename fields and variants, control variant-name prefixes, or mark the backend type body as `opaque`. When a `rust_type` model is not marked opaque, the Lean-side extractor cross-checks its field and variant metadata against the Lean environment and errors on duplicate or unmatched names.
- **Partial trait models**: `Config.filter_trait_impl_methods` explicitly permits a modeled trait/impl to cover only a subset of the methods present on the upstream Rust trait.

Basis: **source** (`backends/lean/Aeneas/Extract/Extract.lean`, `src/Config.ml`).

#### 5.2 Registry Generation (`make extract-lean-std`), the 357-Entry Fingerprint, and Generic `ExtractBuiltin.ml` Mappings

The `Makefile` target `extract-lean-std` (`Makefile`, blob `b547c69dd21e85de6a5eca44690cca6ba4d949d1`) runs:

```bash
cd backends/lean && lake exe extract
```

and formats the generated OCaml code in `src/extract/ExtractBuiltinLean.ml` (blob `433e0fd178f785ec26a9de9b717600c5d2c7a991`). The Lean generator imports the `Aeneas.Std` environment, collects and sorts all `rust_*` descriptors with their Lean file and line comments, and emits OCaml registration lists (`mk_type`, `mk_fun`, `mk_trait_decl`, `mk_trait_impl`).

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the literal Rust-name pattern registrations in `src/extract/ExtractBuiltinLean.ml` partition as follows:

| Registration Kind | Literal Pattern Count (`ac9f1bc5262a5e4ff1e24ca78617121382202727`) | Breakdown by Crate Prefix |
|---|---:|---|
| Types (`mk_type`) | 35 |Part of 319 `core::`, 37 `alloc::`, 1 `std::` across all 357 entries (covering `alloc::vec::Vec`, `alloc::string::String`, `core::option::Option`, `core::result::Result`, ranges, iterator adapters, formatting types, `Pin`, and selected atomic types). |
| Functions (`mk_fun`) | 212 | Scalar arithmetic/conversions/endianness, array/slice indexing, `Vec` operations, iterators, comparisons, formatting, and trait methods. |
| Trait declarations (`mk_trait_decl`) | 45 | Core operational, conversion, indexing, iterator, and closure traits. |
| Trait implementations (`mk_trait_impl`) | 65 | Standard-library implementations for primitives, tuples, slices, vectors, and options. |
| **Total literal registrations** | **357** | **319 `core::` + 37 `alloc::` + 1 `std::`** |

`src/extract/ExtractBuiltin.ml` (blob `6e28b984b6392fd49601aac6903604248f464955`) combines the Lean-generated lists from `ExtractBuiltinLean.ml` with generic backend mappings and synthesized families (including `core::mem::replace`, `core::mem::take`, `Option::unwrap`, slice indexing, `Vec` helpers, `Box` dereference, and scalar families) indexed by `NameMatcher`. The checked-in fixture `tests/src/builtin.rs` (blob `6190ae93469ba094244298b202855e1ac364ba40`) and its generated `tests/lean/Builtin.lean` (blob `14f1a5446f0fc4445707da2475b8d1f34766`) confirm redirection of `bool::clone` to `CloneBool`, integer `clone`, `Into`/`From` trait dictionaries, and `u32::from_le_bytes` / `to_le_bytes` to `Aeneas.Std` models.

Additional standard-library model boundaries inspected at `21345f80fa212c596f6437378d7d57984fa2ea77`:
- `CoreConvertNum` (lines 582–612) defines `from_le_bytes`/`to_le_bytes`/`from_be_bytes`/`to_be_bytes` using `Array U8` for fixed-width signed and unsigned integers, explicitly excluding `usize` and `isize`.
- `Target.lean` declares `get_target` (with an unconstrained-result specification) and `target_feature_enabled` as Lean `axiom`s.
- `src/llbc/Builtin.ml` (blob `fec847925d30e0236f4bd5a83b18b270577f7918`) defines internal LLBC interpreter/translator builtins, which are distinct from the `ExtractBuiltin*.ml` external-model redirection table.

Basis: **source** (`src/extract/ExtractBuiltinLean.ml`, `src/extract/ExtractBuiltin.ml`, `src/llbc/Builtin.ml`, `Makefile`, `CoreConvertNum`, `Target.lean`) + preserved **execution** fixture (`tests/src/builtin.rs`, `tests/lean/Builtin.lean`).

#### 5.3 Unresolved Opaque Filtering, `-split-files` Templates, and the Model Trust Boundary

In `src/Translate.ml` (blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`), the helper that detects opaque non-builtin declarations takes `filter_builtin`: when `filter_builtin` is `true`, external Rust items matched by the standard-library/builtin registry are excluded from the unresolved-opaque inventory. For unmatched external declarations:
- Without user models, `src/extract/ExtractBase.ml` (blob `4fc8a3f35643ba66555f0889790d50993feef1b9`) tracks whether an opaque definition was emitted and notes that extracting an opaque definition generates an `axiom` (an unverified assumption boundary).
- With `-split-files` (`README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`; `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`), Aeneas emits `TypesExternal_Template.lean` and `FunsExternal_Template.lean` pre-populated with `rust_*` attributes alongside user-maintained `TypesExternal.lean` and `FunsExternal.lean` imported by the generated modules, preventing regeneration from overwriting handwritten models.

Crucially, **model registration is not model validation**: `rust_*` attributes check descriptor syntax and basic field/variant arity, not semantic refinement against `rustc` or standard-library MIR. Any proof of a translated Rust function inherits the soundness assumptions of every `Aeneas.Std` model, `Target.lean` axiom, and user-supplied `TypesExternal.lean` / `FunsExternal.lean` declaration it transitively invokes.

Basis: **source** (`src/Translate.ml`, `src/extract/ExtractBase.ml`) + upstream **documentation** (`README.md`, `documentation/aeneas-overview.md`) + **derived** trust-boundary analysis.

## Boundaries

- **Not examined**:
  - Fresh execution of `charon`, `aeneas`, `lake exe extract`, `lake build`, or `rustc` during these inspections (all execution evidence comes from upstream checked-in `.lean`, `.llbc`, and `.out` fixtures).
  - Semantic verification of each of the 357 literal model registrations in `ExtractBuiltinLean.ml` against upstream Rust `core`/`alloc`/`std` implementations.
  - Exhaustive floating-point IEEE arithmetic models, string UTF-8 invariant proofs, or non-Lean extraction backends (Coq, F*, HOL4).
  - Trait aliases (`trait Foo = Bar;`) and type-alias `impl Trait` (TAIT / opaque types), which follow distinct `rustc` and Charon paths from `TypeDeclKind::Alias`.
- **Unknown**:
  - Whether the coordinating Charon revision `9e95cf318e3a2964fcf5e03104cde5b718f98ea5` forms a tested compatible bundle with `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` (whose checked-in `charon-pin` declares `1aebab5f03a58067e5dc0ede2fec584117f54964`).
  - The full acceptance envelope for recursive trait implementations in Lean and cross-compilation scenarios where the Rust target's `usize`/`isize` width diverges from Lean's `System.Platform.numBits`.
- **Unsupported**:
  - Rust function-pointer types (`TFnPtr`, `"Arrow types are not supported yet"`).
  - Generic associated types (`ItemClause`, `"Generic Associated Types are not supported yet"`) and residual unlifted associated types on mutually recursive traits (`tests/src/mutually-recursive-traits.lean.out`).
  - Dynamic trait evidence in `translate_trait_ref_kind` (`"Dynamic trait types are not supported yet"`) and `dyn Trait` in `translate_sty` / borrow-projection paths.
  - Unresolved Charon `UnknownTrait` evidence.
  - Instantiating generic type parameters with mutable references (including `Self` in trait implementations) and ADTs containing nested mutable borrows.
  - Complex higher-rank/nested region binders requiring de Bruijn shifting in `translate_region_binder`, and closure signature region repair when an enclosing function binds multiple regions (`fix_closure_signature_regions`).
  - Raw-pointer dereference in symbolic execution (`InterpPaths.ml`) and `UnwindResume` stack unwinding (`InterpStatements.ml`).
  - End-of-vector insertion (`i == v.len()`) in `Vec.insert` at `21345f80fa212c596f6437378d7d57984fa2ea77` due to the strict `i < length` guard.
- **Known not to apply**:
  - The presence of `→` in generated Lean does not imply support for Rust `fn(...)` pointers (arrows come from backward functions, closures, or eligible `TFnDef` function items).
  - The presence of `ConstRawPtr T` / `MutRawPtr T` / `RawPtr` in generated Lean does not imply modeled pointer provenance, aliasing, validity, or dereference semantics.
  - Logical `structure`, `inductive`, product (`×`), and `ListN` encodings for structs, enums, tuple structs, `Box<T>`, `[T; N]`, `[T]`, and `Vec<T>` do not preserve Rust memory layout, size, alignment, padding, niche optimization, or heap allocation failure.
  - Inhabiting an operational `PartialEq`, `Eq`, `PartialOrd`, or `Ord` dictionary in Lean does not automatically provide mathematical equivalence or order laws without explicit law hypotheses.
  - Emitting a `Drop` trait dictionary or enabling `-eval-drops` loan bookkeeping does not execute arbitrary `Drop::drop` destructor bodies or unwind cleanup.
  - Historical descriptions of Aeneas `Result` as a three-constructor inductive datatype (`ok`/`fail`/`div`) do not apply to `21345f80fa212c596f6437378d7d57984fa2ea77`, where `Result α` is `ITree RustEffect α`.

## Evidence

### 1. Pinned Aeneas `nightly-2026.06.03` (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, observed 2026-09-25 and 2026-09-26)

- **Model registry & extraction source**:
  - `backends/lean/Aeneas/Extract/Extract.lean`, blob `377130a8db02017dd17af1096b025c3a17e63088`: `rust_type`, `rust_fun`, `rust_const`, `rust_trait`, `rust_trait_impl` attributes, `FunInfo`, descriptor validation, and `lake exe extract` generator.
  - `src/extract/ExtractBuiltinLean.ml`, blob `433e0fd178f785ec26a9de9b717600c5d2c7a991`: checked-in generated Lean registry (357 literal entries: 35 types, 212 functions, 45 trait declarations, 65 trait implementations).
  - `src/extract/ExtractBuiltin.ml`, blob `6e28b984b6392fd49601aac6903604248f464955`: generic builtin families, `NameMatcher` indexing, and composition with `ExtractBuiltinLean.ml`.
  - `src/llbc/Builtin.ml`, blob `fec847925d30e0236f4bd5a83b18b270577f7918`: internal LLBC semantic builtins.
  - `Makefile`, blob `b547c69dd21e85de6a5eca44690cca6ba4d949d1`: `extract-lean-std` target.
- **Type, alias, and trait translation source**:
  - `src/PrePasses.ml`, blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`: `filter_type_aliases` and `apply_passes`.
  - `src/Main.ml`: execution order placing `PrePasses.apply_passes` before interpretation, borrow checking, and `Translate.translate_crate`.
  - `src/llbc/TypesAnalysis.ml`, blob `4b80030bddd0fc7d044894a85fe332c8d3bdb5d9`: downstream invariant error on surviving `Alias _`.
  - `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: `translate_sty`, `translate_generic_params`, `translate_fwd_ty`, `translate_trait_ref_kind`, `translate_trait_clause`, backward-type traversal, and `TFnPtr` / GAT `ItemClause` / `Dyn` / `UnknownTrait` / `Alias` rejections.
  - `src/symbolic/SymbolicToPure.ml`, blob `95ba91f539e48009efa420dfa956c4c55581cb3a`: `translate_trait_decl`, `translate_trait_impl`, and residual associated-type warnings/assertions.
  - `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: `builtin_ty`, `ty`, `trait_instance_id`, `trait_decl`, `trait_impl`, and `builtin_impl_data`.
  - `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: Lean `structure` trait extraction, `@[reducible] def` impl dictionaries, parent/constant/type/method fields, and `.default` helpers.
  - `src/extract/ExtractTypes.ml`, blob `371717638f4298cc9c488b31a597608f9bf5089c`: `extract_literal_type`, `extract_ty`, `extract_trait_instance_id`, and ADT/trait printing.
  - `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: Lean builtin type names (`Array`, `Slice`, `Str`, `MutRawPtr`, `ConstRawPtr`) and opaque-extraction axiom tracking.
  - `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: `filter_builtin` exclusion of registered models from unresolved opaque declarations and independent per-item catch-and-omit in `translate_crate_to_pure`.
  - `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: `use_tuple_structs = true` and `parameterize_trait_types = false`.
  - `src/interp/InterpPaths.ml`, blob `ec23375a5ca0680500daea0248d2372c9901156e`: raw-pointer dereference rejection.
  - `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`, and `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`.
- **Preserved upstream Rust/Lean fixtures (`ac9f1bc5262a5e4ff1e24ca78617121382202727`)**:
  - `tests/src/builtin.rs` (blob `6190ae93469ba094244298b202855e1ac364ba40`) and `tests/lean/Builtin.lean` (blob `14f1a5446f0fc4445707da2475b8d1f34766`).
  - `tests/src/arrays.rs` (blob `478af7171452826436f56f12c88493debac8e0d0`) and `tests/lean/Arrays.lean` (blob `00b7716b63b41c4747889b42f2dee3796d3ab12d`).
  - `tests/src/slices.rs` (blob `13bfe864372318725d41e33a4179a74fcfdf1feb`) and `tests/lean/Slices.lean` (blob `f294e70359a20cf3db5022529204fc1102e7aa51`).
  - `tests/src/adt.rs` (blob `cc31a7085737e5efd8910316d99adbd74d9df32c`) and `tests/lean/Adt.lean` (blob `f99cbd9c162d060dc55ea2614d7d0b8bfa32ca9e`).
  - `tests/src/traits.rs` (blob `a20f6ee91960cbacf99e8899a32e789f7b855671`) and `tests/lean/Traits.lean` (blob `d234936b72231024fbccf0030a08023836e5eb6e`).
  - `tests/src/dyn.rs` (blob `fa2b29298fcc157e4b05a61098553525fe867f5d`) and `tests/lean/Dyn.lean` (blob `1ca9dd626eea93ec47dee2094febb8541d41c2c3`).
  - `tests/src/raw_pointers.rs` (blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`) and `tests/src/raw_pointers.lean.out` (blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`).
  - `tests/src/mutually-recursive-traits.rs` (blob `074ff639d23a8eca640a8f0ea1b639da269cf894`) and `tests/src/mutually-recursive-traits.lean.out` (blob `d7d6c54d81761d6020aa8627592340ef43cc78f4`).
  - `tests/src/mini_tree.rs` (blob `fbed6893fb840c0f0bc21bbf3b4e58b69db5ab6c`) and `tests/lean/MiniTree.lean` (blob `ae54d4543872edac62862c999a2f91a227489b2f`).
  - `tests/src/hashmap.rs` (blob `fc18963eba56b3228132126c8ea985a04b2ea46f`) and `tests/lean/Hashmap/Types.lean` (blob `57fd95233a6b5e6fef75ab00e04e9673ef7a085a`).

### 2. Paired Charon `0.1.210` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, observed 2026-09-26)

- `charon/src/ast/types.rs` (blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`), `charon/src/bin/charon-driver/translate/translate_items.rs` (blob `7964644be017856c6d165545a67bd6ef06e0c85c`), `charon/src/transform/add_missing_info/add_missing_alias_clauses.rs` (blob `ce8ad412edd7a95c612020c97c37bbd2796a8f49`), `charon/src/transform/normalize/expand_associated_types.rs` (blob `04c0d0c3ec2d883be87845ae30f198ff0372dd33`), and `charon/src/transform/mod.rs` (blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`).
- Preserved UI fixtures: `charon/tests/ui/issue-395-failed-to-normalize.rs` (blob `08ec48928d42366324f2337fdf04aaaf893d951e`) with `.out` (blob `0fd678541b9c51aa81a123793d56cda629c32665`), and `charon/tests/ui/associated_types/lift-assoc-ty-in-alias.rs` (blob `ed86667309d0d01370cb5b284407db1127494d7c`) with `.out` (blob `37885333c8011fcab23fb647a7b2668ca6740db6`).

### 3. Newer Upstream Aeneas Interfaces (`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, observed 2026-10-15)

- Preserved package index: [`support/aeneas-types-traits-primitives-and-models/source-index.json`](support/aeneas-types-traits-primitives-and-models/source-index.json) records exact symbol/line excerpts, git blob IDs, and negative fetch probes at `21345f80fa212c596f6437378d7d57984fa2ea77`.
- Key inspected source ranges at `21345f80fa212c596f6437378d7d57984fa2ea77`:
  - `src/symbolic/SymbolicToPureTypes.ml` (lines 11–198, 274–284, 397–428): `translate_region_binder`, `translate_generic_args`, `translate_sty`, `translate_fwd_ty`, and union/opaque/alias handling.
  - `src/extract/ExtractBase.ml` (lines 1460–1477) and `src/extract/ExtractTypes.ml` (lines 1330–1382): `type_keyword` (`Type _` vs. `Type`).
  - `src/PrePasses.ml` (lines 1954–2080): `fix_closure_lifetimes` and `fix_closure_signature_regions`.
  - `src/Config.ml` (lines 625–627), `src/Main.ml` (lines 255–258), `src/interp/InterpStatements.ml` (lines 760–781), and `src/symbolic/SymbolicToPure.ml` (lines 33–48): `drop_as_no_op`, `-eval-drops`, `Drop`/`StorageDead`/`Panic`/`UnwindResume` handling.
  - `backends/lean/Aeneas/Std/Primitives.lean` (lines 41–100): `ITree RustEffect α` `Result` and `Error` constructors.
  - `backends/lean/Aeneas/Std/Scalar/Core.lean` (lines 31–80, 602–616) and `Ops/Add.lean`, `CheckedOps/Add.lean`, `WrappingOps/Add.lean`, `OverflowingOps/Add.lean`, `SaturatingOps.lean`, `Ops/Div.lean`.
  - `backends/lean/Aeneas/Std/Core/Cmp.lean` (lines 42–51) and `backends/lean/Aeneas/Std/Core/Ops.lean` (lines 67–100).
  - `backends/lean/Aeneas/Std/Array/Array.lean` (lines 21–45), `backends/lean/Aeneas/Std/SliceDef.lean` (lines 10–35), and `backends/lean/Aeneas/Std/Vec.lean` (lines 25–55).
  - `backends/lean/Aeneas/Extract/Extract.lean` (lines 90–109, 612–620), `CoreConvertNum` (lines 582–612), and `Target.lean`.

## Revalidation

To revalidate this report against a newer Aeneas or Charon revision:

1. **Diff narrow compiler and extractor entry points**:
   - In `AeneasVerif/aeneas`, diff `src/symbolic/SymbolicToPureTypes.ml` (`translate_region_binder`, `translate_generic_params`, `translate_sty`, `translate_fwd_ty`, `translate_trait_ref_kind`), `src/symbolic/SymbolicToPure.ml` (`translate_trait_decl`, `translate_trait_impl`, `translate_fun_decl_body`), `src/PrePasses.ml` (`filter_type_aliases`, `fix_closure_lifetimes`, `fix_closure_signature_regions`), `src/extract/Extract.ml`, `src/extract/ExtractTypes.ml` (`type_keyword`, `extract_ty`), `src/extract/ExtractBase.ml`, `src/Config.ml`, and `src/interp/InterpStatements.ml` (`Drop`, `StorageDead`, `UnwindResume`).
   - In `AeneasVerif/charon`, diff `charon/src/ast/types.rs` (`TypeDeclKind::Alias`), `charon/src/transform/add_missing_info/add_missing_alias_clauses.rs`, and `charon/src/transform/normalize/expand_associated_types.rs`.
2. **Diff and regenerate the Lean standard-library registry and primitive models**:
   - Diff `backends/lean/Aeneas/Extract/Extract.lean`, `backends/lean/Aeneas/Std/Primitives.lean`, `Scalar/Core.lean`, `Core/Cmp.lean`, `Core/Ops.lean`, `Array/Array.lean`, `SliceDef.lean`, and `Vec.lean` (specifically checking whether `Vec.insert` still enforces `i < length` or allows `i ≤ length`).
   - Run `make extract-lean-std` (`cd backends/lean && lake exe extract`), verify byte-for-byte reproducibility of `src/extract/ExtractBuiltinLean.ml`, and recount literal `mk_type`, `mk_fun`, `mk_trait_decl`, and `mk_trait_impl` entries by crate prefix (`core::`, `alloc::`, `std::`).
3. **Run minimal positive and negative fixture probes**:
   - Translate a compact multi-concern Rust crate exercising: all scalar widths, `()`, `!`, 0/1/multi-element tuples, record and tuple structs, enums, `[T; N]`, `[T]`, `Box<T>`, `&T`, `&mut T`, free and generic type aliases (`type A = u32`, `type Pair<T> = (T, T)`), required and default trait methods, supertraits, associated constants, lifted associated types, `FnOnce`/`FnMut`/`Fn` closures, and three external calls (one `Aeneas.Std` builtin, one user `rust_fun` model with varied `canFail`/`lift` flags under `-split-files`, and one unmodeled opaque declaration).
   - Run negative boundary probes for `fn(...)` pointers (`TFnPtr`), GAT `ItemClause`s, mutually recursive traits with unlifted associated types, `dyn Trait` dispatch, raw-pointer dereference, generic `&mut T` instantiation, and `UnwindResume` to verify which rejections remain fail-closed.
