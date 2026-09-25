# Aeneas Rust-to-Lean value, function, and borrow translation at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the release selected by current Anneal, ordinary Rust references do not survive as Lean reference or heap objects. Aeneas functionalizes them. `&T` and `&mut T` both become the translated value for `T` in the forward value type; mutable-borrow effects are reconstructed with generated backward functions whose inputs and outputs are derived from region groups. A Rust function that returns a mutable borrow can therefore become a Lean function returning both a value and a function that later propagates the final borrowed value back to its original owners.

The pinned checked-in `choose` fixture is a compact witness. Rust `fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T` is preserved as generated Lean with shape `Bool → T → T → Result (T × (T → (T × T)))`. The forward component chooses a `T`; the backward component maps the eventual returned value to updated `x` and `y`. Checked-in nested-borrow fixtures show multiple backward functions and multiple abstraction levels, while the source still rejects ADTs containing nested mutable borrows. Support is therefore structured, not all-or-nothing.

Type translation is similarly logical rather than layout-preserving. `Box<T>` is eliminated, tuples become products, structs/enums become logical target ADTs, Rust scalar primitives become Aeneas bounded scalar types such as Lean `Std.U32`, and ordinary references lose their reference constructor. Raw-pointer types are retained as a distinct pure builtin, but the pinned interpreter still rejects raw-pointer dereference, as recorded by a checked-in known-failure artifact.

Function translation proceeds through LLBC symbolic execution, then a pure Aeneas AST, then Lean extraction. Failure is part of the pure signature only when Aeneas effect analysis classifies the function as fallible; the complete output type can combine a forward value, backward functions, and a `Result` wrapper. Traits in the checked-in Lean output are explicit dictionary structures and parameters, not ordinary implicit Lean typeclasses.

No fresh Charon, Aeneas, Lean, or rustc execution was performed. The report uses exact pinned source, documentation, and checked-in generated Lean artifacts. Those artifacts are preserved upstream historical execution evidence, not execution performed on this surface.

## Applicability

- Aeneas: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`.
- Paired Charon: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`.
- Anneal context: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`; `anneal/flake.nix` selects this Aeneas release.
- Current Anneal design deliberately does not freeze the Rust/Charon/Aeneas/Lean boundary. This report records the selected upstream behavior rather than choosing that boundary.

The term **forward type** follows Aeneas `translate_fwd_ty`: the value-level inputs and Rust return value before backward functions and failure effects are combined. A **backward function** is generated from borrow abstractions to propagate values when mutable borrows end; it is not a Rust closure present in source.

## Findings

### The implemented path is LLBC symbolic execution, then a pure AST, then Lean extraction

`src/Translate.ml` runs `evaluate_function_symbolic` for a structured LLBC body, computes a decomposed signature with `SymbolicToPureTypes.translate_fun_sig_from_decl_to_decomposed`, and then passes the symbolic AST through `SymbolicToPure.translate_fun_decl`. The Lean backend therefore prints an already-functionalized pure program rather than directly printing LLBC.

For source correspondence, three boundaries must be tracked separately: Charon LLBC, Aeneas symbolic/pure semantics, and Lean target syntax. Generated helpers such as backward functions have no direct Rust source item.

Basis: **source** plus upstream **documentation**.

### Forward type translation erases ordinary references and boxes

In `src/symbolic/SymbolicToPureTypes.ml`, `translate_fwd_ty` maps `Box<T>` to the translated `T` and maps `TRef` recursively to its referent type. The pure type therefore does not retain an ordinary reference constructor or its mutability. Arrays retain element type and length; slices retain element type; literal primitives remain bounded pure scalar types.

Raw pointers differ: they become the pure raw-pointer builtin carrying const/mut information and the translated pointee. `src/pure/Pure.ml` confirms the target AST has no ordinary reference constructor and documents Box removal as an identity simplification.

This is a semantic abstraction, not ABI/layout equivalence. Rust aliasing and mutation claims must come from the borrow semantics, not from target type shape alone.

Basis: **source**.

### Lean syntax is a second mapping after Aeneas pure types

`src/extract/ExtractTypes.ml` prints bounded scalar types with Lean names such as `Std.U32`, tuples as products, arrows as `→`, and target ADTs as Lean structures or inductives. The checked-in `tests/lean/NoNestedBorrows.lean` confirms representative output: Rust integer parameters become `Std.*` scalars, products become Lean products, and the Rust `Box<List<T>>` link in a recursive list becomes a direct `List T` link because Box was removed earlier.

Basis: **source** + preserved generated artifact.

### Rust structs and enums become logical Lean data declarations

`translate_type_decl_kind` maps supported LLBC structs and enums to pure structure/enum declarations. The generated `NoNestedBorrows.lean` shows a Rust `Pair<T1,T2>` as a Lean `structure`, a recursive Rust `List<T>` as a Lean `inductive`, and an empty struct simplified to `Unit`.

These are logical representations. They do not encode Rust padding, discriminant layout, pointer identity, allocation, or drop behavior.

Basis: **source** + preserved generated artifact.

### Shared references become values and freeze update paths beneath them

The forward translation maps `&T` to `T`. The backward-type traversal supplies the semantic counterpart: when it encounters a shared reference, it stops traversal rather than producing mutable update paths beneath it, with source commentary that the shared borrow freezes everything below it.

The generated `is_cons(&List<T>)` takes a `List T` in Lean, not a reference. The lack of a Lean reference token is therefore the result of earlier symbolic borrow reasoning, not permission to treat Rust shared references as unrestricted copies.

Basis: **source** + preserved generated artifact.

### Mutable references become forward values plus backward value flow

For `&mut T`, the forward input also becomes `T`, but Aeneas computes backward signatures from region structure. Mutable borrows in forward input types can add values that a backward function returns to original owners; mutable borrows in the Rust output type can add inputs that the caller later supplies to the backward function.

`compute_output_ty_from_decomposed` combines the forward value with non-filtered backward functions before applying failure effects. Mutation is therefore represented as value flow rather than target-language heap mutation.

Basis: **source**.

### `choose` is a preserved witness of the forward/backward contract

The Rust fixture `choose<'a,T>(bool,&'a mut T,&'a mut T)->&'a mut T` is preserved in generated Lean as `def choose {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T)))`.

The true branch returns `x` with a backward function that replaces `x` and preserves `y`; the false branch symmetrically updates `y`. Its generated caller receives the pair, changes the returned value, invokes the backward function, and then checks the reconstructed owners. This artifact simultaneously witnesses reference erasure, a returned mutable borrow, and backward reconstruction.

Basis: preserved upstream **execution** artifact paired with its Rust source; no fresh execution.

### Backward functions are organized by region groups, not one per syntax node

The decomposed signature carries `back_sg`, a map keyed by region-group IDs. Each entry contains level-indexed backward inputs and outputs. Consequently the number and type of generated backward functions are determined by region relationships across the function signature, not mechanically by counting `&mut` tokens. Empty backward functions can be filtered, and merged forward/backward outputs can be simplified.

Basis: **source**.

### Nested mutable-borrow signatures have explicit multi-level machinery, with an ADT boundary

`compute_back_ty_num_levels` and `translate_back_ty_aux` count and traverse abstraction levels. The checked-in `NestedBorrows.lean` contains examples such as `inner_mut` with multiple backward functions and `IterMut.next` with a backward function consuming both an updated iterator and optional returned value.

The source nevertheless asserts that ADTs containing nested mutable borrows are not supported in the relevant type analysis. Shared references also stop deeper mutable traversal. Thus nested-borrow support exists for signature-level patterns but is not arbitrary.

Basis: **source** + preserved generated artifact.

### Failure effects are conditional, and can wrap backward functions

`Pure.fun_effect_info.can_fail` controls whether the generated result is wrapped in the pure `Result` type. `fun_sig.output` is documented as containing effects rather than merely the purified Rust return type. The forward value and backward function types are grouped first; failure effects are then applied.

A fallible function returning a mutable borrow can therefore have a successful `Result` payload that itself contains backward functions. Generated tests show assertions, panic paths, and checked operations using the result/error machinery. This does not imply preservation of every Rust unwind distinction; Charon preprocessing can already lose unwinding information.

Basis: **source** + preserved generated artifacts.

### Per-function Aeneas translation can fail instead of producing a pure declaration

`translate_function_to_pure` catches `CFailure`, records a warning identifying the function, and returns `None`. This is a separate completeness boundary from Charon extraction.

A pipeline that wants to claim coverage of all relevant Rust behavior must account for which LLBC declarations successfully produced Aeneas pure/Lean declarations; the presence of a crate-level Lean output is not itself a proof that every function translated.

Basis: **source**.

### Trait obligations are explicit dictionaries in the generated Lean artifacts

The checked-in `Traits.lean` maps Rust trait declarations to Lean structures with method fields. Generic callers receive explicit arguments such as `BoolTraitInst : BoolTrait T`; trait implementations are reducible values of the corresponding structure. Associated types can be represented by extra type parameters or fields, depending on Charon preprocessing.

Describing this exact pin as simply using Lean typeclasses would therefore obscure proof-facing declaration shape.

Basis: **source** + preserved generated artifact.

### Representable raw-pointer types do not imply supported raw-pointer semantics

Pure type translation retains raw-pointer type information, but `tests/src/raw_pointers.lean.out` is a checked-in known-failure artifact saying that Aeneas does not yet support dereferencing raw pointers, with the failure attributed to `interp/InterpPaths.ml`. The root documentation likewise frames the current functional translation around a safe-Rust subset, with unsafe/concurrent support requiring different machinery.

A consumer must distinguish type representability from operational support.

Basis: **source** + preserved known-failure artifact + **documentation**.

### Documentation is conceptual guidance, not an exact support manifest

The root README and `documentation/aeneas-overview.md` are useful for the intended value/backward-continuation model, but exact support should be recovered from pinned source and checked-in tests. In particular, nested borrows are neither uniformly supported nor unsupported; trait dictionaries are explicit in generated Lean; and raw-pointer types are printable even while dereference fails.

Basis: **derived** from **documentation**, **source**, and preserved artifacts.

## Boundaries

- No fresh Charon, Aeneas, Lean, Lake, or rustc execution was performed.
- Checked-in `.lean` and `.lean.out` files are preserved upstream artifacts, not fresh execution by this report.
- The report establishes translation shape for the exact pin; it does not prove semantic soundness of the functionalization for all supported Rust.
- Published Aeneas formal results are not treated as a blanket proof of this exact 2026 implementation without a separate theorem-to-code applicability analysis.
- End-to-end completeness is not established. Charon partial output and Aeneas per-function failure require separate accounting.
- ABI/layout preservation is not claimed; Box/reference removal is an intentional logical abstraction.
- Raw-pointer dereference remains explicitly unsupported in the preserved fixture.
- Multi-level nested borrow machinery does not imply support for ADTs containing nested mutable borrows.
- This report does not inventory every closure/function-pointer, loop/recursion, global/static, trait, or external-model case.
- It does not choose Anneal architecture. Current Anneal design leaves the exact Rust/Charon/Aeneas/Lean proof boundary open.

## Evidence

**Source — primary Aeneas revision.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: `translate_function_to_symbolics`, `translate_function_to_pure_aux`, `translate_function_to_pure`, crate translation staging.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: `translate_fwd_ty`, nested-backward-level analysis, decomposed signatures, backward input/output computation, output composition.
- `src/symbolic/SymbolicToPureExpressions.ml`, blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`: backward-function values and call translation.
- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: pure `ty`, `fun_effect_info`, `back_sg_info`, `decomposed_fun_type`, and `fun_sig`.
- `src/extract/ExtractTypes.ml`, blob `371717638f4298cc9c488b31a597608f9bf5089c`: Lean scalar/product/arrow/type-declaration printing.

**Documentation — same revision.** `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`; `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`.

**Preserved generated artifacts.**

- `tests/src/no_nested_borrows.rs`, blob `707f7d6e1201d1220380dd565a4178806cf3a9ec`, with `tests/lean/NoNestedBorrows.lean`, blob `e2a706b744e2e9a105e305cf8a2b353354209dae`.
- `tests/src/nested-borrows.rs`, blob `61d62cf0e0723a4019e024882e35fb8b212a67eb`, with `tests/lean/NestedBorrows.lean`, blob `61b3b2b31e50555182867a5b73fa510d05106e22`.
- `tests/src/traits.rs`, blob `a20f6ee91960cbacf99e8899a32e789f7b855671`, with `tests/lean/Traits.lean`, blob `d234936b72231024fbccf0030a08023836e5eb6e`.
- `tests/src/raw_pointers.rs`, blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`, with known-failure output `tests/src/raw_pointers.lean.out`, blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`.

No evidence gathered by this report is fresh **execution**. Generated and failure artifacts above pre-existed at the pinned commit.

## Revalidation

For a future pin, first resolve exact Aeneas and paired Charon commits. Diff `SymbolicToPureTypes.ml` around forward-type erasure and backward-level computation, `Pure.ml` around pure types/effects, `Translate.ml` around staging and per-function failure, and `ExtractTypes.ml` around Lean output. Then compare the checked-in `NoNestedBorrows.lean`, `NestedBorrows.lean`, and `Traits.lean` goldens with their Rust fixtures and recheck the raw-pointer known-failure.

On a capable execution surface, regenerate four minimal witnesses at exact revisions: (1) `choose`, one shared-borrow reader, one simple `&mut` updater, and a nested `&mut &mut` signature; (2) an ADT containing a nested mutable borrow plus a single-level control; (3) a raw pointer that is only passed plus one that is dereferenced; and (4) a generic trait with an associated type and method. Preserve LLBC, generated Lean, stdout/stderr, commands, revisions, and hashes. Run the generated Lean through the exact selected `lean-toolchain`. These experiments establish current generated shape and acceptance boundaries; they do not by themselves prove the Rust-to-Lean semantic theorem.
