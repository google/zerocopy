# rustc Const Generics: ValTree Canonicalization, generic_const_exprs Syntactic Equality, and ConstParamTy / StructuralPartialEq Soundness

## Summary

This report establishes primary-source, empirical, and kernel-checked `Lean 4` ground truth for how `rustc` represents, canonicalizes, unifies, mangles, and gates type-system constants across three tightly coupled subsystems:

1. **Type-level `ValTree` canonicalization, `TypeId` equality, and `v0` symbol deduplication (`ConstKind::Value`):** In `rustc`'s type IR (`compiler/rustc_type_ir/src/const_kind.rs:21-252`, `compiler/rustc_middle/src/ty/consts/valtree.rs:18-227`) and const-evaluation lowering (`compiler/rustc_const_eval/src/const_eval/valtrees.rs:21-487`), compile-time interpreter places (`MPlaceTy`) carrying allocation IDs (`AllocId`) and arbitrary struct/enum padding bytes are canonicalized by `const_to_valtree_inner` into hash-consed `ValTreeKind::{Leaf, Branch}` trees. Shared references (`&T`, including `&str`, `&[u8]`, and `&ADT`) dereference through `ecx.deref_pointer(place)`, erasing `AllocId` identity (`valtrees.rs:155-158`). Structs, tuples, and enums project fields structurally via `branches`, erasing all padding bytes (`valtrees.rs:21-60`), with enums prepending `VariantIdx` as a leading `u32` `ScalarInt` leaf (`valtrees.rs:40-46`). Unions (`def.is_union()`), function pointers (`ty::FnPtr`), trait objects, closures, and raw provenance pointers (`scalar.try_to_scalar_int()` error) are rejected via `ValTreeCreationError::NonSupportedType` (`valtrees.rs:130-210`). Downstream, `rustc_symbol_mangling::v0` (`compiler/rustc_symbol_mangling/src/v0.rs:771-947`) serializes canonical `(ct_ty, valtree)` pairs directly (for example `Kj4_`, `KVNtB2_3TagS1ah5_1bb1_EE`, `KVNtNtB2_4Mode7CheckedTh7_EE`, `KRe616e6e65616c_`, `KRAh1_h2_h3_E`), guaranteeing that distinct syntactic constant expressions evaluating to equal `ValTree`s share identical `TypeId`s and compile to a single deduplicated monomorphization in MIR and LLVM IR (`-O0` and `-O2`, natives and Miri under both Stacked Borrows and Tree Borrows). *(Basis: source + execution)*

2. **`min_const_generics` vs. `generic_const_exprs` syntactic unification and trait-solver interaction (`AnonConstKind`, `ConstEvaluatable`, `ConstKind::Expr`):** `rustc_hir_analysis::collect::anon_const_kind` (`compiler/rustc_hir_analysis/src/collect.rs:1813-1841`) classifies anonymous constants into `AnonConstKind::{GCE, MCG, RepeatExprCount, NonTypeSystemInline, NonTypeSystemAnon}`. Stable `min_const_generics` allows generic const parameters only as standalone path/block arguments (`N` or `{ N }`) inside types and array repeat counts, rejecting `[u8; N + 1]` and `[0u8; N + 1]` at collection time, while legacy trait-associated constants in repeat counts (`[0u8; H::<T>::LEN]`) still trigger the `#76200` `const_evaluatable_unchecked` future-incompat warning rather than the generic-param syntax error (`[0u8; { let _: Option<T> = None; 4 }]` errors with `E0308` plus `constant expression depends on a generic parameter`). Under `#![feature(generic_const_exprs)]`, `const_evaluatable_clauses_of` (`compiler/rustc_hir_analysis/src/collect/clauses_of.rs:401-484`) automatically injects `ClauseKind::ConstEvaluatable(c)` bounds for anonymous constants in function signatures and `impl` headers, so `fn sig_auto<const N: usize>(arr: [u8; N + 1])` compiles without an explicit `where` clause whereas body-only or callee-required expressions (`[0u8; N + 1]`) fail as `"unconstrained generic constant"` without `where [(); N + 1]:`. During bound satisfaction, `satisfied_from_param_env` (`compiler/rustc_trait_selection/src/traits/const_evaluatable.rs:159-229`) expands `thir_abstract_const` (`abstract_const.rs:37-79`) and walks `ConstEvaluatable` AST subtrees via syntactic `ocx.eq` (so `where [(); (N + 1) * 2]:` satisfies `[u8; N + 1]` when uniquely matched). Because `ocx.eq` is purely syntactic over `ConstKind::Expr`, commutative rewritings such as `[u8; N + 1]` vs. `[u8; 1 + N]` are rejected with `error[E0308]`, preserving soundness (syntactic identity implies semantic equivalence under every valuation) at the cost of algebraic incompleteness. Across compiler versions, `generic_const_exprs` is incompatible with `-Znext-solver=globally`: passing `-Znext-solver=globally` explicitly with `generic_const_exprs` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` hard-errors (`-Znext-solver=globally and generic_const_exprs are incompatible` + `E0275`), whereas on newer nightlies where `-Znext-solver=globally` is enabled by default for testing (`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` and HEAD `0259d5e9`), `warn_next_solver_and_gce` (`compiler/rustc_ast_passes/src/feature_gate.rs:735-751`) warns and downgrades the crate to `-Znext-solver=coherence` (still mutating incompatibility against `#![feature(gca_const_items)]`, which mandates `-Znext-solver=globally` at `feature_gate.rs:763-783`). *(Basis: source + execution + normative)*

3. **`ConstParamTy` and `StructuralPartialEq` admission rules and type-identity soundness (`coherence/builtin.rs`):** Every type parameterizable in a `const` generic must satisfy `ConstParamTy_: StructuralPartialEq + Eq` (`library/core/src/marker.rs:258, 1112`). `visit_implementation_of_const_param_ty` (`compiler/rustc_hir_analysis/src/coherence/builtin.rs:170-245`) and `type_allowed_to_implement_const_param_ty` (`compiler/rustc_trait_selection/src/traits/misc.rs:92-201`) enforce a closed inductive admissibility discipline: primitive scalars (`u*`, `i*`, `bool`, `char`, `()`) and homogeneous arrays `[T; N]` are admitted unconditionally; `&T`, `[T]`, and `str` additionally require `#![feature(unsized_const_params)]`; ADTs require `#![feature(min_adt_const_params)]` or `#![feature(adt_const_params)]`, with `min_adt_const_params` rejecting structs whose fields are less visible than the struct (`ConstParamTyFieldVisMismatch`) and `#[non_exhaustive]` variants (`NonExhaustive`), whereas full `adt_const_params` admits both while still gating all fields through `ConstParamTy`; and floats (`f32`/`f64`), mutable references (`&'static mut u8`), function pointers, unions, and manual `impl PartialEq` without `#[derive(PartialEq)]` (`E0277` on `StructuralPartialEq`) are rejected. Empirically, bypassing `#[derive(PartialEq)]` under unstable `#![feature(adt_const_params, structural_match)]` by writing a manual constant-true `PartialEq` paired with `unsafe`-free `impl StructuralPartialEq for Weird {}` yields `RUNTIME_EQ=true` alongside `TYPEID_EQ=false` for `Wrap<{ Weird(1) }>` vs. `Wrap<{ Weird(2) }>` natively and under Miri SB/TB, directly proving that `StructuralPartialEq` integrity (structurally derived componentwise equality, excluding IEEE-754 float `-0.0 == +0.0` / `NaN != NaN` and arbitrary user `PartialEq`) is necessary and sufficient for `PartialEq` vs. `ValTree`/`TypeId` equivalence. *(Basis: source + execution + derived)*

4. **Lean `4.34.1` kernel-checked mechanization (`ConstGenericsValTreeCanonicalizationAndStructuralEqSoundness.lean`):** A standalone, zero-`sorry` `2,665`-line (`127,242`-byte) formalization built strictly on `prelude` + `Init.*` (`1,046` local kernel constants, `294` kernel `thmInfo` declarations / `78` top-level `theorem` declarations [`89` total `theorem` declarations], `0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `._unsafe_rec`, `0` `unsafe`/`partial`/`opaque`, only `propext` beyond empty axiom cones) mechanizes:
   - `const_to_valtree` / `valtree_to_const_value` erasure (`ctfe_alloc_id_erasure`, `struct_padding_erasure`, `enum_padding_erasure`), round-trip soundness (`valTree_roundtrip`), and `TypeId`/`v0` deduplication (`eval_eq_guarantees_typeid_and_v0_dedup`, plus 6 concrete probes matching live compiler symbols);
   - `min_const_generics` environment independence (`mcg_closed_const_env_independent`), `generic_const_exprs` syntactic soundness (`synEq_implies_semEq`), algebraic incompleteness witnesses (`gce_syntactic_incompleteness_n_plus_1`, `gce_syntactic_incompleteness_assoc_fold`, `gce_subtree_satisfaction_witness`), and next-solver matrix (`gce_solver_compatibility_theorems`);
   - The inductive `ConstParamTy`/`StructuralPartialEq` <-> `ValTree` bisimulation (`structuralEq_iff_valTree_eq`, `admitted_valtree_typeid_bisimulation`) alongside formalized counterexamples for IEEE-754 `f32` (`-0.0 == +0.0`, `NaN != NaN`), manual `StructuralPartialEq` bypass (`weird_manual_structural_peq_unsoundness_witness`), and `min_adt_const_params` vs. `adt_const_params` / `unsized_const_params` feature gating (`feature_gate_adt_and_unsized_precision`). *(Basis: derived)*

## Applicability

These findings govern:

- **Rust frontend verification & `rustc`-to-Lean type/const lowering (`anneal`, verified `rustc` frontends):** Determining exact canonical equality keys (`(ty, ValTree)`) when modeling monomorphized item identities, `TypeId` comparisons, trait resolution for const-generic bounds, and const-argument well-formedness across MIR lowering and symbol mangling. *(Basis: source + derived)*
- **`min_const_generics` vs. unstable const-generic extensions (`zerocopy` & unsafe Rust consumers):** Selecting safe vs. gated const-generic idioms, understanding why array type lengths (`[u8; N + 1]`) remain unaccepted on stable Rust and why `#![feature(generic_const_exprs)]` still fails `N + 1` vs. `1 + N` unifications without algebraic equivalence classes, and predicting crate-level interactions with `-Znext-solver=globally`. *(Basis: normative + source + execution)*
- **ADT & reference const parameters (`min_adt_const_params`, `adt_const_params`, `unsized_const_params`):** Auditing soundness obligations on custom const parameter types, specifically why `#[derive(PartialEq)]` (`StructuralPartialEq`) and visibility/`#[non_exhaustive]` constraints guard type-system coherence (`PartialEq` iff `ValTree` equality) and why `f32`/`&mut T`/unions/manual `PartialEq` are unsound as unguarded const parameters. *(Basis: source + execution + derived)*

**Toolchain versions & commits covered:**
- `rust-lang/rust` HEAD source audit: commit `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` *(Basis: source)*
- Executed compiler & Miri runtime differential suite: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)` / LLVM `22.1.6` (commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) *(Basis: execution + source)*
- Nightly reference snapshot for default `-Znext-solver=globally` interaction: `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` / LLVM `23.1.5` (toolchain commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, source snapshot `49d734536222bf28bb6d07d885b3a81d145981da`) *(Basis: execution + source)*
- Normative language rules: `rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` *(Basis: normative)*
- Mechanization environment: `leanprover/lean4` v4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) with `prelude` foundation aligned to `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` *(Basis: derived)*

## Findings

### 1. Normative Specification vs. Compiler Architecture for Const Generics

Per `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/items/generics.md:56-225` and `src/const_eval.md:235-262`), stable Rust defines strict syntactic and semantic boundaries on const generic parameters *(Basis: normative)*:

- **Stable const parameter types (`generics.md:56-57`):**
  > `The only allowed types of const parameters are u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, char and bool.`
- **Standalone generic-param restriction (`generics.md:111-123`, `const_eval.md:260-261`):**
  > `Array type length expressions, array repeat length expressions, and const generic arguments are restricted in their use of outer generic parameters: such an expression must either be a single const generic parameter, or an expression that does not reference any generic parameters.`
- **Non-exhaustive impl matching (`generics.md:210-224`):**
  > `When resolving a trait bound obligation, the exhaustiveness of all implementations of const parameters is not considered when determining if the bound is satisfied.` (For instance, implementing `Bar` separately for `Foo<true>` and `Foo<false>` still fails `Foo<B>: Bar` for generic `const B: bool`.)

Internally in `rustc`, constants entering the type system flow through four primary IR representations defined in `compiler/rustc_type_ir/src/const_kind.rs:21-252`, `compiler/rustc_middle/src/ty/consts.rs:1-21`, `compiler/rustc_middle/src/ty/consts/kind.rs:11-142`, and `compiler/rustc_middle/src/ty/consts/valtree.rs:18-227` *(Basis: source)*:

```rust
// compiler/rustc_type_ir/src/const_kind.rs:21-49, 238-252
pub enum ConstKind<I: Interner> {
    Param(I::ParamConst),
    Infer(InferConst),
    Bound(BoundVarIndexKind, ty::BoundConst<I>),
    Placeholder(ty::PlaceholderConst<I>),
    Alias(ty::IsRigid, ty::AliasConst<I>),
    Value(I::ValueConst),
    Error(I::ErrorGuaranteed),
    Expr(I::ExprConst),
}

pub enum ValTreeKind<I: Interner> {
    Leaf(I::ScalarInt),
    Branch(I::Consts),
}
```

At `compiler/rustc_middle/src/ty/consts.rs:21` and `consts/kind.rs:142`, `ConstKind<'_>` is statically asserted to be `32` bytes and `Expr<'_>` (`ExprKind::{Binop, UnOp, FunctionCall, Cast}`) is statically asserted to be `16` bytes on 64-bit targets. Notably, older internal documentation referencing `ConstKind::Unevaluated` now maps onto `ConstKind::Alias(_, ty::AliasConst { kind: AliasConstKind::Anon { def_id } | Free { .. } | Projection { .. } | InherentSelf { .. } | InherentImpl { .. }, args, .. })` (`const_kind.rs:108-149`). Concrete evaluated constants in types are represented exclusively as `ConstKind::Value(ty::Value { ty, valtree })`, never as raw CTFE interpreter allocations. *(Basis: source)*

---

### 2. `ValTree` Canonicalization, `TypeId` Coherence, and `v0` Symbol Deduplication

#### 2.1 Why CTFE Memory Values Must Be Canonicalized (`valtrees.rs` + `const_kind.rs`)

The doc comment in `compiler/rustc_type_ir/src/const_kind.rs:220-231` states the compiler invariant explicitly *(Basis: source)*:

> `We explicitly choose a different datastructure from the way values are processed within CTFE, as in the type system equal values (according to their PartialEq) must also have equal representation (== on the rustc data structure, e.g. ValTree) and vice versa. Since CTFE uses AllocId to represent pointers, it often happens that two different AllocIds point to equal values. So we may end up with different representations for two constants whose value is &42. Furthermore any kind of struct that has padding will have arbitrary values within that padding, even if the values of the struct are the same.`

`const_to_valtree_inner` in `compiler/rustc_const_eval/src/const_eval/valtrees.rs:83-219` enforces this normalization recursively over CTFE `MPlaceTy` places *(Basis: source)*:

| Type Kind (`ty.kind()`) | `const_to_valtree_inner` Action (`valtrees.rs:108-214`) | Canonical `ValTree` Form / Error | Basis |
| --- | --- | --- | --- |
| `ty::FnDef(..)` | Increments `*num_nodes` | `ValTree::zst(tcx)` (`Branch([])`) | source |
| `Bool \| Int \| Uint \| Float \| Char` | Reads immediate `ScalarInt`, increments `*num_nodes` | `ValTree::from_scalar_int(tcx, val)` (`Leaf`) | source |
| `ty::Pat(base, ..)` | Switches `place.layout` to base type & recurses | Identical to base type `ValTree` | source |
| `ty::RawPtr(_, _)` | Rejects `ScalarPair` (wide raw ptr); converts thin scalar via `try_to_scalar_int()` | `Leaf(ScalarInt)` if integer-disguised; `NonSupportedType(ty)` if `AllocId` provenance or wide | source |
| `ty::FnPtr(..)` | Rejects unconditionally (`valtrees.rs:153`) | `Err(ValTreeCreationError::NonSupportedType(ty))` | source |
| `ty::Ref(_, _, _)` | Calls `ecx.deref_pointer(place)` and recurses on pointee | Pointee `ValTree` (`AllocId` erased) | source |
| `ty::Str \| ty::Slice(_) \| ty::Array(_, _)` | Calls `slice_branches`: projects indices `0..place.len(ecx)` | `Branch([v_0, ..., v_{n-1}])` (`u8` leaves for `str`) | source |
| `ty::Tuple(elem_tys)` | Calls `branches(..., None)` projecting fields `0..len` | `Branch([f_0, ..., f_{k-1}])` (no padding) | source |
| `ty::Adt(def, _)` (`!is_union`) | Reads active discriminant; calls `branches` with `def.is_enum().then_some(variant)` | Struct: `Branch([f_i])`; Enum: `Branch([Leaf(variant_idx: u32), f_i...])` (no padding) | source |
| `Union`, `Dynamic`, `Alias`, `Closure`, `Never`, `Coroutine`, `UnsafeBinder` | Rejected | `Err(ValTreeCreationError::NonSupportedType(ty))` | source |

**HEAD (`0259d5e9`) vs. `1.98.0-nightly` (`14210df0e`) cycle-guard refinement:** Comparing `src_cache/head/const_eval_valtrees.rs:21-219` against `src_cache/local198/const_eval_valtrees.rs` shows that upstream HEAD replaced bare recursion + `ensure_sufficient_stack` with explicit `visited: &mut FxHashSet<MPlaceTy<'tcx>>` and `settled: &mut FxHashMap<MPlaceTy<'tcx>, EvalToValTreeResult<'tcx>>` memoization, returning `Err(ValTreeCreationError::CyclicConst)` on self-referential reference graphs (`valtrees.rs:94-106`) instead of risking exponential DAG traversal. Notice also that `const_to_valtree_inner` itself admits `ty::Float(_)` leaves (`valtrees.rs:113`) because `ValTree` is shared by constant pattern matching (`#[allow(illegal_floating_point_literal_pattern)]` history), whereas const generic parameter admission (`coherence/builtin.rs`) rejects floats before any `ValTree` can become a generic parameter argument! *(Basis: source)*

Conversely, `valtree_to_const_value`, `valtree_to_ref`, and `valtree_into_mplace` (`valtrees.rs:298-487`) reconstruct read-only immutable CTFE allocations (`intern_const_alloc_recursive(ecx, InternKind::Constant, alloc)`) from canonical `ValTree`s, reconstructing unsized slice/`&str` metadata (`MemPlaceMeta::Meta(valtree.unwrap_branch().len())` via `reconstruct_place_meta` at `valtrees.rs:223-255`), writing zero/uninit padding automatically, and rebuilding `enum` variant layouts cleanly via `destructure_adt_const()` (`middle_valtree.rs:210-226`). *(Basis: source)*

#### 2.2 Structural `v0` Symbol Mangling & Live Empirical `TypeId`/LLVM IR Verification

In `compiler/rustc_symbol_mangling/src/v0.rs:771-947`, `SymbolMangler::print_const` requires `ConstKind::Value(cv)` for concrete monomorphizations (`Expr`/`Infer`/`Bound`/`Placeholder`/`Error` hit `bug!()` at `v0.rs:800`), maintains a backreference map `self.consts.get(&ct)` (`v0.rs:803-806, 943-945`), and recursively encodes `cv = Value { ty: ct_ty, valtree }` using deterministic prefix grammar:
- Scalars: type prefix (`j` = `usize`, `h` = `u8`, `m` = `u32`, `b` = `bool`, etc.) + optional `n` for negative signed integers + lowercase hex scalar bits + `_` (`v0.rs:812-830`).
- `&str` (`ty::Str`): wraps `valtree` in `&str` (`Ty::new_imm_ref`), calls `cv.try_to_raw_bytes(tcx)` (`middle_valtree.rs:139-166`), and emits `"e"` + two-digit lowercase hex per UTF-8 byte + `"_"` (`v0.rs:833-853`), preceded by `"R"` for the `&` reference (`v0.rs:857-867`). Note that `v0.rs:855-856` still leaves `FIXME(valtrees)` regarding removing the `str` special case once unsized constants normalize uniformly.
- Arrays / Slices / Tuples: `"A"` (array or slice) / `"T"` (tuple) followed by recursively mangled field constants and terminated by `"E"` (`v0.rs:869-891`).
- ADTs (`Struct` / `Enum`): calls `cv.destructure_adt_const()`, emits `"V"` + variant `DefPath`, then `"U"` (unit variant), `"T" ... "E"` (tuple struct/variant), or `"S"` + disambiguated field identifiers + field values + `"E"` (struct variant) (`v0.rs:892-935`).

Live differential execution via `support/probe_const_generics_valtree_and_structural_eq.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (both native `-O0`/`-O2` and `miri 0.1.0` Stacked Borrows & `-Zmiri-tree-borrows`, see `support/probe_results.json`) confirms 100% deduplication across distinct syntactic expressions, distinct padding initializations, and distinct CTFE reference allocations *(Basis: execution)*:

| Probe Pair Tested (`TypeId::of` & Generic Call Pairs) | Canonical `ValTree` | Observed `TypeId` Equality & Runtime Output | Observed Single Deduplicated LLVM `v0` Symbol (`-O0` & `-O2`) | Basis |
| --- | --- | --- | --- | --- |
| `[u8; 2 + 2]` vs. `[u8; 4]` & `size_fn::<{ 2 * 2 }>` vs. `size_fn::<4>` | `Leaf(4: usize)` | `ARR=true,false`, `SZ=8,8` | `_RINv...7size_fnKj4_EB2_` | execution |
| `Tag { a: 2 + 3, b: !false }` vs. `Tag { a: 5, b: true }` (`{ a: u8, b: bool }`) | `Branch([Leaf(5: u8), Leaf(1: bool)])` | `TAG=true,15,15` | `_RINv...7use_tagKVNtB2_3TagS1ah5_1bb1_EEB2_` | execution |
| `Padded { flag: true, val: 42 }` vs. `Padded { flag: true, val: 40 + 2 }` (`bool` + 3B pad + `u32`) | `Branch([Leaf(1), Leaf(42)])` | `PAD=true,42,42` | `_RINv...10use_paddedKVNtB2_6PaddedS4flagb1_3valm2a_EEB2_` | execution |
| `Mode::Checked(3 + 4)` vs. `Mode::Checked(7)` | `Branch([Leaf(1: u32), Leaf(7: u8)])` | `MODE=true,7,7` | `_RINv...8use_modeKVNtNtB2_4Mode7CheckedTh7_EEB2_` | execution |
| `use_str::<{ "anneal" }>` vs. `use_str::<"anneal">` | `Branch([Leaf(97), 110, 110, 101, 97, 108])` | `STR=true,6,6` | `_RINv...7use_strKRe616e6e65616c_EB2_` | execution |
| `use_slice::<{ &[1u8, 2, 3] }>` vs. `use_slice::<{ &ARR_3 }>` | `Branch([Leaf(1), Leaf(2), Leaf(3)])` | `SLICE=true,3,3` | `_RINv...9use_sliceKRAh1_h2_h3_EEB2_` | execution |
| `WrapRef::<{ &TAG_STATIC }>` vs. `WrapRef::<{ &Tag { a: 2 + 3, b: !false } }>` | `Branch([Leaf(5), Leaf(1)])` (ref `AllocId` erased) | `REF=true` | Deduplicated via dereferenced `ValTree` | execution |

And matching the `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` nightly reference snapshot (`size_fn::<{ 2 * 2 }>` vs. `size_fn::<4>`), both `opt_0` and `opt_2` LLVM IR emit **1** single function (`@_RINv...7size_fnKj4_EB2_`), proving version-stable `v0` structural deduplication across `1.98` and `1.102`. *(Basis: execution)*

---

### 3. `min_const_generics` vs. `generic_const_exprs` Syntactic Equality & Next-Solver Interaction

#### 3.1 `AnonConstKind` Classification & Repeat-Count `#76200` Boundary (`collect.rs`)

`compiler/rustc_hir_analysis/src/collect.rs:1813-1841` classifies every `DefKind::AnonConst` before lowering:

```rust
// compiler/rustc_hir_analysis/src/collect.rs:1813-1841
fn anon_const_kind<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> ty::AnonConstKind {
    ...
    match tcx.hir_node(parent_node_id) {
        hir::Node::ConstArg(const_arg) => {
            if tcx.features().generic_const_exprs() {
                ty::AnonConstKind::GCE
            } else if tcx.features().gca() {
                ty::AnonConstKind::MCG
            } else if let hir::Node::Expr(hir::Expr {
                kind: hir::ExprKind::Repeat(_, repeat_count),
                ..
            }) = tcx.parent_hir_node(parent_node_id)
                && repeat_count.hir_id == parent_node_id
            {
                ty::AnonConstKind::RepeatExprCount
            } else {
                ty::AnonConstKind::MCG
            }
        }
        hir::Node::Expr(hir::Expr {
            kind: hir::ExprKind::ConstBlock(..) | hir::ExprKind::InlineAsm(..),
            ..
        }) => ty::AnonConstKind::NonTypeSystemInline,
        _ => ty::AnonConstKind::NonTypeSystemAnon,
    }
}
```

Four distinct behaviors follow directly from this five-way classification and live empirical tests (`probe_results.json`) *(Basis: source + execution)*:
1. **`AnonConstKind::MCG` (array type lengths & const generic arguments without unstable features):** Standalone parameter `[u8; N]` / `[0u8; N]` compiles (`rc=0`), whereas any arithmetic/expression referencing `N` (`[u8; N + 1]`) or any type parameter (`[u8; { let _: Option<T> = None; 4 }]`) fails at HIR lowering with `"error: generic parameters may not be used in const operations"` / `"cannot perform const operation using N"` (or `"T"`).
2. **`AnonConstKind::RepeatExprCount` (`[val; count]`):** Arithmetic over const params (`[0u8; N + 1]`) is rejected immediately (`rc=1`, `"cannot perform const operation using N"`). However, legacy expressions referencing *type* parameters indirectly via trait/impl associated constants (`impl<T> H<T> { const LEN: usize = 4; } ... [0u8; H::<T>::LEN]`) STILL compile on current Rust (`rc=0`) under the backwards-compatibility `#76200` `#[warn(const_evaluatable_unchecked)]` lint! By contrast, directly referencing a type parameter inside an inline block (`[0u8; { let _: Option<T> = None; 4 }]`) fails (`rc=1`) with `E0308` (`expected an array with a size of 4, found one with a size of { let _: Option<T> = None; 4 }`) plus `"error: constant expression depends on a generic parameter"`.
3. **`feature(gca)` branch (`collect.rs:1822`):** Notice that `feature(gca)` routes anonymous `ConstArg`s through `AnonConstKind::MCG` rather than `GCE`, while supporting direct generic const items wrapped in `gca!(...)` (`feature(gca_const_items)`) without building `thir_abstract_const` / `ConstEvaluatable` clauses (`clauses_of.rs:442`, `is_const_evaluatable` at `const_evaluatable.rs:89-94`).
4. **MIR zero-repeat edge guard (`hir_typeck_expr.rs:1720-1751`):** Note also `check_expr_repeat` works around issue `#165323` when `[const { panic!() }; 0]` lowers to `[]` by restoring `old_diverges` only when `ConstKind::Value(0)` or `ConstKind::Infer`, explicitly NOT for `Param`/`Alias`/`Expr` (`hir_typeck_expr.rs:1737-1745`).

#### 3.2 `ConstEvaluatable` Clause Collection & Syntactic-Only `AbstractConst` Unification

Under `#![feature(generic_const_exprs)]`:

1. **Signature & `impl` Header Clause Injection (`clauses_of.rs:401-484`):** `const_evaluatable_clauses_of` runs a `ConstCollector` over existing predicates, `impl` trait_refs (`L466-468`), `impl` `self_ty` (`L471-473`), and function signatures (`fn_sig` at `L475-481`), automatically inserting `(ClauseKind::ConstEvaluatable(c), span)` for every non-default, non-direct `ConstKind::Alias`. Consequently:
   - `pub fn sig_auto<const N: usize>(arr: [u8; N + 1]) -> usize { arr.len() }` **compiles cleanly without an explicit `where` clause** (`gce_sig_auto_clause_without_explicit_where`, `rc=0`) because `[u8; N + 1]` appears in `fn_sig`.
   - Using `[0u8; N + 1]` only inside a function body (`gce_body_missing_const_evaluatable_bound`) or calling a callee constrained by `where [(); N + 1]:` from an unconstrained caller (`gce_caller_missing_const_evaluatable_bound`) **fails (`rc=1`)** with `"error: unconstrained generic constant"`, suggesting `"help: try adding a where bound: where [(); N + 1]:"`. *(Basis: source + execution)*
2. **AST Expansion & Unique Subtree Unification (`const_evaluatable.rs:32-69, 159-229` & `abstract_const.rs:37-79`):** When `is_const_evaluatable` encounters an `AnonConst` with generic parameters, `tcx.expand_abstract_consts(unexpanded_ct)` folds `AliasConst` nodes into `tcx.thir_abstract_const(def_id)` ASTs built from `ConstKind::Expr(Expr { kind: ExprKind::{Binop, UnOp, FunctionCall, Cast}, args })`. Note `is_const_evaluatable` lines `63-68` intentionally ICE if a fully concrete `ConstKind::Expr` somehow reaches evaluation without an enclosing `AnonConst`. Then `satisfied_from_param_env` visits every `ClauseKind::ConstEvaluatable(ce)` in `param_env.caller_bounds().non_trait_clauses()` and walks every AST subtree `c` of `b_ct` using `Visitor::visit_const`:
   - For each node `c`, it probes `ocx.eq(&ObligationCause::dummy(), self.param_env, c, self.ct)` (`const_evaluatable.rs:179-183`).
   - That subtree traversal allows `where [(); (N + 1) * 2]:` to satisfy `[u8; N + 1]` (`gce_subtree_satisfies_bound`, `rc=0`), **provided there is a unique matching candidate** (`single_match`: repeating identical `o == c` stays `Ok(c)`, while two distinct unifying subtrees downgrade `single_match` to `Some(Err(()))` ambiguity!).
   - Critically, `ocx.eq` performs **pure syntactic unification** on `ConstKind::Expr` AST nodes — there is zero commutativity, associativity, distributivity, or constant-folding normalization! Thus `fn bad_comm<const N: usize>(a: [u8; N + 1], b: [u8; 1 + N]) { same_type(a, b) }` fails (`rc=1`, `gce_syntactic_unification_n_plus_1_vs_1_plus_n`) with:
     ```text
     error[E0308]: mismatched types
      --> <tmp>/b_gce_e0308.rs:8:18
       |
     8 |     same_type(a, b)
       |                  ^ expected `N + 1`, found `1 + N`
     ```
   *(Basis: source + execution)*

#### 3.3 `-Znext-solver=globally` Interaction & Nightly Regression Boundary (`1.98` vs. `1.102`/HEAD)

Source inspection + differential compiler runs reveal an important cross-version behavioral boundary between the two nightly cohorts *(Basis: source + execution)*:

| Configuration | `rustc 1.98.0-nightly (14210df0e 2026-05-31)` Behavior (`probe_results.json`) | `rustc 1.102.0-nightly (3ef0c22cd)` & `0259d5e9` HEAD Behavior (`feature_gate.rs:735-783`) |
| --- | --- | --- |
| `#![feature(generic_const_exprs)]` alone | Compiles cleanly with only `incomplete_features` `#76560` warning (legacy solver default). | Default `-Znext-solver=globally` is auto-downgraded by `warn_next_solver_and_gce` to `-Znext-solver=coherence` with warning referencing `#160895`; crate compiles (`rc=0`). |
| `#![feature(generic_const_exprs)]` + explicit `-Znext-solver=globally` | Hard error (`rc=1`): `-Znext-solver=globally and generic_const_exprs are incompatible` + `E0275` overflow evaluating `[(); N + 1]`. | `warn_next_solver_and_gce` (`feature_gate.rs:735-751`) downgrades solver to `NextSolverConfig::Coherence` with warning and falls back to the stable solver. |
| `#![feature(gca_const_items)]` | Requires `-Znext-solver=globally` (`check_features_requiring_new_solver` at `feature_gate.rs:763-783` fails if not `Globally`). | Requires `-Znext-solver=globally`; mutually incompatible with `generic_const_exprs` in a crate since GCE downgrades solver away from `Globally`. |

---

### 4. `ConstParamTy` & `StructuralPartialEq` Admission Rules and Soundness Gate

#### 4.1 Trait Architecture & Builtin Coherence Gate (`core/marker.rs`, `coherence/builtin.rs`, `traits/misc.rs`)

In `library/core/src/marker.rs:255-274, 1105-1145`:
- `#[lang = "const_param_ty"] pub trait ConstParamTy_: StructuralPartialEq + Eq {}` requires BOTH `Eq` and the compiler-internal unstable marker trait `#[lang = "structural_peq"] pub trait StructuralPartialEq {}` (`#[unstable(feature = "structural_match", issue = "31434")]`).
- `StructuralPartialEq` is automatically emitted **only** by `#[derive(PartialEq)]` and built-in primitive marker impls (`usize..isize`, `u8..i128`, `bool`, `char`, `str`, `()`, `[T; N]`, `[T]`, `&T`). Manual `impl PartialEq` does **not** implement `StructuralPartialEq`.
- `ConstParamTy_` additionally requires `#[derive(ConstParamTy)]` (for ADTs, or built-in impls for integers/`bool`/`char`/`()`/`[T; N]`, and under `#[unstable_feature_bound(unsized_const_params)]`: `str`, `[T]`, `&T`).

During coherence checking (`compiler/rustc_hir_analysis/src/coherence/builtin.rs:170-245` + `compiler/rustc_trait_selection/src/traits/misc.rs:92-201`), `visit_implementation_of_const_param_ty` executes the following exact decision tree (unless `#![feature(const_param_ty_unchecked)]` bypasses it at `coherence/builtin.rs:183-185`):

| Candidate Type / Property | `min_adt_const_params` Gate (`!adt_const_params`) | `adt_const_params` Gate | Required Secondary Feature | Compiler Error / Code (`probe_results.json` Verified) | Basis |
| --- | --- | --- | --- | --- | --- |
| `u8..u128`, `usize`, `i8..i128`, `isize`, `bool`, `char`, `()` | **Admitted** | **Admitted** | None (stable scalar primitives / `()` needs `min_adt_const_params` or built-in) | `rc=0` | source + execution |
| `[T; N]` / `(T1, ...)` | **Admitted** iff element(s) `ConstParamTy` (`[T; N]` built-in) | **Admitted** iff elements `ConstParamTy` | `[T; N]` built-in; tuples via ADT/tuple checking | `rc=0` (`misc.rs:117, 120`) | source |
| `&T`, `[T]`, `str` (`&'static str`, `&'static [u8]`) | **Rejected** (`UnsizedConstParamsFeatureRequired`) without `unsized_const_params` | **Admitted** iff `unsized_const_params` enabled & inner `ConstParamTy` | `#![feature(unsized_const_params)]` (`misc.rs:109-116, 160-171`) | `rc=0` with `unsized_const_params` (`SLICE`, `STR`, `REF`) | source + execution |
| `struct S(u8)` with private fields (`pub struct` + private field) | **Rejected** (`ConstParamTyFieldVisMismatch`, `builtin.rs:187-205`) | **Admitted** (`rc=0`, `positive_adt_private_field`) | `#![feature(adt_const_params)]` | `"struct fields are less visible than the struct"` (`min_adt` `rc=1`) vs `rc=0` (`adt`) | source + execution |
| `#[non_exhaustive] struct/enum` | **Rejected** (`NonExhaustive`, `misc.rs:123-134`) | **Admitted** (`rc=0`) | `#![feature(adt_const_params)]` | `"non exhaustive const params are forbidden"` (`min_adt` `rc=1`) | source + execution |
| Struct/enum with manual `PartialEq` (`#[derive(ConstParamTy, Eq)]`) | **Rejected** | **Rejected** | N/A (`#[derive(PartialEq)]` required) | `E0277: the type CustomEq does not #[derive(PartialEq)]` (note `StructuralPartialEq` bound) | source + execution |
| `f32` / `f64` | **Rejected** (`NotAnAdtOrBuiltinAllowed`, `misc.rs:150`) | **Rejected** (`E0741`) | Forbidden by design (`-0.0 == +0.0`, `NaN != NaN`) | `"f32 is forbidden as the type of a const generic parameter"` / `E0741` | source + execution |
| `&'static mut u8` (`Mutability::Mut`) | **Rejected** (`NotAnAdtOrBuiltinAllowed`) | **Rejected** (`E0741`) | Forbidden (`misc.rs:109` matches `Mutability::Not` only) | `E0741: &'static mut u8 can't be used as a const parameter type` | source + execution |
| `union` / `fn()` ptr | **Rejected** (`misc.rs:122, 150`) | **Rejected** | Forbidden (`union` derive rejected; `fn()` lacks canonical structural eq) | `"this trait cannot be derived for unions"` | source + execution |

*Implementation delta note (`1.98.0-nightly` vs. `0259d5e9` HEAD):* `coherence/builtin.rs:186` at `14210df0e` matches `ImplPolarity::Negative | ImplPolarity::Reservation`, whereas HEAD `0259d5e9` simplifies line 179 to `ImplPolarity::Negative` and refactors `errors::*` into `diagnostics::*`; all semantic guards (`const_param_ty_unchecked`, `!adt_const_params` visibility & `#[non_exhaustive]` checks, `unsized_const_params` obligation) are identical across both commits. *(Basis: source)*

#### 4.2 Why `StructuralPartialEq` Is Required for Soundness: Live Divergence Witness (`Weird`)

Because `rustc` determines type identity (`std::any::TypeId::of::<Wrap<C>>()` and monomorphization symbol names) by structural equality of canonical `ValTree`s (`ConstKind::Value`), sound const-generic abstraction requires a **biconditional bisimulation**: two values `v1, v2` satisfy runtime `v1 == v2` iff `const_to_valtree(v1) == const_to_valtree(v2)`.

The `manual_structural_peq_unsoundness_witness` experiment (`support/probe_results.json`) demonstrates what happens when an unstable user manually implements `StructuralPartialEq` on a type whose `PartialEq` disagrees with structural equality (`#![feature(adt_const_params, structural_match)]` with `Weird(u8)`, `PartialEq::eq` returning `true`, plus `impl StructuralPartialEq for Weird {}`):
- At runtime (verified under `-O2` native binary and Miri Stacked Borrows & Tree Borrows), `Weird(1) == Weird(2)` evaluates to **`RUNTIME_EQ=true`**.
- Yet `const_to_valtree` encodes field bits `Leaf(1)` vs `Leaf(2)` cleanly into distinct symbols (`_RINvMs8_...TypeId2ofINt...WrapKVNtBN_5WeirdTh1_EEEBN_` vs. `...KVNtBN_5WeirdTh2_EEEBN_`), yielding **`TYPEID_EQ=false`**.
- At `-O2`, LLVM constant-folds the entire observation into `store i8 1, ptr %rt_eq` alongside `store i8 0, ptr %ty_eq` (`probe_results.json:360`).

Safe Rust closes this soundness hole entirely via `StructuralPartialEq`: because only `#[derive(PartialEq)]` and verified scalar/composite built-in marker impls provide `StructuralPartialEq`, runtime equality agrees componentwise with canonical `ValTree` equality (ignoring padding bytes and `&T` `AllocId` pointers, which `const_to_valtree_inner` also erases). Similarly, `f32` violates both directions even at bit-level representation: `+0.0 == -0.0` (`0x00000000` vs. `0x80000000`) violates `PartialEq -> ValTree`, while `NaN != NaN` (`0x7fc00000`) violates `ValTree -> PartialEq`. *(Basis: source + execution + derived)*

---

### 5. Kernel-Checked `Lean v4.34.1` Formalization (`ConstGenericsValTreeCanonicalizationAndStructuralEqSoundness.lean`)

The formal artifact `support/ConstGenericsValTreeCanonicalizationAndStructuralEqSoundness.lean` (`2,665` lines, `127,242` bytes) formalizes all three pillars in `prelude` + `Init.*` (`Lean v4.34.1`) with every value definition marked `noncomputable def` and higher-order `mapOpt`/`mapOptBool` combinators ensuring clean structural recursion over nested inductive `ConstTy`/`List ConstTy`/`List (List ConstTy)`. *(Basis: derived)*

Verification under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` AND an independent MetaM constant/axiom environment audit (`support/lean_verification_receipt.json`) established:
- **`0` errors, `0` warnings** (`exit 0`).
- **`1,046` local constants** (`16` inductives, `633` defs/auxiliaries, `294` kernel `thmInfo` constants / `78` top-level `theorem` declarations [`89` total `theorem` declarations]).
- **`0` `._unsafe_rec` constants**, **`0` `unsafe` constants**, **`0` `opaque`/`axiom` declarations**, **`0` `sorryAx`**, **`0` `Classical.choice`**, **`0` `Quot.sound`**, **`0` `Lean.ofReduceBool`/`nat_decide`**, **`0` `omega`/`bv_decide`**, **`all_axioms_used = ["propext"]`** (`167` kernel theorems 100% axiom-free, `127` using only `propext`).

| Pillar & Claim | Formalized Lean Symbol (`ConstGenericsValTreeCanonicalizationAndStructuralEqSoundness.lean`) | Lines | Axioms & Purity | Basis |
| --- | --- | --- | --- | --- |
| Reference `AllocId` erasure & aggregate padding erasure in `constToValTree` | `ctfe_alloc_id_erasure`, `struct_padding_erasure`, `tuple_padding_erasure`, `enum_padding_erasure` | L567–589 | Axiom-free (`0` `._unsafe_rec`) | derived |
| Rejection of unions, fn pointers, and `&mut` by `ValTree` | `union_rejected_by_valtree`, `fnPtr_rejected_by_valtree`, `mut_ref_rejected_by_valtree` | L590–601 | Axiom-free | derived |
| Round-trip reconstruction soundness (`valtree_to_const_value` -> `const_to_valtree`) | `valTree_roundtrip`, `valTreeHeterog_roundtrip`, `valTreeVariants_roundtrip`, `valTreeHomog_roundtrip` | L674–875 | `propext` max, `0` `Classical.choice` | derived |
| Semantic eval equality -> unique `ValTree`, `TypeIdentityKey`, and `v0` symbol | `eval_eq_implies_canonical_valtree`, `eval_eq_guarantees_typeid_and_v0_dedup` | L1035–1071 | `propext` max | derived |
| Concrete witnesses matching live LLVM `v0` & `TypeId` probes | `witness_array_2_plus_2_eq_4_valtree_and_v0`, `witness_tag_struct_dedup_with_padding`, `witness_padded_struct_dedup_m2a`, `witness_mode_enum_checked_7_dedup`, `witness_str_anneal_ref_dedup`, `witness_ref_tag_alloc_erasure` | L1080–1135 | 100% axiom-free (`rfl`) | derived |
| `min_const_generics` param-free closure & rejection of `N + 1` | `mcg_closed_const_env_independent`, `mcg_rejects_param_plus_one`, `gce_admits_param_plus_one` | L1372–1436 | `propext` max | derived |
| `generic_const_exprs` syntactic soundness vs. `N + 1` / `(N + 1) + 2` incompleteness & subtree match | `synEq_implies_semEq`, `gce_syntactic_incompleteness_n_plus_1`, `gce_syntactic_incompleteness_assoc_fold`, `gce_subtree_satisfaction_witness`, `gce_solver_compatibility_theorems` | L1360–1480 | `propext` max | derived |
| `ConstParamTy` (`StructuralPartialEq`) <-> `ValTree` / `TypeIdentityKey` bisimulation | `structuralEq_iff_valTree_eq_aux`, `structuralEq_iff_valTree_eq`, `admitted_valtree_typeid_bisimulation` | L2007–2545 | `propext` max (`0` `Classical.choice`) | derived |
| IEEE-754 `f32` (`-0.0 == +0.0`, `NaN != NaN`), `&mut`/union/fnptr, manual `PartialEq`, & gate precision | `f32_neg_zero_eq_pos_zero_yet_distinct_valtree`, `f32_nan_irreflexive_vs_valtree_eq`, `constParamTy_rejects_f32_mut_union_fnptr`, `admit_rejects_manual_partial_eq_weird`, `weird_manual_structural_peq_unsoundness_witness`, `feature_gate_adt_and_unsized_precision` | L2581–2662 | 100% axiom-free / `rfl` | derived |

## Boundaries

To preserve strict negative-space epistemic hygiene, claims outside the verified envelope are partitioned into the four canonical categories:

1. **Known not to apply:**
   - **CTFE pointer-provenance identity inside `TypeId` or mangled symbols:** `ValTree` conversion (`const_to_valtree_inner`) dereferences shared references and strips padding bytes; two distinct CTFE allocations pointing to equal pointee data (`&TAG_STATIC` vs. `&Tag { a: 2 + 3, b: !false }`) are known **not** to yield distinct `TypeId`s or distinct `v0` symbols *(Basis: source + execution + derived)*.
   - **Algebraic reasoning inside `generic_const_exprs` (`N + 1 == 1 + N`):** Under `rustc@0259d5e9` HEAD, `14210df0e`, and `49d73453`, `satisfied_from_param_env` and type unification compare `ConstKind::Expr` ASTs syntactically via `ocx.eq`. Equational identities (`add_comm`, `add_assoc`, constant folding over symbolic params) are known **not** to hold during `rustc` const-generic type unification *(Basis: source + execution + derived)*.
   - **`min_adt_const_params` vs. `adt_const_params` on private fields and `#[non_exhaustive]` ADTs:** Under `#![feature(min_adt_const_params)]`, private struct fields and `#[non_exhaustive]` variants are rejected (`coherence/builtin.rs:187-205`, `traits/misc.rs:123-134`); this restriction explicitly drops out once `#![feature(adt_const_params)]` is enabled *(Basis: source + execution + derived)*.
   - **Manual `PartialEq` compatibility with `#[derive(ConstParamTy)]`:** Implementing `PartialEq` manually without `#[derive(PartialEq)]` is rejected with `E0277` (`StructuralPartialEq` unsatisfied), even if the manual implementation happens to be extensionally identical to componentwise equality *(Basis: source + execution)*.

2. **Unsupported:**
   - **`f32`/`f64`, `&mut T`, unions, closures, trait objects (`dyn Trait`), `fn()` pointers, and `AllocId`-backed raw pointers as const parameter types:** Unsupported in both `min_const_generics` and `adt_const_params` / `unsized_const_params` because they violate either `ValTree` representation (`valtrees.rs:130-210`) or the `StructuralPartialEq` bisimulation invariant (`E0741` / `NotAnAdtOrBuiltinAllowed`) *(Basis: source + execution + derived)*.
   - **`generic_const_exprs` combined with `-Znext-solver=globally` / `#![feature(gca_const_items)]`:** Simultaneous activation of `#![feature(generic_const_exprs)]` and `-Znext-solver=globally` is unsupported (either hard-errors on `1.98.0-nightly` or auto-downgrades to `-Znext-solver=coherence` on `1.102`/HEAD, making `gca_const_items` unusable in the same crate) *(Basis: source + execution)*.

3. **Not examined:**
   - **`feature(min_generic_const_args)` / full `feature(gca_const_items)` lowering & `AliasConstKind::InherentSelf` normalization:** Only the `anon_const_kind` dispatch (`collect.rs:1822-1823`), `clauses_of.rs:442` skip (`is_direct_const`), `const_evaluatable.rs:89-94` branch, and `feature_gate.rs:763-783` `-Znext-solver=globally` gate were inspected; full `gca!` macro expansion, `AssocConst` normalization under `-Znext-solver=globally`, and downstream codegen for `min_generic_const_args` were **not examined** *(Basis: source)*.
   - **Legacy symbol mangling (`-C symbol-mangling-version=legacy`):** All symbol deduplication claims were verified specifically under `rustc_symbol_mangling::v0` (`v0.rs:771-947`) and default `-C symbol-mangling-version=v0` IR emission (`probe_results.json`); legacy mangling hash collisions or formatting were **not examined** *(Basis: source + execution)*.
   - **Recursive / cyclic const references (`VALTREE_MAX_NODES` & `ValTreeCreationError::CyclicConst` paths):** Static guards (`valtrees.rs:94-106`) were observed directly in HEAD `0259d5e9` source, whereas live adversarial inputs overflowing `VALTREE_MAX_NODES` or triggering cyclic `&'static` graphs during valtree lowering were **not executed** *(Basis: source)*.

4. **Unknown:**
   - **Stabilization timeline and final solver convergence between `min_adt_const_params`, `generic_const_exprs`, and `gca_const_items`:** Upstream tracking issues (`#76200`, `#76560`, `#95174`, `#128028`, `#154042`, `#160895`) document active design transitions on `-Znext-solver=globally` and `const_evaluatable` unification; exact future stabilization versions and whether `generic_const_exprs` will be superseded entirely by `min_generic_const_args`/`gca_const_items` remain **unknown** *(Basis: source + execution)*.
   - **Codegen / Miri behavior of `#[feature(adt_const_params)]` when `const_param_ty_unchecked` bypasses coherence on unions or complex unsized types:** Because `const_param_ty_unchecked` skips `visit_implementation_of_const_param_ty` (`coherence/builtin.rs:183-185`) while `const_to_valtree_inner` still rejects unions (`valtrees.rs:174-175`), full ICE vs. graceful error surfaces across arbitrary unchecked types are **unknown** without exhaustive fuzzing *(Basis: source)*.

## Evidence

### 1. Upstream Primary Sources Inspected

| Repository & Commit (`40`-hex SHA) | File & Line Range | Key Symbols & Observed Semantics | Basis |
| --- | --- | --- | --- |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_middle/src/ty/consts.rs:1-21` | Re-exports `ir::ConstKind`, `AliasConst`, `AliasConstKind`, `Const`; `static_assert_size!(ConstKind<'_>, 32)` | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_type_ir/src/const_kind.rs:21-49, 108-149, 220-252` | `ConstKind::{Param, Infer, Bound, Placeholder, Alias, Value, Error, Expr}`, `AliasConstKind::{Projection, InherentSelf, InherentImpl, Free, Anon}`, `ValTreeKind::{Leaf, Branch}` | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_middle/src/ty/consts/kind.rs:11-142` | `ExprKind::{Binop, UnOp, FunctionCall, Cast}`, `Expr<'tcx>`, `static_assert_size!(Expr<'_>, 16)` | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_middle/src/ty/consts/valtree.rs:139-227` | `Value::try_to_raw_bytes`, `Value::destructure_adt_const` | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` & `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_const_eval/src/const_eval/valtrees.rs:21-255, 298-487` | `branches`, `slice_branches`, `const_to_valtree_inner`, `reconstruct_place_meta`, `valtree_to_const_value`, `valtree_into_mplace`; HEAD adds `visited`/`settled` `CyclicConst` guard | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` & `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_symbol_mangling/src/v0.rs:771-947` | `SymbolMangler::print_const` (`self.consts` cache, `e<hex>_` for `str`, `R`/`A`/`T`/`V`+`U`/`T`/`S` encodings) | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_hir_analysis/src/collect.rs:1813-1841` | `anon_const_kind` (`AnonConstKind::{GCE, MCG, RepeatExprCount, NonTypeSystemInline, NonTypeSystemAnon}`) | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_hir_analysis/src/collect/clauses_of.rs:401-484` | `const_evaluatable_clauses_of` (`ConstCollector` auto-injecting `ConstEvaluatable` from `fn_sig` / `impl` headers, skipping const-param defaults and direct consts) | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_middle/src/ty/abstract_const.rs:37-79` | `TyCtxt::expand_abstract_consts` folding `ConstKind::Alias` via `thir_abstract_const` | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_trait_selection/src/traits/const_evaluatable.rs:26-229` | `is_const_evaluatable`, `satisfied_from_param_env` (`Visitor::visit_const` syntactic `ocx.eq` + `single_match` uniqueness) | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_hir_typeck/src/expr.rs:1684-1769` | `FnCtxt::check_expr_repeat` (`#165323` zero-repeat workaround limited to `Value(0)`/`Infer`) | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` & `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_hir_analysis/src/coherence/builtin.rs:170-245`, `compiler/rustc_trait_selection/src/traits/misc.rs:92-201` | `visit_implementation_of_const_param_ty`, `type_allowed_to_implement_const_param_ty` (`const_param_ty_unchecked`, `!adt_const_params` vis & `NonExhaustive` checks, `unsized_const_params` bound) | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_ast_passes/src/feature_gate.rs:735-783`, `compiler/rustc_ast_passes/src/diagnostics.rs:41-50`, `compiler/rustc_session/src/options.rs:1860-1872` | `warn_next_solver_and_gce` (`NextSolverDisabledForGenericConstExprs`, `#160895`), `check_features_requiring_new_solver` (`gca_const_items`), `parse_next_solver_config` | source |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `library/core/src/marker.rs:255-274, 1099-1145` | `StructuralPartialEq`, `ConstParamTy_`, `ConstParamTy` derive, built-in `marker_impls!` | source |
| `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/items/generics.md:56-225`, `src/const_eval.md:235-262` | Normative const-generic allowed types, standalone generic-param rule, and non-exhaustiveness of const impls | normative |

### 2. Differential Empirical Artifacts (`rustc`, `Miri`, MIR, & LLVM IR)

All probes are automated and reproducible via [`support/probe_const_generics_valtree_and_structural_eq.py`](support/probe_const_generics_valtree_and_structural_eq.py), with full captured stdout/stderr, Miri Stacked Borrows (`cargo miri run`) and Tree Borrows (`MIRIFLAGS=-Zmiri-tree-borrows`) runs, optimized MIR excerpts, and `-O0`/`-O2` LLVM IR definitions stored in [`support/probe_results.json`](support/probe_results.json). *(Basis: execution)*

Key empirical verification outcomes on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` + `miri 0.1.0 (14210df0e2 2026-05-31)`:

1. **Deduplication probe (`a_valtree_canonicalization_and_symbol_dedup`):**
   - Native `-O2`, Miri Stacked Borrows, and Miri Tree Borrows all exit `0` printing:
     `ARR=true,false TAG=true,15,15 PAD=true,42,42 MODE=true,7,7 STR=true,6,6 SLICE=true,3,3 REF=true SZ=8,8`.
   - LLVM IR (`-O0` and `-O2`) emits **exactly 6** monomorphized target functions (`size_fn`, `use_tag`, `use_padded`, `use_mode`, `use_str`, `use_slice`), proving single-symbol `v0` deduplication for computed vs. literal arrays (`Kj4_`), computed vs. literal structs (`KVNt...TagS1ah5_1bb1_EE`), differently padded `Padded` instances (`KVNt...PaddedS4flagb1_3valm2a_EE`), enums (`KVNtNt...Mode7CheckedTh7_EE`), `&str` (`KRe616e6e65616c_`), and `&[u8]` (`KRAh1_h2_h3_E`). *(Basis: execution)*

2. **`min_const_generics` & `generic_const_exprs` matrix (`b_min_const_generics_vs_generic_const_exprs_and_syntactic_equality`):**
   - `min_const_generics_reject_param_arith` (`[u8; N + 1]`): `rc=1`, `cannot perform const operation using N`.
   - `repeat_expr_count_reject_param_arith` (`[0u8; N + 1]`): `rc=1`, `cannot perform const operation using N`.
   - `repeat_expr_count_accept_standalone_param` (`[0u8; N]`): `rc=0`.
   - `repeat_expr_count_legacy_assoc_const_76200` (`[0u8; H::<T>::LEN]`): `rc=0` with `#[warn(const_evaluatable_unchecked)]` `#76200` future-incompat warning.
   - `repeat_expr_count_depends_on_ty_param` (`[0u8; { let _: Option<T> = None; 4 }]`): `rc=1`, `E0308` + `constant expression depends on a generic parameter`.
   - `gce_sig_auto_clause_without_explicit_where` (`fn sig_auto<const N: usize>(arr: [u8; N + 1]) -> usize`): `rc=0`.
   - `gce_body_missing_const_evaluatable_bound` (`[0u8; N + 1]` in body): `rc=1`, `unconstrained generic constant` suggesting `where [(); N + 1]:`.
   - `gce_caller_missing_const_evaluatable_bound`: `rc=1`, `unconstrained generic constant`.
   - `gce_subtree_satisfies_bound` (`where [(); (N + 1) * 2]:` satisfying `[u8; N + 1]`): `rc=0`.
   - `gce_accept_with_where_bound`: `rc=0`, prints `GCE_LEN=4` natively and in Miri SB/TB; single LLVM IR symbol `_RINvCs...8b_gce_ok11gce_add_oneKj3_EB2_` (`Kj3_` for `N = 3`).
   - `gce_next_solver_globally_interaction` (`-Znext-solver=globally` on `1.98.0-nightly`): `rc=1`, `-Znext-solver=globally and generic_const_exprs are incompatible` + `E0275`.
   - `gce_syntactic_unification_n_plus_1_vs_1_plus_n`: `rc=1`, `E0308: expected N + 1, found 1 + N`. *(Basis: execution)*

3. **`ConstParamTy` & `StructuralPartialEq` soundness matrix (`c_adt_const_params_valtree_and_structural_eq`):**
   - Rejects `f32` (`mcgs` & `adt_const_params`, `E0741`), `&'static mut u8` (`E0741`), manual `PartialEq` (`E0277` on `StructuralPartialEq`), `union` (`cannot be derived for unions`), `#[non_exhaustive]` under `min_adt_const_params` (`rc=1`), and private struct fields under `min_adt_const_params` (`rc=1`).
   - Admits private fields (`positive_adt_private_field`, `rc=0`) and `#[non_exhaustive]` under `#![feature(adt_const_params)]` (`rc=0`).
   - `manual_structural_peq_unsoundness_witness` (`#![feature(adt_const_params, structural_match)]` with manual constant-true `PartialEq`): `rc=0`, prints `RUNTIME_EQ=true TYPEID_EQ=false` natively (`-O2`) and under Miri SB/TB, with distinct LLVM symbol suffixes `Th1_` vs. `Th2_` proving why unguarded manual `StructuralPartialEq` breaks type identity coherence. *(Basis: execution)*

### 3. Lean `4.34.1` Formalization & Kernel Environment Receipt

- Formalization source: [`support/ConstGenericsValTreeCanonicalizationAndStructuralEqSoundness.lean`](support/ConstGenericsValTreeCanonicalizationAndStructuralEqSoundness.lean) (`2,665` lines, `127,242` bytes, `prelude` + `Init.*` foundation aligned to `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`). *(Basis: derived)*
- MetaM audit receipt: [`support/lean_verification_receipt.json`](support/lean_verification_receipt.json) recording exact local constant census (`1,046` local constants, `294` kernel theorems, `633` defs/matchers/helpers, `16` inductives), `unsafe_rec_count = 0`, `unsafe_const_count = 0`, `opaque_or_axiom_const_count = 0`, `banned_axioms_count = 0`, and `all_axioms_used = ["propext"]`. *(Basis: derived)*

## Revalidation

Any downstream verifier can independently re-run all upstream checks, live `rustc` + `Miri` differential probes, and kernel-checked `Lean 4` proofs locally using the packaged artifacts:

### 1. Re-run Live `rustc` & `Miri` Differential Probes

```bash
python3 support/probe_const_generics_valtree_and_structural_eq.py --out support/probe_results.json
```

Expected checks:
- Probe crate `a_valtree_dedup` prints `ARR=true,false TAG=true,15,15 PAD=true,42,42 MODE=true,7,7 STR=true,6,6 SLICE=true,3,3 REF=true SZ=8,8` natively (`-O2`), under `cargo miri run`, and under `MIRIFLAGS="-Zmiri-tree-borrows" cargo miri run`, with exactly 6 matching deduplicated LLVM IR functions at `-O0` and `-O2`.
- All negative checks (`[u8; N + 1]` in MCG, `[0u8; N + 1]`, `[0u8; { let _: Option<T> = None; 4 }]`, unconstrained GCE bodies/callers, `N + 1` vs. `1 + N` `E0308`, `f32`, `&mut u8`, manual `PartialEq`, `union`, and `min_adt_const_params` private/`#[non_exhaustive]` structs) exit `1` with matching diagnostics, while `#76200` emits `#[warn(const_evaluatable_unchecked)]`.
- On nightlies where `-Znext-solver=globally` is already default (`1.102+` / HEAD), expect `warn_next_solver_and_gce` to emit `#160895` downgrade warning and exit `0` instead of the `1.98` hard error when `-Znext-solver=globally` is active.
- `manual_structural_peq_unsoundness_witness` outputs `RUNTIME_EQ=true TYPEID_EQ=false` natively and under Miri SB/TB.

### 2. Re-verify `Lean v4.34.1` Kernel Check & Purity Audit

```bash
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  "$HOME/.local/bin/anneal-lean-run" --mode file -- \
  "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
  -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/ConstGenericsValTreeCanonicalizationAndStructuralEqSoundness.lean
```

Expected result:
- Exits `0` with zero warnings and zero errors.
- MetaM `env.constants` inspection confirms `unsafe_rec_count = 0`, `unsafe_const_count = 0`, `opaque_or_axiom_const_count = 0`, `banned_axioms_count = 0` (`Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`), and `all_axioms_used = ["propext"]`.

### 3. Revalidate Package Schema & Corpus Indexing

```bash
python3 tools/reference.py catalog
python3 tools/reference.py check
```

Expected result:
- `reference.py catalog` regenerates `CATALOG.json` with `rustc-const-generics-valtree-canonicalization-and-structural-eq-soundness`.
- `reference.py check` exits `0` (`reference check passed`).
