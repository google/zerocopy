# `rustc` `ValTree` Canonicalization, `const_to_pat` `StructuralPartialEq` Active-Variant Lowering, `VALTREE_MAX_NODES` vs. DAG Memoization, and `v0` Const-Generic Symbol Mangling

## Summary

In `rustc`, type-level constants (const generic arguments and constant patterns) do not retain CTFE memory allocations directly; they are quotiented by `const_to_valtree_inner` (`compiler/rustc_const_eval/src/const_eval/valtrees.rs:83-219`) into an untyped, arena-interned tree `ty::ValTreeKind::{Leaf(ScalarInt), Branch(Consts)}` (`compiler/rustc_type_ir/src/const_kind.rs:238-252`) paired externally with a `Ty` in `ty::Value { ty, valtree }` (`compiler/rustc_middle/src/ty/consts/valtree.rs:102-105`). Primary-source inspection across three pinned `rust-lang/rust` revisions (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), live `rustc` + `Miri` execution, and a zero-`sorry`, zero-`Classical.choice` Lean `v4.34.1` formalization establish six load-bearing invariants and cross-version divergences for compiler verification and Anneal's trusted boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):

1. **Field-Only Quotient & Padding Uninitialization:** `branches` projects only declared fields via `project_field` (`valtrees.rs:48-52`) and `ty::Ref` dereferences transparently (`valtrees.rs:155-158`), completely erasing struct/enum padding bytes and reference allocation identities (`AllocId`s). Distinct padding bit-patterns (`[1, 0, 0, 0, 2, 0, 0, 0]` vs. `[1, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0]`) unify to identical `ValTree`s, `TypeId`s (`SAME_TID=true`), and `v0` mangled symbols (`mangle_pad_symbol_count=1`, with `KBK_` backref deduplication in two-argument generic instantiations). Reconstruction via `valtree_into_mplace` allocates fresh uninitialized stack memory (`create_valtree_place`) and writes only logical fields (`valtrees.rs:258-265, 411-487`); Miri reports Undefined Behavior (`at [1], encountered uninitialized memory`) on reading padding bytes from both direct copies and `ValTree`-reconstructed const parameters, even when the source constant was initialized from `[1u8, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0]` via `transmute`.
2. **Asymmetric Type Admission Across `ValTree`, `const_to_pat`, and `ConstParamTy`:** `const_to_valtree_inner` accepts thin provenance-free raw pointers (`val.try_to_scalar_int()` succeeds, `valtrees.rs:141-147`) and `ty::FnDef` ZSTs (`valtrees.rs:109-112`), while rejecting provenance-bearing raw pointers, wide `BackendRepr::ScalarPair` raw pointers even without provenance (`valtrees.rs:138-139`), `ty::FnPtr` (`valtrees.rs:153`), and `union` ADTs (`valtrees.rs:174-175`). `const_to_pat` accepts non-NaN floats (rejecting all NaNs including custom payload NaNs per RFC 3535 at `const_to_pat.rs:451-466`) and lowers them via `TestKind::ScalarEq` (`rustc_mir_build/src/builder/matches/test.rs:49-51, 183-236`) to MIR `BinOp::Eq` (`-0.0` matches `+0.0` and vice versa), whereas `ty::FnDef` is rejected by `const_to_pat` (`InvalidPattern`) and `f64` is forbidden as a `ConstParamTy`.
3. **Active-Variant-Only `StructuralPartialEq` Recursion & Non-`const` `PartialEq`:** `ConstToPat::valtree_to_pat` checks `ty.is_structural_eq_shallow(tcx)` on ADTs (`const_to_pat.rs:74-76, 253`) and, for enums, recurses exclusively into the active variant's fields (`const_to_pat.rs:379-389`). Consequently, `const C_EMPTY: Wrap<Manual> = Wrap::Empty` compiles and matches even when `Manual` has a manual non-structural `impl PartialEq` (because outer `Wrap<Manual>: PartialEq` passes `alias_to_pat` line 216 and `Empty` has no payload), while `Wrap<NoPeq>::Empty` fails the outer `PartialEq` check and `Wrap<Manual>::Full(Manual(1))` fails `TypeNotStructural`. Inside `const fn`, `type_has_partial_eq_impl` (`const_to_pat.rs:638-650`) deliberately accepts non-`const` `PartialEq` impls for backwards compatibility because pattern lowering compares primitives directly without invoking `PartialEq::eq`.
4. **`VALTREE_MAX_NODES = 100_000` Boundary & Cross-Version DAG Memoization Bypass:** `const_to_valtree_inner` checks `if *num_nodes >= VALTREE_MAX_NODES` *before* incrementing (`valtrees.rs:102-116`), admitting `[u8; 100_000]` (`CG_OK=100000`) and rejecting `[u8; 100_001]` (`NodesOverflow`). Commit `c61c52f51de4d41929a9a20f5921afa73e5718cf` (`2026-07-03`) added `visited: FxHashSet<MPlaceTy>` (converting pre-fix `SIGSEGV` crashes on self-referential static cycles like `static X: Thing = Thing(&X); const Y: &Thing = &X` into `ValTreeCreationError::CyclicConst`) together with `settled: FxHashMap<MPlaceTy, EvalToValTreeResult>` (`valtrees.rs:94-96, 217`). Because `settled` returns cached results without charging `num_nodes`, `rustc 1.102.0-nightly` admits a depth-18 binary sharing DAG with `2^18 = 262,144` logical leaf paths (`DAG_CG_2POW18_DEPTH=18`), bypassing `VALTREE_MAX_NODES = 100_000`, whereas pre-fix `rustc 1.98.0-nightly` rejected that DAG with `NodesOverflow` and crashed with `SIGSEGV` on the static cycle.
5. **Array-Pattern `SIGSEGV` Regression Below `VALTREE_MAX_NODES`:** `const_to_pat` expands `[u8; N]` into `PatKind::Array` with `N` scalar subpatterns (`const_to_pat.rs:412-420`), driving `O(N)` recursion in `rustc_pattern_analysis` and MIR match construction. Commit `464199092963f32f12411516db535ca39ba2cb0e` (`2026-08-09`, `Remove ensure_sufficient_stack`) removed dynamic stack growth across 46 files including `valtrees.rs`, `rustc_mir_build/src/builder/matches/mod.rs`, and `rustc_pattern_analysis/src/usefulness.rs`. On `rustc 1.102.0-nightly`, `matches!(x, BIG)` on `[u8; N]` hits immediate `SIGSEGV` (`rc = -11`) across `N = 20_000, 50_000, 99_999` below the `100_000` node cap, whereas `rustc 1.98.0-nightly` (retaining `ensure_sufficient_stack`) compiles `N = 20_000` cleanly in `10.96 s` before hitting timeout (`N = 50_000`) and OOM (`N = 99_999, 100_000`). Both toolchains fail cleanly at `N = 100_001` via `NodesOverflow` before pattern lowering.
6. **`v0` Mangling Injectivity Over Canonical Trees & Anneal Trusted-Boundary Contract:** `V0SymbolMangler::print_const` (`compiler/rustc_symbol_mangling/src/v0.rs:771-947`) is injective over canonical `ValTree`s for a fixed `ConstParamTy` type (mechanized via a constructive prefix-free parser `mangleValTree_injective`) while collapsing padding- and address-distinct allocations via `ValTree` interning and `self.consts` `KB` backrefs. `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` currently restricts `MirAst.ConstLit` (`trusted/lean/Trusted/MirAst.lean:504-506`) to `.scalar (BitVec 128)` and `.zeroSized` and fails closed on `ConstValue::{Slice, Indirect}`, floats, raw pointers, and aggregate constants; any future expansion must preserve uninitialized padding masks, treat `ValTree`-quotiented monomorphization identities as padding/address-blind, distinguish MIR `BinOp::Eq` float lowering from `SwitchInt`, and bound DAG-memoized const expansion.

## Applicability

This report characterizes the interaction among five durable upstream artifacts recorded in `REPORT.json`:

| Subject | Repository & Immutable Revision | Role in This Report |
| :--- | :--- | :--- |
| **`rustc` primary source (HEAD)** | `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`) | Primary line-by-line source audit of `valtrees.rs`, `valtree.rs`, `const_kind.rs`, `const_to_pat.rs`, `misc.rs`, `builtin.rs`, `util.rs`, `matches/test.rs`, `queries.rs`, `v0.rs`, and `library/core/src/marker.rs`. |
| **`rustc 1.102.0-nightly`** | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`, LLVM `23.1.5`) | Post-`c61c52f51de` / post-`464199092963` execution baseline on `x86_64-unknown-linux-gnu` (`support/rustc_1_102_0_nightly_baseline_results.json`); source-diffed against `HEAD` (identical on all audited logic except unreachable `ty::View(..) => unimplemented!()` arms added in `94add9677e2de57a2e414350bedcd13f07426a5e`). |
| **`rustc 1.98.0-nightly` + `Miri`** | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`, LLVM `22.1.6`, `miri 0.1.0`) | Pre-`c61c52f51de` / pre-`464199092963` live execution and Miri probe environment on `x86_64-unknown-linux-gnu` (`support/probe_valtree_and_const_to_pat_results.json`), providing direct A/B causal confirmation of both upstream transitions. |
| **Anneal TCB & MIR semantics** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Inspected consumer architecture (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/rustc-capture/src/driver.rs`, pinned to `1.98.0-nightly (f8a08b688 2026-05-30)`). |
| **Lean 4 kernel verifier** | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Independent kernel checker verifying the standalone formal model in `support/ValTreeCanonicalizationAndConstPatSoundness.lean`. |

### Exact Version-Split Matrix (`1.98.0-nightly` vs. `1.102.0-nightly` / `HEAD`)

Two upstream `rust-lang/rust` commits between `2026-05-31` and `2026-11-11` divide observed behaviors into shared invariants vs. revision-specific regimes:

| Behavior / Mechanism | `1.98.0-nightly` (`14210df0e`) | `1.102.0-nightly` (`3ef0c22cd`) & `HEAD` (`342d74463`) | Causal Commit |
| :--- | :--- | :--- | :--- |
| Padding & reference-identity erasure in `ValTree`, `TypeId`, and `v0` mangling | Identical (`SAME_TID=true`, `REF_SAME_TID=true`, `KBK_` backref) | Identical | Shared |
| Miri uninitialized padding UB on direct & `ValTree`-reconstructed `Padded` | Identical (UB at byte `[1]` across all 4 variants) | Identical (UB at byte `[1]`) | Shared |
| `VALTREE_MAX_NODES = 100_000` boundary (`[u8; 100_000]` ok, `[u8; 100_001]` error) | Identical (`CG_OK=100000`, `100001` `NodesOverflow`) | Identical (`CG_OK=99999`, `100001` `NodesOverflow`) | Shared |
| Active-variant `StructuralPartialEq`, non-`const` `PartialEq` in `const fn`, RFC 3535 float/NaN, ptr/union, `min_adt_const_params` vs. `adt_const_params` gates | Identical across all probes | Identical across all probes | Shared |
| Self-referential static cycle (`static X: Thing = Thing(&X); const Y: &Thing = &X`) in pattern | **`SIGSEGV` stack overflow (`rc = -11`, period-8 cycle)** | Clean `ValTreeCreationError::CyclicConst` error (`constant Y cannot be used as pattern`) | `c61c52f51de4d41929a9a20f5921afa73e5718cf` (`2026-07-03`) |
| Shared binary DAG depth `18` (`2^18 = 262,144` leaves) in `DagTag::<{ &N18 }>` | **Rejected: `NodesOverflow` (`rc = 1`)** (no `settled` cache) | **Accepted (`DAG_CG_2POW18_DEPTH=18`)** (`settled` memoizes without charging `num_nodes`) | `c61c52f51de4d41929a9a20f5921afa73e5718cf` (`2026-07-03`) |
| `matches!(x, BIG)` on `[u8; N]` (`N = 20_000..99_999`) | `N = 20_000` compiles (`10.96 s`); `50_000` times out (`90 s`); `99_999`/`100_000` OOM (`rc = -9`) | **`SIGSEGV` (`rc = -11`) at `N = 20_000, 50_000, 99_999`** (no `ensure_sufficient_stack`) | `464199092963f32f12411516db535ca39ba2cb0e` (`2026-08-09`) |
| `TyKind::View(..)` exhaustiveness arms in `valtrees.rs` / `v0.rs` | Absent | Present (`unimplemented!()` stub, unreachable without view-type lowering) | `94add9677e2de57a2e414350bedcd13f07426a5e` (`2026-11-12`) |

### Relevant Flags, Editions, and Invocation Modes

- All Rust probes execute in Rust 2024 edition (`--edition=2024`) on `x86_64-unknown-linux-gnu`.
- Nightly feature gates exercised explicitly: `#![feature(adt_const_params)]`, `#![feature(min_adt_const_params)]`, `#![feature(unsized_const_params)]`, `#![feature(type_alias_impl_trait)]`.
- Symbol mangling probes pass `-C symbol-mangling-version=v0 -C opt-level=0 --emit=obj` and inspect exported defined symbols via `llvm-nm --defined-only -g`.
- Miri probes invoke `cargo miri run --quiet --offline` with `MIRIFLAGS=-Zmiri-disable-isolation`.

## Findings

### 1. `ValTree` Data Model and `const_to_valtree_inner` Dispatch Semantics

Basis: source (`rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`)

A `ValTree<'tcx>` is an interned pointer to `ty::ValTreeKind<TyCtxt<'tcx>>` (`compiler/rustc_middle/src/ty/consts/valtree.rs:33`, `compiler/rustc_type_ir/src/const_kind.rs:238-252`):

```rust
pub enum ValTreeKind<I: Interner> {
    Leaf(I::ScalarInt),
    Branch(I::Consts),
}

pub struct Value<'tcx> {
    pub ty: Ty<'tcx>,
    pub valtree: ValTree<'tcx>,
}
```

Crucially, `ValTreeKind` carries **no types, no field names, no byte offsets, no padding, no slice metadata (`MemPlaceMeta`), and no allocation provenance (`AllocId`)**. All type/layout context is supplied externally by `ty::Value { ty, valtree }` (or by each branch's child `ty::Const::new_value(tcx, valtree, field_ty)`). Zero-sized values (`ValTree::zst(tcx)`) are canonically represented as `ValTreeKind::Branch(&[])` (`valtree.rs:36-43`).

When `eval_to_valtree` (`compiler/rustc_const_eval/src/const_eval/valtrees.rs:268-292`) converts a CTFE constant `GlobalId` into a type-level constant, it evaluates `tcx.eval_to_allocation_raw`, constructs a read-only `CompileTimeInterpCx` with `CanAccessMutGlobal::No` and `CheckAlignment::No` (`eval_queries.rs:222-235`), wraps the allocation in an `MPlaceTy`, and invokes `const_to_valtree_inner` (`valtrees.rs:83-219`):

| `TyKind` Arm (`valtrees.rs:108-214`) | Action in `const_to_valtree_inner` | `num_nodes` Charge | Information Erased / Preserved |
| :--- | :--- | :--- | :--- |
| `ty::FnDef(..)` (`L109-112`) | Returns `Ok(ValTree::zst(tcx))` | `+1` | Zero-sized item identity lives only in `Ty`, not `ValTree`. |
| `ty::Bool \| Int \| Uint \| Float \| Char` (`L113-119`) | `ecx.read_immediate(place)?.to_scalar_int()` -> `ValTree::from_scalar_int` | `+1` | Preserves exact `ScalarInt` bits (including `-0.0` vs. `+0.0` sign bit and NaN payload bits inside the `ValTree` leaf; NaN filtering happens later in `const_to_pat`). |
| `ty::Pat(base, ..)` (`L121-128`) | Replaces `place.layout` with `ecx.layout_of(*base)` and recurses | Delegated | Pattern-type refinement is invisible in `ValTree`. |
| `ty::RawPtr(_, _)` (`L130-149`) | Reads immediate; if `BackendRepr::ScalarPair { .. }` -> `Err(NonSupportedType(ty))`; else `val.to_scalar().try_to_scalar_int()` -> `Ok(Leaf)` or `Err(NonSupportedType(ty))` | **`+0`** (notably does *not* increment `*num_nodes`!) | Rejects all wide raw pointers (even integer-derived ones) and all provenance-carrying thin pointers; accepts thin provenance-free integer-in-disguise pointers. |
| `ty::FnPtr(..)` (`L151-153`) | `Err(NonSupportedType(ty))` | `0` | Rejected because compile-time `ty::Instance` equality need not agree with runtime code-pointer identity (ICF / cross-DSO duplication). |
| `ty::Ref(_, _, _)` (`L155-158`) | `ecx.deref_pointer(place)` and recurses directly | Delegated | **Transparently erases reference indirection, pointer address, and `AllocId`**; `&T` and `T` share the identical `ValTree`. |
| `ty::Str \| ty::Slice(_) \| ty::Array(_, _)` (`L160-162`) | `slice_branches` (`L63-80`): projects elements `0..len` via `project_index` | Sum of elements (`0` for empty array/slice!) | Erases array/slice backing `AllocId`; `MemPlaceMeta` slice length is recovered from `branches.len()` during reconstruction. |
| `ty::Tuple(elem_tys)` (`L169-171`) | `branches(..., elem_tys.len(), None, ...)` (`L21-60`) | Sum of fields (`+1` if `branches.len() == 0`) | Projects only fields `0..field_count` via `project_field`; **erases all inter-field and trailing padding**. |
| `ty::Adt(def, _)` (`L173-190`) | `def.is_union()` -> `Err(NonSupportedType(ty))`; empty variants -> `bug!`; else `read_discriminant` + `branches` (for enums, `project_downcast` + prepend `variant.as_u32()` as `u32` leaf at index `0`) | Sum of fields (`+1` if `branches.len() == 0`) | **Erases padding bytes, raw niche/tag encoding layout (normalizing to logical `VariantIdx` `u32`), and inactive variants**. |
| `ty::Dynamic \| Alias \| Closure \| Never \| Coroutine* \| Foreign \| Param \| Bound \| Placeholder \| Infer \| UnsafeBinder \| Error` (`L167, L193-210`) | `Err(NonSupportedType(ty))` | `0` | Fail-closed rejection. |
| `ty::View(..)` (`L213`, post-`94add9677e`) | `unimplemented!()` | N/A | Placeholder arm for future view types. |

A subtle accounting detail visible directly in `valtrees.rs:40-57, 130-149`: `branches` increments `*num_nodes += 1` only when `branches.len() == 0` (to account for ZSTs), `slice_branches` never increments `*num_nodes` on empty slices/arrays, `branches` does not increment `*num_nodes` for the prepended enum `VariantIdx` leaf (`L40-46`), and `ty::RawPtr` returns `Ok(ValTree::from_scalar_int(...))` without incrementing `*num_nodes` (`L145`).

### 2. Reconstruction (`valtree_to_const_value` / `valtree_into_mplace`), Padding Uninitialization, and Reference-Identity Erasure

Basis: source (`valtrees.rs:221-487`, `eval_queries.rs:258-338`) + execution (`rustc 1.98.0-nightly` + `Miri`, `rustc 1.102.0-nightly`) + derived (Lean `v4.34.1` Theorems 1–2 & `ce1`)

When MIR or codegen needs a concrete `mir::ConstValue` back from a type-level `ty::Value { ty, valtree }`, `valtree_to_const_value` (`valtrees.rs:298-392`) executes four distinct paths:

1. **ZST & Trivial Scalars (`L310-316, 333-336`):** `FnDef` and any `layout.is_zst()` aggregate return `ConstValue::ZeroSized`; `Bool | Int | Uint | Float | Char | RawPtr` return `ConstValue::Scalar(Scalar::Int(cv.to_leaf()))`.
2. **Scalar-Repr Struct/Tuple Fast Path (`L337-353`):** If `layout.backend_repr.is_scalar()` on a tuple or struct, `valtree_to_const_value` skips allocating an `MPlace`, finds the unique non-ZST field, and recurses on that field's `ValTree`.
3. **References (`L321-330, 395-408`):** `valtree_to_ref` reconstructs `MemPlaceMeta` via `reconstruct_place_meta` (`L223-255`, walking `tcx.struct_tail_raw` down the last branch to recover `Slice`/`Str` element count), allocates a fresh `MemoryKind::Stack` place via `create_valtree_place`, fills it with `valtree_into_mplace`, interns it via `intern_const_alloc_recursive(..., InternKind::Constant, ...)`, and converts the resulting `Immediate` via `op_to_const` (yielding `ConstValue::Slice { alloc_id, meta }` for wide slice/`&str` refs at `eval_queries.rs:312-334` or `ConstValue::Scalar` for thin refs). Because every reconstructed reference gets a newly interned allocation, original pointer identity is permanently severed.
4. **General Aggregates (`L355-366, 411-487`):** `create_valtree_place` allocates fresh uninitialized memory (`ecx.allocate_dyn(layout, MemoryKind::Stack, meta)`). `valtree_into_mplace` writes *only* each field (`project_field` / `project_index`) and—for enums—calls `ecx.write_discriminant(variant_idx, place)` (`L477-480`). **No padding byte is ever written**, so every padding byte in a `ValTree`-reconstructed `ConstValue::Indirect` is guaranteed uninitialized in CTFE/Miri memory.

Empirical confirmation on `rustc 1.98.0-nightly (14210df0e)` + `Miri` (`support/probe_valtree_and_const_to_pat_results.json`) and `rustc 1.102.0-nightly (3ef0c22cd)` (`support/rustc_1_102_0_nightly_baseline_results.json`):

- **Padding-bit unification (`a1_pad_unify`):** For `#[repr(C)] #[derive(PartialEq, Eq, ConstParamTy)] struct Padded { a: u8, b: u32 }` (3 internal padding bytes at offsets `1..4`), defining `PAD_ZERO = transmute([1u8, 0, 0, 0, 2, 0, 0, 0])` and `PAD_DEAD = transmute([1u8, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0])` yields `TypeId::of::<Tag<PAD_ZERO>>() == TypeId::of::<Tag<PAD_DEAD>>()` -> `SAME_TID=true V0=102 V1=102` on both nightlies.
- **Miri padding uninitialization across all four copy/round-trip paths:** Running `cargo miri run` on `transmute::<Padded, [u8; 8]>(...)` triggers the identical Miri UB error `error: Undefined Behavior: constructing invalid value of type [u8; 8]: at [1], encountered uninitialized memory, but expected an integer` in all four configurations:
  1. Direct copy of literal `const P: Padded = Padded { a: 1, b: 2 }` (`rc = 1`, `655.92 ms`);
  2. Direct copy of transmuted `const PAD_DEAD: Padded = unsafe { transmute([1u8, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0]) }` (`rc = 1`, `498.23 ms`)—confirming that typed MIR copy semantics already drop padding bytes in Miri even before `ValTree` conversion;
  3. `ValTree`-reconstructed const generic `inspect::<P_LIT>()` (`rc = 1`, `496.71 ms`);
  4. `ValTree`-reconstructed const generic `inspect::<PAD_DEAD>()` (`rc = 1`, `305.05 ms`), where Miri's backtrace prints the canonicalized monomorphization `0: inspect::<Padded { a: 1, b: 2 }>`.
- **Reference and `&str` identity erasure (`a2_ref_erase`):** Two distinct constant bindings `const A: u8 = 7; const B: u8 = 7; const R1: &u8 = &A; const R2: &u8 = &B` unify to the same `TypeId` (`REF_SAME_TID=true`), and a string literal `"hi"` unifies with `core::str::from_utf8_unchecked(&S2_BYTES)` from a separate byte array (`STR_SAME_TID=true`).

### 3. `VALTREE_MAX_NODES = 100_000`, `visited` Cycle Detection vs. `settled` DAG Memoization, and the `[u8; N]` Pattern `SIGSEGV`

Basis: source (`valtrees.rs:83-119, 216-218`, `mod.rs:28-29`, `queries.rs:206-256`, `const_to_pat.rs:412-420`, commits `c61c52f51de` & `464199092963`) + execution (`1.98.0-nightly` vs. `1.102.0-nightly`) + derived (Lean `v4.34.1` `settledNodeCount_eq` & `ce3`)

#### 3.1 Exact `VALTREE_MAX_NODES` Arithmetic Boundary

`compiler/rustc_const_eval/src/const_eval/mod.rs:29` defines:

```rust
const VALTREE_MAX_NODES: usize = 100000;
```

In `const_to_valtree_inner` (`valtrees.rs:102-118`), the overflow check executes *strictly before* incrementing `*num_nodes`:

```rust
if *num_nodes >= VALTREE_MAX_NODES {
    return Err(ValTreeCreationError::NodesOverflow);
}
```

For `[u8; N]`, the outer array enters `slice_branches` with `*num_nodes == 0` (charging `0` for the branch node itself). Element `i` (`0 <= i < N`) checks `i >= 100_000` and increments `*num_nodes` to `i + 1`. Consequently:
- **`N = 99_999`:** passes (`CG_OK=99999` in `808.13 ms` on `1.98.0-nightly`, `rc = 0` on `1.102.0-nightly`).
- **`N = 100_000`:** passes (`CG_OK=100000` in `163.90 ms` on `1.98.0-nightly`; final `*num_nodes == 100_000`, with no subsequent recursive call to trip `>= 100_000`).
- **`N = 100_001`:** fails on element `100_000` with `ValTreeCreationError::NodesOverflow` -> `diagnostics::MaxNumNodesInValtree` (`queries.rs:231-237`), emitting `error: maximum number of nodes exceeded in constant ...` (`rc = 1` in `83.69 ms` on `1.98.0-nightly` and `rc = 1` on `1.102.0-nightly`).

#### 3.2 `visited` Cycle Detection vs. `settled` DAG Memoization Bypass (`c61c52f51de`)

Prior to `2026-07-03` (including `rustc 1.98.0-nightly@14210df0e`), `const_to_valtree_inner` tracked neither active call-stack places nor completed places. That created a live soundness/termination bug on self-referential `static` cycles:

```rust
#[derive(PartialEq)]
struct Thing(&'static Thing);
static X: Thing = Thing(&X);
const Y: &Thing = &X;
fn main() { if let Y = Y {} }
```

Unlike a self-referential `const` item (`const C: Cyc = Cyc(Some(&C));`), which fails early in query-cycle detection with `error[E0391]: cycle detected when simplifying constant for the type system 'C'` on *both* `1.98.0-nightly` and `1.102.0-nightly`, the `static X` reference cycle succeeds in `eval_to_allocation_raw` (producing a cyclic CTFE allocation graph) and enters `const_to_valtree_inner`. On `rustc 1.98.0-nightly@14210df0e`, `const_to_valtree_inner` recurses infinitely around `&X -> Thing -> &X` without incrementing `num_nodes` (because neither `ty::Ref` nor non-empty `branches` charges `num_nodes`!), crashing `rustc` in `110.85 ms` with **`SIGSEGV` (`rc = -11`, `### cycle encountered after 7 frames with period 8`)**.

Commit `c61c52f51de4d41929a9a20f5921afa73e5718cf` (`2026-07-03`, `detect cycles during valtree construction for self-referential consts`) added two maps keyed by `MPlaceTy<'tcx>` (`valtrees.rs:94-106, 216-218`):

```rust
if let Some(&result) = settled.get(place) {
    return result;
}
if visited.contains(place) {
    return Err(ValTreeCreationError::CyclicConst);
}
if *num_nodes >= VALTREE_MAX_NODES {
    return Err(ValTreeCreationError::NodesOverflow);
}
visited.insert(place.clone());
// ... compute `result` ...
visited.remove(place);
settled.insert(place.clone(), result);
```

This fixes cyclic static references cleanly via `ValTreeCreationError::CyclicConst` -> `diagnostics::CyclicConstInValtree` (`queries.rs:245-251`), **but introduces an exponential bypass of `VALTREE_MAX_NODES = 100_000` for acyclic sharing DAGs**:
- Consider the binary DAG `const N0: Node = Node::Leaf(1); const N{k}: Node = Node::Pair(&N{k-1}, &N{k-1});` for `k = 1..18` (`enum Node { Leaf(u8), Pair(&'static Node, &'static Node) }`).
- The logical unfolded tree has `2^18 = 262,144` leaves (`> 100_000`) and `2^19 - 1 = 524,287` logical nodes.
- Because `&N_{k-1}` resolves to the same `MPlaceTy` on both the left and right fields of `N_k`, the second lookup hits `settled.get(place)` at `valtrees.rs:94-96` and returns the interned `ValTree` pointer **without incrementing `*num_nodes`**. Across all 19 levels, `*num_nodes` increments only once on the single leaf `N0` (`Leaf(1)`), charging `1` (or at most `d + 1 = 19` even if internal nodes were charged), far below `100_000`.
- **Empirical A/B confirmation:**
  - `rustc 1.98.0-nightly@14210df0e` (pre-`c61c52f51de`): `DagTag::<{ &N18 }>` **fails** with `error: maximum number of nodes exceeded in constant main::{constant#0}` (`rc = 1`, `600.42 ms`).
  - `rustc 1.102.0-nightly@3ef0c22cd` (post-`c61c52f51de`): `DagTag::<{ &N18 }>` **succeeds** and executes (`rc = 0`, stdout `DAG_CG_2POW18_DEPTH=18`).
- Meanwhile, using an inline `const { &N10 }` block directly as a pattern is rejected syntactically (`error: const blocks cannot be used as patterns`) on both toolchains, whereas binding a named `const ROOT10: &'static Node = &N10` compiles and matches (`DAG_PAT_NAMED_D10=true`, `432.78 ms` on `1.98.0-nightly`).

#### 3.3 Why `matches!(x, BIG)` on `[u8; 20_000..99_999]` Hits Live `SIGSEGV` Stack Overflow Below `VALTREE_MAX_NODES`

Although `ArrTag::<BIG>` compiles in `< 1 s` at `N = 99_999` and `N = 100_000`, `matches!(x, BIG)` on `const BIG: [u8; N] = [0u8; N]` lowers `ValTree` through `const_to_pat.rs:412-420` into:

```rust
ty::Array(_, _) => PatKind::Array {
    prefix: valtree
        .to_branch()
        .iter()
        .map(|val| *self.valtree_to_pat(val.to_value()))
        .collect(),
    slice: None,
    suffix: Box::new([]),
},
```

This creates a flat THIR pattern with `N` scalar subpatterns (`[0, 0, ..., 0]`). During exhaustiveness checking (`compiler/rustc_pattern_analysis/src/usefulness.rs`) and MIR match-tree lowering (`compiler/rustc_mir_build/src/builder/matches/mod.rs`), `rustc` specializes the match matrix column-by-column recursively across all `N` array elements (`O(N)` call-stack depth!).

Commit `464199092963f32f12411516db535ca39ba2cb0e` (`2026-08-09`, `Remove ensure_sufficient_stack`) removed `rustc_data_structures::stack::ensure_sufficient_stack` across 46 compiler files, explicitly deleting the dynamic stack-growth guards at `rustc_mir_build/src/builder/matches/mod.rs:1767`, `rustc_pattern_analysis/src/usefulness.rs:714, 725, 1755`, and `rustc_const_eval/src/const_eval/valtrees.rs:124`.

Empirical sweep across `N = 1_000..100_001` directly contrasts the pre- and post-`464199092963` regimes:

| Array Length `N` | `1.98.0-nightly` (`14210df0e`, with `ensure_sufficient_stack`) | `1.102.0-nightly` (`3ef0c22cd`, without `ensure_sufficient_stack`) |
| ---: | :--- | :--- |
| `1,000` | `rc = 0` (`178.52 ms`) | `rc = 0` |
| `4,000` | `rc = 0` (`589.45 ms`) | `rc = 0` |
| `10,000` | `rc = 0` (`4,108.57 ms`) | `rc = 0` |
| `15,000` | `rc = 0` (`6,520.14 ms`) | not in baseline sweep |
| `20,000` | `rc = 0` (`10,960.06 ms`, stacker grows stack) | **`rc = -11` (`SIGSEGV` stack overflow)** |
| `50,000` | `TIMEOUT` (`> 90 s`, heavy matrix specialization) | **`rc = -11` (`SIGSEGV` stack overflow)** |
| `99,999` | **`rc = -9` (OOM killer, `18.9 s`)** | **`rc = -11` (`SIGSEGV` stack overflow)** |
| `100,000` | **`rc = -9` (OOM killer, `15.8 s`)** | not in baseline sweep |
| `100,001` | `rc = 1` (`1,472.50 ms`, `maximum number of nodes exceeded`) | `rc = 1` (`maximum number of nodes exceeded`) |

Thus `VALTREE_MAX_NODES = 100_000` fails to protect `rustc` from compiler crashes on array patterns in *either* regime: post-`464199092963` overflows the OS thread stack into `SIGSEGV` starting at `N = 20_000`, while pre-`464199092963` exhausts CPU/memory (`TIMEOUT` / `SIGKILL`) by `N = 50_000..99_999`.

### 4. `const_to_pat`, Active-Variant `StructuralPartialEq`, Floats, Pointers, Unions, and `ConstParamTy` Gates

Basis: source (`const_to_pat.rs:42-698`, `util.rs:1465-1507`, `misc.rs:92-201`, `builtin.rs:170-245`, `matches/test.rs:30-236`, `library/core/src/marker.rs:255-273, 1099-1143`) + execution (`1.98.0-nightly`, `1.102.0-nightly`) + derived (Lean `v4.34.1` Theorems 3–4 & `ce2`)

#### 4.1 Pipeline Order and Active-Variant-Only Structural Recursion

`PatCtxt::const_to_pat` (`const_to_pat.rs:42-56`) dispatches `ty::ConstKind::Alias` to `alias_to_pat` (`L100-227`) and `ty::ConstKind::Value` directly to `valtree_to_pat` (`L244-488`). In `alias_to_pat`:
1. Unless `gca_const_items` or `alias_const.kind.is_direct_const(tcx)` is set (which routes through `try_normalize_erasing_regions`, `L142-157`), `rustc` calls `tcx.const_eval_resolve_for_typeck(self.typing_env, alias_const, self.span)` (`L161-204`). Any `Ok(Err(bad_ty))` from `ValTreeCreationError::NonSupportedType(bad_ty)` is mapped to `UnionPattern` (if union, `L189-192`), `PointerPattern` (if `FnPtr | RawPtr`, `L193-195`), or `InvalidPattern` (`L196-200`).
2. `valtree_to_pat(const_value)` recursively translates the `ValTree` into a THIR `Pat` (`L212`).
3. Only if `!thir_pat.references_error()` does `alias_to_pat` execute the outer `type_has_partial_eq_impl(self.tcx, self.typing_env, ty).has_impl` check (`L214-221`).

Inside `valtree_to_pat`, the structural-match gate is enforced **shallowly per visited ADT node** (`L74-76, 253`):

```rust
fn type_marked_structural(&self, ty: Ty<'tcx>) -> bool {
    ty.is_structural_eq_shallow(self.tcx)
}
// ...
ty::Adt(adt_def, _) if !self.type_marked_structural(ty) => { /* emit TypeNotStructural or TypeNotPartialEq */ }
ty::Adt(adt_def, args) if adt_def.is_enum() => {
    let (&variant_index, fields) = valtree.to_branch().split_first().unwrap();
    let variant_index = VariantIdx::from_u32(variant_index.to_leaf().to_u32());
    PatKind::Variant {
        adt_def: *adt_def,
        args: *args,
        variant_index,
        subpatterns: self.lower_field_values_to_fieldpats(fields.iter().map(|ct| ct.to_value())),
    }
}
```

And `Ty::is_structural_eq_shallow` (`compiler/rustc_middle/src/ty/util.rs:1465-1507`) returns `tcx.has_structural_eq_impl(self)` for `ty::Adt` (without inspecting type parameters or field types!), `true` for `Bool | Char | Int | Uint | Str | Never | Pat | Ref | Array | Slice | Tuple | RawPtr | FnPtr`, and `false` for `Float | FnDef | Closure | Dynamic | Coroutine | Alias | Param | ...`.

This produces a sharp **three-way empirical behavior** on `#[derive(PartialEq)] enum Wrap<T> { Empty, Full(T) }` (where `#[derive(PartialEq)]` generates an unconditional `impl<T> StructuralPartialEq for Wrap<T>` and a conditional `impl<T: PartialEq> PartialEq for Wrap<T>`):

| Probe | Outer `Wrap<T>: StructuralPartialEq`? | Outer `Wrap<T>: PartialEq` (`L216`)? | Active Variant Visited in `valtree_to_pat` | Observed Result (`1.98` & `1.102`) |
| :--- | :--- | :--- | :--- | :--- |
| `const C_EMPTY: Wrap<Manual> = Wrap::Empty;` (`Manual` has manual `impl PartialEq` returning `false`) | Yes | Yes | `Wrap::Empty` (`0` fields; `Manual` never visited) | **ACCEPTED (`rc = 0`, `ACTIVE_VARIANT_EMPTY_MATCHES=true EQ=true`)** |
| `const C_EMPTY: Wrap<NoPeq> = Wrap::Empty;` (`NoPeq` has *no* `PartialEq` impl) | Yes | **No** | `Wrap::Empty` (`0` fields), then fails `L216` | **REJECTED (`rc = 1`, `constant of non-structural type 'Wrap<NoPeq>' in a pattern`)** |
| `const C_FULL: Wrap<Manual> = Wrap::Full(Manual(1));` | Yes | Yes | `Wrap::Full` -> recurses into `Manual` -> `!is_structural_eq_shallow(Manual)` | **REJECTED (`rc = 1`, `constant of non-structural type 'Manual' in a pattern`)** |
| `const M: Manual = Manual(5);` | **No** | Yes | `Manual` fails `L253` directly | **REJECTED (`rc = 1`, `TypeNotStructural`)** |

#### 4.2 Non-`const` `PartialEq` Inside `const fn` Pattern Matching

In `type_has_partial_eq_impl` (`const_to_pat.rs:638-650`), `rustc` explicitly checks only `TraitRef::new(tcx, partial_eq_trait_id, [ty, ty])` via `infcx.predicate_must_hold_modulo_regions(&obligation)` with an inline comment explaining why `const PartialEq` is *not* required even inside `const fn`: backwards compatibility, sound because `PartialEq::eq` is never invoked (lowered MIR compares primitive fields directly). Empirically confirmed by `b2_const_fn`: `const fn is_target(k: Key) -> bool { match k { TARGET => true, _ => false } }` with standard non-`const` `#[derive(PartialEq, Eq)] struct Key(u16, bool)` compiles and evaluates at compile time (`CONST_FN_MATCH T=true F=false`).

#### 4.3 RFC 3535 Float Patterns, Signed Zero `BinOp::Eq`, and `E0741`

Although `is_structural_eq_shallow(ty::Float(_))` returns `false` (`util.rs:1483`), `valtree_to_pat` only guards `ty::Adt` with `type_marked_structural` (`const_to_pat.rs:253`). The `ty::Float(flt)` arm (`const_to_pat.rs:451-466`) checks `is_nan()` across `F16`/`F32`/`F64`/`F128`:
- Any NaN (both canonical `f64::NAN` and non-canonical payload `f64::from_bits(0x7ff0_0000_0000_0001)`) is rejected with `NaNPattern` (`error: cannot use NaN in patterns`, citing RFC 3535).
- Any non-NaN float lowers to `PatKind::Constant { value }`, which `Builder::pick_test_for_match_pair` (`rustc_mir_build/src/builder/matches/test.rs:49-51`) maps to `TestKind::ScalarEq { value }` and `Builder::perform_test` (`L183-236`) lowers to `BinOp::Eq` rather than `TerminatorKind::SwitchInt`.
- Live `--emit=mir` inspection of `match_pos_zero` and `match_neg_zero` (`b3_float_zero`) confirms exact MIR emission:

```mir
fn match_pos_zero(_1: f64) -> bool {
    bb0: {
        _2 = Eq(const 0f64, copy _1);
        switchInt(move _2) -> [0: bb1, otherwise: bb2];
    }
    ...
}
fn match_neg_zero(_1: f64) -> bool {
    bb0: {
        _2 = Eq(const -0f64, copy _1);
        switchInt(move _2) -> [0: bb1, otherwise: bb2];
    }
    ...
}
```

At runtime, `NEG0_MATCHES_POS0=true POS0_MATCHES_NEG0=true NAN_MATCHES_0=false`. Conversely, `struct FTag<const F: f64>;` is rejected (`E0741` on `1.102.0-nightly`; untagged error `'f64' is forbidden as the type of a const generic parameter` on `1.98.0-nightly`) because `f64` does not implement `Eq` or `ConstParamTy_`.

#### 4.4 Raw Pointers, Function Pointers, `FnDef`, Unions, and Padded-Struct Pattern Matching

- **Thin provenance-free raw pointer (`b4_intptr`):** `const INT_PTR: *const u8 = core::ptr::without_provenance(0x1000)` succeeds in `valtrees.rs:144-145` and lowers to `PatKind::Constant` (`const_to_pat.rs:467-471`) -> `TestKind::ScalarEq` (`INT_PTR_MATCH=true MISMATCH=false`).
- **Thin provenance-bearing raw pointer (`b4_provptr`):** `const PROV_PTR: *const u8 = &X as *const u8` fails `try_to_scalar_int()` (`valtrees.rs:146`), producing `PointerPattern` (`error: function pointers and raw pointers not derived from integers in patterns behave unpredictably...`).
- **Wide raw pointer without provenance (`b4_wideptr`):** `core::ptr::slice_from_raw_parts(core::ptr::without_provenance(0x1000), 4)` hits `BackendRepr::ScalarPair` at `valtrees.rs:138-139` and is rejected with `PointerPattern` despite having no provenance.
- **Function pointer (`b4_fnptr`):** Rejected at `valtrees.rs:153` with `PointerPattern` (making `const_to_pat.rs:472-476` `unreachable!`).
- **Function item (`ty::FnDef`, `a4_fndef` / `a4_fndef_direct`):** Accepted by `const_to_valtree_inner` as `ValTree::zst` (`valtrees.rs:109-112`), but rejected in patterns both because `FnDef` does not implement `PartialEq` (`E0277`) and because `valtree_to_pat` falls through to `InvalidPattern` (`const_to_pat.rs:477-484`).
- **Union (`b4_union`):** Rejected at `valtrees.rs:174-175` -> `UnionPattern` (`const_to_pat.rs:189-192`), even when a manual `impl PartialEq` is present.
- **Padded struct (`b5_pad_pat`):** Matching a runtime `Padded` whose padding bytes are `[0xDE, 0xAD, 0xBE]` against `const PAD_ZERO` returns `PAD_PAT_MATCH=true`, because `valtree_to_pat` produces `PatKind::Leaf` with field subpatterns `0: 1u8, 1: 2u32` that never read offsets `1..4`.

#### 4.5 `min_adt_const_params` vs. `adt_const_params` Dual Coherence Gates

`library/core/src/marker.rs:1105-1120` defines `pub trait ConstParamTy_: StructuralPartialEq + Eq {}` and the builtin derive macro `ConstParamTy` gated under `#[unstable(feature = "min_adt_const_params", issue = "154042", implied_by = "adt_const_params")]`. Implementing `ConstParamTy_` triggers two distinct coherence checks in `compiler/rustc_hir_analysis/src/coherence/builtin.rs:170-245` and `compiler/rustc_trait_selection/src/traits/misc.rs:92-201`:

1. **`#[non_exhaustive]` Gate (`misc.rs:123-134`):** Unless `tcx.features().adt_const_params()` is active, any variant where `variant.is_field_list_non_exhaustive()` fails with `ConstParamTyImplementationError::NonExhaustive(attr_span)` (`error: the trait 'ConstParamTy' may not be implemented for this type ... non exhaustive const params are forbidden`). Empirically verified: rejected under `#![feature(min_adt_const_params)]` (`b6_min_nonexh`, `rc = 1`), accepted under `#![feature(adt_const_params)]` (`b6_full_nonexh`, `NONEXH_WITH_FEATURE_OK`).
2. **Field-Visibility Gate (`builtin.rs:187-205`):** Unless `tcx.features().adt_const_params()` is active, any struct having a field whose visibility is strictly narrower than the struct's visibility (`struct_vis.greater_than(field.vis, tcx)`) fails with `ConstParamTyFieldVisMismatch` (`struct fields are less visible than the struct`). Empirically verified: `pub struct PrivField { x: u8 }` is rejected under `#![feature(min_adt_const_params)]` (`b6_min_priv`, `rc = 1`) and accepted under `#![feature(adt_const_params)]` (`b6_full_priv`, `PRIV_WITH_FEATURE_OK`).
3. **Bypass & Unsized Gates:** `#![feature(const_param_ty_unchecked)]` bypasses both checks entirely (`builtin.rs:183-185`), while `ty::Slice`, `ty::Str`, and `ty::Ref(_, inner, Mutability::Not)` require `#[unstable_feature_bound(unsized_const_params)]` (`misc.rs:109-116, 160-171`).

### 5. `v0` Const-Generic Symbol Mangling and `self.consts` Backref Deduplication

Basis: source (`compiler/rustc_symbol_mangling/src/v0.rs:307-311, 771-947, 1027-1077`) + execution (`rustc 1.98.0-nightly` + `llvm-nm`, `rustc 1.102.0-nightly`) + derived (Lean `v4.34.1` `mangleValTree_injective`, `manglePairWithBackref_dedups_mod_pad_and_ref`)

Generic arguments in `V0SymbolMangler::print_path_with_generic_args` (`v0.rs:1046-1062`) emit `I <path> <args...> E`, prefixing every `GenericArgKind::Const(c)` with `K` (`L1057`) before invoking `print_const` (`L771-947`). `print_const` checks the backref table `self.consts: FxHashMap<ty::Const<'tcx>, usize>` at `L803-806` (emitting `B <base62(start - start_offset)>_` via `print_backref`, `L307-311`), encodes the canonical `ValTree`, and caches `!ct.has_escaping_bound_vars()` entries at `L943-945`.

Complete empirical verification on `c_mangle.rs` compiled with `-C symbol-mangling-version=v0 -C opt-level=0 --emit=obj` (matching byte-for-byte apart from crate disambiguator hash across `rustc 1.98.0-nightly` and `rustc 1.102.0-nightly`):

| Rust Instantiation | `v0.rs` Encoding Rule | Observed Mangled Symbol (`1.98.0-nightly` `llvm-nm`) | Structural Decode |
| :--- | :--- | :--- | :--- |
| `mangle_i32::<42>` | `L812-830`: basic type `l` (`i32`) + lowercase hex + `_` | `_RINvCs35L8AT6TD9s_8c_mangle10mangle_i32Kl2a_EB2_` | `K` + `l` (`i32`) + `2a_` (`0x2a = 42`) |
| `mangle_i32::<-42>` | `L820-829`: sign-extend, push `n` if `< 0`, then `unsigned_abs()` hex + `_` | `_RINvCs35L8AT6TD9s_8c_mangle10mangle_i32Kln2a_EB2_` | `K` + `l` (`i32`) + `n` (neg) + `2a_` (`-42`) |
| `mangle_str::<"hi">` | `L857-867` (`R`) + `L833-853` (`e` + 2-digit hex UTF-8 bytes + `_`) | `_RINvCs35L8AT6TD9s_8c_mangle10mangle_strKRe6869_EB2_` | `K` + `R` (`&`) + `e` (`str`) + `6869_` (`b"hi"`) |
| `mangle_arr::<[1, 2, 3]>` | `L869-891`: `A <elem>... E` | `_RINvCs35L8AT6TD9s_8c_mangle10mangle_arrKAh1_h2_h3_EEB2_` | `K` + `A` + `h1_ h2_ h3_` (`u8` = `h`) + `E` |
| `mangle_ref::<R1>` & `mangle_ref::<R2>` (`&7u8`) | `L857-867`: `R <pointee_const>` | `_RINvCs35L8AT6TD9s_8c_mangle10mangle_refKRh7_EB2_` (**count = 1**) | `K` + `R` + `h7_`; `R1` and `R2` collapse into 1 symbol! |
| `mangle_pad::<PAD_ZERO>` & `mangle_pad::<PAD_DEAD>` | `L892-935`: `V <def_path> S (<field_ident> <const>)* E` | `_RINvCs35L8AT6TD9s_8c_mangle10mangle_padKVNtB2_6PaddedS1ah1_1bm2_EEB2_` (**count = 1**) | `K V Nt B2_ 6Padded S 1a h1_ 1b m2_ E`; padding erased -> 1 symbol! |
| `mangle_tup::<TupleStruct(9, true)>` | `L914-917` (`CtorKind::Fn`): `V <def_path> T <fields...> E` | `_RINvCs35L8AT6TD9s_8c_mangle10mangle_tupKVNtB2_11TupleStructTh9_b1_EEB2_` | `K V ... 11TupleStruct T h9_ b1_ E` (`b1_` = `true`) |
| `mangle_enum::<Choice::Unit>` | `L911-913` (`CtorKind::Const`): `V <variant_path> U` | `_RINvCs35L8AT6TD9s_8c_mangle11mangle_enumKVNtNtB2_6Choice4UnitUEB2_` | `... 6Choice 4Unit U` (no `E` terminator for unit variant) |
| `mangle_enum::<Choice::Tup(0x201)>` | `L914-917`: `V <variant_path> T <fields...> E` | `_RINvCs35L8AT6TD9s_8c_mangle11mangle_enumKVNtNtB2_6Choice3TupTt201_EEB2_` | `... 3Tup T t201_ E` (`t` = `u16`) |
| `mangle_enum::<Choice::Named { tag: -3 }>` | `L918-933`: `V <variant_path> S (<field> <const>)* E` | `_RINvCs35L8AT6TD9s_8c_mangle11mangle_enumKVNtNtB2_6Choice5NamedS3tagan3_EEB2_` | `... 5Named S 3tag a n 3_ E` (`a` = `i8`, `n3_` = `-3`) |
| `mangle_dup_backref::<PAD_ZERO, PAD_DEAD>` | `L803-806, L943-945`: second `ty::Const` hits `self.consts` | `_RINvCs35L8AT6TD9s_8c_mangle18mangle_dup_backrefKVNtB2_6PaddedS1ah1_1bm2_EKBK_EB2_` | Second const arg emitted as **`KBK_`** (`B` + base-62 `K_` encoding relative offset `47` since `47 - 1 = 46 -> 'K'` after `_R`, i.e., byte index `49` pointing directly to `VNtB2_6PaddedS1ah1_1bm2_E`)! |

Crucially, `self.consts` keys on interned `ty::Const<'tcx>` (`v0.rs:803`). Because `PAD_ZERO` and `PAD_DEAD` canonicalize to the exact same interned `ValTree`, their `ty::Const` keys are pointer-equal, so `mangle_dup_backref::<PAD_ZERO, PAD_DEAD>` emits `KBK_` for the second parameter—proving end-to-end linker-symbol merging across distinct CTFE padding bit patterns. Note also that `v0.rs:936-938` calls `bug!` on any non-`ConstParamTy` constant type (e.g., `ty::Float`, `ty::RawPtr`, `ty::FnDef`), confirming that symbol mangling strictly relies on `ConstParamTy` coherence checks rather than the broader `ValTree` admission set.

### 6. Mechanized Lean `v4.34.1` Formalization (`support/ValTreeCanonicalizationAndConstPatSoundness.lean`)

Basis: derived (kernel-verified Lean `v4.34.1` proof module, `1,569` lines, `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`)

The standalone Lean `v4.34.1` module `support/ValTreeCanonicalizationAndConstPatSoundness.lean` formalizes an abstract semantics of the audited `rustc` algorithms (explicitly scoped as a standalone formal model without claiming to import `joshlf/anneal`'s `Trusted.MirSemantics`):

1. **Byte-level `AllocVal` with explicit `pad : List MemByte`, `allocAddr : Nat`, `Provenance := Option Nat`, and `FloatVal` (`posZero`, `negZero`, `finite`, `nan`)**, quotiented by structurally recursive `toValTree` and reconstructed by structurally recursive `fromValTree` (which allocates `uninitPad padLen` for every struct/enum padding region).
2. **Active-variant `valTreeToPat`** checking `isStructuralShallow` on ADTs, projecting only the active enum variant via `valTreeVariantsToPat`, rejecting NaN floats and `FnDef`, and matching runtime `AllocVal`s via `patMatches` (using `floatIeeeEq` and ignoring padding/ref addresses).
3. **Type-directed `v0` mangler `mangleValTree`** paired with a constructive prefix-free recursive-descent inverse parser `parseValTree` and a two-argument `manglePairWithBackref` cache model.
4. **Executable `settled`-memoized DAG traversal `evalBinaryDagMemo`** over binary sharing DAGs, directly contrasted against `dagLogicalLeaves` (`2^d`) and `dagUnmemoizedVisits` (`2^(d+1) - 1`) at `VALTREE_MAX_NODES = 100_000`.

Every theorem below passes Lean `v4.34.1` kernel checking with **0 errors, 0 warnings, 0 `sorryAx`, 0 `Classical.choice`, 0 `Lean.ofReduceBool`, 0 `Lean.trustCompiler`, 0 `partial def`, and 0 `._unsafe_rec`**:

| Theorem (`ValTreeFormal.*`) | Mechanized Statement | Kernel `#print axioms` |
| :--- | :--- | :--- |
| `toValTree_ignores_padding_and_ref_addr` | `SameFieldsModPadAndRef a1 a2 → toValTree a1 = toValTree a2` | `[propext, Quot.sound]` |
| `fromValTree_preserves_fields_and_uninit_padding` | `HasTy a ty → toValTree a = .ok vt → ∃ a', fromValTree ty vt = .ok a' ∧ SameFieldsModPadAndRef a a' ∧ allPaddingUninit a' = true ∧ toValTree a' = .ok vt` | `[propext]` |
| `activeVariant_pat_matches_iff_structural_eq` | `HasTy c ty → HasTy x ty → toValTree c = .ok vt → valTreeToPat ty vt = .ok p → patMatches p x = structuralEq c x` | `[propext, Quot.sound]` |
| `provenance_raw_ptr_rejected` | `toValTree (.thinRawPtr addr (some allocId)) = .error .provenanceRawPtr` | none (`[]`) |
| `wide_raw_ptr_rejected` | `toValTree (.wideRawPtr addr metaLen prov) = .error .wideRawPtr` | none (`[]`) |
| `fn_ptr_rejected` | `toValTree (.fnPtr sym) = .error .fnPtr` | none (`[]`) |
| `union_rejected` | `toValTree (.unionVal name raw) = .error .unionType` | none (`[]`) |
| `nan_pattern_rejected` | `valTreeToPat .float (.leafFloat (.nan payload)) = .error .nanPattern` | `[propext]` |
| `fndef_valtree_ok_but_pat_rejected` | `toValTree (.fnDef sym) = .ok ValTree.zst ∧ valTreeToPat (.fnDef sym) ValTree.zst = .error (.unsupportedType "fnDef")` | `[propext]` |
| `mangleValTree_injective` | `mangleValTree ty vt1 = .ok toks → mangleValTree ty vt2 = .ok toks → vt1 = vt2` | `[propext]` |
| `manglePairWithBackref_dedups_mod_pad_and_ref` | `SameFieldsModPadAndRef a1 a2 → toValTree a1 = .ok vt → mangleValTree ty vt = .ok toks → manglePairWithBackref ty a1 a2 = .ok (toks, [.backref 0])` | `[propext, Quot.sound]` |
| `settledNodeCount_eq` | `∀ d, settledNodeCount d = d + 1` | `[propext, Quot.sound]` |
| `ce1_distinct_padding_bytes_unify_to_same_valtree` | Constructive witness: `padZeroVal ≠ padDeadVal`, equal `ValTree`, `KB` backref dedup, reconstructed `[.uninit, .uninit, .uninit]` padding | `[propext]` |
| `ce2_inactive_nonstructural_variant_payload_admitted` | Constructive witness: `Wrap<Manual>::Empty` admitted as `.variantPat "Wrap" 0 .nil` while `Wrap<Manual>::Full(Manual(1))` rejected as `.nonStructural "Manual"` | `[propext]` |
| `ce3_dag_memoized_node_count_exponentially_below_tree_leaves` | Constructive witness: `settledNodeCount 18 = 19 < 100000`, while `dagLogicalLeaves 18 = 262144 > 100000` and `dagUnmemoizedVisits 18 = 524287 > 100000` | `[propext, Quot.sound]` |

### 7. Direct Architectural Implications for `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean:492-560`, `trusted/lean/Trusted/MirSemantics.lean:949-1019, 1429-1570`, `trusted/rustc-capture/src/driver.rs:25-84`) + derived

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes its exact current boundary and five mandatory obligations for any extension covering non-scalar constants, patterns, or ADT const generics:

1. **Current Fail-Closed Status:** `MirAst.ConstLit` (`trusted/lean/Trusted/MirAst.lean:504-506`) defines only `| scalar (bits : BitVec 128) | zeroSized` (explicitly rejecting `ConstValue::Slice`, `ConstValue::Indirect`, floats, raw pointers, and `Operand::RuntimeChecks` via `.unsupported`). `Trusted.MirSemantics.evalTerminator` (`MirSemantics.lean:1553-1567`) supports `.switchInt` only over `.scalar` and `.bool`, and `trusted/rustc-capture/src/driver.rs:25` currently pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and performs no MIR extraction in `after_analysis` yet (`L75-84`). Because Anneal currently fails closed on all aggregates, references, floats, raw pointers, and `ConstValue::Indirect`, none of the `ValTree` hazards introduce unsoundness in `c131b320e` today.
2. **Mandatory Padding-Uninit Preservation on `ConstValue::Indirect`:** When `rustc-capture` adds `ConstValue::Indirect` / aggregate constants, it MUST serialize `Allocation` byte initialization masks (`InitMask`) verbatim rather than filling padding offsets with zero bytes. Treating reconstructed const-generic padding as `0x00` would diverge unsoundly from Miri (where reading byte `[1]` of `Padded` is UB across all four tested paths).
3. **Quotient-Consistent Monomorphization Identity:** Any `rustc-capture` item key or Lean proof-obligation identity for const-generic instantiations MUST key on canonical `ValTree` (or `v0` mangled symbol), never on CTFE allocation bytes or `AllocId`s, because `rustc` unifies `Tag<PAD_ZERO>` with `Tag<PAD_DEAD>` and `RefTag<R1>` with `RefTag<R2>` into single monomorphized instances and single linker symbols.
4. **Separate MIR Lowering for Float & Thin-Raw-Pointer Patterns:** Float patterns lower via `BinOp::Eq` (`TestKind::ScalarEq`), *not* `SwitchInt` bitwise matching. Extending `MirSemantics` to floats must preserve IEEE `-0.0 == +0.0` and NaN non-equality on `BinOp::Eq` rather than reusing `evalSwitchBranches` (`MirSemantics.lean:1466-1476`). Provenance-free thin raw pointers admitted by `valtrees.rs:144-145` similarly lower via `ScalarEq` and must be distinguished from provenance-carrying `PointerVal`s (`MirSemantics.lean:411-421`).
5. **Explicit Capture Guard Against `settled`-Memoized Exponential DAGs & Large Array Patterns:** Once Anneal advances its pinned toolchain past `c61c52f51de` (`2026-07-03`), `VALTREE_MAX_NODES = 100_000` no longer bounds the unfolded leaf count of a `ValTree` (`2^18` leaves pass with `< 20` charged nodes). `rustc-capture` must either represent captured `ValTree` / `ConstValue` graphs with explicit DAG sharing (`AllocId` table) or enforce its own traversal node budget before serialization, and should not rely on `rustc`'s `VALTREE_MAX_NODES` to prevent stack overflow or OOM on large array patterns (`N >= 20_000`).

## Boundaries

- **Not examined (`feature(generic_const_exprs)`, `feature(gca_const_items)`, `feature(deref_patterns)`, `feature(const_param_ty_unchecked)`):** The alternative `try_normalize_erasing_regions` branch in `const_to_pat.rs:142-157` (under `gca_const_items`), `deref_patterns` direct `str` patterns (`const_to_pat.rs:426-429`), and unchecked `ConstParamTy` bypass (`builtin.rs:183-185`) were inspected in source but not executed empirically.
- **Not examined (non-`x86_64` / big-endian targets & non-`v0` `legacy` mangling):** All empirical runs targeted `x86_64-unknown-linux-gnu` with `-C symbol-mangling-version=v0`. Legacy symbol mangling (`compiler/rustc_symbol_mangling/src/legacy.rs`) and big-endian `ScalarInt` byte ordering were not tested.
- **Unsupported (`ty::View`):** In `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `ty::View(..)` hits `unimplemented!()` in `valtrees.rs:213, 390`, `util.rs:1505`, and `v0.rs:691` because view-type lowering is not yet implemented upstream.
- **Known not to apply (Lean model transfer boundary):** `support/ValTreeCanonicalizationAndConstPatSoundness.lean` is a standalone formalization of `ValTree`, `const_to_pat`, `v0` token mangling, and binary-DAG `settled` traversal. Passing Lean `v4.34.1` kernel checks proves mathematical properties of this abstract model—it does *not* mechanically verify `rustc`'s Rust source code, does *not* import `joshlf/anneal`'s `Trusted.MirSemantics`, and does *not* model arbitrary cyclic/non-binary pointer graphs or Rust's full lifetime/borrow-checking interaction (`const_to_pat.rs:632-637`).
- **Known not to apply (`1.98.0-nightly` vs. `1.102.0-nightly` divergence):** The `DAG_CG_2POW18_DEPTH=18` memoization bypass and the `N = 20_000` `SIGSEGV` stack overflow do *not* occur on `rustc 1.98.0-nightly@14210df0e`; conversely, the `SIGSEGV` crash on self-referential `static X: Thing = Thing(&X)` does *not* occur on `rustc 1.102.0-nightly@3ef0c22cd` or `HEAD@342d74463`. Both transitions are bounded precisely by commits `c61c52f51de4d41929a9a20f5921afa73e5718cf` and `464199092963f32f12411516db535ca39ba2cb0e`.
- **Unknown (exact stack-overflow threshold between `N = 10_000` and `N = 20_000` on `1.102.0-nightly`):** The `1.102.0-nightly` sweep sampled `{1000, 4000, 10000, 20000, 50000, 99999, 100001}`; the exact first `N ∈ (10_000, 20_000]` that triggers `SIGSEGV` depends on default thread stack size (`RUST_MIN_STACK` / `ulimit -s`) and frame size on that nightly build and was not binary-searched.

## Evidence

### 1. Audited Primary-Source Revisions and Exact Line Ranges

All commit hashes were resolved live against GitHub on `2026-11-22`:

- **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`):**
  - `compiler/rustc_const_eval/src/const_eval/valtrees.rs:21-60` (`branches`), `63-80` (`slice_branches`), `83-219` (`const_to_valtree_inner`, `settled`/`visited`, `ty::RawPtr`/`FnPtr`/`FnDef`/`Ref`/`Adt` dispatch), `223-255` (`reconstruct_place_meta`), `258-265` (`create_valtree_place`), `268-292` (`eval_to_valtree`), `298-392` (`valtree_to_const_value`), `395-408` (`valtree_to_ref`), `411-487` (`valtree_into_mplace`).
  - `compiler/rustc_const_eval/src/const_eval/mod.rs:28-29` (`const VALTREE_MAX_NODES: usize = 100000`).
  - `compiler/rustc_const_eval/src/const_eval/eval_queries.rs:222-235` (`mk_eval_cx_to_read_const_val`), `258-338` (`op_to_const`, `ConstValue::Slice` / `Indirect`).
  - `compiler/rustc_middle/src/mir/interpret/queries.rs:90-172` (`const_eval_resolve_for_typeck`), `206-256` (`const_eval_global_id_for_typeck`, `NodesOverflow` / `CyclicConst` diagnostics).
  - `compiler/rustc_middle/src/ty/consts/valtree.rs:33-64` (`ValTree`), `102-227` (`Value`, `try_to_raw_bytes`, `destructure_adt_const`).
  - `compiler/rustc_type_ir/src/const_kind.rs:238-252` (`ValTreeKind`).
  - `compiler/rustc_mir_build/src/thir/pattern/const_to_pat.rs:42-56` (`const_to_pat`), `74-76` (`type_marked_structural`), `100-227` (`alias_to_pat`, outer `PartialEq` check at `214-221`), `244-488` (`valtree_to_pat`, active-variant enum recursion at `379-389`, array expansion at `412-420`, RFC 3535 NaN check at `451-466`), `618-698` (`type_has_partial_eq_impl`, non-`const` `PartialEq` rationale at `638-650`).
  - `compiler/rustc_mir_build/src/builder/matches/test.rs:30-63` (`pick_test_for_match_pair`), `183-236` (`TestKind::ScalarEq` -> `BinOp::Eq`).
  - `compiler/rustc_middle/src/ty/util.rs:1465-1507` (`Ty::is_structural_eq_shallow`).
  - `compiler/rustc_trait_selection/src/traits/misc.rs:92-201` (`type_allowed_to_implement_const_param_ty`, `!tcx.features().adt_const_params()` non-exhaustive gate at `123-134`, `unsized_const_params` gate at `109-116, 160-171`).
  - `compiler/rustc_hir_analysis/src/coherence/builtin.rs:170-245` (`visit_implementation_of_const_param_ty`, field-visibility gate at `187-205`).
  - `compiler/rustc_symbol_mangling/src/v0.rs:307-311` (`print_backref`), `771-947` (`print_const`, `self.consts` backref at `803-806, 943-945`, signed `n` prefix at `819-829`, `&str` hex at `833-853`, `R`/`Q` ref at `857-867`, `A`/`T` at `869-891`, `V...U/T/S...E` at `892-935`), `1027-1077` (`print_path_with_generic_args` `K` prefix, `push_integer_62`).
  - `library/core/src/marker.rs:255-273` (`StructuralPartialEq`), `1099-1143` (`ConstParamTy_`, `ConstParamTy` derive macro under `min_adt_const_params`).
- **Causal historical `rust-lang/rust` commits inspected:**
  - `c61c52f51de4d41929a9a20f5921afa73e5718cf` (`2026-07-03`): `detect cycles during valtree construction for self-referential consts` (added `visited` + `settled` to `valtrees.rs` and regression tests `tests/ui/consts/const_in_pattern/cyclic-const-*-issue-144719.rs`).
  - `464199092963f32f12411516db535ca39ba2cb0e` (`2026-08-09`): `Remove ensure_sufficient_stack` (46 files including `valtrees.rs`, `rustc_mir_build/src/builder/matches/mod.rs`, `rustc_pattern_analysis/src/usefulness.rs`).
  - `94add9677e2de57a2e414350bedcd13f07426a5e` (`2026-11-12`): `view-types: add 'View' variant to 'TyKind'` (sole difference in `valtrees.rs` and `v0.rs` between `3ef0c22cd` and `342d74463`).
- **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
  - `trusted/lean/Trusted/MirAst.lean:492-560` (`ConstLit`, `ConstOperand`, `Operand`).
  - `trusted/lean/Trusted/MirSemantics.lean:949-1019` (`evalOperandToSlot`, `evalPrimitiveOperand`), `1429-1570` (`evalSwitchBranches`, `evalBoolSwitchBranches`, `evalTerminator`).
  - `trusted/rustc-capture/src/driver.rs:25, 75-84` (`COMPILER_VERSION`, `after_analysis` callback).

### 2. Preserved Support Artifacts (`support/`)

| File | Description & Observation Date |
| :--- | :--- |
| `support/probe_valtree_and_const_to_pat.py` | Self-contained Python 3 probe harness reproducing all Part A (`ValTree` + 4 Miri padding checks + array sweep + `99_999`/`100_000`/`100_001` boundary + depth-18 DAG + const/static cycles + `FnDef`), Part B (`const_to_pat` + MIR dump + `min_adt_const_params` vs. `adt_const_params`), and Part C (`v0` symbol mangling + `llvm-nm` extraction) experiments (`2026-11-22`). |
| `support/probe_valtree_and_const_to_pat_results.json` | Live execution output from `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` on `x86_64-unknown-linux-gnu` (`2026-11-22T07:14:01Z`). |
| `support/rustc_1_102_0_nightly_baseline_results.json` | Scrubbed cross-version execution output from `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` on `x86_64-unknown-linux-gnu` (`2026-11-21T18:22:14Z`), confirming post-`c61c52f51de` `2^18` DAG memoization and post-`464199092963` `N = 20_000..99_999` array-match `SIGSEGV`. |
| `support/ValTreeCanonicalizationAndConstPatSoundness.lean` | Standalone `1,569`-line Lean `v4.34.1` formalization verified with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, `2026-11-22`). |

### 3. Verbatim Lean `v4.34.1` Kernel Verification & Axiom Audit Log

Command executed (`exit 0`, `0` errors, `0` warnings):

```bash
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/ValTreeCanonicalizationAndConstPatSoundness.lean
```

Verbatim `#print axioms` output:

```text
'ValTreeFormal.toValTree_ignores_padding_and_ref_addr' depends on axioms: [propext, Quot.sound]
'ValTreeFormal.fromValTree_preserves_fields_and_uninit_padding' depends on axioms: [propext]
'ValTreeFormal.activeVariant_pat_matches_iff_structural_eq' depends on axioms: [propext, Quot.sound]
'ValTreeFormal.provenance_raw_ptr_rejected' does not depend on any axioms
'ValTreeFormal.wide_raw_ptr_rejected' does not depend on any axioms
'ValTreeFormal.fn_ptr_rejected' does not depend on any axioms
'ValTreeFormal.union_rejected' does not depend on any axioms
'ValTreeFormal.nan_pattern_rejected' depends on axioms: [propext]
'ValTreeFormal.fndef_valtree_ok_but_pat_rejected' depends on axioms: [propext]
'ValTreeFormal.mangleValTree_injective' depends on axioms: [propext]
'ValTreeFormal.manglePairWithBackref_dedups_mod_pad_and_ref' depends on axioms: [propext, Quot.sound]
'ValTreeFormal.settledNodeCount_eq' depends on axioms: [propext, Quot.sound]
'ValTreeFormal.ce1_distinct_padding_bytes_unify_to_same_valtree' depends on axioms: [propext]
'ValTreeFormal.ce2_inactive_nonstructural_variant_payload_admitted' depends on axioms: [propext]
'ValTreeFormal.ce3_dag_memoized_node_count_exponentially_below_tree_leaves' depends on axioms: [propext, Quot.sound]
```

## Revalidation

To cheaply determine whether these findings still hold on a newer `rust-lang/rust` nightly, `Miri`, `Lean 4`, or `joshlf/anneal` revision:

1. **Re-run the standalone `rustc` + `Miri` + `v0` probe suite (~1–2 minutes):**
   ```bash
   python3 support/probe_valtree_and_const_to_pat.py --output /tmp/valtree_reval.json
   ```
   Check specifically:
   - `part_a_valtree_canonicalization.padding_erasure_unification.stdout == "SAME_TID=true V0=102 V1=102"` and all four Miri padding checks return `rc == 1` with `at [1], encountered uninitialized memory`;
   - `valtree_const_generic_arr_100000.compile_rc == 0` vs. `valtree_const_generic_arr_100001.compile_rc == 1` (`NodesOverflow`);
   - Whether `valtree_dag_cg_2pow18` passes (`settled` bypass still active) or fails (`NodesOverflow` restored for DAGs);
   - Whether `valtree_array_match_size_sweep["20000"]` still crashes (`rc == -11`) or compiles cleanly (e.g., if `rustc_pattern_analysis` / `builder/matches` becomes iterative or restores stack growth);
   - `part_b_const_to_pat_and_structural_eq.active_variant_empty_skips_nonstructural_payload.compile_rc == 0` vs. `active_variant_full_rejects_nonstructural_payload.compile_rc == 1`;
   - `part_c_v0_const_generic_mangling.mangle_pad_symbol_count == 1`, `mangle_ref_symbol_count == 1`, and `KBK_` (or equivalent `KB<base62>_`) backref in `mangle_dup_backref_symbols`.

2. **Diff the narrow upstream `rust-lang/rust` implementation regions since `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:**
   ```bash
   git diff 342d74463af7dd3018ef6aa04dd5500c2deb5bd1..HEAD -- \
     compiler/rustc_const_eval/src/const_eval/valtrees.rs \
     compiler/rustc_const_eval/src/const_eval/mod.rs \
     compiler/rustc_mir_build/src/thir/pattern/const_to_pat.rs \
     compiler/rustc_mir_build/src/builder/matches/test.rs \
     compiler/rustc_middle/src/ty/util.rs \
     compiler/rustc_trait_selection/src/traits/misc.rs \
     compiler/rustc_hir_analysis/src/coherence/builtin.rs \
     compiler/rustc_symbol_mangling/src/v0.rs
   ```
   Changes to `settled` accounting in `valtrees.rs`, `VALTREE_MAX_NODES` in `mod.rs`, `is_structural_eq_shallow` / `valtree_to_pat`, `TestKind::ScalarEq`, `ConstParamTy` coherence checks, or `V0SymbolMangler::print_const` require updating the corresponding sections of this report.

3. **Re-verify the Lean `v4.34.1` formalization and confirm zero `Classical.choice` / `sorryAx` / `Lean.ofReduceBool`:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/ValTreeCanonicalizationAndConstPatSoundness.lean
   ```

4. **Check `joshlf/anneal` capture-boundary drift since `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
   ```bash
   git diff c131b320eeeb26ef692e5afd5ec8db49ee518613..HEAD -- \
     trusted/lean/Trusted/MirAst.lean \
     trusted/lean/Trusted/MirSemantics.lean \
     trusted/rustc-capture/src/driver.rs
   ```
   Any addition of `ConstLit` constructors for `Indirect`/`Slice`/float/raw-pointer constants or live MIR extraction in `rustc-capture` triggers the five boundary obligations in Findings Section 7.
