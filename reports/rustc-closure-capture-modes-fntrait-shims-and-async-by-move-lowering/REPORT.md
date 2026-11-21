# RFC 2229 Disjoint Closure Capture, `Fn`-Trait Shims, and `AsyncFn` `by_move_body` Lowering in `rustc`

## Summary

Closure and `async ||` (`CoroutineClosure`) lowering in `rustc` spans four tightly coupled compiler layers that any verified MIR frontend or operational semantics must preserve in lockstep:

1. **RFC 2229 Disjoint Capture, Truncation, and Drop-Order Sorting (`rustc_hir_typeck::upvar`)**: In Rust Edition 2021+, closures capture minimal disjoint projection paths ordered by the lattice `Immutable < UniqueImmutable < Mutable < ByValue` (plus `ByUse`, which is ordered above `ByRef(_)` and incomparable with `ByValue`). Precision is truncated before raw-pointer dereferences and union projections (`restrict_precision_for_unsafe`), before `Index`/`Subslice` (`restrict_capture_precision`), and—crucially only for non-`Copy` `ByValue` captures—at the outermost ADT implementing `Drop` (`restrict_precision_for_drop_types`). Moving a `Copy` field out of a `Drop` ADT is **not** truncated. Minimized captures per root variable are sorted lexicographically by `FieldIdx` to preserve field declaration drop order.
2. **`UniqueImmBorrow` Representation and Pretty-Printer Erasure**: `ty::BorrowKind::UniqueImmutable` lowers into MIR as `BorrowKind::Mut { kind: MutBorrowKind::ClosureCapture }` (no top-level `BorrowKind::Unique` variant exists in MIR). It arises both when `truncate_place_to_len_and_update_capture_kind` truncates a `Mutable` capture across a `Deref` of `&mut` and when `Builder::limit_capture_mutability` borrows through an immutable (`Mutability::Not`) root binding. `mir::pretty` renders **all** `BorrowKind::Mut { .. }` variants as `&mut` (never `&uniq`), so text MIR dumps display `_5 = &mut _2` on a non-`mut` local `_2: &mut i32` while borrowck still enforces uniqueness via `E0501` and rejects user `&mut r` via `E0596`.
3. **`Fn`/`FnMut`/`FnOnce` Shims, `ClosureFnPointer` Coercion, and `extern "rust-call"` Untupling**: `fn_abi_new_uncached` unpacks the trailing tuple parameter of `extern "rust-call"` signatures into flat ABI arguments. Calling a `Fn` closure via `FnMut::call_mut` generates **no shim** (`needs_fn_once_adapter_shim(Fn, FnMut) == Ok(false)`), relying on ABI equivalence of `&Self` and `&mut Self`. Calling a `Fn`/`FnMut` closure via `FnOnce::call_once` generates `ShimKind::ClosureOnce`, which creates `&mut self`, dispatches to `FnMut::call_mut`, and drops `self` on both the normal return path (`bb1`) and the panic cleanup pad (`bb3` with `UnwindAction::Terminate(InCleanup)`). Coercing a non-capturing closure to `fn(...)` (`PointerCoercion::ClosureFnPointer`) takes the function address of `Instance::resolve_closure(..., ClosureKind::FnOnce)`—i.e., the `ClosureOnce` shim itself—where the zero-sized `self` becomes `PassMode::Ignore` and the remaining untupled ABI matches `extern "Rust" fn(...)`. `ShimKind::FnPtr` explicitly projects each tuple field and emits an indirect `Call`.
4. **`AsyncFn` (`CoroutineClosure`) Lending vs. `by_move_body` Synthesis**: A `Fn`/`FnMut` `async ||` closure's primary inner coroutine (`{closure#0}`) lends upvars by reference from `&self`/`&mut self`. Because `AsyncFnOnce::async_call_once(self, args)` destroys the `call_once` stack frame before returning the `Future`, `rustc` synthesizes a second `DefKind::SyntheticCoroutineBody` (`{synthetic#0}`) via `coroutine_by_move_body_def_id`: it peels one `Deref` from child by-ref captures, remaps 1-to-N child field indices onto parent owned upvars, splices bridging `Field`/`Deref` projections, drops obsolete `FakeBorrowKind::Shallow` borrows, constructs the future via `ShimKind::ConstructCoroutineInClosure`, and routes both `Future::poll` (`try_resolve_item_for_coroutine`) and `ShimKind::DropGlue` to `{synthetic#0}` whenever `args.kind_ty() != id_args.kind_ty()`. Already-`FnOnce` async closures short-circuit without synthesizing `{synthetic#0}`.
5. **Anneal MIR TCB Seam and Mechanized Refinement**: `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted.MirAst` and `Trusted.MirSemantics`) fails closed (`.unsupported`) on `Closure`, `CoroutineClosure`, `Coroutine`, `FnPtr`, `AggregateKind::{Closure,Coroutine,CoroutineClosure}`, `Cast` (`ClosureFnPointer`), `Drop`, `Yield`, `CoroutineDrop`, `BackwardIncompatibleDropHint`, non-empty `Place.projection`, and omits `Body.spread_arg`. A standalone constructive Lean `v4.34.1` formalization (`support/ClosureCaptureAndAsyncFnRefinement.lean`, 24 kernel-checked theorems, zero `sorry`, zero `Classical.choice`, zero native reflection axioms) proves capture-lattice laws, raw-pointer/`Drop`-ADT/`&mut`-deref truncation invariants, disjoint-path frame and drop-count soundness, `ClosureOnceShim`/`ClosureFnPointer`/`FnPtrShim` equivalences, `MakeByMoveBody` 1-to-N place-rewriting preservation, `AsyncFnOnce` dangling-borrow freedom, and two sharpness counterexamples demonstrating why both `by_move_body` synthesis and `Drop`-ADT boundary truncation are semantically mandatory.

## Applicability

This report characterizes four directly examined, immutable upstream artifacts and their relationships:

- **`rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`** (source inspection): authoritative upstream compiler implementation of closure capture analysis, THIR/MIR building, shim synthesis, `extern "rust-call"` ABI untupling, `ClosureFnPointer` codegen, and `coroutine_by_move_body_def_id`.
- **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`; source-diffed against `c7d5ba59d` and directly executed): supplies all live MIR dumps (`-Z dump-mir=all`), LLVM IR (`--emit=llvm-ir`), borrow-checker diagnostics, and native runtime execution in `support/probe_closure_capture_and_async_fn.py`.
- **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`** (source inspection): characterizes the exact trusted MIR AST (`trusted/lean/Trusted/MirAst.lean`) and operational semantics (`trusted/lean/Trusted/MirSemantics.lean`, including conservative `deinitMovedPlace = true` move deinitialization) fail-closed boundary against the `rustc` constructs studied here.
- **`leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`** (execution): kernel-checks `support/ClosureCaptureAndAsyncFnRefinement.lean` under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Version Shared Behavior vs. Revision-Specific Deltas (`14210df0e` vs. `c7d5ba59d`)

Direct line-by-line diffs between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` establish:

- **Shared across both revisions**: RFC 2229 capture minimization (`compute_min_captures`), field-index drop-order sorting, raw-pointer/union/index/drop truncation (`restrict_precision_for_unsafe`, `restrict_capture_precision`, `restrict_precision_for_drop_types`), `MutBorrow -> UniqueImmutable` truncation rule (`truncate_place_to_len_and_update_capture_kind`), `BorrowKind::Mut { kind: MutBorrowKind::ClosureCapture }` emission and `&mut` pretty-printing, `build_call_shim` (`ClosureOnce`, `FnPtr`, `spread_arg`), `build_construct_coroutine_by_move_shim`, `needs_fn_once_adapter_shim`, `try_resolve_item_for_coroutine`, `ClosureFnPointer` codegen (`rvalue.rs`), and `coroutine_by_move_body_def_id` (`by_move_body.rs` differs by only 16 mechanical import/binder-API lines).
- **Revision-specific deltas (`14210df0e` -> `c7d5ba59d`)**:
  1. **`InstanceKind` shim nesting**: In `14210df0e`, shims are direct variants `InstanceKind::{ClosureOnceShim, FnPtrShim, ConstructCoroutineInClosureShim, DropGlue, ...}`. In `c7d5ba59d`, they are grouped under `InstanceKind::Shim(ShimKind<'tcx>)`, with `ShimKind::ClosureOnce { call_once, closure, track_caller }` adding a `closure: DefId` field.
  2. **`mir::pretty` `AggregateKind::Closure` truncation bug fixed**: In `14210df0e` (`compiler/rustc_middle/src/mir/pretty.rs:1260-1267`), printing `AggregateKind::Closure` zips `tcx.upvars_mentioned(def_id).keys()` (one entry per root variable) with `places` (one operand per disjoint captured path), silently dropping trailing operands whenever multiple disjoint fields are captured from the same root variable (empirically observed in Probe 1). In `c7d5ba59d` (`pretty.rs:1267-1272`), this is fixed to zip `tcx.closure_captures(def_id)` with `assert_eq!(captures.len(), places.len())`, emitting `capture.to_symbol()` (e.g., `p__a`, `p__b__val`).
  3. **`UpvarCapture::ByUse` (`hir::CaptureBy::Use`)**: Present in `c7d5ba59d` (`ty/closure.rs:49-76`, `upvar.rs:788, 2256-2271, 2423-2461`) for experimental `use ||` / `.use` ergonomic cloning; `UpvarCapture::partial_cmp` returns `None` for `(ByUse, ByValue)` and `determine_capture_info` triggers `bug!` if the same capture requires both.

Empirical findings apply directly to Rust Edition 2024 (and Edition 2018 where explicitly contrasted) on `x86_64-unknown-linux-gnu` at `-C opt-level=0` (chosen to prevent inlining from hiding shim bodies). Generalization to other targets holds for target-independent HIR/THIR/MIR lowering (`upvar.rs`, `thir/cx/expr.rs`, `shim.rs`, `by_move_body.rs`), while physical register assignment and `sret` byte sizes in LLVM IR are target-ABI-specific.

## Findings

### 1. RFC 2229 Disjoint Field Capture, Lattice Ordering, and Truncation Rules

Basis: source (`rust-lang/rust@c7d5ba59d`, `14210df0e`) + execution (`probe1_rfc2229_disjoint_and_drop`) + derived (`ClosureCaptureAndAsyncFnRefinement.lean`).

#### 1.1 Capture-Mode Lattice and Closure-Kind Inference

`compiler/rustc_middle/src/ty/closure.rs:49-76, 374-453` defines the capture lattice with load-bearing enum discriminant order:

```rust
pub enum BorrowKind { Immutable, UniqueImmutable, Mutable } // Immutable < UniqueImmutable < Mutable
pub enum UpvarCapture { ByRef(BorrowKind), ByUse, ByValue } // ByRef(_) < (ByValue | ByUse)
```

During type-checking (`compiler/rustc_hir_typeck/src/upvar.rs:735-804`), `FnCtxt::process_collected_capture_information` processes each raw `(Place, CaptureInfo)` collected by `ExprUseVisitor` in a fixed five-step pipeline:

1. `restrict_capture_precision(place, capture_kind)` (`upvar.rs:2378-2404`): calls `restrict_precision_for_unsafe` (`upvar.rs:2343-2370`), which truncates before any projection on a raw pointer (`*const T`/`*mut T`, leaving the raw pointer itself captured) or `union` ADT (`i = 0` if `base_ty` is raw ptr/union, `i + 1` if `proj.ty` is raw ptr/union), and truncates at the first `Index` or `Subslice` projection (`i`).
2. `truncate_capture_for_optimization(place, capture_kind)` (`upvar.rs:2727-2747`): finds the rightmost `Deref`; if the type immediately before that `Deref` is a shared reference `&T`, truncates to `idx + 1` (keeping the `*r` deref so `'static` lifetimes inside `&'a &'static A` are preserved while discarding redundant deeper field projections).
3. **Closure-kind escalation (`upvar.rs:757-784`)**: `ByValue -> FnOnce`, `ByRef(Mutable | UniqueImmutable) -> FnMut` (from `Fn`), `ByRef(Immutable)` leaves `Fn` unchanged.
4. **Capture-clause adjustment (`upvar.rs:786-790, 2408-2467`)**:
   - `move ||` (`adjust_for_move_closure`): truncates at the first `Deref` (cannot move behind a reference) and forces `UpvarCapture::ByValue`.
   - `use ||` (`adjust_for_use_closure`): truncates at the first `Deref` and forces `UpvarCapture::ByUse`.
   - non-`move` (`adjust_for_non_move_closure`): if `ByValue`, truncates at the first `Deref`; if `ByUse` (from `.use` inside a non-`use` closure), downgrades to `ByRef(Immutable)`.
5. **`Drop`-ADT truncation (`restrict_precision_for_drop_types`, `upvar.rs:2317-2337`)**: runs **after** step 4 so `move ||` conversions are visible. Crucially, truncation fires **only** when `curr_mode == UpvarCapture::ByValue && !type_is_copy_modulo_regions(param_env, place.ty())`. When triggered, it scans `i in 0..place.projections.len()` and truncates at the **first** (outermost) `ty::Adt(def, _)` with `def.destructor(tcx).is_some()`.

#### 1.2 Minimizing Overlapping Paths and Preserving Field Drop Order

`compute_min_captures` (`upvar.rs:879-1069`) maintains per-root-variable pairwise-incomparable (`PlaceAncestryRelation::Divergent`) capture lists. Whenever a new place is an ancestor or descendant of an existing entry, the deeper place is truncated to the shallower prefix via `truncate_place_to_len_and_update_capture_kind` (`upvar.rs:2633-2658`) and capture modes are joined via `determine_capture_info` (`upvar.rs:2608-2625`).

After minimization, `upvar.rs:1015-1062` sorts each root variable's captures lexicographically by their `ProjectionKind::Field(idx, _)` sequence (filtering out `Deref`/`OpaqueCast`/`UnwrapUnsafeBinder` to avoid ICE #118144). Because closure structs drop fields in declaration order, this preserves pre-RFC-2229 field drop order whenever all fields of a struct are captured.

#### 1.3 Empirical Verification (Probe 1, `rustc 1.98.0-nightly`)

Running `support/probe_closure_capture_and_async_fn.py` on `PairNoDrop { a: Tracked, b: Tracked }` vs. `PairWithDrop { a: Tracked, b: Tracked, log }` (`impl Drop for PairWithDrop`) confirms every branch of the algorithm:

| Specimen | Edition 2024 Outcome | Observed Built MIR Capture | Native Drop / Execution Log |
| :--- | :--- | :--- | :--- |
| One closure moving `p.a` (`!Copy`) & mutably borrowing `p.b.val` on `PairNoDrop` | Compiles (`rc=0`) | Closure body `{closure#0}` has `_1.0: Tracked` (`p__a`, `ByValue`) and `_1.1: &mut i32` (`p__b__val`, `ByRef(Mut)`) | `disjoint_val=1030`; `drop:a,after_c_one,drop:b,after_p_b` |
| `move \|\| p.a.read_val()` (`!Copy` `p.a`) on `PairNoDrop` while caller mutates `p.b` | Compiles (`rc=0`) | `_13 = {closure} { p: move (_4.0: Tracked) }` | `before_c_drop,drop:a,after_c_drop,drop:b` |
| `move \|\| p.a.read_val()` (`!Copy` `p.a`) on `PairWithDrop` | Compiles (`rc=0`); drops whole `PairWithDrop` at `drop(c)` | `_16 = {closure} { p: move _4 }` (whole `PairWithDrop`!) | `before_c_drop,drop:PairWithDrop,drop:a,drop:b,after_c_drop` |
| `move \|\| p.a.val` (`Copy` `i32` leaf) on `PairWithDrop` | Compiles (`rc=0`); **not** truncated! | `_16 = {closure} { p: copy ((_4.0: Tracked).1: i32) }` | `before_c_drop,after_c_drop,drop:PairWithDrop,drop:a,drop:b` |
| `move \|\| unsafe { (*raw).a.val }` with `raw = ptr::null()` | Compiles & runs cleanly (`rc=0`, no null deref) | `_2 = {closure} { raw: copy _1 }` (`size_of_val == 8`) | `raw_ptr_closure_size=8` |
| `\|\| { drop(p.a); }` on `PairWithDrop` | Compile error (`rc=1`) | `error[E0509]: cannot move out of type PairWithDrop, which implements the Drop trait` | — |
| `move \|\| { let _ = p.a.len(); }` on `PairWithDrop`, then reading `p.b` | Compile error (`rc=1`) | `error[E0382]: borrow of moved value: p` (whole `p` moved by `Drop`-ADT truncation) | — |

**Text-MIR Pretty-Printer Hazard (`14210df0e` vs. `c7d5ba59d`)**: In Probe 1's first specimen on `rustc 1.98.0-nightly (14210df0e)`, the caller's built MIR prints `_14 = &mut ((_4.1: Tracked).1: i32); _13 = {closure@...} { p: move (_4.0: Tracked) };`, omitting `_14` from the printed aggregate literal even though `{closure#0}` receives both `_1.0: Tracked` and `_1.1: &mut i32`. This is caused by `14210df0e`'s `pretty.rs:1260-1267` zipping `upvars_mentioned` instead of `closure_captures` (fixed in `c7d5ba59d:1267-1272`). Any verifier or static analyzer must read typed MIR `Rvalue::Aggregate` operands, never text-MIR dumps.

#### 1.4 Mechanized Soundness & Counterexample CE2

In `support/ClosureCaptureAndAsyncFnRefinement.lean`:
- `CaptureMode.join_comm`, `join_assoc`, `join_idem`, `le_join_left`, `le_join_right`, `join_least` prove the capture-mode lattice laws.
- `truncateAtRawPtr_no_raw_deref` proves raw-pointer truncation eliminates all raw-pointer `Deref`s from captured paths.
- `truncateForDropAdt_preserves_copy_leaf` and `truncateForDropAdt_truncates_noncopy_byVal` prove the exact `Copy`-vs-non-`Copy` `Drop`-ADT truncation dichotomy.
- `getAt_setAt_disjoint`, `setAt_setAt_comm_disjoint`, and `disjoint_captures_non_aliasing` prove tree-path separation and non-aliasing for arbitrary pairwise-disjoint minimized capture lists.
- `disjoint_field_move_preserves_dropCount` proves by induction over arbitrary field lists that when `hasCustomDrop = false`, moving field `i` by value and deinitializing slot `i` (`deinitTree`) preserves the exact total drop count (`dropCount child + dropCount remainder = dropCount root`).
- **CE2 (`ce2_splitting_drop_adt_violates_destructor_integrity`)**: for `struct S { a: Box<u32>, b: Box<u32> }` with `impl Drop for S`, moving `s.a` without truncating yields `wholeAdtInitialized naiveRemainder = false` (violating `Drop::drop(&mut self)`'s fully initialized receiver precondition), whereas `truncateForDropAdt` yields projection `[]` (whole `S`), preserving `wholeAdtInitialized = true` and `dropCount = 3`.

---

### 2. `UniqueImmBorrow` (`&uniq` -> `MutBorrowKind::ClosureCapture`) and Upvar Rewriting

Basis: source (`rust-lang/rust@c7d5ba59d`, `14210df0e`) + execution (`probe2_unique_imm_borrow`) + derived (`ClosureCaptureAndAsyncFnRefinement.lean`).

#### 2.1 Why and When `UniqueImmutable` / `MutBorrowKind::ClosureCapture` Occurs

When a closure mutates `*r` through an immutable binding `let r: &mut i32 = &mut x`, taking `&mut r` would violate `r`'s immutability (`E0596`), while taking `&r` would permit aliasing `&&mut i32` and forbid mutating `*r` (`E0594`). `rustc` resolves this in two places:

1. **HIR capture truncation (`upvar.rs:2633-2658`)**: `truncate_place_to_len_and_update_capture_kind` inspects the discarded suffix `len..place.projections.len()`. If `curr_mode == ByRef(Mutable)` and any discarded projection is `ProjectionKind::Deref` on a `&mut _` type, it downgrades `curr_mode` to `ByRef(ty::BorrowKind::UniqueImmutable)`. In Rust 2021+, `|| { *r += 5; }` alone captures `*r` (`&mut (*r)`), whereas combining `&r` (ancestor) with `*r += 7` (descendant) forces truncation back to `r` with `UniqueImmutable` (mechanized in `truncate_mutRef_across_mut_deref_yields_uniqImm`).
2. **THIR and MIR lowering (`thir/cx/expr.rs:1686-1731`, `builder/expr/as_rvalue.rs:646-725`)**:
   - `ThirBuildCx::capture_upvar` (`thir/cx/expr.rs:1710-1719`) maps `ty::BorrowKind::UniqueImmutable` to `mir::BorrowKind::Mut { kind: MutBorrowKind::ClosureCapture }`.
   - Independently, `Builder::limit_capture_mutability` (`as_rvalue.rs:703-706`) lowers mutable borrows of any capture rooted at a `Mutability::Not` local (or non-`mut` parent capture) as `BorrowKind::Mut { kind: MutBorrowKind::ClosureCapture }` rather than `MutBorrowKind::Default`.
   - Upvar uses inside closure bodies are deferred as `ExprKind::UpvarRef` in THIR (`thir/cx/expr.rs:1560-1578`) and rewritten to `CAPTURE_STRUCT_LOCAL` (`_1`) field projections during MIR construction by `to_upvars_resolved_place_builder` + `strip_prefix` (`builder/expr/as_place.rs:172-250`), stripping the captured HIR prefix and appending any remaining projections onto `capture_info.use_place` (which includes an extra `Deref` for `ByRef` captures).

#### 2.2 MIR Pretty-Printing Erasure vs. Borrow-Checker Discrimination (Probe 2)

`compiler/rustc_middle/src/mir/syntax.rs:151-240` defines `BorrowKind::{Shared, Fake(FakeBorrowKind), Mut { kind: MutBorrowKind }}`, where `MutBorrowKind::{Default, TwoPhaseBorrow, ClosureCapture}`. `compiler/rustc_middle/src/mir/pretty.rs:1172-1178` renders every `BorrowKind::Mut { .. }` as `"mut "`—there is **no** `&uniq` token in modern MIR dumps, and `CleanupPostBorrowck` (`cleanup_post_borrowck.rs:31-60`) strips `BorrowKind::Fake(_)` and `BackwardIncompatibleDropHint` while leaving `BorrowKind::Mut { .. }` intact.

Probe 2 empirically separates all four cases on `rustc 1.98.0-nightly`:

- `let r: &mut i32 = &mut x; let mut c = || { *r += 5; };` (Edition 2024): captures `_5 = &mut (*_2)` (`&mut i32`), compiles and yields `15`; adding `let _alias = &r; c();` fails with **`E0501`** (`first borrow occurs due to use of *r in closure`) because `limit_capture_mutability` emitted `MutBorrowKind::ClosureCapture` due to immutable root `r`.
- `let r: &mut i32 = &mut x; let mut c = || { let _ = &r; *r += 7; };` (Edition 2024): captures `_5 = &mut _2` (`&mut &mut i32`) directly from non-`mut` `let _2: &mut i32` (`built_mir_prints_uniq_token = false`, `post_cleanup_prints_mut_on_non_mut_local_r = true`), compiles and yields `17`; adding `let _alias = &r; c();` fails with **`E0501`** (`first borrow occurs due to use of r in closure`).
- `let _p = &mut r;` (Edition 2024 user code): fails with **`E0596`** (`cannot borrow r as mutable, as it is not declared as mutable`), confirming `ClosureCapture` is strictly non-expressible in surface Rust.
- `let mut c = || { *r += 5; }; let _alias = &r; c();` (Edition 2018): fails with **`E0501`** (`first borrow occurs due to use of r in closure`), confirming pre-RFC-2229 whole-binding capture.

---

### 3. `extern "rust-call"` Untupling, `Fn`/`FnMut`/`FnOnce` Shims, and `ClosureFnPointer` Coercion

Basis: source (`rust-lang/rust@c7d5ba59d`, `14210df0e`) + execution (`probe3_fn_trait_shims_and_rust_call`) + derived (`ClosureCaptureAndAsyncFnRefinement.lean`).

#### 3.1 `extern "rust-call"` ABI Untupling and `body.spread_arg`

In `compiler/rustc_ty_utils/src/abi.rs:548-561`, `fn_abi_new_uncached` intercepts `ExternAbi::RustCall`: it pops the final input parameter (asserting it is `ty::Tuple(tupled_arguments)`) and appends its elements as `extra_args` flattened into the physical calling convention. In MIR, shims whose trait signature uses `ExternAbi::RustCall` set `body.spread_arg = Some(Local::new(sig.inputs().len()))` (`shim.rs:1004-1006`), instructing codegen to repack those flat ABI arguments into the MIR tuple local (or pass them through to another `rust-call` callee).

#### 3.2 Dispatch Matrix Across `Fn`, `FnMut`, `FnOnce`, `ClosureFnPointer`, and `FnPtrShim`

From `compiler/rustc_middle/src/ty/instance.rs:785-861, 996-1024`, `compiler/rustc_ty_utils/src/instance.rs:349-384`, `compiler/rustc_mir_transform/src/shim.rs:40-77, 781-1009`, and `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:530-544`:

| Callable Kind | Trait / Coercion Site | Resolved Instance (`c7d5ba59d`) | MIR & ABI Mechanism |
| :--- | :--- | :--- | :--- |
| `Fn` closure | `Fn::call(&self, args)` | `InstanceKind::Item(closure_did)` | Direct call; no shim |
| `Fn` closure | `FnMut::call_mut(&mut self, args)` | `InstanceKind::Item(closure_did)` | **No shim** (`needs_fn_once_adapter_shim(Fn, FnMut) == Ok(false)`); passes `&mut Self` to `fn(&Self, ...)` relying on pointer ABI compatibility |
| `Fn` or `FnMut` closure | `FnOnce::call_once(self, args)` | `Shim(ShimKind::ClosureOnce { .. })` | `Adjustment::RefMut` (`&mut _1`), direct call to `FnMut::call_mut`, `Drop(_1)` in `bb1` (return) AND `bb3` (cleanup pad with `UnwindAction::Terminate(InCleanup)`); `spread_arg = Some(_2)` |
| Non-capturing closure (`ZST`) | `PointerCoercion::ClosureFnPointer` | `Instance::resolve_closure(..., FnOnce)` -> `ShimKind::ClosureOnce` (or item if `FnOnce`) | Takes `get_fn_addr` directly! ZST `self` is `PassMode::Ignore` (0 ABI args), `extern "rust-call"` untuples `(A1, ..., An)`, so machine signature is `fn(A1, ..., An) -> R` |
| `fn(A...) -> R` or `FnDef` | `Fn` / `FnMut` / `FnOnce` | `Shim(ShimKind::FnPtr(trait_item, fnty))` | Receiver adjusted via `Deref(ImmRef)` / `Deref(MutRef)` / `Identity`; MIR explicitly projects `Field(i, ity)` out of `tuple_arg` (`shim.rs:926-931`) for an indirect `Call`; `spread_arg = Some(_2)` |

#### 3.3 Empirical Verification (Probe 3, `-C opt-level=0`, LLVM IR + Native Execution)

Probe 3 verifies every row of the dispatch matrix directly on `rustc 1.98.0-nightly`:

- **`ClosureFnPointer` target**: `coerce_non_capturing()` compiles to `ret ptr @...coerce_non_capturing0...FnOnceTllEE9call_once...`, whose LLVM signature is `define internal i32 @...call_once...(i32 %0, i32 %1)` (zero `self` pointer parameter!), allocating `%_1 = alloca [0 x i8], align 1` internally before invoking `coerce_non_capturing::{closure#0}(ptr %_1, i32 %4, i32 %6)`.
- **No shim for `Fn` called via `FnMut`**: `call_fn_mut::<main::{closure#0}>` emits a single direct `call i32 @...4main0...(ptr align 8 %f, i32 %x, i32 %y)` with no intermediate shim.
- **`ClosureOnceShim` normal + unwind drop ordering**: For capturing `Fn` closure `move |x, y| x + y + tag.get_bias()` owning non-`Copy` `DropTag`, LLVM IR shows both `bb1: call void @...drop_glue(%_1); ret i32 %_0` and `cleanup -> bb3: invoke void @...drop_glue(%_1) to label %bb4 unwind label %terminate` (`terminate: call @...panic_in_cleanup`). Native execution logs `closure_once_log=before_call_once,drop:env,after_call_once` on normal return and `closure_once_unwind_is_err=true log=drop:env,after_catch` on panic unwind.
- **`FnPtrShim` untupling**: `<fn(i32, i32) -> i32 as FnOnce<(i32, i32)>>::call_once` has LLVM signature `(ptr %_1, i32 %0, i32 %1)`, packs/unpacks `%_2 = alloca [8 x i8]`, and performs `%_0 = call i32 %_1(i32 %3, i32 %5)`.

#### 3.4 Mechanized Equivalence

`closureOnceShim_obs_equiv`, `closureOnceShim_fn_drops_original_env`, `closureFnPointer_zst_equiv`, and `fnPtrShim_untuple_equiv` in `support/ClosureCaptureAndAsyncFnRefinement.lean` prove exact return-value and trace equivalence across both normal return and panic unwind paths.

---

### 4. `AsyncFn` (`CoroutineClosure`) Lending vs. `by_move_body` Lowering

Basis: source (`rust-lang/rust@c7d5ba59d`, `14210df0e`) + execution (`probe4_async_closure_by_move_body`) + derived (`ClosureCaptureAndAsyncFnRefinement.lean`).

#### 4.1 Four-Part Compiler Architecture for `by_move_body`

An `async move ||` closure desugars into an outer `CoroutineClosure` owning captured upvars and an inner `Coroutine` (`{closure#0}`). When the outer closure implements `AsyncFn` or `AsyncFnMut`, the inner coroutine captures upvars by reference (`&T` or `&mut T`) from the outer closure's environment so multiple futures can lend from `&self`/`&mut self`. Calling `AsyncFnOnce::async_call_once(self, args)` consumes `self` in the `call_once` frame and returns a `Future` that outlives that frame—so returning a lending coroutine would dangle. `rustc` prevents this across four coordinated components:

1. **Construction shim (`ty_utils/instance.rs:385-406`, `shim.rs:75-77, 1222-1332`)**: When resolving `AsyncFnOnce` on a `CoroutineClosure` whose own `kind() != FnOnce`, `resolve_instance_raw` returns `ShimKind::ConstructCoroutineInClosure { coroutine_closure_def_id, receiver_by_ref: false }`. `build_construct_coroutine_by_move_shim` builds a 1-block MIR body emitting `Rvalue::Aggregate(AggregateKind::Coroutine(coroutine_def_id, coroutine_args), [Move(arg_1), ..., Move(self.upvar_0), ...])` with coroutine `kind_ty = ty::ClosureKind::FnOnce`. (When an `async ||` closure is invoked via synchronous `Fn`/`FnMut` traits—legal only when all upvars are `Copy` `&T`—`ty_utils/instance.rs:360-379` uses `receiver_by_ref: true` and `Copy((*self).upvar_i)`.)
2. **By-move body synthesis (`compiler/rustc_mir_transform/src/coroutine/by_move_body.rs:83-373`)**:
   - Short-circuit (`lines 196-200`): if `coroutine_kind == ty::ClosureKind::FnOnce` already, no second body is needed and `coroutine_def_id` is returned directly.
   - Parent-to-child capture alignment (`ty/closure.rs:455-519`, `by_move_body.rs:129-194`): `analyze_coroutine_closure_captures` matches each parent capture to one **or more** child captures sharing its projection prefix (handling 1-to-N splits when RFC 2229 lets the inner coroutine borrow disjoint fields of a single parent capture, e.g., a `Drop` ADT). For each child field `child_field_idx + num_args`, it computes:
     - `bridging_projections = child.projections[parent.projections.len()..]`, prefixed with `Deref` if `parent_capture.is_by_ref()`,
     - `peel_deref = child_capture.is_by_ref()`,
     - `remapped_idx = parent_field_idx + num_args` and `remapped_ty`.
   - `MakeByMoveBody` (`MutVisitor`, `lines 263-372`): clones `mir_built(coroutine_def_id)`, replaces `_1`'s type with `by_move_coroutine_ty`, rewrites every `_1.childIdx.<tail>` to `_1.remapped_idx.<bridging>.<tail_after_peel_deref>` (asserting the peeled element is `ProjectionElem::Deref`), replaces now-obsolete `BorrowKind::Fake(FakeBorrowKind::Shallow)` borrows of `_1.childIdx` with `StatementKind::Nop`, creates a `DefKind::SyntheticCoroutineBody` (`{synthetic#0}`), and feeds its `mir_built` so `StateTransform` and optimizations process it alongside `{closure#0}`.
3. **`Future::poll` dispatch (`ty/instance.rs:899-919`)**: `try_resolve_item_for_coroutine` compares `args.as_coroutine().kind_ty()` against `id_args.as_coroutine().kind_ty()`. Matching kinds resolve to `InstanceKind::Item(coroutine_def_id)` (`{closure#0}`); mismatching kinds resolve to `InstanceKind::Item(tcx.coroutine_by_move_body_def_id(coroutine_def_id))` (`{synthetic#0}`).
4. **`DropGlue` dispatch (`shim.rs:79-123`)**: `ShimKind::DropGlue` performs the exact same `kind_ty` comparison (`lines 95-105`), selecting `tcx.optimized_mir(tcx.coroutine_by_move_body_def_id(coroutine_def_id)).coroutine_drop()` for `FnOnce`-flavored futures so unpolled or mid-suspension dropped futures drop their moved-in upvars rather than leaking them.

#### 4.2 Empirical Verification (Probe 4, Rust Edition 2024)

Probe 4 compiles and executes four scenarios on `rustc 1.98.0-nightly`:

- **Lending vs. `by_move_body` with bridging projection**: `buf: TrackedBuf` implements `Drop` (parent captures whole `buf: TrackedBuf` by move), while inner lending coroutine borrows `&buf.text: &String`:
  - `{closure#0}` (`built.after.mir`): `_5 = &(*(_1.1: &std::string::String));` — `StateTransform` size `40` bytes (`sret([40 x i8])`).
  - `{synthetic#0}` (`built.after.mir`): `_5 = &((_1.1: TrackedBuf).1: std::string::String);` (peeled `Deref` + spliced bridging field `.1`!) — `StateTransform` emits `drop(((*_34).1: TrackedBuf))` on completion and unwind, size `80` bytes (`sret([80 x i8])`, `+40 B = 48 B TrackedBuf - 8 B &String`).
  - `coroutine_closure_by_move.0.mir`: `_0 = {coroutine} { k: move _2, buf: move (_1.0: TrackedBuf) };`.
  - Native runtime: `lending_vs_once=(23,24,25)` with `log=before_make_once,after_make_once_before_poll,drop:buf1,after_poll_once` (`buf1` survives returning from `construct_once_future` and drops only after the future completes).
- **Mid-suspension drop (`DropGlue` -> `{synthetic#0}` `coroutine_drop`)**: Polling `fut_once` once (`Poll::Pending`) and dropping `Box::pin(fut_once)` outputs `mid_suspend_pending=true log=after_first_pending,drop:buf_suspend,after_drop_suspended` (exact-once drop via `ShimKind::DropGlue`).
- **Already-`FnOnce` short-circuit**: An `async move ||` body that calls `drop(buf)` produces `already_fnonce_synthesizes_synthetic_body: false` (zero `{synthetic#0}` MIR dumps) and executes cleanly (`already_fnonce=12 log=drop:buf_fnonce`).
- **1-to-2 field renumbering + bridging**: `pair: SplitPairWithDrop` (parent captures whole `SplitPairWithDrop` at `_1.0`) with inner lending coroutine capturing TWO disjoint refs `_1.1: &String` (`pair.a.text`) and `_1.2: &String` (`pair.b.text`). In `{synthetic#0}`, `MakeByMoveBody` remaps **both** `_1.1` and `_1.2` onto the single parent field `_1.1: SplitPairWithDrop` with distinct 2-step bridging paths:
  - `_4 = &(((_1.1: SplitPairWithDrop).0: TrackedBuf).1: std::string::String);`
  - `_5 = &(((_1.1: SplitPairWithDrop).1: TrackedBuf).1: std::string::String);`
  - `StateTransform` `sret` grows to `144` bytes; native output: `split_pair=(9,10) log=drop:SplitPairWithDrop,drop:sp_a,drop:sp_b`.

#### 4.3 Mechanized Soundness & Counterexample CE1

In `support/ClosureCaptureAndAsyncFnRefinement.lean`:
- `byMove_place_rewrite_preserves_eval` and `byMove_one_to_two_bridging_preserves_eval` prove that `MakeByMoveBody`'s `peel_deref` + `bridging_projections` + 1-to-N renumbering preserves exact sub-value evaluation for arbitrary `StructVal` trees.
- `asyncFnOnce_by_move_dangling_free` and `lending_and_by_move_compute_same_output` prove that `ByMoveFuture` never triggers `danglingReadUB` after `callOnceFrame` is freed (under arbitrary post-pop store mutations), computes the exact same output as `LendingFuture` polled over a live closure frame, and drops the moved-in upvar **exactly once** on both completion and mid-suspension drop.
- **CE1 (`ce1_naive_async_fn_once_dangles_while_by_move_succeeds`)**: On concrete `ce1Spec` (`upvarVal = 11, arg = 3`), naively delegating `AsyncFnOnce::async_call_once` to `LendingFuture` pointing at `callOnceFrame` and freeing `callOnceFrame` upon return causes `pollLending` to immediately hit `PollResult.danglingReadUB`, whereas `callAsyncFnOnceByMove` completes cleanly with `25` and `[.dropUpvar 7]`.

---

### 5. Seam to `joshlf/anneal@c131b320e` Trusted MIR Semantics

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`).

Inspecting `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes the exact fail-closed verification boundary for supporting closures, shims, and `AsyncFn` in Anneal:

1. **Types (`MirAst.lean:312-321`)**: `MirTy` admits only `.bool`, `.int`, `.unit`, `.never`, fieldless `.enum`, `.tuple`, `.ref`, and `.rawPtr`; `FnPtr`, `Closure`, `CoroutineClosure`, `Coroutine`, `CoroutineWitness`, and field-bearing `Adt` lower fail-closed to `.unsupported`.
2. **Rvalues & Statements (`MirAst.lean:608-628, 654-662`)**: `Rvalue.ref` collapses `BorrowKind` to binary `Mutability` (cannot distinguish `MutBorrowKind::ClosureCapture` vs. `Default` vs. `TwoPhaseBorrow`); `AggregateKind::{Closure, Coroutine, CoroutineClosure}` and `Cast` (`ClosureFnPointer`) fail closed to `.unsupported`; `StatementKind::BackwardIncompatibleDropHint` fails closed to `.unsupported` (note `CleanupPostBorrowck` strips it before `Runtime(PostCleanup)` MIR).
3. **Terminators & Body Metadata (`MirAst.lean:782-795, 815-860`)**: `TerminatorKind` supports only direct `FnDef` `.call` (indirect `FnPtr` calls, `Drop`, `Yield`, and `CoroutineDrop` lower to `.unsupported`); `Body` omits `spread_arg : Option Local` (required to interpret `extern "rust-call"` shims) and `coroutine : Option CoroutineInfo`.
4. **Operational Semantics (`MirSemantics.lean:949-976, 1313, 1568, 1730-1737`)**: `evalOperandToSlot` enforces `deinitMovedPlace = true` (deinitializing moved non-ZST locals to `.live none`) and rejects any non-empty `place.projection` (`!place.projection.isEmpty -> .error .unsupported`); `evalRvalue` faults `.unsupported` on `.ref`, `.addressOf`, and `.aggregateTuple`; `evalTerminator` faults `.unsupported` on `.call`; and `BodyStaticAdmitted` restricts all locals to `isSupportedScalarOrUnitTy`.
5. **Consequence for Verified Lowering (derived)**: Supporting closures and `AsyncFn` in Anneal's MIR TCB requires (a) preserving `deinitMovedPlace = true` at the **per-field** granularity when disjointly moving fields of non-`Drop` structs while forbidding partial moves of `Drop` ADTs (matching `PlaceTree.deinitTree` + CE2), (b) ingesting `Runtime(PostCleanup)` or `Runtime(Optimized)` MIR where `BackwardIncompatibleDropHint`, `Fake` borrows, and `StateTransform` have run, (c) capturing synthesized `ShimKind::{ClosureOnce, FnPtr, ConstructCoroutineInClosure, DropGlue}` and `DefKind::SyntheticCoroutineBody` (`{synthetic#0}`) instances into `Program.bodies` alongside user items, and (d) modeling `Body.spread_arg` plus `&Self` / `&mut Self` aliasing compatibility for `Fn`-via-`FnMut` shimless dispatch.

## Boundaries

- **Standalone Lean model vs. `joshlf/anneal` TCB (`known not to apply` as a direct TCB import)**: `support/ClosureCaptureAndAsyncFnRefinement.lean` is a standalone Lean `v4.34.1` formalization with zero imports of `joshlf/anneal`'s `Trusted.MirAst`/`Trusted.MirSemantics`. It proves core invariants over clean operational models of tree-structured places, `ClosureOnceShim`/`FnPtrShim`, `MakeByMoveBody` place rewriting, and frame-allocated coroutines; it does **not** prove end-to-end refinement of `rustc`'s full MIR/LLVM backend or connect directly to `Trusted.MirSemantics.WellFormed` (which currently rejects closures, projections, references, calls, and drops fail-closed).
- **`Fn`-via-`FnMut` shimless dispatch under Stacked/Tree Borrows (`not examined` dynamically in Miri)**: Source and LLVM IR confirm that calling a `Fn` closure via `FnMut::call_mut` invokes `fn(&Self, ...)` with a `&mut Self` argument without a shim (`needs_fn_once_adapter_shim(Fn, FnMut) == Ok(false)`). Whether any edge-case retagging interaction arises with interior mutability (`UnsafeCell`) under Miri Tree Borrows was not executed in Miri here.
- **Experimental `use ||` / `UpvarCapture::ByUse` and `AsyncDropGlue` (`not examined` empirically)**: `ByUse` capture clauses (`c7d5ba59d` `upvar.rs:788, 2423-2461`) and async drop shims (`ShimKind::{AsyncDropGlue, AsyncDropGlueCtor, FutureDropPoll}`, `shim.rs:131-176`) were observed in upstream source structure only; no nightly feature-gated execution probes were run for them.
- **Packed-struct field reference captures and `#[track_caller]` `ReifyShim` / KCFI (`not examined` empirically)**: `restrict_repr_packed_field_ref_capture` (`upvar.rs:2292`) and `ShimKind::Reify` for `#[track_caller]` closures (`ty/instance.rs:752-774`) were located in source but not probed dynamically.
- **Non-`x86_64` ABI details (`not examined`)**: Probe 3 and Probe 4 LLVM IR (`sret([80 x i8])`, register passing) were collected exclusively on `x86_64-unknown-linux-gnu`; `aarch64`, `i686`, and Windows ABI layouts were not measured.
- **`AsyncFn` `Fn::call` with `receiver_by_ref = true` (`not examined` empirically)**: `build_construct_coroutine_by_move_shim` (`shim.rs:1238-1291`) copies `&T` upvars when a non-lending `async ||` closure is invoked through synchronous `Fn::call`; this branch was verified by source inspection only.
- **`Anneal` support for closures/coroutines (`unsupported`)**: At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` and `Trusted.MirSemantics` explicitly mark closures, coroutines, function pointers, references in evaluation, field projections in evaluation, `Drop`, and `Call` as `.unsupported`.

## Evidence

All upstream Git commit SHAs were resolved live on `2026-11-21` via authenticated GitHub API queries, and all empirical and Lean verification artifacts are preserved in `support/`.

### Primary Upstream Source Citations

- **`rust-lang/rust` @ `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`** (with diffs verified against **`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`**):
  - `compiler/rustc_middle/src/ty/closure.rs`: `CAPTURE_STRUCT_LOCAL` (L21), `UpvarCapture` & `PartialOrd` (L49-76), `CapturedPlace::to_symbol` (L116-152), `BorrowKind` & `to_mutbl_lossy` (L374-453), `analyze_coroutine_closure_captures` (L455-519).
  - `compiler/rustc_hir_typeck/src/upvar.rs`: `process_collected_capture_information` (L735-804), `compute_min_captures` & `FieldIdx` drop-order sort (L879-1069), `InferBorrowKind` delegate (L2179-2313), `restrict_precision_for_drop_types` (L2317-2337), `restrict_precision_for_unsafe` (L2343-2370), `restrict_capture_precision` (L2378-2404), `adjust_for_{move,use,non_move}_closure` (L2408-2467), `determine_capture_info` (L2608-2625), `truncate_place_to_len_and_update_capture_kind` (L2633-2658), `determine_place_ancestry_relation` (L2665-2696), `truncate_capture_for_optimization` (L2727-2747).
  - `compiler/rustc_mir_build/src/thir/cx/expr.rs`: `ExprKind::Closure` lowering (L814-860), `convert_var` (`ExprKind::UpvarRef`, L1560-1578), `convert_captured_hir_place` (L1632-1684), `capture_upvar` (`UniqueImmutable -> MutBorrowKind::ClosureCapture`, L1686-1731).
  - `compiler/rustc_mir_build/src/builder/expr/as_place.rs`: `PlaceBase::Upvar` (L55-61), `convert_to_hir_projections_and_truncate_for_capture` (L81-120), `to_upvars_resolved_place_builder` & `strip_prefix` (L172-250).
  - `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs`: `AggregateKind::{Coroutine,Closure,CoroutineClosure}` (L329-340), `limit_capture_mutability` (`Mutability::Not -> MutBorrowKind::ClosureCapture`, L646-725).
  - `compiler/rustc_middle/src/mir/syntax.rs`: `BorrowKind` & `MutBorrowKind::ClosureCapture` (L151-240).
  - `compiler/rustc_middle/src/mir/pretty.rs`: `BorrowKind::Mut { .. } => "mut "` (L1172-1178); `AggregateKind::Closure` fix (`c7d5ba59d` L1267-1272 vs. `14210df0e` L1260-1267).
  - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`: `CleanupPostBorrowck::run_pass` (L27-84).
  - `compiler/rustc_mir_transform/src/shim.rs`: `make_shim` (`FnPtr`, `ClosureOnce`, `ConstructCoroutineInClosure`, coroutine `DropGlue` dispatch, L32-126), `build_call_shim` (L781-1009, `spread_arg` L1004-1006), `build_construct_coroutine_by_move_shim` (L1222-1332).
  - `compiler/rustc_mir_transform/src/coroutine/by_move_body.rs`: `coroutine_by_move_body_def_id` (L83-255), `MakeByMoveBody` (`visit_place`, `visit_statement`, `visit_local_decl`, L257-373).
  - `compiler/rustc_middle/src/ty/instance.rs`: `InstanceKind` / `ShimKind` (L62-160), `resolve_closure` (L785-797), `fn_once_adapter_instance` (L833-861), `try_resolve_item_for_coroutine` (L863-927), `needs_fn_once_adapter_shim` (L996-1024).
  - `compiler/rustc_ty_utils/src/instance.rs`: `resolve_instance_raw` for `Fn` / `AsyncFn` traits (L349-421).
  - `compiler/rustc_ty_utils/src/abi.rs`: `fn_abi_new_uncached` `ExternAbi::RustCall` untupling (L548-561).
  - `compiler/rustc_codegen_ssa/src/mir/rvalue.rs`: `PointerCoercion::ClosureFnPointer` codegen (L530-544).
- **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`**:
  - `trusted/lean/Trusted/MirAst.lean`: `MirTy` (L272-321), `ProjectionElem`/`Place` (L450-490), `Operand` (`deinitMovedPlace`, L522-560), `Rvalue` (L562-628), `StatementKind` (L630-662), `TerminatorKind` (L742-795), `Body` (L815-860).
  - `trusted/lean/Trusted/MirSemantics.lean`: `evalOperandToSlot` (`deinitMovedPlace = true`, L949-976), `evalRvalue` (L1240-1313), `evalTerminator` (L1537-1569), `BodyStaticAdmitted` (L1730-1737).

### Preserved Empirical & Formal Support Artifacts

- **`support/probe_closure_capture_and_async_fn.py`**: Self-contained Python 3 standard-library harness compiling and executing all 4 probe suites (including 6 negative compile-fail controls) against host `rustc`, capturing MIR dumps, LLVM IR, diagnostics, and native execution output.
- **`support/probe_closure_capture_and_async_fn_results.json`**: Full recorded execution output from `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / LLVM `22.1.6` on `x86_64-unknown-linux-gnu` (`observed_at: 2026-11-21T09:35:22Z`), all 4 positive suites exiting `0` with `0` compiler warnings and all 6 negative controls failing with exact expected error codes (`E0509`, `E0382`, `E0596`, `E0501` x3).
- **`support/ClosureCaptureAndAsyncFnRefinement.lean`** (993 lines): Standalone Lean `v4.34.1` formalization verified with:
  ```bash
  lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/ClosureCaptureAndAsyncFnRefinement.lean
  ```
  Exit code `0`, `0` warnings, `0` `sorry`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`, `0` `partial`, `0` `_unsafe_rec`. All 24 `#print axioms` theorems depend only on `[]`, `[propext]`, or `[propext, Quot.sound]`.

## Revalidation

To cheaply verify whether these findings still hold on a newer `rustc`, `joshlf/anneal`, or Lean release:

1. **Rerun the live `rustc` MIR/LLVM/native probe** (takes ~8 seconds on a single core):
   ```bash
   python3 support/probe_closure_capture_and_async_fn.py --out /tmp/closure_probe_reval.json
   ```
   Confirm:
   - Probe 1: `split_no_drop_log` drops `a` before `after_c_drop` and `b` after; `with_drop_non_copy_log` drops `PairWithDrop,a,b` before `after_c_drop`; `with_drop_copy_field_log` drops `PairWithDrop,a,b` **after** `after_c_drop`; `raw_ptr_closure_size=8`; negative controls emit `E0509` and `E0382`. (On `rustc` >= `c7d5ba59d`, `disjoint_one_closure_construct` will additionally show both `p__a` and `p__b__val` fields in pretty-printed MIR.)
   - Probe 2: `disjoint_deref=15 unique_imm_val=17`; `post_cleanup_prints_mut_on_non_mut_local_r=true`; negative controls emit `E0596` and `E0501`.
   - Probe 3: `coerce_non_capturing` returns `FnOnce::call_once` with 2 integer args `(i32, i32)`; `call_fn_mut` calls `main::{closure#0}` directly; `closure_once_log=before_call_once,drop:env,after_call_once`; `closure_once_unwind_is_err=true log=drop:env,after_catch`.
   - Probe 4: `already_fnonce_synthesizes_synthetic_body=false`; `lending_vs_once=(23,24,25)` with `buf1` dropped only after poll; `mid_suspend_pending=true` drops `buf_suspend` on drop; `{synthetic#0}` for `run_one_to_two_bridging_renumber_case` rewrites both `_1.1` and `_1.2` onto `((_1.1: SplitPairWithDrop).{0,1}: TrackedBuf).1`.
2. **Re-check the Lean kernel mechanization** (takes ~2 seconds):
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/ClosureCaptureAndAsyncFnRefinement.lean
   ```
   Verify exit code `0` and confirm `#print axioms` output contains no `sorryAx`, `Classical.choice`, `Lean.ofReduceBool`, or `Lean.trustCompiler`.
3. **Diff upstream hot paths**: Check `git diff <old>..<new>` on `compiler/rustc_hir_typeck/src/upvar.rs`, `compiler/rustc_mir_transform/src/shim.rs`, `compiler/rustc_mir_transform/src/coroutine/by_move_body.rs`, and `trusted/lean/Trusted/MirAst.lean` (in `joshlf/anneal`) for new `UpvarCapture`, `ShimKind`, `BorrowKind`, or `MirTy` constructors.
