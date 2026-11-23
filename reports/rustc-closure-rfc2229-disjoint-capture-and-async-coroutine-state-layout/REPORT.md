# RFC 2229 Disjoint Closure Capture and Async/Coroutine `StateTransform` Layout Soundness in `rustc`

## Summary

`rustc` compiles closures and `async`/coroutine blocks through two tightly structured analyses whose invariants determine both borrow-check disjointness and runtime memory/aliasing safety:

1. **RFC 2229 Disjoint Place Capture & `ClosureKind` Lattice (`compiler/rustc_hir_typeck/src/upvar.rs`, `compiler/rustc_middle/src/ty/closure.rs`)**:
   Since Edition 2021 (`span.at_least_rust_2021()`), `rustc` records minimal place-projection paths (`CapturedPlace` / `MinCaptureInformationMap`) rather than whole root variables. Wildcard discards such as `let _ = p3;` emit only `Delegate::fake_read` (`PlaceMention` in MIR) and capture **0 bytes**, whereas taking a reference (`let _ = &p3;`) captures an `8`-byte `&Pair` upvar and binding `let _x = s;` consumes `s` (`ByValue`, capturing `24` bytes for `String`). Directly read or copied `Copy` fields inside `move` closures preserve direct field projections (`adjust_for_move_closure` truncates only at the leftmost `Deref`), leaving non-`Copy` sibling fields (e.g., `sm.owned`) unmoved on the caller frame (`8`-byte closure vs. Edition 2018 `E0382`). When a place traverses a shared reference (`&BigRefTarget` field reads), `truncate_capture_for_optimization` trims trailing fields down to the **rightmost** `&`-deref (`idx + 1`), producing an `8`-byte `&BigRefTarget` capture rather than `&u64` while keeping `'static` field borrows isolated when nested derefs exist. When truncation trims across a `&mut` deref (e.g., `*r += 5` on `r: &mut i32`), mutable access downgrades to `BorrowKind::UniqueImmutable`, which still enforces `ClosureKind::FnMut` (`E0525` against `Fn()`) and lowers to `&mut &mut T` via `BorrowKind::to_mutbl_lossy` (`hir::Mutability::Mut`) during codegen.

2. **`StateTransform` Coroutine State Machine, Liveness-Conflict Storage Packing & `!Unpin` Pinning (`compiler/rustc_mir_transform/src/coroutine*`, `compiler/rustc_abi/src/layout/coroutine.rs`, `compiler/rustc_middle/src/ty/sty.rs`, `compiler/rustc_middle/src/mir/query.rs`)**:
   `StateTransform` transforms pre-transform `yield`-bearing MIR into a `Pin<&mut Coroutine> -> Poll<T>` (or `CoroutineState<Y, R>`) poll machine keyed by a discriminant with reserved states `UNRESUMED = 0`, `RETURNED = 1`, `POISONED = 2` (`"Panicked"`), and `SuspendN = 3 + N`. On unwind, cleanup paths are redirected to a poison block executing `SetDiscriminant(POISONED)` followed by `UnwindResume`; live probes on `rustc 1.98.0-nightly` confirm that re-polling a poisoned or returned `async fn` traps (`"async fn resumed after panicking"` / `"async fn resumed after completion"`) while drop shims execute `0` cleanup drops in states `1` and `2` (`DROPS=(0,1,1)`). Across source revisions (`14210df0e` vs. `960ba7cf7`), `rustc` `main` modularized single-file `coroutine.rs` into `coroutine/{mod.rs,layout.rs,drop.rs}`, gated `ResumedAfterPanic`/`ResumedAfterReturn` panic blocks behind `-Z async-panic` (`bool = true` default), and added `PackCoroutineLayout` (`Classic` vs. `CapturesOnly`) to `CoroutineLayout`. Non-overlapping suspend lifetimes (`storage_conflicts` `BitMatrix`) allow sequential locals across distinct `SuspendK` variants to share byte offsets (`SEQ_SIZE = 67` bytes, `align = 1`) compared to concurrently live locals (`OVL_SIZE = 131` bytes), while cross-await internal borrows prevent `Unpin` implementation (`E0277`), preserving stable frame addresses (`SELF_REF_SIZE = 80`, `align = 8`).

3. **Downstream Verifier Boundary (`joshlf/anneal`) & Kernel-Checked Lean `v4.34.1` Formalization**:
   At `joshlf/anneal` revision `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted/MirAst.lean` intentionally maps `TyKind::{Closure, Coroutine, CoroutineWitness, CoroutineClosure}`, `StatementKind::{SetDiscriminant, FakeRead, PlaceMention}`, `AssertKind::{ResumedAfterReturn, ResumedAfterPanic, ResumedAfterDrop}`, `TerminatorKind::{Yield, CoroutineDrop}`, and closure/coroutine `Rvalue::Aggregate` kinds to `.unsupported` (`FaultKind.unsupported`), failing closed rather than mismodeling closures or async state transforms. To establish formal ground truth alongside empirical compiler probing, the preserved standalone Lean `v4.34.1` module `support/ClosureRfc2229AndCoroutineStateLayoutSoundness.lean` (`2,840` lines, `566` `noncomputable def`s, `278` theorems, checked with `-DwarningAsError=true` and `0` `._unsafe_rec`, `0` `sorryAx`, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`) proves: (i) RFC 2229 disjoint-place non-interference and prefix-truncation soundness, (ii) coroutine transition determinism, poison trapping, and zero double-drop, (iii) conflict-graph non-overlapping variant storage packing safety, and (iv) `!Unpin` self-referential pinning address invariance (paired with an explicit counter-witness showing forged `Unpin` violates internal pointer validity).

## Applicability

This report examines and correlates four immutable artifacts, separated by role:

| Subject | Immutable Identity | Role in Report | Scope & Version Status |
| :--- | :--- | :--- | :--- |
| `rustc` nightly binary & compiler source (`rust-lang/rust`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`) | Directly executed compiler binary (`edition_2024`/`edition_2018`, `-Zdump-mir`, `-Zprint-type-sizes`) and matching upstream source tree | Authoritative for every measured MIR dump, type size (`67B`/`131B`/`80B`), closure byte size (`0B`/`8B`/`24B`), diagnostic error (`E0502`/`E0382`/`E0525`/`E0277`), and runtime behavior |
| Upstream `rust-lang/rust` source snapshot | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` (HEAD `main` audited on `2026-11-23`) | Comparative primary-source audit of post-1.98 refactorings | Authoritative for architectural splits (`coroutine.rs` -> `coroutine/{mod.rs,layout.rs,drop.rs}`), `-Z async-panic` gating, `explicit_captures` (`move(expr)`), and `PackCoroutineLayout`; **not executed** as a built compiler binary |
| `joshlf/anneal` MIR formal semantics | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean`) | Downstream verification-boundary audit | Establishes fail-closed `.unsupported` boundary for closure/coroutine lowering as of `2026-11-23` |
| `leanprover/lean4` kernel & elaborator | `5045d0056413266e57c625dcd7c365b10e377c52` (`Lean v4.34.1`, `x86_64-unknown-linux-gnu`) | Machine-checked verification engine for `support/ClosureRfc2229AndCoroutineStateLayoutSoundness.lean` | Checks all `278` theorems using only locked `Init.*` foundations under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` |

### Shared vs. Revision-Specific Behavior Between `14210df0e` and `960ba7cf7`

- **Shared across both revisions**:
  - Edition >= 2021 gating (`span.at_least_rust_2021()`), `MinCaptureInformationMap` ancestry merging (`determine_place_ancestry_relation`), `fake_read` non-capture for wildcards, `restrict_capture_precision`, `truncate_capture_for_optimization` rightmost shared-deref trim, `adjust_for_move_closure` direct field preservation, `ClosureKind` inference before clause adjustment, and `BorrowKind::UniqueImmutable` -> `FnMut` / `to_mutbl_lossy` -> `Mutability::Mut` lowering (`upvar.rs`, `ty/closure.rs`).
  - Reserved coroutine variant discriminants (`UNRESUMED = 0`, `RETURNED = 1`, `POISONED = 2`, `SuspendN = 3 + N`) in `ty/sty.rs`, entry `SwitchInt` dispatch, cleanup unwind redirection to `SetDiscriminant(POISONED)` -> `UnwindResume`, two-pass `coroutine_saved_local_eligibility` (Pass 1 single-variant uniqueness + Pass 2 `storage_conflicts` elimination + `< 2` variant collapse), and prefix promotion plus variant union layout (`rustc_abi/src/layout/coroutine.rs`).
- **Revision-specific differences**:
  - **Coroutine module split**: At `14210df0e`, `StateTransform` and `compute_layout` live in a single 1,996-line `compiler/rustc_mir_transform/src/coroutine.rs`; at `960ba7cf7`, they are factored into `compiler/rustc_mir_transform/src/coroutine/{mod.rs, layout.rs, drop.rs}`.
  - **`-Z async-panic` control**: At `14210df0e` (`coroutine.rs:1243-1271`), `ResumedAfterPanic` and `ResumedAfterReturn` emit `insert_panic_block` unconditionally (for non-`async_drop_in_place` `Async`/`Coroutine`). At `960ba7cf7` (`coroutine/mod.rs:902-925`), both are gated on `tcx.sess.opts.unstable_opts.async_panic` (which defaults to `true`, so default behavior matches `14210df0e`, while `-Z async-panic=false` emits `insert_poll_pending_block`).
  - **`CoroutineLayout` fields**: At `14210df0e` (`mir/query.rs:35-56`), `CoroutineLayout` carries `field_tys`, `field_names`, `variant_fields`, `variant_source_info`, and `storage_conflicts`. At `960ba7cf7` (`mir/query.rs:38-61`), `field_names` moved into `CoroutineSavedTy::debuginfo_name` and `CoroutineLayout` gained `pub pack: PackCoroutineLayout` (`Classic` vs. `CapturesOnly` in `rustc_abi/src/layout/coroutine.rs:44-51`).
  - **Explicit closure capture clauses (`use ||` and `move(expr)`)**: Both `14210df0e` and `960ba7cf7` include `hir::CaptureBy::Use` (`adjust_for_use_closure`), while `960ba7cf7` additionally tracks `explicit_captures` (`upvar.rs:96, 133, 295-296, 404`) and reorders internal helpers by ~80-120 lines.

All empirical binary measurements apply directly to `x86_64-unknown-linux-gnu` pointer width (`8` bytes) and Rust ABI struct field ordering without `-Z randomize-layout`.

## Findings

### 1. RFC 2229 Disjoint Closure Capture & `ClosureKind` Lattice

```text
Basis: source (upvar.rs, ty/closure.rs) + execution (rustc 1.98.0-nightly MIR dumps, type sizes, error probes) + derived
```

#### 1.1 Analysis Pipeline Order (`upvar.rs` & `ty/closure.rs`)

In both `14210df0e` and `960ba7cf7`, `rustc_hir_typeck::upvar::InferBorrowKind` collects variable accesses inside a closure body via `rustc_hir_typeck::expr_use_visitor::Delegate`:

1. **Edition Gate (`enable_precise_capture`)**: Checked via closure span (`span.at_least_rust_2021()`, `upvar.rs:2667-2671` in `14210df0e`, shifted in `960ba7cf7`). Before Edition 2021, accesses truncate to root variables (`projs = []`).
2. **Wildcard Discard Non-Capture (`Delegate::fake_read`)**: For patterns or bindings that read a place purely for initialization/match checking without copying, moving, or taking an address (such as `let _ = p3;` or `let _ = p3.a;`), `fake_read` checks edition and returns without adding a capture entry (`upvar.rs:2100` in `14210df0e`, `upvar.rs:2216` in `960ba7cf7`). Only taking `&p3` triggers `Delegate::borrow` (`UpvarCapture::ByRef(BorrowKind::Immutable)`), and binding `let _x = s;` or dropping/moving invokes `Delegate::consume` (`UpvarCapture::ByValue`).
3. **Minimal Disjoint Capture Map (`compute_min_captures`)**: Per root `LocalVarId`, accesses are inserted into `MinCaptureInformationMap` using `determine_place_ancestry_relation(place_a, place_b)` (`upvar.rs:2581-2612` in `14210df0e`, `upvar.rs:2665-2696` in `960ba7cf7`), which zips projection lists and compares lengths when initial projections match:
   - `Ancestor`: `place_a` is a strict prefix of `place_b` -> existing descendants are removed and their capture requirements are truncated up to `place_a.len()` via `truncate_place_to_len_and_update_capture_kind` and merged into `place_a` via `determine_capture_info`.
   - `SamePlace`: identical paths merge via `determine_capture_info`.
   - `Descendant`: `place_b` is a prefix of `place_a` -> the new access is truncated up to `place_b.len()` and merged into `place_b`.
   - `Divergent`: different roots OR differing projection elements at the first point of divergence -> both entries remain independent captures!
4. **Precision Restrictions Before `ClosureKind` Inference (`process_collected_capture_information`)**:
   - `restrict_capture_precision` (`upvar.rs:2262-2288` in `14210df0e`, `upvar.rs:2378-2404` in `960ba7cf7`): runs `restrict_precision_for_unsafe` (truncates before raw pointer derefs or union field projections so closure capture does not perform unsafe field reads outside an `unsafe` block) and then truncates at the leftmost `ProjectionKind::Index` or `ProjectionKind::Subslice` (arrays/slices are captured wholly rather than per index).
   - `truncate_capture_for_optimization` (`upvar.rs:2643-2663` in `14210df0e`, `upvar.rs:2727-2747` in `960ba7cf7`): searches for the **rightmost** `ProjectionKind::Deref` (`rposition`); if the type before that deref is a shared reference (`ty::Ref(.., hir::Mutability::Not)`), it truncates to `idx + 1` (keeping up through the `&`-deref itself). Crucially, stopping at the rightmost deref preserves outer `'static` references (`drop(&*m.a.field_of_a)` where `m: &'a MyStruct<'b>` and `m.a: &'static A`) rather than collapsing `m.a` back to `m` and needlessly binding the closure lifetime to `'a`.
5. **`ClosureKind` Inference Order Bug/Subtlety (`upvar.rs:757-790` in `960ba7cf7`)**:
   `process_collected_capture_information` infers `ty::ClosureKind` (`Fn` -> `FnMut` -> `FnOnce`, starting from `ClosureKind::LATTICE_BOTTOM = Fn`) from `(place, capture_kind)` **immediately after** `restrict_capture_precision` and `truncate_capture_for_optimization`, and **before** clause adjustments (`adjust_for_move_closure`, `adjust_for_use_closure`, `adjust_for_non_move_closure`) and `restrict_precision_for_drop_types`.
   - `UpvarCapture::ByValue` raises `ClosureKind` to `FnOnce`.
   - `UpvarCapture::ByRef(BorrowKind::Mutable | BorrowKind::UniqueImmutable)` raises `ClosureKind` to `FnMut` (unless already `FnMut` or `FnOnce`).
   - `_` (`ByRef(Immutable)` or `ByUse`) leaves `closure_kind` unchanged.
   This execution order explains two critical Rust behaviors:
   - First, a `move || c.read()` closure can implement `Fn` even after `adjust_for_move_closure` converts every capture's runtime representation to `UpvarCapture::ByValue`, because `ClosureKind` was already fixed as `Fn` before `adjust_for_move_closure` ran.
   - Second, in `determine_capture_info` (`upvar.rs:2608-2625` in `960ba7cf7`), `ByUse` and `ByValue` are ordered symmetrically **above** `MutBorrow > UniqueImmBorrow > ImmBorrow` in `UpvarCapture::partial_cmp` (and `ByUse` vs. `ByValue` is incomparable -> `None => bug!(...)`), **even though** `ByUse.toClosureKind` does not lift `ClosureKind` to `FnMut`/`FnOnce`. Any formal monotonicity law relating `UpvarCapture.dominates` to `ClosureKind.rank` must therefore restrict its domain away from `ByUse` or stratify pre-clause capture kinds separately from post-`adjust_for_use_closure` modes.
6. **Prefix-Truncation Downgrade (`truncate_place_to_len_and_update_capture_kind`) & `UniqueImmutable` (`ty/closure.rs:374-452`)**:
   Whenever a capture of mode `UpvarCapture::ByRef(BorrowKind::Mutable)` is truncated to length `len` and any dropped suffix projection (`place.projections[len..]`) dereferences a `&mut` reference (`ProjectionKind::Deref` where `proj_before_ty` is `ty::Ref(.., hir::Mutability::Mut)`), the capture mode converts from `BorrowKind::Mutable` to `BorrowKind::UniqueImmutable`. Rust exposes no surface syntax `&uniq T` because mutating through `*r` when `r: &mut i32` is an **immutable** local binding requires unique access without mutating `r`'s own pointer slot (`let r = ...`). At codegen/MIR lowering, `BorrowKind::to_mutbl_lossy` (`ty/closure.rs:442-452`) over-approximates `BorrowKind::UniqueImmutable` to `hir::Mutability::Mut` (`&mut &mut i32` in the closure environment tuple), and `process_collected_capture_information` marks the closure `FnMut`.

#### 1.2 Empirical Verification on `rustc 1.98.0-nightly` (`14210df0e`)

Running `support/probe_closure_rfc2229_and_coroutine_layout.py` compiles and executes the complete RFC 2229 matrix against `rustc 1.98.0-nightly` with `-Zdump-mir=built -Zdump-mir-dir=... -Zprint-type-sizes`:

| Probe / Closure Case | Edition | Captured Place & Mode in MIR (`-Zdump-mir=built`) | Measured Closure Size (`-Zprint-type-sizes`) | Trait / Borrow Result | Measured Value / Diagnostic |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `closure#0`: `\|\| p.a` concurrent with `p.b.push('!')` (`Pair { a: i32, b: String }`, 32B) | 2024 | `debug p__a => (*((*_1).0: &i32))` | `8` bytes (align 8) | Compiles & executes | `A=10 B=hi!` |
| Same pattern (`read_a = \|\| p.a; p.b.push('!');`) | **2018** | Root variable `p` borrowed wholly | Compile error | Rejected by borrowck | `error[E0502]: cannot borrow p.b as mutable because it is also borrowed as immutable` |
| `closure#1`: `\|\| *c_val` (`require_fn`, `Fn()`) | 2024 | `debug c_val => (*((*_1).0: &i32))` | `8` bytes (align 8) | Implements `Fn` | `SZ_CAP_C=8 VC=99` |
| `closure#2`: `\|\| { p.a += 5; p.a }` (`require_fn_mut`) | 2024 | `debug p__a => (*((*_1).0: &mut i32))` | `8` bytes (align 8) | Implements `FnMut` | `SZ_MUT_A=8 VMUT=15` |
| `closure#3`: immutable binding `let r_mut: &mut i32`, closure reads `(r_mut as *const _)` and mutates `*r_mut += 5` | 2024 | `debug r_mut => (*((*_1).0: &mut &mut i32))` (`_3 = &(*((*_1).0: &mut &mut i32))`) | `8` bytes (align 8) | `UniqueImmutable` merged -> `FnMut`, rejects `Fn` | `SZ_UNIQ=8 VUNIQ=8`; separate probe `unique_immutable_not_fn_rejected_e0525` fails with `error[E0525]` |
| `closure#4`: `\|\| { let t = s; t.into_bytes().len() }` (`s: String`) | 2024 | `debug s => (_1.0: std::string::String)` (by value) | `24` bytes (align 8) | Implements `FnOnce`, consumes `s` | `VONCE=7`; separate probe `binding_move_let_x_rejected_e0382` fails with `error[E0382]: borrow of moved value: s` |
| `closure#5`: `\|\| { let _ = p3; 6 }` | 2024 | Zero upvar debug locals; body is `_0 = const 6_i32;` | **`0` bytes** (align 1) | `fake_read` non-capture | `SZ_WILD.0 = 0`, `p3` remains intact (`P3_LEN=4`) |
| `closure#6`: `\|\| { let _ = p3.a; 7 }` | 2024 | Zero upvar debug locals; body is `_0 = const 7_i32;` | **`0` bytes** (align 1) | `fake_read` non-capture | `SZ_WILD.1 = 0` |
| `closure#7`: `\|\| { let _ = &p3; 8 }` | 2024 | `debug p3 => (*((*_1).0: &Pair))`, emits `PlaceMention(_2)` | **`8` bytes** (align 8) | `&p3` triggers `Borrow` -> captures `&Pair` | `SZ_WILD.2 = 8`, `VW=21` |
| `closure#8`: `move \|\| sm.copy_n + 1` (`SplitMove { copy_n: u64, owned: String }`) | 2024 | `debug sm__copy_n => ((*_1).0: u64)` | `8` bytes (align 8) | Copies/moves only `copy_n`; `sm.owned` unmoved! | `SZ_MOVE_COPY=8 VMOVE_COPY=78 SM_OWNED_LEN=6` |
| Same `move \|\| sm.copy_n + 1` followed by `sm.owned.len()` | **2018** | Whole `sm` moved into closure | Compile error | Rejected by moveck | `error[E0382]: borrow of moved value: sm` |
| `closure#9`: `\|\| r_target.a + 1` (`r_target: &BigRefTarget`) | 2024 | `debug r_target => (*((*_1).0: &BigRefTarget))`, loads `((*((*_1).0: &BigRefTarget)).0: u64)` | `8` bytes (align 8) | Rightmost shared-deref truncation stops at `&BigRefTarget` | `SZ_TRUNC_SHARED=8 VTRUNC=124` |

Three MIR observations in `probe_results.json` directly confirm the primary-source analysis:

1. **Zero-byte wildcard vs. `PlaceMention` in `closure#5..7`**: Both `let _ = p3;` (`closure#5`) and `let _ = p3.a;` (`closure#6`) optimize to pure `0`-byte ZST closures returning constants with zero upvar fields (`bb0: { _0 = const 6_i32; return; }`). By contrast, `let _ = &p3;` (`closure#7`) captures `(*((*_1).0: &Pair))` (`8` bytes) and executes `PlaceMention(_2)` in `bb0` (with an unreachable `FakeRead(ForMatchedPlace(None), _2)` in `bb1`), proving that taking the reference—even to discard it—turns a non-capturing read into an `8`-byte immutable borrow capture.
2. **Partial copy/move splitting in `closure#8`**: Look at `main::{closure#8}` MIR signature: `_1: &{closure@...}`, `debug sm__copy_n => ((*_1).0: u64)`. Even under `move ||`, `rustc` creates an `8`-byte closure holding only the `u64` copy, leaving the `24`-byte `String` field `sm.owned` untouched and usable on the parent stack (`SM_OWNED_LEN=6`).
3. **`truncate_capture_for_optimization` at the deref boundary in `closure#9`**: Although `BigRefTarget` is `72` bytes (`buf: [u8; 64]` + `a: u64`) and the closure only reads `r_target.a`, the closure debug local is `debug r_target => (*((*_1).0: &BigRefTarget))` and its MIR instruction projects `.0` (`_2 = copy ((*((*_1).0: &BigRefTarget)).0: u64)`). Instead of forming an interior borrow `&r_target.a`, `truncate_capture_for_optimization` truncated the path to `*r_target`, storing the `&BigRefTarget` pointer itself (still `8` bytes).

---

### 2. Async / Coroutine `StateTransform` State Machine & Variant Packing Layout

```text
Basis: source (ty/sty.rs, coroutine*, mir/query.rs, layout/coroutine.rs) + execution (rustc 1.98.0-nightly MIR & runtime probes) + derived
```

#### 2.1 Discriminant Encoding, Panic-Poisoning & Drop Semantics

In `compiler/rustc_middle/src/ty/sty.rs` (`14210df0e:78-144`, `960ba7cf7:84-150`), `CoroutineArgsExt` fixes the discriminant tag scheme:

- `const UNRESUMED: usize = 0;` (`UNRESUMED_NAME = "Unresumed"`)
- `const RETURNED: usize = 1;` (`RETURNED_NAME = "Returned"`)
- `const POISONED: usize = 2;` (`POISONED_NAME = "Panicked"`)
- `const RESERVED_VARIANTS: usize = 3;`
- Any suspension point index `k` receives discriminant `3 + k` and diagnostic name `format!("Suspend{}", k)`.
- `variant_range` covers `0 .. tcx.coroutine_layout(def_id, self.args).unwrap().variant_fields.next_index()`, and `discriminant_for_variant` assigns scalar value `variant_index.as_usize() as u128`. Note that while `discr_ty` helper returns `tcx.types.u32` (`sty.rs:143` / `sty.rs:149`), actual in-memory tag sizing inside `rustc_abi/src/layout/coroutine.rs:184-192` uses `Integer::fit_unsigned((variant_fields.len() - 1) as u128)`, packing states `0..4` into a **`1`-byte** discriminant (`u8` width) as measured by `-Zprint-type-sizes`.

`StateTransform` transforms the coroutine body in `create_coroutine_resume_function` (`coroutine.rs:1223-1280` in `14210df0e`; `coroutine/mod.rs:877-945` in `960ba7cf7`):

1. **Unwind Poisoning (`generate_poison_block_and_redirect_unwinds_there`)**: When `can_unwind` is true (`coroutine.rs:1195-1220` in `14210df0e`), `StateTransform` appends a basic block `poison_block` executing `StatementKind::SetDiscriminant { place: self_ref, variant_index: CoroutineArgs::POISONED }` and terminating with `TerminatorKind::UnwindResume`. Every existing `UnwindResume` terminator (other than `poison_block`) is rewritten to `Goto { target: poison_block }`, and every non-cleanup block terminator with `UnwindAction::Continue` is rewritten to `UnwindAction::Cleanup(poison_block)`.
2. **Entry `SwitchInt` Dispatch**:
   - `UNRESUMED (0)` -> `START_BLOCK`.
   - `POISONED (2)` (when `can_unwind`) -> `insert_panic_block(..., AssertKind::ResumedAfterPanic(..))` (or `insert_poll_pending_block` if `-Z async-panic=false` on `960ba7cf7`).
   - `RETURNED (1)` (when `can_return`): `AsyncGen`/`Gen` insert a `None` return (`Poll::Ready(None)` / `Complete(())`); `Async drop_in_place` glue inserts `Poll::Ready(())`; user `Async`/`Coroutine` inserts `insert_panic_block(..., AssertKind::ResumedAfterReturn(..))` (again gated on `tcx.sess.opts.unstable_opts.async_panic` in `960ba7cf7`).
   - `SuspendK (3 + k)` -> jumps to the resume basic block for suspension point `k`, swapping `SetDiscriminant` transitions upon every `Yield` (`-> SuspendK`) or `Return` (`-> RETURNED`).
   - Any out-of-range discriminant jumps to `TerminatorKind::Unreachable`.
3. **Coroutine Drop Shim (`drop.rs` / `create_coroutine_drop_function`)**: Each variant (`UNRESUMED`, `SuspendK`) has its own drop-cleanup trace generated by `create_cases(..., Operation::Drop)`. States `RETURNED (1)` and `POISONED (2)` execute **zero** saved-local drops because any local live across an unwinding cleanup path was already dropped during stack unwinding before reaching `poison_block`.

Empirical execution (`b_async_coroutine_state_layout_and_unpin::panic_poisoning_and_repoll_traps`) confirms these state transitions directly on `rustc 1.98.0-nightly`:
- First poll drops `0` guards and returns `Pending` (`FIRST_POLL=Pending`, entering `Suspend0 (3)`).
- Second poll panics with `"boom_mid_async"`, unwinding the live `DropCounter` guard once (`DROPS=(0,1,1)` after catch), transitioning the discriminant to `POISONED (2)`.
- Third poll (re-polling poisoned future) traps immediately with `"async fn resumed after panicking"`, leaving drop count at `1`.
- Explicitly dropping the poisoned `Pin<Box<_>>` runs `0` additional drops (`DROPS=(0,1,1)`), proving idempotence in `POISONED`.
- Completing a separate future returns `Poll::Ready(42)` (`RETURNED (1)`), and re-polling it traps with `"async fn resumed after completion"`.

#### 2.2 Liveness-Conflict Graph & Two-Pass Variant Packing (`coroutine/layout.rs`, `rustc_abi/src/layout/coroutine.rs`)

`compute_layout` (`coroutine.rs:967-1075` in `14210df0e`, `coroutine/layout.rs:344-455` in `960ba7cf7`) computes `CoroutineLayout`:
- `variant_fields[v]`: for every `v >= RESERVED_VARIANTS` (`Suspend0`, `Suspend1`, ...), the set of MIR locals appearing in `live_locals_at_suspension_points` (while `Unresumed(0)`, `Returned(1)`, `Panicked(2)` have `variant_fields[v] = []`).
- `storage_conflicts`: a symmetric `BitMatrix<CoroutineSavedLocal, CoroutineSavedLocal>` capturing every pair `(l1, l2)` that is storage-live simultaneously (`StorageLive`..`StorageDead` overlap, checked conservative liveness across basic blocks).

Layout packing then runs `coroutine_saved_local_eligibility` (`rustc_abi/src/layout/coroutine.rs:62-156` in `960ba7cf7`, `42-136` in `14210df0e`):
- **Pass 1 (Variant Uniqueness)**: Iterates `variant_fields`. Any local appearing in `<= 1` variant receives `Assigned(v)` (or `Unassigned` if `0`, which cannot happen for reachable `saved_locals`). Any local appearing in `> 1` variant becomes `Ineligible(None)` and is marked for **prefix promotion** (`ineligible_locals`).
- **Pass 2 (Cross-Variant Conflict Resolution)**: Iterates `(local_a, local_b)` in `storage_conflicts` where neither is already ineligible and `assignments[local_a] != assignments[local_b]`. Because locals in *different* variants could overlap in the union if both stayed variant-specific, one of the two must be promoted to the shared prefix so their storage cannot alias while both are `StorageLive`. `rustc` uses a conflict-degree greedy tiebreaker (`if conflicts_a > conflicts_b { local_a } else { local_b }`, `layout/coroutine.rs:118-122`), making the winner ineligible.
- **Degenerate Single-Variant Collapse (`used_variants.count() < 2`)**: If fewer than `2` variants retain any `Assigned(v)` local, variant overlapping is impossible, so all remaining `Assigned` locals are promoted to `Ineligible` so `layout_of_univariant` can reorder fields aggressively to minimize struct padding (`layout/coroutine.rs:132-145`).
- **Two-Stage Physical Layout (`layout/coroutine.rs:159-250`)**:
  1. `prefix` lays out captures + `tag` (`Scalar::Initialized` with range `0..=max_discr`) + all `ineligible_locals` via `univariant`.
  2. Each variant `v` lays out ONLY `Assigned(v)` locals starting after `prefix_size` (`variant_only_tys`), allowing distinct variants' `Assigned` slots to **reuse the exact same byte offsets**.

Our live probes on `rustc 1.98.0-nightly` verify this packing with exact `-Zdump-mir=StateTransform` and `-Zprint-type-sizes` output:

1. **Sequential Non-Overlapping Async Blocks (`seq_non_overlapping`, `SEQ_SIZE = 67`, `align = 1`)**:
   Two distinct `[u8; 64]` temporaries `a` and `b` live only across disjoint `.await` points (`Suspend0` vs. `Suspend1`), separated by `StorageDead(a)` before `StorageLive(b)`, while `acc1: u8` (`_s0`) becomes `StorageLive` at function entry and is read in `Suspend1`.
   - `StateTransform.after.mir` reports:
     ```text
     coroutine layout {
         field _s0: u8;
         field _s1: [u8; 64];
         field _s2: YieldOnce;
         field _s3: [u8; 64];
         field _s4: YieldOnce;
         variant_fields = {
             Unresumed(0): [],
             Returned (1): [],
             Panicked (2): [],
             Suspend0 (3): [_s1, _s2],
             Suspend1 (4): [_s0, _s3, _s4],
         }
         storage_conflicts = BitMatrix(5x5) {
             (_s0, _s0), (_s0, _s1), (_s0, _s3), (_s0, _s4),
             (_s1, _s0), (_s1, _s1), (_s1, _s2),
             (_s2, _s1), (_s2, _s2),
             (_s3, _s0), (_s3, _s3), (_s3, _s4),
             (_s4, _s0), (_s4, _s3), (_s4, _s4)
         }
     }
     ```
   - Notice why `_s0` (`acc1`, 1B) is promoted to the **prefix**! Although `_s0` only appears in `Suspend1` (`variant_fields[4]`), its MIR `StorageLive` begins in `bb0` *before* `Suspend0`, so `storage_conflicts` contains `(_s0, _s1)` across variants `4 != 3`! Because `_s0` conflicts with `4` entries (`0,1,3,4`) while `_s1` conflicts with only `3` (`0,1,2`), Pass 2 promotes `_s0` to prefix, occupying offset `1` (right after `1B` discriminant at offset `0`). Meanwhile, `_s1` and `_s3` (the two `64`-byte buffers) and `_s2`/`_s4` (`1`-byte `YieldOnce` futures) have **zero** cross-variant entries between `{_s1, _s2}` and `{_s3, _s4}`.
   - `-Zprint-type-sizes` confirms total size **`67` bytes** (`1B` discriminant + `1B` `.acc1` prefix + `1B` `.__awaitee` + `64B` buffer overlapped between `Suspend0` and `Suspend1`)! Notice `-Zprint-type-sizes` prints `Suspend0: 66 bytes (padding: 1 byte, .__awaitee: 1 byte, .a: 64 bytes)` and `Suspend1: 66 bytes (.acc1: 1 byte, .__awaitee: 1 byte, .b: 64 bytes)`, where `Suspend0`'s 1-byte "padding" inside the variant view reflects the skipped prefix slot occupied by `.acc1` (`1B` `.acc1` + `1B` `.__awaitee` + `64B` = `66` bytes after the `1B` tag -> **`67` bytes total**).

2. **Concurrently Live Across `.await` (`live_across_overlapping`, `OVL_SIZE = 131`, `align = 1`)**:
   Both `a: [u8; 64]` (`_s0`) and `b: [u8; 64]` (`_s1`) are live simultaneously across `Suspend0` and `Suspend1`:
   - `variant_fields`: `Suspend0(3): [_s0, _s1, _s2]`, `Suspend1(4): [_s0, _s1, _s3, _s4]`.
   - `_s0` and `_s1` appear in `> 1` variant, fail Pass 1 -> `Ineligible`, and get promoted to prefix without overlap, yielding **`131` bytes** (`1B` discriminant + `64B` `.a` + `64B` `.b` + `1B` `.v1` + `1B` `.__awaitee`).

3. **Self-Referential Async Frame (`self_ref_across_await`, `SELF_REF_SIZE = 80`, `align = 8`) & `!Unpin` Enforcement**:
   Holding `rx: &u8 = &x[0]` across `.await` places `_s0: [u8; 64]`, `_s1: &u8`, and `_s2: YieldOnce` all in `Suspend0(3)`. `-Zprint-type-sizes` reports:
   - Total `80` bytes, `alignment: 8 bytes` (`1B` discriminant, `Suspend0`: `.x: 64 bytes` at `offset: 0`, `.rx: 8 bytes`, `.__awaitee: 1 byte`, `6` bytes end padding to multiple of `8`).
   - Evaluating `fut_self_ref` against `fn require_unpin<T: Unpin>` triggers compile error `error[E0277]: '{async block@...}' cannot be unpinned`, whereas a `#[coroutine]` without cross-yield internal references automatically implements `Unpin` and runs cleanly via `Pin::new(&mut gen_coro).resume(())`, producing `MOVABLE_UNPIN=(Yielded(11),Complete(13))`.

---

### 3. Downstream Verification Implications in `joshlf/anneal`

```text
Basis: source (joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613, trusted/lean/Trusted/MirAst.lean) + derived
```

Direct inspection of `trusted/lean/Trusted/MirAst.lean` at `joshlf/anneal` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes exact fail-closed boundaries where `Anneal`'s typed MIR subset currently rejects both closure environments and coroutine state machines:

| `rustc_middle::mir` Construct | `Trusted/MirAst.lean` Line(s) | Lowering Status in `c131b320e` | Semantic Implication |
| :--- | :--- | :--- | :--- |
| `TyKind::{Closure, CoroutineClosure, Coroutine, CoroutineWitness}` | `MirAst.lean:285-287, 308-311, 321` | `MirTy.unsupported` | Any function whose local table, signature, or captured upvar struct mentions a closure or coroutine type fails closed with `FaultKind.unsupported`. |
| `Rvalue::Aggregate(Closure / Coroutine, _)` | `MirAst.lean:612-618, 628` | `Rvalue.unsupported` | Constructing a closure capture struct or coroutine aggregate cannot step cleanly; only `AggregateKind::Tuple` lowers (`Rvalue.aggregateTuple`). |
| `StatementKind::{SetDiscriminant, FakeRead, PlaceMention}` | `MirAst.lean:636-640, 654-656, 662` | `StatementKind.unsupported` | Both wildcard `PlaceMention`/`FakeRead` statements in RFC 2229 closures and `StateTransform`'s discriminant transitions (`SetDiscriminant`) reject fail-closed rather than silently dropping transitions. |
| `AssertKind::{ResumedAfterReturn, ResumedAfterPanic, ResumedAfterDrop}` | `MirAst.lean:709-711, 727-729, 740` | `AssertKind.unsupported` | Trap assertions inserted for invalid coroutine re-polls (`POISONED`/`RETURNED`) do not yet carry dedicated trap predicates in `MirAst.AssertKind`. |
| `TerminatorKind::{Yield, CoroutineDrop}` and indirect `Call` | `MirAst.lean:762-763, 782-784, 795` | `TerminatorKind.unsupported` | Both pre-`StateTransform` coroutine bodies (`Yield`, `CoroutineDrop`) and indirect `Fn`/`FnMut`/`FnOnce` shim calls reject fail-closed. |

**Derived conclusion**: Admitting closures into a verified MIR semantics cleanly without re-implementing `rustc_hir_typeck` requires ingesting **post-capture, post-RFC-2229 lowered MIR** where each closure's captured environment has already been resolved into explicit struct fields (`CapturedPlace` fields in the closure upvar aggregate) and `FakeRead`/`PlaceMention` no-ops are either admitted as memory no-ops (`FakeRead` preserves non-aliasing) or erased post-borrowck. Admitting `async fn` / `#[coroutine]` similarly requires targeting **post-`StateTransform` MIR**, extending `MirTy` with discriminated variant-union coroutine layouts whose variant field offsets respect `storage_conflicts` (`SetDiscriminant`, variant field projections, and `Pin<&mut Coroutine>` address-stability hypotheses), and adding explicit poison/returned trap semantics (`AssertKind::ResumedAfterPanic`/`ResumedAfterReturn`).

---

### 4. Kernel-Checked Lean `v4.34.1` Formalization

```text
Basis: source (support/ClosureRfc2229AndCoroutineStateLayoutSoundness.lean) + execution (Lean v4.34.1 compiler & MetaM audit)
```

`support/ClosureRfc2229AndCoroutineStateLayoutSoundness.lean` (`2,840` lines, `566` `noncomputable def` definitions, `278` theorems, compiling with zero warnings and zero errors under `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) mechanizes both compiler subsystems cleanly inside Lean `v4.34.1` using **only** `prelude` plus `Init.Core`, `Init.NotationExtra`, `Init.SimpLemmas`, `Init.Tactics`, `Init.Data.Nat.Basic`, `Init.Data.List.Basic`, `Init.Data.List.Notation`, and `Init.Data.Option.Basic`.

#### 4.1 Lean Constructive Purity Guarantees (Verified via MetaM AST Inspection)

To eliminate kernel trust leaks and recursive compiler extraction artifacts (`._unsafe_rec`), the file obeys strict syntactic and MetaM constraints:
- **Zero `partial def`, zero `unsafe`, zero `opaque`, zero custom `axiom`**: Every function definition is structurally recursive with explicit `noncomputable def` annotation (avoiding `noncomputable section`, which does not suppress `_unsafe_rec` generation). Structural equality checks use explicit hand-written `.beq` functions paired with soundness theorems (`.beq_eq`, `.beq_refl`) rather than `deriving DecidableEq` / `deriving Repr`.
- **Forbidden tactics absent**: `0` uses of `sorry`/`sorryAx`, `0` uses of `Classical.choice`, `0` uses of `omega`, `0` uses of `bv_decide`, and `0` uses of `native_decide`. Concrete finite counterexamples (e.g., inequality `0x1000 ≠ 0x2000 + 0` in `forged_unpin_breaks_self_ref_witness`) reduce in **O(1)** via `(nat_beq_true_iff _ _).2 hptr` and kernel `rfl` on `Nat.beq`, avoiding unary `Nat.noConfusion` stack blowup (`maxRecDepth`).
- **MetaM Environment Audit Result**: Adding `958` declarations (`278` theorems, `566` definitions), MetaM inspection over `env.constants` verifies `UNSAFE_RECS=0`, `CUSTOM_AXIOMS=0`, `OPAQUE_OR_UNSAFE=0`, `FORBIDDEN_AXIOMS=0`, and `#print axioms` on all main theorems & witnesses depends strictly on `[propext]` or `[propext, Quot.sound]` (with two purely computational witnesses depending on **zero** axioms `[]`).

#### 4.2 Mechanized Theorems & Specifications

1. **Main Theorem 1 — `rfc2229_disjoint_capture_and_prefix_truncation_soundness`** (axioms: `[propext, Quot.sound]`):
   Conjoins seven verified properties over `CapturePlace { rootVar : Nat; projs : List ProjElem }`, `UpvarCapture`, `ClosureKind`, `LayoutTree`, `ByteRange`, and `MinCaptureList` (`insertMinCapture` / `computeMinCaptures`):
   - **Prefix truncation soundness**: Both `truncateCaptureForOptimization` and `restrictCapturePrecision` strictly produce a prefix (`isProjPrefix p'.projs p.projs = true`) of the original accessed projection path.
   - **`move ||` direct field preservation**: For any `p` with no `Deref` projections (`listAny ProjElem.isDeref p.projs = false`), `adjustForMoveClosure p k` preserves `p` verbatim as `(p, .byValue)`, ensuring non-`Copy` siblings are never pulled into the capture set.
   - **Divergent field byte-slice non-interference (`divergent_field_places_disjoint`)**: Whenever `determinePlaceAncestry p1 p2 = .divergent`, any resolved concrete field paths `extractFieldPath p1.projs = some fs1` / `fs2` inside any `LayoutTree` resolve either to distinct root locals or strictly non-overlapping byte intervals (`sliceDisjoint`: `root1 ≠ root2 ∨ r1.offset + r1.size ≤ r2.offset ∨ r2.offset + r2.size ≤ r1.offset`).
   - **Wildcard non-capture**: `collectEdition2021Uses (.fakeRead p :: rest) = collectEdition2021Uses rest`.
   - **Sibling invariance of `computeMinCaptures`**: Inserting any set of uses all divergent from an external place `q` guarantees every entry in the minimized capture list remains strictly divergent from `q`.
   - **`UniqueImmutable` downgrade & trait consequence**: `UpvarCapture.toClosureKind (.byRef .uniqueImmutable) = .fnMut` and `BorrowKind.toMutblLossy .uniqueImmutable = .mut`.

2. **Main Theorem 2 — `coroutine_determinism_and_poison_trap_invariant`** (axioms: `[propext]`):
   Models `CoroVariantTag` (`unresumed`/`returned`/`panicked`/`suspend k`), `discrOfVariant` (`0/1/2/3+k`) / `variantOfDiscr` bijection, `stepPoll` (including `canUnwind` and `asyncPanic` switches), `runPolls`, and `dropCoro`:
   - `variantOfDiscr (discrOfVariant v) = v` (and injectivity `discrOfVariant_inj`).
   - Single-step transition determinism (`stepPoll_deterministic`).
   - Arbitrary re-poll trace invariance from `discr = 2` (`POISONED`): state stays fixed at `st` and every step emits `.panicPoisonTrap` (`poisoned_repoll_trace_stays_poisoned`).
   - Terminal drop idempotence: `dropCoro` in both `discr = 2` (`POISONED`) and `discr = 1` (`RETURNED`) leaves state unchanged with `0` additional drops executed (`dropCoro_poisoned_zero_drops`, `dropCoro_returned_zero_drops`), complemented by `unwind_then_repoll_and_drop_exact_once` proving exact-once cleanup across `Unresumed -> Unwind(Poisoned) -> Repoll(Trap) -> Drop(No-op)`.

3. **Main Theorem 3 — `conflict_graph_non_overlapping_packing_safety` & `colive_at_suspend_non_overlapping`** (axioms: `[propext, Quot.sound]`):
   Models `CoroutineLayoutInput` (`discrSize`, `savedLocals`, `variantFields`, symmetric `conflicts`), two-pass eligibility (`pass1Elig` + `crossVariantConflict` + `assignEligibility`), prefix/variant sequential packing (`packSeqFrom`, `packCoroutineLayout`), and slot lookup (`assignedSlotFor`):
   - **Conflict-graph packing safety**: For any `WellFormedCoroLayoutInput inp` (`pairwiseDistinct` local IDs, every co-live pair in any variant satisfies `conflicts = true`, and every variant field appears in `savedLocals`) and any distinct conflicting locals `s1, s2` (`inp.conflicts s1.localId s2.localId = true`), both locals receive concrete placed slots `sl1, sl2` starting at or past `inp.discrSize` with strictly disjoint byte intervals (`rangesDisjoint sl1.range sl2.range`).
   - **Co-live variant corollary (`colive_at_suspend_non_overlapping`)**: Any two distinct locals simultaneously present in the same suspend point `variantFields[v]` never alias in memory.

4. **Main Theorem 4 — `self_referential_pinning_stability_invariant` & Negative Counter-Witness** (axioms: `[propext]`, `[propext]`):
   Models `PinCoroMem` (`baseAddr`, `frameSize`, `unpinFlag`, `pinned`, `dropped`, `selfRefTargetOff`, `storedSelfPtr`) and `execPinAction` (`pinFrame`, `initSelfRef`, `pollResume`, `safeMutMove`, `dropFrame`):
   - **Positive invariant**: Over any finite non-drop trace on a valid pinned `!Unpin` frame (`unpinFlag = false`, `pinned = true`), `baseAddr`, `unpinFlag = false`, `pinned = true`, and `selfRefValid` (`ptr = m.baseAddr + off` with `off < frameSize`) are strictly preserved (because any `safeMutMove` fails closed to `none`).
   - **Explicit negative counter-witness (`forged_unpin_breaks_self_ref_witness`)**: Starting at `baseAddr := 0x1000` (`frameSize := 80`) with `unpinFlag := true`, the 2-step trace `[.initSelfRef 0, .safeMutMove 0x2000]` succeeds and leaves `storedSelfPtr = some 0x1000`, `baseAddr = 0x2000`, and `¬ selfRefValid mFinal` (dangling interior self-pointer!).

5. **Concrete Kernel-Reduced Witnesses Matching `rustc 1.98.0-nightly` Probes**:
   - `edition2024_pair_disjoint_witness` (`placePA` vs. `placePB` = `.divergent`) & `edition2024_pair_ranges_disjoint_witness` (`Pair` bytes `[0, 4)` vs. `[4, 28)` — axioms: `[]`).
   - `wildcard_vs_ref_witness` (`fakeRead` length `0` vs. `borrow` length `1` — axioms: `[]`).
   - `move_split_copy_field_witness` (`adjustForMoveClosure` preserves `.field 0` and stays divergent from `.field 1` — axioms: `[propext]`).
   - `shared_deref_truncation_witness` (`truncateCaptureForOptimization` truncates `[.derefShared, .field 0]` to `[.derefShared]` — axioms: `[propext]`).
   - `unique_immutable_truncation_witness` (`truncatePlaceAndUpdateKind` converts `[.derefMut]` + `.byRef .mutable` -> `[], .byRef .uniqueImmutable` — axioms: `[propext]`).
   - `seq_coro_overlap_packing_witness` (`(packCoroutineLayout seqCoroInput).2.2 = 67`, with both `localId = 1` in variant `3` and `localId = 3` in variant `4` placed at `{ offset := 2, size := 64 }`, overlapping cleanly after the `1`-byte discriminant and `1`-byte prefix `acc1` — axioms: `[propext]`).
   - `ovl_coro_full_conflict_witness` (`(packCoroutineLayout ovlCoroInput).2.2 = 131`, placing `localId = 0` at `offset := 1` and `localId = 1` at `offset := 65` — axioms: `[propext]`).

## Boundaries

Every limit below uses the corpus's negative-space distinctions (`not examined`, `unknown`, `known not to apply`, `unsupported`):

1. **`known not to apply` — Lean Tiebreaker vs. `rustc` Conflict-Degree Heuristic in Pass 2**:
   In Pass 2 of `coroutine_saved_local_eligibility` (`rustc_abi/src/layout/coroutine.rs:118-122`), `rustc` resolves a cross-variant conflict between `local_a` and `local_b` by promoting whichever local has strictly **more** conflicts in `storage_conflicts` (`conflicts_a > conflicts_b`). The Lean formalization instead breaks ties deterministically by `Nat.ble l1 l2` (`localId` ordering in `hasCrossConflictWinner`). Because both tiebreakers promote at least one endpoint of every cross-variant conflict edge (and `seqCoroInput` gives `0` both lowest ID `0 < 1,3,4` and highest conflict degree `4 > 2`), both pack `seqCoroInput` to `67` bytes and satisfy `conflict_graph_non_overlapping_packing_safety`. However, arbitrary conflict graphs with non-monotone ID/degree correlation can promote different victims and thus yield different non-minimal frame sizes while still preserving safety.
2. **`known not to apply` — Field Alignment & Univariant Reordering Inside Variant Packing**:
   The Lean model stores `align : Nat` in `SavedLocalSpec` for specification fidelity, whereas `packSeqFrom` packs slots contiguously by byte size (`cursor + s.size`) without alignment rounding or niche/size-descending struct reordering. Real `rustc` (`layout/coroutine.rs:194-250`) runs `calc.univariant`, which reorders fields (`in_memory_order`) and inserts alignment padding (as observed in `SELF_REF_SIZE = 80` = `1B` discr + `64B` + `8B` + `1B` + **`6B` end padding** for `align = 8`).
3. **`known not to apply` — Monotonicity of `UpvarCapture.toClosureKind` Under `ByUse`**:
   Because `ByUse` ranks above `ByRef` in `UpvarCapture::partial_cmp` (`upvar.rs:2613`) yet leaves `ClosureKind` unchanged in `process_collected_capture_information` (`upvar.rs:757-781`, since `adjust_for_use_closure` executes post-inference), `UpvarCapture.toClosureKind_monotone` holds only under explicit hypothesis `a ≠ .byUse`.
4. **`unsupported` — `joshlf/anneal` MIR Ingestion of Closures & Coroutines (`c131b320e`)**:
   `Trusted/MirAst.lean` lowers `Closure`, `Coroutine`, `CoroutineWitness`, `CoroutineClosure`, `SetDiscriminant`, `FakeRead`, `PlaceMention`, `Yield`, `CoroutineDrop`, and coroutine `AssertKind` variants to `.unsupported`, causing fail-closed verification rejection rather than unsoundness or support.
5. **`not examined` — Execution of `rustc` `main` (`960ba7cf7`) Binary Flags (`-Z async-panic=false`, `PackCoroutineLayout::CapturesOnly`, `move(expr)` / `use ||`)**:
   Revision `960ba7cf7` was audited by primary source inspection rather than compiled/executed as a compiler binary. Consequently, runtime effects of `-Z async-panic=false` (returning `Poll::Pending` instead of trapping on `POISONED`/`RETURNED`), experimental size reductions under `PackCoroutineLayout::CapturesOnly`, and codegen edge cases of `explicit_captures` (`move(expr)`) or `use ||` closures remain unexecuted here.
6. **`not examined` — `gen` / `async gen` Iterator Resumption, `panic = "abort"`, and Miri Runtime Aliasing**:
   Source inspection confirms `Gen`/`AsyncGen` emit `None` rather than trapping when resumed in `RETURNED` (`coroutine/mod.rs:927-931`), and drop shims skip `PIN` (`make_coroutine_state_argument_pinned` applies only to `Coroutine`/`Async`/`AsyncGen`, `mod.rs:938-946`), while `can_unwind = false` (`panic = "abort"`) omits poison-block generation (`mod.rs:885-909`); none of those runtime modes were executed under probes in this package. Stacked/Tree Borrows aliasing interaction with self-referential `!Unpin` frames (`UnsafePinned` vs. `MaybeDangling` wrappers) was also not re-run under Miri in this study.
7. **Formal Model vs. Whole-Compiler Verification Boundary**:
   The Lean `v4.34.1` theorems establish internal soundness, safety, and determinism of the formal models distilled from `upvar.rs`, `ty/closure.rs`, `coroutine*`, and `rustc_abi/src/layout/coroutine.rs`; they do not constitute a machine-checked extraction proof of the full Rust compiler binary itself.

## Evidence

### 1. Primary Source Inventory

| Repository | Full Commit SHA | Path | Symbol / Line Range Examined | Key Fact Established |
| :--- | :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_hir_typeck/src/upvar.rs` | `fake_read` (`2100`), `restrict_capture_precision` (`2262-2288`), `adjust_for_move_closure` (`2292-2303`), `determine_place_ancestry_relation` (`2581-2612`), `truncate_capture_for_optimization` (`2643-2663`), `enable_precise_capture` (`2667-2671`) | `rustc 1.98.0-nightly` RFC 2229 wildcard skip, index/raw/union precision bounds, move direct-field preservation, ancestry comparison, rightmost shared-deref trim |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_hir_typeck/src/upvar.rs` | `explicit_captures` (`96,133,295-296,404`), `process_collected_capture_information` (`733-804`), `fake_read` (`2216`), `restrict_capture_precision` (`2378-2404`), `adjust_for_move_closure` (`2408`), `determine_capture_info` (`2608-2625`), `determine_place_ancestry_relation` (`2665`), `truncate_capture_for_optimization` (`2727`) | `ClosureKind` inference runs BEFORE `adjust_for_{move,use,non_move}_closure`; `ByUse`/`ByValue` partial ordering vs. trait rank |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_middle/src/ty/closure.rs` | `UpvarCapture` (`49`), `CapturedPlace` (`96`), `BorrowKind` (`374-428`), `BorrowKind::to_mutbl_lossy` (`442-452`) | Definition of `UniqueImmutable` and lossy upgrade to `hir::Mutability::Mut` (`&mut`) |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` & `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_middle/src/ty/sty.rs` | `CoroutineArgsExt` (`77-159` / `83-160`: `UNRESUMED=0`, `RETURNED=1`, `POISONED=2`, `RESERVED_VARIANTS=3`, `POISONED_NAME="Panicked"`, `variant_name`, `discr_ty`) | Authoritative discriminant index assignment across both `rustc` revisions |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/coroutine.rs` | `compute_layout` (`967-1075`), `insert_panic_block` (`1148`), `generate_poison_block_and_redirect_unwinds_there` (`1195-1220`), `create_coroutine_resume_function` (`1223-1280`) | Single-file coroutine transform emitting unconditional `ResumedAfterPanic`/`ResumedAfterReturn` panic blocks |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_mir_transform/src/coroutine/{mod.rs, layout.rs}` | `create_coroutine_resume_function` (`mod.rs:877-945`), `async_panic` gating (`mod.rs:902-925`), `compute_layout` (`layout.rs:344+`) | Modularized coroutine transform with `-Z async-panic` (`true` default) gating |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` & `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_middle/src/mir/query.rs`, `compiler/rustc_abi/src/layout/coroutine.rs` | `CoroutineLayout` (`query.rs:35-56` / `38-61`), `PackCoroutineLayout` (`layout/coroutine.rs:44-51` in `main`), `coroutine_saved_local_eligibility` (`42-136` / `62-156`), `layout` (`139+` / `159-250`) | Two-pass liveness-conflict packing, `< 2` variant collapse, scalar tag sizing (`Integer::fit_unsigned`), univariant prefix + variant union packing |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` | `MirTy` (`285-321`), `Rvalue` (`612-628`), `StatementKind` (`636-662`), `AssertKind` (`709-740`), `TerminatorKind` (`762-795`) | Fail-closed `.unsupported` lowering boundaries for closures & coroutines |

### 2. Preserved Package Support Artifacts (`2026-11-23`)

| Relative Path | Lines | Size (Bytes) | SHA-256 Digest | Contents & Verification Status |
| :--- | ---: | ---: | :--- | :--- |
| `support/probe_closure_rfc2229_and_coroutine_layout.py` | `569` | `17,595` | `2413a4bd8915defbfbb0fc16a69a9f3db3386e102ba04bcc251c75246b6dab8f` | Self-contained probe harness executing all RFC 2229 & coroutine MIR/size/runtime/negative tests inside `tempfile.TemporaryDirectory()`. Executed cleanly (`exit 0`). |
| `support/probe_results.json` | `125` | `105,781` | `91be1b82779fed9e0874019f4cb752a6cc990056a3222ead295ff662e908ba6d` | Captured `rustc 1.98.0-nightly (14210df0e 2026-05-31)` version metadata, full MIR dumps (`built`, `StateTransform.before`, `StateTransform.after`), filtered `-Zprint-type-sizes` records, runtime stdout (`A=10 ...`, `SEQ_SIZE=67 OVL_SIZE=131 SELF_REF_SIZE=80 ...`, `DROPS=(0,1,1)`), and verbatim diagnostics (`E0502`, `E0382`, `E0525`, `E0277`). |
| `support/ClosureRfc2229AndCoroutineStateLayoutSoundness.lean` | `2,840` | `103,498` | `540c2fc9a3196715c4664fa8cb7ee765af0518a583407f5d2c9234c28a752d3e` | Standalone Lean `v4.34.1` kernel-checked formalization (`MOD_DECLS=958`, `THEOREMS=278`, `DEFS=566`, `UNSAFE_RECS=0`, `CUSTOM_AXIOMS=0`, `OPAQUE_OR_UNSAFE=0`, `FORBIDDEN_AXIOMS=0`), verified with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`). |

### 3. Selected Verbatim Empirical Receipts (`rustc 1.98.0-nightly`)

- **Experiment A stdout (`edition_2024_disjoint_and_traits_ok`)**:
  `A=10 B=hi! STAY_LEN=4 SZ_CAP_C=8 VC=99 SZ_MUT_A=8 VMUT=15 SZ_UNIQ=8 VUNIQ=8 VONCE=7 SZ_WILD=(8,0,0) VW=21 P3_LEN=4 SZ_MOVE_COPY=8 VMOVE_COPY=78 SM_OWNED_LEN=6 SZ_TRUNC_SHARED=8 VTRUNC=124`
- **Experiment B stdout (`async_state_machine_sizes_mir_and_execution`)**:
  `SEQ_SIZE=67 OVL_SIZE=131 SELF_REF_SIZE=80 SEQ_ALIGN=1 SR_ALIGN=8` / `RES=(10,10,42)`
- **Experiment B stdout (`movable_coroutine_without_self_ref_is_unpin_ok`)**:
  `MOVABLE_UNPIN=(Yielded(11),Complete(13))`
- **Experiment B stdout (`panic_poisoning_and_repoll_traps`)**:
  `FIRST_POLL=Pending DROPS=(0,1,1) PANIC1="boom_mid_async" REPOLL_POISON="async fn resumed after panicking" DONE_POLL=Ready(42) REPOLL_DONE="async fn resumed after completion"` (exact panic strings wrapped in backticks around `async fn`).
- **Lean `v4.34.1` Axiom Receipts (`#print axioms` via MetaM)**:
  - `rfc2229_disjoint_capture_and_prefix_truncation_soundness`: `[propext, Quot.sound]`
  - `coroutine_determinism_and_poison_trap_invariant`: `[propext]`
  - `conflict_graph_non_overlapping_packing_safety`: `[propext, Quot.sound]`
  - `colive_at_suspend_non_overlapping`: `[propext, Quot.sound]`
  - `self_referential_pinning_stability_invariant`: `[propext]`
  - `forged_unpin_breaks_self_ref_witness`: `[propext]`
  - `edition2024_pair_disjoint_witness`, `move_split_copy_field_witness`, `shared_deref_truncation_witness`, `unique_immutable_truncation_witness`, `seq_coro_overlap_packing_witness`, `ovl_coro_full_conflict_witness`: `[propext]`
  - `edition2024_pair_ranges_disjoint_witness`, `wildcard_vs_ref_witness`: `[]` (`does not depend on any axioms`)

## Revalidation

To cheaply revalidate all empirical, source, and mechanized claims against a newer `rustc` toolchain, upstream `rust-lang/rust` commit, or `joshlf/anneal` commit:

1. **Rerun Live `rustc` Probe Matrix**:
   Run from the report package directory (requires `rustc` with Edition 2024 and `-Zdump-mir`/`-Zprint-type-sizes` nightly support):
   ```bash
   python3 support/probe_closure_rfc2229_and_coroutine_layout.py
   ```
   Check stdout/JSON deltas against the preserved baseline `support/probe_results.json`: `SZ_WILD=(8,0,0)`, `SZ_MOVE_COPY=8`, `SZ_TRUNC_SHARED=8`, `SEQ_SIZE=67`, `OVL_SIZE=131`, `SELF_REF_SIZE=80`, `DROPS=(0,1,1)`, and diagnostics `E0502`, `E0382`, `E0525`, `E0277`. To test `-Z async-panic=false` on post-`960ba7cf7` toolchains, compile `panic_poisoning_and_repoll_traps` with `-C panic=unwind -Z async-panic=false` and observe whether re-polling `POISONED`/`RETURNED` yields `Poll::Pending` rather than panicking.

2. **Re-check Standalone Lean `v4.34.1` Formalization & Zero-`_unsafe_rec` Purity**:
   Verify kernel acceptance without `sorry` or warnings:
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/ClosureRfc2229AndCoroutineStateLayoutSoundness.lean
   ```
   Pair this with a static check confirming zero forbidden constructs (`sorry`, `omega`, `bv_decide`, `native_decide`, `partial `, `noncomputable section`, `deriving `, `Classical`) outside module comments, and optionally compile with `-R support -o /tmp/Soundness.olean` followed by a MetaM `#eval` over `env.constants` verifying `UNSAFE_RECS=0`, `CUSTOM_AXIOMS=0`, and `FORBIDDEN_AXIOMS=0`.

3. **Targeted Upstream Diff Checks (`rust-lang/rust` & `joshlf/anneal`)**:
   Instead of re-auditing entire crates, inspect only diffs touching:
   - `compiler/rustc_hir_typeck/src/upvar.rs` (functions `compute_min_captures`, `restrict_capture_precision`, `truncate_capture_for_optimization`, `adjust_for_move_closure`, `process_collected_capture_information`, `fake_read`) and `compiler/rustc_middle/src/ty/closure.rs` (`BorrowKind::to_mutbl_lossy`);
   - `compiler/rustc_middle/src/ty/sty.rs` (`CoroutineArgsExt` constants `UNRESUMED`/`RETURNED`/`POISONED`/`RESERVED_VARIANTS`), `compiler/rustc_mir_transform/src/coroutine/` (`create_coroutine_resume_function`, `compute_layout`), and `compiler/rustc_abi/src/layout/coroutine.rs` (`coroutine_saved_local_eligibility`, `PackCoroutineLayout`);
   - `joshlf/anneal` `trusted/lean/Trusted/MirAst.lean` (for any new lowering constructors replacing `.unsupported` on `MirTy::{Closure, Coroutine}`, `StatementKind::SetDiscriminant`, `AssertKind::ResumedAfter*`, or `TerminatorKind::{Yield, CoroutineDrop}`).
