# rustc_hir_typeck Coercion Sites, CoerceMany LUB Unification, and Unconditional Never-Type Fallback Soundness

## Summary

Type checking in `rustc_hir_typeck` separates single-site coercions (`Coerce::coerce` producing `Adjust` / `PointerCoercion` steps), multi-arm least-upper-bound (`LUB`) joins (`CoerceMany` and `try_find_coercion_lub`), place-read gating (`expr_guaranteed_to_constitute_read_for_never`), and end-of-body inference fallback (`FnCtxt::type_inference_fallback` and `fallback_types`). Across upstream `rust-lang/rust` HEAD (`5debe6a1244452beced762385f88a51857a915fc`), the `1.102.0-nightly` baseline (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and the `1.98.0-nightly` toolchain (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), five primary structural facts and soundness invariants govern this surface:

1. **Unconditional post-1.100 never-type (`!`) fallback (`compiler/rustc_hir_typeck/src/fallback.rs:88-94`):** While `1.98.0-nightly` splits diverging fallback via `FnCtxt::diverging_fallback_behavior` (`DivergingFallbackBehavior::ToUnit` in Edition 2021 vs. `ToNever` in Edition 2024), both `1.102.0-nightly` (`3ef0c22cd`) and upstream HEAD (`5debe6a12`, whose `fallback.rs` is byte-identical at `27,573` bytes) remove `DivergingFallbackBehavior` and unconditionally unify every unresolved diverging root `TyVid` with `tcx.types.never` (`!`) in both Edition 2021 and Edition 2024. Unit-only bounds (`Default`, custom unit-only traits) that compiled under `1.98.0` Edition 2021 fail with `E0277` post-1.100 unless explicitly typed `()`.
2. **Undirected coercion-graph soundness guard (`never_type_fallback_flowing_into_unsafe`):** Retaining `NEVER_TYPE_FALLBACK_FLOWING_INTO_UNSAFE` as default `Deny` across both eras (`compiler/rustc_lint_defs/src/builtin.rs:4223-4227`), `lint_never_type_fallback_flowing_into_unsafe_code` (`fallback.rs:231-274`) searches `VecGraph<ty::TyVid, true>` using `graph::depth_first_search_as_undirected` rather than directed DFS. Undirected traversal is required because V-junction LUB joins (`let a = if c { return } else { Default::default() }; let b = if !c { a } else { zeroed() };`) emit only directed edges `?a -> ?b` and `?zeroed -> ?b`; after fallback sets `?b := !`, `try_find_coercion_lub(!, ?zeroed)` invokes `coerce(?zeroed, !)` -> `unify(?zeroed, !)`, propagating `!` backward against `?zeroed -> ?b`. Bypassing the lint with `#[allow]` causes live unannotated `unsafe { core::mem::zeroed() }` (`zeroed::<!>()`) to abort natively via `intrinsics::assert_zero_valid::<T>()` (`rc = -6`) and trigger immediate Miri UB (`constructing invalid value of type !: encountered a value of the never type '!'`) in both Stacked Borrows and Tree Borrows.
3. **`CoerceMany` multi-arm LUB engine (`compiler/rustc_hir_typeck/src/coercion.rs:1380-1800`):** `try_find_coercion_lub` special-cases `(FnDef, FnDef)` and `(Closure, Closure)` pairs by attempting direct lattice LUB first (preserving zero-sized closure/fn-item identities when identical) before widening mismatched or mixed `(Closure, FnDef)` pairs via `Adjust::Pointer(PointerCoercion::{ClosureFnPointer, ReifyFnPointer})`, delegating `(FnPtr, FnPtr)` to normal unification (`PointerCoercion::UnsafeFnPointer`), and falling back to ordering-dependent one-sided `Coerce::coerce(new, prev)` before `Coerce::coerce(prev, new)` (handling `&mut T -> &T`, `*mut T -> *const T`, and `Unsize`). Unhinted array/if joins across differing lengths (`[&[1u8, 2], &[3, 4, 5]]`) are rejected (`E0308`) because `try_find_coercion_lub` does not synthesize `Unsize`; unsizing occurs only when an explicit slice expectation (`&[u8]` / `[&[u8]; 2]`) seeds `CoerceMany::expected_ty`.
4. **`if`/`match`/`array` vs. `loop`/labeled-block expectation-pinning asymmetry:** In `let r = expr;`, `check_decl_initializer` supplies `ExpectHasType(?v_r)`. `check_expr_if` (`expr.rs:1155`) and `check_expr_match` (`_match.rs:63`) strip unresolved `TyVar` hints via `try_structurally_resolve_and_adjust_for_branches`, and `check_expr_array` (`expr.rs:1639-1646`) filters `.is_ty_var()`, isolating `CoerceMany` with a fresh variable so both `(&mut x, &y)` and `(&y, &mut x)` coerce to `&u32`. Conversely, `check_expr_loop` (`expr.rs:1383-1384`) and `check_expr_block` (`fn_ctxt/checks.rs:1343-1344`) call `expected.coercion_target_type` directly without unpinning `?v_r`: the first `break &mut x` calls `fcx.coerce(&mut x, ?v_r)` (`coercion.rs:1749`) and pins `?v_r := &mut u32`, causing outer `check_expr_coercible_to_type` (`&u32` -> `&mut u32`) to fail with `E0308: types differ in mutability`, even though reversing arm order or dropping `let r =` compiles cleanly.
5. **Place-read gating (`rustc_middle/src/hir/mod.rs:230-325`):** Direct wildcard place checks (`let _ = *p;` and `match *p { _ => 43 }` on `*const !`) evaluate `expr_guaranteed_to_constitute_read_for_never == false`, skip MIR alignment/null assertions, and execute cleanly (`42`, `43`) natively and under Miri. Wrapping the dereference in a block (`let _ = { *p };`) or assigning it to unit (`let _x: () = *p;`) switches the parent HIR node to `Node::Block(_)` / `read_pat`, evaluates `true`, emits dereference assertions in MIR, and triggers Miri UB (`constructing invalid value of type !`).
6. **Mechanized Lean `v4.34.1` and Anneal trusted boundary:** `support/HirTypeckCoercionLubAndNeverFallbackSoundness.lean` (`1,739` lines, `745` kernel declarations, checked under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` using only `[propext]`) mechanizes `CoerceStep`/`AdjustChain` soundness, `CoerceMany` validity preservation, all LUB witnesses and expectation-pinning contrasts, undirected coercion-graph taint prevention, place-read gating, and the Anneal boundary (`joshlf/anneal@c131b320e`, where `Trusted.MirAst.Rvalue` omits `Cast`, lowering all `PointerCoercion`s to `.unsupported`, `MirTy.never` evaluates `unreachable` to `.fault .undefined`, and `anneal-rustc-capture` currently pins `1.98.0-nightly`).

## Applicability

This report combines primary-source analysis across three `rust-lang/rust` snapshots, live differential compilation/execution (`rustc` + LLVM IR + MIR + Miri), normative comparison against The Rust Reference, Lean 4 mechanization, and boundary auditing against Anneal. Because observed behavior differs materially across `rustc` releases and editions, applicability is explicitly partitioned by subject:

| Subject / Revision | Role in Report | Scope & Version-Specific Guarantees |
| :--- | :--- | :--- |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` (`main` HEAD) | Primary source authority | Governs `coercion.rs`, `fallback.rs`, `expr.rs`, `_match.rs`, `fn_ctxt/{mod,checks}.rs`, `rustc_middle/src/hir/mod.rs`, `rustc_lint_defs/src/builtin.rs`, `rustc_mir_build`, and `core::mem::zeroed`. Its `fallback.rs` (`27,573` bytes) is byte-identical (`sha256: 61ed7bc4af400a88e9b6373462b3f532478c627770e21dd495a981e837dbac0a`) to `3ef0c22cd`. |
| `rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`) | Post-1.100 empirical baseline | Captured runtime/Miri/MIR/LLVM-IR baseline (`LLVM 23.1.5`) establishing that stable unannotated `!` syntax works without `#![feature(never_type)]` and that diverging fallback chooses `!` identically in Edition 2021 and Edition 2024 (`zeroed::<!>()`, `rc = -6`, Miri UB). |
| `rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`) + `miri 0.1.0 (14210df0e2)` | Live host execution toolchain (`x86_64-unknown-linux-gnu`, `LLVM 22.1.6`) | Executed directly by `support/probe_hir_typeck_coercion_lub_and_never_fallback.py` (`support/probe_results.json`, `2026-11-23`). Isolates pre-1.100 edition split (`Ed2021 -> ()` vs `Ed2024 -> !` with `#![feature(never_type)]`), confirms identical default-deny `never_type_fallback_flowing_into_unsafe` undirected graph behavior in stable Rust, identical place-read gating, and identical `CoerceMany` LUB and `loop`/`'blk` pinning behavior against `5debe6a12`. |
| `rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative language reference | Supplies `r[coerce]` (`type-coercions.md`), `r[divergence]` (`divergence.md`), and `r[undefined.validity.never]` (`behavior-considered-undefined.md`). Matches post-1.100 `!` fallback (`r[divergence.fallback]`), while leaving inference-triggered multi-arm LUB sites (`if`, `match`, `loop`, blocks, unhinted arrays) underspecified compared to `rustc`. |
| `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Downstream verification consumer | Audited via `Trusted.MirAst`, `Trusted.MirSemantics`, `TrustedBoundary.lean`, and `trusted/rustc-capture/src/driver.rs`. Pinned to `1.98.0-nightly (f8a08b688 2026-05-30)` (`driver.rs:25`), placing Anneal's current capture toolchain inside the pre-1.100 edition-split regime. |
| `leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Mechanization proof kernel | Kernel-checked `support/HirTypeckCoercionLubAndNeverFallbackSoundness.lean` (`2026-11-23`) with zero `sorry`, zero `Classical.choice`, zero forbidden axioms/tactics, and zero `._unsafe_rec` compiler helpers. |

**Coherence of combining `1.98.0-nightly`, `1.102.0-nightly`, and HEAD (`5debe6a12`):**
Findings are partitioned cleanly by compiler mechanism:
- **Changed between `1.98.0` and `1.102.0`/HEAD (`fallback.rs`, `fn_ctxt/mod.rs`, `builtin.rs`):** Unfeatured `!` availability, Edition 2021 diverging fallback target (`()` in `1.98.0` vs. `!` in `1.102.0`/HEAD), and deletion of `DEPENDENCY_ON_UNIT_NEVER_TYPE_FALLBACK` (`fallback.rs` size dropped from `32,918` to `27,573` bytes).
- **Shared across `1.98.0`, `1.102.0`, and HEAD (`coercion.rs`, `expr.rs`, `_match.rs`, `checks.rs`, `fallback.rs` graph & `builtin.rs:4223` lint, `hir/mod.rs`):** All four `CoerceMany` LUB rules, the `if`/`match`/`array` vs. `loop`/`'blk` `let`-pinning asymmetry, default-deny `never_type_fallback_flowing_into_unsafe` via `depth_first_search_as_undirected`, and `expr_guaranteed_to_constitute_read_for_never` place-read gating hold uniformly.

## Findings

### 1. Evolution from Edition-Split (`1.98.0`) to Unconditional (`>= 1.100`) Never-Type Fallback

Basis: source + execution + normative

At the end of function-body HIR type checking, `FnCtxt::type_inference_fallback` (`compiler/rustc_hir_typeck/src/fallback.rs:25-45` at `5debe6a12`) runs obligation selection, invokes `self.fallback_types()`, and if any fallback occurred, re-runs `self.select_obligations_where_possible(|_| {})` so trait obligations stalled on unresolved inference variables (such as `<T as Poly>::tag()` or `<T as Default>::default()`) resolve against the fallen-back concrete type. Comparing `14210df0e` (`1.98.0-nightly`) with `3ef0c22cd` (`1.102.0-nightly`) and `5debe6a12` (HEAD) isolates the exact stabilization transition:

| Component / Behavior | `1.98.0-nightly` (`14210df0e`) | `1.102.0-nightly` (`3ef0c22cd`) & HEAD (`5debe6a12`) |
| :--- | :--- | :--- |
| Surface `!` syntax (`impl Poly for !`) | Rejected (`E0658`) in both Ed2021 and Ed2024 without `#![feature(never_type)]` | Accepted in stable code without feature gate in both editions (`3ef0c22cd`) |
| `FnCtxt` fallback config (`fn_ctxt/mod.rs:122-123`) | Stores `diverging_fallback_behavior: DivergingFallbackBehavior` (`Ed2021 -> ToUnit`, `Ed2024 -> ToNever`) and `diverging_block_behavior` (`fn_ctxt/mod.rs:497-514`) | Removed from `FnCtxt` (`fn_ctxt/mod.rs:118-125` at `5debe6a12`); unconditionally falls back to `!` |
| `fallback_types` (`fallback.rs`) | `lines 48-75` + `fallback_if_possible` (`93-130`): substitutes `diverging_fallback_ty` (`()` in Ed2021, `!` in Ed2024) | `lines 66-111`: iterates `diverging_fallback` and unconditionally executes `self.demand_eqtype(span, Ty::new_var(self.tcx, vid), self.tcx.types.never)` (`88-94`) |
| `dependency_on_unit_never_type_fallback` | Emitted (`Deny`) in Ed2021 when diverging fallback to `()` satisfies a unit-only bound; fails in Ed2024 with `E0277` | Removed from `fallback.rs`; both Ed2021 and Ed2024 select `!` and fail unit-only bounds with `E0277` |
| `never_type_fallback_flowing_into_unsafe` | Default `Deny` (`builtin.rs:4164-4173`), annotated as `@future_incompatible` (`Edition2024 => Deny`) | Retained as default `Deny` (`builtin.rs:4223-4227`) without the `Edition2024` conditional |

Note an implementation detail in `5debe6a12`: the doc comment on `fallback_types` at `fallback.rs:55-57` still mentions `"replaced with () or !, depending on ... crate's edition, and the setting of #![rustc_never_type_options(fallback = ...)]"`, even though `fallback_types` at `lines 88-94` and `calculate_diverging_fallback` at `lines 197-229` unconditionally substitute `self.tcx.types.never`. The doc comment lags the code deletion. Meanwhile, `rust-lang/reference@c9cc32825b` (`src/divergence.md:65`) normatively states:

> `r[divergence.fallback]`
> If a type to be inferred is only unified with diverging expressions, then that type will be inferred to be `!`.

Note further the structural qualification recorded in `r[divergence.fallback]` (`src/divergence.md:78-87`): type unification operates *structurally*, so `match foo() { 4 => Default::default(), _ => Some(return) }` infers `Option<!>`, which *does* implement `Default` (`None`), whereas direct `return` + `Default::default()` infers `!`, failing `!: Default`.

#### Empirical Proof of Edition Convergence vs. Split (`probe_fallback` & `zeroed::<!>()`)

Basis: execution + source

Consider the polymorphic probe compiled in `support/probe_hir_typeck_coercion_lub_and_never_fallback.py` (with `#![feature(never_type)]` prepended on `1.98.0-nightly` so `impl Poly for !` is accepted, and in stable Rust on `1.102.0-nightly`):

```rust
trait Poly { fn tag() -> &'static str; }
impl Poly for () { fn tag() -> &'static str { "unit" } }
impl Poly for ! { fn tag() -> &'static str { "never" } }
fn make<T: Poly>() -> (&'static str, Option<T>) { (T::tag(), None) }

pub fn probe_fallback() -> &'static str {
    let (t, o) = make();
    if false { let _x = if true { return "early"; } else { o.unwrap() }; }
    t
}

#[allow(never_type_fallback_flowing_into_unsafe)]
pub fn probe_never_zeroed_live(do_ub: bool) -> &'static str {
    if do_ub {
        let _x = if false { return "early"; } else { unsafe { core::mem::zeroed() } };
    }
    "ok"
}
```

Here `o.unwrap()` coerces against `return "early"` (`!` inside the dead `if false` branch), and `unsafe { core::mem::zeroed() }` has an unconstrained return type coerced alongside `return "early"`. Because `?T` in `make::<T>()` and `?Z` in `zeroed::<Z>()` only interact with diverging expressions (plus `o: Option<?T>`), they enter `CoerceMany` (`fallback.rs` sees them as unresolved diverging root vids). Differential execution records establish exact split vs. convergence:

1. **Pre-1.100 (`rustc 1.98.0-nightly`, `14210df0e`, executed `2026-11-23`):**
   - **Edition 2021** resolves `make::<()>` and `zeroed::<()>` (post-cleanup MIR in `support/probe_results.json`):
     ```rust
     // probe_fallback -> bb0:
     _2 = make::<()>() -> [return: bb1, unwind continue];
     // probe_never_zeroed_live -> bb1:
     _2 = zeroed::<()>() -> [return: bb2, unwind continue];
     ```
     Both native `-O2`/`-O0` (`safe`, `ub`) and Miri (`Stacked Borrows` & `-Zmiri-tree-borrows`) return **`TAG=unit RES=ok`** (`rc = 0`).
   - **Edition 2024** resolves `make::<!>` and `zeroed::<!>` (`support/probe_results.json`), emitting compiler warning `warning: the type '!' does not permit zero-initialization` (`invalid_value` lint):
     ```rust
     // probe_fallback -> bb0:
     _1 = make::<!>() -> [return: bb1, unwind continue];
     // probe_never_zeroed_live -> bb1:
     _2 = zeroed::<!>() -> unwind continue;
     ```
     With arg `safe` (`do_ub = false`), both native and Miri return **`TAG=never RES=ok`** (`rc = 0`). With arg `ub` (`do_ub = true`), native `-O2` and `-O0` abort with `rc = -6` (`attempted to instantiate uninhabited type '!'` at `<RUSTC_SRC>/library/core/src/panicking.rs:225:5`, caused by `intrinsics::assert_zero_valid::<T>()` in `core/mem/mod.rs:760`), and both Miri Stacked Borrows and Tree Borrows abort with `rc = 1`:
     ```text
     error: Undefined Behavior: constructing invalid value of type !: encountered a value of the never type `!`
     ```

2. **Post-1.100 (`rustc 1.102.0-nightly`, `3ef0c22cd`, observed `2026-11-11`):**
   - **Edition 2021 now behaves identically to Edition 2024.** Both editions emit `make::<!>()` and `zeroed::<!>()` in `1-1-000.built.after.mir` and `3-2-000.runtime-post-cleanup.after.mir`, output **`TAG=never RES=ok`** for `safe`, abort natively (`rc = -6`, `attempted to instantiate uninhabited type '!'`) for `ub`, and fail Miri Stacked Borrows & Tree Borrows (`rc = 1`) for `ub`.
   - At `-O0`, LLVM IR for `probe_never_zeroed_live` shows `call void @_RNv...panic_nounwind(...)`, `precondition_check`, `llvm.memset`, another `panic_nounwind`, `store i1 true, ptr poison`, `call void @llvm.trap()`, and `unreachable`; at `-O2`, LLVM reduces `bb1` to `tail call void ...panic_nounwind(...); unreachable` (`3ef0c22cd` LLVM IR receipts).

3. **Stable-syntax unit-trait breakage across eras (`PROG_DEPENDENCY_ON_UNIT`):**
   Even on `1.98.0-nightly`, stable syntax `let x = if cond { return 1; } else { Default::default() }; take(x)` where `OnlyUnit` is implemented only for `()` produces:
   - **Edition 2021 (`1.98.0-nightly`):** Rejected by default-deny lint `error: this function depends on never type fallback being '()'` (`#[deny(dependency_on_unit_never_type_fallback)]`, `support/probe_results.json`).
   - **Edition 2024 (`1.98.0-nightly`) and all post-1.100 editions:** Rejected directly at trait resolution with **two `E0277` errors**: `the trait bound '!: OnlyUnit' is not satisfied` and `the trait bound '!: Default' is not satisfied`.

### 2. Why `never_type_fallback_flowing_into_unsafe` Uses Undirected Coercion-Graph Reachability

Basis: source + execution + derived

In `compiler/rustc_hir_typeck/src/fallback.rs` (`5debe6a12` and `3ef0c22cd`, lines `197-314` and `517-652`; same mechanism in `1.98.0` at `lines 196-425`), fallback safety relies on `NEVER_TYPE_FALLBACK_FLOWING_INTO_UNSAFE` (`Deny` by default in `builtin.rs:4223-4227`) rather than silent soundness. Its detection pipeline runs in four steps inside `calculate_diverging_fallback`:

1. **Diverging roots (`fallback.rs:203-208`):** Collect `diverging_root_vids` — unresolved root inference variables `?d` that were the target of a coercion from `!` (`self.diverging_type_vars`, recorded when `!` coerces to an inference variable).
2. **Unsafe variable visitor (`compute_unsafe_infer_vars`, `fallback.rs:517-652`):** Walk the HIR body collecting every unresolved inference variable appearing in five `UnsafeUseReason` positions:
   - `UnsafeUseReason::Call` (`lines 554-578`): generic args (plus output type via `sig.output()`) of an `unsafe fn` call such as `core::mem::zeroed::<Z>()`.
   - `UnsafeUseReason::Method` (`lines 534-552`): generic args including `Self` of an `unsafe` method call.
   - `UnsafeUseReason::Path` (`lines 583-603`): generic args of a path naming an `unsafe fn`, even if stored in a variable before calling.
   - `UnsafeUseReason::Deref` (`lines 605-612`): pointee type of `*ptr` raw-pointer dereference.
   - `UnsafeUseReason::UnionField` (`lines 614-640`): accessed union field's type on `ExprKind::Field`.
3. **Coercion/subtyping graph construction (`create_coercion_graph`, `fallback.rs:278-314`):** Extract pending obligations whose `ty::PredicateKind` is `Coerce(CoercePredicate { a, b })` or `Subtype(SubtypePredicate { a_is_expected: _, a, b })` and add directed edges `root_vid(a) -> root_vid(b)` into `VecGraph<ty::TyVid, true>`.
4. **Undirected reachability search (`lint_never_type_fallback_flowing_into_unsafe_code`, `fallback.rs:231-241`):**
   ```rust
   let affected_unsafe_infer_vars =
       graph::depth_first_search_as_undirected(&coercion_graph, root_vid)
           .filter_map(|x| unsafe_infer_vars.get(&x).copied())
           .collect::<Vec<_>>();
   ```

**Why directed DFS is insufficient (`PROG_DEFAULT_DENY_UNSAFE_GRAPH_HOP`):**
Consider a V-junction and a 2-hop chain verified live on `rustc 1.98.0-nightly`:

```rust
pub fn trigger_indirect_hop(cond: bool) {
    let a = if cond { return; } else { Default::default() };
    let b = if !cond { a } else { unsafe { core::mem::zeroed() } };
    let _ = b;
}

pub fn trigger_two_hop_coercion(cond: bool) {
    let v0 = if cond { return; } else { loop {} };
    let v1 = if !cond { v0 } else { Default::default() };
    let v2 = if cond { v1 } else { unsafe { core::mem::zeroed() } };
    let _ = v2;
}
```

Tracing `trigger_indirect_hop` step by step explains why undirected graph traversal is mandatory:
- Arm 1 (`if cond { return; } else { Default::default() }`) records `?a` as a diverging root variable (target of `NeverToAny` from `return` and unified with `Default::default()`).
- In `let b = if !cond { a } else { zeroed() };`, `check_expr_if` allocates `?lub` (disjoint from `?b`), coerces `a: ?a` into `?lub` (`Coerce(?a -> ?lub)` edge), and invokes `try_find_coercion_lub(?lub, ?zeroed)` which either adds `Coerce(?zeroed -> ?lub)` or relates `Coerce(?zeroed -> ?b)`. Thus **`?a` and `?zeroed` only co-flow forward into `?b` / `?lub`** — there is **zero** directed path `?a ->* ?zeroed` in `coercion_graph`!
- During `fallback_types()` (`fallback.rs:88-90`), `rustc` sets `?a := !`. When `select_obligations_where_possible` resumes:
  1. `Coerce(?a -> ?b)` sees concrete `!` on the LHS (`a.is_never()` in `coercion.rs:249`), or during LUB unification `?a` resolves and unifies/coerces `?b := !`.
  2. Now `Coerce(?zeroed -> ?b)` has `?zeroed` unresolved on LHS and **`!` concrete on RHS**. `Coerce::coerce` hits `a.is_ty_var()` (`coercion.rs:265`) -> `coerce_from_inference_variable(?zeroed, !)` (`coercion.rs:411`) -> `self.unify(?zeroed, !)`!
  3. Consequently, `?zeroed` is unified backward to `!`, selecting `core::mem::zeroed::<!>()`.

Had `fallback.rs` searched `coercion_graph` only along directed forward edges (`a -> b`), `?zeroed` would never be reached from `?a`, silently allowing `zeroed::<!>()` without triggering `never_type_fallback_flowing_into_unsafe`. Empirically (`support/probe_results.json`, `default_deny_unsafe_graph_hop`), `rustc` catches **all 4 errors** across both functions in both editions:
- Edition 2021 (`1.98.0`): 2 `dependency_on_unit_never_type_fallback` errors (`a: Default`, `v1: Default`) AND **2 `never_type_fallback_flowing_into_unsafe` errors** (`b`'s `zeroed()` on line 4 and `v2`'s `zeroed()` on line 11, noting fix suggestion `let a: () = ...` and `let v0: () = ...`).
- Edition 2024 (`1.98.0`): 2 `E0277: !: Default` errors AND the **exact same 2 `never_type_fallback_flowing_into_unsafe` errors** on lines 4 and 11.

### 3. Single-Site Coercions (`Adjust` & `PointerCoercion`), Transitivity Limits, and `may_coerce` Heuristics

Basis: normative + source

The Rust Reference (`r[coerce.site]`, `src/type-coercions.md:12-99`) enumerates explicit coercion sites (`let` annotations, `static`/`const`, fn/method arguments, struct/enum/union fields, `return` / block tail return, assignment RHS, and structural propagation through array literals, repeat expressions, tuples, parenthesized expressions, and blocks with known type `U`). Internally, `FnCtxt` separates hard coercion sites (`check_expr_coercible_to_type_or_error`, `expr.rs:138-158`) from non-coercive expectation sites (`check_expr_has_type_or_error`, `expr.rs:77-124`), which permit **only** subtyping and `[Adjustment { kind: Adjust::NeverToAny, target: adj_ty }]` (gated by `self.tcx.expr_guaranteed_to_constitute_read_for_never(expr)` at `expr.rs:87-88`).

Every coercion emits a flat ordered vector `Vec<Adjustment<'tcx>>` (`compiler/rustc_middle/src/ty/adjustment.rs:82-114`), later lowered to MIR by `rustc_mir_build`:

| Normative Rule (`r[coerce.types.*]`) | `Coerce::coerce` Dispatch (`coercion.rs`) | Emitted `Adjust` Sequence (`adjustment.rs`) | MIR Lowering (`as_rvalue.rs` / `into.rs`) |
| :--- | :--- | :--- | :--- |
| `r[coerce.types.never]` (`! -> T`) | `lines 249-259`: requires `self.coerce_never` (else `unify`) | `[Adjust::NeverToAny]` (note: `may_coerce_except_never` at `1244-1249` excludes `! -> T`) | Diverging CFG (`TerminatorKind::Unreachable` / call unwind) |
| `a.is_ty_var()` | `coerce_from_inference_variable` (`373-413`) | `CoercePredicate(a -> b)` (or fresh LUB target if `use_lub && b.is_ty_var()`), else `unify` | Wait-for-fallback / unification |
| `r[coerce.types.unsize]` & DST | `coerce_unsized` (`566-740`) | Optional `[Deref(Builtin), Borrow(Ref/RawPtr)]` reborrow + `Adjust::Pointer(PointerCoercion::Unsize)` (`line 704`); requires `Source: CoerceUnsized<Target>` | `Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, origin), ...)` (`as_rvalue.rs:158-170`) |
| `r[coerce.types.mut-reborrow]` & `deref` | `coerce_to_ref` (`422-565`) | `Deref(Builtin \| Overloaded)` chain + `Borrow(AutoBorrow::Ref(mutbl))` | `&(*place)` reborrow or `<T as Deref>::deref` call |
| `r[coerce.types.mut-pointer]` (`*mut -> *const`), `ref-to-pointer`, `mut-to-pointer` | `coerce_to_raw_ptr` (`1136-1184`) | If `&`/`&mut` -> `*`: `[Deref(Builtin), Borrow(AutoBorrow::RawPtr(mutbl))]`; if `*mut -> *const`: `Adjust::Pointer(PointerCoercion::MutToConstPointer)` | `*mut -> *const` lowers to `copy _2 as *const T (PtrToPtr)`; `&T -> *const T` reborrows `&*r` as raw ptr |
| `r[coerce.types.fn]` (`FnDef -> fn/unsafe fn`) | `coerce_from_fn_item` (`1091-1113`) | `Adjust::Pointer(PointerCoercion::ReifyFnPointer(b_hdr.safety()))` (`line 1104`) | `fn_item as fn(...) (PointerCoercion(ReifyFnPointer(Safe\|Unsafe), Implicit))` |
| Safe `fn -> unsafe fn` | `coerce_from_fn_pointer` (`1072-1089`) | `Adjust::Pointer(PointerCoercion::UnsafeFnPointer)` (`line 1084`) if `a.is_safe() && b.is_unsafe()` | `copy p as unsafe fn(...) (PointerCoercion(UnsafeFnPointer, Implicit))` |
| `r[coerce.types.closure]` (`Closure -> fn`) | `coerce_closure_to_fn` (`1117-1134`) | `Adjust::Pointer(PointerCoercion::ClosureFnPointer(safety))` (`line 1129`); fails if closure captures upvars | `const ZeroSized: {closure} as fn(...) (PointerCoercion(ClosureFnPointer(Safe\|Unsafe), Implicit))` |

Two subtle constraints in `Coerce::coerce` matter for verification:
1. **Unidirectional coercion guards (`mut -> imm`, `safe -> unsafe`):** Both `coerce_to_ref` / `coerce_unsized` / `coerce_to_raw_ptr` (`coerce_mutbls`) and `coerce_from_fn_pointer` / `coerce_from_fn_item` enforce monotonicity (`Mutability::Mut <= Mutability::Not`; `Safety::Safe <= Safety::Unsafe`). An immutable reference never coerces to `&mut T`, an `unsafe fn()` never coerces to safe `fn()`, and a capturing closure (`!upvars.is_empty()`) cannot emit `ClosureFnPointer`.
2. **Restricted transitivity:** Although `r[coerce.types.transitive]` states `"T_1 coerces to T_3 where T_1 coerces to T_2 and T_2 coerces to T_3"` with the caveat `"Note that this is not fully supported yet"`, `Coerce::coerce` only composes the specific pipelines coded inside its methods—for example, `coerce_unsized` explicitly synthesizes `[Deref(Builtin), Borrow(Ref(Not)), Pointer(Unsize)]` when coercing `&mut [u8; 2]` to `&[u8]` (`coercion.rs:659-706`), as confirmed directly by the MIR of `lub_if_mut_unsize` and `lub_array_mut_and_shared_unsize` (`_4 = &(*_2); _0 = move _4 as &[u8] (PointerCoercion(Unsize, Implicit))`). Arbitrary transitive user coercions across separate steps are not inferred unless chained at explicit intermediate sites or folded inside `CoerceMany`.

### 4. `CoerceMany` Multi-Arm LUB Algorithm and the `if`/`match` vs. `loop`/Block Pinning Asymmetry

Basis: source + execution + normative + derived

Branching and sequence constructs (`if`, `match`, `loop`, labeled blocks, array literals, multi-`return` functions via `FnCtxt::ret_coercion` at `fn_ctxt/mod.rs:68`) accumulate arm/element types inside `CoerceMany<'tcx>` (`coercion.rs:1616-2189`).

#### 4.1 Internal State Machine (`CoerceMany::coerce_inner` & `try_find_coercion_lub`)

`CoerceMany<'tcx>` tracks three fields (`coercion.rs:1616-1620`):
- `expected_ty: Ty<'tcx>` — the downward target passed when constructing `CoerceMany::new(ty)` / `with_capacity(ty, n)` (`expected_ty()` returns this unchanged across arms, `line 1643`).
- `final_ty: Option<Ty<'tcx>>` — initially `None`; `merged_ty()` (`lines 1651-1653`) returns `final_ty.unwrap_or(expected_ty)`.
- `expressions: Vec<&'tcx hir::Expr<'tcx>>` — every expression coerced so far. Calling `complete(fcx)` when `expressions.is_empty()` and `final_ty.is_none()` (i.e., zero inputs or all diverging `!` inputs) yields `tcx.types.never` (`lines 2179-2188`), matching `all_diverge_if`'s MIR type (`-> !`).

For each non-forced-unit arm `e` of type `e_ty`, `coerce_inner` branches (`lines 1744-1765`):
1. **First expression (`self.expressions.is_empty()`):** Calls `fcx.coerce(e, e_ty, self.expected_ty, AllowTwoPhase::No, Some(cause.clone()))` (`lines 1749-1755`) and sets `self.final_ty = Some(result_ty)`. Notably, if `self.expected_ty` is an unresolved inference variable `?v`, `fcx.coerce` unifies `?v` with `e_ty` (or records `CoercePredicate(e_ty -> ?v)`), and `CoerceMany` records `[e]`.
2. **Subsequent expressions (`!self.expressions.is_empty()`):** Calls `fcx.try_find_coercion_lub(cause, &self.expressions, self.merged_ty(), e, e_ty)` (`lines 1380-1535`):
   - **Fast equality check (`lines 1400-1402`):** If `prev_ty == new_ty`, returns `prev_ty` immediately without coercing.
   - **Pre-coercion LUB for identical `(FnDef, FnDef)` / `(Closure, Closure)` pairs (`lines 1412-1441`):** Calls `lub(prev_ty, new_ty)` first inside `commit_if_ok` (using `ObligationCtxt::lub` under `-Znext-solver` or `at.lub` otherwise). If identical closures/fn-items succeed (e.g., two uses of the same closure `c` in `lub_same_closure_stays_unreified`), it returns the zero-sized type unchanged (`<{closure} as Fn<(u32,)>>::call` in MIR, **no** `ClosureFnPointer` cast). If `lub` fails (e.g., distinct closures or distinct `FnDef`s), it extracts both function signatures via `sig_for_coerce_lub`.
   - **Mixed `(Closure, FnDef)` / `(FnDef, Closure)` pairs (`lines 1443-1447`):** Directly extracts both signatures (`opt_sigs = Some((a_sig, b_sig))`).
   - **Signature safety join + retroactive reification (`lines 1454-1489`):** If one signature is `Safe` and the other is `Unsafe`, promotes the safe signature via `tcx.safe_to_unsafe_sig`, normalizes and takes `lub(a_sig, b_sig)`, constructs `fn_ptr = Ty::new_fn_ptr(self.tcx, sig)`, and retroactively applies `[Adjust::Pointer(ClosureFnPointer\|ReifyFnPointer(sig.safety()))]` to **all prior expressions `self.expressions`** (`lines 1481-1486`) plus `e` (`line 1487`).
   - **Fallback two-direction coercion search (`lines 1499-1534`):** Creates `Coerce` with `use_lub = true` and `coerce_never = true` (`NOTE: coercion LUBs only operate on values and not places`), first attempting `coerce.coerce(new_ty, prev_ty)` (`line 1506`, skipped if `new` already has adjustments) to adjust `new` to `prev_ty`, and if that fails, attempting `coerce.coerce(prev_ty, new_ty)` (`line 1522`) to retroactively apply `adjustments` to every prior `expr in self.expressions` (`lines 1527-1529`) and return the widened `target`. Note `(FnPtr, FnPtr)` (`line 1450`) falls right through to this two-direction coercion search!

#### 4.2 Empirical `CoerceMany` LUB Matrix Across `1.98.0-nightly` and `1.102.0-nightly`

Basis: execution + source

All five positive patterns below executed identically on live `1.98.0-nightly` (`2026-11-23`) and `1.102.0-nightly` (`3ef0c22cd`, `2026-11-11`), passing native `-O2`, Miri Stacked Borrows, and Miri `-Zmiri-tree-borrows`:

| Case (Probe Function) | Input Types / Expectation | Observed Post-Cleanup MIR Adjustments | Runtime Output (`-O2`, SB, TB) |
| :--- | :--- | :--- | :--- |
| `lub_ref_mut_shared` / `lub_ref_shared_mut` | `if cond { &mut u32 } else { &u32 }` (and reversed) in `let r = ...` | Mut arm reborrowed `_4 = &(*_2);`, shared arm `_4 = copy _3;` -> `r: &u32` (order-independent under `if`) | `REF=(5,5)` |
| `lub_array_slices` | `[&[1u8, 2], &[3, 4, 5]]` under `-> [&[u8]; 2]` | Both elements emit `as &[u8] (PointerCoercion(Unsize, Implicit))` | `SLICES=(2,3)` |
| `lub_array_mut_and_shared_unsize` / `lub_if_mut_unsize` | `&mut [u8; 2]` + `&[u8; 3]` under `-> [&[u8]; 2]` and `-> &[u8]` | `&mut [u8; 2]` reborrows `_4 = &(*_1)` then `move _4 as &[u8] (PointerCoercion(Unsize, Implicit))`; `&[u8; 3]` directly casts `copy _2 as &[u8]` (`MSLICES=(2,3)`, `if_unsize.len()=2`) | `MSLICES=(2,3)` |
| Unhinted array/if slices (`no_hint_if`, `no_hint_arr`) | `let _s = if cond { &[1u8, 2] } else { &[3, 4, 5] };` and `[&[1u8, 2], &[3, 4, 5]]` | Rejected (`rc = 1`): `E0308: expected an array with a size of 2, found one with a size of 3` | Compile error (`E0308`) |
| `lub_two_closures` vs `lub_same_closure_stays_unreified` | Two distinct non-capturing closures vs same closure variable `c` | Distinct closures: both arms emit `PointerCoercion(ClosureFnPointer(Safe), Implicit)` (`CLOS=12`). Same `c`: stays ZST `<{closure} as Fn<(u32,)>>::call` (`CLOS=14`) | `CLOS=(12,14)` |
| Capturing closures (`capturing_lub`) | `if cond { \|x\| x + k } else { \|x\| x + 1 }` | Rejected (`rc = 1`): `E0308: no two closures, even if identical, have the same type` | Compile error (`E0308`) |
| `lub_safe_unsafe_fndef` vs `lub_safe_unsafe_fnptr` | `safe_fn` + `unsafe_fn` (`FnDef`) vs `fn(u32)->u32` + `unsafe fn(u32)->u32` (`FnPtr`) | `FnDef` pair: BOTH arms emit `PointerCoercion(ReifyFnPointer(Unsafe), Implicit)` (`FN=30`). `FnPtr` pair: ONLY safe arm emits `PointerCoercion(UnsafeFnPointer, Implicit)` (`FN=20`) | `FN=(30,20)` |
| `lub_raw_mut_to_const` | `if cond { a: *mut u32 } else { b: *const u32 }` | Mut arm emits `_4 = copy _2 as *const u32 (PtrToPtr)`, shared arm `_4 = copy _3` | `RAW=5` |

Notice the normatively subtle array-slice result (`no_hint_if`, `no_hint_arr`): although `try_find_coercion_lub` joins `&mut T` + `&T` -> `&T`, `*mut T` + `*const T` -> `*const T`, and distinct non-capturing closures/fns -> `fn`, it has **no rule** to synthesize `PointerCoercion::Unsize` (`&[u8; 2]` + `&[u8; 3]` -> `&[u8]`) without a pre-existing slice expectation! Why `[&[u8; 2], &[u8; 3]]` succeeds in `lub_array_slices()` and `lub_array_mut_and_shared_unsize()` is that `check_expr_array` (`expr.rs:1633-1647`) calls `.to_option(self).and_then(|uty| ...builtin_index())` on the expected return type `[&[u8]; 2]`, extracting `coerce_to = &[u8]`. Each element then directly coerces to `expected_ty = &[u8]` individually! Without a slice type annotation (`let _a = [&[1u8, 2], &[3, 4, 5]];`), `coerce_to` falls back to `next_ty_var`, element 0 binds `final_ty = &[u8; 2]`, and element 1 fails unification in `try_find_coercion_lub(&[u8; 2], &[u8; 3])`.

In addition, `rustc 1.102.0-nightly` opt-0 LLVM IR (`probe_results` baseline) reveals the exact codegen cost of `ClosureFnPointer` LUB reification: `lub_two_closures` allocates an 8-byte function pointer `%f`, stores one of two distinct `FnOnce::call_once` shims (which each call their respective `i32 {closure}(ptr %_1, i32)`), and executes an indirect `call i32 %_4(i32 %v)`. At `-O2`, LLVM devirtualizes and constant-folds the entire `if cond` closure join down to `ret i32 12`.

#### 4.3 Order-Sensitive Pinning Asymmetry: Generic Calls, `if`/`match`/`array`, and `loop`/Labeled Blocks

Basis: source + execution + derived

Even for single coercions, multi-argument generic unification is order-sensitive because `rustc` checks arguments left-to-right without backtracking:
- `pick(&mut x, &y)` (`fn pick<T>(a: T, _b: T) -> T`) fails with **`E0308: types differ in mutability` (`expected &mut _, found &_`)** because checking `a = &mut x` instantiates `?T := &mut i32` before visiting `_b = &y`.
- `pick(&y, &mut x)` succeeds because `?T := &i32` first, allowing `&mut x` to coerce to `&i32` (`support/probe_results.json`, `call_arg_order_fail` vs. `call_arg_order_ok`).

More subtly, **a structural asymmetry exists inside `rustc_hir_typeck` itself between `if`/`match`/`array` and `loop`/labeled blocks when initializing an unannotated `let` binding**:

1. **`let r = if ...` / `let r = match ...` (Order-Independent — SUCCEEDS for `(&mut, &)` AND `(&, &mut)`):**
   - `check_decl_initializer` (`fn_ctxt/checks.rs:1178-1203`) creates an unresolved variable `local_ty = ?v_r` and calls `check_expr_coercible_to_type(init, ?v_r, None)`, which passes `ExpectHasType(?v_r)` downward (`expr.rs:145`).
   - `check_expr_if` (`expr.rs:1155`) and `check_expr_match` (`_match.rs:63`) immediately transform:
     ```rust
     let expected = orig_expected.try_structurally_resolve_and_adjust_for_branches(self);
     let coerce_to_ty = expected.coercion_target_type(self, sp);
     ```
     Because `?v_r` is an unresolved `TyVar`, `try_structurally_resolve_and_adjust_for_branches` converts `ExpectHasType(?v_r)` into `NoExpectation`, so `coercion_target_type` allocates a **fresh disjoint type variable `?v_lub`**.
   - Arm 0 (`&mut u32`) unifies **`?v_lub`** (NOT `?v_r`!), Arm 1 (`&u32`) runs `try_find_coercion_lub(&mut u32, &u32)` -> `&u32` and retroactively reborrows Arm 0, and `complete()` returns `&u32`. Only *after* `check_expr_if` returns does `demand_coerce_diag(init, &u32, ?v_r)` (`expr.rs:147`) bind `?v_r := &u32`. `check_expr_array` (`expr.rs:1639-1646`) enforces the same guard explicitly via `.filter(|t| !self.deeply_resolve_ignoring_regions_with_obligations(*t).is_ty_var())`.

2. **`let r = loop { ... }` and `let r = 'blk: { ... }` (Order-Sensitive — FAILS for `(&mut, &)`, SUCCEEDS for `(&, &mut)`):**
   - In contrast, `check_expr_loop` (`expr.rs:1383-1384`) and `check_expr_block` (`fn_ctxt/checks.rs:1343-1344`) **skip `try_structurally_resolve_and_adjust_for_branches`** and call `expected.coercion_target_type` directly:
     ```rust
     // expr.rs:1383-1384 (`check_expr_loop`)
     let coerce_to = expected.coercion_target_type(self, body.span);
     Some(CoerceMany::new(coerce_to))

     // fn_ctxt/checks.rs:1343-1344 (`check_expr_block`)
     let coerce_to_ty = expected.coercion_target_type(self, blk.span);
     let coerce = CoerceMany::new(coerce_to_ty);
     ```
   - Inside `let r = loop { if cond { break &mut x; } break &y; };`, `CoerceMany::expected_ty` **aliases `?v_r`**!
   - When Arm 0 (`break &mut x`) executes `coerce.coerce(self, &cause, e, &mut u32)` (`expr.rs:792`), `CoerceMany::coerce_inner` sees `self.expressions.is_empty()` (`coercion.rs:1745-1755`) and runs `fcx.coerce(e, &mut u32, ?v_r, ...)`, which falls through to `self.unify(&mut u32, ?v_r)` and **mutably pins `?v_r := &mut u32`**!
   - Next, Arm 1 (`break &y`) calls `try_find_coercion_lub(&mut u32, &u32)` (`coercion.rs:1757`), which *succeeds* and updates `CoerceMany.final_ty = Some(&u32)`, returning `&u32` as the type of the `loop`/`'blk` expression.
   - Finally, back in `check_decl_initializer`, `check_expr_coercible_to_type` invokes `demand_coerce_diag(init, &u32, ?v_r /* already pinned to &mut u32 */)` and **aborts with `E0308: types differ in mutability (expected &mut _, found &_)`**!

Empirical verification (`support/probe_results.json`) confirms all four corners of this asymmetry across both editions:
- `loop_let_mut_first_fail` (`let r = loop { if cond { break &mut x; } break &y; };`): fails `E0308 types differ in mutability`.
- `block_let_mut_first_fail` (`let r = 'blk: { if cond { break 'blk &mut x; } &y };`): fails `E0308 types differ in mutability`.
- `lub_loop_shared_first` (`let s = loop { if cond { break &y; } break &mut x; };`) and `lub_block_shared_first` (`let r = 'blk: { if cond { break 'blk &y; } &mut x };`): both compile cleanly (`MIR` shows `s: &u32`, `r: &u32`) and output `BLK=5 LP=5`.
- `loop_and_block_stmt_no_expectation_ok` (dropping `let r =` so expectation is `NoExpectation`): both `&mut`-first `loop { ... };` and `'blk: { ... };` compile cleanly (`rc = 0`) because `coercion_target_type` sees `NoExpectation` and creates a fresh `?v_lub`!

### 5. Uninhabited Place-Read Gating (`expr_guaranteed_to_constitute_read_for_never`) and Wildcard Soundness

Basis: source + execution + normative

The Rust Reference (`r[undefined.validity.never]`, `src/undefined-behavior.md:130-131`) specifies that `"A ! value must never exist"`, and `r[undefined.validity.def]` states `"producing an invalid value is hence immediate UB"`. To keep `let _ = *p;` or `match *p { _ => ... }` sound on pointers/places of uninhabited type `!` without forcing spurious UB or treating the following statements as diverging, `rustc` inserts a syntactic place-read gate in both `check_expr_has_type_or_error` (`expr.rs:88`) and `Coerce::coerce` / expression checking (`expr.rs:306-307`), implemented by `TyCtxt::expr_guaranteed_to_constitute_read_for_never` (`compiler/rustc_middle/src/hir/mod.rs:230-325`):

- **Non-place expressions (`!expr.is_syntactic_place_expr()`):** Always return `true` (`line 236-237`), since computing an immediate produces a value of type `!`.
- **Syntactic place expressions (`*p`, field access):** Inspect `self.parent_hir_node(expr.hir_id)`:
  - `ExprKind::AddrOf | ExprKind::Field` -> `false` (`line 247`).
  - `ExprKind::Assign(lhs, _, _)` -> `expr.hir_id != lhs.hir_id` (`lines 255-258`).
  - `ExprKind::Match(scrutinee, arms, _)` -> `arms.iter().all(|arm| arm.pat.is_guaranteed_to_constitute_read_for_never())` (`lines 262-265`): if *any* arm has a wildcard (`_`), returns `false`!
  - `Node::LetStmt(LetStmt { init: Some(_), pat, .. })` -> `pat.is_guaranteed_to_constitute_read_for_never()` (`lines 307-310`): `let _ = *p;` returns `false`, whereas `let _x: () = *p;` (binding pattern `_x` reads the place into a variable) returns `true`!
  - `ExprKind::Block` / `Node::Block(_)` / `ExprKind::Type` forwarding -> `Node::Block(_)` (`line 313`) unconditionally returns **`true`**! Therefore wrapping `*p` inside `{ *p }` changes the immediate HIR parent of `*p` from `Node::LetStmt(wild)` to `Node::Block(_)`, triggering a read!

Live execution of `PROG_NEVER_ALL_DIVERGING_AND_PLACE_READ` (`rustc 1.98.0-nightly` + Miri Stacked Borrows, `support/probe_results.json`) confirms every detail of the generated post-cleanup MIR and runtime semantics on `let p: *const ! = (&dummy as *const u8).cast()`:

| Function & Syntax | `read_for_never` | Observed Post-Cleanup MIR (`1.98.0`) | Native `-O0` (`Ed2021` / `Ed2024`) | Miri Stacked Borrows (`Ed2021` / `Ed2024`) |
| :--- | :--- | :--- | :--- | :--- |
| `place_deref_wildcard`: `let _ = *p; 42` | `false` (`LetStmt` `_`) | `_0 = const 42_u32; return;` (zero deref asserts!) | `rc=0`: `MODE=wild VAL=42` / `rc=0`: `MODE=wild VAL=42` | `rc=0`: `MODE=wild VAL=42` / `rc=0`: `MODE=wild VAL=42` |
| `place_match_wildcard`: `match *p { _ => 43 }` | `false` (`Match` arm `_`) | `_0 = const 43_u32; return;` (zero deref asserts!) | `rc=0`: `MODE=match_wild VAL=43` / `rc=0`: `MODE=match_wild VAL=43` | `rc=0`: `MODE=match_wild VAL=43` / `rc=0`: `MODE=match_wild VAL=43` |
| `place_block_deref`: `let _ = { *p }; 44` | `true` (`Node::Block`) | Emits `bb0` alignment assert + `bb1` null assert on `_1`; `bb2`: `unreachable;` in Ed2021 vs `_0 = const 44_u32; return;` in Ed2024 | `rc=-4` (`SIGILL` in Ed2021) / `rc=0` `VAL=44` in Ed2024 | **BOTH FAIL `rc=1` UB:** `constructing invalid value of type !: encountered a value of the never type '!'` (`src/main.rs:28:15`) |
| `place_deref_read_unit`: `let _x: () = *p; 45` | `true` (`LetStmt` `_x`) | Emits `bb0` alignment assert + `bb1` null assert on `_1`; `bb2: { unreachable; }` in BOTH editions | **BOTH FAIL `rc=-4`** (`SIGILL` on `unreachable`) | **BOTH FAIL `rc=1` UB:** `constructing invalid value of type !: encountered a value of the never type '!'` (`src/main.rs:35:18`) |

Crucially, even though `-O0` Edition 2024 native compilation of `place_block_deref` happened to preserve `_0 = const 44_u32; return;` after `bb1` (where alignment and null checks passed on `&dummy`), **Miri immediately halts `place_block_deref` as UB in both editions** because evaluating `{ *p }` produces a `!`-typed place read inside the block!

### 6. Mechanized Lean `v4.34.1` Formalization (`HirTypeckCoercionLubAndNeverFallbackSoundness.lean`)

Basis: source + derived + execution

`support/HirTypeckCoercionLubAndNeverFallbackSoundness.lean` (`1,739` lines, `75,112` bytes, `sha256: 106fa077cbfda8391ec65b66dbcab4f4b48c03a6f1a6508134895388156fa752`) mechanizes the relational type system, `CoerceMany` algorithm, never-type fallback coercion graph, place-read gate, and Anneal trusted boundary in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). To guarantee zero kernel contamination or compiler-generated partial auxiliaries (`._unsafe_rec`), every `def` carries `noncomputable def`, no `deriving` clauses are used on recursive/container types, and all proofs use only constructive pattern matching and case splitting (`0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`). MetaM inspection across the compiled environment reports **`DECL_COUNT = 745`**, **`UNSAFE_RECS = []`**, **`UNSAFE_CINFOS = []`**, **`BAD_AXIOMS = []`**, and **`ALL_AXIOMS_USED = [propext]`**.

Key verified theorems and definitions across the module's sections:

1. **Coercion Subtyping & Dynamic Outcome Soundness (Lines 32–550):**
   - `CoerceStep` (`lines 429-462`) and `AdjustChain` (`lines 464-487`) inductively type single coercions and transitive chains over `RustTy` (`never`, `unit`, `u32`, `u8`, `bool`, `tyVar`, `ref`, `rawPtr`, `array`, `slice`, `fnItem`, `fnPtr`, `closure`).
   - `coerceStep_sound` (`lines 494-514`) and `adjustChain_preserves_inhabited` (`lines 516-521`) prove every valid adjustment sequence preserves `isInhabited` (`never_uninhabited`, `unit_inhabited`, `zeroValid_implies_inhabited`). `normal_outcome_impossible_at_never` (`lines 406-412`) proves normal evaluation cannot return a value of type `!`, grounding `NeverToAny`.
   - Constructive negative witnesses reject unsound coercions: `capturing_closure_cannot_reify` (`line 529`), `imm_ref_cannot_coerce_to_mut` (`line 536`), and `unsafe_fnptr_cannot_become_safe` (`line 543`).

2. **Soundness of `tryCoerceConcrete`, `tryFindCoercionLub`, and `CoerceMany` (Lines 551–1301):**
   - `tryCoerceConcrete_sound` (`lines 648-776`), `tryFindCoercionLub_sound` (`lines 968-989`), and `stepCoerceMany_preserves_validity` (`lines 1055-1100`): whenever `stepCoerceMany st eTy = some st'`, `AllExprsValidTo st'.exprs st'.finalTy` holds — formalizing retroactive adjustment propagation (`allExprsValidTo_extend`) across all previously coerced branches.
   - Witness theorems match the live `rustc` matrix one-for-one:
     - `lub_ref_order_independent` (`line 1107`): both `(&mut T, &T)` and `(&T, &mut T)` return `&T` under `tryFindCoercionLub`.
     - `lub_array_mut_and_shared_unsize_with_slice_hint` (`line 1135`) vs. `lub_array_slices_without_hint_fails` (`line 1162`): unsize LUB succeeds (`[derefBuiltin, borrowRef .imm, pointer .unsize]` + `[pointer .unsize]`) under slice target `.ref .imm (.slice elem)` and fails (`none`) when initialized with `.tyVar 0`.
     - `lub_same_closure_stays_zst` (`line 1182`) vs. `lub_distinct_closures_reify` (`line 1189`): same closure returns `([ ], [ ], closure ...)` while distinct non-capturing closures retroactively reify both arms via `PointerCoercion.closureFnPointer .isSafe`.
     - `lub_safe_unsafe_fndef_reifies` (`line 1202`) & `lub_raw_mut_const_witness` (`line 1215`).
     - `generic_pick_order_asymmetric` (`line 1239`): `checkGenericPick (&mut T) (&T) = none` vs `checkGenericPick (&T) (&mut T) = some (&T)`.
     - `if_vs_loop_pinning_contrast` (`line 1282`): over `runLetBoundCoerceMany`, `adjustForBranches = true` (`if`/`match`) succeeds on both `(&mut, &)` and `(&, &mut)`, whereas `adjustForBranches = false` (`loop`/`'blk`) returns `none` on `(&mut, &)` and `some (&T)` on `(&, &mut)`.

3. **Post-1.100 Unconditional Fallback & Undirected Coercion-Graph Soundness (Lines 1305–1615):**
   - `post1_100_unconditional_never_edition_invariant` (`line 1323`) & `unit_only_breaks_under_post1_100` (`line 1336`).
   - `path_preserves_never_assignment` (`line 1441`), **`default_deny_prevents_unsafe_never_instantiation`** (`line 1456`: if `LintAcceptsUnsafeFlow st`, then every unsafe variable `(u, reason)` satisfies `assign u != .never`), and `tainted_flow_forces_never_ub` (`line 1473`: any unannotated undirected-reachable unsafe variable forces `¬ zeroValid (assign u)` and refutes `LintAcceptsUnsafeFlow st`).
   - **`undirected_catches_indirect_hop`** (`line 1507`) vs. **`directed_misses_indirect_hop`** (`line 1515`), plus `undirected_catches_two_hop` (`line 1548`): formally proves why `fallback.rs:238` requires `depth_first_search_as_undirected`.
   - `place_read_gating_soundness` (`line 1596`) & `wildcard_never_place_contradiction_guarded` (`line 1613`): proves `constitutesReadForNever` evaluates `false` on `.letWildcard` and `.matchWildcard` (no `!` value read/assertion emitted), and `true` on `.blockWrap` and `.letRead`, forcing UB (`none` outcome) on dereferencing `.rawPtr` to `!`.

4. **Anneal Boundary & End-to-End Composition (`anneal_fail_closed_boundary` & `hir_typeck_coercion_lub_and_never_fallback_master_theorem`, Lines 1626–1738):**
   - `anneal_fail_closed_boundary` (`line 1676`) and `anneal_pointer_coercion_targets_unsupported` (`line 1683`) combine with `hir_typeck_coercion_lub_and_never_fallback_master_theorem` (`lines 1701-1737`) to compose all four pillars into one kernel-checked proposition.

### 7. Anneal Verification Boundary (`joshlf/anneal@c131b320e`)

Basis: source + derived

Auditing `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/{MirAst,MirSemantics}.lean`, `trusted/rustc-capture/src/driver.rs`, `trusted/audit/TrustedBoundary.lean`) reveals three concrete architectural couplings with `rustc_hir_typeck` coercions and never-type fallback:

1. **`anneal-rustc-capture` compiler pin sits in the pre-1.100 edition-split regime:** `trusted/rustc-capture/src/driver.rs:25` enforces `const COMPILER_VERSION: &str = "1.98.0-nightly (f8a08b688 2026-05-30)";` via `rustc_interface::util::rustc_version_str()`. On that compiler, Edition 2021 crates still resolve unannotated diverging inference variables to `()` (`MirTy.unit`), whereas Edition 2024 crates resolve them to `!` (`MirTy.never`). Upgrading Anneal's pinned `rustc` to `>= 1.100` will silently flip Edition 2021 diverging fallback targets in downstream crates to `MirTy.never` (proven in `post1_100_unconditional_never_edition_invariant`), potentially altering `MirSemantics` admissibility or triggering `E0277` / `zeroed::<!>()` panics unless explicit type annotations are present.
2. **All `PointerCoercion` casts and coercion targets fail closed at `Trusted.MirAst`:** `Trusted.MirAst.Rvalue` (`trusted/lean/Trusted/MirAst.lean:620-628`) omits `Rvalue::Cast` completely (`Cast` lowers to `Rvalue.unsupported`, lines `612-613`), and `Trusted.MirAst.MirTy` (`lines 312-321`) lowers `Slice`, `FnDef`, `FnPtr`, and `Closure` to `MirTy.unsupported` (`lines 308-311`). Consequently, every `PointerCoercion::{ReifyFnPointer, UnsafeFnPointer, ClosureFnPointer, MutToConstPointer, Unsize}` emitted by `Coerce::coerce` or `CoerceMany` causes `Trusted.MirSemantics.evalRvalue` / `BodyStaticAdmitted` (`isSupportedScalarOrUnitTy`, `MirSemantics.lean:721-724`) to fail closed (`FaultKind.unsupported`). Meanwhile, `&mut T -> &T` / `&*ptr` MIR reborrows emit `Rvalue::Ref`, which is represented in `MirAst.Rvalue` (`line 625`), while reference types (`MirTy.ref`) themselves remain outside `isSupportedScalarOrUnitTy` (`MirSemantics.lean:721-724`).
3. **`MirTy.never` admission and `TerminatorKind.unreachable` UB fidelity:** `Trusted.MirAst.MirTy.never` (`MirAst.lean:316`) is explicitly admitted inside `isSupportedScalarOrUnitTy` (`MirSemantics.lean:722`) and validated via `canaryNeverParamBody` (`MirSemantics.lean:2513-2564`). Executing `TerminatorKind.unreachable` evaluates to `.fault .undefined` (`MirSemantics.lean:1551-1552`), matching `Miri` and `rustc` UB when a post-`NeverToAny` or diverging branch becomes dynamically reachable (`anneal_fail_closed_boundary`).

## Boundaries

- **Known not to apply (`1.98.0` vs. `1.102.0`/HEAD edition split):** Live execution on this host ran `rustc 1.98.0-nightly (14210df0e)`, so pre-1.100 behaviors observed there — specifically requiring `#![feature(never_type)]` to name `!`, resolving diverging variables to `()` in Edition 2021, and emitting `DEPENDENCY_ON_UNIT_NEVER_TYPE_FALLBACK` — **do not apply** to `1.102.0-nightly` (`3ef0c22cd`) or upstream HEAD (`5debe6a12`), where `!` is stable syntax and Edition 2021 unconditionally falls back to `!`. Conversely, post-1.100 Edition 2021 `zeroed::<!>()` abort without Edition 2024 cannot be directly reproduced on `1.98.0` without passing `--edition=2024`.
- **Not examined (`place_block_deref` post-cleanup MIR difference in `1.98.0` Ed2021 vs Ed2024):** `probe_results.json` records that on `1.98.0-nightly`, `place_block_deref` (`let _ = { *p }; 44`) lowers `bb2` to `unreachable;` in `--edition=2021` (native `-O0` `rc = -4` `SIGILL`) yet keeps `_0 = const 44_u32; return;` in `--edition=2024` (native `-O0` `rc = 0`), while still emitting the `bb0`/`bb1` pointer alignment/null assertions and still triggering Miri UB `constructing invalid value of type !` at `let _ = { *p };` in both editions. Which MIR pass produced that `bb2` difference in `1.98.0` was not investigated.
- **Not examined (`-Znext-solver` inside `Coerce` / `coerce_unsized` vs. `coerce_unsized_old_solver`):** Although source lines for the next-generation solver branch in `try_find_coercion_lub` (`coercion.rs:1417-1425`) and `coerce_unsized` vs. `coerce_unsized_old_solver` (`coercion.rs:566-1070`) were inspected, differential compilation with `-Znext-solver` was not executed.
- **Unknown (`#![rustc_never_type_options]` attribute existence at HEAD):** The docstring at `fallback.rs:57` (`5debe6a12`) still references `#![rustc_never_type_options(fallback = ...)]`, whereas `fallback_types()` (`lines 66-111`) has no fallback-option branch; whether any attribute parsing remains elsewhere in `rustc_hir` at `5debe6a12` was not checked.
- **Not examined (broader coercion targets and targets beyond `x86_64-unknown-linux-gnu`):** Trait-object unsizing (`Box<T> -> Box<dyn Trait>`), `CoerceUnsized` custom smart pointers, `PointerCoercion::ArrayToPointer`, pin ergonomics (`coerce_pin_ref_to_ref` / `coerce_to_pin_ref`), `GenericReborrow`, `&dyn Trait` supertrait upcasting, and non-`x86_64` architectures were not benchmarked or probed.
- **Standalone Lean formalization scope:** `support/HirTypeckCoercionLubAndNeverFallbackSoundness.lean` models the type-checking, coercion-graph, place-read, and Anneal fail-closed boundary rules directly over self-contained `RustTy`, `CoerceManyState`, `InferFlowState`, and `AnnealMirTy` inductives; it does not import Anneal's `Trusted.MirSemantics` module directly and does not formalize region/lifetime borrow checking (`NLL`/`Polonius`) or full LLVM lowering.

## Evidence

### Preserved Package Artifacts

| Artifact Path (Relative to Package Root) | Lines | Bytes | SHA-256 | Role & Provenance |
| :--- | ---: | ---: | :--- | :--- |
| `support/probe_hir_typeck_coercion_lub_and_never_fallback.py` | 891 | 27,436 | `525fa2eeade5634395f34376b81d9c0363ded0b60df2c4d6574c57bd1a5dafea` | Self-contained differential `rustc`/`Miri` probe harness (reproduces Part A fallback/unsafe/place-read checks and Part B `CoerceMany` LUB + `loop`/`'blk` pinning checks across Edition 2021 and Edition 2024). |
| `support/probe_results.json` | 611 | 84,209 | `445a7c32284c2c8102fe2462ff694eef6e661ce50d67d99dc2b83d9e8fc79e21` | Sanitized output emitted on `2026-11-23` running `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` on `x86_64-unknown-linux-gnu` (`LLVM 22.1.6`). |
| `support/HirTypeckCoercionLubAndNeverFallbackSoundness.lean` | 1,739 | 75,112 | `106fa077cbfda8391ec65b66dbcab4f4b48c03a6f1a6508134895388156fa752` | Kernel-checked Lean `v4.34.1` formalization (`745` declarations, axioms `[propext]`, zero `._unsafe_rec`, zero unsafe `ConstantInfo`s, zero `sorry`). |
| `REPORT.json` | 70 | 1,970 | `ebb18022f8a888787c46275623c47ef85f728f9e3d0aea5b22bc6dd8720620dc` | Machine metadata referencing all 6 pinned commits (`observed_at: 2026-11-23`). |

### Primary Source Anchors

1. **`rust-lang/rust` @ `5debe6a1244452beced762385f88a51857a915fc` (`main` HEAD, inspected `2026-11-23`):**
   - `compiler/rustc_hir_typeck/src/fallback.rs`: `27,573` bytes (`lines 1-652`, `sha256: 61ed7bc4af400a88e9b6373462b3f532478c627770e21dd495a981e837dbac0a`, byte-identical to `3ef0c22cd`); `type_inference_fallback` (`25-45`), `fallback_types` (`66-111`, unconditional `!` fallback at `88-94`), `calculate_diverging_fallback` (`197-229`), `lint_never_type_fallback_flowing_into_unsafe_code` (`231-274`, undirected DFS at `238`), `create_coercion_graph` (`278-314`), `compute_unsafe_infer_vars` (`517-652`).
   - `compiler/rustc_hir_typeck/src/coercion.rs` (`2,289` lines): `Coerce::coerce` (`242-370`, `NeverToAny` at `249-259`), `coerce_from_inference_variable` (`373-413`), `coerce_to_ref` (`422-565`), `coerce_unsized` (`566-740`, reborrow+unsize at `659-706`), `coerce_from_fn_pointer` (`1072-1089`), `coerce_from_fn_item` (`1091-1113`), `coerce_closure_to_fn` (`1117-1134`), `coerce_to_raw_ptr` (`1136-1184`), `may_coerce` / `may_coerce_except_never` (`1222-1249`), `try_find_coercion_lub` (`1380-1535`), `CoerceMany` (`1616-1696`), `coerce_inner` (`1703-1800+`), `complete` (`2179-2188`).
   - `compiler/rustc_hir_typeck/src/expr.rs` (`2,980` lines): `check_expr_has_type_or_error` (`77-124`, `NeverToAny` + `read_for_never` check at `87-88`), `check_expr_coercible_to_type_or_error` (`138-158`), `check_expr_break` (`724-820+`, calling `coerce.coerce` at `792`), `check_expr_if` (`1135-1170+`, `try_structurally_resolve_and_adjust_for_branches` at `1155`), `check_expr_loop` (`1373-1405+`, direct `coercion_target_type` at `1383`), `check_expr_array` (`1628-1655+`, `.is_ty_var()` filter at `1644`).
   - `compiler/rustc_hir_typeck/src/_match.rs` (`564` lines): `check_expr_match` (`19-80`, `try_structurally_resolve_and_adjust_for_branches` at `63`).
   - `compiler/rustc_hir_typeck/src/fn_ctxt/checks.rs` (`3,817` lines): `check_decl_initializer` (`1166-1204`), `check_expr_block` (`1322-1415+`, direct `coercion_target_type` at `1343`).
   - `compiler/rustc_hir_typeck/src/fn_ctxt/mod.rs` (`501` lines): `ret_coercion` (`68`), `diverges` (`108`), absence of `DivergingFallbackBehavior`.
   - `compiler/rustc_middle/src/hir/mod.rs` (`507` lines): `TyCtxt::expr_guaranteed_to_constitute_read_for_never` (`230-325`).
   - `compiler/rustc_middle/src/ty/adjustment.rs` (`263` lines): `PointerCoercion` (`11-40`), `Adjustment` (`83-86`), `Adjust` (`95-114`).
   - `compiler/rustc_lint_defs/src/builtin.rs` (`6,016` lines): `NEVER_TYPE_FALLBACK_FLOWING_INTO_UNSAFE` (`4223-4227`).
   - `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs`: `ExprKind::PointerCoercion` (`158-171`).
   - `library/core/src/mem/mod.rs`: `pub const unsafe fn zeroed<T>() -> T` calling `intrinsics::assert_zero_valid::<T>()` (`757-763`).

2. **Pre-1.100 vs. Post-1.100 Toolchain Deltas:**
   - `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`): `compiler/rustc_hir_typeck/src/fallback.rs` (`765` lines, `32,918` bytes, `sha256: 97e51e8c6f0c6b7416b2407d128085b1b7af44c60a35f1d8d5a908b8904263e0`), `fn_ctxt/mod.rs` (`523` lines, `diverging_fallback_behavior` at `122`, `never_type_behavior` at `497-523`), `builtin.rs` (`4164-4200`).
   - `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`): recorded runtime, Miri, MIR, and `-O0`/`-O2` LLVM IR observations confirming Edition 2021 + Edition 2024 parity (`TAG=never RES=ok`, `rc = -6` panic in `core/src/panicking.rs:225:5`, Miri UB on `zeroed::<!>()`, and all 4 `CoerceMany` LUB patterns).

3. **Normative Reference (`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):**
   - `src/type-coercions.md` (`r[coerce]`, `lines 1-200`), `src/divergence.md` (`r[divergence.fallback]`, `lines 1-91`), `src/behavior-considered-undefined.md` (`r[undefined.validity.never]`, `lines 116-132`).

4. **Anneal Repository (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
   - `trusted/rustc-capture/src/driver.rs` (`COMPILER_VERSION` at `line 25`).
   - `trusted/lean/Trusted/MirAst.lean` (`noncomputable` / `._unsafe_rec` policy at `lines 77-91`, `MirTy` at `312-321`, `Rvalue` at `620-628`, `TerminatorKind` at `785-795`).
   - `trusted/lean/Trusted/MirSemantics.lean` (`isSupportedScalarOrUnitTy` at `721-724`, `evalRvalue` at `1240-1285`, `evalTerminator` at `1537-1569`, `BodyStaticAdmitted` / `BodyVerified` at `1730-1758`, `canaryNeverParamBody` at `2513-2564`).
   - `trusted/audit/TrustedBoundary.lean` (`lines 1-90`).

### Verification Logs

1. **Differential `rustc`/`Miri` Probe Execution (`2026-11-23`):**
   - Command: `python3 support/probe_hir_typeck_coercion_lub_and_never_fallback.py --out support/probe_results.json`
   - Outcome: Exit `0`; generated `support/probe_results.json` (`611` lines, `84,209` bytes) covering Part A (`unfeatured_never_compile`, `feature_never_native_opt{2,0}`, `feature_never_mir_excerpts`, `feature_never_miri_runs` SB/TB, `default_deny_unsafe_direct`, `default_deny_unsafe_graph_hop`, `dependency_on_unit_lint`, `all_diverging_and_place_read_mir`, `place_read_native_opt0`, `place_read_miri`) and Part B (`native_opt2`, 12 `mir_excerpts`, `miri_runs` SB/TB, `call_arg_order_{fail,ok}`, `loop_let_mut_first_fail`, `block_let_mut_first_fail`, `loop_and_block_stmt_no_expectation_ok`, `capturing_closure_lub_rejected`, `array_lub_without_slice_hint_rejected`) across both Edition 2021 and Edition 2024.

2. **Lean `v4.34.1` Kernel & Purity Check (`2026-11-23`):**
   - Command:
     `LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" anneal-lean-run --mode file -- "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/HirTypeckCoercionLubAndNeverFallbackSoundness.lean`
   - Outcome: Exit `0` with zero warnings or errors.
   - MetaM `env.constants.toList` & `Lean.collectAxioms` inspection over the elaborated environment confirmed: `DECL_COUNT=745`, `UNSAFE_RECS=[]`, `UNSAFE_CINFOS=[]`, `BAD_AXIOMS=[]`, and `ALL_AXIOMS_USED=[propext]`.

## Revalidation

Each structural and runtime finding can be independently revalidated with lightweight, targeted checks:

1. **Re-run the differential `rustc` + Miri probe harness against any target toolchain:**
   ```bash
   python3 support/probe_hir_typeck_coercion_lub_and_never_fallback.py \
     --rustc rustc --cargo cargo --out /tmp/probe_recheck.json
   ```
   Compare `part_a_never_fallback.edition_2021.feature_never_native_opt2.runs.safe.stdout`: `TAG=unit RES=ok` identifies pre-1.100 edition-split fallback, whereas `TAG=never RES=ok` (and `unfeatured_never_compile.rc == 0`) confirms post-1.100 unconditional `!` fallback. Check `part_b_coerce_many_lub.edition_2024.loop_let_mut_first_fail.rc == 1` and `array_lub_without_slice_hint_rejected.rc == 1` to confirm whether `check_expr_loop`/`check_expr_block` `?v_r` pinning and unhinted `[&[u8; 2], &[u8; 3]]` rejection still hold in newer `rustc`.

2. **Inspect upstream `rustc_hir_typeck` drift in < 1 minute via Git diff:**
   Diff `5debe6a1244452beced762385f88a51857a915fc..HEAD` across only the determining files:
   ```bash
   git diff 5debe6a1244452beced762385f88a51857a915fc..HEAD -- \
     compiler/rustc_hir_typeck/src/fallback.rs \
     compiler/rustc_hir_typeck/src/coercion.rs \
     compiler/rustc_hir_typeck/src/expr.rs \
     compiler/rustc_hir_typeck/src/_match.rs \
     compiler/rustc_hir_typeck/src/fn_ctxt/checks.rs \
     compiler/rustc_middle/src/hir/mod.rs
   ```
   Specifically check: (a) whether `check_expr_loop` (`expr.rs:1383`) or `check_expr_block` (`fn_ctxt/checks.rs:1343`) adds `.try_structurally_resolve_and_adjust_for_branches(self)` (which would fix the `let r = loop { break &mut x; break &y }` asymmetry), (b) whether `try_find_coercion_lub` (`coercion.rs:1405-1452`) gains array-to-slice unsizing, and (c) whether `fallback.rs:238` retains `depth_first_search_as_undirected`.

3. **Kernel-recheck the Lean `v4.34.1` mechanization:**
   ```bash
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/HirTypeckCoercionLubAndNeverFallbackSoundness.lean
   ```
   Confirm exit code `0` with zero diagnostics.

4. **Check Anneal capture pin and `MirAst` extension status:**
   Inspect `trusted/rustc-capture/src/driver.rs` (`COMPILER_VERSION`) and `trusted/lean/Trusted/MirAst.lean` (`Rvalue` / `MirTy`) in `joshlf/anneal` to detect when `anneal-rustc-capture` crosses into `rustc >= 1.100` (eliminating Edition 2021 `()` diverging fallback) or adds explicit `Rvalue::Cast` / `PointerCoercion` variants.
