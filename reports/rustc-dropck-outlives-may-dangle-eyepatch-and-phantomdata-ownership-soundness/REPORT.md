# `rustc_traits::dropck_outlives`, `#[may_dangle]` (`dropck_eyepatch`) Soundness, Missing-`PhantomData<T>` Use-After-Free, and `Vec<T>` Ownership-Marker Restoration

## Summary

In Rust, lexical scopes destroy initialized locals in reverse declaration order (`StorageDead` on later-declared locals executes before `Drop::drop` on earlier-declared locals). Consequently, `rustc` cannot rely solely on reflexive region outlives (`'a: 'a`) whenever a dropped container executes user-defined destructor code or element drop glue: a cyclic or reverse-ordered borrow `'a` between two locals in the same scope can leave the target slot deallocated when the container's destructor runs. Primary-source inspection of `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201` on `main` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` on `1.98.0-nightly`), `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), live execution of `12` `rustc` probes, `5` `Miri` probes, and unoptimized MIR capture (`support/probe_dropck_may_dangle_phantomdata.py`, `support/probe_results.json`), plus a `1,678`-line pure kernel-checked Lean `v4.34.1` development (`support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean`, `0` `._unsafe_rec`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, max axiom `[propext]`) establish five invariants:

1. **Non-parametric `Drop` constraint splitting (`adt_dtorck_constraint` and `destructor_constraints`):** `rustc_borrowck::type_check::liveness::trace` invokes `DropckOutlives` (`compute_dropck_outlives_with_errors`) whenever a local is drop-live at a `Drop` terminator (`liveness/trace.rs:430-455, 534-664, 785-830`). For any ADT with a `Drop` impl, `TyCtxt::destructor_constraints` (`rustc_middle/src/ty/util.rs:466-538`) places every generic lifetime, type, or const parameter whose `GenericParamDef.pure_wrt_drop` is `false` directly into `DropckConstraint.outlives`—forcing all regions in that parameter to remain live at the drop point regardless of the struct's field types (`E0597` even when `Boxed<&Cell<u32>>::drop` is empty or `PlainDropRaw<&Cell<u32>>` holds only `*mut T` + `PhantomData<T>`).
2. **`#[may_dangle]` (`pure_wrt_drop`) exemptions and missing-`PhantomData<T>` use-after-free:** Applying `#[may_dangle]` under `#![feature(dropck_eyepatch)]` sets `pure_wrt_drop = true` during AST-to-HIR lowering (`rustc_ast_lowering/src/lib.rs:2389`), requires `unsafe impl` (`E0569`, enforced in `rustc_hir_analysis/src/coherence/unsafety.rs:20-103`), and removes the marked parameter from `destructor_constraints`. When an `unsafe impl<#[may_dangle] T> Drop` container stores elements behind `*mut T` or `NonNull<T>`—whose `trivial_dropck_outlives` predicate returns `true` (`query/dropck_outlives.rs:44`)—omitting `PhantomData<T>` empties both `outlives` and `dtorck_types`. Both `rustc` (`compile_rc = 0`) and our `-Z mir-opt-level=0 --emit=mir` capture (`StorageDead(_2)` immediately preceding `drop(_1)`) show `RawBoxNoPhantom<Inspector<'_>>` compiling cleanly and aborting under `Miri` (`rc = 1`) with `Undefined Behavior: constructing invalid value of type &std::cell::Cell<u32>: encountered a dangling reference (use-after-free)` inside `<Inspector<'_> as Drop>::drop`.
3. **Orthogonality of subtyping variance and dropck ownership:** Replacing `PhantomData<T>` with `PhantomData<fn() -> T>` preserves identical `Covariant` variance on `T`, yet `trivial_dropck_outlives(ty::FnPtr)` returns `true` (`query/dropck_outlives.rs:41`). Consequently, `RawBoxFnMarker<Inspector<'_>>` triggers the exact same `Miri` UAF (`rc = 1`). Moreover, even `PhantomData<T>` only protects *nested destructors* of `T` via `dtorck_types`; when `T = &'a String` (`trivial_dropck_outlives(ty::Ref) = true`), an `unsafe impl<#[may_dangle] T: Display> Drop` that violates `pure_wrt_drop` by directly reading `*self.0` compiles (`rc = 0`) and triggers `Miri` UAF (`rc = 1`) in `<&String as Display>::fmt`.
4. **`PhantomData<T>` restoration and `Vec<T, A>` / `RawVec<T, A>` asymmetric eyepatch:** Adding `PhantomData<T>` causes `adt_dtorck_constraint` (`rustc_traits/src/dropck_outlives.rs:40-52`) to insert `T` into `dtorck_types` (not `outlives`) because `trivial_dropck_outlives(PhantomData<T>)` is explicitly `false` (`query/dropck_outlives.rs:74-78`). When `T = Inspector<'_>`, `dtorck_types` expands `Inspector<'_>` and rejects reverse-order scopes (`E0597`); when `T = &'a Cell<u32>`, `trivial_dropck_outlives` short-circuits `dtorck_types` at `ty::Ref`, allowing both `RawBox<&Cell<u32>>` and `std::vec::Vec<&Cell<u32>>` (`library/alloc/src/vec/mod.rs:448-451, 4595-4608`, backed by `RawVec<T, A>` carrying `_marker: PhantomData<T>` in `library/alloc/src/raw_vec/mod.rs:78-81`) to compile and pass `Miri` (`rc = 0`, `DROPCK_SAFE=2`). Meanwhile, `Vec<T, A>` keeps allocator parameter `A` un-eyepatched so `RawVec::drop` (`A::deallocate`) still forces `A` to outlive `Vec`.
5. **Mechanized Lean `v4.34.1` soundness, strict inclusion, and Anneal TCB mapping:** In `RustcDropckMayDanglePhantomData` (`support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean`), we prove: (a) general scope soundness `dropck_accepts_scope_implies_no_dangling_read` under `PureWrtDrop` and `PhantomData` ownership honesty, plus `conservative_dropck_scope_implies_no_dangling_read` showing conservative mode protects even dishonest `#[may_dangle]` impls; (b) constructive UAF counterexamples for missing `PhantomData<T>`, `PhantomData<fn() -> T>`, and untruthful `pure_wrt_drop`, alongside `PhantomData<T>` rejection restoration; (c) `trivialDropckOutlives_implies_dropRVal_ok` for general trivial types plus `Vec`/`RawBox` restoration and `Vec`/`BTreeMap` allocator-parameter asymmetry; and (d) strict inclusion `conservative_implies_eyepatch_phantom_scope` (`Conservative ⊊ Eyepatch + PhantomData`) via `strict_inclusion_between_dropck_regimes`. In `joshlf/anneal@c131b320`, `Trusted.MirAst` erases regions on `MirTy.ref` and fails closed (`FaultKind.unsupported`) on `TerminatorKind.Drop` and non-fieldless-enum ADTs (`MirAst.lean:304-321, 782-795`); any future MIR extension enabling `Drop` on generic containers must enforce these invariants.

## Applicability

This report characterizes `rustc` drop checking, `#[may_dangle]` (`dropck_eyepatch`), `PhantomData<T>` dropck ownership, and `Vec<T, A>` / `RawVec<T, A>` container markers across the four durable upstream subjects in `REPORT.json`:

- **Primary compiler and standard library source (`rust-lang/rust@20fe935d50367c0ff8872c2ebfa050c5c99d9201`):** Direct line-by-line inspection of `compiler/rustc_traits/src/dropck_outlives.rs`, `compiler/rustc_middle/src/ty/util.rs`, `compiler/rustc_middle/src/ty/generics.rs`, `compiler/rustc_middle/src/ty/adt.rs`, `compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs`, `compiler/rustc_borrowck/src/type_check/liveness/trace.rs`, `compiler/rustc_ast_lowering/src/lib.rs`, `compiler/rustc_passes/src/check_attr.rs`, `compiler/rustc_hir_analysis/src/coherence/unsafety.rs`, `library/alloc/src/vec/mod.rs`, `library/alloc/src/raw_vec/mod.rs`, `library/alloc/src/boxed.rs`, `library/core/src/marker.rs`, `library/core/src/ptr/non_null.rs`, and `library/core/src/mem/manually_drop.rs`.
- **Empirical compiler, MIR, and `Miri` execution toolchain (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):** Live execution of `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (LLVM `22.1.6`, host and target `x86_64-unknown-linux-gnu`) and `miri 0.1.0 (14210df0e2 2026-05-31)` on `--edition=2024` probes (`support/probe_dropck_may_dangle_phantomdata.py`, `support/probe_results.json`), plus direct source diffing against `20fe935d5036`.
- **Cross-revision continuity and deltas (`14210df0e` vs. `20fe935d5`):** Direct file-level `diff -u` across both `rust-lang/rust` revisions establishes that the core `dropck_outlives` algorithms (`adt_dtorck_constraint`, `dedup_dtorck_constraint`, `destructor_constraints`, `trivial_dropck_outlives`, `compute_dropck_outlives_with_errors`, and borrowck `compute_drop_live_points_for`) share identical logic and error semantics across both revisions. Three concrete source changes occurred between `14210df0e` (`2026-05-31`) and `20fe935d5` (`2026-11-24`):
  1. `library/alloc/src/raw_vec/mod.rs`: `RawVecInner<A>` migrated from `ptr: Unique<u8>` (`14210df0e` line `86`) to `ptr: NonNull<u8>` (`20fe935d5` line `91`), deleting `Unique<T>` from `RawVec` and updating `RawVec`'s doc comment (`20fe935d5` line `67`) to state explicitly: `"Carries PhantomData<T> for auto trait and may_dangle correctness."`
  2. `library/alloc/src/vec/mod.rs`: `Allocator` on `Vec<T, A>` moved from `#[unstable(feature = "allocator_api", issue = "32838")]` (`14210df0e` line `438`) to `#[stable(feature = "allocator_api", since = "1.100.0")]` (`20fe935d5` line `448`), and `Drop for Vec<T, A>` moved from `unsafe impl<#[may_dangle] T, A: Allocator>` (`14210df0e` line `4286`) to `const unsafe impl<#[may_dangle] T: [const] Destruct, A: [const] Allocator + [const] Destruct>` (`20fe935d5` line `4595`).
  3. `compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs`: `20fe935d5` adds an `unimplemented!()` arm for experimental `ty::View(..)` (`lines 93, 425`), widens `Err` from `Vec<E>` to `ThinVec<E>`, and removes `stack::ensure_sufficient_stack` around `Array`/`Slice` recursion (`line 294`), leaving `trivial_dropck_outlives` and `compute_dropck_outlives_with_errors` semantics unchanged.
- **Anneal trusted boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Direct inspection of `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/audit/TrustedBoundary.lean`, and `trusted/rustc-capture/src/driver.rs` (`rustc 1.98.0-nightly`) establishes how Anneal handles regions, `StorageDead`, `deinitMovedPlace = true`, `TerminatorKind::Drop`, and kernel purity checks.
- **Mechanized proof checker (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** All proofs in `support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean` (`1,678` lines) are kernel-checked under Lean `v4.34.1` with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and verified via Lean MetaM (`audit_metam.lean` check) to contain `0` `._unsafe_rec` constants, `0` `unsafe` constants, `0` `partial` definitions, and union axiom set `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).
- **Model–system relation:** No mechanized simulation or abstraction proof connects `RustcDropckMayDanglePhantomData` in Lean directly to the `rustc` compiler binary or `Miri` interpreter. The Lean development formalizes a fixed-arity structural ADT and lexical-scope drop model constructed directly from the audited `rustc` source definitions; empirical agreement between the Lean model and `rustc`/`Miri` is established separately across all tested scenarios (`derived` modeling correspondence backed by `12` `rustc`, `5` `Miri`, and `1` MIR probe executions).
- **Stability and edition scope:** Non-eyepatched `Drop` (`E0597`), `PhantomData<T>`, `ManuallyDrop<T>`, and `Vec<T>`'s standard-library behavior apply on stable Rust (`--edition=2024` and earlier editions). Authoring user-defined `#[may_dangle]` destructors requires nightly `#![feature(dropck_eyepatch)]` (`rust-lang/rust#34761`).
- **Adjacent corpus reports:** Complements [drop-check-may-dangle-and-destructor-soundness-for-generic-containers](../drop-check-may-dangle-and-destructor-soundness-for-generic-containers/REPORT.md) (which proves `noUseSuffices`, `headNoDrop`, and `deepNoDrop` policy comparisons in an RFC-level toy model without running `rustc`/`Miri`) and [rustc-variance-dropck-may-dangle-rpit-capture-and-dispatch-from-dyn](../rustc-variance-dropck-may-dangle-rpit-capture-and-dispatch-from-dyn/REPORT.md) (which covers the 4-element variance lattice, Edition 2024 RPIT capture, and `CoerceUnsized`/`DispatchFromDyn` alongside a compact `Dropck` summary). This package extends both with a deep audit of `rustc_traits::dropck_outlives` / `destructor_constraints` / `RawVecInner` post-`Unique<T>` migration, `-Z mir-opt-level=0` `StorageDead` ordering proof, 17-probe `rustc`+`Miri` differential verification, and a standalone `1,678`-line `Quot.sound`-free Lean `v4.34.1` soundness/counterexample/inclusion proof suite.

## Findings

### 1. The `rustc` Drop-Check Pipeline: `liveness::trace`, `adt_dtorck_constraint`, `destructor_constraints`, and `trivial_dropck_outlives`

Basis: source + execution + derived

#### 1.1 Borrow-Checker Drop-Liveness Invocation (`liveness/trace.rs`)

During NLL borrow checking (`compiler/rustc_borrowck/src/type_check/liveness/trace.rs`), `LivenessComputation::compute` (`lines 390-455`) distinguishes **use-liveness** (`use_live_at`, requiring *all* regions in `local_ty` to be live at CFG points before an ordinary read/move) from **drop-liveness** (`drop_live_at`, covering CFG points after a local's last use where it remains at least partially initialized and reaches a `TerminatorKind::Drop`):

```rust
// compiler/rustc_borrowck/src/type_check/liveness/trace.rs:421-454 (rust-lang/rust@20fe935d5036)
        if !self.use_live_at.is_empty() {
            make_all_regions_live(
                self.infcx,
                universal_regions,
                liveness_constraints,
                local_ty,
                &self.use_live_at,
            );
        }
        if !self.drop_live_at.is_empty() {
            let drop_data = get_drop_args();
            ...
            for &kind in drop_data {
                make_all_regions_live(
                    self.infcx,
                    universal_regions,
                    liveness_constraints,
                    kind,
                    &drop_live_at,
                );
            }
        }
```

When `compute_drop_live_points_for` (`lines 534-563`) finds at least one initialized drop point via `MaybeInitializedPlaces`, `compute_for_local` (`lines 146-188`) invokes `dropck_local` (`lines 785-830`), which performs the canonical trait query `DropckOutlives { dropped_ty: local_ty }` (`line 792`). Only the generic arguments returned in `dropck_result.kinds` (together with `region_constraint_data`) are constrained to remain live across `drop_live_at` points (`lines 167-187, 445-453`).

#### 1.2 Query Pipeline: `adt_dtorck_constraint`, `destructor_constraints`, and `trivial_dropck_outlives`

The `dropck_outlives` query (`compiler/rustc_traits/src/dropck_outlives.rs:20-29`) delegates to `compute_dropck_outlives_inner` / `compute_dropck_outlives_with_errors` (`compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs:97-253`), which iteratively drains a `FxHashSet`-deduplicated DFS worklist (`ty_stack`, `ty_set` at `lines 155-249`) populated by `dtorck_constraint_for_ty_inner` (`lines 258-427`) and per-ADT query `adt_dtorck_constraint` (`compiler/rustc_traits/src/dropck_outlives.rs:32-65`).

```rust
// compiler/rustc_traits/src/dropck_outlives.rs:32-73 (rust-lang/rust@20fe935d5036)
pub(crate) fn adt_dtorck_constraint(tcx: TyCtxt<'_>, def_id: DefId) -> &DropckConstraint<'_> {
    let def = tcx.adt_def(def_id);
    let span = tcx.def_span(def_id);
    let typing_env = ty::TypingEnv::non_body_analysis(tcx, def_id);

    if def.is_manually_drop() {
        bug!("`ManuallyDrop` should have been handled by `trivial_dropck_outlives`");
    } else if def.is_phantom_data() {
        let args = GenericArgs::identity_for_item(tcx, def_id);
        assert_eq!(args.len(), 1);
        let result = DropckConstraint {
            outlives: vec![],
            dtorck_types: vec![args.type_at(0)],
            overflows: vec![],
        };
        return tcx.arena.alloc(result);
    }

    let mut result = DropckConstraint::empty();
    for field in def.all_fields() {
        let fty = tcx.type_of(field.did).instantiate_identity().skip_norm_wip();
        dtorck_constraint_for_ty_inner(tcx, typing_env, span, 0, fty, &mut result);
    }
    result.outlives.extend(tcx.destructor_constraints(def));
    dedup_dtorck_constraint(&mut result);
    tcx.arena.alloc(result)
}
```

Four exact compiler mechanics determine what ends up in `DropckOutlivesResult.kinds`:

1. **`trivial_dropck_outlives(tcx, ty)` short-circuit (`query/dropck_outlives.rs:28-95`):**
   - Returns **`true`** (zero `outlives` and zero `dtorck_types`) for primitives (`Bool`, `Int`, `Uint`, `Float`, `Char`, `Never`, `Str`), `FnDef`, **`FnPtr`**, **`RawPtr(_, _)`**, **`Ref(..)`**, `Foreign`, `CoroutineWitness`, `[T; 0]` (`lines 52-58`), and **`ManuallyDrop<T>`** (`def.is_manually_drop()` at `lines 69-72`).
   - Recurses on `[T]` / `ty::Pat` (`line 51`), non-zero-length `[T; N]` (`line 56`), tuples (`line 62`), and closure upvars (`lines 64-67`).
   - Returns **`false`** for all other ADTs (`lines 73-79`)—explicitly including **`PhantomData<T>`** (`"PhantomData doesn't have a dtor, but it is considered to own its content, so it is non-trivial"`, `lines 74-76`).
2. **`PhantomData<T>` moves `T` into `dtorck_types`, not `outlives` (`traits/dropck_outlives.rs:40-52`):**
   `adt_dtorck_constraint` special-cases `def.is_phantom_data()` to emit `outlives: vec![]` and `dtorck_types: vec![args.type_at(0)]`. Thus, `PhantomData<T>` never forces `T`'s regions to live unless `T` itself (or a transitive field of `T`) requires dropck liveness.
3. **`TyCtxt::destructor_constraints(def)` places non-`#[may_dangle]` `Drop` parameters into `outlives` (`rustc_middle/src/ty/util.rs:466-538`):**
   ```rust
   // compiler/rustc_middle/src/ty/util.rs:510-535 (rust-lang/rust@20fe935d5036)
        let result = iter::zip(item_args, impl_args)
            .filter(|&(_, arg)| {
                match arg.kind() {
                    GenericArgKind::Lifetime(region) => match region.kind() {
                        ty::ReEarlyParam(ebr) => {
                            !impl_generics.region_param(ebr, self).pure_wrt_drop
                        }
                        _ => false,
                    },
                    GenericArgKind::Type(ty) => match *ty.kind() {
                        ty::Param(pt) => !impl_generics.type_param(pt, self).pure_wrt_drop,
                        _ => false,
                    },
                    GenericArgKind::Const(ct) => match ct.kind() {
                        ty::ConstKind::Param(pc) => {
                            !impl_generics.const_param(pc, self).pure_wrt_drop
                        }
                        _ => false,
                    },
                }
            })
            .map(|(item_param, _)| item_param)
            .collect();
   ```
   When AST lowering processes a generic parameter on an item (`compiler/rustc_ast_lowering/src/lib.rs:2389`), `pure_wrt_drop` is initialized to `attr::contains_name(&param.attrs, sym::may_dangle)`. On any `Drop` impl without `#[may_dangle]`, `!pure_wrt_drop` evaluates to `true` for every matched generic parameter (`lifetime`, `type`, or `const`), appending those parameters straight into `result.outlives` (`traits/dropck_outlives.rs:59`). Everything in `outlives` is unconditionally appended to `DropckOutlivesResult.kinds` (`query/dropck_outlives.rs:180`) without checking `trivial_dropck_outlives`.
4. **`#[may_dangle]` gatekeeping (`check_attr.rs:938-963`, `coherence/unsafety.rs:20-103`):**
   `check_may_dangle` (`compiler/rustc_passes/src/check_attr.rs:939-963`) rejects `#[may_dangle]` outside lifetime or type generic parameters on `LangItem::Drop` impls (`diagnostics::InvalidMayDangle`), and `coherence::unsafety::check_item` (`compiler/rustc_hir_analysis/src/coherence/unsafety.rs:20-21, 89-103`) requires an `unsafe impl` whenever any own generic parameter has `pure_wrt_drop == true`, emitting `error[E0569]: requires an 'unsafe impl' declaration due to '#[may_dangle]' attribute`.

#### 1.3 Empirical Verification of Conservative RFC 1238 Dropck

Live `rustc 1.98.0-nightly` probes (`support/probe_results.json`) verify all four boundary conditions predicted by `destructor_constraints`:

- **`Boxed<T>(T)` with plain `impl<T> Drop for Boxed<T> { fn drop(&mut self) {} }` (`a_boxed_sibling_declared_after_rejected_e0597`):** Declaring `let boxed;` before `let cell = Cell::new(1u32); boxed = Boxed(&cell);` is rejected with `error[E0597]: 'cell' does not live long enough` (`borrow might be used here, when 'boxed' is dropped and runs the 'Drop' code for type 'Boxed'`), even though `Boxed::drop` does nothing and `&Cell<u32>` has `trivial_dropck_outlives == true`. Reordering `let cell` before `let boxed` (`a_boxed_sibling_declared_before_ok`) compiles and outputs `BOXED_BEFORE_OK=1`.
- **`PlainDropRaw<T>(*mut T, PhantomData<T>)` with plain `impl<T> Drop` (`a_plain_drop_with_raw_ptr_field_still_e0597`):** Storing `&cell` behind `*mut T` still fails with `E0597` when `Drop` lacks `#[may_dangle]`, confirming `destructor_constraints` places `T` into `outlives` independently of the struct's fields.
- **`PlainBox<T>(T)` without `impl Drop` (`a_plain_no_drop_allows_cyclic_borrow_ok`):** Omitting `Drop` leaves `destructor_constraints == []`; `PlainBox(&cell)` recurses into field `T = &Cell<u32>`, hits `trivial_dropck_outlives(&Cell<u32>) == true`, compiles cleanly, and runs (`PLAIN_NO_DROP_OK=1`).
- **`impl<#[may_dangle] T> Drop` without `unsafe` (`b_may_dangle_without_unsafe_impl_rejected`):** Rejected with exact `E0569` diagnostic matching `coherence/unsafety.rs:94-101`.

---

### 2. `#[may_dangle]` Soundness Coupling, Missing-`PhantomData<T>` UAF Witness, and Variance Orthogonality

Basis: source + execution + derived

#### 2.1 How Missing `PhantomData<T>` Under `#[may_dangle]` Produces Live Use-After-Free

Consider a generic raw-pointer owner without `PhantomData<T>`:

```rust
#![feature(dropck_eyepatch)]
struct RawBox<T>(*mut T);

unsafe impl<#[may_dangle] T> Drop for RawBox<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.0)); } // drops the owned `T`!
    }
}
```

Tracing `adt_dtorck_constraint(RawBox)` (`rustc_traits/src/dropck_outlives.rs:32-65`):
1. `destructor_constraints(RawBox)` sees `impl_generics.type_param(T).pure_wrt_drop == true` (`#[may_dangle] T`), returning **`outlives = []`**.
2. `def.all_fields()` contains a single field `*mut T` (`ty::RawPtr(T, Mut)`). `dtorck_constraint_for_ty_inner` calls `trivial_dropck_outlives(*mut T)` (`query/dropck_outlives.rs:44`), which returns **`true`**, short-circuiting immediately (`line 271`) and returning **`dtorck_types = []`**.
3. Thus `DropckOutlives { dropped_ty: RawBox<Inspector<'_>> }` returns **`kinds = []`**!

Because `compute_drop_live_points_for` marks zero regions live across `drop_live_at` for `raw: RawBox<Inspector<'_>>`, NLL borrowck allows `let cell = Cell::new(1u32);` to be declared *after* `raw` and destroyed *before* `drop(raw)`. Our live `-Z mir-opt-level=0 --emit=mir` capture (`support/probe_results.json`, `mir_drop_order_evidence.fn_main_mir`) directly observes the exact MIR basic block `bb3` emitted for `main()`:

```text
    scope 1 {
        debug raw => _1;
        let _2: std::cell::Cell<u32>;
        scope 2 {
            debug cell => _2;
            scope 3 { }
        }
    }
    ...
    bb3: {
        ...
        _1 = move _3;
        ...
        _0 = const ();
        StorageDead(_2);
        drop(_1) -> [return: bb4, unwind: bb5];
    }
```

`StorageDead(_2)` deallocates `cell`'s stack slot (`_2`) **immediately before** `drop(_1)` invokes `<RawBox<Inspector<'_>> as Drop>::drop`, which executes `Box::from_raw(self.0)` and runs `<Inspector<'_> as Drop>::drop`. Running this exact program under `cargo +nightly miri run --offline` (`miri_eyepatch_without_phantom_unsound_inspector_uaf`) prints `REACHED_END_BEFORE_DROP=1` and aborts (`returncode = 1`) with Miri's dangling-reference diagnostic:

```text
error: Undefined Behavior: constructing invalid value of type &std::cell::Cell<u32>: encountered a dangling reference (use-after-free)
 --> src/main.rs:9:9
  |
9 |         self.0.set(self.0.get() + 10);
  |         ^^^^^^ Undefined Behavior occurred here
  ...
          0: <Inspector<'_> as std::ops::Drop>::drop
          ...
          4: <RawBox<Inspector<'_>> as std::ops::Drop>::drop
          5: std::ptr::drop_glue::<RawBox<Inspector<'_>>>
          6: main
```

#### 2.2 Why Variance-Only Markers (`PhantomData<fn() -> T>`) Still Trigger Identical UAF

A common misconception is that `PhantomData<T>` is needed merely to fix variance on `*mut T` (which is invariant, whereas `NonNull<T>` is already covariant). In `compiler/rustc_hir_analysis/src/variance/`, `PhantomData<T>` and `PhantomData<fn() -> T>` induce **identical `Covariant` variance** on `T` (`Covariant.xform(Covariant) = Covariant`). Yet `adt_dtorck_constraint` on `RawBoxFnMarker<T>(*mut T, PhantomData<fn() -> T>)` expands `PhantomData<fn() -> T>` into `dtorck_types = [fn() -> T]`, and on the next worklist iteration `trivial_dropck_outlives(ty::FnPtr)` returns **`true`** (`query/dropck_outlives.rs:41`). Empirical `rustc` and `Miri` probes (`d_eyepatch_with_phantom_fn_ptr_still_compiles`, `miri_eyepatch_with_phantom_fn_ptr_uaf`) confirm that `RawBoxFnMarker<Inspector<'_>>` compiles (`rc = 0`), prints `REACHED_END_WITH_FN_MARKER=1`, and aborts in `Miri` (`rc = 1`) with the identical UAF in `<Inspector<'_> as Drop>::drop`. Only `PhantomData<T>` (or an un-eyepatched `T`) places `T` itself onto `dtorck_types`.

#### 2.3 Why `PhantomData<T>` Cannot Catch Direct Reads Inside `#[may_dangle]` `Drop` (`pure_wrt_drop` Violation)

`PhantomData<T>` only registers ownership for `T`'s *own destructor* via `dtorck_types`. When `T = &'a String` (`Copy`, `trivial_dropck_outlives(&'a String) == true` at `query/dropck_outlives.rs:45`), `PhantomData<&'a String>` expands `&'a String` and immediately terminates with zero region obligations (`kinds = []`). Consequently, if `unsafe impl<#[may_dangle] T: Display> Drop for LiarBox<T>` violates the `pure_wrt_drop` contract by directly reading/formatting `*self.0` inside `Drop::drop` (`f_eyepatch_with_phantom_liar_reads_ref_compiles`), `rustc` compiles cleanly (`rc = 0`) and `Miri` aborts (`rc = 1`, `miri_eyepatch_with_phantom_liar_reads_ref_uaf`) at `<&std::string::String as std::fmt::Display>::fmt` with `encountered a dangling reference (use-after-free)`. Sound `unsafe impl<#[may_dangle] T> Drop` therefore demands **two independent safety invariants**:
1. **Parametric purity (`pure_wrt_drop`):** The `Drop::drop` body itself must not access any value or borrow behind `T` (other than moving/dropping `T` via `drop_in_place` or freeing raw memory).
2. **Ownership declaration (`PhantomData<T>`):** If `Drop::drop` runs `T`'s destructor (`drop_in_place`, `Box::from_raw`, `ptr::read`), the type must contain a field that places `T` into `dtorck_types` (`T` directly or `PhantomData<T>`).

---

### 3. `PhantomData<T>` Drop-Check Restoration, `Vec<T, A>` / `RawVec<T, A>`, and `ManuallyDrop<T>` Boundaries

Basis: source + execution + derived

#### 3.1 `PhantomData<T>` Restoration on Custom Containers and `std::vec::Vec<T>`

Adding `_marker: PhantomData<T>` to `struct RawBox<T>(*mut T, PhantomData<T>)` causes `adt_dtorck_constraint` to emit `outlives: []` (from `#[may_dangle] T`) and `dtorck_types: [PhantomData<T>]` $\to$ `[T]`:
- **Non-trivial element (`T = Inspector<'_>`):** `compute_dropck_outlives_with_errors` pops `Inspector<'_>`, sees its un-eyepatched `Drop` impl, puts `'_` into `result.kinds`, and `rustc` rejects `let raw; let cell = ...; raw = RawBox(..., PhantomData)` with `error[E0597]: 'cell' does not live long enough` (`e_eyepatch_with_phantom_rejects_inspector_e0597`).
- **Trivial element (`T = &'a Cell<u32>`):** `dtorck_types` pops `&'a Cell<u32>` and short-circuits on `trivial_dropck_outlives(ty::Ref) == true` (`query/dropck_outlives.rs:45`), returning `kinds = []` and allowing dangling `&'a Cell<u32>` elements soundly (`DROPCK_SAFE=2` in both native execution and `Miri`, `e_eyepatch_with_phantom_and_std_vec_allow_trivial_ref_exec` and `miri_eyepatch_with_phantom_and_std_vec_trivial_ref_safe`).

In the Rust standard library, `Vec<T, A>` relies on this exact two-layer chain:

```rust
// library/alloc/src/vec/mod.rs:448-451, 4595-4608 (rust-lang/rust@20fe935d5036)
pub struct Vec<T, #[stable(feature = "allocator_api", since = "1.100.0")] A: Allocator = Global> {
    buf: RawVec<T, A>,
    len: usize,
}

const unsafe impl<#[may_dangle] T: [const] Destruct, A: [const] Allocator + [const] Destruct> Drop
    for Vec<T, A>
{
    fn drop(&mut self) {
        unsafe {
            self.as_mut_ptr().cast_slice(self.len).drop_in_place()
        }
        // RawVec handles deallocation
    }
}
```

And inside `library/alloc/src/raw_vec/mod.rs` (`20fe935d5036` lines `78-99, 439-445, 909-917`):

```rust
pub(crate) struct RawVec<T, A: Allocator = Global> {
    inner: RawVecInner<A>,
    _marker: PhantomData<T>,
}

struct RawVecInner<A: Allocator = Global> {
    ptr: NonNull<u8>,
    cap: Cap,
    alloc: A,
}

const unsafe impl<#[may_dangle] T, A: [const] Allocator + [const] Destruct> Drop for RawVec<T, A> {
    fn drop(&mut self) {
        unsafe { self.inner.deallocate(T::LAYOUT) }
    }
}
```

Tracing `adt_dtorck_constraint(Vec<T, A>)`:
1. `Vec`'s `Drop` impl marks `T` as `#[may_dangle]` (`pure_wrt_drop = true`) while leaving **`A` un-eyepatched** (`pure_wrt_drop = false`), so `destructor_constraints(Vec)` emits `outlives = [A]`.
2. Field `buf: RawVec<T, A>` enters `dtorck_types`. `RawVec`'s `Drop` impl likewise marks `T` as `#[may_dangle]` and `A` un-eyepatched (`outlives = [A]`), while `RawVec`'s fields push `_marker: PhantomData<T>` $\to$ `T` and `inner: RawVecInner<A>` $\to$ `NonNull<u8>` (trivial!) + `alloc: A` into `dtorck_types`.
3. `dedup_dtorck_constraint` (`traits/dropck_outlives.rs:67-73`) deduplicates `A` in `outlives` and `T` in `dtorck_types`. Because `Vec::drop` calls `self.alloc.deallocate(ptr, layout)` via `RawVecInner::deallocate` (`raw_vec/mod.rs:909-917`), keeping `A` in `outlives` guarantees any borrowed allocator (such as `&'a Arena`) strictly outlives the `Vec`, while `PhantomData<T>` on `RawVec` ensures `Vec::drop`'s `drop_in_place()` cannot invoke a dangling `Inspector::drop`.

#### 3.2 Historical `Unique<T>` Migration (`14210df0e` $\to$ `20fe935d5`) and `ManuallyDrop<T>`

At `rust-lang/rust@14210df0e` (`1.98.0-nightly`), `RawVecInner` held `ptr: Unique<u8>` (`raw_vec/mod.rs:86`), while `RawVec<T, A>` already carried `_marker: PhantomData<T>` (`line 75`). By `20fe935d5`, `Unique<T>` was removed from `RawVec` (`NonNull<u8>` + explicit `Send`/`Sync`/`UnwindSafe` impls at `lines 102-104`) and from `Box` (`BoxRaw<T> { pointer: NonNull<T>, _marker: PhantomData<T> }` at `library/alloc/src/boxed.rs:238-241`), making the `PhantomData<T>` ownership marker directly explicit on both `RawVec` and `BoxRaw`.

Separately, `ManuallyDrop<T>` (`library/core/src/mem/manually_drop.rs:152-158`) is the unique standard-library transparent wrapper whose `trivial_dropck_outlives` returns **`true`** (`query/dropck_outlives.rs:70-72`). Our probe `e_manually_drop_trivial_dropck_exec` / `miri_manually_drop_trivial_dropck_safe` verifies that `let guard; let cell = Cell::new(1u32); guard = ManuallyDrop::new(Inspector(&cell));` compiles cleanly and passes `Miri` (`MANUALLY_DROP_SAFE=1`) because `ManuallyDrop` never invokes `Inspector::drop`.

---

### 4. Complete Live Empirical Matrix (`12` `rustc`, `5` `Miri`, `1` MIR Capture)

Basis: execution

All probes executed cleanly inside `with tempfile.TemporaryDirectory():` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)` with `--edition=2024` and zero compiler warnings (`support/probe_dropck_may_dangle_phantomdata.py`, full scrubbed artifacts in `support/probe_results.json`):

| Probe ID | Type / `Drop` Signature | Scope Order / Test | `rustc` (`rc`) | Exec / `Miri` (`rc`) | Key Output / Diagnostic |
| :--- | :--- | :--- | :---: | :---: | :--- |
| `a_boxed_sibling_declared_after_rejected_e0597` | `Boxed<T>(T)`, plain `impl<T> Drop` | `(boxed, cell)` | **`1` (`E0597`)** | — | `borrow might be used here, when 'boxed' is dropped` |
| `a_boxed_sibling_declared_before_ok` | `Boxed<T>(T)`, plain `impl<T> Drop` | `(cell, boxed)` | `0` | Native `0` | `BOXED_BEFORE_OK=1` |
| `a_plain_no_drop_allows_cyclic_borrow_ok` | `PlainBox<T>(T)`, no `Drop` | `(boxed, cell)` | `0` | Native `0` | `PLAIN_NO_DROP_OK=1` |
| `a_plain_drop_with_raw_ptr_field_still_e0597` | `PlainDropRaw<T>(*mut T, PhantomData<T>)`, plain `Drop` | `(raw, cell)` | **`1` (`E0597`)** | — | `destructor_constraints` puts `T` in `outlives` despite `*mut T` |
| `b_may_dangle_without_unsafe_impl_rejected` | `impl<#[may_dangle] T> Drop` (non-`unsafe`) | trait impl check | **`1` (`E0569`)** | — | `requires an 'unsafe impl' declaration due to '#[may_dangle]'` |
| `c_eyepatch_without_phantom_allows_dangling_ref` | `RawBoxNoPhantom<T>(*mut ManuallyDrop<T>)`, `#[may_dangle] T` | `(raw, cell)` | `0` | Native `0` | `NO_PHANTOM_REF_OK=1` |
| `c_eyepatch_without_phantom_allows_unsound_inspector_compile` + `miri_..._uaf` | `RawBox<Inspector<'_>>(*mut T)`, `#[may_dangle] T` (drops `T`) | `(raw, cell)` | **`0`** | **`Miri 1` (UAF)** | `REACHED_END_BEFORE_DROP=1` then `encountered a dangling reference` at `Inspector::drop` |
| `d_eyepatch_with_phantom_fn_ptr_still_compiles` + `miri_..._uaf` | `RawBoxFnMarker<Inspector<'_>>(*mut T, PhantomData<fn() -> T>)` | `(raw, cell)` | **`0`** | **`Miri 1` (UAF)** | `REACHED_END_WITH_FN_MARKER=1` then `encountered a dangling reference` at `Inspector::drop` |
| `e_eyepatch_with_phantom_rejects_inspector_e0597` | `RawBox<Inspector<'_>>(*mut T, PhantomData<T>)`, `#[may_dangle] T` | `(raw, cell)` | **`1` (`E0597`)** | — | `PhantomData<T>` puts `T` in `dtorck_types`, catching `Inspector` |
| `e_eyepatch_with_phantom_and_std_vec_allow_trivial_ref_exec` + `miri_..._safe` | `Vec<&Cell<u32>>` + `RawBox<&Cell<u32>>` (`PhantomData<T>`) | `(v, raw, cell)` | `0` | Native `0` / `Miri 0` | `DROPCK_SAFE=2` |
| `e_manually_drop_trivial_dropck_exec` + `miri_..._safe` | `ManuallyDrop<Inspector<'_>>` | `(guard, cell)` | `0` | Native `0` / `Miri 0` | `MANUALLY_DROP_SAFE=1` |
| `f_eyepatch_with_phantom_liar_reads_ref_compiles` + `miri_..._uaf` | `LiarBox<&String>(*mut T, PhantomData<T>)`, `#[may_dangle] T` (reads `T`) | `(raw, text)` | **`0`** | **`Miri 1` (UAF)** | `encountered a dangling reference` in `<&String as Display>::fmt` |

---

### 5. Kernel-Checked Lean `v4.34.1` Formalization (`RustcDropckMayDanglePhantomData`)

Basis: source + execution (Lean `v4.34.1` kernel check & MetaM environment audit)

`support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean` (`1,678` lines, `649` constants, `176` total theorems including `23` top-level theorems) mechanizes the `rustc` dropck algorithm, stack-scope reverse-order execution, honesty invariants, and soundness/counterexample/inclusion proofs in pure core Lean `v4.34.1` (`0` `._unsafe_rec`, `0` `unsafe`, `0` `partial`, `0` `sorryAx`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, union axioms `[propext]`). Every `def` is marked `noncomputable def`, every `Bool` conditional uses definitional `bIf` rather than `Decidable` `ite`, and `Ty` uses fixed-arity constructors so every recursive pass reduces directly via `Ty.rec`.

#### 5.1 Formalized `rustc` Dropck Predicates and Stack-Scope Semantics

Key definitions mirroring `rustc` (`support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean:30-701`):
- `trivialDropckOutlives : Ty → Bool` (`lines 317-330`): returns `true` for `.prim`, `.cellU32`, `.ref`, `.rawPtr`, `.fnPtr`, `.array0`, `.manuallyDrop`, recurses on `.arrayPos`/`.pair`, and returns `false` for `.phantomData`, `.adt1`, `.adt2`, `.regAdt`.
- `destructorConstraintRegions` (`lines 357-372`): returns `[]` if `!dropMeta.hasDrop`; otherwise extracts `collectAllRegions` for every parameter where `ignoreEyepatch || !dropMeta.pureWrtDrop_i`.
- `adt1DtorckConstraint` / `adt2DtorckConstraint` / `regAdtDtorckConstraint` (`lines 376-404`): mirrors `adt_dtorck_constraint` across `Boxed`, `PlainBox`, `PlainDropRaw`, `RawBoxNoPhantom`, `RawBoxFnMarker`, `RawBoxWithPhantom`, `LiarBoxWithPhantom`, `RawVec<T, A>`, `Vec<T, A>`, `Box<T, A>`, `BTreeMap<K, A>`, `Inspector<'a>`, `ArenaAlloc<'a>`, and `CycleNode<'a>`.
- `collectObligationsList` (`lines 492-493`): runs worklist expansion via `tyDtorckStep` / `collectObligationsRaw` (`lines 481-490`, handling `.phantomData` by pushing `inner` to `dtorckTypes` with `outlivesRegions := []`) and deduplicates regions via `dedupRegions` (mirroring `dedup_dtorck_constraint`).
- `execReverseScope` (`lines 609-610`) & `dropckAcceptsScope` (`lines 624-625`): executes slots `n-1, ..., 0` under `slotLiveDuringDrop k target := natLt target k` (`StorageDead(j)` already ran for `j > k`), returning `.ubDanglingRead target` if any destructor or `drop_in_place` reads a slot with `live target = false`.
- Honesty predicates `adt1HonestB`, `adt2HonestB`, `regAdtHonestB`, and `ScopeWellFormed` (`lines 646-697`): require that whenever `pureWrtDrop = true` (`#[may_dangle]`) or `hasDrop = false`, `Drop::drop` does not directly read that parameter, and whenever `dropsParam0Elements = true` under `pureWrtDrop0 = true`, either `hasDirectParam0` or `hasPhantomParam0` / `hasPhantomBoxPair` is declared.

#### 5.2 Mechanized Theorems (Verbatim Signatures)

1. **General Soundness and Conservative Protection (`lines 823-1258`):**
   ```lean
   theorem dropRVal_ok_of_dropckAccepts
       (ignoreEyepatch : Bool)
       (live : Region → Bool) (slotLive : Nat → Bool)
       (h_agree : ∀ s, live (.rSlot s) = true → slotLive s = true)
       (v : RVal) (t : Ty) (ht : ValTyped v t)
       (hhon : tyAdtsHonest t = true)
       (hacc : dropckTyAccepts ignoreEyepatch live t = true) :
       dropRVal slotLive v = .ok

   theorem dropck_accepts_scope_implies_no_dangling_read
       (ignoreEyepatch : Bool) (slots : List ScopeSlot)
       (hwf : ScopeWellFormed slots)
       (hacc : dropckAcceptsScope ignoreEyepatch slots = true) :
       execReverseScope slots = .ok

   theorem conservative_dropck_scope_implies_no_dangling_read
       (slots : List ScopeSlot)
       (htyped : ScopeTypedOnly slots)
       (hacc : dropckAcceptsScope true slots = true) :
       execReverseScope slots = .ok
   ```
   `dropck_accepts_scope_implies_no_dangling_read` establishes that when `ScopeWellFormed` holds (`PureWrtDrop` + `PhantomData<T>` ownership honesty), dropck acceptance guarantees `.ok` across all reverse-order drops; `conservative_dropck_scope_implies_no_dangling_read` proves that conservative RFC 1238 dropck (`ignoreEyepatch = true`) ensures `.ok` even for scopes containing dishonest `#[may_dangle]` ADTs (`RawBoxNoPh`, `RawBoxFnPh`, `LiarBoxWithPh`).

2. **Missing-`PhantomData<T>`, Variance-Only `PhantomData<fn() -> T>`, and Untruthful `pure_wrt_drop` Witnesses (`lines 1315-1368`):**
   ```lean
   theorem missing_phantom_eyepatch_unsound_witness :
       collectObligationsList false 16 [.adt1 .rawBoxNoPh (.regAdt .inspector (.rSlot 1))] = [] ∧
       dropckAcceptsScope false scopeRawBoxNoPhInspector = true ∧
       execReverseScope scopeRawBoxNoPhInspector = .ubDanglingRead 1

   theorem phantom_fn_ptr_same_variance_still_unsound_witness :
       unaryMarkerVariance .rawBoxFnPh = unaryMarkerVariance .rawBoxWithPh ∧
       collectObligationsList false 16 [.adt1 .rawBoxFnPh (.regAdt .inspector (.rSlot 1))] = [] ∧
       dropckAcceptsScope false scopeRawBoxFnPhInspector = true ∧
       execReverseScope scopeRawBoxFnPhInspector = .ubDanglingRead 1

   theorem phantom_data_restores_rejection_for_inspector :
       collectObligationsList false 16 [.adt1 .rawBoxWithPh (.regAdt .inspector (.rSlot 1))] = [.rSlot 1] ∧
       dropckAcceptsScope false scopeRawBoxWithPhInspector = false

   theorem pure_wrt_drop_liar_with_phantom_unsound_witness :
       collectObligationsList false 16 [.adt1 .liarBoxWithPh (.ref (.rSlot 1) false .cellU32)] = [] ∧
       dropckAcceptsScope false scopeLiarBoxWithPhRef = true ∧
       execReverseScope scopeLiarBoxWithPhRef = .ubDanglingRead 1
   ```
   (Supplemented by `boxed_dropck_rejects_after_accepts_before` and `conservative_dropck_rejects_all_three_eyepatch_holes`.)

3. **`trivial_dropck_outlives` Soundness, `Vec<T, A>` Restoration, and Allocator Asymmetry (`lines 1376-1487`):**
   ```lean
   theorem trivialDropckOutlives_implies_dropRVal_ok
       (slotLive : Nat → Bool) (v : RVal) (t : Ty)
       (ht : ValTyped v t) (htriv : trivialDropckOutlives t = true) :
       dropRVal slotLive v = .ok

   theorem vec_and_rawbox_phantom_allow_dangling_cell_ref_sound :
       collectObligationsList false 16 [.adt2 .vec (.ref (.rSlot 2) false .cellU32) .prim] = [] ∧
       collectObligationsList false 16 [.adt1 .rawBoxWithPh (.ref (.rSlot 2) false .cellU32)] = [] ∧
       dropckAcceptsScope false scopeVecAndRawBoxCellRef = true ∧
       execReverseScope scopeVecAndRawBoxCellRef = .ok

   theorem vec_and_btree_allocator_eyepatch_asymmetry :
       collectObligationsList false 16 [.adt2 .vec (.ref (.rSlot 1) false .cellU32) (.regAdt .arenaRef (.rSlot 2))] = [.rSlot 2] ∧
       dropckAcceptsScope false scopeVecBorrowedArenaBefore = false ∧
       dropckAcceptsScope false scopeVecArenaBeforeElemAfter = true ∧
       execReverseScope scopeVecArenaBeforeElemAfter = .ok ∧
       dropckAcceptsScope false scopeBTreeArenaAfter = false ∧
       dropckAcceptsScope false scopeBTreeArenaBeforeElemAfter = true ∧
       execReverseScope scopeBTreeArenaBeforeElemAfter = .ok
   ```
   (Supplemented by `trivial_dropck_outlives_ref_sound` and `manuallyDrop_inspector_trivial_dropck_sound`.)

4. **Strict Inclusion and Variance Orthogonality (`lines 1527-1676`):**
   ```lean
   theorem conservative_implies_eyepatch_phantom_ty
       (live : Region → Bool) (t : Ty)
       (h : dropckTyAccepts true live t = true) :
       dropckTyAccepts false live t = true

   theorem conservative_implies_eyepatch_phantom_scope (slots : List ScopeSlot)
       (h : dropckAcceptsScope true slots = true) :
       dropckAcceptsScope false slots = true

   theorem strict_inclusion_between_dropck_regimes :
       (∀ slots, dropckAcceptsScope true slots = true → dropckAcceptsScope false slots = true) ∧
       (dropckAcceptsScope false scopeVecAndRawBoxCellRef = true ∧
        dropckAcceptsScope true scopeVecAndRawBoxCellRef = false ∧
        execReverseScope scopeVecAndRawBoxCellRef = .ok) ∧
       (dropckAcceptsScope false scopeRawBoxWithPhInspector = false ∧
        dropckAcceptsScope false scopeRawBoxNoPhInspector = true ∧
        execReverseScope scopeRawBoxNoPhInspector = .ubDanglingRead 1)
   ```
   Plus `xform_assoc`, `xform_cov_identity`, `xform_contra_involutive`, `glb_comm_idem`, and `variance_orthogonal_to_dropck_ownership`.

---

### 6. Mapping to `joshlf/anneal` Trusted MIR Boundary (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Basis: source + derived

Inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/audit/TrustedBoundary.lean`) shows how Anneal currently positions its trust perimeter relative to `rustc`'s `dropck_outlives`:

1. **Region erasure and explicit fail-closed `Drop` boundary:** `MirTy.ref` erases lifetimes (`MirAst.lean:304-305`), non-fieldless-enum ADTs (`Vec`, `Box`, `RawBox`, `PhantomData`, `Inspector`) lower to `MirTy.unsupported` (`MirAst.lean:308-321`), and `TerminatorKind::Drop` lowers to `TerminatorKind.unsupported` (`MirAst.lean:782-795`), stepping deterministically to `.fault .unsupported` (`MirSemantics.lean:1568-1569`) and refuting `WellFormed`.
2. **Active `StorageDead` and `deinitMovedPlace = true` sensitivity:** `MirSemantics.lean` already implements `StatementKind.storageDead` (transitioning stack slots to `.dead`, `lines 1391-1405`) and conservative move deinitialization (`evalOperandToSlot` setting moved non-ZST locals to `liveUninitSlot ty`, `lines 949-976`). As shown by our captured MIR (`bb3: StorageDead(_2); drop(_1)`), once a future Anneal extension admits `TerminatorKind::Drop` on generic ADTs, `StorageDead` of a borrowed stack slot **genuinely precedes** `drop(_1)` for eyepatched containers! Any verified MIR semantics or proof-carrying lowering admitting `Drop` must therefore either (a) rely on `rustc`'s `dropck_outlives` + `PureWrtDrop` + `PhantomData<T>` invariants as explicit soundness preconditions before erasing regions, or (b) validate root vs. tracked pointee retags under Miri's `mayDangle = true` behind `&mut self` without dereferencing dead stack slots.
3. **Compatibility with `TrustedBoundary.lean`:** `TrustedBoundary.lean` (`lines 92-105, 1661-1668, 2164`) forbids `unsafe`, `partial`, `sorryAx`, `Classical.choice` (`Quot`/axiom checks), `Lean.ofReduceBool`/`Lean.ofReduceNat`/`Lean.trustCompiler`, and compiler-generated `._unsafe_rec` helpers on verified modules. Structuring `DropckOutlivesMayDangleAndPhantomDataSoundness.lean` with explicit `noncomputable def` on every definition, zero `deriving` clauses, and definitional `bIf` branching demonstrates that complex recursive `rustc` type-checker semantics can be mechanized and verified in Lean `v4.34.1` with **`0` `._unsafe_rec`**, **`0` `Quot.sound`**, **`0` `Classical.choice`**, and only `[propext]`.

## Boundaries

- **Known not to apply:**
  1. Adding `PhantomData<T>` to a type with a non-eyepatched `impl<T> Drop` (`PlainDropRaw`) is **known not to apply** any relaxation or additional dropck protection beyond `T`'s direct presence in `outlives` (`a_plain_drop_with_raw_ptr_field_still_e0597`, `ty/util.rs:519-521`).
  2. Substituting variance-equivalent markers such as `PhantomData<fn() -> T>` or `PhantomData<*const T>` for `PhantomData<T>` is **known not to apply** dropck ownership (`d_eyepatch_with_phantom_fn_ptr_still_compiles`, `query/dropck_outlives.rs:41, 44`).
  3. `PhantomData<T>` is **known not to apply** protection against `Drop::drop` bodies that violate `pure_wrt_drop` by directly reading or formatting `T` when `T` is a trivial-dropck reference like `&'a String` (`f_eyepatch_with_phantom_liar_reads_ref_compiles`, `miri_eyepatch_with_phantom_liar_reads_ref_uaf`).
  4. `dropck_outlives` rules are **known not to apply** inside `ManuallyDrop<T>` (`trivial_dropck_outlives(ManuallyDrop<T>) == true`, `e_manually_drop_trivial_dropck_exec`), unless the enclosing type explicitly adds another ownership marker (like `BTreeMap`'s `PhantomData<Box<(K, V), A>>` + un-eyepatched `A`).
- **Unsupported:**
  1. User-written `#[may_dangle]` destructors are **unsupported** on stable Rust (requiring nightly `#![feature(dropck_eyepatch)]`), and applying `#[may_dangle]` to non-`Drop` impls, `const` generic parameters (`check_may_dangle` restricts to `Lifetime` and `Type` at `check_attr.rs:942`), or without `unsafe impl` (`E0569`) is **unsupported**.
  2. In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `TerminatorKind::Drop`, non-fieldless-enum ADTs (`Vec`, `Box`, `PhantomData`), and `TyKind::FnPtr` are **unsupported** (`FaultKind.unsupported`).
- **Unknown:**
  1. Whether a future Rust edition or RFC will stabilize a sound, safe replacement for `#![feature(dropck_eyepatch)]` (`rust-lang/rust#34761`) remains **unknown**.
  2. Whether `ty::View(..)` (`unimplemented!()` in `query/dropck_outlives.rs:93, 425` at `20fe935d5036`) will treat view types as trivial or structural in dropck remains **unknown**.
- **Not examined:**
  1. Experimental `AsyncDrop` (`TyCtxt::async_destructor` in `ty/util.rs:456`, `LangItem::AsyncDrop` in `coherence/builtin.rs:41`), coroutine interior witness dropck (`query/dropck_outlives.rs:315-378`), `-Zpolonius=next` deferred region liveness (`liveness/trace.rs:71-76`), and `MaybeDangling<P>` (`#[lang = "maybe_dangling"]`) MIR validity flags were **not examined** in this report's empirical or Lean suites.
  2. Cyclic self-referential recursive ADTs (`struct Node<'a>(Vec<Node<'a>>)` via `ty_set` cycle-breaking in `compute_dropck_outlives_with_errors` at `query/dropck_outlives.rs:158, 243`) were **not examined** in the fixed-arity Lean `Ty` mechanization (which covers acyclic nested generic constructors).

## Evidence

### 1. Primary Source Inventory (`rust-lang/rust` and `joshlf/anneal`)

| Repository & Commit SHA | File Path & Lines | Symbol / Construct Audited (`Basis`) |
| :--- | :--- | :--- |
| `rust-lang/rust`<br>`20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `compiler/rustc_traits/src/dropck_outlives.rs:20-73` | `source`: `dropck_outlives`, `adt_dtorck_constraint` (`PhantomData<T>` -> `dtorck_types: [T]`, `destructor_constraints` -> `outlives`), `dedup_dtorck_constraint` |
| `rust-lang/rust`<br>`20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `compiler/rustc_middle/src/ty/util.rs:466-538` | `source`: `TyCtxt::destructor_constraints` (`!pure_wrt_drop` filter across lifetime/type/const params) |
| `rust-lang/rust`<br>`20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs:28-427` | `source`: `trivial_dropck_outlives`, `compute_dropck_outlives_inner`, `compute_dropck_outlives_with_errors`, `dtorck_constraint_for_ty_inner` |
| `rust-lang/rust`<br>`20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `compiler/rustc_borrowck/src/type_check/liveness/trace.rs:43-188, 390-455, 534-664, 785-830` | `source`: `LivenessComputation::compute`, `compute_drop_live_points_for`, `dropck_local` |
| `rust-lang/rust`<br>`20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `compiler/rustc_ast_lowering/src/lib.rs:2384-2395`; `compiler/rustc_middle/src/ty/generics.rs:71-83`; `compiler/rustc_passes/src/check_attr.rs:938-963`; `compiler/rustc_hir_analysis/src/coherence/unsafety.rs:20-103` | `source`: `pure_wrt_drop` lowering from `sym::may_dangle`, `check_may_dangle`, `E0569` `unsafe impl` enforcement |
| `rust-lang/rust`<br>`20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `library/alloc/src/vec/mod.rs:448-451, 4595-4608`; `library/alloc/src/raw_vec/mod.rs:67, 78-99, 439-445, 909-917`; `library/alloc/src/boxed.rs:238-245, 2126-2143` | `source`: `Vec<T, A>::drop`, `RawVec<T, A>` (`NonNull<u8>` + `_marker: PhantomData<T>`), `BoxRaw<T>` / `Box<T, A>::drop` |
| `rust-lang/rust`<br>`20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `library/core/src/marker.rs:810-812`; `library/core/src/ptr/non_null.rs:78-80`; `library/core/src/mem/manually_drop.rs:152-158` | `source`: `#[lang = "phantom_data"]`, `NonNull<T>`, `#[lang = "manually_drop"]` |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `library/alloc/src/raw_vec/mod.rs:73-94`; `library/alloc/src/vec/mod.rs:438-441, 4286-4296` | `source`: `1.98.0-nightly` baseline (`RawVecInner.ptr: Unique<u8>`, pre-const `Drop for Vec<T, A>`) |
| `joshlf/anneal`<br>`c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:304-321, 742-795`; `trusted/lean/Trusted/MirSemantics.lean:949-976, 1391-1405, 1537-1570`; `trusted/audit/TrustedBoundary.lean:92-105, 1615-1668, 2164`; `trusted/rustc-capture/src/driver.rs:25` | `source`: Region erasure, fail-closed `Drop` / non-fieldless ADT boundaries, `deinitMovedPlace = true`, `StorageDead`, and `_unsafe_rec` / axiom rules |

### 2. Executed Toolchain Probes (`2026-11-24`, `support/probe_dropck_may_dangle_phantomdata.py`)

- **Command:** `python3 support/probe_dropck_may_dangle_phantomdata.py` (executes every probe inside `with tempfile.TemporaryDirectory():` using `rustc +nightly --edition=2024`, `rustc +nightly --edition=2024 -Z mir-opt-level=0 --emit=mir`, and `cargo +nightly miri run --offline`).
- **Observed toolchain versions:** `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (LLVM `22.1.6`, `x86_64-unknown-linux-gnu`), `miri 0.1.0 (14210df0e2 2026-05-31)`.
- **Observed counts:** `12/12` `rustc` probe expectations matched (`0` warnings), `5/5` `Miri` probe expectations matched (`3` UAF detections `rc = 1` + `2` clean passes `rc = 0`), `1/1` unoptimized MIR `StorageDead(_2); drop(_1)` capture (`rc = 0`). Full scrubbed outputs archived in `support/probe_results.json`.

### 3. Lean `v4.34.1` Kernel Check & MetaM Audit (`2026-11-24`, `support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean`)

- **File:** `support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean` (`1,678` lines, `84,418` bytes).
- **Kernel check command (`exit 0`):** `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean` under `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
- **MetaM environment audit (`exit 0`, `METAM_AUDIT_PASSED=1`):**
  - Total declarations in `RustcDropckMayDanglePhantomData`: `649` (`176` theorems, `23` explicit user theorems).
  - `_unsafe_rec` constants: **`0`**.
  - `unsafe` constants: **`0`**.
  - Forbidden tokens (`sorry`, `Classical`, `omega`, `bv_decide`, `native_decide`, `partial`): **`0`**.
  - Union of axioms across all `649` constants (`Lean.collectAxioms`): **`[propext]`** (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.ofReduceNat`, `0` `Lean.trustCompiler`).

## Revalidation

Run these three self-contained checks from the package directory (or corpus root) to revalidate every empirical, mechanized, and structural claim:

1. **Re-execute all `12` `rustc`, `5` `Miri`, and `1` MIR probes inside temporary directories:**
   ```bash
   PATH="$HOME/.cargo/bin:$PATH" python3 support/probe_dropck_may_dangle_phantomdata.py --out /tmp/probe_results_recheck.json
   python3 -c '
   import json, re, sys
   norm = lambda d: re.sub(r"target\(s\) in \d+\.\d+s", "target(s) in <TIME>", json.dumps(d, sort_keys=True))
   a = json.load(open("support/probe_results.json"))
   b = json.load(open("/tmp/probe_results_recheck.json"))
   assert norm(a) == norm(b), "probe output mismatch"
   print("PROBES_REVALIDATED=1")
   '
   rm -f /tmp/probe_results_recheck.json
   ```
   *(Version pins: if `rustc +nightly` or `miri` updates past `14210df0e`, check `rustc --version --verbose` and inspect any diagnostic phrasing changes while verifying exit codes and `DROPCK_SAFE=2` / `MANUALLY_DROP_SAFE=1` / Miri UAF outcomes.)*

2. **Re-verify the Lean `v4.34.1` formalization and confirm `0` warnings / `0` `_unsafe_rec` / `0` forbidden axioms:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/DropckOutlivesMayDangleAndPhantomDataSoundness.lean
   ```

3. **Check upstream `rust-lang/rust` drift on the audited compiler and stdlib regions:**
   Diff `compiler/rustc_traits/src/dropck_outlives.rs`, `compiler/rustc_middle/src/ty/util.rs`, `compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs`, `compiler/rustc_borrowck/src/type_check/liveness/trace.rs`, `library/alloc/src/vec/mod.rs`, and `library/alloc/src/raw_vec/mod.rs` against `20fe935d50367c0ff8872c2ebfa050c5c99d9201`. Any change to `adt_dtorck_constraint`, `destructor_constraints`, `trivial_dropck_outlives`, or `RawVec._marker` invalidates the corresponding source claim and requires updating the affected findings.

4. **Validate corpus metadata and prose headings from the corpus root:**
   ```bash
   python3 tools/reference.py check
   ```
