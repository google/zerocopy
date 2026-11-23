# `rustc` `unsafe<'a> T` (`feature(unsafe_binders)`): MIR Semantics, `v0` Symbol-Mangling and Miri Validity ICEs, `!Copy` Enforcement, and Optimization Opacity

## Summary

Rust's unstable `#![feature(unsafe_binders)]` (`unsafe<'a> T`, tracked upstream as `ty::UnsafeBinder(Binder<Ty>)` and manipulated via `core::unsafe_binder::{wrap_binder!, unwrap_binder!}`) erases higher-ranked lifetime parameters behind an `unsafe` type boundary without changing runtime size, alignment, or ABI representation. Across upstream `rust-lang/rust` HEAD (`5debe6a1244452beced762385f88a51857a915fc`), executed nightly `rustc 1.98.0-nightly` / `miri 0.1.0` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), five tightly coupled behaviors govern static semantics, verification tooling, compilation, and optimization:

1. **Static Safety Boundary (`!Copy`, `BikeshedGuaranteedNoDrop`, and `E0133`):** Constructing (`Rvalue::WrapUnsafeBinder`) or projecting through (`ProjectionElem::UnwrapUnsafeBinder`) an unsafe binder requires an `unsafe` context (`check_unsafety.rs`, emitting `E0133`). Although `rustc_ty_utils::layout` delegates layout transparently to the bound-region-erased inner type, `rustc_trait_selection` intentionally omits builtin `Copy`/`Clone` candidate assembly for *all* `ty::UnsafeBinder(_)` types—even `unsafe<> u32`—enforcing linear move semantics unless duplicated via explicit bitwise `ptr::read` (`E0382` / `E0277`). Meanwhile, well-formedness (`wf.rs:978-993`) enforces the sealed internal trait `BikeshedGuaranteedNoDrop`, admitting references (`&T`, `&mut T`), `ManuallyDrop<T>`, and `Copy` types while rejecting both non-`Copy` destructible types (`unsafe<> String`) and nested unsafe binders (`unsafe<'b> unsafe<'a> &'a u32`).
2. **Default `v0` Symbol-Mangling ICE (`v0.rs:679` / `v0.rs:591`):** Because `-Csymbol-mangling-version` defaults to `v0` (`options.rs:2440-2442`), `V0SymbolMangler::print_type` panics (`rc=101`) whenever any monomorphized non-inlined item, generic instantiation at `-Copt-level=0`, or drop glue carries `ty::UnsafeBinder(_)` in its signature or generic arguments (`v0.rs:679` `unimplemented!()` at `5debe6a12`; `v0.rs:591` `todo!()` at `14210df0e`). Passing `-Csymbol-mangling-version=hashed` also panics because `hashed` delegates to `v0::mangle`. At `-Copt-level=2`, `#[inline]` functions such as `core::ptr::read::<unsafe<'a> &'a mut u32>` escape the ICE *only* when inlining eliminates the item before monomorphized symbol partitioning; `#[inline(never)]` generic items still ICE. `-Csymbol-mangling-version=legacy` avoids the ICE (`rc=0`) by hashing generic args and formatting binders via `PrettyPrinter` only for drop shims.
3. **Miri Runtime Validity Panic (`validity.rs:987` / `validity.rs:994`) and Aliasing-Check Suppression Footgun:** Miri evaluates `WrapUnsafeBinder` (`step.rs:291-296`) and `UnwrapUnsafeBinder` (`projection.rs:417`) identically to layout-preserving transmutes, yet `ValidityVisitor::try_visit_primitive` panics (`not yet implemented: FIXME(unsafe_binder)`) whenever validation touches any `ty::UnsafeBinder(_)` value (`rc=101` under both Stacked Borrows and `-Zmiri-tree-borrows`). Passing `-Zmiri-disable-validation` prevents the panic (`rc=0`), **but is unsound as a verification workaround**: `src/tools/miri/src/bin/miri.rs` (`689-692` at `5debe6a12`, `734-737` at `14210df0e`) sets `miri_config.borrow_tracker = None` whenever `validation == ValidationMode::No`, silently disabling *both* scalar validity checks and Stacked/Tree Borrows aliasing enforcement.
4. **MIR Optimization Opacity (`SROA`, `GVN`) vs. `ReferencePropagation` Pass-Through and Zero-Cost Codegen:** Neither `ScalarReplacementOfAggregates` (`sroa.rs`) nor `GVN` (`gvn.rs`) cancels or scalarizes `WrapUnsafeBinder`/`UnwrapUnsafeBinder` pairs: a tuple wrapped and immediately unwrapped (`unwrap_binder!(wrap_binder!(tup)).0`) survives intact through `Runtime(Optimized)` MIR at `-Zmir-opt-level=2`. Conversely, `ReferencePropagation` (`ref_prop.rs:193-202`) *does* propagate through `UnwrapUnsafeBinder` because `ProjectionElem::UnwrapUnsafeBinder::is_stable_offset()` returns `true` (`statement.rs:287`). At codegen (`rustc_codegen_ssa`), both forms are zero-cost identity/retyping operations, allowing LLVM `-Copt-level=2` to fold tuple unwrap chains down to `ret i32 %a`.
5. **`Anneal` Fail-Closed Boundary and Lean v4.34.1 Mechanization:** `joshlf/anneal` (`trusted/lean/Trusted/MirAst.lean:285,462,578`) explicitly routes `TyKind::UnsafeBinder`, `ProjectionElem::UnwrapUnsafeBinder`, and `Rvalue::WrapUnsafeBinder` to `.unsupported` (`FaultKind.unsupported`), preventing unsound verification over unmodeled lifetime-erased binder semantics. All three semantic fixes and soundness theorems—recursive validity delegation (repairing `validity.rs:987`), `UnwrapUnsafeBinder(WrapUnsafeBinder(v))` algebraic cancellation & `SROA` scalarization preservation (`deinitMovedPlace`-aware), and a prefix-free `'Z' [G<n>_] <ty>` `v0` grammar extension with constructive round-trip decoding and full injectivity—are kernel-checked in `support/UnsafeBindersManglingValidityAndScalarizeSoundness.lean` (2,593 LOC, 620 theorems, 0 `sorry`, 0 `Classical.choice`, 0 `omega`/`native_decide`/`bv_decide`, 0 `._unsafe_rec`).

## Applicability

This report characterizes three concrete software revisions recorded in `REPORT.json`, together with the cross-compiler version differences established between them:

1. **Upstream `rust-lang/rust` HEAD (`5debe6a1244452beced762385f88a51857a915fc`):** Audited directly at source level across `library/core`, `compiler/rustc_type_ir`, `compiler/rustc_trait_selection`, `compiler/rustc_ty_utils`, `compiler/rustc_middle`, `compiler/rustc_mir_build`, `compiler/rustc_mir_transform`, `compiler/rustc_mir_dataflow`, `compiler/rustc_symbol_mangling`, `compiler/rustc_const_eval`, `compiler/rustc_codegen_ssa`, `compiler/rustc_session`, and `src/tools/miri`.
2. **Executed Nightly Toolchain (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):** `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM `22.1.6` and `miri 0.1.0 (14210df0e2 2026-05-31)` on host `x86_64-unknown-linux-gnu`. Source files from this exact commit were also inspected alongside `5debe6a12` to pin exact panic line numbers (`v0.rs:591:37`, `validity.rs:994:36`, `miri.rs:734-737`). All empirical compilation matrices, MIR/LLVM IR dumps, and Miri runs in `support/probe_results.json` come directly from this toolchain.
3. **`joshlf/anneal` HEAD (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Inspected in `trusted/lean/Trusted/MirAst.lean` to establish how Anneal's trusted Rust MIR capture and semantics handle `UnsafeBinder` constructs. Internally, `MirAst.lean` documents alignment with `rust-lang/rust` commit `8144389c895da997dbdecaa635e41d6a50be6ffd`; both `c131b32` and upstream `5debe6a12` share the same core MIR variants for unsafe binders.

### Version-Delta Matrix (`14210df0e` vs. `5debe6a12`)

Between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) and `5debe6a1244452beced762385f88a51857a915fc`, the compiler behavior on `unsafe_binders` remained invariant, while surrounding edits shifted exact source line numbers and converted `todo!()` placeholders to `unimplemented!()`:

| Subsystem | File | `14210df0e` (Executed Toolchain) | `5debe6a12` (Upstream HEAD) | Behavioral Delta |
| --- | --- | --- | --- | --- |
| `v0` Symbol Mangling | `compiler/rustc_symbol_mangling/src/v0.rs` | `591:37` — `ty::UnsafeBinder(..) => todo!()` | `679:37` — `ty::UnsafeBinder(..) => unimplemented!()` | Identical runtime panic (`not yet implemented`, `rc=101`) |
| Miri / CTFE Validity | `compiler/rustc_const_eval/src/interpret/validity.rs` | `994:36` — `ty::UnsafeBinder(_) => todo!("FIXME(unsafe_binder)")` | `987:36` — `ty::UnsafeBinder(_) => unimplemented!("FIXME(unsafe_binder)")` | Identical panic (`not yet implemented: FIXME(unsafe_binder)`) |
| Miri Disable-Validation Hook | `src/tools/miri/src/bin/miri.rs` | `518-520`, `734-737` — `if miri_config.validation == ValidationMode::No { miri_config.borrow_tracker = None; }` | `475-477`, `689-692` — identical check and assignment | Identical aliasing-tracker suppression |
| MIR Validator | `compiler/rustc_mir_transform/src/validate.rs` | `872-890` (`UnwrapUnsafeBinder`), `1432-1448` (`WrapUnsafeBinder`) | `890-908` (`UnwrapUnsafeBinder`), `1461-1477` (`WrapUnsafeBinder`) | Same checks and copy-paste `"WrapUnsafeBinder..."` message |
| `SROA` Pass | `compiler/rustc_mir_transform/src/sroa.rs` | `111`, `126`, `159` | `100`, `115`, `148` | Same `Field`-only escape & replacement matching |
| `GVN` Pass | `compiler/rustc_mir_transform/src/gvn.rs` | `914`, `1095` | `921`, `1101`, `1753` | Same opaque `UnwrapUnsafeBinder(())` / `Transmute` handling |
| Codegen SSA | `compiler/rustc_codegen_ssa/src/mir/{rvalue.rs, place.rs}` | `rvalue.rs:734-739`, `place.rs:363-365` | `rvalue.rs:845-850`, `place.rs:383-385` | Same zero-cost layout rewrap / `project_type` lowering |

### Scope Constraints

* All empirical Rust probes compile with `--edition=2024` and `#![feature(unsafe_binders)]` (which itself emits `#[warn(incomplete_features)]`).
* All optimization claims distinguish `-Zmir-opt-level=0`/`-Copt-level=0` from `-Zmir-opt-level=2`/`-Copt-level=2` and inspect actual emitted MIR phases (`built`, `analysis-post-cleanup`, `runtime-post-cleanup`, `ReferencePropagation`, `ScalarReplacementOfAggregates`, `GVN`, `runtime-optimized`) plus LLVM IR (`--emit=llvm-ir`) on `x86_64-unknown-linux-gnu`.
* Mechanized proofs are written in pure Lean `v4.34.1` (`Init` prelude only, no Mathlib, `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) modeling faithful abstract machines parameterized over `deinitMovedPlace : Bool`, validity modes, borrow tracking, and RFC 2603 `v0` type productions.

## Findings

### 1. Type Representation, `!Copy` Enforcement, `BikeshedGuaranteedNoDrop` Well-Formedness, and Unsafety Gate

**Basis:** `source` + `execution` + `derived`

At the type-IR layer, `rustc_type_ir::TyKind::UnsafeBinder(UnsafeBinderInner<I>)` (`compiler/rustc_type_ir/src/ty_kind.rs:1357`) wraps `ty::Binder<I, I::Ty>`, storing a list of bound lifetime variables alongside the inner guarded type `T`. In `library/core/src/unsafe_binder.rs:4-17`, user syntax enters exclusively through two macros expanding to internal keywords:

```rust
pub macro unwrap_binder($expr:expr $( ; $ty:ty )?) {
    k#unwrap_binder($expr $( , $ty )?)
}
pub macro wrap_binder($expr:expr $( ; $ty:ty )?) {
    k#wrap_binder($expr $( , $ty )?)
}
```

#### Transparent Layout vs. Mandatory Move Semantics (`!Copy`)

Type layout and drop-glue analysis treat `ty::UnsafeBinder(bound_ty)` identically to its bound-region-erased underlying type:

* `compiler/rustc_ty_utils/src/layout.rs:874-877`:
  ```rust
  ty::UnsafeBinder(bound_ty) => {
      let ty = tcx.instantiate_bound_regions_with_erased(bound_ty.into());
      cx.layout_of(ty)?.layout
  }
  ```
* `compiler/rustc_ty_utils/src/needs_drop.rs:239-242`:
  ```rust
  ty::UnsafeBinder(bound_ty) => {
      let ty = self.tcx.instantiate_bound_regions_with_erased(bound_ty.into());
      queue_type(self, ty);
  }
  ```

Despite transparent layout equivalence (`tyLayout_unsafeBinder` in `UnsafeBindersManglingValidityAndScalarizeSoundness.lean:515`), `rustc_trait_selection/src/traits/select/candidate_assembly.rs:1174-1176` explicitly declines to assemble builtin `Copy` or `Clone` trait implementations for `ty::UnsafeBinder(_)`:

```rust
// FIXME(unsafe_binder): Should we conditionally
// (i.e. universally) implement copy/clone?
ty::UnsafeBinder(_) => {}
```

Consequently, **all** `unsafe<'a> T` types are non-`Copy`—even when `T` is `&'a u32` or a trivial `Copy` primitive with zero bound lifetimes such as `unsafe<> u32`. Live `rustc` (`14210df0e`) rejects every duplicate use with `E0382` / `E0277`:

| Static Probe Case | Rust Construct | Exit Code | Diagnostic Summary |
| --- | --- | --- | --- |
| `non_copy_shared_ref` | `let b2 = b;` where `b: unsafe<'a> &'a u32` | `1` | `error[E0382]: use of moved value: b` (`unsafe<'a> &'a u32` does not implement `Copy`) |
| `non_copy_mut_ref` | `let b2 = b;` where `b: unsafe<'a> &'a mut u32` | `1` | `error[E0382]: use of moved value: b` |
| `non_copy_even_inner_u32` | `let b2 = b;` where `b: unsafe<> u32` | `1` | `error[E0382]: use of moved value: b` (`unsafe<> u32` does not implement `Copy`) |
| `trait_bound_not_copy` | `req_copy::<unsafe<'a> &'a u32>(b)` with `T: Copy` | `1` | `error[E0277]: the trait bound unsafe<'a> &'a u32: Copy is not satisfied` |
| `unsafety_gate_wrap` | `wrap_binder!(x)` outside `unsafe` | `1` | `error[E0133]: unsafe binder cast is unsafe and requires unsafe block...` |
| `unsafety_gate_unwrap` | `*unwrap_binder!(b)` outside `unsafe` | `1` | `error[E0133]: unsafe binder cast is unsafe and requires unsafe block...` |

Note why this restriction matters for Rust soundness (`derived`): `unsafe<'a> T` can guard non-trivial aliasing invariants (e.g., `unsafe<'a> &'a mut u32` stored inside a custom handle). Allowing implicit `Copy` on `unsafe<'a> T` merely because `T` happens to be `&'a mut u32` or `T: Copy` is subtle, so conservative `!Copy` forces any duplication of `unsafe<'a> T` through explicit unsafe bitwise reads (`core::ptr::read(&b)`), keeping alias duplication explicitly unsafe. Meanwhile, `rustc_mir_build/src/check_unsafety.rs:611-615` gates *all three* THIR expressions (`ExprKind::PlaceUnwrapUnsafeBinder`, `ExprKind::ValueUnwrapUnsafeBinder`, `ExprKind::WrapUnsafeBinder`) via `self.requires_unsafe(expr.span, UnsafeBinderCast)` (`E0133`).

#### `BikeshedGuaranteedNoDrop` Well-Formedness Constraint

Unlike layout transparency, well-formedness checking in `compiler/rustc_trait_selection/src/traits/wf.rs:978-993` constrains the inner type of any `ty::UnsafeBinder(ty)` (when `!ty.has_escaping_bound_vars()`) to implement `LangItem::BikeshedGuaranteedNoDrop`:

```rust
ty::UnsafeBinder(ty) => {
    // FIXME(unsafe_binders): For now, we have no way to express
    // that a type must be `ManuallyDrop` OR `Copy` (or a pointer).
    if !ty.has_escaping_bound_vars() {
        self.out.push(traits::Obligation::new(
            self.tcx(),
            self.cause(ObligationCauseCode::Misc),
            self.param_env,
            ty.map_bound(|ty| {
                ty::TraitRef::new(
                    self.tcx(),
                    self.tcx().require_lang_item(
                        LangItem::BikeshedGuaranteedNoDrop,
                        self.span,
                    ),
                    [ty],
                )
            }),
        ));
    }
}
```

In `compiler/rustc_trait_selection/src/traits/select/confirmation.rs:1173-1250`, `confirm_bikeshed_guaranteed_no_drop_candidate` satisfies this obligation *only* for:
1. Shared and mutable references `ty::Ref(..)` (`L1183`),
2. `ManuallyDrop<T>` (`ty::Adt(def, _) if def.is_manually_drop()`, `L1185`),
3. Tuples `ty::Tuple(tys)` and arrays `ty::Array(elem_ty, _)` recursively over elements (`L1188-1209`),
4. Otherwise, types implementing `Copy` (`L1214-1250`).

Because the fallback arm maps non-ref/non-`ManuallyDrop` types to `LangItem::Copy` **without** special-casing `ty::UnsafeBinder(_)`, live `rustc` (`14210df0e`) produces two crisp consequences confirmed in `static_checks`:
* `wf_rejects_string_binder`: `unsafe<> String` fails with `error[E0277]: the trait bound String: Copy is not satisfied` (`rc=1`).
* `wf_rejects_nested_binder`: `unsafe<'b> unsafe<'a> &'a u32` **also fails** (`rc=1`) with `error[E0277]: the trait bound unsafe<'a> &'a u32: Copy is not satisfied` (because the outer `unsafe<'b> _` checks `BikeshedGuaranteedNoDrop` on `unsafe<'a> &'a u32`, which falls into the `Copy` requirement and fails because nested `unsafeBinder` is `!Copy`).
* `wf_accepts_manually_drop_string`: `unsafe<> ManuallyDrop<String>` compiles cleanly (`rc=0`), matching the Lean `wf_accepts_manuallyDrop_binder` and `wf_rejects_nested_unsafeBinder` theorems (`support/UnsafeBindersManglingValidityAndScalarizeSoundness.lean:448-452`).

---

### 2. MIR Representation, Validator Diagnostics, and `Anneal` Fail-Closed Boundary

**Basis:** `source` + `derived`

During MIR building (`compiler/rustc_mir_build/src/builder/expr/`), binder operations lower asymmetrically—wrapping is an `Rvalue`, whereas unwrapping is a **place projection**:

| Construct | Source THIR Expr | Built MIR Node | Source File & Lines (`5debe6a12`) | Semantic Properties |
| --- | --- | --- | --- | --- |
| Wrap (`wrap_binder!(x)`) | `ExprKind::WrapUnsafeBinder { source }` | `Rvalue::WrapUnsafeBinder(source, expr.ty)` | `as_rvalue.rs:361-372`, `syntax.rs:1469` | Evaluates `source` as operand; `is_safe_to_remove() == true` (`statement.rs:808`); `Rvalue::ty` returns stored `ty` (`statement.rs:864`) |
| Unwrap (`unwrap_binder!(p)`) | `ExprKind::PlaceUnwrapUnsafeBinder` / `ValueUnwrapUnsafeBinder` | `PlaceElem::UnwrapUnsafeBinder(expr.ty)` | `as_place.rs:535-546`, `syntax.rs:1262` | Place projection (`is_indirect() == false` `statement.rs:273`, `is_stable_offset() == true` `statement.rs:287`, `can_use_in_debuginfo() == false` `statement.rs:316` with `FIXME(unsafe_binders)`) |

Notice why `ValueUnwrapUnsafeBinder` exists in `as_place.rs:541-546`: if the input to `unwrap_binder!` is an rvalue expression rather than a place, MIR construction materializes it into a temporary via `this.as_temp(...)` and attaches `PlaceElem::UnwrapUnsafeBinder(expr.ty)`. In `built` / `runtime-post-cleanup` MIR of `dup_mut_via_ptr_read`, dereferencing an unwrapped reference (`*unwrap_binder!(b)`) produces `_11 = no_retag copy unwrap_binder!(_2; &mut u32); _7 = &mut (*_11);`.

#### `Validator` Checks and Copy-Paste Diagnostic Bug

In `compiler/rustc_mir_transform/src/validate.rs` (`890-908` and `1461-1477` at `5debe6a12`; `872-890` and `1432-1448` at `14210df0e`), `Validator` enforces type consistency for both constructs by erasing bound regions via `self.tcx.instantiate_bound_regions_with_erased(*binder_ty)`:
* For `Rvalue::WrapUnsafeBinder(op, ty)`: checks `*ty.kind()` is `ty::UnsafeBinder(binder_ty)` and calls `self.mir_assign_valid_types(unwrapped_ty, binder_inner_ty)`.
* For `ProjectionElem::UnwrapUnsafeBinder(unwrapped_ty)`: checks `place_ref` has type `ty::UnsafeBinder(binder_ty)` and calls `self.mir_assign_valid_types(unwrapped_ty, binder_inner_ty)`. Notice a minor upstream diagnostic copy-paste bug at `validate.rs:895` (`877` at `14210df0e`): when the base of `ProjectionElem::UnwrapUnsafeBinder` is not a `ty::UnsafeBinder`, the validator reports `"WrapUnsafeBinder does not produce a ty::UnsafeBinder"` instead of naming `UnwrapUnsafeBinder`.

#### `joshlf/anneal` Trusted Boundary Disposition

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirAst.lean` documents `TyKind::UnsafeBinder` (`L285`), `ProjectionElem::UnwrapUnsafeBinder` (`L462`), and `Rvalue::WrapUnsafeBinder` (`L578`) in its upstream `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`) correspondence inventory and **deliberately excludes all three from executable MIR semantics**:
* `MirTy` (`L308-321`) maps unmodeled `TyKind` variants to `MirTy.unsupported`.
* `ProjectionElem` (`L469-475`) maps `UnwrapUnsafeBinder` to `ProjectionElem.unsupported`.
* `Rvalue` (`L612-628`) maps `WrapUnsafeBinder` to `Rvalue.unsupported`.

Because `Trusted.MirSemantics` fails closed with `FaultKind.unsupported` whenever capture encounters `.unsupported`, Anneal cannot silently mis-model lifetime erasure, non-`Copy` semantics, or missing Miri validity checks on `unsafe_binders` code.

---

### 3. Default `v0` Symbol-Mangling ICE (`v0.rs:679` / `591`), Legacy Avoidance, and Total `'Z'` Grammar Extension

**Basis:** `source` + `execution` + `derived`

#### Root Cause of the `rustc` Panic

Compiler flag `symbol_mangling_version` defaults to `v0` (`compiler/rustc_session/src/options.rs:2440-2442`: `"which mangling version to use for symbol names ('legacy', 'v0' (default), or 'hashed')"`). In `compiler/rustc_symbol_mangling/src/v0.rs`, `V0SymbolMangler::print_type` explicitly aborts on `ty::UnsafeBinder(..)`:
* At `5debe6a12` (`L678-679`): `// FIXME(unsafe_binder): \n ty::UnsafeBinder(..) => unimplemented!(),`
* At `14210df0e` (`L590-591`): `// FIXME(unsafe_binder): \n ty::UnsafeBinder(..) => todo!(),`

Whenever `collect_and_partition_mono_items` collects any surviving monomorphized `Instance` whose `DefId` path or generic substitution contains `unsafe<'a> T`, querying `symbol_name` reaches `V0SymbolMangler::print_type` and aborts compilation (`rc=101`). Crucially:
1. **`-Csymbol-mangling-version=hashed` also ICEs (`rc=101`)** because the query trace passes directly through `rustc_symbol_mangling::v0::mangle` (`ptr_read_opt0_hashed` stderr frames 12–14) before hashing the mangled string.
2. **Inlining at `-Copt-level=2` masks the ICE only when the generic callee disappears from mono items:** `core::ptr::read::<unsafe<'a> &'a mut u32>` panics at `-Copt-level=0` (`ptr_read_opt0_default`, `ptr_read_opt0_v0`) but compiles cleanly and prints `42` at `-Copt-level=2` (`ptr_read_opt2_default`, `ptr_read_opt2_v0`), whereas adding `#[inline(never)]` (`noinline_opt2_v0`) causes `-Copt-level=2` to panic at the exact same `v0.rs:591:37` location.
3. **`core::ptr::drop_in_place` shims also panic under `v0` (`drop_glue_opt0_v0`, `rc=101`)**, even when wrapping `ManuallyDrop<String>`.
4. **`-Csymbol-mangling-version=legacy` avoids the ICE across all cases (`rc=0`)**: In `compiler/rustc_symbol_mangling/src/legacy.rs:70-87,125-140`, `get_symbol_hash` feeds `instance` into `StableHasher` without printing raw RFC 2603 type tags, and `legacy::mangle` passes `ty::GenericArgs::empty()` to `print_def_path` for ordinary generic functions (only formatting `instance.args` for `DropGlue` / `AsyncDropGlue*` / `FutureDropPoll` shims, which invoke `rustc_middle/src/ty/print/pretty.rs:815-819` to emit escaped `<unsafe<...>>`).

#### Executed Mangling Matrix (`14210df0e`)

| Matrix Case | Flags | Compile `rc` | Execution `rc` / `stdout` | Triggered Frame / Site |
| --- | --- | --- | --- | --- |
| `ptr_read_opt0_default` | `--edition=2024 -Copt-level=0` | `101` | — | `v0.rs:591:37` on `core::ptr::read::<unsafe<'a> &'a mut u32>` |
| `ptr_read_opt0_v0` | `--edition=2024 -Copt-level=0 -Csymbol-mangling-version=v0` | `101` | — | `v0.rs:591:37` |
| `ptr_read_opt0_hashed` | `--edition=2024 -Copt-level=0 -Zunstable-options -Csymbol-mangling-version=hashed` | `101` | — | `v0.rs:591:37` via `v0::mangle` |
| `ptr_read_opt0_legacy` | `--edition=2024 -Copt-level=0 -Zunstable-options -Csymbol-mangling-version=legacy` | `0` | `0` (`"42"`) | Succeeds (`legacy::mangle` skips generic args in symbol name) |
| `ptr_read_opt2_default` | `--edition=2024 -Copt-level=2` | `0` | `0` (`"42"`) | Inlining eliminates `core::ptr::read` mono item |
| `ptr_read_opt2_v0` | `--edition=2024 -Copt-level=2 -Csymbol-mangling-version=v0` | `0` | `0` (`"42"`) | Same post-inline avoidance |
| `noinline_opt2_v0` | `--edition=2024 -Copt-level=2 -Csymbol-mangling-version=v0` | `101` | — | `v0.rs:591:37` on `id_noinline::<unsafe<'a> &'a mut u32>` |
| `noinline_opt2_legacy` | `--edition=2024 -Copt-level=2 -Zunstable-options -Csymbol-mangling-version=legacy` | `0` | `0` (`"41"`) | Succeeds |
| `drop_glue_opt0_v0` | `--edition=2024 -Copt-level=0 -Csymbol-mangling-version=v0` | `101` | — | `v0.rs:591:37` on `drop_in_place::<unsafe<> ManuallyDrop<String>>` |
| `drop_glue_opt0_legacy` | `--edition=2024 -Copt-level=0 -Zunstable-options -Csymbol-mangling-version=legacy` | `0` | `0` (`"DROP_OK"`) | Succeeds via `pretty_print_type` (`pretty.rs:815-819`) |

#### Prefix-Free `v0` Production Extension (`Z [G<n>_] <ty>`) and Collision Analysis

Auditing every uppercase production head in `compiler/rustc_symbol_mangling/src/v0.rs` (`lines 127-1062` at `5debe6a12`) reveals that:
* Lowercase letters `a, b, c, d, e, f, h, i, j, l, m, n, o, p, s, t, u, x, y, z` encode primitives/unit/`Param`/paths, `'v'` marks C-variadic, and `'w'` marks splatted args.
* Among `A..Z`, `'A'` (Array), `'B'` (Backref), `'C'` (Crate/Float/Const), `'D'` (Dyn), `'E'` (End), `'F'` (FnPtr), `'G'` (Binder), `'I'` (Generic path), `'K'` (ABI), `'L'` (Lifetime), `'M'` (Inherent impl), `'N'` (Nested path), `'O'` (`*mut`/Pat Or), `'P'` (`*const`), `'Q'` (`&mut`), `'R'` (`&`/Range), `'S'` (Slice), `'T'` (Tuple), `'U'` (`unsafe fn`), `'V'` (Const value), `'W'` (Pat), `'X'` (Trait impl), `'Y'` (QSelf/Assoc) are all assigned, leaving **only `'H'`, `'J'`, and `'Z'`** completely unused as grammar tag heads.
* Choosing tag `'Z'` with `self.wrap_binder(...)` mirrors `ty::FnPtr` (`F`) and `ty::Dynamic` (`D`):
  ```text
  <type> ::= ... | Z [<generic-args-binder-G>] <type>
  where wrap_binder emits "" for 0 bound lifetimes, "G_" for 1, "G0_" for 2, etc.
  ```
* Choosing any in-grammar FnPtr/Tuple delimiter instead of `'Z'` breaks prefix-freeness:
  * **`'U'` collides with `unsafe fn`:** Under `'U'`, `fn(unsafe<> u32) -> u32` mangles to `FUmEm`, bit-for-bit identical to `unsafe fn(u32) -> u32` (`mangle_unsafeBinder_collides_if_using_U`).
  * **`'G'` collides with HRTB binders inside `FnPtr`:** Under `'G'`, a `fn` argument starting with `unsafe<'a> &'a mut u32` creates `G_<ty>` ambiguity with `for<'a> fn(&'a mut u32) -> u32` (`FG_QL0_mEm`, `mangle_unsafeBinder_collides_if_using_G`). Furthermore, inside `unsafe<> (unsafe<> T)`, omitted `bl=0` prefixes would be swallowed by a greedy `'G'` parser if the inner type could begin with `'G'`.
  * **`'K'` collides with `extern "C"` ABI prefixes:** Inside `FnPtr`, `'F'` parses optional `"KC"` / `"K<abi>"` (`v0.rs:648-657`) after optional `'U'` (`mangle_unsafeBinder_collides_if_using_K`: `FKCEm`).
  * **`'E'` collides with `FnPtr` / `Tuple` end delimiters:** (`mangle_unsafeBinder_collides_if_using_E`: `FEm`).

In `support/UnsafeBindersManglingValidityAndScalarizeSoundness.lean` (Part IV, lines `1720-2593`), we construct total encoder `encodeMangleTy`, exact RFC 2603 base-62 integer codec (`encodeInteger62`/`decodeInteger62`), fuel-indexed decoder `decodeMangleTy`, head-separation invariant `encodeMangleTy_head_not_ctrl` (`c ∉ {'L','G','U','K','E','_'}`), round-trip proof `decodeMangleTy_encodeMangleTy_roundtrip`, full prefix-freeness (`encodeMangleTy_prefix_free`), and injectivity (`encodeMangleTy_injective`), together with golden certificates `unsafe<> u32 ↦ "Zm"`, `unsafe<'a> &'a mut u32 ↦ "ZG_QL0_m"`, and `fn(unsafe<> u32) -> u32 ↦ "FZmEm" ≠ "FUmEm"`.

---

### 4. Miri Validity Panic (`validity.rs:987` / `994`), `-Zmiri-disable-validation` Aliasing Suppression, and Recursive Fix

**Basis:** `source` + `execution` + `derived`

At evaluation time, `rustc_const_eval/src/interpret/` treats `UnsafeBinder` as layout-transparent bytes with provenance:
* `step.rs:291-296`: `WrapUnsafeBinder(op, _ty)` evaluates `op` and invokes `self.copy_op_allow_transmute(&op, &dest)` (*"Constructing an unsafe binder acts like a transmute since the operand's layout does not change."*).
* `projection.rs:417`: `UnwrapUnsafeBinder(target)` returns `base.transmute(self.layout_of(target)?, self)?`.

However, `ValidityVisitor::try_visit_primitive` in `compiler/rustc_const_eval/src/interpret/validity.rs` (`L987` at `5debe6a12`: `ty::UnsafeBinder(_) => unimplemented!("FIXME(unsafe_binder)")`; `L994` at `14210df0e`: `ty::UnsafeBinder(_) => todo!("FIXME(unsafe_binder)")`) aborts immediately with a Rust ICE whenever operand validation runs under default validation settings.

#### Executed Miri Matrix & Soundness Controls (`14210df0e`)

| Miri Probe Case | `MIRIFLAGS` | Exit `rc` | Observed Output / Failure |
| --- | --- | --- | --- |
| `ubinder_probe` (`sb_default`) | *(none, Stacked Borrows)* | `101` | `panicked at <rustc>/compiler/rustc_const_eval/src/interpret/validity.rs:994:36: not yet implemented: FIXME(unsafe_binder)` during `eval_rvalue_into_place` (`wrap_binder!`) |
| `ubinder_probe` (`tb_default`) | `-Zmiri-tree-borrows` | `101` | Same panic at `validity.rs:994:36` |
| `ubinder_probe` (`sb_disable_validation`) | `-Zmiri-disable-validation` | `0` | `REF=41 MUT=42 TUP=7 RP=12 DUP=(20, 20)` (**aliasing UB inside `dup_mut_via_ptr_read` undetected**) |
| `ubinder_probe` (`tb_disable_validation`) | `-Zmiri-tree-borrows -Zmiri-disable-validation` | `0` | `REF=41 MUT=42 TUP=7 RP=12 DUP=(20, 20)` (**Tree Borrows aliasing UB undetected**) |
| Control `invalid_bool__default` | *(none)* | `101` | `panicked at validity.rs:994:36` on `core::mem::transmute::<u8, unsafe<> bool>(2u8)` inside `InterpCx::cast` before catching invalid `bool` `2u8` |
| Control `invalid_bool__disable_validation` | `-Zmiri-disable-validation` | `0` | `INVALID_BOOL_SURVIVED` (**invalid bit pattern `2u8` accepted without UB**) |
| Control `dup_raw__default` | *(none)* | `1` | `error: Undefined Behavior: attempting a write access using <tag> ... invalidated at offsets [0x0..0x4] by a Unique retag` (Stacked Borrows catches UB on plain `&mut *p` aliasing) |
| Control `dup_raw__disable_validation` | `-Zmiri-disable-validation` | `0` | `DUP_RAW=(20, 20)` (**confirms `-Zmiri-disable-validation` disables Stacked Borrows aliasing checks globally**) |

Look at why `-Zmiri-disable-validation` disables aliasing checks even when combined with `-Zmiri-tree-borrows` or default Stacked Borrows: in `src/tools/miri/src/bin/miri.rs` (`L689-692` at `5debe6a12`; `L734-737` at `14210df0e`), Miri explicitly zeros `borrow_tracker`:

```rust
// Disabling validation also disables aliasing checks (as retags are done during validation).
if miri_config.validation == ValidationMode::No {
    miri_config.borrow_tracker = None;
}
```

#### Mechanized Sound Fix (`validateValCore true`)

Because `ValidityVisitor` runs lazily during operand writes/casts/calls (`validate_operand_internal`) and Miri triggers pointer retags *during* validation, repairing `validity.rs:987`/`994` requires delegating `ty::UnsafeBinder(bound_ty)` recursively to `tcx.instantiate_bound_regions_with_erased(*bound_ty)` (preserving `WithRetag` and `ValidityMode`) rather than returning `interp_ok(true)`. Notice why `interp_ok(true)` (skip-validation) would still be unsound: as modeled by `fixedValidity_catches_invalid_bool_in_binder` and `fixedValidity_catches_dangling_ref_in_binder` (`support/UnsafeBindersManglingValidityAndScalarizeSoundness.lean:1023-1037`), transmuting `2u8` into `unsafe<> bool` or reading a dangling `unsafe<'a> &'a u32` violates Rust's bit-validity and dereferenceable-reference invariants; only delegating validation (`validateValCore true`) rejects invalid inner scalars, dangling pointers, and duplicated `&mut` borrows (`runDupMutScenario .shallow .enabled = .err .aliasingUB`, `L1071`) while guaranteeing zero `fixmeUnsafeBinder` panics (`fixedValidity_never_fixme`, `L884-1020`) and explaining why `ValidationMode.no` kills `borrow_tracker` (`disable_validation_kills_borrow_tracker` `L574`, `disable_validation_hides_dup_mut_aliasing` `L1075`).

Note also one subtle interaction in `runtime-post-cleanup` MIR: inspecting `dup_mut_via_ptr_read.3-2-000.runtime-post-cleanup.after.mir` reveals:
```rust
_11 = no_retag copy unwrap_binder!(_2; &mut u32);
_7 = &mut (*_11);
_12 = no_retag copy unwrap_binder!(_4; &mut u32);
_8 = &mut (*_12);
```
Even when `no_retag` suppresses retagging on the intermediate local move (`_11`, `_12`), the reborrow `_7 = &mut (*_11)` (and the original `wrap_binder!(&mut v)` / `ptr::read` assignment once `validity.rs:987` delegates validation to `&'erased mut u32`) restores full Stacked/Tree Borrows aliasing detection.

---

### 5. `SROA` and `GVN` MIR Optimization Opacity vs. `ReferencePropagation` Pass-Through and LLVM Lowering

**Basis:** `source` + `execution` + `derived`

Despite zero runtime overhead in codegen, unsafe binders create an optimization cliff in mid-level MIR (`-Zmir-opt-level=2`):

1. **`ScalarReplacementOfAggregates` (`compiler/rustc_mir_transform/src/sroa.rs`):**
   * `EscapeVisitor::visit_place` (`L100-103` at `5debe6a12`; `L111-114` at `14210df0e`) only exempts projections starting with `PlaceElem::Field(..)`:
     ```rust
     if let &[PlaceElem::Field(..), ..] = &place.projection[..] {
         return;
     }
     ```
     Any projection beginning with `PlaceElem::UnwrapUnsafeBinder(..)` falls through to `self.super_place`, marking the binder local as escaping (`self.set.insert(local)` at `L95`/`L106`).
   * `EscapeVisitor::visit_assign` (`L112-121` HEAD; `L123-132` installed) only exempts `Rvalue::Aggregate(..) | Rvalue::Use(..)`, so `_6 = wrap_binder!(move _7; unsafe<> (u32, u64))` (`Rvalue::WrapUnsafeBinder`) treats the local as escaping/non-scalarizable.
   * `ReplacementMap::replace_place` (`L148-154` HEAD; `L159-165` installed) strictly matches `&[PlaceElem::Field(f, _), ref rest @ ..]`, ignoring `UnwrapUnsafeBinder`.
   * `rustc_mir_dataflow/src/value_analysis.rs:995-1034` (`iter_fields`) handles `Tuple`, `Adt`, `Closure`, `Coroutine`, and `CoroutineClosure`, returning `()` (`_ => ()`, `L1032`) for `ty::UnsafeBinder`.

2. **`GVN` (`compiler/rustc_mir_transform/src/gvn.rs`):**
   * `Rvalue::WrapUnsafeBinder(ref mut op, _)` (`L1101-1104` HEAD; `L1095-1098` installed) lowers to `Value::Cast { kind: CastKind::Transmute, value }`.
   * `ProjectionElem::UnwrapUnsafeBinder(_)` (`L921` HEAD; `L914` installed) records `Value::Projection(value, ProjectionElem::UnwrapUnsafeBinder(()))` unconditionally, with **no algebraic rule canceling `Projection(Cast { kind: Transmute, value }, UnwrapUnsafeBinder(()))` back to `value`** (modeled directly by `gvn_current_fails_wrap_unwrap_tuple` vs `gvn_fixed_cancels_wrap_unwrap_tuple` in `UnsafeBindersManglingValidityAndScalarizeSoundness.lean:1553-1565`).
   * `ty_may_have_ref_inner` (`L1753` HEAD) classifies `ty::UnsafeBinder(_)` as `true` unconditionally, blocking downstream value-inference optimizations assuming reference-freeness.

3. **`ReferencePropagation` (`compiler/rustc_mir_transform/src/ref_prop.rs:193-202`):**
   * Because `ProjectionElem::UnwrapUnsafeBinder::is_stable_offset()` returns `true` (`statement.rs:287`), `is_constant_place` accepts places containing `UnwrapUnsafeBinder` both directly and after an initial `Deref`:
     ```rust
     rest.iter().all(PlaceElem::is_stable_offset)
     ```
   * Live `-Zdump-mir=all` confirms this exact dichotomy:
     * **`wrap_unwrap_tuple` retains all binder scaffolding through `runtime-optimized.after.mir`:**
       ```rust
       StorageLive(_3);
       _3 = (copy _1, copy _2);
       StorageLive(_4);
       _4 = wrap_binder!(copy _3; unsafe<> (u32, u64));
       _0 = copy (unwrap_binder!(_4; (u32, u64)).0: u32);
       StorageDead(_4);
       StorageDead(_3);
       ```
     * **`ref_prop_through_unwrap` eliminates the intermediate `&u32` borrow `_2` across `UnwrapUnsafeBinder`:**
       Before `ReferencePropagation`: `_3 = &(unwrap_binder!((*_1); (u32, u64)).0: u32); _2 = copy _3; _0 = copy (*_2);`
       In `runtime-optimized.after.mir`: `_0 = copy (unwrap_binder!((*_1); (u32, u64)).0: u32);`.

4. **Zero-Cost Codegen & LLVM `-Copt-level=2` Elimination:**
   * `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:845-850` (`5debe6a12`; `L734-739` at `14210df0e`): `WrapUnsafeBinder` computes `layout_of(monomorphized binder_ty)` and returns `OperandRef { val: operand.val, layout, move_annotation: None }` with zero emitted instructions.
   * `compiler/rustc_codegen_ssa/src/mir/place.rs:383-385` (`5debe6a12`; `L363-365` at `14210df0e`): `UnwrapUnsafeBinder(ty)` emits `cg_base.project_type(bx, self.monomorphize(ty))` with zero address arithmetic.
   * Thus LLVM `-Copt-level=2` (`opt2_v0` IR) collapses the surviving MIR completely:
     * `wrap_unwrap_tuple(i32 noundef returned %a, i64 noundef %b)` -> `start: ret i32 %a`
     * `wrap_unwrap_ref` -> `%_0 = load i32, ptr %x, align 4, !noundef !4; ret i32 %_0`
     * `ref_prop_through_unwrap` -> `%_0 = load i32, ptr %wb, align 8, !noundef !4; ret i32 %_0`
     * `dup_mut_via_ptr_read` -> `store i32 20, ptr %x, align 4; ret { i32, i32 } { i32 20, i32 20 }` (confirming LLVM dead-store elimination over the aliased `*r1 = 10` write because `dup_mut_via_ptr_read` violated `&mut` uniqueness UB).

5. **Mechanized Soundness Under `deinitMovedPlace` (`unwrap_wrap_cancel_sound` and `sroa_binder_scalarize_sound`):**
   * `unwrap_wrap_cancel_sound` (`support/UnsafeBindersManglingValidityAndScalarizeSoundness.lean:1270-1522`) proves across *both* `deinitMovedPlace = false` (stock codegen) and `deinitMovedPlace = true` (strict move-deinitializing semantics) that `[StorageLive(wb), wb = wrap_binder!(op), dst = unwrap_binder!(wb), StorageDead(wb)]` and `[dst = op]` either fail with the exact same error `e` or yield states agreeing on every local `i ≠ wbIdx` and all memory/tracker fields—confirming algebraic cancellation preserves even `move` deinitialization when `op` is disjoint from `wb`.
   * `sroa_binder_scalarize_sound` (`L1570-1719`) proves that replacing `tup = (a, b); wb = wrap_binder!(tup); ret = unwrap_binder!(wb).0` with scalarized locals `(f0, f1)` produces identical `ret` value `va` and memory `s1.mem = s2.mem`.

## Boundaries

* **unsupported — `Anneal` MIR Verification of `unsafe_binders`:** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean:285,308-321,462,469-475,578,612-628`) fails closed with `.unsupported` / `FaultKind.unsupported` for `TyKind::UnsafeBinder`, `ProjectionElem::UnwrapUnsafeBinder`, and `Rvalue::WrapUnsafeBinder`.
* **unsupported — Upstream Default `v0` Symbol Mangling & Miri Validation on `unsafe_binders`:** `rustc_symbol_mangling/src/v0.rs` (`679` at `5debe6a12`; `591` at `14210df0e`) and `rustc_const_eval/src/interpret/validity.rs` (`987` at `5debe6a12`; `994` at `14210df0e`) explicitly panic via `unimplemented!()` / `todo!()`.
* **known not to apply — `-Copt-level=2` ICE Avoidance to Non-Inlined Items or `-Csymbol-mangling-version=hashed`:** Compiling with `-Copt-level=2` only avoids `v0.rs:679`/`591` if LLVM/MIR inlining removes all mono items whose `Instance` involves `ty::UnsafeBinder` (`ptr_read_opt2_v0` passes, whereas `noinline_opt2_v0` ICEs). Switching to `-Csymbol-mangling-version=hashed` does *not* bypass `v0` because `hashed` computes the `v0::mangle` string first (`ptr_read_opt0_hashed` ICEs).
* **known not to apply — `-Zmiri-disable-validation` to Sound UB Verification:** Passing `-Zmiri-disable-validation` clears `miri_config.borrow_tracker = None` (`miri.rs:690-692` / `735-737`), hiding both invalid-bit-pattern UB (`invalid_bool__disable_validation`) and `&mut` / `*mut` Stacked/Tree Borrows aliasing UB (`dup_raw__disable_validation`, `sb_disable_validation`, `tb_disable_validation`).
* **known not to apply — Explicit Inner `Copy`/`ManuallyDrop<Copy>` Ergonomics to `unsafe<'a> T: Copy`:** Even `unsafe<> u32` fails `E0382` and `E0277` because `candidate_assembly.rs:1176` lacks any `Copy`/`Clone` candidate for `ty::UnsafeBinder(_)`; similarly `unsafe<'b> unsafe<'a> &'a u32` fails `BikeshedGuaranteedNoDrop` because `confirmation.rs:1237` routes nested `UnsafeBinder` through `Copy`.
* **not examined — Compile-Time CTFE Evaluation of `wrap_binder!`/`unwrap_binder!` Inside `const` Items:** Const evaluation invokes the same `rustc_const_eval/src/interpret/{step.rs, projection.rs, validity.rs}` interpreter; whether CTFE intern/valtree validation hits `validity.rs:987` on `const` expressions involving `unsafe_binders` was not separately probed via a `const fn` test binary (Miri runtime validation via `eval_rvalue_into_place` and `cast` was executed directly).
* **not examined — Other MIR Passes Beyond `SROA`, `GVN`, and `ReferencePropagation` (`DestinationPropagation`, `ConstProp`, `InstSimplify`):** Individual intermediate MIR files for passes outside the target set in `probe_unsafe_binders_v0_ice_miri_and_mir_opt.py` were not isolated individually, though their net effect is bounded directly by `runtime-optimized.after.mir`, where `wrap_binder!`/`unwrap_binder!` persists in `wrap_unwrap_tuple`.
* **not examined — `ty::View(..)` & Non-`x86_64-unknown-linux-gnu` Targets:** Upstream `v0.rs:691`, `gvn.rs:1760`, and `confirmation.rs:1257` also carry `FIXME(scrabsha)` `unimplemented!()` arms for `ty::View(..)`, which was outside this study; architectures other than `x86_64-unknown-linux-gnu` were not executed.
* **unknown — Future Upstream Design Evolution:** Upstream `FIXME` comments in `wf.rs:979-980`, `candidate_assembly.rs:1174-1175`, `statement.rs:315`, `v0.rs:678`, and `validity.rs:987` document unresolved upstream design choices (e.g., whether `UnsafeBinder` will remain `!Copy` permanently or allow non-`G`/non-`Z` RFC 2603 tag choices, and whether lifetime-bound retagging on `unwrap_binder!` needs specialized Miri Tree Borrows rules beyond `instantiate_bound_regions_with_erased`).

## Evidence

### 1. Primary-Source Repository Coordinates

| Subject Revision | File & Line Range | Symbol / Mechanism Observed |
| --- | --- | --- |
| `rust-lang/rust@5debe6a1244452beced762385f88a51857a915fc` | `library/core/src/unsafe_binder.rs:4-17` | `wrap_binder!` -> `k#wrap_binder`, `unwrap_binder!` -> `k#unwrap_binder` |
| `5debe6a12` | `compiler/rustc_type_ir/src/ty_kind.rs:1357` | `pub struct UnsafeBinderInner<I: Interner>(ty::Binder<I, I::Ty>)` |
| `5debe6a12` | `compiler/rustc_middle/src/mir/syntax.rs:1262,1469` | `ProjectionElem::UnwrapUnsafeBinder(T)`, `Rvalue::WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>)` |
| `5debe6a12` | `compiler/rustc_middle/src/mir/statement.rs:273,287,316,808,864` | `is_indirect=false`, `is_stable_offset=true`, `can_use_in_debuginfo=false`, `is_safe_to_remove=true`, `Rvalue::ty` |
| `5debe6a12` | `compiler/rustc_mir_build/src/builder/expr/as_place.rs:535-546` | `PlaceUnwrapUnsafeBinder` / `ValueUnwrapUnsafeBinder` -> `PlaceElem::UnwrapUnsafeBinder` |
| `5debe6a12` | `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs:361-372` | `ExprKind::WrapUnsafeBinder` -> `Rvalue::WrapUnsafeBinder` |
| `5debe6a12` | `compiler/rustc_mir_build/src/check_unsafety.rs:611-615` | `requires_unsafe(expr.span, UnsafeBinderCast)` (`E0133`) |
| `5debe6a12` | `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:1174-1176` | `ty::UnsafeBinder(_) => {}` (zero builtin `Copy`/`Clone` candidates) |
| `5debe6a12` | `compiler/rustc_trait_selection/src/traits/wf.rs:978-993` | `LangItem::BikeshedGuaranteedNoDrop` obligation on `ty::UnsafeBinder` |
| `5debe6a12` | `compiler/rustc_trait_selection/src/traits/select/confirmation.rs:1173-1250` | `confirm_bikeshed_guaranteed_no_drop_candidate` (`&T`/`&mut T`/`ManuallyDrop`/`Copy`) |
| `5debe6a12` | `compiler/rustc_ty_utils/src/{layout.rs:874-877, needs_drop.rs:239-242}` | Layout and drop delegation to `instantiate_bound_regions_with_erased` |
| `5debe6a12` / `14210df0e` | `compiler/rustc_mir_transform/src/validate.rs:{890-908,1461-1477}` / `{872-890,1432-1448}` | `Validator` binder checks and `"WrapUnsafeBinder..."` copy-paste error message |
| `5debe6a12` / `14210df0e` | `compiler/rustc_mir_transform/src/sroa.rs:{100,115,148}` / `{111,126,159}` | `Field`-only escape/replacement checks |
| `5debe6a12` | `compiler/rustc_mir_dataflow/src/value_analysis.rs:995-1034` | `iter_fields` ignores `ty::UnsafeBinder` (`_ => ()` at `L1032`) |
| `5debe6a12` / `14210df0e` | `compiler/rustc_mir_transform/src/gvn.rs:{921,1101,1753}` / `{914,1095}` | `UnwrapUnsafeBinder(())` opacity, `CastKind::Transmute`, conservative `ty_may_have_ref_inner` |
| `5debe6a12` | `compiler/rustc_mir_transform/src/ref_prop.rs:193-202` | `is_constant_place` accepts `is_stable_offset` (`UnwrapUnsafeBinder`) |
| `5debe6a12` | `compiler/rustc_session/src/options.rs:2440-2442` | Default `symbol-mangling-version` is `v0` |
| `5debe6a12` / `14210df0e` | `compiler/rustc_symbol_mangling/src/v0.rs:679` / `591` | `ty::UnsafeBinder(..) => unimplemented!()` / `todo!()` |
| `5debe6a12` | `compiler/rustc_symbol_mangling/src/legacy.rs:70-87,125-140` + `pretty.rs:815-819` | `legacy::mangle` hashes args and skips arg names outside drop shims |
| `5debe6a12` | `compiler/rustc_const_eval/src/interpret/{step.rs:291-296, projection.rs:417}` | `copy_op_allow_transmute` & `base.transmute(layout_of(target))` |
| `5debe6a12` / `14210df0e` | `compiler/rustc_const_eval/src/interpret/validity.rs:987` / `994` | `unimplemented!("FIXME(unsafe_binder)")` / `todo!("FIXME(unsafe_binder)")` |
| `5debe6a12` / `14210df0e` | `src/tools/miri/src/bin/miri.rs:{475-477,689-692}` / `{518-520,734-737}` | `ValidationMode::No` sets `miri_config.borrow_tracker = None` |
| `5debe6a12` / `14210df0e` | `compiler/rustc_codegen_ssa/src/mir/{rvalue.rs:845-850, place.rs:383-385}` / `{734-739,363-365}` | Transparent layout rewrap and `project_type` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:285,308-321,462,469-475,578,612-628` | `.unsupported` fail-closed boundary (referencing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`) |

### 2. Executed Probe & Preserved Support Artifacts (`2026-11-23`)

* **`support/probe_unsafe_binders_v0_ice_miri_and_mir_opt.py`**: Self-contained Python 3 driver exercising `rustc` (`1.98.0-nightly`, `14210df0e`) and `cargo +nightly miri run` (`miri 0.1.0`, `14210df0e2`) across 5 suites: 9 static checks (`rc=1` on all 8 error cases, `rc=0` on `wf_accepts_manually_drop_string`), 10 mangling matrix builds/executions, 2 MIR/LLVM dump pipelines (`opt0_legacy` producing 5 LLVM IR functions and 20 MIR dumps, `opt2_v0` producing 5 LLVM IR functions and 50 MIR dumps), 4 Miri differential executions on `ubinder_probe`, and 4 Miri control executions on `invalid_bool` / `dup_raw`.
* **`support/probe_results.json`**: Complete sanitized JSON capture from executing `probe_unsafe_binders_v0_ice_miri_and_mir_opt.py --json-out support/probe_results.json`.

### 3. Mechanized Lean `v4.34.1` Formalization (`support/UnsafeBindersManglingValidityAndScalarizeSoundness.lean`)

Verified on `2026-11-23` using `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`) and a Lean MetaM constant/axiom inspector checking every theorem and `noncomputable def` in the module environment:
* **Metrics:** 2,593 lines, 1,439 local constants, 620 theorems, 684 definitions (`unsafe_recs = []`, `bad_axioms = []`; zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `deriving` clauses).
* **Core Checked Theorems:**
  * Part I (Types, Layout, Lifetime Erasure): `eraseRegionAt_of_lt`, `eraseBoundRegions_closed`, `eraseRegionAt_reduces_closed`, `eraseBoundRegions_reduces_closed`, `tyIsCopy_unsafeBinder_false`, `wf_accepts_mut_ref_binder`, `wf_accepts_manuallyDrop_binder`, `wf_rejects_nested_unsafeBinder`, `tyLayout_eraseBoundRegions`, `tyLayout_unsafeBinder`.
  * Part II (Miri Validity Fix & Tracker Interaction): `disable_validation_kills_borrow_tracker`, `stockMiri_panics_on_unsafeBinder`, `fixedValidity_unsafeBinder_delegates`, `fixedValidity_never_fixme`, `fixedValidity_catches_invalid_bool_in_binder`, `disable_validation_misses_invalid_bool`, `fixedValidity_catches_dangling_ref_in_binder`, `fixedValidity_catches_dup_mut_aliasing`, `disable_validation_hides_dup_mut_aliasing`.
  * Part III (MIR Semantics, Algebraic Cancellation, GVN, SROA): `unwrap_wrap_cancel_sound` (both `deinitMovedPlace = true` and `false`), `gvn_current_fails_wrap_unwrap_tuple`, `gvn_fixed_cancels_wrap_unwrap_tuple`, `sroa_binder_scalarize_sound`.
  * Part IV (RFC 2603 Base-62 & `'Z'` Extension Codec): `decodeDigit62_encodeDigit62`, `encodePosDigits62_stepDigits`, `decodeInteger62_encodeInteger62_roundtrip`, `decodeOptInteger62_encodeOptInteger62_roundtrip`, `decodeMangleRegion_encodeMangleRegion_roundtrip`, `encodeMangleTy_head_not_ctrl`, `decodeMangleTy_encodeMangleTy_roundtrip`, `encodeMangleTy_prefix_free`, `encodeMangleTy_injective`, plus golden/collision theorems `mangle_unsafeBinder_empty_u32_golden`, `mangle_unsafeBinder_mut_ref_golden`, `mangle_fnPtr_taking_unsafeBinder_vs_unsafeFn_distinct`, and `mangle_unsafeBinder_collides_if_using_{U,G,K,E}`.

## Revalidation

To test whether these compiler behaviors, Miri panics, optimization boundaries, or Anneal exclusions have changed in a newer toolchain or upstream revision, run the following focused checks from a report package directory:

1. **Re-run the complete live `rustc` + `miri` differential probe:**
   ```bash
   python3 support/probe_unsafe_binders_v0_ice_miri_and_mir_opt.py \
     --json-out /tmp/unsafe_binders_revalidation.json
   ```
   Check in particular whether `ptr_read_opt0_default` / `noinline_opt2_v0` transition from `rc=101` to `rc=0` (indicating `v0.rs:679` gained `ty::UnsafeBinder` support), whether `sb_default` stops panicking at `validity.rs:987`/`994` and starts catching aliasing UB (`rc=1` matching `dup_raw__default`), and whether `wrap_unwrap_tuple.runtime-optimized.after.mir` eliminates `wrap_binder!` / `unwrap_binder!`.
2. **Inspect the narrow upstream watchlist lines (`git diff` across target revisions of `rust-lang/rust`):**
   * `compiler/rustc_symbol_mangling/src/v0.rs` around `ty::UnsafeBinder(..)` (checking any tag choice for prefix-freeness against `'G'`, `'U'`, `'K'`, `'E'`)
   * `compiler/rustc_const_eval/src/interpret/validity.rs` around `ty::UnsafeBinder(_)` (verifying recursive delegation vs. skip-validation)
   * `src/tools/miri/src/bin/miri.rs` around `ValidationMode::No` / `borrow_tracker`
   * `compiler/rustc_mir_transform/src/{sroa.rs, gvn.rs, validate.rs}` and `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` (`ty::UnsafeBinder(_)`)
3. **Inspect `joshlf/anneal` MIR AST support:** Check `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `ProjectionElem`, `Rvalue`) to see whether `UnsafeBinder`, `UnwrapUnsafeBinder`, and `WrapUnsafeBinder` remain fail-closed `.unsupported` or have promoted to first-class constructors.
4. **Re-verify the Lean `v4.34.1` kernel proofs:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/UnsafeBindersManglingValidityAndScalarizeSoundness.lean
   ```
