# Rust Zero-Sized `FnDef` Items, Non-Null `FnPtr` Niche Layouts, Closure-to-`fn` Coercion, and `#[track_caller]` `ReifyShim` Wrapper Synthesis

## Summary

In `rustc`, every free function item, associated function, and monomorphized callee inhabits a unique zero-sized `TyKind::FnDef` type (`size = 0`, `align = 1`, `BackendRepr::Memory { sized: true }`, `largest_niche: None`) that encodes identity statically at the type level and compiles generic call sites to direct monomorphized calls with zero pointer indirection and zero ABI argument overhead for the callee value itself. Coercing a function item (`PointerCoercion::ReifyFnPointer`) or a zero-upvar closure (`PointerCoercion::ClosureFnPointer`) produces an erased `TyKind::FnPtr` scalar pointer (`size = 8`, `align = 8` on 64-bit targets, `BackendRepr::Scalar`) whose `Scalar::Initialized` validity range excludes zero (`valid_range = 1..=u64::MAX`), emitting LLVM `nonnull` parameter/return metadata, allowing `Option<fn(...)>` (for all ABIs including `extern "C"` and `unsafe extern "C"`) to collapse to `8` bytes with `None` represented by bit pattern `0`, and causing `null` `fn()` construction to fail Miri validity checks as immediate Undefined Behavior.

Coercion from closures is strictly stricter than RFC 2229 capture analysis: `sig_for_closure_coercion` inspects `tcx.upvars_mentioned` before capture minimization runs, so a closure that merely mentions a binding in an unused local (`let _ = k;`) fails with `E0308` (`closures can only be coerced to fn types if they do not capture any variables`) even when zero environment data would otherwise be needed. Non-capturing closures lower to `fn()` via `Instance::resolve_closure(..., ty::ClosureKind::FnOnce)` where the zero-sized `self` parameter is assigned `PassMode::Ignore` and dropped from the LLVM signature. When reifying a `#[track_caller]` `FnDef` to `fn()`, `rustc` cannot point directly at the target body (whose ABI takes an extra trailing 24-byte `core::panic::Location<'static>` parameter); instead `Instance::resolve_for_fn_ptr` synthesizes a wrapper shim (`ShimKind::Reify`) via `build_call_shim(..., CallKind::Direct(def_id))` whose `span = tcx.def_span(def_id)` is fixed statically to the `FnDef`'s own declaration span (`tracked_callee` line `4`), contrasting both with direct `FnDef` calls (which bind each callsite's location: lines `19` and `20`) and with `<FnDef as Fn>::call` trait calls (which lower through `ShimKind::FnPtr` and inherit `library/core/src/ops/function.rs:79`).

Across all examined `rust-lang/rust` revisions (`14210df0e` through `f7da9a423`), layout, niche selection, coercion gating, and shim synthesis semantics remain invariant aside from internal API refactors (`LayoutData::unit` dropping `cx` and switching `AbiAlign::new(dl.i8_align)` to `Align::ONE`, `TyKind::FnDef` wrapping generic args in `ty::Binder`, and enum niche helpers moving into `rustc_abi::layout::enum_layout`). All runtime, IR, MIR, KCFI, and Miri findings were empirically reproduced on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`103/103` checks passing), complemented by a standalone `1,626`-line Lean `v4.34.1` mechanization (`53` declared theorems; `260` kernel theorem constants under axioms `[Quot.sound, propext]` with `0` `_unsafe_rec` and `0` `Classical.choice`/`sorryAx`/`omega`/`bv_decide`/`native_decide`). Comparing against `joshlf/anneal` (`c131b320`), Anneal's trusted MIR semantics (`Trusted.MirAst` / `Trusted.MirSemantics`) presently fail closed on function types, pointer-coercion rvalues, and `TerminatorKind::Call`, while vendored `lean-miri` already models `ReifyFnPointer` and `ClosureFnPointer` casts.

## Applicability

### Subjects and Relationships

| Subject (`REPORT.json`) | Revision / Version | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (live `main` HEAD) | `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | Primary compiler source authority for `ty_kind.rs`, `sty.rs`, `layout.rs`, `enum_layout.rs`, `lib.rs` (`Niche`), `abi.rs`, `coercion.rs`, `instance.rs`, `shim.rs`, `rvalue.rs`, and `block.rs`. |
| `rust-lang/rust` (`rustc 1.98.0-nightly`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`) | Both primary-source audited and **empirically executed** toolchain for native `-O0`/`-O3` binaries, `--emit=llvm-ir`, `-Zdump-mir=all`, `-Zprint-type-sizes`, `-Zsanitizer=kcfi`, and `miri` (default and `-Zmir-opt-level=3 -Zinline-mir=yes`). |
| `rust-lang/rust` (intermediate snapshot) | `49d734536222bf28bb6d07d885b3a81d145981da` | Cross-revision source audit confirming stability of `FnPtr` niche layout, `FnDef` unit sizing, and `coercion.rs` gating. |
| `rust-lang/rust` (`rustc 1.102.0-nightly`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`) | Cross-revision source audit matching `f7da9a4` layout and coercion structure cleanly. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Target verification architecture evaluated for compatibility with `FnDef`/`FnPtr` layouts, ZST moves (`deinitMovedPlace`), coercions, and calls (`Trusted.MirAst`, `Trusted.MirSemantics`, `vendor/lean-miri`). |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel proof checker and MetaM environment auditor verifying `support/FnDefZstFnPtrNicheAndReifyShimSoundness.lean`. |

Multiple upstream `rust-lang/rust` revisions are combined to distinguish enduring architectural invariants from internal refactors between May 2026 and November 2026, while relating compiler lowering behavior directly to `joshlf/anneal`'s TCB boundaries and formalizing the mathematical model in Lean `v4.34.1`.

### Cross-Revision Comparison (`14210df` through `f7da9a4`)

Direct source comparison across the four audited `rust-lang/rust` commits establishes that the observable type-system, layout, coercion, and shim semantics are unchanged, while four internal source shapes evolved:

| Compiler Component | `14210df0e` (`2026-05-31`) | `49d734536` (`2026-09-11`) | `3ef0c22cd` (`2026-11-11`) & `f7da9a423` (`main`) | Effect on Observable Semantics |
| :--- | :--- | :--- | :--- | :--- |
| `TyKind::FnDef` variant (`ty_kind.rs`) | `FnDef(I::FunctionId, I::GenericArgs)` (L168) | Audited via `layout.rs` / `sty.rs` | `FnDef(I::FunctionId, ty::Binder<I, I::GenericArgs>)` (`f7da9a4` L223) | Wraps `FnDef` generic arguments in a `ty::Binder`; external `size_of`, coercion, and mono behavior unchanged. |
| `LayoutData::unit` signature & align (`layout.rs`, `simple.rs`) | `LayoutData::unit(cx, sized)` using `AbiAlign::new(dl.i8_align)` (`layout.rs:519`) | `LayoutData::unit(cx, sized)` (`layout.rs:550`) | `LayoutData::unit(sized)` using `align: Align::ONE` (`layout.rs:547`, `simple.rs:13-30`) | Drops `cx` parameter on ZST unit construction; on `x86_64`, `dl.i8_align` and `Align::ONE` are both `1` byte. |
| `TyKind::FnPtr` scalar layout (`layout.rs`) | `ptr.valid_range_mut().start = 1`, `LayoutData::scalar(cx, ptr)` (`L401-405`) | Identical at `L431-435` | Identical at `L428-432` | Identical `size = 8`, `valid_range = 1..=u64::MAX`, `Option<fn()> = 8 B` niche. |
| Enum niche layout module | Inline in `rustc_ty_utils/src/layout.rs` (`L574-743`) | Audited via `layout.rs` | Extracted to `rustc_abi/src/layout/enum_layout.rs` (`L15-58, 537-679` / `3ef0c22` `L558-664`) + `Niche::reserve` (`lib.rs:2122-2214`) | Code reorganization only; single invalid `0` value yields `niche_start = 0`, `BackendRepr::Scalar`. |
| Closure coercion check (`coercion.rs`) | `sig_for_closure_coercion` (`L1292+`, checks `upvars_mentioned`) | Identical logic (`L1292+`) | Identical logic (`L1342-1372`) | Mention-only captures consistently fail with `E0308`. |

### Scope Constraints

- **Target architecture and ABI**: Quantitative size/alignment figures (`FnPtr` = 8 B, align = 8 B, `Option<fn()>` = 8 B, `Option<Option<fn()>>` = 16 B, `Location` = 24 B) apply to 64-bit targets such as `x86_64-unknown-linux-gnu` (`edition = 2024`). On targets with 32-bit instruction pointers, pointer size scales accordingly while preserving non-null niche eligibility.
- **Standalone Lean model vs. live compiler**: Mechanized proofs in `support/FnDefZstFnPtrNicheAndReifyShimSoundness.lean` formalize an explicit mathematical model of these `rustc` subsystems inside Lean `v4.34.1` rather than executing against `rustc`'s Rust source or Anneal's live AST extraction pipeline.

## Findings

### 1. Type Representation and Size/Alignment Contrast (`TyKind::FnDef` vs. `TyKind::FnPtr`)

`rustc` maintains a strict representation divide between the uncoerced function item type `TyKind::FnDef` and the reified function pointer type `TyKind::FnPtr`. Every function item definition receives a distinct zero-sized singleton type encoding its compile-time item identity (`FunctionId` and generic arguments), whereas `TyKind::FnPtr` erases item identity into a uniform ABI-carrying code pointer.

```text
Basis: source + execution + derived
```

In upstream `compiler/rustc_type_ir/src/ty_kind.rs`:
- At `14210df0e` (`L168, L188`), the variants are `FnDef(I::FunctionId, I::GenericArgs)` and `FnPtr(ty::Binder<I, FnSigTys<I>>, FnHeader<I>)`.
- At `f7da9a423` (`L223, L243`), `FnDef` wraps its generic arguments in a binder: `FnDef(I::FunctionId, ty::Binder<I, I::GenericArgs>)`, while `FnPtr` retains `(ty::Binder<I, FnSigTys<I>>, FnHeader<I>)`.
- Constructors live in `compiler/rustc_middle/src/ty/sty.rs` (`Ty::new_fn_def`, `Ty::new_fn_ptr` at `f7da9a4` `L677-694`, `14210df` `L713-730`, `49d7345` `L708-725`, `3ef0c22` `L717-734`).

In `compiler/rustc_ty_utils/src/layout.rs`:
- **`FnDef` layout**: At `f7da9a4` / `3ef0c22` (`L544-547`), `let sized = matches!(ty.kind(), ty::FnDef(..)); tcx.mk_layout(LayoutData::unit(sized))` (`49d7345` `L547-550` and `14210df` `L516-519` call `LayoutData::unit(cx, sized)`). Per `compiler/rustc_abi/src/layout/simple.rs:13-30`, `LayoutData::unit(sized)` sets `size: Size::ZERO`, `align: Align::ONE` (`AbiAlign::new(dl.i8_align)` in `14210df`), `backend_repr: BackendRepr::Memory { sized }`, and `largest_niche: None`. Thus `FnDef` is a **1-aligned, 0-byte sized ZST with no niche**.
- **`FnPtr` layout**: At `f7da9a4` / `3ef0c22` (`L428-432`, identical at `49d7345` `L431-435` and `14210df` `L401-405`), `ty::FnPtr(..)` builds `scalar_unit(Pointer(dl.instruction_address_space))` with `ptr.valid_range_mut().start = 1` and returns `tcx.mk_layout(LayoutData::scalar(cx, ptr))`. On 64-bit `x86_64`, `Pointer` has size `8`, alignment `8`, and `valid_range = 1..=u64::MAX`.

Empirical measurements from Part A (`probe_a.rs` in `support/probe_fndef_fnptr_reify_shims.py`, recorded in `support/probe_results.json`) match identically across native binary execution and `miri --edition=2024`:

| Probe Key | Probe Expression (`probe_a.rs`) | Measured (Native & Miri) | Mechanism Confirmed |
| :--- | :--- | :--- | :--- |
| `FNDEF_SZ`, `FNDEF_ALIGN` | `size_of_val(&add_one)`, `align_of_val(&add_one)` | `0`, `1` | `LayoutData::unit(true)` (`size=0`, `align=1`). |
| `ID_U32_SZ`, `ID_U64_SZ` | `size_of_val(&generic_id::<u32>)`, `&generic_id::<u64>` | `0`, `0` | Distinct generic instantiations remain ZSTs. |
| `TUP_FNDEF_SZ` | `tuple_fndef_size(add_one)` (`size_of::<(F, u32)>()`) | `4` | `(FnDef, u32)` adds `0` bytes (`u32` size `4`, align `4`). |
| `FNPTR_SZ`, `FNPTR_ALIGN` | `size_of::<fn()>()`, `align_of::<fn()>()` | `8`, `8` | `LayoutData::scalar` over `Pointer(dl.instruction_address_space)`. |
| `TUP_FNPTR_SZ` | `size_of::<(fn(u32) -> u32, u32)>()` | `16` | `8` (ptr) + `4` (`u32`) + `4` (tail padding to align `8`) = `16` bytes. |
| `DISTINCT_FNDEFS` | `type_id_of_val(&add_one) != type_id_of_val(&sub_one) && generic_id::<u32> != generic_id::<u64>` | `true` | Distinct functions and distinct generic args yield distinct `FnDef` types (`TypeId`). |
| `SAME_FNPTR_TYPEID` | `fp1 = add_one; fp2 = sub_one; type_id_of_val(&fp1) == type_id_of_val(&fp2)` | `true` | Reification to `fn(u32) -> u32` erases item identity into a single `TypeId`. |

This representation contrast is formalized in Lean `v4.34.1` by `fnDef_layout_is_sized_zst` (`L306-310`), `fnPtr_layout_8B_nonnull_niche` (`L330-335`), and `tuple_fnDef_vs_fnPtr_with_u32` (`L323-325` for `(u32, FnDef)` vs `(u32, fn())` = `4` vs `16`) in `support/FnDefZstFnPtrNicheAndReifyShimSoundness.lean`.

### 2. Non-Null Pointer Niche Allocation in `Option<fn()>` and Multi-Variant Collapse

Because every `TyKind::FnPtr` marks address `0` outside its `WrappingRange`, Rust's enum layout engine uses bit pattern `0` to encode `Option::None` inside the same 8-byte scalar word for one `Option` wrapper, and immediately exhausts the scalar's niche supply so nested `Option<Option<fn()>>` expands to `16` bytes.

```text
Basis: source + execution + derived
```

#### Niche Mechanics in `rustc_abi`

Tracing `compiler/rustc_abi/src/lib.rs:2122-2214` and `compiler/rustc_abi/src/layout/enum_layout.rs:15-58, 537-679` (`f7da9a4`; identically structured in `3ef0c22` `L15-58, 558-664` and inline in `14210df` `layout.rs:574-743`):
1. `Niche::from_scalar` and `Niche::available` inspect a `FnPtr`'s `Scalar::Initialized` validity range (`start = 1`, `end = u64::MAX`), leaving exactly one unused bit pattern (`0`).
2. When laying out `Option<fn()>`, there is `count = 1` tagless variant (`None`) alongside the payload variant (`Some(fn())`). `Niche::reserve` evaluates the gaps around `valid_range`, finding `next_down = 0 <= next_up = 0` and choosing `move_start`. This sets `niche_start = 0`, assigns tag `0` to `None`, and expands the combined enum scalar's `valid_range` to `0..=u64::MAX`.
3. `calculate_niche_abi` detects that the niche occupies the single 8-byte scalar at offset `0` and produces `BackendRepr::Scalar(niche_scalar)` with no remaining niche.
4. Contrastingly:
   - `Option<FnDef>` (`size = 1`, `align = 1`): `FnDef` has `largest_niche: None` (`LayoutData::unit`), so `Option<FnDef>` falls back to a `1`-byte `Direct` tagged enum.
   - `Option<Option<fn()>>` (`size = 16`, `align = 8`): Once the inner `Option` claims bit pattern `0` (`valid_range = 0..=u64::MAX`), no niche remains for the outer `Option`, forcing a `Direct` tagged layout padded to `16` bytes.
   - `Option<extern "C" fn()>` and `Option<unsafe extern "C" fn(u32) -> u32>` (`size = 8`, `None = 0`): ABI and `unsafe` qualifiers preserve `valid_range.start = 1`.

#### Live Verification: Bit Representation, LLVM Attributes, and Miri UB

Part A of `support/probe_results.json` confirms every niche property across both native compilation and Miri, and `-Z print-type-sizes` reports:
```text
print-type-size type: `std::option::Option<extern "C" fn()>`: 8 bytes, alignment: 8 bytes
print-type-size type: `std::option::Option<fn()>`: 8 bytes, alignment: 8 bytes
```
Runtime and Miri checks record:
- `OPT_FNDEF_SZ=1`, `OPT_FNPTR_SZ=8`, `OPT_EXT_C_SZ=8`, `OPT_UNSAFE_EXT_C_SZ=8`, `OPT_OPT_FNPTR_SZ=16`.
- `NONE_BITS=0`, `NONE_C_BITS=0`, `SOME_NONZERO=true`, `SOME_C_NONZERO=true`, `ZERO_IS_NONE=true` (`transmute::<usize, Option<fn()>>(0usize).is_none()` evaluates to `true`).
- **Miri null-pointer UB probe (`probe_a_null_ub.rs`)**: `let bad: fn() = unsafe { transmute(0usize) };` emits compile warning `warning: the type fn() does not permit zero-initialization` and aborts Miri execution (exit code `1`) with:
  ```text
  error: Undefined Behavior: constructing invalid value of type fn(): encountered a null function pointer
   --> $WORK/probe_a_null_ub.rs:4:30
    |
  4 |     let bad: fn() = unsafe { transmute(0usize) };
    |                              ^^^^^^^^^^^^^^^^^ Undefined Behavior occurred here
  ```
- **LLVM IR metadata propagation (`rustc_ty_utils/src/abi.rs:318-338`, `rustc_codegen_llvm/src/abi.rs:43,47`)**: For `Scalar::Initialized { value: Pointer(_), valid_range }`, `!valid_range.contains(0)` sets `ArgAttribute::NonNull`, lowered to LLVM `AttributeKind::NonNull` (`nonnull`). In Part C (`probe_results.json` `-C opt-level=3 --emit=llvm-ir`):
  - Bare `fn(u32) -> u32` parameters and return values carry `nonnull`:
    ```llvm
    define noundef i32 @call_via_fnptr(ptr noundef nonnull readonly captures(none) %f, i32 noundef %x) unnamed_addr #4 personality ptr @rust_eh_personality {
    define noundef nonnull ptr @reify_step() unnamed_addr #5 {
    ```
  - `Option<fn(u32) -> u32>` omits `nonnull` (since `0` validly encodes `None`) and tests `null` directly:
    ```llvm
    define noundef i32 @unwrap_opt_fn(ptr noundef readonly captures(address_is_null) %0, i32 noundef %x) unnamed_addr #4 personality ptr @rust_eh_personality {
    start:
      %.not = icmp eq ptr %0, null
      br i1 %.not, label %bb5, label %bb3
    ```

The Lean formalization captures this completely in `option_fnPtr_layout_8B_nicheScalar` (`L357-361`), `option_fnDef_layout_1B_direct` (`L315-318`), `option_option_fnPtr_layout_16B_direct` (`L366-369`), `option_extern_c_fnPtr_layout_8B` (`L374-376`), `optFnPtr_niche_bijective` (`L460-462`), `null_word_invalid_for_fnPtr` (`L455-456`), `option_size_trichotomy` (`L1554-1558`), `nonNullPtrRange_cardinality_and_niche` (`L1484-1488`), and `optFnPtr_dispatch_soundness` (`L1440-1447`).

### 3. Pointer Coercion Rules: Function Items and Non-Capturing Closures vs. `E0308` Capturing Rejection

During HIR typechecking, `rustc` permits implicit pointer coercion from `TyKind::FnDef` to `TyKind::FnPtr` (`ReifyFnPointer`) and from zero-upvar `TyKind::Closure` to `TyKind::FnPtr` (`ClosureFnPointer`). Both are gated by syntactic/type-level predicates before MIR optimization, creating sharp edges for mention-only closures, safety narrowing, and intrinsics.

```text
Basis: source + execution + derived
```

#### Frontend Typecheck Dispatch (`rustc_hir_typeck/src/coercion.rs`)

In `compiler/rustc_hir_typeck/src/coercion.rs` (`f7da9a4` / `3ef0c22`, corresponding to `14210df` `L1053, L1079, L1292` and `49d7345` `L1041, L1067, L1292`):
1. `coerce` (`L327-346`) dispatches `(source, target)` where `target` is `ty::FnPtr`:
   - `ty::FnDef` -> `coerce_from_fn_item` (`L1091-1113`), constructing `PointerCoercion::ReifyFnPointer`.
   - `ty::Closure` -> `coerce_closure_to_fn` (`L1117-1134`), constructing `PointerCoercion::ClosureFnPointer`.
2. `sig_for_fn_def_coercion` (`L1305-1340`):
   - **Rejects compiler intrinsics**: fails when `tcx.intrinsic(def_id).is_some()` (`cannot coerce intrinsics to function pointers`).
   - **Rejects forced-inline items**: fails when `InlineAttr::Force` is set, while allowing `#[inline(always)]` items (`INLINE_ALWAYS=10` confirmed in Part B).
   - **Safety monotonicity**: permits `safe -> unsafe` coercion, rejects `unsafe -> safe` with `E0308` (`expected safe fn, found unsafe fn`).
3. `sig_for_closure_coercion` (`L1342-1372`):
   - **Upvar gate prior to RFC 2229 capture analysis**: checks `!tcx.upvars_mentioned(closure_def.expect_local()).is_none_or(|u| u.is_empty())`. Because `upvars_mentioned` records lexical HIR mentions of outer local bindings rather than the reduced set of captured fields under RFC 2229 capture analysis, any closure whose body mentions an outer variable fails with `E0308` (`closures can only be coerced to fn types if they do not capture any variables`) even if the value is immediately discarded (`let _ = k;`). Conversely, referencing a `const` item (`K_CONST: u32 = 10`) is not an upvar and coerces cleanly (`CONST_RES=42`).

#### Live Coercion Results and Negative Controls (`Part B`)

All 10 parsed metrics from `probe_b.rs` match identically across native execution and Miri (`probe_results.json`), while all 4 negative controls fail compilation with exit code `1`:

| Case | Exact Rust Construct (`probe_fndef_fnptr_reify_shims.py`) | Result (Native & Miri) | Mechanism |
| :--- | :--- | :--- | :--- |
| Non-capturing closure -> `fn` | `let noncap = \|x: u32\| x + 1; let f_noncap: fn(u32) -> u32 = noncap; f_noncap(41)` | `NONCAP_SZ=0`, `NONCAP=42` | `ClosureFnPointer(Safe)`; closure value stays ZST (`0` B). |
| Closure referencing `const` -> `fn` | `const K_CONST: u32 = 10; let f_const: fn(u32) -> u32 = \|x\| x + K_CONST; f_const(32)` | `CONST_RES=42` | `K_CONST` is a `const` item, not an upvar. |
| Safe closure -> `unsafe fn` | `let f_unsafe_from_closure: unsafe fn(u32) -> u32 = \|x\| x + 5;` (`arg=10`) | `UNSAFE_CLOSURE=15` | `ClosureFnPointer(Unsafe)` widens safety. |
| Safe `FnDef` -> `unsafe fn` | `let f_unsafe_from_fndef: unsafe fn(u32) -> u32 = safe_fn;` (`safe_fn(x) = x+3`, `arg=10`) | `UNSAFE_FNDEF=13` | `ReifyFnPointer(Unsafe)` widens safety. |
| `#[inline(always)]` `FnDef` -> `fn` | `let f_inline_always: fn(u32) -> u32 = inlined_always_fn;` (`x+2`, `arg=8`) | `INLINE_ALWAYS=10` | Permitted (`InlineAttr::Force` blocked, `#[inline(always)]` allowed). |
| `FnDef` via `F: Fn` generic vs `fn()` via `F: Fn` | `call_generic(safe_fn, 52)` vs `call_generic(f_noncap, 98)` (`f_noncap = \|x\| x+1`) | `GEN_SZ=0`, `GEN_RES=55`, `FNPTR_TRAIT_SZ=8`, `FNPTR_TRAIT_RES=99` | `FnDef` passes 0-byte ZST (`ShimKind::FnPtr`), `fn()` passes 8-byte pointer. |
| Capturing closure -> `fn` (negative) | `let _f: fn(u32) -> u32 = \|x\| x + k;` | Rejected (`rc=1`): `error[E0308]` (`\`k\` captured here`) | `upvars_mentioned` non-empty. |
| Mention-only closure -> `fn` (negative) | `let _f: fn(u32) -> u32 = \|x\| { let _ = k; x + 1 };` | Rejected (`rc=1`): `error[E0308]` (`\`k\` captured here` at `let _ = k;`) | `sig_for_closure_coercion` inspects `upvars_mentioned` before RFC 2229 discard minimization. |
| `unsafe` `FnDef` -> `safe fn` (negative) | `unsafe fn danger(x: u32) -> u32 { x + 1 } ... let _f: fn(u32) -> u32 = danger;` | Rejected (`rc=1`): `error[E0308]` (`expected safe fn, found unsafe fn`) | Safety cannot narrow across coercion. |
| Intrinsic -> `fn` (negative) | `let _f: unsafe extern "rust-intrinsic" fn(u32) -> u32 = core::intrinsics::black_box::<u32>;` | Rejected (`rc=1`): `E0703`, `E0658`, `error[E0308]: cannot coerce intrinsics to function pointers` | Explicitly rejected in `sig_for_fn_def_coercion`. |

#### Codegen Lowering of Non-Capturing Closures (`PassMode::Ignore` on ZST `self`)

In `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` (`f7da9a4` `L521-555`, `14210df` `L416-445`), lowering `ClosureFnPointer` calls `ty::Instance::resolve_closure(..., ty::ClosureKind::FnOnce)`. Inside `ShimKind::ClosureOnce`, the ZST closure `self` argument receives `PassMode::Ignore` in `compiler/rustc_ty_utils/src/abi.rs:437-441`, eliminating the environment parameter from the generated LLVM signature. Part C verifies this directly in LLVM IR (`-C opt-level=3 --emit=llvm-ir`) and MIR (`-Zdump-mir=all`):
- **Optimized MIR (`ir_probe.reify_noncap_closure.3-3-000.runtime-optimized.after.mir`)**:
  ```rust
  _0 = const ZeroSized: {closure@$WORK/ir_probe.rs:36:5: 36:8} as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit));
  ```
- **Lowered LLVM IR**: `reify_noncap_closure` returns `@_RNvYNCNvCs39AAWccqKvi_8ir_probe20reify_noncap_closure0INtNtNtCs8b4M6GsfcPr_4core3ops8function6FnOnceTmEE9call_onceB6_`, whose compiled LLVM function takes only `(i32 noundef %0)` with zero closure-pointer argument:
  ```llvm
  define internal noundef i32 @_RNvYNCNvCs39AAWccqKvi_8ir_probe20reify_noncap_closure0INtNtNtCs8b4M6GsfcPr_4core3ops8function6FnOnceTmEE9call_onceB6_(i32 noundef %0) unnamed_addr #3 personality ptr @rust_eh_personality {
  start:
    %_0.i = add i32 %0, 7
    ret i32 %_0.i
  }
  ```

In Lean `v4.34.1`, these coercion rules and the semantic impossibility of environmentless multi-capture dispatch are proved in `zero_capture_closure_is_zst` (`L559-562`), `zero_capture_closure_coerces_complete` (`L591-597`), `nonempty_upvars_closure_e0308_necessary` (`L606-609`), `mention_only_upvar_blocks_coercion` (`L619-623`), `closure_coercion_iff_zero_upvars` (`L628-633`), `fndef_safety_widening_and_rejection` (`L648-653`), `intrinsic_and_force_inline_fndef_rejected` (`L658-660`), and `environmentless_fnptr_cannot_distinguish_captures` (`L669-675`).

### 4. Direct Monomorphized Calls, Indirect Function Pointer Calls, and `Fn` Trait Dispatch Shims

Calling an untracked `FnDef` through a generic `F: Fn(u32) -> u32` parameter erases the ZST callee and monomorphizes down to a static direct `tail call`, whereas calling a `fn(u32) -> u32` value emits an indirect `invoke` (or `tail call`) through a `nonnull` code pointer. Crucially, passing an `FnDef` to `F: Fn(...)` synthesizes `ShimKind::FnPtr`, whose untupling shim lives inside `core::ops::function`.

```text
Basis: source + execution + derived
```

#### Source Mechanics and Observed IR/MIR (`ir_probe.rs`)

In `compiler/rustc_ty_utils/src/instance.rs:349-359`, `<F as FnOnce/FnMut/Fn>::call*` when `F` is `ty::FnDef | ty::FnPtr` resolves to `ShimKind::FnPtr` (`compiler/rustc_mir_transform/src/shim.rs:781-1009`), constructing a wrapper shim that untuples the argument tuple `_2` and invokes `(*_1)(move (_2.0))`.

Part C (`-C opt-level=3 --emit=llvm-ir` and `-Zdump-mir=all`, `probe_results.json`) shows all three call paths:
1. **Direct generic `FnDef` call (`call_via_fndef` -> `apply_generic::<step>`)**:
   `apply_generic` monomorphized with `step` omits the ZST `FnDef` value from the LLVM IR parameter list completely:
   ```llvm
   define internal fastcc noundef i32 @_RINvCs39AAWccqKvi_8ir_probe13apply_genericNvB2_4stepEB2_(i32 noundef %x) unnamed_addr #1 personality ptr @rust_eh_personality {
   start:
   ; call ir_probe::step
     %_0.i = tail call noundef i32 @_RNvCs39AAWccqKvi_8ir_probe4step(i32 noundef %x) #7
     ret i32 %_0.i
   }
   ```
2. **Indirect `fn(u32) -> u32` call (`call_via_fnptr` and `apply_generic::<fn(u32) -> u32>`)**:
   `call_via_fnptr` receives `ptr noundef nonnull readonly captures(none) %f` and executes an indirect `invoke`:
   ```llvm
   define noundef i32 @call_via_fnptr(ptr noundef nonnull readonly captures(none) %f, i32 noundef %x) unnamed_addr #4 personality ptr @rust_eh_personality {
   start:
     %_0 = invoke noundef i32 %f(i32 noundef %x)
             to label %bb1 unwind label %terminate
   ```
   When dispatched through `apply_generic::<fn(u32) -> u32>` (`call_fnptr_via_trait`), LLVM passes `ptr noundef nonnull readonly captures(none) %0` (`fn()`) and `i32 %x`, executing `tail call noundef i32 %0(i32 noundef %x)`.
3. **`ShimKind::FnPtr` MIR dump (`core.ops-function-Fn-call.3-3-000.runtime-optimized.after.mir`)**:
   ```rust
   fn call(_1: &fn(u32) -> u32 {tracked_callee}, _2: (u32,)) -> <fn(u32) -> u32 {tracked_callee} as FnOnce<(u32,)>>::Output {
       let mut _0: <fn(u32) -> u32 {tracked_callee} as FnOnce<(u32,)>>::Output;
       bb0: {
           _0 = move (*_1)(move (_2.0: u32)) -> [return: bb1, unwind continue];
       }
       bb1: {
           return;
       }
   }
   ```
4. **Monomorphic item collection (`-Zprint-mono-items=yes` excerpt)**: `rustc` emits `MONO_ITEM fn tracked_callee - shim(reify)`, `MONO_ITEM fn <fn(u32) -> u32 {step} as std::ops::Fn<(u32,)>>::call - shim(fn(u32) -> u32 {step})`, `MONO_ITEM fn <fn(u32) -> u32 {tracked_callee} as std::ops::Fn<(u32,)>>::call - shim(fn(u32) -> u32 {tracked_callee})`, and `MONO_ITEM fn <{closure@$WORK/ir_probe.rs:36:5: 36:8} as std::ops::FnOnce<(u32,)>>::call_once - shim`.

In Lean `v4.34.1`, `fndef_to_fnptr_obs_equiv_untracked` (`L996-1002`), `noncap_closure_to_fnptr_obs_equiv` (`L1012-1015`), `stepEquiv_reify_untracked` (`L1384-1388`), `stepEquiv_reify_noncap_closure` (`L1393-1396`), `evalPipeline_congr` (`L1409-1412`), and `witness_part_c_step_reify_equivalence` (`L1343-1347`) establish exact observational and trace equivalence for untracked items and non-capturing closures under reification.

### 5. `#[track_caller]` `ReifyShim` Wrapper Synthesis and Call-Site Location Semantics

When an item carries `#[track_caller]`, its concrete ABI includes a trailing implicit caller-location argument (`ptr noalias noundef readonly align 8 captures(none) dereferenceable(24)` pointing to a `core::panic::Location<'static>`). Because an ordinary `fn(...)` pointer ABI omits that implicit parameter, `rustc` synthesizes `ShimKind::Reify` so indirect calls through `fn()` do not read uninitialized/stale location registers — binding the target item's own definition span statically instead.

```text
Basis: source + execution + derived
```

#### Compiler Resolution and Codegen Pipeline

1. **Resolution (`compiler/rustc_middle/src/ty/instance.rs:45-160, 306-320, 655-702`)**: `ty::Instance::resolve_for_fn_ptr` resolves the underlying callee for `ReifyFnPointer`. When the callee requires a caller location (`#[track_caller]`) — or requires a distinct KCFI reification shim — it resolves to `ShimKind::Reify(def_id, reason)` rather than calling the bare target symbol directly.
2. **Shim MIR construction (`compiler/rustc_mir_transform/src/shim.rs:32-73, 781-1009`)**: `make_shim` handles `ShimKind::Reify(def_id, reason)` via `build_call_shim(tcx, shim, None, CallKind::Direct(def_id))` with `span = tcx.def_span(def_id)`. The synthesized wrapper has two basic blocks (`bb0` calling `tracked_callee(move _1)` -> `bb1: return`):
   ```rust
   // MIR for `tracked_callee` after runtime-optimized (`ir_probe.tracked_callee.3-3-000.runtime-optimized.after.mir`)
   fn tracked_callee(_1: u32) -> u32 {
       let mut _0: u32;
       bb0: {
           _0 = tracked_callee(move _1) -> [return: bb1, unwind continue];
       }
       bb1: {
           return;
       }
   }
   ```
   - **MIR dump stem-overwrite hazard observed**: `ir_probe.tracked_callee.1-1-003.SimplifyCfg-make_shim.after.mir` and `ir_probe.tracked_callee.3-3-000.runtime-optimized.after.mir` collide on the same output filename stem as `tracked_callee` itself, overwriting the target body's MIR dump with the 2-block `ShimKind::Reify` MIR!
3. **Codegen and LLVM IR (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:521-555`, `block.rs:1060-1165, 1430-1620`)**:
   - Direct call `call_tracked_direct` passes a static 24-byte `Location` for its callsite (`@alloc_2043973f129ffcc9ca1bfb095f1ea61d`):
     ```llvm
     %_0 = tail call noundef i32 @_RNvCs39AAWccqKvi_8ir_probe14tracked_callee(i32 noundef %x, ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_2043973f129ffcc9ca1bfb095f1ea61d)
     ```
   - Coercing `tracked_callee as fn(u32) -> u32` inside `reify_tracked_fn` returns `@_RNSNvCs39AAWccqKvi_8ir_probe14tracked_callee5reify` (shifting under `-Zsanitizer=kcfi` to `@_RNSNvCs39AAWccqKvi_8ir_probe14tracked_callee11reify_fnptr(i32 noundef %_1) unnamed_addr #1 !kcfi_type !6`), which takes one explicit `i32 %_1` argument and tail-calls `tracked_callee` with `reify`'s static `def_span` allocation `@alloc_ea61ed1d21bc87c4baae4a310296c961`:
     ```llvm
     define internal noundef i32 @_RNSNvCs39AAWccqKvi_8ir_probe14tracked_callee5reify(i32 noundef %_1) unnamed_addr #1 {
     start:
     ; call ir_probe::tracked_callee
       %_0 = tail call noundef i32 @_RNvCs39AAWccqKvi_8ir_probe14tracked_callee(i32 noundef %_1, ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_ea61ed1d21bc87c4baae4a310296c961) #7
       ret i32 %_0
     }
     ```
   - Monomorphized generic `apply_generic::<tracked_callee>` (`call_tracked_via_fntrait`) lowers `<tracked_callee as Fn>::call` (`ShimKind::FnPtr`), passing `@alloc_e0cb832995812be2e234c034ca31ebda`, distinct from both direct calls and the `ReifyShim`!

#### Complete 7-Case `#[track_caller]` Location Matrix (`Part D`)

Running `probe_d.rs` across all four execution regimes — native `-C opt-level=0`, native `-C opt-level=3`, Miri default, and Miri `-Zmir-opt-level=3 -Zinline-mir=yes` — yields **identical results** across every single regime (`Part D` in `support/probe_results.json`):

| Probe Key | Call Expression & Source Marker (`probe_d.rs`) | Output (`tag:line`) | Mechanism |
| :--- | :--- | :--- | :--- |
| `DIRECT1` | `tracked_callee(10)` at line `19` (`DIRECT_1_LINE=19`) | `10:19` | Direct `FnDef` call passes line `19`'s static `Location`. |
| `DIRECT2` | `tracked_callee(20)` at line `20` (`DIRECT_2_LINE=20`) | `20:20` | Direct `FnDef` call passes line `20`'s static `Location`. |
| `REIFY1` | `let fp: fn(u32) -> (u32, u32) = tracked_callee;` (line `22`); `fp(10)` (line `23`) | `10:4` | Indirect `fn` pointer calls `tracked_callee - shim(reify)`, passing `tracked_callee`'s own `def_span` (`DEF_LINE=4`). |
| `REIFY2` | `fp(20)` at line `24` (`REIFY_2_LINE=24`) | `20:4` | `ReifyShim` `Location` is callsite-invariant (always line `4`). |
| `HELPER` | `apply_fnptr(fp, 30)` at line `25` (`HELPER_LINE=25`) | `30:4` | Forwarding `fp` through non-`#[track_caller]` helper still executes `ReifyShim` (line `4`). |
| `FNTRAIT_FNPTR` | `apply_fntrait(fp, 40)` at line `26` (`FNTRAIT_CALLER_LINE=26`) | `40:4` | `<fn() as Fn>::call` dispatches indirectly through `fp`, landing in `ReifyShim` (line `4`). |
| `FNTRAIT_FNDEF` | `apply_fntrait(tracked_callee, 50)` at line `27` (`FNDEF_FNTRAIT_CALLER_LINE=27`) | `50:79` | `<FnDef as Fn>::call` lowers through `ShimKind::FnPtr` inside `library/core/src/ops/function.rs:79` (`core_ops_function_fn_call_line = 79`), whose `def_span` overrides both line `27` and line `4`. |

In Lean `v4.34.1`, `reifyShim_abi_safety` (`L1045-1056`), `track_caller_reify_shim_soundness` (`L1087-1096`), `track_caller_reify_constancy_across_callsites` (`L1109-1123`), `kcfi_reify_reason_preserves_behavior` (`L1141-1145`), `fnTrait_fnptr_vs_fndef_track_caller_asymmetry` (`L1154-1165`), `optFnPtr_dispatch_track_caller_soundness` (`L1456-1465`), `ce_omitting_reify_shim_breaks_abi_and_location` (`L1182-1190`), and `witness_part_d_track_caller_matrix` (`L1300-1318`) formalize this matrix and prove that omitting `ReifyShim` breaks ABI register typing.

### 6. Kernel-Checked Lean `v4.34.1` Soundness Formalization and Anneal TCB Boundary Analysis

Our formalization in `support/FnDefZstFnPtrNicheAndReifyShimSoundness.lean` (`1,626` LOC, `72,457` bytes) mechanizes the full subsystem cleanly inside Lean `v4.34.1` using purely structural recursion with every definition marked `noncomputable def` and zero uses of classical choice, `omega`, `bv_decide`, `native_decide`, `partial def`, `WellFounded`, `Acc.rec`, or `_unsafe_rec` compiled recursion helpers (`EnvironmentAudit.lean` MetaM kernel audit reports `260` theorem constants from `53` declared `theorem`s, `513` definition constants from `69` declared `noncomputable def`/`abbrev`s, and `31` inductive constants from `30` declared `inductive`/`structure`s; reachable axioms strictly `[Quot.sound, propext]`).

```text
Basis: source + execution + derived
```

#### Headline Formal Theorems (`support/FnDefZstFnPtrNicheAndReifyShimSoundness.lean`)

| Domain | Theorem Name & Location | Formal Statement & Significance |
| :--- | :--- | :--- |
| Layout & ZST | `fnDef_layout_is_sized_zst` (`L306-310`) | `(computeLayout (.fnDef id sig))` satisfies `sizeBytes = 0`, `alignBytes = 1`, `sized = true`, `nicheAvailable = 0`. |
| Layout & ZST | `tuple_fnDef_vs_fnPtr_with_u32` (`L323-325`) | `(u32, FnDef)` has `sizeBytes = 4`, whereas `(u32, fn())` has `sizeBytes = 16`. |
| Niche | `fnPtr_layout_8B_nonnull_niche` (`L330-335`) | `FnPtr` has `sizeBytes = 8`, `alignBytes = 8`, `validRange = nonNullPtrRange`, `nicheAvailable = 1`, `backendRepr = .scalar`. |
| Niche | `option_size_trichotomy` (`L1554-1558`) | Proves simultaneously: `size(Option<FnPtr>) = size(FnPtr)` (`8 = 8`), `size(Option<FnDef>) > size(FnDef)` (`1 > 0`), and `size(Option<Option<FnPtr>>) > size(Option<FnPtr>)` (`16 > 8`). |
| Niche Bijection | `optFnPtr_niche_bijective` (`L460-462`), `optFnPtr_none_iff_zero` (`L427-428`), `null_word_invalid_for_fnPtr` (`L455-456`) | Proves `encodeOptFnPtr : Option CodeAddr -> Word64` and `decodeOptFnPtr` form a constructive bijection with `(encodeOptFnPtr opt).val = 0 <-> opt = none` and `nonNullPtrRange.contains Word64.zero.val = false`. |
| Coercion | `closure_coercion_iff_zero_upvars` (`L628-633`), `mention_only_upvar_blocks_coercion` (`L619-623`) | Proves `coerceClosureToFnPtr` succeeds iff `cl.upvarsMentioned = []`, including when `cl.captures = []` yet `cl.upvarsMentioned != []` (`mention_only_upvar_blocks_coercion` forces `.err .closureHasUpvars`, modeling `E0308`). |
| Coercion Neg. | `environmentless_fnptr_cannot_distinguish_captures` (`L669-675`) | Proves mathematically why any captured difference `body k1 x != body k2 x` cannot be satisfied simultaneously by a single bare function `bareFnPtr : Nat -> Nat`. |
| Reify / Obs. Equiv | `fndef_to_fnptr_obs_equiv_untracked` (`L996-1002`), `noncap_closure_to_fnptr_obs_equiv` (`L1012-1015`), `evalPipeline_congr` (`L1409-1412`) | Calling a reified untracked `FnDef` or non-capturing closure produces identical outcome and call trace (`StepEquiv` congruence across call pipelines) to a direct monomorphic call. |
| `#[track_caller]` | `reifyShim_abi_safety` (`L1045-1056`) | Starting from `AbiRegsWellTyped (fnPtrAbi explicitArity) regs`, `applyReifyShimAbi` preserves every `k < explicitArity` argument register unchanged and sets slot `explicitArity` to `.loc item.defSpan`, yielding a well-typed `(explicitArity + 1)` ABI. |
| `#[track_caller]` | `track_caller_reify_shim_soundness` (`L1087-1096`), `track_caller_reify_constancy_across_callsites` (`L1109-1123`) | Proves indirect reified `fn()` call produces the exact outcome of calling `item` directly at `item.defSpan`, invariant even when direct calls at distinct callsites `cs1 != cs2` observe different results. |
| `Fn` Trait Asymmetry | `fnTrait_fnptr_vs_fndef_track_caller_asymmetry` (`L1154-1165`) | Proves `<fn() as Fn>::call` lands in `ReifyShim` (`item.defSpan`, line `4`) while `<FnDef as Fn>::call` binds `fnTraitSpan` (`core/src/ops/function.rs:79`). |
| ABI Counterexample | `ce_omitting_reify_shim_breaks_abi_and_location` (`L1182-1190`) | Counterexample proving omitting `ReifyShim` yields `.ubAbiLocationMismatch` and leaves `staleLoc != item.defSpan` in the implicit location slot. |
| Probe Witnesses | `witness_part_a_layout_sizes` (`L1230`), `witness_part_a_niche_encoding` (`L1247`), `witness_part_b_coercion_outcomes` (`L1264`), `witness_part_d_track_caller_matrix` (`L1300`), `witness_part_c_step_reify_equivalence` (`L1343`) | Kernel-checked theorem witnesses matching Parts A–D of `support/probe_results.json`. |
| Anneal Boundary | `anneal_tcb_fails_closed_on_fn_types` (`L1594-1601`), `zst_move_preservation_vs_fnptr_deinit` (`L1620-1623`) | Records Anneal's fail-closed `MirTy` boundary and ZST move vs scalar deinitialization asymmetry. |

#### Implications for `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Direct inspection of `joshlf/anneal` (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/rustc-capture/src/driver.rs`, and `vendor/lean-miri/Miri/Interpreter/Cast.lean`) shows a sharp distinction between vendored interpretation and kernel TCB support:
1. **Vendored interpreter vs. Trusted verifier**: `vendor/lean-miri/Miri/Interpreter/Cast.lean:365-384` already handles `ReifyFnPointer` and `ClosureFnPointer` casts in `lean-miri`. Conversely, Anneal's kernel-verified TCB (`Trusted.MirAst`: `MirTy` `L308-321`, `Rvalue` `L612-628`, `TerminatorKind` `L780-795`; `Trusted.MirSemantics`: `evalRvalue` `L1313` and `evalTerminator` `L1568` returning `.fault .unsupported` on `.call`) currently fails closed on function types, pointer coercions, and function calls (`anneal_tcb_fails_closed_on_fn_types`).
2. **ZST Move Hazard (`evalOperandToSlot`, `deinitMovedPlace = true`, `MirSemantics.lean:949-976`)**: `evalOperandToSlot` marks moved places uninitialized via `deinitMovedPlace = true`. While reading an uninitialized or zeroed 8-byte `FnPtr` slot is invalid/UB, `FnDef` and non-capturing `Closure` singletons carry zero bytes (`zst_move_preservation_vs_fnptr_deinit`). Extending `Trusted.MirSemantics` in future work to cover function items, `fn()` pointers, or calls requires:
   - representing `FnDef` and non-capturing closures as `0`-byte, `1`-aligned sized ZSTs (`largest_niche = None`) without introducing uninitialized-byte traps on zero-byte copies/moves;
   - enforcing non-zero scalar validity (`word != 0`) on `FnPtr` reads and decoding `Option<fn()>` at `niche_start = 0`;
   - modeling `ReifyShim` / `ShimKind::FnPtr` caller-location binding (`def_span`) explicitly during indirect call resolution.

## Boundaries

- **not examined — Runtime function pointer address equality and linker ICF**: Whether distinct zero-sized `FnDef` items or separate coercions of identical bodies produce identical or distinct `usize` code addresses at runtime under LLVM Identical Code Folding (ICF) or `-Zmerge-functions` was not executed or modeled.
- **not examined — Trait objects, async closures, naked functions, variadics, and non-64-bit / Harvard architectures**: `&dyn Fn*`, `AsyncFn*` coroutines, `#[naked]`, variadic `extern "C"`, 32-bit pointer targets, and targets where `dl.instruction_address_space` uses non-64-bit pointers were not probed.
- **not examined — Multi-CGU `ReifyShim` linkage and ThinLTO**: Part C probes compiled with `-C codegen-units=1`; `Linkage::Internal` duplication or merging across multiple CGUs / ThinLTO crates was not tested.
- **unknown — Combined `#[inline(always)]` + `#[track_caller]` reification behavior**: Part B exercised `#[inline(always)]` without `#[track_caller]`, while Parts C and D exercised `#[track_caller]` with `#[inline(never)]`; their combined optimization behavior under reification was not measured.
- **known not to apply — RFC 2229 capture minimization before `fn()` coercion**: Closure-to-`fn` coercion does **not** inherit RFC 2229 field elimination; unused lexical mentions such as `let _ = k;` still fail with `E0308` (`mention_only_upvar_blocks_coercion`).
- **known not to apply — Callsite `#[track_caller]` propagation through `fn()` or `<FnDef as Fn>::call`**: Neither reified `fn()` pointers nor passing a `#[track_caller]` `FnDef` to a non-`#[track_caller]` generic `F: Fn` preserve the outer callsite's location (`REIFY1=10:4` binds line `4`, while `FNTRAIT_FNDEF=50:79` binds `core/src/ops/function.rs:79`).
- **unsupported — End-to-end linkage into `joshlf/anneal` (`c131b320`)**: `Trusted.MirAst` and `Trusted.MirSemantics` fail closed on function types, pointer coercions, and `.call` terminators (`MirSemantics.lean:1568`). Consequently, `support/FnDefZstFnPtrNicheAndReifyShimSoundness.lean` is a **standalone** Lean `v4.34.1` formalization establishing mathematical soundness of the modeled compiler semantics and matching the probe outputs, rather than a live proof integrated into `anneal`'s TCB.
- **not examined (execution) — `rustc` revisions `49d7345`, `3ef0c22`, and `f7da9a4`**: These revisions were verified by upstream source audit only; empirical binaries, LLVM IR, MIR dumps, KCFI headers, and Miri checks ran on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with `LLVM 22.1.6`.

## Evidence

### Primary Git Source Anchors

All upstream commits were resolved directly against `rust-lang/rust`, `joshlf/anneal`, and `leanprover/lean4`.

1. **`rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `49d734536222bf28bb6d07d885b3a81d145981da`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`)**:
   - `compiler/rustc_type_ir/src/ty_kind.rs`: `14210df` `L168, L188`; `f7da9a4` `L223, L243` (`TyKind::FnDef`, `TyKind::FnPtr`).
   - `compiler/rustc_middle/src/ty/sty.rs`: `f7da9a4` `L677-694`; `14210df` `L713-730`; `49d7345` `L708-725`; `3ef0c22` `L717-734` (`Ty::new_fn_def`, `Ty::new_fn_ptr`).
   - `compiler/rustc_ty_utils/src/layout.rs`: `f7da9a4` / `3ef0c22` `L428-432, L544-547`; `49d7345` `L431-435, L547-550`; `14210df` `L401-405, L516-519, L574-743`.
   - `compiler/rustc_abi/src/layout/simple.rs`: `f7da9a4` & `14210df` `L13-30` (`LayoutData::unit`).
   - `compiler/rustc_abi/src/lib.rs`: `f7da9a4` `L2122-2214` (`Niche::{from_scalar, available, reserve}`).
   - `compiler/rustc_abi/src/layout/enum_layout.rs`: `f7da9a4` `L15-58, L537-679`; `3ef0c22` `L15-58, L558-664` (`move_start`, `calculate_niche_abi`).
   - `compiler/rustc_ty_utils/src/abi.rs`: `f7da9a4` `L318-338` (`ArgAttribute::NonNull`), `L437-441` (`PassMode::Ignore` for ZSTs).
   - `compiler/rustc_codegen_llvm/src/abi.rs`: `14210df` `L43`; `f7da9a4` `L43, L47` (`ArgAttribute::NonNull -> AttributeKind::NonNull`).
   - `compiler/rustc_hir_typeck/src/coercion.rs`: `f7da9a4` / `3ef0c22` `L327-346, L1091-1113, L1117-1134, L1305-1340, L1342-1372`; `14210df` `L1053, L1079, L1292`; `49d7345` `L1041, L1067, L1292`.
   - `compiler/rustc_middle/src/ty/instance.rs`: `f7da9a4` `L45-160, L306-320, L655-702`; `14210df` `L45-145, L311-319, L584-627`.
   - `compiler/rustc_ty_utils/src/instance.rs`: `L349-359` (`FnDef | FnPtr -> ShimKind::FnPtr`).
   - `compiler/rustc_mir_transform/src/shim.rs`: `f7da9a4` `L32-73, L781-1009`; `14210df` `L67-98, L811-1009`.
   - `compiler/rustc_codegen_ssa/src/mir/rvalue.rs`: `f7da9a4` `L521-555`; `14210df` `L416-445`.
   - `compiler/rustc_codegen_ssa/src/mir/block.rs`: `f7da9a4` `L1060-1165, L1430-1620`.
   - `library/core/src/ops/function.rs`: `L79` (`core_ops_function_fn_call_line: 79` in `rustc 1.98.0-nightly 14210df0e` sysroot).
2. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)**:
   - `trusted/lean/Trusted/MirAst.lean`: `L308-321` (`MirTy`), `L612-628` (`Rvalue`), `L780-795` (`TerminatorKind`).
   - `trusted/lean/Trusted/MirSemantics.lean`: `L949-976` (`evalOperandToSlot`, `deinitMovedPlace = true`), `L1313` (`evalRvalue`), `L1568` (`evalTerminator` `.call => .fault .unsupported`).
   - `vendor/lean-miri/Miri/Interpreter/Cast.lean`: `L365-384` (`ReifyFnPointer` / `ClosureFnPointer`).
   - `trusted/rustc-capture/src/driver.rs`: `L1-152`.

### Empirical Execution Evidence (`support/probe_results.json`)

- Observed `2026-11-24` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`LLVM version: 22.1.6`, `x86_64-unknown-linux-gnu`) and `$SYSROOT/bin/miri --edition=2024 --sysroot $MIRI_SYSROOT`.
- All **`103/103` checks passed (`failed: []`)**: `41` checks in Part A (native & Miri sizes, niche zero-bit representation, and null-`fn()` Miri UB trap), `24` checks in Part B (native & Miri positive coercions + `4` `rustc` negative controls), `10` checks in Part C (LLVM `-O3` IR, `-Zdump-mir=all` across `1,298` dump files, `-Zprint-mono-items=yes`, and `-Zsanitizer=kcfi`), and `28` checks in Part D (`#[track_caller]` matrix across `-O0`, `-O3`, Miri default, and Miri `-Zmir-opt-level=3 -Zinline-mir=yes`).

### Lean `v4.34.1` Verification Receipt (`support/lean_check_output.txt`)

Verified against `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with flags `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`:
```text
module constants audited: 260 theorems, 513 definitions, 31 inductive types
axioms reachable from the module: [Quot.sound, propext]
audit passed: 0 _unsafe_rec; 0 axiom/opaque/unsafe/partial; 0 WellFounded/Acc.rec; 0 Classical.choice/sorryAx/ofReduceBool
```

### Preserved Package Artifacts

| Package File | Lines | Bytes | SHA-256 Digest |
| :--- | ---: | ---: | :--- |
| `support/probe_fndef_fnptr_reify_shims.py` | 933 | 30,511 | `2e4a935a822e95aa575c185184f24236525b3ecb1a6af78c987d0ae342a9d837` |
| `support/probe_results.json` | 703 | 44,976 | `925b20d732116054d9525b0b90536dd6b05d446a5e54e9dbef40f3408c41af75` |
| `support/FnDefZstFnPtrNicheAndReifyShimSoundness.lean` | 1,626 | 72,457 | `ebe041d1de95a60e1ba38a82aaa8ae1556c820f25c5ea736eff96cbfcd00192c` |
| `support/EnvironmentAudit.lean` | 61 | 3,025 | `66a0f7a6fbe6b39a920f6a76d799814b002e19792fed02396f5b8d03400d37d7` |
| `support/lean_check_output.txt` | 3 | 255 | `d04c66db047d180f78a6aae4c647fc74c2f52f5a8d6cadf44227bb09dc50fec1` |

## Revalidation

To revalidate the empirical and mechanized claims in this package cleanly on another toolchain or commit:

1. **Re-run all 103 `rustc`, LLVM IR, MIR dump, KCFI, and Miri probes** (requires `rustc +nightly` with `miri` and `rust-src` installed):
   ```bash
   python3 support/probe_fndef_fnptr_reify_shims.py
   ```
   Confirm exit code `0`, `(103/103 checks passed)`, `self_checks.failed == []`, and check `core_ops_function_fn_call_line` in `support/probe_results.json` if `library/core/src/ops/function.rs` moves line `79`.

2. **Re-verify the Lean `v4.34.1` formalization and kernel/MetaM purity audit** into a temporary `.olean` directory:
   ```bash
   LEAN_BIN="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
   OLEAN_TMP="$(mktemp -d)"
   trap 'rm -rf "$OLEAN_TMP"' EXIT
   cd support
   "$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     --root=. -o "$OLEAN_TMP/FnDefZstFnPtrNicheAndReifyShimSoundness.olean" \
     FnDefZstFnPtrNicheAndReifyShimSoundness.lean
   LEAN_PATH="$OLEAN_TMP" "$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     EnvironmentAudit.lean
   ```
   Confirm zero warnings/errors and unchanged axiom/recursion audit output (`[Quot.sound, propext]`, `0 _unsafe_rec`).

3. **Targeted upstream source diff check (`rust-lang/rust` and `joshlf/anneal`)**:
   ```bash
   git -C <rust-repo> diff f7da9a42368f31abb02b8064bb93a11bf9ba9f5e..HEAD -- \
     compiler/rustc_type_ir/src/ty_kind.rs \
     compiler/rustc_middle/src/ty/sty.rs \
     compiler/rustc_ty_utils/src/layout.rs \
     compiler/rustc_abi/src/lib.rs \
     compiler/rustc_abi/src/layout/enum_layout.rs \
     compiler/rustc_hir_typeck/src/coercion.rs \
     compiler/rustc_middle/src/ty/instance.rs \
     compiler/rustc_mir_transform/src/shim.rs \
     compiler/rustc_ty_utils/src/abi.rs \
     compiler/rustc_codegen_ssa/src/mir/rvalue.rs \
     compiler/rustc_codegen_ssa/src/mir/block.rs
   git -C <anneal-repo> diff c131b320eeeb26ef692e5afd5ec8db49ee518613..HEAD -- \
     trusted/lean/Trusted/MirAst.lean \
     trusted/lean/Trusted/MirSemantics.lean
   ```

4. **Corpus structure and metadata validation** from the corpus root:
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
